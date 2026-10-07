//! Facts about each expression that kernels otherwise compute on import.

use crate::{
    error::{corrupt, Result},
    record::{Binding, Record},
};
use serde::{Deserialize, Serialize};
use xxhash_rust::xxh3::xxh3_64;

/// Written after every expression record in a blean file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct Info {
    /// Structural hash, blind to binder names and binder info as expression identity is.
    #[serde(with = "postcard::fixint::le")]
    pub hash: u64,
    /// One more than the largest de Bruijn index that escapes the term, or 0 if it is closed.
    pub loose_bvar_range: u32,
    /// [`Info::LEVEL_PARAM`] and [`Info::FVAR`].
    pub flags: u8,
}

impl Info {
    pub const LEVEL_PARAM: u8 = 1;
    /// Never set by exporters, since declarations are closed; kept for kernels that share the
    /// layout with their own terms.
    pub const FVAR: u8 = 2;

    #[must_use]
    pub const fn has_level_param(self) -> bool {
        self.flags & Self::LEVEL_PARAM != 0
    }
}

/// Computes [`Info`] for a record stream, from the info of the records each one refers to.
#[derive(Debug, Default)]
pub struct Tracker {
    names: Vec<u64>,
    levels: Vec<(u64, bool)>,
    exprs: Vec<Info>,
    buf: Vec<u8>,
}

/// `xxh3_64(tag ++ parts)`: the hash of every node, with child hashes and integers
/// little-endian and strings as their UTF-8 bytes.
fn hash(buf: &mut Vec<u8>, tag: u8, parts: impl FnOnce(&mut Vec<u8>)) -> u64 {
    buf.clear();
    buf.push(tag);
    parts(buf);
    xxh3_64(buf)
}

fn put(buf: &mut Vec<u8>, x: u64) {
    buf.extend_from_slice(&x.to_le_bytes());
}

impl Tracker {
    #[must_use]
    pub fn new() -> Self {
        let mut buf = Vec::new();
        Self {
            names: vec![hash(&mut buf, 0, |_| {})],
            levels: vec![(hash(&mut buf, 3, |_| {}), false)],
            exprs: Vec::new(),
            buf,
        }
    }

    fn name(&self, id: u32) -> Result<u64> {
        get(&self.names, id).copied()
    }

    fn level(&self, id: u32) -> Result<(u64, bool)> {
        get(&self.levels, id).copied()
    }

    fn expr(&self, id: u32) -> Result<Info> {
        get(&self.exprs, id).copied()
    }

    /// Take in the next record, returning its info if it is an expression.
    pub fn observe(&mut self, r: &Record<'_>) -> Result<Option<Info>> {
        let buf = &mut self.buf;
        match r {
            Record::NameStr { pre, str } => {
                let p = get(&self.names, *pre)?;
                let h = hash(buf, 1, |b| {
                    put(b, *p);
                    b.extend_from_slice(str.as_bytes());
                });
                self.names.push(h);
            }
            Record::NameNum { pre, i } => {
                let p = get(&self.names, *pre)?;
                let h = hash(buf, 2, |b| {
                    put(b, *p);
                    put(b, *i);
                });
                self.names.push(h);
            }
            Record::Succ(a) => {
                let (a, p) = self.level(*a)?;
                let h = hash(&mut self.buf, 4, |b| put(b, a));
                self.levels.push((h, p));
            }
            Record::Max(a, b) | Record::IMax(a, b) => {
                let ((a, pa), (b, pb)) = (self.level(*a)?, self.level(*b)?);
                let tag = if matches!(r, Record::Max(..)) { 5 } else { 6 };
                let h = hash(&mut self.buf, tag, |x| {
                    put(x, a);
                    put(x, b);
                });
                self.levels.push((h, pa || pb));
            }
            Record::Param(n) => {
                let n = self.name(*n)?;
                let h = hash(&mut self.buf, 7, |b| put(b, n));
                self.levels.push((h, true));
            }
            Record::Meta(_) | Record::Decl(_) | Record::End(_) => {}
            _ => {
                let info = self.expr_info(r)?;
                self.exprs.push(info);
                return Ok(Some(info));
            }
        }
        Ok(None)
    }

    fn expr_info(&mut self, r: &Record<'_>) -> Result<Info> {
        let lp = |b: bool| if b { Info::LEVEL_PARAM } else { 0 };
        let node = |this: &mut Self, tag: u8, kids: &[Info], extra: &[u64], lbr: u32| {
            let h = hash(&mut this.buf, tag, |b| {
                for k in kids {
                    put(b, k.hash);
                }
                for &x in extra {
                    put(b, x);
                }
            });
            Info {
                hash: h,
                loose_bvar_range: lbr,
                flags: kids.iter().fold(0, |f, k| f | k.flags),
            }
        };
        let binder = |this: &mut Self, tag: u8, b: &Binding| -> Result<Info> {
            let (t, body) = (this.expr(b.ty)?, this.expr(b.body)?);
            let lbr = t
                .loose_bvar_range
                .max(body.loose_bvar_range.saturating_sub(1));
            Ok(node(this, tag, &[t, body], &[], lbr))
        };
        Ok(match r {
            Record::BVar(i) => {
                let i = u32::try_from(*i)
                    .ok()
                    .and_then(|i| i.checked_add(1))
                    .ok_or_else(|| corrupt("bound variable index too large"))?;
                Info {
                    hash: hash(&mut self.buf, 8, |b| put(b, u64::from(i - 1))),
                    loose_bvar_range: i,
                    flags: 0,
                }
            }
            Record::Sort(l) => {
                let (l, p) = self.level(*l)?;
                Info {
                    hash: hash(&mut self.buf, 9, |b| put(b, l)),
                    loose_bvar_range: 0,
                    flags: lp(p),
                }
            }
            Record::Const { name, us } => {
                let n = self.name(*name)?;
                let us = us
                    .iter()
                    .map(|&u| self.level(u))
                    .collect::<Result<Vec<_>>>()?;
                Info {
                    hash: hash(&mut self.buf, 10, |b| {
                        put(b, n);
                        for &(u, _) in &us {
                            put(b, u);
                        }
                    }),
                    loose_bvar_range: 0,
                    flags: lp(us.iter().any(|u| u.1)),
                }
            }
            Record::App { fun, arg } => {
                let (f, a) = (self.expr(*fun)?, self.expr(*arg)?);
                let lbr = f.loose_bvar_range.max(a.loose_bvar_range);
                node(self, 11, &[f, a], &[], lbr)
            }
            Record::Lam(b) => binder(self, 12, b)?,
            Record::Pi(b) => binder(self, 13, b)?,
            Record::Let {
                ty, value, body, ..
            } => {
                let (t, v, b) = (self.expr(*ty)?, self.expr(*value)?, self.expr(*body)?);
                let lbr = t
                    .loose_bvar_range
                    .max(v.loose_bvar_range)
                    .max(b.loose_bvar_range.saturating_sub(1));
                node(self, 14, &[t, v, b], &[], lbr)
            }
            Record::Nat(v) | Record::Str(v) => {
                let tag = if matches!(r, Record::Nat(_)) { 15 } else { 16 };
                Info {
                    hash: hash(&mut self.buf, tag, |b| b.extend_from_slice(v.as_bytes())),
                    ..Info::default()
                }
            }
            Record::Proj {
                type_name,
                idx,
                struct_,
            } => {
                let (n, x) = (self.name(*type_name)?, self.expr(*struct_)?);
                let lbr = x.loose_bvar_range;
                node(self, 17, &[x], &[n, *idx], lbr)
            }
            Record::MData(x) => self.expr(*x)?,
            Record::Meta(_)
            | Record::NameStr { .. }
            | Record::NameNum { .. }
            | Record::Succ(_)
            | Record::Max(..)
            | Record::IMax(..)
            | Record::Param(_)
            | Record::Decl(_)
            | Record::End(_) => unreachable!("not an expression"),
        })
    }
}

fn get<T>(table: &[T], id: u32) -> Result<&T> {
    table
        .get(id as usize)
        .ok_or_else(|| corrupt(format!("reference to undefined id {id}")))
}
