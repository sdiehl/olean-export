//! One line of the export stream with every reference resolved to an output id. The
//! traversal in [`crate::Exporter`] produces these and every output format consumes them.
//!
//! The derived serde layout is also the blean format (see [`crate::blean`]), so variant
//! and field order are part of the format and must not change.

use crate::{
    env::{Binder, Hints, QuotKind},
    error::Result,
};
use serde::{Deserialize, Serialize};
use std::borrow::Cow;

/// Ids are implicit: names and levels count from 1 (0 is the anonymous name and the zero
/// level), expressions from 0, each in record order. Records only refer to earlier ones.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Record<'a> {
    /// The `meta` object as JSON. Always first.
    Meta(#[serde(borrow)] Cow<'a, str>),
    NameStr {
        pre: u32,
        #[serde(borrow)]
        str: Cow<'a, str>,
    },
    NameNum {
        pre: u32,
        i: u64,
    },
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
    BVar(u64),
    Sort(u32),
    Const {
        name: u32,
        us: Vec<u32>,
    },
    App {
        fun: u32,
        arg: u32,
    },
    Lam(Binding),
    Pi(Binding),
    Let {
        name: u32,
        ty: u32,
        value: u32,
        body: u32,
        nondep: bool,
    },
    /// Decimal digits.
    Nat(#[serde(borrow)] Cow<'a, str>),
    Str(#[serde(borrow)] Cow<'a, str>),
    Proj {
        type_name: u32,
        idx: u64,
        struct_: u32,
    },
    /// lean4export's metadata wrapper, which kernels read as the wrapped term.
    MData(u32),
    Decl(Decl),
    /// Always last.
    End(Counts),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Binding {
    pub info: Binder,
    pub name: u32,
    pub ty: u32,
    pub body: u32,
}

/// Records written so far for each table, which is also the next id each hands out. Fixed
/// width on the wire, so a blean file ends with these as three little-endian `u32`s.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counts {
    #[serde(with = "postcard::fixint::le")]
    pub names: u32,
    #[serde(with = "postcard::fixint::le")]
    pub levels: u32,
    #[serde(with = "postcard::fixint::le")]
    pub exprs: u32,
}

impl Default for Counts {
    fn default() -> Self {
        Self {
            names: 1,
            levels: 1,
            exprs: 0,
        }
    }
}

impl Record<'_> {
    /// Which table the record adds to, if any.
    #[must_use]
    pub const fn table(&self) -> Option<Table> {
        match self {
            Self::NameStr { .. } | Self::NameNum { .. } => Some(Table::Names),
            Self::Succ(_) | Self::Max(..) | Self::IMax(..) | Self::Param(_) => Some(Table::Levels),
            Self::Meta(_) | Self::Decl(_) | Self::End(_) => None,
            _ => Some(Table::Exprs),
        }
    }
}

impl Record<'_> {
    /// Rewrite every id the record refers to with `f`, given the table it points into.
    pub fn map_ids(&mut self, f: &impl Fn(Table, u32) -> u32) {
        let n = |x: &mut u32| *x = f(Table::Names, *x);
        let l = |x: &mut u32| *x = f(Table::Levels, *x);
        let e = |x: &mut u32| *x = f(Table::Exprs, *x);
        let head = |h: &mut Head| {
            n(&mut h.name);
            h.level_params.iter_mut().for_each(n);
            e(&mut h.ty);
        };
        match self {
            Self::Meta(_) | Self::BVar(_) | Self::Nat(_) | Self::Str(_) | Self::End(_) => {}
            Self::NameStr { pre, .. } | Self::NameNum { pre, .. } => n(pre),
            Self::Succ(a) | Self::Sort(a) => l(a),
            Self::Max(a, b) | Self::IMax(a, b) => {
                l(a);
                l(b);
            }
            Self::Param(p) => n(p),
            Self::Const { name, us } => {
                n(name);
                us.iter_mut().for_each(l);
            }
            Self::App { fun, arg } => {
                e(fun);
                e(arg);
            }
            Self::Lam(b) | Self::Pi(b) => {
                n(&mut b.name);
                e(&mut b.ty);
                e(&mut b.body);
            }
            Self::Let {
                name,
                ty,
                value,
                body,
                ..
            } => {
                n(name);
                e(ty);
                e(value);
                e(body);
            }
            Self::Proj {
                type_name, struct_, ..
            } => {
                n(type_name);
                e(struct_);
            }
            Self::MData(x) => e(x),
            Self::Decl(d) => match d {
                Decl::Axiom { head: h, all, .. } => {
                    head(h);
                    all.iter_mut().flatten().for_each(n);
                }
                Decl::Def {
                    head: h,
                    value,
                    all,
                    ..
                }
                | Decl::Thm {
                    head: h,
                    value,
                    all,
                } => {
                    head(h);
                    e(value);
                    all.iter_mut().for_each(n);
                }
                Decl::Opaque {
                    head: h,
                    value,
                    all,
                    ..
                } => {
                    head(h);
                    e(value);
                    all.iter_mut().flatten().for_each(n);
                }
                Decl::Quot { head: h, .. } => head(h),
                Decl::Inductive { types, ctors, recs } => {
                    for t in types {
                        head(&mut t.head);
                        t.all.iter_mut().for_each(n);
                        t.ctors.iter_mut().for_each(n);
                    }
                    for c in ctors {
                        head(&mut c.head);
                        n(&mut c.induct);
                    }
                    for r in recs {
                        head(&mut r.head);
                        r.all.iter_mut().for_each(n);
                        for rule in &mut r.rules {
                            n(&mut rule.ctor);
                            e(&mut rule.rhs);
                        }
                    }
                }
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Table {
    Names,
    Levels,
    Exprs,
}

impl Counts {
    /// Take the id of `r` if it defines a name, level or expression.
    pub fn assign(&mut self, r: &Record<'_>) -> Option<u32> {
        let next = match r.table()? {
            Table::Names => &mut self.names,
            Table::Levels => &mut self.levels,
            Table::Exprs => &mut self.exprs,
        };
        *next += 1;
        Some(*next - 1)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Safety {
    Safe,
    Unsafe,
    Partial,
}

/// The fields every declaration starts with.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Head {
    pub name: u32,
    pub level_params: Vec<u32>,
    pub ty: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Decl {
    /// `all` is never written by olean-export, but some lean4export versions write it.
    Axiom {
        head: Head,
        is_unsafe: bool,
        all: Option<Vec<u32>>,
    },
    Def {
        head: Head,
        value: u32,
        hints: Hints,
        safety: Safety,
        all: Vec<u32>,
    },
    Thm {
        head: Head,
        value: u32,
        all: Vec<u32>,
    },
    Opaque {
        head: Head,
        value: u32,
        is_unsafe: bool,
        all: Option<Vec<u32>>,
    },
    Quot {
        head: Head,
        kind: QuotKind,
    },
    Inductive {
        types: Vec<IndType>,
        ctors: Vec<IndCtor>,
        recs: Vec<IndRec>,
    },
}

impl Decl {
    /// The declared name, the first type's for an inductive block.
    #[must_use]
    pub fn name(&self) -> Option<u32> {
        match self {
            Self::Axiom { head, .. }
            | Self::Def { head, .. }
            | Self::Thm { head, .. }
            | Self::Opaque { head, .. }
            | Self::Quot { head, .. } => Some(head.name),
            Self::Inductive { types, .. } => types.first().map(|t| t.head.name),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndType {
    pub head: Head,
    pub is_unsafe: bool,
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<u32>,
    pub ctors: Vec<u32>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_reflexive: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndCtor {
    pub head: Head,
    pub is_unsafe: bool,
    pub induct: u32,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndRec {
    pub head: Head,
    pub is_unsafe: bool,
    pub all: Vec<u32>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<IndRule>,
    pub k: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndRule {
    pub ctor: u32,
    pub nfields: u64,
    pub rhs: u32,
}

/// A destination for records. `id` is the id `r` defines, if it defines a name, level or
/// expression; ids count from where the stream started, also across a resumed export.
pub trait Sink {
    type Output;
    fn record(&mut self, id: Option<u32>, r: &Record<'_>) -> Result<()>;
    fn finish(self) -> Result<Self::Output>;
}
