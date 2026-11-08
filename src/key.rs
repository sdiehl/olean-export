//! Declaration keys, shared by external checkers.
//!
//! A unit is one declaration, or one inductive block, and its key is the blake3 hash of a
//! canonical encoding of the unit that names every constant it mentions from an earlier
//! unit by that unit's key. So a key covers its unit's whole dependency closure, and does
//! not depend on id numbering, record order or which file a unit came from.

use crate::{
    env::Hints,
    error::{corrupt, Result},
    record::{Decl, Head, Record, Safety, Sink, Table},
};
use rustc_hash::FxHashMap;

pub type Key = [u8; 32];

/// A declaration and the key of its unit, `None` when the unit has none.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Keyed {
    pub name: String,
    pub key: Option<Key>,
    /// Position in its unit.
    pub offset: u32,
}

mod tag {
    pub(super) const ANON: u8 = 0;
    pub(super) const STR: u8 = 1;
    pub(super) const NUM: u8 = 2;
    pub(super) const ZERO: u8 = 3;
    pub(super) const SUCC: u8 = 4;
    pub(super) const MAX: u8 = 5;
    pub(super) const IMAX: u8 = 6;
    pub(super) const PARAM: u8 = 7;
    pub(super) const VAR: u8 = 8;
    pub(super) const SORT: u8 = 9;
    pub(super) const CONST: u8 = 10;
    pub(super) const APP: u8 = 11;
    pub(super) const LAM: u8 = 12;
    pub(super) const PI: u8 = 13;
    pub(super) const LET: u8 = 14;
    pub(super) const PROJ: u8 = 15;
    pub(super) const NAT: u8 = 16;
    pub(super) const STRLIT: u8 = 17;
    pub(super) const OWN: u8 = 18;
    pub(super) const DEP: u8 = 19;
    pub(super) const AXIOM: u8 = 20;
    pub(super) const QUOT: u8 = 21;
    pub(super) const THM: u8 = 22;
    pub(super) const DEF: u8 = 23;
    pub(super) const OPAQUE: u8 = 24;
    pub(super) const IND: u8 = 25;
    pub(super) const CTOR: u8 = 26;
    pub(super) const REC: u8 = 27;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Name {
    Anon,
    Str(u32, Box<str>),
    Num(u32, u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Level {
    Zero,
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
}

/// Children are resolved through `MData`, names and levels are canonical.
#[derive(Debug)]
enum Expr {
    Var(u64),
    Sort(u32),
    Const(u32, Box<[u32]>),
    App(u32, u32),
    Lam(u32, u32),
    Pi(u32, u32),
    Let(u32, u32, u32, bool),
    Proj(u32, u64, u32),
    Nat(Box<[u8]>),
    Str(Box<str>),
}

/// A [`Sink`] that computes the key of every declaration in an export.
#[derive(Debug)]
pub struct Keys {
    names: Vec<Name>,
    name_ids: FxHashMap<Name, u32>,
    name_of: Vec<u32>,
    levels: Vec<Level>,
    level_ids: FxHashMap<Level, u32>,
    level_of: Vec<u32>,
    exprs: Vec<Expr>,
    expr_of: Vec<u32>,
    decls: FxHashMap<u32, (Option<Key>, u32)>,
    out: Vec<Keyed>,
}

impl Default for Keys {
    fn default() -> Self {
        let mut k = Self {
            names: Vec::new(),
            name_ids: FxHashMap::default(),
            name_of: Vec::new(),
            levels: Vec::new(),
            level_ids: FxHashMap::default(),
            level_of: Vec::new(),
            exprs: Vec::new(),
            expr_of: Vec::new(),
            decls: FxHashMap::default(),
            out: Vec::new(),
        };
        let anon = k.name(Name::Anon);
        let zero = k.level(Level::Zero);
        k.name_of.push(anon);
        k.level_of.push(zero);
        k
    }
}

impl Keys {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn name(&mut self, n: Name) -> u32 {
        if let Some(&i) = self.name_ids.get(&n) {
            return i;
        }
        let i = u32::try_from(self.names.len()).expect("name count");
        self.names.push(n.clone());
        self.name_ids.insert(n, i);
        i
    }

    fn level(&mut self, l: Level) -> u32 {
        if let Some(&i) = self.level_ids.get(&l) {
            return i;
        }
        let i = u32::try_from(self.levels.len()).expect("level count");
        self.levels.push(l);
        self.level_ids.insert(l, i);
        i
    }

    fn n(&self, i: u32) -> Result<u32> {
        self.name_of
            .get(i as usize)
            .copied()
            .ok_or_else(|| corrupt("keys: unknown name id"))
    }

    fn l(&self, i: u32) -> Result<u32> {
        self.level_of
            .get(i as usize)
            .copied()
            .ok_or_else(|| corrupt("keys: unknown level id"))
    }

    fn e(&self, i: u32) -> Result<u32> {
        self.expr_of
            .get(i as usize)
            .copied()
            .ok_or_else(|| corrupt("keys: unknown expression id"))
    }

    fn dotted(&self, n: u32) -> String {
        let (pre, last) = match &self.names[n as usize] {
            Name::Anon => return String::new(),
            Name::Str(p, s) => (*p, s.to_string()),
            Name::Num(p, i) => (*p, i.to_string()),
        };
        match &self.names[pre as usize] {
            Name::Anon => last,
            _ => format!("{}.{last}", self.dotted(pre)),
        }
    }

    fn push_expr(&mut self, x: Expr) {
        let i = u32::try_from(self.exprs.len()).expect("expression count");
        self.exprs.push(x);
        self.expr_of.push(i);
    }

    fn take(&mut self, r: &Record<'_>) -> Result<()> {
        match r {
            Record::Meta(_) | Record::End(_) => {}
            Record::NameStr { pre, str } => {
                let n = Name::Str(self.n(*pre)?, str.as_ref().into());
                let i = self.name(n);
                self.name_of.push(i);
            }
            Record::NameNum { pre, i } => {
                let n = Name::Num(self.n(*pre)?, *i);
                let i = self.name(n);
                self.name_of.push(i);
            }
            Record::Succ(a) => self.add_level(Level::Succ(self.l(*a)?)),
            Record::Max(a, b) => self.add_level(Level::Max(self.l(*a)?, self.l(*b)?)),
            Record::IMax(a, b) => self.add_level(Level::IMax(self.l(*a)?, self.l(*b)?)),
            Record::Param(n) => self.add_level(Level::Param(self.n(*n)?)),
            Record::BVar(i) => self.push_expr(Expr::Var(*i)),
            Record::Sort(l) => self.push_expr(Expr::Sort(self.l(*l)?)),
            Record::Const { name, us } => {
                let us = us.iter().map(|&u| self.l(u)).collect::<Result<_>>()?;
                self.push_expr(Expr::Const(self.n(*name)?, us));
            }
            Record::App { fun, arg } => self.push_expr(Expr::App(self.e(*fun)?, self.e(*arg)?)),
            Record::Lam(b) => self.push_expr(Expr::Lam(self.e(b.ty)?, self.e(b.body)?)),
            Record::Pi(b) => self.push_expr(Expr::Pi(self.e(b.ty)?, self.e(b.body)?)),
            Record::Let {
                ty,
                value,
                body,
                nondep,
                ..
            } => self.push_expr(Expr::Let(
                self.e(*ty)?,
                self.e(*value)?,
                self.e(*body)?,
                *nondep,
            )),
            Record::Nat(d) => self.push_expr(Expr::Nat(nat_le(d)?.into())),
            Record::Str(s) => self.push_expr(Expr::Str(s.as_ref().into())),
            Record::Proj {
                type_name,
                idx,
                struct_,
            } => self.push_expr(Expr::Proj(self.n(*type_name)?, *idx, self.e(*struct_)?)),
            Record::MData(x) => {
                let x = self.e(*x)?;
                self.expr_of.push(x);
            }
            Record::Decl(d) => self.unit(d)?,
        }
        Ok(())
    }

    /// Every id the declaration refers to is in range, so encoding can index freely.
    fn check(&self, d: &Decl) -> Result<()> {
        let ok = std::cell::Cell::new(true);
        Record::Decl(d.clone()).map_ids(&|t, i| {
            let n = match t {
                Table::Names => self.name_of.len(),
                Table::Levels => self.level_of.len(),
                Table::Exprs => self.expr_of.len(),
            };
            ok.set(ok.get() && (i as usize) < n);
            i
        });
        if ok.get() {
            Ok(())
        } else {
            Err(corrupt("keys: declaration refers to an unknown id"))
        }
    }

    fn add_level(&mut self, l: Level) {
        let i = self.level(l);
        self.level_of.push(i);
    }

    fn unit(&mut self, d: &Decl) -> Result<()> {
        let members: Vec<&Head> = match d {
            Decl::Axiom { head, .. }
            | Decl::Def { head, .. }
            | Decl::Thm { head, .. }
            | Decl::Opaque { head, .. }
            | Decl::Quot { head, .. } => vec![head],
            Decl::Inductive { types, ctors, recs } => types
                .iter()
                .map(|t| &t.head)
                .chain(ctors.iter().map(|c| &c.head))
                .chain(recs.iter().map(|r| &r.head))
                .collect(),
        };
        let names = members
            .iter()
            .map(|h| self.n(h.name))
            .collect::<Result<Vec<_>>>()?;
        self.check(d)?;
        for h in &members {
            for &p in &h.level_params {
                let p = self.name_of[p as usize];
                self.level(Level::Param(p));
            }
        }
        let key = Enc::new(self, &names).unit(d);
        for (offset, &n) in (0..).zip(&names) {
            if self.decls.insert(n, (key, offset)).is_some() {
                return Err(corrupt(format!(
                    "keys: duplicate declaration {}",
                    self.dotted(n)
                )));
            }
            self.out.push(Keyed {
                name: self.dotted(n),
                key,
                offset,
            });
        }
        Ok(())
    }
}

impl Sink for &mut Keys {
    type Output = ();

    fn record(&mut self, _: Option<u32>, r: &Record<'_>) -> Result<()> {
        self.take(r)
    }

    fn finish(self) -> Result<()> {
        Ok(())
    }
}

impl Keys {
    /// Every declaration seen so far with its key, in export order.
    #[must_use]
    pub fn into_keys(self) -> Vec<Keyed> {
        self.out
    }
}

/// Little-endian bytes of a decimal numeral, `[0]` for zero, as `BigUint::to_bytes_le`.
fn nat_le(digits: &str) -> Result<Vec<u8>> {
    let mut v = vec![0u8];
    for c in digits.bytes() {
        if !c.is_ascii_digit() {
            return Err(corrupt("keys: invalid natural literal"));
        }
        let mut carry = u32::from(c - b'0');
        for b in &mut v {
            let x = u32::from(*b) * 10 + carry;
            *b = x.to_le_bytes()[0];
            carry = x >> 8;
        }
        while carry > 0 {
            v.push(carry.to_le_bytes()[0]);
            carry >>= 8;
        }
    }
    while v.len() > 1 && v.last() == Some(&0) {
        v.pop();
    }
    Ok(v)
}

/// The encoding of one unit. `None` stands for a unit without a key.
struct Enc<'k> {
    k: &'k Keys,
    own: &'k [u32],
    buf: Vec<u8>,
    names: FxHashMap<u32, u32>,
    levels: FxHashMap<u32, u32>,
    exprs: FxHashMap<u32, u32>,
    next: u32,
}

impl<'k> Enc<'k> {
    fn new(k: &'k Keys, own: &'k [u32]) -> Self {
        Self {
            k,
            own,
            buf: Vec::new(),
            names: FxHashMap::default(),
            levels: FxHashMap::default(),
            exprs: FxHashMap::default(),
            next: 0,
        }
    }

    fn u64(&mut self, mut x: u64) {
        while x >= 0x80 {
            self.buf.push(x.to_le_bytes()[0] | 0x80);
            x >>= 7;
        }
        self.buf.push(x.to_le_bytes()[0]);
    }

    fn bytes(&mut self, b: &[u8]) {
        self.u64(b.len() as u64);
        self.buf.extend_from_slice(b);
    }

    fn record(&mut self, t: u8, args: &[u64]) {
        self.buf.push(t);
        for &a in args {
            self.u64(a);
        }
    }

    fn name(&mut self, n: u32) -> u64 {
        if let Some(&i) = self.names.get(&n) {
            return i.into();
        }
        match &self.k.names[n as usize] {
            Name::Anon => self.buf.push(tag::ANON),
            Name::Str(p, s) => {
                let p = self.name(*p);
                self.record(tag::STR, &[p]);
                self.bytes(s.as_bytes());
            }
            Name::Num(p, i) => {
                let p = self.name(*p);
                self.record(tag::NUM, &[p]);
                self.buf.extend_from_slice(&i.to_le_bytes());
            }
        }
        let i = u32::try_from(self.names.len()).expect("name count");
        self.names.insert(n, i);
        i.into()
    }

    fn level(&mut self, l: u32) -> u64 {
        if let Some(&i) = self.levels.get(&l) {
            return i.into();
        }
        match self.k.levels[l as usize] {
            Level::Zero => self.record(tag::ZERO, &[]),
            Level::Succ(x) => {
                let x = self.level(x);
                self.record(tag::SUCC, &[x]);
            }
            Level::Max(x, y) => {
                let [x, y] = [self.level(x), self.level(y)];
                self.record(tag::MAX, &[x, y]);
            }
            Level::IMax(x, y) => {
                let [x, y] = [self.level(x), self.level(y)];
                self.record(tag::IMAX, &[x, y]);
            }
            Level::Param(n) => {
                let n = self.name(n);
                self.record(tag::PARAM, &[n]);
            }
        }
        let i = u32::try_from(self.levels.len()).expect("level count");
        self.levels.insert(l, i);
        i.into()
    }

    fn konst(&mut self, n: u32) -> Option<()> {
        if let Some(off) = self.own.iter().position(|&o| o == n) {
            self.record(tag::OWN, &[off as u64]);
        } else {
            let &(key, off) = self.k.decls.get(&n)?;
            self.buf.push(tag::DEP);
            self.buf.extend_from_slice(&key?);
            self.u64(off.into());
        }
        Some(())
    }

    fn konsts(&mut self, ns: &[u32]) -> Option<()> {
        self.u64(ns.len() as u64);
        ns.iter()
            .try_for_each(|&n| self.konst(self.k.name_of[n as usize]))
    }

    fn next(&mut self) -> u64 {
        self.next += 1;
        (self.next - 1).into()
    }

    fn expr(&mut self, e: u32) -> Option<u64> {
        let k = self.k;
        if let Expr::Var(i) = k.exprs[e as usize] {
            self.record(tag::VAR, &[i]);
            return Some(self.next());
        }
        if let Some(&i) = self.exprs.get(&e) {
            return Some(i.into());
        }
        match &k.exprs[e as usize] {
            Expr::Var(_) => unreachable!(),
            Expr::Sort(l) => {
                let l = self.level(*l);
                self.record(tag::SORT, &[l]);
            }
            Expr::Const(n, us) => {
                let ls: Vec<u64> = us.iter().map(|&u| self.level(u)).collect();
                self.record(tag::CONST, &[ls.len() as u64]);
                for &l in &ls {
                    self.u64(l);
                }
                self.konst(*n)?;
            }
            Expr::App(f, a) => {
                let [f, a] = [self.expr(*f)?, self.expr(*a)?];
                self.record(tag::APP, &[f, a]);
            }
            Expr::Lam(t, b) | Expr::Pi(t, b) => {
                let tg = if matches!(k.exprs[e as usize], Expr::Lam(..)) {
                    tag::LAM
                } else {
                    tag::PI
                };
                let [t, b] = [self.expr(*t)?, self.expr(*b)?];
                self.record(tg, &[t, b]);
            }
            Expr::Let(t, v, b, nondep) => {
                let t = self.expr(*t)?;
                let v = self.expr(*v)?;
                let b = self.expr(*b)?;
                self.record(tag::LET, &[t, v, b, u64::from(*nondep)]);
            }
            Expr::Proj(n, idx, x) => {
                let x = self.expr(*x)?;
                self.record(tag::PROJ, &[*idx, x]);
                self.konst(*n)?;
            }
            Expr::Nat(b) => {
                self.buf.push(tag::NAT);
                self.bytes(b);
            }
            Expr::Str(s) => {
                self.buf.push(tag::STRLIT);
                self.bytes(s.as_bytes());
            }
        }
        let i = self.next;
        self.next += 1;
        self.exprs.insert(e, i);
        Some(i.into())
    }

    fn info(&mut self, t: u8, h: &Head) -> Option<()> {
        let k = self.k;
        let n = self.name(k.name_of[h.name as usize]);
        let us: Vec<u64> = h
            .level_params
            .iter()
            .map(|&p| {
                let p = k.name_of[p as usize];
                self.level(k.level_ids[&Level::Param(p)])
            })
            .collect();
        let ty = self.expr(k.expr_of[h.ty as usize])?;
        self.record(t, &[n, ty, us.len() as u64]);
        for &u in &us {
            self.u64(u);
        }
        Some(())
    }

    fn value(&mut self, t: u8, h: &Head, v: u32) -> Option<()> {
        let v = self.expr(self.k.expr_of[v as usize])?;
        self.info(t, h)?;
        self.u64(v);
        Some(())
    }

    fn unit(mut self, d: &Decl) -> Option<Key> {
        self.encode(d)?;
        Some(*blake3::hash(&self.buf).as_bytes())
    }

    fn encode(&mut self, d: &Decl) -> Option<()> {
        match d {
            Decl::Axiom {
                head, is_unsafe, ..
            } => {
                if *is_unsafe {
                    return None;
                }
                self.info(tag::AXIOM, head)
            }
            Decl::Quot { head, .. } => self.info(tag::QUOT, head),
            Decl::Thm { head, value, .. } => self.value(tag::THM, head, *value),
            Decl::Opaque {
                head,
                value,
                is_unsafe,
                ..
            } => {
                if *is_unsafe {
                    return None;
                }
                self.value(tag::OPAQUE, head, *value)
            }
            Decl::Def {
                head,
                value,
                hints,
                safety,
                ..
            } => {
                if *safety != Safety::Safe {
                    return None;
                }
                self.value(tag::DEF, head, *value)?;
                let h = match hints {
                    Hints::Opaque => 0,
                    Hints::Abbrev => 1,
                    Hints::Regular(k) => u64::from(*k) + 2,
                };
                self.buf.extend_from_slice(&h.to_le_bytes());
                Some(())
            }
            Decl::Inductive { types, ctors, recs } => {
                let unsafe_ = types.iter().any(|t| t.is_unsafe)
                    || ctors.iter().any(|c| c.is_unsafe)
                    || recs.iter().any(|r| r.is_unsafe);
                if unsafe_ {
                    return None;
                }
                for t in types {
                    self.info(tag::IND, &t.head)?;
                    self.record(
                        tag::IND,
                        &[
                            u64::from(t.is_rec),
                            t.num_nested,
                            u64::from(t.is_reflexive),
                            t.num_params,
                            t.num_indices,
                        ],
                    );
                    self.konsts(&t.all)?;
                    self.konsts(&t.ctors)?;
                }
                for c in ctors {
                    self.info(tag::CTOR, &c.head)?;
                    self.record(tag::CTOR, &[c.cidx, c.num_params, c.num_fields]);
                    self.konst(self.k.name_of[c.induct as usize])?;
                }
                for r in recs {
                    self.info(tag::REC, &r.head)?;
                    self.record(
                        tag::REC,
                        &[
                            r.num_params,
                            r.num_indices,
                            r.num_motives,
                            r.num_minors,
                            u64::from(r.k),
                            r.rules.len() as u64,
                        ],
                    );
                    self.konsts(&r.all)?;
                    for rule in &r.rules {
                        let rhs = self.expr(self.k.expr_of[rule.rhs as usize])?;
                        self.record(tag::REC, &[rule.nfields, rhs]);
                        self.konst(self.k.name_of[rule.ctor as usize])?;
                    }
                }
                Some(())
            }
        }
    }
}
