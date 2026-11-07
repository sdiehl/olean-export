//! Compare two exports up to id numbering, record order and binders.
//!
//! lean4export shares subterms by Lean's `BEq`, which ignores binders, so where two
//! alpha-equivalent terms meet it may write either's binders. Both streams are hash-consed
//! into one table, so equal terms get equal ids on either side and a declaration compares
//! by `==` in time linear in its DAG, never its tree.

use crate::{
    error::Result,
    record::{Decl, Head, IndCtor, IndRec, IndRule, IndType, Record, Sink, Table},
};
use hashbrown::{hash_table::Entry, HashTable};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::hash::BuildHasher;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Key {
    Anon,
    Zero,
    NameStr(u32, Box<str>),
    NameNum(u32, u64),
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
    BVar(u64),
    Sort(u32),
    Const(u32, Box<[u32]>),
    App(u32, u32),
    Lam(u32, u32),
    Pi(u32, u32),
    Let(u32, u32, u32, bool),
    Nat(Box<str>),
    Str(Box<str>),
    Proj(u32, u64, u32),
    MData(u32),
}

#[derive(Debug, Default)]
struct Canon {
    nodes: Vec<Key>,
    index: HashTable<u32>,
}

impl Canon {
    fn intern(&mut self, k: Key) -> u32 {
        let h = FxBuildHasher.hash_one(&k);
        let nodes = &mut self.nodes;
        match self.index.entry(
            h,
            |&i| nodes[i as usize] == k,
            |&i| FxBuildHasher.hash_one(&nodes[i as usize]),
        ) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let i = u32::try_from(nodes.len()).expect("table overflow");
                nodes.push(k);
                e.insert(i);
                i
            }
        }
    }

    fn name(&self, n: u32) -> String {
        let join = |p: u32, s: &str| match self.nodes[p as usize] {
            Key::Anon => s.to_string(),
            _ => format!("{}.{s}", self.name(p)),
        };
        match &self.nodes[n as usize] {
            Key::NameStr(p, s) => join(*p, s),
            Key::NameNum(p, i) => join(*p, &i.to_string()),
            _ => String::new(),
        }
    }
}

/// One stream's ids mapped into the shared table, and its declarations by first name.
struct Side<'c> {
    canon: &'c mut Canon,
    names: Vec<u32>,
    levels: Vec<u32>,
    exprs: Vec<u32>,
    decls: FxHashMap<u32, Decl>,
    dups: Vec<u32>,
    count: usize,
}

impl<'c> Side<'c> {
    fn new(canon: &'c mut Canon) -> Self {
        let names = vec![canon.intern(Key::Anon)];
        let levels = vec![canon.intern(Key::Zero)];
        Self {
            canon,
            names,
            levels,
            exprs: Vec::new(),
            decls: FxHashMap::default(),
            dups: Vec::new(),
            count: 0,
        }
    }

    fn n(&self, i: u32) -> u32 {
        self.names[i as usize]
    }

    fn ns(&self, is: &[u32]) -> Vec<u32> {
        is.iter().map(|&i| self.n(i)).collect()
    }

    fn l(&self, i: u32) -> u32 {
        self.levels[i as usize]
    }

    fn e(&self, i: u32) -> u32 {
        self.exprs[i as usize]
    }

    fn head(&self, h: &Head) -> Head {
        Head {
            name: self.n(h.name),
            level_params: self.ns(&h.level_params),
            ty: self.e(h.ty),
        }
    }

    /// `d` over shared ids, with what lean4export may vary dropped: the `all` of axioms
    /// and opaques, which only some versions write, and the order of a block's recursors.
    fn decl(&self, d: &Decl) -> Decl {
        match d {
            Decl::Axiom {
                head, is_unsafe, ..
            } => Decl::Axiom {
                head: self.head(head),
                is_unsafe: *is_unsafe,
                all: None,
            },
            Decl::Def {
                head,
                value,
                hints,
                safety,
                all,
            } => Decl::Def {
                head: self.head(head),
                value: self.e(*value),
                hints: *hints,
                safety: *safety,
                all: self.ns(all),
            },
            Decl::Thm { head, value, all } => Decl::Thm {
                head: self.head(head),
                value: self.e(*value),
                all: self.ns(all),
            },
            Decl::Opaque {
                head,
                value,
                is_unsafe,
                ..
            } => Decl::Opaque {
                head: self.head(head),
                value: self.e(*value),
                is_unsafe: *is_unsafe,
                all: None,
            },
            Decl::Quot { head, kind } => Decl::Quot {
                head: self.head(head),
                kind: *kind,
            },
            Decl::Inductive { types, ctors, recs } => {
                let mut recs: Vec<IndRec> = recs
                    .iter()
                    .map(|r| IndRec {
                        head: self.head(&r.head),
                        all: self.ns(&r.all),
                        rules: r
                            .rules
                            .iter()
                            .map(|u| IndRule {
                                ctor: self.n(u.ctor),
                                nfields: u.nfields,
                                rhs: self.e(u.rhs),
                            })
                            .collect(),
                        ..r.clone()
                    })
                    .collect();
                recs.sort_by_key(|r| r.head.name);
                Decl::Inductive {
                    types: types
                        .iter()
                        .map(|t| IndType {
                            head: self.head(&t.head),
                            all: self.ns(&t.all),
                            ctors: self.ns(&t.ctors),
                            ..t.clone()
                        })
                        .collect(),
                    ctors: ctors
                        .iter()
                        .map(|c| IndCtor {
                            head: self.head(&c.head),
                            induct: self.n(c.induct),
                            ..c.clone()
                        })
                        .collect(),
                    recs,
                }
            }
        }
    }
}

impl Sink for &mut Side<'_> {
    type Output = ();

    fn record(&mut self, r: &Record<'_>) -> Result<()> {
        let key = match r {
            Record::Meta(_) | Record::End(_) => return Ok(()),
            Record::Decl(d) => {
                let d = self.decl(d);
                let k = first(&d);
                self.count += 1;
                if self.decls.insert(k, d).is_some() {
                    self.dups.push(k);
                }
                return Ok(());
            }
            Record::NameStr { pre, str } => Key::NameStr(self.n(*pre), (**str).into()),
            Record::NameNum { pre, i } => Key::NameNum(self.n(*pre), *i),
            Record::Succ(l) => Key::Succ(self.l(*l)),
            Record::Max(a, b) => Key::Max(self.l(*a), self.l(*b)),
            Record::IMax(a, b) => Key::IMax(self.l(*a), self.l(*b)),
            Record::Param(n) => Key::Param(self.n(*n)),
            Record::BVar(i) => Key::BVar(*i),
            Record::Sort(l) => Key::Sort(self.l(*l)),
            Record::Const { name, us } => {
                Key::Const(self.n(*name), us.iter().map(|&u| self.l(u)).collect())
            }
            Record::App { fun, arg } => Key::App(self.e(*fun), self.e(*arg)),
            Record::Lam(b) => Key::Lam(self.e(b.ty), self.e(b.body)),
            Record::Pi(b) => Key::Pi(self.e(b.ty), self.e(b.body)),
            Record::Let {
                ty,
                value,
                body,
                nondep,
                ..
            } => Key::Let(self.e(*ty), self.e(*value), self.e(*body), *nondep),
            Record::Nat(s) => Key::Nat((**s).into()),
            Record::Str(s) => Key::Str((**s).into()),
            Record::Proj {
                type_name,
                idx,
                struct_,
            } => Key::Proj(self.n(*type_name), *idx, self.e(*struct_)),
            Record::MData(e) => Key::MData(self.e(*e)),
        };
        let table = r.table();
        let id = self.canon.intern(key);
        match table {
            Some(Table::Names) => self.names.push(id),
            Some(Table::Levels) => self.levels.push(id),
            _ => self.exprs.push(id),
        }
        Ok(())
    }

    fn finish(self) -> Result<()> {
        Ok(())
    }
}

fn first(d: &Decl) -> u32 {
    match d {
        Decl::Axiom { head, .. }
        | Decl::Def { head, .. }
        | Decl::Thm { head, .. }
        | Decl::Opaque { head, .. }
        | Decl::Quot { head, .. } => head.name,
        Decl::Inductive { types, .. } => types.first().map_or(0, |t| t.head.name),
    }
}

/// Which part of two declarations under one name first differs.
fn what(a: &Decl, b: &Decl) -> &'static str {
    let parts = |d: &Decl| match d {
        Decl::Axiom { head, .. } | Decl::Quot { head, .. } => Some((head.clone(), None)),
        Decl::Def { head, value, .. }
        | Decl::Thm { head, value, .. }
        | Decl::Opaque { head, value, .. } => Some((head.clone(), Some(*value))),
        Decl::Inductive { .. } => None,
    };
    if std::mem::discriminant(a) != std::mem::discriminant(b) {
        return "kind";
    }
    match (parts(a), parts(b)) {
        (Some((x, _)), Some((y, _))) if x.level_params != y.level_params => "level params",
        (Some((x, _)), Some((y, _))) if x.ty != y.ty => "type",
        (Some((_, v)), Some((_, w))) if v != w => "value",
        (None, None) => "inductive block",
        _ => "attributes",
    }
}

/// How two exports differ, every list sorted by name.
#[derive(Debug, Default)]
pub struct Diff {
    pub decls: (usize, usize),
    pub only_a: Vec<String>,
    pub only_b: Vec<String>,
    pub differ: Vec<(String, &'static str)>,
    pub dups: (Vec<String>, Vec<String>),
}

impl Diff {
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.only_a.is_empty()
            && self.only_b.is_empty()
            && self.differ.is_empty()
            && self.dups.0.is_empty()
            && self.dups.1.is_empty()
    }
}

/// Compare two exports, each NDJSON or blean.
pub fn compare(a: &[u8], b: &[u8]) -> Result<Diff> {
    fn load(bytes: &[u8], side: &mut Side<'_>) -> Result<()> {
        if crate::blean::sniff(bytes) {
            crate::blean::read(bytes, side)
        } else {
            crate::ndjson::read(bytes, side)
        }
    }
    let mut canon = Canon::default();
    let (da, ca, pa) = {
        let mut s = Side::new(&mut canon);
        load(a, &mut s)?;
        (s.decls, s.count, s.dups)
    };
    let (db, cb, pb) = {
        let mut s = Side::new(&mut canon);
        load(b, &mut s)?;
        (s.decls, s.count, s.dups)
    };
    let names = |ks: &mut dyn Iterator<Item = u32>| {
        let mut v: Vec<String> = ks.map(|k| canon.name(k)).collect();
        v.sort_unstable();
        v
    };
    let mut differ: Vec<_> = da
        .iter()
        .filter_map(|(k, x)| {
            let y = db.get(k)?;
            (x != y).then(|| (canon.name(*k), what(x, y)))
        })
        .collect();
    differ.sort_unstable();
    Ok(Diff {
        decls: (ca, cb),
        only_a: names(&mut da.keys().copied().filter(|k| !db.contains_key(k))),
        only_b: names(&mut db.keys().copied().filter(|k| !da.contains_key(k))),
        differ,
        dups: (names(&mut pa.into_iter()), names(&mut pb.into_iter())),
    })
}
