use crate::olean::{is_scalar, small_nat, Header, Image};
use hashbrown::{hash_table::Entry, HashTable};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use std::{
    hash::{BuildHasher, Hash},
    io,
    path::{Path, PathBuf},
};

pub type NameId = u32;
pub type LevelId = u32;
pub type ExprId = u32;

pub const ANON: NameId = 0;
pub const ZERO: LevelId = 0;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Name {
    Anon,
    Str(NameId, Box<str>),
    Num(NameId, u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Binder {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// Equality and hashing ignore binder names and annotations, matching Lean's `BEq Expr`,
/// so terms that differ only there share one id, as they do in lean4export.
#[derive(Debug, Clone)]
pub enum Expr {
    BVar(u64),
    Sort(LevelId),
    Const(NameId, Box<[LevelId]>),
    App(ExprId, ExprId),
    Lam(NameId, ExprId, ExprId, Binder),
    Pi(NameId, ExprId, ExprId, Binder),
    Let(NameId, ExprId, ExprId, ExprId),
    Nat(Box<str>),
    Str(Box<str>),
    Proj(NameId, u64, ExprId),
}

impl Expr {
    fn key(&self) -> (u8, u64, u64, u64, Option<&str>, Option<&[LevelId]>) {
        match self {
            Self::BVar(i) => (0, *i, 0, 0, None, None),
            Self::Sort(l) => (1, (*l).into(), 0, 0, None, None),
            Self::Const(n, us) => (2, (*n).into(), 0, 0, None, Some(us)),
            Self::App(f, a) => (3, (*f).into(), (*a).into(), 0, None, None),
            Self::Lam(_, t, b, _) => (4, (*t).into(), (*b).into(), 0, None, None),
            Self::Pi(_, t, b, _) => (5, (*t).into(), (*b).into(), 0, None, None),
            Self::Let(_, t, v, b) => (6, (*t).into(), (*v).into(), (*b).into(), None, None),
            Self::Nat(v) => (7, 0, 0, 0, Some(v), None),
            Self::Str(v) => (8, 0, 0, 0, Some(v), None),
            Self::Proj(n, i, x) => (9, (*n).into(), *i, (*x).into(), None, None),
        }
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl Eq for Expr {}

impl Hash for Expr {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.key().hash(h);
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Debug, Clone, Copy)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

#[derive(Debug)]
pub struct Rule {
    pub ctor: NameId,
    pub nfields: u64,
    pub rhs: ExprId,
}

#[derive(Debug)]
pub enum Kind {
    Axiom,
    Defn {
        value: ExprId,
        hints: Hints,
        all: Vec<NameId>,
    },
    Thm {
        value: ExprId,
        all: Vec<NameId>,
    },
    Opaque {
        value: ExprId,
        all: Vec<NameId>,
    },
    Quot(QuotKind),
    Induct {
        num_params: u64,
        num_indices: u64,
        all: Vec<NameId>,
        ctors: Vec<NameId>,
        num_nested: u64,
        is_rec: bool,
        is_reflexive: bool,
    },
    Ctor {
        induct: NameId,
        cidx: u64,
        num_params: u64,
        num_fields: u64,
    },
    Rec {
        all: Vec<NameId>,
        num_params: u64,
        num_indices: u64,
        num_motives: u64,
        num_minors: u64,
        rules: Vec<Rule>,
        k: bool,
    },
}

/// A declaration the kernel would accept. Unsafe and partial ones are dropped at load time.
#[derive(Debug)]
pub struct Const {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
    pub kind: Kind,
}

/// A hash-consing arena: structurally equal nodes get the same id, and ids are dense.
#[derive(Debug)]
pub struct Table<T> {
    pub nodes: Vec<T>,
    index: HashTable<u32>,
}

impl<T: Hash + Eq> Table<T> {
    const fn new() -> Self {
        Self {
            nodes: Vec::new(),
            index: HashTable::new(),
        }
    }

    pub fn intern(&mut self, t: T) -> u32 {
        let h = FxBuildHasher.hash_one(&t);
        let nodes = &self.nodes;
        match self.index.entry(
            h,
            |&i| nodes[i as usize] == t,
            |&i| FxBuildHasher.hash_one(&nodes[i as usize]),
        ) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let id = u32::try_from(self.nodes.len()).expect("table overflow");
                e.insert(id);
                self.nodes.push(t);
                id
            }
        }
    }

    pub fn get(&self, t: &T) -> Option<u32> {
        let h = FxBuildHasher.hash_one(t);
        self.index
            .find(h, |&i| &self.nodes[i as usize] == t)
            .copied()
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.nodes.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

impl<T> std::ops::Index<u32> for Table<T> {
    type Output = T;
    fn index(&self, i: u32) -> &T {
        &self.nodes[i as usize]
    }
}

/// Every constant reachable from a set of root modules, in import order.
#[derive(Debug)]
pub struct Env {
    pub names: Table<Name>,
    pub levels: Table<Level>,
    pub exprs: Table<Expr>,
    pub consts: FxHashMap<NameId, Const>,
    pub order: Vec<NameId>,
    pub recursors: FxHashMap<NameId, Vec<NameId>>,
    pub modules: Vec<String>,
    pub header: Header,
    pub skipped: usize,
}

impl Env {
    fn new() -> Self {
        let mut env = Self {
            names: Table::new(),
            levels: Table::new(),
            exprs: Table::new(),
            consts: FxHashMap::default(),
            order: Vec::new(),
            recursors: FxHashMap::default(),
            modules: Vec::new(),
            header: Header::default(),
            skipped: 0,
        };
        env.names.intern(Name::Anon);
        env.levels.intern(Level::Zero);
        env
    }

    /// Load `roots` and their transitive imports, resolving modules against `search`.
    pub fn load(search: &[PathBuf], roots: &[&str]) -> io::Result<Self> {
        Self::load_with(search, roots, &mut |_| {})
    }

    /// Like [`Env::load`], calling `progress` after each module is decoded.
    pub fn load_with(
        search: &[PathBuf],
        roots: &[&str],
        progress: &mut dyn FnMut(&Self),
    ) -> io::Result<Self> {
        let mut env = Self::new();
        let mut seen = FxHashSet::default();
        for root in roots {
            env.visit(search, root, &mut seen, progress)?;
        }
        Ok(env)
    }

    /// The constants `lean4export` exports when given no explicit names.
    pub fn roots(&self) -> impl Iterator<Item = NameId> + '_ {
        self.order.iter().copied().filter(|&c| !self.is_internal(c))
    }

    fn visit(
        &mut self,
        search: &[PathBuf],
        module: &str,
        seen: &mut FxHashSet<String>,
        progress: &mut dyn FnMut(&Self),
    ) -> io::Result<()> {
        if !seen.insert(module.to_owned()) {
            return Ok(());
        }
        let path = resolve(search, module)?;
        let mut img = Image::open(&path)?;
        let data = img.root;
        let imports: Vec<String> = img
            .array(img.field(data, 0))
            .map(|i| img.str_name(img.field(i, 0)))
            .collect();
        for import in &imports {
            self.visit(search, import, seen, progress)?;
        }
        if img.scalar_u8(data, 0) == 1 {
            img.push_part(&path.with_extension("olean.server"))?;
            img.push_part(&path.with_extension("olean.private"))?;
        }
        self.header = img.header.clone();
        let mut dec = Decoder {
            img: &img,
            env: self,
            names: FxHashMap::default(),
            levels: FxHashMap::default(),
            exprs: FxHashMap::default(),
        };
        for c in img.array(img.field(img.root, 2)) {
            dec.constant(c);
        }
        self.modules.push(module.to_owned());
        progress(self);
        Ok(())
    }

    /// Look up a dotted name such as `Nat.add` without interning it.
    #[must_use]
    pub fn find_name(&self, dotted: &str) -> Option<NameId> {
        dotted.split('.').try_fold(ANON, |pre, s| {
            let n = s
                .parse()
                .map_or_else(|_| Name::Str(pre, s.into()), |i| Name::Num(pre, i));
            self.names.get(&n)
        })
    }

    #[must_use]
    pub fn display(&self, n: NameId) -> String {
        match &self.names[n] {
            Name::Anon => String::new(),
            Name::Str(ANON, s) => s.to_string(),
            Name::Num(ANON, i) => i.to_string(),
            Name::Str(p, s) => format!("{}.{s}", self.display(*p)),
            Name::Num(p, i) => format!("{}.{i}", self.display(*p)),
        }
    }

    #[must_use]
    pub fn is_internal(&self, n: NameId) -> bool {
        match &self.names[n] {
            Name::Anon => false,
            Name::Str(p, s) => s.starts_with('_') || self.is_internal(*p),
            Name::Num(p, _) => self.is_internal(*p),
        }
    }
}

fn resolve(search: &[PathBuf], module: &str) -> io::Result<PathBuf> {
    let rel: PathBuf = module.split('.').collect();
    search
        .iter()
        .map(|dir| dir.join(&rel).with_extension("olean"))
        .find(|p| p.is_file())
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!("module {module} not found on LEAN_PATH"),
            )
        })
}

impl Image {
    fn str_name(&self, o: u64) -> String {
        let mut parts = Vec::new();
        let mut o = o;
        while !is_scalar(o) && self.tag(o) != 0 {
            parts.push(if self.tag(o) == 1 {
                self.str(self.field(o, 1)).to_owned()
            } else {
                self.nat_decimal(self.field(o, 1))
            });
            o = self.field(o, 0);
        }
        parts.reverse();
        parts.join(".")
    }
}

/// Translates one module's objects into the shared tables, memoized by address since the
/// compactor already maximally shares structurally equal objects within a module.
struct Decoder<'a> {
    img: &'a Image,
    env: &'a mut Env,
    names: FxHashMap<u64, NameId>,
    levels: FxHashMap<u64, LevelId>,
    exprs: FxHashMap<u64, ExprId>,
}

impl Decoder<'_> {
    fn name(&mut self, o: u64) -> NameId {
        if is_scalar(o) || self.img.tag(o) == 0 {
            return ANON;
        }
        if let Some(&id) = self.names.get(&o) {
            return id;
        }
        let pre = self.name(self.img.field(o, 0));
        let arg = self.img.field(o, 1);
        let n = match self.img.tag(o) {
            1 => Name::Str(pre, self.img.str(arg).into()),
            _ => Name::Num(pre, small_nat(arg)),
        };
        let id = self.env.names.intern(n);
        self.names.insert(o, id);
        id
    }

    fn names(&mut self, o: u64) -> Vec<NameId> {
        self.img.list(o).into_iter().map(|n| self.name(n)).collect()
    }

    fn level(&mut self, o: u64) -> LevelId {
        if is_scalar(o) || self.img.tag(o) == 0 {
            return ZERO;
        }
        if let Some(&id) = self.levels.get(&o) {
            return id;
        }
        let img = self.img;
        let l = match img.tag(o) {
            1 => Level::Succ(self.level(img.field(o, 0))),
            2 => Level::Max(self.level(img.field(o, 0)), self.level(img.field(o, 1))),
            3 => Level::IMax(self.level(img.field(o, 0)), self.level(img.field(o, 1))),
            4 => Level::Param(self.name(img.field(o, 0))),
            t => panic!("unexpected level tag {t}"),
        };
        let id = self.env.levels.intern(l);
        self.levels.insert(o, id);
        id
    }

    fn expr(&mut self, o: u64) -> ExprId {
        if let Some(&id) = self.exprs.get(&o) {
            return id;
        }
        let img = self.img;
        let f = |i| img.field(o, i);
        let binder = |img: &Image| match img.scalar_u8(o, 8) {
            0 => Binder::Default,
            1 => Binder::Implicit,
            2 => Binder::StrictImplicit,
            _ => Binder::InstImplicit,
        };
        let e = match img.tag(o) {
            0 => Expr::BVar(small_nat(f(0))),
            3 => Expr::Sort(self.level(f(0))),
            4 => {
                let us = img.list(f(1)).into_iter().map(|l| self.level(l)).collect();
                Expr::Const(self.name(f(0)), us)
            }
            5 => Expr::App(self.expr(f(0)), self.expr(f(1))),
            6 => Expr::Lam(
                self.name(f(0)),
                self.expr(f(1)),
                self.expr(f(2)),
                binder(img),
            ),
            7 => Expr::Pi(
                self.name(f(0)),
                self.expr(f(1)),
                self.expr(f(2)),
                binder(img),
            ),
            8 => Expr::Let(
                self.name(f(0)),
                self.expr(f(1)),
                self.expr(f(2)),
                self.expr(f(3)),
            ),
            9 => {
                let lit = f(0);
                if img.tag(lit) == 0 {
                    Expr::Nat(img.nat_decimal(img.field(lit, 0)).into())
                } else {
                    Expr::Str(img.str(img.field(lit, 0)).into())
                }
            }
            10 => {
                let id = self.expr(f(1));
                self.exprs.insert(o, id);
                return id;
            }
            11 => Expr::Proj(self.name(f(0)), small_nat(f(1)), self.expr(f(2))),
            t => panic!("unexpected expression tag {t} (free or meta variable in a declaration)"),
        };
        let id = self.env.exprs.intern(e);
        self.exprs.insert(o, id);
        id
    }

    fn constant(&mut self, info: u64) {
        let img = self.img;
        let tag = img.tag(info);
        let val = img.field(info, 0);
        let unsafe_flag = match tag {
            1 => img.scalar_u8(val, 0) != 1,
            0 | 3 | 6 => img.scalar_u8(val, 0) != 0,
            5 | 7 => img.scalar_u8(val, 1) != 0,
            _ => false,
        };
        if unsafe_flag {
            self.env.skipped += 1;
            return;
        }
        let f = |i| img.field(val, i);
        let cv = f(0);
        let name = self.name(img.field(cv, 0));
        let level_params = self.names(img.field(cv, 1));
        for &p in &level_params {
            self.env.levels.intern(Level::Param(p));
        }
        let ty = self.expr(img.field(cv, 2));
        let nat = |i| small_nat(f(i));
        let kind = match tag {
            0 => Kind::Axiom,
            1 => {
                let h = f(2);
                let hints = if is_scalar(h) {
                    if h >> 1 == 0 {
                        Hints::Opaque
                    } else {
                        Hints::Abbrev
                    }
                } else {
                    Hints::Regular(img.scalar_u32(h))
                };
                Kind::Defn {
                    value: self.expr(f(1)),
                    hints,
                    all: self.names(f(3)),
                }
            }
            2 => Kind::Thm {
                value: self.expr(f(1)),
                all: self.names(f(2)),
            },
            3 => Kind::Opaque {
                value: self.expr(f(1)),
                all: self.names(f(2)),
            },
            4 => Kind::Quot(match img.scalar_u8(val, 0) {
                0 => QuotKind::Type,
                1 => QuotKind::Ctor,
                2 => QuotKind::Lift,
                _ => QuotKind::Ind,
            }),
            5 => Kind::Induct {
                num_params: nat(1),
                num_indices: nat(2),
                all: self.names(f(3)),
                ctors: self.names(f(4)),
                num_nested: nat(5),
                is_rec: img.scalar_u8(val, 0) != 0,
                is_reflexive: img.scalar_u8(val, 2) != 0,
            },
            6 => Kind::Ctor {
                induct: self.name(f(1)),
                cidx: nat(2),
                num_params: nat(3),
                num_fields: nat(4),
            },
            7 => {
                let all = self.names(f(1));
                for &ind in &all {
                    self.env.recursors.entry(ind).or_default().push(name);
                }
                let rules = img
                    .list(f(6))
                    .into_iter()
                    .map(|r| Rule {
                        ctor: self.name(img.field(r, 0)),
                        nfields: small_nat(img.field(r, 1)),
                        rhs: self.expr(img.field(r, 2)),
                    })
                    .collect();
                Kind::Rec {
                    all,
                    num_params: nat(2),
                    num_indices: nat(3),
                    num_motives: nat(4),
                    num_minors: nat(5),
                    rules,
                    k: img.scalar_u8(val, 0) != 0,
                }
            }
            t => panic!("unexpected constant tag {t}"),
        };
        self.env.order.push(name);
        self.env.consts.insert(
            name,
            Const {
                name,
                level_params,
                ty,
                kind,
            },
        );
    }
}

#[must_use]
pub fn search_path() -> Vec<PathBuf> {
    let mut dirs: Vec<PathBuf> = std::env::var_os("LEAN_PATH")
        .map(|p| std::env::split_paths(&p).collect())
        .unwrap_or_default();
    if let Some(root) = std::env::var_os("LEAN_SYSROOT") {
        dirs.push(Path::new(&root).join("lib").join("lean"));
    }
    dirs
}
