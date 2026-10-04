use crate::olean::{is_scalar, small_nat, Header, Image};
use hashbrown::{hash_table::Entry, HashTable};
use rayon::prelude::*;
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

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::BVar(a), Self::BVar(b)) => a == b,
            (Self::Sort(a), Self::Sort(b)) => a == b,
            (Self::Const(n, us), Self::Const(m, vs)) => n == m && us == vs,
            (Self::App(f, a), Self::App(g, b)) => f == g && a == b,
            (Self::Lam(_, t, b, _), Self::Lam(_, u, c, _))
            | (Self::Pi(_, t, b, _), Self::Pi(_, u, c, _)) => t == u && b == c,
            (Self::Let(_, t, v, b), Self::Let(_, u, w, c)) => t == u && v == w && b == c,
            (Self::Nat(a), Self::Nat(b)) | (Self::Str(a), Self::Str(b)) => a == b,
            (Self::Proj(n, i, x), Self::Proj(m, j, y)) => n == m && i == j && x == y,
            _ => false,
        }
    }
}

impl Eq for Expr {}

impl Hash for Expr {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        let pack = |a: u32, b: u32| u64::from(a) << 32 | u64::from(b);
        match self {
            Self::BVar(i) => h.write_u64(*i),
            Self::Sort(l) => h.write_u32(*l),
            Self::Const(n, us) => {
                h.write_u32(*n);
                us.iter().for_each(|&u| h.write_u32(u));
            }
            Self::App(f, a) => h.write_u64(pack(*f, *a)),
            Self::Lam(_, t, b, _) | Self::Pi(_, t, b, _) => h.write_u64(pack(*t, *b)),
            Self::Let(_, t, v, b) => {
                h.write_u64(pack(*t, *v));
                h.write_u32(*b);
            }
            Self::Nat(v) | Self::Str(v) => h.write(v.as_bytes()),
            Self::Proj(n, i, x) => {
                h.write_u64(pack(*n, *x));
                h.write_u64(*i);
            }
        }
        h.write_u8(self.tag());
    }
}

impl Expr {
    const fn tag(&self) -> u8 {
        match self {
            Self::BVar(_) => 0,
            Self::Sort(_) => 1,
            Self::Const(..) => 2,
            Self::App(..) => 3,
            Self::Lam(..) => 4,
            Self::Pi(..) => 5,
            Self::Let(..) => 6,
            Self::Nat(_) => 7,
            Self::Str(_) => 8,
            Self::Proj(..) => 9,
        }
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
    hashes: Vec<u64>,
    index: HashTable<u32>,
}

impl<T: Hash + Eq> Table<T> {
    const fn new() -> Self {
        Self {
            nodes: Vec::new(),
            hashes: Vec::new(),
            index: HashTable::new(),
        }
    }

    pub fn intern(&mut self, t: T) -> u32 {
        let h = FxBuildHasher.hash_one(&t);
        let (nodes, hashes) = (&self.nodes, &self.hashes);
        match self.index.entry(
            h,
            |&i| hashes[i as usize] == h && nodes[i as usize] == t,
            |&i| hashes[i as usize],
        ) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let id = u32::try_from(self.nodes.len()).expect("table overflow");
                e.insert(id);
                self.nodes.push(t);
                self.hashes.push(h);
                id
            }
        }
    }

    fn reserve(&mut self, n: usize) {
        let hashes = &self.hashes;
        self.index.reserve(n, |&i| hashes[i as usize]);
        self.nodes.reserve(n);
        self.hashes.reserve(n);
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
        let jobs = std::thread::available_parallelism().map_or(1, usize::from);
        Self::load_with(search, roots, jobs, &mut |_| {})
    }

    /// Like [`Env::load`] on `jobs` threads, calling `progress` after each module is merged.
    ///
    /// Modules decode in parallel into private tables, which are merged into `self` in import
    /// order, so the result is the same for any `jobs`.
    pub fn load_with(
        search: &[PathBuf],
        roots: &[&str],
        jobs: usize,
        progress: &mut (dyn FnMut(&Self) + Send),
    ) -> io::Result<Self> {
        let mut seen = FxHashSet::default();
        let mut found = Vec::new();
        for root in roots {
            discover(search, root, &mut seen, &mut found)?;
        }
        // Sizing the shared tables up front avoids rehashing them while they grow, which was
        // a quarter of merge time. Across Lean and Mathlib there is about one expression per
        // 64 bytes of olean and one name per 1200.
        let bytes: u64 = found
            .iter()
            .flat_map(|(_, p)| {
                ["olean", "olean.server", "olean.private"].map(|e| p.with_extension(e))
            })
            .filter_map(|p| std::fs::metadata(p).ok())
            .map(|m| m.len())
            .sum();
        let mut env = Self::new();
        let estimate = |per: u64| usize::try_from(bytes / per).unwrap_or(0);
        env.exprs.reserve(estimate(64));
        env.names.reserve(estimate(1200));
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(jobs.max(1))
            .stack_size(crate::STACK)
            .build()
            .map_err(io::Error::other)?;
        pool.install(|| {
            let mut found = found.into_iter();
            let mut ready = Vec::new();
            loop {
                let batch: Vec<_> = found.by_ref().take(jobs.max(1) * 8).collect();
                if batch.is_empty() && ready.is_empty() {
                    break;
                }
                let merging = std::mem::take(&mut ready);
                let ((), next) = rayon::join(
                    || {
                        for (module, local) in merging {
                            env.merge(local, module);
                            progress(&env);
                        }
                    },
                    || {
                        batch
                            .into_par_iter()
                            .map(|(module, path)| Ok((module, Self::decode(&path)?)))
                            .collect::<io::Result<Vec<_>>>()
                    },
                );
                ready = next?;
            }
            Ok::<_, io::Error>(())
        })?;
        Ok(env)
    }

    /// The constants `lean4export` exports when given no explicit names.
    pub fn roots(&self) -> impl Iterator<Item = NameId> + '_ {
        self.order.iter().copied().filter(|&c| !self.is_internal(c))
    }

    fn decode(path: &Path) -> io::Result<Self> {
        let mut img = Image::open(path)?;
        if img.scalar_u8(img.root, 0) == 1 {
            img.push_part(&path.with_extension("olean.server"))?;
            img.push_part(&path.with_extension("olean.private"))?;
        }
        let img = &img;
        let mut env = Self::new();
        env.header = img.header.clone();
        let mut dec = Decoder {
            img,
            env: &mut env,
            memo: vec![0; img.slots()],
        };
        for c in img.array(img.field(img.root, 2)) {
            dec.constant(c);
        }
        Ok(env)
    }

    /// Re-intern a module's private tables into `self`. Children always have smaller ids
    /// than their parents, so one forward pass over each table suffices.
    fn merge(&mut self, local: Self, module: String) {
        let mut nm = Vec::with_capacity(local.names.len());
        for n in local.names.nodes {
            nm.push(match n {
                Name::Anon => ANON,
                Name::Str(p, s) => self.names.intern(Name::Str(nm[p as usize], s)),
                Name::Num(p, i) => self.names.intern(Name::Num(nm[p as usize], i)),
            });
        }
        let n = |x: NameId| nm[x as usize];
        let ns = |v: Vec<NameId>| v.into_iter().map(n).collect::<Vec<_>>();
        let mut lm = Vec::with_capacity(local.levels.len());
        for l in local.levels.nodes {
            let l = match l {
                Level::Zero => Level::Zero,
                Level::Succ(a) => Level::Succ(lm[a as usize]),
                Level::Max(a, b) => Level::Max(lm[a as usize], lm[b as usize]),
                Level::IMax(a, b) => Level::IMax(lm[a as usize], lm[b as usize]),
                Level::Param(p) => Level::Param(n(p)),
            };
            lm.push(self.levels.intern(l));
        }
        let mut em: Vec<ExprId> = Vec::with_capacity(local.exprs.len());
        for e in local.exprs.nodes {
            let x = |i: ExprId| em[i as usize];
            let e = match e {
                Expr::BVar(i) => Expr::BVar(i),
                Expr::Sort(l) => Expr::Sort(lm[l as usize]),
                Expr::Const(c, us) => {
                    Expr::Const(n(c), us.iter().map(|&u| lm[u as usize]).collect())
                }
                Expr::App(f, a) => Expr::App(x(f), x(a)),
                Expr::Lam(b, t, v, bi) => Expr::Lam(n(b), x(t), x(v), bi),
                Expr::Pi(b, t, v, bi) => Expr::Pi(n(b), x(t), x(v), bi),
                Expr::Let(b, t, v, body) => Expr::Let(n(b), x(t), x(v), x(body)),
                lit @ (Expr::Nat(_) | Expr::Str(_)) => lit,
                Expr::Proj(s, i, v) => Expr::Proj(n(s), i, x(v)),
            };
            let id = self.exprs.intern(e);
            em.push(id);
        }
        let x = |i: ExprId| em[i as usize];
        let mut consts = local.consts;
        for c in local.order {
            let k = consts
                .remove(&c)
                .expect("every ordered constant was decoded");
            let kind = match k.kind {
                Kind::Defn { value, hints, all } => Kind::Defn {
                    value: x(value),
                    hints,
                    all: ns(all),
                },
                Kind::Thm { value, all } => Kind::Thm {
                    value: x(value),
                    all: ns(all),
                },
                Kind::Opaque { value, all } => Kind::Opaque {
                    value: x(value),
                    all: ns(all),
                },
                Kind::Induct {
                    num_params,
                    num_indices,
                    all,
                    ctors,
                    num_nested,
                    is_rec,
                    is_reflexive,
                } => Kind::Induct {
                    num_params,
                    num_indices,
                    all: ns(all),
                    ctors: ns(ctors),
                    num_nested,
                    is_rec,
                    is_reflexive,
                },
                Kind::Ctor {
                    induct,
                    cidx,
                    num_params,
                    num_fields,
                } => Kind::Ctor {
                    induct: n(induct),
                    cidx,
                    num_params,
                    num_fields,
                },
                Kind::Rec {
                    all,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rules,
                    k,
                } => Kind::Rec {
                    all: ns(all),
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rules: rules
                        .into_iter()
                        .map(|r| Rule {
                            ctor: n(r.ctor),
                            nfields: r.nfields,
                            rhs: x(r.rhs),
                        })
                        .collect(),
                    k,
                },
                other @ (Kind::Axiom | Kind::Quot(_)) => other,
            };
            let name = n(c);
            self.order.push(name);
            self.consts.insert(
                name,
                Const {
                    name,
                    level_params: ns(k.level_params),
                    ty: x(k.ty),
                    kind,
                },
            );
        }
        for (ind, recs) in local.recursors {
            self.recursors
                .entry(n(ind))
                .or_default()
                .extend(recs.into_iter().map(n));
        }
        self.skipped += local.skipped;
        self.header = local.header;
        self.modules.push(module);
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

/// Find `module` and its imports, appending them to `out` in import order.
fn discover(
    search: &[PathBuf],
    module: &str,
    seen: &mut FxHashSet<String>,
    out: &mut Vec<(String, PathBuf)>,
) -> io::Result<()> {
    if !seen.insert(module.to_owned()) {
        return Ok(());
    }
    let path = resolve(search, module)?;
    let img = Image::open(&path)?;
    let imports: Vec<String> = img
        .array(img.field(img.root, 0))
        .map(|i| img.str_name(img.field(i, 0)))
        .collect();
    drop(img);
    for import in &imports {
        discover(search, import, seen, out)?;
    }
    out.push((module.to_owned(), path));
    Ok(())
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
    /// Table id plus one for each decoded object, by slot. An object is only ever decoded as
    /// one of name, level or expression, so the kinds can share it.
    memo: Vec<u32>,
}

impl Decoder<'_> {
    fn seen(&self, o: u64) -> Option<u32> {
        self.memo[self.img.slot(o)].checked_sub(1)
    }

    fn remember(&mut self, o: u64, id: u32) -> u32 {
        let slot = self.img.slot(o);
        self.memo[slot] = id + 1;
        id
    }

    fn name(&mut self, o: u64) -> NameId {
        if is_scalar(o) || self.img.tag(o) == 0 {
            return ANON;
        }
        if let Some(id) = self.seen(o) {
            return id;
        }
        let pre = self.name(self.img.field(o, 0));
        let arg = self.img.field(o, 1);
        let n = match self.img.tag(o) {
            1 => Name::Str(pre, self.img.str(arg).into()),
            _ => Name::Num(pre, small_nat(arg)),
        };
        let id = self.env.names.intern(n);
        self.remember(o, id)
    }

    fn names(&mut self, o: u64) -> Vec<NameId> {
        self.img.list(o).into_iter().map(|n| self.name(n)).collect()
    }

    fn level(&mut self, o: u64) -> LevelId {
        if is_scalar(o) || self.img.tag(o) == 0 {
            return ZERO;
        }
        if let Some(id) = self.seen(o) {
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
        self.remember(o, id)
    }

    fn expr(&mut self, o: u64) -> ExprId {
        if let Some(id) = self.seen(o) {
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
                return self.remember(o, id);
            }
            11 => Expr::Proj(self.name(f(0)), small_nat(f(1)), self.expr(f(2))),
            t => panic!("unexpected expression tag {t} (free or meta variable in a declaration)"),
        };
        let id = self.env.exprs.intern(e);
        self.remember(o, id)
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
