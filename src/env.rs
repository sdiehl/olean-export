use crate::{
    error::{at, corrupt, Error, Result},
    olean::{is_scalar, small_nat, Header, Image},
};
use hashbrown::{hash_table::Entry, HashTable};
use parking_lot::{Mutex, MutexGuard};
use rayon::prelude::*;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use std::{
    fmt,
    hash::{BuildHasher, Hash},
    marker::PhantomData,
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicU64, AtomicUsize, Ordering::Relaxed},
        OnceLock,
    },
    time::SystemTime,
};

/// The id of a `T` in its table.
#[derive(PartialEq, Eq, Hash)]
pub struct Id<T>(u32, PhantomData<fn() -> T>);

impl<T> Id<T> {
    const fn new(i: u32) -> Self {
        Self(i, PhantomData)
    }

    /// The id as an index, for arrays sized by a table's `bound`.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Id<T> {}

impl<T> fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

pub type NameId = Id<Name>;
pub type LevelId = Id<Level>;
pub type ExprId = Id<Expr>;

pub const ANON: NameId = Id::new(0);
pub const ZERO: LevelId = Id::new(0);

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
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
            Self::Sort(l) => h.write_u32(l.0),
            Self::Const(n, us) => {
                h.write_u32(n.0);
                us.iter().for_each(|u| h.write_u32(u.0));
            }
            Self::App(f, a) => h.write_u64(pack(f.0, a.0)),
            Self::Lam(_, t, b, _) | Self::Pi(_, t, b, _) => h.write_u64(pack(t.0, b.0)),
            Self::Let(_, t, v, b) => {
                h.write_u64(pack(t.0, v.0));
                h.write_u32(b.0);
            }
            Self::Nat(v) | Self::Str(v) => h.write(v.as_bytes()),
            Self::Proj(n, i, x) => {
                h.write_u64(pack(n.0, x.0));
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
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
pub struct Defn {
    pub value: ExprId,
    pub hints: Hints,
    pub all: Vec<NameId>,
}

/// The value of a theorem or opaque constant.
#[derive(Debug)]
pub struct Body {
    pub value: ExprId,
    pub all: Vec<NameId>,
}

#[derive(Debug)]
pub struct Inductive {
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<NameId>,
    pub ctors: Vec<NameId>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_reflexive: bool,
}

#[derive(Debug)]
pub struct Ctor {
    pub induct: NameId,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
}

#[derive(Debug)]
pub struct Rec {
    pub all: Vec<NameId>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<Rule>,
    pub k: bool,
}

#[derive(Debug)]
pub enum Kind {
    Axiom,
    Defn(Defn),
    Thm(Body),
    Opaque(Body),
    Quot(QuotKind),
    Induct(Inductive),
    Ctor(Ctor),
    Rec(Rec),
}

/// A declaration the kernel would accept. Unsafe and partial ones are dropped at load time.
#[derive(Debug)]
pub struct Const {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
    pub kind: Kind,
}

const SHARDS: usize = 256;
const CHUNK: usize = 1 << 14;

#[derive(Debug)]
struct Shard<T> {
    nodes: Vec<T>,
    index: HashTable<u32>,
}

fn hash<T: Hash>(t: &T) -> u64 {
    FxBuildHasher.hash_one(t)
}

/// The shard of a hash. Fx hashes are weak in their middle bits, so mix them first.
const fn shard_of(h: u64) -> usize {
    (h.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 56) as usize % SHARDS
}

fn id(n: usize) -> u32 {
    u32::try_from(n).expect("table overflow")
}

/// A hash-consing arena split into locked shards so that every decoding thread can intern
/// into it at once.
#[derive(Debug)]
struct Shared<T>(Vec<Mutex<Shard<T>>>);

impl<T: Hash + Eq> Shared<T> {
    /// A table with room for about `n` nodes, whose id 0 is `zero`.
    fn new(zero: T, n: usize) -> Self {
        let mut shards: Vec<_> = (0..SHARDS)
            .map(|_| Shard {
                nodes: Vec::with_capacity(n / SHARDS),
                index: HashTable::with_capacity(n / SHARDS),
            })
            .collect();
        shards[0].index.insert_unique(hash(&zero), 0, |_| 0);
        shards[0].nodes.push(zero);
        Self(shards.into_iter().map(Mutex::new).collect())
    }

    fn intern(&self, t: T) -> Id<T> {
        let h = hash(&t);
        let k = shard_of(h);
        let mut g = self.0[k].lock();
        let s = &mut *g;
        let nodes = &mut s.nodes;
        let i = match s.index.entry(
            h,
            |&i| nodes[i as usize] == t,
            |&i| hash(&nodes[i as usize]),
        ) {
            Entry::Occupied(e) => *e.get() as usize,
            Entry::Vacant(e) => {
                e.insert(id(nodes.len()));
                nodes.push(t);
                nodes.len() - 1
            }
        };
        drop(g);
        Id::new(id(i * SHARDS + k))
    }

    fn freeze(self) -> Table<T> {
        Table(self.0.into_iter().map(Mutex::into_inner).collect())
    }
}

impl<T> Table<T> {
    fn thaw(self) -> Shared<T> {
        Shared(self.0.into_iter().map(Mutex::new).collect())
    }
}

/// A hash-consing arena: structurally equal nodes get the same id. Ids are interleaved
/// across shards, so they are nearly but not exactly dense.
#[derive(Debug)]
pub struct Table<T>(Vec<Shard<T>>);

impl<T: Hash + Eq> Table<T> {
    pub fn get(&self, t: &T) -> Option<Id<T>> {
        let h = hash(t);
        let k = shard_of(h);
        let s = &self.0[k];
        let i = s.index.find(h, |&i| s.nodes[i as usize] == *t)?;
        Some(Id::new(id(*i as usize * SHARDS + k)))
    }

    /// The number of nodes.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.iter().map(|s| s.nodes.len()).sum()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// One past the largest id, for arrays indexed by id.
    #[must_use]
    pub fn bound(&self) -> usize {
        self.0.iter().map(|s| s.nodes.len()).max().unwrap_or(0) * SHARDS
    }
}

impl<T> std::ops::Index<Id<T>> for Table<T> {
    type Output = T;
    fn index(&self, i: Id<T>) -> &T {
        let i = i.index();
        &self.0[i % SHARDS].nodes[i / SHARDS]
    }
}

#[derive(Debug)]
struct Chunk {
    nodes: Vec<Expr>,
    ranks: Vec<u32>,
}

/// Expressions, interned through a sharded index but stored in chunks that each thread fills
/// on its own, so that a term sits near its subterms in memory.
///
/// Equal terms can differ in binder names. The copy from the earliest module in import order
/// wins, whatever order the modules were decoded in.
struct SharedExprs {
    index: Vec<Mutex<HashTable<u32>>>,
    chunks: Vec<OnceLock<Box<Mutex<Chunk>>>>,
    next: AtomicUsize,
}

impl SharedExprs {
    fn new(n: usize) -> Self {
        Self {
            index: (0..SHARDS)
                .map(|_| Mutex::new(HashTable::with_capacity(n / SHARDS)))
                .collect(),
            chunks: (0..=u32::MAX as usize / CHUNK)
                .map(|_| OnceLock::new())
                .collect(),
            next: AtomicUsize::new(0),
        }
    }

    fn chunk(&self, k: usize) -> MutexGuard<'_, Chunk> {
        self.chunks[k]
            .get()
            .expect("chunk is published before its ids")
            .lock()
    }

    /// Run `f` on node `i` and its rank.
    fn with<R>(&self, i: u32, f: impl FnOnce(&mut Expr, &mut u32) -> R) -> R {
        let i = i as usize;
        let mut g = self.chunk(i / CHUNK);
        let c = &mut *g;
        let r = f(&mut c.nodes[i % CHUNK], &mut c.ranks[i % CHUNK]);
        drop(g);
        r
    }

    /// Intern `e` from module `rank`, adding it to the chunk `cursor` if it is new.
    #[allow(clippy::significant_drop_tightening)]
    fn intern(&self, e: Expr, rank: u32, cursor: &mut Option<usize>) -> ExprId {
        let h = hash(&e);
        let mut index = self.index[shard_of(h)].lock();
        let entry = index.entry(
            h,
            |&i| self.with(i, |n, _| *n == e),
            |&i| self.with(i, |n, _| hash(n)),
        );
        let i = match entry {
            Entry::Occupied(o) => {
                let i = *o.get();
                self.with(i, |n, r| {
                    if rank < *r {
                        *n = e;
                        *r = rank;
                    }
                });
                i
            }
            Entry::Vacant(v) => {
                let (k, mut c) = match cursor.map(|k| (k, self.chunk(k))) {
                    Some((k, c)) if c.nodes.len() < CHUNK => (k, c),
                    _ => {
                        let k = self.next.fetch_add(1, Relaxed);
                        self.chunks.get(k).expect("table overflow").get_or_init(|| {
                            Box::new(Mutex::new(Chunk {
                                nodes: Vec::with_capacity(CHUNK),
                                ranks: Vec::with_capacity(CHUNK),
                            }))
                        });
                        *cursor = Some(k);
                        (k, self.chunk(k))
                    }
                };
                let i = id(k * CHUNK + c.nodes.len());
                c.nodes.push(e);
                c.ranks.push(rank);
                v.insert(i);
                i
            }
        };
        Id::new(i)
    }

    /// The expressions, plus the index and ranks [`Env::reload`] needs to intern more.
    fn freeze(self) -> (Exprs, Vec<HashTable<u32>>, Vec<Vec<u32>>) {
        let n = self.next.into_inner();
        let (nodes, ranks) = self
            .chunks
            .into_iter()
            .take(n)
            .map(|c| {
                let c = c.into_inner().expect("chunk is published").into_inner();
                (c.nodes, c.ranks)
            })
            .unzip();
        let index = self.index.into_iter().map(Mutex::into_inner).collect();
        (Exprs(nodes), index, ranks)
    }

    fn thaw(exprs: Exprs, index: Vec<HashTable<u32>>, ranks: Vec<Vec<u32>>) -> Self {
        let n = exprs.0.len();
        let chunks: Vec<_> = (0..=u32::MAX as usize / CHUNK)
            .map(|_| OnceLock::new())
            .collect();
        for ((c, nodes), ranks) in chunks.iter().zip(exprs.0).zip(ranks) {
            c.set(Box::new(Mutex::new(Chunk { nodes, ranks })))
                .expect("chunk is set once");
        }
        Self {
            index: index.into_iter().map(Mutex::new).collect(),
            chunks,
            next: AtomicUsize::new(n),
        }
    }
}

/// Expressions by id. Ids come in chunks, each filled by one decoding thread, with gaps.
#[derive(Debug)]
pub struct Exprs(Vec<Vec<Expr>>);

impl Exprs {
    /// The number of expressions.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.iter().map(Vec::len).sum()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// One past the largest id, for arrays indexed by id.
    #[must_use]
    pub const fn bound(&self) -> usize {
        self.0.len() * CHUNK
    }
}

impl std::ops::Index<ExprId> for Exprs {
    type Output = Expr;
    fn index(&self, i: ExprId) -> &Expr {
        let i = i.index();
        &self.0[i / CHUNK][i % CHUNK]
    }
}

/// The tables every module of one load interns into.
struct Tables {
    names: Shared<Name>,
    levels: Shared<Level>,
    exprs: SharedExprs,
}

/// What one module adds besides table entries.
struct Module {
    consts: Vec<Const>,
    recursors: FxHashMap<NameId, Vec<NameId>>,
    skipped: usize,
    header: Header,
}

/// The olean parts of a module that exist, with their sizes and modification times.
type Stamp = Vec<(u64, Option<SystemTime>)>;

const PARTS: [&str; 3] = ["olean", "olean.server", "olean.private"];

fn stamp(path: &Path) -> Stamp {
    PARTS
        .iter()
        .filter_map(|e| std::fs::metadata(path.with_extension(e)).ok())
        .map(|m| (m.len(), m.modified().ok()))
        .collect()
}

/// A decoded module, as [`Env::reload`] tracks it.
#[derive(Debug)]
struct Loaded {
    module: String,
    stamp: Stamp,
    consts: Vec<NameId>,
    recursors: FxHashMap<NameId, Vec<NameId>>,
    skipped: usize,
    header: Header,
}

/// What an env from [`Env::open`] keeps to decode more modules into its tables.
#[derive(Debug)]
struct Live {
    search: Vec<PathBuf>,
    roots: Vec<String>,
    jobs: usize,
    index: Vec<HashTable<u32>>,
    ranks: Vec<Vec<u32>>,
    loaded: Vec<Loaded>,
}

/// What [`Env::reload`] changed.
#[derive(Debug, Default)]
pub struct Reload {
    /// Modules decoded again, in import order.
    pub modules: Vec<String>,
    /// Their constants, in load order.
    pub consts: Vec<NameId>,
    /// Constants no longer in the environment.
    pub removed: Vec<NameId>,
}

impl Reload {
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.modules.is_empty() && self.removed.is_empty()
    }
}

static LINEAGE: AtomicU64 = AtomicU64::new(0);

/// Every constant reachable from a set of root modules, in import order.
#[derive(Debug)]
pub struct Env {
    pub names: Table<Name>,
    pub levels: Table<Level>,
    pub exprs: Exprs,
    pub consts: FxHashMap<NameId, Const>,
    pub order: Vec<NameId>,
    pub recursors: FxHashMap<NameId, Vec<NameId>>,
    pub modules: Vec<String>,
    pub header: Header,
    pub skipped: usize,
    pub(crate) lineage: u64,
    live: Option<Box<Live>>,
}

impl Env {
    /// Load `roots` and their transitive imports, resolving modules against `search`.
    pub fn load(search: &[PathBuf], roots: &[&str]) -> Result<Self> {
        let jobs = std::thread::available_parallelism().map_or(1, usize::from);
        Self::load_with(search, roots, jobs, &|_, _| {})
    }

    /// Like [`Env::load`] on `jobs` threads, calling `progress` with the number of modules
    /// and constants decoded so far.
    ///
    /// Modules decode in parallel straight into shared tables, and the result is the same
    /// for any `jobs`.
    pub fn load_with(
        search: &[PathBuf],
        roots: &[&str],
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
    ) -> Result<Self> {
        Self::build(search, roots, jobs, progress, false)
    }

    /// Like [`Env::load_with`], but keeps the expression index so that [`Env::reload`] can
    /// decode changed modules into the same tables. That costs about 10 bytes per expression.
    pub fn open(search: &[PathBuf], roots: &[&str], jobs: usize) -> Result<Self> {
        Self::build(search, roots, jobs, &|_, _| {}, true)
    }

    fn build(
        search: &[PathBuf],
        roots: &[&str],
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
        live: bool,
    ) -> Result<Self> {
        let found = discover_all(search, roots)?;
        let stamps: Vec<Stamp> = found.iter().map(|(_, p)| stamp(p)).collect();
        // Sizing the tables up front avoids rehashing them while they grow. Across Lean and
        // Mathlib there is about one expression per 64 bytes of olean and one name per 1200.
        let bytes: u64 = stamps.iter().flatten().map(|(len, _)| len).sum();
        let estimate = |per: u64| usize::try_from(bytes / per).unwrap_or(0);
        let tables = Tables {
            names: Shared::new(Name::Anon, estimate(1200)),
            levels: Shared::new(Level::Zero, 0),
            exprs: SharedExprs::new(estimate(64)),
        };
        let paths: Vec<_> = found.iter().map(|(_, p)| p.as_path()).enumerate().collect();
        let decoded = decode_all(&tables, &paths, jobs, progress);
        let (exprs, index, ranks) = tables.exprs.freeze();
        let kept = live.then_some((index, ranks));
        let decoded = decoded?;
        let mut env = Self {
            names: tables.names.freeze(),
            levels: tables.levels.freeze(),
            exprs,
            consts: FxHashMap::default(),
            order: Vec::new(),
            recursors: FxHashMap::default(),
            modules: Vec::new(),
            header: Header::default(),
            skipped: 0,
            lineage: LINEAGE.fetch_add(1, Relaxed),
            live: None,
        };
        let loaded: Vec<_> = found
            .into_iter()
            .zip(stamps)
            .zip(decoded)
            .map(|(((module, _), stamp), m)| env.add(module, stamp, m))
            .collect();
        env.index(&loaded);
        if let Some((index, ranks)) = kept {
            env.live = Some(Box::new(Live {
                search: search.to_vec(),
                roots: roots.iter().map(|&r| r.to_owned()).collect(),
                jobs,
                index,
                ranks,
                loaded,
            }));
        }
        Ok(env)
    }

    fn add(&mut self, module: String, stamp: Stamp, m: Module) -> Loaded {
        let consts = m.consts.iter().map(|c| c.name).collect();
        self.consts
            .extend(m.consts.into_iter().map(|c| (c.name, c)));
        Loaded {
            module,
            stamp,
            consts,
            recursors: m.recursors,
            skipped: m.skipped,
            header: m.header,
        }
    }

    /// Rebuild the load order and everything summed over modules.
    fn index(&mut self, loaded: &[Loaded]) {
        self.order = loaded
            .iter()
            .flat_map(|l| l.consts.iter().copied())
            .collect();
        self.recursors.clear();
        for (ind, recs) in loaded.iter().flat_map(|l| &l.recursors) {
            self.recursors.entry(*ind).or_default().extend(recs);
        }
        self.modules = loaded.iter().map(|l| l.module.clone()).collect();
        self.header = loaded.last().map(|l| l.header.clone()).unwrap_or_default();
        self.skipped = loaded.iter().map(|l| l.skipped).sum();
    }

    /// Decode again the modules whose oleans changed since the last load, add newly imported
    /// ones and drop those no longer imported. Every id stays valid and the tables only grow,
    /// so an [`crate::Exporter`] can resume from a [`crate::Mark`] and write just the
    /// changes. Binder names, which no kernel reads, may differ from a fresh load.
    pub fn reload(&mut self) -> Result<Reload> {
        let mut live = self
            .live
            .take()
            .ok_or_else(|| corrupt("reload needs an environment from Env::open"))?;
        let r = self.reload_with(&mut live);
        self.live = Some(live);
        r
    }

    fn reload_with(&mut self, live: &mut Live) -> Result<Reload> {
        let roots: Vec<&str> = live.roots.iter().map(String::as_str).collect();
        let found = discover_all(&live.search, &roots)?;
        let stamps: Vec<Stamp> = found.iter().map(|(_, p)| stamp(p)).collect();
        let fresh: Vec<(usize, &Path)> = {
            let prev: FxHashMap<&str, &Stamp> = live
                .loaded
                .iter()
                .map(|l| (l.module.as_str(), &l.stamp))
                .collect();
            if found.len() == prev.len()
                && found
                    .iter()
                    .zip(&stamps)
                    .all(|((m, _), s)| prev.get(m.as_str()) == Some(&s))
            {
                return Ok(Reload::default());
            }
            found
                .iter()
                .zip(&stamps)
                .enumerate()
                .filter(|(_, ((m, _), s))| prev.get(m.as_str()) != Some(s))
                .map(|(i, ((_, p), _))| (i, p.as_path()))
                .collect()
        };
        let tables = Tables {
            names: std::mem::replace(&mut self.names, Table(Vec::new())).thaw(),
            levels: std::mem::replace(&mut self.levels, Table(Vec::new())).thaw(),
            exprs: SharedExprs::thaw(
                std::mem::replace(&mut self.exprs, Exprs(Vec::new())),
                std::mem::take(&mut live.index),
                std::mem::take(&mut live.ranks),
            ),
        };
        let decoded = decode_all(&tables, &fresh, live.jobs, &|_, _| {});
        self.names = tables.names.freeze();
        self.levels = tables.levels.freeze();
        (self.exprs, live.index, live.ranks) = tables.exprs.freeze();
        let mut decoded: FxHashMap<usize, Module> =
            fresh.iter().map(|&(i, _)| i).zip(decoded?).collect();
        let mut prev: FxHashMap<String, Loaded> = std::mem::take(&mut live.loaded)
            .into_iter()
            .map(|l| (l.module.clone(), l))
            .collect();
        let imported: FxHashSet<&str> = found.iter().map(|(m, _)| m.as_str()).collect();
        let mut stale = Vec::new();
        prev.retain(|m, l| {
            let keep =
                imported.contains(m.as_str()) && !fresh.iter().any(|&(i, _)| found[i].0 == *m);
            if !keep {
                stale.append(&mut l.consts);
            }
            keep
        });
        for c in &stale {
            self.consts.remove(c);
        }
        let mut reload = Reload::default();
        live.loaded = found
            .into_iter()
            .zip(stamps)
            .enumerate()
            .map(|(i, ((module, _), stamp))| match decoded.remove(&i) {
                Some(m) => {
                    reload.modules.push(module.clone());
                    reload.consts.extend(m.consts.iter().map(|c| c.name));
                    self.add(module, stamp, m)
                }
                None => prev.remove(&module).expect("unchanged module was loaded"),
            })
            .collect();
        self.index(&live.loaded);
        reload.removed = stale
            .into_iter()
            .filter(|c| !self.consts.contains_key(c))
            .collect();
        Ok(reload)
    }

    /// The constants `lean4export` exports when given no explicit names.
    pub fn roots(&self) -> impl Iterator<Item = NameId> + '_ {
        self.order.iter().copied().filter(|&c| !self.is_internal(c))
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

fn decode(tables: &Tables, rank: u32, cursor: &mut Option<usize>, path: &Path) -> Result<Module> {
    let img = Image::open_module(path)?;
    let mut dec = Decoder {
        img: &img,
        tables,
        rank,
        cursor,
        memo: vec![0; img.slots()],
        module: Module {
            consts: Vec::new(),
            recursors: FxHashMap::default(),
            skipped: 0,
            header: img.header.clone(),
        },
    };
    dec.run().map_err(at(path))?;
    Ok(dec.module)
}

/// Decode the modules at `paths`, each with its rank in import order, on `jobs` threads.
fn decode_all(
    tables: &Tables,
    paths: &[(usize, &Path)],
    jobs: usize,
    progress: &(dyn Fn(usize, usize) + Sync),
) -> Result<Vec<Module>> {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs.max(1))
        .build()?;
    let (done, consts) = (AtomicUsize::new(0), AtomicUsize::new(0));
    pool.install(|| {
        paths
            .par_iter()
            .map_init(
                || None,
                |cursor, &(rank, path)| {
                    let rank = u32::try_from(rank).expect("module count");
                    let m = decode(tables, rank, cursor, path)?;
                    let n = consts.fetch_add(m.consts.len(), Relaxed) + m.consts.len();
                    progress(done.fetch_add(1, Relaxed) + 1, n);
                    Ok(m)
                },
            )
            .collect()
    })
}

fn discover_all(search: &[PathBuf], roots: &[&str]) -> Result<Vec<(String, PathBuf)>> {
    let mut seen = FxHashSet::default();
    let mut found = Vec::new();
    for root in roots {
        discover(search, root, &mut seen, &mut found)?;
    }
    Ok(found)
}

/// Find `module` and its imports, appending them to `out` in import order.
fn discover(
    search: &[PathBuf],
    module: &str,
    seen: &mut FxHashSet<String>,
    out: &mut Vec<(String, PathBuf)>,
) -> Result<()> {
    if !seen.insert(module.to_owned()) {
        return Ok(());
    }
    let path = resolve(search, module)?;
    let img = Image::open(&path)?;
    let imports = img.imports().map_err(at(&path))?;
    drop(img);
    for import in &imports {
        discover(search, import, seen, out)?;
    }
    out.push((module.to_owned(), path));
    Ok(())
}

/// The `.olean` for a dotted module name such as `Init.Prelude`, from the first directory
/// of `search` that has it.
pub fn resolve(search: &[PathBuf], module: &str) -> Result<PathBuf> {
    let rel: PathBuf = module.split('.').collect();
    search
        .iter()
        .map(|dir| dir.join(&rel).with_extension("olean"))
        .find(|p| p.is_file())
        .ok_or_else(|| Error::ModuleNotFound(module.to_owned()))
}

impl Image {
    pub(crate) fn imports(&self) -> Result<Vec<String>> {
        let imports = self.array(self.field(self.root, 0)?)?;
        imports
            .into_iter()
            .map(|i| self.str_name(self.field(i, 0)?))
            .collect()
    }

    pub(crate) fn str_name(&self, mut o: u64) -> Result<String> {
        let mut parts = Vec::new();
        while !is_scalar(o) && self.tag(o)? != 0 {
            parts.push(if self.tag(o)? == 1 {
                self.str(self.field(o, 1)?)?.to_owned()
            } else {
                self.nat_decimal(self.field(o, 1)?)?
            });
            o = self.field(o, 0)?;
        }
        parts.reverse();
        Ok(parts.join("."))
    }
}

/// Translates one module's objects into the shared tables, memoized by address since the
/// compactor already maximally shares structurally equal objects within a module.
struct Decoder<'a> {
    img: &'a Image,
    tables: &'a Tables,
    /// The module's position in import order.
    rank: u32,
    /// The expression chunk this thread is filling.
    cursor: &'a mut Option<usize>,
    module: Module,
    /// Table id plus one for each decoded object, by slot. An object is only ever decoded as
    /// one of name, level or expression, so the kinds can share it.
    memo: Vec<u32>,
}

/// The memo mark of an expression whose subterms are still being decoded.
const PENDING: u32 = u32::MAX;

impl Decoder<'_> {
    fn run(&mut self) -> Result<()> {
        let img = self.img;
        for c in img.array(img.field(img.root, 2)?)? {
            self.constant(c)?;
        }
        Ok(())
    }

    /// The memo slot of `o`, and its id if it was already decoded.
    fn seen<T>(&self, o: u64) -> Result<(usize, Option<Id<T>>)> {
        let slot = self.img.slot(o)?;
        Ok((slot, self.memo[slot].checked_sub(1).map(Id::new)))
    }

    fn remember<T>(&mut self, slot: usize, id: Id<T>) -> Id<T> {
        self.memo[slot] = id.0 + 1;
        id
    }

    fn name(&mut self, o: u64) -> Result<NameId> {
        let img = self.img;
        if is_scalar(o) || img.tag(o)? == 0 {
            return Ok(ANON);
        }
        let (slot, seen) = self.seen(o)?;
        if let Some(id) = seen {
            return Ok(id);
        }
        let pre = self.name(img.field(o, 0)?)?;
        let arg = img.field(o, 1)?;
        let n = match img.tag(o)? {
            1 => Name::Str(pre, img.str(arg)?.into()),
            _ => Name::Num(pre, small_nat(arg)?),
        };
        let id = self.tables.names.intern(n);
        Ok(self.remember(slot, id))
    }

    fn names(&mut self, o: u64) -> Result<Vec<NameId>> {
        self.img
            .list(o)?
            .into_iter()
            .map(|n| self.name(n))
            .collect()
    }

    fn level(&mut self, o: u64) -> Result<LevelId> {
        let img = self.img;
        if is_scalar(o) || img.tag(o)? == 0 {
            return Ok(ZERO);
        }
        let (slot, seen) = self.seen(o)?;
        if let Some(id) = seen {
            return Ok(id);
        }
        let f = |i| img.field(o, i);
        let l = match img.tag(o)? {
            1 => Level::Succ(self.level(f(0)?)?),
            2 => Level::Max(self.level(f(0)?)?, self.level(f(1)?)?),
            3 => Level::IMax(self.level(f(0)?)?, self.level(f(1)?)?),
            4 => Level::Param(self.name(f(0)?)?),
            t => return Err(corrupt(format!("unexpected level tag {t}"))),
        };
        let id = self.tables.levels.intern(l);
        Ok(self.remember(slot, id))
    }

    /// Decode `root` after its subterms, on a worklist rather than the stack. A slot is
    /// [`PENDING`] while its subterms are queued, which catches cyclic images.
    fn expr(&mut self, root: u64) -> Result<ExprId> {
        let img = self.img;
        let mut work = vec![(root, false)];
        while let Some((o, ready)) = work.pop() {
            let slot = img.slot(o)?;
            let f = |i| img.field(o, i);
            let tag = img.tag(o)?;
            if !ready {
                match self.memo[slot] {
                    0 => {}
                    PENDING => return Err(corrupt("cyclic expression")),
                    _ => continue,
                }
                self.memo[slot] = PENDING;
                work.push((o, true));
                let subs: &[u64] = match tag {
                    5 => &[0, 1],
                    6 | 7 => &[1, 2],
                    8 => &[1, 2, 3],
                    10 => &[1],
                    11 => &[2],
                    _ => &[],
                };
                for &i in subs.iter().rev() {
                    work.push((f(i)?, false));
                }
                continue;
            }
            let binder = || {
                Ok::<_, Error>(match img.scalar_u8(o, 8)? {
                    0 => Binder::Default,
                    1 => Binder::Implicit,
                    2 => Binder::StrictImplicit,
                    _ => Binder::InstImplicit,
                })
            };
            let e = match tag {
                0 => Expr::BVar(small_nat(f(0)?)?),
                3 => Expr::Sort(self.level(f(0)?)?),
                4 => {
                    let us = img.list(f(1)?)?;
                    let us = us
                        .into_iter()
                        .map(|l| self.level(l))
                        .collect::<Result<_>>()?;
                    Expr::Const(self.name(f(0)?)?, us)
                }
                5 => Expr::App(self.done(f(0)?)?, self.done(f(1)?)?),
                6 => Expr::Lam(
                    self.name(f(0)?)?,
                    self.done(f(1)?)?,
                    self.done(f(2)?)?,
                    binder()?,
                ),
                7 => Expr::Pi(
                    self.name(f(0)?)?,
                    self.done(f(1)?)?,
                    self.done(f(2)?)?,
                    binder()?,
                ),
                8 => Expr::Let(
                    self.name(f(0)?)?,
                    self.done(f(1)?)?,
                    self.done(f(2)?)?,
                    self.done(f(3)?)?,
                ),
                9 => {
                    let lit = f(0)?;
                    let val = img.field(lit, 0)?;
                    if img.tag(lit)? == 0 {
                        Expr::Nat(img.nat_decimal(val)?.into())
                    } else {
                        Expr::Str(img.str(val)?.into())
                    }
                }
                10 => {
                    let id = self.done(f(1)?)?;
                    self.remember(slot, id);
                    continue;
                }
                11 => Expr::Proj(self.name(f(0)?)?, small_nat(f(1)?)?, self.done(f(2)?)?),
                t => {
                    return Err(corrupt(format!(
                        "unexpected expression tag {t} (free or meta variable in a declaration)"
                    )))
                }
            };
            let id = self.tables.exprs.intern(e, self.rank, self.cursor);
            self.remember(slot, id);
        }
        self.done(root)
    }

    /// The id of an already decoded subterm.
    fn done(&self, o: u64) -> Result<ExprId> {
        self.seen(o)?
            .1
            .ok_or_else(|| corrupt("subterm decoded out of order"))
    }

    fn constant(&mut self, info: u64) -> Result<()> {
        let img = self.img;
        let tag = img.tag(info)?;
        let val = img.field(info, 0)?;
        let unsafe_flag = match tag {
            1 => img.scalar_u8(val, 0)? != 1,
            0 | 3 | 6 => img.scalar_u8(val, 0)? != 0,
            5 | 7 => img.scalar_u8(val, 1)? != 0,
            _ => false,
        };
        if unsafe_flag {
            self.module.skipped += 1;
            return Ok(());
        }
        let f = |i| img.field(val, i);
        let nat = |i| small_nat(f(i)?);
        let cv = f(0)?;
        let name = self.name(img.field(cv, 0)?)?;
        let level_params = self.names(img.field(cv, 1)?)?;
        for &p in &level_params {
            self.tables.levels.intern(Level::Param(p));
        }
        let ty = self.expr(img.field(cv, 2)?)?;
        let kind = match tag {
            0 => Kind::Axiom,
            1 => {
                let h = f(2)?;
                let hints = if !is_scalar(h) {
                    Hints::Regular(img.scalar_u32(h)?)
                } else if h >> 1 == 0 {
                    Hints::Opaque
                } else {
                    Hints::Abbrev
                };
                Kind::Defn(Defn {
                    value: self.expr(f(1)?)?,
                    hints,
                    all: self.names(f(3)?)?,
                })
            }
            2 => Kind::Thm(Body {
                value: self.expr(f(1)?)?,
                all: self.names(f(2)?)?,
            }),
            3 => Kind::Opaque(Body {
                value: self.expr(f(1)?)?,
                all: self.names(f(2)?)?,
            }),
            4 => Kind::Quot(match img.scalar_u8(val, 0)? {
                0 => QuotKind::Type,
                1 => QuotKind::Ctor,
                2 => QuotKind::Lift,
                _ => QuotKind::Ind,
            }),
            5 => Kind::Induct(Inductive {
                num_params: nat(1)?,
                num_indices: nat(2)?,
                all: self.names(f(3)?)?,
                ctors: self.names(f(4)?)?,
                num_nested: nat(5)?,
                is_rec: img.scalar_u8(val, 0)? != 0,
                is_reflexive: img.scalar_u8(val, 2)? != 0,
            }),
            6 => Kind::Ctor(Ctor {
                induct: self.name(f(1)?)?,
                cidx: nat(2)?,
                num_params: nat(3)?,
                num_fields: nat(4)?,
            }),
            7 => {
                let all = self.names(f(1)?)?;
                for &ind in &all {
                    self.module.recursors.entry(ind).or_default().push(name);
                }
                let mut rules = Vec::new();
                for r in img.list(f(6)?)? {
                    rules.push(Rule {
                        ctor: self.name(img.field(r, 0)?)?,
                        nfields: small_nat(img.field(r, 1)?)?,
                        rhs: self.expr(img.field(r, 2)?)?,
                    });
                }
                Kind::Rec(Rec {
                    all,
                    num_params: nat(2)?,
                    num_indices: nat(3)?,
                    num_motives: nat(4)?,
                    num_minors: nat(5)?,
                    rules,
                    k: img.scalar_u8(val, 0)? != 0,
                })
            }
            t => return Err(corrupt(format!("unexpected constant tag {t}"))),
        };
        self.module.consts.push(Const {
            name,
            level_params,
            ty,
            kind,
        });
        Ok(())
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
