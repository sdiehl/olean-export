use crate::olean::{at, corrupt, is_scalar, small_nat, Header, Image};
use hashbrown::{hash_table::Entry, HashTable};
use parking_lot::{Mutex, MutexGuard};
use rayon::prelude::*;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use std::{
    hash::{BuildHasher, Hash},
    io,
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicUsize, Ordering::Relaxed},
        OnceLock,
    },
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

    fn intern(&self, t: T) -> u32 {
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
        id(i * SHARDS + k)
    }

    fn freeze(self) -> Table<T> {
        Table(self.0.into_iter().map(Mutex::into_inner).collect())
    }
}

/// A hash-consing arena: structurally equal nodes get the same id. Ids are interleaved
/// across shards, so they are nearly but not exactly dense.
#[derive(Debug)]
pub struct Table<T>(Vec<Shard<T>>);

impl<T: Hash + Eq> Table<T> {
    pub fn get(&self, t: &T) -> Option<u32> {
        let h = hash(t);
        let k = shard_of(h);
        let s = &self.0[k];
        let i = s.index.find(h, |&i| s.nodes[i as usize] == *t)?;
        Some(id(*i as usize * SHARDS + k))
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

impl<T> std::ops::Index<u32> for Table<T> {
    type Output = T;
    fn index(&self, i: u32) -> &T {
        let i = i as usize;
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

    /// Intern `e` from module `rank`, adding it to the chunk `cursor` if it is new.
    #[allow(clippy::significant_drop_tightening)]
    fn intern(&self, e: Expr, rank: u32, cursor: &mut Option<usize>) -> u32 {
        let h = hash(&e);
        let mut index = self.index[shard_of(h)].lock();
        let node = |i: u32, f: &mut dyn FnMut(&mut Expr, &mut u32)| {
            let i = i as usize;
            let mut g = self.chunk(i / CHUNK);
            let c = &mut *g;
            f(&mut c.nodes[i % CHUNK], &mut c.ranks[i % CHUNK]);
            drop(g);
        };
        let entry = index.entry(
            h,
            |&i| {
                let mut eq = false;
                node(i, &mut |n, _| eq = *n == e);
                eq
            },
            |&i| {
                let mut h = 0;
                node(i, &mut |n, _| h = hash(n));
                h
            },
        );
        match entry {
            Entry::Occupied(o) => {
                let i = *o.get();
                node(i, &mut |n, r| {
                    if rank < *r {
                        *n = e.clone();
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
        }
    }

    fn freeze(self) -> Exprs {
        let n = self.next.into_inner();
        let chunks = self.chunks.into_iter().take(n).map(|c| {
            let c = c.into_inner().expect("chunk is published");
            c.into_inner().nodes
        });
        Exprs(chunks.collect())
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

impl std::ops::Index<u32> for Exprs {
    type Output = Expr;
    fn index(&self, i: u32) -> &Expr {
        let i = i as usize;
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
}

impl Env {
    /// Load `roots` and their transitive imports, resolving modules against `search`.
    pub fn load(search: &[PathBuf], roots: &[&str]) -> io::Result<Self> {
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
    ) -> io::Result<Self> {
        let mut seen = FxHashSet::default();
        let mut found = Vec::new();
        for root in roots {
            discover(search, root, &mut seen, &mut found)?;
        }
        // Sizing the tables up front avoids rehashing them while they grow. Across Lean and
        // Mathlib there is about one expression per 64 bytes of olean and one name per 1200.
        let bytes: u64 = found
            .iter()
            .flat_map(|(_, p)| {
                ["olean", "olean.server", "olean.private"].map(|e| p.with_extension(e))
            })
            .filter_map(|p| std::fs::metadata(p).ok())
            .map(|m| m.len())
            .sum();
        let estimate = |per: u64| usize::try_from(bytes / per).unwrap_or(0);
        let tables = Tables {
            names: Shared::new(Name::Anon, estimate(1200)),
            levels: Shared::new(Level::Zero, 0),
            exprs: SharedExprs::new(estimate(64)),
        };
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(jobs.max(1))
            .stack_size(crate::STACK)
            .build()
            .map_err(io::Error::other)?;
        let (done, consts) = (AtomicUsize::new(0), AtomicUsize::new(0));
        let decoded = pool.install(|| {
            found
                .par_iter()
                .enumerate()
                .map_init(
                    || None,
                    |cursor, (rank, (_, path))| {
                        let rank = u32::try_from(rank).expect("module count");
                        let m = decode(&tables, rank, cursor, path)?;
                        let n = consts.fetch_add(m.consts.len(), Relaxed) + m.consts.len();
                        progress(done.fetch_add(1, Relaxed) + 1, n);
                        Ok(m)
                    },
                )
                .collect::<io::Result<Vec<_>>>()
        })?;
        let mut env = Self {
            names: tables.names.freeze(),
            levels: tables.levels.freeze(),
            exprs: tables.exprs.freeze(),
            consts: FxHashMap::default(),
            order: Vec::new(),
            recursors: FxHashMap::default(),
            modules: Vec::new(),
            header: Header::default(),
            skipped: 0,
        };
        for ((module, _), m) in found.into_iter().zip(decoded) {
            for c in m.consts {
                env.order.push(c.name);
                env.consts.insert(c.name, c);
            }
            for (ind, recs) in m.recursors {
                env.recursors.entry(ind).or_default().extend(recs);
            }
            env.skipped += m.skipped;
            env.header = m.header;
            env.modules.push(module);
        }
        Ok(env)
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

fn decode(
    tables: &Tables,
    rank: u32,
    cursor: &mut Option<usize>,
    path: &Path,
) -> io::Result<Module> {
    let mut img = Image::open(path)?;
    if img.scalar_u8(img.root, 0).map_err(at(path))? == 1 {
        img.push_part(&path.with_extension("olean.server"))?;
        img.push_part(&path.with_extension("olean.private"))?;
    }
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
    let imports = img.imports().map_err(at(&path))?;
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
    fn imports(&self) -> io::Result<Vec<String>> {
        let imports = self.array(self.field(self.root, 0)?)?;
        imports
            .into_iter()
            .map(|i| self.str_name(self.field(i, 0)?))
            .collect()
    }

    fn str_name(&self, mut o: u64) -> io::Result<String> {
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

impl Decoder<'_> {
    fn run(&mut self) -> io::Result<()> {
        let img = self.img;
        for c in img.array(img.field(img.root, 2)?)? {
            self.constant(c)?;
        }
        Ok(())
    }

    /// The memo slot of `o`, and its id if it was already decoded.
    fn seen(&self, o: u64) -> io::Result<(usize, Option<u32>)> {
        let slot = self.img.slot(o)?;
        Ok((slot, self.memo[slot].checked_sub(1)))
    }

    fn remember(&mut self, slot: usize, id: u32) -> u32 {
        self.memo[slot] = id + 1;
        id
    }

    fn name(&mut self, o: u64) -> io::Result<NameId> {
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

    fn names(&mut self, o: u64) -> io::Result<Vec<NameId>> {
        self.img
            .list(o)?
            .into_iter()
            .map(|n| self.name(n))
            .collect()
    }

    fn level(&mut self, o: u64) -> io::Result<LevelId> {
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

    fn expr(&mut self, o: u64) -> io::Result<ExprId> {
        let (slot, seen) = self.seen(o)?;
        if let Some(id) = seen {
            return Ok(id);
        }
        let img = self.img;
        let f = |i| img.field(o, i);
        let binder = || {
            Ok::<_, io::Error>(match img.scalar_u8(o, 8)? {
                0 => Binder::Default,
                1 => Binder::Implicit,
                2 => Binder::StrictImplicit,
                _ => Binder::InstImplicit,
            })
        };
        let e = match img.tag(o)? {
            0 => Expr::BVar(small_nat(f(0)?)?),
            3 => Expr::Sort(self.level(f(0)?)?),
            4 => {
                let us = img.list(f(1)?)?;
                let us = us
                    .into_iter()
                    .map(|l| self.level(l))
                    .collect::<io::Result<_>>()?;
                Expr::Const(self.name(f(0)?)?, us)
            }
            5 => Expr::App(self.expr(f(0)?)?, self.expr(f(1)?)?),
            6 => Expr::Lam(
                self.name(f(0)?)?,
                self.expr(f(1)?)?,
                self.expr(f(2)?)?,
                binder()?,
            ),
            7 => Expr::Pi(
                self.name(f(0)?)?,
                self.expr(f(1)?)?,
                self.expr(f(2)?)?,
                binder()?,
            ),
            8 => Expr::Let(
                self.name(f(0)?)?,
                self.expr(f(1)?)?,
                self.expr(f(2)?)?,
                self.expr(f(3)?)?,
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
                let id = self.expr(f(1)?)?;
                return Ok(self.remember(slot, id));
            }
            11 => Expr::Proj(self.name(f(0)?)?, small_nat(f(1)?)?, self.expr(f(2)?)?),
            t => {
                return Err(corrupt(format!(
                    "unexpected expression tag {t} (free or meta variable in a declaration)"
                )))
            }
        };
        let id = self.tables.exprs.intern(e, self.rank, self.cursor);
        Ok(self.remember(slot, id))
    }

    fn constant(&mut self, info: u64) -> io::Result<()> {
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
                Kind::Defn {
                    value: self.expr(f(1)?)?,
                    hints,
                    all: self.names(f(3)?)?,
                }
            }
            2 => Kind::Thm {
                value: self.expr(f(1)?)?,
                all: self.names(f(2)?)?,
            },
            3 => Kind::Opaque {
                value: self.expr(f(1)?)?,
                all: self.names(f(2)?)?,
            },
            4 => Kind::Quot(match img.scalar_u8(val, 0)? {
                0 => QuotKind::Type,
                1 => QuotKind::Ctor,
                2 => QuotKind::Lift,
                _ => QuotKind::Ind,
            }),
            5 => Kind::Induct {
                num_params: nat(1)?,
                num_indices: nat(2)?,
                all: self.names(f(3)?)?,
                ctors: self.names(f(4)?)?,
                num_nested: nat(5)?,
                is_rec: img.scalar_u8(val, 0)? != 0,
                is_reflexive: img.scalar_u8(val, 2)? != 0,
            },
            6 => Kind::Ctor {
                induct: self.name(f(1)?)?,
                cidx: nat(2)?,
                num_params: nat(3)?,
                num_fields: nat(4)?,
            },
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
                Kind::Rec {
                    all,
                    num_params: nat(2)?,
                    num_indices: nat(3)?,
                    num_motives: nat(4)?,
                    num_minors: nat(5)?,
                    rules,
                    k: img.scalar_u8(val, 0)? != 0,
                }
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
