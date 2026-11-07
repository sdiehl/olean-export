use super::term::{Expr, ExprId, Id, Level, Name};
use hashbrown::{hash_table::Entry, HashTable};
use parking_lot::{Mutex, MutexGuard};
use rustc_hash::FxBuildHasher;
use std::{
    hash::{BuildHasher, Hash},
    ops::Index,
    sync::{
        atomic::{AtomicUsize, Ordering::Relaxed},
        OnceLock,
    },
};

const SHARDS: usize = 256;

const CHUNK: usize = 1 << 14;

#[derive(Debug)]
pub(super) struct Shard<T> {
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
pub(super) struct Shared<T>(Vec<Mutex<Shard<T>>>);

impl<T: Hash + Eq> Shared<T> {
    /// A table with room for about `n` nodes, whose id 0 is `zero`.
    pub(super) fn new(zero: T, n: usize) -> Self {
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

    pub(super) fn intern(&self, t: T) -> Id<T> {
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

    pub(super) fn freeze(self) -> Table<T> {
        Table(self.0.into_iter().map(Mutex::into_inner).collect())
    }
}

impl<T> Table<T> {
    pub(super) fn thaw(self) -> Shared<T> {
        Shared(self.0.into_iter().map(Mutex::new).collect())
    }
}

/// A hash-consing arena: structurally equal nodes get the same id. Ids are interleaved
/// across shards, so they are nearly but not exactly dense.
#[derive(Debug)]
pub struct Table<T>(pub(super) Vec<Shard<T>>);

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

impl<T> Index<Id<T>> for Table<T> {
    type Output = T;
    fn index(&self, i: Id<T>) -> &T {
        let i = i.index();
        &self.0[i % SHARDS].nodes[i / SHARDS]
    }
}

#[derive(Debug)]
pub(super) struct Chunk {
    nodes: Vec<Expr>,
    ranks: Vec<u32>,
}

/// Expressions, interned through a sharded index but stored in chunks that each thread fills
/// on its own, so that a term sits near its subterms in memory.
///
/// Equal terms can differ in binder names. The copy from the earliest module in import order
/// wins, whatever order the modules were decoded in.
pub(super) struct SharedExprs {
    index: Vec<Mutex<HashTable<u32>>>,
    chunks: Slots,
    next: AtomicUsize,
}

const PAGE: usize = 512;

type Slot = OnceLock<Box<Mutex<Chunk>>>;

/// A slot for every chunk an id can name, allocated a page at a time as chunks are claimed.
struct Slots(Box<[OnceLock<Box<[Slot]>>]>);

impl Slots {
    fn new() -> Self {
        Self(
            (0..=u32::MAX as usize / CHUNK / PAGE)
                .map(|_| OnceLock::new())
                .collect(),
        )
    }

    fn get(&self, k: usize) -> &Slot {
        let page = self.0.get(k / PAGE).expect("table overflow");
        &page.get_or_init(|| (0..PAGE).map(|_| OnceLock::new()).collect())[k % PAGE]
    }

    /// The chunks claimed, in id order.
    fn into_chunks(self) -> impl Iterator<Item = Chunk> {
        self.0
            .into_vec()
            .into_iter()
            .filter_map(OnceLock::into_inner)
            .flat_map(<[_]>::into_vec)
            .map_while(OnceLock::into_inner)
            .map(|c| c.into_inner())
    }
}

impl SharedExprs {
    pub(super) fn new(n: usize) -> Self {
        Self {
            index: (0..SHARDS)
                .map(|_| Mutex::new(HashTable::with_capacity(n / SHARDS)))
                .collect(),
            chunks: Slots::new(),
            next: AtomicUsize::new(0),
        }
    }

    fn chunk(&self, k: usize) -> MutexGuard<'_, Chunk> {
        self.chunks
            .get(k)
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
    pub(super) fn intern(&self, e: Expr, rank: u32, cursor: &mut Option<usize>) -> ExprId {
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
                        self.chunks.get(k).get_or_init(|| {
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
    pub(super) fn freeze(self) -> (Exprs, Vec<HashTable<u32>>, Vec<Vec<u32>>) {
        let (nodes, ranks) = self
            .chunks
            .into_chunks()
            .map(|c| (c.nodes, c.ranks))
            .unzip();
        let index = self.index.into_iter().map(Mutex::into_inner).collect();
        (Exprs(nodes), index, ranks)
    }

    pub(super) fn thaw(exprs: Exprs, index: Vec<HashTable<u32>>, ranks: Vec<Vec<u32>>) -> Self {
        let n = exprs.0.len();
        let chunks = Slots::new();
        for (k, (nodes, ranks)) in exprs.0.into_iter().zip(ranks).enumerate() {
            chunks
                .get(k)
                .set(Box::new(Mutex::new(Chunk { nodes, ranks })))
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
#[derive(Debug, Default)]
pub struct Exprs(pub(super) Vec<Vec<Expr>>);

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

impl Index<ExprId> for Exprs {
    type Output = Expr;
    fn index(&self, i: ExprId) -> &Expr {
        let i = i.index();
        &self.0[i / CHUNK][i % CHUNK]
    }
}

/// The tables every module of one load interns into.
pub(super) struct Tables {
    pub(super) names: Shared<Name>,
    pub(super) levels: Shared<Level>,
    pub(super) exprs: SharedExprs,
}
