mod decode;
mod reload;
mod table;
mod term;
mod walk;

pub use reload::Reload;
pub use table::{Exprs, Table};
pub use term::{
    Binder, Body, Const, Ctor, Defn, Expr, ExprId, Hints, Id, Inductive, Kind, Level, LevelId,
    Name, NameId, QuotKind, Rec, Rule, Theorem, ANON, ZERO,
};
pub(crate) use walk::{Builtins, Dep, Depth, Family};

use self::{
    decode::{decode_all, Module},
    reload::{stamp, Live, Loaded, Stamp},
    table::{Shared, SharedExprs, Tables},
};
use crate::{
    error::{at, Error, Result},
    olean::{Header, Image},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    borrow::Cow,
    env,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering::Relaxed},
    thread,
};

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
    /// Where each module's constants end in `order`.
    ends: Vec<usize>,
    pub(crate) lineage: u64,
    live: Option<Box<Live>>,
}

/// Identifier-shaped tokens of Lean's term syntax, which a name must not print as.
const KEYWORDS: &[&str] = &[
    "Prop", "Sort", "Type", "at", "by", "calc", "do", "else", "end", "forall", "from", "fun",
    "have", "if", "in", "let", "match", "nofun", "nomatch", "open", "show", "sorry", "suffices",
    "then", "this", "where", "with",
];

/// A name component in `«»` unless Lean would read it back as itself unescaped. Lean has no
/// way to write a `»` in a name, so `»` and `\` are written after a `\`, which no name Lean
/// can print contains.
pub(crate) fn escape(s: &str) -> Cow<'_, str> {
    let letter = |c: char| {
        let u = u32::from(c);
        c.is_ascii_alphabetic()
            || c == '_'
            || ((0x3b1..=0x3c9).contains(&u) && u != 0x3bb)
            || ((0x391..=0x3a9).contains(&u) && u != 0x3a0 && u != 0x3a3)
            || matches!(u, 0x3ca..=0x3fb | 0x1f00..=0x1ffe | 0x2100..=0x214f | 0x1d49c..=0x1d59f)
    };
    let rest = |c: char| {
        letter(c)
            || c.is_ascii_digit()
            || matches!(c, '\'' | '!' | '?')
            || matches!(u32::from(c), 0x2080..=0x2089 | 0x2090..=0x209c | 0x1d62..=0x1d6a | 0x2c7c)
    };
    let mut cs = s.chars();
    let plain = cs.next().is_some_and(letter) && cs.all(rest) && !KEYWORDS.contains(&s);
    if plain {
        Cow::Borrowed(s)
    } else if s.contains(['»', '\\']) {
        Cow::Owned(format!("«{}»", s.replace('\\', "\\\\").replace('»', "\\»")))
    } else {
        Cow::Owned(format!("«{s}»"))
    }
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

#[must_use]
pub fn search_path() -> Vec<PathBuf> {
    let mut dirs: Vec<PathBuf> = env::var_os("LEAN_PATH")
        .map(|p| env::split_paths(&p).collect())
        .unwrap_or_default();
    if let Some(root) = env::var_os("LEAN_SYSROOT") {
        dirs.push(Path::new(&root).join("lib").join("lean"));
    }
    dirs
}

impl Env {
    /// Load `roots` and their transitive imports, resolving modules against `search`.
    pub fn load(search: &[PathBuf], roots: &[&str]) -> Result<Self> {
        let jobs = thread::available_parallelism().map_or(1, usize::from);
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
        Self::build(search, roots, jobs, progress, false, false)
    }

    fn build(
        search: &[PathBuf],
        roots: &[&str],
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
        live: bool,
        lazy: bool,
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
        let decoded = decode_all(&tables, &paths, jobs, progress, lazy);
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
            ends: Vec::new(),
            lineage: LINEAGE.fetch_add(1, Relaxed),
            live: None,
        };
        let loaded: Vec<_> = found
            .into_iter()
            .zip(stamps)
            .zip(decoded)
            .map(|(((module, path), stamp), m)| env.add(module, path, stamp, m))
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

    fn add(&mut self, module: String, path: PathBuf, stamp: Stamp, m: Module) -> Loaded {
        let consts = m.consts.iter().map(|c| c.name).collect();
        self.consts
            .extend(m.consts.into_iter().map(|c| (c.name, c)));
        Loaded {
            module,
            path,
            stamp,
            consts,
            recursors: m.recursors,
            skipped: m.skipped,
            header: m.header,
            pending: m.pending,
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
        self.ends = loaded
            .iter()
            .scan(0, |end, l| {
                *end += l.consts.len();
                Some(*end)
            })
            .collect();
    }

    /// The constants `lean4export` exports when given no explicit names.
    pub fn roots(&self) -> impl Iterator<Item = NameId> + '_ {
        self.order.iter().copied().filter(|&c| !self.is_internal(c))
    }

    /// Look up a name such as `Nat.add` or `Foo.«bar.baz»`, as [`Env::display`] writes it,
    /// without interning it.
    #[must_use]
    pub fn find_name(&self, dotted: &str) -> Option<NameId> {
        let (mut pre, mut rest) = (ANON, dotted);
        loop {
            let (n, tail) = if let Some(r) = rest.strip_prefix('«') {
                let (mut s, mut cs) = (String::new(), r.char_indices());
                let end = loop {
                    match cs.next()? {
                        (_, '\\') => s.push(cs.next()?.1),
                        (i, '»') => break i + '»'.len_utf8(),
                        (_, c) => s.push(c),
                    }
                };
                (Name::Str(pre, s.into()), &r[end..])
            } else {
                let (s, tail) = rest.split_at(rest.find('.').unwrap_or(rest.len()));
                let n = s
                    .parse()
                    .map_or_else(|_| Name::Str(pre, s.into()), |i| Name::Num(pre, i));
                (n, tail)
            };
            pre = self.names.get(&n)?;
            match tail.strip_prefix('.') {
                Some(t) => rest = t,
                None => return tail.is_empty().then_some(pre),
            }
        }
    }

    /// `n` as Lean reads it back: components that are not plain identifiers, or are
    /// keywords, go in `«»`.
    #[must_use]
    pub fn display(&self, n: NameId) -> String {
        self.join(n, true)
    }

    /// `n` with its components joined as they are, as `declRangeExt` keys it.
    pub(crate) fn dotted(&self, n: NameId) -> String {
        self.join(n, false)
    }

    fn join(&self, n: NameId, escaped: bool) -> String {
        let (pre, last) = match &self.names[n] {
            Name::Anon => return String::new(),
            Name::Str(p, s) if escaped => (*p, escape(s).into_owned()),
            Name::Str(p, s) => (*p, s.to_string()),
            Name::Num(p, i) => (*p, i.to_string()),
        };
        match pre {
            ANON => last,
            p => format!("{}.{last}", self.join(p, escaped)),
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
