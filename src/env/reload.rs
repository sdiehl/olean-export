use super::{
    decode::{decode_all, Module},
    discover_all,
    table::{SharedExprs, Table, Tables},
    term::NameId,
    Env,
};
use crate::{
    error::{Error, Result},
    inspect::Import,
    olean::Header,
};
use hashbrown::HashTable;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    fs, mem,
    path::{Path, PathBuf},
    time::SystemTime,
};

/// The olean parts of a module that exist, with their sizes and modification times.
pub(super) type Stamp = Vec<(u64, Option<SystemTime>)>;

const PARTS: [&str; 3] = ["olean", "olean.server", "olean.private"];

pub(super) fn stamp(path: &Path) -> Stamp {
    PARTS
        .iter()
        .filter_map(|e| fs::metadata(path.with_extension(e)).ok())
        .map(|m| (m.len(), m.modified().ok()))
        .collect()
}

/// A decoded module, as [`Env::reload`] tracks it.
#[derive(Debug)]
pub(super) struct Loaded {
    pub(super) module: String,
    pub(super) path: PathBuf,
    pub(super) stamp: Stamp,
    pub(super) consts: Vec<NameId>,
    pub(super) recursors: FxHashMap<NameId, Vec<NameId>>,
    pub(super) skipped: usize,
    pub(super) header: Header,
    pub(super) imports: Vec<Import>,
    pub(super) exported: Option<FxHashMap<NameId, bool>>,
    pub(super) pending: Vec<(NameId, u64)>,
}

/// What an env from [`Env::open`] keeps to decode more modules into its tables.
#[derive(Debug)]
pub(super) struct Live {
    pub(super) search: Vec<PathBuf>,
    pub(super) roots: Vec<String>,
    pub(super) jobs: usize,
    pub(super) index: Vec<HashTable<u32>>,
    pub(super) ranks: Vec<Vec<u32>>,
    pub(super) loaded: Vec<Loaded>,
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

impl Env {
    /// Like [`Env::load_with`], but keeps the expression index so that [`Env::reload`] can
    /// decode changed modules into the same tables. That costs about 10 bytes per expression.
    pub fn open(search: &[PathBuf], roots: &[&str], jobs: usize) -> Result<Self> {
        Self::build(search, roots, jobs, &|_, _| {}, true, false)
    }

    /// Decode again the modules whose oleans changed since the last load, add newly imported
    /// ones and drop those no longer imported. Every id stays valid and the tables only grow,
    /// so an [`crate::Exporter`] can resume from a [`crate::Mark`] and write just the
    /// changes. Binder names, which no kernel reads, may differ from a fresh load.
    pub fn reload(&mut self) -> Result<Reload> {
        let mut live = self
            .live
            .take()
            .ok_or(Error::Misuse("reload needs an environment from Env::open"))?;
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
        let tables = self.thaw(live);
        let decoded = decode_all(&tables, &fresh, live.jobs, &|_, _| {}, false);
        self.freeze(tables, live);
        let mut decoded: FxHashMap<usize, Module> =
            fresh.iter().map(|&(i, _)| i).zip(decoded?).collect();
        let mut prev: FxHashMap<String, Loaded> = mem::take(&mut live.loaded)
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
            .map(|(i, ((module, path), stamp))| match decoded.remove(&i) {
                Some(m) => {
                    reload.modules.push(module.clone());
                    reload.consts.extend(m.consts.iter().map(|c| c.name));
                    self.add(module, path, stamp, m)
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

    /// Hand the tables back to shared, growable form to decode more into them.
    pub(super) fn thaw(&mut self, live: &mut Live) -> Tables {
        Tables {
            names: mem::replace(&mut self.names, Table(Vec::new())).thaw(),
            levels: mem::replace(&mut self.levels, Table(Vec::new())).thaw(),
            exprs: SharedExprs::thaw(
                mem::take(&mut self.exprs),
                mem::take(&mut live.index),
                mem::take(&mut live.ranks),
            ),
        }
    }

    pub(super) fn freeze(&mut self, tables: Tables, live: &mut Live) {
        self.names = tables.names.freeze();
        self.levels = tables.levels.freeze();
        (self.exprs, live.index, live.ranks) = tables.exprs.freeze();
    }
}
