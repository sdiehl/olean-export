//! Per-module exports and joining them back into one.

use crate::{
    blean::{self, Blean},
    error::{corrupt, Result},
    ndjson::{self, Ndjson},
    record::{Counts, Record, Sink, Table},
    Env, Exporter,
};
use rustc_hash::{FxHashMap, FxHashSet};
use serde_json::Value;
use std::{
    fs::File,
    io::{BufWriter, Write},
    path::{Path, PathBuf},
};
use xxhash_rust::xxh3::xxh3_128;

/// The `meta` object of an NDJSON or blean export, read from its first record.
pub fn meta(bytes: &[u8]) -> Result<Value> {
    let json = if blean::sniff(bytes) {
        match blean::entries(bytes)?.next() {
            Some(Ok((Record::Meta(m), _))) => m.into_owned(),
            Some(Err(e)) => return Err(e),
            _ => return Err(corrupt("export does not start with meta")),
        }
    } else {
        let line = bytes.split(|&b| b == b'\n').next().unwrap_or_default();
        let v: Value = serde_json::from_slice(line)?;
        v.get("meta")
            .ok_or_else(|| corrupt("export does not start with meta"))?
            .to_string()
    };
    Ok(serde_json::from_str(&json)?)
}

/// A per-module file's `meta`.
struct Module {
    name: String,
    imports: Vec<(String, String)>,
    interface: Option<String>,
    public: bool,
    inside: Vec<String>,
}

fn module(meta: &Value) -> Result<Module> {
    let m = meta
        .get("module")
        .ok_or_else(|| corrupt("not a per-module export"))?;
    let s = |v: &Value| v.as_str().map(str::to_owned);
    let bad = || corrupt("bad module in meta");
    Ok(Module {
        name: m.get("name").and_then(s).ok_or_else(bad)?,
        imports: m
            .get("imports")
            .and_then(Value::as_array)
            .ok_or_else(bad)?
            .iter()
            .map(|i| Some((s(i.get("name")?)?, s(i.get("blake3")?)?)))
            .collect::<Option<_>>()
            .ok_or_else(bad)?,
        interface: m.get("interface").and_then(s),
        public: m.get("public").and_then(Value::as_bool) == Some(true),
        inside: (m
            .get("inside")
            .and_then(Value::as_array)
            .into_iter()
            .flatten())
        .filter_map(s)
        .collect(),
    })
}

/// Hex blake3 of an export's bytes, as per-module metas name their imports.
#[must_use]
pub fn hash(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

/// The order to join per-module `files` in, imports first. Fails unless every import of
/// every file is among them with the hash it was exported against, or is the module whose
/// interface has that hash.
pub fn order(files: &[&[u8]]) -> Result<Vec<usize>> {
    plan(files, None)
}

/// The files to join for `root` as Lean showed it its imports, imports first.
pub fn view(files: &[&[u8]], root: &str) -> Result<Vec<usize>> {
    plan(files, Some(root))
}

fn plan(files: &[&[u8]], root: Option<&str>) -> Result<Vec<usize>> {
    let mods = files
        .iter()
        .map(|b| module(&meta(b)?))
        .collect::<Result<Vec<_>>>()?;
    let mut by_name: FxHashMap<&str, Vec<usize>> = FxHashMap::default();
    for (i, m) in mods.iter().enumerate() {
        let given = by_name.entry(m.name.as_str()).or_default();
        if root.is_none() && !given.is_empty() {
            return Err(corrupt(format!("module {} given twice", m.name)));
        }
        given.push(i);
    }
    let hashes: Vec<String> = files.iter().map(|b| hash(b)).collect();
    let start = root
        .map(|r| {
            (by_name.get(r).into_iter().flatten().copied())
                .find(|&j| !mods[j].public)
                .ok_or_else(|| corrupt(format!("module {r} is not given")))
        })
        .transpose()?;
    // a root outside the module system sees all of every module under it
    let whole = start.is_none_or(|j| mods[j].interface.is_none());
    let mut deps = Vec::with_capacity(files.len());
    for m in &mods {
        let mut d = Vec::new();
        for (i, h) in &m.imports {
            let given = by_name
                .get(i.as_str())
                .ok_or_else(|| corrupt(format!("{} imports {i}, which is not given", m.name)))?;
            let of = |j: usize| mods[j].interface.as_ref() == Some(h);
            let found = (given.iter().copied())
                .filter(|&j| hashes[j] == *h || whole && of(j))
                .min_by_key(|&j| mods[j].public);
            d.push(found.ok_or_else(|| {
                corrupt(if given.iter().any(|&j| of(j)) {
                    format!(
                        "{} imports the interface of {i}, which is not given",
                        m.name
                    )
                } else {
                    format!("{} was exported against another {i}", m.name)
                })
            })?);
        }
        deps.push(d);
    }
    if let Some(start) = start {
        let mut seen = vec![false; files.len()];
        let mut stack = vec![start];
        while let Some(i) = stack.pop() {
            if !std::mem::replace(&mut seen[i], true) {
                stack.extend(&deps[i]);
            }
        }
        let reached: FxHashMap<&str, usize> = (0..files.len())
            .filter(|&i| seen[i] && !mods[i].public)
            .map(|i| (mods[i].name.as_str(), i))
            .collect();
        for d in deps.iter_mut().flatten() {
            *d = *reached.get(mods[*d].name.as_str()).unwrap_or(d);
        }
        // the first copy of a declaration wins, so a module joined whole goes before an
        // interface that states its constants as axioms
        for (i, m) in mods.iter().enumerate() {
            deps[i].extend(m.inside.iter().filter_map(|o| reached.get(o.as_str())));
        }
    }
    let starts = start.map_or_else(|| (0..files.len()).collect(), |s| vec![s]);
    let mut out = Vec::with_capacity(files.len());
    let mut state = vec![0u8; files.len()];
    for root in starts {
        let mut stack = vec![(root, 0)];
        while let Some((i, k)) = stack.pop() {
            if k == 0 {
                match state[i] {
                    2 => continue,
                    1 => return Err(corrupt(format!("import cycle at {}", mods[i].name))),
                    _ => state[i] = 1,
                }
            }
            if let Some(&j) = deps[i].get(k) {
                stack.push((i, k + 1));
                if state[j] != 2 {
                    stack.push((j, 0));
                }
            } else {
                state[i] = 2;
                out.push(i);
            }
        }
    }
    Ok(out)
}

/// Shifts one file's ids past the files before it, and drops declarations an earlier file
/// already made.
struct Shift<'s, S> {
    sink: &'s mut S,
    base: Counts,
    next: Counts,
    names: &'s mut Vec<u128>,
    declared: &'s mut FxHashSet<u128>,
}

impl<S: Sink> Shift<'_, S> {
    fn name(&mut self, pre: u32, tag: u8, last: &[u8]) {
        let mut b = self.names[pre as usize].to_le_bytes().to_vec();
        b.push(tag);
        b.extend_from_slice(last);
        self.names.push(xxh3_128(&b));
    }

    const fn id(&self, t: Table, i: u32) -> u32 {
        match t {
            Table::Names if i > 0 => self.base.names + i - 1,
            Table::Levels if i > 0 => self.base.levels + i - 1,
            Table::Exprs => self.base.exprs + i,
            _ => i,
        }
    }
}

impl<S: Sink> Sink for &mut Shift<'_, S> {
    type Output = ();

    fn record(&mut self, id: Option<u32>, r: &Record<'_>) -> Result<()> {
        match r {
            Record::Meta(_) => Ok(()),
            Record::End(c) => {
                self.next = Counts {
                    names: self.base.names + c.names - 1,
                    levels: self.base.levels + c.levels - 1,
                    exprs: self.base.exprs + c.exprs,
                };
                Ok(())
            }
            r => {
                let mut r = r.clone();
                r.map_ids(&|t, i| self.id(t, i));
                let id = match (id, r.table()) {
                    (Some(i), Some(t)) => Some(self.id(t, i)),
                    (id, _) => id,
                };
                match &r {
                    Record::NameStr { pre, str } => self.name(*pre, 0, str.as_bytes()),
                    Record::NameNum { pre, i } => self.name(*pre, 1, &i.to_le_bytes()),
                    Record::Decl(d) => {
                        let n = d.name().and_then(|n| self.names.get(n as usize));
                        if n.is_some_and(|&n| !self.declared.insert(n)) {
                            return Ok(());
                        }
                    }
                    _ => {}
                }
                self.sink.record(id, &r)
            }
        }
    }

    fn finish(self) -> Result<()> {
        Ok(())
    }
}

/// Join per-module `files` into one export on `sink`, in the order [`order`] gives. Names,
/// levels and expressions two modules share appear once per module, a declaration two
/// modules make appears once.
pub fn join<S: Sink>(files: &[&[u8]], sink: S) -> Result<S::Output> {
    merge(files, &order(files)?, None, sink)
}

/// Join the files [`view`] picks for `root`.
///
/// The meta's `view` names the module and how many declarations come before its own. A
/// checker may take those as given: Lean checks a statement where its module's imports
/// unfold, not where an importer sees them hidden.
pub fn join_view<S: Sink>(files: &[&[u8]], root: &str, sink: S) -> Result<S::Output> {
    merge(files, &view(files, root)?, Some(root), sink)
}

struct Count(u64);

impl Sink for Count {
    type Output = ();

    fn record(&mut self, _: Option<u32>, r: &Record<'_>) -> Result<()> {
        self.0 += u64::from(matches!(r, Record::Decl(_)));
        Ok(())
    }

    fn finish(self) -> Result<()> {
        Ok(())
    }
}

fn pour<S: Sink>(files: &[&[u8]], order: &[usize], sink: &mut S) -> Result<Counts> {
    let mut next = Counts::default();
    let mut names = vec![0];
    let mut declared = FxHashSet::default();
    for &i in order {
        let mut shift = Shift {
            sink: &mut *sink,
            base: next,
            next,
            names: &mut names,
            declared: &mut declared,
        };
        let bytes = files[i];
        if blean::sniff(bytes) {
            blean::read(bytes, &mut shift)?;
        } else {
            ndjson::read(bytes, &mut shift)?;
        }
        next = shift.next;
    }
    Ok(next)
}

fn merge<S: Sink>(
    files: &[&[u8]],
    order: &[usize],
    root: Option<&str>,
    mut sink: S,
) -> Result<S::Output> {
    let Some((_, imports)) = order.split_last() else {
        return Err(corrupt("nothing to join"));
    };
    let mut m = meta(files[order[0]])?;
    if let Some(o) = m.as_object_mut() {
        o.remove("module");
        if let Some(root) = root {
            let mut n = Count(0);
            pour(files, imports, &mut n)?;
            o.insert(
                "view".into(),
                serde_json::json!({"module": root, "imported": n.0}),
            );
        }
    }
    sink.record(None, &Record::Meta(m.to_string().into()))?;
    let next = pour(files, order, &mut sink)?;
    sink.record(None, &Record::End(next))?;
    sink.finish()
}

/// Hashes what it writes.
struct Hashing<W> {
    inner: W,
    hash: blake3::Hasher,
}

impl<W: Write> Write for Hashing<W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let n = self.inner.write(buf)?;
        self.hash.update(&buf[..n]);
        Ok(n)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}

type Out = Hashing<BufWriter<File>>;

/// Export every module of `env` to its own file in `dir`, named after the module.
///
/// Ids count from the start in each file. A file holds every constant its module declares and
/// refers to its imports' constants by name, so joining the files gives a whole export,
/// up to numbering and order, plus the internal constants nothing needs. Returns the files in module order.
pub fn split(env: &Env, dir: &Path, blean: bool) -> Result<Vec<PathBuf>> {
    split_as(env, dir, blean, false)
}

/// Like [`split`], with each module written against what the module system shows it and
/// its interface in `dir/public`.
pub fn split_interfaces(env: &Env, dir: &Path, blean: bool) -> Result<Vec<PathBuf>> {
    split_as(env, dir, blean, true)
}

fn split_as(env: &Env, dir: &Path, blean: bool, interfaces: bool) -> Result<Vec<PathBuf>> {
    if blean {
        split_with(env, dir, "blean", interfaces, Blean::new)
    } else {
        split_with(env, dir, "ndjson", interfaces, Ndjson::new)
    }
}

fn split_with<S: Sink<Output = Out>>(
    env: &Env,
    dir: &Path,
    ext: &str,
    interfaces: bool,
    sink: impl Fn(Out) -> S,
) -> Result<Vec<PathBuf>> {
    let public = dir.join("public");
    std::fs::create_dir_all(if interfaces { &public } else { dir })?;
    let paths: Vec<PathBuf> = env
        .modules
        .iter()
        .map(|m| dir.join(format!("{m}.{ext}")))
        .collect();
    let files: Vec<(usize, bool, PathBuf)> = (0..paths.len())
        .flat_map(|m| {
            let shown = (interfaces && env.exported[m].is_some())
                .then(|| (m, true, public.join(format!("{}.{ext}", env.modules[m]))));
            shown.into_iter().chain([(m, false, paths[m].clone())])
        })
        .collect();
    let open = |p: &Path| -> Result<S> {
        Ok(sink(Hashing {
            inner: BufWriter::with_capacity(1 << 20, File::create(p)?),
            hash: blake3::Hasher::new(),
        }))
    };
    let Some((_, _, first)) = files.first() else {
        return Ok(paths);
    };
    let index: FxHashMap<&str, usize> = env
        .modules
        .iter()
        .enumerate()
        .map(|(i, m)| (m.as_str(), i))
        .collect();
    let mut whole: Vec<String> = Vec::with_capacity(paths.len());
    let mut shown: Vec<Option<String>> = vec![None; paths.len()];
    let mut ex = if interfaces {
        Exporter::restricted(env, open(first)?)
    } else {
        Exporter::per_module(env, open(first)?)
    };
    for (k, (m, interface, _)) in files.iter().enumerate() {
        let (m, name) = (*m, &env.modules[*m]);
        let module = interfaces && env.exported[m].is_some();
        let imports = env.imports[m]
            .iter()
            .filter(|i| !interface || i.exported)
            .map(|i| {
                let j = (index.get(i.module.as_str()).copied())
                    .filter(|&j| j < whole.len())
                    .ok_or_else(|| corrupt(format!("{name} imports unloaded {}", i.module)))?;
                let seen = shown[j]
                    .as_ref()
                    .filter(|_| module && (*interface || !i.all));
                Ok(serde_json::json!({
                    "name": i.module,
                    "blake3": seen.unwrap_or(&whole[j]),
                    "all": i.all,
                    "public": i.exported,
                    "meta": i.meta,
                }))
            })
            .collect::<Result<Vec<_>>>()?;
        let mut meta = serde_json::json!({"name": name, "imports": imports});
        if *interface {
            meta["public"] = true.into();
            meta["inside"] = ex.inside(m).map(|o| env.modules[o].as_str()).collect();
            ex.meta_with(Some(meta))?;
            ex.interface(m)?;
        } else {
            if let Some(h) = &shown[m] {
                meta["interface"] = h.as_str().into();
            }
            ex.meta_with(Some(meta))?;
            ex.module(m)?;
        }
        let Some((_, _, next)) = files.get(k + 1) else {
            break;
        };
        let mut out = ex.split(open(next)?)?;
        out.flush()?;
        let h = out.hash.finalize().to_hex().to_string();
        if *interface {
            shown[m] = Some(h);
        } else {
            whole.push(h);
        }
    }
    ex.finish()?.flush()?;
    Ok(paths)
}
