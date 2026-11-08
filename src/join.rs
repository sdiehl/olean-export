//! Per-module exports and joining them back into one. See docs/INCREMENTAL.md.

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

/// A per-module file's module name and its imports with their blake3 hashes.
fn module(meta: &Value) -> Result<(String, Vec<(String, String)>)> {
    let m = meta
        .get("module")
        .ok_or_else(|| corrupt("not a per-module export"))?;
    let s = |v: &Value| v.as_str().map(str::to_owned);
    let bad = || corrupt("bad module in meta");
    let name = m.get("name").and_then(s).ok_or_else(bad)?;
    let imports = m
        .get("imports")
        .and_then(Value::as_array)
        .ok_or_else(bad)?
        .iter()
        .map(|i| Some((s(i.get("name")?)?, s(i.get("blake3")?)?)))
        .collect::<Option<_>>()
        .ok_or_else(bad)?;
    Ok((name, imports))
}

/// Hex blake3 of an export's bytes, as per-module metas name their imports.
#[must_use]
pub fn hash(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

/// The order to join per-module `files` in, imports first. Fails unless every import of
/// every file is among them with the hash it was exported against.
pub fn order(files: &[&[u8]]) -> Result<Vec<usize>> {
    let mods = files
        .iter()
        .map(|b| module(&meta(b)?))
        .collect::<Result<Vec<_>>>()?;
    let mut by_name = FxHashMap::default();
    for (i, (n, _)) in mods.iter().enumerate() {
        if by_name.insert(n.as_str(), i).is_some() {
            return Err(corrupt(format!("module {n} given twice")));
        }
    }
    let hashes: Vec<String> = files.iter().map(|b| hash(b)).collect();
    let mut deps = Vec::with_capacity(files.len());
    for (n, imports) in &mods {
        let mut d = Vec::new();
        for (i, h) in imports {
            let &j = by_name
                .get(i.as_str())
                .ok_or_else(|| corrupt(format!("{n} imports {i}, which is not given")))?;
            if hashes[j] != *h {
                return Err(corrupt(format!("{n} was exported against another {i}")));
            }
            d.push(j);
        }
        deps.push(d);
    }
    let mut out = Vec::with_capacity(files.len());
    let mut state = vec![0u8; files.len()];
    for root in 0..files.len() {
        let mut stack = vec![(root, 0)];
        while let Some((i, k)) = stack.pop() {
            if k == 0 {
                match state[i] {
                    2 => continue,
                    1 => return Err(corrupt(format!("import cycle at {}", mods[i].0))),
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
pub fn join<S: Sink>(files: &[&[u8]], mut sink: S) -> Result<S::Output> {
    let order = order(files)?;
    let Some(&first) = order.first() else {
        return Err(corrupt("nothing to join"));
    };
    let mut m = meta(files[first])?;
    if let Some(o) = m.as_object_mut() {
        o.remove("module");
    }
    sink.record(None, &Record::Meta(m.to_string().into()))?;
    let mut next = Counts::default();
    let mut names = vec![0];
    let mut declared = FxHashSet::default();
    for i in order {
        let mut shift = Shift {
            sink: &mut sink,
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
    if blean {
        split_with(env, dir, "blean", Blean::new)
    } else {
        split_with(env, dir, "ndjson", Ndjson::new)
    }
}

fn split_with<S: Sink<Output = Out>>(
    env: &Env,
    dir: &Path,
    ext: &str,
    sink: impl Fn(Out) -> S,
) -> Result<Vec<PathBuf>> {
    std::fs::create_dir_all(dir)?;
    let paths: Vec<PathBuf> = env
        .modules
        .iter()
        .map(|m| dir.join(format!("{m}.{ext}")))
        .collect();
    let open = |p: &Path| -> Result<S> {
        Ok(sink(Hashing {
            inner: BufWriter::with_capacity(1 << 20, File::create(p)?),
            hash: blake3::Hasher::new(),
        }))
    };
    let Some(first) = paths.first() else {
        return Ok(paths);
    };
    let index: FxHashMap<&str, usize> = env
        .modules
        .iter()
        .enumerate()
        .map(|(i, m)| (m.as_str(), i))
        .collect();
    let mut hashes: Vec<String> = Vec::with_capacity(paths.len());
    let mut ex = Exporter::per_module(env, open(first)?);
    for m in 0..paths.len() {
        let imports = env.imports[m]
            .iter()
            .map(|i| {
                let h = index
                    .get(i.as_str())
                    .and_then(|&j| hashes.get(j))
                    .ok_or_else(|| corrupt(format!("{} imports unloaded {i}", env.modules[m])))?;
                Ok(serde_json::json!({"name": i, "blake3": h}))
            })
            .collect::<Result<Vec<_>>>()?;
        ex.meta_with(Some(
            serde_json::json!({"name": env.modules[m], "imports": imports}),
        ))?;
        ex.module(m)?;
        if m + 1 == paths.len() {
            break;
        }
        let mut out = ex.split(open(&paths[m + 1])?)?;
        out.flush()?;
        hashes.push(out.hash.finalize().to_hex().to_string());
    }
    ex.finish()?.flush()?;
    Ok(paths)
}
