//! Accepted stores: the declaration keys each checker has accepted, one section per checker,
//! so several checkers share one file.
//!
//! Layout: `MAGIC`, a little-endian `u32` section count, then per section a `u32` name length,
//! the checker name, a 32-byte tag the checker defines, a `u64` key count, and the sorted keys.

use crate::{
    error::{corrupt, Result},
    key::Key,
};
use std::{
    fs::{self, File},
    io::{self, Write},
    path::Path,
};

pub const MAGIC: &[u8; 8] = b"ACCEPT\0\x01";

/// One checker's section. A checker trusts its keys only while `tag` matches its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Section<'a> {
    pub checker: &'a str,
    pub tag: Key,
    pub keys: &'a [Key],
}

impl Section<'_> {
    #[must_use]
    pub fn contains(&self, k: &Key) -> bool {
        self.keys.binary_search(k).is_ok()
    }
}

fn take<'a>(b: &mut &'a [u8], n: usize) -> Result<&'a [u8]> {
    if b.len() < n {
        return Err(corrupt("accepted store: truncated"));
    }
    let (h, t) = b.split_at(n);
    *b = t;
    Ok(h)
}

fn word<const N: usize>(b: &mut &[u8]) -> Result<[u8; N]> {
    Ok(take(b, N)?.try_into().expect("length checked"))
}

/// The sections of a store, borrowing from `bytes`.
pub fn parse(bytes: &[u8]) -> Result<Vec<Section<'_>>> {
    let mut b = bytes;
    if take(&mut b, MAGIC.len())? != MAGIC {
        return Err(corrupt("not an accepted store"));
    }
    let n = u32::from_le_bytes(word(&mut b)?);
    let mut out = Vec::new();
    for _ in 0..n {
        let len = u32::from_le_bytes(word(&mut b)?) as usize;
        let checker = std::str::from_utf8(take(&mut b, len)?)
            .map_err(|_| corrupt("accepted store: checker name is not UTF-8"))?;
        let tag = word(&mut b)?;
        let count = usize::try_from(u64::from_le_bytes(word(&mut b)?))
            .map_err(|_| corrupt("accepted store: key count"))?;
        let bytes = count
            .checked_mul(32)
            .ok_or_else(|| corrupt("accepted store: key count"))?;
        let keys = take(&mut b, bytes)?.as_chunks().0;
        out.push(Section { checker, tag, keys });
    }
    if !b.is_empty() {
        return Err(corrupt("accepted store: trailing bytes"));
    }
    Ok(out)
}

/// Write `sections` in order. Each section's keys must be sorted.
pub fn write(mut w: impl Write, sections: &[Section<'_>]) -> io::Result<()> {
    let n = |x: usize| u32::try_from(x).map_err(|_| io::Error::other("too many sections"));
    w.write_all(MAGIC)?;
    w.write_all(&n(sections.len())?.to_le_bytes())?;
    for s in sections {
        w.write_all(&n(s.checker.len())?.to_le_bytes())?;
        w.write_all(s.checker.as_bytes())?;
        w.write_all(&s.tag)?;
        w.write_all(&(s.keys.len() as u64).to_le_bytes())?;
        s.keys.iter().try_for_each(|k| w.write_all(k))?;
    }
    Ok(())
}

/// Replace the store at `path` with `sections`, atomically: readers that map the old file
/// keep seeing it whole.
pub fn save(path: &Path, sections: &[Section<'_>]) -> io::Result<()> {
    if let Some(dir) = path.parent().filter(|d| !d.as_os_str().is_empty()) {
        fs::create_dir_all(dir)?;
    }
    let tmp = path.with_extension(format!("tmp.{}", std::process::id()));
    let mut f = io::BufWriter::new(File::create(&tmp)?);
    write(&mut f, sections)?;
    f.into_inner()
        .map_err(io::IntoInnerError::into_error)?
        .sync_all()?;
    fs::rename(&tmp, path)
}
