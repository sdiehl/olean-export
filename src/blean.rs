//! blean, the binary export format.
//!
//! [`MAGIC`], then every [`Record`] in order, postcard encoded, each expression record
//! followed by its [`Info`], ending with [`Record::End`]. Strings decode without copying,
//! so a memory-mapped file is read in place.

use crate::{
    error::{corrupt, Result},
    info::{Info, Tracker},
    record::{Counts, Record, Sink, Table},
};
use std::io::Write;

/// File signature; the final byte is the format version.
pub const MAGIC: [u8; 8] = *b"BLEAN\0\0\x01";

/// Writes records as blean.
#[derive(Debug)]
pub struct Blean<W: Write> {
    out: W,
    buf: Vec<u8>,
    info: Tracker,
    started: bool,
}

impl<W: Write> Blean<W> {
    pub fn new(out: W) -> Self {
        Self {
            out,
            buf: Vec::new(),
            info: Tracker::new(),
            started: false,
        }
    }
}

impl<W: Write> Sink for Blean<W> {
    type Output = W;

    fn record(&mut self, r: &Record<'_>) -> Result<()> {
        if !self.started {
            self.out.write_all(&MAGIC)?;
            self.started = true;
        }
        let mut buf = postcard::to_extend(r, std::mem::take(&mut self.buf))?;
        if let Some(info) = self.info.observe(r)? {
            buf = postcard::to_extend(&info, buf)?;
        }
        self.out.write_all(&buf)?;
        buf.clear();
        self.buf = buf;
        Ok(())
    }

    fn finish(mut self) -> Result<W> {
        self.out.flush()?;
        Ok(self.out)
    }
}

/// Whether `bytes` starts like a blean file.
#[must_use]
pub fn sniff(bytes: &[u8]) -> bool {
    bytes.starts_with(&MAGIC)
}

/// The table sizes a complete blean file declares in its last 12 bytes, for presizing
/// before reading. [`entries`] checks them against the records.
pub fn counts(bytes: &[u8]) -> Result<Counts> {
    let tail = bytes
        .len()
        .checked_sub(12)
        .filter(|_| sniff(bytes))
        .map(|at| &bytes[at..])
        .ok_or_else(|| corrupt("not a blean file"))?;
    Ok(postcard::from_bytes(tail)?)
}

/// The records of a complete blean file with each expression's info.
///
/// Strings borrow from `bytes`. Fails on a missing signature, a truncated stream, bytes
/// after the end, or end counts that disagree with the records before them.
pub fn entries(bytes: &[u8]) -> Result<Entries<'_>> {
    let rest = bytes
        .strip_prefix(&MAGIC)
        .ok_or_else(|| corrupt("not a blean file"))?;
    Ok(Entries {
        rest,
        next: Counts::default(),
        done: false,
    })
}

/// Iterator returned by [`entries`].
#[derive(Debug)]
pub struct Entries<'b> {
    rest: &'b [u8],
    next: Counts,
    done: bool,
}

impl<'b> Entries<'b> {
    fn step(&mut self) -> Result<(Record<'b>, Option<Info>)> {
        let (r, rest) = postcard::take_from_bytes::<Record<'b>>(self.rest)?;
        self.rest = rest;
        if let Record::End(counts) = r {
            self.done = true;
            if counts != self.next || !rest.is_empty() {
                return Err(corrupt("blean: bad end record"));
            }
            return Ok((r, None));
        }
        self.next.assign(&r);
        let info = if r.table() == Some(Table::Exprs) {
            let (info, rest) = postcard::take_from_bytes::<Info>(self.rest)?;
            self.rest = rest;
            Some(info)
        } else {
            None
        };
        Ok((r, info))
    }
}

impl<'b> Iterator for Entries<'b> {
    type Item = Result<(Record<'b>, Option<Info>)>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        let r = self.step();
        self.done |= r.is_err();
        Some(r)
    }
}

/// Replay a complete blean file into `sink`.
pub fn read<S: Sink>(bytes: &[u8], mut sink: S) -> Result<S::Output> {
    for e in entries(bytes)? {
        sink.record(&e?.0)?;
    }
    sink.finish()
}
