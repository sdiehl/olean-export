use crate::error::{at, corrupt, Error, Result};
use memmap2::{Mmap, MmapOptions};
use std::{fmt::Write as _, fs::File, path::Path};

const ARRAY: u8 = 246;
const SCALAR_ARRAY: u8 = 248;
const STRING: u8 = 249;
const MPZ: u8 = 250;
const THUNK: u8 = 251;
const TASK: u8 = 252;
const REF: u8 = 253;

/// Fields of the fixed-size header that precedes every compacted region.
#[derive(Debug, Clone, Default)]
pub struct Header {
    pub version: String,
    pub githash: String,
    pub gmp: bool,
}

#[derive(Debug)]
pub(crate) struct Part {
    pub(crate) base: u64,
    slot: usize,
    pub(crate) bytes: Mmap,
}

/// One module's compacted regions. Objects are addressed by the absolute pointers the
/// compactor wrote, and the parts of a `module` file share one address space.
#[derive(Debug)]
pub(crate) struct Image {
    pub(crate) parts: Vec<Part>,
    pub(crate) header: Header,
    pub(crate) root: u64,
}

/// The Lean releases whose object layouts this reader has been checked against.
pub const SUPPORTED: std::ops::RangeInclusive<u32> = 26..=35;

fn cstr(b: &[u8]) -> String {
    String::from_utf8_lossy(b.split(|&c| c == 0).next().unwrap_or_default()).into_owned()
}

impl Image {
    pub(crate) fn open(path: &Path) -> Result<Self> {
        let mut img = Self {
            parts: Vec::new(),
            header: Header::default(),
            root: 0,
        };
        img.push_part(path)?;
        Ok(img)
    }

    /// Open a module's `.olean`, adding its `.server` and `.private` parts if it is in the
    /// module system. The root is then the private part's, which sees all of them.
    pub(crate) fn open_module(path: &Path) -> Result<Self> {
        let mut img = Self::open(path)?;
        if img.scalar_u8(img.root, 0).map_err(at(path))? == 1 {
            img.push_part(&path.with_extension("olean.server"))?;
            img.push_part(&path.with_extension("olean.private"))?;
        }
        Ok(img)
    }

    pub(crate) fn push_part(&mut self, path: &Path) -> Result<()> {
        self.map(path).map_err(at(path))
    }

    fn map(&mut self, path: &Path) -> Result<()> {
        let file = File::open(path)?;
        // SAFETY: the map is read-only and lives as long as `self`. Rewriting an .olean while
        // it is being read is undefined behaviour, the same assumption Lean makes when it maps them.
        #[allow(unsafe_code)]
        let bytes = unsafe { MmapOptions::new().populate().map(&file)? };
        bytes.advise(memmap2::Advice::WillNeed)?;
        if bytes.len() < 96 || &bytes[..5] != b"olean" {
            return Err(Error::NotOlean);
        }
        if bytes[5] != 2 {
            return Err(Error::Format(bytes[5]));
        }
        let version = cstr(&bytes[7..40]);
        let minor = version
            .strip_prefix("4.")
            .and_then(|v| v.split('.').next()?.parse().ok());
        if !minor.is_some_and(|m| SUPPORTED.contains(&m)) {
            return Err(Error::UnsupportedLean(version));
        }
        self.header = Header {
            version,
            githash: cstr(&bytes[40..80]),
            gmp: bytes[6] & 1 == 1,
        };
        let base = le64(&bytes[80..88]);
        self.root = le64(&bytes[88..96]);
        let slot = self.slots();
        self.parts.push(Part { base, slot, bytes });
        Ok(())
    }

    /// One past the largest slot, where every 8-byte aligned object address has a slot.
    pub(crate) fn slots(&self) -> usize {
        self.parts.last().map_or(0, |p| p.slot + p.bytes.len() / 8)
    }

    /// A dense index for the object at `addr`, for memo tables.
    pub(crate) fn slot(&self, addr: u64) -> Result<usize> {
        self.locate(addr, 8).map(|(p, off)| p.slot + off / 8)
    }

    fn locate(&self, addr: u64, len: usize) -> Result<(&Part, usize)> {
        self.parts
            .iter()
            .find_map(|p| {
                let off = usize::try_from(addr.checked_sub(p.base)?).ok()?;
                (off.checked_add(len)? <= p.bytes.len()).then_some((p, off))
            })
            .ok_or_else(|| corrupt(format!("pointer {addr:#x} is outside the module")))
    }

    fn bytes(&self, addr: u64, len: usize) -> Result<&[u8]> {
        self.locate(addr, len)
            .map(|(p, off)| &p.bytes[off..off + len])
    }

    pub(crate) fn u64(&self, addr: u64) -> Result<u64> {
        self.bytes(addr, 8).map(le64)
    }

    pub(crate) fn u8(&self, addr: u64) -> Result<u8> {
        Ok(self.bytes(addr, 1)?[0])
    }

    pub(crate) fn tag(&self, o: u64) -> Result<u8> {
        self.u8(o + 7)
    }

    pub(crate) fn field(&self, o: u64, i: u64) -> Result<u64> {
        self.u64(o + 8 + 8 * i)
    }

    /// The `k`th byte of a constructor's scalar area, which follows its object fields.
    pub(crate) fn scalar_u8(&self, o: u64, k: u64) -> Result<u8> {
        let num_objs = u64::from(self.u8(o + 6)?);
        self.u8(o + 8 + 8 * num_objs + k)
    }

    pub(crate) fn scalar_u32(&self, o: u64) -> Result<u32> {
        let b = self.bytes(o + 8 + 8 * u64::from(self.u8(o + 6)?), 4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    /// The size in bytes of the object at `o`, calling `f` on each object it points to.
    pub(crate) fn children(&self, o: u64, mut f: impl FnMut(u64)) -> Result<u64> {
        let mut each = |from: u64, n: u64| -> Result<()> {
            for i in 0..n {
                let c = self.u64(from + 8 * i)?;
                if !is_scalar(c) {
                    f(c);
                }
            }
            Ok(())
        };
        let b = self.bytes(o + 4, 2)?;
        let cs_sz = u64::from(u16::from_le_bytes([b[0], b[1]]));
        let size = match self.tag(o)? {
            ARRAY => {
                let n = self.u64(o + 16)?;
                each(o + 24, n)?;
                24 + 8 * n
            }
            SCALAR_ARRAY => 24 + u64::from(self.u8(o + 6)?) * self.u64(o + 16)?,
            STRING => 32 + self.u64(o + 16)?,
            THUNK | TASK => {
                each(o + 8, 1)?;
                24
            }
            REF => {
                each(o + 8, 1)?;
                16
            }
            MPZ => cs_sz,
            t if t > MPZ => return Err(corrupt(format!("unexpected object tag {t} at {o:#x}"))),
            _ => {
                each(o + 8, u64::from(self.u8(o + 6)?))?;
                cs_sz
            }
        };
        Ok(size.next_multiple_of(8))
    }

    fn expect(&self, o: u64, tag: u8, what: &str) -> Result<()> {
        if is_scalar(o) || self.tag(o)? != tag {
            return Err(corrupt(format!("expected {what} at {o:#x}")));
        }
        Ok(())
    }

    pub(crate) fn str(&self, o: u64) -> Result<&str> {
        self.expect(o, STRING, "a string")?;
        let size = usize::try_from(self.u64(o + 8)?).map_err(corrupt)?;
        let bytes = self.bytes(o + 32, size.saturating_sub(1))?;
        std::str::from_utf8(bytes).map_err(corrupt)
    }

    pub(crate) fn array(&self, o: u64) -> Result<Vec<u64>> {
        self.expect(o, ARRAY, "an array")?;
        (0..self.u64(o + 8)?)
            .map(|i| self.u64(o + 24 + 8 * i))
            .collect()
    }

    pub(crate) fn list(&self, mut o: u64) -> Result<Vec<u64>> {
        let mut out = Vec::new();
        while !is_scalar(o) {
            out.push(self.field(o, 0)?);
            o = self.field(o, 1)?;
        }
        Ok(out)
    }

    pub(crate) fn nat_decimal(&self, o: u64) -> Result<String> {
        if is_scalar(o) {
            return Ok((o >> 1).to_string());
        }
        self.expect(o, MPZ, "a Nat")?;
        if !self.header.gmp {
            return Err(corrupt("big Nat literals need a Lean built with GMP"));
        }
        let b = self.bytes(o + 12, 4)?;
        let size = u64::from(i32::from_le_bytes([b[0], b[1], b[2], b[3]]).unsigned_abs());
        let mut digits = (0..size)
            .map(|i| self.u64(o + 24 + 8 * i))
            .collect::<Result<Vec<_>>>()?;
        Ok(decimal(&mut digits))
    }
}

pub(crate) const fn is_scalar(o: u64) -> bool {
    o & 1 == 1
}

pub(crate) fn small_nat(o: u64) -> Result<u64> {
    if is_scalar(o) {
        Ok(o >> 1)
    } else {
        Err(corrupt(format!(
            "expected a small Nat, found pointer {o:#x}"
        )))
    }
}

fn le64(b: &[u8]) -> u64 {
    let mut a = [0; 8];
    a.copy_from_slice(&b[..8]);
    u64::from_le_bytes(a)
}

fn decimal(limbs: &mut Vec<u64>) -> String {
    const CHUNK: u64 = 10_000_000_000_000_000_000;
    let mut parts = Vec::new();
    while limbs.iter().any(|&l| l != 0) {
        let mut rem = 0u128;
        for l in limbs.iter_mut().rev() {
            let cur = (rem << 64) | u128::from(*l);
            *l = u64::try_from(cur / u128::from(CHUNK)).expect("quotient fits");
            rem = cur % u128::from(CHUNK);
        }
        parts.push(u64::try_from(rem).expect("remainder fits"));
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
    }
    let mut s = parts.pop().unwrap_or(0).to_string();
    for p in parts.iter().rev() {
        let _ = write!(s, "{p:019}");
    }
    s
}
