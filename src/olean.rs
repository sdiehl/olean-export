use memmap2::{Mmap, MmapOptions};
use std::{fmt::Write as _, fs::File, io, path::Path};

const ARRAY: u8 = 246;
const STRING: u8 = 249;
const MPZ: u8 = 250;

/// Fields of the fixed-size header that precedes every compacted region.
#[derive(Debug, Clone, Default)]
pub struct Header {
    pub version: String,
    pub githash: String,
    pub gmp: bool,
}

#[derive(Debug)]
struct Part {
    base: u64,
    slot: usize,
    bytes: Mmap,
}

/// One module's compacted regions. Objects are addressed by the absolute pointers the
/// compactor wrote, and the parts of a `module` file share one address space.
#[derive(Debug)]
pub(crate) struct Image {
    parts: Vec<Part>,
    pub(crate) header: Header,
    pub(crate) root: u64,
}

fn invalid(path: &Path, msg: &str) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("{}: {msg}", path.display()),
    )
}

fn cstr(b: &[u8]) -> String {
    String::from_utf8_lossy(b.split(|&c| c == 0).next().unwrap_or_default()).into_owned()
}

impl Image {
    pub(crate) fn open(path: &Path) -> io::Result<Self> {
        let mut img = Self {
            parts: Vec::new(),
            header: Header::default(),
            root: 0,
        };
        img.push_part(path)?;
        Ok(img)
    }

    pub(crate) fn push_part(&mut self, path: &Path) -> io::Result<()> {
        let file = File::open(path)?;
        // SAFETY: the map is read-only and lives as long as `self`. Rewriting an .olean while
        // it is being read is undefined behaviour, the same assumption Lean makes when it maps them.
        #[allow(unsafe_code)]
        let bytes = unsafe { MmapOptions::new().populate().map(&file)? };
        bytes.advise(memmap2::Advice::WillNeed)?;
        if bytes.len() < 96 || &bytes[..5] != b"olean" {
            return Err(invalid(path, "not an olean file"));
        }
        let root_at = match bytes[5] {
            2 => 88,
            3 => 96,
            v => return Err(invalid(path, &format!("unsupported olean version {v}"))),
        };
        self.header = Header {
            version: cstr(&bytes[7..40]),
            githash: cstr(&bytes[40..80]),
            gmp: bytes[6] & 1 == 1,
        };
        let base = le64(&bytes[80..88]);
        self.root = le64(&bytes[root_at..root_at + 8]);
        let slot = self.slots();
        self.parts.push(Part { base, slot, bytes });
        Ok(())
    }

    /// One past the largest slot, where every 8-byte aligned object address has a slot.
    pub(crate) fn slots(&self) -> usize {
        self.parts.last().map_or(0, |p| p.slot + p.bytes.len() / 8)
    }

    /// A dense index for the object at `addr`, for memo tables.
    pub(crate) fn slot(&self, addr: u64) -> usize {
        for p in &self.parts {
            if let Some(off) = addr.checked_sub(p.base) {
                let off = usize::try_from(off).unwrap_or(usize::MAX);
                if off < p.bytes.len() {
                    return p.slot + off / 8;
                }
            }
        }
        panic!("pointer {addr:#x} is outside every region of this module")
    }

    fn bytes(&self, addr: u64, len: usize) -> &[u8] {
        for p in &self.parts {
            if let Some(off) = addr.checked_sub(p.base) {
                let off = usize::try_from(off).unwrap_or(usize::MAX);
                if let Some(b) = p.bytes.get(off..off.saturating_add(len)) {
                    return b;
                }
            }
        }
        panic!("pointer {addr:#x} is outside every region of this module")
    }

    pub(crate) fn u64(&self, addr: u64) -> u64 {
        le64(self.bytes(addr, 8))
    }

    pub(crate) fn u8(&self, addr: u64) -> u8 {
        self.bytes(addr, 1)[0]
    }

    pub(crate) fn tag(&self, o: u64) -> u8 {
        self.u8(o + 7)
    }

    pub(crate) fn field(&self, o: u64, i: u64) -> u64 {
        self.u64(o + 8 + 8 * i)
    }

    /// The `k`th byte of a constructor's scalar area, which follows its object fields.
    pub(crate) fn scalar_u8(&self, o: u64, k: u64) -> u8 {
        let num_objs = u64::from(self.u8(o + 6));
        self.u8(o + 8 + 8 * num_objs + k)
    }

    pub(crate) fn scalar_u32(&self, o: u64) -> u32 {
        let b = self.bytes(o + 8 + 8 * u64::from(self.u8(o + 6)), 4);
        u32::from_le_bytes([b[0], b[1], b[2], b[3]])
    }

    pub(crate) fn str(&self, o: u64) -> &str {
        assert_eq!(self.tag(o), STRING, "expected a string object");
        let size = usize::try_from(self.u64(o + 8)).expect("string size");
        let bytes = self.bytes(o + 32, size.saturating_sub(1));
        std::str::from_utf8(bytes).expect("olean strings are UTF-8")
    }

    pub(crate) fn array(&self, o: u64) -> impl Iterator<Item = u64> + '_ {
        assert_eq!(self.tag(o), ARRAY, "expected an array object");
        (0..self.u64(o + 8)).map(move |i| self.u64(o + 24 + 8 * i))
    }

    pub(crate) fn list(&self, mut o: u64) -> Vec<u64> {
        let mut out = Vec::new();
        while !is_scalar(o) {
            out.push(self.field(o, 0));
            o = self.field(o, 1);
        }
        out
    }

    pub(crate) fn nat_decimal(&self, o: u64) -> String {
        if is_scalar(o) {
            return (o >> 1).to_string();
        }
        assert_eq!(self.tag(o), MPZ, "expected a Nat");
        assert!(self.header.gmp, "only GMP bignum encoding is supported");
        let b = self.bytes(o + 12, 4);
        let size = u64::from(i32::from_le_bytes([b[0], b[1], b[2], b[3]]).unsigned_abs());
        let mut digits: Vec<u64> = (0..size).map(|i| self.u64(o + 24 + 8 * i)).collect();
        decimal(&mut digits)
    }
}

pub(crate) const fn is_scalar(o: u64) -> bool {
    o & 1 == 1
}

pub(crate) fn small_nat(o: u64) -> u64 {
    assert!(is_scalar(o), "unexpected bignum in a small Nat field");
    o >> 1
}

fn le64(b: &[u8]) -> u64 {
    u64::from_le_bytes(b.try_into().expect("eight bytes"))
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
