use crate::{
    error::{at, Result},
    olean::{is_scalar, Header, Image},
};
use std::path::{Path, PathBuf};

const KINDS: [&str; 8] = [
    "axiom",
    "def",
    "theorem",
    "opaque",
    "quot",
    "inductive",
    "ctor",
    "recursor",
];

/// One entry of a module's import list.
#[derive(Debug, Clone)]
pub struct Import {
    pub module: String,
    pub all: bool,
    pub exported: bool,
    pub meta: bool,
}

/// A constant as the olean lists it, without its terms.
#[derive(Debug, Clone)]
pub struct Decl {
    pub name: String,
    pub kind: &'static str,
    /// `unsafe` or `partial`, or empty.
    pub safety: &'static str,
}

/// A slice of the module's data and the bytes only it reaches. Shared objects count toward
/// the first section that reaches them, in the order constants, extra names, imports, then
/// environment extensions.
#[derive(Debug, Clone)]
pub struct Section {
    pub name: String,
    pub items: usize,
    pub bytes: u64,
}

/// What one module's olean holds, read straight from its header and `ModuleData` without
/// decoding any terms.
#[derive(Debug, Clone)]
pub struct Summary {
    pub header: Header,
    pub parts: Vec<(PathBuf, u64)>,
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub consts: Vec<Decl>,
    pub extra: Vec<String>,
    pub sections: Vec<Section>,
}

impl Summary {
    pub fn open(path: &Path) -> Result<Self> {
        Self::read(path).map_err(at(path))
    }

    fn read(path: &Path) -> Result<Self> {
        let img = Image::open_module(path)?;
        let root = img.root;
        let is_module = img.parts.len() > 1;
        let paths = if is_module {
            vec![
                path.to_owned(),
                path.with_extension("olean.server"),
                path.with_extension("olean.private"),
            ]
        } else {
            vec![path.to_owned()]
        };
        let parts = paths
            .into_iter()
            .zip(&img.parts)
            .map(|(p, part)| (p, part.bytes.len() as u64))
            .collect();

        let field = |i| img.field(root, i);
        let [imports, consts, extra, entries] =
            [0, 2, 3, 4].map(|i| field(i).and_then(|o| img.array(o)));
        let imports: Vec<Import> = imports?
            .into_iter()
            .map(|i| {
                Ok(Import {
                    module: img.str_name(img.field(i, 0)?)?,
                    all: img.scalar_u8(i, 0)? != 0,
                    exported: img.scalar_u8(i, 1)? != 0,
                    meta: img.scalar_u8(i, 2)? != 0,
                })
            })
            .collect::<Result<_>>()?;
        let consts: Vec<Decl> = consts?
            .into_iter()
            .map(|c| decl(&img, c))
            .collect::<Result<_>>()?;
        let extra: Vec<String> = extra?
            .into_iter()
            .map(|n| img.str_name(n))
            .collect::<Result<_>>()?;

        let mut seen = vec![false; img.slots()];
        let mut section = |name: String, items: usize, roots: &[u64]| {
            Ok::<_, crate::Error>(Section {
                name,
                items,
                bytes: reach(&img, &mut seen, roots)?,
            })
        };
        let mut sections = vec![
            section("constants".into(), consts.len(), &[field(1)?, field(2)?])?,
            section("extra names".into(), extra.len(), &[field(3)?])?,
            section("imports".into(), imports.len(), &[field(0)?])?,
        ];
        for e in entries? {
            let name = img.str_name(img.field(e, 0)?)?;
            let items = img.array(img.field(e, 1)?)?.len();
            sections.push(section(name, items, &[e])?);
        }
        Ok(Self {
            header: img.header.clone(),
            parts,
            is_module,
            imports,
            consts,
            extra,
            sections,
        })
    }

    /// Total size of every part on disk.
    #[must_use]
    pub fn bytes(&self) -> u64 {
        self.parts.iter().map(|p| p.1).sum()
    }
}

fn decl(img: &Image, info: u64) -> Result<Decl> {
    let tag = img.tag(info)?;
    let val = img.field(info, 0)?;
    let flag = |k| Ok::<_, crate::Error>(img.scalar_u8(val, k)? != 0);
    let safety = match tag {
        1 => match img.scalar_u8(val, 0)? {
            0 => "unsafe",
            1 => "",
            _ => "partial",
        },
        0 | 3 | 6 if flag(0)? => "unsafe",
        5 | 7 if flag(1)? => "unsafe",
        _ => "",
    };
    Ok(Decl {
        name: img.str_name(img.field(img.field(val, 0)?, 0)?)?,
        kind: KINDS.get(usize::from(tag)).copied().unwrap_or("?"),
        safety,
    })
}

/// Bytes of the objects reachable from `roots` that no earlier call reached.
fn reach(img: &Image, seen: &mut [bool], roots: &[u64]) -> Result<u64> {
    let mut stack: Vec<u64> = roots.iter().copied().filter(|&o| !is_scalar(o)).collect();
    let mut bytes = 0;
    while let Some(o) = stack.pop() {
        let slot = img.slot(o)?;
        if !std::mem::replace(&mut seen[slot], true) {
            bytes += img.children(o, |c| stack.push(c))?;
        }
    }
    Ok(bytes)
}
