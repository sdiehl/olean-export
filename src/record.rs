//! One line of the export stream with every reference resolved to an output id. The
//! traversal in [`crate::Exporter`] produces these and every output format consumes them.
//!
//! The derived serde layout is also the blean format (see [`crate::blean`]), so variant
//! and field order are part of the format and must not change.

use crate::{
    env::{Binder, Hints, QuotKind},
    error::Result,
};
use serde::{Deserialize, Serialize};
use std::borrow::Cow;

/// Ids are implicit: names and levels count from 1 (0 is the anonymous name and the zero
/// level), expressions from 0, each in record order. Records only refer to earlier ones.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Record<'a> {
    /// The `meta` object as JSON. Always first.
    Meta(#[serde(borrow)] Cow<'a, str>),
    NameStr {
        pre: u32,
        #[serde(borrow)]
        str: Cow<'a, str>,
    },
    NameNum {
        pre: u32,
        i: u64,
    },
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
    BVar(u64),
    Sort(u32),
    Const {
        name: u32,
        us: Vec<u32>,
    },
    App {
        fun: u32,
        arg: u32,
    },
    Lam(Binding),
    Pi(Binding),
    Let {
        name: u32,
        ty: u32,
        value: u32,
        body: u32,
        nondep: bool,
    },
    /// Decimal digits.
    Nat(#[serde(borrow)] Cow<'a, str>),
    Str(#[serde(borrow)] Cow<'a, str>),
    Proj {
        type_name: u32,
        idx: u64,
        struct_: u32,
    },
    /// lean4export's metadata wrapper, which kernels read as the wrapped term.
    MData(u32),
    Decl(Decl),
    /// Always last.
    End(Counts),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Binding {
    pub info: Binder,
    pub name: u32,
    pub ty: u32,
    pub body: u32,
}

/// Records written so far for each table, which is also the next id each hands out. Fixed
/// width on the wire, so a blean file ends with these as three little-endian `u32`s.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counts {
    #[serde(with = "postcard::fixint::le")]
    pub names: u32,
    #[serde(with = "postcard::fixint::le")]
    pub levels: u32,
    #[serde(with = "postcard::fixint::le")]
    pub exprs: u32,
}

impl Default for Counts {
    fn default() -> Self {
        Self {
            names: 1,
            levels: 1,
            exprs: 0,
        }
    }
}

impl Record<'_> {
    /// Which table the record adds to, if any.
    #[must_use]
    pub const fn table(&self) -> Option<Table> {
        match self {
            Self::NameStr { .. } | Self::NameNum { .. } => Some(Table::Names),
            Self::Succ(_) | Self::Max(..) | Self::IMax(..) | Self::Param(_) => Some(Table::Levels),
            Self::Meta(_) | Self::Decl(_) | Self::End(_) => None,
            _ => Some(Table::Exprs),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Table {
    Names,
    Levels,
    Exprs,
}

impl Counts {
    /// Take the id of `r` if it defines a name, level or expression.
    pub fn assign(&mut self, r: &Record<'_>) -> Option<u32> {
        let next = match r.table()? {
            Table::Names => &mut self.names,
            Table::Levels => &mut self.levels,
            Table::Exprs => &mut self.exprs,
        };
        *next += 1;
        Some(*next - 1)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Safety {
    Safe,
    Unsafe,
    Partial,
}

/// The fields every declaration starts with.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Head {
    pub name: u32,
    pub level_params: Vec<u32>,
    pub ty: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Decl {
    /// `all` is never written by olean-export, but some lean4export versions write it.
    Axiom {
        head: Head,
        is_unsafe: bool,
        all: Option<Vec<u32>>,
    },
    Def {
        head: Head,
        value: u32,
        hints: Hints,
        safety: Safety,
        all: Vec<u32>,
    },
    Thm {
        head: Head,
        value: u32,
        all: Vec<u32>,
    },
    Opaque {
        head: Head,
        value: u32,
        is_unsafe: bool,
        all: Option<Vec<u32>>,
    },
    Quot {
        head: Head,
        kind: QuotKind,
    },
    Inductive {
        types: Vec<IndType>,
        ctors: Vec<IndCtor>,
        recs: Vec<IndRec>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndType {
    pub head: Head,
    pub is_unsafe: bool,
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<u32>,
    pub ctors: Vec<u32>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_reflexive: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndCtor {
    pub head: Head,
    pub is_unsafe: bool,
    pub induct: u32,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndRec {
    pub head: Head,
    pub is_unsafe: bool,
    pub all: Vec<u32>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<IndRule>,
    pub k: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndRule {
    pub ctor: u32,
    pub nfields: u64,
    pub rhs: u32,
}

/// A destination for records.
pub trait Sink {
    type Output;
    fn record(&mut self, r: &Record<'_>) -> Result<()>;
    fn finish(self) -> Result<Self::Output>;
}
