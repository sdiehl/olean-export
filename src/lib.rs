//! Read Lean 4 `.olean` files directly and emit the lean4export stream, as NDJSON or in a
//! compact binary form (blean), without starting Lean.
#![allow(
    clippy::missing_errors_doc,
    clippy::redundant_pub_crate,
    clippy::too_many_lines,
    clippy::missing_panics_doc,
    clippy::module_name_repetitions,
    clippy::similar_names,
    clippy::many_single_char_names
)]

pub mod blean;
mod env;
mod error;
mod export;
pub mod info;
mod inspect;
pub mod ndjson;
mod olean;
pub mod record;

pub use env::{
    resolve, search_path, Binder, Body, Const, Ctor, Defn, Env, Expr, ExprId, Exprs, Hints, Id,
    Inductive, Kind, Level, LevelId, Name, NameId, QuotKind, Rec, Rule, Table, ANON, ZERO,
};
pub use error::{Error, Result};
pub use export::Exporter;
pub use info::Info;
pub use inspect::{Decl, Import, Section, Summary};
pub use olean::{Header, SUPPORTED};
pub use record::{Counts, Record, Sink};
