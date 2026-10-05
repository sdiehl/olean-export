//! Read Lean 4 `.olean` files directly and emit the lean4export NDJSON stream, without
//! starting Lean.
#![allow(
    clippy::missing_errors_doc,
    clippy::redundant_pub_crate,
    clippy::too_many_lines,
    clippy::missing_panics_doc,
    clippy::module_name_repetitions,
    clippy::similar_names,
    clippy::many_single_char_names
)]

mod env;
mod error;
mod export;
mod inspect;
mod olean;

pub use env::{
    resolve, search_path, Binder, Body, Const, Ctor, Defn, Env, Expr, ExprId, Exprs, Hints, Id,
    Inductive, Kind, Level, LevelId, Name, NameId, QuotKind, Rec, Rule, Table, ANON, ZERO,
};
pub use error::{Error, Result};
pub use export::{Counts, Exporter};
pub use inspect::{Decl, Import, Section, Summary};
pub use olean::{Header, SUPPORTED};

const STACK: usize = 1 << 30;

/// Run `f` on a thread with a stack deep enough for long application spines and binder chains,
/// re-raising its panic if it has one. [`Exporter`] recurses over terms, so run it inside this.
pub fn with_big_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(s, f)
            .expect("spawn")
            .join()
            .unwrap_or_else(|e| std::panic::resume_unwind(e))
    })
}
