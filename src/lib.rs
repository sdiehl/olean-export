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
mod export;
mod olean;

pub use env::{
    search_path, Binder, Const, Env, Expr, ExprId, Exprs, Hints, Kind, Level, LevelId, Name,
    NameId, QuotKind, Rule, Table, ANON, ZERO,
};
pub use export::Exporter;
pub use olean::{Header, SUPPORTED};

const STACK: usize = 1 << 30;

/// Run `f` on a thread with a stack deep enough for long application spines and binder chains.
pub fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("worker panicked")
}
