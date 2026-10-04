//! Read Lean 4 .olean files directly in Rust and emit the lean4export NDJSON stream for external kernel checkers.

/// Greet by name.
#[must_use]
pub fn greet(name: &str) -> String {
    format!("hello, {name}")
}
