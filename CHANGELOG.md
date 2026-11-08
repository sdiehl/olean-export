# Changelog

## Unreleased

- Add `--per-module` exports and `join` to merge them.
- Add `keys`, closure keys per declaration (`key::Keys`).
- Add `accepted` store format shared by external checkers.
- Fix duplicate recursors when two modules declare one type.
- Escape names with `«»` like Lean, also in `-c`.
- `statement` counts trusted theorems instead of listing them.
- Read big Nat literals from Lean builds without GMP.
- NDJSON reading is 30% faster and checks id keys.
- CI type-checks the statement cones with nano-lean.

## 0.5.0 (2026-11-07)

- Add `compare` to diff two exports up to ids.
- `compare` parses in parallel, 48s vs 176s on Mathlib.
- `-c` leaves theorem values outside the cone undecoded.
- `Kind::Thm` holds a `Theorem` with an optional value.
- Add `statement`, a theorem's proof-free trusted base.
- Add `--rss` to show peak memory.
- Test fixtures and a cone against lean4export output.
- `Sink::record` takes ids, so resumed exports continue them.
- `Error::Misuse` reports API misuse.
- Fix `Exporter::update` missing changed private constants.
- Fix NDJSON escapes differing from Lean's.
- Fix unchecked ids in `compare`.
- Fix broken pipes reported as errors.
- Refuse olean parts from a different Lean build.

## 0.4.0 (2026-10-29)

- Add `Env::open` and `Env::reload`, redecoding only changed modules.
- Add `Exporter::suspend`, `resume` and `update` for reload diffs.

## 0.3.0 (2026-10-12)

- Walk terms and dependencies on worklists, never overflowing stacks.
- Report cyclic object graphs as corrupt oleans.
- Remove `with_big_stack`, `Exporter` runs on any thread.

## 0.2.0 (2026-10-08)

- Add `inspect`, summarizing an olean's imports, constants and sections.
- Add `-f blean` binary export with per-expression hashes.
- Add `convert` between blean and NDJSON.

## 0.1.0 (2026-10-04)

- Read Lean 4.26 to 4.35 oleans, emit lean4export NDJSON.
- Export a module's whole closure, or `-c` constants only.
- Decode modules in parallel, identical output for any `-j`.
- Map oleans into memory and stream the export.
- Report malformed oleans and missing modules as typed errors.
- Add opt-in `mimalloc` feature for the global allocator.
