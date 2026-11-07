# Changelog

## Unreleased

- Names print with `«»` where Lean needs it, and `-c` reads them back. `statement` renames binders that would shadow a constant or print as a keyword.
- `statement` names every axiom but only counts theorems from `--trust`ed modules.
- Read big Nat literals from Lean builds without GMP.
- The NDJSON reader parses each line in one pass, with clearer errors, about 30% faster.
- `just kernel` checks each fixture's statement cone with a kernel.

## 0.5.0 (2026-11-07)

- Add `compare`, which diffs two exports, NDJSON or blean, up to ids, order and binders.
- `-c` leaves theorem values outside the cone undecoded (`Env::load_cone`). `Kind::Thm` now holds a `Theorem` with an optional value.
- Add `statement`, which prints what a theorem's statement rests on, without proofs, minus `--trust`ed modules.
- `compare` parses in parallel: 48s instead of 176s on Mathlib.
- Add `--rss` to show peak memory.
- Test the fixtures and a cone against lean4export output.
- `Sink::record` takes the id each record defines, so a resumed NDJSON export continues its ids. `Error::Misuse` reports API misuse.
- Fix `Exporter::update` missing changed private constants, NDJSON escapes that differed from Lean's, unchecked ids in `compare`, and broken pipes reported as errors.
- Refuse `.olean.server` and `.olean.private` parts from a different Lean build than their `.olean`.

## 0.4.0 (2026-10-29)

- Add `Env::open` and `Env::reload`, which redecode only changed modules and keep ids stable.
- Add `Exporter::suspend`, `resume` and `update` to write only what a reload changed.

## 0.3.0 (2026-10-12)

- Walk terms and constant dependencies on explicit worklists, so no term depth or dependency chain can overflow a thread stack.
- Report a cyclic object graph as a corrupt olean instead of looping or overflowing.
- Remove `with_big_stack` and the 1 GB decoding and export threads it required. Callers can drop the wrapper and run `Exporter` on any thread.

## 0.2.0 (2026-10-08)

- Add `inspect` subcommand summarizing an olean's imports, constants and bytes per section.
- Add `-f blean`, a postcard binary form of the export with per-expression hashes, and `convert` between it and NDJSON.

## 0.1.0 (2026-10-04)

- Read Lean 4.26 to 4.35 `.olean` files and emit the lean4export 3.1.0 NDJSON stream.
- Export every constant reachable from a module, or only those named with `-c`.
- Decode modules in parallel into sharded hash-consing tables, with identical output for any `-j`.
- Map oleans into memory and stream the export through a reusable line buffer.
- Report malformed oleans, unsupported Lean releases and missing modules as typed errors.
- Add opt-in `mimalloc` feature installing mimalloc as the global allocator.
