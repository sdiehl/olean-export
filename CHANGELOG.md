# Changelog

## Unreleased

- Add `inspect` subcommand summarizing an olean's imports, constants and bytes per section.
- Add `-f blean`, a postcard binary form of the export with per-expression hashes, and `convert` between it and NDJSON.

## 0.1.0 (2026-10-04)

- Read Lean 4.26 to 4.35 `.olean` files and emit the lean4export 3.1.0 NDJSON stream.
- Export every constant reachable from a module, or only those named with `-c`.
- Decode modules in parallel into sharded hash-consing tables, with identical output for any `-j`.
- Map oleans into memory and stream the export through a reusable line buffer.
- Report malformed oleans, unsupported Lean releases and missing modules as typed errors.
- Add opt-in `mimalloc` feature installing mimalloc as the global allocator.
