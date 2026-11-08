# olean-export

Rust library for reading and manipulating `.olean` files directly in Rust and emit the [lean4export](https://github.com/leanprover/lean4export) NDJSON stream for external kernel checkers without using Lean compiler directly.

Mostly designed around the ideas of having efficient external binary formats, doing incremental and transitive-cone checking.

The big idea is an `.olean` is already a compacted heap image of `lean.h` objects, so the reader walks those objects, hash-conses names, levels and expressions, and writes the same records lean4export would, in dependency order. But much faster.

The object layout is tied to the Lean release. This version reads olean format v2 as written by Lean 4.26 through 4.35, and refuses files from any other release.

```bash
cargo install olean-export
```

Add `--features mimalloc` to build with the mimalloc allocator.

## Example

[`examples/Hello.lean`](examples/Hello.lean) is compiled to an olean with plain `lean`:

```lean
def double (n : Nat) : Nat := n + n

theorem double_two : double 2 = 4 := rfl
```

```bash
lean -o Hello.olean Hello.lean
```

Export one theorem with everything it depends on, then check it with a kernel such as [nano-lean](https://github.com/sdiehl/nano-lean). Inside a Lake project, `lake env` sets `LEAN_PATH` for you, so you can run:

```bash
$ lake env olean-export Hello -c double_two -o hello.ndjson
654 modules, 65,373 constants decoded in 1.41s
36.82 KiB of NDJSON (138 names, 16 levels, 490 exprs) in 1.41s total, 11.99 MiB/s

$ nl-fast hello.ndjson
import 1.23ms arena 0 MiB, 39 decls 490 exprs 138 names 16 levels
experimental checks 967.17µs: 39 attempted, 0 failures, 0 fallbacks
bridged quot 0 ind 7 ctor 8 rec 7
```

## BLean

Blean is a new binary format that is more efficient to mmap and read than NDJSON.

Add `-f blean` for the same stream in a compact binary form, see [docs/BLEAN.md](docs/BLEAN.md).

```bash
lake env olean-export Hello -c double_two -f blean -o hello.blean
```

## Cone Export

A cone is a set of constants plus everything they mention. Without `-c` the export is the cone of every constant in the loaded modules, like `lean4export`.

- `-c NAME` (repeatable) exports the full cone of `NAME`, proofs included. Only theorem values inside the cone are decoded, the rest stay in their oleans.
- `statement -c NAME` follows only the statement: types, definition bodies and whole inductive families, no proofs. Theorems it reaches are taken as stated. It prints raw terms with source lines for review (`-m N` cuts long terms), or with `-f ndjson|blean` exports the cone with theorems as axioms for a checker.
- `statement --trust MODULES` leaves out what those modules, or modules under them, define, so you can review the trusted base of a Tau Ceti theorem without reading all of Tau Ceti.

```bash
lake env olean-export Mathlib -c Fin.insertNth_apply_succAbove -f blean -o thm.blean
lake env olean-export statement FLT -c THEOREM --trust Init,Std,Lean,Mathlib
```

## Incremental

`--per-module DIR` writes one export per module, pinned to its imports by hash, and `join` merges them back into one. `keys` prints a closure key per declaration, and `accepted` lists a store of keys checkers have already accepted.

```bash
lake env olean-export Mathlib --per-module out/
olean-export join out/*.ndjson -o mathlib.ndjson
```

## Inspect

`inspect` summarizes an olean's imports, constants and bytes per section. `-c` lists every constant.

```bash
$ olean-export inspect tests/cases/build/Top.olean
Lean 4.35.0-rc3 (470d5ce1400764999581fd26d5d72b00d990b0f4), gmp
    39.64 KiB  tests/cases/build/Top.olean

imports (1)
  Base

constants (24): 8 def, 6 ctor, 4 inductive, 4 recursor, 2 theorem

      bytes   share   items  section
  32.43 KiB   81.8%      24  constants
   1.66 KiB    4.2%       7  Lean.declRangeExt
   1.09 KiB    2.8%      24  _private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt
   ...
```

## Compare

`compare` diffs two exports, NDJSON or blean, ignoring record order, ids and binders.

```bash
$ lean4export Top > want.ndjson
$ olean-export Top -f blean -o got.blean
$ olean-export compare want.ndjson got.blean
33 / 33 declarations: 0 only in the first, 0 only in the second, 0 differ, 0 duplicate
```

## Performance

Modules decode in parallel on every core, and `-j N` sets the thread count. The output is identical for any `-j`. `--rss` shows peak resident memory.

Wall time:

| Target                     | lean4export | olean-export | Speedup |
| -------------------------- | ----------- | ------------ | ------- |
| Small model on `Lean`      | 18.3s       | 1.0s         | 18x     |
| All of Mathlib             | 1526s       | 18s          | 85x     |
| One Mathlib theorem (`-c`) | 16.5s       | 5.3s         | 3x      |

Peak memory:

| Target                     | lean4export | olean-export |
| -------------------------- | ----------- | ------------ |
| Small model on `Lean`      | 1.3 GB      | 0.5 GB       |
| All of Mathlib             | 9.4 GB      | 4.3 GB       |
| One Mathlib theorem (`-c`) | 5.6 GB      | 2.0 GB       |

Mathlib is on Lean 4.35.0 (712,205 declarations, identical under `compare`), and the theorem is `Fin.insertNth_apply_succAbove`.

## License

MIT Licensed. Copyright 2026 Stephen Diehl. See [LICENSE](LICENSE) for details.
