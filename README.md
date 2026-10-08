# olean-export

Rust library to read Lean `.olean` files directly in Rust and emit the [lean4export](https://github.com/leanprover/lean4export) NDJSON stream for external kernel checkers without using Lean compiler directly.

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

Without `-c` it exports every constant reachable from the module, like `lean4export Hello`.

## BLean

Blean is a new binary format that is more efficient to mmap and read than NDJSON.

Add `-f blean` for the same stream in a compact binary form, see [docs/README.md](docs/README.md).

```bash
lake env olean-export Hello -c double_two -f blean -o hello.blean
```

## Performance

Modules decode in parallel on every core, and `-j N` sets the thread count. The output is identical for any `-j`.

Wall time:

| Target                    | lean4export | olean-export | Speedup |
| ------------------------- | ----------- | ------------ | ------- |
| Small model on `Lean`     | 18.3s       | 1.0s         | 18x     |
| Mathlib-dependent library | 1541s       | 15s          | 100x    |

Peak memory:

| Target                    | lean4export | olean-export |
| ------------------------- | ----------- | ------------ |
| Small model on `Lean`     | 1.3 GB      | 0.5 GB       |
| Mathlib-dependent library | 9.4 GB      | 4.2 GB       |

## Inspect

`inspect` summarizes one module's olean, by name or path, without decoding any terms: the Lean release, the module system parts, imports, constant kinds, and how many bytes each section and environment extension holds. Shared objects count toward the first section that reaches them, constants first. Pass `-c` to list every constant.

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

## License

MIT Licensed. Copyright 2026 Stephen Diehl. See [LICENSE](LICENSE) for details.
