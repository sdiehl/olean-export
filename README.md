# tiny-olean

Read Lean 4 `.olean` files directly in Rust and emit the [lean4export](https://github.com/leanprover/lean4export) NDJSON stream for external kernel checkers such as [nanoda](https://github.com/ammkrn/nanoda_lib), without starting Lean. An `.olean` is a compacted heap image of `lean.h` objects, so the reader walks those objects, hash-conses names, levels and expressions, and writes the same records lean4export would, in dependency order.

The object layout is tied to the Lean release. This version targets olean format v2 as written by Lean 4.34 and 4.35.

```bash
cargo build --release
cargo test
cargo run --example demo
```

## Example

Compile a Lean file to an olean with plain `lean`:

```lean
-- Hello.lean
def double (n : Nat) : Nat := n + n

theorem double_two : double 2 = 4 := rfl
```

```bash
lean -o Hello.olean Hello.lean
export LEAN_PATH=.:$(lean --print-prefix)/lib/lean
```

Export one theorem with everything it depends on, then check it with a kernel:

```bash
$ tiny-olean Hello -c double_two -o hello.ndjson
654 modules, 65,373 constants decoded in 1.41s
36.82 KiB of NDJSON (138 names, 16 levels, 490 exprs) in 1.41s total, 11.99 MiB/s

$ head -3 hello.ndjson
{"meta":{"exporter":{"name":"tiny-olean","version":"0.1.0"},"format":{"version":"3.1.0"},...}}
{"in":1,"str":{"pre":0,"str":"Eq"}}
{"in":2,"str":{"pre":1,"str":"refl"}}

$ sokonanoda --nat-extension --stdin < hello.ndjson
Checked 39 declarations with no errors
```

Without `-c` it exports every constant reachable from the module, like `lean4export Hello`. Inside a Lake project, `lake env` sets `LEAN_PATH` for you:

```bash
lake env tiny-olean Mathlib -o mathlib.ndjson
```

## Performance

Wall time:

| Target                    | lean4export | tiny-olean | Speedup |
| ------------------------- | ----------- | ---------- | ------- |
| Small model on `Lean`     | 18.3s       | 4.5s       | 4x      |
| Mathlib-dependent library | 1541s       | 64s        | 24x     |

Peak memory:

| Target                    | lean4export | tiny-olean |
| ------------------------- | ----------- | ---------- |
| Small model on `Lean`     | 1.3 GB      | 0.7 GB     |
| Mathlib-dependent library | 9.4 GB      | 5.2 GB     |

## License

MIT Licensed. Copyright 2026 Stephen Diehl. See [LICENSE](LICENSE) for details.
