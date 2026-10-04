# tiny-olean

Rust library to read Lean `.olean` files directly in Rust and emit the [lean4export](https://github.com/leanprover/lean4export) NDJSON stream for external kernel checkers without using Lean compiler directly.

The big idea is an `.olean` is already a compacted heap image of `lean.h` objects, so the reader walks those objects, hash-conses names, levels and expressions, and writes the same records lean4export would, in dependency order. But much faster.

The object layout is tied to the Lean release. This version reads olean format v2 as written by Lean 4.26 through 4.35, and refuses files from any other release rather than risk decoding them wrong. Damaged files produce an error, not a panic.

```bash
cargo build --release
cargo test
cargo run --example demo
```

## Example

[`examples/Hello.lean`](examples/Hello.lean) is compiled to an olean with plain `lean`:

```lean
def double (n : Nat) : Nat := n + n

theorem double_two : double 2 = 4 := rfl
```

```bash
lean -o Hello.olean Hello.lean
```

Export one theorem with everything it depends on, then check it with a kernel. Inside a Lake project, `lake env` sets `LEAN_PATH` for you, so you can run:

```bash
$ lake env tiny-olean Hello -c double_two -o hello.ndjson
654 modules, 65,373 constants decoded in 1.41s
36.82 KiB of NDJSON (138 names, 16 levels, 490 exprs) in 1.41s total, 11.99 MiB/s

$ sokonanoda --nat-extension --print-success-message --stdin < hello.ndjson
Checked 39 declarations with no errors
```

Without `-c` it exports every constant reachable from the module, like `lean4export Hello`.

## Performance

Modules decode in parallel on every core, and `-j N` sets the thread count. The output is identical for any `-j`.

Wall time:

| Target                    | lean4export | tiny-olean | Speedup |
| ------------------------- | ----------- | ---------- | ------- |
| Small model on `Lean`     | 18.3s       | 1.0s       | 18x     |
| Mathlib-dependent library | 1541s       | 15s        | 100x    |

Peak memory:

| Target                    | lean4export | tiny-olean |
| ------------------------- | ----------- | ---------- |
| Small model on `Lean`     | 1.3 GB      | 0.5 GB     |
| Mathlib-dependent library | 9.4 GB      | 4.2 GB     |

## License

MIT Licensed. Copyright 2026 Stephen Diehl. See [LICENSE](LICENSE) for details.
