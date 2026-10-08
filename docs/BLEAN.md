# blean

A binary form of the lean4export 3.1.0 stream: the same records in the same order, without text to parse.

```
"BLEAN\0\0\x01"  record*  End
```

Every record is a [postcard](https://postcard.jamesmunns.com/wire-format) encoding of `Record` in [`src/record.rs`](../src/record.rs), whose variant and field order is the format. Each expression record is followed by its `Info`.

| # | Record                                | #  | Record                                  |
| - | ------------------------------------- | -- | --------------------------------------- |
| 0 | `Meta(str)`, the NDJSON `meta` object | 10 | `App { fun, arg }`                      |
| 1 | `NameStr { pre, str }`                | 11 | `Lam(Binding)`                          |
| 2 | `NameNum { pre, i }`                  | 12 | `Pi(Binding)`                           |
| 3 | `Succ(l)`                             | 13 | `Let { name, ty, value, body, nondep }` |
| 4 | `Max(l, l)`                           | 14 | `Nat(decimal str)`                      |
| 5 | `IMax(l, l)`                          | 15 | `Str(str)`                              |
| 6 | `Param(name)`                         | 16 | `Proj { type_name, idx, struct_ }`      |
| 7 | `BVar(u64)`                           | 17 | `MData(e)`                              |
| 8 | `Sort(l)`                             | 18 | `Decl(Decl)`                            |
| 9 | `Const { name, us }`                  | 19 | `End { names, levels, exprs }`          |

Ids are implicit and dense, in record order: names and levels from 1 (0 is anonymous and zero), expressions from 0. Records only refer to earlier ids.

`End` counts are fixed-width little-endian `u32`, so the last 12 bytes of a file give the table sizes.

`Info { hash: u64 le, loose_bvar_range: varint, flags: u8 }` with flags bit 0 has-level-param and bit 1 has-fvar (never set). `hash` is `xxh3_64(tag ++ parts)`, child hashes and integers as `u64` le, strings as UTF-8, binder names and info ignored:

| Tag | Node  | Parts      | Tag | Node  | Parts             |
| --- | ----- | ---------- | --- | ----- | ----------------- |
| 0   | anon  |            | 9   | sort  | l                 |
| 1   | str   | pre, bytes | 10  | const | name, us...       |
| 2   | num   | pre, i     | 11  | app   | fun, arg          |
| 3   | zero  |            | 12  | lam   | ty, body          |
| 4   | succ  | l          | 13  | pi    | ty, body          |
| 5   | max   | a, b       | 14  | let   | ty, value, body   |
| 6   | imax  | a, b       | 15  | nat   | digits            |
| 7   | param | name       | 16  | str   | bytes             |
| 8   | bvar  | i          | 17  | proj  | struct, name, idx |

`MData` takes the info of the term it wraps.

```bash
olean-export Mathlib -f blean -o mathlib.blean
olean-export convert mathlib.ndjson -o mathlib.blean   # and back
```
