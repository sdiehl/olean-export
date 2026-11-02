# blean

A binary form of the lean4export 3.1.0 stream: the same records in the same order, without text to parse.

```
"BLEAN\0\0\x01"  record*  End
```

Every record is a [postcard](https://postcard.jamesmunns.com/wire-format) encoding of `Record` in [`src/record.rs`](../src/record.rs), whose variant and field order is the format. Each expression record is followed by its `Info`. Sizes count the whole record including its tag byte: a varint `u32` is 8-40 bits, a varint `u64` 8-80, and a string of n bytes is a length varint plus 8n.

| #  | Record                                  | Size (bits)            |
| -- | --------------------------------------- | ---------------------- |
| 0  | `Meta(str)`, the NDJSON `meta` object   | 16-48 + 8n             |
| 1  | `NameStr { pre, str }`                  | 24-120 + 8n            |
| 2  | `NameNum { pre, i }`                    | 24-128                 |
| 3  | `Succ(l)`                               | 16-48                  |
| 4  | `Max(l, l)`                             | 24-88                  |
| 5  | `IMax(l, l)`                            | 24-88                  |
| 6  | `Param(name)`                           | 16-48                  |
| 7  | `BVar(u64)`                             | 16-88                  |
| 8  | `Sort(l)`                               | 16-48                  |
| 9  | `Const { name, us }`                    | 24-88 + 8-40 per level |
| 10 | `App { fun, arg }`                      | 24-88                  |
| 11 | `Lam(Binding)`                          | 40-136                 |
| 12 | `Pi(Binding)`                           | 40-136                 |
| 13 | `Let { name, ty, value, body, nondep }` | 48-176                 |
| 14 | `Nat(decimal str)`                      | 16-48 + 8n             |
| 15 | `Str(str)`                              | 16-48 + 8n             |
| 16 | `Proj { type_name, idx, struct_ }`      | 32-168                 |
| 17 | `MData(e)`                              | 16-48                  |
| 18 | `Decl(Decl)`                            | varies                 |
| 19 | `End { names, levels, exprs }`          | 104                    |

Ids are implicit and dense, in record order: names and levels from 1 (0 is anonymous and zero), expressions from 0. Records only refer to earlier ids.

`End` counts are fixed-width little-endian `u32`, so the last 12 bytes of a file give the table sizes.

`Info { hash: u64 le, loose_bvar_range: varint, flags: u8 }` with flags bit 0 has-level-param and bit 1 has-fvar (never set). `hash` is `xxh3_64(tag ++ parts)`, child hashes and integers as `u64` le, strings as UTF-8, binder names and info ignored. Size is the length of the hashed input. `Info` itself is 80-112 bits:

| Tag | Node  | Parts             | Size (bits)       |
| --- | ----- | ----------------- | ----------------- |
| 0   | anon  |                   | 8                 |
| 1   | str   | pre, bytes        | 72 + 8n           |
| 2   | num   | pre, i            | 136               |
| 3   | zero  |                   | 8                 |
| 4   | succ  | l                 | 72                |
| 5   | max   | a, b              | 136               |
| 6   | imax  | a, b              | 136               |
| 7   | param | name              | 72                |
| 8   | bvar  | i                 | 72                |
| 9   | sort  | l                 | 72                |
| 10  | const | name, us...       | 72 + 64 per level |
| 11  | app   | fun, arg          | 136               |
| 12  | lam   | ty, body          | 136               |
| 13  | pi    | ty, body          | 136               |
| 14  | let   | ty, value, body   | 200               |
| 15  | nat   | digits            | 8 + 8n            |
| 16  | str   | bytes             | 8 + 8n            |
| 17  | proj  | struct, name, idx | 200               |

`MData` takes the info of the term it wraps.

```bash
olean-export Mathlib -f blean -o mathlib.blean
olean-export convert mathlib.ndjson -o mathlib.blean   # and back
```
