[![build-badge](https://github.com/30bit/laski/actions/workflows/ci.yml/badge.svg)](https://github.com/30bit/laski/actions)
[![docs-badge](https://github.com/30bit/laski/actions/workflows/docs.yml/badge.svg)](https://30bit.github.io/laski/laski)

# laski

A library that provides specialized ASCII-only string and character types.

The types `PackedStr12` and `PackedStr24` are meant to be used as a fast and small representation for strings. Both traits are achieved by representing them as integers used in an endianness-agnostic way. Additionally, almost every function is `const`.

Strings are padded to their capacity by ASCII whitespace characters. These can be removed by the trimming functions.

| String type   | Inner type    | Chars | Bytes |
| ------------- | ------------- | ----- | ----- |
| `PackedStr12` | `NonZeroU64`  | 12    | 8     |
| `PackedStr24` | `NonZeroU128` | 24    | 16    |

Note that packing and unpacking of the strings has some overhead. For you to take advantage of `laski`, you should use the packed type extensively after packing once upon obtaining a string, unpacking only for debug or trace.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT) at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
