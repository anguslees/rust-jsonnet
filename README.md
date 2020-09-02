# rust-jsonnet

[![crates.io Version Badge](https://img.shields.io/crates/v/jsonnet-rs.svg)](https://crates.io/crates/jsonnet-rs)
[![docs.rs Doc Badge](https://docs.rs/jsonnet-rs/badge.svg)](https://docs.rs/jsonnet-rs)
[![Build Status Badge](https://github.com/anguslees/rust-jsonnet/workflows/Continuous%20integration/badge.svg?branch=master)](https://github.com/anguslees/rust-jsonnet/actions)

libjsonnet bindings for Rust

```toml
[dependencies]
jsonnet-rs = "0.6"
```

### Building rust-jsonnet

Building `jsonnet-sys` requires gcc (via the `cc` Rust crate).
`libjsonnet` is not typically available as an existing shared library,
so `jsonnet-sys` builds and statically links its own copy.

```sh
$ git clone https://github.com/anguslees/rust-jsonnet
$ cd rust-jsonnet
$ cargo build
```

See also `examples/jsonnet.rs` for an almost-but-not-quite drop-in
replacement for the official `jsonnet` executable implemented using
this library.

# License

`rust-jsonnet` is distributed under the terms of the Apache License
(Version 2.0), the same as `libjsonnet` itself.

See LICENSE for details.
