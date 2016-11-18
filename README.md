# rust-jsonnet

[![Build Status](https://travis-ci.org/anguslees/rust-jsonnet.svg?branch=master)](https://travis-ci.org/anguslees/rust-jsonnet)

libjsonnet bindings for Rust

```toml
[dependencies]
jsonnet = "0.5"
```

### Building rust-jsonnet

Building `jsonnet-sys` requires gcc (via the `gcc` Rust crate).
`libjsonnet` is not typically available as an existing shared library,
so `jsonnet-sys` builds and statically links its own copy.

```sh
$ git clone https://github.com/anguslees/rust-jsonnet
$ cd rust-jsonnet
$ cargo build
```

# License

`rust-jsonnet` is distributed under the terms of the Apache License
(Version 2.0), the same as `libjsonnet` itself.

See LICENSE for details.
