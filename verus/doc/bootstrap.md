# Bootstrapping the toolchain

English | [日本語](bootstrap.ja.md)

Installing the tools of [reproducing.md](reproducing.md) that are not
fetched by rustup or cargo. The counterpart of the SPARK crate's
`spark/doc/bootstrap.md` (github.com/manthonyaiello/Foundation, tag
`spark-v1.0`), with the same sections, and three of its own after them
(Verus, SAW, mir-json). Everything here was done on one x86_64 Ubuntu 24.04
desktop, by hand, on 2026-11-01. Back to the [README](../README.md).

## Cryptol

The FFI check, coverage and mutation testing (`verus/cryptol/`) need
Cryptol 3.6.0 built with FFI support (`cryptol --version` prints `FFI
enabled`). The release tarball
`cryptol-3.6.0-ubuntu-24.04-X64-with-solvers.tar.gz` (sha256 in
[reproducing.md](reproducing.md#tools)) has it, and z3, cvc4, cvc5, yices
and abc in the same `bin/`. It is unpacked into a directory of its own and
put on `PATH` only for the scripts that need it.

### `CRYPTOLPATH`

As in the SPARK crate: the NSA modules are named from the repository root
(`algorithms::AES::Main`, `shared::...`). `scripts/check-ffi.sh` sets
`CRYPTOLPATH` to the repository root and `verus/cryptol`, so a property
module imports `algorithms::AES::GF28` by its NSA name.

On Linux, Cryptol looks for a module's foreign implementations in
`<Module>.so` beside the `.cry` file; `check-ffi.sh` links the FFI library
there. The repository's own `algorithms/AES/{Cipher,KeyExpansion}.so` are
symlinks into NSA's unbuilt Rust, so Cryptol warns that it cannot find
them and falls back to their Cryptol bodies ([ffi.md](ffi.md) says why
the check fails if that Rust is built).

### aarch64 Linux (a container, built from source)

Omitted: the crate has been run on x86_64 Linux only, where Galois's
release is used. The SPARK crate's recipe (GHC 9.8.4 and cabal through
ghcup, a sysroot of Ubuntu's headers) is the one to follow for aarch64
Linux.

### CI

Omitted: there is no CI ([reproducing.md](reproducing.md#what-ci-runs)).

## Bootstrapping the x86_64 instance

Omitted: there is no bootstrap script. The SPARK crate's
`scripts/bootstrap-x86_64.sh` installs its tools from its pin file; here
the tools are installed as this page says.

## Verus

Not in the SPARK crate. Verus is built from source at the commit that its
version names, `bf5bb51f3f1a6ede578fcbafe86cfa1ba1885021`
(github.com/verus-lang/verus), in the release profile with Rust 1.98.1, as
its `BUILD.md` says. The build includes its Z3 (4.16.0). `verus --version`
prints `Version: 0.2026.10.16.bf5bb51`, `Profile: release`.

`cargo verus` must run this build: `Cargo.toml`'s
`[workspace.metadata.verus]` names the version. When the version moves, `rust-toolchain.toml` and `vstd` in
`Cargo.toml` move with it.

## SAW

Not in the SPARK crate's page (its bootstrap script installs SAW on its
x86_64 instance). The release tarball
`saw-1.6-ubuntu-24.04-X64-with-solvers.tar.gz` (sha256 in
[reproducing.md](reproducing.md#tools)), as the SPARK crate pins it.
`saw --version` prints `1.6 (68eed5f release-1.6)`; z3, cvc5, yices,
bitwuzla, boolector, abc and SAW's own `cryptol` are in the same `bin/`.

The release's `.sig` was not checked, as in the SPARK crate: its signing
key is on neither keys.openpgp.org nor keyserver.ubuntu.com, so the pin is
the asset's sha256.

`scripts/check-saw.sh` caps each `saw` run at 10 GB of memory through
`systemd-run --user` where that works.

## mir-json

Not in the SPARK crate (its SAW reads only bitcode). SAW reads Rust's MIR
through mir-json, at the commit SAW 1.6 carries as a submodule,
`8cbf9af1821075ef47cf784fef78d2650827730d` (github.com/GaloisInc/mir-json,
JSON schema 13), with the Rust its `rust-toolchain.toml` names:

```console
$ rustup toolchain install nightly-2026-03-21 --profile minimal --component rustc-dev,rust-src
$ git clone https://github.com/GaloisInc/mir-json src && cd src
$ git checkout 8cbf9af1821075ef47cf784fef78d2650827730d
$ cargo +nightly-2026-03-21 install --path . --locked --root <mir-json>
$ mir-json-translate-libs -o <mir-json>      # the standard library's MIR, rlibs/
```

`MIR_JSON_DIR=<mir-json>` tells `scripts/check-saw.sh` where it is: the
script puts its `bin/` on `PATH`, its `rlibs/` in `SAW_RUST_LIBRARY_PATH`,
and calls `cargo saw-build` with the toolchain `mir-json --version` names.
