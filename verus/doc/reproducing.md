# Reproducing the results

English | [日本語](reproducing.ja.md)

The counterpart of the SPARK crate's `spark/doc/reproducing.md`
(github.com/manthonyaiello/Foundation, tag `spark-v1.0`), with the same
sections. The SPARK crate has two paths: the **FSF path**, with free tools,
and the **SAW path**, which needs GNAT Pro 27's LLVM back end. Here every
tool is free, rustc emits the LLVM bitcode and the MIR that SAW reads, and
so there is one path; its sections are under the first heading. Back to the
[README](../README.md).

## The free path

### Tools

| tool | version | needed for |
|---|---|---|
| Rust (rustup) | 1.98.1, with `llvm-tools` | building, proof, the FFI check, coverage, performance (`rust-toolchain.toml`) |
| Verus | `0.2026.10.16.bf5bb51` (commit `bf5bb51f3f1a6ede578fcbafe86cfa1ba1885021`), with its Z3 4.16.0 | proof (`Cargo.toml`, `[workspace.metadata.verus]`) |
| vstd | `=0.0.0-2026-10-11-0230` | proof (`Cargo.toml`; fetched by cargo) |
| Cryptol, built with FFI support, and z3 | 3.6.0 | the FFI check, coverage, mutation testing |
| SAW | 1.6 | SAW |
| mir-json, and its Rust | commit `8cbf9af`, `nightly-2026-03-21` | SAW on the MIR |
| python3, bash, GNU `c++filt` | | the scripts; `c++filt` for SAW on the bitcode |

Where to get them:

- **Rust 1.98.1**: rustup reads `rust-toolchain.toml`; coverage needs
  `rustup component add llvm-tools --toolchain 1.98.1`.
- **Verus**: built from source at the commit above
  (github.com/verus-lang/verus), release profile, with the Rust above.
  `cargo verus` must find this build: the version in `Cargo.toml` names it.
- **Cryptol 3.6.0** and **SAW 1.6**: Galois's release pages,
  `cryptol-3.6.0-ubuntu-24.04-X64-with-solvers.tar.gz` (sha256
  `621860aa1dedc037e8fc8355bef3edf023e41e78efb7177146126f5a87309962`) and
  `saw-1.6-ubuntu-24.04-X64-with-solvers.tar.gz` (sha256
  `0b25c8b32db8b4a7ec32d6700024af60bb2a0398ee350b630dd84ff377c938f7`), the
  same as the SPARK crate's pins.
- **mir-json**: [bootstrap.md](bootstrap.md#mir-json).

The SPARK crate pins every version and sha256 in
`scripts/toolchain-pins.env`, which its CI and its bootstrap read. Here
the versions are pinned where the tools read them (`rust-toolchain.toml`,
`Cargo.toml`), and the downloads are pinned by this table: there is no
CI and no bootstrap script to read a pin file.

### Steps

From a checkout of the repository:

```console
$ cd verus
$ cargo build
$ cargo test
$ cargo verus verify                    # 326 verified, 0 errors
$ scripts/check-trust-surface.sh
```

**Prove.** `cargo verus verify` verifies every function, in about 14 s on
a 16-CPU x86_64 desktop. There is no gate script, no board and no slow
proof: [proving.md](proving.md).

**Check against the Cryptol.**

```console
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-ffi.sh                  # every property, about 6 min
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-ffi.sh prop_Impl_Dot    # only these
```

Details: [ffi.md](ffi.md).

**SAW.**

```console
$ PATH=<saw-1.6>/bin:<cryptol-3.6.0>/bin:$PATH MIR_JSON_DIR=<mir-json> scripts/check-saw.sh
```

Both routes (LLVM bitcode and MIR), about 15 min; `SAW_ROUTE=llvm` or
`mir` runs one. It writes `saw/results.txt` from a clean tree. Details:
[saw.md](saw.md).

**Coverage** (Linux):

```console
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-coverage.sh    # about 8 min
```

Details: [coverage.md](coverage.md).

**Mutation testing** (hours; [coverage.md](coverage.md#mutation-testing)):

```console
$ scripts/mutation.py setup /tmp/mut
$ scripts/mutation.py prove /tmp/mut
$ scripts/mutation.py ffi /tmp/mut && scripts/mutation.py ffi /tmp/mut --full
$ scripts/mutation.py saw /tmp/mut --baseline
$ scripts/mutation.py saw /tmp/mut ID ...          # the FFI's survivors and the F mutants
$ scripts/mutation.py report /tmp/mut
```

**Performance** (optional):

```console
$ scripts/perf-aes.sh
```

Details: [performance.md](performance.md).

**The documentation gates**: omitted, there are none
([proving.md, "Gates"](proving.md#gates)).

### One command, on x86_64 Linux

Omitted: there is no bootstrap script. The SPARK crate's
`scripts/bootstrap-x86_64.sh` takes a bare Ubuntu 24.04 machine to a green
FFI check; here the tools are installed by hand
([bootstrap.md](bootstrap.md)).

### What CI runs

Omitted: there is no CI. Every check above is run by hand; SAW's runs are
recorded in `saw/results.txt`, with the commit each ran at.

## The SAW path (GNAT Pro)

Omitted: SAW needs no proprietary tool here. The SPARK crate's bitcode must
come from GNAT Pro 27's LLVM back end, with an `llvm-link` of the same LLVM
version; here rustc emits the bitcode (`--emit=llvm-bc`) and mir-json the
MIR, and SAW is run as in the free path above.

### Tools

Omitted: in the table above.

### Steps

Omitted: in "Steps" above. The recorded run (`saw/results.txt`, at `d59a3f0`) took 928 s on a 16-CPU x86_64 desktop: 11 s for
`llvm/aes_impl.saw`, 30 s for `llvm/sha256_impl.saw`, 20 s for
`mir/aes_impl.saw` and 159 s for `mir/sha256_impl.saw`, the rest building
and the negative controls.
