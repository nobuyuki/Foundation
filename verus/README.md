# Verus implementations of AES, SHA-256 and HMAC-SHA-256

English | [日本語](README.ja.md)

This directory is a Cargo crate, `foundation_verus`. It holds Rust
implementations, proved with Verus, of three algorithms from the NSA's
Cryptol specifications in [`../algorithms`](../algorithms):

* **AES** (FIPS 197): key expansion, encryption and decryption, at 128,
  192 and 256-bit keys;
* **SHA-256** (FIPS 180-4): one-shot and streaming;
* **HMAC-SHA-256** (FIPS 198-1): one-shot and incremental.

It mirrors, in Rust and Verus, the SPARK crate `foundation_spark` in
[`../spark`](../spark) (github.com/manthonyaiello/Foundation, tag
`spark-v1.0`, on which this repository is built), part for part: each implementation is proved, with Verus, equal
to a Verus transcription of the NSA's Cryptol, and the implementation is
checked against the Cryptol itself by testing through Cryptol's foreign
function interface and by proof with SAW.

## How the pieces fit

```text
  NSA's Cryptol (algorithms/AES, SHA2, HMAC)
        ^                          ^
        |                          |
        |                          |
  Spec layer: Verus spec fns, declaration by declaration the Cryptol
        ^                          |
        | Verus, for all inputs    |
        |                          | the FFI check (testing), and
  Implementation layer: Rust       | SAW at fixed sizes, on the LLVM
  (ensures: "the result is the     | bitcode and on the MIR:
   spec's")  ----------------------+ implementation = Cryptol
```

* The **spec layer** mirrors the Cryptol as closely as Verus allows: the
  same names, the same types (`Seq<bool>` where Cryptol has bit strings,
  Rust integers for words), the same recursion and folds. It is `spec fn`:
  it is proved about, and never compiled. The Cryptol built-ins it is
  written in (`foldl`, `@`, `join`, `split`, ...) are stated once, in
  [`src/cryptol/`](src/cryptol) ([doc/cryptol-prelude.md](doc/cryptol-prelude.md)).
* The **implementation layer** is ordinary Rust, written to run. Each
  function's `ensures` says its result is the spec layer's. Lemmas
  (`proof fn`) and representation layers (bytes against bits, streaming
  against one-shot) sit between the two.
* **Verus** proves the implementation equal to the spec layer for every
  input, and proves the absence of run-time errors (overflow,
  out-of-bounds indexing, and so on) everywhere.
* The **FFI check** calls the executables from Cryptol and compares them
  with NSA's Cryptol, exhaustively where the input space is small and on
  random and known-answer inputs otherwise.
* **SAW** proves the compiled code of the implementation equal to NSA's
  Cryptol, with no Verus spec in between, at fixed key sizes and message
  lengths, by two routes: rustc's LLVM bitcode and its MIR.

Where the SPARK crate differs: its spec layer is ghost code that can be
compiled, so its FFI check and SAW also compare the spec layer with the
Cryptol. A Verus spec function is not compiled, so here the spec layer is
compared with the Cryptol only through the executables proved equal to it
([doc/ffi.md](doc/ffi.md)).

The walkthroughs show the chain on real code, Cryptol and Verus side by
side:

* [AES](doc/walkthroughs/aes.md)
* [SHA-256](doc/walkthroughs/sha-256.md)
* [HMAC-SHA-256](doc/walkthroughs/hmac-sha-256.md)

## What is proved

* **Every function Verus checks is verified**: 326 verified, 0 errors
  (`cargo verus verify`) at `d59a3f0`, in about 14 s on a 16-CPU desktop.
  No function raises Verus's resource limit, and no proof is slow
  ([doc/proving.md](doc/proving.md)).
* **Nothing is assumed.** There is no `assume`, `admit`, `axiom fn`,
  `external_body`, `#[verifier::external]` or termination exemption. The
  only code Verus does not see is the FFI exports of `src/ffi/`, which
  export the executables to Cryptol for testing, each listed with its
  reason in [`scripts/trust-surface.txt`](scripts/trust-surface.txt)
  (100 entries); `scripts/check-trust-surface.sh` checks this, as the
  SPARK crate's script of the same name does.
* **The implementation equals the spec layer for every input**, including
  every message length below 2^61 bytes (for HMAC, every text shorter than
  its `Max_Text`) and every way of splitting a message into chunks for the
  streaming SHA-256 and HMAC interfaces.
* **The Cryptol's own properties of AES** (13 of the 15 that
  `algorithms/AES` states, as in the SPARK crate) are proved of the spec
  layer, once for all key sizes.
* **SAW**: 84 results on each route (LLVM bitcode and MIR: AES 46,
  SHA-256 and HMAC 38), with 8 negative controls on each that fail as they
  must (`saw/results.txt`, at `d59a3f0`). AES at k = 128, 192 and 256;
  SHA-256's compression function for every input; hashing at twelve
  lengths and HMAC at seven (key, text) pairs, chosen at the padding
  boundaries. Details and what SAW leaves out: [doc/saw.md](doc/saw.md).

What is **not** proved:

* that the spec layer equals the Cryptol. That rests on close reading, on
  the re-proved properties (AES), and on the FFI check and SAW of the
  executables proved equal to it: SAW covers all of AES's sizes, SHA-256's
  compression and hashing and HMAC only at the lengths SAW was run at;
* that the compiler is correct. Verus reasons about the Rust source; SAW
  about the bitcode and the MIR that rustc 1.98.1 and mir-json emit;
* Verus itself, vstd, and the SMT solver;
* timing. The AES here is not constant time: its S-box is a table lookup
  indexed by key and state bytes.

## What is tested

* **The FFI check**: 73 properties
  ([`cryptol/properties.txt`](cryptol/properties.txt)), the SPARK crate's
  for its executables (its other 68 test spec functions, which cannot run
  here). They compare the crate's functions with NSA's Cryptol, with
  Cryptol's `:exhaust` or `:check`, plus the known-answer vectors of
  FIPS 197, FIPS 180-4 and RFC 4231. [doc/ffi.md](doc/ffi.md).
* **Coverage** of the executable code under those properties, by region,
  line and branch outcome. **There is no MC/DC**, which the SPARK crate
  measures: rustc has no MC/DC instrumentation. The implementation layer
  is covered entirely (regions 947/947, branches 80/80); the 11 gaps,
  explained in [`coverage/explained.txt`](coverage/explained.txt), are the
  FFI exports' checks of what Cryptol's types ensure.
  [doc/coverage.md](doc/coverage.md).
* **Mutation testing**: 88 small faults in the executable code
  ([`mutation/mutants.txt`](mutation/mutants.txt): the SPARK crate's 84,
  less three that Rust slices cannot express, with the seven of
  `SHA2.Functions` written twice). The FFI properties catch 73. Of the
  other 15, 10 do not change behaviour, and 5 are real bugs in the
  streaming SHA-256's length encoding that only show on messages longer
  than the properties try; Verus fails to verify all five. Verus also
  fails 5 of the 10 harmless ones: a failed proof is not a bug found.
  [doc/coverage.md](doc/coverage.md), "Mutation testing".
* **Performance** against NSA's Rust reference AES
  (`../algorithms/AES/rust/`, unmodified, same rustc and profiles): about
  twice as fast, and about twice the size, at `opt-level` 3 on an x86_64
  desktop. [doc/performance.md](doc/performance.md).

## Layout

| path | what |
|---|---|
| [`src/aes/`](src/aes), [`src/sha2/`](src/sha2), [`src/hmac/`](src/hmac) | per algorithm: the spec layer (one module per Cryptol module), the implementation (`aes_impl`, `sha256_stream`, `sha256_impl`), and their lemmas |
| [`src/cryptol/`](src/cryptol) | Cryptol's built-ins as spec functions and lemmas |
| [`src/ffi/`](src/ffi) | the FFI exports to Cryptol (outside `verus!`) |
| [`ffi/`](ffi) | the FFI library: a cdylib of `src/ffi/`, its own workspace |
| [`cryptol/`](cryptol) | our Cryptol: the property modules that call the exports, and `properties.txt` |
| [`saw/`](saw) | the SAW proofs: `llvm/` (on the bitcode) and `mir/` (on the MIR), and `results.txt`, the record of the last run |
| [`coverage/`](coverage), [`mutation/`](mutation) | coverage and mutation-testing inputs |
| [`perf/`](perf) | the performance harness (its own workspace), and in `perf/rust/` NSA's side |
| [`scripts/`](scripts) | the trust-surface gate and its manifest, the FFI, SAW and coverage checks, mutation testing, the performance comparison |
| [`doc/`](doc) | the detailed documents below |

## Reproducing

From `verus/`:

```console
$ cargo build && cargo test
$ cargo verus verify                                   # 326 verified, 0 errors
$ scripts/check-trust-surface.sh
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-ffi.sh   # needs Cryptol 3.6.0 with FFI
```

Verus `0.2026.10.16.bf5bb51` is pinned in `Cargo.toml`
(`[workspace.metadata.verus]`), with Rust `1.98.1` (`rust-toolchain.toml`)
and vstd `=0.0.0-2026-10-11-0230`. Cryptol 3.6.0 and SAW 1.6 come from
Galois's release pages (builds "with solvers"). Every tool is free, SAW
included: rustc emits the bitcode and mir-json the MIR. Step by step, with
SAW, coverage, mutation testing and performance:
[doc/reproducing.md](doc/reproducing.md).

## Documents

| document | what it covers |
|---|---|
| [doc/reproducing.md](doc/reproducing.md) | the tools, and every check step by step |
| [doc/proving.md](doc/proving.md) | running Verus, resource limits, where spec and implementation differ by design, the Cryptol's own properties, the gates |
| [doc/cryptol-prelude.md](doc/cryptol-prelude.md) | Cryptol's built-ins in Verus, and the choices made in stating them |
| [doc/ffi.md](doc/ffi.md) | the FFI check: how Rust is called from Cryptol, what a pass requires, what it does not reach |
| [doc/coverage.md](doc/coverage.md) | coverage under the FFI properties, and mutation testing |
| [doc/performance.md](doc/performance.md) | size and speed against NSA's Rust AES |
| [doc/saw.md](doc/saw.md) | the SAW proofs: what is proved at which sizes, what is not, the bitcode and the MIR, how to run them |
| [doc/bootstrap.md](doc/bootstrap.md) | installing Verus, Cryptol, SAW and mir-json |
| [doc/walkthroughs/](doc/walkthroughs) | AES, SHA-256 and HMAC-SHA-256: Cryptol and Verus side by side |
