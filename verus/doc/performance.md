# Performance

Size and speed of the crate's AES against NSA's Rust reference AES, on an
x86_64 Linux desktop. The counterpart of the SPARK crate's
`spark/doc/performance.md`. Back to the [README](../README.md).

## How to run it

`scripts/perf-aes.sh` compares the crate's AES (`aes::aes_impl`) with the
repository's reference, NSA's Rust `Cipher` and `KeyExpansion` crates
(`../algorithms/AES/rust/`, used unmodified as path dependencies). AES
only: there is no reference SHA-256 or HMAC to compare with, as in the
SPARK crate.

```console
$ scripts/perf-aes.sh                     # prints and writes target/perf/perf-report.md
$ PERF_SKIP_BENCH=1 scripts/perf-aes.sh   # builds and sizes only
$ PERF_QUICK=1 scripts/perf-aes.sh        # a smoke test, not a measurement
```

It needs cargo, `git`, binutils' `nm` and `size`, and `python3`. It runs on
Linux, and on macOS for the times only: there the report leaves out the
size table. Mach-O symbols have no sizes, and the SPARK script reads the
linker map for them instead, which would need the map's Rust names
demangled. A macOS run here is a reference point, on a machine not like
the Linux one, not a second platform of the same comparison. A full run
takes about 40 seconds, builds included.

The harness has the SPARK crate's `spark/perf/` layout. `perf/` is the
crate's side: a Cargo package with its own workspace, as `ffi/` is, in
place of `perf.gpr`. Its `src/perf_aes.rs` holds the wrappers
(`perf_aes.ads` and `.adb`) and its `src/perf_bench.rs` the benchmark
(`perf_bench.adb`). `perf/rust/` is NSA's side, the SPARK crate's
`spark/perf/rust/` unchanged but for its comments and a `[workspace]`
table. Neither is part of the crate, verified, or in the trust-surface
scan, which covers `src/`. The script builds:

| build | flags |
|---|---|
| `verus-O2`, `verus-O3` | `perf/Cargo.toml` profiles `perf-o2`/`perf-o3`: release, `opt-level` 2 / 3, `lto = "fat"`, `codegen-units = 1`, as NSA's side |
| `verus-O3-checks` | profile `perf-o3-checks`: `perf-o3` with `overflow-checks` and `debug-assertions` on |
| `verus-release` | plain `--release`: `opt-level` 3, no LTO, 16 codegen units |
| `rust-O2`, `rust-O3` | `perf/rust/Cargo.toml` profiles `perf-o2`/`perf-o3`, the SPARK crate's |
| `rust-release` | plain `--release` |

Everything else is the release default: no overflow checks, no debug
assertions, `panic = "unwind"`. Slice bounds checks stay. Rust has no
switch to remove them, and Verus's proof that no index is out of range
does not reach rustc, which does not see a `requires`. `verus-O3-checks`
is the counterpart of the SPARK crate's `spark-O3-checks`, which keeps the
run-time checks that the proof made redundant. `perf.adc`'s
`Assertion_Policy (Ignore)` has no counterpart to set: Verus erases every
spec, proof and ghost item from a cargo build. **Both sides are compiled
by the same rustc** (`rust-toolchain.toml`, 1.98.1) with the same
profiles. The SPARK comparison sets GCC against rustc; here the builds
differ only in their source. No `target-cpu`: rustc's default for the
target. (`verus-release` has no SPARK counterpart. It is there to set
against `rust-release`.)

**How it measures.** `perf_bench.rs` does what NSA's side's `main.rs`
does, in the same order, as `perf_bench.adb` does. Each side calls its AES
through one non-inlined wrapper per operation. The crate's functions take
the key size as a const generic (Cryptol's `{k}`), and the SPARK crate's
and NSA's take it at run time. So the crate's wrappers take it at run time
and `match` it to the three instances. Both harnesses pass the key size
through `black_box`, so no wrapper is specialized for a constant key size
(the SPARK harness reads it from a `Volatile` for the same reason). Each
harness first checks FIPS-197 Appendix C.1–C.3: encrypt, then decrypt
back, by both decryptions on the crate's side. Then it times each
operation in batches of 10 000 chained calls, each output being the next
input: 20 batches of warm-up, then 101 timed batches, on `Instant`
(`CLOCK_MONOTONIC` on Linux). It reports the median time per call and the
quartiles.

Sizes are read from the linked executable's symbols with `nm -S -C`.
"AES" is every symbol of the crate (`foundation_verus::*`), or of NSA's
two crates. The wrappers are `perf_aes::*` and
`aes_perf::{expand_key, encrypt, decrypt}`. The harnesses and Rust's std
are not counted. Anonymous constants are not counted either, as in the
SPARK script. The crate's S-boxes `S_BOX` and `INV_S_BOX` are among them:
they are `const`s, and rustc emits them without a symbol. NSA's `SBOX` and
`INVSBOX` are `static`s, with symbols. So the crate's "AES data" is 0, and
its 512 bytes of S-boxes are not in the table. NSA's 812 bytes are its
S-boxes, `RCON` and the two `PERM` tables.

**What the comparison is.** As the SPARK document says of its own: NSA's
Rust is a reference implementation, with a table S-box, `mul_bytes` by
shift-and-add, an `if` on the secret in `xTimes`, no T-tables and no
hardware AES instructions. The crate is the same algorithm: table
S-boxes, and `x_times` by a shift and a conditional reduction, with
`MixColumns`' products as sums of `x_times`. NSA's `inv_cipher` undoes
the rounds of `cipher` in reverse order, as `decrypt_block_prime`
(InvCipher') does. `decrypt_block` is FIPS's InvCipher, which NSA's Rust
does not have, so both are set against NSA's `decrypt`.

## x86_64, Linux (a desktop)

Intel Core i9-9900K (8 cores, 16 logical CPUs), Linux 7.1, rustc 1.98.1,
2026-11-02 09:24 UTC.
Two full runs, back to back; the numbers are the first's. The second's
medians are within 3% of them in 71 of 75 cells and within 5.5% in all,
and the sizes are identical. **A shared desktop, not an idle machine**:
the 1-minute load was 0.98 before the first run and 1.44 after the second
(the benchmark is one of it), with no proof or other benchmark running.
No thread was pinned to a core. The quartiles are 0.9% apart in the
median cell, within 2% in 56 of 75 cells and within 4.4% in all.

Size (bytes):

| build | AES text | AES data | wrappers | AES total | executable text |
|---|---:|---:|---:|---:|---:|
| `verus-O2` | 2430 | 0 | 7294 | 9724 | 282 954 |
| `verus-O3` | 2151 | 0 | 5794 | 7945 | 285 866 |
| `verus-O3-checks` | 2151 | 0 | 5794 | 7945 | 286 778 |
| `verus-release` | 2170 | 0 | 6190 | 8360 | 298 819 |
| `rust-O2` | 3316 | 812 | 15 | 4143 | 276 714 |
| `rust-O3` | 3447 | 812 | 15 | 4274 | 280 026 |
| `rust-release` | 3297 | 812 | 18 | 4127 | 292 979 |

* **Read "AES total", not "AES text".** rustc inlines the crate's
  ciphers and key schedule into the wrappers, in every build, the one
  without LTO included: they are generic, so their instances are compiled
  in `perf_aes`, the crate that names them. Only the leaves the instances
  share stay as functions: at `opt-level` 3 `mix_columns` 728,
  `inv_mix_column` 452, `inv_round` 352, `inv_round_prime` 330 and `round`
  289 bytes. The wrappers are `encrypt` 2400, `expand_key` 1673,
  `decrypt_prime` 1029 and `decrypt` 692. NSA's wrappers are tail calls.
  Its `key_expansion` is 1324 bytes, `inv_mixcolumns_step` 668, `cipher`
  645 and `inv_cipher` 643.
* **The crate's AES is about twice the size of NSA's**: 1.9× at
  `opt-level` 3 (7945 against 4274 bytes), 2.3× at 2 and 2.0× without
  LTO. With the crate's 512 bytes of S-boxes counted, 2.0× at
  `opt-level` 3 (8457 against 4274). Each of its operations is compiled
  three times, once per key size, the const generic `k`, against NSA's
  once.
* **`verus-O3-checks` is the same machine code as `verus-O3`.** The
  disassembly of the crate's AES and its wrappers is identical
  instruction for instruction in the two builds. Only the addresses of the
  panic locations, which are std's data, differ. With overflow checks and
  debug assertions on, rustc emits nothing more in the AES: no check it
  would add survives optimization. The executables differ by 912 bytes, in
  std and the harness.
* The sizes depend on what rustc chooses to inline.

Time (ns per call, median; first and third quartile in the report):

| op | `verus-O3` | `rust-O3` | `verus-O2` | `rust-O2` | `verus-release` | `rust-release` |
|---|---:|---:|---:|---:|---:|---:|
| AES-128 `expand_key` | 73.9 | 336.0 | 80.3 | 335.7 | 73.9 | 312.7 |
| AES-128 encrypt | 246.6 | 444.7 | 239.4 | 479.6 | 244.9 | 438.1 |
| AES-128 decrypt (`decrypt_block`) | 369.1 | 712.9 | 382.5 | 762.9 | 372.8 | 757.4 |
| AES-128 `decrypt_block_prime` | 380.1 | 712.9 | 395.0 | 762.9 | 375.5 | 757.4 |
| AES-192 `expand_key` | 95.2 | 389.5 | 103.9 | 382.6 | 96.1 | 347.0 |
| AES-192 encrypt | 299.0 | 536.3 | 289.0 | 571.3 | 296.8 | 526.5 |
| AES-192 decrypt (`decrypt_block`) | 449.2 | 865.6 | 463.9 | 921.9 | 453.5 | 916.4 |
| AES-192 `decrypt_block_prime` | 453.2 | 865.6 | 479.7 | 921.9 | 457.3 | 916.4 |
| AES-256 `expand_key` | 113.2 | 446.7 | 113.5 | 445.5 | 108.5 | 411.9 |
| AES-256 encrypt | 350.7 | 624.0 | 338.4 | 708.5 | 349.3 | 617.8 |
| AES-256 decrypt (`decrypt_block`) | 529.2 | 1014.3 | 546.0 | 1077.8 | 535.6 | 1072.4 |
| AES-256 `decrypt_block_prime` | 533.5 | 1014.3 | 564.6 | 1077.8 | 538.8 | 1072.4 |

(The Rust columns of the `decrypt_block_prime` rows repeat NSA's one
decryption. `verus-O3-checks`, the same code as `verus-O3`, is within 4%
of it in every cell, 0.98–1.04×. That is the size of an effect that code
layout and the machine alone make here, and a bound on what the other
columns can tell apart.)

What it shows, at `opt-level` 3:

* **The crate's AES is about twice as fast as NSA's**: key expansion
  0.22–0.25×, encrypt 0.55–0.56×, decrypt 0.52× (`decrypt_block`) and
  0.52–0.53× (`decrypt_block_prime`, the same structure as NSA's
  `inv_cipher`). The SPARK crate on its x86_64 instance had encrypt
  0.51–0.53×, key expansion 0.39–0.42× and decrypt 1.01–1.03× against the
  same Rust (rustc 1.95.0, another CPU). Both compilers being rustc here,
  the gap is in the source. Where in the source has not been looked into.
* **The ratios hold across the profiles**: at `opt-level` 2 the crate is
  0.24–0.27× on key expansion, 0.48–0.51× on encrypt and 0.50–0.52× on
  decrypt, and without LTO 0.24–0.28×, 0.56–0.57× and 0.49–0.50×.
* **`opt-level` 2 against 3, and LTO, matter little to either side**,
  within or near the 4% above: the crate at 2 is 3–4% faster on encrypt,
  3–6% slower on decrypt and up to 9% slower on key expansion, and the
  crate without LTO is within 4% of `perf-o3`. NSA's at 2 is 6–14% slower
  on the ciphers. NSA's `key_expansion` is 7–11% faster in the plain
  release build than at `perf-o3`, as the SPARK document found (25–27% on
  its x86_64 instance), and its decryption 6% slower.
* **The checks cost nothing here**: the proof makes overflow impossible,
  and in this code rustc reaches the same conclusion on its own (above).
  The bounds checks are another matter. They stay in every build, proof
  or not: the crate's AES at `perf-o3` still has 28 calls to the
  bounds-check panic, and NSA's 15.
