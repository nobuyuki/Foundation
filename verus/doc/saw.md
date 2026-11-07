# SAW

English | [日本語](saw.ja.md)

SAW proofs that the crate's implementation layer equals NSA's Cryptol,
at fixed sizes, by two routes: on rustc's LLVM bitcode of the crate
(`llvm_verify`, the SPARK crate's route) and on its MIR (`mir_verify`,
the route of NSA's own Rust proofs, `algorithms/AES/rust/*/theorems/saw.py`).
The counterpart of the SPARK crate's `spark/doc/saw.md`
(github.com/manthonyaiello/Foundation, tag `spark-v1.0`). They run
locally, not in CI; the record of the last run is `saw/results.txt`.
Back to the [README](../README.md).

## What SAW proves

SAW proves the **implementation** layer equal to NSA's Cryptol directly,
independently of the Verus spec layer and of Verus: the leaves of
`aes::aes_impl`, its rounds, the key schedule and the ciphers at each
key size, and `aes::aes_impl::main`'s `encrypt` and `decrypt`, against
`algorithms/AES/{GF28,SBox,Cipher,KeyExpansion,Main}.cry`; SHA-256's
leaves and compression function for all inputs, and the one-shot
SHA-256 and HMAC-SHA-256 at fixed lengths, against
`algorithms/SHA2/Main.cry` and `algorithms/HMAC/Main.cry`. The NSA
Cryptol is imported unmodified. **Both routes prove the same functions
against the same Cryptol with the same overrides and tactics**, script for
script (`saw/llvm/` and `saw/mir/`); they differ only in what SAW reads
(the bitcode or the MIR) and so in how a contract states the arguments.

**SAW proves each size separately; Verus covers every size.** `compress`
is proved for every hash value and block, but `hash` and `hmac_sha256`
take slices, and SAW executes them at one length at a time: each row
below is one length. Verus proves the same functions for every length
(below `2^61` bytes) against the Verus spec layer, which the FFI check
tests against the same Cryptol.

### AES

| Rust (`aes::aes_impl::`) | Cryptol | sizes | overrides | tactic |
|---|---|---|---|---|
| `x_times` | `GF28.cry`: `xTimes` | | | rme |
| `dot` | `GF28.cry`: `(•)` | | | rme |
| `sub_byte`, `inv_sub_byte` | `SBox.cry`: `\b -> SBox @ b`, `\b -> InvSBox @ b` | | | rme |
| `sub_bytes`, `inv_sub_bytes` | `Cipher.cry`: `SubBytes`, `InvSubBytes` | | `sub_byte`, `inv_sub_byte` | rme |
| `shift_rows`, `inv_shift_rows` | `ShiftRows`, `InvShiftRows` | | | rme |
| `add_round_key` | `AddRoundKey` | | | rme |
| `mix_column` | `MixColumnsStep` | | `x_times` | rme |
| `inv_mix_byte` | `\a b c d -> InvMixColumnsStep [a, b, c, d] @ 0` | | `x_times` | rme |
| `inv_mix_column` | `InvMixColumnsStep` | | `inv_mix_byte` | rme |
| `column` (private) | `\s j -> (split s : [4]AESWord) @ j`, `j < 4` | | | z3 (rme did not finish on the 64-bit `4 * j`) |
| `mix_columns`, `inv_mix_columns` | `MixColumns`, `InvMixColumns` | | `column`, the column step | rme |
| `round`, `inv_round` | `Round`, `InvRound` | | their four steps | rme |
| `inv_round_prime` | `InvRound'` | | its four steps | z3, the four uninterpreted (rme: not in 14 minutes) |
| `sub_word`, `rot_word`, `xor_word` | `KeyExpansion.cry`: `SubWord`, `RotWord`, `^` | | `sub_byte` | rme |
| `rcon` | `(drop`{1} Rcon) @ (i - 1)`, `1 <= i <= 10` (`Rcon @ i`; `Rcon @ 0` is `undefined`, which SAW would evaluate at a symbolic index) | | | z3 |
| `expand_key::<k>` | ``KeyExpansion`{k}`` of the first `Nk k` key words; the rest of the 15 blocks zero | k = 128, 192, 256, at `Nk k` key words; at k = 128, 192 also at 8 (what `encrypt` passes) | `sub_word`, `rot_word`, `xor_word`, `rcon` | z3, `SubWord` uninterpreted |
| `encrypt_block::<k>` | ``Cipher`{k}`` of the first `Nr k + 1` round keys | k = 128, 192, 256 at `Nr k + 1` round keys; at 128, 192 also at 15 | `round`, `sub_bytes`, `shift_rows`, `add_round_key` | z3, `Round`, `SubBytes`, `ShiftRows`, `AddRoundKey` uninterpreted |
| `decrypt_block::<k>` | ``InvCipher`{k}`` | as `encrypt_block` | `inv_round`, `inv_sub_bytes`, `inv_shift_rows`, `add_round_key` | z3, those four uninterpreted |
| `decrypt_block_prime::<k>` | ``InvCipher'`{k}`` | k = 128, 192, 256 | `inv_round_prime` and the steps | z3, `InvRound'` and the steps uninterpreted |
| `main::encrypt::<k>`, `main::decrypt::<k>` | `Main.cry`: ``AES`{k}.Encrypt``, ``.Decrypt``, on the bits | k = 128, 192, 256 | `expand_key` at 8 key words, `encrypt_block` (`decrypt_block`) at 15 round keys (`key_words_of` executed) | z3, `KeyExpansion` and `Cipher` (`InvCipher`) uninterpreted |

The lengths "also at 8" and "also at 15" are those `main::encrypt` and
`main::decrypt` pass (`key_words_of` returns `[AESWord; 8]`, `expand_key`
`[Block; 15]`): an override matches only the sizes its contract states,
so those proofs are what lets `encrypt` and `decrypt` use them.

**Beyond the SPARK crate's AES proofs**, which it leaves out or cannot
make: `dot` (no cipher calls it; the SPARK crate's is not proved by SAW),
`sub_word`, `rot_word`, `xor_word` and `rcon` on their own (GNAT-LLVM
inlines the SPARK expression functions into `Expand_Key` even at `-O0`;
rustc keeps them functions), `column`, `inv_round_prime` and
`decrypt_block_prime` (FIPS 197's equivalent inverse cipher, against which
NSA's template proves its `inv_cipher`; the SPARK crate proves only its
spec layer's), and `main::encrypt` and `main::decrypt` (the SPARK crate
proves its spec layer's `Main` against `Main.cry`, and FFI-checks its
`Impl.Main`).

### SHA-256 and HMAC-SHA-256

The Cryptol: `step` and `hash` of `algorithms/SHA2/Main.cry` at SHA-256's
parameters, and `HMAC` of `algorithms/HMAC/Main.cry`, through
`saw/SHA256Main.cry`, which instantiates `Main` with **SHA256.cry's own
parameters, copied**, as the SPARK crate's `saw/SHA256Main.cry` does:
`SHA256.cry` instantiates `Main` privately, so its `step` cannot be named,
and SAW 1.6 cannot load `SHA256.cry` at all (its translation of
`algorithms/PBKDF/Main.cry`, which `packaging/Hash.cry` imports, fails).
`HMAC` is stated as `Hash.cry` states it, ``HMAC`{λ = 256, B = 64, k, n,
L = 32} hash hash hash``.

| Rust | Cryptol | sizes (bytes) | overrides | tactic |
|---|---|---|---|---|
| `sha2::notation::exec::ROTR::<n>`, `SHR::<n>` (12 instances) | `Notation.cry`: ``ROTR`{n, 32}``, ``SHR`{n, 32}`` | | | rme |
| `sha2::functions::exec::SIGMA_256_0/1`, `sigma_256_0/1` | `Functions.cry` | | their three `ROTR`/`SHR` | rme |
| `sha2::functions::exec::Ch`, `Maj` | `Functions.cry`: `Ch`, `Maj` at `[32]` | | | rme |
| `sha2::sha256_stream::compress` | `Main.cry`: `step` | all `h`, `m` | the four sigmas, `Ch`, `Maj` | z3, the four sigmas uninterpreted |
| `sha2::sha256_stream::hash` | `\msg -> split (hash (join msg))` | 0, 1, 55, 56, 63, 64, 65, 100, 119, 120, 128, 200 | `compress` | z3, `step` and the sigmas uninterpreted (at 0: none) |
| `hmac::sha256_impl::hmac_sha256` | `\key text -> split (HMAC`{256, 64, k, 8 * n, 32} hash hash hash key (join text))` | (key, text): (0, 0), (32, 3), (32, 32), (64, 3), (64, 32), (65, 3), (100, 32) | `compress`; at keys 65 and 100, `hash` at that length | z3, `step` and the sigmas uninterpreted (at (0, 0): none) |

The lengths are the SPARK crate's: each case of the padding (55, the
longest message whose padding fits one block; 56, the shortest that needs
two; 64 and 128, whole blocks; 119 and 120, the boundary in the second
block; 200, four blocks) and each case of `HMAC_init` (a key shorter than
the block, the block, and longer: hashed first).

- **`compress` is one function**, its schedule loop and its 64-round loop
  inline, as the SPARK crate's: SAW executes the 64 rounds with every
  call overridden, and z3 has the sigmas uninterpreted on both sides.
  `Ch` and `Maj` stay interpreted: `Functions.cry`'s take a tuple, and
  SAW 1.6's what4 back end cannot make an uninterpreted function of one.
  Its feed-forward is core's `u32::wrapping_add` (a call in a loop),
  executed
  (the SPARK crate's `"+"` on `Hash_Value` is a function of its own,
  proved by z3).
- **With no symbolic input** (`hash` at 0 bytes, `hmac_sha256` at (0, 0))
  SAW evaluates the overrides' `step` on constants, so nothing is
  uninterpreted there, as the SPARK crate found.
- **No lax arithmetic.** The SPARK crate loads its SHA-256 module a second
  time with SAW's lax arithmetic for the proofs that make a null range
  (GNAT-LLVM's length of `Lo .. Hi` makes a poison `add nuw` that SAW
  rejects). Rust's empty slices make no such value: every proof here,
  at 0 bytes too, is under SAW's ordinary arithmetic, with rustc's
  overflow checks in the code.

### What SAW proves on its own, in place, or not at all

Each function below is proved by Verus for all inputs and FFI-checked.

| function | executed within | why not on its own |
|---|---|---|
| `sha256_stream::init`, `update`, `finalize`, `load_block`, `to_digest` | every `hash` result (`hash` is `init`, one `update`, `finalize`; `compress` is the only override) | `update` and `finalize` would need a contract over the streaming context and its invariant, and SAW would still prove them only at fixed fill levels and data lengths; `load_block` and `to_digest` take slices and offsets that differ from call to call (the SPARK crate's reasons) |
| the same, and `hmac::sha256_impl::init_key`, `exec::xor_pad`, `init`, `update`, `finalize` | every `hmac_sha256` result | the incremental interface is the same function as the one-shot `hmac_sha256` |
| `sha256_stream::hash_chunked`, `ffi::hmac_sha256::hmac_chunked` | none | their claim is the digest for every way of splitting the message into chunks; SAW can only check particular splits |
| `aes::aes_impl::main::key_words_of` | `main::encrypt`, `main::decrypt` | a byte regrouping with no Cryptol name of its own (`split (split key)` inside `AES`{k}.Encrypt`) |

### The spec layer

The SPARK crate also proves its ghost spec layer equal to the Cryptol, on
bitcode built with ghost code on (`-gnatec=saw/spec.adc`). A Verus spec
function is not compiled at all: `cargo build`, `rustc --emit=llvm-bc`
and mir-json all see the crate with `verus!`'s spec and proof code
erased, so there is no bitcode or MIR of the spec layer for SAW to read
(as there is no FFI export of it: [ffi.md](ffi.md)). The spec layer is
tied to the Cryptol through the implementation instead: Verus proves each
implementation function equal to its spec function, and SAW (at these
sizes) and the FFI check (on random and exhaustive inputs) the
implementation equal to the Cryptol.

## Why fixed sizes

As the SPARK crate's (its `doc/saw.md`, "Why fixed sizes: what NSA's own
proofs do"): NSA's implementation proofs in this repository,
`algorithms/AES/rust/Cipher/theorems/saw.py` and
`KeyExpansion/theorems/saw.py`, prove the cipher, the inverse cipher and
the key expansion at k = 128, 192 and 256, one proof per key size; the
proofs here are at the same three sizes. SHA-256 and HMAC have no NSA
implementation proof; their lengths come from SAW itself, which executes
the code symbolically, so loop bounds and buffer sizes must be concrete.
What Verus adds is every size, every chunking and every call sequence
(`hash_chunked` and the streaming interfaces), and the absence of run-time
errors for every input; what SAW adds is a check of the code rustc
actually compiles against NSA's own Cryptol, with no Verus spec layer in
between.

## The bitcode

`check-saw.sh` compiles the library with the toolchain of
`rust-toolchain.toml` (rustc 1.98.1, LLVM 22):

```console
$ cargo rustc --lib -- --emit=llvm-bc,llvm-ir,dep-info -C codegen-units=1 -C debuginfo=0 -C no-prepopulate-passes
```

- **The dev profile** (`-O0`, overflow checks, debug assertions): the
  checks' panics are calls SAW must find unreachable at the sizes proved.
- **`codegen-units=1`**: one LLVM module, so every override is of the
  module verified (SAW takes an override only from it). The generic
  functions' instances at k = 128, 192 and 256 are in it because the
  crate's `ffi` module instantiates them.
- **No debug info**, as the SPARK crate's (SAW 1.6 rejected GNAT's).
- **`-C no-prepopulate-passes`**: no LLVM pass runs. At `-O0` rustc still
  runs LLVM's always-inliner, which inlines the `#[inline(always)]`
  functions (`ROTR`, `SHR`, the sigmas, `Ch`, `Maj`) into `compress`;
  then no proof of them can be its override, and z3 did not prove
  `compress` against `step` with the sigmas interpreted in 500 s. Without
  the pass they are calls, and `compress` is proved in 3 s with the
  sigmas uninterpreted. (The SPARK crate's `-fno-inline` for its spec
  layer, for the same reason.) What changes is only that: the
  `#[inline(always)]` functions, the crate's and core's (`u32::wrapping_add`,
  slice indexing, pointer casts), are calls rather than inlined. Compared
  on 2026-11-01, the IR of `round`, `mix_columns`, `expand_key::<128>` and
  `hash` is the same line for line with and without the switch, and
  `compress`'s differs by its six call sites of the sigmas, `Ch` and `Maj`
  and its eleven of `u32::wrapping_add`.
- **Names.** rustc mangles them (the v0 scheme), with a hash of the crate
  that changes with the toolchain and the build. `check-saw.sh` demangles
  every defined symbol (GNU `c++filt`) and writes `saw/obj/symbols.saw`,
  one binding per function of the crate (not of its `ffi` module):
  `aes::aes_impl::expand_key::<128>` is `rust__aes__aes_impl__expand_key__128`.

What rustc makes of the functions (x86_64, read from the `.ll`):

- `u8` is `i8`, `u32` `i32`, `usize` `i64`.
- **An `AESWord` (`[u8; 4]`) by value is one `i32`**, its byte `i` the
  `i`-th byte in memory, so on a little-endian target the `i32` is the
  bytes reversed and joined: the contracts take a fresh `i32` and give
  the Cryptol `reverse (split x)` (an override's argument must be a
  variable SAW can match a caller's value against, not a term of one).
- A `&mut Block` or `&[u32; 8]` is a pointer; a slice `&[T]` two
  arguments, the data pointer and the length.
- An array of more than 16 bytes returned by value (`[Block; 15]`,
  `[u8; 32]`) is returned through a hidden first pointer (`sret`); a
  `Block` (16 bytes) passed by value (`main::encrypt`'s `input`) by a
  pointer to the caller's copy.
- Element `i` of a Rust array is element `i` of the Cryptol sequence, and
  a `u8` is the `[8]` whose head is its most significant bit, so nothing
  else is reordered.

## The MIR

`check-saw.sh` compiles the library with mir-json's `cargo saw-build`,
which links the crate's MIR with its dependencies' and the standard
library's into `saw/obj/mir/foundation_verus.linked-mir.json`.

- **mir-json 8cbf9af**, the commit SAW 1.6 bundles as a submodule, schema
  13, which SAW 1.6 reads. It is a rustc plugin, built for one nightly
  toolchain, **nightly-2026-03-21 (rustc 1.96.0-nightly)**, not the crate's
  1.98.1: the MIR route checks the crate as that rustc compiles it. The
  crate needs nothing of 1.98 outside Verus's own checks (vstd's unstable
  features are on only when Verus verifies), and it builds with both.
  `MIR_JSON_DIR` names the install (`bin/` and `rlibs/`, the standard
  library translated by `mir-json-translate-libs`).
- `saw-build` is `cargo test`'s build, so the crate is compiled with
  `cfg(test)`; its unit tests are in the MIR too, and the functions proved
  are the same source.
- At `-O0` rustc's MIR inliner is off, so the `#[inline(always)]`
  functions stay calls, as in the bitcode (SAW applies the sigmas'
  overrides 64 times in `compress`).
- **Names** are Rust paths: `foundation_verus::aes::aes_impl::x_times`. A
  generic instance has a hash in its name, and
  `mir_find_name crate path [mir_const mir_u32 {{ 128 : [32] }}]` finds it.
- **Types are Rust's**: an `AESWord` is `mir_array 4 mir_u8`, a slice
  `mir_slice_value` of an allocation, a `&mut` a `mir_alloc_mut`. The
  contracts are those of NSA's template.

## Running it

There is **no `llvm_unsafe_assume_spec` or `mir_unsafe_assume_spec`**:
every override is a proof in the same run, and `check-saw.sh` refuses to
run if a script under `saw/` contains one. Nor is there an **`admit`** (or
`assume_unsat`, `assume_valid`), matched as a word anywhere in the
scripts, comments included.

```console
$ PATH=<saw-1.6>/bin:$PATH MIR_JSON_DIR=<mir-json> scripts/check-saw.sh   # both routes; writes saw/results.txt
$ ... scripts/check-saw.sh --print                                       # run, print the record, write nothing
$ SAW_ROUTE=llvm ... scripts/check-saw.sh --print                        # one route only (llvm or mir)
```

`<saw-1.6>` is SAW's 1.6 release with its solvers, and `<mir-json>` an
install of mir-json 8cbf9af ([bootstrap.md](bootstrap.md)). A one-route
run is never a record: the script requires `--print` with it.

**A memory cap on every `saw` run**, as the SPARK crate's: each runs in
its own systemd scope, `MemoryMax=10G`, `MemorySwapMax=0`
(`SAW_MEMORY_MAX` overrides the 10G). A run killed by the cap is a
failure, and a negative control killed by it does not count as failing.

**The negative controls**, `saw/llvm/negative/*.saw` and
`saw/mir/negative/*.saw`, the SPARK crate's eight, each of which must fail
with a counterexample:

- `x_times` against the shift without the reduction: `b = 128`;
- `sub_bytes` against `InvSubBytes`;
- `expand_key` at 128 against `KeyExpansion` of the key words reversed;
- `encrypt_block` at 256 against `Cipher` of the round keys reversed;
- `decrypt_block` at 128 against `InvCipher` of the round keys reversed;
- `compress` against `step` with the feed-forward adding `h`'s words
  reversed (`step h m - h + reverse h`);
- `hash` at 56 bytes against `hash` of the message's bytes reversed;
- `hmac_sha256` at a 100-byte key and a 3-byte text against `HMAC` of the
  key reversed.

All but the first two run their route's script first and use its
overrides and tactics, so they show that neither the overrides nor the
uninterpreted functions make the proofs vacuous.

**The record.** Every run that passes writes `saw/results.txt`: the commit
(the tree must be clean), the date, the host, the versions of rustc,
cargo, c++filt, SAW, z3 and mir-json (with its commit and toolchain), the
memory cap, the switches, the sha256 of the bitcode and the MIR, of every
source rustc read for the bitcode (its dep-info: the crate's, vstd's and
the other dependencies'), of `Cargo.lock`, of every NSA Cryptol file
imported and of `saw/SHA256Main.cry`, each result with its tactic and
SAW's time for it, each negative control's counterexample and time, and
the wall-clock. Commit it with the change it checks. The bitcode and the
MIR (`saw/obj/`) are not tracked.

**Measured** (a `--print` run of 2026-11-01 on an x86_64 Linux machine,
16 CPUs; `results.txt` holds the recorded run): 168 proofs, 84 per route
(AES 46, SHA-256 and HMAC 38), and 16 negative controls failing as they
must, in 925 s in all. The proofs themselves take 10 s (`llvm/aes_impl.saw`),
30 s (`llvm/sha256_impl.saw`), 20 s (`mir/aes_impl.saw`) and 160 s
(`mir/sha256_impl.saw`); each proof is under a second on the bitcode but
`hmac_sha256` at (0, 0) (12 s, the whole digest evaluated on constants),
and on the MIR `hash` and `hmac_sha256` take 3 to 16 s each. Most of the
rest is the negative controls, which run their route's script first.
