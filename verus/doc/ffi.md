# The FFI check against the Cryptol

How the crate's executable functions are called from Cryptol through its
`foreign` interface and compared with NSA's Cryptol, by exhaustive or random
testing. The counterpart of the SPARK crate's `spark/doc/ffi.md`
(github.com/manthonyaiello/Foundation, tag `spark-v1.0`). Back to the
[README](../README.md).

## The FFI harness

The FFI check is the machine check that the crate computes what the Cryptol
says: the executable functions are exported through C, called from Cryptol by
`foreign`, and compared with the NSA functions they implement, with `:exhaust`
or `:check`. It is testing, not proof.

```console
$ FFI_JOBS=3 scripts/check-ffi.sh             # build, run every property
$ scripts/check-ffi.sh prop_Impl_Dot          # only these properties
```

It needs Cryptol 3.6 built with FFI support (`cryptol --version` says "FFI
enabled") on `PATH`, or named by `CRYPTOL`, with z3 on `PATH` (Cryptol's type
checker needs it; the `with-solvers` release has both in its `bin/`), cargo
with the toolchain of `rust-toolchain.toml`, and python3. It sets
`CRYPTOLPATH` to the repository root and `cryptol/`, so a property module
imports `algorithms::AES::GF28` by its NSA name. The script is the SPARK
crate's, with cargo for gprbuild; its macOS steps (`.dylib`, an ad hoc
signed copy of a hardened-runtime Cryptol) are kept but have not been run.

**The pieces.**

- `ffi/Cargo.toml` builds the FFI library,
  `target/release/libfoundation_verus_ffi.so`: a `cdylib` whose `lib.rs`
  re-exports the crate's `ffi` module. It is its own Cargo workspace, so
  `cargo verus verify` and `cargo build` in `verus/` do not build it, and its
  release profile keeps overflow checks and debug assertions. (The SPARK
  crate's `foundation_spark_ffi.gpr`.)
- `src/ffi/`: per Cryptol module, one Rust module (`ffi::aes_gf28`, ...) of
  `extern "C"` exports, plus the helpers in `src/ffi/mod.rs`. Each file is a
  `foreign-binding` entry in `scripts/trust-surface.txt`, and each export an
  `outside-verus` and an `unsafe` entry.
- `cryptol/Verus/<path>/<File>.cry`: a module (`Verus::AES::GF28`) that
  declares the exports as `foreign verus_<name>` **without a Cryptol body**
  and states the properties (`verus_x_times b == xTimes b`). Cryptol loads a
  module's foreign implementations from `<File>.so` beside it;
  `check-ffi.sh` links the library there (gitignored).
- `cryptol/properties.txt`: module, property, function, mode, test count.
- `scripts/check-ffi.sh`: builds, links, runs each property in its own
  `cryptol -b`, writes `target/ffi/ffi-results.txt` (the SPARK crate's
  format), and keeps each run's script and output in `target/ffi/run/`.

**What is exported: the executable functions only.** The SPARK crate builds
its library with `-gnata`, so that its ghost spec layer executes, and checks
each spec function directly against the Cryptol it transcribes, as well as
each executable function. A Verus `spec fn` is not compiled at all, so the
crate exports
its executable functions (the implementation layers, and the executable
copies of spec functions such as `sha2::functions::exec`), each proved equal
to the spec function it implements, and the spec layer is checked through
those proofs: a sample on which an export agrees with the Cryptol is one on
which the spec function does. The SPARK crate already draws the bulk of its
random tests on the executables for this reason ("Targeted, not volume" in
its doc).

What that leaves unchecked against the Cryptol, compared with the SPARK
crate (68 of its 141 properties have no counterpart; `properties.txt` lists
them):

- the spec functions with no executable counterpart, checked only as parts
  of the functions above them: Preprocessing.cry's `pad` and `parse`
  (the SPARK crate's `prop_pad`, `prop_parse`), and the prelude's generics
  (its `SPARK/Prelude.cry`: `foldl`, `bit`, `join`, `split`, `pmult`,
  `pmod`, `pdiv`, ...), which have no counterpart module here;
- SHA-256 and HMAC on bit strings whose length is not a whole number of
  bytes (`prop_hash_bits`, `prop_HMAC_bits`): the executables work on bytes,
  and are proved equal to the spec only there;
- the spec's own functions where an executable checks the same Cryptol
  (`prop_Dot` / `prop_Impl_Dot`, `prop_Cipher128` / `prop_Encrypt_Block128`,
  `prop_KeyExpansion128` / `prop_Expand_Key128`, `prop_step` /
  `prop_Compress`, `prop_HMAC_init` / `prop_Init_Key`, and so on): only the
  second of each pair is here.

Where a SPARK spec property also checked NSA's Cryptol itself against
published vectors (`prop_hash_FIPS`, `prop_HMAC_RFC4231`), that half is
kept, in the executable's property (`prop_Stream_Hash_FIPS`,
`prop_HMAC_SHA256_RFC4231`), as `fips197C` is in Main.cry's.

**The exports.** Each export reads Cryptol's arguments into Rust values,
checks at run time each precondition of the function it calls that
Cryptol's types are meant to ensure (`Key k`; `1 <= i <= 10` for `rcon`;
SHA-256's `Max_Bytes` and HMAC's `Max_Text`; a sorted chunking within the
message), calls the proved function, and writes its result. A failed check
panics, and a panic in an `extern "C"` function aborts Cryptol, so the run
fails. Code with logic of its own is inside `verus!` and proved: the
incremental HMAC's loop over a chunking is `ffi::hmac_sha256::hmac_chunked`,
proved equal to the spec's `HMAC` (the SPARK crate's
`FFI.HMAC_SHA256_Impl.HMAC_Chunked`; SHA-256's is the crate's own
`sha256_stream::hash_chunked`). The SPARK crate needs two units per module
(a ghost shim and an export that imports it by GNAT's link name) because
its spec is ghost; the exports here call ordinary functions, so there is one
module per Cryptol module, and no link-name trick.

**What a pass requires.** As in the SPARK crate, Cryptol 3.6 can report a
run that never called the library without failing it, so `check-ffi.sh`
passes a property only when:

- `cryptol` exits 0, with no `ERROR`, counterexample or `[error]`;
- the property's module printed `Loading dynamic library <File>.so`. A
  body-less `foreign` whose library is missing does not fail the load:
  each call is then an evaluation error. With a body, the missing library
  would make the property compare the Cryptol with itself, and pass;
- no module outside `cryptol/` loaded a dynamic library. NSA's `foreign`
  declarations with Cryptol bodies (`AES::Cipher`, `AES::KeyExpansion`,
  `Keccak::StepMappings`) fall back to those bodies, because the
  repository's `.so` files are symlinks into the unbuilt `rust/*/target/`.
  If someone builds that Rust, the comparison would silently become Verus
  against NSA's Rust, so `check-ffi.sh` fails instead;
- Cryptol reports `Passed N tests.` with N the planned count, and `Q.E.D.`
  for `:exhaust`.

**Passing bit sequences.** Cryptol's C calling convention passes `[K]` only
for a constant `K <= 64` (as `uint8_t` .. `uint64_t`), and sequences of such
words (`[n][8]` as `uint8_t *`, with each size variable passed first as a
`size_t`); a sequence result is written through a pointer after the
arguments, and `()` passes nothing. An arbitrary-length `[l]` is rejected.
So Main.cry's `[k]` key and `[128]` block are split into bytes on the
Cryptol side and the result joined: ``join (verus_encrypt`{k} (split key)
(split in))``, which is what `aes_impl::main::encrypt` takes and is proved
about. SHA-256 and HMAC take messages as `[n][8]` and are compared with
``SHA256::hash (join M)``. A length that depends on a type is read only up
to what Cryptol passed: `[Nr k + 1]Block` as `k / 32 + 7` blocks, after
`Key k` is checked.

**Targeted, not volume.** The properties and their test counts are the
SPARK crate's for its executables: the byte-level functions exhaustively
(`xTimes`, `(•)`, the S-boxes, `Rcon`), the round transformations at
10,000, the block ciphers and the key schedule at 1,000 per key size, the
byte-level AES at 1,000 composed (`implEncrypt`) and 100 whole
(`execEncrypt`), SHA-256 at the padding boundaries and a fixed list of
longer lengths (drawn by the SPARK crate), HMAC under keys of 63, 64 and 65
bytes and at the boundary key lengths, random chunkings of 12 cut points,
and the published vectors (FIPS 197 Appendices A to C, Tests.cry's,
FIPS 180-4's, RFC 4231's). N is per property in `properties.txt`.
