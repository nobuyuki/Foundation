# Proving

English | [日本語](proving.ja.md)

How the crate is proved with Verus: the command, the resource limits, where
the spec layer and the implementation are deliberately not one-to-one, the
Cryptol's own properties re-proved in Verus, and the gates. The counterpart
of the SPARK crate's `spark/doc/proving.md`
(github.com/manthonyaiello/Foundation, tag `spark-v1.0`), with the same
sections; those with no counterpart here say why. Back to the
[README](../README.md).

## Running Verus

The crate is verified with `cargo verus verify` from `verus/`, for local
runs and for every record alike:

```console
$ cd verus
$ cargo verus verify
verification results:: 326 verified, 0 errors
```

Verus `0.2026.10.16.bf5bb51` is pinned in `Cargo.toml`
(`[workspace.metadata.verus]`), with Rust `1.98.1` (`rust-toolchain.toml`)
and `vstd =0.0.0-2026-10-11-0230` (`Cargo.toml`), and the three move
together. A full run at `d59a3f0` takes about 14 s on a 16-CPU x86_64 desktop; the slowest module, `aes::sbox_entries`, takes
about 12 s on its own. One module is verified with

```console
$ cargo verus focus -- --verify-only-module aes::sbox_entries
```

Cargo decides whether to re-run Verus from the crate's contents, so
touching a file does not re-verify it; `cargo clean -p foundation_verus`
does. A plain `cargo build` must also succeed: ghost code (`spec`,
`proof`, `ghost` variables) is erased, and `use`s needed only by ghost code
are behind `#[cfg(verus_only)]`.

The SPARK crate's `scripts/prove.sh` (the one way to call gnatprove, which
refuses level and timeout switches and checks that the run wrote its
results anew) has no counterpart: `cargo verus verify` takes its settings
from the sources, and reports every function it checked in one line.

Verus `bf5bb51` panics (in its interpreter) on an `assert(...) by
(bit_vector)` that indexes an array parameter: the panic of Verus issue
[#3076](https://github.com/verus-lang/verus/issues/3076), there reached
from `by (compute)`. No proof of the crate is written that way.

## Levels

The SPARK crate commits a proof level per unit in its GPR. Verus has no
levels: each query has a resource limit, `rlimit`, which a function can
raise with `#[verifier::rlimit(n)]`. **No function raises it**: every
proof is within Verus's default. The heaviest, measured by rlimit count,
are `sha2::sha256_stream::lemma_update` (about 5M), `aes::aes_impl::expand_key`
and `aes::properties::MixColumnsStepInverts` (about 3M each). The rlimit
is counted by the solver's own steps, not by time, so a proof does not
time out on a loaded machine (the SPARK crate's "the local default is
marginal on a loaded machine" has no counterpart).

## The board

Omitted: the crate has no board. The SPARK crate's `scripts/board.py`
counts, per Cryptol function, its spec, its FFI check, its proof, its SAW
results and its holes, from gnatprove's per-unit results. Verus reports
only the totals (326 verified, 0 errors), and a function that fails is an
error, so a board of proof results would add little; the FFI, SAW,
coverage and mutation records are each kept apart
([ffi.md](ffi.md), [saw.md](saw.md), [coverage.md](coverage.md)).

## Where spec and implementation are not one-to-one

The spec layer mirrors the Cryptol declaration by declaration; the
implementation is shaped for execution. Mostly there is one executable
function per spec function, proved equal to it. In the places below there
is not, by design, as in the SPARK crate. None is a hole or a missing
proof.

| row | covered by | why this is the design |
|---|---|---|
| `AES::SBox::affine`, `GF2::inverse (AES)` | `aes_impl::sub_byte`'s postcondition is `SBox()[b]`, the table (FFI: `SBox` `:exhaust` 256). `properties::SBoxCorrect` proves `affine(b) == SBox()[b]` for every byte, from `sbox_entries` | As in the SPARK crate: the implementation reads the S-box table, and SBox.cry states `SBoxCorrect` relating it to `affine`, built on `inverse` |
| `SHA2::Preprocessing::pad (SHA-256)` | `sha256_stream::hash`'s postcondition is the spec's `hash`, which is defined through `pad`. `finalize` writes only the padded message's last one or two blocks (`tail_pad`), and `lemma_final` proves them those of `pad_bytes(M)`, which `lemma_pad_bytes_bits` proves the bytes of `pad` | As in the SPARK crate: a streaming hash never builds the padded message. Unlike it, `pad` is not FFI-checked or SAW-proved on its own, as a spec function cannot be executed ([ffi.md](ffi.md)) |
| `SHA2::Functions::Ch`, `Maj`, `SIGMA_256_0/1`, `sigma_256_0/1`; `SHA2::Notation::ROTR`, `SHR`; the constants `K_256`, `H0_256` | the executable twins of the same names in each module's `exec`, each proved equal to its spec function | The SPARK crate's spec functions on `Unsigned_32` are executable, and are the implementation (its kind `impl = spec`). A Verus `spec fn` is not compiled, so each has a twin with the same body |
| `SHA2::Main::hash (SHA-256, bytes)` | `sha256_stream::hash`, proved equal to `sha256_bytes::hash_bytes` and to the spec's `hash` on the message's bits | As in the SPARK crate: `hash_bytes` is the representation layer, `hash` on the bits of a byte sequence, proved equal to it (`lemma_hash_bytes`) |
| `HMAC::Main::HMAC_init (SHA-256)` | `hmac::sha256_impl::init_key`, proved to compute the spec function `K0`, which `lemma_K0` proves `HMAC_init` on the bits | The SPARK crate's contracts call its executable `Init_Key` and `Xor_Pad`; a Verus contract cannot call executable code, so `K0` and `xor_pad` are spec functions with executable counterparts |

The parts of the implementation that SAW does not prove on their own are
in [saw.md, "What SAW proves on its own, in place, or not at all"](saw.md#what-saw-proves-on-its-own-in-place-or-not-at-all).

## The Cryptol's own properties, re-proved

`aes::properties` states and proves, of the Verus spec layer, the same 13
of the 15 properties that `algorithms/AES` states about itself as the
SPARK crate's `AES.Spec.Properties` (`GF28MultiplicationCorrect`,
`SBoxCorrect`, `SBoxInverts`, the `*Inverts` of `Cipher.cry`,
`InvCipherEquivalence`, `EncryptInverts`, ...). `SBoxPolynomialIsIrreducible`
and `inverseCorrect` are not stated, as in the SPARK crate.

**Here they are not optional.** The SPARK crate keeps them as a cross-check
of its spec layer, which SAW already proves equal to the Cryptol at k =
128, 192 and 256. SAW cannot do that here: a Verus spec function is not
compiled, so SAW proves only the implementation layer ([saw.md](saw.md#the-spec-layer)),
and these properties are the only check, by proof, that the spec layer
behaves as the Cryptol says it does.

**They are cheap.** The four that take a key size are generic in the const
`k` and require `Key k`, so each is proved once for all key sizes (the
SPARK crate states them over its dispatchers). `SBoxCorrect`, the SPARK
crate's slow unit (about 26 min cold, 1 h 40 min in CI), is evaluated by
Verus's interpreter, one row of FIPS 197's Table 4 at a time, in about
12 s ([`aes::sbox_entries`](../src/aes/sbox_entries.rs) says how). How each
is proved, and where the proofs differ from the SPARK crate's, is in the
module's doc comment ([`aes::properties`](../src/aes/properties.rs)).

## Slow proofs

Omitted: no proof is slow. The SPARK crate proves its slow unit
`SBox_Entries` on demand, and its gate detects when an input of that proof
changes. Here the counterpart `aes::sbox_entries` is part of every run.

## Gates

The SPARK crate's CI runs its gates on every change. This crate has no
CI: the gates are run by hand, the same way:

- `scripts/check-trust-surface.sh`: every site in `src/` that Verus does
  not prove (code outside `verus!`, `assume`, `admit`, `axiom fn`, an
  external body or specification, a termination exemption, a cfg the
  verifier does not see, `unsafe`, a foreign binding, a call of a vstd
  function that vstd does not prove) is listed with a reason in
  `scripts/trust-surface.txt`. Only the FFI exports of `src/ffi/` are
  there (100 entries); nothing is assumed.
- `cargo verus verify`: every function verified, `0 errors`. The SPARK
  crate's `scripts/check-proof.sh` also fails on a unit missing from
  gnatprove's report or an entity it skipped; Verus verifies every function
  in `verus!` and reports an error for any it cannot, and what is outside
  `verus!` is the trust surface's.
- `cargo build` and `cargo test` (FIPS 197's, FIPS 180-4's and RFC 4231's
  vectors, and the chunked SHA-256 against the one-shot), without warnings.

The SPARK crate's documentation gates (`check-doc-placement.sh`,
`check-docs.sh`, gnatdoc) and its slow-proof gate (`test-slow-proofs.sh`)
have no counterpart. There is no slow proof, and the documentation gate
is not set up. Its nearest counterpart is rustc's `missing_docs` lint:
`RUSTFLAGS="-W missing_docs" cargo build` reports no undocumented item,
but it sees only what a plain build compiles, not the spec
and proof functions, and the crate does not enable it.
