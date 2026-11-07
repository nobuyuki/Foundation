# HMAC-SHA-256: from NSA's Cryptol to Verus

English | [日本語](hmac-sha-256.ja.md)

How the crate implements HMAC-SHA-256 (FIPS 198-1) and how it is tied to
NSA's Cryptol of HMAC, `algorithms/HMAC/Main.cry`. The counterpart of the
SPARK crate's `spark/doc/walkthroughs/hmac-sha-256.md`
(github.com/manthonyaiello/Foundation, tag `spark-v1.0`), with the same
sections, shortened: each says what the Verus code does and where it
differs, and the code, with its doc comments, is in the files it names.
HMAC uses SHA-256 only through its interface; SHA-256 has its own page,
[sha-256.md](sha-256.md).

## The three layers

- **The spec layer** (`src/hmac/`: `mod.rs`, `main`, `sha256`), `spec fn`s
  that mirror the Cryptol: `HMAC`, `HMAC_init`, `opad` and `ipad` have the
  same names, arguments and case structure as in Main.cry. The trait
  `hmac::main::Parameters` plays the part of the Cryptol function's hash
  arguments and size parameters, and its implementation `hmac::sha256::SHA256`
  that of `packaging/Hash.cry`'s `HMAC` at SHA-256.
- **The implementation layer** (`hmac::sha256_impl`), executable. It works
  on bytes, and hashes through two streaming SHA-256 contexts. Its
  `ensures` state that its results equal the spec layer's on the bits.
  Between the two sit `sha256_bytes::bits_of`, the streaming theorems of
  `sha256_stream` (`lemma_update`, `lemma_final`), and lemmas in
  `sha256_impl` itself.
- **The checks**: Verus proves implementation = spec layer for every key
  and text within the length bounds; the FFI check runs the executables
  against NSA's Cryptol; SAW proves the compiled implementation equal to
  NSA's Cryptol at a few fixed lengths.

```text
  NSA's Cryptol                              Verus
  ------------                               -----
  algorithms/HMAC/Main.cry   <-- mirrors --  hmac::main (trait Parameters, spec fn)
  packaging/Hash.cry: HMAC   <-- mirrors --  hmac::sha256 (impl Parameters)
        ^       ^                                  ^
        |       |                                  | Verus: equal on the
        |       |                                  | bits, all inputs
        |       |                            hmac::sha256_impl (executable)
        |       |                                  |  built on
        |       |                            sha2::sha256_stream (executable)
        |       |
        |       +-- FFI (random tests, RFC 4231) -- executables
        +---------- SAW (fixed lengths) ----------- bitcode and MIR of the executables
```

The chain closes as in the SPARK crate, with one link fewer: the spec
layer is compared with the Cryptol only by close reading and through the
executables proved equal to it, as it cannot be executed or compiled.

## Reading the notation

As in [sha-256.md](sha-256.md#reading-the-notation). In addition, Cryptol's
`^` on bit strings is the prelude's `bit_sequences::xor`, `#` is `Seq`'s
`+`, and ``take`{λ}`` is `.take(λ)`.

## The spec layer, declaration by declaration

### `HMAC`'s parameters: type parameters and hash arguments

[`main.rs`](../../src/hmac/main.rs). Main.cry's `HMAC` takes the hash
functions `Hk`, `Hn`, `HL` as arguments and the sizes `B`, `L` as type
parameters; here they are the trait `Parameters`, in the same order, as
in SHA-2's `main` (the SPARK crate makes them a generic's formals). The
per-call sizes `k` (the key's length), `n` (the text's) and `λ` stay per
call: `k` and `n` are the lengths of the `Seq`s, `λ` a `nat` argument.
The Cryptol gives the hashes the input types `[k * 8]`, `[B * 8 + n]` and
`[(B + L) * 8]`; here a hash takes any bit sequence shorter than
`max_length`, and the `recommends` of `HMAC` and `HMAC_init` carry those
constraints, as `packaging/Hash.cry`'s `UpperLimit` constraints do.

### The type constraints

The Cryptol's constraints on `B` and `L`, and that every hash returns
`[L * 8]`, are the `ensures` of `Parameters::type_constraints`, which
`hmac::sha256` proves (with `lemma_hash_len`). The constraints on `k`,
`n` and `λ` are `recommends`.

### `opad` and `ipad`

`opad = join(repeat(B, 0x5C))`, `ipad = join(repeat(B, 0x36))`, through
the prelude's `repeat` and `join` at bytes (`hmac/mod.rs`).

### `HMAC_init`: the key preprocessing

`HMAC_init(K)`, by cases on `K.len()` in the Cryptol's order of guards
(`k == B`, `k > B`, `k < B`): the key's bits; the hashed key padded with
zeros; the key padded with zeros. It is private in Main.cry and public
here because the implementation is proved against it, as in the SPARK
crate.

### `HMAC`

`HMAC(K, text, λ) = HL((K0 ^ opad) + Hn((K0 ^ ipad) + text)).take(λ)`,
with `K0 = HMAC_init(K)` a `let`.

### The SHA-256 instance

[`sha256.rs`](../../src/hmac/sha256.rs). `impl Parameters for SHA256`,
as `packaging/Hash.cry`'s `HMAC` instantiates Main.cry for SHA256.cry:
`B = 64`, `L = 32`, and `Hk`, `Hn`, `HL` all `sha2::main::hash::<SHA256>`,
whose bound `2 ^^ 64` bits is Hash.cry's `2 ^^ UpperLimit`.

## The Cryptol prelude in Verus

HMAC uses `repeat`, `zero`, `^` and `join` on bytes, each the prelude's
([cryptol-prelude.md](../cryptol-prelude.md)) at the types HMAC uses
(`hmac/mod.rs`). The SPARK crate's `Byte_Index` and its bounds have no
counterpart: lengths are `nat`.

## The implementation and how Verus ties it to the spec

[`sha256_impl.rs`](../../src/hmac/sha256_impl.rs).

### The one-shot MAC and the key preprocessing

`init_key(key)` returns the 64-byte K0 and ensures it is the spec
function `K0(key@)`: a key longer than 64 bytes is hashed with
`sha256_stream::hash` and padded, a shorter one padded. `lemma_K0` proves
that `K0` on the bits is `HMAC_init`. `exec::xor_pad` computes the spec
function `xor_pad`. `hmac_sha256(key, text)` ensures
`bits_of(d@) == HMAC::<SHA256>(key@, bits_of(text@), 256)`; it is `init`,
one `update` and `finalize`.

The SPARK crate's contracts call its executable `Init_Key` and `Xor_Pad`;
a Verus contract cannot call executable code, so `K0` and `xor_pad` are
spec functions that the executables are proved to compute.

### The incremental interface

A `Context` holds an inner `sha256_stream::Context`, fed K0 xor ipad and
then the text, and K0 xor opad. `init(key)` ensures `models(c, key@,
empty)`; `update(c, data)` ensures `absorbed`; `lemma_update` gives
`models(c, key, M + data)`; `lemma_final` proves that `finalize`'s MAC is
`HMAC` of the key and `M` on the bits. As in `sha256_stream`, a context
does not hold its key or text: the lemmas take them. `finished` says that
the inner context has a digest by `exists`, where the SPARK crate writes a
call of its executable `SHA256_Stream.Final`.

### What the HMAC proof rests on from SHA-256

`sha256_stream::lemma_update` and `lemma_final` (the contexts compute
`hash_bytes` of what they were fed) and `sha256_bytes::lemma_hash_bytes`
(`hash_bytes` is the spec's `hash` on the bits). Nothing else of SHA-256's
proof is used.

### How the proof goes

`lemma_hmac` proves that the outer digest of the two streams' messages
is, on the bits, the spec's `HMAC` at `λ = 256`: from the bits of
concatenations (`lemma_bits_of_append`), of zeros, of K0 (`lemma_K0`)
and of K0 xor a pad (`lemma_pad_xor_bits`). The SPARK crate's
extensionality lemmas (`Lemma_Word_Of_Ext`, `Lemma_Hash_Ext`, ...) and
`To_Bytes` have no counterpart, as `Seq` equality is equality; nor has
`Lemma_Prefix_Extends`, which the SPARK crate states apart to keep a
prover within its time.

## How it is checked against NSA's Cryptol

### The FFI check

[`cryptol/Verus/HMAC/SHA256.cry`](../../cryptol/Verus/HMAC/SHA256.cry):
`hmac_sha256` and the incremental interface (through
`ffi::hmac_sha256::hmac_chunked`, proved in `verus!`) under random keys and
texts, at the boundary key lengths (63, 64, 65 bytes), at long lengths and
on RFC 4231's vectors; `init_key` against `HMAC_init`. The SPARK crate's
properties of the spec functions (`prop_HMAC_bits`, ...) have no
counterpart ([ffi.md](../ffi.md)).

### SAW

[saw.md, "SHA-256 and HMAC-SHA-256"](../saw.md#sha-256-and-hmac-sha-256):
`hmac_sha256` against ``HMAC`{256, 64, k, 8 * n, 32} hash hash hash`` at
seven (key, text) lengths in bytes, (0, 0), (32, 3), (32, 32), (64, 3),
(64, 32), (65, 3), (100, 32), on the bitcode and on the MIR. The
incremental interface is not proved on its own: it is the same function
as the one-shot.

### What is proved for all inputs, and what is not

Proved for all inputs, by Verus: the executables equal the spec layer's
`HMAC`, for every key shorter than `2 ^^ 61` bytes, every text shorter
than `Max_Text` (`2 ^^ 61 - 64` bytes), and every chunking. Not proved:
that the spec layer equals NSA's `HMAC` at every length (testing, and SAW
at seven lengths), and HMAC on texts that are not a whole number of bytes
(the executables work on bytes).

## Where spec and implementation are not one-to-one

As in [proving.md](../proving.md#where-spec-and-implementation-are-not-one-to-one):
`HMAC_init` is implemented by `init_key` through the spec function `K0`,
and the pads by `exec::xor_pad` through `xor_pad`, because a contract
cannot call executable code.
