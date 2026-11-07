# AES: the Verus spec layer beside NSA's Cryptol

English | [日本語](aes.ja.md)

How the crate implements AES (FIPS 197) at 128, 192 and 256-bit keys and
how it is tied to NSA's Cryptol in `algorithms/AES/`. The counterpart of
the SPARK crate's `spark/doc/walkthroughs/aes.md`
(github.com/manthonyaiello/Foundation, tag `spark-v1.0`), with the same
sections, shortened: each says what the Verus code does and where it
differs, and the code, with its doc comments, is in the files it names.

There are two layers, and lemmas between them:

- **The spec layer** (`src/aes/`: `types`, `gf28`, `gf2`, `sbox`,
  `key_expansion`, `cipher`, `main`), one module per Cryptol module, the
  `spec fn`s named as the Cryptol's. `gf2` is the part of
  `shared/algebra/Polynomial/GF2.cry` that SBox.cry imports. The
  properties the Cryptol states about itself are proved in `properties`
  and `sbox_entries`.
- **The implementation layer** (`aes_impl`, `aes_impl::main`): the key
  schedule, the round transformations and the block ciphers in place on
  bytes, each `ensures` the spec function it implements; and AES on key
  and block bytes, proved equal to Main.cry's `Encrypt` and `Decrypt` on
  the bits. The lemmas are in `lemmas` and `main_lemmas`.

```text
  NSA Cryptol (algorithms/AES/*.cry)
        ^                     ^
        | FFI (testing)       | SAW, k = 128, 192, 256
        |                     | (bitcode and MIR)
        |                     |
  spec layer (spec fn) ---- properties: the Cryptol's own, re-proved
        ^                     |
        | Verus, all inputs   |
        |                     |
  aes_impl, aes_impl::main (executable)
```

As for SHA-256, the SPARK crate's arrows from the spec layer to the
Cryptol (the FFI check and SAW on its ghost code) are missing here: a spec
function is not compiled ([ffi.md](../ffi.md)). That makes the re-proved
properties the only check, by proof, of the spec layer's own behaviour
([proving.md](../proving.md#the-cryptols-own-properties-re-proved)).

## Reading the notation

As in [sha-256.md](sha-256.md#reading-the-notation). In
addition: Cryptol's `{k} (Key k) => ...` is a function generic in
`const k: u32` with `recommends Key(k as nat)` (spec) or `requires`
(exec); ``f`{128}`` is `f::<128>`; `xs @@ is` is the prelude's
`bulk_index`; `arbitrary()` is a value of which nothing is known.

## The spec layer, declaration by declaration

### Types (`Types.cry`)

[`types.rs`](../../src/aes/types.rs). `Key(k)` is Types.cry's type
constraint, clause for clause; `Nk` and `Nr` are spec functions of `k as
nat`. A `Block` and an `AESWord` are `Seq<u8>` of lengths 16 and 4, and the
lengths are `recommends` of the functions that take them. `split` and
`join` between a block and its four columns are here, as in the SPARK
crate's `Types`.

**Key-size polymorphism** is where the two crates differ most. Ada has no
type-level numbers, so the SPARK crate has a generic `AES_K` for the `{k}`
functions, three instances, and a ghost `Spec.Dispatch` to select one by a
run-time key size. Here `k` is a const generic: a value in exec code as
well as in spec code, so one implementation generic in `k` is proved once
against the spec at the same `k`, and none of the three is needed.

### GF(2^8) (`GF28.cry`)

[`gf28.rs`](../../src/aes/gf28.rs). `dot(b, c)` (Cryptol's `•`) is the
prelude's `pmod(pmult(b, c), m)` at `[8] -> [8] -> [15]` and `[15] -> [9]
-> [8]`, computed in `u16` and cast to `u8`; `lemma_dot` proves the cast
loses nothing. `xTimes(b) = dot(b, 2)`.

### GF(2) polynomials (`shared/algebra/Polynomial/GF2.cry`)

[`gf2.rs`](../../src/aes/gf2.rs). `inverse` through `pgcd`, at the types
SBox.cry uses (`a : [8]`, `p : [9]`). `pmult` and `pdiv` are the
prelude's (the SPARK crate states both inline, for measured reasons).
`inner`, local to `pgcd` in the Cryptol, is top-level, and its recursion
is `decreases s[3] when is_state(s) via inner_decreases`: each step
replaces `r'` by a remainder modulo `r'`, which `lemma_division` proves
smaller.

### S-boxes (`SBox.cry`)

[`sbox.rs`](../../src/aes/sbox.rs). `SBox` and `InvSBox` are the tables,
entry for entry. `affine(b)` is stated as the Cryptol states it, on bit
sequences, through the prelude's `reverse`, `join` and `value`.

### Key expansion (`KeyExpansion.cry`)

[`key_expansion.rs`](../../src/aes/key_expansion.rs). `RotWord`,
`SubWord`, `Rcon` (element 0, Cryptol's `undefined`, is `arbitrary()`; the
SPARK crate's table has no element 0). The self-referential sequence `w`
is a recursive function of the index `i` and of the key that the Cryptol
closes over, `decreases i when Key(k) && 0 <= i`. `KeyExpansion::<k>`
regroups the words into `Nr k + 1` round keys. NSA declares `KeyExpansion`
`foreign`, with Rust behind it; this mirrors its Cryptol body.

### Round transformations and ciphers (`Cipher.cry`)

[`cipher.rs`](../../src/aes/cipher.rs). `SubBytes`, `ShiftRows`,
`MixColumns` (through `MixColumnsStep` on each column), `AddRoundKey`,
their inverses, `Round`, `InvRound`, `InvRound'` (`InvRound_prime`: `'`
is not allowed in a Rust name), and `Cipher`, `InvCipher` and
`InvCipher'`, each the prelude's `foldl` of a round over the middle round
keys, with `[w0] # ws # [wr]` as `ws[0]`, `ws.subrange(1, Nr)`, `ws[Nr]`.
NSA declares `Cipher` `foreign`; this mirrors its Cryptol body.

### The top level (`Main.cry`)

[`main.rs`](../../src/aes/main.rs). Main.cry's record ``AES`{k}`` is
`struct AES<const k: u32>` with the associated spec functions `Encrypt` and
`Decrypt`, on bit sequences, and `AES128` is `type AES128 = AES<128>`. The
`split` and `join` between bits, bytes and words are `split_block`,
`join_block` and `split_key`.

### The Cryptol's own properties (`aes::properties`)

[`properties.rs`](../../src/aes/properties.rs). 13 of the 15, as in the
SPARK crate, each a `proof fn` named as the property, whose `ensures` is
its body. The four that take a key size are proved once for all `k`.
`SBoxCorrect` is evaluated by Verus's interpreter (`by (compute_only)`)
one row of the table at a time in [`sbox_entries`](../../src/aes/sbox_entries.rs),
on trait-free copies of `inverse`'s functions proved equal to them;
`SBoxInverts` is evaluated too. `MixColumnsStepInverts` rewrites each `•`
by a constant into `xTimes` and leaves the rest to one `bit_vector` query,
in place of the SPARK crate's linearity lemmas. Why each differs is in the
module's doc comment.

## The Cryptol prelude in Verus

AES uses `foldl` (the round folds, GF28MultiplicationCorrect), `@@`
(SubBytes, ShiftRows and their inverses), `join` and `split` between bytes
and bits, `@` and `head` on words, `pmult`, `pmod`, `pdiv` and `reverse`,
all from `src/cryptol/`; nothing is written out
([cryptol-prelude.md](../cryptol-prelude.md)).

## The implementation layer and the proof chain

### Dispatch: one implementation, three key sizes

Omitted: there is no dispatch. The functions with a `{k}` in the spec are
generic in the same const `k` and require `Key(k)`, so the one
implementation serves the three key sizes and its proof is one proof
(see "Types" above).

### The executable functions and their contracts

[`aes_impl.rs`](../../src/aes/aes_impl.rs). `x_times`, `dot`, `sub_byte`,
`sub_word`, `rot_word`, `xor_word`, `rcon`, `expand_key::<k>`,
`sub_bytes`, `shift_rows`, `mix_column`, `mix_columns`, `add_round_key`,
`round`, their inverses, `inv_round_prime`, `encrypt_block::<k>`,
`decrypt_block::<k>` and `decrypt_block_prime::<k>`. A block is
`Block = [u8; 16]` and a word `AESWord = [u8; 4]`, whose views are the
spec's. `expand_key` returns `[[u8; 16]; 15]`, the round keys of the
largest key, as NSA's Rust does; the spec sees the first `Nr k + 1`
(`round_keys`), and the key's first `Nk k` words (`key_words`), as Rust
has no array whose length is an expression in `k`.
[`aes_impl/main.rs`](../../src/aes/aes_impl/main.rs): `encrypt::<k>` and
`decrypt::<k>` take the key's `k / 8` bytes and a block, and ensure
`join_block(r@) == AES::<k>::Encrypt(join_key(key@), join_block(input@))`.

### How Verus gets from the code to the spec

The round loops' invariant is the prelude's `foldl_take` of the rounds
over the first `r` round keys: one more round key is one more round, by
definition, so the SPARK crate's `*_Eq`, `Take_Eq` and `Snoc` lemmas are
not needed. `MixColumns` and `InvMixColumns` are `xTimes` alone, proved
against `•` by `lemma_dot_column` and `lemma_dot_inverse_column`; rows 1
to 3 of `InvMixColumnsStep` need the xor reordered (`lemma_xor_rotate`,
`bit_vector`). The S-box tables and `Rcon` are spec functions, so the
executable `S_BOX`, `INV_S_BOX` and `rcon` are proved equal to them.
`main_lemmas::lemma_split_join_key` carries the bytes of the key to the
spec's `split_key`.

## How it is checked

### Verus: implementation = spec, for all inputs

Every function above, for every key and block at k = 128, 192 and 256.

### The FFI check: executables against NSA's Cryptol, by testing

[`cryptol/Verus/AES/`](../../cryptol/Verus/AES): `xTimes`, `•`, the
S-boxes and `Rcon` exhaustively; the round transformations at 10,000;
the key schedule and the block ciphers at 1,000 per key size;
`encrypt` and `decrypt` composed and whole; FIPS 197's Appendices A to C.
The SPARK crate's properties of the spec functions have no counterpart
([ffi.md](../ffi.md)).

### SAW: bitcode and MIR = NSA's Cryptol, at k = 128, 192 and 256

[saw.md, "AES"](../saw.md#aes): every executable function above, its
leaves to `main::encrypt` and `main::decrypt`, against the Cryptol, at the
three key sizes, on the LLVM bitcode and on the MIR. As all of AES's sizes
are these three, this is a proof for all inputs, of the executables.

### What is proved, and what is only tested

Proved for all inputs: the executables equal the spec layer (Verus), and
equal NSA's Cryptol (SAW, at the three key sizes). Not proved: that the
spec layer equals NSA's Cryptol; it is checked by reading, by the
re-proved properties, and through the executables. Timing is not: the
S-box is a table lookup indexed by key and state bytes, as in the SPARK
crate's `main` (its constant-time branch has no counterpart).

## Where spec and implementation are not one-to-one

As in [proving.md](../proving.md#where-spec-and-implementation-are-not-one-to-one):
`affine` and `inverse` have no executable counterpart; `sub_byte` reads
the table, which `SBoxCorrect` proves equal to `affine`.
