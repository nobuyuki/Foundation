# The Cryptol prelude in Verus

The Cryptol built-ins the spec layers are written in (`foldl`, `@`,
`join`, `split`, `pmult`, ...), stated once in Verus as spec functions and
lemmas. The counterpart of the SPARK crate's `spark/doc/cryptol-prelude.md`
(github.com/manthonyaiello/Foundation, tag `spark-v1.0`), with the same
sections. Back to the [README](../README.md).

## The Cryptol prelude

`src/cryptol/` (`foundation_verus::cryptol`) states, once and under their
Cryptol names, the Cryptol built-ins the spec layers are written in. A spec
module calls them where the Cryptol calls the built-in, so a reviewer checks
each translation from Cryptol to Verus here, once, and the spec bodies are
left with the algorithm. Every function is a `spec fn` (with its lemmas as
`proof fn`), generic over the word type where the Cryptol is polymorphic in
the width: the trait [`Word`](../src/cryptol/mod.rs), implemented for `u8`,
`u16` and `u32`, is the counterpart of the SPARK crate's generic formal
`type Word is mod <>`.

| module | Cryptol | stated from |
|---|---|---|
| [`folds`](../src/cryptol/folds.rs) (`foldl`, `foldl_take`) | `foldl f z xs`, ``foldl f z (take`{N} xs)`` | Cryptol.cry:1146 (a primitive) and its example `((0 + 1) + 2) + 3` |
| [`enumeration_folds`](../src/cryptol/enumeration_folds.rs) (`foldl`) | `foldl f z [from ..< to]` | the same, and RefMan BasicTypes.rst:169 |
| [`words`](../src/cryptol/words.rs) (`bit`, `bit_in`, `head`) | `x @ j`, `head x` on a word `[w]` | Cryptol.cry:900 (a primitive), :796 (bit order), :855 (head's body) |
| [`join_split`](../src/cryptol/join_split.rs) (`join`, `split_at`, `value`) | `join`, `split` between `[n][w]` and `[n * w]` | Cryptol.cry:815 and :822 (primitives, documented as inverses) |
| [`bit_sequences`](../src/cryptol/bit_sequences.rs) (`zero`, `literal`, `xor`) | `zero : [n]`, `` `v : [n] ``, `^` on `[n]` | Cryptol.cry:304 (a primitive), RefMan BasicSyntax.rst:349 |
| [`sequences`](../src/cryptol/sequences.rs) (`reverse`, `repeat`) | `reverse`, `repeat` | Cryptol.cry:828 (a primitive), :1215 (repeat's body) |
| [`bulk_indexing`](../src/cryptol/bulk_indexing.rs) (`bulk_index`) | `xs @@ is` | Cryptol.cry:906 (its body) |
| [`numeric`](../src/cryptol/numeric.rs) (`ceil_div`, `ceil_mod`) | the type operators `/^`, `%^` | Cryptol.cry:135 and :141 (primitives) |
| [`polynomial_products`](../src/cryptol/polynomial_products.rs) (`pmult`) | `pmult` | Cryptol.cry:1005 (a primitive); RefMan BasicSyntax.rst:352 |
| [`polynomial_remainders`](../src/cryptol/polynomial_remainders.rs) (`pmod`) | `pmod` | Cryptol.cry:1015 (a primitive) |
| [`polynomial_quotients`](../src/cryptol/polynomial_quotients.rs) (`pdiv`) | `pdiv` | Cryptol.cry:1010 (a primitive) |

Line numbers are those of Cryptol 3.6.0's `lib/Cryptol.cry`, as in the
SPARK crate's table, whose rows these are. The choices a reviewer should
know:

- **Folds recurse from the last element**, as the SPARK prelude's do:
  ``foldl f z (take`{N} xs) = f (foldl f z (take`{N - 1} xs)) (xs @ (N -
  1))``. It is the shape of the implementation's loops, whose invariant
  after N steps is the fold of the first N, so the step is the definition.
- **Closures are closures** (a difference from the SPARK crate). A
  Cryptol fold's function may mention local values (SHA-2's `step3`
  mentions the block). Ada's generic formal functions are not closures, so
  the SPARK prelude passes the value as an explicit first argument; Verus
  has `spec_fn` closures, so here the function is a closure, as in the
  Cryptol.
- **Words are numbers**, as in the SPARK crate: a `[w]` is a Rust unsigned
  integer (the `Word` trait), bit `j` of a word has weight
  `2 ^^ (w - 1 - j)`, and `join_split::value` is the conversion from bits
  to a word that Cryptol needs no name for. The polynomial modules read a
  word as a polynomial the same way, the bit of weight `2 ^^ i` the
  coefficient of `x ^^ i`.
- **Lengths and indices are `int` and `nat`** (a difference). They are
  unbounded, so the SPARK crate's 128-bit `Bit_Index` and its bounds have no
  counterpart.
- **Type parameters.** Cryptol's numeric type parameters `{u, v}` are
  const generics where Rust allows them; where the Cryptol writes an
  expression in them (`1 + v`), they are `nat` arguments, as Rust's const
  generics cannot be computed. `remainders` and `quotients` do not take
  `v`, where the SPARK crate instantiates `pdiv` at `V - 1`.

**Who uses it.** SHA-2 (`foldl` over the blocks and over the rounds, `@`,
`join`, `split`, `zero`, the literal of `pad`, `/^` and `%^`), HMAC
(`repeat`, `zero`, `^`, `join` on bytes) and AES (`foldl` for the round
folds and GF28MultiplicationCorrect, `@@`, `join` and `split` between bytes
and bits, `@` and `head` on words, `pmult`, `pmod`, `pdiv` and `reverse`).

The SPARK crate's account of what moved into its prelude and what stayed
written out, each for a measured reason (a wrapper that cost a prover
steps, `pmod` returning a `Byte`, `pmult` at `[9] x [9]` in the slow
`SBox_Entries`, `pdiv`'s leading term, `Types.Split`), is omitted: here
nothing stayed written out. GF28's `pmod` and GF2's `pmult` and `pdiv` are
the prelude's. The one exception in kind is `SBoxCorrect`
([proving.md](proving.md#the-cryptols-own-properties-re-proved)), which
evaluates trait-free copies of these functions, proved equal to the
prelude's.

**How it is checked.** Verus proves the lemmas about the prelude (the
properties the spec layers use) along with the rest. The SPARK crate also
checks each generic against Cryptol's built-in through the FFI
(`spark/cryptol/SPARK/Prelude.cry`, 22 properties) and SAW proves each
instance its spec layers call; both are omitted here, because a Verus spec
function cannot be executed or compiled (the FFI check and SAW reach only
the executable code: [ffi.md](ffi.md), [saw.md](saw.md#the-spec-layer)).
The prelude is checked against Cryptol only through the executables that
are proved equal to the spec functions written in it.
