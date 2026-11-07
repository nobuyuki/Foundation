//! The Secure Hash Algorithm 2 (SHA-2) [FIPS-PUB-180-4 Sections 6.2 and
//! 6.4], mirroring the parameterized module algorithms/SHA2/Main.cry.
//!
//! Its `parameter` block (Main.cry:11) is the trait [`Parameters`], in the
//! same order, and its declarations are spec functions generic over an
//! implementation of it, `P`. [`super::sha256`] implements it as SHA256.cry
//! instantiates the Cryptol. (The SPARK crate's counterpart is the generic
//! package `Main`, its formals the parameters.)
//!
//! This module holds the compression function `step` (Main.cry:67) and its
//! local definitions, and `hash` (Main.cry:55) over bit sequences with its
//! local types `k` and `N` as functions of the message length. It also holds
//! Preprocessing.cry's `pad` and `parse`, at the `{m, w}` that `hash`
//! applies them at, as the SPARK crate does: in the Cryptol they are
//! polymorphic in `w`, and here `w`, and the word type `parse` produces,
//! are `P`'s.
//!
//! Cryptol's `[8][w]` (a hash value), `[16][w]` (a block) and `[N][16][w]`
//! are `Seq<P::Word>` and `Seq<Seq<P::Word>>`; their lengths, which a Verus
//! `Seq` type does not carry, are those the functions build, and those
//! callers pass. Bit sequences `[l]` are `Seq<bool>`, bit 0 first, as
//! Cryptol's `@` counts.

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::cryptol::Word;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_only)]
use crate::cryptol::{bit_sequences, enumeration_folds, folds, join_split, numeric, words};
#[cfg(verus_only)]
use super::functions::{Ch, Maj};

verus! {

/// Main.cry's `parameter` block (Main.cry:11-43).
pub trait Parameters {
    /// A word, Cryptol's `[w]`. The SPARK crate's formal `type Word is mod <>`.
    type Word: Word;

    /// Number of bits in a message digest, Cryptol's `type d` (Main.cry:16).
    spec fn d() -> nat;

    /// Number of bits in a word, Cryptol's `type w` (Main.cry:22,
    /// [FIPS-PUB-180-4 Section 2.2.1]).
    spec fn w() -> nat;

    /// Number of elements of `K` (and `W`), Cryptol's `type Klen`
    /// (Main.cry:30, [FIPS-PUB-180-4 Sections 4.2.2 and 4.2.3]).
    spec fn Klen() -> nat;

    /// SHA-2 constants, Cryptol's `K : [Klen][w]` (Main.cry:34).
    spec fn K() -> Seq<Self::Word>;

    /// Initial hash value, Cryptol's `H0 : [8][w]` (Main.cry:37,
    /// [FIPS-PUB-180-4 Section 5.3]).
    spec fn H0() -> Seq<Self::Word>;

    /// Cryptol's `SIGMA_0 : [w] -> [w]` (Main.cry:40, [FIPS-PUB-180-4 Section 4.1]).
    spec fn SIGMA_0(x: Self::Word) -> Self::Word;

    /// Cryptol's `SIGMA_1 : [w] -> [w]` (Main.cry:41).
    spec fn SIGMA_1(x: Self::Word) -> Self::Word;

    /// Cryptol's `sigma_0 : [w] -> [w]` (Main.cry:42).
    spec fn sigma_0(x: Self::Word) -> Self::Word;

    /// Cryptol's `sigma_1 : [w] -> [w]` (Main.cry:43).
    spec fn sigma_1(x: Self::Word) -> Self::Word;

    /// The parameter block's type constraints, `fin d, d > 0` and
    /// `fin w, w > 0, 8 * w >= d` (Main.cry:17, :23), with what Cryptol's
    /// types carry and a `Seq` does not: `Word` is `[w]`, `K` is
    /// `[Klen][w]` and `H0` is `[8][w]`. Each implementation proves them.
    /// (The SPARK crate checks them with `pragma Compile_Time_Error` and
    /// `pragma Assert` at the instance.)
    proof fn type_constraints()
        ensures
            Self::d() > 0,
            Self::w() > 0,
            8 * Self::w() >= Self::d(),
            Self::Word::width() == Self::w(),
            Self::K().len() == Self::Klen(),
            Self::H0().len() == 8,
    ;
}

/// The message schedule, `step`'s local `W : [Klen][w]` (Main.cry:70,
/// Step 1 of [FIPS-PUB-180-4 Sections 6.2.2 and 6.4.2]):
/// `W@t = if t <= 15 then M @ t else sigma_1 (W@(t-2)) + W@(t-7) +
/// sigma_0 (W@(t-15)) + W@(t-16)`. The Cryptol sequence is defined by
/// recursion on its own elements; here it is a recursive function of the
/// index `t`, and of the block `M` that the Cryptol closes over.
pub open spec fn W<P: Parameters>(M: Seq<P::Word>, t: int) -> P::Word
    recommends
        0 <= t < P::Klen(),
    decreases t,
{
    if t <= 15 {
        M[t]
    } else {
        P::Word::add(
            P::Word::add(
                P::Word::add(P::sigma_1(W::<P>(M, t - 2)), W::<P>(M, t - 7)),
                P::sigma_0(W::<P>(M, t - 15)),
            ),
            W::<P>(M, t - 16),
        )
    }
}

/// `step3`'s local `T1 = h + SIGMA_1 e + Ch (e, f, g) + K@t + W@t`
/// (Main.cry:87, Step 3 of [FIPS-PUB-180-4 Sections 6.2.2 and 6.4.2]),
/// where `[a, b, c, d, e, f, g, h]` is `vars`: `h` is `vars[7]`, and
/// `e, f, g` are `vars[4], vars[5], vars[6]`. The block `M` is `W`'s.
pub open spec fn T1<P: Parameters>(M: Seq<P::Word>, vars: Seq<P::Word>, t: int) -> P::Word
    recommends
        0 <= t < P::Klen(),
{
    P::Word::add(
        P::Word::add(
            P::Word::add(
                P::Word::add(vars[7], P::SIGMA_1(vars[4])),
                Ch(vars[4], vars[5], vars[6]),
            ),
            P::K()[t],
        ),
        W::<P>(M, t),
    )
}

/// `step3`'s local `T2 = SIGMA_0 a + Maj (a, b, c)` (Main.cry:88), where
/// `a, b, c` are `vars[0], vars[1], vars[2]`.
pub open spec fn T2<P: Parameters>(vars: Seq<P::Word>) -> P::Word {
    P::Word::add(P::SIGMA_0(vars[0]), Maj(vars[0], vars[1], vars[2]))
}

/// One round of the compression, `step`'s local `step3` (Main.cry:75, Step
/// 3 of [FIPS-PUB-180-4 Sections 6.2.2 and 6.4.2]):
/// `step3 [a, b, c, d, e, f, g, h] t = [T1 + T2, a, b, c, d + T1, e, f, g]`.
/// The Cryptol names the working variables by a pattern; here they are
/// `vars[0]` to `vars[7]`. The block `M`, which the Cryptol closes over
/// through `W`, is an explicit parameter.
pub open spec fn step3<P: Parameters>(M: Seq<P::Word>, vars: Seq<P::Word>, t: int) -> Seq<P::Word>
    recommends
        0 <= t < P::Klen(),
{
    seq![
        P::Word::add(T1::<P>(M, vars, t), T2::<P>(vars)),
        vars[0],
        vars[1],
        vars[2],
        P::Word::add(vars[3], T1::<P>(M, vars, t)),
        vars[4],
        vars[5],
        vars[6],
    ]
}

/// `foldl step3 H [0 ..< n]`, the left fold of `step3` over the first `n`
/// rounds; at `n = Klen` it is `step`'s `H'` (Main.cry:74, Steps 2 and 3 of
/// [FIPS-PUB-180-4 Sections 6.2.2 and 6.4.2]). The function folded is
/// `step3` closed over the block, as in the Cryptol. `n` is a parameter,
/// not always `Klen`, so that the implementation's loop invariant can name
/// the fold after `t` rounds.
pub open spec fn foldl_step3<P: Parameters>(M: Seq<P::Word>, H: Seq<P::Word>, n: int) -> Seq<P::Word>
    recommends
        0 <= n <= P::Klen(),
{
    enumeration_folds::foldl(|vars: Seq<P::Word>, t: int| step3::<P>(M, vars, t), H, 0, n)
}

/// Cryptol's `+` on `[8][w]`, as `step` uses it: element-wise, each word
/// modulo `2 ^^ w`.
pub open spec fn add<W: Word>(left: Seq<W>, right: Seq<W>) -> Seq<W> {
    Seq::new(left.len(), |i: int| W::add(left[i], right[i]))
}

/// The compression function, Cryptol's `step H M = H + H'` (Main.cry:67,
/// Step 4 of [FIPS-PUB-180-4 Sections 6.2.2 and 6.4.2]), where
/// `H' = foldl step3 H [0 ..< Klen]`.
pub open spec fn step<P: Parameters>(H: Seq<P::Word>, M: Seq<P::Word>) -> Seq<P::Word> {
    add(H, foldl_step3::<P>(M, H, P::Klen() as int))
}

/// The number of bits in a message block, Cryptol's `type m = w * 16`
/// (Main.cry:48, [FIPS-PUB-180-4 Section 2.2.1]).
pub open spec fn m<P: Parameters>() -> nat {
    P::w() * 16
}

/// The bound on message lengths: `hash` admits `l` with `width l <= 2 * w`
/// (Main.cry:55), that is `l < 2 ^^ (2 * w)`. (The SPARK crate bounds it
/// further by its index type, at `2 ** 64`, the same at `w = 32`.)
pub open spec fn max_length<P: Parameters>() -> nat {
    pow2(2 * P::w())
}

/// The number of zero bits in the padding, `hash`'s local
/// `type k = (l + 1 + 2 * w) %^ m` (Main.cry:58, [FIPS-PUB-180-4 Section
/// 5.1.1]), as a function of the message length `l`.
pub open spec fn k<P: Parameters>(l: nat) -> nat {
    numeric::ceil_mod(l + 1 + 2 * P::w(), m::<P>())
}

/// The number of blocks in the padded message, `hash`'s local
/// `type N = (l + 1 + 2 * w) /^ m` (Main.cry:59, [FIPS-PUB-180-4 Section
/// 5.2.1]), as a function of the message length `l`.
pub open spec fn N<P: Parameters>(l: nat) -> nat {
    numeric::ceil_div(l + 1 + 2 * P::w(), m::<P>())
}

/// The padding, Cryptol's ``pad`{m, w, l, k}`` as `hash` applies it
/// (Preprocessing.cry:14, [FIPS-PUB-180-4 Section 5.1]):
/// ``pad M = M # 0b1 # zero # (`l : [2 * w])``, with `l` the length of
/// `M` and `k` as above. The result has `l + 1 + k + 2 * w` bits, that is
/// `N (l)` blocks.
pub open spec fn pad<P: Parameters>(M: Seq<bool>) -> Seq<bool>
    recommends
        M.len() < max_length::<P>(),
{
    M + seq![true] + bit_sequences::zero(k::<P>(M.len())) + bit_sequences::literal(
        M.len(),
        2 * P::w(),
    )
}

/// Block `i` of ``parse`{w, N} p`` (Preprocessing.cry:51): the 16 words of
/// ``split`{N * 16, w} p`` from word `16 * i`, which the outer
/// ``split`{N, 16}`` groups as block `i`.
pub open spec fn parse_block<P: Parameters>(p: Seq<bool>, i: int) -> Seq<P::Word>
    recommends
        0 <= i,
        (i + 1) * m::<P>() <= p.len(),
{
    Seq::new(16, |j: int| join_split::split_at::<P::Word>(p, 16 * i + j))
}

/// The parsing of a padded message into blocks, Cryptol's ``parse`{w, N}``
/// (Preprocessing.cry:47, [FIPS-PUB-180-4 Section 5.2]):
/// ``parse M = split`{N, 16} (split`{N * 16, w} M)``. The inner split cuts
/// `p` into `N * 16` words of `w` bits and the outer groups them 16 to a
/// block, so block `i` is `parse_block(p, i)`.
pub open spec fn parse<P: Parameters>(p: Seq<bool>, N: nat) -> Seq<Seq<P::Word>>
    recommends
        p.len() == N * m::<P>(),
{
    Seq::new(N, |i: int| parse_block::<P>(p, i))
}

/// ``foldl step H (take`{n} Ms)``, the left fold of `step` over the first
/// `n` blocks. At `n = Ms.len()` it is `hash`'s `H = foldl step H0 M'`
/// (Main.cry:61, [FIPS-PUB-180-4 Sections 6.2 and 6.4]).
pub open spec fn foldl_step<P: Parameters>(H: Seq<P::Word>, Ms: Seq<Seq<P::Word>>, n: int) -> Seq<P::Word>
    recommends
        0 <= n <= Ms.len(),
{
    folds::foldl_take(|h: Seq<P::Word>, b: Seq<P::Word>| step::<P>(h, b), H, Ms, n)
}

/// Bit `j` of a word, Cryptol's `x @ j` on `[w]`, as the prelude states
/// it: most significant bit first.
pub open spec fn bit<P: Parameters>(x: P::Word, j: int) -> bool
    recommends
        0 <= j < P::w(),
{
    words::bit(x, j)
}

/// Cryptol's `join` on `[8][w]`, as `hash` applies it (Main.cry:56): the 8
/// words' bits in order.
pub open spec fn join<P: Parameters>(H: Seq<P::Word>) -> Seq<bool> {
    join_split::join(H)
}

/// SHA-2, Cryptol's `hash M = take (join H)` (Main.cry:55,
/// [FIPS-PUB-180-4 Sections 6.2 and 6.4]), where
/// ``M' = parse`{w, N} (pad`{m, w, l, k} M)`` and `H = foldl step H0 M'`:
/// the message is padded, parsed into `N (l)` blocks, and folded through
/// `step` from `H0`, and the digest is the first `d` bits of the result.
/// The `where` locals are inlined.
pub open spec fn hash<P: Parameters>(M: Seq<bool>) -> Seq<bool>
    recommends
        M.len() < max_length::<P>(),
{
    join::<P>(
        foldl_step::<P>(P::H0(), parse::<P>(pad::<P>(M), N::<P>(M.len())), N::<P>(M.len()) as int),
    ).take(P::d() as int)
}

} // verus!
