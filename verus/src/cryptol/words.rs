//! Cryptol's `@` and `head` on a word `[w]` (Cryptol.cry:900, a primitive;
//! :796, bit order; :855, head's body), as the SPARK prelude's `Words`
//! (spark/src/cryptol/foundation_spark-cryptol-words.ads).

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use super::Word;

verus! {

/// `x @ j` on a word `[width]` held in `W`: bit `j`, counting from the most
/// significant, so bit `j` has weight `2 ^^ (width - 1 - j)`. Stated, as in
/// the SPARK prelude, by shifting that bit to the bottom and masking it.
///
/// The word may be narrower than `W` (AES holds the `[15]` product of
/// `pmult` in a `u16`); its value is then below `2 ^^ width`, and the bits
/// of `W` above `width` are not Cryptol's. The SPARK prelude's `Words`
/// takes the width as a generic formal `Width`; here it is an argument,
/// because the polynomial modules call it at widths such as `1 + v`, which
/// a const generic cannot be computed as.
pub open spec fn bit_in<W: Word>(width: nat, x: W, j: int) -> bool
    recommends
        width <= W::width(),
        0 <= j < width,
{
    W::and(W::shr(x, (width - 1 - j) as nat), W::one()) == W::one()
}

/// `x @ j` on a word `[w]` that fills `W`: [`bit_in`] at `W`'s width.
pub open spec fn bit<W: Word>(x: W, j: int) -> bool
    recommends
        0 <= j < W::width(),
{
    bit_in(W::width(), x, j)
}

/// `head x` on a word: its most significant bit, `x @ 0`.
pub open spec fn head<W: Word>(x: W) -> bool
    recommends
        W::width() > 0,
{
    bit(x, 0)
}

} // verus!
