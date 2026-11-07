//! Cryptol's product of polynomials over GF(2), `pmult : {u, v} (fin u,
//! fin v) => [1 + u] -> [1 + v] -> [1 + u + v]` (Cryptol.cry:1005, a
//! primitive that "performs multiplication of polynomials over GF(2)";
//! docs/CryptolPrims.md, "GF(2) polynomials"), as the SPARK prelude's
//! `Polynomial_Products`
//! (spark/src/cryptol/foundation_spark-cryptol-polynomial_products.ads).
//!
//! A word is a polynomial by its bits: the bit of weight `2 ^^ i` is the
//! coefficient of `x ^^ i`, as Cryptol's polynomial literals are (RefMan
//! BasicSyntax.rst:352, `<| x^^4 + x^^3 + x |>` is `0b11010`). Addition of
//! polynomials over GF(2) is exclusive or, and multiplication by `x` is a
//! doubling, so the product is the long multiplication by `y`'s bits, most
//! significant first: [`products`]`(x, y, n)` is `x` times the leading `n`
//! bits of `y`, and the next bit doubles it (one more power of `x`) and
//! adds `x` if the bit is set.
//!
//! Cryptol's type parameters `{u, v}` are const generics, as in
//! `sha2::notation`. The words are held in one [`Word`] type `W`, wide
//! enough for the product; the SPARK prelude rejects a narrower one when it
//! is instantiated, and here that is a `recommends`.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_only)]
use super::Word;
#[cfg(verus_only)]
use super::words::bit_in;

verus! {

/// `x` times the leading `n` bits of the `[1 + v]` `y` (the polynomial they
/// make, read as an `n`-bit word), by long multiplication, most
/// significant bit first. The doubling is `W::add(p, p)`, as the SPARK
/// prelude's `2 * Products (...)` and `join_split::value`'s doubling are.
pub open spec fn products<const v: u32, W: Word>(x: W, y: W, n: nat) -> W
    recommends
        n <= 1 + v,
    decreases n,
{
    if n == 0 {
        W::zero()
    } else {
        let p = products::<v, W>(x, y, (n - 1) as nat);
        W::xor(W::add(p, p), if bit_in((1 + v) as nat, y, n - 1) { x } else { W::zero() })
    }
}

/// `` pmult`{u, v} x y ``: the product of `x` and `y` as polynomials over
/// GF(2), of degree at most `u + v`.
pub open spec fn pmult<const u: u32, const v: u32, W: Word>(x: W, y: W) -> W
    recommends
        1 + u + v < W::width(),
        W::to_nat(x) < pow2((1 + u) as nat),
        W::to_nat(y) < pow2((1 + v) as nat),
{
    products::<v, W>(x, y, (1 + v) as nat)
}

} // verus!
