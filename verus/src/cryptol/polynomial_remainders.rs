//! Cryptol's remainder of polynomials over GF(2), `pmod : {u, v} (fin u,
//! fin v) => [u] -> [1 + v] -> [v]` (Cryptol.cry:1015, a primitive that
//! "performs modulus of polynomials over GF(2)"; docs/CryptolPrims.md,
//! "GF(2) polynomials"), as the SPARK prelude's `Polynomial_Remainders`
//! (spark/src/cryptol/foundation_spark-cryptol-polynomial_remainders.ads).
//! Words are polynomials by their bits, as in
//! [`polynomial_products`](super::polynomial_products).
//!
//! Stated as long division over the bits of the dividend, most significant
//! first: the remainder of the leading `n` bits is the remainder of the
//! leading `n - 1` bits times `x`, plus bit `n - 1`, reduced once by the
//! modulus. A partial remainder has degree below the modulus's, so after
//! the shift it has degree at most the modulus's, and one subtraction
//! (exclusive or) of the modulus, when its coefficient of `x ^^ (pdeg m)`
//! is set, brings it back below. [`top`]`(m)` is that leading term,
//! `x ^^ (pdeg m)`. Cryptol reports "division by 0" for a zero modulus, so
//! `m != 0` is a `recommends`.
//!
//! `{u, v}` are const generics, as in `polynomial_products`. Only `pmod`
//! takes `v`: the division steps do not depend on it.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_only)]
use super::Word;
#[cfg(verus_only)]
use super::words::bit_in;

verus! {

/// The leading term of a polynomial, `x ^^ (pdeg m)`: the largest power of
/// 2 not above `m` (0 for `m = 0`). On the polynomial's value, a `nat`,
/// where the SPARK prelude's `Top` is on its modular type: it is only
/// compared with, and the recursion then needs no lemma about `W` to end.
pub open spec fn top(m: nat) -> nat
    decreases m,
{
    if m <= 1 {
        m
    } else {
        2 * top(m / 2)
    }
}

/// One step of the long division: `t`, of degree at most `pdeg m`, less
/// `m` when its coefficient of `x ^^ (pdeg m)` is set.
pub open spec fn reduce<W: Word>(t: W, m: W) -> W {
    if W::to_nat(t) >= top(W::to_nat(m)) {
        W::xor(t, m)
    } else {
        t
    }
}

/// The remainder modulo `m` of the leading `n` bits of the `[u]` `x` (the
/// polynomial they make, read as an `n`-bit word). The SPARK prelude's
/// `2 * Remainders (...) + (if ... then 1 else 0)`, with the doubling
/// `W::add(r, r)` as in `products`.
pub open spec fn remainders<const u: u32, W: Word>(x: W, m: W, n: nat) -> W
    recommends
        n <= u,
    decreases n,
{
    if n == 0 {
        W::zero()
    } else {
        let r = remainders::<u, W>(x, m, (n - 1) as nat);
        reduce(W::add(W::add(r, r), if bit_in(u as nat, x, n - 1) { W::one() } else { W::zero() }), m)
    }
}

/// `` pmod`{u, v} x m ``: the remainder of `x` modulo `m` as polynomials
/// over GF(2), of degree below `m`'s.
pub open spec fn pmod<const u: u32, const v: u32, W: Word>(x: W, m: W) -> W
    recommends
        u < W::width(),
        1 + v < W::width(),
        W::to_nat(x) < pow2(u as nat),
        W::to_nat(m) < pow2((1 + v) as nat),
        W::to_nat(m) != 0,
{
    remainders::<u, W>(x, m, u as nat)
}

} // verus!
