//! Cryptol's quotient of polynomials over GF(2), `pdiv : {u, v} (fin u,
//! fin v) => [u] -> [v] -> [u]` (Cryptol.cry:1010, a primitive that
//! "performs division of polynomials over GF(2)"; docs/CryptolPrims.md,
//! "GF(2) polynomials"), as the SPARK prelude's `Polynomial_Quotients`
//! (spark/src/cryptol/foundation_spark-cryptol-polynomial_quotients.ads).
//! Words are polynomials by their bits, as in
//! [`polynomial_products`](super::polynomial_products).
//!
//! Stated as the long division of
//! [`polynomial_remainders`](super::polynomial_remainders): each step adds
//! one quotient bit, set when the step subtracts the divisor. Cryptol
//! reports "division by 0" for a zero divisor, so `y != 0` is a
//! `recommends`, and a `[0]` divisor can only be zero, so `v` is at least 1.
//! The SPARK prelude instantiates `Polynomial_Remainders` at `{u, v - 1}`
//! for the divisor, a `[v] = [1 + (v - 1)]`; here `remainders` does not
//! take `v`, so no `v - 1` is needed (a const generic cannot be computed).

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_only)]
use super::Word;
#[cfg(verus_only)]
use super::words::bit_in;
#[cfg(verus_only)]
use super::polynomial_remainders::{remainders, top};

verus! {

/// The quotient by `y` of the leading `n` bits of the `[u]` `x`: one bit
/// per step of [`remainders`], set when that step subtracts `y`.
pub open spec fn quotients<const u: u32, W: Word>(x: W, y: W, n: nat) -> W
    recommends
        n <= u,
    decreases n,
{
    if n == 0 {
        W::zero()
    } else {
        let q = quotients::<u, W>(x, y, (n - 1) as nat);
        let r = remainders::<u, W>(x, y, (n - 1) as nat);
        let t = W::add(W::add(r, r), if bit_in(u as nat, x, n - 1) { W::one() } else { W::zero() });
        W::add(W::add(q, q), if W::to_nat(t) >= top(W::to_nat(y)) { W::one() } else { W::zero() })
    }
}

/// `` pdiv`{u, v} x y ``: the quotient of `x` by `y` as polynomials over
/// GF(2). The widths are those the SPARK prelude requires of its
/// `Polynomial_Remainders` instance at `{u, v - 1}`.
pub open spec fn pdiv<const u: u32, const v: u32, W: Word>(x: W, y: W) -> W
    recommends
        1 <= v,
        u < W::width(),
        v < W::width(),
        W::to_nat(x) < pow2(u as nat),
        W::to_nat(y) < pow2(v as nat),
        W::to_nat(y) != 0,
{
    quotients::<u, W>(x, y, u as nat)
}

} // verus!
