//! Multiplication in GF(2^8), mirroring algorithms/AES/GF28.cry
//! [FIPS-PUB-197 Section 4.2], as the SPARK crate's `AES.Spec.GF28`
//! (spark/src/aes/foundation_spark-aes-spec-gf28.ads).
//!
//! GF28.cry defines `(•)` as `pmod (pmult b c) m`, with Cryptol's
//! primitive polynomial product and remainder over GF(2). They are the
//! prelude's [`pmult`](polynomial_products::pmult) at `[8] -> [8] -> [15]`
//! and [`pmod`](polynomial_remainders::pmod) at `[15] -> [9] -> [8]`, with
//! the polynomials in a `u16`. Rust has no operator `•`, so `(•)` is
//! [`dot`], as the SPARK crate's `Dot`.
//!
//! The SPARK crate keeps `pmod` inline, because its prelude's `Pmod`
//! returns a polynomial whose bound below `2 ** 8` no expression function
//! can call the proof of. Here the prelude's is used: `dot` casts its
//! `[8]` result from the `u16` to a `u8`, and [`lemma_dot`] proves that
//! the cast drops no coefficient.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::{polynomial_products, polynomial_remainders};
#[cfg(verus_only)]
use crate::cryptol::polynomial_remainders::{reduce, remainders, top};
#[cfg(verus_only)]
use crate::cryptol::words::head;
#[cfg(verus_only)]
use super::gf2::lemma_top;

verus! {

/// GF28.cry, in `(•)`: `m = <| x^^8 + x^^4 + x^^3 + x + 1 |>`, the AES
/// polynomial [FIPS-PUB-197 Section 4.2], a `[9]`.
pub open spec fn m() -> u16 {
    0x11b
}

/// GF28.cry: `(•) b c = pmod (pmult b c) m` (GF28.cry:12). Multiplication
/// in GF(2^8) [FIPS-PUB-197 Section 4.2].
pub open spec fn dot(b: u8, c: u8) -> u8 {
    polynomial_remainders::pmod::<15, 8, u16>(
        polynomial_products::pmult::<7, 7, u16>(b as u16, c as u16),
        m(),
    ) as u8
}

/// GF28.cry: `xTimes b = b << 1 ^ (if head b then 0x1b else 0x00)`
/// (GF28.cry:21). The product `b • 0x02` [FIPS-PUB-197 Section 4.2].
pub open spec fn xTimes(b: u8) -> u8 {
    (b << 1u8) ^ (if head::<u8>(b) { 0x1bu8 } else { 0x00u8 })
}

/// Each step of the prelude's long division by `m` leaves a remainder
/// below `top m = x ^^ 8`.
pub proof fn lemma_remainders_byte(x: u16, n: nat)
    ensures
        remainders::<15, u16>(x, m(), n) < 0x100,
    decreases n,
{
    lemma_top(0x11b);
    assert(top(0x11b) == 0x100) by {
        reveal_with_fuel(top, 10);
    }
    if n > 0 {
        lemma_remainders_byte(x, (n - 1) as nat);
        let r = remainders::<15, u16>(x, m(), (n - 1) as nat);
        let b: u16 = if crate::cryptol::words::bit_in(15, x, n - 1) { 1 } else { 0 };
        let t = vstd::wrapping::u16_specs::wrapping_add(
            vstd::wrapping::u16_specs::wrapping_add(r, r), b);
        assert(t < 0x200);
        assert(remainders::<15, u16>(x, m(), n) == reduce(t, m()));
        assert(t >= 0x100 && t < 0x200 ==> (t ^ 0x11bu16) < 0x100) by (bit_vector);
    }
}

/// `pmod`'s `[8]` result fits a `u8`, so `dot`'s cast keeps all of it:
/// `dot b c` is the remainder itself.
pub proof fn lemma_dot(b: u8, c: u8)
    ensures
        dot(b, c) as u16 == polynomial_remainders::pmod::<15, 8, u16>(
            polynomial_products::pmult::<7, 7, u16>(b as u16, c as u16),
            m(),
        ),
{
    lemma_remainders_byte(polynomial_products::pmult::<7, 7, u16>(b as u16, c as u16), 15);
}

} // verus!
