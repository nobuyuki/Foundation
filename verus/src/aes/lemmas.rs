//! Lemmas about the AES spec layer, as the SPARK crate's `AES.Lemmas`
//! (spark/src/aes/foundation_spark-aes-lemmas.ads). They are not in the
//! Cryptol: each states a property of a spec-layer function that the
//! Cryptol evaluates and Verus has to prove.
//!
//! GF(2^8). The spec's `dot` is GF28.cry's `pmod (pmult b c) m`, two
//! recursive folds over bits. The implementation multiplies by the
//! constants of `MixColumns` and `InvMixColumns` with `xTimes` alone.
//! [`lemma_dot`] connects the two for any constant below 16: [`Pm`] gives
//! `pmult`'s closed form ([`lemma_pmult_fold`]), the remainder is the
//! dividend itself while the dividend has degree below 8
//! ([`lemma_pmod_small`]), and the last three reduction steps are left to
//! `bit_vector` ([`lemma_remainders_step`] states one step in its terms).
//!
//! Bytes and bits. Cryptol's `split` and `join` between `[8]` and its
//! bits are inverses: [`lemma_value_byte`] and [`lemma_value_bits`], at
//! the prelude's `value` and `bit`.
//!
//! [`lemma_dot_column`] and [`lemma_dot_inverse_column`] state `lemma_dot`
//! at the constants of `MixColumns` and `InvMixColumns`, for
//! [`super::properties`] and [`super::aes_impl`].
//!
//! Lemmas of the SPARK crate's `AES.Lemmas` without a counterpart: the
//! `*_Eq` lemmas (a function maps equal arrays to equal results) and
//! `Lemma_Foldl_*_Take_Eq`, because Verus's `==` on sequences is
//! equality, and `Lemma_Foldl_*_Snoc`, because the implementation's loops
//! keep the prelude's `foldl_take` over the spec's own sequence as their
//! invariant, which is one round longer per step by definition. The
//! byte-and-bit lemmas are ones the SPARK crate states in place.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::join_split;
#[cfg(verus_only)]
use crate::cryptol::words::bit;
#[cfg(verus_only)]
use crate::cryptol::polynomial_products::{pmult, products};
#[cfg(verus_only)]
use crate::cryptol::polynomial_remainders::{remainders, top};
#[cfg(verus_only)]
use super::gf28::{dot, lemma_dot as lemma_dot_cast, lemma_remainders_byte, m, xTimes};

verus! {

/// The carry-less product of `b` and `d`, two `[8]`s in `u16`s, as
/// polynomials over GF(2), in closed form: the exclusive-or of `d * x ^^ i`
/// over the bits `i` set in `b` (of weight `2 ^^ i`). The SPARK crate's
/// `Pm`, with its `Term`s written out.
pub open spec fn Pm(b: u16, d: u16) -> u16 {
    (if b & 1u16 != 0u16 { d << 0u16 } else { 0u16 })
    ^ (if b & 2u16 != 0u16 { d << 1u16 } else { 0u16 })
    ^ (if b & 4u16 != 0u16 { d << 2u16 } else { 0u16 })
    ^ (if b & 8u16 != 0u16 { d << 3u16 } else { 0u16 })
    ^ (if b & 16u16 != 0u16 { d << 4u16 } else { 0u16 })
    ^ (if b & 32u16 != 0u16 { d << 5u16 } else { 0u16 })
    ^ (if b & 64u16 != 0u16 { d << 6u16 } else { 0u16 })
    ^ (if b & 128u16 != 0u16 { d << 7u16 } else { 0u16 })
}

/// The product `b • c` for a `b` below 16, with `xTimes` alone: the
/// exclusive-or of `c • x ^^ i` over the bits `i` set in `b`. The SPARK
/// crate's `By_xTimes`.
pub open spec fn By_xTimes(b: u8, c: u8) -> u8
    recommends
        b < 16,
{
    (if b & 1u8 != 0u8 { c } else { 0u8 })
    ^ (if b & 2u8 != 0u8 { xTimes(c) } else { 0u8 })
    ^ (if b & 4u8 != 0u8 { xTimes(xTimes(c)) } else { 0u8 })
    ^ (if b & 8u8 != 0u8 { xTimes(xTimes(xTimes(c))) } else { 0u8 })
}

/// `xTimes` in the terms of `bit_vector`: `head b` is the top bit.
pub proof fn lemma_xtimes(b: u8)
    ensures
        xTimes(b) == (b << 1u8) ^ (if (b >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }),
{
}

/// `Word::add(p, p)` at `u16` is a shift by one, below `2 ^^ 15`.
pub proof fn lemma_double_16(p: u16)
    requires
        p < 0x8000,
    ensures
        vstd::wrapping::u16_specs::wrapping_add(p, p) == p << 1u16,
{
    assert(p < 0x8000 ==> p << 1u16 == p + p) by (bit_vector);
}

/// The leading term of `m` is `x ^^ 8`.
pub proof fn lemma_top_m()
    ensures
        top(m() as nat) == 0x100,
{
    reveal_with_fuel(top, 10);
}

/// Step `n` of `pmod x m`'s long division, in the terms of `bit_vector`:
/// the remainder so far, shifted up by one, with bit `n - 1` of the `[15]`
/// `x` brought down, less `m` if it reaches `x ^^ 8`.
pub proof fn lemma_remainders_step(x: u16, n: nat)
    requires
        1 <= n <= 15,
    ensures
        ({
            let r = remainders::<15, u16>(x, m(), (n - 1) as nat);
            let t = (r << 1u16) | ((x >> ((15 - n) as u16)) & 1u16);
            remainders::<15, u16>(x, m(), n) == if t >= 0x100u16 { t ^ 0x11bu16 } else { t }
        }),
        remainders::<15, u16>(x, m(), (n - 1) as nat) < 0x100,
{
    lemma_remainders_byte(x, (n - 1) as nat);
    lemma_top_m();
    let r = remainders::<15, u16>(x, m(), (n - 1) as nat);
    lemma_double_16(r);
    let k = (15 - n) as u16;
    assert((15 - 1 - (n - 1)) as nat as u16 == k);
    let b: u16 = if (x >> k) & 1u16 == 1u16 { 1 } else { 0 };
    assert(r < 0x100 && k < 15 && b == (if (x >> k) & 1u16 == 1u16 { 1u16 } else { 0u16 })
        ==> (r << 1u16) + b == (r << 1u16) | ((x >> k) & 1u16) && (r << 1u16) + b < 0x200) by (bit_vector);
}

/// The closed form of a step of `Pm`: `Pm b (c >> k)` is `Pm b (c >> (k +
/// 1))`, one place up, plus `b` if bit `k` of `c` (of weight `2 ^^ k`) is
/// set; and `Pm b (c >> (k + 1))` is below `2 ^^ 14`.
pub proof fn lemma_pm_step(b: u16, c: u16, k: u16)
    requires
        b < 0x100,
        c < 0x100,
        k < 8,
    ensures
        Pm(b, c >> k) == (Pm(b, c >> (k + 1) as u16) << 1u16) ^ (if (c >> k) & 1u16 == 1u16 { b } else { 0u16 }),
        Pm(b, c >> (k + 1) as u16) < 0x4000,
{
    let d = c >> k;
    let e = c >> (k + 1) as u16;
    assert(k < 8 && c < 0x100 && d == c >> k && e == c >> (k + 1u16) ==> e == d >> 1u16 && d < 0x100) by (bit_vector);
    let p = Pm(b, d);
    let q = Pm(b, e);
    assert(b < 0x100 && d < 0x100 && e == d >> 1u16 && p == ((if b & 1u16 != 0u16 { d << 0u16 } else { 0u16 })
        ^ (if b & 2u16 != 0u16 { d << 1u16 } else { 0u16 })
        ^ (if b & 4u16 != 0u16 { d << 2u16 } else { 0u16 })
        ^ (if b & 8u16 != 0u16 { d << 3u16 } else { 0u16 })
        ^ (if b & 16u16 != 0u16 { d << 4u16 } else { 0u16 })
        ^ (if b & 32u16 != 0u16 { d << 5u16 } else { 0u16 })
        ^ (if b & 64u16 != 0u16 { d << 6u16 } else { 0u16 })
        ^ (if b & 128u16 != 0u16 { d << 7u16 } else { 0u16 }))
        && q == ((if b & 1u16 != 0u16 { e << 0u16 } else { 0u16 })
        ^ (if b & 2u16 != 0u16 { e << 1u16 } else { 0u16 })
        ^ (if b & 4u16 != 0u16 { e << 2u16 } else { 0u16 })
        ^ (if b & 8u16 != 0u16 { e << 3u16 } else { 0u16 })
        ^ (if b & 16u16 != 0u16 { e << 4u16 } else { 0u16 })
        ^ (if b & 32u16 != 0u16 { e << 5u16 } else { 0u16 })
        ^ (if b & 64u16 != 0u16 { e << 6u16 } else { 0u16 })
        ^ (if b & 128u16 != 0u16 { e << 7u16 } else { 0u16 })) ==> p == (q << 1u16) ^ (if d & 1u16 == 1u16 { b } else { 0u16 }) && q < 0x4000)
        by (bit_vector);
}

/// `Pm` of a zero multiplier is zero.
pub proof fn lemma_pm_zero(b: u16)
    ensures
        Pm(b, 0) == 0,
{
    let p = Pm(b, 0);
    assert(p == ((if b & 1u16 != 0u16 { 0u16 << 0u16 } else { 0u16 })
        ^ (if b & 2u16 != 0u16 { 0u16 << 1u16 } else { 0u16 })
        ^ (if b & 4u16 != 0u16 { 0u16 << 2u16 } else { 0u16 })
        ^ (if b & 8u16 != 0u16 { 0u16 << 3u16 } else { 0u16 })
        ^ (if b & 16u16 != 0u16 { 0u16 << 4u16 } else { 0u16 })
        ^ (if b & 32u16 != 0u16 { 0u16 << 5u16 } else { 0u16 })
        ^ (if b & 64u16 != 0u16 { 0u16 << 6u16 } else { 0u16 })
        ^ (if b & 128u16 != 0u16 { 0u16 << 7u16 } else { 0u16 })) ==> p == 0) by (bit_vector);
}

/// `pmult`'s fold after `n` steps is the closed-form product of `b` with
/// the leading `n` bits of `c`. The SPARK crate's `Lemma_Pmult_Fold`.
pub proof fn lemma_pmult_fold(b: u16, c: u16, n: nat)
    requires
        b < 0x100,
        c < 0x100,
        n <= 8,
    ensures
        products::<7, u16>(b, c, n) == Pm(b, c >> ((8 - n) as u16)),
    decreases n,
{
    if n == 0 {
        assert(c < 0x100 ==> c >> 8u16 == 0) by (bit_vector);
        lemma_pm_zero(b);
    } else {
        lemma_pmult_fold(b, c, (n - 1) as nat);
        let k = (8 - n) as u16;
        lemma_pm_step(b, c, k);
        assert((8 - (n - 1)) as nat as u16 == (k + 1) as u16);
        let p = products::<7, u16>(b, c, (n - 1) as nat);
        lemma_double_16(p);
        assert((1 + 7 - 1 - (n - 1)) as nat as u16 == k);
    }
}

/// `Pm` is commutative: so is `pmult`.
pub proof fn lemma_pm_commutes(b: u16, c: u16)
    requires
        b < 0x100,
        c < 0x100,
    ensures
        Pm(b, c) == Pm(c, b),
{
    let p = Pm(b, c);
    let q = Pm(c, b);
    assert(b < 0x100 && c < 0x100 && p == ((if b & 1u16 != 0u16 { c << 0u16 } else { 0u16 })
        ^ (if b & 2u16 != 0u16 { c << 1u16 } else { 0u16 })
        ^ (if b & 4u16 != 0u16 { c << 2u16 } else { 0u16 })
        ^ (if b & 8u16 != 0u16 { c << 3u16 } else { 0u16 })
        ^ (if b & 16u16 != 0u16 { c << 4u16 } else { 0u16 })
        ^ (if b & 32u16 != 0u16 { c << 5u16 } else { 0u16 })
        ^ (if b & 64u16 != 0u16 { c << 6u16 } else { 0u16 })
        ^ (if b & 128u16 != 0u16 { c << 7u16 } else { 0u16 }))
        && q == ((if c & 1u16 != 0u16 { b << 0u16 } else { 0u16 })
        ^ (if c & 2u16 != 0u16 { b << 1u16 } else { 0u16 })
        ^ (if c & 4u16 != 0u16 { b << 2u16 } else { 0u16 })
        ^ (if c & 8u16 != 0u16 { b << 3u16 } else { 0u16 })
        ^ (if c & 16u16 != 0u16 { b << 4u16 } else { 0u16 })
        ^ (if c & 32u16 != 0u16 { b << 5u16 } else { 0u16 })
        ^ (if c & 64u16 != 0u16 { b << 6u16 } else { 0u16 })
        ^ (if c & 128u16 != 0u16 { b << 7u16 } else { 0u16 })) ==> p == q) by (bit_vector);
}

/// `pmod`'s long division leaves the leading `n` bits of the `[15]` `x`
/// unreduced while they have degree below 8. The SPARK crate's
/// `Lemma_Pmod_Small`, at GF28.cry's `m`.
pub proof fn lemma_pmod_small(x: u16, n: nat)
    requires
        n <= 15,
        x < 0x8000,
        x >> ((15 - n) as u16) < 0x100,
    ensures
        remainders::<15, u16>(x, m(), n) == x >> ((15 - n) as u16),
    decreases n,
{
    if n == 0 {
        assert(x < 0x8000 ==> x >> 15u16 == 0) by (bit_vector);
    } else {
        let k = (15 - n) as u16;
        assert((15 - (n - 1)) as u16 == k + 1u16);
        assert(k < 15 && (x >> k) < 0x100 ==> (x >> (k + 1u16)) < 0x100) by (bit_vector);
        lemma_pmod_small(x, (n - 1) as nat);
        lemma_remainders_step(x, n);
        let r = x >> (k + 1u16);
        assert(k < 15 && (x >> k) < 0x100 && r == x >> (k + 1u16) ==> ((r << 1u16) | ((x >> k) & 1u16))
            == x >> k) by (bit_vector);
    }
}

/// GF28.cry's `(•)` by a constant below 16 is the exclusive-or of `xTimes`
/// powers that [`By_xTimes`] computes. The SPARK crate's `Lemma_Dot`.
/// (`gf28::lemma_dot` is another: that `dot`'s cast to `u8` keeps all of
/// the remainder.)
pub proof fn lemma_dot(b: u8, c: u8)
    requires
        b < 16,
    ensures
        dot(b, c) == By_xTimes(b, c),
{
    let bb = b as u16;
    let cc = c as u16;
    let x = pmult::<7, 7, u16>(bb, cc);
    lemma_pmult_fold(bb, cc, 8);
    assert(cc >> 0u16 == cc) by (bit_vector);
    assert(x == Pm(bb, cc));
    assert(bb < 16 && cc < 0x100 && x == ((if bb & 1u16 != 0u16 { cc << 0u16 } else { 0u16 })
        ^ (if bb & 2u16 != 0u16 { cc << 1u16 } else { 0u16 })
        ^ (if bb & 4u16 != 0u16 { cc << 2u16 } else { 0u16 })
        ^ (if bb & 8u16 != 0u16 { cc << 3u16 } else { 0u16 })
        ^ (if bb & 16u16 != 0u16 { cc << 4u16 } else { 0u16 })
        ^ (if bb & 32u16 != 0u16 { cc << 5u16 } else { 0u16 })
        ^ (if bb & 64u16 != 0u16 { cc << 6u16 } else { 0u16 })
        ^ (if bb & 128u16 != 0u16 { cc << 7u16 } else { 0u16 })) ==> x < 0x800) by (bit_vector);
    assert(x < 0x800 ==> x >> 3u16 < 0x100 && x < 0x8000) by (bit_vector);
    lemma_pmod_small(x, 12);
    lemma_remainders_step(x, 13);
    lemma_remainders_step(x, 14);
    lemma_remainders_step(x, 15);
    lemma_dot_cast(b, c);
    let r12 = remainders::<15, u16>(x, m(), 12);
    let r13 = remainders::<15, u16>(x, m(), 13);
    let r14 = remainders::<15, u16>(x, m(), 14);
    let r15 = remainders::<15, u16>(x, m(), 15);
    let d = dot(b, c);
    let c1 = xTimes(c);
    let c2 = xTimes(c1);
    let c3 = xTimes(c2);
    lemma_xtimes(c);
    lemma_xtimes(c1);
    lemma_xtimes(c2);
    let y = By_xTimes(b, c);
    assert(b < 16 && x == ((if bb & 1u16 != 0u16 { cc << 0u16 } else { 0u16 })
        ^ (if bb & 2u16 != 0u16 { cc << 1u16 } else { 0u16 })
        ^ (if bb & 4u16 != 0u16 { cc << 2u16 } else { 0u16 })
        ^ (if bb & 8u16 != 0u16 { cc << 3u16 } else { 0u16 })
        ^ (if bb & 16u16 != 0u16 { cc << 4u16 } else { 0u16 })
        ^ (if bb & 32u16 != 0u16 { cc << 5u16 } else { 0u16 })
        ^ (if bb & 64u16 != 0u16 { cc << 6u16 } else { 0u16 })
        ^ (if bb & 128u16 != 0u16 { cc << 7u16 } else { 0u16 })) && bb == b as u16 && cc == c as u16
        && r12 == x >> 3u16
        && r13 == (if ((r12 << 1u16) | ((x >> 2u16) & 1u16)) >= 0x100u16 { ((r12 << 1u16) | ((x >> 2u16) & 1u16)) ^ 0x11bu16 } else { (r12 << 1u16) | ((x >> 2u16) & 1u16) })
        && r14 == (if ((r13 << 1u16) | ((x >> 1u16) & 1u16)) >= 0x100u16 { ((r13 << 1u16) | ((x >> 1u16) & 1u16)) ^ 0x11bu16 } else { (r13 << 1u16) | ((x >> 1u16) & 1u16) })
        && r15 == (if ((r14 << 1u16) | ((x >> 0u16) & 1u16)) >= 0x100u16 { ((r14 << 1u16) | ((x >> 0u16) & 1u16)) ^ 0x11bu16 } else { (r14 << 1u16) | ((x >> 0u16) & 1u16) })
        && r13 < 0x100 && r14 < 0x100
        && d as u16 == r15
        && c1 == (c << 1u8) ^ (if (c >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 })
        && c2 == (c1 << 1u8) ^ (if (c1 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 })
        && c3 == (c2 << 1u8) ^ (if (c2 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 })
        && y == (if b & 1u8 != 0u8 { c } else { 0u8 }) ^ (if b & 2u8 != 0u8 { c1 } else { 0u8 })
            ^ (if b & 4u8 != 0u8 { c2 } else { 0u8 }) ^ (if b & 8u8 != 0u8 { c3 } else { 0u8 })
        ==> d == y) by (bit_vector);
}

/// The products by the constants of `MixColumns`, 0x02 and 0x03, as
/// `xTimes` sums. The SPARK crate's implementation calls `Lemma_Dot` at
/// each constant; the sums are stated once here.
pub proof fn lemma_dot_column(c: u8)
    ensures
        dot(0x02, c) == xTimes(c),
        dot(0x03, c) == c ^ xTimes(c),
{
    lemma_dot(0x02, c);
    lemma_dot(0x03, c);
    let (x1, x2, x3) = (xTimes(c), xTimes(xTimes(c)), xTimes(xTimes(xTimes(c))));
    assert(((if 0x02u8 & 1u8 != 0u8 { c } else { 0u8 }) ^ (if 0x02u8 & 2u8 != 0u8 { x1 } else { 0u8 }) ^ (if 0x02u8 & 4u8 != 0u8 { x2 } else { 0u8 }) ^ (if 0x02u8 & 8u8 != 0u8 { x3 } else { 0u8 })) == x1 && ((if 0x03u8 & 1u8 != 0u8 { c } else { 0u8 }) ^ (if 0x03u8 & 2u8 != 0u8 { x1 } else { 0u8 }) ^ (if 0x03u8 & 4u8 != 0u8 { x2 } else { 0u8 }) ^ (if 0x03u8 & 8u8 != 0u8 { x3 } else { 0u8 })) == c ^ x1) by (bit_vector);
}

/// The products by the constants of `InvMixColumns`, 0x09, 0x0b, 0x0d and
/// 0x0e, as `xTimes` sums.
pub proof fn lemma_dot_inverse_column(c: u8)
    ensures
        dot(0x09, c) == c ^ xTimes(xTimes(xTimes(c))),
        dot(0x0b, c) == c ^ xTimes(c) ^ xTimes(xTimes(xTimes(c))),
        dot(0x0d, c) == c ^ xTimes(xTimes(c)) ^ xTimes(xTimes(xTimes(c))),
        dot(0x0e, c) == xTimes(c) ^ xTimes(xTimes(c)) ^ xTimes(xTimes(xTimes(c))),
{
    lemma_dot(0x09, c);
    lemma_dot(0x0b, c);
    lemma_dot(0x0d, c);
    lemma_dot(0x0e, c);
    let (x1, x2, x3) = (xTimes(c), xTimes(xTimes(c)), xTimes(xTimes(xTimes(c))));
    assert(((if 0x09u8 & 1u8 != 0u8 { c } else { 0u8 }) ^ (if 0x09u8 & 2u8 != 0u8 { x1 } else { 0u8 }) ^ (if 0x09u8 & 4u8 != 0u8 { x2 } else { 0u8 }) ^ (if 0x09u8 & 8u8 != 0u8 { x3 } else { 0u8 })) == c ^ x3 && ((if 0x0bu8 & 1u8 != 0u8 { c } else { 0u8 }) ^ (if 0x0bu8 & 2u8 != 0u8 { x1 } else { 0u8 }) ^ (if 0x0bu8 & 4u8 != 0u8 { x2 } else { 0u8 }) ^ (if 0x0bu8 & 8u8 != 0u8 { x3 } else { 0u8 })) == c ^ x1 ^ x3 && ((if 0x0du8 & 1u8 != 0u8 { c } else { 0u8 }) ^ (if 0x0du8 & 2u8 != 0u8 { x1 } else { 0u8 }) ^ (if 0x0du8 & 4u8 != 0u8 { x2 } else { 0u8 }) ^ (if 0x0du8 & 8u8 != 0u8 { x3 } else { 0u8 })) == c ^ x2 ^ x3 && ((if 0x0eu8 & 1u8 != 0u8 { c } else { 0u8 }) ^ (if 0x0eu8 & 2u8 != 0u8 { x1 } else { 0u8 }) ^ (if 0x0eu8 & 4u8 != 0u8 { x2 } else { 0u8 }) ^ (if 0x0eu8 & 8u8 != 0u8 { x3 } else { 0u8 })) == x1 ^ x2 ^ x3)
        by (bit_vector);
}

// ---------------------------------------------------------------------
// Bytes and bits.

/// The prelude's `value` at `[8]` reads a byte back from its bits: the 8
/// bits of `p` from `s` are `y`'s, most significant first.
pub proof fn lemma_value_byte(p: Seq<bool>, s: int, y: u8)
    requires
        0 <= s,
        forall|j: int| 0 <= j < 8 ==> p[s + j] == #[trigger] bit::<u8>(y, j),
    ensures
        join_split::value::<u8>(p, s, 8) == y,
{
    // The value of the first `c` bits is the top `c` bits of `y`.
    assert forall|c: nat| c <= 8 implies #[trigger] join_split::value::<u8>(p, s, c) == y >> ((8 - c) as u8) by {
        lemma_value_byte_prefix(p, s, y, c);
    }
    assert(y >> 0u8 == y) by (bit_vector);
}

pub proof fn lemma_value_byte_prefix(p: Seq<bool>, s: int, y: u8, c: nat)
    requires
        0 <= s,
        c <= 8,
        forall|j: int| 0 <= j < 8 ==> p[s + j] == #[trigger] bit::<u8>(y, j),
    ensures
        join_split::value::<u8>(p, s, c) == y >> ((8 - c) as u8),
    decreases c,
{
    if c == 0 {
        assert(y >> 8u8 == 0) by (bit_vector);
    } else {
        lemma_value_byte_prefix(p, s, y, (c - 1) as nat);
        let v = y >> ((9 - c) as u8);
        let k = (8 - c) as u8;
        assert(p[s + c - 1] == bit::<u8>(y, c - 1));
        assert(bit::<u8>(y, c - 1) == ((y >> k) & 1u8 == 1u8));
        assert(k < 8 ==> y >> (k + 1u8) == (y >> k) >> 1u8) by (bit_vector);
        assert((9 - c) as u8 == k + 1u8);
        let b: u8 = if p[s + c - 1] { 1 } else { 0 };
        assert(k < 8 && v == (y >> k) >> 1u8 && b == (if (y >> k) & 1u8 == 1u8 { 1u8 } else { 0u8 })
            ==> (v as int) + (v as int) + (b as int) == (y >> k) as int) by (bit_vector);
    }
}

/// The prelude's `value` at `[8]` over the first `c` bits of `p` from `s`
/// has those bits, most significant first, and is below `2 ^^ c`.
pub proof fn lemma_value_bits_prefix(p: Seq<bool>, s: int, c: nat)
    requires
        0 <= s,
        c <= 8,
    ensures
        c < 8 ==> join_split::value::<u8>(p, s, c) >> (c as u8) == 0u8,
        forall|j: int| 0 <= j < c ==> ((join_split::value::<u8>(p, s, c) >> ((c - 1 - j) as u8)) & 1u8 == 1u8)
            == #[trigger] p[s + j],
    decreases c,
{
    if c == 0 {
        let z = join_split::value::<u8>(p, s, 0);
        assert(z == 0u8);
        assert(z == 0u8 ==> z >> 0u8 == 0u8) by (bit_vector);
    } else {
        lemma_value_bits_prefix(p, s, (c - 1) as nat);
        let v = join_split::value::<u8>(p, s, (c - 1) as nat);
        let w = join_split::value::<u8>(p, s, c);
        let b: u8 = if p[s + c - 1] { 1 } else { 0 };
        let k = (c - 1) as u8;
        assert(v >> k == 0u8);
        assert(k < 8 && v >> k == 0u8 ==> v < 128u8) by (bit_vector);
        lemma_double_8(v);
        assert(w == vstd::wrapping::u8_specs::wrapping_add(v << 1u8, b));
        assert(v < 128u8 && b <= 1 ==> vstd::wrapping::u8_specs::wrapping_add(v << 1u8, b) == ((v << 1u8) | b)) by {
            assert(v < 128u8 && b <= 1 ==> (v << 1u8) + b == ((v << 1u8) | b) && (v << 1u8) + b < 256) by (bit_vector);
        }
        let w2 = (v << 1u8) | b;
        assert(w == w2);
        assert(k < 7 && v >> k == 0u8 && b <= 1 && w2 == (v << 1u8) | b ==> w2 >> (k + 1u8) == 0u8) by (bit_vector);
        assert(b <= 1 && w2 == (v << 1u8) | b ==> ((w2 >> 0u8) & 1u8 == 1u8) == (b == 1u8)) by (bit_vector);
        assert forall|j: int| 0 <= j < c implies ((w >> ((c - 1 - j) as u8)) & 1u8 == 1u8) == #[trigger] p[s + j] by {
            if j < c - 1 {
                let t = (c - 2 - j) as u8;
                assert((c - 1 - j) as u8 == t + 1u8);
                assert(t < 7 && b <= 1 && v < 128u8 && w2 == (v << 1u8) | b ==> (w2 >> (t + 1u8)) == v >> t) by (bit_vector);
                assert(((v >> (((c - 1) - 1 - j) as u8)) & 1u8 == 1u8) == p[s + j]);
            }
        }
    }
}

/// The bits of the prelude's `value` at `[8]` over the 8 bits of `p` from
/// `s` are those bits: `split` then `join` is the identity on bits.
pub proof fn lemma_value_bits(p: Seq<bool>, s: int)
    requires
        0 <= s,
    ensures
        forall|j: int| 0 <= j < 8 ==> #[trigger] bit::<u8>(join_split::value::<u8>(p, s, 8), j) == p[s + j],
{
    lemma_value_bits_prefix(p, s, 8);
    assert forall|j: int| 0 <= j < 8 implies #[trigger] bit::<u8>(join_split::value::<u8>(p, s, 8), j) == p[s + j] by {
        assert((8 - 1 - j) as nat as u8 == (8 - 1 - j) as u8);
    }
}

/// `Word::add(v, v)` at `u8` is a shift by one, below `2 ^^ 7`.
pub proof fn lemma_double_8(v: u8)
    requires
        v < 0x80,
    ensures
        vstd::wrapping::u8_specs::wrapping_add(v, v) == v << 1u8,
{
    assert(v < 0x80 ==> v << 1u8 == v + v) by (bit_vector);
}

} // verus!
