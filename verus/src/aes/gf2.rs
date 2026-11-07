//! The polynomial arithmetic over GF(2) that algorithms/AES/SBox.cry
//! imports from shared/algebra/Polynomial/GF2.cry (`inverse`, through
//! `pgcd`), at the types SBox.cry uses it at: `inverse a p` with `a : [8]`
//! and `p : [9]`, so `pgcd` works on polynomials of type `[9]`
//! [FIPS-PUB-197 Section 4.4]. As the SPARK crate's `AES.Spec.GF2`
//! (spark/src/aes/foundation_spark-aes-spec-gf2.ads).
//!
//! A polynomial is held as its coefficient bits in an unsigned integer, as
//! in the prelude ([`crate::cryptol::polynomial_products`]): a `[9]` in a
//! `u16`, and a `[17]` product of two of them in a `u32`. GF2.cry's
//! `(^*) = pmult` and `(^/) = pdiv` are the prelude's
//! [`pmult`](polynomial_products::pmult) and
//! [`pdiv`](polynomial_quotients::pdiv) at these types. The SPARK crate
//! states both inline instead, `pmult` as a closed form because the
//! prelude's fold made its exhaustive S-box proof much slower, and `pdiv`
//! by its own long division because the prelude's did not let
//! `Inner_Step`'s postcondition prove; here the prelude's are used, and
//! [`lemma_division`] proves what `inner`'s termination needs of them.
//!
//! `inner`, local to `pgcd` in the Cryptol, is a top-level function here,
//! as in the SPARK crate. Its recursion ends because each step replaces
//! `r'` by a remainder modulo `r'`, which is smaller; that is its
//! `decreases`, proved by [`inner_decreases`].

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::{polynomial_products, polynomial_quotients, polynomial_remainders};
#[cfg(verus_only)]
use crate::cryptol::polynomial_remainders::{remainders, top};
#[cfg(verus_only)]
use crate::cryptol::polynomial_quotients::quotients;
#[cfg(verus_only)]
use crate::cryptol::polynomial_products::products;

verus! {

/// Whether `x` is a `[9]`.
pub open spec fn is_poly9(x: u16) -> bool {
    x < 0x200
}

/// GF2.cry: `(^*) = pmult` (GF2.cry:42), at type `[9] -> [9] -> [17]`:
/// the product of `x` and `y` as polynomials over GF(2). The prelude's
/// `` pmult`{8, 8} ``, in a `u32`.
pub open spec fn pmult(x: u16, y: u16) -> u32 {
    polynomial_products::pmult::<8, 8, u32>(x as u32, y as u32)
}

/// GF2.cry: `(^/) = pdiv` (GF2.cry:47), at type `[9] -> [9] -> [9]`: the
/// quotient of `x` by `y` as polynomials over GF(2). The prelude's
/// `` pdiv`{9, 9} ``.
pub open spec fn pdiv(x: u16, y: u16) -> u16
    recommends
        is_poly9(x),
        is_poly9(y),
        y != 0,
{
    polynomial_quotients::pdiv::<9, 9, u16>(x, y)
}

/// GF2.cry, in `pgcd`'s `inner`: `x ^. x' = drop (zext x ^ q ^* x')`
/// (GF2.cry:121), at type `[9]`, with the quotient `q` of the step as an
/// argument: `x - q * x'`, of which `drop` keeps the low nine
/// coefficients. The SPARK crate's `Sub_Mult`.
pub open spec fn sub_mult(x: u16, x1: u16, q: u16) -> u16 {
    (((x as u32) ^ pmult(q, x1)) & 0x1ff) as u16
}

/// GF2.cry, in `pgcd`: `type State = [6]Poly`, the state
/// `[r, s, t, r', s', t']` of the extended Euclidean algorithm, with
/// `Poly = [9]`: whether `s` is one.
pub open spec fn is_state(s: Seq<u16>) -> bool {
    &&& s.len() == 6
    &&& forall|i: int| 0 <= i < 6 ==> is_poly9(#[trigger] s[i])
}

/// GF2.cry, in `pgcd` (GF2.cry:112): `inner [r, s, t, r', s', t'] =
/// if r' == <| 0 |> then [r, s, t, r', s', t'] else inner [r', s', t',
/// r'', s'', t'']`, where `q = r ^/ r'` and `[r'', s'', t''] = zipWith (^.)
/// [r, s, t] [r', s', t']`. The state is indexed from 0, so `r'` is
/// `s[3]`. Its `decreases` is `r'`, as in the SPARK crate.
pub open spec fn inner(s: Seq<u16>) -> Seq<u16>
    decreases s[3],
    when is_state(s)
    via inner_decreases
{
    if s[3] == 0 {
        s
    } else {
        let q = pdiv(s[0], s[3]);
        inner(seq![
            s[3], s[4], s[5],
            sub_mult(s[0], s[3], q), sub_mult(s[1], s[4], q), sub_mult(s[2], s[5], q),
        ])
    }
}

/// `inner`'s recursion is well founded: the new `r'`, `r - (r ^/ r') * r'`,
/// is the remainder of `r` modulo `r'` ([`lemma_division`]), which is
/// below `r'`.
#[via_fn]
proof fn inner_decreases(s: Seq<u16>) {
    if s[3] != 0 {
        let q = pdiv(s[0], s[3]);
        lemma_division(s[0], s[3]);
        lemma_top(s[3] as nat);
        let n = seq![
            s[3], s[4], s[5],
            sub_mult(s[0], s[3], q), sub_mult(s[1], s[4], q), sub_mult(s[2], s[5], q),
        ];
        assert forall|x: u16, x1: u16, q: u16| is_poly9(#[trigger] sub_mult(x, x1, q)) by {
            let p = pmult(q, x1);
            assert((((x as u32) ^ p) & 0x1ff) < 0x200) by (bit_vector);
        }
        assert(is_state(n)) by {
            assert forall|i: int| 0 <= i < 6 implies is_poly9(#[trigger] n[i]) by {
                if i < 3 {
                    assert(n[i] == s[i + 3]);
                }
            }
        }
    }
}

/// GF2.cry: `pgcd a b = [g, u, v, a', b']` (GF2.cry:107), where
/// `[g, u, v, _, b', a'] = inner [zext a, <| 1 |>, <| 0 |>, zext b,
/// <| 0 |>, <| 1 |>]`, at `wa = 7` and `wb = 8` (`a : [8]`, `b : [9]`), so
/// `Poly = [9]`.
pub open spec fn pgcd(a: u8, b: u16) -> Seq<u16>
    recommends
        is_poly9(b),
{
    let s = inner(seq![a as u16, 1, 0, b, 0, 1]);
    seq![s[0], s[1], s[2], s[5], s[4]]
}

/// GF2.cry: `inverse a p = tail (pgcd`{wb=v} a p @ 1)` (GF2.cry:135), at
/// `u = 7` and `v = 8` (`a : [8]`, `p : [9]`, result `[8]`): the
/// multiplicative inverse of `a` modulo `p`, by the extended Euclidean
/// algorithm. `tail` of the `[9]` Bezout coefficient drops its leading
/// coefficient, that of `x ^^ 8`, which the cast to `u8` does.
pub open spec fn inverse(a: u8, p: u16) -> u8
    recommends
        is_poly9(p),
{
    pgcd(a, p)[1] as u8
}

// ---------------------------------------------------------------------
// The long division of the prelude, at the types of `pgcd`.

/// `top m`, the leading term `x ^^ (pdeg m)` of a nonzero `m`, is a power
/// of 2 with `top m <= m < 2 * top m`.
pub proof fn lemma_top(m: nat)
    requires
        0 < m < 0x10000,
    ensures
        1 <= top(m) <= m < 2 * top(m),
        (top(m) as u32) & (((top(m) as u32) - 1u32) as u32) == 0u32,
    decreases m,
{
    if m > 1 {
        lemma_top(m / 2);
        let t = top(m / 2) as u32;
        let t2 = top(m) as u32;
        assert(t2 == t << 1u32) by {
            assert(t < 0x8000 ==> t << 1u32 == t + t) by (bit_vector);
        }
        assert(1 <= t < 0x8000 && t & ((t - 1u32) as u32) == 0u32
            ==> (t << 1u32) & (((t << 1u32) - 1u32) as u32) == 0u32) by (bit_vector);
    } else {
        assert(1u32 & 0u32 == 0u32) by (bit_vector);
    }
}

/// Doubling a `u32` by `Word::add` is a shift by one.
proof fn lemma_double_u32(a: u32)
    ensures
        vstd::wrapping::u32_specs::wrapping_add(a, a) == a << 1u32,
{
    assert(a < 0x8000_0000 ==> a << 1u32 == a + a) by (bit_vector);
    assert(a >= 0x8000_0000 ==> (a << 1u32) as int == a + a - 0x1_0000_0000) by (bit_vector);
}

/// The leading `n` bits of a `[9]` `x` are the leading `n - 1` bits, one
/// place up, and bit `n - 1`.
proof fn lemma_shift_step(x: u32, n: nat)
    requires
        1 <= n <= 9,
    ensures
        x >> ((9 - n) as u32) == ((x >> ((10 - n) as u32)) << 1u32) ^ ((x >> ((9 - n) as u32)) & 1u32),
{
    let s = (9 - n) as u32;
    assert(s < 9 ==> x >> s == ((x >> (s + 1u32)) << 1u32) ^ ((x >> s) & 1u32)) by (bit_vector);
    assert((10 - n) as u32 == s + 1u32);
}

/// `products` is linear in its first argument.
proof fn lemma_products_xor(a: u32, b: u32, y: u32, n: nat)
    ensures
        products::<8, u32>(a ^ b, y, n) == products::<8, u32>(a, y, n) ^ products::<8, u32>(b, y, n),
    decreases n,
{
    if n > 0 {
        lemma_products_xor(a, b, y, (n - 1) as nat);
        let pa = products::<8, u32>(a, y, (n - 1) as nat);
        let pb = products::<8, u32>(b, y, (n - 1) as nat);
        lemma_double_u32(pa);
        lemma_double_u32(pb);
        lemma_double_u32(pa ^ pb);
        assert(((pa ^ pb) << 1u32) == (pa << 1u32) ^ (pb << 1u32)) by (bit_vector);
        assert(((pa << 1u32) ^ (pb << 1u32)) ^ (a ^ b) == ((pa << 1u32) ^ a) ^ ((pb << 1u32) ^ b))
            by (bit_vector);
        assert(((pa << 1u32) ^ (pb << 1u32)) ^ 0u32 == ((pa << 1u32) ^ 0u32) ^ ((pb << 1u32) ^ 0u32))
            by (bit_vector);
    } else {
        assert((0u32 ^ 0u32) == 0u32) by (bit_vector);
    }
}

/// `products` commutes with doubling its first argument.
proof fn lemma_products_double(a: u32, y: u32, n: nat)
    ensures
        products::<8, u32>(a << 1u32, y, n) == products::<8, u32>(a, y, n) << 1u32,
    decreases n,
{
    if n > 0 {
        lemma_products_double(a, y, (n - 1) as nat);
        let p = products::<8, u32>(a, y, (n - 1) as nat);
        lemma_double_u32(p);
        lemma_double_u32(p << 1u32);
        assert(((p << 1u32) << 1u32) ^ (a << 1u32) == ((p << 1u32) ^ a) << 1u32) by (bit_vector);
        assert(((p << 1u32) << 1u32) ^ 0u32 == ((p << 1u32) ^ 0u32) << 1u32) by (bit_vector);
    } else {
        assert((0u32 << 1u32) == 0u32) by (bit_vector);
    }
}

/// `products` of 0 is 0, and of 1 is the leading `n` bits of the `[9]`
/// `y`.
proof fn lemma_products_unit(y: u32, n: nat)
    requires
        y < 0x200,
        n <= 9,
    ensures
        products::<8, u32>(0, y, n) == 0,
        products::<8, u32>(1, y, n) == y >> ((9 - n) as u32),
    decreases n,
{
    if n > 0 {
        lemma_products_unit(y, (n - 1) as nat);
        lemma_double_u32(0);
        lemma_double_u32(y >> ((10 - n) as u32));
        lemma_shift_step(y, n);
        let s = (9 - n) as u32;
        assert(((y >> s) & 1u32) == 1u32 || ((y >> s) & 1u32) == 0u32) by (bit_vector);
        assert((0u32 << 1u32) ^ 0u32 == 0u32) by (bit_vector);
    } else {
        assert(y < 0x200 ==> y >> 9u32 == 0u32) by (bit_vector);
    }
}

/// `pmult` of a quotient extended by one bit `c`.
proof fn lemma_pmult_step(q: u32, c: u32, y: u32)
    requires
        y < 0x200,
        c == 0 || c == 1,
    ensures
        polynomial_products::pmult::<8, 8, u32>((q << 1u32) ^ c, y)
            == (polynomial_products::pmult::<8, 8, u32>(q, y) << 1u32) ^ (if c == 1 { y } else { 0 }),
{
    lemma_products_xor(q << 1u32, c, y, 9);
    lemma_products_double(q, y, 9);
    lemma_products_unit(y, 9);
    assert(y >> 0u32 == y) by (bit_vector);
}

/// The long division of the prelude at `[9]`, step by step: after `n`
/// steps, the remainder is below `top y` and the quotient below `2 ^^ n`,
/// and quotient times `y` plus remainder is the leading `n` bits of `x`.
pub proof fn lemma_division_steps(x: u16, y: u16, n: nat)
    requires
        is_poly9(x),
        is_poly9(y),
        y != 0,
        n <= 9,
    ensures
        remainders::<9, u16>(x, y, n) < top(y as nat),
        quotients::<9, u16>(x, y, n) < (1u32 << (n as u32)),
        pmult(quotients::<9, u16>(x, y, n), y) ^ (remainders::<9, u16>(x, y, n) as u32)
            == (x as u32) >> ((9 - n) as u32),
    decreases n,
{
    lemma_top(y as nat);
    let T = top(y as nat) as u32;
    if n == 0 {
        assert(products::<8, u32>(0, y as u32, 9) == 0) by {
            lemma_products_unit(y as u32, 9);
        }
        let xx = x as u32;
        assert(xx < 0x200 ==> xx >> 9u32 == 0u32) by (bit_vector);
        assert(0u32 ^ 0u32 == 0u32 && (1u32 << 0u32) == 1u32) by (bit_vector);
    } else {
        lemma_division_steps(x, y, (n - 1) as nat);
        let r = remainders::<9, u16>(x, y, (n - 1) as nat);
        let q = quotients::<9, u16>(x, y, (n - 1) as nat);
        let b: u16 = if crate::cryptol::words::bit_in(9, x, n - 1) { 1 } else { 0 };
        let t = vstd::wrapping::u16_specs::wrapping_add(
            vstd::wrapping::u16_specs::wrapping_add(r, r), b);
        let c: u16 = if t as nat >= top(y as nat) { 1 } else { 0 };
        assert(t == 2 * r + b);
        let q1 = quotients::<9, u16>(x, y, n);
        let r1 = remainders::<9, u16>(x, y, n);
        assert(q1 == vstd::wrapping::u16_specs::wrapping_add(
            vstd::wrapping::u16_specs::wrapping_add(q, q), c));
        let m = (n - 1) as u32;
        assert(q < (1u32 << m));
        assert(m < 9 && (q as u32) < (1u32 << m) ==> (q as u32) < 0x100) by (bit_vector);
        assert(q1 == 2 * q + c);
        assert((q1 as u32) == ((q as u32) << 1u32) ^ (c as u32)) by {
            let qq = q as u32;
            let cc = c as u32;
            assert(qq < 0x100 && cc < 2 ==> qq * 2 + cc == (qq << 1u32) ^ cc) by (bit_vector);
        }
        assert(q1 < (1u32 << (n as u32))) by {
            let qq = q as u32;
            let cc = c as u32;
            assert(m < 9 && qq < (1u32 << m) && cc < 2 ==> qq * 2 + cc < (1u32 << (m + 1u32))) by (bit_vector);
            assert(n as u32 == m + 1u32);
        }
        // The remainder.
        let tt = t as u32;
        let yy = y as u32;
        assert(r1 == crate::cryptol::polynomial_remainders::reduce(t, y));
        assert(tt < 2 * T);
        assert(T <= 0x100 && T >= 1 && T & ((T - 1u32) as u32) == 0u32 && tt >= T && tt < (T << 1u32)
            && yy >= T && yy < (T << 1u32) ==> (tt ^ yy) < T) by (bit_vector);
        assert(T <= 0x100 ==> (T << 1u32) == T + T) by (bit_vector);
        assert(T <= 0x100) by {
            assert(T < 0x200 && T & ((T - 1u32) as u32) == 0u32 ==> T <= 0x100) by (bit_vector);
        }
        assert((r1 as u32) == (if c == 1 { tt ^ yy } else { tt })) by {
            assert(tt < 0x200 && yy < 0x200 ==> (tt ^ yy) < 0x200) by (bit_vector);
        }
        // The identity.
        lemma_pmult_step(q as u32, c as u32, yy);
        let p = pmult(q, y);
        let rr = r as u32;
        let bb = b as u32;
        let xx = x as u32;
        assert(tt == (rr << 1u32) ^ bb) by {
            assert(rr < 0x100 && bb < 2 ==> rr * 2 + bb == (rr << 1u32) ^ bb) by (bit_vector);
        }
        lemma_shift_step(xx, n);
        let s = (9 - n) as u32;
        assert(bb == ((xx >> s) & 1u32)) by {
            assert(crate::cryptol::words::bit_in(9, x, n - 1) == (((x >> (s as u16)) & 1u16) == 1u16));
            assert(x < 0x200 && s < 9 ==> ((((x >> (s as u16)) & 1u16) == 1u16) == ((((x as u32) >> s) & 1u32) == 1u32))
                && ((((x as u32) >> s) & 1u32) == 0u32 || (((x as u32) >> s) & 1u32) == 1u32)) by (bit_vector);
        }
        assert(((p << 1u32) ^ yy) ^ (tt ^ yy) == (p << 1u32) ^ tt) by (bit_vector);
        assert(((p << 1u32) ^ 0u32) ^ tt == (p << 1u32) ^ tt) by (bit_vector);
        assert((p << 1u32) ^ ((rr << 1u32) ^ bb) == ((p ^ rr) << 1u32) ^ bb) by (bit_vector);
    }
}

/// The prelude's `pdiv` at `[9]`: `x - (x ^/ y) * y` is the remainder of
/// `x` modulo `y`, below `top y`.
pub proof fn lemma_division(x: u16, y: u16)
    requires
        is_poly9(x),
        is_poly9(y),
        y != 0,
    ensures
        sub_mult(x, y, pdiv(x, y)) == remainders::<9, u16>(x, y, 9),
        sub_mult(x, y, pdiv(x, y)) < top(y as nat),
{
    lemma_division_steps(x, y, 9);
    let p = pmult(pdiv(x, y), y);
    let r = remainders::<9, u16>(x, y, 9) as u32;
    let xx = x as u32;
    assert(xx >> 0u32 == xx) by (bit_vector);
    assert(p ^ r == xx ==> xx ^ p == r) by (bit_vector);
    lemma_top(y as nat);
    assert(r < 0x200 ==> (r & 0x1ff) == r) by (bit_vector);
}

} // verus!
