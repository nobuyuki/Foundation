//! SBox.cry's `SBoxCorrect`, entry by entry: `affine b == SBox @ b` for
//! each of the 256 bytes `b`, by evaluation, as the SPARK crate's
//! `AES.Spec.SBox.SBox_Entries`
//! (spark/src/aes/foundation_spark-aes-spec-sbox-sbox_entries.ads).
//! [`lemma_sbox_entry`] states one entry; `SBoxCorrect` itself is stated in
//! [`super::properties`], with the other properties of algorithms/AES.
//!
//! How it is evaluated differs. The SPARK crate's unit is generated: for
//! each byte it lists the states that `pgcd`'s `inner` passes through, and
//! the provers check each step on constants (2501 checks, about 26 min).
//! Here Verus's interpreter (`by (compute_only)`) evaluates the entries,
//! one row of FIPS 197's Table 4 at a time ([`row_correct`]). The
//! prelude's polynomial functions are generic in
//! [`Word`](crate::cryptol::Word); the spec's `inverse` is first copied
//! here without the trait, at the types `pgcd` uses
//! ([`products_9`], [`remainders_9`], [`quotients_9`], [`inner_c`],
//! [`inverse_c`]), and proved equal to the original for all inputs
//! ([`lemma_inverse_c`]). The bit-sequence form of `affine` is likewise
//! proved equal to its byte form [`affine_byte`] ([`lemma_affine`]).
//! What is evaluated is then `affine_byte (inverse_c b) == SBox @ b`.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::polynomial_products::products;
#[cfg(verus_only)]
use crate::cryptol::polynomial_quotients::quotients;
#[cfg(verus_only)]
use crate::cryptol::polynomial_remainders::{remainders, top};
#[cfg(verus_only)]
use crate::cryptol::sequences::reverse;
#[cfg(verus_only)]
use crate::cryptol::words::bit;
#[cfg(verus_only)]
use super::gf2::{inner, inverse, is_poly9, is_state, lemma_division, lemma_top, pdiv, pmult, sub_mult};
#[cfg(verus_only)]
use super::sbox::{SBox, SBoxPolynomial, affine, bits};
#[cfg(verus_only)]
use super::lemmas::lemma_value_byte;

verus! {

// ---------------------------------------------------------------------
// `inverse` without the trait.

/// `Word::add(p, p)` at `u32`.
pub open spec fn double_32(p: u32) -> u32 {
    vstd::wrapping::u32_specs::wrapping_add(p, p)
}

/// The prelude's [`products`] at `v = 8` in a `u32`, as `GF2.pmult`
/// applies it, with the methods of `Word for u32` written out.
pub open spec fn products_9(x: u32, y: u32, n: nat) -> u32
    decreases n,
{
    if n == 0 {
        0
    } else {
        double_32(products_9(x, y, (n - 1) as nat)) ^ (if (y >> ((9 - 1 - (n - 1)) as nat as u32)) & 1u32
            == 1u32 {
            x
        } else {
            0u32
        })
    }
}

/// The bit of the leading `n` bits of the `[9]` `x` that step `n` of the
/// prelude's long division brings down, as 0 or 1.
pub open spec fn next_bit_9(x: u16, n: nat) -> u16 {
    if (x >> ((9 - 1 - (n - 1)) as nat as u16)) & 1u16 == 1u16 {
        1u16
    } else {
        0u16
    }
}

/// `Word::add(Word::add(r, r), b)` at `u16`: `r` shifted up by one, and the
/// bit `b` brought down.
pub open spec fn add_bit_16(r: u16, b: u16) -> u16 {
    vstd::wrapping::u16_specs::wrapping_add(vstd::wrapping::u16_specs::wrapping_add(r, r), b)
}

/// The prelude's `reduce` in a `u16`.
pub open spec fn reduce_16(t: u16, m: u16) -> u16 {
    if t as nat >= top(m as nat) {
        t ^ m
    } else {
        t
    }
}

/// The prelude's [`remainders`] at `u = 9` in a `u16`.
pub open spec fn remainders_9(x: u16, m: u16, n: nat) -> u16
    decreases n,
{
    if n == 0 {
        0
    } else {
        reduce_16(add_bit_16(remainders_9(x, m, (n - 1) as nat), next_bit_9(x, n)), m)
    }
}

/// One step of the prelude's `quotients` in a `u16`: the quotient so far
/// `q`, shifted up by one, and a bit set when the step subtracts `y` from
/// `t`.
pub open spec fn quotient_step_16(q: u16, t: u16, y: u16) -> u16 {
    vstd::wrapping::u16_specs::wrapping_add(
        vstd::wrapping::u16_specs::wrapping_add(q, q),
        if t as nat >= top(y as nat) { 1u16 } else { 0u16 },
    )
}

/// The prelude's [`quotients`] at `u = 9` in a `u16`.
pub open spec fn quotients_9(x: u16, y: u16, n: nat) -> u16
    decreases n,
{
    if n == 0 {
        0
    } else {
        quotient_step_16(
            quotients_9(x, y, (n - 1) as nat),
            add_bit_16(remainders_9(x, y, (n - 1) as nat), next_bit_9(x, n)),
            y,
        )
    }
}

/// `GF2.sub_mult` with `pmult` as `products_9`.
pub open spec fn sub_mult_c(x: u16, x1: u16, q: u16) -> u16 {
    (((x as u32) ^ products_9(q as u32, x1 as u32, 9)) & 0x1ff) as u16
}

/// The state after one step of `inner` from `s`, whose quotient is `q`.
pub open spec fn step_with(s: Seq<u16>, q: u16) -> Seq<u16> {
    seq![
        s[3], s[4], s[5],
        sub_mult_c(s[0], s[3], q), sub_mult_c(s[1], s[4], q), sub_mult_c(s[2], s[5], q),
    ]
}

/// The state after one step of `inner` from `s`, with the copies.
pub open spec fn step_c(s: Seq<u16>) -> Seq<u16> {
    step_with(s, quotients_9(s[0], s[3], 9))
}

/// `GF2.inner` with the copies, and with a bound `fuel` on the number of
/// steps in place of `inner`'s `decreases` on `r'`: from a state, `inner`
/// takes fewer steps than its `r'` ([`lemma_inner_c`]).
pub open spec fn inner_c(s: Seq<u16>, fuel: nat) -> Seq<u16>
    decreases fuel,
{
    if s[3] == 0 || fuel == 0 {
        s
    } else {
        inner_c(step_c(s), (fuel - 1) as nat)
    }
}

/// `GF2.inverse a SBoxPolynomial` with the copies: `pgcd`'s `u` is `s`, at
/// index 1, of the final state.
pub open spec fn inverse_c(a: u8) -> u8 {
    inner_c(seq![a as u16, 1, 0, SBoxPolynomial(), 0, 1], 0x200)[1] as u8
}

proof fn lemma_products_9(x: u32, y: u32, n: nat)
    ensures
        products::<8, u32>(x, y, n) == products_9(x, y, n),
    decreases n,
{
    if n > 0 {
        lemma_products_9(x, y, (n - 1) as nat);
    }
}

proof fn lemma_remainders_9(x: u16, m: u16, n: nat)
    ensures
        remainders::<9, u16>(x, m, n) == remainders_9(x, m, n),
    decreases n,
{
    if n > 0 {
        lemma_remainders_9(x, m, (n - 1) as nat);
    }
}

proof fn lemma_quotients_9(x: u16, y: u16, n: nat)
    ensures
        quotients::<9, u16>(x, y, n) == quotients_9(x, y, n),
    decreases n,
{
    if n > 0 {
        lemma_quotients_9(x, y, (n - 1) as nat);
        lemma_remainders_9(x, y, (n - 1) as nat);
    }
}

/// `inner_c` is `inner` from any state, given more fuel than `r'`: each
/// step of `inner` replaces `r'` by a smaller one.
proof fn lemma_inner_c(s: Seq<u16>, fuel: nat)
    requires
        is_state(s),
        fuel > s[3],
    ensures
        inner(s) == inner_c(s, fuel),
    decreases s[3],
{
    if s[3] != 0 {
        let q = pdiv(s[0], s[3]);
        let n = seq![
            s[3], s[4], s[5],
            sub_mult(s[0], s[3], q), sub_mult(s[1], s[4], q), sub_mult(s[2], s[5], q),
        ];
        lemma_quotients_9(s[0], s[3], 9);
        assert forall|x: u16, x1: u16| #[trigger] sub_mult(x, x1, q) == sub_mult_c(x, x1, q) by {
            lemma_products_9(q as u32, x1 as u32, 9);
        }
        assert(n =~= step_c(s));
        lemma_division(s[0], s[3]);
        lemma_top(s[3] as nat);
        assert forall|x: u16, x1: u16| is_poly9(#[trigger] sub_mult(x, x1, q)) by {
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
        assert(inner(s) == inner(n));
        lemma_inner_c(n, (fuel - 1) as nat);
    }
}

/// The spec's `inverse` at `SBoxPolynomial` is [`inverse_c`].
pub proof fn lemma_inverse_c(a: u8)
    ensures
        inverse(a, SBoxPolynomial()) == inverse_c(a),
{
    let s = seq![a as u16, 1, 0, SBoxPolynomial(), 0, 1];
    assert(is_state(s)) by {
        assert forall|i: int| 0 <= i < 6 implies is_poly9(#[trigger] s[i]) by {}
    }
    lemma_inner_c(s, 0x200);
}

// ---------------------------------------------------------------------
// `affine` on bytes.

/// SBox.cry's `affine`, after the inverse, on the byte `v`: bit `i` (of
/// weight `2 ^^ i`) of the result is bits `i`, `i + 4`, `i + 5`, `i + 6`
/// and `i + 7` of `v`, modulo 8, and bit `i` of `0x63`, added: `v` and its
/// rotations left by 1 to 4, and `0x63` [FIPS-PUB-197 Section 5.1.1,
/// equation 5.1].
pub open spec fn affine_byte(v: u8) -> u8 {
    v ^ ((v << 1u8) | (v >> 7u8)) ^ ((v << 2u8) | (v >> 6u8)) ^ ((v << 3u8) | (v >> 5u8)) ^ ((v
        << 4u8) | (v >> 4u8)) ^ 0x63u8
}

/// Bit `t` of a byte, as SBox.cry's `affine` reads it from `bits`.
proof fn lemma_bits(v: u8, t: int)
    requires
        0 <= t < 8,
    ensures
        bits(v)[t] == ((v >> ((7 - t) as u8)) & 1u8 == 1u8),
{
    assert(t / 8 == 0 && t % 8 == t);
}

/// Bit `i` (of weight `2 ^^ i`) of `affine_byte v`, where `a4` to `a7`
/// are `i + 4` to `i + 7` modulo 8.
proof fn lemma_affine_bit(v: u8, i: u8, a4: u8, a5: u8, a6: u8, a7: u8)
    requires
        i < 8,
        a4 == (i + 4) % 8,
        a5 == (i + 5) % 8,
        a6 == (i + 6) % 8,
        a7 == (i + 7) % 8,
    ensures
        ((affine_byte(v) >> i) & 1u8 == 1u8) == (((v >> i) & 1u8 == 1u8) ^ ((v >> a4) & 1u8 == 1u8) ^ ((v
            >> a5) & 1u8 == 1u8) ^ ((v >> a6) & 1u8 == 1u8) ^ ((v >> a7) & 1u8 == 1u8) ^ ((0x63u8 >> i) & 1u8
            == 1u8)),
{
    // The eight cases, as `i + 4` is not a `u8` in `bit_vector`.
    assert((i == 0 && a4 == 4 && a5 == 5 && a6 == 6 && a7 == 7) || (i == 1 && a4 == 5 && a5 == 6 && a6 == 7 && a7 == 0)
        || (i == 2 && a4 == 6 && a5 == 7 && a6 == 0 && a7 == 1) || (i == 3 && a4 == 7 && a5 == 0 && a6 == 1 && a7 == 2)
        || (i == 4 && a4 == 0 && a5 == 1 && a6 == 2 && a7 == 3) || (i == 5 && a4 == 1 && a5 == 2 && a6 == 3 && a7 == 4)
        || (i == 6 && a4 == 2 && a5 == 3 && a6 == 4 && a7 == 5) || (i == 7 && a4 == 3 && a5 == 4 && a6 == 5 && a7 == 6));
    assert((i == 0 && a4 == 4 && a5 == 5 && a6 == 6 && a7 == 7) || (i == 1 && a4 == 5 && a5 == 6 && a6 == 7 && a7 == 0)
        || (i == 2 && a4 == 6 && a5 == 7 && a6 == 0 && a7 == 1) || (i == 3 && a4 == 7 && a5 == 0 && a6 == 1 && a7 == 2)
        || (i == 4 && a4 == 0 && a5 == 1 && a6 == 2 && a7 == 3) || (i == 5 && a4 == 1 && a5 == 2 && a6 == 3 && a7 == 4)
        || (i == 6 && a4 == 2 && a5 == 3 && a6 == 4 && a7 == 5) || (i == 7 && a4 == 3 && a5 == 4 && a6 == 5 && a7 == 6)
        ==> ((((v ^ ((v << 1u8) | (v >> 7u8)) ^ ((v << 2u8) | (v >> 6u8)) ^ ((v << 3u8) | (v >> 5u8)) ^ ((v
        << 4u8) | (v >> 4u8)) ^ 0x63u8) >> i) & 1u8 == 1u8) == ((((v >> i) & 1u8 == 1u8) ^ ((v >> a4) & 1u8
        == 1u8) ^ ((v >> a5) & 1u8 == 1u8) ^ ((v >> a6) & 1u8 == 1u8) ^ ((v >> a7) & 1u8 == 1u8) ^ ((0x63u8
        >> i) & 1u8 == 1u8))))) by (bit_vector);
}

/// SBox.cry's `affine b` is [`affine_byte`] of `inverse b SBoxPolynomial`.
pub proof fn lemma_affine(b: u8)
    ensures
        affine(b) == affine_byte(inverse(b, SBoxPolynomial())),
{
    let v = inverse(b, SBoxPolynomial());
    let r = affine_byte(v);
    let c = reverse(bits(0b01100011));
    let b_ = reverse(bits(v));
    let b1 = Seq::new(
        8,
        |i: int|
            b_[i] ^ b_[(i + 4) % 8] ^ b_[(i + 5) % 8] ^ b_[(i + 6) % 8] ^ b_[(i + 7) % 8] ^ c[i],
    );
    assert(bits(v).len() == 8 && bits(0b01100011u8).len() == 8);
    assert forall|i: int| 0 <= i < 8 implies #[trigger] b_[i] == ((v >> (i as u8)) & 1u8 == 1u8) by {
        lemma_bits(v, 7 - i);
    }
    assert forall|i: int| 0 <= i < 8 implies #[trigger] c[i] == ((0x63u8 >> (i as u8)) & 1u8 == 1u8) by {
        lemma_bits(0b01100011u8, 7 - i);
    }
    assert forall|j: int| 0 <= j < 8 implies reverse(b1)[0 + j] == #[trigger] bit::<u8>(r, j) by {
        let i = 7 - j;
        assert(reverse(b1)[j] == b1[i]);
        let (a4, a5, a6, a7) = (((i + 4) % 8) as u8, ((i + 5) % 8) as u8, ((i + 6) % 8) as u8, ((i + 7) % 8) as u8);
        assert(b_[(i + 4) % 8] == ((v >> a4) & 1u8 == 1u8));
        assert(b_[(i + 5) % 8] == ((v >> a5) & 1u8 == 1u8));
        assert(b_[(i + 6) % 8] == ((v >> a6) & 1u8 == 1u8));
        assert(b_[(i + 7) % 8] == ((v >> a7) & 1u8 == 1u8));
        lemma_affine_bit(v, i as u8, a4, a5, a6, a7);
        assert(b_[i] == ((v >> (i as u8)) & 1u8 == 1u8));
        assert(c[i] == ((0x63u8 >> (i as u8)) & 1u8 == 1u8));
        assert(bit::<u8>(r, j) == ((r >> (i as u8)) & 1u8 == 1u8));
    }
    lemma_value_byte(reverse(b1), 0, r);
}

// ---------------------------------------------------------------------
// The entries.

/// Entries `16 * r` to `16 * r + n - 1` of the S-box, in row `r` of
/// FIPS 197's Table 4, are the affine transformation of the inverse, as
/// `inverse_c` and `affine_byte` compute them.
pub open spec fn row_prefix_correct(r: nat, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        let b = 16 * r + n - 1;
        affine_byte(inverse_c(b as u8)) == SBox()[b] && row_prefix_correct(r, (n - 1) as nat)
    }
}

/// All of row `r`.
pub open spec fn row_correct(r: nat) -> bool {
    row_prefix_correct(r, 16)
}

proof fn lemma_row_prefix(r: nat, n: nat, b: u8)
    requires
        row_prefix_correct(r, n),
        16 * r <= b < 16 * r + n,
    ensures
        affine_byte(inverse_c(b)) == SBox()[b as int],
    decreases n,
{
    if (b as nat) < 16 * r + n - 1 {
        lemma_row_prefix(r, (n - 1) as nat, b);
    }
}

// One evaluation per row.

proof fn lemma_row_0()
    ensures
        row_correct(0),
{
    assert(row_correct(0)) by (compute_only);
}

proof fn lemma_row_1()
    ensures
        row_correct(1),
{
    assert(row_correct(1)) by (compute_only);
}

proof fn lemma_row_2()
    ensures
        row_correct(2),
{
    assert(row_correct(2)) by (compute_only);
}

proof fn lemma_row_3()
    ensures
        row_correct(3),
{
    assert(row_correct(3)) by (compute_only);
}

proof fn lemma_row_4()
    ensures
        row_correct(4),
{
    assert(row_correct(4)) by (compute_only);
}

proof fn lemma_row_5()
    ensures
        row_correct(5),
{
    assert(row_correct(5)) by (compute_only);
}

proof fn lemma_row_6()
    ensures
        row_correct(6),
{
    assert(row_correct(6)) by (compute_only);
}

proof fn lemma_row_7()
    ensures
        row_correct(7),
{
    assert(row_correct(7)) by (compute_only);
}

proof fn lemma_row_8()
    ensures
        row_correct(8),
{
    assert(row_correct(8)) by (compute_only);
}

proof fn lemma_row_9()
    ensures
        row_correct(9),
{
    assert(row_correct(9)) by (compute_only);
}

proof fn lemma_row_a()
    ensures
        row_correct(10),
{
    assert(row_correct(10)) by (compute_only);
}

proof fn lemma_row_b()
    ensures
        row_correct(11),
{
    assert(row_correct(11)) by (compute_only);
}

proof fn lemma_row_c()
    ensures
        row_correct(12),
{
    assert(row_correct(12)) by (compute_only);
}

proof fn lemma_row_d()
    ensures
        row_correct(13),
{
    assert(row_correct(13)) by (compute_only);
}

proof fn lemma_row_e()
    ensures
        row_correct(14),
{
    assert(row_correct(14)) by (compute_only);
}

proof fn lemma_row_f()
    ensures
        row_correct(15),
{
    assert(row_correct(15)) by (compute_only);
}

/// SBox.cry's `SBoxCorrect` at the byte `b`: `affine b == SBox @ b`.
pub proof fn lemma_sbox_entry(b: u8)
    ensures
        affine(b) == SBox()[b as int],
{
    let r = (b / 16) as nat;
    match b / 16 {
        0u8 => lemma_row_0(),
        1u8 => lemma_row_1(),
        2u8 => lemma_row_2(),
        3u8 => lemma_row_3(),
        4u8 => lemma_row_4(),
        5u8 => lemma_row_5(),
        6u8 => lemma_row_6(),
        7u8 => lemma_row_7(),
        8u8 => lemma_row_8(),
        9u8 => lemma_row_9(),
        10u8 => lemma_row_a(),
        11u8 => lemma_row_b(),
        12u8 => lemma_row_c(),
        13u8 => lemma_row_d(),
        14u8 => lemma_row_e(),
        _ => lemma_row_f(),
    }
    lemma_row_prefix(r, 16, b);
    lemma_inverse_c(b);
    lemma_affine(b);
}

} // verus!
