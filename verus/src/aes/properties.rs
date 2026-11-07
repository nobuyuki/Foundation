//! The properties that algorithms/AES states about itself, proved of the
//! spec layer, as the SPARK crate's `AES.Spec.Properties`
//! (spark/src/aes/foundation_spark-aes-spec-properties.ads): GF28.cry's
//! `GF28MultiplicationCorrect`, SBox.cry's `SBoxCorrect` and `SBoxInverts`,
//! Cipher.cry's `SubBytesInverts`, `ShiftRowsInverts`,
//! `MixColumnsStepInverts`, `MixColumnsInverts`, `AddRoundKeyInvolution`,
//! `RoundInverts`, `InvCipherEquivalence`, `CipherInverts` and
//! `CipherInverts'`, and Main.cry's `EncryptInverts`. As in the SPARK
//! crate, SBox.cry's `SBoxPolynomialIsIrreducible` and `inverseCorrect` are
//! not stated (spark/doc/proving.md, "The Cryptol's own properties,
//! re-proved"). `SBoxCorrect` is proved entry by entry, by evaluation, in
//! [`super::sbox_entries`].
//!
//! Each property is a proof function named as the Cryptol property, whose
//! `ensures` is the property's body and whose parameters are its
//! arguments; the Cryptol types of the arguments (`Block`, `AESWord`,
//! `[Nr k + 1]Block`, `[k]`, `[128]`) are its `requires`. `'` is not
//! allowed in a Rust name, so `CipherInverts'` is `CipherInverts_prime`.
//! Where the Cryptol is polymorphic in the key size, `{k} (Key k)`, the
//! property is generic in the const `k` and requires `Key k`: one proof
//! holds for every key size, as the SPARK crate obtains with its
//! dispatchers. The other functions are the lemmas the properties are
//! proved with.
//!
//! Differences from the SPARK crate's proofs:
//! - Verus's `==` on sequences is equality, so the SPARK crate's `*_Eq`
//!   lemmas (a function maps equal arrays to equal results) are not
//!   needed.
//! - `SBoxInverts` is evaluated by Verus's interpreter for the 256 bytes;
//!   the SPARK crate's provers evaluate it from the tables.
//! - `MixColumnsStepInverts` rewrites each `•` by a constant with `xTimes`
//!   ([`lemma_dot_column`], [`lemma_dot_inverse_column`]) and leaves the rest
//!   to one `bit_vector` query, in
//!   place of the SPARK crate's linearity lemmas (`Lemma_xTimes_Xor`,
//!   `Lemma_Dot_Xor`, `Lemma_Dot_Xor4`) and `Lemma_Coefficients`.
//! - `pmult`'s commutativity is proved of its closed form [`Pm`] by
//!   `bit_vector` ([`lemma_pm_commutes`]), and the bound the SPARK crate's
//!   `Lemma_Pmult_Bound` gives comes with [`lemma_pm_step`].

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::folds::{foldl, foldl_take};
#[cfg(verus_only)]
use crate::cryptol::join_split;
#[cfg(verus_only)]
use crate::cryptol::polynomial_products::{pmult, products};
#[cfg(verus_only)]
use crate::cryptol::polynomial_remainders::remainders;
#[cfg(verus_only)]
use crate::cryptol::sequences::reverse;
#[cfg(verus_only)]
use super::cipher::{
    AddRoundKey, Cipher, InvCipher, InvCipher_prime, InvMixColumns, InvMixColumnsStep, InvRound,
    InvRound_prime, InvShiftRows, InvSubBytes, MixColumns, MixColumnsStep, Round, ShiftRows, SubBytes,
};
#[cfg(verus_only)]
use super::gf28::{dot, lemma_dot as lemma_dot_cast, lemma_remainders_byte, m, xTimes};
#[cfg(verus_only)]
use super::key_expansion::KeyExpansion;
#[cfg(verus_only)]
use super::lemmas::{
    Pm, lemma_dot, lemma_dot_column, lemma_dot_inverse_column, lemma_double_16, lemma_pm_commutes,
    lemma_pm_step, lemma_pmod_small, lemma_pmult_fold, lemma_remainders_step, lemma_value_bits,
    lemma_value_byte, lemma_xtimes,
};
#[cfg(verus_only)]
use super::main::{AES, join_block, split_block, split_key};
#[cfg(verus_only)]
use super::sbox::{InvSBox, SBox, affine, bits};
#[cfg(verus_only)]
use super::sbox_entries::lemma_sbox_entry;
#[cfg(verus_only)]
use super::types::{AESWord, Block, Key, Nr, is_round_keys, join, split};

verus! {

// ---------------------------------------------------------------------
// GF28

/// GF28.cry, in `GF28MultiplicationCorrect`: the fold's function
/// `\a bi -> xTimes a ^ if bi then c else 0x00`, closing over `c`. The
/// SPARK crate's `Mult_Step`, whose `Mult_Env` is the closure here.
pub open spec fn mult_step(c: u8) -> spec_fn(u8, bool) -> u8 {
    |a: u8, bi: bool| xTimes(a) ^ (if bi { c } else { 0x00u8 })
}

/// GF28.cry: `property GF28MultiplicationCorrect b c = xTimes b == b • 2
/// /\ b • c == foldl (\a bi -> xTimes a ^ if bi then c else 0x00) 0x00 b`
/// [FIPS-PUB-197 Section 4.2]. The fold is over the bits of `b`, most
/// significant first, as Cryptol orders them: `b` as a sequence is
/// [`bits`]`(b)`. The two conjuncts are proved apart, as in the SPARK
/// crate.
pub proof fn GF28MultiplicationCorrect(b: u8, c: u8)
    ensures
        xTimes(b) == dot(b, 2),
        dot(b, c) == foldl(mult_step(c), 0x00u8, bits(b)),
{
    lemma_xtimes_dot(b);
    lemma_dot_foldl(b, c);
}

/// GF28.cry's `pmult` at `[8]` is the closed form [`Pm`].
proof fn lemma_pmult_pm(b: u8, c: u8)
    ensures
        pmult::<7, 7, u16>(b as u16, c as u16) == Pm(b as u16, c as u16),
{
    lemma_pmult_fold(b as u16, c as u16, 8);
    let cc = c as u16;
    assert(cc >> 0u16 == cc) by (bit_vector);
}

/// `(•)` is commutative, as `pmult` is. The SPARK crate's
/// `Lemma_Pmult_Commutes`, for the product reduced.
proof fn lemma_dot_commutes(b: u8, c: u8)
    ensures
        dot(b, c) == dot(c, b),
{
    lemma_pmult_pm(b, c);
    lemma_pmult_pm(c, b);
    lemma_pm_commutes(b as u16, c as u16);
}

/// GF28MultiplicationCorrect's first conjunct: `xTimes b == b • 2`.
proof fn lemma_xtimes_dot(b: u8)
    ensures
        xTimes(b) == dot(b, 2),
{
    lemma_dot_commutes(b, 2);
    lemma_dot(2, b);
    let x = xTimes(b);
    assert((if 2u8 & 1u8 != 0u8 { b } else { 0u8 }) ^ (if 2u8 & 2u8 != 0u8 { x } else { 0u8 }) ^ (if 2u8
        & 4u8 != 0u8 { xTimes(x) } else { 0u8 }) ^ (if 2u8 & 8u8 != 0u8 { xTimes(xTimes(x)) } else { 0u8 })
        == x) by {
        let x2 = xTimes(x);
        let x3 = xTimes(x2);
        assert((if 2u8 & 1u8 != 0u8 { b } else { 0u8 }) ^ (if 2u8 & 2u8 != 0u8 { x } else { 0u8 }) ^ (if 2u8
            & 4u8 != 0u8 { x2 } else { 0u8 }) ^ (if 2u8 & 8u8 != 0u8 { x3 } else { 0u8 }) == x) by (bit_vector);
    }
}

/// The remainder is linear: the first `n` steps of `pmod (x ^ y) m` are
/// those of `pmod x m` and `pmod y m`, added. The SPARK crate's
/// `Lemma_Pmod_Xor`.
proof fn lemma_pmod_xor(x: u16, y: u16, n: nat)
    requires
        n <= 15,
    ensures
        remainders::<15, u16>(x ^ y, m(), n) == remainders::<15, u16>(x, m(), n) ^ remainders::<15, u16>(y, m(), n),
    decreases n,
{
    if n == 0 {
        assert(0u16 ^ 0u16 == 0u16) by (bit_vector);
    } else {
        lemma_pmod_xor(x, y, (n - 1) as nat);
        lemma_remainders_step(x, n);
        lemma_remainders_step(y, n);
        lemma_remainders_step(x ^ y, n);
        let k = (15 - n) as u16;
        let rx = remainders::<15, u16>(x, m(), (n - 1) as nat);
        let ry = remainders::<15, u16>(y, m(), (n - 1) as nat);
        let rxy = remainders::<15, u16>(x ^ y, m(), (n - 1) as nat);
        let sx = remainders::<15, u16>(x, m(), n);
        let sy = remainders::<15, u16>(y, m(), n);
        let sxy = remainders::<15, u16>(x ^ y, m(), n);
        assert(rx < 0x100 && ry < 0x100 && rxy == rx ^ ry && sx == (if ((rx << 1u16) | ((x >> k) & 1u16)) >= 0x100u16 { ((rx << 1u16) | ((x >> k) & 1u16)) ^ 0x11bu16 } else { ((rx << 1u16) | ((x >> k) & 1u16)) }) && sy == (if ((ry << 1u16) | ((y >> k) & 1u16)) >= 0x100u16 { ((ry << 1u16) | ((y >> k) & 1u16)) ^ 0x11bu16 } else { ((ry << 1u16) | ((y >> k) & 1u16)) })
            && sxy == (if ((rxy << 1u16) | (((x ^ y) >> k) & 1u16)) >= 0x100u16 { ((rxy << 1u16) | (((x ^ y) >> k) & 1u16)) ^ 0x11bu16 } else { ((rxy << 1u16) | (((x ^ y) >> k) & 1u16)) }) ==> sxy == sx ^ sy) by (bit_vector);
    }
}

/// The first `n` bits of `x * x`, as a `[15]`, are the first `n + 1` bits
/// of `x`, whose first bit is 0, so their remainders agree. The SPARK
/// crate's `Lemma_Pmod_Shift`.
proof fn lemma_pmod_shift(x: u16, n: nat)
    requires
        n <= 14,
        x < 0x4000,
    ensures
        remainders::<15, u16>(x << 1u16, m(), n) == remainders::<15, u16>(x, m(), n + 1),
    decreases n,
{
    if n == 0 {
        lemma_remainders_step(x, 1);
        let r = remainders::<15, u16>(x, m(), 0);
        let s = remainders::<15, u16>(x, m(), 1);
        assert(x < 0x4000 && r == 0u16 && s == (if ((r << 1u16) | ((x >> 14u16) & 1u16)) >= 0x100u16 { ((r << 1u16) | ((x >> 14u16) & 1u16)) ^ 0x11bu16 } else { ((r << 1u16) | ((x >> 14u16) & 1u16)) }) ==> s == 0u16) by (bit_vector);
    } else {
        lemma_pmod_shift(x, (n - 1) as nat);
        lemma_remainders_step(x << 1u16, n);
        lemma_remainders_step(x, n + 1);
        let k = (14 - n) as u16;
        assert((15 - n) as u16 == k + 1u16);
        assert((15 - (n + 1)) as u16 == k);
        let r1 = remainders::<15, u16>(x << 1u16, m(), (n - 1) as nat);
        let r2 = remainders::<15, u16>(x, m(), n);
        let s1 = remainders::<15, u16>(x << 1u16, m(), n);
        let s2 = remainders::<15, u16>(x, m(), n + 1);
        assert(x < 0x4000 && k < 14 && r1 == r2 && s1 == (if ((r1 << 1u16) | (((x << 1u16) >> (k + 1u16)) & 1u16)) >= 0x100u16 { ((r1 << 1u16) | (((x << 1u16) >> (k + 1u16)) & 1u16)) ^ 0x11bu16 } else { ((r1 << 1u16) | (((x << 1u16) >> (k + 1u16)) & 1u16)) }) && s2 == (if ((r2 << 1u16) | ((x >> k) & 1u16)) >= 0x100u16 { ((r2 << 1u16) | ((x >> k) & 1u16)) ^ 0x11bu16 } else { ((r2 << 1u16) | ((x >> k) & 1u16)) }) ==> s1 == s2)
            by (bit_vector);
    }
}

/// `pmod (x * x) m` is `xTimes (pmod x m)`. The SPARK crate's
/// `Lemma_Pmod_Times_X`.
proof fn lemma_pmod_times_x(x: u16)
    requires
        x < 0x4000,
    ensures
        remainders::<15, u16>(x << 1u16, m(), 15) == xTimes(remainders::<15, u16>(x, m(), 15) as u8) as u16,
{
    lemma_pmod_shift(x, 14);
    lemma_remainders_step(x << 1u16, 15);
    lemma_remainders_byte(x, 15);
    let r = remainders::<15, u16>(x, m(), 15);
    lemma_xtimes(r as u8);
    let s = remainders::<15, u16>(x << 1u16, m(), 15);
    let xt = xTimes(r as u8);
    assert(r < 0x100 && x < 0x4000 && s == (if ((r << 1u16) | (((x << 1u16) >> 0u16) & 1u16)) >= 0x100u16 { ((r << 1u16) | (((x << 1u16) >> 0u16) & 1u16)) ^ 0x11bu16 } else { ((r << 1u16) | (((x << 1u16) >> 0u16) & 1u16)) }) && xt == (((r as u8) << 1u8) ^ (if ((r as u8) >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 })) ==> s == xt as u16) by (bit_vector);
}

/// The remainder of the product of `c` with the leading `n` bits of `b` is
/// the first `n` steps of GF28MultiplicationCorrect's fold over `b`. The
/// SPARK crate's `Lemma_Pmod_Pmult_Fold`.
proof fn lemma_pmod_pmult_fold(b: u8, c: u8, n: nat)
    requires
        n <= 8,
    ensures
        remainders::<15, u16>(products::<7, u16>(c as u16, b as u16, n), m(), 15)
            == foldl_take(mult_step(c), 0x00u8, bits(b), n as int) as u16,
    decreases n,
{
    let bb = b as u16;
    let cc = c as u16;
    if n == 0 {
        assert(0u16 >> 0u16 == 0u16) by (bit_vector);
        lemma_pmod_small(0, 15);
    } else {
        lemma_pmod_pmult_fold(b, c, (n - 1) as nat);
        let k = (8 - n) as u16;
        let p = products::<7, u16>(cc, bb, (n - 1) as nat);
        lemma_pmult_fold(cc, bb, (n - 1) as nat);
        assert((8 - (n - 1)) as nat as u16 == (k + 1) as u16);
        lemma_pm_step(cc, bb, k);
        lemma_double_16(p);
        assert((1 + 7 - 1 - (n - 1)) as nat as u16 == k);
        let set = (bb >> k) & 1u16 == 1u16;
        let t: u16 = if set { cc } else { 0u16 };
        assert(products::<7, u16>(cc, bb, n) == (p << 1u16) ^ t);
        lemma_pmod_xor(p << 1u16, t, 15);
        lemma_pmod_times_x(p);
        assert(t < 0x100 && t >> 0u16 == t) by {
            assert(cc < 0x100 ==> cc >> 0u16 == cc) by (bit_vector);
            assert(0u16 >> 0u16 == 0u16) by (bit_vector);
        }
        lemma_pmod_small(t, 15);
        // The bit of `b` that step `n` of the fold reads.
        let f = foldl_take(mult_step(c), 0x00u8, bits(b), (n - 1) as int);
        assert(bits(b)[n - 1] == set) by {
            assert((n - 1) / 8 == 0 && (n - 1) % 8 == n - 1);
            let k8 = (8 - 1 - (n - 1)) as nat as u8;
            assert(k8 as u16 == k);
            assert(k8 < 8 ==> (((b >> k8) & 1u8) == 1u8) == ((((b as u16) >> (k8 as u16)) & 1u16) == 1u16))
                by (bit_vector);
        }
        let xt = xTimes(f);
        assert(foldl_take(mult_step(c), 0x00u8, bits(b), n as int) == xt ^ (if set { c } else { 0x00u8 }));
        assert(remainders::<15, u16>(p, m(), 15) as u8 == f);
        if set {
            assert((xt as u16) ^ (c as u16) == (xt ^ c) as u16) by (bit_vector);
        } else {
            assert((xt as u16) ^ 0u16 == (xt ^ 0u8) as u16) by (bit_vector);
        }
    }
}

/// GF28MultiplicationCorrect's second conjunct: `b • c` is the fold over
/// the bits of `b`.
proof fn lemma_dot_foldl(b: u8, c: u8)
    ensures
        dot(b, c) == foldl(mult_step(c), 0x00u8, bits(b)),
{
    lemma_dot_cast(b, c);
    lemma_pmult_pm(b, c);
    lemma_pm_commutes(b as u16, c as u16);
    lemma_pmult_fold(c as u16, b as u16, 8);
    let bb = b as u16;
    assert(bb >> 0u16 == bb) by (bit_vector);
    lemma_pmod_pmult_fold(b, c, 8);
    assert(bits(b).len() == 8);
}

// ---------------------------------------------------------------------
// SBox

/// SBox.cry: `property SBoxCorrect = [ affine b | b <- [0..255] ] == SBox`
/// [FIPS-PUB-197 Section 5.1.1]: entry `b` of the S-box is `affine b`.
pub proof fn SBoxCorrect()
    ensures
        Seq::new(256, |b: int| affine(b as u8)) == SBox(),
{
    assert(SBox().len() == 256) by (compute_only);
    assert forall|b: int| 0 <= b < 256 implies affine(b as u8) == SBox()[b] by {
        lemma_sbox_entry(b as u8);
    }
    assert(Seq::new(256, |b: int| affine(b as u8)) =~= SBox());
}

/// Entries 0 to `n - 1` of `SBox` are undone by `InvSBox`.
pub open spec fn inverts_upto(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        InvSBox()[SBox()[n - 1] as int] == (n - 1) as u8 && inverts_upto((n - 1) as nat)
    }
}

proof fn lemma_inverts_upto(n: nat, b: u8)
    requires
        inverts_upto(n),
        (b as nat) < n,
    ensures
        InvSBox()[SBox()[b as int] as int] == b,
    decreases n,
{
    if (b as nat) < n - 1 {
        lemma_inverts_upto((n - 1) as nat, b);
    }
}

/// SBox.cry: `property SBoxInverts b = InvSBox @ (SBox @ b) == b`, by
/// evaluation of the 256 entries.
pub proof fn SBoxInverts(b: u8)
    ensures
        InvSBox()[SBox()[b as int] as int] == b,
{
    assert(inverts_upto(256)) by (compute_only);
    lemma_inverts_upto(256, b);
}

// ---------------------------------------------------------------------
// Cipher

/// Cipher.cry: `property SubBytesInverts bs = InvSubBytes (SubBytes bs) ==
/// bs`.
pub proof fn SubBytesInverts(bs: Block)
    requires
        bs.len() == 16,
    ensures
        InvSubBytes(SubBytes(bs)) == bs,
{
    assert forall|j: int| 0 <= j < 16 implies #[trigger] InvSubBytes(SubBytes(bs))[j] == bs[j] by {
        SBoxInverts(bs[j]);
    }
    assert(InvSubBytes(SubBytes(bs)) =~= bs);
}

/// Cipher.cry: `property ShiftRowsInverts xs = InvShiftRows (ShiftRows xs)
/// == xs`.
pub proof fn ShiftRowsInverts(xs: Block)
    requires
        xs.len() == 16,
    ensures
        InvShiftRows(ShiftRows(xs)) == xs,
{
    assert(InvShiftRows(ShiftRows(xs)) =~= xs);
}

/// Cipher.cry: `property MixColumnsStepInverts b = InvMixColumnsStep
/// (MixColumnsStep b) == b`. Each `•` by a constant is an `xTimes` sum
/// ([`lemma_dot_column`], [`lemma_dot_inverse_column`]), and `bit_vector`
/// checks the result from those sums: `aI` is `xTimes sI`, and `tJ_n` is
/// `xTimes` applied `n` times to `tJ`, byte `J` of `MixColumnsStep b`.
pub proof fn MixColumnsStepInverts(b: AESWord)
    requires
        b.len() == 4,
    ensures
        InvMixColumnsStep(MixColumnsStep(b)) == b,
{
    hide(xTimes);
    hide(dot);
    let s0 = b[0];
    let a0 = xTimes(s0);
    lemma_xtimes(s0);
    lemma_dot_column(s0);
    let s1 = b[1];
    let a1 = xTimes(s1);
    lemma_xtimes(s1);
    lemma_dot_column(s1);
    let s2 = b[2];
    let a2 = xTimes(s2);
    lemma_xtimes(s2);
    lemma_dot_column(s2);
    let s3 = b[3];
    let a3 = xTimes(s3);
    lemma_xtimes(s3);
    lemma_dot_column(s3);
    let t = MixColumnsStep(b);
    let t0 = t[0];
    let t0_1 = xTimes(t0);
    let t0_2 = xTimes(t0_1);
    let t0_3 = xTimes(t0_2);
    lemma_xtimes(t0);
    lemma_xtimes(t0_1);
    lemma_xtimes(t0_2);
    lemma_dot_inverse_column(t0);
    let t1 = t[1];
    let t1_1 = xTimes(t1);
    let t1_2 = xTimes(t1_1);
    let t1_3 = xTimes(t1_2);
    lemma_xtimes(t1);
    lemma_xtimes(t1_1);
    lemma_xtimes(t1_2);
    lemma_dot_inverse_column(t1);
    let t2 = t[2];
    let t2_1 = xTimes(t2);
    let t2_2 = xTimes(t2_1);
    let t2_3 = xTimes(t2_2);
    lemma_xtimes(t2);
    lemma_xtimes(t2_1);
    lemma_xtimes(t2_2);
    lemma_dot_inverse_column(t2);
    let t3 = t[3];
    let t3_1 = xTimes(t3);
    let t3_2 = xTimes(t3_1);
    let t3_3 = xTimes(t3_2);
    lemma_xtimes(t3);
    lemma_xtimes(t3_1);
    lemma_xtimes(t3_2);
    lemma_dot_inverse_column(t3);
    let o = InvMixColumnsStep(t);
    let o0 = o[0];
    let o1 = o[1];
    let o2 = o[2];
    let o3 = o[3];
    assert(a0 == ((s0 << 1u8) ^ (if (s0 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && a1 == ((s1 << 1u8) ^ (if (s1 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && a2 == ((s2 << 1u8) ^ (if (s2 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && a3 == ((s3 << 1u8) ^ (if (s3 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t0 == a0 ^ (s1 ^ a1) ^ s2 ^ s3
        && t1 == s0 ^ a1 ^ (s2 ^ a2) ^ s3
        && t2 == s0 ^ s1 ^ a2 ^ (s3 ^ a3)
        && t3 == (s0 ^ a0) ^ s1 ^ s2 ^ a3
        && t0_1 == ((t0 << 1u8) ^ (if (t0 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t0_2 == ((t0_1 << 1u8) ^ (if (t0_1 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t0_3 == ((t0_2 << 1u8) ^ (if (t0_2 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t1_1 == ((t1 << 1u8) ^ (if (t1 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t1_2 == ((t1_1 << 1u8) ^ (if (t1_1 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t1_3 == ((t1_2 << 1u8) ^ (if (t1_2 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t2_1 == ((t2 << 1u8) ^ (if (t2 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t2_2 == ((t2_1 << 1u8) ^ (if (t2_1 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t2_3 == ((t2_2 << 1u8) ^ (if (t2_2 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t3_1 == ((t3 << 1u8) ^ (if (t3 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t3_2 == ((t3_1 << 1u8) ^ (if (t3_1 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && t3_3 == ((t3_2 << 1u8) ^ (if (t3_2 >> 7u8) & 1u8 == 1u8 { 0x1bu8 } else { 0x00u8 }))
        && o0 == (t0_1 ^ t0_2 ^ t0_3) ^ (t1 ^ t1_1 ^ t1_3) ^ (t2 ^ t2_2 ^ t2_3) ^ (t3 ^ t3_3)
        && o1 == (t0 ^ t0_3) ^ (t1_1 ^ t1_2 ^ t1_3) ^ (t2 ^ t2_1 ^ t2_3) ^ (t3 ^ t3_2 ^ t3_3)
        && o2 == (t0 ^ t0_2 ^ t0_3) ^ (t1 ^ t1_3) ^ (t2_1 ^ t2_2 ^ t2_3) ^ (t3 ^ t3_1 ^ t3_3)
        && o3 == (t0 ^ t0_1 ^ t0_3) ^ (t1 ^ t1_2 ^ t1_3) ^ (t2 ^ t2_3) ^ (t3_1 ^ t3_2 ^ t3_3)
        ==> o0 == s0 && o1 == s1 && o2 == s2 && o3 == s3) by (bit_vector);
    assert(o =~= b);
}

/// A column of `MixColumns` or `InvMixColumns` is a word.
proof fn lemma_step_len(s: AESWord)
    ensures
        MixColumnsStep(s).len() == 4,
        InvMixColumnsStep(s).len() == 4,
{
    hide(dot);
}

/// Cipher.cry: `property MixColumnsInverts bs = InvMixColumns (MixColumns
/// bs) == bs`.
pub proof fn MixColumnsInverts(bs: Block)
    requires
        bs.len() == 16,
    ensures
        InvMixColumns(MixColumns(bs)) == bs,
{
    hide(MixColumnsStep);
    hide(InvMixColumnsStep);
    let cols = split(bs);
    let mixed = cols.map_values(|s: AESWord| MixColumnsStep(s));
    assert forall|j: int| 0 <= j < 4 implies #[trigger] InvMixColumnsStep(mixed[j]) == cols[j] by {
        MixColumnsStepInverts(cols[j]);
    }
    let mc = MixColumns(bs);
    assert forall|j: int| 0 <= j < 4 implies #[trigger] split(mc)[j] == mixed[j] by {
        lemma_step_len(cols[j]);
        assert forall|i: int| 0 <= i < 4 implies #[trigger] split(mc)[j][i] == mixed[j][i] by {
            assert((4 * j + i) / 4 == j && (4 * j + i) % 4 == i);
        }
        assert(split(mc)[j] =~= mixed[j]);
    }
    assert(split(mc) =~= mixed);
    let inv = split(mc).map_values(|s: AESWord| InvMixColumnsStep(s));
    assert forall|j: int| 0 <= j < 4 implies #[trigger] inv[j] == cols[j] by {}
    assert(inv =~= cols);
    assert forall|i: int| 0 <= i < 16 implies #[trigger] join(cols)[i] == bs[i] by {
        assert(4 * (i / 4) + i % 4 == i);
    }
    assert(join(cols) =~= bs);
}

/// Cipher.cry: `property AddRoundKeyInvolution bs w = AddRoundKey
/// (AddRoundKey bs w) w == bs`.
pub proof fn AddRoundKeyInvolution(bs: Block, w: Block)
    requires
        bs.len() == 16,
        w.len() == 16,
    ensures
        AddRoundKey(AddRoundKey(bs, w), w) == bs,
{
    assert forall|i: int| 0 <= i < 16 implies #[trigger] AddRoundKey(AddRoundKey(bs, w), w)[i] == bs[i] by {
        let (x, y) = (bs[i], w[i]);
        assert((x ^ y) ^ y == x) by (bit_vector);
    }
    assert(AddRoundKey(AddRoundKey(bs, w), w) =~= bs);
}

/// Cipher.cry: `property RoundInverts xs ki = InvRound' (Round xs ki) ki ==
/// xs`.
pub proof fn RoundInverts(xs: Block, ki: Block)
    requires
        xs.len() == 16,
        ki.len() == 16,
    ensures
        InvRound_prime(Round(xs, ki), ki) == xs,
{
    let s1 = ShiftRows(SubBytes(xs));
    let s2 = MixColumns(s1);
    AddRoundKeyInvolution(s2, ki);
    MixColumnsInverts(s1);
    ShiftRowsInverts(SubBytes(xs));
    SubBytesInverts(xs);
}

/// foldl `InvRound'` from `InvSubBytes (InvShiftRows z)` is `InvSubBytes
/// (InvShiftRows)` of foldl `InvRound` from `z`: `InvRound'` is `InvRound`
/// with `InvSubBytes` and `InvShiftRows` moved from its front to its back.
/// For the first `n` steps, by induction from the last step, as the
/// prelude's `foldl` recurses. The fold functions are the closures of
/// `InvCipher` and `InvCipher'`, which `f` and `g` are. The SPARK crate's
/// `Lemma_Equivalence_Take`.
proof fn lemma_equivalence_take(
    f: spec_fn(Block, Block) -> Block,
    g: spec_fn(Block, Block) -> Block,
    z: Block,
    xs: Seq<Block>,
    n: int,
)
    requires
        forall|a: Block, k: Block| #[trigger] f(a, k) == InvRound(a, k),
        forall|a: Block, k: Block| #[trigger] g(a, k) == InvRound_prime(a, k),
        0 <= n <= xs.len(),
    ensures
        foldl_take(g, InvSubBytes(InvShiftRows(z)), xs, n) == InvSubBytes(InvShiftRows(foldl_take(f, z, xs, n))),
    decreases n,
{
    if n > 0 {
        lemma_equivalence_take(f, g, z, xs, n - 1);
        let a = foldl_take(f, z, xs, n - 1);
        assert(g(InvSubBytes(InvShiftRows(a)), xs[n - 1]) == InvSubBytes(InvShiftRows(f(a, xs[n - 1]))));
    }
}

/// Cipher.cry: `property InvCipherEquivalence ws state = InvCipher`{k} ws
/// state == InvCipher'`{k} ws state`, for `{k} (Key k)` and
/// `ws : [Nr k + 1]Block`.
pub proof fn InvCipherEquivalence<const k: u32>(ws: Seq<Block>, state: Block)
    requires
        Key(k as nat),
        is_round_keys(k as nat, ws),
        state.len() == 16,
    ensures
        InvCipher::<k>(ws, state) == InvCipher_prime::<k>(ws, state),
{
    let Nr = Nr(k as nat) as int;
    let rev = reverse(ws.subrange(1, Nr));
    lemma_equivalence_take(
        |xs: Block, ki: Block| InvRound(xs, ki),
        |xs: Block, ki: Block| InvRound_prime(xs, ki),
        AddRoundKey(state, ws[Nr]),
        rev,
        rev.len() as int,
    );
}

/// The length of a fold of `Round`: a round's result is a block.
proof fn lemma_foldl_round_len(f: spec_fn(Block, Block) -> Block, z: Block, xs: Seq<Block>, n: int)
    requires
        forall|a: Block, k: Block| #[trigger] f(a, k) == Round(a, k),
        z.len() == 16,
    ensures
        foldl_take(f, z, xs, n).len() == 16,
{
}

/// The first `n` steps of foldl `InvRound'` over the reversed round keys
/// undo the last `n` rounds of foldl `Round`, by induction from the last
/// step, as the prelude's `foldl` recurses. The SPARK crate's
/// `Lemma_Inverts_Take`.
proof fn lemma_inverts_take(
    f: spec_fn(Block, Block) -> Block,
    g: spec_fn(Block, Block) -> Block,
    z: Block,
    xs: Seq<Block>,
    n: int,
)
    requires
        forall|a: Block, k: Block| #[trigger] f(a, k) == Round(a, k),
        forall|a: Block, k: Block| #[trigger] g(a, k) == InvRound_prime(a, k),
        z.len() == 16,
        forall|i: int| 0 <= i < xs.len() ==> (#[trigger] xs[i]).len() == 16,
        0 <= n <= xs.len(),
    ensures
        foldl_take(g, foldl(f, z, xs), reverse(xs), n) == foldl_take(f, z, xs, xs.len() - n),
    decreases n,
{
    if n > 0 {
        lemma_inverts_take(f, g, z, xs, n - 1);
        let l = xs.len() as int;
        let x = xs[l - n];
        let p = foldl_take(f, z, xs, l - n);
        assert(reverse(xs)[n - 1] == x);
        assert(foldl_take(f, z, xs, l - (n - 1)) == Round(p, x));
        lemma_foldl_round_len(f, z, xs, l - n);
        RoundInverts(p, x);
    }
}

/// Cipher.cry: `property CipherInverts' ws state = InvCipher'`{k} ws
/// (Cipher`{k} ws state) == state`, for `{k} (Key k)` and
/// `ws : [Nr k + 1]Block`. [`CipherInverts`] is proved from it.
pub proof fn CipherInverts_prime<const k: u32>(ws: Seq<Block>, state: Block)
    requires
        Key(k as nat),
        is_round_keys(k as nat, ws),
        state.len() == 16,
    ensures
        InvCipher_prime::<k>(ws, Cipher::<k>(ws, state)) == state,
{
    let Nr = Nr(k as nat) as int;
    let f = |xs: Block, ki: Block| Round(xs, ki);
    let g = |xs: Block, ki: Block| InvRound_prime(xs, ki);
    let mid = ws.subrange(1, Nr);
    let z = AddRoundKey(state, ws[0]);
    let fr = foldl(f, z, mid);
    let s1 = ShiftRows(SubBytes(fr));
    let c = Cipher::<k>(ws, state);
    assert(c == AddRoundKey(s1, ws[Nr]));
    assert(ws[Nr].len() == 16 && ws[0].len() == 16);
    AddRoundKeyInvolution(s1, ws[Nr]);
    lemma_foldl_round_len(f, z, mid, mid.len() as int);
    ShiftRowsInverts(SubBytes(fr));
    SubBytesInverts(fr);
    assert(InvSubBytes(InvShiftRows(AddRoundKey(c, ws[Nr]))) == fr);
    assert forall|i: int| 0 <= i < mid.len() implies (#[trigger] mid[i]).len() == 16 by {
        assert(mid[i] == ws[i + 1]);
    }
    lemma_inverts_take(f, g, z, mid, mid.len() as int);
    AddRoundKeyInvolution(state, ws[0]);
}

/// Cipher.cry: `property CipherInverts ws state = InvCipher`{k} ws
/// (Cipher`{k} ws state) == state`, for `{k} (Key k)` and
/// `ws : [Nr k + 1]Block`.
pub proof fn CipherInverts<const k: u32>(ws: Seq<Block>, state: Block)
    requires
        Key(k as nat),
        is_round_keys(k as nat, ws),
        state.len() == 16,
    ensures
        InvCipher::<k>(ws, Cipher::<k>(ws, state)) == state,
{
    InvCipherEquivalence::<k>(ws, Cipher::<k>(ws, state));
    CipherInverts_prime::<k>(ws, state);
}

// ---------------------------------------------------------------------
// Main

/// Cryptol's split at `[128] -> [16][8]` undoes its join at `[16][8] ->
/// [128]`. The SPARK crate's `Lemma_Split_Join_Block`.
pub proof fn lemma_split_join_block(b: Block)
    requires
        b.len() == 16,
    ensures
        split_block(join_block(b)) == b,
{
    let p = join_block(b);
    assert forall|i: int| 0 <= i < 16 implies #[trigger] split_block(p)[i] == b[i] by {
        assert forall|j: int| 0 <= j < 8 implies p[i * 8 + j] == #[trigger] crate::cryptol::words::bit::<u8>(b[i], j) by {
            assert((i * 8 + j) / 8 == i && (i * 8 + j) % 8 == j);
        }
        lemma_value_byte(p, i * 8, b[i]);
    }
    assert(split_block(p) =~= b);
}

/// Cryptol's join at `[16][8] -> [128]` undoes its split at `[128] ->
/// [16][8]`. The SPARK crate's `Lemma_Join_Split_Block`.
proof fn lemma_join_split_block(bs: Seq<bool>)
    requires
        bs.len() == 128,
    ensures
        join_block(split_block(bs)) == bs,
{
    let s = split_block(bs);
    assert forall|t: int| 0 <= t < 128 implies #[trigger] join_block(s)[t] == bs[t] by {
        let i = t / 8;
        let j = t % 8;
        assert(0 <= i < 16 && 0 <= j < 8 && i * 8 + j == t);
        lemma_value_bits(bs, i * 8);
    }
    assert(join_block(s) =~= bs);
}

/// Main.cry: `property EncryptInverts key in = AES`{k}.Decrypt key
/// (AES`{k}.Encrypt key in) == in`, for `{k} (Key k)`, `key : [k]` and
/// `in : [128]`. The Cryptol's `in` is `input`.
pub proof fn EncryptInverts<const k: u32>(key: Seq<bool>, input: Seq<bool>)
    requires
        Key(k as nat),
        key.len() == k,
        input.len() == 128,
    ensures
        AES::<k>::Decrypt(key, AES::<k>::Encrypt(key, input)) == input,
{
    let w = KeyExpansion::<k>(split_key::<k>(key));
    let p = split_block(input);
    let c = Cipher::<k>(w, p);
    assert(is_round_keys(k as nat, w));
    lemma_split_join_block(c);
    CipherInverts::<k>(w, p);
    lemma_join_split_block(input);
}

} // verus!
