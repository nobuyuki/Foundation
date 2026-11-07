//! The AES implementation layer [FIPS-PUB-197 Sections 5.1 to 5.3]:
//! executable AES on bytes, proved equal to the spec layer, as the SPARK
//! crate's `AES.Impl` (spark/src/aes/foundation_spark-aes-impl.ads). The
//! key schedule is expanded into round keys, and one block is encrypted or
//! decrypted in place, a round at a time, with loops.
//!
//! Every function's postcondition states equality with the spec-layer
//! function it implements. The arithmetic of `MixColumns` and
//! `InvMixColumns` is `xTimes` alone, proved against GF28.cry's `(•)` by
//! [`lemma_dot_column`] and [`lemma_dot_inverse_column`] (from the SPARK
//! crate's `Lemma_Dot`). The round loops are proved against Cipher.cry's
//! `foldl` with the prelude's `foldl_take` as the invariant: the fold of
//! one more round key is one more round, by definition.
//!
//! Key sizes. One implementation serves k = 128, 192 and 256: the
//! functions with a `{k}` in the spec are generic in the same const `k`
//! and require `Key k`, as the spec's are ([`super::types`]), so no code is
//! tripled and no dispatcher is needed (the SPARK crate passes the key size
//! as a run-time `K` and names the spec through `Spec.Dispatch`).
//!
//! Representation. A block is a [`Block`], `[u8; 16]`, and a word an
//! [`AESWord`], `[u8; 4]`, whose views are the spec's `Block` and
//! `AESWord` ([`types::Block`], [`types::AESWord`]). The key words and the round
//! keys are slices that hold at least `Nk k` words and `Nr k + 1` blocks,
//! and the spec sees their first `Nk k` and `Nr k + 1` ([`key_words`],
//! [`round_keys`]). [`expand_key`] returns the 15 blocks of the largest
//! key, `[[u8; 16]; 15]`, as NSA's Rust `key_expansion` does, of which the
//! first `Nr k + 1` are the round keys: Rust has no array whose length is
//! an expression in `k`, and as the spec reads only the prefix, a caller
//! passes that array whole, without cutting a slice of exactly `Nr k + 1`
//! blocks from it. (The SPARK crate's `Round_Keys` and `Key_Words` are
//! unconstrained arrays, whose lengths its preconditions fix.)
//!
//! What differs from the SPARK crate, and why:
//! - The spec's S-box tables and `Rcon` are spec functions, so the
//!   executable copies [`S_BOX`] and [`INV_S_BOX`] are proved equal to
//!   them as constants, and `rcon`'s cases are checked against `Rcon`.
//! - Verus's `==` on sequences is equality, so the SPARK crate's `*_Eq`
//!   lemmas (`Lemma_MixColumns_Eq`, `Lemma_Round_Eq`, ...) and the ghost
//!   `Expected` of its `Mix_Columns` are not needed, nor are its
//!   `Lemma_Foldl_*_Take_Eq` and `Lemma_Foldl_*_Snoc`: the loops' invariant
//!   is the fold over the first `r` round keys of the one sequence the
//!   spec folds over, which is the prelude's `foldl_take`.
//! - `MixColumns` and `InvMixColumns` handle the four columns with four
//!   calls rather than an aggregate over `Split`, as there is no executable
//!   `split`.
//! - Names are Rust's: `X_Times` is [`x_times`], `Sub_Byte` [`sub_byte`],
//!   and so on, and the spec's `xTimes`, `dot`, `SBox` keep the Cryptol
//!   names.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::folds::{foldl, foldl_take};
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
use super::gf28::{self, lemma_dot as lemma_dot_cast, lemma_remainders_byte, m, xTimes};
#[cfg(verus_only)]
use super::key_expansion::{KeyExpansion, Rcon, RotWord, SubWord, w, xor};
#[cfg(verus_only)]
use super::lemmas::{
    lemma_dot_column, lemma_dot_inverse_column, lemma_double_16, lemma_pm_step, lemma_pmult_fold,
    lemma_remainders_step, lemma_xtimes,
};
#[cfg(verus_only)]
use super::sbox::{InvSBox, SBox};
#[cfg(verus_only)]
use super::types::{self, Key, Nk, Nr, split};

pub mod main;

verus! {

/// A block, Types.cry's `Block = [16][8]`, as bytes: its view is the
/// spec's [`types::Block`].
pub type Block = [u8; 16];

/// A word, Types.cry's `AESWord = [4][8]`, as bytes: its view is the
/// spec's [`types::AESWord`].
pub type AESWord = [u8; 4];

/// The spec's key, `[Nk k]AESWord`, of the first `Nk k` words of `key`.
pub open spec fn key_words<const k: u32>(key: Seq<AESWord>) -> Seq<types::AESWord> {
    Seq::new(Nk(k as nat), |j: int| key[j]@)
}

/// The spec's round keys, `[Nr k + 1]Block`, of the first `Nr k + 1`
/// blocks of `ws`.
pub open spec fn round_keys<const k: u32>(ws: Seq<Block>) -> Seq<types::Block> {
    Seq::new(Nr(k as nat) + 1, |r: int| ws[r]@)
}

/// `Key k` is one of the three key sizes.
pub proof fn lemma_key_sizes(k: nat)
    requires
        Key(k),
    ensures
        k == 128 || k == 192 || k == 256,
        Nk(k) == 4 || Nk(k) == 6 || Nk(k) == 8,
        Nr(k) <= 14,
{
}

/// `b • 0x02`, by a shift and a conditional reduction.
pub fn x_times(b: u8) -> (r: u8)
    ensures
        r == xTimes(b),
{
    proof {
        lemma_xtimes(b);
        assert(((b >> 7u8) & 1u8 == 1u8) == (b >= 0x80u8)) by (bit_vector);
    }
    (b << 1u8) ^ (if b >= 0x80 { 0x1bu8 } else { 0x00u8 })
}

/// Multiplication in GF(2^8) of any two bytes, by a carry-less product and
/// a long division, each a loop over bits, as GF28.cry's `pmult` and
/// `pmod` compute them. The ciphers do not call it: they multiply by
/// `MixColumns`' constants with [`x_times`].
pub fn dot(b: u8, c: u8) -> (r: u8)
    ensures
        r == gf28::dot(b, c),
{
    let bb = b as u16;
    let cc = c as u16;
    let mut p: u16 = 0;
    let mut n: u16 = 0;
    while n < 8
        invariant
            n <= 8,
            bb == b as u16,
            cc == c as u16,
            p == products::<7, u16>(bb, cc, n as nat),
        decreases 8 - n,
    {
        proof {
            lemma_pmult_fold(bb, cc, n as nat);
            lemma_pm_step(bb, cc, (7 - n) as u16);
            assert((7 - n + 1) as u16 == (8 - n) as nat as u16);
            lemma_double_16(p);
            assert((1 + 7 - 1 - n) as nat as u16 == (7 - n) as u16);
        }
        p = (p << 1u16) ^ (if (cc >> (7 - n)) & 1u16 == 1u16 { bb } else { 0u16 });
        n += 1;
    }
    assert(p == pmult::<7, 7, u16>(bb, cc));
    let mut r: u16 = 0;
    let mut n: u16 = 0;
    while n < 15
        invariant
            n <= 15,
            r == remainders::<15, u16>(p, m(), n as nat),
        decreases 15 - n,
    {
        proof {
            lemma_remainders_step(p, (n + 1) as nat);
            assert((15 - (n + 1)) as u16 == (14 - n) as u16);
        }
        let t = (r << 1u16) | ((p >> (14 - n)) & 1u16);
        r = if t >= 0x100 { t ^ 0x11b } else { t };
        n += 1;
    }
    proof {
        lemma_remainders_byte(p, 15);
        lemma_dot_cast(b, c);
    }
    r as u8
}

/// The S-box as an executable table [FIPS-PUB-197 Table 4]. The spec's
/// `SBox` is a spec function, so the implementation has its own copy,
/// proved equal to it.
pub exec const S_BOX: [u8; 256]
    ensures
        S_BOX@ == SBox(),
{
    let t = [
        0x63u8, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
    ];
    proof {
        assert(t@ =~= SBox());
    }
    t
}

/// The inverse S-box as an executable table [FIPS-PUB-197 Table 6], the
/// implementation's copy of the spec's `InvSBox`.
pub exec const INV_S_BOX: [u8; 256]
    ensures
        INV_S_BOX@ == InvSBox(),
{
    let t = [
        0x52u8, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
        0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
        0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
        0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
        0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
        0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
        0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
        0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
        0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
        0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
        0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
        0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
        0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
        0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
        0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d,
    ];
    proof {
        assert(t@ =~= InvSBox());
    }
    t
}

/// The S-box applied to one byte, a lookup in [`S_BOX`]: SBox.cry's `SBox
/// @ b`.
pub fn sub_byte(b: u8) -> (r: u8)
    ensures
        r == SBox()[b as int],
{
    S_BOX[b as usize]
}

/// The inverse S-box applied to one byte, a lookup in [`INV_S_BOX`]:
/// SBox.cry's `InvSBox @ b`.
pub fn inv_sub_byte(b: u8) -> (r: u8)
    ensures
        r == InvSBox()[b as int],
{
    INV_S_BOX[b as usize]
}

/// The S-box applied to each byte of a word: KeyExpansion.cry's `SubWord
/// a`.
pub fn sub_word(a: AESWord) -> (r: AESWord)
    ensures
        r@ == SubWord(a@),
{
    let r = [sub_byte(a[0]), sub_byte(a[1]), sub_byte(a[2]), sub_byte(a[3])];
    assert(r@ =~= SubWord(a@));
    r
}

/// The cyclic permutation of a word: KeyExpansion.cry's `RotWord a`.
pub fn rot_word(a: AESWord) -> (r: AESWord)
    ensures
        r@ == RotWord(a@),
{
    let r = [a[1], a[2], a[3], a[0]];
    assert(r@ =~= RotWord(a@));
    r
}

/// The bytewise exclusive-or of two words, as KeyExpansion.cry uses `^` on
/// words.
pub fn xor_word(a: AESWord, b: AESWord) -> (r: AESWord)
    ensures
        r@ == xor(a@, b@),
{
    let r = [a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2], a[3] ^ b[3]];
    assert(r@ =~= xor(a@, b@));
    r
}

/// The round constant `i` [FIPS-PUB-197 Section 5.2], its first byte by a
/// case on `i` and the rest zero: KeyExpansion.cry's `Rcon @ i`, for the
/// indices 1 to 10 that the key schedule reads.
pub fn rcon(i: usize) -> (r: AESWord)
    requires
        1 <= i <= 10,
    ensures
        r@ == Rcon()[i as int],
{
    let b: u8 = match i {
        1 => 0x01,
        2 => 0x02,
        3 => 0x04,
        4 => 0x08,
        5 => 0x10,
        6 => 0x20,
        7 => 0x40,
        8 => 0x80,
        9 => 0x1b,
        _ => 0x36,
    };
    let r = [b, 0, 0, 0];
    assert(r@ =~= Rcon()[i as int]);
    r
}

/// The key schedule [FIPS-PUB-197 Section 5.2]: the `4 * (Nr k + 1)` words
/// of the expanded key, KeyExpansion.cry's `w`, computed in one loop, each
/// from the word `Nk k` before it and the word just before it, then
/// regrouped into `Nr k + 1` round keys. The key is the first `Nk k` words
/// of `key`, and the round keys are the first `Nr k + 1` blocks of the
/// result (the rest are zero).
pub fn expand_key<const k: u32>(key: &[AESWord]) -> (ws: [Block; 15])
    requires
        Key(k as nat),
        Nk(k as nat) <= key@.len(),
    ensures
        round_keys::<k>(ws@) == KeyExpansion::<k>(key_words::<k>(key@)),
{
    proof {
        lemma_key_sizes(k as nat);
    }
    let ghost kw = key_words::<k>(key@);
    let nk: usize = (k / 32) as usize;
    let nr: usize = nk + 6;
    let mut ew: [AESWord; 60] = [[0u8; 4]; 60];
    let mut i: usize = 0;
    while i < 4 * (nr + 1)
        invariant
            Key(k as nat),
            nk == Nk(k as nat),
            nr == Nr(k as nat),
            nk == 4 || nk == 6 || nk == 8,
            nk <= key@.len(),
            kw == key_words::<k>(key@),
            i <= 4 * (nr + 1),
            forall|j: int| 0 <= j < i ==> (#[trigger] ew[j])@ == w::<k>(kw, j),
        decreases 4 * (nr + 1) - i,
    {
        let temp: AESWord;
        if i < nk {
            temp = key[i];
        } else {
            assert(ew[i - nk]@ == w::<k>(kw, i - nk));
            assert(ew[i - 1]@ == w::<k>(kw, i - 1));
            if i % nk == 0 {
                assert(1 <= i / nk <= 10) by (nonlinear_arith)
                    requires
                        nk == 4 || nk == 6 || nk == 8,
                        nk <= i < 4 * (nk + 7),
                {
                    if nk == 4 {
                        assert(i / 4 <= 10);
                    } else if nk == 6 {
                        assert(i / 6 <= 10);
                    } else {
                        assert(i / 8 <= 10);
                    }
                }
                temp = xor_word(xor_word(ew[i - nk], sub_word(rot_word(ew[i - 1]))), rcon(i / nk));
            } else if i % nk == 4 && nk > 6 {
                temp = xor_word(ew[i - nk], sub_word(ew[i - 1]));
            } else {
                temp = xor_word(ew[i - nk], ew[i - 1]);
            }
        }
        assert(temp@ == w::<k>(kw, i as int));
        ew[i] = temp;
        i += 1;
    }

    let mut ws: [Block; 15] = [[0u8; 16]; 15];
    let mut r: usize = 0;
    while r < nr + 1
        invariant
            Key(k as nat),
            nr == Nr(k as nat),
            nr <= 14,
            r <= nr + 1,
            kw == key_words::<k>(key@),
            forall|j: int| 0 <= j < 4 * (nr + 1) ==> (#[trigger] ew[j])@ == w::<k>(kw, j),
            forall|q: int| 0 <= q < r ==> (#[trigger] ws[q])@ == KeyExpansion::<k>(kw)[q],
        decreases nr + 1 - r,
    {
        let a = ew[4 * r];
        let b = ew[4 * r + 1];
        let c = ew[4 * r + 2];
        let d = ew[4 * r + 3];
        ws[r] = [
            a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3],
            c[0], c[1], c[2], c[3], d[0], d[1], d[2], d[3],
        ];
        assert(ws[r as int]@ =~= KeyExpansion::<k>(kw)[r as int]) by {
            assert(a@ == w::<k>(kw, 4 * r as int));
            assert(b@ == w::<k>(kw, 4 * r + 1));
            assert(c@ == w::<k>(kw, 4 * r + 2));
            assert(d@ == w::<k>(kw, 4 * r + 3));
        }
        r += 1;
    }
    assert(round_keys::<k>(ws@) =~= KeyExpansion::<k>(kw));
    ws
}

/// `SubBytes` in place: the S-box applied to each byte of the state.
pub fn sub_bytes(state: &mut Block)
    ensures
        final(state)@ == SubBytes(old(state)@),
{
    let ghost s = state@;
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|j: int| 0 <= j < i ==> #[trigger] state[j] == SBox()[s[j] as int],
            forall|j: int| i <= j < 16 ==> #[trigger] state[j] == s[j],
        decreases 16 - i,
    {
        state[i] = sub_byte(state[i]);
        i += 1;
    }
    assert(state@ =~= SubBytes(s));
}

/// `InvSubBytes` in place: the inverse S-box applied to each byte.
pub fn inv_sub_bytes(state: &mut Block)
    ensures
        final(state)@ == InvSubBytes(old(state)@),
{
    let ghost s = state@;
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|j: int| 0 <= j < i ==> #[trigger] state[j] == InvSBox()[s[j] as int],
            forall|j: int| i <= j < 16 ==> #[trigger] state[j] == s[j],
        decreases 16 - i,
    {
        state[i] = inv_sub_byte(state[i]);
        i += 1;
    }
    assert(state@ =~= InvSubBytes(s));
}

/// `ShiftRows` in place: row `r` of the state rotated left by `r`.
pub fn shift_rows(state: &mut Block)
    ensures
        final(state)@ == ShiftRows(old(state)@),
{
    let s = *state;
    *state = [
        s[0], s[5], s[10], s[15], s[4], s[9], s[14], s[3],
        s[8], s[13], s[2], s[7], s[12], s[1], s[6], s[11],
    ];
    assert(state@ =~= ShiftRows(s@));
}

/// `InvShiftRows` in place: row `r` of the state rotated right by `r`.
pub fn inv_shift_rows(state: &mut Block)
    ensures
        final(state)@ == InvShiftRows(old(state)@),
{
    let s = *state;
    *state = [
        s[0], s[13], s[10], s[7], s[4], s[1], s[14], s[11],
        s[8], s[5], s[2], s[15], s[12], s[9], s[6], s[3],
    ];
    assert(state@ =~= InvShiftRows(s@));
}

/// One column of `MixColumns`, with [`x_times`] for the products by 0x02
/// and 0x03: Cipher.cry's `MixColumnsStep s`.
pub fn mix_column(s: AESWord) -> (r: AESWord)
    ensures
        r@ == MixColumnsStep(s@),
{
    let x = [x_times(s[0]), x_times(s[1]), x_times(s[2]), x_times(s[3])];
    proof {
        lemma_dot_column(s[0]);
        lemma_dot_column(s[1]);
        lemma_dot_column(s[2]);
        lemma_dot_column(s[3]);
    }
    let r = [
        x[0] ^ (s[1] ^ x[1]) ^ s[2] ^ s[3],
        s[0] ^ x[1] ^ (s[2] ^ x[2]) ^ s[3],
        s[0] ^ s[1] ^ x[2] ^ (s[3] ^ x[3]),
        (s[0] ^ x[0]) ^ s[1] ^ s[2] ^ x[3],
    ];
    assert(r@ =~= MixColumnsStep(s@));
    r
}

/// One byte of `InvMixColumnsStep`: `0x0e • a ^ 0x0b • b ^ 0x0d • c ^ 0x09
/// • d`, with [`x_times`] alone. [`inv_mix_column`] calls it once per row,
/// rotating the column, as the SPARK crate's `Inv_Mix_Byte`.
pub fn inv_mix_byte(a: u8, b: u8, c: u8, d: u8) -> (r: u8)
    ensures
        r == gf28::dot(0x0e, a) ^ gf28::dot(0x0b, b) ^ gf28::dot(0x0d, c) ^ gf28::dot(0x09, d),
{
    let a2 = x_times(a);
    let a4 = x_times(a2);
    let a8 = x_times(a4);
    let b2 = x_times(b);
    let b4 = x_times(b2);
    let b8 = x_times(b4);
    let c2 = x_times(c);
    let c4 = x_times(c2);
    let c8 = x_times(c4);
    let d2 = x_times(d);
    let d4 = x_times(d2);
    let d8 = x_times(d4);
    proof {
        lemma_dot_inverse_column(a);
        lemma_dot_inverse_column(b);
        lemma_dot_inverse_column(c);
        lemma_dot_inverse_column(d);
    }
    (a2 ^ a4 ^ a8) ^ (b ^ b2 ^ b8) ^ (c ^ c4 ^ c8) ^ (d ^ d8)
}

/// `^` on bytes is associative and commutative: four terms rotated.
pub proof fn lemma_xor_rotate(a: u8, b: u8, c: u8, d: u8)
    ensures
        b ^ c ^ d ^ a == a ^ b ^ c ^ d,
        c ^ d ^ a ^ b == a ^ b ^ c ^ d,
        d ^ a ^ b ^ c == a ^ b ^ c ^ d,
{
    assert(b ^ c ^ d ^ a == a ^ b ^ c ^ d && c ^ d ^ a ^ b == a ^ b ^ c ^ d && d ^ a ^ b ^ c == a ^ b ^ c ^ d)
        by (bit_vector);
}

/// One column of `InvMixColumns`: Cipher.cry's `InvMixColumnsStep s`.
pub fn inv_mix_column(s: AESWord) -> (r: AESWord)
    ensures
        r@ == InvMixColumnsStep(s@),
{
    hide(gf28::dot);
    let r = [
        inv_mix_byte(s[0], s[1], s[2], s[3]),
        inv_mix_byte(s[1], s[2], s[3], s[0]),
        inv_mix_byte(s[2], s[3], s[0], s[1]),
        inv_mix_byte(s[3], s[0], s[1], s[2]),
    ];
    // Rows 1 to 3 have their four products in rotated order: `^` commutes.
    proof {
        lemma_xor_rotate(gf28::dot(0x09, s[0]), gf28::dot(0x0e, s[1]), gf28::dot(0x0b, s[2]), gf28::dot(0x0d, s[3]));
        lemma_xor_rotate(gf28::dot(0x0d, s[0]), gf28::dot(0x09, s[1]), gf28::dot(0x0e, s[2]), gf28::dot(0x0b, s[3]));
        lemma_xor_rotate(gf28::dot(0x0b, s[0]), gf28::dot(0x0d, s[1]), gf28::dot(0x09, s[2]), gf28::dot(0x0e, s[3]));
        assert(r@ =~= InvMixColumnsStep(s@));
    }
    r
}

/// Column `j` of a block, as `split` cuts it.
fn column(s: &Block, j: usize) -> (r: AESWord)
    requires
        j < 4,
    ensures
        r@ == split(s@)[j as int],
{
    let r = [s[4 * j], s[4 * j + 1], s[4 * j + 2], s[4 * j + 3]];
    assert(r@ =~= split(s@)[j as int]);
    r
}

/// `MixColumns` in place, a column at a time.
pub fn mix_columns(state: &mut Block)
    ensures
        final(state)@ == MixColumns(old(state)@),
{
    hide(gf28::dot);
    let s = *state;
    let c0 = mix_column(column(&s, 0));
    let c1 = mix_column(column(&s, 1));
    let c2 = mix_column(column(&s, 2));
    let c3 = mix_column(column(&s, 3));
    *state = [
        c0[0], c0[1], c0[2], c0[3], c1[0], c1[1], c1[2], c1[3],
        c2[0], c2[1], c2[2], c2[3], c3[0], c3[1], c3[2], c3[3],
    ];
    assert(state@ =~= MixColumns(s@));
}

/// `InvMixColumns` in place, a column at a time.
pub fn inv_mix_columns(state: &mut Block)
    ensures
        final(state)@ == InvMixColumns(old(state)@),
{
    hide(gf28::dot);
    let s = *state;
    let c0 = inv_mix_column(column(&s, 0));
    let c1 = inv_mix_column(column(&s, 1));
    let c2 = inv_mix_column(column(&s, 2));
    let c3 = inv_mix_column(column(&s, 3));
    *state = [
        c0[0], c0[1], c0[2], c0[3], c1[0], c1[1], c1[2], c1[3],
        c2[0], c2[1], c2[2], c2[3], c3[0], c3[1], c3[2], c3[3],
    ];
    assert(state@ =~= InvMixColumns(s@));
}

/// `AddRoundKey` in place: the round key added to the state.
pub fn add_round_key(state: &mut Block, key: &Block)
    ensures
        final(state)@ == AddRoundKey(old(state)@, key@),
{
    let ghost s = state@;
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|j: int| 0 <= j < i ==> #[trigger] state[j] == s[j] ^ key[j],
            forall|j: int| i <= j < 16 ==> #[trigger] state[j] == s[j],
        decreases 16 - i,
    {
        state[i] = state[i] ^ key[i];
        i += 1;
    }
    assert(state@ =~= AddRoundKey(s, key@));
}

/// One round of encryption in place: Cipher.cry's `Round`.
pub fn round(state: &mut Block, key: &Block)
    ensures
        final(state)@ == Round(old(state)@, key@),
{
    sub_bytes(state);
    shift_rows(state);
    mix_columns(state);
    add_round_key(state, key);
}

/// One round of decryption in place: Cipher.cry's `InvRound`.
pub fn inv_round(state: &mut Block, key: &Block)
    ensures
        final(state)@ == InvRound(old(state)@, key@),
{
    inv_shift_rows(state);
    inv_sub_bytes(state);
    add_round_key(state, key);
    inv_mix_columns(state);
}

/// One round of the alternate decryption `InvCipher'` in place:
/// Cipher.cry's `InvRound'`.
pub fn inv_round_prime(state: &mut Block, key: &Block)
    ensures
        final(state)@ == InvRound_prime(old(state)@, key@),
{
    add_round_key(state, key);
    inv_mix_columns(state);
    inv_shift_rows(state);
    inv_sub_bytes(state);
}

/// AES encryption of one block in place [FIPS-PUB-197 Section 5.1]:
/// `AddRoundKey` by `w[0]`, `Nr k - 1` rounds by `w[1]` to `w[Nr k - 1]`,
/// and the final round without `MixColumns` by `w[Nr k]`. Cipher.cry's
/// ``Cipher`{k}`` of the round keys, the first `Nr k + 1` blocks of `w`.
pub fn encrypt_block<const k: u32>(w: &[Block], state: &mut Block)
    requires
        Key(k as nat),
        Nr(k as nat) + 1 <= w@.len(),
    ensures
        final(state)@ == Cipher::<k>(round_keys::<k>(w@), old(state)@),
{
    proof {
        lemma_key_sizes(k as nat);
    }
    let nr: usize = (k / 32 + 6) as usize;
    let ghost ws = round_keys::<k>(w@);
    let ghost f = |xs: types::Block, ki: types::Block| Round(xs, ki);
    let ghost mid = ws.subrange(1, nr as int);
    let ghost s = state@;
    add_round_key(state, &w[0]);
    let ghost s0 = state@;
    let mut r: usize = 1;
    while r < nr
        invariant
            nr == Nr(k as nat),
            nr + 1 <= w@.len(),
            1 <= r <= nr,
            ws == round_keys::<k>(w@),
            mid == ws.subrange(1, nr as int),
            forall|a: types::Block, b: types::Block| #[trigger] f(a, b) == Round(a, b),
            state@ == foldl_take(f, s0, mid, r - 1),
        decreases nr - r,
    {
        round(state, &w[r]);
        assert(mid[r - 1] == w@[r as int]@);
        r += 1;
    }
    sub_bytes(state);
    shift_rows(state);
    add_round_key(state, &w[nr]);
    assert(ws[0] == w@[0]@ && ws[nr as int] == w@[nr as int]@);
}

/// AES decryption of one block in place [FIPS-PUB-197 Section 5.3]:
/// `AddRoundKey` by `w[Nr k]`, `Nr k - 1` inverse rounds by `w[Nr k - 1]`
/// down to `w[1]`, and the final inverse round without `InvMixColumns` by
/// `w[0]`. Cipher.cry's ``InvCipher`{k}``.
pub fn decrypt_block<const k: u32>(w: &[Block], state: &mut Block)
    requires
        Key(k as nat),
        Nr(k as nat) + 1 <= w@.len(),
    ensures
        final(state)@ == InvCipher::<k>(round_keys::<k>(w@), old(state)@),
{
    proof {
        lemma_key_sizes(k as nat);
    }
    let nr: usize = (k / 32 + 6) as usize;
    let ghost ws = round_keys::<k>(w@);
    let ghost f = |xs: types::Block, ki: types::Block| InvRound(xs, ki);
    let ghost rk = reverse(ws.subrange(1, nr as int));
    add_round_key(state, &w[nr]);
    let ghost s0 = state@;
    let mut j: usize = 1;
    while j < nr
        invariant
            nr == Nr(k as nat),
            nr + 1 <= w@.len(),
            1 <= j <= nr,
            ws == round_keys::<k>(w@),
            rk == reverse(ws.subrange(1, nr as int)),
            forall|a: types::Block, b: types::Block| #[trigger] f(a, b) == InvRound(a, b),
            state@ == foldl_take(f, s0, rk, j - 1),
        decreases nr - j,
    {
        inv_round(state, &w[nr - j]);
        assert(rk[j - 1] == w@[nr - j]@);
        j += 1;
    }
    inv_shift_rows(state);
    inv_sub_bytes(state);
    add_round_key(state, &w[0]);
    assert(ws[0] == w@[0]@ && ws[nr as int] == w@[nr as int]@);
}

/// The alternate AES decryption `InvCipher'` of one block in place, the
/// rounds of [`encrypt_block`] undone in reverse order: Cipher.cry's
/// ``InvCipher'`{k}``.
pub fn decrypt_block_prime<const k: u32>(w: &[Block], state: &mut Block)
    requires
        Key(k as nat),
        Nr(k as nat) + 1 <= w@.len(),
    ensures
        final(state)@ == InvCipher_prime::<k>(round_keys::<k>(w@), old(state)@),
{
    proof {
        lemma_key_sizes(k as nat);
    }
    let nr: usize = (k / 32 + 6) as usize;
    let ghost ws = round_keys::<k>(w@);
    let ghost f = |xs: types::Block, ki: types::Block| InvRound_prime(xs, ki);
    let ghost rk = reverse(ws.subrange(1, nr as int));
    add_round_key(state, &w[nr]);
    inv_shift_rows(state);
    inv_sub_bytes(state);
    let ghost s0 = state@;
    let mut j: usize = 1;
    while j < nr
        invariant
            nr == Nr(k as nat),
            nr + 1 <= w@.len(),
            1 <= j <= nr,
            ws == round_keys::<k>(w@),
            rk == reverse(ws.subrange(1, nr as int)),
            forall|a: types::Block, b: types::Block| #[trigger] f(a, b) == InvRound_prime(a, b),
            state@ == foldl_take(f, s0, rk, j - 1),
        decreases nr - j,
    {
        inv_round_prime(state, &w[nr - j]);
        assert(rk[j - 1] == w@[nr - j]@);
        j += 1;
    }
    add_round_key(state, &w[0]);
    assert(ws[0] == w@[0]@ && ws[nr as int] == w@[nr as int]@);
}

} // verus!
