//! The byte-level refinement of SHA-256 [FIPS-PUB-180-4 Sections 5.1.1,
//! 5.2.1 and 6.2], mirroring the SPARK crate's `SHA256_Bytes`
//! (spark/src/sha2/foundation_spark-sha2-sha256_bytes.ads): messages and
//! digests as bytes, as every C library sees them, proved equal to the
//! SHA256 instance of the spec layer's bit-level `hash` (Main.cry:55). This
//! is a representation change, so it is not part of the spec layer, which
//! mirrors the Cryptol.
//!
//! A byte is read most significant bit first ([`bits_of`]), as Cryptol's
//! `join : [n][8] -> [8 * n]` does. The padding is the byte string FIPS
//! 180-4 describes for a whole number of bytes: 0x80, zero bytes, and the
//! bit length as 8 big-endian bytes ([`pad_bytes`]). Words are read from it
//! four bytes at a time, big-endian ([`parse_bytes`]). [`hash_bytes`] folds
//! the spec's `step` over those blocks from `H0` and writes the digest's
//! words out big-endian. [`lemma_hash_bytes`] proves
//! `bits_of(hash_bytes(M)) == hash::<SHA256>(bits_of(M))`.
//!
//! Everything here is spec or proof: the executable compression and its
//! streaming interface are [`super::sha256_stream`]'s. This module is what
//! that refines to, at the level of bytes and words, with no bit sequences
//! left in its statements.
//!
//! The padding lemma [`lemma_pad`] is stated for a message of any bit
//! length, not just a whole number of bytes, as in the SPARK crate.
//!
//! The SPARK crate's extensionality lemmas (`Lemma_W_Ext`,
//! `Lemma_Foldl_Step3_Ext`, `Lemma_Foldl_Step_Ext`) have no counterpart:
//! they are needed there because Ada's array `=` is not the provers'
//! logical equality, while Verus's `Seq` equality is (`=~=` proves it), and
//! spec functions of equal arguments are equal.
//!
//! Lengths and positions are `nat` and `int`, so the SPARK crate's
//! `Byte_Index` and its bounds have no counterpart beyond [`Max_Bytes`];
//! byte sequences are `Seq<u8>` indexed from 0, and the SPARK crate's
//! slices `M (F .. F + 63)` are `subrange`s.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_only)]
use crate::cryptol::{bit_sequences, join_split, numeric};
#[cfg(verus_only)]
use super::main::{N, bit, foldl_step, hash, join, k, max_length, pad, parse, parse_block};
#[cfg(verus_only)]
use super::preprocessing::H0_256;
#[cfg(verus_only)]
use super::sha256::SHA256;

verus! {

/// The bound on message lengths in bytes: Main's `max_length` (`2 ^^ 64`
/// bits at `w = 32`) divided by 8.
pub open spec fn Max_Bytes() -> nat {
    0x2000_0000_0000_0000
}

/// Bit `j` of a byte, Cryptol's `b @ j` on `[8]`: most significant bit
/// first.
pub open spec fn byte_bit(b: u8, j: int) -> bool
    recommends
        0 <= j < 8,
{
    (b >> ((7 - j) as u8)) & 1 == 1
}

/// The bits of a byte sequence, Cryptol's `join` on `[n][8]`: each byte's
/// bits in order, most significant first, so bit `i` is bit `i % 8` of
/// byte `i / 8`.
pub open spec fn bits_of(M: Seq<u8>) -> Seq<bool> {
    Seq::new(8 * M.len(), |i: int| byte_bit(M[i / 8], i % 8))
}

/// The number of 64-byte blocks in the padding of a message of `count`
/// bytes: the least `n` with `64 * n >= count + 9` (the message, the 0x80
/// byte and the 8-byte length). It is Main's `N(8 * count)`
/// ([`lemma_blocks`]).
pub open spec fn blocks(count: nat) -> nat {
    (count + 72) / 64
}

/// Byte `j` of `L` written as 8 bytes, big-endian: byte 0 is the most
/// significant.
pub open spec fn length_byte(L: u64, j: int) -> u8
    recommends
        0 <= j < 8,
{
    ((L >> ((56 - 8 * j) as u64)) & 0xff) as u8
}

/// Byte `i` of the padded message [FIPS-PUB-180-4 Section 5.1.1] for a
/// message `M` of `n` whole bytes: `M`, the byte 0x80 (a 1 bit and seven of
/// the zeros), zero bytes up to 8 short of a whole block, and the bit
/// length `8 * n` as 8 big-endian bytes.
pub open spec fn padded_byte(M: Seq<u8>, i: int) -> u8
    recommends
        M.len() < Max_Bytes(),
        0 <= i < 64 * blocks(M.len()),
{
    if i < M.len() {
        M[i]
    } else if i == M.len() {
        0x80
    } else if i < 64 * blocks(M.len()) - 8 {
        0
    } else {
        length_byte((8 * M.len()) as u64, i - (64 * blocks(M.len()) - 8))
    }
}

/// The padded message, byte by byte ([`padded_byte`]): Preprocessing.cry's
/// `pad` (Preprocessing.cry:14) for a whole number of bytes, proved equal
/// to `pad` on the bits by [`lemma_pad_bytes`]. It has `64 * blocks(n)`
/// bytes.
pub open spec fn pad_bytes(M: Seq<u8>) -> Seq<u8>
    recommends
        M.len() < Max_Bytes(),
{
    Seq::new(64 * blocks(M.len()), |i: int| padded_byte(M, i))
}

/// The four bytes of `P` from `F` read as a word, big-endian
/// [FIPS-PUB-180-4 Section 3.1]: `P[F]` is the most significant.
pub open spec fn word_at(P: Seq<u8>, F: int) -> u32
    recommends
        0 <= F,
        F + 4 <= P.len(),
{
    (0x100_0000 * P[F] + 0x1_0000 * P[F + 1] + 0x100 * P[F + 2] + P[F + 3]) as u32
}

/// Block `I` of a padded message as 16 big-endian words: word `J` is read
/// from byte `64 * I + 4 * J`.
pub open spec fn block_at(P: Seq<u8>, I: int) -> Seq<u32>
    recommends
        0 <= I,
        64 * (I + 1) <= P.len(),
{
    Seq::new(16, |J: int| word_at(P, 64 * I + 4 * J))
}

/// The padded message's `N` blocks [FIPS-PUB-180-4 Section 5.2.1], read as
/// words from bytes: Preprocessing.cry's `parse` (Preprocessing.cry:47),
/// proved equal to `parse` on the bits by [`lemma_parse_bytes`].
pub open spec fn parse_bytes(P: Seq<u8>, N: nat) -> Seq<Seq<u32>>
    recommends
        P.len() == 64 * N,
{
    Seq::new(N, |I: int| block_at(P, I))
}

/// Byte `j` of a word written as 4 bytes, big-endian [FIPS-PUB-180-4
/// Section 3.1]: byte 0 is the most significant.
pub open spec fn word_byte(x: u32, j: int) -> u8
    recommends
        0 <= j < 4,
{
    ((x >> ((24 - 8 * j) as u32)) & 0xff) as u8
}

/// A hash value written as 32 bytes, each word big-endian: Main.cry's
/// `take (join H)` (Main.cry:56) at `d = 256 = 8 * w`, as bytes.
pub open spec fn digest_bytes(H: Seq<u32>) -> Seq<u8>
    recommends
        H.len() == 8,
{
    Seq::new(32, |i: int| word_byte(H[i / 4], i % 4))
}

/// SHA-256 of a message of whole bytes, at the level of bytes and words
/// [FIPS-PUB-180-4 Section 6.2]: pad to bytes, read the blocks' words
/// big-endian, fold the spec's `step` over them from `H0`, and write the
/// result big-endian. [`lemma_hash_bytes`] proves it equal to
/// `hash::<SHA256>` on the message's bits.
pub open spec fn hash_bytes(M: Seq<u8>) -> Seq<u8>
    recommends
        M.len() < Max_Bytes(),
{
    digest_bytes(
        foldl_step::<SHA256>(
            H0_256(),
            parse_bytes(pad_bytes(M), blocks(M.len())),
            blocks(M.len()) as int,
        ),
    )
}

/// The length of a literal ``(`v : [w])`` is `w`.
pub proof fn lemma_literal_len(v: nat, w: nat)
    ensures
        bit_sequences::literal(v, w).len() == w,
    decreases w,
{
    if w > 0 {
        lemma_literal_len(v / 2, (w - 1) as nat);
    }
}

/// The literal ``(`v : [w])`` (Preprocessing.cry:23's ``(`l : [2 * w])``),
/// bit by bit: bit `i` of `v` in `w` bits is bit `w - 1 - i` of `v`,
/// counting from the least significant. By induction on `w`.
pub proof fn lemma_to_bits(v: u64, w: nat)
    requires
        w <= 64,
    ensures
        bit_sequences::literal(v as nat, w).len() == w,
        forall|i: int|
            0 <= i < w ==> #[trigger] bit_sequences::literal(v as nat, w)[i] == ((v >> ((w - 1
                - i) as u64)) & 1 == 1),
    decreases w,
{
    lemma_literal_len(v as nat, w);
    if w > 0 {
        let v2: u64 = v / 2;
        lemma_to_bits(v2, (w - 1) as nat);
        assert(v as nat / 2 == v2 as nat);
        assert((v % 2 == 1) == ((v >> 0u64) & 1 == 1)) by (bit_vector);
        assert(forall|s: u64| s < 63 ==> #[trigger] ((v / 2) >> s) == v >> ((s + 1) as u64))
            by (bit_vector);
        assert forall|i: int| 0 <= i < w implies #[trigger] bit_sequences::literal(
            v as nat,
            w,
        )[i] == ((v >> ((w - 1 - i) as u64)) & 1 == 1) by {
            if i < w - 1 {
                assert(((v2 >> ((w - 2 - i) as u64))) == v >> ((w - 1 - i) as u64));
            }
        }
    }
}

/// `a /^ b` and `a %^ b` (the prelude's `ceil_div`, `ceil_mod`) bound
/// `a` from above by less than one `b`.
pub proof fn lemma_ceil_div(a: nat, b: nat)
    requires
        b > 0,
    ensures
        a <= numeric::ceil_div(a, b) * b < a + b,
        numeric::ceil_mod(a, b) + a == numeric::ceil_div(a, b) * b,
{
    let x = (a + (b - 1)) as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, b as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(x, b as int);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(x, b as int);
    let q = x / b as int;
    let r = x % b as int;
    vstd::arithmetic::mul::lemma_mul_is_commutative(b as int, q);
    assert(numeric::ceil_div(a, b) == q);
    assert(q * b == x - r);
}

/// The padding of a message of any bit length `l` [FIPS-PUB-180-4 Section
/// 5.1.1], Preprocessing.cry's `pad` (Preprocessing.cry:14), bit by bit:
/// the padded message has `N(l)` blocks; its bits are `M`'s, then a 1 at
/// `l`, then 0s up to 64 bits short of the end, and then `l` as 64 bits,
/// most significant first. Stated for general `l`, not only `l = 8 * n`,
/// so that a trailing partial byte needs no new lemma about `pad`.
pub proof fn lemma_pad(M: Seq<bool>)
    requires
        M.len() < max_length::<SHA256>(),
    ensures
        M.len() < 0x1_0000_0000_0000_0000,
        pad::<SHA256>(M).len() == 512 * N::<SHA256>(M.len()),
        forall|i: int|
            0 <= i < pad::<SHA256>(M).len() ==> #[trigger] pad::<SHA256>(M)[i] == if i < M.len() {
                M[i]
            } else if i == M.len() {
                true
            } else if i < 512 * N::<SHA256>(M.len()) - 64 {
                false
            } else {
                ((M.len() as u64) >> ((512 * N::<SHA256>(M.len()) - 1 - i) as u64)) & 1 == 1
            },
{
    vstd::arithmetic::power2::lemma2_to64();
    let l = M.len();
    let L = l as u64;
    lemma_ceil_div(l + 1 + 64, 512);
    lemma_to_bits(L, 64);
    assert(L as nat == l);
    let kk = k::<SHA256>(l);
    assert(kk + l + 65 == 512 * N::<SHA256>(l));
    let p = pad::<SHA256>(M);
    assert(p == M + seq![true] + bit_sequences::zero(kk) + bit_sequences::literal(l, 64));
    assert forall|i: int| 0 <= i < p.len() implies #[trigger] p[i] == if i < l {
        M[i]
    } else if i == l {
        true
    } else if i < 512 * N::<SHA256>(l) - 64 {
        false
    } else {
        (L >> ((512 * N::<SHA256>(l) - 1 - i) as u64)) & 1 == 1
    } by {
        if i >= l + 1 + kk {
            let j = i - (l + 1 + kk);
            assert(bit_sequences::literal(L as nat, 64)[j] == ((L >> ((64 - 1 - j) as u64)) & 1 == 1));
        }
    }
}

/// `(8 * b + t) / 8 == b` and `(8 * b + t) % 8 == t`: the byte and the bit
/// of bit `8 * b + t`.
pub proof fn lemma_div_mod_8(b: int, t: int)
    requires
        0 <= b,
        0 <= t < 8,
    ensures
        (8 * b + t) / 8 == b,
        (8 * b + t) % 8 == t,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(8 * b + t, 8, b, t);
}

/// `blocks(n)` is Main's `N(8 * n)`: the byte-level and the bit-level
/// padding of a message of `n` bytes have the same number of blocks.
pub proof fn lemma_blocks(n: nat)
    ensures
        N::<SHA256>(8 * n) == blocks(n),
{
    let x = (n + 72) as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, 64);
    vstd::arithmetic::div_mod::lemma_mod_bound(x, 64);
    let q = x / 64;
    let r = x % 64;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((8 * n + 65 + 511) as int, 512, q, 8 * r);
}

/// Bit `t` of byte `j` of `L` written big-endian is bit `8 * j + t` of `L`
/// in 64 bits, most significant first.
pub proof fn lemma_length_bits(L: u64)
    ensures
        forall|j: int, t: int|
            0 <= j < 8 && 0 <= t < 8 ==> #[trigger] byte_bit(length_byte(L, j), t) == ((L >> ((63
                - 8 * j - t) as u64)) & 1 == 1),
{
    assert(forall|j: u64, t: u64|
        j < 8 && t < 8 ==> (((((L >> ((56 - 8 * j) as u64)) & 0xff) as u8) >> ((7 - t) as u8)) & 1
            == 1) == ((#[trigger] (L >> ((63 - 8 * j - t) as u64))) & 1 == 1)) by (bit_vector);
    assert forall|j: int, t: int| 0 <= j < 8 && 0 <= t < 8 implies #[trigger] byte_bit(
        length_byte(L, j),
        t,
    ) == ((L >> ((63 - 8 * j - t) as u64)) & 1 == 1) by {
        let jj = j as u64;
        let tt = t as u64;
        assert((((((L >> ((56 - 8 * jj) as u64)) & 0xff) as u8) >> ((7 - tt) as u8)) & 1 == 1)
            == ((L >> ((63 - 8 * jj - tt) as u64)) & 1 == 1));
    }
}

/// The byte 0x80: bit 0 is 1, bits 1 to 7 are 0; and a zero byte's bits
/// are 0.
pub proof fn lemma_byte_bits_0x80_0()
    ensures
        byte_bit(0x80, 0),
        forall|t: int| 1 <= t < 8 ==> !#[trigger] byte_bit(0x80, t),
        forall|t: int| 0 <= t < 8 ==> !#[trigger] byte_bit(0, t),
{
    assert(forall|t: u8| 1 <= t < 8 ==> #[trigger] ((0x80u8 >> ((7 - t) as u8)) & 1) != 1)
        by (bit_vector);
    assert(forall|t: u8| t < 8 ==> #[trigger] ((0u8 >> ((7 - t) as u8)) & 1) != 1)
        by (bit_vector);
    assert((0x80u8 >> 7u8) & 1 == 1) by (bit_vector);
    assert forall|t: int| 1 <= t < 8 implies !#[trigger] byte_bit(0x80, t) by {
        assert(((0x80u8 >> ((7 - (t as u8)) as u8)) & 1) != 1);
    }
    assert forall|t: int| 0 <= t < 8 implies !#[trigger] byte_bit(0, t) by {
        assert(((0u8 >> ((7 - (t as u8)) as u8)) & 1) != 1);
    }
}

/// The byte-level padding is the bit-level `pad` for `l = 8 * n`, byte by
/// byte: bit `t` of padded byte `b` is bit `8 * b + t` of `pad` on the
/// message's bits, and `N(8 * n) = blocks(n)`. Proved from [`lemma_pad`]
/// by cases on the part of the padding that byte `b` falls in.
pub proof fn lemma_pad_bytes_bits(M: Seq<u8>)
    requires
        M.len() < Max_Bytes(),
    ensures
        N::<SHA256>(8 * M.len()) == blocks(M.len()),
        bits_of(M).len() < max_length::<SHA256>(),
        pad::<SHA256>(bits_of(M)).len() == 8 * pad_bytes(M).len(),
        forall|b: int, t: int|
            0 <= b < pad_bytes(M).len() && 0 <= t < 8 ==> pad::<SHA256>(bits_of(M))[8 * b + t]
                == #[trigger] byte_bit(pad_bytes(M)[b], t),
{
    let n = M.len();
    let q = blocks(n);
    let bits = bits_of(M);
    let L = (8 * n) as u64;
    vstd::arithmetic::power2::lemma2_to64();
    lemma_blocks(n);
    lemma_pad(bits);
    lemma_length_bits(L);
    lemma_byte_bits_0x80_0();
    assert(n + 9 <= 64 * q) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod((n + 72) as int, 64);
        vstd::arithmetic::div_mod::lemma_mod_bound((n + 72) as int, 64);
    }
    let p = pad::<SHA256>(bits);
    assert forall|b: int, t: int| 0 <= b < pad_bytes(M).len() && 0 <= t < 8 implies p[8 * b + t]
        == #[trigger] byte_bit(pad_bytes(M)[b], t) by {
        let i = 8 * b + t;
        lemma_div_mod_8(b, t);
        if b < n {
        } else if b == n {
        } else if b < 64 * q - 8 {
        } else {
            let j = b - (64 * q - 8);
            assert(512 * q - 1 - i == 63 - 8 * j - t);
        }
    }
}

/// The byte-level padding is the bit-level `pad` for `l = 8 * n`: the bits
/// of `pad_bytes(M)` are `pad` of the bits of `M`, and both have
/// `blocks(n) = N(8 * n)` blocks.
pub proof fn lemma_pad_bytes(M: Seq<u8>)
    requires
        M.len() < Max_Bytes(),
    ensures
        N::<SHA256>(8 * M.len()) == blocks(M.len()),
        bits_of(M).len() < max_length::<SHA256>(),
        bits_of(pad_bytes(M)) == pad::<SHA256>(bits_of(M)),
{
    lemma_pad_bytes_bits(M);
    let pb = pad_bytes(M);
    let p = pad::<SHA256>(bits_of(M));
    assert forall|i: int| 0 <= i < p.len() implies #[trigger] bits_of(pb)[i] == p[i] by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 8);
        vstd::arithmetic::div_mod::lemma_mod_bound(i, 8);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(i, 8);
        assert(byte_bit(pb[i / 8], i % 8) == p[8 * (i / 8) + i % 8]);
    }
    assert(bits_of(pb) =~= p);
}

/// A byte is the sum of its bits, each at its weight: bit `t` (most
/// significant first) has weight `2 ^^ (7 - t)`.
pub proof fn lemma_byte_value(x: u8)
    ensures
        x as int == 128 * ((x >> 7u8) & 1) + 64 * ((x >> 6u8) & 1) + 32 * ((x >> 5u8) & 1) + 16 * ((
        x >> 4u8) & 1) + 8 * ((x >> 3u8) & 1) + 4 * ((x >> 2u8) & 1) + 2 * ((x >> 1u8) & 1) + ((x
            >> 0u8) & 1),
        forall|t: int| 0 <= t < 8 ==> #[trigger] byte_bit(x, t) == ((x >> ((7 - t) as u8)) & 1 == 1),
        forall|t: u8| t < 8 ==> #[trigger] ((x >> t) & 1) <= 1,
{
    assert(x as int == 128 * ((x >> 7u8) & 1) + 64 * ((x >> 6u8) & 1) + 32 * ((x >> 5u8) & 1) + 16
        * ((x >> 4u8) & 1) + 8 * ((x >> 3u8) & 1) + 4 * ((x >> 2u8) & 1) + 2 * ((x >> 1u8) & 1) + ((x
        >> 0u8) & 1)) by (bit_vector);
    assert(forall|t: u8| t < 8 ==> #[trigger] ((x >> t) & 1) <= 1) by (bit_vector);
}

/// One more bit read: `value` (the conversion in `parse`'s `split`) over
/// `c + 1` bits is twice the value over `c` bits plus the new bit, with no
/// wrapping, and the value over `c` bits is below `2 ^^ c`.
pub proof fn lemma_value_step(p: Seq<bool>, s: int, c: nat)
    requires
        c < 32,
    ensures
        (join_split::value::<u32>(p, s, c) as nat) < pow2(c),
        join_split::value::<u32>(p, s, c + 1) as int == 2 * join_split::value::<u32>(p, s, c) + if p[s
            + c] {
            1int
        } else {
            0int
        },
        (join_split::value::<u32>(p, s, c + 1) as nat) < pow2(c + 1),
    decreases c,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma_pow2_unfold(c + 1);
    if c == 0 {
        assert(join_split::value::<u32>(p, s, 0) == 0);
        vstd::arithmetic::power2::lemma_pow2_unfold(1);
        assert(pow2(0) == 1) by { vstd::arithmetic::power2::lemma2_to64(); }
    } else {
        lemma_value_step(p, s, (c - 1) as nat);
    }
    vstd::arithmetic::power2::lemma_pow2_strictly_increases(c, 32);
    let v = join_split::value::<u32>(p, s, c);
    assert(join_split::value::<u32>(p, s, c + 1) == vstd::wrapping::u32_specs::wrapping_add(
        vstd::wrapping::u32_specs::wrapping_add(v, v),
        if p[s + c] { 1u32 } else { 0u32 },
    ));
}

/// Reading 8 more bits that are the byte `x` appends `x` to the word read
/// so far: `value` over `a + 8` bits is the value over `a` bits, shifted
/// left 8, plus `x`.
pub proof fn lemma_word_of_byte(p: Seq<bool>, s: int, a: nat, x: u8)
    requires
        a <= 24,
        forall|t: int| 0 <= t < 8 ==> p[s + a + t] == #[trigger] byte_bit(x, t),
    ensures
        join_split::value::<u32>(p, s, a + 8) as int == 256 * join_split::value::<u32>(p, s, a) + x,
{
    lemma_byte_value(x);
    lemma_value_step(p, s, a);
    lemma_value_step(p, s, a + 1);
    lemma_value_step(p, s, a + 2);
    lemma_value_step(p, s, a + 3);
    lemma_value_step(p, s, a + 4);
    lemma_value_step(p, s, a + 5);
    lemma_value_step(p, s, a + 6);
    lemma_value_step(p, s, a + 7);
    assert(byte_bit(x, 0) == p[s + a + 0]);
    assert(byte_bit(x, 1) == p[s + a + 1]);
    assert(byte_bit(x, 2) == p[s + a + 2]);
    assert(byte_bit(x, 3) == p[s + a + 3]);
    assert(byte_bit(x, 4) == p[s + a + 4]);
    assert(byte_bit(x, 5) == p[s + a + 5]);
    assert(byte_bit(x, 6) == p[s + a + 6]);
    assert(byte_bit(x, 7) == p[s + a + 7]);
    assert(((x >> 7u8) & 1) <= 1);
    assert(((x >> 6u8) & 1) <= 1);
    assert(((x >> 5u8) & 1) <= 1);
    assert(((x >> 4u8) & 1) <= 1);
    assert(((x >> 3u8) & 1) <= 1);
    assert(((x >> 2u8) & 1) <= 1);
    assert(((x >> 1u8) & 1) <= 1);
    assert(((x >> 0u8) & 1) <= 1);
}

/// The 32 bits of `p` from `s`, read as `value` reads them, are the
/// big-endian word of the 4 bytes of `Q` from `F`, when those bits are
/// those bytes' bits.
pub proof fn lemma_word_of_bytes(p: Seq<bool>, s: int, Q: Seq<u8>, F: int)
    requires
        0 <= F,
        F + 4 <= Q.len(),
        forall|k: int, t: int|
            0 <= k < 4 && 0 <= t < 8 ==> p[s + 8 * k + t] == #[trigger] byte_bit(Q[F + k], t),
    ensures
        join_split::value::<u32>(p, s, 32) == word_at(Q, F),
{
    assert forall|t: int| 0 <= t < 8 implies p[s + 0 + t] == #[trigger] byte_bit(Q[F], t) by {
        assert(p[s + 8 * 0 + t] == byte_bit(Q[F + 0], t));
    }
    assert forall|t: int| 0 <= t < 8 implies p[s + 8 + t] == #[trigger] byte_bit(Q[F + 1], t) by {
        assert(p[s + 8 * 1 + t] == byte_bit(Q[F + 1], t));
    }
    assert forall|t: int| 0 <= t < 8 implies p[s + 16 + t] == #[trigger] byte_bit(Q[F + 2], t) by {
        assert(p[s + 8 * 2 + t] == byte_bit(Q[F + 2], t));
    }
    assert forall|t: int| 0 <= t < 8 implies p[s + 24 + t] == #[trigger] byte_bit(Q[F + 3], t) by {
        assert(p[s + 8 * 3 + t] == byte_bit(Q[F + 3], t));
    }
    assert(join_split::value::<u32>(p, s, 0) == 0);
    lemma_word_of_byte(p, s, 0, Q[F]);
    lemma_word_of_byte(p, s, 8, Q[F + 1]);
    lemma_word_of_byte(p, s, 16, Q[F + 2]);
    lemma_word_of_byte(p, s, 24, Q[F + 3]);
}

/// The byte-level parse of the byte-level padding is `parse` of `pad`
/// (Preprocessing.cry:47 and :14) on the message's bits: word `J` of block
/// `I`, read big-endian from bytes, is the 32 bits that `split` cuts at
/// `(16 * I + J) * 32`.
pub proof fn lemma_parse_bytes(M: Seq<u8>)
    requires
        M.len() < Max_Bytes(),
    ensures
        N::<SHA256>(8 * M.len()) == blocks(M.len()),
        parse_bytes(pad_bytes(M), blocks(M.len())) == parse::<SHA256>(
            pad::<SHA256>(bits_of(M)),
            blocks(M.len()),
        ),
{
    lemma_pad_bytes_bits(M);
    let q = blocks(M.len());
    let pb = pad_bytes(M);
    let p = pad::<SHA256>(bits_of(M));
    assert forall|I: int| 0 <= I < q implies #[trigger] block_at(pb, I) == parse_block::<SHA256>(
        p,
        I,
    ) by {
        assert forall|J: int| 0 <= J < 16 implies #[trigger] block_at(pb, I)[J]
            == parse_block::<SHA256>(p, I)[J] by {
            let F = 64 * I + 4 * J;
            let s = (16 * I + J) * 32;
            assert forall|k: int, t: int| 0 <= k < 4 && 0 <= t < 8 implies p[s + 8 * k + t]
                == #[trigger] byte_bit(pb[F + k], t) by {
                assert(s + 8 * k + t == 8 * (F + k) + t);
            }
            lemma_word_of_bytes(p, s, pb, F);
        }
        assert(block_at(pb, I) =~= parse_block::<SHA256>(p, I));
    }
    assert(parse_bytes(pb, q) =~= parse::<SHA256>(p, q));
}

/// Bit `j` of a word, as Main.cry's `join` reads it (Main's `bit`), is bit
/// `j % 8` of its big-endian byte `j / 8`, for `j = 8 * b + t`.
pub proof fn lemma_word_bits(x: u32)
    ensures
        forall|b: int, t: int|
            0 <= b < 4 && 0 <= t < 8 ==> #[trigger] bit::<SHA256>(x, 8 * b + t) == byte_bit(
                word_byte(x, b),
                t,
            ),
{
    assert(forall|b: u32, t: u32|
        b < 4 && t < 8 ==> ((#[trigger] (x >> ((31 - (8 * b + t)) as u32))) & 1 == 1) == ((((((x
            >> ((24 - 8 * b) as u32)) & 0xff) as u8) >> ((7 - t) as u8)) & 1) == 1)) by (bit_vector);
    assert forall|b: int, t: int| 0 <= b < 4 && 0 <= t < 8 implies #[trigger] bit::<SHA256>(
        x,
        8 * b + t,
    ) == byte_bit(word_byte(x, b), t) by {
        let bb = b as u32;
        let tt = t as u32;
        assert(((x >> ((31 - (8 * bb + tt)) as u32)) & 1 == 1) == ((((((x >> ((24 - 8 * bb) as u32))
            & 0xff) as u8) >> ((7 - tt) as u8)) & 1) == 1));
    }
}

/// The digest bytes are Main.cry's `take (join H)` (Main.cry:56) at
/// `d = 256`: bit `i` of the bytes is bit `i % 32` of word `i / 32`.
pub proof fn lemma_digest_bytes(H: Seq<u32>)
    requires
        H.len() == 8,
    ensures
        bits_of(digest_bytes(H)) == join::<SHA256>(H).take(256),
{
    let D = digest_bytes(H);
    let J = join::<SHA256>(H);
    assert forall|i: int| 0 <= i < 256 implies #[trigger] bits_of(D)[i] == J[i] by {
        let w = i / 32;
        let r = i % 32;
        let b = r / 8;
        let t = r % 8;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 32);
        vstd::arithmetic::div_mod::lemma_mod_bound(i, 32);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(i, 32);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r, 8);
        vstd::arithmetic::div_mod::lemma_mod_bound(r, 8);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(r, 8);
        assert(i == 8 * (4 * w + b) + t);
        lemma_div_mod_8(4 * w + b, t);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(4 * w + b, 4, w, b);
        lemma_word_bits(H[w]);
        assert(bit::<SHA256>(H[w], 8 * b + t) == byte_bit(word_byte(H[w], b), t));
    }
    assert(bits_of(D) =~= J.take(256));
}

/// The byte-level refinement: SHA-256 over bytes is Main.cry's `hash`
/// (Main.cry:55) over the message's bits, for every message of whole
/// bytes.
pub proof fn lemma_hash_bytes(M: Seq<u8>)
    requires
        M.len() < Max_Bytes(),
    ensures
        bits_of(hash_bytes(M)) == hash::<SHA256>(bits_of(M)),
{
    lemma_parse_bytes(M);
    let q = blocks(M.len());
    let H = foldl_step::<SHA256>(H0_256(), parse_bytes(pad_bytes(M), q), q as int);
    lemma_foldl_step_len(H0_256(), parse_bytes(pad_bytes(M), q), q as int);
    lemma_digest_bytes(H);
}

/// `foldl step H` (Main.cry:61) keeps a hash value's 8 words.
pub proof fn lemma_foldl_step_len(H: Seq<u32>, Ms: Seq<Seq<u32>>, n: int)
    requires
        H.len() == 8,
    ensures
        foldl_step::<SHA256>(H, Ms, n).len() == 8,
    decreases n,
{
    if n > 0 {
        lemma_foldl_step_len(H, Ms, n - 1);
    }
}

} // verus!
