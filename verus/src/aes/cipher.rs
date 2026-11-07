//! The round transformations and the ciphers of algorithms/AES/Cipher.cry
//! [FIPS-PUB-197 Sections 5.1 and 5.3], as the SPARK crate's
//! `AES.Spec.Cipher` and the `Cipher`, `InvCipher` and `InvCipher_Prime`
//! of its generic `AES.Spec.AES_K`
//! (spark/src/aes/foundation_spark-aes-spec-cipher.ads,
//! spark/src/aes/foundation_spark-aes-spec-aes_k.ads).
//!
//! Cryptol's built-ins are the prelude's ([`crate::cryptol`]): `@@` in
//! `SubBytes`, `InvSubBytes`, `ShiftRows` and `InvShiftRows` is
//! [`bulk_index`], `foldl` is [`foldl`] with the round function as a
//! closure, and `reverse` is [`reverse`]. Rust names cannot contain `'`,
//! so `InvRound'` and `InvCipher'` are `InvRound_prime` and
//! `InvCipher_prime`; `in` is a Rust keyword, so the ciphers' `in` is
//! `input`. The pattern `[w0] # ws # [wr]` is `ws[0]`, the middle
//! `ws.subrange(1, Nr)` and `ws[Nr]`.
//!
//! Cipher.cry's properties are stated and proved in
//! [`super::properties`].

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::bulk_indexing::bulk_index;
#[cfg(verus_only)]
use crate::cryptol::folds::foldl;
#[cfg(verus_only)]
use crate::cryptol::sequences::reverse;
#[cfg(verus_only)]
use super::gf28::dot;
#[cfg(verus_only)]
use super::sbox::{InvSBox, SBox};
#[cfg(verus_only)]
use super::types::{AESWord, Block, Key, Nr, join, split};

verus! {

/// Cipher.cry: `Round xs ki = AddRoundKey (MixColumns (ShiftRows (SubBytes
/// xs))) ki` (Cipher.cry:17). One round of encryption [FIPS-PUB-197
/// Section 5.1].
pub open spec fn Round(xs: Block, ki: Block) -> Block {
    AddRoundKey(MixColumns(ShiftRows(SubBytes(xs))), ki)
}

/// Cipher.cry: `Cipher : {k} (Key k) => [Nr k + 1]Block -> Block -> Block`
/// (Cipher.cry:24), AES encryption [FIPS-PUB-197 Section 5.1]:
/// `Cipher ([w0] # ws # [wr]) in = state_final`, where
/// `state_initial = AddRoundKey in w0`,
/// `state_rounds = foldl Round state_initial ws` and
/// `state_final = AddRoundKey (ShiftRows (SubBytes state_rounds)) wr`.
/// NSA declares it `foreign`, with Rust behind it; this mirrors its
/// Cryptol body.
pub open spec fn Cipher<const k: u32>(ws: Seq<Block>, input: Block) -> Block
    recommends
        Key(k as nat),
        ws.len() == Nr(k as nat) + 1,
{
    let Nr = Nr(k as nat) as int;
    let state_initial = AddRoundKey(input, ws[0]);
    let state_rounds = foldl(|xs: Block, ki: Block| Round(xs, ki), state_initial, ws.subrange(1, Nr));
    let state_final = AddRoundKey(ShiftRows(SubBytes(state_rounds)), ws[Nr]);
    state_final
}

/// Cipher.cry: `InvRound xs ki = InvMixColumns (AddRoundKey (InvSubBytes
/// (InvShiftRows xs)) ki)` (Cipher.cry:35). One round of decryption
/// [FIPS-PUB-197 Section 5.3].
pub open spec fn InvRound(xs: Block, ki: Block) -> Block {
    InvMixColumns(AddRoundKey(InvSubBytes(InvShiftRows(xs)), ki))
}

/// Cipher.cry: `InvRound' xs ki = InvSubBytes (InvShiftRows (InvMixColumns
/// (AddRoundKey xs ki)))` (Cipher.cry:42), the round that is a proper
/// inverse of `Round`.
pub open spec fn InvRound_prime(xs: Block, ki: Block) -> Block {
    InvSubBytes(InvShiftRows(InvMixColumns(AddRoundKey(xs, ki))))
}

/// Cipher.cry: `InvCipher : {k} (Key k) => [Nr k + 1]Block -> Block ->
/// Block` (Cipher.cry:56), AES decryption [FIPS-PUB-197 Section 5.3]:
/// `InvCipher ([w0] # ws # [wr]) in = state_final`, where
/// `state_initial = AddRoundKey in wr`,
/// `state_rounds = foldl InvRound state_initial (reverse ws)` and
/// `state_final = AddRoundKey (InvSubBytes (InvShiftRows state_rounds)) w0`.
/// NSA declares it `foreign`, with Rust behind it; this mirrors its
/// Cryptol body.
pub open spec fn InvCipher<const k: u32>(ws: Seq<Block>, input: Block) -> Block
    recommends
        Key(k as nat),
        ws.len() == Nr(k as nat) + 1,
{
    let Nr = Nr(k as nat) as int;
    let state_initial = AddRoundKey(input, ws[Nr]);
    let state_rounds = foldl(
        |xs: Block, ki: Block| InvRound(xs, ki),
        state_initial,
        reverse(ws.subrange(1, Nr)),
    );
    let state_final = AddRoundKey(InvSubBytes(InvShiftRows(state_rounds)), ws[0]);
    state_final
}

/// Cipher.cry: `InvCipher' : {k} (Key k) => [Nr k + 1]Block -> Block ->
/// Block` (Cipher.cry:69), the alternate decryption that is more obviously
/// the inverse of `Cipher` [FIPS-PUB-197 Section 5.3]:
/// `InvCipher' ([w0] # ws # [wr]) in = state_final`, where
/// `state_initial = InvSubBytes (InvShiftRows (AddRoundKey in wr))`,
/// `state_rounds = foldl InvRound' state_initial (reverse ws)` and
/// `state_final = AddRoundKey state_rounds w0`.
pub open spec fn InvCipher_prime<const k: u32>(ws: Seq<Block>, input: Block) -> Block
    recommends
        Key(k as nat),
        ws.len() == Nr(k as nat) + 1,
{
    let Nr = Nr(k as nat) as int;
    let state_initial = InvSubBytes(InvShiftRows(AddRoundKey(input, ws[Nr])));
    let state_rounds = foldl(
        |xs: Block, ki: Block| InvRound_prime(xs, ki),
        state_initial,
        reverse(ws.subrange(1, Nr)),
    );
    let state_final = AddRoundKey(state_rounds, ws[0]);
    state_final
}

/// Cipher.cry: `SubBytes bs = SBox @@ bs` (Cipher.cry:104) [FIPS-PUB-197
/// Section 5.1.1].
pub open spec fn SubBytes(bs: Block) -> Block {
    bulk_index(SBox(), bs)
}

/// Cipher.cry: `InvSubBytes bs = InvSBox @@ bs` (Cipher.cry:111)
/// [FIPS-PUB-197 Section 5.3.2].
pub open spec fn InvSubBytes(bs: Block) -> Block {
    bulk_index(InvSBox(), bs)
}

/// Cipher.cry: `ShiftRows bs = bs @@ [0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2,
/// 7, 12, 1, 6, 11]` (Cipher.cry:127), `ShiftRows` as a permutation of the
/// bytes of the block [FIPS-PUB-197 Section 5.1.2]. Cryptol infers the
/// type of the literal indices; here they are bytes.
pub open spec fn ShiftRows(bs: Block) -> Block {
    bulk_index(bs, seq![0u8, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11])
}

/// Cipher.cry: `InvShiftRows bs = bs @@ [0, 13, 10, 7, 4, 1, 14, 11, 8, 5,
/// 2, 15, 12, 9, 6, 3]` (Cipher.cry:140) [FIPS-PUB-197 Section 5.3.1].
pub open spec fn InvShiftRows(bs: Block) -> Block {
    bulk_index(bs, seq![0u8, 13, 10, 7, 4, 1, 14, 11, 8, 5, 2, 15, 12, 9, 6, 3])
}

/// Cipher.cry: `MixColumnsStep [s0, s1, s2, s3]` (Cipher.cry:157), one
/// column of `MixColumns` [FIPS-PUB-197 Section 5.1.3].
pub open spec fn MixColumnsStep(s: AESWord) -> AESWord
    recommends
        s.len() == 4,
{
    let (s0, s1, s2, s3) = (s[0], s[1], s[2], s[3]);
    seq![
        dot(0x02, s0) ^ dot(0x03, s1) ^ s2 ^ s3,
        s0 ^ dot(0x02, s1) ^ dot(0x03, s2) ^ s3,
        s0 ^ s1 ^ dot(0x02, s2) ^ dot(0x03, s3),
        dot(0x03, s0) ^ s1 ^ s2 ^ dot(0x02, s3),
    ]
}

/// Cipher.cry: `MixColumns bs = join (map MixColumnsStep (split bs))`
/// (Cipher.cry:169) [FIPS-PUB-197 Section 5.1.3].
pub open spec fn MixColumns(bs: Block) -> Block {
    join(split(bs).map_values(|s: AESWord| MixColumnsStep(s)))
}

/// Cipher.cry: `InvMixColumnsStep [s0, s1, s2, s3]` (Cipher.cry:175), one
/// column of `InvMixColumns` [FIPS-PUB-197 Section 5.3.3].
pub open spec fn InvMixColumnsStep(s: AESWord) -> AESWord
    recommends
        s.len() == 4,
{
    let (s0, s1, s2, s3) = (s[0], s[1], s[2], s[3]);
    seq![
        dot(0x0e, s0) ^ dot(0x0b, s1) ^ dot(0x0d, s2) ^ dot(0x09, s3),
        dot(0x09, s0) ^ dot(0x0e, s1) ^ dot(0x0b, s2) ^ dot(0x0d, s3),
        dot(0x0d, s0) ^ dot(0x09, s1) ^ dot(0x0e, s2) ^ dot(0x0b, s3),
        dot(0x0b, s0) ^ dot(0x0d, s1) ^ dot(0x09, s2) ^ dot(0x0e, s3),
    ]
}

/// Cipher.cry: `InvMixColumns bs = join (map InvMixColumnsStep (split
/// bs))` (Cipher.cry:187) [FIPS-PUB-197 Section 5.3.3].
pub open spec fn InvMixColumns(bs: Block) -> Block {
    join(split(bs).map_values(|s: AESWord| InvMixColumnsStep(s)))
}

/// Cipher.cry: `AddRoundKey bs w = bs ^ w` (Cipher.cry:208), Cryptol's `^`
/// at type `Block`, bytewise [FIPS-PUB-197 Section 5.1.4].
pub open spec fn AddRoundKey(bs: Block, w: Block) -> Block
    recommends
        bs.len() == 16,
        w.len() == 16,
{
    Seq::new(16, |i: int| bs[i] ^ w[i])
}

} // verus!
