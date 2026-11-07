//! The key schedule, mirroring algorithms/AES/KeyExpansion.cry
//! [FIPS-PUB-197 Section 5.2], as the SPARK crate's
//! `AES.Spec.KeyExpansion` and the `KeyExpansion` and `W` of its generic
//! `AES.Spec.AES_K` (spark/src/aes/foundation_spark-aes-spec-keyexpansion.ads,
//! spark/src/aes/foundation_spark-aes-spec-aes_k.ads).
//!
//! `KeyExpansion : {k} (Key k) => ...` is generic in the const `k`
//! ([`super::types`]), so it is here with the helpers that have no `{k}`.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use super::sbox::SBox;
#[cfg(verus_only)]
use super::types::{AESWord, Block, Key, Nk, Nr, join};

verus! {

/// Cryptol's `^` at type `AESWord`, as KeyExpansion.cry applies it to
/// words: the bytewise exclusive or.
pub open spec fn xor(a: AESWord, b: AESWord) -> AESWord
    recommends
        a.len() == 4,
        b.len() == 4,
{
    Seq::new(4, |i: int| a[i] ^ b[i])
}

/// KeyExpansion.cry: `Rcon : [11]AESWord` (KeyExpansion.cry:16), the round
/// constants [FIPS-PUB-197 Sections 2.1 and 5.2], entry for entry. Element
/// 0 is Cryptol's `undefined`, which is vstd's `arbitrary()`: a value of
/// which nothing is known. `KeyExpansion` reads only elements 1 to 10.
/// (The SPARK crate's table has no element 0 instead, so that a read of it
/// is a failed index check.)
pub open spec fn Rcon() -> Seq<AESWord> {
    seq![
        arbitrary(),
        seq![0x01u8, 0x00, 0x00, 0x00],
        seq![0x02u8, 0x00, 0x00, 0x00],
        seq![0x04u8, 0x00, 0x00, 0x00],
        seq![0x08u8, 0x00, 0x00, 0x00],
        seq![0x10u8, 0x00, 0x00, 0x00],
        seq![0x20u8, 0x00, 0x00, 0x00],
        seq![0x40u8, 0x00, 0x00, 0x00],
        seq![0x80u8, 0x00, 0x00, 0x00],
        seq![0x1bu8, 0x00, 0x00, 0x00],
        seq![0x36u8, 0x00, 0x00, 0x00],
    ]
}

/// KeyExpansion.cry: `RotWord [a0, a1, a2, a3] = [a1, a2, a3, a0]`
/// (KeyExpansion.cry:35), the cyclic permutation of a word [FIPS-PUB-197
/// Section 5.2].
pub open spec fn RotWord(a: AESWord) -> AESWord
    recommends
        a.len() == 4,
{
    seq![a[1], a[2], a[3], a[0]]
}

/// KeyExpansion.cry: `SubWord [a0, a1, a2, a3] = [SBox @ a0, SBox @ a1,
/// SBox @ a2, SBox @ a3]` (KeyExpansion.cry:42), the S-box applied to each
/// byte of a word [FIPS-PUB-197 Section 5.2].
pub open spec fn SubWord(a: AESWord) -> AESWord
    recommends
        a.len() == 4,
{
    seq![SBox()[a[0] as int], SBox()[a[1] as int], SBox()[a[2] as int], SBox()[a[3] as int]]
}

/// KeyExpansion.cry, in `KeyExpansion`'s `where`: the element `w @ i` of
/// the expanded key (KeyExpansion.cry:55), case for case: `key @ i` for
/// `i < Nk`; `w @ (i - Nk) ^ SubWord (RotWord (w @ (i - 1))) ^ Rcon @ (i /
/// Nk)` when `i % Nk == 0`; `w @ (i - Nk) ^ SubWord (w @ (i - 1))` when
/// `i % Nk == 4 /\ Nk > 6`; and `w @ (i - Nk) ^ w @ (i - 1)` otherwise
/// [FIPS-PUB-197 Section 5.2, Figure 11]. The sequence `w` is defined in
/// terms of itself; here it is a recursive function of the index `i`, and
/// of the `key` that the Cryptol closes over, whose `decreases` is `i`, as
/// in the SPARK crate: each case reads `w` at smaller indices only. That
/// needs `Nk > 0`, which `Key k` gives, hence its `when`.
pub open spec fn w<const k: u32>(key: Seq<AESWord>, i: int) -> AESWord
    recommends
        0 <= i < 4 * (Nr(k as nat) + 1),
    decreases i,
    when Key(k as nat) && 0 <= i
{
    let Nk = Nk(k as nat) as int;
    if i < Nk {
        key[i]
    } else if i % Nk == 0 {
        xor(xor(w::<k>(key, i - Nk), SubWord(RotWord(w::<k>(key, i - 1)))), Rcon()[i / Nk])
    } else if i % Nk == 4 && Nk > 6 {
        xor(w::<k>(key, i - Nk), SubWord(w::<k>(key, i - 1)))
    } else {
        xor(w::<k>(key, i - Nk), w::<k>(key, i - 1))
    }
}

/// KeyExpansion.cry: `KeyExpansion : {k} (Key k) => [Nk k]AESWord ->
/// [Nr k + 1]Block`, `KeyExpansion key = split (split (join (join w)))`
/// (KeyExpansion.cry:51) [FIPS-PUB-197 Section 5.2]. The `split` and
/// `join` regroup the `4 * (Nr k + 1)` words of `w` into `Nr k + 1` blocks
/// of four consecutive words: round key `r` is the [`join`] of
/// `w @ (4 * r)` to `w @ (4 * r + 3)`, in order, as in the SPARK crate.
/// NSA declares it `foreign`, with Rust behind it; this mirrors its
/// Cryptol body.
pub open spec fn KeyExpansion<const k: u32>(key: Seq<AESWord>) -> Seq<Block>
    recommends
        Key(k as nat),
        key.len() == Nk(k as nat),
{
    Seq::new(
        Nr(k as nat) + 1,
        |r: int| join(Seq::new(4, |j: int| w::<k>(key, 4 * r + j))),
    )
}

} // verus!
