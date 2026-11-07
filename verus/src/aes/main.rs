//! The top level of AES, mirroring algorithms/AES/Main.cry [FIPS-PUB-197
//! Section 5], as the SPARK crate's `AES.Spec.Main`, the `Split_Key`,
//! `Encrypt` and `Decrypt` of its generic `AES.Spec.AES_K`, and its
//! instances `AES128`, `AES192` and `AES256`
//! (spark/src/aes/foundation_spark-aes-spec-main.ads,
//! spark/src/aes/foundation_spark-aes-spec-aes_k.ads).
//!
//! Main.cry's `AES : {k} (Key k) => { Encrypt : ..., Decrypt : ... }` is a
//! record of two functions, polymorphic in `k`. Here it is the struct
//! [`AES`] with the const generic `k`, whose associated spec functions
//! are the fields, so ``AES`{k}.Encrypt`` is `AES::<k>::Encrypt`, and
//! Main.cry's `AES128 = AES`{128}` is the type alias [`AES128`], so
//! Cryptol's `AES128.Encrypt` is `AES128::Encrypt`.
//!
//! Main.cry works on bit sequences `[k]` and `[128]`, which are
//! `Seq<bool>`, element 0 the Cryptol's first (most significant) bit.
//! Cryptol's `split` and `join` between them and bytes are the prelude's
//! ([`join_split`]) at `[8]`.
//!
//! Main.cry's property `EncryptInverts` is stated and proved in
//! [`super::properties`].

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::join_split;
#[cfg(verus_only)]
use super::cipher::{Cipher, InvCipher};
#[cfg(verus_only)]
use super::key_expansion::KeyExpansion;
#[cfg(verus_only)]
use super::types::{AESWord, Block, Key, Nk};

verus! {

/// Main.cry: `split in`, Cryptol's `split` at `[128] -> [16][8] = Block`:
/// byte `i` is bits `8 * i` to `8 * i + 7`, the prelude's `split`.
pub open spec fn split_block(bs: Seq<bool>) -> Block
    recommends
        bs.len() == 128,
{
    Seq::new(16, |i: int| join_split::split_at::<u8>(bs, i))
}

/// Main.cry: `join (Cipher`{k} ...)`, Cryptol's `join` at `Block =
/// [16][8] -> [128]`, the inverse of [`split_block`]: the prelude's
/// `join`.
pub open spec fn join_block(b: Block) -> Seq<bool> {
    join_split::join::<u8>(b)
}

/// Main.cry: `split (split key)`, Cryptol's `split` twice at `[k] ->
/// [Nk k][32] -> [Nk k][4][8] = [Nk k]AESWord`. Byte `i` of word `j` is
/// byte `4 * j + i` of the prelude's `split` at `[k] -> [k / 8][8]`.
pub open spec fn split_key<const k: u32>(key: Seq<bool>) -> Seq<AESWord>
    recommends
        Key(k as nat),
        key.len() == k,
{
    Seq::new(
        Nk(k as nat),
        |j: int| Seq::new(4, |i: int| join_split::split_at::<u8>(key, 4 * j + i)),
    )
}

/// Main.cry: `AES : {k} (Key k) => { Encrypt : ([k] -> [128] -> [128]),
/// Decrypt : ([k] -> [128] -> [128]) }` (Main.cry:18), the record of the
/// AES block cipher functions [FIPS-PUB-197 Section 5]. Its fields are the
/// associated functions `Encrypt` and `Decrypt`.
pub struct AES<const k: u32>;

impl<const k: u32> AES<k> {
    /// Main.cry: `Encrypt key in = join (Cipher`{k} (KeyExpansion`{k}
    /// (split (split key))) (split in))` (Main.cry:22) [FIPS-PUB-197
    /// Section 5]. The Cryptol's `in` is `input`.
    pub open spec fn Encrypt(key: Seq<bool>, input: Seq<bool>) -> Seq<bool>
        recommends
            Key(k as nat),
            key.len() == k,
            input.len() == 128,
    {
        join_block(Cipher::<k>(KeyExpansion::<k>(split_key::<k>(key)), split_block(input)))
    }

    /// Main.cry: `Decrypt key in = join (InvCipher`{k} (KeyExpansion`{k}
    /// (split (split key))) (split in))` (Main.cry:23) [FIPS-PUB-197
    /// Section 5].
    pub open spec fn Decrypt(key: Seq<bool>, input: Seq<bool>) -> Seq<bool>
        recommends
            Key(k as nat),
            key.len() == k,
            input.len() == 128,
    {
        join_block(InvCipher::<k>(KeyExpansion::<k>(split_key::<k>(key)), split_block(input)))
    }
}

/// Main.cry: `AES128 = AES`{128}` (Main.cry:38), the AES-128 block cipher
/// [FIPS-PUB-197 Section 5].
pub type AES128 = AES<128>;

/// Main.cry: `AES192 = AES`{192}` (Main.cry:43), the AES-192 block cipher
/// [FIPS-PUB-197 Section 5].
pub type AES192 = AES<192>;

/// Main.cry: `AES256 = AES`{256}` (Main.cry:48), the AES-256 block cipher
/// [FIPS-PUB-197 Section 5].
pub type AES256 = AES<256>;

} // verus!
