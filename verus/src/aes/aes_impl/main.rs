//! The executable AES block cipher on bytes, the implementation of
//! algorithms/AES/Main.cry's ``AES`{k}.Encrypt`` and `Decrypt`
//! [FIPS-PUB-197 Section 5], as the SPARK crate's `AES.Impl.Main`
//! (spark/src/aes/foundation_spark-aes-impl-main.ads): the key schedule
//! ([`super::expand_key`]) of the key's words, then one block encrypted
//! ([`super::encrypt_block`]) or decrypted ([`super::decrypt_block`]).
//!
//! Main.cry's `Encrypt` and `Decrypt` take a key `[k]` and a block `[128]`
//! as bit sequences, which the spec layer ([`crate::aes::main`]) states
//! over `Seq<bool>`. The implementation stops at bytes: a key is its
//! `k / 8` bytes and a block its 16, and each postcondition says that the
//! bits of the result are the spec's `Encrypt` or `Decrypt` of the bits of
//! the key and the block, with Cryptol's `join` ([`join_key`],
//! [`join_block`]) between the two. This is a representation change, so
//! it is not part of the spec layer.
//!
//! Key sizes. As in [`super`], one implementation generic in the const
//! `k` serves k = 128, 192 and 256, with `Key k` and the key's length as
//! the precondition.
//!
//! Nothing executable here calls spec code: `join_key`, `join_block` and
//! the spec appear only in contracts, and the proof's lemmas
//! ([`crate::aes::main_lemmas`] and the spec layer's
//! [`lemma_split_join_block`]) only in proof blocks.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::join_split;
#[cfg(verus_only)]
use crate::aes::main::{AES, join_block, split_block, split_key};
#[cfg(verus_only)]
use crate::aes::main_lemmas::lemma_split_join_key;
#[cfg(verus_only)]
use crate::aes::properties::lemma_split_join_block;
#[cfg(verus_only)]
use crate::aes::types::{Key, Nk};
#[cfg(verus_only)]
use super::key_words;
use super::{AESWord, Block, decrypt_block, encrypt_block, expand_key};

verus! {

/// Cryptol's `join` at type `[k / 8][8] -> [k]`, the key's bits: bit `n` is
/// bit `n % 8` of byte `n / 8`, most significant first, as
/// [`join_block`] joins a block. The SPARK crate's `Join_Key`.
pub open spec fn join_key(key: Seq<u8>) -> Seq<bool> {
    join_split::join::<u8>(key)
}

/// The key's bytes as `Nk k` words, four bytes to a word: Main.cry's
/// `split (split key)` at `[k] -> [Nk k][4][8]`, on bytes. The words are
/// the first `Nk k` of the 8 of the largest key, as [`super::expand_key`]
/// reads them. The SPARK crate's `Key_Words_Of`.
pub fn key_words_of<const k: u32>(key: &[u8]) -> (ws: [AESWord; 8])
    requires
        Key(k as nat),
        key@.len() == k / 8,
    ensures
        forall|j: int, i: int| 0 <= j < Nk(k as nat) && 0 <= i < 4 ==> #[trigger] ws[j][i] == key@[4 * j + i],
{
    let nk: usize = (k / 32) as usize;
    let mut ws: [AESWord; 8] = [[0u8; 4]; 8];
    let mut j: usize = 0;
    while j < nk
        invariant
            Key(k as nat),
            nk == Nk(k as nat),
            nk <= 8,
            key@.len() == 4 * nk,
            j <= nk,
            forall|j2: int, i: int| 0 <= j2 < j && 0 <= i < 4 ==> #[trigger] ws[j2][i] == key@[4 * j2 + i],
        decreases nk - j,
    {
        ws[j] = [key[4 * j], key[4 * j + 1], key[4 * j + 2], key[4 * j + 3]];
        j += 1;
    }
    ws
}

/// AES encryption of one block [FIPS-PUB-197 Section 5.1]: `expand_key`
/// of the key's words, then `encrypt_block`. Proved equal, on the bits, to
/// Main.cry's ``AES`{k}.Encrypt``.
pub fn encrypt<const k: u32>(key: &[u8], input: Block) -> (r: Block)
    requires
        Key(k as nat),
        key@.len() == k / 8,
    ensures
        join_block(r@) == AES::<k>::Encrypt(join_key(key@), join_block(input@)),
{
    let ws = key_words_of::<k>(key);
    let w = expand_key::<k>(&ws);
    let mut state = input;
    encrypt_block::<k>(&w, &mut state);
    proof {
        lemma_split_join_key::<k>(key@);
        let kb = split_key::<k>(join_key(key@));
        assert forall|j: int| 0 <= j < Nk(k as nat) implies #[trigger] key_words::<k>(ws@)[j] =~= kb[j] by {
            assert(forall|i: int| 0 <= i < 4 ==> #[trigger] ws[j][i] == kb[j][i]);
        }
        assert(key_words::<k>(ws@) =~= kb);
        lemma_split_join_block(input@);
    }
    state
}

/// AES decryption of one block [FIPS-PUB-197 Section 5.3]: `expand_key`
/// of the key's words, then `decrypt_block`. Proved equal, on the bits, to
/// Main.cry's ``AES`{k}.Decrypt``.
pub fn decrypt<const k: u32>(key: &[u8], input: Block) -> (r: Block)
    requires
        Key(k as nat),
        key@.len() == k / 8,
    ensures
        join_block(r@) == AES::<k>::Decrypt(join_key(key@), join_block(input@)),
{
    let ws = key_words_of::<k>(key);
    let w = expand_key::<k>(&ws);
    let mut state = input;
    decrypt_block::<k>(&w, &mut state);
    proof {
        lemma_split_join_key::<k>(key@);
        let kb = split_key::<k>(join_key(key@));
        assert forall|j: int| 0 <= j < Nk(k as nat) implies #[trigger] key_words::<k>(ws@)[j] =~= kb[j] by {
            assert(forall|i: int| 0 <= i < 4 ==> #[trigger] ws[j][i] == kb[j][i]);
        }
        assert(key_words::<k>(ws@) =~= kb);
        lemma_split_join_block(input@);
    }
    state
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{decrypt, encrypt, key_words_of};
    use crate::aes::aes_impl::{decrypt_block, decrypt_block_prime, dot, encrypt_block, expand_key, x_times};

    /// Parse bytes written in hexadecimal.
    fn hex(s: &str) -> Vec<u8> {
        (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
    }

    fn block(s: &str) -> [u8; 16] {
        hex(s).try_into().unwrap()
    }

    /// Encrypt with `k`, check the ciphertext, and decrypt back with both
    /// decryptions.
    fn check<const K: u32>(key: &str, pt: &str, ct: &str) {
        let key = hex(key);
        let (pt, ct) = (block(pt), block(ct));
        assert_eq!(encrypt::<K>(&key, pt), ct);
        assert_eq!(decrypt::<K>(&key, ct), pt);
        let w = expand_key::<K>(&key_words_of::<K>(&key));
        let mut s = ct;
        decrypt_block_prime::<K>(&w, &mut s);
        assert_eq!(s, pt);
    }

    /// FIPS 197 Appendix B (the cipher example) and Appendix C (the example
    /// vectors for the three key sizes).
    #[test]
    fn fips_197_vectors() {
        check::<128>("2b7e151628aed2a6abf7158809cf4f3c", "3243f6a8885a308d313198a2e0370734", "3925841d02dc09fbdc118597196a0b32");
        check::<128>("000102030405060708090a0b0c0d0e0f", "00112233445566778899aabbccddeeff", "69c4e0d86a7b0430d8cdb78070b4c55a");
        check::<192>(
            "000102030405060708090a0b0c0d0e0f1011121314151617",
            "00112233445566778899aabbccddeeff",
            "dda97ca4864cdfe06eaf70a0ec0d7191",
        );
        check::<256>(
            "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
            "00112233445566778899aabbccddeeff",
            "8ea2b7ca516745bfeafc49904b496089",
        );
    }

    /// FIPS 197 Appendix A: the last word of each expanded key, and the
    /// first round key, which is the cipher key.
    #[test]
    fn fips_197_key_expansion() {
        fn last<const K: u32>(key: &str) -> [u8; 4] {
            let key = hex(key);
            let w = expand_key::<K>(&key_words_of::<K>(&key));
            assert_eq!(&w[0][..], &key[..16]);
            let nr = (K / 32 + 6) as usize;
            w[nr][12..16].try_into().unwrap()
        }
        assert_eq!(last::<128>("2b7e151628aed2a6abf7158809cf4f3c"), [0xb6, 0x63, 0x0c, 0xa6]);
        assert_eq!(last::<192>("8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b"), [0x01, 0x00, 0x22, 0x02]);
        assert_eq!(
            last::<256>("603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4"),
            [0x70, 0x6c, 0x63, 0x1e]
        );
    }

    /// `dot` against multiplication by `x_times` and addition, over all
    /// pairs of bytes.
    #[test]
    fn dot_all_bytes() {
        for b in 0..=255u8 {
            for c in 0..=255u8 {
                let (mut p, mut a) = (0u8, b);
                for i in 0..8 {
                    if (c >> i) & 1 == 1 {
                        p ^= a;
                    }
                    a = x_times(a);
                }
                assert_eq!(dot(b, c), p, "{b:#04x} • {c:#04x}");
            }
        }
    }

    /// Encrypting and decrypting blocks under keys made by a simple
    /// generator gets the blocks back, for the three key sizes.
    #[test]
    fn round_trips() {
        let mut x: u32 = 1;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            x as u8
        };
        for _ in 0..100 {
            let key: Vec<u8> = (0..32).map(|_| next()).collect();
            let pt: [u8; 16] = core::array::from_fn(|_| next());
            let w = expand_key::<256>(&key_words_of::<256>(&key));
            let mut s = pt;
            encrypt_block::<256>(&w, &mut s);
            let ct = s;
            decrypt_block::<256>(&w, &mut s);
            assert_eq!(s, pt);
            assert_eq!(decrypt::<128>(&key[..16], encrypt::<128>(&key[..16], pt)), pt);
            assert_eq!(decrypt::<192>(&key[..24], encrypt::<192>(&key[..24], pt)), pt);
            assert_eq!(encrypt::<256>(&key, pt), ct);
        }
    }
}
