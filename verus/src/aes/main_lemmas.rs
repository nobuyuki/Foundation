//! Lemmas that [`super::aes_impl::main`]'s `encrypt` and `decrypt` are
//! proved with, as the SPARK crate's `AES.Main_Lemmas`
//! (spark/src/aes/foundation_spark-aes-main_lemmas.ads): the bytes-to-bits
//! layer between the implementation and Main.cry's `Encrypt` and
//! `Decrypt`. It is not in the Cryptol: it states a property that the
//! Cryptol evaluates and Verus has to prove.
//!
//! Only `Lemma_Split_Join_Key` has a counterpart. The SPARK crate's other
//! lemmas here (`Lemma_W_Eq`, `Lemma_KeyExpansion_Eq`, `Lemma_Round_Key_Eq`,
//! `Lemma_Foldl_Round_Eq`, `Lemma_Cipher_Eq`, `Lemma_InvCipher_Eq`) state
//! that the spec's functions map equal arrays to equal results, because
//! Ada's `=` on arrays is not the provers' equality; Verus's `==` on
//! sequences is, so they are not needed.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::join_split;
#[cfg(verus_only)]
use crate::cryptol::words::bit;
#[cfg(verus_only)]
use super::aes_impl::main::join_key;
#[cfg(verus_only)]
use super::lemmas::lemma_value_byte;
#[cfg(verus_only)]
use super::main::split_key;
#[cfg(verus_only)]
use super::types::{Key, Nk};

verus! {

/// Cryptol's `split` at `[8 * n] -> [n][8]` undoes its `join` at `[n][8]
/// -> [8 * n]`, byte by byte: byte `t` of the bits of `bs` is `bs @ t`.
pub proof fn lemma_split_at_join(bs: Seq<u8>, t: int)
    requires
        0 <= t < bs.len(),
    ensures
        join_split::split_at::<u8>(join_split::join::<u8>(bs), t) == bs[t],
{
    let p = join_split::join::<u8>(bs);
    assert forall|j: int| 0 <= j < 8 implies p[t * 8 + j] == #[trigger] bit::<u8>(bs[t], j) by {
        assert((t * 8 + j) / 8 == t && (t * 8 + j) % 8 == j);
    }
    lemma_value_byte(p, t * 8, bs[t]);
}

/// Main.cry's `split (split key)` of the key's bits is the key's bytes,
/// four to a word: Cryptol's `split` at `[k] -> [Nk k][4][8]` undoes its
/// `join` at `[k / 8][8] -> [k]`. The SPARK crate's
/// `Lemma_Split_Join_Key`.
pub proof fn lemma_split_join_key<const k: u32>(key: Seq<u8>)
    requires
        Key(k as nat),
        key.len() == k / 8,
    ensures
        join_key(key).len() == k,
        forall|j: int, i: int| 0 <= j < Nk(k as nat) && 0 <= i < 4 ==>
            #[trigger] split_key::<k>(join_key(key))[j][i] == key[4 * j + i],
{
    assert forall|j: int, i: int| 0 <= j < Nk(k as nat) && 0 <= i < 4 implies
        #[trigger] split_key::<k>(join_key(key))[j][i] == key[4 * j + i] by {
        lemma_split_at_join(key, 4 * j + i);
    }
}

} // verus!
