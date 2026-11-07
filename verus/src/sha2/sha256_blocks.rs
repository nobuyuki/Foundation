//! Folding SHA-256's compression over the 64-byte blocks of a byte
//! sequence, for the streaming implementation ([`super::sha256_stream`]),
//! mirroring the SPARK crate's `SHA256_Blocks`
//! (spark/src/sha2/foundation_spark-sha2-sha256_blocks.ads). The byte-level
//! refinement ([`super::sha256_bytes`]) states SHA-256 as Main.cry's
//! `foldl step H0` (Main.cry:61) over the blocks that `parse_bytes` reads
//! from the whole padded message. A streaming hash never holds that
//! message: it compresses each block as soon as it has one, so it needs
//! the fold over any run of whole blocks of any byte sequence, starting at
//! any byte and from any hash value, and the facts that let such folds be
//! cut, glued and compared:
//!
//! * [`lemma_fold_split`]: folding `A + B` blocks is folding `A` blocks and
//!   then `B` more from the hash value reached (the fold-append lemma);
//! * [`lemma_fold_ext`]: folds over equal bytes from equal hash values are
//!   equal, wherever the bytes sit;
//! * [`lemma_foldl_parse`]: [`fold_blocks`] over a padded message is the
//!   `foldl_step` over `parse_bytes` that `hash_bytes` is stated with.
//!
//! The SPARK crate's `Lemma_Step_Ext` has no counterpart: `step` of equal
//! arguments is equal in Verus without a lemma. `Lemma_Block_Ext` and
//! `Lemma_Fold_Ext` remain, since they compare bytes at different
//! positions of different sequences. Nor is there a `Max_Blocks` or an
//! `Offset` type: positions are `int`, which does not overflow.
//!
//! Everything here is spec or proof. This is not part of the spec layer,
//! which mirrors the Cryptol: it is proof scaffolding for the
//! implementation.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use super::main::{foldl_step, parse, parse_block, step};
#[cfg(verus_only)]
use super::sha256::SHA256;
#[cfg(verus_only)]
use super::sha256_bytes::{bits_of, byte_bit, lemma_div_mod_8, lemma_word_of_bytes, parse_bytes, word_at};

verus! {

/// Whether `K` whole blocks of `M` start at byte `F`: bytes `F` to
/// `F + 64 * K - 1` are all in `M`.
pub open spec fn fits(M: Seq<u8>, F: int, K: nat) -> bool {
    0 <= F && F + 64 * K <= M.len()
}

/// The 64 bytes of `M` from `F` as a message block [FIPS-PUB-180-4 Section
/// 5.2.1]: word `J` is the big-endian word at byte `F + 4 * J`, as
/// `block_at` reads block `I` from byte `64 * I`.
pub open spec fn block_from(M: Seq<u8>, F: int) -> Seq<u32>
    recommends
        fits(M, F, 1),
{
    Seq::new(16, |J: int| word_at(M, F + 4 * J))
}

/// `foldl step H` (Main.cry:61) over the `K` blocks of `M` from byte `F`:
/// the first `K - 1` of them folded, then `step` on block `K - 1`, which
/// starts at byte `F + 64 * (K - 1)`.
pub open spec fn fold_blocks(H: Seq<u32>, M: Seq<u8>, F: int, K: nat) -> Seq<u32>
    recommends
        fits(M, F, K),
    decreases K,
{
    if K == 0 {
        H
    } else {
        step::<SHA256>(fold_blocks(H, M, F, (K - 1) as nat), block_from(M, F + 64 * (K - 1)))
    }
}

/// The blocks read from 64 equal bytes are equal, wherever the bytes sit
/// in their sequences.
pub proof fn lemma_block_ext(M1: Seq<u8>, F1: int, M2: Seq<u8>, F2: int)
    requires
        fits(M1, F1, 1),
        fits(M2, F2, 1),
        forall|i: int| 0 <= i < 64 ==> M1[F1 + i] == #[trigger] M2[F2 + i],
    ensures
        block_from(M1, F1) == block_from(M2, F2),
{
    assert forall|J: int| 0 <= J < 16 implies #[trigger] block_from(M1, F1)[J] == block_from(
        M2,
        F2,
    )[J] by {
        assert(M1[F1 + (4 * J)] == M2[F2 + (4 * J)]);
        assert(M1[F1 + (4 * J + 1)] == M2[F2 + (4 * J + 1)]);
        assert(M1[F1 + (4 * J + 2)] == M2[F2 + (4 * J + 2)]);
        assert(M1[F1 + (4 * J + 3)] == M2[F2 + (4 * J + 3)]);
    }
    assert(block_from(M1, F1) =~= block_from(M2, F2));
}

/// Folds over `K` blocks of equal bytes, from the same hash value, are
/// equal, wherever the bytes sit in their sequences. By induction on `K`,
/// with [`lemma_block_ext`] for each block.
pub proof fn lemma_fold_ext(H: Seq<u32>, M1: Seq<u8>, F1: int, M2: Seq<u8>, F2: int, K: nat)
    requires
        fits(M1, F1, K),
        fits(M2, F2, K),
        forall|i: int| 0 <= i < 64 * K ==> M1[F1 + i] == #[trigger] M2[F2 + i],
    ensures
        fold_blocks(H, M1, F1, K) == fold_blocks(H, M2, F2, K),
    decreases K,
{
    if K > 0 {
        let k1 = (K - 1) as nat;
        lemma_fold_ext(H, M1, F1, M2, F2, k1);
        assert forall|i: int| 0 <= i < 64 implies M1[(F1 + 64 * k1) + i] == #[trigger] M2[(F2 + 64
            * k1) + i] by {
            assert(M1[F1 + (64 * k1 + i)] == M2[F2 + (64 * k1 + i)]);
        }
        lemma_block_ext(M1, F1 + 64 * k1, M2, F2 + 64 * k1);
    }
}

/// The fold-append lemma: folding the first `A + B` blocks from `F` is
/// folding the first `A` and then the `B` after them, from the hash value
/// the first `A` reach. By induction on `B`: `B = 0` is the definition, and
/// each further block is one more `step` on both sides.
pub proof fn lemma_fold_split(H: Seq<u32>, M: Seq<u8>, F: int, A: nat, B: nat)
    requires
        fits(M, F, A + B),
    ensures
        fold_blocks(H, M, F, A + B) == fold_blocks(fold_blocks(H, M, F, A), M, F + 64 * A, B),
    decreases B,
{
    if B > 0 {
        lemma_fold_split(H, M, F, A, (B - 1) as nat);
        assert(F + 64 * (A + B - 1) == (F + 64 * A) + 64 * (B - 1));
    }
}

/// Folding `step` over the first `N` blocks of `parse_bytes(P, Nb)`, as
/// `hash_bytes` does, is [`fold_blocks`] over the first `N` blocks of
/// `P`'s bytes. By induction on `N`.
pub proof fn lemma_foldl_parse(H: Seq<u32>, P: Seq<u8>, Nb: nat, N: nat)
    requires
        P.len() == 64 * Nb,
        N <= Nb,
    ensures
        foldl_step::<SHA256>(H, parse_bytes(P, Nb), N as int) == fold_blocks(H, P, 0, N),
    decreases N,
{
    if N > 0 {
        lemma_foldl_parse(H, P, Nb, (N - 1) as nat);
        assert(parse_bytes(P, Nb)[N - 1] =~= block_from(P, 0 + 64 * (N - 1)));
    }
}

/// The 64 bytes of `M` from `F`, read as a block, are Preprocessing.cry's
/// ``parse`{32, 1}`` (Preprocessing.cry:47) of their bits: word `J` of the
/// block is the 32 bits that `split` cuts at `32 * J`. [`block_from`] is
/// `parse` one block at a time, on bytes.
pub proof fn lemma_block_parse(M: Seq<u8>, F: int)
    requires
        fits(M, F, 1),
    ensures
        block_from(M, F) == parse::<SHA256>(bits_of(M.subrange(F, F + 64)), 1)[0],
{
    let S = M.subrange(F, F + 64);
    let P = bits_of(S);
    assert forall|J: int| 0 <= J < 16 implies #[trigger] block_from(M, F)[J]
        == parse_block::<SHA256>(P, 0)[J] by {
        assert forall|k: int, t: int| 0 <= k < 4 && 0 <= t < 8 implies P[32 * J + 8 * k + t]
            == #[trigger] byte_bit(S[4 * J + k], t) by {
            lemma_div_mod_8(4 * J + k, t);
            assert(32 * J + 8 * k + t == 8 * (4 * J + k) + t);
        }
        lemma_word_of_bytes(P, 32 * J, S, 4 * J);
        assert(S[4 * J] == M[F + 4 * J]);
        assert(S[4 * J + 1] == M[F + 4 * J + 1]);
        assert(S[4 * J + 2] == M[F + 4 * J + 2]);
        assert(S[4 * J + 3] == M[F + 4 * J + 3]);
    }
    assert(block_from(M, F) =~= parse_block::<SHA256>(P, 0));
}

} // verus!
