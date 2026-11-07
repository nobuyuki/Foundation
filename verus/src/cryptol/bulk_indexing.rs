//! Cryptol's bulk index operator `(@@) : {n, k, ix, a} (Integral ix) =>
//! [n]a -> [k]ix -> [k]a` (Cryptol.cry:906), as the SPARK prelude's
//! `Bulk_Indexing`
//! (spark/src/cryptol/foundation_spark-cryptol-bulk_indexing.ads). AES
//! uses it on a block (ShiftRows, `bs @@ [0, 5, 10, ...]`) and on a table
//! indexed by bytes (SubBytes, `SBox @@ bs`).

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use super::Word;

verus! {

/// `xs @@ is`, by its Cryptol body `xs @@ is = [ xs @ i | i <- is ]`:
/// element `j` of the result is the element of `xs` at index `is @ j`.
/// Cryptol's `Integral ix` is a word type `I` here, as the indices AES
/// uses are words (the bytes of a block, and the literals of ShiftRows),
/// and an index is the word's value, [`Word::to_nat`]. `is` is a Rust
/// reserved word, so the index sequence is `ixs`, as in the SPARK prelude.
pub open spec fn bulk_index<A, I: Word>(xs: Seq<A>, ixs: Seq<I>) -> Seq<A>
    recommends
        forall|j: int| 0 <= j < ixs.len() ==> I::to_nat(#[trigger] ixs[j]) < xs.len(),
{
    Seq::new(ixs.len(), |j: int| xs[I::to_nat(ixs[j]) as int])
}

} // verus!
