//! Cryptol's `foldl` over a sequence (Cryptol.cry:1146, a primitive), as
//! the SPARK prelude's `Folds` (spark/src/cryptol/foundation_spark-cryptol-folds.ads).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// ``foldl f z (take`{n} xs)``: the left fold of `f` over the first `n`
/// elements of `xs`. Cryptol states `foldl` by its example
/// `foldl (+) 0 [1,2,3] = ((0 + 1) + 2) + 3`, which applies `f` last to
/// the last element; that is the recursion here, so the fold of `n + 1`
/// elements is, by definition, one `f` after the fold of `n`.
pub open spec fn foldl_take<A, B>(f: spec_fn(A, B) -> A, z: A, xs: Seq<B>, n: int) -> A
    recommends
        n <= xs.len(),
    decreases n,
{
    if n <= 0 {
        z
    } else {
        f(foldl_take(f, z, xs, n - 1), xs[n - 1])
    }
}

/// `foldl f z xs`: the left fold of `f` over all of `xs`.
pub open spec fn foldl<A, B>(f: spec_fn(A, B) -> A, z: A, xs: Seq<B>) -> A {
    foldl_take(f, z, xs, xs.len() as int)
}

} // verus!
