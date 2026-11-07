//! Cryptol's `foldl` over an enumeration `[from ..< to]` (Cryptol.cry:1146,
//! RefMan BasicTypes.rst:169), as the SPARK prelude's `Enumeration_Folds`
//! (spark/src/cryptol/foundation_spark-cryptol-enumeration_folds.ads).
//!
//! The SPARK generic passes what the function closes over (SHA-2's block,
//! for `step3`) as an explicit first argument `E`, because Ada's generic
//! formal functions are not closures. Here `f` is a closure, as in the
//! Cryptol.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `foldl f z [from ..< to]`, recursing from the last element as
/// [`super::folds::foldl_take`] does: the fold up to `to` is `f` at
/// `to - 1` after the fold up to `to - 1`.
pub open spec fn foldl<A>(f: spec_fn(A, int) -> A, z: A, from: int, to: int) -> A
    decreases to - from,
{
    if to <= from {
        z
    } else {
        f(foldl(f, z, from, to - 1), to - 1)
    }
}

} // verus!
