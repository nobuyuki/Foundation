//! Cryptol's `reverse` (Cryptol.cry:828, a primitive) and `repeat`
//! (Cryptol.cry:1215), as the SPARK prelude's `Sequences`
//! (spark/src/cryptol/foundation_spark-cryptol-sequences.ads).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `reverse xs`, which "reverses the elements in a sequence": element `i`
/// is element `n - 1 - i` of `xs`. The SPARK prelude names it `Reverse_Of`
/// because `reverse` is an Ada reserved word; it is not one in Rust.
pub open spec fn reverse<A>(xs: Seq<A>) -> Seq<A> {
    Seq::new(xs.len(), |i: int| xs[xs.len() - 1 - i])
}

/// `` repeat`{count} x ``: `count` copies of `x`, by its Cryptol body
/// `repeat x = [ x | _ <- zero : [n] ]`.
pub open spec fn repeat<A>(count: nat, x: A) -> Seq<A> {
    Seq::new(count, |i: int| x)
}

} // verus!
