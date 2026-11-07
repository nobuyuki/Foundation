//! Cryptol's `join` and `split` between words and bits, `[n][w]` and
//! `[n * w]` (Cryptol.cry:815 and :822, primitives documented as inverses),
//! as the SPARK prelude's `Join_Split`
//! (spark/src/cryptol/foundation_spark-cryptol-join_split.ads).

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use super::Word;
#[cfg(verus_only)]
use super::words::bit;

verus! {

/// `join xs` for `xs : [n][w]`: the words' bits in order, so bit `i` of the
/// result is bit `i % w` of word `i / w`.
pub open spec fn join<W: Word>(xs: Seq<W>) -> Seq<bool> {
    Seq::new(
        xs.len() * W::width(),
        |i: int| bit(xs[i / W::width() as int], i % W::width() as int),
    )
}

/// The `count` bits of `p` from `first`, read as a number most significant
/// bit first. At `count = w` it is a word `[w]` that `split` cuts from bits:
/// in Cryptol a word is its bits, so the conversion has no name there.
/// Stated by recursion on `count`, as in the SPARK prelude: the last bit
/// read is the least significant.
pub open spec fn value<W: Word>(p: Seq<bool>, first: int, count: nat) -> W
    recommends
        count <= W::width(),
        0 <= first,
        first + count <= p.len(),
    decreases count,
{
    if count == 0 {
        W::zero()
    } else {
        let v = value::<W>(p, first, (count - 1) as nat);
        W::add(W::add(v, v), if p[first + count - 1] { W::one() } else { W::zero() })
    }
}

/// Word `k` of ``split`{n, w} p``: the `w` bits of `p` from `k * w`.
pub open spec fn split_at<W: Word>(p: Seq<bool>, k: int) -> W
    recommends
        0 <= k,
        (k + 1) * W::width() <= p.len(),
{
    value::<W>(p, k * W::width(), W::width())
}

} // verus!
