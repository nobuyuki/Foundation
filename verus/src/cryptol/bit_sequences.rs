//! Cryptol's `zero` and numeric literals at bit sequences `[n]`
//! (Cryptol.cry:304, a primitive; RefMan BasicSyntax.rst:349), as the SPARK
//! prelude's `Bit_Sequences`
//! (spark/src/cryptol/foundation_spark-cryptol-bit_sequences.ads), and
//! Cryptol's `^` on `[n]`, which the SPARK crate writes as Ada's `xor` on
//! Boolean arrays.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `zero : [count]`: `count` bits, all 0.
pub open spec fn zero(count: nat) -> Seq<bool> {
    Seq::new(count, |i: int| false)
}

/// The literal `` `value : [width] ``: `value` in `width` bits, most
/// significant first. By recursion on the width: the last bit is
/// `value % 2`, and the bits before it are `value / 2` in `width - 1`
/// bits. Cryptol rejects a literal that does not fit its type; here a
/// `value` of `2 ^^ width` or more keeps its `width` low bits, and callers
/// must require that it fits.
pub open spec fn literal(value: nat, width: nat) -> Seq<bool>
    decreases width,
{
    if width == 0 {
        Seq::empty()
    } else {
        literal(value / 2, (width - 1) as nat).push(value % 2 == 1)
    }
}

/// `a ^ b` on `[n]` (a method of Cryptol's class `Logic`, a primitive):
/// bitwise exclusive or, so bit `i` of the result is 1 when exactly one of
/// bit `i` of `a` and bit `i` of `b` is. Cryptol requires the two to have
/// the same length; the result has `a`'s.
pub open spec fn xor(a: Seq<bool>, b: Seq<bool>) -> Seq<bool>
    recommends
        a.len() == b.len(),
{
    Seq::new(a.len(), |i: int| a[i] != b[i])
}

} // verus!
