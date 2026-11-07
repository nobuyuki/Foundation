//! Cryptol's type operators `/^` and `%^` (Cryptol.cry:135 and :141,
//! primitives), as the SPARK prelude's `Numeric`
//! (spark/src/cryptol/foundation_spark-cryptol-numeric.ads).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `a /^ b`: division rounding up.
pub open spec fn ceil_div(a: nat, b: nat) -> nat
    recommends
        b > 0,
{
    ((a + (b - 1)) / b as int) as nat
}

/// `a %^ b`: what to add to `a` to reach a multiple of `b`.
pub open spec fn ceil_mod(a: nat, b: nat) -> nat
    recommends
        b > 0,
{
    (ceil_div(a, b) * b - a) as nat
}

} // verus!
