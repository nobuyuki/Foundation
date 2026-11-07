//! Secure Hash Algorithm notation [FIPS-PUB-180-4 Section 3.2], mirroring
//! algorithms/SHA2/Notation.cry: the shift and rotate operations that
//! Functions.cry builds the SHA-2 logical functions from.
//!
//! Cryptol's type parameters `{n, w}` are a const generic `n` and the word
//! type `W` (whose width is `w`), so Cryptol's ``ROTR`{2} x`` on `[32]` is
//! `ROTR::<2, u32>(x)`. The constraint `n < w` is a `recommends`.
//!
//! Not mirrored, because SHA-256 does not use it: `ROTL` (SHA-1). The
//! Cryptol's examples and properties (`hexDigitIs4Bits` to `ROTRAsROTL`) are
//! statements about the notation, not functions to mirror.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::Word;

verus! {

/// The right shift operation, Cryptol's ``SHR x = x >> `n``
/// (Notation.cry:60, [FIPS-PUB-180-4 Section 3.2]).
pub open spec fn SHR<const n: u32, W: Word>(x: W) -> W
    recommends
        n < W::width(),
{
    W::shr(x, n as nat)
}

/// The rotate right (circular right shift) operation, Cryptol's
/// ``ROTR x = x >>> `n`` (Notation.cry:67, [FIPS-PUB-180-4 Section 3.2]).
/// Stated as FIPS defines it, and as Cryptol's `ROTRIsRightCircularShift`
/// (Notation.cry:107) proves it equal to `>>>`:
/// ``(x >> `n) || (x << `(w - n))``. The SPARK crate states it the same way.
pub open spec fn ROTR<const n: u32, W: Word>(x: W) -> W
    recommends
        n < W::width(),
{
    W::or(W::shr(x, n as nat), W::shl(x, (W::width() - n) as nat))
}

} // verus!

/// The executable `ROTR` and `SHR` on `[32]`. Verus spec functions do not
/// run, so where the SPARK crate's spec functions are executable (on
/// `Unsigned_32`, with no change of representation), here each has an
/// executable twin of the same name and body, proved equal to it.
pub mod exec {
    #[allow(unused_imports)]
    use vstd::prelude::*;

    verus! {

    /// [`super::ROTR`] on `[32]`.
    #[inline(always)]
    pub fn ROTR<const n: u32>(x: u32) -> (r: u32)
        requires
            0 < n < 32,
        ensures
            r == super::ROTR::<n, u32>(x),
    {
        (x >> n) | (x << (32 - n))
    }

    /// [`super::SHR`] on `[32]`.
    #[inline(always)]
    pub fn SHR<const n: u32>(x: u32) -> (r: u32)
        requires
            n < 32,
        ensures
            r == super::SHR::<n, u32>(x),
    {
        x >> n
    }

    } // verus!
}
