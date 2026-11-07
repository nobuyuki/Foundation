//! The Secure Hash Algorithm functions and constants [FIPS-PUB-180-4
//! Section 4], mirroring algorithms/SHA2/Functions.cry for SHA-256: the
//! logical functions `Ch` and `Maj`, the SHA-224/256 functions
//! `SIGMA_256_0/1` and `sigma_256_0/1` [FIPS-PUB-180-4 Section 4.1.2], and
//! the constants `K_256` [FIPS-PUB-180-4 Section 4.2.2].
//!
//! `Ch` and `Maj` are polymorphic in the Cryptol, so they are generic over
//! the word type here. Rust identifiers are case-sensitive, so the
//! lower-case `sigma_256_0/1` keep their Cryptol names (the SPARK crate's
//! are `Small_Sigma_256_0/1`).
//!
//! Not mirrored, because SHA-256 does not use them: `Parity`, the SHA-1
//! sequences `f` and `K_SHA1`, and the SHA-384/512 functions and `K_512`.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::Word;
#[cfg(verus_only)]
use super::notation::{ROTR, SHR};

verus! {

/// The choose function, Cryptol's `Ch (x, y, z) = (x && y) ^ (~x && z)`
/// (Functions.cry:13, [FIPS-PUB-180-4 Section 4.1]). The Cryptol takes a
/// tuple; this takes three arguments.
pub open spec fn Ch<W: Word>(x: W, y: W, z: W) -> W {
    W::xor(W::and(x, y), W::and(W::not(x), z))
}

/// The majority vote function, Cryptol's
/// `Maj (x, y, z) = (x && y) ^ (x && z) ^ (y && z)` (Functions.cry:23,
/// [FIPS-PUB-180-4 Section 4.1]).
pub open spec fn Maj<W: Word>(x: W, y: W, z: W) -> W {
    W::xor(W::xor(W::and(x, y), W::and(x, z)), W::and(y, z))
}

/// Cryptol's ``SIGMA_256_0 x = ROTR`{ 2} x ^ ROTR`{13} x ^ ROTR`{22} x``
/// (Functions.cry:26, [FIPS-PUB-180-4 Section 4.1.2]).
pub open spec fn SIGMA_256_0(x: u32) -> u32 {
    ROTR::<2, u32>(x) ^ ROTR::<13, u32>(x) ^ ROTR::<22, u32>(x)
}

/// Cryptol's ``SIGMA_256_1 x = ROTR`{ 6} x ^ ROTR`{11} x ^ ROTR`{25} x``
/// (Functions.cry:27).
pub open spec fn SIGMA_256_1(x: u32) -> u32 {
    ROTR::<6, u32>(x) ^ ROTR::<11, u32>(x) ^ ROTR::<25, u32>(x)
}

/// Cryptol's ``sigma_256_0 x = ROTR`{ 7} x ^ ROTR`{18} x ^ SHR`{ 3} x``
/// (Functions.cry:28).
pub open spec fn sigma_256_0(x: u32) -> u32 {
    ROTR::<7, u32>(x) ^ ROTR::<18, u32>(x) ^ SHR::<3, u32>(x)
}

/// Cryptol's ``sigma_256_1 x = ROTR`{17} x ^ ROTR`{19} x ^ SHR`{10} x``
/// (Functions.cry:29).
pub open spec fn sigma_256_1(x: u32) -> u32 {
    ROTR::<17, u32>(x) ^ ROTR::<19, u32>(x) ^ SHR::<10, u32>(x)
}

/// The SHA-224/256 constants, Cryptol's `K_256 : [64][32]`
/// (Functions.cry:57, [FIPS-PUB-180-4 Section 4.2.2]), copied word for word.
pub open spec fn K_256() -> Seq<u32> {
    seq![
        0x428a2f98u32, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ]
}

} // verus!

/// The executable twins of this module's functions on `[32]`, each of the
/// same name and body as its spec function and proved equal to it (see
/// [`super::notation::exec`]). They are what `compress` calls at run time,
/// as the SPARK crate's `Compress` calls its spec functions.
pub mod exec {
    #[allow(unused_imports)]
    use vstd::prelude::*;
    use crate::sha2::notation::exec::{ROTR, SHR};

    verus! {

    /// [`super::Ch`] on `[32]`.
    #[inline(always)]
    pub fn Ch(x: u32, y: u32, z: u32) -> (r: u32)
        ensures
            r == super::Ch::<u32>(x, y, z),
    {
        (x & y) ^ (!x & z)
    }

    /// [`super::Maj`] on `[32]`.
    #[inline(always)]
    pub fn Maj(x: u32, y: u32, z: u32) -> (r: u32)
        ensures
            r == super::Maj::<u32>(x, y, z),
    {
        (x & y) ^ (x & z) ^ (y & z)
    }

    /// [`super::SIGMA_256_0`].
    #[inline(always)]
    pub fn SIGMA_256_0(x: u32) -> (r: u32)
        ensures
            r == super::SIGMA_256_0(x),
    {
        ROTR::<2>(x) ^ ROTR::<13>(x) ^ ROTR::<22>(x)
    }

    /// [`super::SIGMA_256_1`].
    #[inline(always)]
    pub fn SIGMA_256_1(x: u32) -> (r: u32)
        ensures
            r == super::SIGMA_256_1(x),
    {
        ROTR::<6>(x) ^ ROTR::<11>(x) ^ ROTR::<25>(x)
    }

    /// [`super::sigma_256_0`].
    #[inline(always)]
    pub fn sigma_256_0(x: u32) -> (r: u32)
        ensures
            r == super::sigma_256_0(x),
    {
        ROTR::<7>(x) ^ ROTR::<18>(x) ^ SHR::<3>(x)
    }

    /// [`super::sigma_256_1`].
    #[inline(always)]
    pub fn sigma_256_1(x: u32) -> (r: u32)
        ensures
            r == super::sigma_256_1(x),
    {
        ROTR::<17>(x) ^ ROTR::<19>(x) ^ SHR::<10>(x)
    }

    /// [`super::K_256`].
    pub exec const K_256: [u32; 64]
        ensures
            K_256@ == super::K_256(),
    {
        [
            0x428a2f98u32, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
            0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
            0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
            0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
            0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
            0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
            0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
        ]
    }

    } // verus!
}
