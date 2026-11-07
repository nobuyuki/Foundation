//! Secure Hash Algorithm preprocessing [FIPS-PUB-180-4 Section 5],
//! mirroring algorithms/SHA2/Preprocessing.cry: the SHA-256 initial hash
//! value. `pad` and `parse` (Preprocessing.cry:14 and :47) are in
//! [`super::main`], at the word size `hash` applies them at, as in the
//! SPARK crate, because `parse` produces Main's words. The other initial
//! hash values are not used by SHA-256.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The SHA-256 initial hash value, Cryptol's `H0_256 : [8][32]`
/// (Preprocessing.cry:81, [FIPS-PUB-180-4 Section 5.3.3]).
pub open spec fn H0_256() -> Seq<u32> {
    seq![
        0x6a09e667u32, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ]
}

} // verus!

/// The executable [`H0_256`].
pub mod exec {
    #[allow(unused_imports)]
    use vstd::prelude::*;

    verus! {

    /// [`super::H0_256`].
    pub exec const H0_256: [u32; 8]
        ensures
            H0_256@ == super::H0_256(),
    {
        [
            0x6a09e667u32, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
            0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
        ]
    }

    } // verus!
}
