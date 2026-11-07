//! The Secure Hash Algorithm with a digest size of 256 bits (SHA-256)
//! [FIPS-PUB-180-4 Section 6.2], mirroring algorithms/SHA2/SHA256.cry: Main
//! instantiated as SHA256.cry instantiates `SHA2::Main` (SHA256.cry:19),
//! with `d = 256`, `w = 32`, `Klen = 64`, `H0 = H0_256`, `K = K_256`, and
//! the SHA-224/256 SIGMA and sigma functions. `main::hash::<SHA256>` is
//! SHA256.cry's `_hash = SHA256::hash`.
//!
//! SHA256.cry is itself an instance of packaging/Hash.cry, which wraps
//! `_hash` as `hash` and adds HMAC and PBKDF2. As in the SPARK crate, there
//! is no packaging layer here.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use super::functions::{K_256, SIGMA_256_0, SIGMA_256_1, sigma_256_0, sigma_256_1};
use super::main::Parameters;
#[cfg(verus_only)]
use super::preprocessing::H0_256;

verus! {

/// SHA-256's instance of Main.cry's parameters.
pub struct SHA256;

impl Parameters for SHA256 {
    type Word = u32;

    open spec fn d() -> nat {
        256
    }

    open spec fn w() -> nat {
        32
    }

    open spec fn Klen() -> nat {
        64
    }

    open spec fn K() -> Seq<u32> {
        K_256()
    }

    open spec fn H0() -> Seq<u32> {
        H0_256()
    }

    open spec fn SIGMA_0(x: u32) -> u32 {
        SIGMA_256_0(x)
    }

    open spec fn SIGMA_1(x: u32) -> u32 {
        SIGMA_256_1(x)
    }

    open spec fn sigma_0(x: u32) -> u32 {
        sigma_256_0(x)
    }

    open spec fn sigma_1(x: u32) -> u32 {
        sigma_256_1(x)
    }

    proof fn type_constraints() {
    }
}

} // verus!
