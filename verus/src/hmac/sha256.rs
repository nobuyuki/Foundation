//! HMAC-SHA-256 [FIPS-PUB-198-1, FIPS-PUB-180-4 Section 6.2], as the SPARK
//! crate's `HMAC.SHA256` (spark/src/hmac/foundation_spark-hmac-sha256.ads):
//! Main's parameters as packaging/Hash.cry's `HMAC` (Hash.cry:71) gives
//! them for algorithms/SHA2/SHA256.cry: `B = BlockSize / 8 = 64`,
//! `L = DigestSize / 8 = 32`, and `Hk`, `Hn` and `HL` all the SHA-256
//! `hash` (Main.cry:55 of algorithms/SHA2), whose message bound `2 ^^ 64`
//! is Hash.cry's `2 ^^ UpperLimit` at SHA256.cry's `UpperLimit = 64`.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
use super::main::Parameters;
#[cfg(verus_only)]
use crate::sha2::{self, main::hash};

verus! {

/// HMAC-SHA-256's instance of Main.cry's parameters.
pub struct SHA256;

impl Parameters for SHA256 {
    open spec fn B() -> nat {
        64
    }

    open spec fn L() -> nat {
        32
    }

    open spec fn max_length() -> nat {
        sha2::main::max_length::<sha2::sha256::SHA256>()
    }

    open spec fn Hk(M: Seq<bool>) -> Seq<bool> {
        hash::<sha2::sha256::SHA256>(M)
    }

    open spec fn Hn(M: Seq<bool>) -> Seq<bool> {
        hash::<sha2::sha256::SHA256>(M)
    }

    open spec fn HL(M: Seq<bool>) -> Seq<bool> {
        hash::<sha2::sha256::SHA256>(M)
    }

    proof fn type_constraints() {
        vstd::arithmetic::power2::lemma2_to64();
        assert forall|M: Seq<bool>| #[trigger] hash::<sha2::sha256::SHA256>(M).len() == 256 by {
            lemma_hash_len(M);
        }
    }
}

/// SHA-256's `hash` (Main.cry:55) returns `[256]`, for every message.
pub proof fn lemma_hash_len(M: Seq<bool>)
    ensures
        hash::<sha2::sha256::SHA256>(M).len() == 256,
{
    let n = sha2::main::N::<sha2::sha256::SHA256>(M.len());
    let Ms = sha2::main::parse::<sha2::sha256::SHA256>(sha2::main::pad::<sha2::sha256::SHA256>(M), n);
    sha2::sha256_bytes::lemma_foldl_step_len(sha2::preprocessing::H0_256(), Ms, n as int);
}

} // verus!
