//! The keyed-Hash Message Authentication Code (HMAC) [FIPS-PUB-198-1],
//! mirroring algorithms/HMAC/Main.cry, as the SPARK crate's `HMAC`
//! (spark/src/hmac/).
//!
//! The spec layer is [`main`] (Main.cry, whose `HMAC` takes the hash
//! functions as arguments, as a trait of its parameters and spec functions
//! generic over it) and its instance for SHA-256, [`sha256`], which
//! instantiates it as packaging/Hash.cry's `HMAC` does for
//! algorithms/SHA2/SHA256.cry. The implementation layer is
//! [`sha256_impl`], proved equal to the spec on the bits.
//!
//! This module holds what Main.cry takes from Cryptol's prelude at the
//! types HMAC uses it: byte sequences `[k][8]`, their `join`, `repeat` and
//! `zero`, each the prelude's ([`crate::cryptol`]) at these types. Keys
//! are `Seq<u8>`, and messages, keys after `join`, and digests are bit
//! sequences `Seq<bool>`, the type the hash functions take and return.
//! (The SPARK crate's `Byte_Index` and its bounds have no counterpart:
//! lengths are `nat`.)

pub mod main;
pub mod sha256;
pub mod sha256_impl;

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::{bit_sequences, join_split, sequences};

verus! {

/// Cryptol's `join : [k][8] -> [k * 8]`, as Main.cry applies it to the key
/// (Main.cry:63 to :65) and to the pads (Main.cry:46 and :47): each byte's
/// bits in order, most significant first, so bit `i` is bit `i % 8` of
/// byte `i / 8`.
pub open spec fn join(K: Seq<u8>) -> Seq<bool> {
    join_split::join::<u8>(K)
}

/// Cryptol's `` repeat`{count} x `` at `[count][8]`, as Main.cry builds the
/// pads (Main.cry:46 and :47): `count` copies of the byte `x`.
pub open spec fn repeat(count: nat, x: u8) -> Seq<u8> {
    sequences::repeat(count, x)
}

/// Cryptol's `zero` at type `[count]`, as `HMAC_init` pads the key with it
/// (Main.cry:64 and :65): `count` zero bits.
pub open spec fn zero(count: nat) -> Seq<bool> {
    bit_sequences::zero(count)
}

} // verus!
