//! The keyed-Hash Message Authentication Code (HMAC) [FIPS-PUB-198-1
//! Section 4], mirroring algorithms/HMAC/Main.cry, as the SPARK crate's
//! generic `HMAC.Main` (spark/src/hmac/foundation_spark-hmac-main.ads).
//!
//! The Cryptol's `HMAC` (Main.cry:26) takes its hash functions `Hk`, `Hn`
//! and `HL` as arguments and the sizes `B` and `L` as type parameters.
//! Here they are the trait [`Parameters`], in the same order, as in
//! SHA2's `main` (the SPARK crate makes them a generic's formals); the
//! per-call sizes `k` (the key's length), `n` (the text's) and `λ` (the
//! output's) stay per call. [`super::sha256`] implements it as
//! packaging/Hash.cry's `HMAC` (Hash.cry:71) instantiates the Cryptol,
//! with every hash the one SHA-256 `hash`.
//!
//! Cryptol gives `Hk`, `Hn` and `HL` the input types `[k * 8]`,
//! `[B * 8 + n]` and `[(B + L) * 8]`, and leaves it to the caller to have
//! hash functions of those types: packaging/Hash.cry does so with its
//! `UpperLimit` constraints (Hash.cry:74 to :76). Here a hash takes any
//! bit sequence shorter than `max_length`, and the `recommends` of `HMAC`
//! and `HMAC_init` carry those constraints. That every hash returns
//! `[L * 8]`, and the Cryptol's constraints on `B` and `L`, are
//! [`Parameters::type_constraints`].

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_only)]
use crate::cryptol::bit_sequences;
#[cfg(verus_only)]
use super::{join, repeat, zero};

verus! {

/// The parameters of Main.cry's `HMAC` (Main.cry:26 to :36): the sizes
/// `B` and `L`, and the hash functions.
pub trait Parameters {
    /// Cryptol's `B`, the block size of the hash's input in bytes
    /// (Main.cry:15).
    spec fn B() -> nat;

    /// Cryptol's `L`, the size of the hash's output in bytes (Main.cry:18).
    spec fn L() -> nat;

    /// The hash functions' bound on their message length in bits: they
    /// take a message `M` with `M.len() < max_length()`. packaging/Hash.cry's
    /// `UpperLimit` (Hash.cry:28) as a length, `2 ^^ UpperLimit`.
    spec fn max_length() -> nat;

    /// Cryptol's `Hk : [k * 8] -> [L * 8]` (Main.cry:34), the hash of a
    /// long key.
    spec fn Hk(M: Seq<bool>) -> Seq<bool>;

    /// Cryptol's `Hn : [B * 8 + n] -> [L * 8]` (Main.cry:35), the inner
    /// hash.
    spec fn Hn(M: Seq<bool>) -> Seq<bool>;

    /// Cryptol's `HL : [(B + L) * 8] -> [L * 8]` (Main.cry:36), the outer
    /// hash.
    spec fn HL(M: Seq<bool>) -> Seq<bool>;

    /// The Cryptol's type constraints on the parameters,
    /// `fin B, 2 ^^ B >= 8 * B` and `L <= B` (Main.cry:29 and :32), with
    /// what the hashes' types carry and a `Seq` does not: each returns
    /// `[L * 8]`. Each implementation proves them. (The SPARK crate checks
    /// the first two with `pragma Compile_Time_Error` and states the third
    /// as its formals' postconditions.) The constraints on `λ` and `n`
    /// (Main.cry:28 and :31) are per call: `HMAC`'s `recommends`.
    proof fn type_constraints()
        ensures
            pow2(Self::B()) >= 8 * Self::B(),
            Self::L() <= Self::B(),
            forall|M: Seq<bool>| M.len() < Self::max_length() ==> #[trigger] Self::Hk(M).len() == 8 * Self::L(),
            forall|M: Seq<bool>| M.len() < Self::max_length() ==> #[trigger] Self::Hn(M).len() == 8 * Self::L(),
            forall|M: Seq<bool>| M.len() < Self::max_length() ==> #[trigger] Self::HL(M).len() == 8 * Self::L(),
    ;
}

/// Cryptol's `2 ^^ B - 8 * B`, the bound on the text's length `n`
/// (Main.cry:31, [FIPS-PUB-198-1 Section 2.3]).
pub open spec fn text_limit<P: Parameters>() -> nat {
    (pow2(P::B()) - 8 * P::B()) as nat
}

/// `HMAC`'s local `opad = join (repeat`{B} 0x5C)` (Main.cry:46,
/// [FIPS-PUB-198-1 Section 2.3]), the outer pad: `B` bytes 0x5C.
pub open spec fn opad<P: Parameters>() -> Seq<bool> {
    join(repeat(P::B(), 0x5C))
}

/// `HMAC`'s local `ipad = join (repeat`{B} 0x36)` (Main.cry:47,
/// [FIPS-PUB-198-1 Section 2.3]), the inner pad: `B` bytes 0x36.
pub open spec fn ipad<P: Parameters>() -> Seq<bool> {
    join(repeat(P::B(), 0x36))
}

/// The key preprocessing, Cryptol's `HMAC_init Hk K` (Main.cry:56, Steps
/// 1 to 3 of [FIPS-PUB-198-1 Section 4 Table 1]), private in Main.cry and
/// public here because [`super::sha256_impl`] is proved against it, as in
/// the SPARK crate. By cases on the key's length `k`, in the Cryptol's
/// order of guards (`k == B`, `k > B`, `k < B`): a key of `B` bytes is its
/// bits; a longer key is hashed with `Hk` and the `L`-byte digest padded
/// with zeros to `B` bytes; a shorter key is padded with zeros to `B`
/// bytes. Only a longer key is hashed, so only it must have its `8 * k`
/// bits below `max_length`, as `Hk`'s type `[k * 8]` requires of the
/// Cryptol's caller. The result is `K0`, the key as `B * 8` bits.
pub open spec fn HMAC_init<P: Parameters>(K: Seq<u8>) -> Seq<bool>
    recommends
        K.len() <= P::B() || 8 * K.len() < P::max_length(),
{
    if K.len() == P::B() {
        join(K)
    } else if K.len() > P::B() {
        P::Hk(join(K)) + zero((8 * (P::B() - P::L())) as nat)
    } else {
        join(K) + zero((8 * (P::B() - K.len())) as nat)
    }
}

/// HMAC, Cryptol's `HMAC Hk Hn HL K text` (Main.cry:40, [FIPS-PUB-198-1
/// Section 4]): `take (HL ((K0 ^ opad) # (Hn ((K0 ^ ipad) # text))))`,
/// where `K0 = HMAC_init Hk K`. Cryptol's `^` is the prelude's
/// [`bit_sequences::xor`], `#` is `+`, and `take` at `[λ]` is `take(λ)`.
///
/// The `recommends` are the Cryptol's constraints, `λ <= L * 8` and
/// `n < 2 ^^ B - 8 * B` (Main.cry:28 and :31), with what the hashes'
/// types ask of the caller: `Hk`'s `[k * 8]` (for a long key), `Hn`'s
/// `[B * 8 + n]` and `HL`'s `[(B + L) * 8]`, each a message shorter than
/// `max_length`, as packaging/Hash.cry's `UpperLimit` constraints state
/// them (Hash.cry:74 to :76).
pub open spec fn HMAC<P: Parameters>(K: Seq<u8>, text: Seq<bool>, lambda: nat) -> Seq<bool>
    recommends
        K.len() <= P::B() || 8 * K.len() < P::max_length(),
        text.len() < text_limit::<P>(),
        8 * P::B() + text.len() < P::max_length(),
        8 * (P::B() + P::L()) < P::max_length(),
        lambda <= 8 * P::L(),
{
    let K0 = HMAC_init::<P>(K);
    P::HL(
        bit_sequences::xor(K0, opad::<P>()) + P::Hn(bit_sequences::xor(K0, ipad::<P>()) + text),
    ).take(lambda as int)
}

} // verus!
