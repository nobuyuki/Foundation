//! The types AES is stated in, mirroring algorithms/AES/Types.cry
//! [FIPS-PUB-197 Sections 2.1, 2.3 and 5], as the SPARK crate's
//! `AES.Spec.Types` (spark/src/aes/foundation_spark-aes-spec-types.ads).
//!
//! Key-size polymorphism. The Cryptol is polymorphic in the key size `k`
//! under the constraint `Key k` (`{k} (Key k) => ...`). Here, as Cryptol's
//! type parameters are elsewhere in the crate (`sha2::notation`,
//! the polynomial modules of the prelude), `k` is a const generic
//! `const k: u32`, so ``Cipher`{128}`` is `Cipher::<128>`, and the
//! constraint `Key k` is the spec function [`Key`], clause for clause, as a
//! `recommends`. The type functions `Nk` and `Nr` are spec functions of
//! `k as nat`.
//!
//! The SPARK crate needs more, because Ada has no type-level numbers: a
//! generic `AES_K` for the `{k}` functions, its three instances, and the
//! ghost `Spec.Dispatch`, which selects an instance by a run-time key size
//! for the implementation. None of these is needed here: a const generic
//! is a value in exec code as well as in spec code, so one implementation
//! generic in `k` can be proved once against the spec at the same `k`.
//!
//! Sequences are `Seq`, as in the rest of the crate: a `Block` is a
//! `Seq<u8>` of length 16, and the lengths of `[16][8]`, `[4][8]`,
//! `[Nk k]AESWord` and `[Nr k + 1]Block` are `recommends` of the functions
//! that take them. A byte is a `u8`, and Cryptol's bit 0 of a `[8]` is its
//! most significant bit ([`crate::cryptol::words`]).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Types.cry: `type constraint Key k = (fin k, k % 64 == 0, k / 64 >= 2,
/// k / 64 <= 4)` (Types.cry:12), the standard key sizes 128, 192 and 256
/// [FIPS-PUB-197 Sections 1, 5 and 6.1]. `fin k` holds of any `nat`.
pub open spec fn Key(k: nat) -> bool {
    &&& k % 64 == 0
    &&& k / 64 >= 2
    &&& k / 64 <= 4
}

/// Types.cry: `type Block = [16][8]` (Types.cry:18). The input, output,
/// State and Round Key [FIPS-PUB-197 Section 2.1].
pub type Block = Seq<u8>;

/// Types.cry: `type AESWord = [4][8]` (Types.cry:25), a 32-bit word as four
/// bytes [FIPS-PUB-197 Section 2.1].
pub type AESWord = Seq<u8>;

/// Types.cry: `type Nk k = k / 32` (Types.cry:32). The number of 32-bit
/// words in the key: 4, 6 or 8 [FIPS-PUB-197 Sections 2.3 and 5].
pub open spec fn Nk(k: nat) -> nat {
    k / 32
}

/// Types.cry: `type Nr k = Nk k + 6` (Types.cry:39). The number of rounds:
/// 10, 12 or 14 [FIPS-PUB-197 Sections 2.3 and 5].
pub open spec fn Nr(k: nat) -> nat {
    Nk(k) + 6
}

/// Whether `ws` has Cryptol's type `[Nr k + 1]Block`: `Nr k + 1` round
/// keys of 16 bytes each. The SPARK crate's `Is_Round_Keys`.
pub open spec fn is_round_keys(k: nat, ws: Seq<Block>) -> bool {
    &&& ws.len() == Nr(k) + 1
    &&& forall|i: int| 0 <= i < ws.len() ==> (#[trigger] ws[i]).len() == 16
}

/// Cryptol's `split` at type `Block -> [4]AESWord`, as Cipher.cry's
/// `MixColumns` applies it: column `j` is bytes `4 * j` to `4 * j + 3`.
pub open spec fn split(bs: Block) -> Seq<AESWord>
    recommends
        bs.len() == 16,
{
    Seq::new(4, |j: int| Seq::new(4, |i: int| bs[4 * j + i]))
}

/// Cryptol's `join` at type `[4]AESWord -> Block`, the inverse of
/// [`split`]: byte `i` is byte `i % 4` of column `i / 4`. Also
/// KeyExpansion.cry's regrouping of four words of `w` into a round key.
pub open spec fn join(ws: Seq<AESWord>) -> Block
    recommends
        ws.len() == 4,
        forall|j: int| 0 <= j < 4 ==> (#[trigger] ws[j]).len() == 4,
{
    Seq::new(16, |i: int| ws[i / 4][i % 4])
}

} // verus!
