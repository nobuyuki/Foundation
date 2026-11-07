//! Cryptol's built-ins (foldl, @, join, split, ...) as spec functions and lemmas.
//!
//! The spec layers are written in these, under their Cryptol names, so that
//! each translation from Cryptol to Verus is checked here once and the spec
//! bodies are left with the algorithm. This mirrors the SPARK crate's
//! `Foundation_Spark.Cryptol` (spark/src/cryptol/, spark/doc/cryptol-prelude.md).
//!
//! | module | Cryptol |
//! |---|---|
//! | [`Word`] (this module) | a word `[w]` at a fixed width, as a Rust unsigned integer |
//! | [`folds`] | `foldl f z xs`, ``foldl f z (take`{N} xs)`` |
//! | [`enumeration_folds`] | `foldl f z [from ..< to]` |
//! | [`words`] | `x @ j`, `head x` on a word `[w]` |
//! | [`bulk_indexing`] | `xs @@ is` |
//! | [`join_split`] | `join`, `split` between `[n][w]` and `[n * w]` |
//! | [`bit_sequences`] | `zero : [n]`, `` `v : [n] ``, `^` on `[n]` |
//! | [`sequences`] | `reverse`, `repeat` |
//! | [`numeric`] | the type operators `/^`, `%^` |
//! | [`polynomial_products`] | `pmult` |
//! | [`polynomial_remainders`] | `pmod` |
//! | [`polynomial_quotients`] | `pdiv` |
//!
//! Choices a reviewer should know (spark/doc/cryptol-prelude.md has the
//! SPARK crate's, which these follow except where said):
//! - **Folds recurse from the last element**, as the SPARK prelude's do:
//!   ``foldl f z (take`{N} xs) = f (foldl f z (take`{N - 1} xs)) (xs @ (N - 1))``,
//!   after Cryptol's documented example `foldl (+) 0 [1,2,3] = ((0 + 1) + 2) + 3`.
//!   It is the shape of the implementation's loops.
//! - **Closures are closures.** The SPARK prelude passes what a fold's
//!   function closes over as an explicit first argument, because Ada's
//!   generic formal functions are not closures. Verus has `spec_fn`
//!   closures, so here the function is a closure, as in the Cryptol.
//! - **Words are numbers**, as in the SPARK crate: a `[w]` is a Rust
//!   unsigned integer of `w` bits (the [`Word`] trait), and bit `j` of a
//!   word has weight `2 ^^ (w - 1 - j)`. The polynomial modules read a
//!   word as a polynomial the same way: the bit of weight `2 ^^ i` is the
//!   coefficient of `x ^^ i`.
//! - **Lengths and indices are `int`/`nat`**, which are unbounded, so the
//!   SPARK crate's 128-bit `Bit_Index` and its bounds have no counterpart.

pub mod folds;
pub mod enumeration_folds;
pub mod words;
pub mod join_split;
pub mod bit_sequences;
pub mod bulk_indexing;
pub mod sequences;
pub mod numeric;
pub mod polynomial_products;
pub mod polynomial_remainders;
pub mod polynomial_quotients;

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Cryptol's word type `[w]` at one fixed width, with the operations the
/// spec layers apply to words: Cryptol's `+` (modulo `2 ^^ w`), `&&`, `||`,
/// `^`, `~`, `>>` and `<<`, and the literals 0 and 1. The counterpart of
/// the SPARK crate's generic formal `type Word is mod <>`, whose modulus is
/// `2 ** Word_Size`.
pub trait Word: Sized + Copy {
    /// The number of bits, Cryptol's `w`.
    spec fn width() -> nat;

    /// Cryptol's `+` on `[w]`: addition modulo `2 ^^ w`.
    spec fn add(a: Self, b: Self) -> Self;

    /// Cryptol's `&&` on `[w]`, bitwise.
    spec fn and(a: Self, b: Self) -> Self;

    /// Cryptol's `||` on `[w]`, bitwise.
    spec fn or(a: Self, b: Self) -> Self;

    /// Cryptol's `^` on `[w]`, bitwise.
    spec fn xor(a: Self, b: Self) -> Self;

    /// Cryptol's `~` on `[w]`, bitwise.
    spec fn not(a: Self) -> Self;

    /// Cryptol's `x >> n` on `[w]`, zeros shifted in.
    spec fn shr(a: Self, n: nat) -> Self;

    /// Cryptol's `x << n` on `[w]`, zeros shifted in.
    spec fn shl(a: Self, n: nat) -> Self;

    /// The literal `0 : [w]`.
    spec fn zero() -> Self;

    /// The literal `1 : [w]`.
    spec fn one() -> Self;

    /// The word as an unsigned number, which Cryptol's `<`, `>=`, `toInteger`
    /// and index operators (`@`, `@@`, at an index of type `[w]`) see. A
    /// modular type's value in the SPARK crate.
    spec fn to_nat(a: Self) -> nat;
}

/// `[8]`, a byte, as HMAC's keys `[k][8]` and pads hold them.
impl Word for u8 {
    open spec fn width() -> nat {
        8
    }

    /// vstd's specification of `u8::wrapping_add`, as for `u32`.
    open spec fn add(a: u8, b: u8) -> u8 {
        vstd::wrapping::u8_specs::wrapping_add(a, b)
    }

    open spec fn and(a: u8, b: u8) -> u8 {
        a & b
    }

    open spec fn or(a: u8, b: u8) -> u8 {
        a | b
    }

    open spec fn xor(a: u8, b: u8) -> u8 {
        a ^ b
    }

    open spec fn not(a: u8) -> u8 {
        !a
    }

    open spec fn shr(a: u8, n: nat) -> u8 {
        a >> (n as u8)
    }

    open spec fn shl(a: u8, n: nat) -> u8 {
        a << (n as u8)
    }

    open spec fn zero() -> u8 {
        0
    }

    open spec fn one() -> u8 {
        1
    }

    open spec fn to_nat(a: u8) -> nat {
        a as nat
    }
}

/// `[16]`, which AES's GF(2^8) arithmetic holds its polynomials in (the
/// `[15]` product of `pmult` and the `[9]` modulus), as the SPARK crate's
/// `GF28.Poly` (`Unsigned_16`) does.
impl Word for u16 {
    open spec fn width() -> nat {
        16
    }

    /// vstd's specification of `u16::wrapping_add`, as for `u32`.
    open spec fn add(a: u16, b: u16) -> u16 {
        vstd::wrapping::u16_specs::wrapping_add(a, b)
    }

    open spec fn and(a: u16, b: u16) -> u16 {
        a & b
    }

    open spec fn or(a: u16, b: u16) -> u16 {
        a | b
    }

    open spec fn xor(a: u16, b: u16) -> u16 {
        a ^ b
    }

    open spec fn not(a: u16) -> u16 {
        !a
    }

    open spec fn shr(a: u16, n: nat) -> u16 {
        a >> (n as u16)
    }

    open spec fn shl(a: u16, n: nat) -> u16 {
        a << (n as u16)
    }

    open spec fn zero() -> u16 {
        0
    }

    open spec fn one() -> u16 {
        1
    }

    open spec fn to_nat(a: u16) -> nat {
        a as nat
    }
}

/// `[32]`.
impl Word for u32 {
    open spec fn width() -> nat {
        32
    }

    /// vstd's specification of `u32::wrapping_add`, which is addition
    /// modulo `2 ^^ 32` written as a case split.
    open spec fn add(a: u32, b: u32) -> u32 {
        vstd::wrapping::u32_specs::wrapping_add(a, b)
    }

    open spec fn and(a: u32, b: u32) -> u32 {
        a & b
    }

    open spec fn or(a: u32, b: u32) -> u32 {
        a | b
    }

    open spec fn xor(a: u32, b: u32) -> u32 {
        a ^ b
    }

    open spec fn not(a: u32) -> u32 {
        !a
    }

    open spec fn shr(a: u32, n: nat) -> u32 {
        a >> (n as u32)
    }

    open spec fn shl(a: u32, n: nat) -> u32 {
        a << (n as u32)
    }

    open spec fn zero() -> u32 {
        0
    }

    open spec fn one() -> u32 {
        1
    }

    open spec fn to_nat(a: u32) -> nat {
        a as nat
    }
}

} // verus!
