//! Root of the Verus implementations of the Foundation Cryptol
//! specifications. Modules mirror the algorithms/ tree (and the SPARK
//! crate `foundation_spark`): `cryptol` states Cryptol's built-ins once,
//! and each algorithm module holds a spec layer that tracks the Cryptol
//! closely, plus implementation and refinement layers proved equal to it.
//!
//! The spec layers keep Cryptol's names (`SIGMA_256_0`, `W`, `T1`, `Ch`,
//! the const generic `n` of ``ROTR`{n}``), hence the naming lints are off.

#![allow(non_snake_case, non_upper_case_globals)]

pub mod cryptol;
pub mod aes;
pub mod sha2;
pub mod hmac;
pub mod ffi;

#[allow(unused_imports)]
use vstd::prelude::*;
