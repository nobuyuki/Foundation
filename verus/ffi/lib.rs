//! The FFI library: a cdylib of the crate's `ffi` module (src/ffi/), whose
//! `#[unsafe(no_mangle)] extern "C"` functions are the symbols Cryptol's
//! `foreign` declarations under cryptol/ look up. Built by
//! scripts/check-ffi.sh (doc/ffi.md).

pub use foundation_verus::ffi;
