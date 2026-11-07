//! The entry points the benchmark times and the size table measures: one
//! non-inlined wrapper per AES operation, as perf/rust/src/lib.rs has for
//! the Rust (the SPARK crate's `perf/src/perf_aes.ads` and `.adb`).
//! Whatever the optimizer inlines into a wrapper (at `opt-level` 3 with
//! LTO, usually the whole operation) is counted in its size, and every
//! timed call is one real call on both sides.
//!
//! The crate's functions take the key size as a const generic (Cryptol's
//! `{k}`); the SPARK crate's and NSA's take it at run time. Each wrapper
//! takes it at run time, as the SPARK crate's do, and dispatches to the
//! three instances. perf/src/perf_bench.rs passes the key size through
//! `black_box`, so the timed code is each instance's general code, with the
//! dispatch, and no wrapper is specialized for a constant key size.

pub use foundation_verus::aes::aes_impl::{AESWord, Block};
use foundation_verus::aes::aes_impl;

/// `aes_impl::expand_key`: KeyExpansion [FIPS-PUB-197 Section 5.2] at key
/// size `k` (128, 192 or 256) of the cipher key, the first `k / 32` words
/// of `key`. The round keys are the first `k / 32 + 7` of the 15 blocks.
#[inline(never)]
#[must_use]
pub fn expand_key(k: usize, key: &[AESWord]) -> [Block; 15] {
    match k {
        128 => aes_impl::expand_key::<128>(key),
        192 => aes_impl::expand_key::<192>(key),
        256 => aes_impl::expand_key::<256>(key),
        _ => unreachable!(),
    }
}

/// `aes_impl::encrypt_block`: Cipher [FIPS-PUB-197 Section 5.1] of
/// `state` in place, under the round keys `w`, at key size `k`.
#[inline(never)]
pub fn encrypt(k: usize, w: &[Block], state: &mut Block) {
    match k {
        128 => aes_impl::encrypt_block::<128>(w, state),
        192 => aes_impl::encrypt_block::<192>(w, state),
        256 => aes_impl::encrypt_block::<256>(w, state),
        _ => unreachable!(),
    }
}

/// `aes_impl::decrypt_block`: InvCipher [FIPS-PUB-197 Section 5.3] of
/// `state` in place.
#[inline(never)]
pub fn decrypt(k: usize, w: &[Block], state: &mut Block) {
    match k {
        128 => aes_impl::decrypt_block::<128>(w, state),
        192 => aes_impl::decrypt_block::<192>(w, state),
        256 => aes_impl::decrypt_block::<256>(w, state),
        _ => unreachable!(),
    }
}

/// `aes_impl::decrypt_block_prime`: InvCipher', the rounds of Cipher undone
/// in reverse order, the structure of NSA's Rust `inv_cipher`.
#[inline(never)]
pub fn decrypt_prime(k: usize, w: &[Block], state: &mut Block) {
    match k {
        128 => aes_impl::decrypt_block_prime::<128>(w, state),
        192 => aes_impl::decrypt_block_prime::<192>(w, state),
        256 => aes_impl::decrypt_block_prime::<256>(w, state),
        _ => unreachable!(),
    }
}
