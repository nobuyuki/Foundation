//! The entry points the benchmark times and the size table measures:
//! one non-inlined wrapper per operation of NSA's Rust AES
//! (`algorithms/AES/rust/`), as `perf/src/perf_aes.rs` has for the Verus.
//! Whatever the optimizer inlines into a wrapper is counted in its size,
//! and every timed call is one real call on both sides.

#![allow(non_snake_case)]

pub use Cipher::{Block, Word};

/// `KeyExpansion` [FIPS-PUB-197 Section 5.2]: NSA's `key_expansion`.
#[inline(never)]
#[must_use]
pub fn expand_key(k: usize, key: &[Word]) -> [Block; 15] {
    KeyExpansion::key_expansion(k, key)
}

/// `Cipher` [FIPS-PUB-197 Section 5.1]: NSA's `cipher`.
#[inline(never)]
#[must_use]
pub fn encrypt(ks: &[Block], block: Block) -> Block {
    Cipher::cipher(ks, block)
}

/// `InvCipher` [FIPS-PUB-197 Section 5.3]: NSA's `inv_cipher`, which undoes
/// the rounds of `cipher` in reverse order.
#[inline(never)]
#[must_use]
pub fn decrypt(ks: &[Block], block: Block) -> Block {
    Cipher::inv_cipher(ks, block)
}
