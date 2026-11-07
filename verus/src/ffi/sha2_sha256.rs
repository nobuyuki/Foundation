//! SHA-256's compression and hash, as the executable
//! [`sha256_stream::compress`], [`sha256_stream::hash`] and
//! [`sha256_stream::hash_chunked`], for verus/cryptol/Verus/SHA2/SHA256.cry.
//! The SPARK crate's `FFI.SHA2_SHA256_Stream` (`FFI.SHA2_SHA256` and its
//! exports export the spec layer's `Step`, `Hash` and `Hash_Bytes`, which
//! have no executable counterpart here other than these).
//!
//! A message is `[n][8]`: `n` as a `size_t`, then a pointer to its bytes.
//! A chunking is `[c][64]`, the ends of its chunks: `c`, then a pointer to
//! `c` 64-bit words ([`super::chunking`]).

use super::{MAX_BYTES, array, chunking, put, slice};
use crate::sha2::sha256_stream;

/// Cryptol's `foreign verus_compress : [8][32] -> [16][32] -> [8][32]`
/// (Main.cry's `step` at SHA256.cry's parameters).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_compress(h: *const u32, m: *const u32, output: *mut u32) {
    let mut h: [u32; 8] = unsafe { array(h) };
    let m: [u32; 16] = unsafe { array(m) };
    sha256_stream::compress(&mut h, &m);
    unsafe { put(output, h) }
}

/// Cryptol's `foreign verus_hash : {n} (fin n, 61 >= width n) => [n][8] ->
/// [32][8]` (SHA256.cry's `hash` of the message's bits).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_hash(n: usize, m: *const u8, output: *mut u8) {
    assert!(n < MAX_BYTES);
    let m: &[u8] = unsafe { slice(m, n) };
    unsafe { put(output, sha256_stream::hash(m)) }
}

/// Cryptol's `foreign verus_hash_chunked : {n, c} (fin n, 61 >= width n,
/// fin c, 64 >= c) => [n][8] -> [c][64] -> [32][8]`: `init`, `update` on
/// each chunk (a last one running to `n`), `finalize`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_hash_chunked(n: usize, c: usize, m: *const u8, ends: *const u64, output: *mut u8) {
    assert!(n < MAX_BYTES);
    let m: &[u8] = unsafe { slice(m, n) };
    let ends = unsafe { chunking(ends, c, n) };
    unsafe { put(output, sha256_stream::hash_chunked(m, &ends)) }
}
