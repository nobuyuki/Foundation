//! HMAC-SHA-256, as the executable [`sha256_impl::hmac_sha256`],
//! [`sha256_impl::init_key`] and [`hmac_chunked`] (`init`, `update` on each
//! chunk, `finalize`), for verus/cryptol/Verus/HMAC/SHA256.cry. The SPARK
//! crate's `FFI.HMAC_SHA256_Impl` (`FFI.HMAC_SHA256` and its exports export
//! the spec layer's `HMAC` and `HMAC_init`, which have no executable
//! counterpart here other than these).
//!
//! A key is `[k][8]` and a text `[n][8]`: the length as a `size_t`, then a
//! pointer to the bytes. A chunking of the text is `[c][64]`, as for
//! SHA-256 ([`super::chunking`]).

#[allow(unused_imports)]
use vstd::prelude::*;
use crate::hmac::sha256_impl::{self, finalize, init, update};
#[cfg(verus_only)]
use crate::hmac::sha256_impl::{Max_Text, count, lemma_final, lemma_update, models};
#[cfg(verus_only)]
use crate::hmac::main::HMAC;
#[cfg(verus_only)]
use crate::hmac::sha256::SHA256;
#[cfg(verus_only)]
use crate::sha2::sha256_bytes::{Max_Bytes, bits_of};
use super::{MAX_BYTES, chunking, put, slice};

verus! {

/// HMAC-SHA-256 of `text` under `key` through the incremental interface:
/// `init`, then `update` on each chunk of `text` that `ends` cuts (chunk
/// `j` runs from the end of chunk `j - 1`, or 0, up to `ends[j]`, and a
/// last chunk to the end), then `finalize`. Proved equal, on the bits, to
/// the spec's `HMAC` at `λ = 256` for every chunking. The SPARK crate's
/// `FFI.HMAC_SHA256_Impl.HMAC_Chunked`, as `sha256_stream::hash_chunked`
/// is its `SHA256_Stream.Hash_Chunked`.
pub fn hmac_chunked(key: &[u8], text: &[u8], ends: &[usize]) -> (d: [u8; 32])
    requires
        key@.len() < Max_Bytes(),
        text@.len() < Max_Text(),
        forall|j: int| 0 <= j < ends@.len() ==> #[trigger] ends@[j] <= text@.len(),
        forall|j: int| 0 < j < ends@.len() ==> ends@[j - 1] <= #[trigger] ends@[j],
    ensures
        bits_of(d@) == HMAC::<SHA256>(key@, bits_of(text@), 256),
{
    let len = text.len();
    let mut c = init(key);
    let mut done: usize = 0;
    assert(text@.subrange(0, 0) =~= Seq::<u8>::empty());
    let mut j: usize = 0;
    while j < ends.len()
        invariant
            len == text@.len() < Max_Text(),
            key@.len() < Max_Bytes(),
            forall|j: int| 0 <= j < ends@.len() ==> #[trigger] ends@[j] <= text@.len(),
            forall|j: int| 0 < j < ends@.len() ==> ends@[j - 1] <= #[trigger] ends@[j],
            j <= ends@.len(),
            if j > 0 { done == ends@[j - 1] } else { done == 0 },
            done <= len,
            models(c, key@, text@.subrange(0, done as int)),
            count(c) == 64 + done,
        decreases ends@.len() - j,
    {
        let e = ends[j];
        let ghost c0 = c;
        let chunk = &text[done..e];
        update(&mut c, chunk);
        proof {
            assert(text@.subrange(0, done as int) + chunk@ =~= text@.subrange(0, e as int));
            lemma_update(c0, chunk@, c, key@, text@.subrange(0, done as int));
        }
        done = e;
        j += 1;
    }
    let ghost c0 = c;
    let chunk = &text[done..len];
    update(&mut c, chunk);
    proof {
        assert(text@.subrange(0, done as int) + chunk@ =~= text@);
        lemma_update(c0, chunk@, c, key@, text@.subrange(0, done as int));
        lemma_final(c, key@, text@);
    }
    finalize(&c)
}

} // verus!

/// HMAC's bound on a text, in bytes: a text has fewer
/// (`sha256_impl::Max_Text`, Main.cry's `n < 2 ^^ B - 8 * B` in bytes).
const MAX_TEXT: usize = MAX_BYTES - 64;

/// Cryptol's `foreign verus_hmac_sha256 : {k, n} (fin k, 61 >= width k,
/// fin n, 61 >= width n) => [k][8] -> [n][8] -> [32][8]`
/// (SHA256.cry's `HMAC` of the text's bits).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_hmac_sha256(k: usize, n: usize, key: *const u8, text: *const u8, output: *mut u8) {
    assert!(k < MAX_BYTES && n < MAX_TEXT);
    let key: &[u8] = unsafe { slice(key, k) };
    let text: &[u8] = unsafe { slice(text, n) };
    unsafe { put(output, sha256_impl::hmac_sha256(key, text)) }
}

/// Cryptol's `foreign verus_init_key : {k} (fin k, 61 >= width k) =>
/// [k][8] -> [64][8]` (Main.cry's `HMAC_init`, K0).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_init_key(k: usize, key: *const u8, output: *mut u8) {
    assert!(k < MAX_BYTES);
    let key: &[u8] = unsafe { slice(key, k) };
    unsafe { put(output, sha256_impl::init_key(key)) }
}

/// Cryptol's `foreign verus_hmac_chunked : {k, n, c} (fin k, 61 >= width
/// k, fin n, 61 >= width n, fin c, 64 >= c) => [k][8] -> [n][8] -> [c][64]
/// -> [32][8]` ([`hmac_chunked`]).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_hmac_chunked(
    k: usize,
    n: usize,
    c: usize,
    key: *const u8,
    text: *const u8,
    ends: *const u64,
    output: *mut u8,
) {
    assert!(k < MAX_BYTES && n < MAX_TEXT);
    let key: &[u8] = unsafe { slice(key, k) };
    let text: &[u8] = unsafe { slice(text, n) };
    let ends = unsafe { chunking(ends, c, n) };
    unsafe { put(output, hmac_chunked(key, text, &ends)) }
}
