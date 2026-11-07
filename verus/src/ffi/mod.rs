//! The FFI exports: the crate's executable functions as C functions, for
//! Cryptol's `foreign` declarations under `verus/cryptol/`, which compare
//! them with NSA's Cryptol (the counterpart of the SPARK crate's
//! `spark/src/ffi/`; scripts/check-ffi.sh runs the comparison).
//!
//! One module per Cryptol module checked, as the SPARK crate's units:
//! [`aes_gf28`], [`aes_sbox`], [`aes_cipher`], [`aes_key_expansion`] and
//! [`aes_main`] (algorithms/AES/), [`sha2_functions`],
//! [`sha2_preprocessing`] and [`sha2_sha256`] (algorithms/SHA2/), and
//! [`hmac_sha256`] (algorithms/SHA2/SHA256.cry's `HMAC`).
//!
//! Only executable functions are exported. The SPARK crate executes its
//! ghost spec layer too, built with `-gnata`, and checks it directly; a
//! Verus `spec fn` cannot be executed, so the spec layer is checked through
//! the proofs: each function exported here is proved equal to the spec
//! function it implements, so a sample on which it agrees with the Cryptol
//! is one on which the spec does (doc/ffi.md says what is not reached).
//!
//! The exports are outside `verus!`: they take raw pointers, as Cryptol's
//! C calling convention passes sequences, and are `unsafe`. Each is a
//! `foreign-binding` file of scripts/trust-surface.txt. They do no more than
//! read Cryptol's arguments into Rust values, check at run time each
//! precondition of the function they call that Cryptol's types are meant to
//! ensure (a failed check panics, which aborts Cryptol: the run fails), call
//! it, and write its result through Cryptol's output pointer. Code with any
//! logic of its own, such as [`hmac_sha256::hmac_chunked`]'s loop, is
//! inside `verus!` and proved.
//!
//! Cryptol's convention (Cryptol 3.6): a `[K]` word with `K <= 64` is the
//! smallest of `uint8_t` .. `uint64_t` that holds it; a sequence of such
//! words is a pointer to its elements, a sequence of sequences flattened; a
//! numeric type parameter is a leading `size_t`, in the order of the type
//! variables; a sequence result is written through a pointer passed after
//! the arguments; `()` passes nothing.
//!
//! The FFI library itself is `verus/ffi/` (a cdylib that re-exports this
//! module, ffi/Cargo.toml), so a plain build of the crate does not make one.

pub mod aes_gf28;
pub mod aes_sbox;
pub mod aes_cipher;
pub mod aes_key_expansion;
pub mod aes_main;
pub mod sha2_functions;
pub mod sha2_preprocessing;
pub mod sha2_sha256;
pub mod hmac_sha256;

/// The `n` elements at `p`: a Cryptol `[n]T` argument. Cryptol may pass any
/// pointer for an empty sequence, so `n == 0` does not read `p`.
///
/// # Safety
/// When `n > 0`, `p` points to `n` readable `T`s that outlive `'a`.
pub(crate) unsafe fn slice<'a, T>(p: *const T, n: usize) -> &'a [T] {
    if n == 0 { &[] } else { unsafe { core::slice::from_raw_parts(p, n) } }
}

/// The `N` elements at `p`: a Cryptol `[N]T` argument of a fixed length.
///
/// # Safety
/// `p` points to `N` readable `T`s.
pub(crate) unsafe fn array<const N: usize, T: Copy>(p: *const T) -> [T; N] {
    unsafe { p.cast::<[T; N]>().read_unaligned() }
}

/// Writes `v` through `p`: a Cryptol `[N]T` result.
///
/// # Safety
/// `p` points to `N` writable `T`s.
pub(crate) unsafe fn put<const N: usize, T: Copy>(p: *mut T, v: [T; N]) {
    unsafe { p.cast::<[T; N]>().write_unaligned(v) }
}

/// The ends of a chunking, Cryptol's `[c][64]`, as `usize`s, after
/// checking that each is at most `n` and none is below the one before it:
/// the preconditions of the chunked hashes, which the Cryptol properties
/// ensure by sorting their cut points modulo `n + 1`.
///
/// # Safety
/// When `c > 0`, `p` points to `c` readable `u64`s.
pub(crate) unsafe fn chunking(p: *const u64, c: usize, n: usize) -> Vec<usize> {
    let ends: Vec<usize> = unsafe { slice(p, c) }.iter().map(|&e| usize::try_from(e).unwrap()).collect();
    assert!(ends.iter().all(|&e| e <= n), "a chunk ends after the message");
    assert!(ends.windows(2).all(|w| w[0] <= w[1]), "the chunk ends are not sorted");
    ends
}

/// SHA-256's bound on a message, in bytes: a message has fewer
/// (`sha256_bytes::Max_Bytes`, Cryptol's `64 >= width (8 * n)`).
pub(crate) const MAX_BYTES: usize = 1 << 61;

/// Checks that `k` is 128, 192 or 256 (Types.cry's `Key k`), before
/// anything is read at a length that depends on `k`: Cryptol checks `Key k`
/// at the call.
pub(crate) fn check_key_size(k: usize) {
    assert!(k == 128 || k == 192 || k == 256, "not an AES key size");
}
