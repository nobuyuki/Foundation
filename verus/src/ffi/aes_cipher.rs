//! Cipher.cry's round transformations and ciphers, as the executable
//! functions of [`aes_impl`], for verus/cryptol/Verus/AES/Cipher.cry. The
//! SPARK crate's `FFI.AES_Cipher` and its exports (the spec layer's) and
//! the block ciphers of `FFI.AES_Impl`.
//!
//! A `Block` (`[16][8]`) or an `AESWord` (`[4][8]`) is a pointer to its
//! bytes, and a result is written through the pointer after the arguments.
//! The functions of [`aes_impl`] change a block in place, so each export
//! copies the block in, calls, and writes the block out. The ciphers take
//! `{k}` as a `size_t` and the round keys `[Nr k + 1]Block` as a pointer to
//! `Nr k + 1` blocks; the export dispatches on `k` to the function's const
//! generic `k`, after checking `Key k` ([`super::check_key_size`]).

use super::{array, check_key_size, put, slice};
use crate::aes::aes_impl::{self, AESWord, Block};

/// Cryptol's `foreign verus_sub_bytes : Block -> Block`
/// (Cipher.cry's `SubBytes`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_sub_bytes(bs: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    aes_impl::sub_bytes(&mut state);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_inv_sub_bytes : Block -> Block`
/// (Cipher.cry's `InvSubBytes`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_inv_sub_bytes(bs: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    aes_impl::inv_sub_bytes(&mut state);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_shift_rows : Block -> Block`
/// (Cipher.cry's `ShiftRows`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_shift_rows(bs: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    aes_impl::shift_rows(&mut state);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_inv_shift_rows : Block -> Block`
/// (Cipher.cry's `InvShiftRows`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_inv_shift_rows(bs: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    aes_impl::inv_shift_rows(&mut state);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_mix_columns : Block -> Block`
/// (Cipher.cry's `MixColumns`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_mix_columns(bs: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    aes_impl::mix_columns(&mut state);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_inv_mix_columns : Block -> Block`
/// (Cipher.cry's `InvMixColumns`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_inv_mix_columns(bs: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    aes_impl::inv_mix_columns(&mut state);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_mix_column : AESWord -> AESWord`
/// (Cipher.cry's `MixColumnsStep`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_mix_column(s: *const u8, output: *mut u8) {
    let s: AESWord = unsafe { array(s) };
    unsafe { put(output, aes_impl::mix_column(s)) }
}

/// Cryptol's `foreign verus_inv_mix_column : AESWord -> AESWord`
/// (Cipher.cry's `InvMixColumnsStep`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_inv_mix_column(s: *const u8, output: *mut u8) {
    let s: AESWord = unsafe { array(s) };
    unsafe { put(output, aes_impl::inv_mix_column(s)) }
}

/// Cryptol's `foreign verus_add_round_key : Block -> Block -> Block`
/// (Cipher.cry's `AddRoundKey`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_add_round_key(bs: *const u8, key: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    let key: Block = unsafe { array(key) };
    aes_impl::add_round_key(&mut state, &key);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_round : Block -> Block -> Block`
/// (Cipher.cry's `Round`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_round(bs: *const u8, key: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    let key: Block = unsafe { array(key) };
    aes_impl::round(&mut state, &key);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_inv_round : Block -> Block -> Block`
/// (Cipher.cry's `InvRound`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_inv_round(bs: *const u8, key: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    let key: Block = unsafe { array(key) };
    aes_impl::inv_round(&mut state, &key);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_inv_round_prime : Block -> Block -> Block`
/// (Cipher.cry's `InvRound'`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_inv_round_prime(bs: *const u8, key: *const u8, output: *mut u8) {
    let mut state: Block = unsafe { array(bs) };
    let key: Block = unsafe { array(key) };
    aes_impl::inv_round_prime(&mut state, &key);
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_encrypt_block : {k} (Key k) => [Nr k + 1]Block ->
/// Block -> Block` (Cipher.cry's `Cipher`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_encrypt_block(k: usize, w: *const u8, input: *const u8, output: *mut u8) {
    check_key_size(k);
    let w: &[Block] = unsafe { slice(w.cast::<Block>(), k / 32 + 7) };
    let mut state: Block = unsafe { array(input) };
    match k {
        128 => aes_impl::encrypt_block::<128>(w, &mut state),
        192 => aes_impl::encrypt_block::<192>(w, &mut state),
        256 => aes_impl::encrypt_block::<256>(w, &mut state),
        _ => unreachable!(),
    }
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_decrypt_block : {k} (Key k) => [Nr k + 1]Block ->
/// Block -> Block` (Cipher.cry's `InvCipher`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_decrypt_block(k: usize, w: *const u8, input: *const u8, output: *mut u8) {
    check_key_size(k);
    let w: &[Block] = unsafe { slice(w.cast::<Block>(), k / 32 + 7) };
    let mut state: Block = unsafe { array(input) };
    match k {
        128 => aes_impl::decrypt_block::<128>(w, &mut state),
        192 => aes_impl::decrypt_block::<192>(w, &mut state),
        256 => aes_impl::decrypt_block::<256>(w, &mut state),
        _ => unreachable!(),
    }
    unsafe { put(output, state) }
}

/// Cryptol's `foreign verus_decrypt_block_prime : {k} (Key k) => [Nr k + 1]Block ->
/// Block -> Block` (Cipher.cry's `InvCipher'`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_decrypt_block_prime(k: usize, w: *const u8, input: *const u8, output: *mut u8) {
    check_key_size(k);
    let w: &[Block] = unsafe { slice(w.cast::<Block>(), k / 32 + 7) };
    let mut state: Block = unsafe { array(input) };
    match k {
        128 => aes_impl::decrypt_block_prime::<128>(w, &mut state),
        192 => aes_impl::decrypt_block_prime::<192>(w, &mut state),
        256 => aes_impl::decrypt_block_prime::<256>(w, &mut state),
        _ => unreachable!(),
    }
    unsafe { put(output, state) }
}
