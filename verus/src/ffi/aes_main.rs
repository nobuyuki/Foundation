//! Main.cry's ``AES`{k}.Encrypt`` and ``Decrypt``, over bytes, as the
//! executable [`main::encrypt`] and [`main::decrypt`], for
//! verus/cryptol/Verus/AES/Main.cry. The SPARK crate's `FFI.AES_Main` and
//! its exports (the spec layer's, which join the bytes into its bits) and
//! `FFI.AES_Impl`'s `spark_Impl_Encrypt` and `spark_Impl_Decrypt`.
//!
//! Cryptol cannot pass Main.cry's `[k]` key and `[128]` block, so the
//! Cryptol module splits them into `[k / 8][8]` and `[16][8]` and joins the
//! result; these functions take and give bytes, as `encrypt` and `decrypt`
//! do, and are proved equal on the bits to Main.cry's.

use super::{array, check_key_size, put, slice};
use crate::aes::aes_impl::{Block, main};

/// Cryptol's `foreign verus_encrypt : {k} (Key k) => [k / 8][8] ->
/// [16][8] -> [16][8]`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_encrypt(k: usize, key: *const u8, input: *const u8, output: *mut u8) {
    check_key_size(k);
    let key: &[u8] = unsafe { slice(key, k / 8) };
    let input: Block = unsafe { array(input) };
    let r = match k {
        128 => main::encrypt::<128>(key, input),
        192 => main::encrypt::<192>(key, input),
        256 => main::encrypt::<256>(key, input),
        _ => unreachable!(),
    };
    unsafe { put(output, r) }
}

/// Cryptol's `foreign verus_decrypt : {k} (Key k) => [k / 8][8] ->
/// [16][8] -> [16][8]`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_decrypt(k: usize, key: *const u8, input: *const u8, output: *mut u8) {
    check_key_size(k);
    let key: &[u8] = unsafe { slice(key, k / 8) };
    let input: Block = unsafe { array(input) };
    let r = match k {
        128 => main::decrypt::<128>(key, input),
        192 => main::decrypt::<192>(key, input),
        256 => main::decrypt::<256>(key, input),
        _ => unreachable!(),
    };
    unsafe { put(output, r) }
}
