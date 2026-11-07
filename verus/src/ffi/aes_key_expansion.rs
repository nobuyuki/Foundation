//! KeyExpansion.cry's `RotWord`, `SubWord`, `Rcon` and `KeyExpansion`, as
//! the executable functions of [`aes_impl`], for
//! verus/cryptol/Verus/AES/KeyExpansion.cry. The SPARK crate's
//! `FFI.AES_KeyExpansion` and its exports (the spec layer's) and
//! `FFI.AES_Impl`'s `spark_Expand_Key`.

use super::{array, check_key_size, put, slice};
use crate::aes::aes_impl::{self, AESWord, Block};

/// Cryptol's `foreign verus_rot_word : AESWord -> AESWord`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_rot_word(a: *const u8, output: *mut u8) {
    let a: AESWord = unsafe { array(a) };
    unsafe { put(output, aes_impl::rot_word(a)) }
}

/// Cryptol's `foreign verus_sub_word : AESWord -> AESWord`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_sub_word(a: *const u8, output: *mut u8) {
    let a: AESWord = unsafe { array(a) };
    unsafe { put(output, aes_impl::sub_word(a)) }
}

/// Cryptol's `foreign verus_rcon : [8] -> AESWord`: KeyExpansion.cry's
/// `Rcon @ i`, at the indices 1 .. 10 that `KeyExpansion` reads (`rcon`'s
/// precondition, checked; Cryptol's element 0 is undefined).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_rcon(i: u8, output: *mut u8) {
    assert!((1..=10).contains(&i), "Rcon is read at 1 .. 10 only");
    unsafe { put(output, aes_impl::rcon(i as usize)) }
}

/// Cryptol's `foreign verus_expand_key : {k} (Key k) => [Nk k]AESWord ->
/// [Nr k + 1]Block`: the key's `Nk k` words in, the first `Nr k + 1` of
/// `expand_key`'s 15 blocks out.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_expand_key(k: usize, key: *const u8, output: *mut u8) {
    check_key_size(k);
    let n = k / 32 + 7;
    let key: &[AESWord] = unsafe { slice(key.cast::<AESWord>(), k / 32) };
    let ws: [Block; 15] = match k {
        128 => aes_impl::expand_key::<128>(key),
        192 => aes_impl::expand_key::<192>(key),
        256 => aes_impl::expand_key::<256>(key),
        _ => unreachable!(),
    };
    let out: &mut [Block] = unsafe { core::slice::from_raw_parts_mut(output.cast::<Block>(), n) };
    out.copy_from_slice(&ws[..n]);
}
