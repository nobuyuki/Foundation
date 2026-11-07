//! SBox.cry's tables `SBox` and `InvSBox`, read at a byte, as the
//! executable [`aes_impl::sub_byte`] and [`aes_impl::inv_sub_byte`], for
//! verus/cryptol/Verus/AES/SBox.cry. The SPARK crate's `FFI.AES_SBox` and
//! its exports, which read the spec layer's tables.

use crate::aes::aes_impl;

/// Cryptol's `foreign verus_sub_byte : [8] -> [8]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_sub_byte(b: u8) -> u8 {
    aes_impl::sub_byte(b)
}

/// Cryptol's `foreign verus_inv_sub_byte : [8] -> [8]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_inv_sub_byte(b: u8) -> u8 {
    aes_impl::inv_sub_byte(b)
}
