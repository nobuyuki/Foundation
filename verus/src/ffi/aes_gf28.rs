//! GF28.cry's `xTimes` and `(•)`, as the executable [`aes_impl::x_times`]
//! and [`aes_impl::dot`], for verus/cryptol/Verus/AES/GF28.cry. The SPARK
//! crate's `FFI.AES_GF28` and its exports, which export the spec layer's
//! (and `FFI.AES_Impl`'s `spark_Impl_Dot`).

use crate::aes::aes_impl;

/// Cryptol's `foreign verus_x_times : [8] -> [8]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_x_times(b: u8) -> u8 {
    aes_impl::x_times(b)
}

/// Cryptol's `foreign verus_dot : [8] -> [8] -> [8]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_dot(b: u8, c: u8) -> u8 {
    aes_impl::dot(b, c)
}
