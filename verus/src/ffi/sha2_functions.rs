//! Functions.cry's SHA-256 functions and `K_256`, as their executable
//! copies in [`functions::exec`], for
//! verus/cryptol/Verus/SHA2/Functions.cry. The SPARK crate's
//! `FFI.SHA2_Functions` and its exports, which export the spec layer's.

use super::put;
use crate::sha2::functions::exec as functions;

/// Cryptol's `foreign verus_Ch : [32] -> [32] -> [32] -> [32]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_Ch(x: u32, y: u32, z: u32) -> u32 {
    functions::Ch(x, y, z)
}

/// Cryptol's `foreign verus_Maj : [32] -> [32] -> [32] -> [32]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_Maj(x: u32, y: u32, z: u32) -> u32 {
    functions::Maj(x, y, z)
}

/// Cryptol's `foreign verus_SIGMA_256_0 : [32] -> [32]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_SIGMA_256_0(x: u32) -> u32 {
    functions::SIGMA_256_0(x)
}

/// Cryptol's `foreign verus_SIGMA_256_1 : [32] -> [32]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_SIGMA_256_1(x: u32) -> u32 {
    functions::SIGMA_256_1(x)
}

/// Cryptol's `foreign verus_sigma_256_0 : [32] -> [32]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_sigma_256_0(x: u32) -> u32 {
    functions::sigma_256_0(x)
}

/// Cryptol's `foreign verus_sigma_256_1 : [32] -> [32]`.
#[unsafe(no_mangle)]
pub extern "C" fn verus_sigma_256_1(x: u32) -> u32 {
    functions::sigma_256_1(x)
}

/// Cryptol's `foreign verus_K_256 : () -> [64][32]`: the executable
/// constant, proved equal to the spec's `K_256`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_K_256(output: *mut u32) {
    unsafe { put(output, functions::K_256) }
}
