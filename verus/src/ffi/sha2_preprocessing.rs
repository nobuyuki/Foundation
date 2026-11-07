//! Preprocessing.cry's `H0_256`, and the parse of one block, as the
//! executable [`preprocessing::exec::H0_256`] and
//! [`sha256_stream::load_block`], for
//! verus/cryptol/Verus/SHA2/Preprocessing.cry. The SPARK crate's
//! `FFI.SHA2_Preprocessing` and its exports (the spec layer's `H0_256`,
//! `Pad` and `Parse`) and `FFI.SHA2_SHA256_Stream`'s `spark_Load_Block`.
//! `pad` and `parse` have no executable counterpart, so they are not
//! exported.

use super::{array, put};
use crate::sha2::{preprocessing, sha256_stream};

/// Cryptol's `foreign verus_H0_256 : () -> [8][32]`: the executable
/// constant, proved equal to the spec's `H0_256`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_H0_256(output: *mut u32) {
    unsafe { put(output, preprocessing::exec::H0_256) }
}

/// Cryptol's `foreign verus_load_block : [64][8] -> [16][32]`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verus_load_block(bytes: *const u8, output: *mut u32) {
    let b: [u8; 64] = unsafe { array(bytes) };
    unsafe { put(output, sha256_stream::load_block(&b, 0)) }
}
