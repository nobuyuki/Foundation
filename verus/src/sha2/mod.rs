//! SHA-256 (FIPS 180-4): spec layer, one-shot and streaming implementations.
//!
//! The spec layer is one module per Cryptol module of algorithms/SHA2/, as
//! in the SPARK crate (spark/src/sha2/): [`notation`] (Notation.cry),
//! [`functions`] (Functions.cry), [`preprocessing`] (Preprocessing.cry),
//! [`main`] (the parameterized Main.cry, as a trait of its parameters and
//! spec functions generic over it) and [`sha256`] (SHA256.cry, the
//! instance). The implementation layer is [`sha256_stream`], proved equal
//! to the spec through the byte-level refinement [`sha256_bytes`] and the
//! block folds of [`sha256_blocks`], as in the SPARK crate.

pub mod notation;
pub mod functions;
pub mod preprocessing;
pub mod main;
pub mod sha256;
pub mod sha256_bytes;
pub mod sha256_blocks;
pub mod sha256_stream;
