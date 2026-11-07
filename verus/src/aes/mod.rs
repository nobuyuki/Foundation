//! AES (FIPS 197): spec layer, implementation and lemmas.
//!
//! The spec layer is one module per Cryptol module of algorithms/AES/, as
//! in the SPARK crate (spark/src/aes/): [`types`] (Types.cry), [`gf28`]
//! (GF28.cry), [`gf2`] (the part of shared/algebra/Polynomial/GF2.cry that
//! SBox.cry imports), [`sbox`] (SBox.cry), [`key_expansion`]
//! (KeyExpansion.cry), [`cipher`] (Cipher.cry) and [`main`] (Main.cry).
//! The `{k}` functions are generic in a const `k`, so the SPARK crate's
//! generic `AES_K`, its instances and `Spec.Dispatch` have no counterpart
//! ([`types`] says why).
//!
//! The properties that algorithms/AES states about itself are proved of
//! the spec layer in [`properties`], as the SPARK crate's
//! `AES.Spec.Properties`, `SBoxCorrect` entry by entry in
//! [`sbox_entries`] (its `AES.Spec.SBox.SBox_Entries`), with lemmas in
//! [`lemmas`] (its `AES.Lemmas`).
//!
//! The implementation layer is [`aes_impl`] (the SPARK crate's
//! `AES.Impl`: the key schedule, the round transformations and the block
//! ciphers in place, proved equal to the spec) and [`aes_impl::main`] (its
//! `AES.Impl.Main`: AES on key and block bytes, proved equal to Main.cry's
//! `Encrypt` and `Decrypt` on the bits), with [`main_lemmas`] (its
//! `AES.Main_Lemmas`).

pub mod types;
pub mod gf28;
pub mod gf2;
pub mod sbox;
pub mod key_expansion;
pub mod cipher;
pub mod main;
pub mod lemmas;
pub mod sbox_entries;
pub mod properties;
pub mod aes_impl;
pub mod main_lemmas;
