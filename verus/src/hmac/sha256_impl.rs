//! The executable HMAC-SHA-256 [FIPS-PUB-198-1 Section 4], over bytes,
//! proved equal to the spec layer's `HMAC` at [`super::sha256::SHA256`]
//! (algorithms/HMAC/Main.cry's `HMAC`, instantiated by packaging/Hash.cry
//! at SHA-256) on the bits of its key, text and MAC, as the SPARK crate's
//! `HMAC.SHA256_Impl` (spark/src/hmac/foundation_spark-hmac-sha256_impl.ads).
//! This is a representation change (bytes for bits, streaming for
//! whole-message hashing), so it is not part of the spec layer, which
//! mirrors the Cryptol.
//!
//! The MAC is computed with the streaming SHA-256
//! ([`crate::sha2::sha256_stream`]) as FIPS 198-1 describes it: the key is
//! brought to one 64-byte block K0 ([`init_key`], Steps 1 to 3), an inner
//! context hashes K0 xor ipad and then the text (Steps 4 to 6), and an
//! outer context hashes K0 xor opad and then the inner digest (Steps 7 to
//! 9). The text is never copied: the inner context consumes it in place.
//!
//! [`hmac_sha256`] is the one-shot MAC. [`init`], [`update`] and
//! [`finalize`] are the incremental interface, with the lemmas
//! [`lemma_update`] and [`lemma_final`] carrying the key and the text to
//! the spec, as `sha256_stream`'s do: a context does not hold its key or
//! text. (SPARK's `Final` is `finalize`, as in `sha256_stream`.)
//!
//! The proof composes the streaming theorems of `sha256_stream`
//! (`lemma_update`, `lemma_final`: the contexts compute `hash_bytes` of
//! what they were fed), [`sha256_bytes::lemma_hash_bytes`] (`hash_bytes`
//! is the spec's `hash` on the bits), and lemmas here on the bits of
//! concatenations, pads and xors ([`lemma_hmac`]).
//!
//! What differs from the SPARK crate, and why:
//! - Executable code cannot appear in specifications, so K0 and K0 xor a
//!   pad, which the SPARK crate's contracts write as calls of its
//!   `Init_Key` and `Xor_Pad`, are the spec functions [`K0`] and
//!   [`xor_pad`]; `init_key` and [`exec::xor_pad`] are proved to compute
//!   them. [`lemma_K0`] is `Init_Key`'s postcondition on the bits.
//! - A byte sequence is a `Seq<u8>` from 0 either way, so the SPARK crate's
//!   `To_Bytes` has no counterpart.
//! - The SPARK crate's extensionality lemmas (`Lemma_Word_Of_Ext`,
//!   `Lemma_Parse_Block_Ext`, `Lemma_Hash_Ext`, `Lemma_Join_Ext`,
//!   `Lemma_Digest_Bits`, `Lemma_Bits_Trans`) have no counterpart: Ada's
//!   array `=` is not the provers' equality, while `Seq` equality is.
//!   Nor has `Lemma_Prefix_Extends`, which states a step apart only to
//!   keep a prover within its time; here [`lemma_update`] takes the text
//!   after `data` as `M + data`, as `sha256_stream::lemma_update` does.
//! - `Lemma_Bits_Of_Append` and `Lemma_Message_Bits` are one lemma,
//!   [`lemma_bits_of_append`], stated for any two byte sequences.
//! - [`finished`] says that the inner context has a digest: the SPARK
//!   crate writes it as a call of `SHA256_Stream.Final`, which is
//!   executable.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::cryptol::{bit_sequences, join_split, words};
#[cfg(verus_only)]
use crate::sha2::main::hash;
use crate::sha2::sha256_stream;
#[cfg(verus_only)]
use crate::sha2::sha256_bytes::{self, Max_Bytes, bits_of, byte_bit, hash_bytes, lemma_div_mod_8};
#[cfg(verus_only)]
use super::main::{HMAC, HMAC_init, Parameters, ipad, opad};
#[cfg(verus_only)]
use super::sha256::{SHA256, lemma_hash_len};
#[cfg(verus_only)]
use super::{join, repeat, zero};

verus! {

/// The bound on a text's length in bytes: a text has fewer than
/// `Max_Text()` bytes. It is Main.cry's `n < 2 ^^ B - 8 * B` (Main.cry:31)
/// at `B = 64`, in bytes, and also what keeps the inner hash's message
/// (`64 + n` bytes) below SHA-256's `Max_Bytes` (`2 ^^ 61`).
pub open spec fn Max_Text() -> nat {
    (Max_Bytes() - 64) as nat
}

/// `count` zero bytes.
pub open spec fn zeros(count: nat) -> Seq<u8> {
    Seq::new(count, |i: int| 0u8)
}

/// K0, the key brought to SHA-256's block size `B = 64` bytes [FIPS-PUB-198-1
/// Section 4, Steps 1 to 3], over bytes: a key longer than 64 bytes is
/// hashed and its 32-byte digest padded with zeros; a key of 64 bytes or
/// fewer is padded with zeros. What [`init_key`] computes, and on the bits
/// the spec's `HMAC_init` ([`lemma_K0`]).
pub open spec fn K0(key: Seq<u8>) -> Seq<u8> {
    if key.len() > 64 {
        hash_bytes(key) + zeros(32)
    } else {
        key + zeros((64 - key.len()) as nat)
    }
}

/// K0 xor a pad: every byte of `k0` xored with `x` (0x36 for ipad, 0x5C for
/// opad). What [`exec::xor_pad`] computes.
pub open spec fn xor_pad(k0: Seq<u8>, x: u8) -> Seq<u8> {
    Seq::new(k0.len(), |j: int| k0[j] ^ x)
}

/// What the inner hash absorbs for `key` and the text `M`: K0 xor ipad,
/// then `M`.
pub open spec fn inner_prefix(key: Seq<u8>, M: Seq<u8>) -> Seq<u8> {
    xor_pad(K0(key), 0x36) + M
}

/// The executable pieces whose spec functions are named alike.
pub mod exec {
    #[allow(unused_imports)]
    use vstd::prelude::*;

    verus! {

    /// K0 xor a pad: every byte of `k0` xored with `x`.
    pub fn xor_pad(k0: &[u8; 64], x: u8) -> (p: [u8; 64])
        ensures
            p@ == super::xor_pad(k0@, x),
    {
        let mut p = [0u8; 64];
        let mut j: usize = 0;
        while j < 64
            invariant
                j <= 64,
                forall|j2: int| 0 <= j2 < j ==> #[trigger] p[j2] == k0[j2] ^ x,
            decreases 64 - j,
        {
            p[j] = k0[j] ^ x;
            j += 1;
        }
        assert(p@ =~= super::xor_pad(k0@, x));
        p
    }

    } // verus!
}

/// The key preprocessing, Steps 1 to 3 of [FIPS-PUB-198-1 Section 4]: a
/// key of 64 bytes is K0 as it is, a longer key is hashed with SHA-256 and
/// its 32-byte digest padded with zeros, and a shorter key is padded with
/// zeros. Proved equal, on the bits, to the spec's `HMAC_init`
/// (Main.cry:56).
pub fn init_key(key: &[u8]) -> (k0: [u8; 64])
    requires
        key@.len() < Max_Bytes(),
    ensures
        k0@ == K0(key@),
        bits_of(k0@) == HMAC_init::<SHA256>(key@),
{
    let mut k0 = [0u8; 64];
    let len = key.len();
    if len > 64 {
        let d = sha256_stream::hash(key);
        let mut j: usize = 0;
        while j < 32
            invariant
                j <= 32,
                forall|j2: int| 0 <= j2 < j ==> #[trigger] k0[j2] == d[j2],
                forall|j2: int| j <= j2 < 64 ==> #[trigger] k0[j2] == 0,
            decreases 32 - j,
        {
            k0[j] = d[j];
            j += 1;
        }
        assert(k0@ =~= K0(key@));
    } else {
        let mut j: usize = 0;
        while j < len
            invariant
                len == key@.len() <= 64,
                j <= len,
                forall|j2: int| 0 <= j2 < j ==> #[trigger] k0[j2] == key@[j2],
                forall|j2: int| j <= j2 < 64 ==> #[trigger] k0[j2] == 0,
            decreases len - j,
        {
            k0[j] = key[j];
            j += 1;
        }
        assert(k0@ =~= K0(key@));
    }
    proof {
        lemma_K0(key@);
    }
    k0
}

/// An HMAC-SHA-256 computation in progress: the inner SHA-256 context,
/// fed K0 xor ipad and the text so far, and K0 xor opad for `finalize`.
pub struct Context {
    /// The inner hash, fed K0 xor ipad and then the text.
    inner: sha256_stream::Context,
    /// K0 xor opad.
    o_pad: [u8; 64],
}

/// The number of bytes the inner hash has absorbed: the 64 of K0 xor ipad,
/// and then the text's.
pub closed spec fn count(c: Context) -> nat {
    sha256_stream::count(c.inner)
}

/// Whether `c` is HMAC-SHA-256 under `key` after the text `M`: its inner
/// hash has absorbed K0 xor ipad and then `M`, and it holds K0 xor opad.
pub closed spec fn models(c: Context, key: Seq<u8>, M: Seq<u8>) -> bool {
    &&& M.len() < Max_Text()
    &&& sha256_stream::models(c.inner, inner_prefix(key, M))
    &&& c.o_pad@ == xor_pad(K0(key), 0x5C)
}

/// Whether `c1` is `c0` after the bytes `data`.
pub closed spec fn absorbed(c0: Context, data: Seq<u8>, c1: Context) -> bool {
    &&& sha256_stream::absorbed(c0.inner, data, c1.inner)
    &&& c1.o_pad == c0.o_pad
}

/// Whether `d` is the outer hash of `c`: SHA-256 of `c`'s K0 xor opad
/// followed by the digest of `c`'s inner context.
pub closed spec fn finished(c: Context, d: Seq<u8>) -> bool {
    exists|inner: Seq<u8>| #[trigger]
        sha256_stream::finished(c.inner, inner) && d == hash_bytes(c.o_pad@ + inner)
}

/// Starts HMAC-SHA-256 under `key`: K0 ([`init_key`]), and an inner
/// SHA-256 context fed K0 xor ipad.
pub fn init(key: &[u8]) -> (c: Context)
    requires
        key@.len() < Max_Bytes(),
    ensures
        models(c, key@, Seq::empty()),
        count(c) == 64,
{
    let k0 = init_key(key);
    let i_pad = exec::xor_pad(&k0, 0x36);
    let o_pad = exec::xor_pad(&k0, 0x5C);
    let mut inner = sha256_stream::init();
    let ghost c0 = inner;
    sha256_stream::update(&mut inner, &i_pad);
    proof {
        sha256_stream::lemma_update(c0, i_pad@, inner, Seq::empty());
        assert(Seq::<u8>::empty() + i_pad@ =~= inner_prefix(key@, Seq::empty()));
    }
    Context { inner, o_pad }
}

/// Absorbs the next bytes of the text.
pub fn update(c: &mut Context, data: &[u8])
    requires
        count(*old(c)) < Max_Bytes(),
        data@.len() < Max_Bytes() - count(*old(c)),
    ensures
        absorbed(*old(c), data@, *final(c)),
        count(*final(c)) == count(*old(c)) + data@.len(),
{
    sha256_stream::update(&mut c.inner, data);
}

/// The MAC of the text absorbed so far: the outer SHA-256 of K0 xor opad
/// and the inner digest. `c` is not changed.
pub fn finalize(c: &Context) -> (d: [u8; 32])
    requires
        count(*c) < Max_Bytes(),
    ensures
        finished(*c, d@),
{
    let inner = sha256_stream::finalize(&c.inner);
    let ghost M_out = c.o_pad@ + inner@;
    let mut o = sha256_stream::init();
    let ghost o0 = o;
    sha256_stream::update(&mut o, &c.o_pad);
    proof {
        sha256_stream::lemma_update(o0, c.o_pad@, o, Seq::empty());
        assert(Seq::<u8>::empty() + c.o_pad@ =~= c.o_pad@);
    }
    let ghost o1 = o;
    sha256_stream::update(&mut o, &inner);
    proof {
        sha256_stream::lemma_update(o1, inner@, o, c.o_pad@);
        sha256_stream::lemma_final(o, M_out);
    }
    let d = sha256_stream::finalize(&o);
    assert(sha256_stream::finished(c.inner, inner@));
    d
}

/// `update` extends the text: a context for `M`, after `data`, is one for
/// `M + data`.
pub proof fn lemma_update(c0: Context, data: Seq<u8>, c1: Context, key: Seq<u8>, M: Seq<u8>)
    requires
        (M + data).len() < Max_Text(),
        models(c0, key, M),
        absorbed(c0, data, c1),
    ensures
        models(c1, key, M + data),
{
    sha256_stream::lemma_update(c0.inner, data, c1.inner, inner_prefix(key, M));
    assert(inner_prefix(key, M) + data =~= inner_prefix(key, M + data));
}

/// `finalize` of a context for `key` and `M` is the spec's `HMAC` of them,
/// on the bits, at `λ = 256`.
pub proof fn lemma_final(c: Context, key: Seq<u8>, M: Seq<u8>)
    requires
        key.len() < Max_Bytes(),
        models(c, key, M),
    ensures
        M.len() < Max_Text(),
        count(c) < Max_Bytes(),
        forall|d: Seq<u8>| #[trigger]
            finished(c, d) ==> bits_of(d) == HMAC::<SHA256>(key, bits_of(M), 256),
{
    sha256_stream::lemma_final(c.inner, inner_prefix(key, M));
    assert forall|d: Seq<u8>| #[trigger] finished(c, d) implies bits_of(d) == HMAC::<SHA256>(
        key,
        bits_of(M),
        256,
    ) by {
        let inner = choose|inner: Seq<u8>|
            #[trigger] sha256_stream::finished(c.inner, inner) && d == hash_bytes(c.o_pad@ + inner);
        lemma_hmac(key, M);
    }
}

/// HMAC-SHA-256 [FIPS-PUB-198-1 Section 4] with the full 256-bit MAC,
/// through two streaming SHA-256 contexts: the inner one hashes K0 xor
/// ipad and then `text`, the outer one K0 xor opad and then the inner
/// digest. Proved equal, on the bits, to the spec's `HMAC` (Main.cry:40)
/// at `λ = 256`, packaging/Hash.cry's `HMAC` (Hash.cry:71) at SHA-256.
pub fn hmac_sha256(key: &[u8], text: &[u8]) -> (d: [u8; 32])
    requires
        key@.len() < Max_Bytes(),
        text@.len() < Max_Text(),
    ensures
        bits_of(d@) == HMAC::<SHA256>(key@, bits_of(text@), 256),
{
    let mut c = init(key);
    let ghost c0 = c;
    update(&mut c, text);
    proof {
        lemma_update(c0, text@, c, key@, Seq::empty());
        assert(Seq::<u8>::empty() + text@ =~= text@);
        lemma_final(c, key@, text@);
    }
    finalize(&c)
}

// ---------------------------------------------------------------------
// Lemmas on the bits.
// ---------------------------------------------------------------------

/// The bits of `a + b` are `a`'s bits followed by `b`'s.
pub proof fn lemma_bits_of_append(a: Seq<u8>, b: Seq<u8>)
    ensures
        bits_of(a + b) == bits_of(a) + bits_of(b),
{
    assert forall|i: int| 0 <= i < 8 * (a.len() + b.len()) implies #[trigger] bits_of(a + b)[i] == (
    bits_of(a) + bits_of(b))[i] by {
        let q = i / 8;
        let t = i % 8;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 8);
        if i >= 8 * a.len() {
            let i2 = i - 8 * a.len();
            assert(i2 == 8 * (q - a.len()) + t);
            lemma_div_mod_8(q - a.len(), t);
        }
    }
    assert(bits_of(a + b) =~= bits_of(a) + bits_of(b));
}

/// The bits of `count` zero bytes are `count * 8` zero bits.
pub proof fn lemma_bits_zeros(count: nat)
    ensures
        bits_of(zeros(count)) == zero(8 * count),
{
    assert forall|i: int| 0 <= i < 8 * count implies #[trigger] bits_of(zeros(count))[i] == zero(
        8 * count,
    )[i] by {
        let t = (i % 8) as u8;
        assert(t < 8);
        assert((0u8 >> (7 - t) as u8) & 1 != 1) by (bit_vector)
            requires
                t < 8,
        ;
    }
    assert(bits_of(zeros(count)) =~= zero(8 * count));
}

/// The prelude's bit of a byte, `x @ j` on `[8]`, is `sha256_bytes`'s
/// [`byte_bit`].
pub proof fn lemma_byte_bit(x: u8, j: int)
    requires
        0 <= j < 8,
    ensures
        words::bit::<u8>(x, j) == byte_bit(x, j),
{
}

/// The spec's `join` of a key's bytes is `sha256_bytes`'s `bits_of` of them.
pub proof fn lemma_join_bits(K: Seq<u8>)
    ensures
        join(K) == bits_of(K),
{
    assert forall|i: int| 0 <= i < 8 * K.len() implies #[trigger] join(K)[i] == bits_of(K)[i] by {
        lemma_byte_bit(K[i / 8], i % 8);
    }
    assert(join(K) =~= bits_of(K));
}

/// K0 on the bits is the spec's `HMAC_init` (Main.cry:56): the three cases
/// of the Cryptol, through `lemma_hash_bytes` for a long key.
pub proof fn lemma_K0(key: Seq<u8>)
    requires
        key.len() < Max_Bytes(),
    ensures
        K0(key).len() == 64,
        bits_of(K0(key)) == HMAC_init::<SHA256>(key),
{
    lemma_join_bits(key);
    if key.len() > 64 {
        sha256_bytes::lemma_hash_bytes(key);
        lemma_hash_len(bits_of(key));
        lemma_bits_of_append(hash_bytes(key), zeros(32));
        lemma_bits_zeros(32);
        assert(bits_of(hash_bytes(key)).len() == 256);
    } else {
        lemma_bits_of_append(key, zeros((64 - key.len()) as nat));
        lemma_bits_zeros((64 - key.len()) as nat);
        if key.len() == 64 {
            assert(zero(0) =~= Seq::<bool>::empty());
            assert(bits_of(key) + Seq::<bool>::empty() =~= bits_of(key));
        }
    }
}

/// A bit of a xor is the xor of the bits.
pub proof fn lemma_byte_bit_xor(a: u8, b: u8, j: int)
    requires
        0 <= j < 8,
    ensures
        byte_bit(a ^ b, j) == (byte_bit(a, j) != byte_bit(b, j)),
{
    let s = (7 - j) as u8;
    assert(((a ^ b) >> s) & 1 == 1 <==> (((a >> s) & 1 == 1) != ((b >> s) & 1 == 1)))
        by (bit_vector);
}

/// The bits of the spec's pads, `join (repeat`{64} x)`: bit `i` is bit
/// `i % 8` of `x`.
pub proof fn lemma_pad_bits(x: u8)
    ensures
        join(repeat(64, x)).len() == 512,
        forall|i: int| 0 <= i < 512 ==> #[trigger] join(repeat(64, x))[i] == byte_bit(x, i % 8),
{
    assert forall|i: int| 0 <= i < 512 implies #[trigger] join(repeat(64, x))[i] == byte_bit(
        x,
        i % 8,
    ) by {
        lemma_byte_bit(x, i % 8);
    }
}

/// The bits of K0 xor a pad, K0 xor ipad or K0 xor opad, are the spec's
/// `K0 ^ ipad` or `K0 ^ opad` (Main.cry:42 and :43), when K0's bits are
/// `HMAC_init` and the pad is `join (repeat`{64} x)`.
pub proof fn lemma_pad_xor_bits(k0: Seq<u8>, x: u8)
    requires
        k0.len() == 64,
    ensures
        bits_of(xor_pad(k0, x)) == bit_sequences::xor(bits_of(k0), join(repeat(64, x))),
{
    lemma_pad_bits(x);
    let P = xor_pad(k0, x);
    assert forall|i: int| 0 <= i < 512 implies #[trigger] bits_of(P)[i] == bit_sequences::xor(
        bits_of(k0),
        join(repeat(64, x)),
    )[i] by {
        lemma_byte_bit_xor(k0[i / 8], x, i % 8);
    }
    assert(bits_of(P) =~= bit_sequences::xor(bits_of(k0), join(repeat(64, x))));
}

/// The inner hash's message in the spec, `(K0 ^ ipad) # text`
/// (Main.cry:43).
pub open spec fn inner_message(K: Seq<u8>, T: Seq<bool>) -> Seq<bool> {
    bit_sequences::xor(HMAC_init::<SHA256>(K), ipad::<SHA256>()) + T
}

/// The outer hash's message in the spec, `(K0 ^ opad) # Hn (...)`
/// (Main.cry:42).
pub open spec fn outer_message(K: Seq<u8>, T: Seq<bool>) -> Seq<bool> {
    bit_sequences::xor(HMAC_init::<SHA256>(K), opad::<SHA256>()) + hash::<
        crate::sha2::sha256::SHA256,
    >(inner_message(K, T))
}

/// The spec's `HMAC` at `λ = 256` unfolded, with `Hk`, `Hn` and `HL` the
/// SHA-256 hash, as [`SHA256`] instantiates them: the first 256 bits are
/// the whole outer digest.
pub proof fn lemma_hmac_unfold(K: Seq<u8>, T: Seq<bool>)
    ensures
        HMAC::<SHA256>(K, T, 256) == hash::<crate::sha2::sha256::SHA256>(outer_message(K, T)),
{
    let H = hash::<crate::sha2::sha256::SHA256>(outer_message(K, T));
    lemma_hash_len(outer_message(K, T));
    assert(H.take(256) =~= H);
}

/// The bits of the two streams' messages are the spec's: K0 xor ipad then
/// `text` is, on the bits, `(K0 ^ ipad) # text`, and K0 xor opad then the
/// inner digest is `(K0 ^ opad) # Hn (...)`. So the outer digest is, on
/// the bits, the spec's `HMAC` at `λ = 256`.
pub proof fn lemma_hmac(key: Seq<u8>, text: Seq<u8>)
    requires
        key.len() < Max_Bytes(),
        text.len() < Max_Text(),
    ensures
        bits_of(hash_bytes(xor_pad(K0(key), 0x5C) + hash_bytes(inner_prefix(key, text))))
            == HMAC::<SHA256>(key, bits_of(text), 256),
{
    let k0 = K0(key);
    let T = bits_of(text);
    let M_in = inner_prefix(key, text);
    let inner = hash_bytes(M_in);
    let M_out = xor_pad(k0, 0x5C) + inner;
    lemma_K0(key);
    lemma_pad_xor_bits(k0, 0x36);
    lemma_pad_xor_bits(k0, 0x5C);

    // The inner hash.
    lemma_bits_of_append(xor_pad(k0, 0x36), text);
    assert(bits_of(M_in) == inner_message(key, T));
    sha256_bytes::lemma_hash_bytes(M_in);

    // The outer hash.
    lemma_bits_of_append(xor_pad(k0, 0x5C), inner);
    assert(bits_of(M_out) == outer_message(key, T));
    sha256_bytes::lemma_hash_bytes(M_out);
    lemma_hmac_unfold(key, T);
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{finalize, hmac_sha256, init, update};
    use crate::sha2::sha256_stream::hash;

    /// Parse bytes written in hexadecimal.
    fn hex(s: &str) -> Vec<u8> {
        (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
    }

    /// HMAC-SHA-256 written as FIPS 198-1 states it, with the one-shot
    /// SHA-256 over concatenated byte vectors: the reference the tests
    /// compare against.
    fn reference(key: &[u8], text: &[u8]) -> [u8; 32] {
        let mut k0 = if key.len() > 64 { hash(key).to_vec() } else { key.to_vec() };
        k0.resize(64, 0);
        let mut m_in: Vec<u8> = k0.iter().map(|b| b ^ 0x36).collect();
        m_in.extend_from_slice(text);
        let mut m_out: Vec<u8> = k0.iter().map(|b| b ^ 0x5C).collect();
        m_out.extend_from_slice(&hash(&m_in));
        hash(&m_out)
    }

    /// RFC 4231's test cases 1 to 7 for HMAC-SHA-256. Case 5's MAC is
    /// truncated to 128 bits, so its first 16 bytes are compared.
    #[test]
    fn rfc_4231() {
        let cases: [(Vec<u8>, Vec<u8>, &str); 7] = [
            (
                vec![0x0b; 20],
                b"Hi There".to_vec(),
                "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
            ),
            (
                b"Jefe".to_vec(),
                b"what do ya want for nothing?".to_vec(),
                "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
            ),
            (
                vec![0xaa; 20],
                vec![0xdd; 50],
                "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe",
            ),
            (
                hex("0102030405060708090a0b0c0d0e0f10111213141516171819"),
                vec![0xcd; 50],
                "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b",
            ),
            (
                vec![0x0c; 20],
                b"Test With Truncation".to_vec(),
                "a3b6167473100ee06e0c796c2955552b",
            ),
            (
                vec![0xaa; 131],
                b"Test Using Larger Than Block-Size Key - Hash Key First".to_vec(),
                "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54",
            ),
            (
                vec![0xaa; 131],
                b"This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm.".to_vec(),
                "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2",
            ),
        ];
        for (n, (key, text, mac)) in cases.iter().enumerate() {
            let mac = hex(mac);
            assert_eq!(&hmac_sha256(key, text)[..mac.len()], &mac[..], "case {}", n + 1);
        }
    }

    /// Keys of every length from 0 to 150 bytes (each case of the key
    /// preprocessing) and texts of every length from 0 to 150, in one call
    /// and fed in two pieces: all agree with the reference.
    #[test]
    fn agrees_with_reference() {
        let m: Vec<u8> = (0..150u32).map(|i| (i * 7 + 3) as u8).collect();
        for k in 0..=150 {
            let key = &m[..k];
            let text = &m[150 - (k * 13) % 150..];
            assert_eq!(hmac_sha256(key, text), reference(key, text), "key {k}");
        }
        let key = &m[..20];
        for n in 0..=150 {
            let text = &m[..n];
            let whole = reference(key, text);
            assert_eq!(hmac_sha256(key, text), whole, "text {n}");
            for cut in [0, 1.min(n), n / 2, n] {
                let mut c = init(key);
                update(&mut c, &text[..cut]);
                update(&mut c, &text[cut..]);
                assert_eq!(finalize(&c), whole, "text {n}, cut {cut}");
            }
        }
    }
}
