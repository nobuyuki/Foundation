//! SHA-256, the implementation layer [FIPS-PUB-180-4 Sections 5 and 6.2],
//! mirroring the SPARK crate's `SHA256_Stream`
//! (spark/src/sha2/foundation_spark-sha2-sha256_stream.ads): executable
//! code proved equal to the byte-level refinement
//! [`sha256_bytes::hash_bytes`], and through
//! [`sha256_bytes::lemma_hash_bytes`] to the spec layer's `hash`
//! (Main.cry:55) on the message's bits.
//!
//! [`compress`] is the compression function in place, proved equal to the
//! spec's `step` (Main.cry:67). [`hash`] is the one-shot hash. [`init`],
//! [`update`] and [`finalize`] are the streaming interface over a
//! [`Context`]: the hash value so far, a 64-byte buffer, and the number of
//! bytes consumed. (SPARK's `Final` is `finalize` here: `final` is a
//! reserved word in Rust.)
//!
//! What a context means. [`models`]`(c, M)` says that `c` is the context
//! after consuming exactly the bytes `M`: its count is `M`'s length, its
//! hash value is `step` folded from `H0` over `M`'s whole blocks, and its
//! buffer holds the bytes after them. `init` models the empty message.
//! `update`'s postcondition ([`absorbed`]) relates the new context to the
//! old one and the data, and [`lemma_update`] turns that into
//! `models(c, M + data)`. `finalize` pads the buffered bytes and compresses
//! the last one or two blocks, and [`lemma_final`] proves that its digest
//! is `hash_bytes(M)` whenever `models(c, M)`. So for any chunking of a
//! message, `finalize` after `init` and an `update` per chunk is
//! `hash_bytes` of the message, by induction on the chunks with `models` as
//! the invariant ([`hash_chunked`] states this for the chunks of one
//! slice).
//!
//! The lemmas take the message as an argument because a context does not
//! hold it, as in the SPARK crate. (Verus has ghost fields, so a context
//! could carry its message; the SPARK crate's shape is kept.)
//!
//! Nothing executable here calls spec code: `step`, `hash_bytes` and the
//! folds of [`super::sha256_blocks`] appear only in contracts, assertions
//! and lemmas.

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_only)]
use super::main::{self, W, foldl_step3, parse, step, step3};
#[cfg(verus_only)]
use super::preprocessing::H0_256;
#[cfg(verus_only)]
use super::sha256::SHA256;
#[cfg(verus_only)]
use super::sha256_blocks::{block_from, fold_blocks, lemma_block_ext, lemma_block_parse, lemma_fold_ext, lemma_fold_split, lemma_foldl_parse};
#[cfg(verus_only)]
use super::sha256_bytes::{self, Max_Bytes, bits_of, blocks, digest_bytes, hash_bytes, length_byte, pad_bytes, word_at, word_byte};
use super::functions::exec::{Ch, K_256, Maj, SIGMA_256_0, SIGMA_256_1, sigma_256_0, sigma_256_1};
use super::preprocessing::exec::H0_256 as H0_256_exec;

verus! {

/// The compression function, in place: `h` becomes Cryptol's `step h m` at
/// SHA-256's parameters (Main.cry:67). It computes the whole 64-word
/// schedule, then runs the 64 rounds, as the SPARK crate's `Compress` does.
pub fn compress(h: &mut [u32; 8], m: &[u32; 16])
    ensures
        final(h)@ == step::<SHA256>(old(h)@, m@),
{
    // Step 1: the message schedule. After word t, every word computed so
    // far is the spec's W.
    let mut sched = [0u32; 64];
    let mut t: usize = 0;
    while t < 64
        invariant
            t <= 64,
            forall|s: int| 0 <= s < t ==> sched[s] == W::<SHA256>(m@, s),
        decreases 64 - t,
    {
        if t < 16 {
            sched[t] = m[t];
        } else {
            sched[t] = sigma_256_1(sched[t - 2]).wrapping_add(sched[t - 7]).wrapping_add(
                sigma_256_0(sched[t - 15]),
            ).wrapping_add(sched[t - 16]);
        }
        t += 1;
    }

    // Steps 2 and 3: the rounds. After round t, the working variables are
    // the spec's fold of the first t rounds.
    let ghost h0 = h@;
    let mut v: [u32; 8] = *h;
    let mut t: usize = 0;
    while t < 64
        invariant
            t <= 64,
            h@ == h0,
            forall|s: int| 0 <= s < 64 ==> sched[s] == W::<SHA256>(m@, s),
            v@ == foldl_step3::<SHA256>(m@, h0, t as int),
        decreases 64 - t,
    {
        let ghost v0 = v@;
        let t1 = v[7].wrapping_add(SIGMA_256_1(v[4])).wrapping_add(Ch(v[4], v[5], v[6])).wrapping_add(
            K_256[t],
        ).wrapping_add(sched[t]);
        let t2 = SIGMA_256_0(v[0]).wrapping_add(Maj(v[0], v[1], v[2]));
        v = [t1.wrapping_add(t2), v[0], v[1], v[2], v[3].wrapping_add(t1), v[4], v[5], v[6]];
        assert(v@ =~= step3::<SHA256>(m@, v0, t as int));
        t += 1;
    }

    // Step 4: H + H'.
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            v@ == foldl_step3::<SHA256>(m@, h0, 64),
            forall|j: int| 0 <= j < i ==> #[trigger] h[j] == vstd::wrapping::u32_specs::wrapping_add(h0[j], v[j]),
            forall|j: int| i <= j < 8 ==> #[trigger] h[j] == h0[j],
        decreases 8 - i,
    {
        h[i] = h[i].wrapping_add(v[i]);
        i += 1;
    }
    assert(h@ =~= step::<SHA256>(h0, m@));
}

/// The 64 bytes of `b` from `f` as a message block, each word read
/// big-endian [FIPS-PUB-180-4 Sections 3.1 and 5.2.1]. It is the executable
/// `parse` (Preprocessing.cry:47), one block at a time: the block is the
/// spec's `parse` of the 64 bytes' bits, with `N = 1`
/// ([`lemma_block_parse`]). `update` and `finalize` parse each block with
/// it as they reach it, since a streaming hash never holds the whole padded
/// message that `parse` takes.
pub fn load_block(b: &[u8], f: usize) -> (r: [u32; 16])
    requires
        f + 64 <= b@.len(),
    ensures
        r@ == block_from(b@, f as int),
        r@ == parse::<SHA256>(bits_of(b@.subrange(f as int, f + 64)), 1)[0],
{
    let _n = b.len();
    let mut r = [0u32; 16];
    let mut j: usize = 0;
    while j < 16
        invariant
            j <= 16,
            f + 64 <= b@.len() == _n,
            forall|k: int| 0 <= k < j ==> r[k] == word_at(b@, f + 4 * k),
        decreases 16 - j,
    {
        let i = f + 4 * j;
        r[j] = 0x100_0000 * (b[i] as u32) + 0x1_0000 * (b[i + 1] as u32) + 0x100 * (b[i + 2] as u32)
            + (b[i + 3] as u32);
        j += 1;
    }
    proof {
        lemma_block_parse(b@, f as int);
    }
    assert(r@ =~= block_from(b@, f as int));
    r
}

/// A hash value written as 32 bytes, each word big-endian [FIPS-PUB-180-4
/// Section 6.2.2].
pub fn to_digest(h: &[u32; 8]) -> (d: [u8; 32])
    ensures
        d@ == digest_bytes(h@),
{
    let mut d = [0u8; 32];
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            forall|k: int| 0 <= k < i ==> d[k] == word_byte(h[k / 4], k % 4),
        decreases 32 - i,
    {
        let x = h[i / 4];
        let v = (x >> (24 - 8 * (i % 4)) as u32) & 0xff;
        assert(v <= 0xff) by (bit_vector)
            requires
                v == (x >> (24 - 8 * (i % 4)) as u32) & 0xff,
        ;
        d[i] = v as u8;
        i += 1;
    }
    assert(d@ =~= digest_bytes(h@));
    d
}

/// The state of a streaming SHA-256 computation: the hash value after the
/// whole blocks consumed, the bytes consumed since, and the number of bytes
/// consumed. [`models`] states its meaning.
pub struct Context {
    /// The hash value after the whole blocks consumed.
    h: [u32; 8],
    /// The bytes consumed since: the first `count % 64`.
    buf: [u8; 64],
    /// The number of bytes consumed.
    count: u64,
}

/// The number of bytes `c` has consumed.
pub closed spec fn count(c: Context) -> nat {
    c.count as nat
}

/// Whether `c` is the context after consuming exactly the bytes of `M`:
/// `M` has fewer than `Max_Bytes` bytes and `c` has counted them; `c`'s
/// hash value is `step` folded from `H0` over `M`'s `M.len() / 64` whole
/// blocks ([`fold_blocks`]); and `c`'s buffer holds `M`'s last
/// `M.len() % 64` bytes, the ones after those blocks.
pub closed spec fn models(c: Context, M: Seq<u8>) -> bool {
    &&& M.len() < Max_Bytes()
    &&& c.count == M.len()
    &&& c.h@ == fold_blocks(H0_256(), M, 0, M.len() / 64)
    &&& forall|i: int| 0 <= i < M.len() % 64 ==> c.buf[i] == #[trigger] M[64 * (M.len() / 64) + i]
}

/// The bytes `c0` has buffered followed by `data`: what `update` folds into
/// `c0`'s hash value.
pub closed spec fn joined(c0: Context, data: Seq<u8>) -> Seq<u8> {
    let r = c0.count % 64;
    Seq::new((r + data.len()) as nat, |i: int| if i < r { c0.buf[i] } else { data[i - r] })
}

/// Whether `c1` is `c0` after consuming `data`: `c1` has counted `data`'s
/// bytes on top of `c0`'s, and `c1`'s hash value and buffer are `c0`'s
/// hash value with `step` folded over the whole blocks, and the bytes left
/// over, of `c0`'s buffered bytes followed by `data` ([`joined`]).
/// `update`'s postcondition, stated without the message, which a context
/// does not hold.
pub closed spec fn absorbed(c0: Context, data: Seq<u8>, c1: Context) -> bool {
    let J = joined(c0, data);
    &&& c1.count == c0.count + data.len()
    &&& c1.h@ == fold_blocks(c0.h@, J, 0, J.len() / 64)
    &&& forall|i: int| 0 <= i < J.len() % 64 ==> c1.buf[i] == #[trigger] J[64 * (J.len() / 64) + i]
}

/// The number of blocks the padding of `c`'s buffered bytes takes: 1, or 2
/// when fewer than 9 bytes of the block are free.
pub closed spec fn tail_blocks(c: Context) -> nat {
    ((c.count % 64 + 72) / 64) as nat
}

/// The last `tail_blocks(c)` blocks of the padded message, as `pad_bytes`
/// ends a message of `c.count` bytes: the buffered bytes, 0x80, zeros, and
/// the bit length as 8 big-endian bytes; zeros after them. 128 bytes.
pub closed spec fn tail_pad(c: Context) -> Seq<u8> {
    let r = c.count % 64;
    let tb = tail_blocks(c);
    Seq::new(
        128,
        |i: int|
            if i < r {
                c.buf[i]
            } else if i == r {
                0x80
            } else if i < 64 * tb - 8 {
                0
            } else if i < 64 * tb {
                length_byte((8 * c.count) as u64, i - (64 * tb - 8))
            } else {
                0
            },
    )
}

/// Whether `d` is the digest of `c`: `c`'s hash value with `step` folded
/// over the one or two blocks of `c`'s buffered bytes padded as the end of
/// a message of `count(c)` bytes, written big-endian. `finalize`'s
/// postcondition, stated without the message.
pub closed spec fn finished(c: Context, d: Seq<u8>) -> bool {
    d == digest_bytes(fold_blocks(c.h@, tail_pad(c), 0, tail_blocks(c)))
}

/// Start a SHA-256 computation [FIPS-PUB-180-4 Section 5.3.3]: the hash
/// value `H0`, nothing consumed. The context models the empty message.
pub fn init() -> (c: Context)
    ensures
        models(c, Seq::empty()),
        count(c) == 0,
{
    Context { h: H0_256_exec, buf: [0u8; 64], count: 0 }
}

/// Consume `data`: fill the buffer and compress it once full, compress each
/// whole block of `data` in place, and buffer the rest. The total stays
/// below `Max_Bytes` (`2 ^^ 64` bits). [`lemma_update`] gives
/// `models(c, M + data)` from `models(old(c), M)`.
pub fn update(c: &mut Context, data: &[u8])
    requires
        count(*old(c)) < Max_Bytes(),
        data@.len() < Max_Bytes() - count(*old(c)),
    ensures
        absorbed(*old(c), data@, *final(c)),
        count(*final(c)) == count(*old(c)) + data@.len(),
{
    let ghost c0 = *c;
    let ghost J = joined(c0, data@);
    let len = data.len();
    let r = (c.count % 64) as usize;
    let mut done: usize = 0;

    // Fill the buffer, and compress it if it is full.
    if r > 0 {
        done = if 64 - r < len { 64 - r } else { len };
        let mut i: usize = 0;
        while i < done
            invariant
                c.h == c0.h,
                c.count == c0.count,
                r == c0.count % 64,
                0 < r < 64,
                done <= 64 - r,
                done <= len == data@.len(),
                i <= done,
                J == joined(c0, data@),
                J.len() == r + len,
                forall|k: int| 0 <= k < r + i ==> #[trigger] c.buf[k] == J[k],
            decreases done - i,
        {
            c.buf[r + i] = data[i];
            i += 1;
        }
        if r + done == 64 {
            let blk = load_block(&c.buf, 0);
            proof {
                lemma_block_ext(c.buf@, 0, J, 0);
                reveal_with_fuel(fold_blocks, 2);
            }
            compress(&mut c.h, &blk);
        }
    }
    assert(done == len || (r + done) % 64 == 0);
    assert(c.h@ == fold_blocks(c0.h@, J, 0, ((r + done) / 64) as nat));

    // Compress the whole blocks of data in place.
    while len - done >= 64
        invariant
            len == data@.len(),
            J == joined(c0, data@),
            J.len() == r + len,
            r == c0.count % 64,
            r < 64,
            done <= len,
            done == len || (r + done) % 64 == 0,
            r + done < 64 || (r + done) % 64 == 0,
            r + done < 64 ==> forall|k: int| 0 <= k < r + done ==> #[trigger] c.buf[k] == J[k],
            c.h@ == fold_blocks(c0.h@, J, 0, ((r + done) / 64) as nat),
            c.count == c0.count,
            forall|k: int| 0 <= k < len ==> #[trigger] J[r + k] == data@[k],
        decreases len - done,
    {
        let blk = load_block(data, done);
        proof {
            let kb = ((r + done) / 64) as nat;
            assert(r + done == 64 * kb);
            assert forall|i: int| 0 <= i < 64 implies data@[done + i] == #[trigger] J[(r + done) + i] by {
                assert(J[r + (done + i)] == data@[done + i]);
            }
            lemma_block_ext(data@, done as int, J, r + done);
            assert((r + done + 64) / 64 == kb + 1);
        }
        compress(&mut c.h, &blk);
        done += 64;
    }

    // Buffer the rest.
    if done < len {
        let ghost h1 = c.h;
        let mut i: usize = 0;
        while i < len - done
            invariant
                done < len == data@.len(),
                len - done < 64,
                c.h == h1,
                c.count == c0.count,
                i <= len - done,
                forall|k: int| 0 <= k < i ==> #[trigger] c.buf[k] == data@[done + k],
            decreases len - done - i,
        {
            c.buf[i] = data[done + i];
            i += 1;
        }
    }
    c.count = c.count + len as u64;
    proof {
        assert(J.len() / 64 == (r + done) / 64);
        if done < len {
            assert(J.len() % 64 == len - done);
            assert forall|i: int| 0 <= i < J.len() % 64 implies c.buf[i] == #[trigger] J[64 * (J.len()
                / 64) + i] by {
                assert(64 * (J.len() / 64) + i == r + (done + i));
            }
        } else {
            assert(J.len() == r + done);
        }
    }
}

/// The digest of the bytes `c` has consumed [FIPS-PUB-180-4 Sections 5.1.1
/// and 6.2]: pad the buffered bytes (0x80, zeros, and the bit length as 8
/// big-endian bytes) to one block, or two when fewer than 9 bytes of the
/// block are free, compress them, and write the hash value big-endian.
/// [`lemma_final`] proves it `hash_bytes` of the message `c` models. `c` is
/// not changed.
pub fn finalize(c: &Context) -> (d: [u8; 32])
    requires
        count(*c) < Max_Bytes(),
    ensures
        finished(*c, d@),
{
    let r = (c.count % 64) as usize;
    let tb: usize = if r < 56 { 1 } else { 2 };
    let l: u64 = 8 * c.count;
    let mut last = [0u8; 128];
    let mut h = c.h;

    // Pad [FIPS-PUB-180-4 Section 5.1.1]: the buffered bytes, 0x80, zeros,
    // and the bit length as 8 big-endian bytes.
    let mut i: usize = 0;
    while i < r
        invariant
            r == c.count % 64,
            i <= r,
            forall|k: int| 0 <= k < i ==> #[trigger] last[k] == c.buf[k],
            forall|k: int| i <= k < 128 ==> #[trigger] last[k] == 0,
        decreases r - i,
    {
        last[i] = c.buf[i];
        i += 1;
    }
    last[r] = 0x80;
    let mut k: usize = 0;
    while k < 8
        invariant
            r == c.count % 64,
            tb == tail_blocks(*c),
            l == 8 * c.count,
            k <= 8,
            forall|j: int| 0 <= j < r ==> #[trigger] last[j] == c.buf[j],
            last[r as int] == 0x80,
            forall|j: int| r < j < 64 * tb - 8 ==> #[trigger] last[j] == 0,
            forall|j: int| 0 <= j < k ==> #[trigger] last[64 * tb - 8 + j] == length_byte(l, j),
            forall|j: int| 64 * tb - 8 + k <= j < 128 ==> #[trigger] last[j] == 0,
        decreases 8 - k,
    {
        let v = (l >> (56 - 8 * k) as u64) & 0xff;
        assert(v <= 0xff) by (bit_vector)
            requires
                v == (l >> (56 - 8 * k) as u64) & 0xff,
        ;
        last[64 * tb - 8 + k] = v as u8;
        k += 1;
    }
    assert(last@ =~= tail_pad(*c)) by {
        assert forall|j: int| 64 * tb - 8 <= j < 64 * tb implies #[trigger] last[j] == length_byte(
            l,
            j - (64 * tb - 8),
        ) by {
            assert(last[64 * tb - 8 + (j - (64 * tb - 8))] == length_byte(l, j - (64 * tb - 8)));
        }
    }

    // Compress the last one or two blocks.
    let blk = load_block(&last, 0);
    proof {
        lemma_block_ext(last@, 0, tail_pad(*c), 0);
    }
    compress(&mut h, &blk);
    assert(h@ == fold_blocks(c.h@, tail_pad(*c), 0, 1)) by {
        reveal_with_fuel(fold_blocks, 2);
    }
    if tb == 2 {
        let blk = load_block(&last, 64);
        proof {
            assert forall|i: int| 0 <= i < 64 implies last@[64 + i] == #[trigger] tail_pad(*c)[64
                + i] by {}
            lemma_block_ext(last@, 64, tail_pad(*c), 64);
        }
        compress(&mut h, &blk);
    }
    assert(h@ == fold_blocks(c.h@, tail_pad(*c), 0, tail_blocks(*c)));
    to_digest(&h)
}

/// `update` preserves the meaning of a context: if `c0` models `M` and `c1`
/// is `c0` after `data`, then `c1` models `M + data`. The proof cuts the
/// fold of `M + data` at `M`'s last whole block ([`lemma_fold_split`]) and
/// compares each part with what `c0` and `c1` hold ([`lemma_fold_ext`]).
pub proof fn lemma_update(c0: Context, data: Seq<u8>, c1: Context, M: Seq<u8>)
    requires
        (M + data).len() < Max_Bytes(),
        models(c0, M),
        absorbed(c0, data, c1),
    ensures
        models(c1, M + data),
{
    let M2 = M + data;
    let q0 = M.len() / 64;
    let r0 = M.len() % 64;
    let J = joined(c0, data);
    let K = J.len() / 64;
    assert(J.len() == r0 + data.len());
    assert(M2.len() / 64 == q0 + K);
    assert(M2.len() % 64 == J.len() % 64);
    assert forall|i: int| 0 <= i < J.len() implies #[trigger] J[i] == M2[64 * q0 + i] by {
        if i < r0 {
            assert(c0.buf[i] == M[64 * q0 + i]);
        } else {
            assert(M2[M.len() + (i - r0)] == data[i - r0]);
        }
    }
    lemma_fold_split(H0_256(), M2, 0, q0, K);
    assert forall|i: int| 0 <= i < 64 * q0 implies M[0 + i] == #[trigger] M2[0 + i] by {}
    lemma_fold_ext(H0_256(), M, 0, M2, 0, q0);
    assert forall|i: int| 0 <= i < 64 * K implies J[0 + i] == #[trigger] M2[(0 + 64 * q0) + i] by {}
    lemma_fold_ext(c0.h@, J, 0, M2, (64 * q0) as int, K);
    assert forall|i: int| 0 <= i < M2.len() % 64 implies c1.buf[i] == #[trigger] M2[64 * (M2.len()
        / 64) + i] by {
        assert(J[64 * K + i] == M2[64 * q0 + (64 * K + i)]);
    }
}

/// `finalize` computes `hash_bytes`: if `c` models `M`, the digest of `c`
/// is `hash_bytes(M)`. The proof reads the padded message's last one or two
/// blocks as the padded buffer, and its blocks before them as the ones
/// folded into `c`'s hash value ([`lemma_foldl_parse`],
/// [`lemma_fold_split`], [`lemma_fold_ext`]).
pub proof fn lemma_final(c: Context, M: Seq<u8>)
    requires
        models(c, M),
    ensures
        count(c) < Max_Bytes(),
        forall|d: Seq<u8>| #[trigger] finished(c, d) ==> d == hash_bytes(M),
{
    let n = M.len();
    let q = n / 64;
    let tb = tail_blocks(c);
    let nb = blocks(n);
    let pb = pad_bytes(M);
    let tp = tail_pad(c);
    assert(nb == q + tb);
    assert forall|i: int| 0 <= i < 64 * q implies pb[0 + i] == #[trigger] M[0 + i] by {}
    assert forall|i: int| 0 <= i < 64 * tb implies pb[(0 + 64 * q) + i] == #[trigger] tp[0 + i] by {
        assert(64 * q + i - (64 * nb - 8) == i - (64 * tb - 8));
        if i < n % 64 {
            assert(c.buf[i] == M[64 * q + i]);
        }
    }
    lemma_foldl_parse(H0_256(), pb, nb, nb);
    lemma_fold_split(H0_256(), pb, 0, q, tb);
    lemma_fold_ext(H0_256(), pb, 0, M, 0, q);
    lemma_fold_ext(c.h@, pb, (64 * q) as int, tp, 0, tb);
}

/// SHA-256 of a message of whole bytes, in one call: `init`, one `update`,
/// `finalize`. Proved equal to `hash_bytes`, and so to the spec's `hash`
/// (Main.cry:55) on the message's bits.
pub fn hash(M: &[u8]) -> (d: [u8; 32])
    requires
        M@.len() < Max_Bytes(),
    ensures
        d@ == hash_bytes(M@),
        bits_of(d@) == main::hash::<SHA256>(bits_of(M@)),
{
    let mut c = init();
    let ghost c0 = c;
    update(&mut c, M);
    proof {
        lemma_update(c0, M@, c, Seq::empty());
        assert(Seq::<u8>::empty() + M@ =~= M@);
        lemma_final(c, M@);
        sha256_bytes::lemma_hash_bytes(M@);
    }
    finalize(&c)
}

/// SHA-256 of `M` fed to `update` in chunks: `init`, an `update` for each
/// chunk `ends` describes, one more for the bytes after the last, and
/// `finalize`. Chunk `j` is the bytes from the end of chunk `j - 1` (or
/// from 0) up to, not including, `ends[j]`. Proved equal to
/// `hash_bytes(M)` for every chunking, which is the streaming theorem
/// `finalize(update*(init, chunks)) == hash_bytes(concatenation of chunks)`
/// for the chunks of one slice.
pub fn hash_chunked(M: &[u8], ends: &[usize]) -> (d: [u8; 32])
    requires
        M@.len() < Max_Bytes(),
        forall|j: int| 0 <= j < ends@.len() ==> #[trigger] ends@[j] <= M@.len(),
        forall|j: int| 0 < j < ends@.len() ==> ends@[j - 1] <= #[trigger] ends@[j],
    ensures
        d@ == hash_bytes(M@),
{
    let len = M.len();
    let mut c = init();
    let mut done: usize = 0;
    assert(M@.subrange(0, 0) =~= Seq::<u8>::empty());
    let mut j: usize = 0;
    while j < ends.len()
        invariant
            len == M@.len() < Max_Bytes(),
            forall|j: int| 0 <= j < ends@.len() ==> #[trigger] ends@[j] <= M@.len(),
            forall|j: int| 0 < j < ends@.len() ==> ends@[j - 1] <= #[trigger] ends@[j],
            j <= ends@.len(),
            if j > 0 { done == ends@[j - 1] } else { done == 0 },
            done <= len,
            models(c, M@.subrange(0, done as int)),
            count(c) == done,
        decreases ends@.len() - j,
    {
        let e = ends[j];
        let ghost c0 = c;
        let chunk = &M[done..e];
        update(&mut c, chunk);
        proof {
            assert(M@.subrange(0, done as int) + chunk@ =~= M@.subrange(0, e as int));
            lemma_update(c0, chunk@, c, M@.subrange(0, done as int));
        }
        done = e;
        j += 1;
    }
    let ghost c0 = c;
    let chunk = &M[done..len];
    update(&mut c, chunk);
    proof {
        assert(M@.subrange(0, done as int) + chunk@ =~= M@);
        lemma_update(c0, chunk@, c, M@.subrange(0, done as int));
        lemma_final(c, M@);
    }
    finalize(&c)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{compress, finalize, hash, hash_chunked, init, update};
    use crate::sha2::preprocessing::exec::H0_256;

    /// Parse a digest written in hexadecimal.
    fn hex(s: &str) -> [u8; 32] {
        let mut d = [0u8; 32];
        for i in 0..32 {
            d[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
        }
        d
    }

    const ABC: &str = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
    const EMPTY: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
    const TWO_BLOCK_MSG: &[u8] = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    const TWO_BLOCK: &str = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";
    const MILLION_A: &str = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0";

    /// FIPS 180-4's one-block example, "abc" (SHA256.cry's test vectors and
    /// the NIST examples): the padded block, compressed from H0, is the digest.
    #[test]
    fn compress_abc() {
        let mut m = [0u32; 16];
        m[0] = 0x61626380;
        m[15] = 24;
        let mut h = H0_256;
        compress(&mut h, &m);
        assert_eq!(
            h,
            [
                0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
                0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad,
            ]
        );
    }

    /// The NIST examples: "abc", the empty message, the two-block 448-bit
    /// message, and a million "a"s.
    #[test]
    fn hash_examples() {
        assert_eq!(hash(b"abc"), hex(ABC));
        assert_eq!(hash(b""), hex(EMPTY));
        assert_eq!(hash(TWO_BLOCK_MSG), hex(TWO_BLOCK));
        assert_eq!(hash(&vec![b'a'; 1_000_000]), hex(MILLION_A));
    }

    /// Every length from 0 to 200 bytes, so that each case of the padding
    /// (one tail block or two) and of the buffer is met, hashed in one call
    /// and in chunks of every size from 1 to 70 bytes: all agree.
    #[test]
    fn chunked_agrees() {
        let m: Vec<u8> = (0..200u32).map(|i| (i * 7 + 3) as u8).collect();
        for n in 0..=200 {
            let whole = hash(&m[..n]);
            for size in 1..=70 {
                let ends: Vec<usize> = (1..).map(|j| j * size).take_while(|&e| e <= n).collect();
                assert_eq!(hash_chunked(&m[..n], &ends), whole, "n = {n}, size = {size}");
            }
        }
        let mut c = init();
        update(&mut c, b"ab");
        update(&mut c, b"");
        update(&mut c, b"c");
        assert_eq!(finalize(&c), hex(ABC));
    }
}
