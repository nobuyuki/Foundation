//! The Rust side of the AES benchmark; `perf/src/perf_bench.rs`
//! is the Verus side, and does the same thing in the same order.
//!
//! First the FIPS-197 Appendix C known answers go through the build under
//! test (C.1, C.2, C.3: encrypt, then decrypt back), printed as `kat` lines
//! that `scripts/perf-aes.sh` checks. Then, for k = 128, 192 and 256, each
//! operation is timed in batches of `BATCH` calls: `WARM` batches are run
//! and discarded, then `REPS` batches are timed with `std::time::Instant`
//! (`CLOCK_UPTIME_RAW` on macOS, `CLOCK_MONOTONIC` on Linux). Every call's
//! output feeds the next call's input. One `bench` line per operation gives
//! the time per call over the timed batches, in nanoseconds: median,
//! minimum, first quartile, third quartile, maximum.
//!
//! Usage: `aes_perf [quick]` (quick: few, small batches, for a smoke test)

use std::fmt::Write as _;
use std::hint::black_box;
use std::time::Instant;

use aes_perf::{decrypt, encrypt, expand_key, Block, Word};

/// Run sizes: batches discarded, batches timed, calls per batch.
struct Plan {
    warm: usize,
    reps: usize,
    batch: u32,
}

/// The key size's label.
fn tag(k: usize) -> String {
    format!("aes{k}")
}

/// A block in hexadecimal, byte 0 first.
fn hex(b: &Block) -> String {
    b.iter().fold(String::new(), |mut s, x| {
        let _ = write!(s, "{x:02x}");
        s
    })
}

/// The key 00 01 02 ... of FIPS-PUB-197 Appendix C, as `k / 32` words.
fn key_of(k: usize) -> Vec<Word> {
    (0..k / 32)
        .map(|i| {
            let mut w: Word = [0; 4];
            for (j, x) in w.iter_mut().enumerate() {
                *x = u8::try_from((4 * i + j) % 256).unwrap_or(0);
            }
            w
        })
        .collect()
}

/// FIPS-PUB-197 Appendix C at `k`: prints the ciphertext of 00 11 22 ... ff
/// and its decryption.
fn known_answer(k: usize) {
    let w = expand_key(k, &key_of(k));
    let ks = &w[..=k / 32 + 6];
    let mut pt: Block = [0; 16];
    for (i, x) in pt.iter_mut().enumerate() {
        *x = u8::try_from(17 * i).unwrap_or(0);
    }
    let ct = encrypt(ks, pt);
    println!("kat {} encrypt {}", tag(k), hex(&ct));
    println!("kat {} decrypt {}", tag(k), hex(&decrypt(ks, ct)));
}

/// Sort the samples and print their `bench` line.
fn report(t: &str, op: &str, s: &mut [f64]) {
    s.sort_by(f64::total_cmp);
    let q = |i: usize| s[(s.len() - 1) * i / 4];
    println!(
        "bench {t} {op} {:.2} {:.2} {:.2} {:.2} {:.2}",
        q(2),
        q(0),
        q(1),
        q(3),
        q(4)
    );
}

/// Time `step` in batches as `plan` says, and report it.
fn time(plan: &Plan, t: &str, op: &str, mut step: impl FnMut()) {
    let mut s = Vec::with_capacity(plan.reps);
    for r in 0..plan.warm + plan.reps {
        let t0 = Instant::now();
        for _ in 0..plan.batch {
            step();
        }
        let ns = t0.elapsed().as_secs_f64() * 1.0e9 / f64::from(plan.batch);
        if r >= plan.warm {
            s.push(ns);
        }
    }
    report(t, op, &mut s);
}

/// Time `expand_key`, `encrypt` and `decrypt` at `k`.
fn bench(plan: &Plan, k: usize) -> u8 {
    let t = tag(k);
    let nr = k / 32 + 6;
    let mut key = key_of(k);
    let mut w = expand_key(k, &key);
    time(plan, &t, "expand_key", || {
        w = expand_key(black_box(k), black_box(&key));
        key[0][0] ^= w[nr][0];
    });
    let mut state: Block = [0; 16];
    for (i, x) in state.iter_mut().enumerate() {
        *x = u8::try_from(i).unwrap_or(0);
    }
    let ks = &w[..=nr];
    time(plan, &t, "encrypt", || {
        state = encrypt(black_box(ks), state);
    });
    time(plan, &t, "decrypt", || {
        state = decrypt(black_box(ks), state);
    });
    state[0] ^ key[0][0]
}

fn main() {
    let quick = std::env::args().nth(1).as_deref() == Some("quick");
    let plan = if quick {
        Plan {
            warm: 2,
            reps: 5,
            batch: 100,
        }
    } else {
        Plan {
            warm: 20,
            reps: 101,
            batch: 10_000,
        }
    };
    // Through black_box, so that no wrapper is specialized for a constant
    // key size, as perf/src/perf_bench.rs does.
    let sizes = black_box([128usize, 192, 256]);
    for k in sizes {
        known_answer(k);
    }
    let mut sink = 0u8;
    for k in sizes {
        sink ^= bench(&plan, k);
    }
    println!("sink {sink}");
}
