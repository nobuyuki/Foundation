//! The Verus side of the AES benchmark; perf/rust/src/main.rs is the Rust
//! side, and does the same thing in the same order (the SPARK crate's
//! `perf/src/perf_bench.adb`).
//!
//! First the FIPS-197 Appendix C known answers go through the build under
//! test (C.1, C.2, C.3: encrypt, then both decryptions back), printed as
//! `kat` lines that `scripts/perf-report.py` checks. Then, for k = 128, 192
//! and 256, each operation is timed in batches of `batch` calls: `warm`
//! batches are run and discarded, then `reps` batches are timed with
//! `std::time::Instant` (`CLOCK_MONOTONIC` on Linux, `CLOCK_UPTIME_RAW` on
//! macOS), as perf/rust/src/main.rs does. Every call's output feeds the
//! next call's input, so no call can be hoisted or dropped. One `bench`
//! line per operation gives the time per call over the timed batches, in
//! nanoseconds: median, minimum, first quartile, third quartile, maximum.
//!
//! Usage: `perf_bench [quick]` (quick: few, small batches, for a smoke test)

use std::fmt::Write as _;
use std::hint::black_box;
use std::time::Instant;

use perf_aes::{AESWord, Block};

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
fn key_of(k: usize) -> Vec<AESWord> {
    (0..k / 32)
        .map(|i| {
            let mut w: AESWord = [0; 4];
            for (j, x) in w.iter_mut().enumerate() {
                *x = u8::try_from((4 * i + j) % 256).unwrap_or(0);
            }
            w
        })
        .collect()
}

/// FIPS-PUB-197 Appendix C at `k`: the key 00 01 02 ..., the plaintext
/// 00 11 22 ... ff. Prints the ciphertext and both decryptions of it.
fn known_answer(k: usize) {
    let w = perf_aes::expand_key(k, &key_of(k));
    let ks = &w[..=k / 32 + 6];
    let mut ct: Block = [0; 16];
    for (i, x) in ct.iter_mut().enumerate() {
        *x = u8::try_from(17 * i).unwrap_or(0);
    }
    perf_aes::encrypt(k, ks, &mut ct);
    println!("kat {} encrypt {}", tag(k), hex(&ct));
    let mut d = ct;
    perf_aes::decrypt(k, ks, &mut d);
    println!("kat {} decrypt {}", tag(k), hex(&d));
    let mut d = ct;
    perf_aes::decrypt_prime(k, ks, &mut d);
    println!("kat {} decrypt_prime {}", tag(k), hex(&d));
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

/// Time `expand_key`, `encrypt`, `decrypt` and `decrypt_prime` at `k`.
fn bench(plan: &Plan, k: usize) -> u8 {
    let t = tag(k);
    let nr = k / 32 + 6;
    let mut key = key_of(k);
    let mut w = perf_aes::expand_key(k, &key);
    time(plan, &t, "expand_key", || {
        w = perf_aes::expand_key(black_box(k), black_box(&key));
        key[0][0] ^= w[nr][0];
    });
    let mut state: Block = [0; 16];
    for (i, x) in state.iter_mut().enumerate() {
        *x = u8::try_from(i).unwrap_or(0);
    }
    let ks = &w[..=nr];
    time(plan, &t, "encrypt", || {
        perf_aes::encrypt(black_box(k), black_box(ks), &mut state);
    });
    time(plan, &t, "decrypt", || {
        perf_aes::decrypt(black_box(k), black_box(ks), &mut state);
    });
    time(plan, &t, "decrypt_prime", || {
        perf_aes::decrypt_prime(black_box(k), black_box(ks), &mut state);
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
    // key size, as perf/rust/src/main.rs does (perf_bench.adb reads its
    // sizes from a Volatile).
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
