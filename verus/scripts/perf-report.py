#!/usr/bin/env python3
"""perf-report.py -- the size and benchmark tables.

The SPARK crate's spark/scripts/perf-report.py, for the Verus crate. Called
by scripts/perf-aes.sh with the perf output directory. It reads
<dir>/manifest.txt, one build per line:

    name|side|binary|bench-output

where side is "verus" or "rust", and prints Markdown to stdout:

* the known-answer check (FIPS-197 Appendix C) of every build: any mismatch
  or missing answer is an error (exit 1);
* the size table: per build, the text and data of the AES library code, the
  wrappers, and the whole executable's text for scale; then each AES
  function's text, per build;
* the benchmark table: per key size and operation, each build's median ns
  per call, with the interquartile range, and the Verus/Rust ratios.

Sizes come from the symbol table of the linked executable, `nm -S -C`
(binutils, which demangles Rust's v0 symbols to their paths), on Linux
only. On macOS the size table is left out and the rest is printed: Mach-O
symbols have no sizes, and the SPARK script reads ld64's linker map
there instead, which would need the map's names demangled; macOS is run
here for the times only. Anonymous constants
(Rust's .Lanon.*, among them the S-box tables of both sides, which are
`const`s) are local labels with no symbol and are not counted in either
side's AES data, as in the SPARK script.

"AES library code" is, for Verus, every symbol of the crate
(foundation_verus::*), and for Rust, every symbol of NSA's Cipher and
KeyExpansion crates. The wrappers are perf_aes::* and aes_perf::{expand_key,
encrypt, decrypt}. Everything else (the harnesses, perf_bench and aes_perf's
main, Rust's std, core and alloc) is left out of the AES columns.
"""

import os
import re
import subprocess
import sys

KAT = {
    ("aes128", "encrypt"): "69c4e0d86a7b0430d8cdb78070b4c55a",
    ("aes192", "encrypt"): "dda97ca4864cdfe06eaf70a0ec0d7191",
    ("aes256", "encrypt"): "8ea2b7ca516745bfeafc49904b496089",
}
PLAIN = "00112233445566778899aabbccddeeff"
SIZES = ["aes128", "aes192", "aes256"]
OPS = ["expand_key", "encrypt", "decrypt", "decrypt_prime"]


def run(cmd):
    """Run a command and return its standard output."""
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout


def classify(side, name):
    """Where a demangled symbol belongs: ("lib", name), ("wrap", name), or
    None."""
    if side == "verus":
        if name.startswith("foundation_verus::"):
            return "lib", name[len("foundation_verus::"):]
        if name.startswith("perf_aes::"):
            return "wrap", name
        return None
    if name.startswith("Cipher::") or name.startswith("KeyExpansion::"):
        return "lib", name
    if name in ("aes_perf::expand_key", "aes_perf::encrypt", "aes_perf::decrypt"):
        return "wrap", name
    return None


def symbols(binary):
    """(name, size, is_text) of every sized symbol, and the .text size."""
    out = []
    for line in run(["nm", "-S", "-C", "--defined-only", binary]).splitlines():
        f = line.split(None, 3)
        if len(f) == 4 and re.fullmatch(r"[0-9a-f]+", f[1]):
            out.append((f[3], int(f[1], 16), f[2] in "tT"))
    text = 0
    for line in run(["size", "-A", binary]).splitlines():
        f = line.split()
        if len(f) >= 2 and f[0] == ".text":
            text = int(f[1])
    return out, text


def sizes(side, binary):
    """Per-function AES sizes and the totals of one build."""
    syms, text = symbols(binary)
    funcs = {}
    tot = {"lib_text": 0, "lib_data": 0, "wrap_text": 0, "bin_text": text}
    for name, size, is_text in syms:
        c = classify(side, name)
        if c is None:
            continue
        kind, label = c
        if is_text:
            funcs[label] = funcs.get(label, 0) + size
            tot[kind + "_text"] += size
        elif kind == "lib":
            tot["lib_data"] += size
            funcs[label + " (data)"] = size
    return funcs, tot


def bench(path):
    """KAT lines and bench lines of one run."""
    kat, res = {}, {}
    if not os.path.exists(path):
        return kat, res
    for line in open(path):
        f = line.split()
        if f and f[0] == "kat":
            kat[(f[1], f[2])] = f[3]
        elif f and f[0] == "bench":
            res[(f[1], f[2])] = [float(x) for x in f[3:8]]
    return kat, res


def peer(name):
    """The Rust build a Verus build is set against: the same profile, and
    for verus-O3-checks, rust-O3."""
    return "rust-" + name[len("verus-"):].replace("-checks", "")


def ratios(runs):
    """Verus median / Rust median, each Verus build against the Rust build
    of its profile. NSA's inv_cipher undoes the rounds of cipher in reverse
    order, as decrypt_block_prime does, so Rust's decrypt is set against
    both Verus decryptions."""
    rust = {name: res for name, side, res in runs if side == "rust"}
    pairs = [(name, res, peer(name), rust[peer(name)])
             for name, side, res in runs if side == "verus" and peer(name) in rust]
    if not pairs:
        return
    print("\n## Verus / Rust (median over median, same profile)\n")
    print("| op | " + " | ".join(f"{p[0]} / {p[2]}" for p in pairs) + " |")
    print("|---|" + "---:|" * len(pairs))
    for k in SIZES:
        for op in OPS:
            r_op = "decrypt" if op == "decrypt_prime" else op
            cells = []
            for _n, s, _rn, r in pairs:
                if (k, op) in s and (k, r_op) in r:
                    cells.append(f"{s[(k, op)][0] / r[(k, r_op)][0]:.2f}")
                else:
                    cells.append("")
            print(f"| {k} {op} | " + " | ".join(cells) + " |")


def main():
    out = sys.argv[1]
    builds = []
    for line in open(os.path.join(out, "manifest.txt")):
        if line.strip():
            name, side, binary, res = line.strip().split("|")
            builds.append((name, side, binary, res))

    status = 0
    print("## Known answers (FIPS-197 Appendix C.1-C.3)\n")
    for name, side, _, res in builds:
        kat, _r = bench(res)
        if not kat:
            print(f"* {name}: not run")
            continue
        ops = ["encrypt", "decrypt"] + (["decrypt_prime"] if side == "verus" else [])
        want = {(k, op): KAT[(k, "encrypt")] if op == "encrypt" else PLAIN
                for k in SIZES for op in ops}
        bad = sorted(k for k in want if kat.get(k) != want[k])
        extra = sorted(k for k in kat if k not in want)
        if bad or extra:
            status = 1
            print(f"* {name}: **FAIL** {bad + extra}")
        else:
            print(f"* {name}: {len(kat)}/{len(want)} match")

    print("\n## Size (bytes, linked executable)\n")
    if not sys.platform.startswith("linux"):
        print("Not measured: Linux only (nm -S); see scripts/perf-report.py.")
        builds_sized = []
    else:
        builds_sized = builds
    if builds_sized:
        print("| build | AES text | AES data | wrappers | AES total | "
              "executable text |")
        print("|---|---:|---:|---:|---:|---:|")
    per = {}
    for name, side, binary, _ in builds_sized:
        funcs, t = sizes(side, binary)
        per[name] = funcs
        print(f"| {name} | {t['lib_text']} | {t['lib_data']} | "
              f"{t['wrap_text']} | "
              f"{t['lib_text'] + t['lib_data'] + t['wrap_text']} | "
              f"{t['bin_text']} |")

    if builds_sized:
        print("\n### Per function (text bytes; data marked)\n")
    for name, _side, _b, _r in builds_sized:
        funcs = per[name]
        items = sorted(funcs.items(), key=lambda kv: (-kv[1], kv[0]))
        print(f"* **{name}**: " + ", ".join(f"`{k}` {v}" for k, v in items))

    print("\n## Time (ns per call: median, [p25, p75])\n")
    runs = [(name, side, bench(res)[1]) for name, side, _, res in builds]
    runs = [r for r in runs if r[2]]
    if runs:
        print("| op | " + " | ".join(r[0] for r in runs) + " |")
        print("|---|" + "---:|" * len(runs))
        for k in SIZES:
            for op in OPS:
                cells = []
                for _n, _s, res in runs:
                    v = res.get((k, op))
                    cells.append(f"{v[0]:.1f} [{v[2]:.1f}, {v[3]:.1f}]"
                                 if v else "")
                if any(cells):
                    print(f"| {k} {op} | " + " | ".join(cells) + " |")
        print("\nmin / max per op and build: in each build's .bench.txt "
              "(fields: median min p25 p75 max).")
        ratios(runs)
    sys.exit(status)


if __name__ == "__main__":
    main()
