#!/usr/bin/env bash
#
# perf-aes.sh -- binary size and performance of the crate's AES against
# NSA's Rust AES (doc/performance.md), on the machine it runs on. The SPARK
# crate's spark/scripts/perf-aes.sh, for the Verus crate. Linux, or macOS
# for the times only: the size table needs nm -S (scripts/perf-report.py).
#
# 1. Builds the harness perf/ (perf_bench, timing through perf_aes's
#    non-inlined wrappers) of the crate with cargo, four ways (the SPARK
#    crate's perf/perf.gpr variants):
#      verus-O2          profile perf-o2: opt-level 2, lto "fat", 1 codegen unit
#      verus-O3          profile perf-o3: opt-level 3, lto "fat", 1 codegen unit
#      verus-O3-checks   profile perf-o3-checks: perf-o3 with overflow checks
#                        and debug assertions
#      verus-release     plain --release: opt-level 3, no LTO, 16 codegen units
# 2. Builds the Rust harness perf/rust (NSA's Cipher and KeyExpansion
#    crates behind non-inlined wrappers) with cargo, three ways:
#      rust-O2           profile perf-o2: opt-level 2, lto "fat", 1 codegen unit
#      rust-O3           profile perf-o3: opt-level 3, lto "fat", 1 codegen unit
#      rust-release      plain --release: opt-level 3, no LTO, 16 codegen units
#    Both with the same rustc (rust-toolchain.toml).
# 3. Unless PERF_SKIP_BENCH=1, runs every executable once, one after the
#    other (the FIPS-197 Appendix C known answers, then the timings), and
#    records the machine's load before and after.
# 4. Prints the known-answer check, the size table (Linux only) and the
#    time table (scripts/perf-report.py), and writes them to
#    target/perf/perf-report.md.
#
# Usage (from verus/):
#   scripts/perf-aes.sh
# Env:
#   CARGO            cargo (default: cargo)
#   PERF_QUICK       1 for a smoke test (few, small batches): not a measurement
#   PERF_SKIP_BENCH  1 to build and measure sizes only
#
# Exit status: 1 if a build fails or a known answer is wrong, 0 otherwise.
# Timings are reported, never enforced.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CARGO="${CARGO:-cargo}"
OUT="target/perf"
REPORT="$OUT/perf-report.md"
JOBS="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)"

case "$(uname -s)" in
  Darwin) OS=darwin ;;
  Linux)  OS=linux ;;
  *) echo "perf-aes.sh: unsupported system $(uname -s)" >&2; exit 2 ;;
esac

cpu() {
  if [ "$OS" = darwin ]; then
    sysctl -n machdep.cpu.brand_string
  else
    grep -m1 -E '^(model name|Model)' /proc/cpuinfo | sed 's/.*: //' || uname -m
  fi
}

mkdir -p "$OUT"
: > "$OUT/manifest.txt"
RUN_ARG=""
if [ "${PERF_QUICK:-0}" = 1 ]; then RUN_ARG=quick; fi

load() {
  uptime | sed 's/.*load average[s]*: *//'
}

cargo_build() { # name side manifest target-dir profile binary
  echo ">> building $1" >&2
  "$CARGO" build --quiet --locked --manifest-path "$3" --target-dir "$4" \
    --profile "$5" --bin "$6"
  echo "$1|$2|$4/$5/$6|$OUT/$1.bench.txt" >> "$OUT/manifest.txt"
}

verus_build() { # name profile
  cargo_build "$1" verus perf/Cargo.toml "$OUT/verus" "$2" perf_bench
}

rust_build() { # name profile
  cargo_build "$1" rust perf/rust/Cargo.toml "$OUT/rust" "$2" aes_perf
}

verus_build verus-O2 perf-o2
verus_build verus-O3 perf-o3
verus_build verus-O3-checks perf-o3-checks
verus_build verus-release release
rust_build rust-O2 perf-o2
rust_build rust-O3 perf-o3
rust_build rust-release release

{
  echo "# perf-aes.sh on $(uname -s) $(uname -m), $(date -u +%Y-%m-%dT%H:%M:%SZ), commit $(git rev-parse --short HEAD)$(git diff --quiet HEAD -- . || echo ' (dirty)')"
  echo
  echo "* CPU: $(cpu), $JOBS logical CPUs"
  if [ "$OS" = darwin ]; then
    echo "* OS: macOS $(sw_vers -productVersion)"
  else
    echo "* OS: Linux $(uname -r)"
  fi
  echo "* Rust: $(cd perf && rustc --version), host $(cd perf && rustc -vV | sed -n 's/^host: //p')"
  if [ -n "$RUN_ARG" ]; then
    echo "* **PERF_QUICK=1: a smoke test, not a measurement**"
  fi
} > "$REPORT"

if [ "${PERF_SKIP_BENCH:-0}" != 1 ]; then
  echo "* load before (1, 5, 15 min): $(load)" >> "$REPORT"
  while IFS='|' read -r name _side binary result; do
    echo ">> running $name" >&2
    # shellcheck disable=SC2086  # RUN_ARG is empty or one word
    "$binary" $RUN_ARG > "$result"
  done < "$OUT/manifest.txt"
  echo "* load after (1, 5, 15 min): $(load)" >> "$REPORT"
else
  rm -f "$OUT"/*.bench.txt
fi
echo >> "$REPORT"

status=0
python3 -I scripts/perf-report.py "$OUT" >> "$REPORT" || status=1
cat "$REPORT"
echo ">> wrote $REPORT" >&2
exit "$status"
