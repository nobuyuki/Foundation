#!/usr/bin/env bash
#
# check-coverage.sh -- source-based coverage (LLVM, through rustc's
# -C instrument-coverage) of the executable Verus code under the
# Cryptol-driven FFI properties: region, line and branch coverage of the
# files in coverage/units.txt (the executable implementations and the FFI
# exports), from every property of cryptol/properties.txt.
#
# The counterpart of the SPARK crate's spark/scripts/check-coverage.sh
# (github.com/manthonyaiello/Foundation, tag spark-v1.0), which measures
# statement, decision and MC/DC with gnatcov. Here a region stands for a
# statement and a branch outcome for a decision outcome; there is NO MC/DC:
# rustc has no MC/DC instrumentation (Rust 1.98.1, and nightly 1.101 too,
# accept only block, branch and condition for -Zcoverage-options).
# doc/coverage.md says more.
#
# 1. Builds the FFI library (ffi/) instrumented, into its own target
#    directory (target/cov/), with the profile check-ffi.sh uses (release,
#    overflow checks, debug assertions) and RUSTFLAGS
#    "-C instrument-coverage -Zcoverage-options=branch,condition". The
#    branch options are unstable: the build sets RUSTC_BOOTSTRAP=1 on the
#    pinned toolchain (rust-toolchain.toml) rather than switch to a nightly
#    one, so the code measured is the code rustc 1.98.1 compiles. Nothing
#    else is built that way: the crate's own build, the proof and the FFI
#    check's library are untouched. The build's own tools (proc macros,
#    build scripts) are instrumented too and write profiles when they run;
#    those go to target/cov/build-prof/ and are not used.
# 2. Runs scripts/check-ffi.sh against that library (FFI_LIB, FFI_OUT),
#    which judges every property as usual. The library carries LLVM's
#    profiling runtime, which registers its own exit handler when Cryptol
#    loads the library, so each `cryptol -b` (one per property) writes its
#    own profile (LLVM_PROFILE_FILE, target/cov/traces/<pid>.profraw) when it
#    exits; no counterpart of the SPARK crate's coverage/ dump unit is
#    needed. A run that wrote no profile fails this script.
# 3. Merges the profiles (llvm-profdata) and writes target/cov/report/:
#    summary.txt (the per-file table, and each violation with its
#    explanation from coverage/explained.txt, from
#    scripts/coverage-summary.py), report.txt (llvm-cov report, per file and
#    per function), html/ (the annotated sources, with branch counts) and
#    export.json (llvm-cov export, which summary.txt is computed from).
# 4. A run of every property on a clean tree writes coverage/results.txt:
#    the commit, the date, the tools and summary.txt (this crate has no CI
#    to keep the numbers, as the SPARK crate's does).
#
# Usage (from anywhere; needs cargo, the toolchain of rust-toolchain.toml
# with its llvm-tools component, and what check-ffi.sh needs):
#   scripts/check-coverage.sh                 every property
#   scripts/check-coverage.sh PROPERTY ...    only these (a partial report)
#
# Env:
#   LLVM_PROFDATA, LLVM_COV  the binaries (default: those of the toolchain's
#               llvm-tools component, `rustup component add llvm-tools`).
#               Their LLVM must be rustc's, or the profiles do not read.
#   CRYPTOL, FFI_JOBS, CARGO: as for check-ffi.sh.
#
# Exit status: 0 when every property passed, every run wrote a profile and
# every violation (a region never executed, a branch outcome never taken) is
# explained in coverage/explained.txt; 1 when one of those fails; 2 on a
# usage or setup error. A partial run (PROPERTY ...) leaves violations that
# the whole run would cover, so read its verdict accordingly.
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CARGO="${CARGO:-cargo}"
JOBS="${FFI_JOBS:-$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN)}"

COV="target/cov"
TRACES="$COV/traces"
REPORT="$COV/report"
UNITS="coverage/units.txt"
EXPLAINED="coverage/explained.txt"
RESULTS="coverage/results.txt"
FLAGS="-C instrument-coverage -Zcoverage-options=branch,condition"

case "$(uname -s)" in
  Darwin) EXT=dylib ;;
  *)      EXT=so ;;
esac
LIB="$COV/release/libfoundation_verus_ffi.$EXT"

die() { echo "check-coverage.sh: $*" >&2; exit 2; }

# Cryptol before the long build, and absolute, as check-ffi.sh resolves it
# (it runs Cryptol from another directory, where a relative PATH entry does
# not hold); passed on to check-ffi.sh, and recorded in coverage/results.txt.
found="$(command -v "${CRYPTOL:-cryptol}" 2>/dev/null)" \
  || die "${CRYPTOL:-cryptol} not found (put it on PATH, or set CRYPTOL)"
case "$found" in
  /*) CRYPTOL="$found" ;;
  *)  CRYPTOL="$(cd "$(dirname "$found")" && pwd)/$(basename "$found")" ;;
esac
export CRYPTOL

[ -f "$UNITS" ] || die "missing $UNITS"
[ -f "$EXPLAINED" ] || die "missing $EXPLAINED"

# The LLVM tools of the pinned toolchain (rustc runs from verus/, so
# rust-toolchain.toml picks it).
tools="$(rustc --print sysroot)/lib/rustlib/$(rustc -vV | sed -n 's/^host: //p')/bin"
LLVM_PROFDATA="${LLVM_PROFDATA:-$tools/llvm-profdata}"
LLVM_COV="${LLVM_COV:-$tools/llvm-cov}"
for t in "$LLVM_PROFDATA" "$LLVM_COV"; do
  [ -x "$t" ] || die "no $t (rustup component add llvm-tools, or set LLVM_PROFDATA and LLVM_COV)"
done

# --- 1. the instrumented library ---------------------------------------------------

echo ">> building the instrumented FFI library (ffi/, $FLAGS, -j$JOBS)"
rm -rf "$COV/build-prof"
mkdir -p "$COV/build-prof"
(cd ffi && RUSTC_BOOTSTRAP=1 RUSTFLAGS="$FLAGS" CARGO_TARGET_DIR="$ROOT/$COV" \
   LLVM_PROFILE_FILE="$ROOT/$COV/build-prof/%p.profraw" \
   "$CARGO" build --release --quiet --locked -j"$JOBS")
[ -f "$LIB" ] || die "the build did not produce $LIB"

# --- 2. the properties, each run writing a profile ---------------------------------

rm -rf "$TRACES" "$REPORT"
mkdir -p "$TRACES" "$REPORT"
# %p: one file per process. Two runs with the same pid would share a file;
# the count below would then fall short and fail the script.
export LLVM_PROFILE_FILE="$ROOT/$TRACES/%p.profraw"

status=0
FFI_LIB="$LIB" FFI_OUT="$COV/ffi" GITHUB_STEP_SUMMARY='' \
  "$ROOT/scripts/check-ffi.sh" "$@" || status=$?
unset LLVM_PROFILE_FILE
[ "$status" -le 1 ] || exit "$status"

runs="$(grep -vc '^#' "$COV/ffi/ffi-results.txt" || true)"
traces=("$TRACES"/*.profraw)
[ -e "${traces[0]}" ] || traces=()
echo ">> $runs cryptol run(s), ${#traces[@]} profile(s)"
if [ "${#traces[@]}" -ne "$runs" ]; then
  echo "!! expected one profile per cryptol run" >&2
  status=1
fi
[ "${#traces[@]}" -gt 0 ] || die "no profile to report on"

# --- 3. the report -----------------------------------------------------------------------

echo ">> merging ${#traces[@]} profiles"
"$LLVM_PROFDATA" merge -sparse "${traces[@]}" -o "$COV/merged.profdata"
COV_ARGS=("$LIB" -instr-profile="$COV/merged.profdata")
"$LLVM_COV" export "${COV_ARGS[@]}" > "$REPORT/export.json"
"$LLVM_COV" report "${COV_ARGS[@]}" --show-branch-summary \
  "$ROOT/src" > "$REPORT/report.txt"
"$LLVM_COV" report "${COV_ARGS[@]}" --show-functions --show-branch-summary \
  "$ROOT/src" >> "$REPORT/report.txt"
"$LLVM_COV" show "${COV_ARGS[@]}" -format=html -show-branches=count \
  -show-line-counts-or-regions -output-dir="$REPORT/html" "$ROOT/src"

explained=0
python3 "$ROOT/scripts/coverage-summary.py" "$REPORT/export.json" "$ROOT/src" \
  --units "$UNITS" --explained "$EXPLAINED" \
  > "$REPORT/summary.txt" || explained=$?
cat "$REPORT/summary.txt"
case "$explained" in
  0) ;;
  1) echo "!! a violation is not explained in verus/$EXPLAINED (close it with a property, or explain it), or verus/$UNITS is stale" >&2
     status=1 ;;
  *) die "coverage-summary.py failed" ;;
esac

if [ -n "${GITHUB_STEP_SUMMARY-}" ]; then
  {
    echo "### Coverage under the FFI properties (region, line, branch; no MC/DC)"
    echo
    echo '```'
    cat "$REPORT/summary.txt"
    echo '```'
  } >> "$GITHUB_STEP_SUMMARY"
fi

if [ "$status" -ne 0 ]; then
  echo "!! COVERAGE RUN FAILED -- see above; report: verus/$REPORT"
  exit 1
fi
echo ">> coverage report: verus/$REPORT (summary.txt, report.txt, html/)"

# --- 4. the record ------------------------------------------------------------------------

# A run of every property on a clean tree (outside the record itself)
# writes coverage/results.txt, the provenance of the numbers doc/coverage.md
# quotes (the SPARK crate measures in CI; this crate has none). The record
# names HEAD, so a dirty tree or a partial run writes none.
if [ "$#" -gt 0 ]; then
  echo ">> partial run: $RESULTS not written"
elif [ -n "$(git status --porcelain -- . ":(exclude)$RESULTS")" ]; then
  echo ">> the tree is not clean: $RESULTS not written (it names HEAD; commit first)"
else
  {
    echo "# coverage/results.txt -- written by scripts/check-coverage.sh; do not edit."
    echo "#"
    echo "# Coverage of the Verus crate's executable code under every FFI property"
    echo "# (cryptol/properties.txt): regions, lines and branch outcomes, from"
    echo "# rustc's $FLAGS."
    echo "# No MC/DC: rustc has no MC/DC instrumentation. doc/coverage.md."
    echo
    echo "commit      $(git rev-parse HEAD)"
    echo "date        $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "rustc       $(rustc -vV | sed -n 's/^release: //p') ($(rustc -vV | sed -n 's/^commit-hash: //p' | cut -c1-9)), LLVM $(rustc -vV | sed -n 's/^LLVM version: //p')"
    echo "llvm-cov    $("$LLVM_COV" --version | sed -n 's/.*LLVM version //p' | head -n 1)"
    echo "cryptol     $("$CRYPTOL" --version | head -n 1)"
    echo "properties  $runs, $runs profiles"
    echo
    cat "$REPORT/summary.txt"
  } > "$RESULTS"
  echo ">> wrote verus/$RESULTS"
fi
