#!/usr/bin/env bash
#
# check-ffi.sh -- run every FFI property: the Verus crate's executable
# functions against the NSA Cryptol, through Cryptol's foreign function
# interface.
#
# The counterpart of the SPARK crate's spark/scripts/check-ffi.sh
# (github.com/manthonyaiello/Foundation, tag spark-v1.0). It differs in
# step 1 (cargo builds ffi/, a cdylib of the crate's src/ffi/, where the
# SPARK script runs gprbuild on foundation_spark_ffi.gpr) and in paths
# (target/ffi for obj/ffi); doc/ffi.md says what the properties cover.
#
# 1. Builds the FFI library (ffi/Cargo.toml: a cdylib re-exporting the
#    crate's src/ffi/, release profile with overflow checks and debug
#    assertions).
# 2. Links it beside every module under cryptol/ as <File>.so (<File>.dylib
#    on macOS), which is where Cryptol looks for a module's foreign
#    implementations. The links are build output (gitignored).
# 3. Runs each property of cryptol/properties.txt in its own `cryptol -b`,
#    with :exhaust or :check, and writes target/ffi/ffi-results.txt (the FFI
#    log, in the format of the SPARK crate's, which its scripts/board.py
#    reads; README "The board" there).
#
# A property passes only when ALL of these hold, because Cryptol 3.6 can
# report a run that never called Verus without failing it:
#
#   * cryptol exits 0, and its output has no ERROR and no counterexample;
#   * the property's module loaded its library: "Loading module <M>" is
#     followed by "Loading dynamic library <File>.so". A body-less foreign
#     whose library is missing does NOT stop the module from loading:
#     Cryptol warns ("Could not load all foreign implementations") and only
#     the calls fail;
#   * no module outside cryptol/ loaded a dynamic library. NSA's foreign
#     declarations with Cryptol bodies (AES::Cipher, AES::KeyExpansion,
#     Keccak::StepMappings) fall back to their Cryptol bodies when their
#     Rust library is absent, as it is in this repository (the .so files are
#     symlinks into unbuilt rust/*/target/). That fallback is what we want:
#     the properties compare Verus with the Cryptol. If someone builds the
#     Rust, the comparison would silently become Verus against NSA's Rust, so a
#     library loaded by any other module fails the run;
#   * Cryptol reports "Passed N tests" with N the property's planned count
#     (for :exhaust, the size of the domain), and Q.E.D. for :exhaust.
#
# A failing property is logged with passed = 0: Cryptol stops at the first
# counterexample and does not say how many tests passed before it.
#
# Usage (from anywhere; needs cargo and the toolchain of rust-toolchain.toml):
#   scripts/check-ffi.sh                 build, run every property
#   scripts/check-ffi.sh PROPERTY ...    build, run only these properties
#                                        (the log then holds only these)
#
# Env:
#   CRYPTOL     the cryptol binary (default: cryptol). It must report
#               "FFI enabled" in `cryptol --version`. On macOS, a binary
#               signed with the hardened runtime (Galois's release) is run
#               through an ad hoc signed copy under FFI_OUT (see step 0).
#   FFI_JOBS    cargo -j (default: nproc). On a shared machine, set it.
#   CARGO       the cargo binary (default: cargo).
#   FFI_LIB     a library already built, to run the properties against
#               instead of building ffi/ (relative to verus/), as
#               scripts/check-coverage.sh passes an instrumented one.
#   FFI_OUT     where the runs and the log go (default: target/ffi, relative
#               to verus/).
#
# Exit status: 0 when every property passed, 1 when one failed, 2 on a usage
# or setup error.
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO="$(cd "$ROOT/.." && pwd)"
cd "$ROOT"

CARGO="${CARGO:-cargo}"
CRYPTOL="${CRYPTOL:-cryptol}"
JOBS="${FFI_JOBS:-$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN)}"

PROPS="cryptol/properties.txt"
OUT="${FFI_OUT:-target/ffi}"
RUN="$OUT/run"
LOG="$OUT/ffi-results.txt"

case "$(uname -s)" in
  Darwin) EXT=dylib ;;
  *)      EXT=so ;;
esac
LIB="${FFI_LIB:-target/release/libfoundation_verus_ffi.$EXT}"

die() { echo "check-ffi.sh: $*" >&2; exit 2; }
trim() { local s="$1"; s="${s#"${s%%[![:space:]]*}"}"; printf '%s' "${s%"${s##*[![:space:]]}"}"; }

found="$(command -v "$CRYPTOL" 2>/dev/null)" || die "$CRYPTOL not found (put it on PATH, or set CRYPTOL)"
# Why absolute: the runs below are from $REPO, not from here, so a cryptol
# found through a relative PATH entry (or a relative CRYPTOL) would not be
# found there, and every property would fail with exit status 127.
case "$found" in
  /*) CRYPTOL="$found" ;;
  *)  CRYPTOL="$(cd "$(dirname "$found")" && pwd)/$(basename "$found")" ;;
esac
"$CRYPTOL" --version | grep -q "FFI enabled" \
  || die "$CRYPTOL was built without FFI support"
[ -f "$PROPS" ] || die "missing $PROPS"

# --- 0. macOS: a Cryptol that may load our library -------------------------------

# Why re-sign: Galois's macOS Cryptol has the hardened runtime without
# disable-library-validation, so dlopen refuses our (differently signed)
# library. We run an ad hoc signed copy under $OUT/cryptol-adhoc instead;
# the installed binary is never modified.
if [ "$(uname -s)" = Darwin ]; then
  # Captured, not piped into grep -q: under pipefail, codesign killed by
  # SIGPIPE would fail the test.
  src="$(command -v "$CRYPTOL")"
  sig="$(codesign -dv "$src" 2>&1 || true)"
  ent="$(codesign -d --entitlements - "$src" 2>/dev/null || true)"
  if [[ "$sig" == *"flags="*"(runtime)"* ]] \
     && [[ "$ent" != *"com.apple.security.cs.disable-library-validation"* ]]; then
    adhoc_dir="$ROOT/$OUT/cryptol-adhoc"
    adhoc="$adhoc_dir/cryptol"
    if [ ! -x "$adhoc" ] || [ "$src" -nt "$adhoc" ] \
       || [ "$(cat "$adhoc_dir/source" 2>/dev/null)" != "$src" ]; then
      echo ">> $src has the hardened runtime: making an ad hoc signed copy in $OUT/cryptol-adhoc"
      mkdir -p "$adhoc_dir"
      cp "$src" "$adhoc"
      codesign --force --sign - "$adhoc" 2>/dev/null \
        || die "codesign could not re-sign $adhoc"
      printf '%s\n' "$src" > "$adhoc_dir/source"
    fi
    CRYPTOL="$adhoc"
    "$CRYPTOL" --version | grep -q "FFI enabled" \
      || die "$CRYPTOL (the ad hoc signed copy of $src) does not run"
  fi
fi

# --- 1. the library ------------------------------------------------------------

if [ -n "${FFI_LIB-}" ]; then
  [ -f "$LIB" ] || die "FFI_LIB: no library $LIB"
  echo ">> using the library $LIB (FFI_LIB)"
else
  echo ">> building the FFI library (ffi/, -j$JOBS)"
  # ffi/ is its own workspace; its target directory is the crate's.
  (cd ffi && CARGO_TARGET_DIR="$ROOT/target" "$CARGO" build --release --quiet --locked -j"$JOBS")
  [ -f "$LIB" ] || die "the build did not produce $LIB"
fi

# --- 2. the links ---------------------------------------------------------------

# Our modules: every .cry under cryptol/, by its module name. Each gets the
# library beside it, and only these may load one.
#
# OURS is a newline-separated list, not an associative array, and the link's
# relative path comes from python3, not `realpath --relative-to`: macOS ships
# bash 3.2 and a BSD realpath, and the script runs there too.
OURS=""
while IFS= read -r cry; do
  mod="$(sed -nE 's/^[[:space:]]*module[[:space:]]+([A-Za-z0-9_:]+)[[:space:]]+where.*/\1/p' "$cry" | head -n 1)"
  [ -n "$mod" ] || die "$cry declares no module"
  OURS="${OURS}${mod}"$'\n'
  dir="$(dirname "$cry")"
  rel="$(python3 -c 'import os, sys; print(os.path.relpath(os.path.realpath(sys.argv[1]), os.path.realpath(sys.argv[2])))' "$LIB" "$dir")"
  ln -sfn "$rel" "$dir/$(basename "$cry" .cry).$EXT"
done < <(find cryptol -name '*.cry' | sort)

# --- 3. the properties -------------------------------------------------------------

mkdir -p "$RUN"
COMMIT="$(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo unknown)"
if [ -n "$(git -C "$ROOT" status --porcelain -- . 2>/dev/null)" ]; then
  echo "!! the tree has uncommitted changes: the log names $COMMIT, but the library was built from the working tree" >&2
fi

export CRYPTOLPATH="$REPO:$ROOT/cryptol"

{
  echo "# FFI log written by scripts/check-ffi.sh at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "# $("$CRYPTOL" --version | head -n 1), library $LIB"
  echo "# property | function | mode | run | passed | commit"
} > "$LOG"

want=("$@")
fail=0
ran=0

# Checks the output of one run (file $1) of property $2 from module $3, whose
# library file is $4, planned as $5 tests in mode $6. Prints what is wrong and
# returns 1, or prints the number of tests that passed and returns 0.
judge() {
  local out="$1" prop="$2" mod="$3" lib="$4" n="$5" mode="$6" bad=0 passed
  awk -v mod="$mod" -v lib="$lib" '
    BEGIN { split("", ours) }
    FNR == NR { ours[$0] = 1; next }
    /^Loading module / { cur = $3; if (cur == mod) seen = 1; next }
    /Could not load all foreign implementations for module / {
      m = $0; sub(/.*for module /, "", m); sub(/:[ \t]*$/, "", m)
      if (m in ours) { print "module " m " did not load its foreign implementations"; bad = 1 }
      next
    }
    /^Loading dynamic library / {
      if (!(cur in ours)) { print "module " cur " (not ours) loaded " $4; bad = 1 }
      if (cur == mod && $4 == lib) loaded = 1
      next
    }
    END {
      if (!seen)   { print "module " mod " was not loaded"; bad = 1 }
      if (!loaded) { print "module " mod " did not load its library " lib; bad = 1 }
      exit bad
    }
  ' <(printf '%s' "$OURS") "$out" || bad=1
  if grep -qE 'ERROR|Counterexample|\[error\]' "$out"; then
    grep -E 'ERROR|Counterexample|\[error\]' "$out" | head -n 5
    bad=1
  fi
  passed="$(sed -nE 's/.*Passed ([0-9]+) tests\..*/\1/p' "$out" | tail -n 1)"
  if [ "$passed" != "$n" ]; then
    echo "expected \"Passed $n tests.\", got ${passed:-none}"
    bad=1
  fi
  if [ "$mode" = exhaust ] && ! grep -q '^Q\.E\.D\.' "$out"; then
    echo "no Q.E.D. from :exhaust"
    bad=1
  fi
  [ "$bad" -eq 0 ] || return 1
  echo "$passed"
}

while IFS='|' read -r file prop func mode n; do
  file="$(trim "$file")"; prop="$(trim "$prop")"; func="$(trim "$func")"
  mode="$(trim "$mode")"; n="$(trim "$n")"
  case "$file" in ''|'#'*) continue ;; esac
  if [ "${#want[@]}" -gt 0 ] && [[ ! " ${want[*]} " == *" $prop "* ]]; then
    continue
  fi
  [ -f "cryptol/$file" ] || die "$PROPS: no module cryptol/$file"
  case "$mode" in exhaust|check) ;; *) die "$PROPS: $prop: mode must be exhaust or check" ;; esac
  [[ "$n" =~ ^[0-9]+$ ]] || die "$PROPS: $prop: tests must be a number"
  mod="$(sed -nE 's/^[[:space:]]*module[[:space:]]+([A-Za-z0-9_:]+)[[:space:]]+where.*/\1/p' "cryptol/$file" | head -n 1)"

  script="$RUN/$prop.icry"
  {
    [ "$mode" = check ] && echo ":set tests=$n"
    echo ":load $ROOT/cryptol/$file"
    echo ":$mode $prop"
  } > "$script"

  echo ">> $prop ($func): :$mode, $n tests"
  status=0
  t0=$SECONDS
  (cd "$REPO" && "$CRYPTOL" -b "$ROOT/$script") > "$RUN/$prop.out" 2>&1 || status=$?
  ran=$((ran + 1))
  secs=$((SECONDS - t0))

  verdict=0
  result="$(judge "$RUN/$prop.out" "$prop" "$mod" "$(basename "$file" .cry).$EXT" "$n" "$mode")" || verdict=1
  if [ "$status" -ne 0 ]; then
    result="cryptol exited $status"$'\n'"$result"
    verdict=1
  fi

  if [ "$verdict" -eq 0 ]; then
    echo "   PASS  $prop: :$mode $result/$n (${secs} s)"
    echo "$prop | $func | $mode | $n | $result | $COMMIT" >> "$LOG"
  else
    fail=1
    echo "   FAIL  $prop: :$mode (${secs} s; output: verus/$RUN/$prop.out)"
    printf '%s\n' "$result" | sed '/^$/d; s/^/         /'
    echo "$prop | $func | $mode | $n | 0 | $COMMIT" >> "$LOG"
  fi
done < "$PROPS"

[ "$ran" -gt 0 ] || die "no property ran"

if [ -n "${GITHUB_STEP_SUMMARY-}" ]; then
  {
    echo "### FFI properties"
    echo
    echo '```'
    grep -v '^#' "$LOG"
    echo '```'
  } >> "$GITHUB_STEP_SUMMARY"
fi

if [ "$fail" -ne 0 ]; then
  echo "!! FFI CHECK FAILED -- log: verus/$LOG"
  exit 1
fi
echo ">> FFI OK -- $ran propert$( [ "$ran" -eq 1 ] && echo y || echo ies ) passed. Log: verus/$LOG"
