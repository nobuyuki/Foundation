#!/usr/bin/env bash
#
# check-saw.sh -- SAW's proofs of the Verus crate's AES, SHA-256 and
# HMAC-SHA-256 implementations against NSA's Cryptol, by two routes: on
# rustc's LLVM bitcode of the crate (llvm_verify, the SPARK crate's route)
# and on its MIR (mir_verify, the route of NSA's own Rust proofs,
# algorithms/AES/rust/*/theorems/saw.py). doc/saw.md says what is proved.
#
# The counterpart of the SPARK crate's spark/scripts/check-saw.sh
# (github.com/manthonyaiello/Foundation, tag spark-v1.0). It differs in
# step 1 (rustc makes the bitcode of the whole library, one module, where
# the SPARK script compiles each unit with GNAT Pro's llvm-gcc and links
# them with llvm-link; and mir-json makes its MIR), in step 2 (the Verus
# spec layer is erased from every build, so there is no spec layer to
# prove: doc/saw.md, "The spec layer"), and in having the MIR route.
#
# LOCAL ONLY: never wired into a CI workflow (as the SPARK crate's). Every
# run records its provenance in saw/results.txt: the commit, the date, the
# tool versions, the compiler switches, the sha256 of the bitcode and the
# MIR, of each source rustc read for the bitcode and of each Cryptol file
# imported, every result, the negative controls' counterexamples, and the
# wall-clock.
#
# What it does, for each route of SAW_ROUTE (llvm, then mir):
#   1. llvm: compiles the library (src/lib.rs) with rustc of
#      rust-toolchain.toml to LLVM bitcode, saw/obj/foundation_verus.bc
#      (SWITCHES below), and writes saw/obj/symbols.saw, which binds each of
#      the crate's function symbols to a name the scripts use (rustc's
#      mangled names hold a hash of the crate: saw/llvm/aes_impl_common.saw);
#      mir: compiles it with mir-json (cargo saw-build, on the nightly
#      toolchain mir-json is built for) to
#      saw/obj/mir/foundation_verus.linked-mir.json;
#   2. checks that no proof function (lemma_*) is in it (Verus erases spec
#      and proof code from a cargo build; a lemma there would mean it was
#      not);
#   3. refuses any *_unsafe_assume_spec or admit in saw/ (every override
#      must be a proof, every goal proved by a solver), then runs
#      saw/<route>/aes_impl.saw and saw/<route>/sha256_impl.saw, every
#      proof of which must succeed;
#   4. runs each saw/<route>/negative/*.saw, every one of which must FAIL
#      with a counterexample (the negative controls);
# and then
#   5. writes saw/results.txt (unless --print).
#
# Every saw run is in its own systemd scope capped at SAW_MEMORY_MAX (10G,
# no swap) when systemd-run --user works, so that a proof that blows up is
# killed alone instead of taking the machine down. A run killed by the cap
# is a failure, reported as such. Without systemd-run the runs are not
# capped, and the script says so.
#
# Usage (from anywhere):
#   scripts/check-saw.sh           run, and record saw/results.txt
#   scripts/check-saw.sh --print   run, and print the record instead
#
# Recording needs a clean tree (outside saw/results.txt): the record names
# HEAD as the commit checked, and a dirty tree is not HEAD.
#
# Env:
#   MIR_JSON_DIR   REQUIRED for the mir route: a mir-json install, with
#                  bin/ (mir-json, cargo-saw-build) and rlibs/ (the standard
#                  library translated by mir-json-translate-libs). Its
#                  schema must be SAW's (13 for SAW 1.6), and its toolchain
#                  (`mir-json --version` names it) installed with rustup.
#                  doc/bootstrap.md installs 8cbf9af, the commit SAW 1.6
#                  bundles.
#   SAW_ROUTE      optional: all (the default), llvm or mir. Anything but
#                  all is a partial run, never a record: it needs --print.
#   SAW_MEMORY_MAX optional: the memory cap of each saw run (default 10G).
#   CARGO          the cargo binary (default: cargo).
#   saw and z3 must be on PATH (the bin/ of SAW's 1.6 release with solvers
#   holds both); and GNU c++filt.
#
# Exit status: 0 when every proof passed and every negative control failed;
# 1 otherwise; 2 on a usage error.
#
set -euo pipefail

VERUS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ROOT_DIR="$(cd "$VERUS_DIR/.." && pwd)"
SAW_DIR="$VERUS_DIR/saw"
OBJ_DIR="$SAW_DIR/obj"
MIR_OBJ_DIR="$OBJ_DIR/mir"
RESULTS="$SAW_DIR/results.txt"
CARGO="${CARGO:-cargo}"

die() { printf '!! %s\n' "$*" >&2; exit 1; }

PRINT=0
case "${1:-}" in
  "") ;;
  --print) PRINT=1 ;;
  -h|--help) sed -n '2,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d'; exit 0 ;;
  *) echo "check-saw.sh: unknown argument: $1" >&2; exit 2 ;;
esac

SAW_ROUTE="${SAW_ROUTE:-all}"
case "$SAW_ROUTE" in
  all) ROUTES=(llvm mir) ;;
  llvm|mir) ROUTES=("$SAW_ROUTE") ;;
  *) echo "check-saw.sh: SAW_ROUTE must be all, llvm or mir, not $SAW_ROUTE" >&2; exit 2 ;;
esac
if [ "$SAW_ROUTE" != all ] && [ "$PRINT" -eq 0 ]; then
  echo "check-saw.sh: SAW_ROUTE=$SAW_ROUTE is a partial run, not a record: add --print" >&2
  exit 2
fi
has_route() { case " ${ROUTES[*]} " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }

# --- the toolchain -------------------------------------------------------------

for t in saw z3 c++filt; do
  command -v "$t" >/dev/null 2>&1 || die "$t is not on PATH (saw and z3: the bin/ of SAW 1.6's release; c++filt: GNU binutils)"
done

# Captured, not piped into head: a tool can die of SIGPIPE under pipefail.
first_line() { local out; out="$("$@" 2>&1)" || true; printf '%s\n' "${out%%$'\n'*}"; }
V_SAW="$(first_line saw --version)"
V_Z3="$(first_line z3 --version)"
V_CXXFILT="$(first_line c++filt --version)"
cd "$VERUS_DIR"
V_RUSTC="$(rustc -vV | sed -n 's/^release: //p') ($(rustc -vV | sed -n 's/^commit-hash: //p' | cut -c1-9)), LLVM $(rustc -vV | sed -n 's/^LLVM version: //p')"
V_CARGO="$(first_line "$CARGO" --version)"

# mir-json, for the mir route: its schema must be the one SAW reads.
SAW_MIR_SCHEMA=13  # SAW 1.6's (its README, "Rust"); SAW refuses any other
if has_route mir; then
  [ -n "${MIR_JSON_DIR:-}" ] || die "MIR_JSON_DIR is unset: the mir route needs a mir-json install
   (bin/ and rlibs/; doc/bootstrap.md), or run SAW_ROUTE=llvm --print"
  [ -x "$MIR_JSON_DIR/bin/mir-json" ] && [ -x "$MIR_JSON_DIR/bin/cargo-saw-build" ] \
    || die "MIR_JSON_DIR=$MIR_JSON_DIR has no bin/mir-json and bin/cargo-saw-build"
  [ -d "$MIR_JSON_DIR/rlibs" ] || die "MIR_JSON_DIR=$MIR_JSON_DIR has no rlibs/ (run mir-json-translate-libs)"
  V_MIR_JSON_ALL="$("$MIR_JSON_DIR/bin/mir-json" --version 2>&1 || true)"
  V_MIR_JSON="$(printf '%s\n' "$V_MIR_JSON_ALL" | grep '^mir-json ')"
  MIR_TOOLCHAIN="$(printf '%s\n' "$V_MIR_JSON_ALL" | sed -n 's/^Rust toolchain //p')"
  [ -n "$MIR_TOOLCHAIN" ] || die "mir-json --version names no Rust toolchain"
  case "$V_MIR_JSON" in
    *"schema version $SAW_MIR_SCHEMA)"*) ;;
    *) die "mir-json's schema is not $SAW_MIR_SCHEMA, which SAW reads: $V_MIR_JSON" ;;
  esac
  V_MIR_RUSTC="$(printf '%s\n' "$V_MIR_JSON_ALL" | grep '^rustc ')"
  V_MIR_COMMIT="$(git -C "$MIR_JSON_DIR/src" rev-parse HEAD 2>/dev/null || echo "unknown (no src/ checkout)")"
  export SAW_RUST_LIBRARY_PATH="$MIR_JSON_DIR/rlibs"
fi

# The commit checked, and whether the tree is clean.
COMMIT="$(git -C "$ROOT_DIR" rev-parse HEAD)"
DIRTY=""
if [ -n "$(git -C "$ROOT_DIR" status --porcelain -- . ":(exclude)${RESULTS#"$ROOT_DIR"/}")" ]; then
  [ "$PRINT" -eq 1 ] || die "the tree is not clean: commit first, or run with --print (a record names HEAD)"
  DIRTY=" (with uncommitted changes: --print only)"
fi

# The memory cap.
SAW_MEMORY_MAX="${SAW_MEMORY_MAX:-10G}"
CAP=()
if systemd-run --user --scope --quiet -p MemoryMax=1G -p MemorySwapMax=0 true >/dev/null 2>&1; then
  CAP=(systemd-run --user --scope --quiet -p "MemoryMax=$SAW_MEMORY_MAX" -p MemorySwapMax=0)
  CAP_NOTE="each saw run in its own systemd scope, MemoryMax=$SAW_MEMORY_MAX, MemorySwapMax=0"
else
  CAP_NOTE="none (systemd-run --user does not work here): the saw runs are not capped"
  echo ">> WARNING: $CAP_NOTE" >&2
fi

T0="$(date +%s)"

# --- 1. the bitcode --------------------------------------------------------------

# -O0 (the dev profile), with its overflow checks and debug assertions:
# the checks' panics are calls SAW must find unreachable at the sizes
# proved. codegen-units=1: one module, so that every override is of the
# module verified. No debug info. -C no-prepopulate-passes: no LLVM pass
# runs, not even the always-inliner, which at -O0 still inlines the
# #[inline(always)] functions (the SHA-2 ROTR, SHR, SIGMA and sigma, Ch,
# Maj) into compress, where no proof of them could be its override
# (doc/saw.md, "The bitcode"). rustc's own MIR inlining is off at -O0.
SWITCHES=(--emit=llvm-bc,llvm-ir,dep-info -C codegen-units=1 -C debuginfo=0 -C no-prepopulate-passes)
TARGET_DIR="$OBJ_DIR/target"
rm -rf "$OBJ_DIR"
mkdir -p "$OBJ_DIR"
BC="$OBJ_DIR/foundation_verus.bc"
LL="$OBJ_DIR/foundation_verus.ll"
DEP="$OBJ_DIR/foundation_verus.d"
MIR_JSON="$MIR_OBJ_DIR/foundation_verus.linked-mir.json"
N_SYMBOLS=0
if has_route llvm; then
echo ">> cargo rustc --lib -- ${SWITCHES[*]}"
CARGO_INCREMENTAL=0 "$CARGO" rustc --lib --quiet --target-dir "$TARGET_DIR" -- "${SWITCHES[@]}"
deps="$TARGET_DIR/debug/deps"
bc_src="$(ls "$deps"/foundation_verus-*.bc)"
[ "$(printf '%s\n' "$bc_src" | wc -l)" -eq 1 ] || die "more than one foundation_verus-*.bc in $deps"
cp "$bc_src" "$BC"
cp "${bc_src%.bc}.ll" "$LL"
cp "${bc_src%.bc}.d" "$DEP"

# The symbols: every function the bitcode defines, demangled (rustc's v0
# scheme; GNU c++filt reads it), and for each of the crate's own (not of
# its ffi module, nor a closure or a trait impl) a binding
#   let rust__<path> = "<symbol>";
# with the path's "::" as "__" and a const generic argument <128: u32> as
# "__128". Two functions with one name would be a bug of this mapping.
grep '^define' "$LL" | grep -o '@_R[A-Za-z0-9_]*' | sed 's/^@//' > "$OBJ_DIR/mangled.txt"
c++filt < "$OBJ_DIR/mangled.txt" > "$OBJ_DIR/demangled.txt"
paste "$OBJ_DIR/mangled.txt" "$OBJ_DIR/demangled.txt" | awk -F'\t' '
  {
    m = $1; d = $2
    if (d !~ /^foundation_verus\[[0-9a-f]+\]::/) next
    sub(/^foundation_verus\[[0-9a-f]+\]::/, "", d)
    if (d ~ /^ffi::/) next
    while (match(d, /::<[0-9]+: u32>/)) {
      arg = substr(d, RSTART + 3, RLENGTH - 3); sub(/: u32>$/, "", arg)
      d = substr(d, 1, RSTART - 1) "__" arg substr(d, RSTART + RLENGTH)
    }
    gsub(/::/, "__", d)
    if (d !~ /^[A-Za-z0-9_]+$/) next
    if (d in seen) { print "check-saw.sh: two functions named " d > "/dev/stderr"; bad = 1 }
    seen[d] = 1
    printf "let rust__%s = \"%s\";\n", d, m
  }
  END { exit bad }
' > "$OBJ_DIR/symbols.saw" || die "the symbol map is ambiguous (above)"
N_SYMBOLS="$(grep -c '^let ' "$OBJ_DIR/symbols.saw")"
echo ">> saw/obj/symbols.saw: $N_SYMBOLS functions of the crate"

# --- 2. the bitcode holds no proof code -------------------------------------------

lemmas="$(grep -E '::lemma_|^lemma_' "$OBJ_DIR/demangled.txt" || true)"
[ -z "$lemmas" ] || die "proof functions in the bitcode (Verus should have erased them):
$lemmas"
echo ">> foundation_verus.bc: $(wc -l < "$OBJ_DIR/mangled.txt") functions defined, no lemma_"
fi

# The MIR: mir-json's cargo saw-build, on mir-json's toolchain, with the
# standard library it translated (SAW_RUST_LIBRARY_PATH). saw-build is
# cargo test's build, so the crate is compiled with cfg(test) (its unit
# tests are in the MIR too; the functions proved are the same source).
# The dev profile: -O0, at which rustc's MIR inliner is off, so the
# #[inline(always)] functions stay calls (as -C no-prepopulate-passes
# keeps them in the bitcode).
if has_route mir; then
  echo ">> cargo saw-build --lib (mir-json, $MIR_TOOLCHAIN)"
  mkdir -p "$MIR_OBJ_DIR"
  PATH="$MIR_JSON_DIR/bin:$PATH" RUSTUP_TOOLCHAIN="$MIR_TOOLCHAIN" CARGO_INCREMENTAL=0 \
    "$CARGO" saw-build --lib --quiet --target-dir "$MIR_OBJ_DIR/target" > "$MIR_OBJ_DIR/saw-build.log" 2>&1 \
    || { tail -20 "$MIR_OBJ_DIR/saw-build.log" >&2; die "cargo saw-build failed (log: $MIR_OBJ_DIR/saw-build.log)"; }
  json_src="$(find "$MIR_OBJ_DIR/target" -name 'foundation_verus-*.linked-mir.json')"
  [ "$(printf '%s\n' "$json_src" | wc -l)" -eq 1 ] || die "not one foundation_verus-*.linked-mir.json under $MIR_OBJ_DIR/target"
  cp "$json_src" "$MIR_JSON"
  # The crate's functions in it, by name (mir-json's own names, crate
  # paths with a hash), for the lemma check.
  grep -o '"name": *"foundation_verus/[0-9a-f]*::[^"]*"' "$MIR_JSON" | sed 's/^"name": *"//; s/"$//' | sort -u > "$MIR_OBJ_DIR/names.txt" || true
  [ -s "$MIR_OBJ_DIR/names.txt" ] || die "no function of the crate found in $MIR_JSON"
  lemmas="$(grep -E '::lemma_' "$MIR_OBJ_DIR/names.txt" || true)"
  [ -z "$lemmas" ] || die "proof functions in the MIR (Verus should have erased them):
$lemmas"
  echo ">> foundation_verus.linked-mir.json: $(wc -l < "$MIR_OBJ_DIR/names.txt") names of the crate, no lemma_"
fi

# --- 3. the proofs ---------------------------------------------------------------------

# No assumption: every override must be a proof, and every goal proved by a
# solver. Refused: an assumed spec (llvm_unsafe_assume_spec), and the
# tactics that prove nothing, admit and its older names assume_unsat and
# assume_valid, matched as whole words, comments included.
assumed="$(grep -rn --include='*.saw' -E '_unsafe_assume|(^|[^[:alnum:]_])(admit|assume_unsat|assume_valid)([^[:alnum:]_]|$)' "$SAW_DIR" \
  | grep -v "^$OBJ_DIR/" || true)"
[ -z "$assumed" ] || die "an assumed spec or admit in saw/: every override and goal must be proved:
$assumed"

export CRYPTOLPATH="$ROOT_DIR"
LOG_DIR="$OBJ_DIR/logs"
mkdir -p "$LOG_DIR"

KILLED_BY_CAP=137  # 128 + SIGKILL: what a scope killed by its MemoryMax returns

run_saw() {  # run_saw ROUTE FILE LOG: saw FILE from saw/ROUTE/, capped, its output in LOG
  local status=0
  (cd "$SAW_DIR/$1" && "${CAP[@]+"${CAP[@]}"}" saw "$2") > "$3" 2>&1 || status=$?
  if [ "$status" -eq "$KILLED_BY_CAP" ] && [ "${#CAP[@]}" -gt 0 ]; then
    echo "!! KILLED (SIGKILL): saw $1/$2 reached the memory cap ($SAW_MEMORY_MAX)" >> "$3"
  fi
  return "$status"
}

PROVED=()
T_PROOFS=()
NEGATIVE=()
N_PROVED=0
for route in "${ROUTES[@]}"; do
  case "$route" in
    llvm) verb=llvm_verify ;;
    mir) verb=mir_verify ;;
  esac
  for name in aes_impl sha256_impl; do
    script="$name.saw"
    log="$LOG_DIR/$route-$name.log"
    echo ">> saw $route/$script"
    t="$(date +%s)"
    status=0
    run_saw "$route" "$script" "$log" || status=$?
    if [ "$status" -ne 0 ]; then
      grep -v 'override\|^Matching\|^Branching\|^  variant' "$log" | tail -40 >&2
      [ "$status" -ne "$KILLED_BY_CAP" ] || die "saw $route/$script was KILLED by the memory cap ($SAW_MEMORY_MAX): a failure (log: $log)"
      die "saw $route/$script FAILED (log: $log)"
    fi
    T_PROOFS+=("$(( $(date +%s) - t )) s for $route/$script")
    # Each RESULT line, with the time SAW's `time` printed just before it
    # for that proof (the common files' verify_symbol).
    mod_proved=()
    while IFS= read -r line; do mod_proved+=("$line"); done < <(awk -v route="$route" -v verb="$verb" '
      /^Time: / { t = $2; sub(/s$/, "", t) }
      /^RESULT proved / { sub(/^RESULT proved /, ""); printf "%s %s: %s, %.2f s\n", route, verb, $0, t; t = "" }
    ' "$log")
    [ "${#mod_proved[@]}" -gt 0 ] || die "saw $route/$script proved nothing (log: $log)"
    n_succeeded="$(grep -c '^Proof succeeded!' "$log" || true)"
    [ "$n_succeeded" -eq "${#mod_proved[@]}" ] \
      || die "$route/$script: $n_succeeded proofs succeeded but there are ${#mod_proved[@]} RESULT lines"
    N_PROVED=$(( N_PROVED + ${#mod_proved[@]} ))
    for p in "${mod_proved[@]}"; do echo "   proved $p"; PROVED+=("$p"); done
  done

  # --- 4. the negative controls -------------------------------------------------------------
  n_neg=0
  for f in "$SAW_DIR/$route"/negative/*.saw; do
    [ -e "$f" ] || continue
    name="negative/$(basename "$f")"
    log="$LOG_DIR/$route-$(basename "$f" .saw).log"
    echo ">> saw $route/$name (must fail)"
    status=0
    run_saw "$route" "$name" "$log" || status=$?
    [ "$status" -ne 0 ] || die "NEGATIVE CONTROL PROVED: $route/$name must fail (log: $log)"
    [ "$status" -ne "$KILLED_BY_CAP" ] \
      || die "$route/$name was KILLED by the memory cap ($SAW_MEMORY_MAX), not refuted (log: $log)"
    grep -q '^Proof failed\.' "$log" && grep -q -- '-Counterexample-' "$log" \
      || { tail -20 "$log" >&2; die "$route/$name failed without a counterexample (log: $log)"; }
    target="$(sed -n 's/^Verifying \(.*\) *\.\.\.$/\1/p' "$log" | tail -1 | sed 's/ *$//' | c++filt | sed 's/\[[0-9a-f]*\]//g')"
    cex="$(sed -n '/-Counterexample-/,/^---*$/p' "$log" | sed '1d;$d' | sed 's/^ *//' | tr '\n' ' ' | sed 's/ $//')"
    t_neg="$(awk '/^Time: / { t = $2 } END { sub(/s$/, "", t); if (t != "") printf "%.2f s", t }' "$log")"
    NEGATIVE+=("$route/$name: $target fails${t_neg:+ in $t_neg}, counterexample $cex")
    echo "   failed as it must: $target, counterexample $cex"
    n_neg=$(( n_neg + 1 ))
  done
  [ "$n_neg" -gt 0 ] || die "no negative control in saw/$route/negative/"
done

T_TOTAL=$(( $(date +%s) - T0 ))

# --- 5. the record --------------------------------------------------------------------------

sha() { { sha256sum "$1" 2>/dev/null || shasum -a 256 "$1"; } | cut -d' ' -f1; }

# The Cryptol the scripts import: NSA's (by the paths the scripts name) and
# ours (saw/SHA256Main.cry), with what they import in turn.
CRYPTOL_FILES=(
  algorithms/AES/Types.cry algorithms/AES/GF28.cry algorithms/AES/SBox.cry
  algorithms/AES/Cipher.cry algorithms/AES/KeyExpansion.cry algorithms/AES/Main.cry
  shared/algebra/Polynomial/GF2.cry
  algorithms/SHA2/Main.cry algorithms/SHA2/Notation.cry algorithms/SHA2/Functions.cry
  algorithms/SHA2/Preprocessing.cry algorithms/HMAC/Main.cry
)
OUR_CRYPTOL=(verus/saw/SHA256Main.cry)

record() {
  echo "# saw/${RESULTS##*/} -- written by scripts/check-saw.sh; do not edit."
  echo "#"
  echo "# SAW proofs of the Verus crate's AES, SHA-256 and HMAC-SHA-256"
  echo "# implementations against NSA's Cryptol, on rustc's LLVM bitcode of the"
  echo "# crate (llvm_verify, lines \"proved llvm\") and on its MIR (mir_verify,"
  echo "# lines \"proved mir\"). Local only, never run by CI: this record is the"
  echo "# provenance of the result. doc/saw.md."
  echo
  echo "commit      $COMMIT$DIRTY"
  echo "date        $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "host        $(uname -m), $(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN) CPUs"
  echo "rustc       $V_RUSTC"
  echo "cargo       $V_CARGO"
  echo "c++filt     $V_CXXFILT"
  echo "saw         $V_SAW"
  echo "solvers     rme (SAW's built-in); z3 on PATH: $V_Z3 (each proof's below)"
  echo "memory cap  $CAP_NOTE"
  echo "routes      SAW_ROUTE=$SAW_ROUTE (${ROUTES[*]})"
  if has_route llvm; then
    echo "switches    llvm: cargo rustc --lib (dev profile: -O0, overflow checks, debug assertions) -- ${SWITCHES[*]}"
    echo "bitcode     $(sha "$BC") saw/obj/foundation_verus.bc ($(wc -l < "$OBJ_DIR/mangled.txt") functions, $N_SYMBOLS of the crate bound in symbols.saw)"
  fi
  if has_route mir; then
    echo "mir-json    $V_MIR_JSON, commit $V_MIR_COMMIT, toolchain $MIR_TOOLCHAIN: $V_MIR_RUSTC"
    echo "switches    mir: cargo saw-build --lib (cargo test's build, dev profile: -O0, overflow checks, debug assertions, cfg(test))"
    echo "mir         $(sha "$MIR_JSON") saw/obj/mir/foundation_verus.linked-mir.json ($(wc -l < "$MIR_OBJ_DIR/names.txt") names of the crate)"
  fi
  # The sources rustc read for the bitcode (its dep-info; the MIR is of
  # the same tree), the crate's by path under verus/, the rest (vstd and
  # the other dependencies) by path under the cargo registry, by sha256.
  # Without the llvm route, the crate's own sources.
  if has_route llvm; then
    sed -n '1s/^[^:]*: //p' "$DEP" | tr ' ' '\n' | grep -v '^$' | sort -u
  else
    find "$VERUS_DIR/src" -name '*.rs' | sort
  fi | while read -r f; do
    case "$f" in
      "$VERUS_DIR"/*) echo "source      $(sha "$f") ${f#"$VERUS_DIR"/}" ;;
      */registry/src/*/*) echo "dependency  $(sha "$f") ${f#*/registry/src/*/}" ;;
      *) echo "source      $(sha "$f") $f" ;;
    esac
  done
  echo "lockfile    $(sha "$VERUS_DIR/Cargo.lock") Cargo.lock"
  for f in "${CRYPTOL_FILES[@]}"; do
    echo "cryptol     $(sha "$ROOT_DIR/$f") $f"
  done
  for f in "${OUR_CRYPTOL[@]}"; do
    echo "cryptol     $(sha "$ROOT_DIR/$f") $f (ours)"
  done
  for p in "${PROVED[@]}"; do
    echo "proved      $p"
  done
  for n in "${NEGATIVE[@]}"; do
    echo "negative    $n"
  done
  local IFS=';'
  echo "wall-clock  ${T_PROOFS[*]}; ${T_TOTAL} s in all" | sed 's/;/; /g; s/;  /; /g'
}

if [ "$PRINT" -eq 1 ]; then
  record
else
  record > "$RESULTS"
  echo ">> wrote ${RESULTS#"$ROOT_DIR"/}"
fi
echo ">> SAW (${ROUTES[*]}): $N_PROVED proved, ${#NEGATIVE[@]} negative controls failed as they must (${T_TOTAL} s)"
