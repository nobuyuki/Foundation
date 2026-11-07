#!/usr/bin/env bash
#
# check-trust-surface.sh -- gate the crate's trust surface against a manifest.
#
# The counterpart of the SPARK crate's spark/scripts/check-trust-surface.sh
# (github.com/manthonyaiello/Foundation, tag spark-v1.0), itself adapted from
# memcp's (manthonyaiello/memcp).
#
# The trust surface is everything a proof of this crate does not cover: code
# Verus does not verify, assumptions it takes on faith, functions whose bodies
# it does not check, and the foreign boundary. trust-surface.txt (beside this
# script) lists every such site with a justification; this script derives the
# same set from the sources and fails on any difference.
#
# This crate is meant to be at the SPARK crate's level: every implementation
# proved equal to the spec layer, with no assumptions. So the manifest should
# only hold what no Verus formulation avoids (the FFI exports of src/ffi/,
# and vstd's unverified functions the crate cannot do without). Anything else
# is a hole, and a hole is reported as one in the change that adds it, even
# when the manifest line makes this gate pass.
#
# Scope: git-tracked Rust sources under verus/src/, recursively, minus the
# items under #[cfg(test)] (tests are not part of what is proved, as the SPARK
# crate's tests are not in spark/src). Paths are relative to verus/.
#
# Kinds, each with the SPARK kind it stands for:
#   outside-verus     an item (fn, struct, enum, union, trait, impl, const,
#                     static, macro_rules!) outside every verus! { } block,
#                     which Verus does not see    (SPARK_Mode => Off)      entity
#   assume            assume(..), admit(), axiom fn  (pragma Assume)       entity
#   external          #[verifier::external_body], #[verifier::external],
#                     #[verifier(external..)], the external_*_specification
#                     and external_trait_extension attributes, and
#                     assume_specification[..]    (a GNATprove justification:
#                     Skip_Proof and the like)                             entity
#   no-termination    #[verifier::exec_allows_no_decreases_clause],
#                     #[verifier::assume_termination]                      entity
#   unverified-cfg    a cfg or cfg_attr other than cfg(test) and
#                     cfg(verus_only): the build may then compile code
#                     Verus did not verify    (pragma Suppress, in that the
#                     build differs from what was proved)                  entity
#   unsafe            the unsafe keyword                                   entity
#   foreign-binding   extern "C", extern { }, no_mangle, export_name,
#                     link_name, #[link]      (Import / Export / C)        file
#   vstd-trusted      a path vstd::..::f naming an exec or proof fn of vstd
#                     whose body Verus does not check (external_body or
#                     external), that is an axiom fn, or that uses assume or
#                     admit; Verus only.
#                     The entity is the path.                              entity
#
# Differences from the SPARK script, all deliberate:
#   * Rust lint suppressions (#[allow(..)]) are not a kind. SPARK counts
#     pragma Warnings (Off) because gnatprove's flow analysis is part of its
#     proof; a rustc lint does not change what Verus proves. (The crate has
#     #[allow(unused_imports)] on the use of vstd::prelude, which only ghost
#     code reads, and #![allow(non_snake_case, ..)] for Cryptol's names.)
#   * vstd-trusted is new: the SPARK crate depends on no library proved by
#     someone else, this one on vstd.
#   * The entity of an attribute is the item it is on; of a statement (assume,
#     an unsafe block), the innermost named item around it.
#
# Not counted: Verus, Z3, rustc and vstd's specifications of std (the
# assume_specification items that give u32::wrapping_add, indexing and the
# like their meaning, reached through vstd::prelude and method calls) are the
# trusted base, as gnatprove, the provers and GNAT's semantics of Ada are the
# SPARK crate's. vstd-trusted follows only explicit vstd:: paths to fns, not
# methods (vstd::seq::Seq::<T>::empty) nor names brought in by use .. ::*.
#
# Known limits. The lexer is small: it knows // and /* */ comments, string
# literals and char literals, not raw strings (r"..", r#".."#), which the crate
# does not use; a raw string holding a quote or a brace would derail it. A
# #[cfg(test)] module must be inline (mod tests { .. }) to be left out. Cargo
# features and build flags live in Cargo.toml and rust-toolchain.toml, not in
# src/, and are reviewed there.
#
# Usage:
#   scripts/check-trust-surface.sh          # gate (exit 1 on any difference)
#   scripts/check-trust-surface.sh --list   # print the derived set, manifest-shaped
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MANIFEST="scripts/trust-surface.txt"

LIST=0
case "${1:-}" in
  --list) LIST=1 ;;
  "") ;;
  *) echo "!! unknown argument: $1" >&2; exit 2 ;;
esac

# --- the file universe --------------------------------------------------------

# git-tracked only, so build output cannot enter the surface by appearing on
# disk.
rust_sources() {
  git ls-files -- src | grep -E '^src/.+\.rs$' || true
}

# --- the lexer ----------------------------------------------------------------

# An awk function, shared by the scanners below: clean(line) returns the line
# with comments, string literals and char literals blanked to spaces (so that
# columns are kept), carrying a block comment or a string across lines in the
# globals in_block and in_str.
LEXER='
function clean(s,    out, i, n, c, d, m) {
  out = ""; n = length(s); i = 1
  while (i <= n) {
    c = substr(s, i, 1); d = substr(s, i, 2)
    if (in_block) {
      if (d == "*/") { in_block = 0; out = out "  "; i += 2 } else { out = out " "; i++ }
    } else if (in_str) {
      if (c == "\\") { out = out "  "; i += 2 }
      else if (c == "\"") { in_str = 0; out = out " "; i++ }
      else { out = out " "; i++ }
    } else if (d == "//") {
      break
    } else if (d == "/*") {
      in_block = 1; out = out "  "; i += 2
    } else if (c == "\"") {
      in_str = 1; out = out " "; i++
    } else if (c == "'"'"'") {
      m = substr(s, i)
      if (match(m, /^'"'"'\\[^'"'"']*'"'"'/) || match(m, /^'"'"'[^\\'"'"']'"'"'/)) {
        out = out sprintf("%" RLENGTH "s", ""); i += RLENGTH
      } else { out = out c; i++ }
    } else { out = out c; i++ }
  }
  return out
}
'

# --- deriving the surface -----------------------------------------------------

# Emit "kind|entity" for every site in file $1, and "foreign-binding|-" once if
# it binds across the language boundary.
scan_file() {
  awk "$LEXER"'
    function push(name, verus, test) {
      depth++; sname[depth] = name; sverus[depth] = verus; stest[depth] = test
    }
    function inside(flag,    i) {
      for (i = depth; i >= 1; i--) if ((flag == "verus" ? sverus[i] : stest[i])) return 1
      return 0
    }
    function enclosing(    i) {
      for (i = depth; i >= 1; i--) if (sname[i] != "") return sname[i]
      return ""
    }
    function site(kind, entity) {
      if (pending_test || inside("test")) return
      if (entity == "") {
        printf "!! cannot name the entity at %s:%d (%s) -- the gate needs one\n", FILENAME, FNR, kind > "/dev/stderr"
        failed = 1; return
      }
      print kind "|" entity
    }
    # Attribute sites wait for the item they are on.
    function attr(kind) { nattr++; attrs[nattr] = kind }
    function flush(entity,    i) {
      for (i = 1; i <= nattr; i++) site(attrs[i], entity)
      nattr = 0
    }
    function header(kind, name) {
      flush(name)
      pending = name
      if (kind != "mod" && !inside("verus") && !pending_verus)
        site("outside-verus", name)
    }
    function ev(col, what) { if (!(col in evs)) evs[col] = what }
    {
      line = clean($0)
      if (line ~ /extern[ \t]*"|extern[ \t]*\{|no_mangle|export_name|link_name|#\[[ \t]*link[ \t]*[(\]]/)
        foreign = 1
      if (line ~ /extern[ \t]*$/) foreign = 1   # extern "C" after a cleaned string
      delete evs
      # Item headers.
      rest = line; off = 0
      while (match(rest, /(^|[^A-Za-z0-9_])(fn|struct|enum|union|trait|mod|static|const)[ \t]+[A-Za-z_][A-Za-z0-9_]*/)) {
        tok = substr(rest, RSTART, RLENGTH); col = off + RSTART
        sub(/^[^A-Za-z]*/, "", tok); split(tok, w, /[ \t]+/)
        # Not const fn, not a const generic (<const n: u32, const m: ..>), and
        # not a raw pointer type (*const T).
        before = substr(line, 1, col); sub(/[ \t]+$/, "", before)
        if (substr(before, length(before)) ~ /[A-Za-z0-9_]/) before = substr(before, 1, length(before) - 1)
        sub(/[ \t]+$/, "", before)
        if (!(w[1] == "const" && (w[2] == "fn" || substr(before, length(before)) ~ /[<,*]/)))
          ev(col, "H " w[1] " " w[2])
        off += RSTART + RLENGTH - 1; rest = substr(rest, RSTART + RLENGTH)
      }
      rest = line; off = 0
      while (match(rest, /(^|[^A-Za-z0-9_])(impl|macro_rules[ \t]*!)([^A-Za-z0-9_]|$)[^{;]*/)) {
        tok = substr(rest, RSTART, RLENGTH); col = off + RSTART
        sub(/^[^A-Za-z]*/, "", tok); gsub(/[ \t]+/, " ", tok); sub(/ +$/, "", tok)
        if (tok ~ /^macro_rules/) tok = "macro_rules! " substr(rest, RSTART + RLENGTH)
        ev(col, "H impl " tok)
        off += RSTART + RLENGTH - 1; rest = substr(rest, RSTART + RLENGTH)
      }
      # Sites and markers.
      scan(line, "(^|[^A-Za-z0-9_])verus[ \t]*!", "V")
      scan(line, "#!?\\[[ \t]*cfg[ \t]*\\([ \t]*test[ \t]*\\)[ \t]*\\]", "T")
      scan(line, "(^|[^A-Za-z0-9_])(assume|admit)[ \t]*\\(", "S assume")
      scan(line, "(^|[^A-Za-z0-9_])unsafe([^A-Za-z0-9_]|$)", "A unsafe")
      scan(line, "(^|[^A-Za-z0-9_])axiom[ \t]+fn([^A-Za-z0-9_]|$)", "A assume")
      scan(line, "verifier[ \t]*(::[ \t]*|\\([ \t]*)(external|external_body|external_fn_specification|external_type_specification|external_trait_specification|external_trait_extension)([^A-Za-z0-9_]|$)", "A external")
      scan(line, "verifier[ \t]*(::[ \t]*|\\([ \t]*)(exec_allows_no_decreases_clause|assume_termination)([^A-Za-z0-9_]|$)", "A no-termination")
      scan(line, "(^|[^A-Za-z0-9_])assume_specification[ \t]*(<[^\\[]*>)?[ \t]*\\[[^\\]]*\\]", "X")
      scan(line, "(^|[^A-Za-z0-9_])cfg(_attr)?[ \t]*\\([^\\]]*", "C")
      # Brackets.
      for (i = 1; i <= length(line); i++) {
        c = substr(line, i, 1)
        if (c == "{" || c == "}" || c == ";" || c == "(" || c == ")" || c == "[" || c == "]") ev(i, "B " c)
      }
      for (i = 1; i <= length(line); i++) {
        if (!(i in evs)) continue
        e = evs[i]; k = substr(e, 1, 1); arg = substr(e, 3)
        if (k == "H") {
          split(arg, w, " "); name = substr(arg, length(w[1]) + 2)
          header(w[1], name)
        } else if (k == "V") {
          pending_verus = 1
        } else if (k == "T") {
          pending_test = 1
        } else if (k == "S") {
          site(arg, enclosing())
        } else if (k == "A") {
          attr(arg)
        } else if (k == "X") {
          m = substr(line, i); match(m, /\[[^\]]*\]/)
          ent = substr(m, RSTART + 1, RLENGTH - 2); gsub(/[ \t]+/, "", ent)
          flush(ent); site("external", ent)
        } else if (k == "C") {
          m = substr(line, i); sub(/^[^c]*/, "", m); gsub(/[ \t]/, "", m)
          if (m !~ /^cfg\((test|verus_only)\)/) attr("unverified-cfg")
        } else if (k == "B") {
          if (arg == "(" || arg == "[") parens++
          else if (arg == ")" || arg == "]") parens--
          else if (arg == "{") {
            if (nattr) flush(pending != "" ? pending : enclosing())
            push(pending, pending_verus, pending_test)
            pending = ""; pending_verus = 0; pending_test = 0
          } else if (arg == "}") {
            if (depth > 0) depth--
          } else if (arg == ";" && parens == 0) {
            if (nattr) flush(pending != "" ? pending : enclosing())
            pending = ""; pending_test = 0
          }
        }
      }
    }
    function scan(s, re, what,    rest, off) {
      rest = s; off = 0
      while (match(rest, re)) {
        col = off + RSTART
        if (substr(rest, RSTART, 1) !~ /[A-Za-z#]/) col++
        ev(col, what)
        off += RSTART + RLENGTH - 1; rest = substr(rest, RSTART + RLENGTH)
        if (RLENGTH == 0) break
      }
    }
    END {
      if (nattr) { printf "!! %s: an attribute at the end of the file names no item\n", FILENAME > "/dev/stderr"; failed = 1 }
      if (foreign) print "foreign-binding|-"
      exit failed ? 2 : 0
    }
  ' "$1"
}

# The vstd package's source directory, from Cargo's lock file.
vstd_dir() {
  local manifest
  manifest="$(cargo metadata --format-version 1 --offline 2>/dev/null \
    | grep -o '"manifest_path":"[^"]*/vstd-[^"]*/Cargo.toml"' | head -1 \
    | sed 's/^"manifest_path":"//; s/"$//')" || true
  [ -n "$manifest" ] || { echo "!! cannot find vstd's sources (cargo metadata --offline)" >&2; exit 2; }
  dirname "$manifest"
}

# True when some definition of a non-spec fn named $2 in vstd file $1 is not
# checked by Verus: an external or external_body attribute in the block of
# attributes above it, or assume or admit in its body.
vstd_fn_trusted() {
  awk -v want="$2" "$LEXER"'
    {
      line = clean($0)
      if (body) {
        if (line ~ /(^|[^A-Za-z0-9_])(assume|admit)[ \t]*\(/) bad = 1
        t = line; o = gsub(/\{/, "{", t); t = line; cl = gsub(/\}/, "}", t)
        depth += o - cl
        if (opened && depth <= 0) { body = 0; if (bad) trusted = 1 }
        if (o > 0) opened = 1
        if (!opened && line ~ /;[ \t]*$/) body = 0
        next
      }
      if (match(line, "(^|[^A-Za-z0-9_])fn[ \t]+" want "([^A-Za-z0-9_]|$)")) {
        found = 1
        pre = substr(line, 1, RSTART)
        if (pre !~ /(^|[^A-Za-z0-9_])spec[ \t]*(\([^)]*\))?[ \t]*$/) {
          if (pre ~ /(^|[^A-Za-z0-9_])axiom[ \t]*$/) trusted = 1
          if (attrs ~ /verifier[ \t]*(::[ \t]*|\([ \t]*)external(_body)?([^A-Za-z0-9_]|$)/) trusted = 1
          body = 1; bad = 0; opened = 0
          t = line; o = gsub(/\{/, "{", t); t = line; cl = gsub(/\}/, "}", t)
          depth = o - cl; if (o > 0) opened = 1
          if (opened && depth <= 0) body = 0
        }
        attrs = ""; next
      }
      if (line ~ /^[ \t]*(#|pub|$)/ || line ~ /^[ \t]*(open|closed|proof|exec|spec|broadcast|const|unsafe)[ \t]*$/) attrs = attrs " " line
      else attrs = ""
    }
    END { exit (!found ? 3 : (trusted ? 0 : 1)) }
  ' "$1"
}

# Emit "vstd-trusted|path" for every vstd::..::f path in file $1 that names a
# fn vstd does not check.
scan_vstd() {
  local file="$1" vdir="$2" path segs n k mod cand rc
  awk "$LEXER"'{ print clean($0) }' "$file" \
    | { grep -oE 'vstd(::[A-Za-z_][A-Za-z0-9_]*)+' || true; } | sort -u \
    | while IFS= read -r path; do
        IFS=: read -r -a segs <<<"${path//::/:}"
        n=${#segs[@]}
        # A module (vstd::prelude, from use vstd::prelude::*) names no fn.
        mod="$(IFS=/; echo "${segs[*]:1}")"
        if [ "$n" -eq 1 ] || [ -f "$vdir/$mod.rs" ] || [ -f "$vdir/$mod/mod.rs" ]; then continue; fi
        cand=""
        for ((k = n - 2; k >= 1; k--)); do
          mod="$(IFS=/; echo "${segs[*]:1:k}")"
          if [ -f "$vdir/$mod.rs" ]; then cand="$vdir/$mod.rs"; break; fi
          if [ -f "$vdir/$mod/mod.rs" ]; then cand="$vdir/$mod/mod.rs"; break; fi
        done
        [ -n "$cand" ] || cand="$vdir/vstd.rs"
        rc=0; vstd_fn_trusted "$cand" "${segs[n-1]}" || rc=$?
        case "$rc" in
          0) printf 'vstd-trusted|%s\n' "$path" ;;
          1) ;;
          # A capitalized name is a type or a constant (vstd::seq::Seq), not
          # a fn: its methods (vstd::seq::Seq::<T>::empty) are not traced.
          *) case "${segs[n-1]}" in
               [A-Z]*) ;;
               *) echo "!! $file: cannot find fn ${segs[n-1]} of $path in ${cand#"$vdir"/}" >&2; exit 2 ;;
             esac ;;
        esac
      done
}

derive() {
  local file vdir
  vdir="$(vstd_dir)" || return 2
  while IFS= read -r file; do
    scan_file "$file" | sed "s#^\([^|]*\)|#\1|$file|#" || return 2
    scan_vstd "$file" "$vdir" | sed "s#^\([^|]*\)|#\1|$file|#" || return 2
  done < <(rust_sources)
}

DERIVED_RAW="$(derive)" || exit 2
DERIVED="$(printf '%s\n' "$DERIVED_RAW" | sed '/^$/d' | sort -u)"

# --- --list: print the derived set in manifest form ---------------------------

if [ "$LIST" -eq 1 ]; then
  printf '%s\n' "$DERIVED" | while IFS='|' read -r kind path entity; do
    [ -z "$kind" ] && continue
    printf '%-16s | %-40s | %-24s | \n' "$kind" "$path" "$entity"
  done
  exit 0
fi

[ -f "$MANIFEST" ] || { echo "!! missing manifest $MANIFEST" >&2; exit 2; }

# --- reading the manifest -----------------------------------------------------

# Non-comment, non-blank lines, whitespace squeezed out of the key fields so the
# manifest can stay column-aligned for a human reader.
MANIFEST_KEYS="$(
  { grep -vE '^[[:space:]]*#|^[[:space:]]*$' "$MANIFEST" || true; } \
  | awk -F'|' '{ for (i = 1; i <= 3; i++) { gsub(/^[ \t]+|[ \t]+$/, "", $i) }
                 print $1 "|" $2 "|" $3 }' \
  | sort -u
)"

# Entries whose justification field is empty or missing.
UNJUSTIFIED="$(
  { grep -vE '^[[:space:]]*#|^[[:space:]]*$' "$MANIFEST" || true; } \
  | awk -F'|' '{ j = (NF >= 4 ? $4 : ""); gsub(/^[ \t]+|[ \t]+$/, "", j)
                 if (j == "") { for (i = 1; i <= 3; i++) gsub(/^[ \t]+|[ \t]+$/, "", $i)
                                print $1 "|" $2 "|" $3 } }'
)"

# --- gate ---------------------------------------------------------------------

ADDED="$(comm -23 <(printf '%s\n' "$DERIVED") <(printf '%s\n' "$MANIFEST_KEYS") | sed '/^$/d' || true)"
STALE="$(comm -13 <(printf '%s\n' "$DERIVED") <(printf '%s\n' "$MANIFEST_KEYS") | sed '/^$/d' || true)"

fail=0

if [ -n "$ADDED" ]; then
  fail=1
  cat >&2 <<EOF

!! TRUST SURFACE GREW -- these sites are not in verus/$MANIFEST:

$(printf '%s\n' "$ADDED" | sed 's/^/     /')

   Each is something Verus does not prove. This crate is meant to have no
   assumptions; the only expected entries are the FFI exports and vstd's
   unverified functions the crate cannot do without.

   If the site is unavoidable: add a line to verus/$MANIFEST naming it and
   saying, in one sentence, why no Verus formulation works, and report it in
   the change as a hole. If it is not, the fix is in the code.
EOF
fi

if [ -n "$STALE" ]; then
  fail=1
  cat >&2 <<EOF

!! STALE MANIFEST ENTRIES -- listed in verus/$MANIFEST, absent from the tree:

$(printf '%s\n' "$STALE" | sed 's/^/     /')

   The trust surface shrank. Delete these lines.
EOF
fi

if [ -n "$UNJUSTIFIED" ]; then
  fail=1
  cat >&2 <<EOF

!! UNJUSTIFIED ENTRIES -- no text in the fourth field of verus/$MANIFEST:

$(printf '%s\n' "$UNJUSTIFIED" | sed 's/^/     /')

   An entry without a justification is an exception nobody has argued for.
EOF
fi

if [ "$fail" -ne 0 ]; then
  exit 1
fi

n_sources="$(rust_sources | grep -c . || true)"
n_sites="$(printf '%s\n' "$DERIVED" | grep -c . || true)"
echo ">> TRUST SURFACE OK -- ${n_sites} site(s) over ${n_sources} tracked source(s), all in verus/$MANIFEST."
