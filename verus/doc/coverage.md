# Coverage and mutation testing

How much of the executable code the FFI properties run: LLVM source-based
coverage (rustc's `-C instrument-coverage`), by region, line and branch
outcome. The counterpart of the "Coverage" part of the SPARK crate's
`spark/doc/coverage.md` (github.com/manthonyaiello/Foundation, tag
`spark-v1.0`), which measures with GNATcoverage; and, in
[Mutation testing](#mutation-testing), which faults the properties, Verus
and SAW catch. Back to the [README](../README.md).

**No MC/DC.** The SPARK crate measures statement, decision and MC/DC
(`--level=stmt+mcdc`). This crate measures no MC/DC, because rustc cannot:
its MC/DC instrumentation has been removed, and Rust 1.98.1 (the pinned
toolchain), as well as nightly 1.96 and 1.101, accept only `block`,
`branch` and `condition` for `-Zcoverage-options`. What is measured
instead:

| SPARK (gnatcov) | here (llvm-cov) |
|---|---|
| statement | region: rustc's code regions, the stretches of code a counter covers; also lines |
| decision | branch outcome: the true and false sides of each `if`, `while` and `match` arm (`branch`), and of each operand of `&&` and `\|\|` (`condition`) |
| MC/DC | **none** |

Condition coverage (both sides of each operand of `&&` and `||`) is weaker
than MC/DC: it does not ask that each operand be shown to change the
decision's outcome on its own.

## Running it

`scripts/check-coverage.sh` measures the files of `coverage/units.txt`
(the executables `aes/aes_impl.rs`, `aes/aes_impl/main.rs`,
`sha2/sha256_stream.rs` and `hmac/sha256_impl.rs`, the exec counterparts
in `sha2/functions.rs` and `sha2/notation.rs`, and the FFI exports
`ffi/*.rs`), under every property of `cryptol/properties.txt`. The spec
layer is out of scope: `cargo build` erases every `spec fn`, `proof fn`,
proof block, assertion and loop invariant, so there is no code to cover,
as the SPARK crate's Ghost code has none without `-gnata`.

```console
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-coverage.sh   # every property
$ scripts/check-coverage.sh prop_Impl_Dot                     # a partial report
```

It needs the toolchain's `llvm-tools` component
(`rustup component add llvm-tools --toolchain 1.98.1`: `llvm-profdata` and
`llvm-cov` of rustc's own LLVM, or the profiles do not read) and what
`check-ffi.sh` needs. It

1. builds the FFI library (`ffi/`) instrumented, into `target/cov/`, with
   the FFI check's profile (release, overflow checks, debug assertions) and
   `RUSTFLAGS="-C instrument-coverage -Zcoverage-options=branch,condition"`.
   The branch options are unstable, so the build sets `RUSTC_BOOTSTRAP=1`
   on the pinned 1.98.1 rather than switch to a nightly, and the code
   measured is the code the pinned rustc compiles. Only this build does:
   the crate's build, the proof and the FFI check's library are untouched;
2. runs `check-ffi.sh` against that library (`FFI_LIB`, `FFI_OUT`), which
   judges every property as usual;
3. merges the profiles into `target/cov/report/`: `summary.txt` (the
   per-file table and every violation with its explanation, from
   `scripts/coverage-summary.py`), `report.txt` (llvm-cov's per-file and
   per-function report), `html/` (annotated sources, with branch counts)
   and `export.json`;
4. on a run of every property from a clean tree, writes
   `coverage/results.txt` (commit, date, tools, the table). The SPARK
   crate keeps its numbers in CI; this crate has none.

**A profile from Cryptol's process.** The library carries LLVM's
profiling runtime, which registers its own exit handler when Cryptol
loads the library, so every `cryptol -b` (one per property) writes its
own profile into `target/cov/traces/` (`LLVM_PROFILE_FILE`, one file per
pid) when it exits. The SPARK crate needs a unit of its own for this
(`coverage/foundation_spark_coverage`, which registers gnatcov's dump with
`atexit`); this crate needs none. The script fails unless there is one
profile per run. The build's own instrumented tools (proc macros, build
scripts) write profiles too; those go to `target/cov/build-prof/` and are
not used.

**Generic functions.** A generic function has one record per
instantiation (`encrypt_block::<128>`, `::<192>`, `::<256>`). A region or
a branch outcome is covered when any instantiation covers it, and is
counted once, by its source position.

**What is not counted.** A branch inside a macro's expansion has no region
in the file: the failing side of an `assert!` on a single condition is
not counted, while each operand of an `&&` or `||` in it is. Overflow and
bounds checks, which the compiler inserts, are not branches of the
source, and are not counted as such (the proofs rule out their failing
side in the verified code).

## Explained, or closed

Every violation (a region never executed, a branch outcome never taken)
must match an entry of `coverage/explained.txt` (the file, the trimmed
text of the line, the reason), or the script fails. As in the SPARK
crate, an entry is for code the properties cannot reach by construction;
a gap in the targeted tests is closed with a property instead. The script
also fails when a file under `src/` has instrumented code and is not in
`units.txt`, or a listed file has none, so new executable code cannot be
left out of the measure unnoticed.

The entries are the FFI exports' run-time checks of what Cryptol's types
already ensure (`src/ffi/mod.rs`): the `_ => unreachable!()` arm after
`check_key_size` (Cryptol's `Key k` allows only 128, 192 and 256), the
last operand of `check_key_size` itself, and HMAC's `k < MAX_BYTES && n <
MAX_TEXT` (Cryptol's `61 >= width k`). The SPARK crate's exports have no
such checks, so its file has no entries. The implementation layer
(`aes/`, `sha2/`, `hmac/`) has no entry: the properties run all of it.

Measured on 2026-11-02:

| | region | line | branch | MC/DC |
|---|---|---|---|---|
| implementation layer and exec counterparts | 947/947 | 692/692 | 80/80 | not measured |
| FFI exports | 583/589 | 267/273 | 13/18 | not measured |
| total | 1530/1536 | 959/965 | 93/98 | not measured |

with the 11 violations, all in the FFI exports, explained.

## Mutation testing

Coverage says which code the FFI properties run, not which inputs they
try. `scripts/mutation.py`, the counterpart of the SPARK crate's
`spark/scripts/mutation.py`, measures the difference: it applies each
mutant of [`mutation/mutants.txt`](../mutation/mutants.txt) in a scratch
copy of the checkout, never in the checkout itself, and records what
catches it:

* **FFI**: the library built from the mutated tree, against the
  properties that reach the mutated code (stopping at the first failure),
  and for a survivor of those, against every property (`--full`);
* **Verus**: `cargo verus focus -- --verify-only-module M ...` on the
  mutated code's modules, the failure sorted into unproved (a
  verification error: a postcondition, an assertion, a loop invariant, a
  precondition or an overflow not proved), timeout (the resource limit,
  rlimit, reached and nothing else: not a refutation) or nocompile.
  Verus gives no counterexample, so there is no counterpart to the SPARK
  column's "refuted";
* **SAW**: `check-saw.sh --print` per mutant, both routes (LLVM and MIR)
  unless `SAW_ROUTE` says otherwise.

```console
$ scripts/mutation.py check                      # every mutant applies
$ scripts/mutation.py setup /tmp/mut             # the scratch copy
$ scripts/mutation.py ffi /tmp/mut --baseline    # the controls: the
$ scripts/mutation.py prove /tmp/mut --baseline  #   unmutated tree passes
$ scripts/mutation.py ffi /tmp/mut               # every mutant
$ scripts/mutation.py ffi /tmp/mut --full        # survivors: every property
$ scripts/mutation.py prove /tmp/mut             # every mutant
$ scripts/mutation.py saw /tmp/mut --baseline
$ scripts/mutation.py saw /tmp/mut ID ...        # the survivors, and F*
$ scripts/mutation.py report /tmp/mut            # the table, as Markdown
```

It needs what `check-ffi.sh` and `check-saw.sh` need, and `cargo verus`
(on `PATH`, or `CARGO_VERUS`). `witness` runs one
Cryptol `:check` against a mutant at an input the properties never try,
and `diagnose` runs Verus on a mutant again with more arguments (a larger
`--rlimit`); both are diagnostics, outside the columns.

**The mutants.** The SPARK crate's 84 faults, under the same ids, each
written on the Verus line that does what the SPARK line does: 34 in
`aes/aes_impl.rs` (A), 5 in `aes/aes_impl/main.rs` (M), 26 in
`sha2/sha256_stream.rs` (S), 9 in `hmac/sha256_impl.rs` (H) and 14 in
`sha2/functions.rs` (F), 88 in all. Where they differ from the SPARK list:

* S27–S29 are left out. They index a message array from 0 rather than
  from its `'First`; a Rust slice always starts at 0, so the fault cannot
  be written;
* A29 drops the initialization of the key schedule in the SPARK list.
  Rust does not allow reading an uninitialized array, so here the
  schedule is initialized to ones rather than zeros: equivalent, as is
  the SPARK mutant, since every word is written before it is read;
* F01–F07 are written twice. In the SPARK crate, `SHA2.Functions` is
  shared by the spec and the implementation, so one mutant changes both.
  Here the spec functions and their exec counterparts are separate
  functions (Verus cannot run a `spec fn`), so `F01a`–`F07a` change the
  exec counterpart only, and `F01b`–`F07b` change both the same way, as
  the SPARK mutant does: they are the one kind of mutant of more than one
  line.

**The verdict.** The last column says which of the FFI and Verus catches
the mutant: both, FFI only, Verus only (with "(rlimit)" when Verus only
timed out), or neither. The SPARK script says "FFI" whenever the FFI
catches it, and does not record whether the proof does too; this column
says so, since F01a–F07a and F01b–F07b differ just there.

### Results

Run on 2026-11-03 on an x86_64 Linux machine (Intel Core i9-9900K). The
controls pass: the
unmutated tree passes the 72 properties the mutants reach, Verus verifies
the 18 modules they touch (145 verified, 26 s), and SAW proves the
unmutated implementation on both routes (168 proofs, the 16 negative
controls failing, 934 s).

The FFI kills 73 of the 88. Of the 15 survivors, all of which pass every
property (`--full`), 10 are equivalent mutants (A20, A29, A33, M04, S08,
S10, S12, S14, S25, S26) and 5 are real bugs in the streaming SHA-256's
length encoding (S20–S24) that only show on messages longer than the
properties try (from 4 KiB for S24 up to 2^53 bytes for S21). These
are the SPARK crate's survivors, less S27, its sixth real bug, which has
no counterpart here.

Verus fails all 5 real bugs, at a loop invariant (and, for four of them, a
precondition) of the length's encoding in `finalize`, each by a verification error, where
gnatprove fails the SPARK crate's by timeout. Of the 73 the FFI kills,
Verus fails 66: 62 by a verification error and 4 (A25, A27, A28, M03) by
reaching the resource limit; the other 7 are F01b–F07b, which Verus
proves, as gnatprove proves the SPARK crate's F01–F07: the implementation
is proved against the same, mutated, spec. F01a–F07a, which change the
exec counterpart only, Verus fails.

Of the 10 equivalent mutants, Verus proves 4 (A29, A33, S12, S26), times
out on M04 and fails the other 5 (A20, S08, S10, S14, S25), although the
code still meets its contract: a Verus failure is a proof that does not
go through, not a bug found.

SAW (both routes, `mutation.py saw`) was run on 29 of the mutants: the 15
FFI survivors and the 14 F mutants.

* It proves 9 of the 10 equivalent mutants. M04 (InvCipher' for
  InvCipher) hangs: the LLVM route's proof of `main::decrypt` at k = 128,
  which overrides `decrypt_block_prime` with its proved `InvCipher'`
  contract, does not finish its goal against Main.cry's `Decrypt` (an
  InvCipher) within the hour `mutation.py` allows. The SPARK crate's SAW
  proves its M04, and fails S14, which SAW proves here.
* It passes all 5 real bugs, as in the SPARK crate: its hash proofs are at
  fixed lengths of at most 200 bytes. Verus is the only one of the three
  that rejects them.
* It rejects F01 and F07 (a and b alike: SAW reads the exec code, which
  the two share) with a counterexample, and F02 (Maj) at the 10G memory
  cap under rme, as the SPARK crate's SAW does. F03–F06 stop the LLVM
  script at an unbound name: the mutant no longer calls the const-generic
  instance the script verifies first (`ROTR::<13>`, `SHR::<3>`,
  `SHR::<10>`, `ROTR::<25>`), so rustc emits no such function. The column
  records these as an `error`, not a failure.
