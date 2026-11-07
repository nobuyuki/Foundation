#!/usr/bin/env python3
"""mutation.py -- mutation testing of the executable Verus code.

The counterpart of the SPARK crate's spark/scripts/mutation.py
(github.com/manthonyaiello/Foundation, tag spark-v1.0), with the same
commands and columns. It differs in the tools (cargo builds the FFI library
where the SPARK script runs gprbuild; Verus verifies where gnatprove proves;
check-saw.sh runs SAW on the bitcode and the MIR of rustc), in the proof
column's outcomes (Verus reports no counterexample: see classify), and in
allowing a mutant of more than one line (mutation/mutants.txt, the F*b
mutants).

Each mutant of mutation/mutants.txt is a small change to the executable
code. For each one, this script records what catches it:

  * the FFI column: the mutant's FFI properties (scripts/check-ffi.sh, run
    against a library built from the mutated tree), and, for a survivor of
    those, every property (--full);
  * the Verus column: Verus on the mutant's modules (`cargo verus focus --
    --verify-only-module M ...`). A failure is classified by what Verus
    said: a verification error (a postcondition, an assertion, an
    invariant, a precondition, an overflow ... not proved), or a resource
    limit (rlimit) reached and nothing else (a timeout: not a refutation),
    or a compile error;
  * the SAW column: scripts/check-saw.sh --print per mutant, both routes
    unless SAW_ROUTE says otherwise.

Mutants are applied in a scratch copy of the checkout (the TREE), one at a
time, and the pristine file is restored after each, so the checkout this
script lives in is never modified. Results go to TREE/results/.

Usage (from anywhere):

  mutation.py check                      every mutant applies to the sources
  mutation.py list                       the mutants, one per line
  mutation.py setup TREE                 copy the checkout to TREE, build it
  mutation.py ffi TREE [ID ...] [--full] [--baseline] [--redo]
  mutation.py prove TREE [ID ...] [--baseline] [--redo]
  mutation.py saw TREE ID ... [--baseline]
                                         the SAW column
  mutation.py report TREE                the results table, as Markdown
  mutation.py reclassify TREE            classify the saved proof logs again
  mutation.py diagnose TREE ID ... -- VERUS_ARGS
                                         Verus again with extra arguments
                                         (--rlimit 100: more time;
                                         diagnostic only)
  mutation.py witness TREE ID MODULE EXPR TESTS
                                         one Cryptol :check of EXPR (from
                                         cryptol/MODULE) against the mutant

With no ID, ffi and prove take every mutant without a result yet (--redo:
every mutant). A mutant's properties run one at a time and stop at the
first that fails (its killer); a survivor has passed them all. --baseline
runs the column on the unmutated tree: the union of the mutants'
properties, or of their modules; it must pass.

Env:
  FFI_JOBS, CRYPTOL, CARGO  as for check-ffi.sh (CRYPTOL must report "FFI
                            enabled"); FFI_JOBS also builds the library.
  CARGO_VERUS               the cargo-verus command, word-split (default:
                            "cargo verus").
  MIR_JSON_DIR, SAW_ROUTE, SAW_MEMORY_MAX
                            as for check-saw.sh (saw, z3 on PATH).
  MUTATION_TIMEOUT          seconds before one column's run of one mutant is
                            killed and recorded as a hang (default 3600).
"""

import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import time

VERUS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(VERUS)
DATA = os.path.join(VERUS, "mutation", "mutants.txt")
EXT = "dylib" if sys.platform == "darwin" else "so"
FFI_LIB = "target/release/libfoundation_verus_ffi.%s" % EXT


def die(msg):
    sys.stderr.write("mutation.py: %s\n" % msg)
    sys.exit(2)


# --------------------------------------------------------------- the data


class Edit(object):
    def __init__(self, file, line, old, new, lineno):
        self.file, self.line, self.old, self.new = file, line, old, new
        self.lineno = lineno


class Mutant(object):
    """A mutant: its id, its edits (one per line of mutants.txt with its
    id), and the ffi, prove and what that every one of those lines gives."""

    def __init__(self, mid, ffi, prove, what):
        self.id = mid
        self.ffi = ffi.split()
        self.prove = prove.split()
        self.what = what
        self.edits = []

    @property
    def file(self):
        return self.edits[0].file

    @property
    def line(self):
        return self.edits[0].line


def unescape(s):
    # A | inside a field is written \| (the field separator is " | ").
    return s.replace("\\|", "|")


def load():
    """The mutants (in order) and the groups of mutants.txt."""
    groups = {}
    mutants = []
    by = {}
    with open(DATA) as f:
        for n, raw in enumerate(f, 1):
            line = raw.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            m = re.match(r"^group\s+(\S+)\s*=\s*(.*)$", line)
            if m:
                groups[m.group(1)] = m.group(2).split()
                continue
            fields = [unescape(x.strip()) for x in line.split(" | ")]
            if len(fields) != 8:
                die("%s:%d: %d fields, not 8" % (DATA, n, len(fields)))
            mid, file, ln, old, new, ffi, prove, what = fields
            if mid in by:
                mu = by[mid]
                if mu is not mutants[-1]:
                    die("%s:%d: the lines of %s are not together" % (DATA, n, mid))
                if (mu.ffi, mu.prove, mu.what) != (ffi.split(), prove.split(), what):
                    die("%s:%d: %s's ffi, prove or what differs from its first line"
                        % (DATA, n, mid))
            else:
                mu = Mutant(mid, ffi, prove, what)
                by[mid] = mu
                mutants.append(mu)
            mu.edits.append(Edit(file, int(ln), old, new, n))
    return mutants, groups


def expand(names, groups, seen=()):
    out = []
    for x in names:
        if x in groups:
            if x in seen:
                die("group %s includes itself" % x)
            out += expand(groups[x], groups, seen + (x,))
        else:
            out.append(x)
    # Unique, in order.
    res = []
    for x in out:
        if x not in res:
            res.append(x)
    return res


def properties():
    """The property names of cryptol/properties.txt, in order."""
    props = []
    with open(os.path.join(VERUS, "cryptol", "properties.txt")) as f:
        for line in f:
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            props.append(line.split("|")[1].strip())
    return props


def module_exists(root, path):
    """Whether the module path (aes::aes_impl::main) is a module of the
    crate under root/src: a file a/b.rs or a/b/mod.rs, or a `mod` item in
    its parent's file."""
    parts = path.split("::")
    src = os.path.join(root, "src")
    if os.path.exists(os.path.join(src, *parts) + ".rs") or \
            os.path.exists(os.path.join(src, *(parts + ["mod.rs"]))):
        return True
    parent = parts[:-1]
    for cand in ([os.path.join(src, *parent) + ".rs",
                  os.path.join(src, *(parent + ["mod.rs"]))] if parent else
                 [os.path.join(src, "lib.rs")]):
        if os.path.exists(cand):
            with open(cand) as f:
                if re.search(r"^\s*(pub\s+)?mod\s+%s\s*\{" % re.escape(parts[-1]),
                             f.read(), re.M):
                    return True
    return False


def apply_edit(e, text):
    """The source text with e applied, or a reason it does not apply."""
    lines = text.split("\n")
    if e.line < 1 or e.line > len(lines):
        return None, "line %d is past the end" % e.line
    src = lines[e.line - 1]
    count = src.count(e.old)
    if count != 1:
        return None, "'%s' occurs %d times on line %d: %s" % (
            e.old, count, e.line, src.strip())
    lines[e.line - 1] = src.replace(e.old, e.new)
    return "\n".join(lines), None


def mutate_texts(m, read):
    """{file: mutated text} for m, read(file) giving a pristine text; or a
    reason it does not apply."""
    texts = {}
    for e in m.edits:
        if e.file not in texts:
            texts[e.file] = read(e.file)
        new, why = apply_edit(e, texts[e.file])
        if new is None:
            return None, why
        texts[e.file] = new
    return texts, None


# --------------------------------------------------------------- the tree


def tree_paths(tree):
    tree = os.path.abspath(tree)
    return (tree, os.path.join(tree, "repo", "verus"),
            os.path.join(tree, "pristine"), os.path.join(tree, "results"))


def write_fresh(path, text):
    """Write text to path with a new mtime, so that cargo sees the change (a
    restored file must not look older than its build)."""
    with open(path, "w") as f:
        f.write(text)
    now = time.time()
    os.utime(path, (now, now))


def restore_all(tree):
    _, verus, pristine, _ = tree_paths(tree)
    for root, _, files in os.walk(pristine):
        for name in files:
            p = os.path.join(root, name)
            rel = os.path.relpath(p, pristine)
            dst = os.path.join(verus, rel)
            with open(p) as f:
                orig = f.read()
            with open(dst) as f:
                cur = f.read()
            if cur != orig:
                write_fresh(dst, orig)


class Applied(object):
    """Context manager: m applied in the tree, the pristine files restored
    on exit."""

    def __init__(self, tree, m):
        self.tree, self.m = tree, m

    def __enter__(self):
        _, verus, pristine, _ = tree_paths(self.tree)

        def read(file):
            src = os.path.join(verus, file)
            keep = os.path.join(pristine, file)
            if not os.path.exists(keep):
                os.makedirs(os.path.dirname(keep), exist_ok=True)
                shutil.copyfile(src, keep)
            with open(keep) as f:
                return f.read()

        texts, why = mutate_texts(self.m, read)
        if texts is None:
            die("%s: %s" % (self.m.id, why))
        for file, text in texts.items():
            write_fresh(os.path.join(verus, file), text)
        return self

    def __exit__(self, *exc):
        restore_all(self.tree)
        return False


class Unmutated(object):
    """Context manager: the tree as it is (the control of a witness)."""

    def __init__(self, tree):
        self.tree = tree

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False


def run(cmd, cwd, log, env=None, timeout=None):
    """Run cmd with output to log; (exit status, seconds). A run past
    timeout is killed with its process group and returns status None."""
    t0 = time.time()
    with open(log, "w") as out:
        out.write(">> %s\n" % " ".join(shlex.quote(c) for c in cmd))
        out.flush()
        p = subprocess.Popen(cmd, cwd=cwd, stdout=out, stderr=subprocess.STDOUT,
                             env=env, start_new_session=True)
        try:
            status = p.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()
            status = None
    return status, int(time.time() - t0)


def timeout():
    return int(os.environ.get("MUTATION_TIMEOUT", "3600"))


def cargo_verus():
    return shlex.split(os.environ.get("CARGO_VERUS", "cargo verus"))


# --------------------------------------------------------------- results


def result_path(tree, column, mid):
    d = os.path.join(tree_paths(tree)[3], column)
    os.makedirs(d, exist_ok=True)
    return os.path.join(d, mid + ".json")


def save(tree, column, mid, res):
    with open(result_path(tree, column, mid), "w") as f:
        json.dump(res, f, indent=1, sort_keys=True)
        f.write("\n")


def loaded(tree, column, mid):
    p = result_path(tree, column, mid)
    if not os.path.exists(p):
        return None
    with open(p) as f:
        return json.load(f)


# --------------------------------------------------------------- commands


def cmd_check(_args):
    mutants, groups = load()
    props = set(properties())
    bad = 0
    n_edits = 0

    def read(file):
        with open(os.path.join(VERUS, file)) as f:
            return f.read()

    for m in mutants:
        missing = [e.file for e in m.edits
                   if not os.path.exists(os.path.join(VERUS, e.file))]
        if missing:
            print("%s: no file %s" % (m.id, " ".join(missing)))
            bad += 1
            continue
        n_edits += len(m.edits)
        _, why = mutate_texts(m, read)
        if why:
            print("%s: %s" % (m.id, why))
            bad += 1
        for p in expand(m.ffi, groups):
            if p not in props:
                print("%s: no property %s" % (m.id, p))
                bad += 1
        for u in expand(m.prove, groups):
            if not module_exists(VERUS, u):
                print("%s: no module %s" % (m.id, u))
                bad += 1
    print("%d mutants (%d changes), %d problems" % (len(mutants), n_edits, bad))
    return 1 if bad else 0


def cmd_list(_args):
    mutants, groups = load()
    for m in mutants:
        where = ", ".join("%s:%d" % (e.file, e.line) for e in m.edits)
        print("%s  %s  %s  [%d properties; %s]" % (
            m.id, where, m.what, len(expand(m.ffi, groups)),
            " ".join(expand(m.prove, groups))))
    return 0


def git_out(args):
    p = subprocess.run(["git", "-C", REPO] + args, capture_output=True, text=True)
    return p.stdout.strip() if p.returncode == 0 else None


def cmd_setup(args):
    if len(args) != 1:
        die("setup TREE")
    tree, verus, _, _ = tree_paths(args[0])
    if os.path.exists(os.path.join(tree, "repo")):
        die("%s exists" % os.path.join(tree, "repo"))
    os.makedirs(tree, exist_ok=True)

    def ign(d, names):
        skip = set(n for n in names if n in (".git", "target"))
        # The links check-ffi.sh makes beside our .cry files are build
        # output (gitignored); NSA's .so/.dylib links beside theirs are kept
        # (dangling symlinks into unbuilt Rust, as in the checkout).
        if os.path.abspath(d).startswith(os.path.join(VERUS, "cryptol")):
            skip |= set(n for n in names if n.endswith((".so", ".dylib")))
        return skip

    shutil.copytree(REPO, os.path.join(tree, "repo"), symlinks=True,
                    ignore=ign)
    # The commit copied, for the report (the tree has no git of its own
    # until `saw`).
    status = git_out(["status", "--porcelain", "--", "verus"])
    with open(os.path.join(tree, "source.json"), "w") as f:
        json.dump({"commit": git_out(["rev-parse", "HEAD"]),
                   "dirty": bool(status), "date": time.strftime(
                       "%Y-%m-%dT%H:%M:%SZ", time.gmtime())}, f, indent=1)
        f.write("\n")
    status, secs = build_ffi(verus, os.path.join(tree, "setup.log"))
    if status != 0:
        die("the FFI library does not build in %s (setup.log)" % verus)
    print("setup: %s (the FFI library built, %d s)" % (verus, secs))
    return 0


def select(args, mutants):
    ids = [a for a in args if not a.startswith("--")]
    if not ids:
        return mutants
    by = dict((m.id, m) for m in mutants)
    for i in ids:
        if i not in by:
            die("no mutant %s" % i)
    return [by[i] for i in ids]


def build_ffi(verus, log):
    """check-ffi.sh's step 1: ffi/ (its own workspace) built into the
    crate's target directory."""
    jobs = os.environ.get("FFI_JOBS", str(os.cpu_count() or 1))
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = os.path.join(verus, "target")
    cargo = os.environ.get("CARGO", "cargo")
    return run([cargo, "build", "--release", "--locked", "-j" + jobs],
               os.path.join(verus, "ffi"), log, env=env)


def ffi_once(tree, props, logbase, stop_early=True):
    """Build the library from the tree as it is and run props (all when
    props is None). A dict: outcome, failed properties, times."""
    _, verus, _, _ = tree_paths(tree)
    status, bsecs = build_ffi(verus, logbase + ".build.log")
    if status != 0:
        return {"outcome": "nocompile", "build_s": bsecs}
    env = dict(os.environ)
    env["FFI_LIB"] = FFI_LIB
    if props is None or not stop_early:
        cmd = ["scripts/check-ffi.sh"] + (props or [])
        status, secs = run(cmd, verus, logbase + ".log", env=env,
                           timeout=timeout())
        with open(logbase + ".log") as f:
            out = f.read()
    else:
        # One property per check-ffi.sh run (each is its own cryptol run
        # anyway), stopping at the first that fails: a killed mutant needs
        # one killer, and only a survivor needs them all.
        out, secs, status = "", 0, 0
        for p in props:
            st, s = run(["scripts/check-ffi.sh", p], verus,
                        logbase + ".one.log", env=env, timeout=timeout())
            secs += s
            with open(logbase + ".one.log") as f:
                out += f.read()
            if st != 0:
                status = st
                break
        with open(logbase + ".log", "w") as f:
            f.write(out)
    failed = re.findall(r"^\s+FAIL\s+(\S+):", out, re.M)
    passed = re.findall(r"^\s+PASS\s+(\S+):", out, re.M)
    res = {"build_s": bsecs, "run_s": secs, "failed": failed,
           "passed": len(passed)}
    if status is None:
        res["outcome"] = "hang"
    elif status == 0 and not failed:
        res["outcome"] = "survived"
    elif status == 1 and failed:
        res["outcome"] = "killed"
        # The first lines of each failure's reason, from the log.
        why = {}
        for p in failed:
            m = re.search(r"^\s+FAIL\s+%s:.*\n((?:\s{9}.*\n){0,3})"
                          % re.escape(p), out, re.M)
            why[p] = [x.strip() for x in (m.group(1) if m else "").splitlines()]
        res["why"] = why
    else:
        res["outcome"] = "error"
        res["status"] = status
    return res


def cmd_ffi(args):
    if not args:
        die("ffi TREE [ID ...] [--full] [--baseline] [--redo]")
    tree = args[0]
    rest = args[1:]
    full = "--full" in rest
    mutants, groups = load()
    logs = os.path.join(tree_paths(tree)[3], "ffi")
    os.makedirs(logs, exist_ok=True)
    restore_all(tree)
    if "--baseline" in rest:
        props = None if full else expand(
            [p for m in mutants for p in m.ffi], groups)
        res = ffi_once(tree, props, os.path.join(logs, "baseline"),
                       stop_early=False)
        res["properties"] = "all" if full else len(props)
        save(tree, "ffi", "baseline" + ("-full" if full else ""), res)
        print("baseline: %s (%s properties, %s passed)" % (
            res["outcome"], res["properties"], res.get("passed")))
        return 0 if res["outcome"] == "survived" else 1
    column = "ffi-full" if full else "ffi"
    for m in select(rest, mutants):
        if loaded(tree, column, m.id) and "--redo" not in rest and \
                not [a for a in rest if not a.startswith("--")]:
            continue
        if full:
            t = loaded(tree, "ffi", m.id)
            if not t or t["outcome"] != "survived":
                continue
        props = None if full else expand(m.ffi, groups)
        with Applied(tree, m):
            res = ffi_once(tree, props,
                           os.path.join(logs, m.id + ("-full" if full else "")))
        res["properties"] = "all" if full else len(props)
        save(tree, column, m.id, res)
        print("%s %s: %s%s (%s properties, %s s)" % (
            column, m.id, res["outcome"],
            (" by " + " ".join(res["failed"])) if res.get("failed") else "",
            res["properties"], res.get("run_s", res.get("build_s"))))
        sys.stdout.flush()
    return 0


# Verus's messages, as rustc's: a header "error: postcondition not
# satisfied" (rustc's own errors carry a code: "error[E0308]: ..."), then
# "--> file:line:col" and the source excerpt, with notes ("note: ...",
# "= note: ...") that are not messages of their own here. The run ends with
# "verification results:: N verified, M errors" (absent when rustc stopped
# before Verus ran) and cargo's "error: could not compile ...".
HEAD = re.compile(r"^(error|warning)(\[(E\d+)\])?: (.*)$")
LOC = re.compile(r"^\s*--> (\S+\.rs):(\d+):(\d+)")
SUMMARY = re.compile(r"^verification results:: (\d+) verified, (\d+) errors", re.M)
CARGO_TAIL = re.compile(r"^(could not compile|aborting due to|\d+ warnings? emitted)")
RLIMIT = re.compile(r"[Rr]esource limit|rlimit")
# What Verus says when it fails to prove something.
VERIFY = re.compile(r"not satisfied|assertion failed|might not|possible "
                    r"arithmetic|possible division|precondition|postcondition|"
                    r"invariant|decreases|loop must|termination|not proved|"
                    r"out of bounds|could not prove|cannot prove")


def parse_messages(log_text):
    """Every message of the run: dicts of severity, code, location, text."""
    msgs = []
    cur = None
    for line in log_text.splitlines():
        m = HEAD.match(line)
        if m:
            if CARGO_TAIL.match(m.group(4)):
                cur = None
                continue
            cur = {"severity": m.group(1), "code": m.group(3),
                   "text": m.group(4), "at": "?"}
            msgs.append(cur)
            continue
        if cur is None:
            continue
        m = LOC.match(line)
        if m and cur["at"] == "?":
            cur["at"] = "%s:%s:%s" % m.group(1, 2, 3)
    return msgs


def classify(log_text):
    """The Verus column's outcome, and each message with its kind: verify
    (Verus failed to prove it), rlimit (the resource limit reached), error
    (rustc, or Verus refusing the code: no proof was attempted), warning."""
    msgs = []
    for x in parse_messages(log_text):
        if x["severity"] == "warning":
            kind = "warning"
        elif x["code"]:
            kind = "error"
        elif RLIMIT.search(x["text"]):
            kind = "rlimit"
        elif VERIFY.search(x["text"]):
            kind = "verify"
        else:
            kind = "error"
        msgs.append({"at": x["at"], "severity": x["severity"], "kind": kind,
                     "text": x["text"][:500]})
    kinds = set(x["kind"] for x in msgs)
    s = SUMMARY.search(log_text)
    if s is None and ("error" in kinds or not msgs):
        # rustc (or Verus's own checks) stopped the build before any proof.
        outcome = "nocompile" if "error" in kinds else "no result"
    elif "verify" in kinds or (s and int(s.group(2)) > 0 and "rlimit" not in kinds):
        outcome = "unproved"
    elif "rlimit" in kinds:
        outcome = "timeout"
    elif "error" in kinds:
        outcome = "error"
    else:
        outcome = "proved"
    return outcome, msgs


def verified_count(log_text):
    s = SUMMARY.search(log_text)
    return (int(s.group(1)), int(s.group(2))) if s else None


def prove_once(tree, modules, logbase, extra=()):
    _, verus, _, _ = tree_paths(tree)
    log = logbase + ".log"
    cmd = cargo_verus() + ["focus", "--"]
    for u in modules:
        cmd += ["--verify-only-module", u]
    cmd += list(extra)
    status, secs = run(cmd, verus, log, timeout=timeout())
    with open(log) as f:
        text = f.read()
    res = {"run_s": secs, "status": status, "modules": modules}
    if extra:
        res["args"] = list(extra)
    if status is None:
        res["outcome"] = "hang"
        return res
    outcome, msgs = classify(text)
    vc = verified_count(text)
    if vc:
        res["verified"], res["errors"] = vc
    if status == 0 and outcome == "no result":
        # cargo replayed an earlier, successful verification of this very
        # text (cargo-verus caches): what it replays is a pass.
        outcome = "proved"
        res["cached"] = True
    if status != 0 and outcome == "proved":
        outcome = "error"
    res["outcome"] = outcome
    res["messages"] = msgs
    return res


def cmd_prove(args):
    if not args:
        die("prove TREE [ID ...] [--baseline] [--redo]")
    tree = args[0]
    rest = args[1:]
    mutants, groups = load()
    logs = os.path.join(tree_paths(tree)[3], "prove")
    os.makedirs(logs, exist_ok=True)
    restore_all(tree)
    if "--baseline" in rest:
        modules = expand([u for m in mutants for u in m.prove], groups)
        res = prove_once(tree, modules, os.path.join(logs, "baseline"))
        save(tree, "prove", "baseline", res)
        print("baseline: %s (%d modules, %s verified, %d s)" % (
            res["outcome"], len(modules), res.get("verified"), res["run_s"]))
        return 0 if res["outcome"] == "proved" else 1
    explicit = [a for a in rest if not a.startswith("--")]
    for m in select(rest, mutants):
        if loaded(tree, "prove", m.id) and "--redo" not in rest \
                and not explicit:
            continue
        modules = expand(m.prove, groups)
        with Applied(tree, m):
            res = prove_once(tree, modules, os.path.join(logs, m.id))
        save(tree, "prove", m.id, res)
        print("prove %s: %s %s (%d s)" % (
            m.id, res["outcome"], kinds_text(res), res["run_s"]))
        sys.stdout.flush()
    return 0


def kinds_text(res):
    kinds = {}
    for x in res.get("messages", []):
        if isinstance(x, dict) and x["kind"] != "warning":
            kinds[x["kind"]] = kinds.get(x["kind"], 0) + 1
    return " ".join("%s=%d" % kv for kv in sorted(kinds.items()))


def cmd_diagnose(args):
    """Verify mutants again with extra Verus arguments after -- (--rlimit
    100, say), to see whether more time turns a timeout into a pass or a
    verification error. Diagnostic only: the Verus column is prove's, at
    the committed settings. Results in TREE/results/diagnose/."""
    if "--" not in args or len(args) < 3:
        die("diagnose TREE ID ... -- VERUS_ARGS ...")
    k = args.index("--")
    tree, ids, extra = args[0], args[1:k], args[k + 1:]
    mutants, groups = load()
    logs = os.path.join(tree_paths(tree)[3], "diagnose")
    os.makedirs(logs, exist_ok=True)
    restore_all(tree)
    for m in select(ids, mutants):
        modules = expand(m.prove, groups)
        with Applied(tree, m):
            res = prove_once(tree, modules, os.path.join(logs, m.id), extra)
        save(tree, "diagnose", m.id, res)
        print("diagnose %s: %s (%d s)" % (m.id, res["outcome"], res["run_s"]))
        for x in res.get("messages", []):
            print("   %s %s %s" % (x["kind"], x["at"], x["text"][:300]))
        sys.stdout.flush()
    return 0


def cmd_witness(args):
    """Run one Cryptol :check against the library built with a mutant (or
    with none, ID "none", the control) applied, typically at an input the
    properties never try (a longer message): a concrete witness that an FFI
    survivor is a real bug. MODULE is under cryptol/; EXPR is a Cryptol
    expression of a function to Bit that may use the module's definitions.
    The links check-ffi.sh makes beside the modules must exist (any ffi run
    in the tree makes them)."""
    if len(args) != 5:
        die("witness TREE ID MODULE EXPR TESTS")
    tree, mid, module, expr, tests = args
    mutants, _ = load()
    m = None if mid == "none" else select([mid], mutants)[0]
    _, verus, _, results = tree_paths(tree)
    repo = os.path.dirname(verus)
    logs = os.path.join(results, "witness")
    os.makedirs(logs, exist_ok=True)
    restore_all(tree)
    icry = os.path.join(logs, mid + ".icry")
    with open(icry, "w") as f:
        f.write(":set tests=%s\n:load %s\n:check %s\n"
                % (tests, os.path.join(verus, "cryptol", module), expr))
    # check-ffi.sh's ad hoc signed copy on macOS (made by any earlier run
    # in this tree), else CRYPTOL.
    cryptol = os.path.join(verus, "target", "ffi", "cryptol-adhoc", "cryptol")
    if not os.path.exists(cryptol):
        cryptol = shutil.which(os.environ.get("CRYPTOL", "cryptol")) or "cryptol"
    env = dict(os.environ)
    env["CRYPTOLPATH"] = "%s:%s" % (repo, os.path.join(verus, "cryptol"))
    with (Applied(tree, m) if m else Unmutated(tree)):
        st, _ = build_ffi(verus, os.path.join(logs, mid + ".build.log"))
        if st != 0:
            die("%s does not build" % mid)
        st, secs = run([cryptol, "-b", icry], repo,
                       os.path.join(logs, mid + ".log"), env=env,
                       timeout=timeout())
    with open(os.path.join(logs, mid + ".log")) as f:
        out = f.read()
    verdict = ("counterexample" if "Counterexample" in out or
               re.search(r"^\s*= False", out, re.M) else
               "passed" if re.search(r"Passed \d+ tests", out) else "error")
    print("witness %s: %s (%s s; log %s)" % (mid, verdict, secs,
                                           os.path.join(logs, mid + ".log")))
    return 0 if verdict == "counterexample" else 1


def saw_git(tree):
    """check-saw.sh reads the commit (git rev-parse HEAD) and whether the
    tree is clean (git status), but setup copies no .git: give the tree's
    repo a git of its own, one commit of the pristine copy, so that a
    mutant is an uncommitted change (check-saw.sh --print says "with
    uncommitted changes: --print only")."""
    repo = os.path.dirname(tree_paths(tree)[1])
    if os.path.exists(os.path.join(repo, ".git")):
        return
    git = ["git", "-c", "user.name=mutation.py",
           "-c", "user.email=mutation@localhost", "-c", "commit.gpgsign=false"]
    log = os.path.join(tree_paths(tree)[0], "git.log")
    for cmd in (["init", "-q"], ["add", "-A"],
                ["commit", "-q", "-m", "pristine copy (mutation.py saw)"]):
        status, _ = run(git + cmd, repo, log)
        if status != 0:
            die("git %s failed in %s (%s)" % (cmd[0], repo, log))


def demangle(name):
    p = subprocess.run(["c++filt"], input=name, capture_output=True, text=True)
    out = p.stdout.strip() if p.returncode == 0 and p.stdout.strip() else name
    return re.sub(r"\[[0-9a-f]+\]", "", out)


def saw_script_result(res, keep):
    """Fill in res (a run whose script res["script"] failed or was killed)
    from that script's saved saw log in keep: the function being verified,
    whether there is a counterexample, the error lines. A script that
    stops at an unbound name (a symbol the scripts verify that the mutated
    build no longer has: a const-generic instance the mutant stopped
    calling) proved nothing false: its outcome is "error", not "failed"."""
    route, name = res["script"].split("/", 1)
    slog = os.path.join(keep, "%s-%s.log" % (route, name[:-4]))
    text = ""
    if os.path.exists(slog):
        with open(slog) as f:
            text = f.read()
    # The function being verified when the proof failed.
    verifying = re.findall(r"^Verifying (\S+?) *\.\.\.$", text, re.M)
    res["subprogram"] = demangle(verifying[-1]) if verifying else None
    res["cex"] = "-Counterexample-" in text
    err = [x for x in text.splitlines()
           if re.search(r"Proof failed|error|Error|failed", x)]
    res["errors"] = [x.strip()[:300] for x in err[:10]]
    unbound = re.search(r'Error: Unbound variable: "(\S+)"', text)
    if res["outcome"] == "failed" and unbound:
        res["outcome"] = "error"
        res["unbound"] = unbound.group(1)
        res["subprogram"] = None


def saw_once(tree, logbase):
    """check-saw.sh --print on the tree as it is. A dict: outcome (proved,
    failed: a proof failed, with a counterexample or not; killed: the
    memory cap; error: anything else), the script and function that failed,
    and the per-script times."""
    _, verus, _, _ = tree_paths(tree)
    log = logbase + ".log"
    status, secs = run(["scripts/check-saw.sh", "--print"], verus, log,
                       timeout=timeout())
    # check-saw.sh clears saw/obj/ each run: keep this run's saw logs.
    keep = logbase + ".logs"
    if os.path.exists(keep):
        shutil.rmtree(keep)
    src = os.path.join(verus, "saw", "obj", "logs")
    if os.path.isdir(src):
        shutil.copytree(src, keep)
    with open(log) as f:
        out = f.read()
    res = {"status": status, "run_s": secs,
           "route": os.environ.get("SAW_ROUTE", "all")}
    m = re.search(r"^>> SAW \([^)]*\): (\d+) proved", out, re.M)
    res["proved"] = int(m.group(1)) if m else None
    res["times"] = re.findall(r"(\d+ s for \S+\.saw)", out)
    script = re.search(r"saw (\S+\.saw) (FAILED|was KILLED)", out)
    neg = re.search(r"NEGATIVE CONTROL PROVED: (\S+)", out)
    if status is None:
        res["outcome"] = "hang"
    elif status == 0:
        res["outcome"] = "proved"
    elif script:
        res["script"] = script.group(1)
        res["outcome"] = "killed" if script.group(2) != "FAILED" else "failed"
        saw_script_result(res, keep)
    elif neg:
        res["outcome"] = "error"
        res["script"] = neg.group(1)
        res["errors"] = ["negative control proved"]
    else:
        res["outcome"] = "error"
        res["errors"] = [x[:300] for x in out.splitlines() if
                         x.startswith("!!")][:10]
    return res


def cmd_saw(args):
    """The SAW column: per mutant, scripts/check-saw.sh --print in the tree
    with the mutant applied (SAW_ROUTE: both routes by default). A mutant
    SAW catches makes a proof fail (check-saw.sh stops at the first script
    that fails); a negative control that stops failing is reported as an
    error. --baseline: the unmutated tree (it must prove). Results in
    TREE/results/saw/, with each run's saw logs in <ID>.logs/."""
    if len(args) < 2:
        die("saw TREE ID ... | saw TREE --baseline")
    tree, rest = args[0], args[1:]
    mutants, _ = load()
    logs = os.path.join(tree_paths(tree)[3], "saw")
    os.makedirs(logs, exist_ok=True)
    restore_all(tree)
    saw_git(tree)
    if "--baseline" in rest:
        res = saw_once(tree, os.path.join(logs, "baseline"))
        save(tree, "saw", "baseline", res)
        print("saw baseline: %s, %s proved (%d s)" % (
            res["outcome"], res.get("proved"), res["run_s"]))
        return 0 if res["outcome"] == "proved" else 1
    for m in select(rest, mutants):
        with Applied(tree, m):
            res = saw_once(tree, os.path.join(logs, m.id))
        save(tree, "saw", m.id, res)
        print("saw %s: %s%s (%d s)" % (
            m.id, res["outcome"],
            (" at %s %s%s" % (res.get("script"), res.get("subprogram"),
                              ", counterexample" if res.get("cex") else ""))
            if res.get("script") else "", res["run_s"]))
        sys.stdout.flush()
    return 0


def cmd_reclassify(args):
    """Re-read every saved proof log, and every saved saw log of a failed
    script, and classify it again (after a change to the classifier; the
    logs are the record)."""
    if len(args) != 1:
        die("reclassify TREE")
    tree = args[0]
    for path in sorted(os.listdir(os.path.join(tree_paths(tree)[3], "prove"))):
        if not path.endswith(".json"):
            continue
        mid = path[:-5]
        res = loaded(tree, "prove", mid)
        log = os.path.join(tree_paths(tree)[3], "prove", mid + ".log")
        if not os.path.exists(log) or res.get("outcome") == "hang":
            continue
        with open(log) as f:
            text = f.read()
        outcome, msgs = classify(text)
        if res.get("status") == 0 and outcome == "no result":
            outcome = "proved"
        if res.get("status") not in (0, None) and outcome == "proved":
            outcome = "error"
        res["outcome"], res["messages"] = outcome, msgs
        save(tree, "prove", mid, res)
        print("%s: %s" % (mid, outcome))
    sawdir = os.path.join(tree_paths(tree)[3], "saw")
    for path in sorted(os.listdir(sawdir) if os.path.isdir(sawdir) else []):
        if not path.endswith(".json"):
            continue
        mid = path[:-5]
        res = loaded(tree, "saw", mid)
        if not res.get("script"):
            continue
        if res["outcome"] == "error":
            res["outcome"] = "failed"
        saw_script_result(res, os.path.join(sawdir, mid + ".logs"))
        save(tree, "saw", mid, res)
        print("saw %s: %s" % (mid, res["outcome"]))
    return 0


def cell_ffi(r, rf):
    if not r:
        return "not run"
    o = r["outcome"]
    if o == "killed":
        return "killed by %s" % " ".join(r["failed"])
    if o == "survived":
        if rf:
            if rf["outcome"] == "killed":
                return "survived %d; killed by %s" % (
                    r["properties"], " ".join(rf["failed"]))
            return "survived %d; %s all" % (r["properties"], rf["outcome"])
        return "survived %d" % r["properties"]
    return o


def cell_prove(r):
    if not r:
        return "not run"
    k = kinds_text(r)
    return "%s (%s)" % (r["outcome"], k.replace("=", " ")) if k else r["outcome"]


def cell_saw(r):
    if not r:
        return ""
    if r.get("unbound"):
        return "error at %s: `%s` unbound" % (r["script"], r["unbound"])
    if r.get("script"):
        return "%s at %s `%s`%s" % (
            r["outcome"], r["script"], r.get("subprogram"),
            " (counterexample)" if r.get("cex") else "")
    return r["outcome"]


def verdict(m, rf, rff, rp):
    """The mutant's category for the table."""
    if not rf or not rp:
        return "incomplete"
    if rf["outcome"] == "nocompile" or rp["outcome"] == "nocompile":
        return "does not compile"
    ffi_killed = rf["outcome"] in ("killed", "hang") or (
        rff is not None and rff["outcome"] in ("killed", "hang"))
    proof_killed = rp["outcome"] in ("unproved", "timeout", "error")
    if ffi_killed and proof_killed:
        return "both"
    if ffi_killed:
        return "FFI only"
    if rf["outcome"] != "survived" or (rff and rff["outcome"] != "survived"):
        return "FFI error"
    if rp["outcome"] == "unproved":
        return "Verus only"
    if rp["outcome"] == "timeout":
        return "Verus only (rlimit)"
    if rp["outcome"] == "proved":
        return "neither"
    return "Verus: " + rp["outcome"]


def cmd_report(args):
    if len(args) != 1:
        die("report TREE")
    tree = args[0]
    mutants, _ = load()
    rows = []
    counts = {}
    for m in mutants:
        rf = loaded(tree, "ffi", m.id)
        rff = loaded(tree, "ffi-full", m.id)
        rp = loaded(tree, "prove", m.id)
        rs = loaded(tree, "saw", m.id)
        v = verdict(m, rf, rff, rp)
        counts[v] = counts.get(v, 0) + 1
        where = ", ".join("`%s`:%d" % (os.path.basename(e.file), e.line)
                          for e in m.edits)
        rows.append("| %s | %s | %s | %s | %s | %s | %s |" % (
            m.id, where, m.what.replace("|", "\\|"),
            cell_ffi(rf, rff), cell_prove(rp), cell_saw(rs), v))
    src = os.path.join(tree_paths(tree)[0], "source.json")
    if os.path.exists(src):
        with open(src) as f:
            s = json.load(f)
        print("Tree copied from commit %s%s at %s." % (
            s.get("commit"), " (with uncommitted changes)" if s.get("dirty")
            else "", s.get("date")))
        print()
    print("| id | where | mutant | FFI | Verus | SAW | caught by |")
    print("|---|---|---|---|---|---|---|")
    for r in rows:
        print(r)
    print()
    for k in sorted(counts):
        print("* %s: %d" % (k, counts[k]))
    return 0


def main(argv):
    if not argv:
        sys.stderr.write(__doc__)
        return 2
    cmds = {"check": cmd_check, "list": cmd_list, "setup": cmd_setup,
            "ffi": cmd_ffi, "prove": cmd_prove, "report": cmd_report,
            "reclassify": cmd_reclassify, "diagnose": cmd_diagnose,
            "witness": cmd_witness, "saw": cmd_saw}
    if argv[0] not in cmds:
        die("unknown command %s" % argv[0])
    return cmds[argv[0]](argv[1:])


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
