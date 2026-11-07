#!/usr/bin/env python3
"""coverage-summary.py -- the per-file coverage table of check-coverage.sh.

The counterpart of the SPARK crate's spark/scripts/coverage-summary.py
(github.com/manthonyaiello/Foundation, tag spark-v1.0). That one reads
gnatcov's XML; this one reads `llvm-cov export` (JSON) of the instrumented
FFI library.

For each source file of interest (coverage/units.txt, paths relative to
verus/src/) it prints the regions, lines and branch outcomes covered out of
those instrumented, then the totals. Regions are rustc's code regions (the
nearest thing to gnatcov's statements); a branch is one outcome of an
`if`, a `while`, a `match` arm or an operand of `&&` / `||` (rustc's
-Zcoverage-options=branch,condition; the nearest thing to gnatcov's
decisions). There is no MC/DC column: rustc does not measure it.

A generic function has one record per instantiation; a region or a branch
outcome is covered when any instantiation covers it, so each is counted
once, by its source position.

With --explained, it then lists every violation (a region never executed, a
branch outcome never taken) with the entry of coverage/explained.txt that
explains it, or as UNEXPLAINED, and exits 1 when one is unexplained. An
entry is "file | line text | reason": it matches a violation that starts on
a line of that file whose text, trimmed, is that text. It also exits 1 when
a file under verus/src/ has instrumented code and is not in units.txt, or a
file of units.txt has none (the list has gone stale).

Usage: coverage-summary.py EXPORT_JSON SRC_DIR --units UNITS [--explained EXPLAINED]
"""

import argparse
import json
import os
import sys

# llvm-cov's region kinds (llvm::coverage::CounterMappingRegion).
CODE_REGION = 0

KINDS = ("region", "line", "branch")


def read_units(path):
    """The files of interest, relative to SRC_DIR, in the order listed."""
    units = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if line:
                units.append(line)
    return units


def read_explained(path):
    """{(file, line text): reason} from explained.txt."""
    entries = {}
    with open(path, encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            parts = [p.strip() for p in line.split(" | ")]
            if len(parts) != 3 or not all(parts):
                sys.exit("%s:%d: expected \"file | line text | reason\"" % (path, n))
            entries[(parts[0], parts[1])] = parts[2]
    return entries


def collect(export, src_dir):
    """Per file under src_dir: {"region": {pos: count}, "branch": {(pos, outcome): count},
    "lines": (covered, total)}, merged over the instantiations by maximum."""
    src_dir = os.path.realpath(src_dir) + os.sep
    files = {}
    for data in export["data"]:
        for fn in data["functions"]:
            names = fn["filenames"]
            for r in fn["regions"]:
                l1, c1, l2, c2, count, file_id, _exp, kind = r[:8]
                path = os.path.realpath(names[file_id])
                if not path.startswith(src_dir) or kind != CODE_REGION:
                    continue
                acc = files.setdefault(path[len(src_dir):],
                                       {"region": {}, "branch": {}})
                pos = (l1, c1, l2, c2)
                acc["region"][pos] = max(acc["region"].get(pos, 0), count)
            for b in fn.get("branches", []):
                l1, c1, l2, c2, t, f, file_id = b[:7]
                path = os.path.realpath(names[file_id])
                if not path.startswith(src_dir):
                    continue
                acc = files.setdefault(path[len(src_dir):],
                                       {"region": {}, "branch": {}})
                pos = (l1, c1, l2, c2)
                for outcome, count in (("true", t), ("false", f)):
                    key = (pos, outcome)
                    acc["branch"][key] = max(acc["branch"].get(key, 0), count)
        # Lines: llvm-cov's own count for the file (it merges the
        # instantiations itself); only the total is reported, not each line.
        for fi in data["files"]:
            path = os.path.realpath(fi["filename"])
            if not path.startswith(src_dir):
                continue
            acc = files.setdefault(path[len(src_dir):],
                                   {"region": {}, "branch": {}})
            acc["lines"] = (fi["summary"]["lines"]["covered"], fi["summary"]["lines"]["count"])
    return files


def cell(covered, total):
    """"covered/total (pct%)", or "-" when there is nothing to cover."""
    if total == 0:
        return "-"
    return "%d/%d (%d%%)" % (covered, total, 100 * covered // total)


def stats(acc):
    """{kind: (covered, total)}."""
    row = {k: (sum(1 for c in acc[k].values() if c > 0), len(acc[k])) for k in ("region", "branch")}
    row["line"] = acc.get("lines", (0, 0))
    return row


def violations(files, units, src_dir, explained):
    """Print each violation with its explanation; return the unexplained count."""
    entries = read_explained(explained)
    found = []
    for unit in units:
        acc = files.get(unit)
        if acc is None:
            continue
        for pos, count in acc["region"].items():
            if count == 0:
                found.append((unit, pos, "region never executed"))
        for (pos, outcome), count in acc["branch"].items():
            if count == 0:
                found.append((unit, pos, "branch never %s" % outcome))
    found.sort()
    lines_of = {}
    unexplained = 0
    used = set()
    print()
    print("violations: %d" % len(found))
    for unit, (l1, c1, l2, c2), what in found:
        if unit not in lines_of:
            with open(os.path.join(src_dir, unit), encoding="utf-8") as f:
                lines_of[unit] = f.read().splitlines()
        text = lines_of[unit][l1 - 1].strip()
        reason = entries.get((unit, text))
        where = "%s:%d:%d-%d:%d" % (unit, l1, c1, l2, c2)
        if reason is None:
            unexplained += 1
            print("  UNEXPLAINED %s: %s" % (where, what))
            print("              %s" % text)
        else:
            used.add((unit, text))
            print("  explained   %s: %s" % (where, what))
            print("              %s" % reason)
    for key in sorted(set(entries) - used):
        print("  (stale entry, matched nothing: %s | %s)" % key)
    print("unexplained: %d" % unexplained)
    return unexplained


def main(argv):
    ap = argparse.ArgumentParser(description="The per-file coverage table.")
    ap.add_argument("export_json")
    ap.add_argument("src_dir")
    ap.add_argument("--units", required=True)
    ap.add_argument("--explained")
    args = ap.parse_args(argv[1:])
    with open(args.export_json, encoding="utf-8") as f:
        export = json.load(f)
    units = read_units(args.units)
    files = collect(export, args.src_dir)

    bad = 0
    for path in sorted(set(files) - set(units)):
        if files[path]["region"]:
            print("!! %s has instrumented code and is not in %s" % (path, args.units))
            bad = 1
    for unit in units:
        if unit not in files or not files[unit]["region"]:
            print("!! %s (in %s) has no instrumented code" % (unit, args.units))
            bad = 1

    width = max(len(u) for u in units)
    head = "%-*s  %-16s  %-16s  %-16s" % (width, "file (verus/src/)", "region", "line", "branch")
    print(head)
    print("-" * len(head))
    total = {k: [0, 0] for k in KINDS}
    for unit in units:
        row = stats(files[unit]) if unit in files else {k: (0, 0) for k in KINDS}
        print("%-*s  %-16s  %-16s  %-16s" % (width, unit, *(cell(*row[k]) for k in KINDS)))
        for k in KINDS:
            total[k][0] += row[k][0]
            total[k][1] += row[k][1]
    print("-" * len(head))
    print("%-*s  %-16s  %-16s  %-16s" % (width, "total", *(cell(*total[k]) for k in KINDS)))
    print("(MC/DC: not measured; rustc has no MC/DC instrumentation)")
    if args.explained and violations(files, units, args.src_dir, args.explained):
        bad = 1
    sys.exit(bad)


if __name__ == "__main__":
    main(sys.argv)
