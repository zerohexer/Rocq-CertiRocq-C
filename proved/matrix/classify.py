#!/usr/bin/env python3
"""classify.py RESULTS... : the construct table's verdict for every cell, from the output of kitc.py (one line per cell).

Each cell is `ok` (translated and proved), `design` (refused because the value would be allocated behind the programmer's
back, or a memory used after it was handed on: what a runtime-free language cannot do), `invalid` (the generated program
is not Rocq: no verdict) or `gap` (runtime-free, not yet translated or proved), with the category of the gap.
Prints the summary and, with --md FILE, writes the table."""
import re, sys, collections

# cells whose refusal is by design: a value that needs allocation, a memory used after it was handed on
DESIGN_CELLS = {"A_par_option", "A_par_list", "A_par_sum", "P_mem_dup", "A_par_fun_in_pair", "A_par_fun_result"}
INVALID = re.compile(r"Cannot guess decreasing|Unable to unify|not found in the current environment|The reference .* was not found|Syntax error")

# (regex on the refusal, category), tried in order
GAP = [
  (r"PROOF FAILED", "a proof the tactics do not find (the translation was accepted)"),
  (r"must name no variable of the caller", "a function given that names a variable of the caller (a closure)"),
  (r"a let of a type this translator does not read", "a local function, a polymorphic or class-based helper, a memory inside a record"),
  (r"not a test this translator reads", "a boolean made by an if or a match"),
  (r"parameters or result are not of a kind", "a function giving back a boolean, a record of three, or a number with a memory, by recursion"),
  (r"a match used as a (number|memory) that this translator does not read", "a match on a counter that is not a recursion"),
  (r"not a counter this translator reads|not a test: (eqb|ltb)", "arithmetic or a comparison on counters"),
  (r"a match this translator does not read", "a pair of a number and a memory"),
  (r"not a record this translator reads", "a choice between records"),
]

def cells(paths):
    for p in paths:
        for line in open(p):
            line = line.strip()
            if not line:
                continue
            name = line.split()[0]
            yield name, line

def classify(name, line):
    if " PROVED " in line or line.split()[1:2] == ["PROVED"]:
        return "ok", ""
    if name in DESIGN_CELLS:
        return "design", ""
    if INVALID.search(line):
        return "invalid", ""
    for rx, cat in GAP:
        if re.search(rx, line):
            return "gap", cat
    return "gap", "unclassified: " + line[len(name):][:100]

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    md = None
    if "--md" in sys.argv:
        md = sys.argv[sys.argv.index("--md") + 1]
        args = [a for a in args if a != md]
    tally = collections.Counter()
    gaps = collections.defaultdict(list)
    design, invalid = [], []
    for name, line in cells(args):
        c, cat = classify(name, line)
        tally[c] += 1
        if c == "gap":
            gaps[cat].append(name)
        elif c == "design":
            design.append(name)
        elif c == "invalid":
            invalid.append(name)
    total = sum(tally.values())
    out = [f"{total} cells: {tally['ok']} translated and proved, {tally['design']} refused by design, "
           f"{tally['gap']} gaps, {tally['invalid']} not Rocq (no verdict)"]
    for cat, ns in sorted(gaps.items(), key=lambda kv: -len(kv[1])):
        out.append(f"\ngap ({len(ns)}): {cat}\n  " + " ".join(sorted(ns)))
    if design:
        out.append("\nby design: " + " ".join(sorted(design)))
    if invalid:
        out.append("\nnot Rocq: " + " ".join(sorted(invalid)))
    text = "\n".join(out)
    print(text)
    if md:
        open(md, "w").write("# The construct table\n\n```\n" + text + "\n```\n")

if __name__ == "__main__":
    main()
