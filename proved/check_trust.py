#!/usr/bin/env python3
"""check_trust.py: what is assumed, against proved/TRUSTED.txt (Rocq-C-solution.md §1.10, §13.9).

The list names every axiom of the proofs, every operation of the machine, every C body of hw/kq_hw.h and what the proved route's theorem
rests on.  A name in the tree and not on the list, or on the list and not in the tree, is a difference and this exits 1: a chain and a
push stop.  Adding to the list is the owner's decision.

  check_trust.py                the tree
  check_trust.py --gate LOG     also the gate's `Print Assumptions` list in LOG, and what each program's end theorem rests on
                                (its `NAME END-ASSUM n: names` lines, one for each program through the verified compiler, step 96)
"""
import re, subprocess, sys, os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SKIP = ("proved/gen/", "proved/matrix/", "proved/examples/", "tests/", "rocq-fork/")

def tracked():
    out = subprocess.run(["git", "-C", ROOT, "ls-files", "*.v"], capture_output=True, text=True, check=True).stdout.split()
    return [f for f in out if not f.startswith(SKIP)]

def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i): depth += 1; i += 2
        elif s.startswith("*)", i) and depth: depth -= 1; i += 2
        else:
            if not depth: out.append(s[i])
            i += 1
    return "".join(out)

def tree():
    found = {"axiom": set(), "hwop": set(), "hwfop": set(), "cbody": set(), "admitted": set()}
    for f in tracked():
        s = strip_comments(open(os.path.join(ROOT, f), errors="replace").read())
        for m in re.finditer(r"(?m)^\s*(?:Axiom|Axioms|Parameter|Parameters|Conjecture)\s+([^:.]*):", s):
            for n in m.group(1).split():
                found["axiom"].add(f + ":" + n)
        if re.search(r"\bAdmitted\b|\bAdmit\b", s):
            found["admitted"].add(f)
    kql = strip_comments(open(os.path.join(ROOT, "proved/KQL.v")).read())
    for key, name in [("hwop", "hwop"), ("hwfop", "hwfop")]:
        m = re.search(r"Inductive\s+" + name + r"\s*:=([^.]*)\.", kql)
        found[key] = {x.strip() for x in m.group(1).split("|") if x.strip()}
    h = open(os.path.join(ROOT, "hw/kq_hw.h")).read()
    found["cbody"] = set(re.findall(r"KQ_HW\s+\w+\s+(kq_hw_\w+)\s*\(", h))
    return found

def listed():
    want = {"axiom": set(), "hwop": set(), "hwfop": set(), "cbody": set(), "admitted": set(), "assumption": set()}
    for line in open(os.path.join(ROOT, "proved/TRUSTED.txt")):
        line = line.split("#", 1)[0].strip()
        if not line: continue
        kind, name = line.split()[:2]
        want[kind].add(name)
    return want

def main():
    t, w, bad = tree(), listed(), 0
    for k in ("axiom", "hwop", "hwfop", "cbody", "admitted"):
        for n in sorted(t[k] - w[k]):
            print(f"NOT ON THE LIST: {k} {n}"); bad += 1
        for n in sorted(w[k] - t[k]):
            print(f"ON THE LIST, NOT IN THE TREE: {k} {n}"); bad += 1
    if "--gate" in sys.argv:
        lines = open(sys.argv[sys.argv.index("--gate") + 1], errors="replace").read().split("\n")
        i = [j for j, l in enumerate(lines) if "trusted base" in l]
        got = set(lines[i[0] + 1].split()) if i else set()
        if not got:
            print("NO ASSUMPTIONS IN THE GATE'S LOG"); bad += 1
        for n in sorted(got - w["assumption"]):
            print(f"NOT ON THE LIST: assumption {n}"); bad += 1
        for n in sorted(w["assumption"] - got):
            print(f"ON THE LIST, NOT IN THE GATE: assumption {n}"); bad += 1
        # (step 96) each program's end theorem: every name it rests on on the list, and one line for each program through
        ends = {}
        for l in lines:
            m = re.match(r"^(\S+) END-ASSUM (\d+):(.*)$", l)
            if m:
                ends[m.group(1)] = m.group(3).split()
                if len(ends[m.group(1)]) != int(m.group(2)):
                    print(f"END THEOREM LINE CUT: {m.group(1)}"); bad += 1
        thr = set()
        if any("== through the verified compiler" in l for l in lines):
            k = [j for j, l in enumerate(lines) if "== through the verified compiler" in l][0] + 1
            while k < len(lines) and not lines[k].startswith("=="):
                if "by the verified compiler" in lines[k]: thr.add(lines[k].split()[0])
                k += 1
        if not ends:
            print("NO END THEOREMS IN THE GATE'S LOG"); bad += 1
        for prog in sorted(thr - set(ends)):
            print(f"NO END THEOREM PRINTED: {prog}"); bad += 1
        for prog, names in sorted(ends.items()):
            for n in names:
                if n not in w["assumption"]:
                    print(f"NOT ON THE LIST: assumption {n} (the end theorem of {prog})"); bad += 1
        if ends:
            print(f"end theorems: {len(ends)} programs, each within the list" if not bad else f"end theorems: {len(ends)} programs")
    if bad:
        print(f"TRUST CHANGED: {bad} differences (Rocq-C-solution.md §13.9: the owner's decision)")
        return 1
    print("trust unchanged")
    return 0

if __name__ == "__main__":
    sys.exit(main())
