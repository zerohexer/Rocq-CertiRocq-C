#!/usr/bin/env python3
"""check_patch.py ROCQ_SRC: the facts ConvMemo.v assumes of the OCaml, checked on a patched Rocq tree (Rocq-C-solution.md
§12.R (2)).  Exit 0 when all hold.

  1. every cell literal carries identity 0: each record literal of [fconstr] (a { .. } with a [term] or [mark] field, or a
     copy { v with .. }) in kernel/cClosure.ml sets [fid = 0];
  2. the counter is the only place an identity is given: [.fid <-] appears once, in [uid], after the counter is
     incremented (so 0 is never given);
  3. [update] writes only the mark and the term, and the only other in-place write of a term is the lock of a cell under
     reduction ([zupdate]: [FLOCKED], written back with its reduct by [update] when the reduction ends);
  4. the table exists only for checked conversion: [ConvCache.create] is called only under [use_cache], the checked entry
     point passes [~use_cache:true], unification ([generic_conv]) passes [~use_cache:false], and the syntactic
     pre-check registered on CClosure runs with [cnv_cache = None];
  5. a hit is answered without touching the universe state: the [Some true] branch returns [cuniv] as given."""
import re, sys

src = sys.argv[1] if len(sys.argv) > 1 else "."
cc = open(f"{src}/kernel/cClosure.ml").read()
cv = open(f"{src}/kernel/conversion.ml").read()

def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i): depth += 1; i += 2; continue
        if depth and s.startswith("*)", i): depth -= 1; i += 2; continue
        if not depth: out.append(s[i])
        i += 1
    return "".join(out)

cc0, cv0 = strip_comments(cc), strip_comments(cv)
fails = []
def check(ok, what):
    print(("ok    " if ok else "FAIL  ") + what)
    if not ok: fails.append(what)

# 1. every fconstr literal and copy sets fid = 0
lits = [m for m in re.finditer(r"\{([^{}]*)\}", cc0)]
cells = [m.group(1) for m in lits
         if re.search(r"(^|[;\s])(term|mark)\s*(=|;|$)", m.group(1)) or re.search(r"\bwith\b\s*(fid|term|mark)\b", m.group(1))]
bad = [c.strip()[:80] for c in cells if not re.search(r"\bfid\s*=\s*0\b", c)]
check(len(cells) > 20 and not bad, f"1. all {len(cells)} cell literals/copies set fid = 0" + ("" if not bad else f": missing in {bad[:3]}"))
nonzero = re.findall(r"\bfid\s*=\s*(?!0\b)\w+", cc0)
check(not nonzero, "1'. no literal sets a nonzero fid" + ("" if not nonzero else f": {nonzero[:3]}"))

# 2. the only write of an identity, in uid, after the counter
writes = re.findall(r"\.fid\s*<-", cc0)
uid = re.search(r"let uid v =\s*if v\.fid != 0 then v\.fid\s*else begin incr fid_counter; v\.fid <- !fid_counter; !fid_counter end", cc0)
check(len(writes) == 1 and uid is not None, f"2. one write of an identity ({len(writes)} found), in uid, after incr fid_counter")
incrs = re.findall(r"fid_counter\s*:=|incr fid_counter|decr fid_counter", cc0)
check(len(incrs) == 1, f"2'. the counter is only incremented, once, in uid ({len(incrs)} uses)")

# 3. update writes only mark and term
upd = re.search(r"let update v1 mark t =\s*v1\.mark <- mark; v1\.term <- t\s*\n", cc0)
check(upd is not None, "3. update v1 mark t writes v1.mark and v1.term only")
tw = re.findall(r"(\w+)\.term\s*<-\s*(\w+)", cc0)
check(sorted(tw) == sorted([("v1", "t"), ("m", "FLOCKED")]), f"3'. the in-place term writes are update's and zupdate's lock ({tw})")

# 4. the table only for checked conversion
check(re.search(r"let cache = if use_cache then ConvCache\.create \(\) else None in", cv0) is not None,
      "4. the table is created only under use_cache")
check(len(re.findall(r"ConvCache\.create", cv0)) == 1, "4'. ConvCache.create appears once in conversion.ml")
check(re.search(r"clos_gen_conv ~typed ~use_cache:true", cv0) is not None, "4''. checked conversion (gen_conv) uses the table")
check(re.search(r"let generic_conv[\s\S]{0,400}?clos_gen_conv ~typed:false ~use_cache:false", cv0) is not None,
      "4'''. unification (generic_conv) does not")
check(re.search(r"err_ret = box; cnv_cache = None \}", cv0) is not None, "4''''. the pre-check registered on CClosure runs without the table")
calls = re.findall(r"clos_gen_conv ~typed\S* ~use_cache:\w+", cv0)
allc = re.findall(r"clos_gen_conv ~typed", cv0)
check(len(calls) == len(allc), f"4v. every call of clos_gen_conv says whether it uses the table ({len(calls)}/{len(allc)})")

# 5. a hit returns the universe state unchanged; a miss records the comparison's own outcome
check(re.search(r"\| Some true -> cuniv\s*\| Some false -> raise NotConvertible", cv0) is not None,
      "5. a hit returns cuniv as given, or raises NotConvertible")

print("check_patch: " + ("all hold" if not fails else f"{len(fails)} FAIL"))
sys.exit(1 if fails else 0)
