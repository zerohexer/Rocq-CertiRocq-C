#!/usr/bin/env python3
"""p_prep.py BODY EXT OUT_BODY OUT_EXT   (hw/build_proved.sh)

Makes a program of hw/ (written for the kit route) readable by the proved route's translator, changing nothing in its text
that it can read already:
  - `Axiom NAME : int -> .. -> mem -> mem.` (or `.. -> int`) listed in hw/NAME.ext (`ROCQNAME CNAME`) becomes a definition
    that calls the program's own routine by its number (hw/User.v): hw_user / hw_userf; OUT_EXT lists the numbers
    (`NUMBER CNAME ARGUMENTS KIND`, the numbering is the order of EXT, the same for every program of a kernel);
  - `Definition main : int := let kq_keep := .. in BODY.` with a body that is more than a call becomes a function of the
    numbers kq_arg k and of the starting memory kq_input 0, called by a main that the driver reads."""
import re, sys

body_f, ext_f, out_body, out_ext = sys.argv[1:5]
text = open(body_f).read()
ext = []
try:
    for line in open(ext_f):
        line = line.split("#")[0].split()
        if len(line) >= 2:
            ext.append((line[0], line[1]))
except FileNotFoundError:
    pass
num = {r: i for i, (r, c) in enumerate(ext)}
cname = {r: c for r, c in ext}

ext_lines = []
for r, c in ext:
    m = re.search(r"Axiom\s+" + re.escape(r) + r"\s*:\s*([^.]*?)\.", text, re.S)
    if m:
        ty = [t.strip() for t in m.group(1).split("->")]
        kind = "mem" if ty[-1] == "mem" else "pure"
        nargs = len([t for t in ty[:-1] if t != "mem"])
        k = num[r]
        ps = " ".join("a%d" % j for j in range(nargs))
        pad = " ".join(["0"] * (4 - nargs))
        call_args = " ".join(["a%d" % j for j in range(nargs)] + ([pad] if pad else []))
        if kind == "mem":
            new = "Definition %s %s(s : mem) : mem := hw_user %d %s s." % (r, ("(" + ps + " : int) ") if ps else "", k, call_args)
        else:
            new = "Definition %s %s: int := hw_userf %d %s." % (r, ("(" + ps + " : int) ") if ps else "", k, call_args)
        text = text[:m.start()] + new + text[m.end():]
    ext_lines.append("%d %s %d %s" % (num[r], c, nargs if m else 0, kind if m else "mem"))
open(out_ext, "w").write("\n".join(ext_lines) + ("\n" if ext_lines else ""))

m = re.search(r"Definition main : int :=\s*let kq_keep :=[^\n]*\n?(.*)\.\s*$", text, re.S)
if m:
    b = m.group(1)
    if re.search(r"\blet\b|\bif\b|\bmatch\b", b):
        args = sorted({int(x) for x in re.findall(r"kq_arg\s+(\d+)", b)})
        b2 = re.sub(r"\(?\s*kq_arg\s+(\d+)\s*\)?", lambda mm: " arg%s " % mm.group(1), b)
        b2 = re.sub(r"\(?\s*kq_input\s+0\s*\)?", " s_in ", b2)
        ps = "".join("(arg%d : int) " % a for a in args)
        head = "Definition kqp_main %s(s_in : mem) : int :=\n%s.\n\n" % (ps, b2.strip())
        call = "kqp_main " + " ".join("(kq_arg %d)" % a for a in args) + (" " if args else "") + "(kq_input 0)"
        newmain = ("Definition main : int :=\n  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in\n  %s.\n" % call)
        text = text[:m.start()] + head + newmain
open(out_body, "w").write(text)
