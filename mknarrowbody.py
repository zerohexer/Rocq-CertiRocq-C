#!/usr/bin/env python3
"""mknarrowbody.py SRC.body DST.body NAME1 NAME2 ..  : the program with the blocks NAME1, NAME2, .. (Local Notations
of block numbers) made NARROW: every `rd NAME` / `upd NAME` becomes `rd32 NAME` / `upd32 NAME`, and NAMEk is narrow
block k-1 (mknarrow.py puts the copies there).  Nothing else in the text changes; a block number that reaches `rd` /
`upd` in any other way stops this."""
import sys, re
src, dst, names = sys.argv[1], sys.argv[2], sys.argv[3:]
s = open(src).read()
for k, nm in enumerate(names):
    pat = re.compile(r'(Local Notation %s := )(\d+)(\.)' % re.escape(nm))
    assert len(pat.findall(s)) == 1, 'no notation for ' + nm
    s = pat.sub(lambda m: m.group(1) + str(k) + m.group(3) + '   (* narrow *)', s)
    s = re.sub(r'\brd\s+%s\b' % re.escape(nm), 'rd32 ' + nm, s)
    s = re.sub(r'\bupd\s+%s\b' % re.escape(nm), 'upd32 ' + nm, s)
# every remaining wide access must name a block that stayed wide
wide = set(re.findall(r'Local Notation (\w+) := \d+\.(?!   \(\* narrow)', s))
for m in re.finditer(r'\b(rd|upd)\s+(\S+)', s):
    if m.group(2) not in wide: sys.exit('mknarrowbody: `%s %s` names no wide block' % (m.group(1), m.group(2)))
head = '(* %s WITH NARROW BLOCKS (4 bytes a cell; KQRun.v: rd32, upd32): %s; written by mknarrowbody.py from %s *)\n' % (
    dst.split('/')[-1].replace('.body', ''), ', '.join(names), src.split('/')[-1])
open(dst, 'w').write(head + s)
