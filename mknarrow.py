#!/usr/bin/env python3
"""mknarrow.py SRC.mem DST.mem I1 I2 ..   (setup.sh, from narrow.tsv)

The memory of a program that keeps some of its blocks NARROW (KQRun.v: rd32 / upd32, cells of 4 bytes): the blocks
of SRC.mem as they are, then the section `n32 <k>` with a copy of wide blocks I1, I2, .. as narrow blocks 0, 1, ..
(the program reads and writes those copies; the wide originals stay as they are and are not used).  Every number
copied must fit in 32 bits (signed): otherwise this stops."""
import sys
src, dst, idx = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3:]]
lines = open(src).read().split('\n')
nb = int(lines[0]); blocks = lines[1:1 + nb]
assert len(blocks) == nb, 'a block line is missing'
out = [str(nb)] + blocks + ['n32 %d' % len(idx)]
for i in idx:
    f = blocks[i].split()
    n = int(f[0])
    if len(f) == 2 and f[1] == 'z': out.append(blocks[i]); continue
    assert len(f) == n + 1, 'block %d: %d cells announced, %d there' % (i, n, len(f) - 1)
    for v in f[1:]:
        x = int(v)
        if not (-2**31 <= x < 2**31): sys.exit('mknarrow: block %d holds %d, which does not fit in 32 bits' % (i, x))
    out.append(blocks[i])
open(dst, 'w').write('\n'.join(out) + '\n')
