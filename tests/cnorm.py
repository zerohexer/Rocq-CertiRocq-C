#!/usr/bin/env python3
"""cnorm.py FILE.c PROGRAM : the C of a program with what is only a NAME taken out, so that two programs that are the
same C up to names compare equal: the program's own name, and the numbers the compiler puts at the end of every name
it makes (`f_case_known_202`, `$k3_245`) -- each such name becomes its base and the order of its first appearance."""
import sys, re
s = open(sys.argv[1]).read().replace(sys.argv[2], 'PROG').replace(sys.argv[2].upper(), 'PROG')
seen = {}
def r(m):
    w = m.group(0)
    if w not in seen: seen[w] = '%s_#%d' % (m.group(1), len(seen))
    return seen[w]
sys.stdout.write(re.sub(r'([A-Za-z_$][A-Za-z_$]*(?:[0-9]+[A-Za-z_$]+)*)_([0-9]+)\b', r, s))
