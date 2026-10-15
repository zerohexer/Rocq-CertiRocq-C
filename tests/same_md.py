#!/usr/bin/env python3
"""same_md.py results/same.txt : the result of tests/same.sh as one Markdown table, a row per loop."""
import sys
WHAT = {'sum': 'a loop that only looks', 'toss': 'a choice the machine cannot guess', 'heavy': 'the same, more work on each side',
        'rare': 'a choice nearly always the same way', 'clamp': 'read one block, write another', 'count': 'read, then read and write',
        'search': 'a choice at every step of a search', 'tree': 'a function that calls itself twice'}
ker = None; rows = {}; order = []
tail = []
for l in open(sys.argv[1]):
    l = l.rstrip('\n')
    if l.startswith('--- '): ker = l[4:].strip(); rows[ker] = []; order.append(ker); continue
    if l.startswith('ways that') or l.startswith('GATE'): tail.append(l); continue
    f = l.split()
    if ker is None or len(f) < 5 or l.startswith('the same loop'): continue
    name = f[0]
    if f[1] == 'rule': kind = 'rule ' + f[2]; rest = f[3:]
    else: kind = f[1]; rest = f[2:]
    rows[ker].append((name, kind, float(rest[0]), float(rest[1]), rest[2]))
print('| Loop | ways that must be the same | of them the very same C as the first | their times, ms | other ways (times the first) |')
print('|---|---|---|---|---|')
for k in order:
    same = [r for r in rows[k] if r[1] == 'same']
    oth = [r for r in rows[k] if r[1] != 'same']
    sameC = sum(1 for r in same if r[4] == 'A')
    ts = [r[2] for r in same]
    def fmt(x): return ('%.1f' % x) if x < 100 else ('%.0f' % x)
    o = '; '.join('`%s` (%s) %.2f' % (r[0], r[1] if r[1] != 'arith' else 'other arithmetic', r[3]) for r in oth) or '-'
    print('| %s: %s | %d | %d | %s - %s | %s |' % (k, WHAT.get(k, ''), len(same), sameC, fmt(min(ts)), fmt(max(ts)), o))
print()
for t in tail: print(t)
