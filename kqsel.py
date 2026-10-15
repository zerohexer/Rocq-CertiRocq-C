#!/usr/bin/env python3
"""kqsel.py RUN.txt BUILD.log [TH [MINN]] : what a measuring run says about a program's tests.

RUN.txt is the output of a program built with `kq_fast_ord _ PInstr` (lines `prof K MET TRUE WRONG`: test K was met
MET times, was true TRUE times, and a machine would have guessed it wrong WRONG times); BUILD.log is the log of that
build (its line `KQ-TESTS: K:kind:function ..` says what each test is).

Printed on the first line: the tests to make WITHOUT A JUMP, as a Rocq list -- those met at least MINN times
(1000) and guessed wrong at least TH per cent of the time (10), of the two kinds that can be:
    kind c   between two plain numbers: made a choice without a jump (kq_select);
    kind t   two arms that do the same steps on numbers that may differ (two calls of one loop, two writes of one
             cell): made ONE sequence of steps, each number that differs chosen without a jump (a step of the second
             kind, KQFast.v).
Then one line per test met.  A test of kind j (between different work) stays a jump whatever is measured: the arm
not taken is work not done."""
import sys, re
run, log = sys.argv[1], sys.argv[2]
TH = float(sys.argv[3]) if len(sys.argv) > 3 else 10.0
MINN = int(sys.argv[4]) if len(sys.argv) > 4 else 1000
kind, fn = {}, {}
for l in open(log, errors='replace'):
    if l.startswith('KQ-TESTS:'):
        for w in l.split()[1:]:
            k, c, f = w.split(':', 2); kind[int(k)] = c; fn[int(k)] = f
rows = []
for l in open(run, errors='replace'):
    f = l.split()
    if len(f) == 5 and f[0] == 'prof': rows.append(tuple(int(x) for x in f[1:]))
sel = [k for k, n, t, w in rows if kind.get(k) in ('c', 't') and n >= MINN and 100.0 * w >= TH * n]
print('[' + '; '.join(str(k) for k in sel) + ']')
WHAT = {'c': 'two plain numbers', 't': 'the same steps on other numbers', 'j': 'different work'}
for k, n, t, w in rows:
    c = kind.get(k, '?'); pw = 100.0 * w / n
    note = ''
    if k in sel: note = '  -> made without a jump' + (' (one sequence of steps)' if c == 't' else '')
    elif n >= MINN and pw >= TH and c == 'j': note = '  (a jump the data makes costly; it is what the data costs)'
    print('  test %-3d in %-14s between %-33s met %10d times, true %5.1f%%, guessed wrong %5.1f%%%s' % (k, fn.get(k, '?'), WHAT.get(c, c), n, 100.0 * t / n, pw, note))
