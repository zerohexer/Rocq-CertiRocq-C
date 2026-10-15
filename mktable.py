#!/usr/bin/env python3
"""mktable.py TABLE.txt : the lines of table.sh (dbg/table_<tag>.txt) as one Markdown table, one row per problem.

Columns: the C++ reference; the same C++ with 8-byte cells (where there is such a file); the C++ written the way the
fast Rocq version is (where there is one); the corpus program with rebuilt pairs removed; the fastest program written
by the guideline; and that last one (or, where there is none, the corpus program) divided by the C++ reference."""
import sys
path = sys.argv[1]; LW = 76
WHAT = {
 'CF455A': 'two loops over 5 million cells', 'CF380C': 'segment tree, 100 000 queries', 'CF1100F': 'table of bases, 500 000 queries',
 'CF868F': 'divide and conquer with a moving window', 'CF631E': 'hull of lines, binary search', 'CF833B': 'segment tree, add and maximum on ranges',
 'CF17E': 'palindromes of 2 million letters', 'CF20C': 'shortest paths with a heap', 'CF1039D': 'greedy on a tree, divide and conquer',
 'CF813F': 'offline: sort, segment tree, union-find with undo', 'CF235C': 'suffix automaton', 'CF1172F': 'segment tree of sorted arrays',
 'CF432D': 'prefix function of 2 million letters', 'CF453B': 'table over sets of primes', 'CF622F': 'modular arithmetic, 1 million terms',
 'CF61E': 'tree of sums (binary indexed), used twice', 'CF385C': 'sieve up to 10 million', 'CF1167C': 'union-find',
 'CF163A': 'table of 25 million cells, two rows kept', 'CF460C': 'binary search on the answer', 'CF35C': 'walk over a 2000 x 2000 grid with a queue',
 'CF295B': 'all shortest ways, 500 vertices', 'CF339D': 'tree updated from the bottom, 2 million changes', 'CF547B': 'nearest smaller with a stack',
 'CF165E': 'table over sets of 22 bits', 'CF7D': 'two running hashes over 5 million letters'}
rows, order = {}, []
for l in open(path):
    l = l.rstrip('\n')
    if l.startswith('#LW '): LW = int(l.split()[1]); continue      # the width table.sh used for the first column
    if l.startswith('#') or len(l) <= LW: continue
    label = l[:LW].rstrip(); f = l[LW:].split()
    if len(f) < 4: continue
    p, best, ok = f[0], f[1], f[-1]
    if p not in rows: rows[p] = {'h': None, 'bad': False}; order.append(p)
    r = rows[p]
    if ok != 'ok': r['bad'] = True
    try: t = float(best)
    except ValueError: continue
    if label == 'C++': r['c'] = t
    elif label == 'C++ with 64-bit cells': r['c64'] = t
    elif label == 'C++ written the way the fast Rocq is': r['cw'] = t
    elif label == 'corpus text, exactly': r['f'] = t
    elif label.startswith('corpus text, pairs not rebuilt'): r['e'] = t
    elif label.startswith('by the guideline'):
        if r['h'] is None or t < r['h']: r['h'] = t
def ms(x): return '-' if x is None else ('%.1f' % x if x < 100 else '%.0f' % x)
print('| Problem | What the work is | C++ | C++, 8-byte cells | C++ written the same way | Rocq, corpus text | Rocq, by the guideline | best Rocq / C++ |')
print('|---|---|---|---|---|---|---|---|')
ratios, new = [], []
for p in order:
    r = rows[p]; c = r.get('c'); h = r['h']; e = r.get('e')
    best = h if h is not None else e
    ratio = best / c if (best is not None and c) else None
    if ratio is not None: ratios.append(ratio)
    print('| %s%s | %s | %s | %s | %s | %s | %s | %s |' % (p, ' (new)' if e is None else '', WHAT.get(p, ''), ms(c), ms(r.get('c64')), ms(r.get('cw')),
          ms(e) + ((' (%s with the exact text)' % ms(r['f'])) if (e is not None and r.get('f') and r['f'] > 1.3 * e) else ''),
          '**%s**' % ms(h) if h is not None else 'as the corpus text', ('**%.2f**' % ratio) if ratio is not None else '-'))
ratios.sort()
n = len(ratios)
print()
print('%d problems.  Best Rocq / C++: median %.2f; %d at or below 1.25; %d at or below 1.5; the largest %.2f.' % (
    n, ratios[n // 2], sum(1 for x in ratios if x <= 1.25), sum(1 for x in ratios if x <= 1.5), ratios[-1]))
if any(rows[p]['bad'] for p in order): print('AN ANSWER DIFFERS in: ' + ' '.join(p for p in order if rows[p]['bad']))
