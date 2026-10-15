#!/usr/bin/env python3
"""mkbig.py OUTDIR : the large inputs of the four timed problems, always the same (fixed seeds).

Per problem:  NAME.in    what the C++ reference reads
              NAME.mem   the same data as the memory a Rocq program starts with: <number of blocks>, then per block
                         <length> <cell> <cell> ..
              NAME.args  the numbers on the Rocq program's command line
and the memories of the hand-written versions that lay their data out differently (H_CF380C.mem, O_CF868F.mem)."""
import random, sys, os
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
only = set(sys.argv[2:])                              # problem names; none given = all
def want(*names): return not only or bool(only & set(names))
def w(name, text): open(os.path.join(out, name), 'w').write(text)
z = lambda k: ' '.join(['0'] * k)
def blk(vals): return '%d %s' % (len(vals), ' '.join(map(str, vals)))     # a block with these cells
def zero(k): return '%d z' % k                                             # a block of k zeros
def wmem(name, blocks): w(name + '.mem', '%d\n' % len(blocks) + '\n'.join(blocks) + '\n')

def first_four():

    # ---- CF380C: a string of 10^6 brackets, 10^5 queries
    random.seed(5)
    n, q = 1000000, 100000
    s = ''.join(random.choice('()') for _ in range(n))
    qs = []
    for _ in range(q):
        l = random.randint(1, n); r = random.randint(l, n); qs.append((l, r))
    w('CF380C.in', s + '\n%d\n' % q + ''.join('%d %d\n' % x for x in qs))
    brackets = '%d 0 %s' % (n + 1, ' '.join('1' if c == '(' else '0' for c in s))
    ql, qr, ans = '%d %s' % (q, ' '.join(str(l) for l, r in qs)), '%d %s' % (q, ' '.join(str(r) for l, r in qs)), '%d %s' % (q, z(q))
    tree = '%d %s' % (4 * n + 4, z(4 * n + 4))
    w('CF380C.mem', '\n'.join(['7', brackets, tree, tree, tree, ql, qr, ans]) + '\n')
    w('CF380C.args', '%d 22 %d\n' % (q, n))
    # the hand-written version that keeps a node's three numbers next to each other: the tree in ONE block
    w('H_CF380C.mem', '\n'.join(['7', brackets, '%d %s' % (12 * n + 16, z(12 * n + 16)), '4 0 0 0 0', '1 0', ql, qr, ans]) + '\n')
    w('H_CF380C.args', '%d 22 %d\n' % (q, n))

    random.seed(9)
    # ---- CF455A: 5 * 10^6 numbers in 1..100000
    n, M = 5000000, 100000
    a = [random.randint(1, M) for _ in range(n)]
    w('CF455A.in', '%d\n%s\n' % (n, ' '.join(map(str, a))))
    w('CF455A.mem', '3\n%d %s\n%d %s\n%d %s\n' % (n, ' '.join(map(str, a)), M + 2, z(M + 2), M + 2, z(M + 2)))
    w('CF455A.args', '%d %d %d\n' % (n, M, M))
    # ---- CF1100F: 5 * 10^5 values below 2^20, 5 * 10^5 queries
    n, q = 500000, 500000
    c = [random.randint(0, 1000000) for _ in range(n)]
    qs = []
    for _ in range(q):
        l = random.randint(1, n); r = random.randint(l, n); qs.append((l, r))
    w('CF1100F.in', '%d\n%s\n%d\n' % (n, ' '.join(map(str, c)), q) + ''.join('%d %d\n' % x for x in qs))
    rows = '%d %s' % ((n + 1) * 20, z((n + 1) * 20))
    w('CF1100F.mem', '7\n%d 0 %s\n20 %s\n' % (n + 1, ' '.join(map(str, c)), z(20)) + rows + '\n' + rows + '\n' +
      '%d %s\n%d %s\n%d %s\n' % (q, ' '.join(str(l) for l, r in qs), q, ' '.join(str(r) for l, r in qs), q, z(q)))
    w('CF1100F.args', '%d %d\n' % (n, q))
    # ---- CF868F: 10^5 values in 1..300, 20 parts
    n, k = 100000, 20
    a = [random.randint(1, 300) for _ in range(n)]
    w('CF868F.in', '%d %d\n%s\n' % (n, k, ' '.join(map(str, a))))
    head = '5\n%d 0 %s\n%d %s\n%d %s\n%d %s\n' % (n + 1, ' '.join(map(str, a)), n + 2, z(n + 2), n + 2, z(n + 2), n + 2, z(n + 2))
    w('CF868F.mem', head + '3 0 0 0\n')
    w('O_CF868F.mem', head + '5 0 0 0 0 0\n')      # the hand-written versions keep five numbers between scans
    w('CF868F.args', '%d 20 %d %d\n' % (k, n, n))

if want('CF380C', 'CF455A', 'CF1100F', 'CF868F', 'CF1100Fw'): first_four()
if want('CF1100Fw', 'CF1100F'): w('CF1100Fw.args', '500000 500000 20\n')   # the same problem, the row width given at run time

# ------------------------------------------------------------------ the rest of the corpus (2026-10-14)
if want('CF631E'):                                    # Product Sum: n numbers, |a| <= 10^6
    random.seed(11); n = 200000
    a = [random.randint(-1000000, 1000000) for _ in range(n)]
    w('CF631E.in', '%d\n%s\n' % (n, ' '.join(map(str, a))))
    wmem('CF631E', [blk([0] + a + [0]), zero(n + 2), zero(n + 3), zero(2)])
    w('CF631E.args', '%d\n' % n)

if want('CF833B'):                                    # The Bakery: n cakes, k boxes
    random.seed(12); n, k = 35000, 50
    a = [random.randint(1, n) for _ in range(n)]
    w('CF833B.in', '%d %d\n%s\n' % (n, k, ' '.join(map(str, a))))
    wmem('CF833B', [blk([0] + a + [0]), zero(n + 2), zero(n + 2), zero(4 * n + 8), zero(4 * n + 8), zero(n + 2), zero(n + 2)])
    w('CF833B.args', '%d %d 18 %d\n' % (k, n, n))

if want('CF17E'):                                     # Palisection: a string of 2 * 10^6 letters
    random.seed(13); n = 2000000
    s = ''.join(random.choice('ab') for _ in range(n))
    w('CF17E.in', '%d\n%s\n' % (n, s))
    wmem('CF17E', [blk([ord(c) - 97 for c in s]), zero(n + 2), zero(n + 2), zero(n + 2), zero(n + 2)])
    w('CF17E.args', '%d %d\n' % (n, n))

if want('CF622F'):                                    # The Sum of the k-th Powers
    n, k = 987654321, 1000000
    w('CF622F.in', '%d %d\n' % (n, k))
    wmem('CF622F', [zero(k + 4)] * 5)
    w('CF622F.args', '%d %d %d %d\n' % (k + 1, k + 2, n, k))

if want('CF432D'):                                    # Prefixes and Suffixes: a periodic string, so that it has borders
    random.seed(14); n = 2000000
    base = ''.join(random.choice('abc') for _ in range(997))
    s = (base * (n // 997 + 1))[:n]
    w('CF432D.in', s + '\n')
    wmem('CF432D', [blk([ord(c) - 96 for c in s]), zero(n + 2), zero(n + 2), zero(n + 2), zero(n + 2)])
    w('CF432D.args', '%d %d %d\n' % (n, n + 1, n))

if want('CF453B'):                                    # Little Pony and Harmony Chest
    random.seed(15); n = 100
    a = [random.randint(1, 30) for _ in range(n)]
    w('CF453B.in', '%d\n%s\n' % (n, ' '.join(map(str, a))))
    wmem('CF453B', [blk(a + [0]), zero(64), zero(20), zero((n + 1) * 131072)])
    w('CF453B.args', '131072 %d %d %d\n' % ((n + 1) * 131072, n, n))

if want('CF20C'):                                     # Dijkstra?: n vertices, m weighted edges
    random.seed(16); n, m = 100000, 100000
    es = [(random.randint(1, n), random.randint(1, n), random.randint(1, 1000000)) for _ in range(m)]
    w('CF20C.in', '%d %d\n' % (n, m) + ''.join('%d %d %d\n' % e for e in es))
    wmem('CF20C', [blk([e[0] for e in es]), blk([e[1] for e in es]), blk([e[2] for e in es]), zero(n + 2), zero(2 * m + 4),
                   zero(2 * m + 4), zero(2 * m + 4), zero(n + 2), zero(n + 2), zero(2 * m + 4), zero(2 * m + 4), zero(2), zero(n + 2)])
    w('CF20C.args', '%d %d %d 20 %d\n' % (n, m, 2 * m, n))

if want('CF1039D'):                                   # You Are Given a Tree: a tree with long paths
    random.seed(17); n = 100000
    par = [0, 0] + [i - random.randint(1, min(i - 1, 3)) for i in range(2, n + 1)]
    perm = list(range(1, n + 1)); random.shuffle(perm); lab = [0] + perm
    es = []
    for i in range(2, n + 1):
        u, v = lab[i], lab[par[i]]
        es.append((u, v) if random.random() < 0.5 else (v, u))
    random.shuffle(es)
    w('CF1039D.in', '%d\n' % n + ''.join('%d %d\n' % e for e in es))
    wmem('CF1039D', [blk([e[0] for e in es] + [0]), blk([e[1] for e in es] + [0]), zero(n + 2), zero(2 * n + 4), zero(2 * n + 4),
                     zero(n + 2), zero(n + 2), zero(n + 3), zero(n + 3), zero(n + 2), zero(2)])
    w('CF1039D.args', '%d %d %d\n' % (n, n, n))

if want('CF813F'):                                    # Bipartite Checking: edges switched on and off
    random.seed(18); n, q = 100000, 100000
    pool = []
    while len(pool) < 50000:
        x, y = random.randint(1, n), random.randint(1, n)
        if x != y: pool.append((min(x, y), max(x, y)))
    qs = [random.choice(pool) for _ in range(q)]
    w('CF813F.in', '%d %d\n' % (n, q) + ''.join('%d %d\n' % e for e in qs))
    R = 3600000
    wmem('CF813F', [blk([0] + [e[0] for e in qs] + [0]), blk([0] + [e[1] for e in qs] + [0]), zero(q + 2), zero(q + 2), zero(q + 2),
                    zero(4 * q + 8), zero(R), zero(R), zero(R), zero(4), zero(n + 2), zero(n + 2), zero(n + 2), zero(n + 2),
                    zero(n + 2), zero(q + 2)])
    w('CF813F.args', '%d %d %d %d\n' % (q, n, q, n))

if want('CF235C'):                                    # Cyclical Quest: a text and 20000 short patterns
    random.seed(19); n, q = 200000, 20000
    s = ''.join(random.choice('abc') for _ in range(n))
    xs = []
    for t in range(q):
        m = random.randint(1, 19)
        if t % 2 == 0:
            i = random.randint(0, n - m); x = s[i:i + m]; r = random.randint(0, m - 1); x = x[r:] + x[:r]
        else:
            x = ''.join(random.choice('abc') for _ in range(m))
        xs.append(x)
    w('CF235C.in', s + '\n%d\n' % q + ''.join(x + '\n' for x in xs))
    offs, tot = [], 0
    for x in xs: offs.append(tot); tot += len(x)
    wmem('CF235C', [blk([ord(c) - 97 for c in s]), zero((2 * n + 2) * 26), zero(2 * n + 3), zero(2 * n + 3), zero(2 * n + 3), zero(2),
                    zero(n + 3), zero(2 * n + 3), blk([ord(c) - 97 for x in xs for c in x]), blk(offs), blk([len(x) for x in xs]),
                    zero(2 * n + 3), zero(q + 1)])
    w('CF235C.args', '%d %d %d %d\n' % (n, 2 * n + 2, q, 2 * max(len(x) for x in xs)))
    # the hand-written version that keeps one record of 30 cells per state
    wmem('H_CF235C', [blk([ord(c) - 97 for c in s]), zero((2 * n + 3) * 30), zero(1), zero(1), zero(1), zero(2),
                      zero(n + 3), zero(2 * n + 3), blk([ord(c) - 97 for x in xs for c in x]), blk(offs), blk([len(x) for x in xs]),
                      zero(1), zero(q + 1)])

if want('CF1172F'):                                   # Nauuo and Bug
    random.seed(20); n, q = 200000, 200000
    p = random.randint(400000000, 1000000000)
    a = [random.randint(-1000000000, 1000000000) for _ in range(n)]
    qs = []
    for _ in range(q):
        l = random.randint(1, n); r = random.randint(l, n); qs.append((l, r))
    w('CF1172F.in', '%d %d %d\n%s\n' % (n, q, p, ' '.join(map(str, a))) + ''.join('%d %d\n' % x for x in qs))
    wmem('CF1172F', [blk([0] + a + [0]), zero(4 * n + 8), zero(4 * n + 8), zero(5500000), zero(2),
                     blk([x[0] for x in qs]), blk([x[1] for x in qs]), zero(q + 1)])
    w('CF1172F.args', '%d %d 20 %d %d\n' % (n, q, n, p))

# ------------------------------------------------------------------ new problems, written by the guideline from the start (2026-10-14)
if want('CF61E'):                                     # Enemy is weak: a permutation of 1 .. n
    random.seed(21); n = 1000000
    a = list(range(1, n + 1)); random.shuffle(a)
    w('CF61E.in', '%d\n%s\n' % (n, ' '.join(map(str, a))))
    wmem('CF61E', [blk([0] + a + [0]), zero(n + 2), zero(n + 2)])
    w('CF61E.args', '%d\n' % n)

if want('CF385C'):                                    # Bear and Prime Numbers: numbers up to 10^7, queries up to 2 * 10^9
    random.seed(22); n, q, MAX = 1000000, 50000, 10000000
    x = [random.randint(2, MAX) for _ in range(n)]
    qs = []
    for _ in range(q):
        l = random.randint(2, MAX); r = l + random.randint(0, 1999999990 - MAX); qs.append((l, r))
    w('CF385C.in', '%d\n%s\n%d\n' % (n, ' '.join(map(str, x)), q) + ''.join('%d %d\n' % t for t in qs))
    wmem('CF385C', [blk(x), zero(MAX + 2), zero(MAX + 2), blk([t[0] for t in qs]), blk([t[1] for t in qs]), zero(q + 1)])
    w('CF385C.args', '%d %d %d\n' % (n, q, MAX))

if want('CF1167C'):                                   # News Distribution: groups of users
    random.seed(23); n, m = 500000, 100000
    groups = []
    for _ in range(m):
        k = random.randint(0, 10)
        groups.append(random.sample(range(1, n + 1), k))
    flat = [u for g in groups for u in g]; starts = [0]
    for g in groups: starts.append(starts[-1] + len(g))
    w('CF1167C.in', '%d %d\n' % (n, m) + ''.join('%d %s\n' % (len(g), ' '.join(map(str, g))) for g in groups))
    wmem('CF1167C', [blk(flat + [0]), blk(starts), zero(n + 2), zero(n + 2), zero(n + 2)])
    w('CF1167C.args', '%d %d %d\n' % (n, m, len(flat) + 1))

if want('CF163A'):                                    # Substring and Subsequence: two strings of 5000 letters
    random.seed(24); n = m = 5000
    s = ''.join(random.choice('abcd') for _ in range(n)); t = ''.join(random.choice('abcd') for _ in range(m))
    w('CF163A.in', '%s\n%s\n' % (s, t))
    wmem('CF163A', [blk([0] + [ord(c) for c in s] + [0]), blk([0] + [ord(c) for c in t] + [0]), zero(m + 2), zero(m + 2), zero(2)])
    w('CF163A.args', '%d %d %d %d\n' % (n, m + 1, n, m))

if want('CF460C'):                                    # Present (20 times the judge's largest input)
    random.seed(25); n, m, wd = 2000000, 2000000, 1000
    a = [random.randint(1, 1000) for _ in range(n)]
    w('CF460C.in', '%d %d %d\n%s\n' % (n, m, wd, ' '.join(map(str, a))))
    wmem('CF460C', [blk([0] + a + [0]), zero(n + 2), zero(2)])
    w('CF460C.args', '%d %d %d %d %d\n' % (n, n + 1, n, wd, m))

if want('CF35C'):                                     # Fire Again: a 2000 x 2000 forest, 10 fires
    random.seed(26); N = M = 2000; K = 10; wd = M + 2
    cells = set()
    while len(cells) < K: cells.add((random.randint(1, N), random.randint(1, M)))
    cells = sorted(cells)
    w('CF35C.in', '%d %d %d\n' % (N, M, K) + ''.join('%d %d\n' % c for c in cells))
    wmem('CF35C', [zero((N + 2) * wd), zero(N * M + 2), blk([r * wd + c for r, c in cells]), zero(4)])
    w('CF35C.args', '%d %d %d %d %d\n' % (N + 2, wd, K, N * M + 1, (N + 1) * wd))

if want('CF295B'):                                    # Greg and Graph: 500 vertices
    random.seed(27); n = 500
    d = [[0 if i == j else random.randint(1, 100000) for j in range(n)] for i in range(n)]
    x = list(range(1, n + 1)); random.shuffle(x)
    w('CF295B.in', '%d\n' % n + ''.join(' '.join(map(str, r)) + '\n' for r in d) + ' '.join(map(str, x)) + '\n')
    wmem('CF295B', [blk([v for r in d for v in r]), blk([v - 1 for v in x]), zero(n + 1), zero(n + 1)])
    w('CF295B.args', '%d %d\n' % (n, n + 1))

if want('CF339D'):                                    # Xenia and Bit Operations (2^20 numbers, 2 million changes)
    random.seed(28); n, m = 20, 2000000; N = 1 << n
    a = [random.randint(0, (1 << 30) - 1) for _ in range(N)]
    qs = [(random.randint(1, N), random.randint(0, (1 << 30) - 1)) for _ in range(m)]
    w('CF339D.in', '%d %d\n%s\n' % (n, m, ' '.join(map(str, a))) + ''.join('%d %d\n' % t for t in qs))
    wmem('CF339D', [blk([0] * N + a), blk([t[0] for t in qs]), blk([t[1] for t in qs]), zero(m + 1)])
    w('CF339D.args', '%d %d\n' % (m, N >> 1))

if want('CF547B'):                                    # Mike and Feet (10 times the judge's largest input)
    random.seed(29); n = 2000000
    a = [random.randint(1, 1000000000) for _ in range(n)]
    w('CF547B.in', '%d\n%s\n' % (n, ' '.join(map(str, a))))
    wmem('CF547B', [blk([0] + a + [0]), zero(n + 2), zero(n + 2), zero(n + 2), zero(n + 2)])
    w('CF547B.args', '%d %d\n' % (n, n + 1))

if want('CF165E'):                                    # Compatible Numbers: 10^6 numbers below 2^22
    random.seed(30); n, FULL = 1000000, 1 << 22
    a = [random.randint(1, 4000000) for _ in range(n)]
    w('CF165E.in', '%d\n%s\n' % (n, ' '.join(map(str, a))))
    wmem('CF165E', [blk(a), zero(FULL), zero(n + 1)])
    w('CF165E.args', '%d %d\n' % (n, FULL))

if want('CF7D'):                                      # Palindrome Degree: 5 million letters
    random.seed(31); n = 5000000
    s = 'a' * 2000000 + ''.join(random.choice('ab') for _ in range(n - 2000000))
    w('CF7D.in', s + '\n')
    wmem('CF7D', [blk([0] + [ord(c) for c in s] + [0]), zero(n + 2)])
    w('CF7D.args', '%d\n' % n)
