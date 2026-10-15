#!/usr/bin/env python3
"""kq_post3.py IN.c OUT.c [options]

Clean-ups of the C that CertiRocq generates.  Nothing here changes what a function computes or in which order: lines of
exact shapes are removed or moved into the branch that needs them, one statement that recomputes a value the function
was given is added, and functions are marked for the C compiler.  A shape this tool does not know makes it STOP
(exit 1) rather than guess.

 ROOTS      (default; --keep-roots turns it off; --nogc removes them all, for linking with kq_nogc.c)
     Before a call the generated code saves every variable that is still needed afterwards into the function's frame,
     where the collector can find it, and reloads it after: the collector MOVES what a variable points to.  A machine
     integer, a boolean or the memory token points to nothing, so saving it is wasted work -- most of what a loop over
     the memory does per round.  A whole-program pass finds the variables that can only ever hold such values (the
     result of an integer operation, of a read of the memory, a constant, a parameter that every caller gives such a
     value, ..; anything loaded from a built value, or of an unknown origin, counts as a pointer) and removes their
     saves and reloads.  A function left with nothing to save no longer links a frame at all, and the C compiler can
     turn its last call into a jump.  The collector itself is untouched and still sees every pointer.

 SHAPE      --shape=inplace (default) | split | none
     A function that begins by looking at one of its parameters (every `match` and `if` of the program becomes one):
       * the check for free space made on entry is moved into the cases that build something, and a case that builds
         nothing no longer writes the allocation pointer back before every call;
       * RECOMPUTE: when every caller computes that parameter the same way from the other arguments it passes
         (`f (fuel' =? 0) .. fuel' ..` -- every loop of the program), the function computes it again itself on entry.
         The value is the same; but the C compiler now sees the loop's "go on or stop" test next to the numbers it
         tests, instead of a boolean carried round the loop as a number.
       * MERGE: when two or more cases end by calling the same function (the `then` and the `else` of an `if` that both
         go round the loop, with different numbers), each case only puts its numbers into variables and ONE call is
         made after the cases.  A loop then has one place where it goes round, and the C compiler can turn a choice
         between two numbers into a conditional move instead of a jump it cannot predict.
     split: instead, cut the function into one function per case (kept for comparison).

 INLINE     the pieces of ONE loop of the program (the cases of its `if`s: a cycle of calls) are written out into the
     function where the loop is entered -- a loop becomes one C function whatever the C compiler's own size limits say.
     --loops=noinline keeps every loop a function of its own; --loops=free (default) leaves that to the C compiler.
     --linkage=static (default) | extern.

 TESTS      (default; --keep-tests turns it off)  "is it a pointer?" tests with one possible answer are replaced by it.

 DEAD       a function that nothing reaches from `body` is not written out (and takes no part in ROOTS: its parameters
     would count as "anything").

 FLAT       the report ends with what is left that a program of the fast fragment does not have: values built (pairs,
     closures) and how many of them inside a loop, closures built, calls through a closure.  A program with no
     closure and nothing built inside a loop is FLAT: its loops never touch the collector.  With --flat the tool
     exits with status 3 (after writing the output) when the program is not.
"""
import re, sys

args = sys.argv[1:]
opts = {}
for a in [a for a in args if a.startswith('--')]:
    k, _, v = a[2:].partition('='); opts[k] = v or True
files = [a for a in args if not a.startswith('--')]
KNOWN = {'nogc', 'keep-roots', 'shape', 'linkage', 'loops', 'keep-tests', 'no-recompute', 'no-sink', 'no-inline-attrs', 'no-merge', 'flat', 'keep-dead'}
if set(opts) - KNOWN or len(files) != 2: sys.exit(__doc__)
NOGC, KEEP_ROOTS, KEEP_TESTS = 'nogc' in opts, 'keep-roots' in opts, 'keep-tests' in opts
SHAPE, LINKAGE, LOOPS = opts.get('shape', 'inplace'), opts.get('linkage', 'static'), opts.get('loops', 'free')
RECOMPUTE, SINK, MERGE = 'no-recompute' not in opts, 'no-sink' not in opts, 'no-merge' not in opts
if SHAPE not in ('inplace', 'split', 'none') or LINKAGE not in ('static', 'extern') or LOOPS not in ('free', 'noinline'): sys.exit(__doc__)
def stop(msg): sys.exit('kq_post3: ' + msg)

# ------------------------------------------------------------------------------------------------ reading the file
class Fn:
    def __init__(self, name, header, body): self.name, self.header, self.body, self.attr = name, header, body, ''
    @property
    def params(self): return re.findall(r'value (\$\w+)', self.header)

src = open(files[0]).read().split('\n')
items = []                                   # in file order: a line of text, or a Fn
i, n = 0, len(src)
while i < n:
    m = re.match(r'^value (\w+)\(struct thread_info \*\$tinfo', src[i])
    if m:
        j = i; header = src[i]
        while not header.rstrip().endswith(')'):
            j += 1; header += ' ' + src[j].strip()
        if src[j + 1] != '{': stop('no body after ' + header[:60])
        k = j + 2
        while k < n and src[k] != '}': k += 1
        if k >= n: stop('unterminated function ' + m.group(1))
        items.append(Fn(m.group(1), header, src[j + 2:k])); i = k + 1
    else:
        items.append(src[i]); i += 1
fns = [x for x in items if isinstance(x, Fn)]
byname = {f.name: f for f in fns}
if 'body' not in byname: stop('no `body`')

def statements(lines):
    """the lines of a function as statements (a call is printed on several lines)"""
    cur = ''
    for l in lines:
        t = l.strip()
        if not t: continue
        cur = (cur + ' ' + t).strip()
        if t[-1] in ';{}:': yield cur; cur = ''
    if cur: stop('a statement without an end: ' + cur[:80])
def flat(lines): return '\n'.join(statements(lines))      # one statement per line: a call and its function on ONE line
def count_uses(name, text):
    """(every mention, direct calls) of a function's name in statements"""
    return (len(re.findall(r'(?<![\w$])' + re.escape(name) + r'(?!\w)', text)), len(re.findall(r'\)\) ' + re.escape(name) + r'\)', text)))

RX_CALL = re.compile(r'^(\$\w+) = \(\(value \(\*\)\(([^()]*)\)\) (\$?\w+)\) ?\(([^()]*)\);$')

# ------------------------------------------------------------------------------------------------ DEAD
def outside_names(x):                        # function names in a line outside the functions that is not a prototype
    if re.match(r'^(extern )?value \w+\(', x) or '_info_' in x.split('=')[0]: return set()
    return {g for g in re.findall(r'(?<![\w$])[A-Za-z_]\w*', x) if g in byname}
ndead = 0
if 'keep-dead' not in opts:
    mentions = {f.name: {g for g in re.findall(r'(?<![\w$])[A-Za-z_]\w*', flat(f.body)) if g in byname} for f in fns}
    live, todo = set(), ['body'] + sorted(g for x in items if isinstance(x, str) for g in outside_names(x))
    while todo:
        g = todo.pop()
        if g in live: continue
        live.add(g); todo += sorted(mentions[g] - live)
    ndead = len(fns) - len(live)
    if ndead:
        def gone(x):
            if isinstance(x, Fn): return x.name not in live
            m = re.match(r'^(extern )?value (\w+)\(', x)
            return bool(m) and m.group(2) in byname and m.group(2) not in live
        items = [x for x in items if not gone(x)]
        fns = [f for f in fns if f.name in live]; byname = {f.name: f for f in fns}

taken = set()                                # functions named other than as the function of a direct call
for f in fns:
    text = flat(f.body)
    for g in byname:
        tot, direct = count_uses(g, text)
        if tot != direct: taken.add(g)
for x in items:                              # .. or named outside the functions (a table of closures)
    if isinstance(x, str) and not re.match(r'^(extern )?value \w+\(', x) and '_info_' not in x.split('=')[0]:
        for g in byname:
            if re.search(r'(?<![\w$])' + re.escape(g) + r'(?!\w)', x): taken.add(g)

# ------------------------------------------------------------------------------------------------ ROOTS
RX_SAVE   = re.compile(r'^(\s*)\*\(root \+ (\d+)LL\) = (\$\w+);$')
RX_RELOAD = re.compile(r'^(\s*)(\$\w+) = \*\(root \+ (\d+)LL\);$')
RX_NEXT   = re.compile(r'^(\s*)frame\.next = root \+ (\d+)LL;$')
RX_LINK   = re.compile(r'^\s*\(\*\$tinfo\)\.fp = &frame;$')
RX_UNLINK = re.compile(r'^\s*\(\*\$tinfo\)\.fp = frame\.prev;$')
RX_ENTRY  = re.compile(r'^\s*(frame\.next = root;|frame\.root = root;|frame\.prev = \(\*\$tinfo\)\.fp;)$')
RX_DECL   = re.compile(r'^\s*(struct stack_frame frame;|value root\[\d+\];)$')
RX_HEAPCHK = re.compile(r'^(\s*)if \(!\(\d+LL <= \$limit - \$alloc\)\) \{$')

# operations whose result is never a pointer into the collector's memory
CMP_OPS = {'prim_int63_' + x for x in 'eqb ltb leb ltsb lesb'.split()}
INT_OPS = CMP_OPS | {'prim_int63_' + x for x in ('add sub mul div mod divs mods land lor lxor lsl lsr asr compare compares '
                                                 'head0 tail0 addmuldiv').split()}
KQ_INT = {'kq_rdb', 'kq_rd32', 'kq_rd_u', 'kq_rd32_u', 'kq_fits', 'kq_len', 'kq_len32', 'kq_arg', 'kq_input', 'kq_sum', 'kq_nat_int',
          'kq_in', 'kq_out', 'kq_select', 'kq_sel_lts', 'kq_sel_les', 'kq_sel_eq', 'kq_sel_ltu', 'kq_sel_leu', 'kq_prof',
          'kq_selectn', 'kq_sel_ges', 'kq_sel_gts', 'kq_sel_ne', 'kq_sel_geu', 'kq_sel_gtu'}    # numbers in, a number out

def pointer_analysis():
    """the set of (function, variable) that may hold a pointer into the collector's memory.

    What a variable may point to is a set of PLACES WHERE THE PROGRAM BUILDS A VALUE (one per `x = alloc + 1`), or the
    mark U for "anything": the result of a closure, of an operation this tool does not know, a parameter of a function
    used as a value.  What each field of a built value may point to is tracked per place, so that the number taken back
    out of a pair is known to be a number (and the pair inside a pair to be a pair).  An empty set means: never a
    pointer."""
    U = ('U',)
    pts, fld, ret = {}, {}, {}                              # (fn, var) -> set; (site, field) -> set; fn -> set
    cons = []                                               # constraints, re-run until nothing changes
    def P(fn, v): return pts.setdefault((fn, v), set())
    for f in fns:
        fn = f.name; ret.setdefault(fn, set())
        for st in statements(f.body):
            m = RX_CALL.match(st)
            if m:
                lhs, callee, a = m.group(1), m.group(3), [x.strip() for x in m.group(4).split(',')]
                if callee in byname:
                    if a[0] != '$tinfo': stop('a call without the thread record: ' + st[:80])
                    ps = byname[callee].params
                    cons.append(('res', fn, lhs, callee))
                    if len(ps) != len(a) - 1:
                        for q in ps: P(callee, q).add(U)
                    else:
                        for q, x in zip(ps, a[1:]):
                            if x.startswith('$'): cons.append(('copy', callee, q, fn, x))
                            else: P(callee, q).add(U)
                elif callee in INT_OPS or callee in KQ_INT or callee.startswith('kq_hw_'): pass   # hw/kq_hw.h: numbers in, a number out
                elif callee in ('kq_updb', 'kq_upd32', 'kq_upd_u', 'kq_upd32_u'): cons.append(('copy', fn, lhs, fn, a[3]))
                else: P(fn, lhs).add(U)                     # a closure, or an operation not listed above
                continue
            m = re.match(r'^\*\(\(value \*\) (\$\w+) \+ (-?\d+)LL\) = (.*);$', st)
            if m:                                           # a field of a value being built
                x, k, rhs = m.group(1), int(m.group(2)), m.group(3)
                if k >= 0 and rhs.startswith('$'): cons.append(('store', fn, x, k, rhs))
                elif not (re.fullmatch(r'\d+LLU?', rhs) or rhs in byname or rhs.startswith('$')): stop('a store of an unknown shape: ' + st[:80])
                continue
            m = re.match(r'^(\$\w+) = (.*);$', st)
            if m:
                lhs, rhs = m.group(1), m.group(2)
                if lhs in ('$alloc', '$limit', '$args'): continue
                ml = re.fullmatch(r'\*\(\(value \*\) (\$\w+) \+ (\d+)LL\)', rhs)
                if re.fullmatch(r'\d+LLU?', rhs) or re.fullmatch(r'\*\(root \+ \d+LL\)', rhs): pass   # a constant; a reload
                elif re.fullmatch(r'\(value\) \(\$alloc \+ 1LL\)', rhs): P(fn, lhs).add(('site', fn, lhs))
                elif ml: cons.append(('load', fn, lhs, ml.group(1), int(ml.group(2))))
                else: P(fn, lhs).add(U)                     # anything else
                continue
            m = re.match(r'^return (\$\w+);$', st)
            if m: cons.append(('ret', fn, m.group(1))); continue
            if re.match(r'^return\b', st): stop('a return of an unknown shape: ' + st[:80])
            if re.search(r'\$\w+\s*(\+\+|--|[-+*/%&|^]=|<<=|>>=)', st): stop('an assignment of an unknown shape: ' + st[:80])
    for g in taken:
        for q in byname[g].params: P(g, q).add(U)
    changed = True
    def into(dst, src):
        n = len(dst); dst |= src; return len(dst) != n
    while changed:
        changed = False
        for c in cons:
            if c[0] == 'copy': changed |= into(P(c[1], c[2]), P(c[3], c[4]))
            elif c[0] == 'res': changed |= into(P(c[1], c[2]), ret[c[3]])
            elif c[0] == 'ret': changed |= into(ret[c[1]], P(c[1], c[2]))
            elif c[0] == 'store':
                _, fn, x, k, v = c
                for o in list(P(fn, x)):
                    if o == U: stop('%s: a store into a value of unknown origin' % fn)
                    changed |= into(fld.setdefault((o, k), set()), P(fn, v))
            elif c[0] == 'load':
                _, fn, lhs, p_, k = c
                for o in list(P(fn, p_)):
                    if o == U: changed |= into(P(fn, lhs), {U})
                    else: changed |= into(P(fn, lhs), fld.get((o, k), set()))
    return {k for k, v in pts.items() if v}

def roots_pass(f, keep):
    """rewrite the save / reload groups of f, keeping the variables for which keep(v) holds; returns (#kept, #dropped)

    A group is:   saves (slots n-1 .. 0), `frame.next = root + n`, the link, THE CALL (or the collector), reloads, the unlink.
    Between the call and the reloads there can be a check for free space; it saves the call's own result in the next
    slots (n, n+1, ..), moves frame.next, calls the collector, reloads -- without linking the frame again."""
    L, out, i, kept, dropped = f.body, [], 0, 0, 0
    def bad(what, line=''): stop('%s: %s%s' % (f.name, what, (': ' + line.strip()) if line else ''))
    while i < len(L):
        if not (RX_SAVE.match(L[i]) or RX_NEXT.match(L[i])):
            if RX_RELOAD.match(L[i]) or RX_LINK.match(L[i]) or RX_UNLINK.match(L[i]): bad('a frame line outside a save group', L[i])
            out.append(L[i]); i += 1; continue
        j, saves = i, []
        while RX_SAVE.match(L[j]):
            m = RX_SAVE.match(L[j]); saves.append((int(m.group(2)), m.group(3))); j += 1
        mn = RX_NEXT.match(L[j]); n = len(saves)
        if not mn or int(mn.group(2)) != n or not RX_LINK.match(L[j + 1]): bad('a save group of an unknown shape', L[j])
        if sorted(k for k, _ in saves) != list(range(n)) or len({v for _, v in saves}) != n: bad('save slots')
        ind = mn.group(1)
        order = [v for _, v in saves if keep(v)]            # in the order written (highest slot first)
        new = {v: len(order) - 1 - t for t, v in enumerate(order)}; m_ = len(order)
        kept += m_; dropped += n - m_
        for v in order: out.append('%s*(root + %dLL) = %s;' % (ind, new[v], v))
        if m_: out.append('%sframe.next = root + %dLL;' % (ind, m_)); out.append(L[j + 1])
        k, seen = j + 2, set()
        inner_open, isaves, inew, ilinked, iseen, iind = False, [], {}, False, set(), ''
        while k < len(L) and not RX_UNLINK.match(L[k]):
            l = L[k]; ms, mr, mx, mh = RX_SAVE.match(l), RX_RELOAD.match(l), RX_NEXT.match(l), RX_HEAPCHK.match(l)
            if mh:
                if inner_open: bad('a check for free space inside another', l)
                inner_open, isaves, inew, ilinked, iseen, iind = True, [], {}, False, set(), mh.group(1)
                out.append(l)
            elif ms:
                if not inner_open or int(ms.group(2)) != n + len(isaves): bad('a save in the middle of a group', l)
                v = ms.group(3); isaves.append((int(ms.group(2)), v))
                if keep(v): inew[v] = m_ + len(inew); out.append('%s*(root + %dLL) = %s;' % (ms.group(1), inew[v], v)); kept += 1
                else: dropped += 1
            elif mx:
                if not inner_open or int(mx.group(2)) != n + len(isaves): bad('frame.next in the middle of a group', l)
                if inew:
                    out.append('%sframe.next = root + %dLL;' % (mx.group(1), m_ + len(inew)))
                    if not m_: out.append('%s(*$tinfo).fp = &frame;' % mx.group(1)); ilinked = True
            elif mr:
                idx, v = int(mr.group(3)), mr.group(2)
                if idx >= n:
                    if not inner_open or (idx, v) not in isaves or v in iseen: bad('a reload that matches no save', l)
                    iseen.add(v)
                    if v in inew: out.append('%s%s = *(root + %dLL);' % (mr.group(1), v, inew[v]))
                else:
                    if inner_open or (idx, v) not in saves or v in seen: bad('a reload that matches no save', l)
                    seen.add(v)
                    if v in new: out.append('%s%s = *(root + %dLL);' % (mr.group(1), v, new[v]))
            elif inner_open and l == iind + '}':
                if iseen != {v for _, v in isaves}: bad('a check for free space that does not reload what it saved')
                if ilinked: out.append('%s  (*$tinfo).fp = frame.prev;' % iind)
                inner_open = False; out.append(l)
            else:
                if re.search(r'\broot\b|\bframe\b', l): bad('an unknown frame line', l)
                out.append(l)
            k += 1
        if k >= len(L) or inner_open or seen != {v for _, v in saves}: bad('a save group that is not closed')
        if m_: out.append(L[k])
        i = k + 1
    f.body = out
    return kept, dropped

rep = {'functions': len(fns)}
if ndead: rep['functions nothing reaches (not written)'] = ndead
if NOGC:
    removed = 0
    for f in fns:
        k, d = roots_pass(f, lambda v: False); removed += d
        f.body = [l for l in f.body if not RX_ENTRY.match(l)]
        left = [l for l in f.body if re.search(r'\broot\b|\bframe\b', l) and not RX_DECL.match(l)]
        if left: stop('%s: a line still mentions the frame: %s' % (f.name, left[0].strip()))
    rep['saves removed'] = removed
elif not KEEP_ROOTS:
    P = pointer_analysis(); kept = dropped = unframed = 0
    for f in fns:
        k, d = roots_pass(f, lambda v, fn=f.name: (fn, v) in P); kept += k; dropped += d
        if k == 0 and any(RX_ENTRY.match(l) for l in f.body):
            f.body = [l for l in f.body if not RX_ENTRY.match(l)]; unframed += 1
    rep['saves kept'] = kept; rep['saves removed'] = dropped; rep['functions without a frame'] = unframed

# ------------------------------------------------------------------------------------------------ SHAPE
RX_GC = re.compile(r'^  if \(!\(\d+LL <= \$limit - \$alloc\)\) \{$')
RX_ALLOCSTORE = re.compile(r'^\s*\(\*\$tinfo\)\.(alloc = \$alloc|limit = \$limit);$')
def builds(lines): return any(re.match(r'^\s*\$alloc = \$alloc \+ \d+LL;$', l) for l in lines)
def heap_check(pre):
    """(the prologue without its check for free space, the check's lines) -- the check is at most one block"""
    for a, l in enumerate(pre):
        if RX_GC.match(l):
            b = a + 1
            while pre[b] != '  }': b += 1
            return pre[:a] + pre[b + 1:], pre[a:b + 1]
    return pre, []
def no_stores(lines): return [l for l in lines if not RX_ALLOCSTORE.match(l)]
def quiet(lines):
    """code that builds nothing: no check for free space, no writing back of the allocation pointer"""
    rest, chk = heap_check(lines)
    return no_stores(rest)

def cases_of(f):
    """f as (prologue lines, the parameter looked at, [(side, label, case lines)]) when its body is one test of a
    parameter, else None"""
    L = f.body
    for t, l in enumerate(L):
        if re.match(r'^  if \((\(\$\w+ & 1\) == 0|[01])\) \{$', l): break
    else: return None
    m = re.match(r'^    switch \(\*\(\(value \*\) (\$\w+) \+ -1LL\) & 255LL\) \{$', L[t + 1] if t + 1 < len(L) else '')
    if not m: return None
    s = m.group(1)
    if s not in f.params or L[-1] != '  }': return None
    pre = L[:t]
    for l in pre:                                           # the prologue: declarations, the loads, the free-space check
        if l.startswith('  }') or l.startswith('    ') or RX_GC.match(l): continue
        if re.match(r'^  (struct stack_frame frame;|value root\[\d+\];|register (value \*?|_Bool )\$\w+;|\$alloc = \(\*\$tinfo\)\.alloc;|'
                    r'\$limit = \(\*\$tinfo\)\.limit;|\$args = \(\*\$tinfo\)\.args;|frame\.next = root;|frame\.root = root;|'
                    r'frame\.prev = \(\*\$tinfo\)\.fp;)$', l): continue
        return None
    try: e = L.index('  } else {', t)
    except ValueError: return None
    if L[e - 1] != '    }' or L[e + 1] != '    switch (%s >> 1LL) {' % s or L[-2] != '    }': return None
    cases = []
    for side, a, b in (('b', t + 2, e - 1), ('u', e + 2, len(L) - 2)):
        cur = None
        for l in L[a:b]:
            if not l.strip(): continue
            m = re.match(r'^      (case (\d+)|default):$', l)
            if m: cur = (side, m.group(2) if m.group(2) is not None else 'd', []); cases.append(cur); continue
            if cur is None or not l.startswith('        '): return None
            cur[2].append(l[6:])
    if not cases: return None
    for side, lab, body in cases:
        if body and body[-1] == '  break;': body.pop()
        if not body: return None                            # a case that runs on into the next one: left as it is
    return pre, s, cases

def recompute_plan():
    """for a function whose every caller computes the parameter it looks at as  CMP(x, y)  with x and y each another
    argument of the same call or a constant: the statement that computes it again from the function's own parameters"""
    defs, callsites = {}, {}                                # per function: var -> [right-hand sides]; callee -> [(caller, args)]
    for f in fns:
        d = {}
        for st in statements(f.body):
            m = re.match(r'^(\$\w+) = (.*);$', st)
            if m and not re.fullmatch(r'\*\(root \+ \d+LL\)', m.group(2)): d.setdefault(m.group(1), []).append(m.group(2))
            mc = RX_CALL.match(st)
            if mc and mc.group(3) in byname:
                callsites.setdefault(mc.group(3), []).append((f.name, [x.strip() for x in mc.group(4).split(',')][1:]))
        defs[f.name] = d
    plan = {}
    for f in fns:
        if f.name == 'body' or f.name in taken or f.name not in callsites: continue
        c = cases_of(f)
        if c is None: continue
        s = c[1]; ps = f.params; si = ps.index(s); choice = None
        for caller, a in callsites[f.name]:
            if len(a) != len(ps): choice = set(); break
            d = defs[caller].get(a[si], [])
            m = re.fullmatch(r'\(\(value \(\*\)\(value, value\)\) (\w+)\) ?\((\$\w+), (\$\w+)\)', d[0]) if len(d) == 1 else None
            if not m or m.group(1) not in CMP_OPS: choice = set(); break
            def descr(v):
                out = {('p', k) for k, x in enumerate(a) if x == v and k != si}
                dv = defs[caller].get(v, [])
                if len(dv) == 1 and re.fullmatch(r'\d+LLU?', dv[0]): out.add(('c', dv[0]))
                return out
            here = {(m.group(1), x, y) for x in descr(m.group(2)) for y in descr(m.group(3))}
            choice = here if choice is None else (choice & here)
            if not choice: break
        if choice:
            op, x, y = sorted(choice)[0]
            w = lambda t: ps[t[1]] if t[0] == 'p' else t[1]
            plan[f.name] = '  %s = ((value (*)(value, value)) %s)(%s, %s);' % (s, op, w(x), w(y))
    return plan

PRE_SHAPES = ('  $args = (*$tinfo).args;', '  (*$tinfo).alloc = $alloc;', '  (*$tinfo).limit = $limit;', '  /*skip*/;')
POST_SHAPES = ('  $alloc = (*$tinfo).alloc;', '  $limit = (*$tinfo).limit;', '  /*skip*/;', '  (*$tinfo).alloc = $alloc;', '  (*$tinfo).limit = $limit;')
def tail_call(body):
    """a case that ends  `y = F(tinfo, args); return y;`  (with the usual lines around the call and nothing saved for
    the collector) as (index where that ending starts, lines before the call, lines after it, F, its type, args)"""
    m = re.match(r'^  return (\$\w+);$', body[-1]) if body else None
    if not m: return None
    y, k = m.group(1), len(body) - 2
    post = []
    while k >= 0 and body[k] in POST_SHAPES: post.insert(0, body[k]); k -= 1
    e = k                                                   # the last line of the call
    while k >= 0 and not re.match(r'^  \$\w+ =', body[k]): k -= 1
    if k < 0 or not body[k].startswith('  %s =' % y): return None
    mc = RX_CALL.match(' '.join(l.strip() for l in body[k:e + 1]))
    if not mc or mc.group(3) not in byname: return None
    a = [x.strip() for x in mc.group(4).split(',')]
    if a[0] != '$tinfo': return None
    pre, k = [], k - 1
    while k >= 0 and body[k] in PRE_SHAPES: pre.insert(0, body[k]); k -= 1
    return k + 1, tuple(pre), tuple(post), mc.group(3), mc.group(2), a[1:]

def merge_tail_calls(cases):
    """(new cases, declarations, the lines of the one call after the cases) -- or (cases, [], []) when fewer than two
    cases end by calling the same function in the same way"""
    found = {}
    for t, (side, lab, body) in enumerate(cases):
        tc = tail_call(body)
        if tc: found.setdefault((tc[3], tc[4], tc[1], tc[2], len(tc[5])), []).append((t, tc))
    best = max(found.values(), key=len) if found else []
    if len(best) < 2: return cases, [], []
    _, (_, pre, post, callee, sig, a0) = best[0]
    n = len(a0); tmp = ['$kq_m%d' % (k + 1) for k in range(n)]
    new = list(cases)
    for t, (start, _, _, _, _, a) in best:
        side, lab, body = cases[t]
        new[t] = (side, lab, body[:start] + ['  %s = %s;' % (tmp[k], a[k]) for k in range(n)])
    decls = ['  register value %s;' % v for v in tmp + ['$kq_mr']]
    tail = list(pre) + ['  $kq_mr = ((value (*)(%s)) %s)(%s);' % (sig, callee, ', '.join(['$tinfo'] + tmp))] + list(post) + ['  return $kq_mr;']
    return new, decls, tail

def rebuild(pre, s, cases):
    out = list(pre) + ['  if ((%s & 1) == 0) {' % s, '    switch (*((value *) %s + -1LL) & 255LL) {' % s]
    for side in ('b', 'u'):
        if side == 'u': out += ['    }', '  } else {', '    switch (%s >> 1LL) {' % s]
        for sd, lab, body in cases:
            if sd != side: continue
            out.append('      default:' if lab == 'd' else '      case %s:' % lab)
            out += ['      ' + l for l in body] + ['        break;']
        out.append('      ')
    return out + ['    }', '  }']

protos, nrec, nsunk, nmerged = [], 0, 0, 0
pieces, parts = [], {}                       # the functions holding code after this step; original name -> pieces a call reaches
if SHAPE == 'inplace':
    plan = recompute_plan() if RECOMPUTE else {}
    for f in fns:
        pieces.append(f); parts[f.name] = [f]
        if f.name == 'body': continue
        c = cases_of(f)
        if c is None:
            if not builds(f.body): f.body = quiet(f.body)
            continue
        pre, s, cases = c
        if SINK:
            pre, chk = heap_check(pre)
            if chk or True:
                newcases = []
                for side, lab, body in cases:
                    if builds(body): body = chk + body
                    else: body = no_stores(body)
                    newcases.append((side, lab, body))
                cases = newcases; nsunk += bool(chk)
        elif not builds(f.body): pre = quiet(pre); cases = [(a, b, no_stores(x)) for a, b, x in cases]
        tail = []
        if MERGE:
            cases, decls, tail = merge_tail_calls(cases); pre = decls + pre; nmerged += bool(tail)
        if f.name in plan: pre = pre + [plan[f.name]]; nrec += 1
        f.body = rebuild(pre, s, cases) + tail
    rep['free-space checks moved into a case'] = nsunk; rep['tests recomputed on entry'] = nrec; rep['functions with their calls merged'] = nmerged
elif SHAPE == 'split':
    new_items, nsplit = [], 0
    for x in items:
        if not isinstance(x, Fn) or x.name == 'body':
            new_items.append(x)
            if isinstance(x, Fn): pieces.append(x); parts[x.name] = [x]
            continue
        f = x; c = cases_of(f)
        if c is None:
            if not builds(f.body): f.body = quiet(f.body)
            pieces.append(f); parts[f.name] = [f]; new_items.append(f); continue
        pre, s_, cases = c; nsplit += 1
        sig = f.header[len('value ' + f.name):]
        call = '(' + ', '.join(['$tinfo'] + f.params) + ')'
        disp = {'b': [], 'u': []}; parts[f.name] = []
        for side, lab, body in cases:
            name = '%s__%s%s' % (f.name, side, lab)
            lines = pre + body
            if not builds(lines): lines = quiet(lines)
            g = Fn(name, 'value ' + name + sig, lines)
            new_items.append(g); pieces.append(g); parts[f.name].append(g)
            protos.append('static value %s%s;' % (name, re.sub(r' \$\w+', '', sig).replace('struct thread_info *$tinfo', 'struct thread_info *')))
            disp[side].append('      %s return %s%s;' % ('default:' if lab == 'd' else 'case %s:' % lab, name, call))
        def sw(expr, rows): return ['    switch (%s) {' % expr] + rows + ['    }']
        if disp['b'] and disp['u']:
            d = ['  if ((%s & 1) == 0) {' % s_] + sw('*((value *) %s + -1LL) & 255LL' % s_, disp['b']) + ['  } else {'] + sw('%s >> 1LL' % s_, disp['u']) + ['  }']
        elif disp['u']: d = [l[2:] for l in sw('%s >> 1LL' % s_, disp['u'])]
        else: d = [l[2:] for l in sw('*((value *) %s + -1LL) & 255LL' % s_, disp['b'])]
        f.body = d; f.attr = '__attribute__((always_inline)) '; f.dispatcher = True
        new_items.append(f)
    items = new_items; rep['functions cut by case'] = nsplit
else:
    for f in fns:
        pieces.append(f); parts[f.name] = [f]
        if f.name != 'body' and not builds(f.body): f.body = quiet(f.body)

# ------------------------------------------------------------------------------------------------ INLINE
if SHAPE != 'none' and 'no-inline-attrs' not in opts:
    idx = {id(g): t for t, g in enumerate(pieces)}
    sites = [[] for _ in pieces]                            # per piece: the pieces holding a call that reaches it, one per call
    succ = [set() for _ in pieces]
    for t, g in enumerate(pieces):
        text = flat(g.body)
        for name in parts:
            for _ in range(count_uses(name, text)[1]):
                for h in parts[name]: sites[idx[id(h)]].append(t); succ[t].add(idx[id(h)])
    # strongly connected components (Tarjan, without recursion): a component with a cycle is a LOOP of the program
    comp, low, num, onst, st, cnt, ncomp = [None] * len(pieces), {}, {}, set(), [], 0, 0
    for root in range(len(pieces)):
        if root in num: continue
        work = [(root, iter(sorted(succ[root])))]; num[root] = low[root] = cnt; cnt += 1; st.append(root); onst.add(root)
        while work:
            v, it = work[-1]
            for w in it:
                if w not in num:
                    num[w] = low[w] = cnt; cnt += 1; st.append(w); onst.add(w); work.append((w, iter(sorted(succ[w])))); break
                elif w in onst: low[v] = min(low[v], num[w])
            else:
                work.pop()
                if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == num[v]:
                    while True:
                        w = st.pop(); onst.discard(w); comp[w] = ncomp
                        if w == v: break
                    ncomp += 1
    size = {}
    for c in comp: size[c] = size.get(c, 0) + 1
    def cyclic(t): return size[comp[t]] > 1 or t in succ[t]
    ninl = nloops = 0
    for t, g in enumerate(pieces):
        if g.name == 'body' or g.name.split('__')[0] in taken: continue
        callers = sites[t]
        if len(callers) == 1 and (not cyclic(t) or comp[callers[0]] == comp[t]):
            g.attr = '__attribute__((always_inline)) '; ninl += 1        # one call, and no loop of its own: written out there
        elif cyclic(t) and (len(callers) >= 2 or any(comp[c] != comp[t] for c in callers)):
            nloops += 1                                     # where a loop is entered
            if LOOPS == 'noinline': g.attr = '__attribute__((noinline)) '
    rep['written out at their one call'] = ninl; rep['loops'] = nloops

# ------------------------------------------------------------------------------------------------ TESTS
def one_sided(lines):
    n, k, done = len(lines), 0, 0
    while k < n:
        m = re.match(r'^(\s*)if \(\(\$(\w+) & 1\) == 0\) \{$', lines[k])
        if m:
            ind, x = m.group(1), m.group(2)
            if k + 1 < n and lines[k + 1] == ind + '  switch (*((value *) $%s + -1LL) & 255LL) {' % x:
                e = k + 2
                while e < n and lines[e] != ind + '} else {': e += 1
                if e + 1 < n and lines[e + 1] == ind + '  switch ($%s >> 1LL) {' % x:
                    f = e + 2
                    while f < n and lines[f] != ind + '}': f += 1
                    boxed = [y for y in lines[k + 2:e - 1] if y.strip()]
                    unboxed = [y for y in lines[e + 2:f - 1] if y.strip()]
                    if lines[e - 1] == ind + '  }' and f < n and lines[f - 1] == ind + '  }':
                        if not boxed and unboxed: lines[k] = ind + 'if (0) {'; done += 1
                        elif not unboxed and boxed: lines[k] = ind + 'if (1) {'; done += 1
        k += 1
    return done
if not KEEP_TESTS:
    rep['one-sided tests'] = sum(one_sided(x.body) for x in items if isinstance(x, Fn))

# ------------------------------------------------------------------------------------------------ FLAT
final = [x for x in items if isinstance(x, Fn)]
fnames = {x.name for x in final}
calls = {x.name: {g for g in re.findall(r'(?<![\w$])[A-Za-z_]\w*', flat(x.body)) if g in fnames} for x in final}
def reach(g):                                # every function a call of g can lead to
    seen, todo = set(), list(calls[g])
    while todo:
        h = todo.pop()
        if h not in seen: seen.add(h); todo += list(calls[h] - seen)
    return seen
R = {g: reach(g) for g in fnames}
hot = set()                                  # the functions of a loop (a cycle of calls), and everything a loop calls
for g in fnames:
    if g in R[g]: hot |= {g} | R[g]
nbuilt = nhot = nclo = nclocall = 0; where, wherehot = [], []
for x in final:
    b = c = k = 0
    for st in statements(x.body):
        if re.match(r'^\$alloc = \$alloc \+ \d+LL;$', st): b += 1
        m = re.match(r'^\*\(\(value \*\) \$\w+ \+ -?\d+LL\) = (\w+);$', st)
        if m and m.group(1) in fnames: c += 1
        m = RX_CALL.match(st)
        if m and m.group(3).startswith('$'): k += 1
    nbuilt += b; nclo += c; nclocall += k
    if b and x.name in hot: nhot += b; wherehot.append(x.name)
    if c or k: where.append(x.name)
rep['values built'] = nbuilt; rep['of them inside a loop'] = nhot; rep['closures built'] = nclo; rep['calls through a closure'] = nclocall

# ------------------------------------------------------------------------------------------------ writing
out, proto_done = [], False
names = {x.name for x in items if isinstance(x, Fn)}
static = LINKAGE == 'static' or SHAPE == 'split'
for x in items:
    if isinstance(x, Fn):
        if not proto_done and protos: out += protos; proto_done = True
        if x.name == 'body': out.append(x.header)
        else: out.append(('static ' if static else '') + x.attr + x.header)
        out.append('{'); out += x.body; out.append('}')
    else:
        m = re.match(r'^(extern )?value (\w+)\(', x)
        if m and m.group(2) != 'body' and m.group(2) in names and static: x = 'static ' + x[len(m.group(1) or ''):]
        out.append(x)
open(files[1], 'w').write('\n'.join(out))
print('%s: %s' % (files[0].split('/')[-1], ', '.join('%d %s' % (v, k) for k, v in rep.items())))
if nclo or nclocall: print('NOT FLAT: closures are built or called in ' + ', '.join(where))
if nhot: print('NOT FLAT: a loop builds values in ' + ', '.join(wherehot))
if 'flat' in opts and (nclo or nclocall or nhot): sys.exit(3)
