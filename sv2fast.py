#!/usr/bin/env python3
"""sv2fast.py NAME.sv [OUTNAME] > OUTNAME.v

A plain-function surface program (Z, `rd` / `upd` on a memory of blocks) made ready for the fast native route.  The
program's own text is rewritten word for word as in sv2int.py (only the names of the arithmetic change).  Around it:

  * KQNat.v: a nat (the loop budget) is kept as one machine integer;
  * `CertiRocq Extract Inline [..]`: the program's NON-RECURSIVE definitions that are safe to write out at their uses.
    Writing a definition out moves the moment its arguments are computed from the call to the use.  With a memory that
    is written in place that is only right when an argument reads and writes no memory; so a definition is listed only
    if, at every one of its calls, each memory argument is a plain variable and every other argument is free of memory
    operations (and is plain arithmetic when the definition uses it more than once);
  * `main`: solve's arguments from the command line, its memory from the input file;
  * the compile command, with the settings measured to matter."""
import re, sys, os
ETA = '--eta' in sys.argv
if ETA: sys.argv.remove('--eta')
name = os.path.basename(sys.argv[1])[:-3]
out = sys.argv[2] if len(sys.argv) > 2 else name
s = open(sys.argv[1]).read()

def eta_pairs(t):
    """--eta : `(let p := E in ((fst p), (snd p)))` is E.  The surface files of the corpus were printed by a translator
    that takes a returned pair apart and builds it again; the rebuilt pair is equal to the pair (it is not the same
    text, so this IS a change of the program's text, the only one this tool makes)."""
    n = 0
    while True:
        m = re.search(r"\(let (kqp\d+) := \(", t)
        hit = None
        for m in re.finditer(r"\(let (kqp\d+) := \(", t):
            i = m.end() - 1; d = 0; j = i
            while j < len(t):
                if t[j] == '(': d += 1
                elif t[j] == ')':
                    d -= 1
                    if d == 0: break
                j += 1
            tail = ' in ((fst %s), (snd %s)))' % (m.group(1), m.group(1))
            if t.startswith(tail, j + 1): hit = (m.start(), i, j, j + 1 + len(tail)); break
        if not hit: return t, n
        a0, i, j, e = hit
        t = t[:a0] + t[i:j + 1] + t[e:]; n += 1
if ETA:
    s, kq_eta = eta_pairs(s)
    sys.stderr.write('%s: %d rebuilt pair(s) removed\n' % (name, kq_eta))
MAP = {'Z.ltb': 'PrimInt63.ltsb', 'Z.leb': 'PrimInt63.lesb', 'Z.eqb': 'PrimInt63.eqb', 'Z.min': 'zmin', 'Z.max': 'zmax',
       'Z.abs': 'zabs', 'Z.opp': 'zopp', 'Z.even': 'zeven', 'Z.lxor': 'PrimInt63.lxor', 'Z.land': 'PrimInt63.land',
       'Z.lor': 'PrimInt63.lor'}
for a, b in MAP.items(): s = re.sub(re.escape(a) + r'\b', b, s)
left = sorted(set(re.findall(r'\bZ\.[A-Za-z_0-9]+', s)))
if left: sys.exit('unported: ' + ' '.join(left))
s = re.sub(r'\bZ\b', 'int', s)

# ---- the definitions: kind, name, parameters, body
starts = [m for m in re.finditer(r'^(Definition|Fixpoint)\s+([A-Za-z_][A-Za-z_0-9\']*)', s, re.M)]
defs = []
for i, m in enumerate(starts):
    text = s[m.end(): starts[i + 1].start() if i + 1 < len(starts) else len(s)]
    head, _, body = text.partition(':=')
    params = []
    for names, ty in re.findall(r'\(\s*([A-Za-z_0-9\' ]+?)\s*:\s*([^()]+?)\s*\)', head):
        params += [(n, ty.strip()) for n in names.split()]
    defs.append({'kind': m.group(1), 'name': m.group(2), 'params': params, 'body': body, 'head': head})
by = {d['name']: d for d in defs}
m = by.get('solve')
if not m: sys.exit('no solve')
ret = re.sub(r'[()\s]', '', m['head'].split(')')[-1].lstrip(' :')) if ')' in m['head'] else ''
ret = re.sub(r'[()\s]', '', re.search(r':\s*([^:]+?)\s*$', m['head']).group(1))

def ident_uses(text, x): return len(re.findall(r"(?<![A-Za-z_0-9'.])" + re.escape(x) + r"(?![A-Za-z_0-9'])", text))
def is_ident(a): return re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*", a) is not None
def pure(d): return all(t != 'mem' for _, t in d['params'])
NONPURE = {d['name'] for d in defs if d['params'] and not pure(d)} | {'rd', 'upd', 'kq_input', 'kq_arg', 'kq_sum', 'kq_nat'}
USERFN = {d['name'] for d in defs if d['params']}

def call_args(text, pos):
    """the arguments of the call whose function name ends at pos, or None when it is not written as a call `(f a b ..)`"""
    args, i, n = [], pos, len(text)
    while True:
        while i < n and text[i].isspace(): i += 1
        if i >= n or text[i] == ')': return args
        if text[i] == '(':
            d, j = 0, i
            while j < n:
                if text[j] == '(': d += 1
                elif text[j] == ')':
                    d -= 1
                    if d == 0: break
                j += 1
            args.append(text[i:j + 1]); i = j + 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in '()': j += 1
            tok = text[i:j]
            if tok in ('in', 'then', 'else', 'with', 'end', '=>', '|', ':=') or not re.fullmatch(r"-?[A-Za-z_0-9'.]+", tok): return None
            args.append(tok); i = j

def arg_ok(a, multi, is_mem):
    if is_mem: return is_ident(a)
    ids = set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*", a))
    if ids & NONPURE: return False
    if multi and not is_ident(a) and (ids & USERFN): return False
    return True

def inlinable(d):
    if d['kind'] != 'Definition' or d['name'] in ('solve', 'main'): return False
    if not d['params']: return not (set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*", d['body'])) & NONPURE)
    for o in defs:
        if o is d: continue
        for mm in re.finditer(r"(?<![A-Za-z_0-9'.])" + re.escape(d['name']) + r"(?![A-Za-z_0-9'])", o['body']):
            before = o['body'][:mm.start()].rstrip()
            if not before.endswith('('): return False
            args = call_args(o['body'], mm.end())
            if args is None or len(args) != len(d['params']): return False
            for (p, ty), a in zip(d['params'], args):
                if not arg_ok(a, ident_uses(d['body'], p) > 1, ty == 'mem'): return False
    return True

inl = [d['name'] for d in defs if inlinable(d)]
# a `match` on a budget must look at a plain variable (its text is written out twice by KQNat)
for mm in re.finditer(r'match\s+(.+?)\s+with\s*\|?\s*O\b', s):
    if not is_ident(mm.group(1)): sys.exit('a match on a budget that is not a variable: ' + mm.group(1))

args, k = [], 0
for n, ty in by['solve']['params']:
    if ty == 'nat': args.append('(kq_nat (kq_arg %d))' % k); k += 1
    elif ty == 'int': args.append('(kq_arg %d)' % k); k += 1
    elif ty == 'mem': args.append('(kq_input 0)')
    else: sys.exit('solve: parameter type ' + ty)
call = 'solve ' + ' '.join(args)
body = {'int': call, 'int*mem': 'fst (%s)' % call, 'mem': 'kq_sum (%s)' % call}.get(ret)
if body is None: sys.exit('solve: result type ' + ret)
print('''From CertiRocq.Plugin Require Import CertiRocq.
From MetaRocq.Template Require Import All.
Require Import KQ.KQRun KQ.KQShape KQ.KQNat.
Open Scope sint63_scope.
Open Scope kq_scope.

%s
(* KQ-ARGS %d : %s *)
(* the first line only makes the compiler keep the three definitions of KQNat.v at hand *)
Definition main : int :=
  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in
  %s.

MetaRocq Run (kq_shape main).
CertiRocq Extract Inline [ zdiv, zmod, kq_jump ].
%sCertiRocq Compile --allow-unsafe-erasure --anf-variant 9 --c-args 1000 --output "%s_prog" main
Extract Constants [ rd => "kq_rdb", upd => "kq_updb", kq_arg => "kq_arg", kq_input => "kq_input", kq_sum => "kq_sum", kq_nat => "kq_nat_int", kq_select => "kq_select", kq_sel_lts => "kq_sel_lts", kq_sel_les => "kq_sel_les", kq_sel_eq => "kq_sel_eq", kq_sel_ltu => "kq_sel_ltu", kq_sel_leu => "kq_sel_leu", kq_selectn => "kq_selectn", kq_sel_ges => "kq_sel_ges", kq_sel_gts => "kq_sel_gts", kq_sel_ne => "kq_sel_ne", kq_sel_geu => "kq_sel_geu", kq_sel_gtu => "kq_sel_gtu", kq_prof => "kq_prof", kq_in => "kq_in", kq_out => "kq_out", rd32 => "kq_rd32", upd32 => "kq_upd32" ]
Include [ "kq_io.h" ].''' % (s, k, ' '.join('%s:%s' % p for p in by['solve']['params']), body,
                              ('CertiRocq Extract Inline [ %s ].\n' % ', '.join(inl)) if inl else '', out))
sys.stderr.write('%s: written out at their uses: %s\n' % (name, ' '.join(inl) or '-'))
