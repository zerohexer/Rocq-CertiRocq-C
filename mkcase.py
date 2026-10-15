#!/usr/bin/env python3
"""mkcase.py NAME SEED : a random small input for sv/NAME.sv -- case/NAME.mem (for the native run), case/NAME.args, and
case/NAME_ref.v, which evaluates the ORIGINAL program (Z, lists) on the same input inside Rocq."""
import re, sys, random
name, seed = sys.argv[1], int(sys.argv[2]); random.seed(seed)
src = open('sv/%s.sv' % name).read()
m = re.search(r'Definition solve\s+(.*?)\s*:\s*([^:=]+?)\s*:=', src, re.S)
params = [(n, t) for ns, t in re.findall(r'\(\s*([A-Za-z_0-9\' ]+?)\s*:\s*([A-Za-z_0-9]+)\s*\)', m.group(1)) for n in ns.split()]
ret = re.sub(r'[()\s]', '', m.group(2))
NB, LEN, VMAX = 28, 96, 9
mem = [[random.randint(0, VMAX) for _ in range(LEN)] for _ in range(NB)]
vals = []
for n, t in params:
    if t == 'nat': vals.append(5 if n in ('h', 'w', 'w1', 'wn') else 12)
    elif t == 'Z': vals.append(12)
open('case/%s.mem' % name, 'w').write('%d\n' % NB + ''.join('%d %s\n' % (len(b), ' '.join(map(str, b))) for b in mem))
open('case/%s.args' % name, 'w').write(' '.join(map(str, vals)) + '\n')
it = iter(vals)
call = 'solve ' + ' '.join(('%d%%nat' % next(it)) if t == 'nat' else (str(next(it)) if t == 'Z' else 'kq_in') for n, t in params)
res = {'Z': '(%s, 0)' % call, 'Z*mem': "(let r := %s in (fst r, chk (snd r)))" % call, 'mem': '(let r := %s in (chk r, chk r))' % call}[ret]
open('case/%s_ref.v' % name, 'w').write('''From Stdlib Require Import List ZArith Bool.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (list (list Z)).
Definition rd (h i : Z) (s : mem) : Z := nth (Z.to_nat i) (nth (Z.to_nat h) s []) 0.
Fixpoint updL {A : Type} (i : nat) (x : A) (l : list A) : list A :=
  match i, l with | _, [] => [] | O, _ :: t => x :: t | S i', hh :: t => hh :: updL i' x t end.
Definition upd (h i v : Z) (s : mem) : mem := updL (Z.to_nat h) (updL (Z.to_nat i) v (nth (Z.to_nat h) s [])) s.
Definition chk (s : mem) : Z :=
  snd (fold_left (fun (st : Z * Z) (b : list Z) =>
         let h := fst st in
         (h + 1, snd (fold_left (fun (su : Z * Z) (v : Z) =>
                        let i := fst su in
                        (i + 1, (snd su + (((h + 1) * (i + 1)) mod 1000000007) * (v mod 1000000007)) mod 1000000007))
                      b (0, snd st)))) s (0, 0)).

%s
Definition kq_in : mem := [%s].
Timeout 300 Eval vm_compute in %s.
''' % (src, ';\n  '.join('[' + '; '.join(map(str, b)) + ']' for b in mem), res))
print(name, ret, vals)
