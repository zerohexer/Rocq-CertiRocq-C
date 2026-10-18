#!/usr/bin/env python3
"""mkworst.py OUTDIR : THE SAME COMPUTATION WRITTEN AS BADLY AS THE CHECKER ALLOWS.

For three kernels (a mixed loop, a search, a histogram) the first way is written by the guideline; the others break
one rule after another until the last way breaks all of them together:
    state in cells      rule 1: running totals and counters live in memory cells, read and written every round
    phases              rule 2: one loop that asks several questions per element, a phase number choosing which
    repeated reads      the same cell read again at every use
    helpers             a non-recursive Definition for every small step
The ways of one kernel compute the same number.  tests/worst.sh builds each through the kit route and through the proved
route and times it next to the first way, and next to a plain C version of the first way (tests/worst_ref.c).

OUTDIR gets NAME.body per way, same.mem, same.args, same.tsv (name, kernel, kind) -- the layout of tests/mksame.py."""
import sys, os, random
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
MAIN = '''
Definition main : int :=
  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in
  solve (kq_nat (kq_arg 0)) (kq_nat (kq_arg 1)) (kq_nat (kq_arg 2)) (kq_arg 1) (kq_input 0).
'''
ways = []
def way(kernel, name, kind, text): ways.append((kernel, kernel + '_' + name, kind, text.strip('\n') + '\n' + MAIN))

# blocks: 0 = data (values 0..999), 1 = output, 2 = sorted table of 1024, 3 = state cells, 4 = counters (1024)

# ------------------------------------------------------------------ mix: two running values, a write per element
OUTER_MIX = '''
Fixpoint outer (fuel n m : nat) (s : mem) : mem :=
  match fuel with O => s | S f => outer f n m (%s) end.
Definition solve (r n m : nat) (nz : int) (s : mem) : int :=
  let s1 := outer r n m s in rd 3 0 s1 + rd 1 (nz - 1) s1.
'''
def mix(name, kind, inner, call): way('mix', name, kind, inner + OUTER_MIX % call)
mix('guideline', 'first', '''
Fixpoint inner (fuel : nat) (i acc cnt : int) (s : mem) : mem :=
  match fuel with
  | O => upd 3 0 (acc + cnt) s
  | S f =>
    let x := rd 0 i s in
    let a := if (x land 1) =? 0 then acc + x * 3 else acc - x in
    let c := if x <? 500 then cnt + 1 else cnt in
    inner f (i + 1) a c (upd 1 i (a land 1023) s)
  end.''', 'inner n 0 0 0 s')
mix('state_in_cells', 'rule 1', '''
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => upd 3 0 (rd 3 1 s + rd 3 2 s) s
  | S f =>
    let x := rd 0 i s in
    let s1 := upd 3 1 (if (x land 1) =? 0 then rd 3 1 s + x * 3 else rd 3 1 s - x) s in
    let s2 := upd 3 2 (if x <? 500 then rd 3 2 s1 + 1 else rd 3 2 s1) s1 in
    inner f (i + 1) (upd 1 i (rd 3 1 s2 land 1023) s2)
  end.''', 'inner n 0 (upd 3 2 0 (upd 3 1 0 s))')
mix('phases', 'rule 2', '''
Fixpoint inner (fuel : nat) (ph i x acc cnt : int) (s : mem) : mem :=
  match fuel with
  | O => upd 3 0 (acc + cnt) s
  | S f =>
    if ph =? 0 then inner f 1 i (rd 0 i s) acc cnt s
    else if ph =? 1 then inner f 2 i x (if (x land 1) =? 0 then acc + x * 3 else acc - x) cnt s
    else inner f 0 (i + 1) x acc (if x <? 500 then cnt + 1 else cnt) (upd 1 i (acc land 1023) s)
  end.''', 'inner m 0 0 0 0 0 s')
mix('phases_and_cells', 'rule 1+2', '''
Fixpoint inner (fuel : nat) (ph i : int) (s : mem) : mem :=
  match fuel with
  | O => upd 3 0 (rd 3 1 s + rd 3 2 s) s
  | S f =>
    if ph =? 0 then inner f 1 i (upd 3 3 (rd 0 i s) s)
    else if ph =? 1 then
      inner f 2 i (upd 3 1 (if (rd 3 3 s land 1) =? 0 then rd 3 1 s + rd 3 3 s * 3 else rd 3 1 s - rd 3 3 s) s)
    else
      inner f 0 (i + 1) (upd 1 i (rd 3 1 s land 1023)
        (upd 3 2 (if rd 3 3 s <? 500 then rd 3 2 s + 1 else rd 3 2 s) s))
  end.''', 'inner m 0 0 (upd 3 2 0 (upd 3 1 0 s))')
mix('everything', 'rules 1+2+helpers', '''
Definition odd (x : int) : bool := (x land 1) =? 1.
Definition small (x : int) : bool := x <? 500.
Definition cur (s : mem) (i : int) : int := rd 0 i s.
Definition bump (c : bool) (v d : int) : int := if c then v + d else v.
Definition mixed (x a : int) : int := if odd x then a - x else a + x * 3.
Fixpoint inner (fuel : nat) (ph i : int) (s : mem) : mem :=
  match fuel with
  | O => upd 3 0 (rd 3 1 s + rd 3 2 s) s
  | S f =>
    if ph =? 0 then inner f 1 i (upd 3 3 (cur s i) s)
    else if ph =? 1 then inner f 2 i (upd 3 1 (mixed (cur s i) (rd 3 1 s)) s)
    else
      let s1 := upd 3 2 (bump (small (cur s i)) (rd 3 2 s) 1) s in
      inner f 0 (i + 1) (upd 1 i (rd 3 1 s1 land 1023) s1)
  end.''', 'inner m 0 0 (upd 3 2 0 (upd 3 1 0 s))')

# ------------------------------------------------------------------ search: ten steps of a search per element
OUTER_SEARCH = '''
Fixpoint outer (fuel n m : nat) (acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => outer f n m (%s) s end.
Definition solve (r n m : nat) (nz : int) (s : mem) : int := outer r n m 0 s.
'''
def search(name, kind, text, call): way('search', name, kind, text + OUTER_SEARCH % call)
OUTER_SEARCH_MEM = '''
Fixpoint outer (fuel n m : nat) (s : mem) : mem :=
  match fuel with O => s | S f => outer f n m (inner n 0 s) end.
Definition solve (r n m : nat) (nz : int) (s : mem) : int := rd 3 4 (outer r n m (upd 3 4 0 s)).
'''
def search_mem(name, kind, text): way('search', name, kind, text + OUTER_SEARCH_MEM)
search('guideline', 'first', '''
Fixpoint lb (fuel : nat) (lo len key : int) (s : mem) : int :=
  match fuel with
  | O => lo
  | S f => let half := len >> 1 in lb f (if rd 2 (lo + half) s <? key then lo + half else lo) (len - half) key s
  end.
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) (acc + lb 10 0 1024 (rd 0 i s) s) s end.''', 'inner n 0 acc s')
search_mem('state_in_cells', 'rule 1', '''
Fixpoint lb (fuel : nat) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f =>
    let half := rd 3 1 s >> 1 in
    lb f (upd 3 1 (rd 3 1 s - half)
           (upd 3 0 (if rd 2 (rd 3 0 s + half) s <? rd 3 2 s then rd 3 0 s + half else rd 3 0 s) s))
  end.
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f =>
    let s1 := lb 10 (upd 3 2 (rd 0 i s) (upd 3 1 1024 (upd 3 0 0 s))) in
    inner f (i + 1) (upd 3 4 (rd 3 4 s1 + rd 3 0 s1) s1)
  end.''')
search('phases', 'rule 2', '''
Fixpoint lb (fuel : nat) (ph lo len key mid v : int) (s : mem) : int :=
  match fuel with
  | O => lo
  | S f =>
    if ph =? 0 then lb f 1 lo len key (lo + (len >> 1)) v s
    else if ph =? 1 then lb f 2 lo len key mid (rd 2 mid s) s
    else lb f 0 (if v <? key then mid else lo) (len - (len >> 1)) key mid v s
  end.
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) (acc + lb 30 0 0 1024 (rd 0 i s) 0 0 s) s end.''', 'inner n 0 acc s')
search_mem('phases_and_cells', 'rule 1+2', '''
Fixpoint lb (fuel : nat) (ph : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f =>
    if ph =? 0 then lb f 1 (upd 3 5 (rd 3 0 s + (rd 3 1 s >> 1)) s)
    else if ph =? 1 then lb f 2 (upd 3 6 (rd 2 (rd 3 5 s) s) s)
    else lb f 0 (upd 3 1 (rd 3 1 s - (rd 3 1 s >> 1))
                  (upd 3 0 (if rd 3 6 s <? rd 3 2 s then rd 3 5 s else rd 3 0 s) s))
  end.
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f =>
    let s1 := lb 30 0 (upd 3 2 (rd 0 i s) (upd 3 1 1024 (upd 3 0 0 s))) in
    inner f (i + 1) (upd 3 4 (rd 3 4 s1 + rd 3 0 s1) s1)
  end.''')

# ------------------------------------------------------------------ hist: a counter table, read-modify-write
OUTER_HIST = '''
Fixpoint outer (fuel n m : nat) (s : mem) : mem :=
  match fuel with O => s | S f => outer f n m (inner n 0 s) end.
Definition solve (r n m : nat) (nz : int) (s : mem) : int :=
  let s1 := outer r n m s in rd 4 0 s1 + rd 4 1 s1 + rd 4 511 s1 + rd 4 1023 s1.
'''
def hist(name, kind, text): way('hist', name, kind, text + OUTER_HIST)
hist('guideline', 'first', '''
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => let k := rd 0 i s land 1023 in inner f (i + 1) (upd 4 k (rd 4 k s + 1) s)
  end.''')
hist('repeated_reads', 'repeats', '''
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => inner f (i + 1) (upd 4 (rd 0 i s land 1023) (rd 4 (rd 0 i s land 1023) s + 1) s)
  end.''')
hist('state_in_cells', 'rule 1', '''
Fixpoint inner (fuel : nat) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f =>
    let s1 := upd 3 7 (rd 0 (rd 3 8 s) s land 1023) s in
    let s2 := upd 4 (rd 3 7 s1) (rd 4 (rd 3 7 s1) s1 + 1) s1 in
    inner f (upd 3 8 (rd 3 8 s2 + 1) s2)
  end.
Definition inner0 (n : nat) (s : mem) : mem := inner n (upd 3 8 0 s).''')
hist('phases_and_helpers', 'rule 2+helpers', '''
Definition key (s : mem) (i : int) : int := rd 0 i s land 1023.
Definition count (s : mem) (k : int) : int := rd 4 k s.
Fixpoint inner (fuel : nat) (ph i k v : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f =>
    if ph =? 0 then inner f 1 i (key s i) v s
    else if ph =? 1 then inner f 2 i k (count s k) s
    else inner f 0 (i + 1) k v (upd 4 k (v + 1) s)
  end.''')
for n_, (k_, nm_, kd_, tx_) in enumerate(ways):
    if nm_ == 'hist_state_in_cells':
        ways[n_] = (k_, nm_, kd_, tx_.replace('inner n 0 s', 'inner0 n s'))
    if nm_ == 'hist_phases_and_helpers':
        ways[n_] = (k_, nm_, kd_, tx_.replace('outer f n m (inner n 0 s)', 'outer f n m (inner m 0 0 0 0 s)'))

for kernel, name, kind, text in ways:
    open(os.path.join(out, name + '.body'), 'w').write(
        '(* the same computation, written as badly as the checker allows: kernel `%s`, way `%s` (%s) *)\n' % (kernel, name, kind) + text)
open(os.path.join(out, 'same.tsv'), 'w').write(''.join('%s\t%s\t%s\n' % (name, kernel, kind) for kernel, name, kind, _ in ways))
random.seed(41); n = 100000
A = [random.randint(0, 999) for _ in range(n)]
blocks = [A, [0] * n, sorted(random.randint(0, 999) for _ in range(1024)), [0] * 16, [0] * 1024]
with open(os.path.join(out, 'same.mem'), 'w') as f:
    f.write('%d\n' % len(blocks))
    for b in blocks: f.write('%d %s\n' % (len(b), ' '.join(map(str, b))))
open(os.path.join(out, 'same.args'), 'w').write('200 %d %d\n' % (n, 3 * n))
print('%d ways of %d kernels' % (len(ways), len({w[0] for w in ways})))
