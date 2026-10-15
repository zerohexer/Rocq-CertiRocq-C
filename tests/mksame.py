#!/usr/bin/env python3
"""mksame.py OUTDIR : THE SAME LOOP WRITTEN MANY WAYS.

"Consistent" has a meaning a machine can check: two ways of writing the same loop in Rocq must give the same speed.
This writes, for a few small loops (kernels), the same computation in several equivalent ways -- a different order of
parameters, every step named by a `let`, the arithmetic behind a helper definition, the `if` turned round, a wrapper,
many parameters, two places that call the loop, a choice written as an `if` or as `kq_select` -- and tests/same.sh
puts each through the translator (KQFast.v), builds them all, checks that every way of one kernel gives the same
answer, and reports how far apart their times are and which ways came out as the very same C.

A way is written as  NAME: KIND  where KIND is
    same      it must run as fast as the kernel's first way (the gate fails beyond a tolerance);
    rule N    it breaks rule N of WRITING-FAST-ROCQ.md on purpose: reported, to show what the rule is worth;
    arith     the same result by OTHER arithmetic (`o + o` for `2 * o`, a count that runs down): equal as numbers, not
              the same operations -- reported, not required to be as fast.

The kernels: sum (a loop that only looks), toss (a choice the machine cannot guess), heavy (the same with more work on
each side), rare (a choice that is nearly always the same way), clamp (read one block, write another), count (read,
then read and write), search (a choice at every step of a search), tree (a function that calls itself twice).

OUTDIR gets NAME.body per way, same.mem (the memory all of them run on), same.args, same.tsv (name, kernel, kind)."""
import sys, os, random
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
MAIN = '''
Definition main : int :=
  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in
  solve (kq_nat (kq_arg 0)) (kq_nat (kq_arg 1)) (kq_arg 1) (kq_input 0).
'''
ways = []          # (kernel, name, kind, text)
def way(kernel, name, kind, text): ways.append((kernel, kernel + '_' + name, kind, text.strip('\n') + '\n' + MAIN))

# ------------------------------------------------------------------ sum: add up a block (a loop that only looks)
OUTER_SUM = '''
Fixpoint outer (fuel n : nat) (nz acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => outer f n nz (%s) s end.
Definition solve (r n : nat) (nz : int) (s : mem) : int := outer r n nz 0 s.
'''
def sum_way(name, kind, inner, call): way('sum', name, kind, inner + OUTER_SUM % call)
sum_way('first', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) (acc + rd 0 i s) s end.''', 'inner n 0 acc s')
sum_way('budget_last', 'same', '''
Fixpoint inner (i acc : int) (s : mem) (fuel : nat) {struct fuel} : int :=
  match fuel with O => acc | S f => inner (i + 1) (acc + rd 0 i s) s f end.''', 'inner 0 acc s n')
sum_way('memory_first', 'same', '''
Fixpoint inner (s : mem) (fuel : nat) (acc i : int) {struct fuel} : int :=
  match fuel with O => acc | S f => inner s f (acc + rd 0 i s) (i + 1) end.''', 'inner s n acc 0')
sum_way('second_test', 'rule 8', '''
Fixpoint inner (fuel : nat) (i n acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => if n <=? i then acc else inner f (i + 1) n (acc + rd 0 i s) s end.''', 'inner n 0 nz acc s')
sum_way('every_step_named', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in let a := acc + x in let j := i + 1 in inner f j a s
  end.''', 'inner n 0 acc s')
sum_way('helper', 'same', '''
Definition add2 (a b : int) : int := a + b.
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (add2 i 1) (add2 acc (rd 0 i s)) s end.''', 'inner n 0 acc s')
sum_way('helper_with_memory', 'same', '''
Definition cell (i : int) (s : mem) : int := rd 0 i s.
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) (acc + cell i s) s end.''', 'inner n 0 acc s')
sum_way('wrapper', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) (acc + rd 0 i s) s end.
Definition whole (n : nat) (acc : int) (s : mem) : int := inner n 0 acc s.''', 'whole n acc s')
sum_way('unused_parameter', 'same', '''
Fixpoint inner (fuel : nat) (i z acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) z (acc + rd 0 i s) s end.''', 'inner n 0 7 acc s')
sum_way('block_as_parameter', 'same', '''
Fixpoint inner (fuel : nat) (h i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f h (i + 1) (acc + rd h i s) s end.''', 'inner n 0 0 acc s')
sum_way('block_as_definition', 'same', '''
Definition rA : int := 0.
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) (acc + rd rA i s) s end.''', 'inner n 0 acc s')
sum_way('cases_other_way_round', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with S f => inner f (i + 1) (acc + rd 0 i s) s | O => acc end.''', 'inner n 0 acc s')
sum_way('sums_other_way_round', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (1 + i) (rd 0 i s + acc) s end.''', 'inner n 0 acc s')
sum_way('from_the_end', 'arith', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i - 1) (acc + rd 0 i s) s end.''', 'inner n (nz - 1) acc s')
sum_way('nine_parameters', 'same', '''
Fixpoint inner (fuel : nat) (i p1 p2 p3 p4 p5 p6 acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) p1 p2 p3 p4 p5 p6 (acc + rd 0 i s) s end.''', 'inner n 0 1 2 3 4 5 6 acc s')
sum_way('two_callers', 'same', '''
Fixpoint inner (fuel : nat) (i p1 p2 p3 p4 p5 p6 acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) p1 p2 p3 p4 p5 p6 (acc + rd 0 i s) s end.''',
  'if (acc land 1) =? 0 then inner n 0 1 2 3 4 5 6 acc s else inner n 0 6 5 4 3 2 1 acc s')
sum_way('two_loops_in_turn', 'rule 2', '''
Fixpoint innerA (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => innerB f (i + 1) (acc + rd 0 i s) s end
with innerB (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => innerA f (i + 1) (acc + rd 0 i s) s end.''', 'innerA n 0 acc s')
way('sum', 'state_in_a_cell', 'rule 1', '''
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with O => s | S f => inner f (i + 1) (upd 3 0 (rd 3 0 s + rd 0 i s) s) end.
Fixpoint outer (fuel n : nat) (s : mem) : mem :=
  match fuel with O => s | S f => outer f n (inner n 0 s) end.
Definition solve (r n : nat) (nz : int) (s : mem) : int := rd 3 0 (outer r n s).
''')

# ------------------------------------------------------------------ toss: a choice the machine cannot guess
OUTER_TOSS = OUTER_SUM
def toss_way(name, kind, inner, call='inner n 0 acc s'): way('toss', name, kind, inner + OUTER_TOSS % call)
toss_way('first', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in inner f (i + 1) (if (x land 1) =? 0 then acc + x else acc - x) s
  end.''')
toss_way('test_named', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in let c := (x land 1) =? 0 in inner f (i + 1) (if c then acc + x else acc - x) s
  end.''')
toss_way('turned_round', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in inner f (i + 1) (if negb ((x land 1) =? 0) then acc - x else acc + x) s
  end.''')
toss_way('other_test', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in inner f (i + 1) (if (x land 1) =? 1 then acc - x else acc + x) s
  end.''')
toss_way('helper', 'same', '''
Definition pick (c : bool) (a b : int) : int := if c then a else b.
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in inner f (i + 1) (pick ((x land 1) =? 0) (acc + x) (acc - x)) s
  end.''')
toss_way('result_named', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in let a := if (x land 1) =? 0 then acc + x else acc - x in inner f (i + 1) a s
  end.''')
toss_way('two_calls', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in if (x land 1) =? 0 then inner f (i + 1) (acc + x) s else inner f (i + 1) (acc - x) s
  end.''')
toss_way('numbers_named_before', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in let a := acc + x in let b := acc - x in inner f (i + 1) (if (x land 1) =? 0 then a else b) s
  end.''')
toss_way('select_written', 'same', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in inner f (i + 1) (kq_select ((x land 1) =? 0) (acc + x) (acc - x)) s
  end.''')
toss_way('by_arithmetic', 'arith', '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => let x := rd 0 i s in inner f (i + 1) (acc + x - 2 * x * (x land 1)) s
  end.''')

# ------------------------------------------------------------------ heavy: the same choice with more work on each side
def loop_way(kernel, name, kind, step):
    way(kernel, name, kind, '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with
  | O => acc
  | S f => %s
  end.''' % step + OUTER_SUM % 'inner n 0 acc s')
HA, HB = 'acc + 3 * x + (x >> 2)', 'acc - 5 * x - (x >> 3)'
loop_way('heavy', 'first', 'same', 'let x := rd 0 i s in inner f (i + 1) (if (x land 1) =? 0 then %s else %s) s' % (HA, HB))
loop_way('heavy', 'numbers_named_before', 'same', 'let x := rd 0 i s in let a := %s in let b := %s in inner f (i + 1) (if (x land 1) =? 0 then a else b) s' % (HA, HB))
loop_way('heavy', 'select_written', 'same', 'let x := rd 0 i s in inner f (i + 1) (kq_select ((x land 1) =? 0) (%s) (%s)) s' % (HA, HB))
loop_way('heavy', 'turned_round', 'same', 'let x := rd 0 i s in inner f (i + 1) (if negb ((x land 1) =? 0) then %s else %s) s' % (HB, HA))
loop_way('heavy', 'two_calls', 'same', 'let x := rd 0 i s in if (x land 1) =? 0 then inner f (i + 1) (%s) s else inner f (i + 1) (%s) s' % (HA, HB))

# ------------------------------------------------------------------ rare: a test that is nearly always the same way
# (block 0 holds numbers below 1000: `x <? 990` is true 99 times in 100).  Here a JUMP is the fast form: the machine
# guesses it, and the number not taken is never worked out.
RA, RB = 'acc + 1', '(acc * 3) land 1048575'
loop_way('rare', 'first', 'same', 'let x := rd 0 i s in inner f (i + 1) (if x <? 990 then %s else %s) s' % (RA, RB))
loop_way('rare', 'numbers_named_before', 'same', 'let x := rd 0 i s in let a := %s in let b := %s in inner f (i + 1) (if x <? 990 then a else b) s' % (RA, RB))
loop_way('rare', 'two_calls', 'same', 'let x := rd 0 i s in if x <? 990 then inner f (i + 1) (%s) s else inner f (i + 1) (%s) s' % (RA, RB))
loop_way('rare', 'select_written', 'rule 4', 'let x := rd 0 i s in inner f (i + 1) (kq_select (x <? 990) (%s) (%s)) s' % (RA, RB))

# ------------------------------------------------------------------ clamp: read one block, write another
OUTER_CLAMP = '''
Fixpoint outer (fuel n : nat) (nz t : int) (s : mem) : mem :=
  match fuel with O => s | S f => outer f n nz (t + 5) (%s) end.
Fixpoint total (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => total f (i + 1) (acc + rd 1 i s) s end.
Definition solve (r n : nat) (nz : int) (s : mem) : int := total n 0 0 (outer r n nz 0 s).
'''
def clamp_way(name, kind, inner, call='inner n 0 t s'): way('clamp', name, kind, inner + OUTER_CLAMP % call)
clamp_way('first', 'same', '''
Fixpoint inner (fuel : nat) (i t : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => let x := rd 0 i s in inner f (i + 1) t (upd 1 i (if x <? t then x else t) s)
  end.''')
clamp_way('helper_min', 'same', '''
Fixpoint inner (fuel : nat) (i t : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => inner f (i + 1) t (upd 1 i (zmin (rd 0 i s) t) s)
  end.''')
clamp_way('every_step_named', 'same', '''
Fixpoint inner (fuel : nat) (i t : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => let x := rd 0 i s in let c := x <? t in let v := if c then x else t in let s1 := upd 1 i v s in
           let j := i + 1 in inner f j t s1
  end.''')
clamp_way('read_twice', 'same', '''
Fixpoint inner (fuel : nat) (i t : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => inner f (i + 1) t (upd 1 i (if rd 0 i s <? t then rd 0 i s else t) s)
  end.''')
clamp_way('helper_writes', 'same', '''
Definition put (i v : int) (s : mem) : mem := upd 1 i v s.
Fixpoint inner (fuel : nat) (i t : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => let x := rd 0 i s in inner f (i + 1) t (put i (if x <? t then x else t) s)
  end.''')
clamp_way('turned_round', 'same', '''
Fixpoint inner (fuel : nat) (i t : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => let x := rd 0 i s in inner f (i + 1) t (upd 1 i (if t <=? x then t else x) s)
  end.''')
clamp_way('two_writes', 'same', '''
Fixpoint inner (fuel : nat) (i t : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => let x := rd 0 i s in if x <? t then inner f (i + 1) t (upd 1 i x s) else inner f (i + 1) t (upd 1 i t s)
  end.''')

# ------------------------------------------------------------------ count: read a cell, then read and write another
OUTER_COUNT = '''
Fixpoint outer (fuel n : nat) (s : mem) : mem :=
  match fuel with O => s | S f => outer f n (%s) end.
Fixpoint total (fuel : nat) (j acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => total f (j + 1) (acc + rd 4 j s * (j + 1)) s end.
Definition solve (r n : nat) (nz : int) (s : mem) : int := total 1024 0 0 (outer r n s).
'''
def count_way(name, kind, inner, call='inner n 0 s'): way('count', name, kind, inner + OUTER_COUNT % call)
count_way('first', 'same', '''
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => let x := rd 0 i s land 1023 in inner f (i + 1) (upd 4 x (rd 4 x s + 1) s)
  end.''')
count_way('helper_writes', 'same', '''
Definition bump (x : int) (s : mem) : mem := upd 4 x (rd 4 x s + 1) s.
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => inner f (i + 1) (bump (rd 0 i s land 1023) s)
  end.''')
count_way('every_step_named', 'same', '''
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => let a := rd 0 i s in let x := a land 1023 in let c := rd 4 x s in let c1 := c + 1 in
           let s1 := upd 4 x c1 s in inner f (i + 1) s1
  end.''')
count_way('read_twice', 'same', '''
Fixpoint inner (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => inner f (i + 1) (upd 4 (rd 0 i s land 1023) (rd 4 (rd 0 i s land 1023) s + 1) s)
  end.''')

# ------------------------------------------------------------------ search: ten steps of a search, a choice at every one
OUTER_SEARCH = '''
Fixpoint inner (fuel : nat) (i acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => inner f (i + 1) (acc + %s) s end.
Fixpoint outer (fuel n : nat) (acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => outer f n (inner n 0 acc s) s end.
Definition solve (r n : nat) (nz : int) (s : mem) : int := outer r n 0 s.
'''
def search_way(name, kind, lb, call='lb 10 0 1024 (rd 0 i s) s'): way('search', name, kind, lb + OUTER_SEARCH % call)
search_way('first', 'same', '''
Fixpoint lb (fuel : nat) (lo len key : int) (s : mem) : int :=
  match fuel with
  | O => lo
  | S f => let half := len >> 1 in lb f (if rd 2 (lo + half) s <? key then lo + half else lo) (len - half) key s
  end.''')
search_way('every_step_named', 'same', '''
Fixpoint lb (fuel : nat) (lo len key : int) (s : mem) : int :=
  match fuel with
  | O => lo
  | S f => let half := len >> 1 in let mid := lo + half in let v := rd 2 mid s in let c := v <? key in
           let lo1 := if c then mid else lo in let len1 := len - half in lb f lo1 len1 key s
  end.''')
search_way('turned_round', 'same', '''
Fixpoint lb (fuel : nat) (lo len key : int) (s : mem) : int :=
  match fuel with
  | O => lo
  | S f => let half := len >> 1 in lb f (if key <=? rd 2 (lo + half) s then lo else lo + half) (len - half) key s
  end.''')
search_way('helper', 'same', '''
Definition pick (c : bool) (a b : int) : int := if c then a else b.
Fixpoint lb (fuel : nat) (lo len key : int) (s : mem) : int :=
  match fuel with
  | O => lo
  | S f => let half := len >> 1 in lb f (pick (rd 2 (lo + half) s <? key) (lo + half) lo) (len - half) key s
  end.''')
search_way('select_written', 'same', '''
Fixpoint lb (fuel : nat) (lo len key : int) (s : mem) : int :=
  match fuel with
  | O => lo
  | S f => let half := len >> 1 in lb f (kq_select (rd 2 (lo + half) s <? key) (lo + half) lo) (len - half) key s
  end.''')
search_way('second_test', 'rule 8', '''
Fixpoint lb (fuel : nat) (lo len key : int) (s : mem) : int :=
  match fuel with
  | O => lo
  | S f => if len <=? 1 then lo
           else let half := len >> 1 in lb f (if rd 2 (lo + half) s <? key then lo + half else lo) (len - half) key s
  end.''')
search_way('two_calls', 'same', '''
Fixpoint lb (fuel : nat) (lo len key : int) (s : mem) : int :=
  match fuel with
  | O => lo
  | S f => let half := len >> 1 in
           if rd 2 (lo + half) s <? key then lb f (lo + half) (len - half) key s else lb f lo (len - half) key s
  end.''')

# ------------------------------------------------------------------ tree: a function that calls itself twice
OUTER_TREE = '''
Fixpoint outer (fuel : nat) (acc : int) (s : mem) : int :=
  match fuel with O => acc | S f => outer f (acc + %s) s end.
Definition solve (r n : nat) (nz : int) (s : mem) : int := outer r 0 s.
'''
def tree_way(name, kind, t, call='tsum 15 1 s'): way('tree', name, kind, t + OUTER_TREE % call)
tree_way('first', 'same', '''
Fixpoint tsum (h : nat) (o : int) (s : mem) : int :=
  match h with O => rd 0 o s | S h' => tsum h' (2 * o) s + tsum h' (2 * o + 1) s end.''')
tree_way('every_step_named', 'same', '''
Fixpoint tsum (h : nat) (o : int) (s : mem) : int :=
  match h with
  | O => rd 0 o s
  | S h' => let l := 2 * o in let a := tsum h' l s in let r := l + 1 in let b := tsum h' r s in a + b
  end.''')
tree_way('doubled_by_adding', 'arith', '''
Fixpoint tsum (h : nat) (o : int) (s : mem) : int :=
  match h with O => rd 0 o s | S h' => tsum h' (o + o) s + tsum h' (o + o + 1) s end.''')
tree_way('total_passed_on', 'arith', '''
Fixpoint tacc (h : nat) (o acc : int) (s : mem) : int :=
  match h with O => acc + rd 0 o s | S h' => tacc h' (2 * o + 1) (tacc h' (2 * o) acc s) s end.''', 'tacc 15 1 0 s')

for kernel, name, kind, text in ways:
    open(os.path.join(out, name + '.body'), 'w').write('(* the same loop, written many ways: kernel `%s`, this way must be: %s *)\n' % (kernel, kind) + text)
open(os.path.join(out, 'same.tsv'), 'w').write(''.join('%s\t%s\t%s\n' % (name, kernel, kind) for kernel, name, kind, _ in ways))
random.seed(41); n = 100000
A = [random.randint(0, 999) for _ in range(n)]
blocks = [A, [0] * n, list(range(1024)), [0] * 16, [0] * 1024]
with open(os.path.join(out, 'same.mem'), 'w') as f:
    f.write('%d\n' % len(blocks))
    for b in blocks: f.write('%d %s\n' % (len(b), ' '.join(map(str, b))))
open(os.path.join(out, 'same.args'), 'w').write('200 %d\n' % n)
print('%d ways of %d kernels' % (len(ways), len({w[0] for w in ways})))
