(* lib/Loop.v -- LOOPS THE WAY C WRITES THEM, with no fuel to choose.

   A loop over a range of integers runs a known number of times, hi - lo, and that count is what Rocq's rule of a
   shrinking argument needs: `kq_nat (hi - lo)` is the number of rounds (0 when hi is not above lo).  So these loops are
   exact: there is no budget that can be too small and silently cut the loop short.

       loop_up lo hi acc (fun i acc => ..)       for (i = lo; i < hi; i++) acc = ..;   gives the accumulator
       loop_up_m lo hi s (fun i s => ..)         the same, with a memory as the state: gives the memory
       loop_find lo hi (fun i => test)           the first i in lo .. hi - 1 for which the test holds, hi if none; stops there

   The function given may name any variable of the text around it (a bound, an array's block, a memory it reads): the
   loop is copied for the function it is given, as a macro is (proved/README.md, functions as values).
   A program that names a loop_ function gets this text in front of it (proved/kitc.py), as for lib/Slab.v and lib/View.v.
   A loop that ends on something found in the data and has no bound of its own (Collatz) still needs a budget or a proof
   that it ends; that is a different loop. *)
From Stdlib Require Import Sint63.
Require Import KQ.KQRun.
Open Scope sint63_scope.

(* LOOP-BEGIN *)
Fixpoint loop_up_go (k : nat) (i acc : int) (body : int -> int -> int) : int :=
  match k with O => acc | S k' => loop_up_go k' (i + 1) (body i acc) body end.
Definition loop_up (lo hi acc : int) (body : int -> int -> int) : int := loop_up_go (kq_nat (hi - lo)) lo acc body.

Fixpoint loop_up_m_go (k : nat) (i : int) (body : int -> mem -> mem) (s : mem) : mem :=
  match k with O => s | S k' => loop_up_m_go k' (i + 1) body (body i s) end.
Definition loop_up_m (lo hi : int) (s : mem) (body : int -> mem -> mem) : mem := loop_up_m_go (kq_nat (hi - lo)) lo body s.

Fixpoint loop_find_go (k : nat) (i hi : int) (p : int -> bool) : int :=
  match k with O => hi | S k' => if p i then i else loop_find_go k' (i + 1) hi p end.
Definition loop_find (lo hi : int) (p : int -> bool) : int := loop_find_go (kq_nat (hi - lo)) lo hi p.

(* a loop on two numbers that ends when its test fails: the number of rounds is bounded by a MEASURE, a number that falls at
   every round (gcd: the second number).  The budget is the measure itself, so it is never a guess; lib/LoopSpec.v proves that
   when the measure falls the loop ends with the test false (loop_two_ends).
       loop_two meas c fa fb a b      while (c a b) { (a, b) = (fa a b, fb a b) }      gives a *)
Fixpoint loop_two_go (k : nat) (a b : int) (c : int -> int -> bool) (fa fb : int -> int -> int) : int :=
  match k with
  | O => a
  | S k' => if c a b then loop_two_go k' (fa a b) (fb a b) c fa fb else a
  end.
Definition loop_two (meas : int -> int -> int) (c : int -> int -> bool) (fa fb : int -> int -> int) (a b : int) : int :=
  loop_two_go (kq_nat (meas a b)) a b c fa fb.

(* RECURSION WITH A MEASURE: write the function as its body with a `rec` for the recursive call, and a measure that falls at
   every call of rec:   wfix2 meas (fun rec a b => .. rec a' b' ..) a b.
   The budget is the measure plus one, never a guess.  The body may call rec in any position (a tail call is a loop, another is
   a call), and may use any variable of the text around it.  lib/LoopSpec.v proves, for every one of these, the equation
   `wfix2 meas F a b = F (wfix2 meas F) a b` when F calls rec only at a smaller measure (the proof of that is the termination
   argument, and it is the user's: a tactic does the usual ones).
       wfixN       N numbers -> a number            wfixNm      N numbers and a memory (read) -> a number
       wfixmN      N numbers and a memory -> the memory it ends with (the loop's state is the memory) *)
Fixpoint wfix1_go (k : nat) (F : (int -> int) -> int -> int) (a : int) : int :=
  match k with O => 0 | S k' => F (wfix1_go k' F) a end.
Definition wfix1 (meas : int -> int) (F : (int -> int) -> int -> int) (a : int) : int :=
  wfix1_go (kq_nat (meas a + 1)) F a.
Fixpoint wfix2_go (k : nat) (F : (int -> int -> int) -> int -> int -> int) (a b : int) : int :=
  match k with O => 0 | S k' => F (wfix2_go k' F) a b end.
Definition wfix2 (meas : int -> int -> int) (F : (int -> int -> int) -> int -> int -> int) (a b : int) : int :=
  wfix2_go (kq_nat (meas a b + 1)) F a b.
Fixpoint wfix3_go (k : nat) (F : (int -> int -> int -> int) -> int -> int -> int -> int) (a b c : int) : int :=
  match k with O => 0 | S k' => F (wfix3_go k' F) a b c end.
Definition wfix3 (meas : int -> int -> int -> int) (F : (int -> int -> int -> int) -> int -> int -> int -> int) (a b c : int) : int :=
  wfix3_go (kq_nat (meas a b c + 1)) F a b c.

Fixpoint wfix1m_go (k : nat) (F : (int -> mem -> int) -> int -> mem -> int) (a : int) (s : mem) : int :=
  match k with O => 0 | S k' => F (wfix1m_go k' F) a s end.
Definition wfix1m (meas : int -> int) (F : (int -> mem -> int) -> int -> mem -> int) (a : int) (s : mem) : int :=
  wfix1m_go (kq_nat (meas a + 1)) F a s.
Fixpoint wfix2m_go (k : nat) (F : (int -> int -> mem -> int) -> int -> int -> mem -> int) (a b : int) (s : mem) : int :=
  match k with O => 0 | S k' => F (wfix2m_go k' F) a b s end.
Definition wfix2m (meas : int -> int -> int) (F : (int -> int -> mem -> int) -> int -> int -> mem -> int) (a b : int) (s : mem) : int :=
  wfix2m_go (kq_nat (meas a b + 1)) F a b s.
Fixpoint wfix3m_go (k : nat) (F : (int -> int -> int -> mem -> int) -> int -> int -> int -> mem -> int) (a b c : int) (s : mem) : int :=
  match k with O => 0 | S k' => F (wfix3m_go k' F) a b c s end.
Definition wfix3m (meas : int -> int -> int -> int) (F : (int -> int -> int -> mem -> int) -> int -> int -> int -> mem -> int) (a b c : int) (s : mem) : int :=
  wfix3m_go (kq_nat (meas a b c + 1)) F a b c s.

Fixpoint wfixm1_go (k : nat) (F : (int -> mem -> mem) -> int -> mem -> mem) (a : int) (s : mem) : mem :=
  match k with O => s | S k' => F (wfixm1_go k' F) a s end.
Definition wfixm1 (meas : int -> int) (F : (int -> mem -> mem) -> int -> mem -> mem) (a : int) (s : mem) : mem :=
  wfixm1_go (kq_nat (meas a + 1)) F a s.
Fixpoint wfixm2_go (k : nat) (F : (int -> int -> mem -> mem) -> int -> int -> mem -> mem) (a b : int) (s : mem) : mem :=
  match k with O => s | S k' => F (wfixm2_go k' F) a b s end.
Definition wfixm2 (meas : int -> int -> int) (F : (int -> int -> mem -> mem) -> int -> int -> mem -> mem) (a b : int) (s : mem) : mem :=
  wfixm2_go (kq_nat (meas a b + 1)) F a b s.
(* LOOP-END *)
