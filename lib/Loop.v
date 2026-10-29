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
(* LOOP-END *)
