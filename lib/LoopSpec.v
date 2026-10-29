(* lib/LoopSpec.v -- WHAT THE LOOPS OF lib/Loop.v GUARANTEE.  A loop whose budget is a measure that falls at every round
   ends with its test false: the budget is never too small.

   `loop_two_state` is the loop run to the end: the pair of numbers it stops at.  `loop_two_go k` with a budget k at least the
   measure gives its first number, and the test is false there.  (loop_two's budget is `kq_nat (meas a b)`, and a number of
   at most 2^60 has the natural number of that size: proved as `kq_nat_val` in proved/KQMAuto.v.) *)
From Stdlib Require Import ZArith Lia Sint63.
Require Import KQ.KQRun KQ.lib.Loop.
Open Scope sint63_scope.
Notation Z_ := Sint63.to_Z.

Fixpoint loop_two_state (k : nat) (a b : int) (c : int -> int -> bool) (fa fb : int -> int -> int) : int * int :=
  match k with
  | O => (a, b)
  | S k' => if c a b then loop_two_state k' (fa a b) (fb a b) c fa fb else (a, b)
  end.

Lemma loop_two_go_state (k : nat) : forall a b c fa fb, loop_two_go k a b c fa fb = fst (loop_two_state k a b c fa fb).
Proof.
  induction k as [|k IH]; intros a b c fa fb; cbn [loop_two_go loop_two_state]; [reflexivity | ].
  destruct (c a b); [apply IH | reflexivity].
Qed.

(* the measure falls at every round that runs, and stays at least 0 *)
Definition falls (meas : int -> int -> int) (c : int -> int -> bool) (fa fb : int -> int -> int) : Prop :=
  forall a b, c a b = true -> (0 <= Z_ (meas (fa a b) (fb a b)) /\ Z_ (meas (fa a b) (fb a b)) < Z_ (meas a b))%Z.

Theorem loop_two_ends (meas : int -> int -> int) (c : int -> int -> bool) (fa fb : int -> int -> int) :
  falls meas c fa fb ->
  forall k a b, (Z_ (meas a b) <= Z.of_nat k)%Z ->
  c (fst (loop_two_state k a b c fa fb)) (snd (loop_two_state k a b c fa fb)) = false.
Proof.
  intros F. induction k as [|k IH]; intros a b M; cbn [loop_two_state].
  - destruct (c a b) eqn:E; [ | exact E]. exfalso. pose proof (F a b E) as [H0 H1]. cbn in M. lia.
  - destruct (c a b) eqn:E.
    + pose proof (F a b E) as [H0 H1]. apply IH. rewrite Nat2Z.inj_succ in M. lia.
    + exact E.
Qed.

(* the loop with a budget at least the measure: its answer is the first number it stops at, and the test is false there *)
Corollary loop_two_go_ends (meas : int -> int -> int) (c : int -> int -> bool) (fa fb : int -> int -> int) (k : nat) (a b : int) :
  falls meas c fa fb -> (Z_ (meas a b) <= Z.of_nat k)%Z ->
  exists b', c (loop_two_go k a b c fa fb) b' = false.
Proof.
  intros F M. exists (snd (loop_two_state k a b c fa fb)). rewrite loop_two_go_state.
  exact (loop_two_ends meas c fa fb F k a b M).
Qed.
