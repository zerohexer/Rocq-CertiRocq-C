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

(* ======================================================================================================================
   RECURSION WITH A MEASURE (wfix1 .. wfixm2 of lib/Loop.v).  Written once for any argument type A and result type B.

   A function `go k` (the loop with a budget k) is described by one equation: with one more budget it is F applied to itself with
   one less (what it gives with no budget is never reached once the budget is above the measure, so it is not mentioned).  F is the body of the function, with `rec` for the recursive call.  The
   function is well defined when F calls `rec` only at an argument of smaller measure m (the argument is in the domain P
   and the measure is not below 0); that is the termination argument, stated as `dec`:  F gives the same answer for two
   `rec`s that agree on every smaller argument.  Then
     - the budget does not matter once it is above the measure (wf_indep),
     - the loop satisfies the equation of the recursive function (wf_eq): the equation Program Fixpoint proves with `Fix_eq`,
     - the loop with the measure as its budget is that function (wf_wrapper_eq), and
     - properties of it are proved by induction on the measure (wf_ind), with no unfolding by hand. *)
Section WF.
Context {A B : Type} (F : (A -> B) -> A -> B) (go : nat -> A -> B) (m : A -> Z) (P : A -> Prop).
Hypothesis H1 : forall k x, go (S k) x = F (go k) x.

Definition dec : Prop :=
  forall (r1 r2 : A -> B) x, P x -> (forall y, P y -> (0 <= m y < m x)%Z -> r1 y = r2 y) -> F r1 x = F r2 x.

Lemma wf_indep : dec -> forall k1 k2 x, P x -> (0 <= m x)%Z -> (m x < Z.of_nat k1)%Z -> (m x < Z.of_nat k2)%Z -> go k1 x = go k2 x.
Proof.
  intros D k1. induction k1 as [|k1 IH]; intros k2 x Px M0 M1 M2; [cbn in M1; lia | ].
  destruct k2 as [|k2]; [cbn in M2; lia | ].
  rewrite !H1. apply D; [exact Px | ]. intros y Py [Y0 Y1]. apply IH; [exact Py | exact Y0 | | ];
    rewrite Nat2Z.inj_succ in *; lia.
Qed.

Lemma wf_eq : dec -> forall k x, P x -> (0 <= m x)%Z -> (m x < Z.of_nat k)%Z -> go k x = F (go k) x.
Proof.
  intros D k x Px M0 M1. destruct k as [|k]; [cbn in M1; lia | ].
  rewrite H1. apply D; [exact Px | ]. intros y Py [Y0 Y1]. apply wf_indep; [exact D | exact Py | exact Y0 | | ];
    rewrite Nat2Z.inj_succ in *; lia.
Qed.

(* the budget is a function of the argument, at least measure + 1 (below 2^60: what a budget can hold) *)
Variable fuel : A -> nat.
Hypothesis Hfuel : forall x, P x -> (0 <= m x)%Z -> (m x + 1 <= 2 ^ 60)%Z -> (m x + 1 <= Z.of_nat (fuel x))%Z.
Definition W (x : A) : B := go (fuel x) x.

Theorem wf_wrapper_eq : dec -> forall x, P x -> (0 <= m x)%Z -> (m x + 1 <= 2 ^ 60)%Z -> W x = F W x.
Proof.
  intros D x Px M0 M1. pose proof (Hfuel x Px M0 M1) as Fx. unfold W at 1.
  rewrite (wf_eq D (fuel x) x Px M0 ltac:(lia)). apply D; [exact Px | ]. intros y Py [Y0 Y1].
  unfold W. apply wf_indep; [exact D | exact Py | exact Y0 | lia | ].
  pose proof (Hfuel y Py Y0 ltac:(lia)) as Fy. lia.
Qed.

(* a property of the function proved by induction on the measure: if it holds of F's answer whenever it holds of rec's at the
   smaller arguments, it holds of the function *)
Theorem wf_ind (Q : A -> B -> Prop) : dec ->
  (forall x, P x -> (0 <= m x)%Z -> (m x + 1 <= 2 ^ 60)%Z ->
     forall r : A -> B, (forall y, P y -> (0 <= m y < m x)%Z -> Q y (r y)) -> Q x (F r x)) ->
  forall x, P x -> (0 <= m x)%Z -> (m x + 1 <= 2 ^ 60)%Z -> Q x (W x).
Proof.
  intros D S. assert (G : forall n : nat, forall x, P x -> (0 <= m x)%Z -> (m x + 1 <= 2 ^ 60)%Z -> m x = Z.of_nat n -> Q x (W x)).
  { induction n as [n IH] using lt_wf_ind. intros x Px M0 M1 Mn.
    rewrite (wf_wrapper_eq D x Px M0 M1). apply S; [exact Px | exact M0 | exact M1 | ].
    intros y Py [Y0 Y1]. apply (IH (Z.to_nat (m y))); [lia | exact Py | exact Y0 | lia | lia]. }
  intros x Px M0 M1. apply (G (Z.to_nat (m x)) x Px M0 M1). lia.
Qed.
End WF.
