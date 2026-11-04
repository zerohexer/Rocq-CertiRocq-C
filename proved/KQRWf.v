(** Rocq's own measure recursion (Rocq-C-solution.md §4.5, step 56): [Program Fixpoint f x {measure (m x)} := body] is [Fix_sub] over [MR lt m].  A budget
    function [G] that runs the same body equals it at every budget above the measure, by induction on the [Acc] proof.  [fix_sub_eq]'s extensionality
    premise is not used, so neither functional extensionality nor proof irrelevance is. *)
From Stdlib Require Import ZArith Lia.
From Corelib Require Export Program.Wf.
From Stdlib Require Export Program.Utils.
From KQ Require Import KQRun.
From KQC Require KQMAuto.

Section W.
Variables (A : Type) (B : Type) (m : A -> nat) (wf : well_founded (MR lt m)).
Variable Fs : forall x : A, (forall y : {y : A | MR lt m y x}, B) -> B.
Variable G : nat -> A -> B.
Variable d : A -> B.
Hypothesis Hstep : forall k x h, (forall y, h y = (match k with O => d | S k' => G k' end) (proj1_sig y)) -> Fs x h = G k x.
Lemma fix_sub_budget_F : forall x (r : Acc (MR lt m) x) k, (m x <= k)%nat ->
  Fix_F_sub A (MR lt m) (fun _ => B) Fs x r = G k x.
Proof.
  fix IH 2. intros x r k Hk. destruct r as [a]. cbn [Fix_F_sub].
  apply Hstep. intros [y Hy]. cbn [proj1_sig]. destruct k as [|k'].
  - exfalso. unfold MR in Hy. lia.
  - apply IH. unfold MR in Hy. lia.
Qed.
Lemma fix_sub_budget : forall k x, (m x <= k)%nat -> Fix_sub A (MR lt m) wf (fun _ => B) Fs x = G k x.
Proof. intros k x Hk. unfold Fix_sub. apply fix_sub_budget_F. exact Hk. Qed.
End W.

(** a test as [Program] writes it: its branches take the proof of the test *)
Lemma convoy_b : forall (c : bool) (R : Type) (t : true = c -> R) (f : false = c -> R) (p q : R),
  (forall H : true = c, t H = p) -> (forall H : false = c, f H = q) ->
  (if c as a return a = c -> R then t else f) eq_refl = (if c then p else q).
Proof. intros [|] R t f p q Ht Hf; cbn; [apply Ht | apply Hf]. Qed.
(** a match on a counter likewise *)
Lemma convoy_n : forall (c : nat) (R : Type) (t : O = c -> R) (f : forall m, S m = c -> R) (p : R) (q : nat -> R),
  (forall H : O = c, t H = p) -> (forall m (H : S m = c), f m H = q m) ->
  (match c as a return a = c -> R with O => t | S m => f m end) eq_refl = (match c with O => p | S m => q m end).
Proof. intros [|n] R t f p q Ht Hf; cbn; [apply Ht | apply Hf]. Qed.

(** a pair taken apart likewise *)
Lemma convoy_p : forall (A C R : Type) (c : A * C) (t : forall a b, (a, b) = c -> R) (q : A -> C -> R),
  (forall a b (H : (a, b) = c), t a b H = q a b) ->
  (let (a, b) as z return z = c -> R := c in t a b) eq_refl = (let (a, b) := c in q a b).
Proof. intros A C R [a b] t q Ht; cbn; apply Ht. Qed.

(** [if dec c then .. else ..] likewise: [dec] is [sumbool_of_bool] *)
Lemma convoy_d : forall (c : bool) (R : Type) (t : c = true -> R) (f : c = false -> R) (p q : R),
  (forall H : c = true, t H = p) -> (forall H : c = false, f H = q) ->
  (match sumbool_of_bool c with left H => t H | right H => f H end) = (if c then p else q).
Proof. intros [|] R t f p q Ht Hf; cbn; [apply Ht | apply Hf]. Qed.

(** the premise: the tests walked, a recursive call where the hypothesis says *)
Ltac wf_step :=
  repeat (cbn beta iota zeta;
          first [ reflexivity
                | match goal with H : forall y, ?h y = _ |- context [?h ?y0] => rewrite (H y0); cbn [proj1_sig projT1 projT2] end
                | refine (convoy_d _ _ (fun H => _) (fun H => _) _ _ _ _); intro
                | refine (convoy_b _ _ _ _ _ _ _ _); intro
                | refine (convoy_n _ _ _ _ _ _ _ _); intros
                | refine (convoy_p _ _ _ _ _ _ _); intros
                | match goal with |- context [if ?c then _ else _] => destruct c end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | match goal with |- context [match ?c with pair _ _ => _ end] => destruct c end ]).

(** the budget of a measure on a machine number: above it whatever the number *)
Definition kq_budget : nat :=
  (kq_nat 1152921504606846976 + (kq_nat 1152921504606846976 + (kq_nat 1152921504606846976 + kq_nat 1152921504606846975)))%nat.
Lemma to_nat_le_budget : forall e : int, (Z.to_nat (Sint63.to_Z e) <= kq_budget)%nat.
Proof.
  intros x. unfold kq_budget.
  assert (A1 : Z.of_nat (kq_nat 1152921504606846976) = 1152921504606846976%Z) by (apply KQMAuto.kq_nat_val; cbv; split; discriminate).
  assert (A2 : Z.of_nat (kq_nat 1152921504606846975) = 1152921504606846975%Z) by (apply KQMAuto.kq_nat_val; cbv; split; discriminate).
  pose proof (Sint63.to_Z_bounded x) as [_ H].
  assert (M : (Sint63.to_Z Sint63.max_int = 4611686018427387903)%Z) by reflexivity. rewrite M in H.
  apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add, A1, A2. lia.
Qed.
