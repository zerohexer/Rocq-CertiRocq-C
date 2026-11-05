(** Rocq's own measure recursion (Rocq-C-solution.md §4.5, step 56): [Program Fixpoint f x {measure (m x)} := body] is [Fix_sub] over [MR lt m].  A budget
    function [G] that runs the same body equals it at every budget above the measure, by induction on the [Acc] proof.  [fix_sub_eq]'s extensionality
    premise is not used, so neither functional extensionality nor proof irrelevance is. *)
From Stdlib Require Import ZArith Lia.
From Corelib Require Export Program.Wf.
From Stdlib Require Export Program.Utils.
From KQ Require Import KQRun.
From Corelib Require Import Numbers.Cyclic.Int63.CarryType.
From Stdlib Require Sint63 Uint63.
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

(** a budget in phases (step 58): a measure above a counter's range, the budget run out handing on to the phase before *)
Section P.
Variables (A : Type) (B : Type) (m : A -> nat).
Variable Fs : forall x : A, (forall y : {y : A | MR lt m y x}, B) -> B.
Variables (Gp : A -> B) (Kp : nat).
Hypothesis Hp : forall x (r : Acc (MR lt m) x), (m x <= Kp)%nat -> Fix_F_sub A (MR lt m) (fun _ => B) Fs x r = Gp x.
Variable G : nat -> A -> B.
Hypothesis Hstep : forall k x h, (forall y, h y = (match k with O => Gp | S k' => G k' end) (proj1_sig y)) -> Fs x h = G k x.
Lemma fix_sub_phase_F : forall x (r : Acc (MR lt m) x) k, (m x <= k + S Kp)%nat ->
  Fix_F_sub A (MR lt m) (fun _ => B) Fs x r = G k x.
Proof.
  fix IH 2. intros x r k Hk. destruct r as [a]. cbn [Fix_F_sub].
  apply Hstep. intros [y Hy]. cbn [proj1_sig]. destruct k as [|k'].
  - apply Hp. unfold MR in Hy. lia.
  - apply IH. unfold MR in Hy. lia.
Qed.
End P.

(** [Equations]' well-founded recursion (step 60): [FixWf] is [Fix] on the relation of the measure.  The same, on [Fix_F] *)
Section E.
Variables (A : Type) (B : Type) (R : A -> A -> Prop) (m : A -> nat).
Hypothesis Hm : forall a b, R a b -> (m a < m b)%nat.
Variable F : forall x : A, (forall y : A, R y x -> B) -> B.
Variable G : nat -> A -> B.
Variable d : A -> B.
Hypothesis Hstep : forall k x h, (forall y r, h y r = (match k with O => d | S k' => G k' end) y) -> F x h = G k x.
Lemma fix_wf_budget_F : forall x (r : Acc R x) k, (m x <= k)%nat -> Fix_F (fun _ => B) F r = G k x.
Proof.
  fix IH 2. intros x r k Hk. destruct r as [a]. cbn [Fix_F Acc_inv].
  apply Hstep. intros y r. destruct k as [|k'].
  - exfalso. pose proof (Hm _ _ r). lia.
  - apply IH. pose proof (Hm _ _ r). lia.
Qed.
End E.
Section EP.
Variables (A : Type) (B : Type) (R : A -> A -> Prop) (m : A -> nat).
Hypothesis Hm : forall a b, R a b -> (m a < m b)%nat.
Variable F : forall x : A, (forall y : A, R y x -> B) -> B.
Variables (Gp : A -> B) (Kp : nat).
Hypothesis Hp : forall x (r : Acc R x), (m x <= Kp)%nat -> Fix_F (fun _ => B) F r = Gp x.
Variable G : nat -> A -> B.
Hypothesis Hstep : forall k x h, (forall y r, h y r = (match k with O => Gp | S k' => G k' end) y) -> F x h = G k x.
Lemma fix_wf_phase_F : forall x (r : Acc R x) k, (m x <= k + S Kp)%nat -> Fix_F (fun _ => B) F r = G k x.
Proof.
  fix IH 2. intros x r k Hk. destruct r as [a]. cbn [Fix_F Acc_inv].
  apply Hstep. intros y r. destruct k as [|k'].
  - apply Hp. pose proof (Hm _ _ r). lia.
  - apply IH. pose proof (Hm _ _ r). lia.
Qed.
End EP.

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

(** a branch of a [Function]'s induction principle: its tests known, each recursive call's measure below by its [tcc] lemma [T] *)
Ltac fn_branch T :=
  repeat match goal with
         | z := _ |- _ => subst z
         | H : ?n = S _ |- _ => subst n
         | H : ?n = O |- _ => subst n
         | H : ?c = true |- context [?c] => rewrite H
         | H : ?c = false |- context [?c] => rewrite H
         end;
  cbn beta iota zeta;
  repeat match goal with
         | IH : forall kqk : nat, ?w <= kqk -> _ |- _ =>
             match goal with
             | kqh : ?m <= ?K |- _ =>
                 let L := fresh "kqL" in
                 assert (L : w < m) by (pose proof T as kqT; decompose [and] kqT; eauto);
                 match K with
                 | O => exfalso; lia
                 | S ?k => rewrite (IH k) by lia; clear IH L
                 end
             end
         end;
  try reflexivity.

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

(** a bound of a measure (step 58): the bounds of the machine numbers in it, then arithmetic *)
Lemma kq_a1 : Z.of_nat (kq_nat 1152921504606846976) = 1152921504606846976%Z.
Proof. apply KQMAuto.kq_nat_val; cbv; split; discriminate. Qed.
Lemma kq_a2 : Z.of_nat (kq_nat 1152921504606846975) = 1152921504606846975%Z.
Proof. apply KQMAuto.kq_nat_val; cbv; split; discriminate. Qed.
Lemma kq_budget_val : Z.of_nat kq_budget = 4611686018427387903%Z.
Proof. unfold kq_budget. rewrite !Nat2Z.inj_add, kq_a1, kq_a2. reflexivity. Qed.
Lemma sint_bounds : forall e : int, (-4611686018427387904 <= Sint63.to_Z e <= 4611686018427387903)%Z.
Proof.
  intros e. pose proof (Sint63.to_Z_bounded e) as [L H].
  assert (M : (Sint63.to_Z Sint63.max_int = 4611686018427387903)%Z) by reflexivity.
  assert (N : (Sint63.to_Z Sint63.min_int = -4611686018427387904)%Z) by reflexivity. lia.
Qed.
Lemma uint_bounds : forall e : int, (0 <= Uint63.to_Z e <= 9223372036854775807)%Z.
Proof. intros e. pose proof (Uint63.to_Z_bounded e) as [L H]. rewrite KQMAuto.wB_num in H. lia. Qed.
Lemma nat_div_le : forall a b : nat, (a / b <= a)%nat.
Proof. intros a [|b]; [simpl; lia | apply Nat.div_le_upper_bound; lia]. Qed.
Lemma nat_mod_le : forall a b : nat, (a mod b <= a)%nat.
Proof. intros a [|b]; [simpl; lia | apply Nat.mod_le; lia]. Qed.
Ltac bound_of W := match goal with |- _ <= ?b => change (W <= b) end.
Ltac bound_le :=
  pose proof kq_budget_val; pose proof kq_a1; pose proof kq_a2;
  repeat match goal with
         | |- context [Sint63.to_Z ?e] =>
             lazymatch goal with _ : (_ <= Sint63.to_Z e <= _)%Z |- _ => fail | _ => pose proof (sint_bounds e) end
         | |- context [Uint63.to_Z ?e] =>
             lazymatch goal with _ : (_ <= Uint63.to_Z e <= _)%Z |- _ => fail | _ => pose proof (uint_bounds e) end
         | |- context [Nat.log2 ?a] =>
             lazymatch goal with _ : (Nat.log2 a <= a)%nat |- _ => fail | _ => pose proof (Nat.log2_le_lin a (Nat.le_0_l a)) end
         | |- context [Nat.sqrt ?a] =>
             lazymatch goal with _ : (Nat.sqrt a <= a)%nat |- _ => fail | _ => pose proof (Nat.sqrt_le_lin a) end
         | |- context [Nat.div2 ?a] =>
             lazymatch goal with _ : (Nat.div2 a <= a)%nat |- _ => fail | _ => pose proof (Nat.div2_decr a a (le_n a)) end
         | |- context [Nat.div ?a ?b] =>
             lazymatch goal with _ : (Nat.div a b <= a)%nat |- _ => fail | _ => pose proof (nat_div_le a b) end
         | |- context [Nat.modulo ?a ?b] =>
             lazymatch goal with _ : (Nat.modulo a b <= a)%nat |- _ => fail | _ => pose proof (nat_mod_le a b) end
         end;
  lia.

(** the same, the budget in phases (step 58): the budget run out, the call of the phase before, its lemma [A0] *)
Ltac fn_branch_ph T WM A0 :=
  repeat match goal with
         | z := _ |- _ => subst z
         | H : ?n = S _ |- _ => subst n
         | H : ?n = O |- _ => subst n
         | H : ?c = true |- context [?c] => rewrite H
         | H : ?c = false |- context [?c] => rewrite H
         end;
  cbn beta iota zeta;
  repeat match goal with
         | IH : forall kqk : nat, ?w <= kqk + _ -> _ |- _ =>
             match goal with
             | kqh : ?m <= ?K + _ |- _ =>
                 let L := fresh "kqL" in
                 assert (L : w < m) by (pose proof T as kqT; decompose [and] kqT; eauto);
                 match K with
                 | O => clear IH
                 | S ?k => rewrite (IH k) by lia; clear IH L
                 end
             end
         end;
  repeat (rewrite A0 by (unfold WM, kq_budget in *; cbn beta in *; lia));
  try reflexivity.


(** a step of [Equations]' functional: a test through [inspect] or [dec], its equation written into the budget function's own test *)
Ltac eq_step pr :=
  repeat (cbv beta iota zeta; pr;
          first [ match goal with H : forall y r, ?h y r = _ |- context [?h ?y0 ?r0] => rewrite (H y0 r0); cbv beta iota zeta end
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | match goal with |- context [match ?i with exist _ _ _ => _ end] =>
                    let b := fresh "kqb" in let e := fresh "kqe" in destruct i as [b e]; revert e; destruct b; intro e end
                | match goal with |- context [match sumbool_of_bool ?c with left _ => _ | right _ => _ end] =>
                    let e := fresh "kqe" in destruct (sumbool_of_bool c) as [e|e] end
                | match goal with |- context [if ?c then _ else _] => destruct c end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | match goal with |- context [match ?c with pair _ _ => _ end] => destruct c end
                | reflexivity ]).

(** (step 64) the operations of Rocq's machine numbers that its own axioms define by others *)
Lemma kq_compares_def : forall x y : int, PrimInt63.compares x y = if PrimInt63.ltsb x y then Lt else if PrimInt63.eqb x y then Eq else Gt.
Proof.
  intros x y. rewrite Sint63Axioms.compare_spec.
  destruct (PrimInt63.ltsb x y) eqn:E1.
  - apply Sint63Axioms.ltb_spec in E1. exact E1.
  - destruct (PrimInt63.eqb x y) eqn:E2.
    + apply Uint63Axioms.eqb_correct in E2. subst y. apply Z.compare_refl.
    + apply Z.compare_gt_iff. apply Z.nle_gt. intros Hle.
      assert (Hlt : ~ (Sint63Axioms.to_Z x < Sint63Axioms.to_Z y)%Z).
      { intros H. apply Sint63Axioms.ltb_spec in H. rewrite H in E1. discriminate. }
      assert (Heq : Sint63Axioms.to_Z x = Sint63Axioms.to_Z y) by lia.
      assert (x = y) by (apply Sint63.to_Z_inj; exact Heq). subst y. rewrite Uint63.eqb_refl in E2. discriminate.
Qed.
Ltac prim_rw :=
  progress (rewrite ?Uint63Axioms.compare_def_spec, ?kq_compares_def, ?Uint63Axioms.addc_def_spec, ?Uint63Axioms.addcarryc_def_spec,
                    ?Uint63Axioms.subc_def_spec, ?Uint63Axioms.subcarryc_def_spec, ?Uint63Axioms.diveucl_def_spec, ?Uint63Axioms.addmuldiv_def_spec;
            unfold Uint63Axioms.compare_def, Uint63Axioms.addc_def, Uint63Axioms.addcarryc_def, Uint63Axioms.subc_def, Uint63Axioms.subcarryc_def,
                   Uint63Axioms.diveucl_def, Uint63Axioms.addmuldiv_def, Uint63Axioms.addcarry).
(** (step 61) a fixpoint with its own call under a choice in an operand, and the same with the choice floated out: equal at each counter, test by test *)
Ltac own_step IH :=
  repeat (cbn beta iota zeta;
          first [ prim_rw
                | progress (rewrite ?IH)
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | match goal with |- context [match ?c with pair _ _ => _ end] => destruct c end
                | reflexivity ]).

(** (step 61) a fixpoint with its own call on a counter deeper than the predecessor, and a budget function above it: equal at every budget above the counter *)
Ltac deep_step IH pr :=
  repeat (cbn beta iota zeta; pr;
          first [ exfalso; lia
                | progress (rewrite ?IH by lia)
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with pair _ _ => _ end] => destruct c end
                | reflexivity ]).

Definition kq_no_ih : True := I.
Ltac own_step0 :=
  repeat (cbn beta iota zeta;
          first [ prim_rw
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | match goal with |- context [match ?c with pair _ _ => _ end] => destruct c end
                | reflexivity ]).
