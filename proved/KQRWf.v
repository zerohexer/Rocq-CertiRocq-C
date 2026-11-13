(** Rocq's own measure recursion (Rocq-C-solution.md §4.5, step 56): [Program Fixpoint f x {measure (m x)} := body] is [Fix_sub] over [MR lt m].  A budget
    function [G] that runs the same body equals it at every budget above the measure, by induction on the [Acc] proof.  [fix_sub_eq]'s extensionality
    premise is not used, so neither functional extensionality nor proof irrelevance is. *)
From Stdlib Require Import ZArith Lia Btauto.
From Corelib Require Export Program.Wf.
From Stdlib Require Export Program.Utils.
From KQ Require Import KQRun.
From Corelib Require Import Numbers.Cyclic.Int63.CarryType.
From Stdlib Require Sint63 Uint63.
From Stdlib Require Arith.Compare_dec Arith.PeanoNat.
From KQC Require KQMAuto KQPrim.
From Stdlib Require Eqdep_dec.

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
  lazymatch goal with |- context [kq_budget] => pose proof kq_budget_val | _ => idtac end;
  lazymatch goal with |- context [kq_nat _] => pose proof kq_a1; pose proof kq_a2 | _ => idtac end;
  repeat match goal with
         | |- context [Sint63.to_Z ?e] =>
             lazymatch goal with _ : (_ <= Sint63.to_Z e <= _)%Z |- _ => fail | _ => pose proof (sint_bounds e) end
         | |- context [Uint63.to_Z ?e] =>
             lazymatch goal with _ : (_ <= Uint63.to_Z e <= _)%Z |- _ => fail | _ => pose proof (uint_bounds e) end
         | |- context [Nat.log2 ?a] =>
             lazymatch goal with _ : (Nat.log2 a <= a)%nat |- _ => fail | _ => pose proof (Nat.log2_le_lin a (Nat.le_0_l a)) end
         | |- context [Nat.sqrt ?a] =>
             lazymatch goal with _ : (Nat.sqrt a <= a)%nat |- _ => fail | _ => pose proof (Nat.sqrt_le_lin a) end
         | |- context [Init.Nat.div2 ?a] =>
             lazymatch goal with _ : (Init.Nat.div2 a <= a)%nat |- _ => fail | _ => pose proof (Nat.div2_decr a a (Nat.le_succ_diag_r a) : (Init.Nat.div2 a <= a)%nat) end
         | |- context [PeanoNat.Nat.div2 ?a] =>
             lazymatch goal with _ : (PeanoNat.Nat.div2 a <= a)%nat |- _ => fail | _ => pose proof (Nat.div2_decr a a (Nat.le_succ_diag_r a)) end
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
Lemma kq_d_eq : forall (T : Type) (n m : nat) (a b : T), (if PeanoNat.Nat.eq_dec n m then a else b) = (if Nat.eqb n m then a else b).
Proof. intros. destruct (PeanoNat.Nat.eq_dec n m) as [e|e]; [subst m; rewrite PeanoNat.Nat.eqb_refl | apply PeanoNat.Nat.eqb_neq in e; rewrite e]; reflexivity. Qed.
Lemma kq_d_lt : forall (T : Type) (n m : nat) (a b : T), (if Compare_dec.lt_dec n m then a else b) = (if Nat.ltb n m then a else b).
Proof. intros. destruct (Compare_dec.lt_dec n m) as [e|e]; [apply PeanoNat.Nat.ltb_lt in e | apply PeanoNat.Nat.ltb_nlt in e]; rewrite e; reflexivity. Qed.
Lemma kq_d_le : forall (T : Type) (n m : nat) (a b : T), (if Compare_dec.le_dec n m then a else b) = (if Nat.leb n m then a else b).
Proof. intros. destruct (Compare_dec.le_dec n m) as [e|e]; [apply PeanoNat.Nat.leb_le in e | apply PeanoNat.Nat.leb_nle in e]; rewrite e; reflexivity. Qed.
Lemma kq_d_gt : forall (T : Type) (n m : nat) (a b : T), (if Compare_dec.gt_dec n m then a else b) = (if Nat.ltb m n then a else b).
Proof. intros. destruct (Compare_dec.gt_dec n m) as [e|e]; [apply PeanoNat.Nat.ltb_lt in e | apply PeanoNat.Nat.ltb_nlt in e]; rewrite e; reflexivity. Qed.
Lemma kq_d_ge : forall (T : Type) (n m : nat) (a b : T), (if Compare_dec.ge_dec n m then a else b) = (if Nat.leb m n then a else b).
Proof. intros. destruct (Compare_dec.ge_dec n m) as [e|e]; [apply PeanoNat.Nat.leb_le in e | apply PeanoNat.Nat.leb_nle in e]; rewrite e; reflexivity. Qed.
Lemma kq_d_lel : forall (T : Type) (n m : nat) (a b : T), (if Compare_dec.le_lt_dec n m then a else b) = (if Nat.leb n m then a else b).
Proof. intros. destruct (Compare_dec.le_lt_dec n m) as [e|e]; [apply PeanoNat.Nat.leb_le in e | apply PeanoNat.Nat.leb_gt in e]; rewrite e; reflexivity. Qed.
Lemma kq_d_leg : forall (T : Type) (n m : nat) (a b : T), (if Compare_dec.le_gt_dec n m then a else b) = (if Nat.leb n m then a else b).
Proof. intros. destruct (Compare_dec.le_gt_dec n m) as [e|e]; [apply PeanoNat.Nat.leb_le in e | apply PeanoNat.Nat.leb_gt in e]; rewrite e; reflexivity. Qed.
Lemma kq_d_eqs : forall (T : Type) (i j : int) (a b : T), (if Uint63.eqs i j then a else b) = (if PrimInt63.eqb i j then a else b).
Proof. intros. destruct (Uint63.eqs i j) as [e|e]; [subst j; rewrite Uint63.eqb_refl | apply Uint63.eqb_false_spec in e; rewrite e]; reflexivity. Qed.
Lemma kq_compare_nat : forall n m : nat, Nat.compare n m = (if Nat.eqb n m then Eq else if Nat.ltb n m then Lt else Gt).
Proof.
  intros n m. destruct (Nat.eqb n m) eqn:E1; [apply PeanoNat.Nat.eqb_eq in E1; subst m; apply PeanoNat.Nat.compare_refl|].
  apply PeanoNat.Nat.eqb_neq in E1. destruct (Nat.ltb n m) eqn:E2.
  - apply PeanoNat.Nat.ltb_lt in E2. apply PeanoNat.Nat.compare_lt_iff. exact E2.
  - apply PeanoNat.Nat.ltb_nlt in E2. apply PeanoNat.Nat.compare_gt_iff. lia.
Qed.
Ltac prim_rw :=
  progress (rewrite ?kq_d_eq, ?kq_d_lt, ?kq_d_le, ?kq_d_gt, ?kq_d_ge, ?kq_d_lel, ?kq_d_leg, ?kq_d_eqs, ?kq_compare_nat, ?KQPrim.kq_mulc_def, ?KQPrim.kq_h0_eq, ?KQPrim.kq_t0_eq, ?Uint63Axioms.compare_def_spec, ?kq_compares_def, ?Uint63Axioms.addc_def_spec, ?Uint63Axioms.addcarryc_def_spec,
                    ?Uint63Axioms.subc_def_spec, ?Uint63Axioms.subcarryc_def_spec, ?Uint63Axioms.diveucl_def_spec, ?Uint63Axioms.addmuldiv_def_spec;
            unfold Uint63Axioms.compare_def, Uint63Axioms.addc_def, Uint63Axioms.addcarryc_def, Uint63Axioms.subc_def, Uint63Axioms.subcarryc_def,
                   Uint63Axioms.diveucl_def, Uint63Axioms.addmuldiv_def, Uint63Axioms.addcarry).
(** (step 73) [diveucl_21 a b c] where a test has shown [a < c], or the numbers are written, and (step 74) [divs a b] where a test has shown it
    is not the smallest number over -1, or a number is written: the kit's function *)
Ltac kq_part := first [ match goal with |- context [PrimInt63.diveucl_21 _ _ _] => idtac end | match goal with |- context [PrimInt63.divs _ _] => idtac end ].
Ltac kq_guard :=
  kq_part;
  match goal with
  | e : andb ?x ?y = true |- _ => apply Bool.andb_true_iff in e; destruct e
  | e : orb ?x ?y = false |- _ => apply Bool.orb_false_iff in e; destruct e
  | e : negb ?x = true |- _ => apply Bool.negb_true_iff in e
  | e : negb ?x = false |- _ => apply Bool.negb_false_iff in e
  | e : PrimInt63.ltb ?a ?c = true |- context [PrimInt63.diveucl_21 ?a ?b ?c] => rewrite (KQPrim.kq_d21_eq a b c e)
  | e : PrimInt63.leb ?c ?a = false |- context [PrimInt63.diveucl_21 ?a ?b ?c] => rewrite (KQPrim.kq_d21_le a b c e)
  | |- context [PrimInt63.diveucl_21 ?a ?b ?c] => rewrite (KQPrim.kq_d21_eq a b c (eq_refl true))
  | e : PrimInt63.eqb ?b _ = false |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_r a b e)
  | e : PrimInt63.eqb _ ?b = false |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_reqs a b e)
  | e : PrimInt63.ltsb _ ?b = true |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_rlt a b e)
  | e : PrimInt63.lesb _ ?b = true |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_rle a b e)
  | e : PrimInt63.ltsb ?b _ = false |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_rglt a b e)
  | e : PrimInt63.lesb ?b _ = false |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_rgle a b e)
  | e : PrimInt63.eqb ?a _ = false |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_l a b e)
  | e : PrimInt63.eqb _ ?a = false |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_leqs a b e)
  | e : PrimInt63.ltsb _ ?a = true |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_llt a b e)
  | e : PrimInt63.lesb _ ?a = true |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_lle a b e)
  | e : PrimInt63.ltsb ?a _ = false |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_lglt a b e)
  | e : PrimInt63.lesb ?a _ = false |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_lgle a b e)
  | |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_r a b (eq_refl false))
  | |- context [PrimInt63.divs ?a ?b] => rewrite (KQPrim.kq_divs_l a b (eq_refl false))
  | |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e
  end.
(** (step 69) a program's lemmas of what is read in another form: [kitc.py] sets it *)
Ltac kq_rw := fail.
(** (step 76) what a program's rows name, written out: a hook [kitc.py] sets *)
Ltac kq_unf := idtac.
(** (step 76) a function made by tactics: [destruct t eqn:E] leaves a match on [t] applied to [eq_refl], its branches' proofs naming [t], so that [t] cannot be taken apart in the goal; it is told apart beside it *)
Lemma convoy_true : forall (t : bool) (T : Type) (f : t = true -> T) (g : t = false -> T) (e : t = true),
  (match t as b return t = b -> T with true => f | false => g end) eq_refl = f e.
Proof.
  intros t T f g e. revert f g e. destruct t; intros f g e; [| discriminate e].
  rewrite (Eqdep_dec.UIP_refl_bool true e). reflexivity.
Qed.
Lemma convoy_false : forall (t : bool) (T : Type) (f : t = true -> T) (g : t = false -> T) (e : t = false),
  (match t as b return t = b -> T with true => f | false => g end) eq_refl = g e.
Proof.
  intros t T f g e. revert f g e. destruct t; intros f g e; [discriminate e |].
  rewrite (Eqdep_dec.UIP_refl_bool false e). reflexivity.
Qed.
Lemma bool_cases : forall t : bool, {t = true} + {t = false}.
Proof. intros [|]; [left | right]; reflexivity. Defined.
Ltac kq_convoy :=
  match goal with
  | |- context [(match ?t with true => ?f | false => ?g end) (@eq_refl _ _)] =>
      let e := fresh "kqe" in
      destruct (bool_cases t) as [e | e]; [rewrite (convoy_true t _ f g e); try rewrite e | rewrite (convoy_false t _ f g e); try rewrite e]
  end.
(** (step 78) what leaves the cells of the slot block as they are: the laws of the memory, each at block 63 *)
Lemma fr_oth : forall h i j, PrimInt63.eqb h 63 = false -> KQ.KQSpec.other h i 63 j = true.
Proof. intros h i j E. unfold KQ.KQSpec.other. rewrite E. reflexivity. Qed.
Lemma fr_upd : forall h i v j s, PrimInt63.eqb h 63 = false -> rd 63 j (upd h i v s) = rd 63 j s.
Proof. intros h i v j s E. exact (KQ.KQSpec.rd_upd_ne KQ.KQSpec.real KQ.KQSpec.real_laws h i 63 j v s (fr_oth h i j E)). Qed.
Lemma fr_upd32 : forall h i v j s, rd 63 j (upd32 h i v s) = rd 63 j s.
Proof. intros. exact (KQ.KQSpec.rd_upd32 KQ.KQSpec.real KQ.KQSpec.real_laws h i v 63 j s). Qed.
Lemma fr_upd8 : forall h i v j s, rd 63 j (upd8 h i v s) = rd 63 j s.
Proof. intros. unfold upd8. cbv zeta. apply fr_upd32. Qed.
Lemma fr_upd16 : forall h i v j s, rd 63 j (upd16 h i v s) = rd 63 j s.
Proof. intros. unfold upd16. rewrite !fr_upd8. reflexivity. Qed.
Lemma fr_grow : forall h n j s, rd 63 j (kq_grow h n s) = rd 63 j s.
Proof. intros. exact (KQ.KQSpec.rd_grow KQ.KQSpec.real KQ.KQSpec.real_laws h n 63 j s). Qed.
Lemma fr_load : forall w a h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_load w a h i s) = rd 63 j s.
Proof.
  intros w a h i j s E. apply (KQ.KQSpec.load_rd KQ.KQSpec.real KQ.KQSpec.real_laws w a h i 63 j s (fr_oth h i j E)).
  rewrite (fr_oth h _ j E). apply Bool.orb_true_r.
Qed.
Lemma fr_aload : forall w a h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_aload w a h i s) = rd 63 j s.
Proof.
  intros w a h i j s E. apply (KQ.KQSpec.aload_rd KQ.KQSpec.real KQ.KQSpec.real_laws w a h i 63 j s (fr_oth h i j E)).
  rewrite (fr_oth h _ j E). apply Bool.orb_true_r.
Qed.
Lemma fr_store : forall w a v j s, rd 63 j (hw_store w a v s) = rd 63 j s.
Proof. intros. exact (KQ.KQSpec.store_rd KQ.KQSpec.real KQ.KQSpec.real_laws w a v 63 j s). Qed.
Lemma fr_store64 : forall a lo hi j s, rd 63 j (hw_store64 a lo hi s) = rd 63 j s.
Proof. intros. exact (KQ.KQSpec.store64_rd KQ.KQSpec.real KQ.KQSpec.real_laws a lo hi 63 j s). Qed.
Lemma fr_astore : forall w a v j s, rd 63 j (hw_astore w a v s) = rd 63 j s.
Proof. intros. exact (KQ.KQSpec.astore_rd KQ.KQSpec.real KQ.KQSpec.real_laws w a v 63 j s). Qed.
Lemma fr_astore64 : forall a lo hi j s, rd 63 j (hw_astore64 a lo hi s) = rd 63 j s.
Proof. intros. exact (KQ.KQSpec.astore64_rd KQ.KQSpec.real KQ.KQSpec.real_laws a lo hi 63 j s). Qed.
Lemma fr_fence : forall k j s, rd 63 j (hw_fence k s) = rd 63 j s.
Proof. intros. exact (KQ.KQSpec.fence_rd KQ.KQSpec.real KQ.KQSpec.real_laws k 63 j s). Qed.
Lemma fr_atomic : forall op w a v h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_atomic op w a v h i s) = rd 63 j s.
Proof. intros op w a v h i j s E. exact (KQ.KQSpec.atomic_rd KQ.KQSpec.real KQ.KQSpec.real_laws op w a v h i 63 j s (fr_oth h i j E)). Qed.
Lemma fr_atomic64 : forall op a lo hi h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_atomic64 op a lo hi h i s) = rd 63 j s.
Proof. intros op a lo hi h i j s E. exact (KQ.KQSpec.atomic64_rd KQ.KQSpec.real KQ.KQSpec.real_laws op a lo hi h i 63 j s (fr_oth h i j E) (fr_oth h _ j E)). Qed.
Lemma fr_cas : forall w a o n h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_cas w a o n h i s) = rd 63 j s.
Proof. intros w a o n h i j s E. exact (KQ.KQSpec.cas_rd KQ.KQSpec.real KQ.KQSpec.real_laws w a o n h i 63 j s (fr_oth h i j E) (fr_oth h _ j E)). Qed.
Lemma fr_cas64 : forall a ol oh nl nh h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_cas64 a ol oh nl nh h i s) = rd 63 j s.
Proof. intros a ol oh nl nh h i j s E. exact (KQ.KQSpec.cas64_rd KQ.KQSpec.real KQ.KQSpec.real_laws a ol oh nl nh h i 63 j s (fr_oth h i j E) (fr_oth h _ j E) (fr_oth h _ j E)). Qed.
Lemma fr_copy_up : forall k d x h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_copy_up k d x h i s) = rd 63 j s.
Proof.
  induction k as [|k IH]; intros d x h i j s E; cbn [hw_copy_up]; [reflexivity|]. cbv zeta.
  rewrite (IH _ _ _ _ _ _ E), fr_store, (fr_load _ _ _ _ _ _ E). reflexivity.
Qed.
Lemma fr_copy_down : forall k d x h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_copy_down k d x h i s) = rd 63 j s.
Proof.
  induction k as [|k IH]; intros d x h i j s E; cbn [hw_copy_down]; [reflexivity|]. cbv zeta.
  rewrite (IH _ _ _ _ _ _ E), fr_store, (fr_load _ _ _ _ _ _ E). reflexivity.
Qed.
Lemma fr_copy : forall d x n h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_copy d x n h i s) = rd 63 j s.
Proof.
  intros d x n h i j s E. unfold hw_copy.
  destruct (andb (PrimInt63.ltb (PrimInt63.sub d x) n) (negb (PrimInt63.eqb d x))); [apply fr_copy_down | apply fr_copy_up]; exact E.
Qed.
Lemma fr_fill_go : forall k d b j s, rd 63 j (hw_fill_go k d b s) = rd 63 j s.
Proof.
  induction k as [|k IH]; intros d b j s; cbn [hw_fill_go]; [reflexivity|].
  rewrite IH, fr_store. reflexivity.
Qed.
Lemma fr_fill : forall d b n j s, rd 63 j (hw_fill d b n s) = rd 63 j s.
Proof. intros. unfold hw_fill. apply fr_fill_go. Qed.
Lemma fr_cmp_go : forall k x y h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_cmp_go k x y h i s) = rd 63 j s.
Proof.
  induction k as [|k IH]; intros x y h i j s E; cbn [hw_cmp_go]; [apply (fr_upd _ _ _ _ _ E)|]. cbv zeta.
  destruct (PrimInt63.ltb _ _); [|destruct (PrimInt63.ltb _ _)];
    [rewrite (fr_upd _ _ _ _ _ E) | rewrite (fr_upd _ _ _ _ _ E) | rewrite (IH _ _ _ _ _ _ E)];
    rewrite !(fr_load _ _ _ _ _ _ E); reflexivity.
Qed.
Lemma fr_cmp : forall x y n h i j s, PrimInt63.eqb h 63 = false -> rd 63 j (hw_cmp x y n h i s) = rd 63 j s.
Proof. intros x y n h i j s E. unfold hw_cmp. apply (fr_cmp_go _ _ _ _ _ _ _ E). Qed.
(** (step 79) a block's number written, or a parameter the function's lemma takes as not 63 *)
Ltac kq_nc_side := fail.
Ltac nc_lia := lia.
Ltac vm_side := first [ reflexivity | assumption | kq_nc_side ].
Ltac fr_mem :=
  first [ rewrite fr_upd by vm_side | rewrite fr_upd32 | rewrite fr_upd8 | rewrite fr_upd16 | rewrite fr_grow
        | rewrite fr_load by vm_side | rewrite fr_aload by vm_side | rewrite fr_store | rewrite fr_store64 | rewrite fr_astore | rewrite fr_astore64 | rewrite fr_fence
        | rewrite fr_atomic by vm_side | rewrite fr_atomic64 by vm_side | rewrite fr_cas by vm_side | rewrite fr_cas64 by vm_side
        | rewrite fr_copy by vm_side | rewrite fr_fill | rewrite fr_cmp by vm_side ].
(** a program's lemmas that a function leaves the slot block alone: [kitc.py] sets it *)
Ltac kq_fr := fail.
(** a cell of the slot block: the block's room, a number in it *)
Definition slot_lit (W : Z) (j : int) : bool := andb (Z.leb 0 (Sint63.to_Z j)) (Z.ltb (Sint63.to_Z j + 1) W).
Lemma slot_eq : forall (W : Z), (W <= Sint63.to_Z (KQ.KQBound.kq_len 63) + 1)%Z -> forall j v s, slot_lit W j = true ->
  rd 63 j (upd 63 j v s) = v.
Proof.
  intros W Hr j v s L. apply andb_prop in L. destruct L as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
  apply (KQ.KQSpec.rd_upd_eq KQ.KQSpec.real KQ.KQSpec.real_laws).
  unfold KQ.KQSpec.cell. cbn [KQ.KQSpec.Size KQ.KQSpec.real]. pose proof (KQMAuto.size_ge_len 63%uint63 s) as Hs.
  assert (E1 : PrimInt63.lesb 0%uint63 j = true) by (apply (proj2 (KQ.KQSpec.le_Z _ _)); exact L1).
  assert (E2 : PrimInt63.ltsb j (kq_size 63%uint63 s) = true) by (apply (proj2 (KQ.KQSpec.lt_Z _ _)); lia).
  rewrite E1, E2. reflexivity.
Qed.
Lemma slot_ne : forall i j v s, PrimInt63.eqb i j = false -> rd 63 j (upd 63 i v s) = rd 63 j s.
Proof.
  intros i j v s E. apply (KQ.KQSpec.rd_upd_ne KQ.KQSpec.real KQ.KQSpec.real_laws).
  unfold KQ.KQSpec.other. rewrite E, Bool.andb_false_r. reflexivity.
Qed.
Lemma upd_same : forall i o m, rd 63 i m = o -> upd 63 i o m = m.
Proof. intros i o m E. rewrite <- E. apply KQMAuto.upd_rd_id_r. Qed.
(** a call's pair taken apart as its two parts, so that the same call anywhere is the same two parts and what is known of the call applies to them *)
Ltac vm_head t := match t with ?f _ => vm_head f | _ => t end.
Ltac vm_call_pair :=
  match goal with |- context [match ?c with pair _ _ => _ end] =>
    let h := vm_head c in
    first [ is_fix h; rewrite (surjective_pairing c)
          | lazymatch c with context [match _ with _ => _ end] => fail | PrimInt63.diveucl_21 _ _ _ => fail | pair _ _ => fail | _ => rewrite (surjective_pairing c) end ] end.
(** the value of a call taken apart once *)
Ltac vm_case :=
  match goal with
  | e : fst ?c = _ |- context [fst ?c] => rewrite e
  | |- context [match fst ?c with _ => _ end] =>
      first [ let h := vm_head c in is_fix h
            | lazymatch c with context [match _ with _ => _ end] => fail | _ => idtac end ];
      let e := fresh "kqe" in destruct (fst c) eqn:e
  end.
Ltac vm_slot :=
  first [ match goal with Hr : (_ <= Sint63.to_Z (KQ.KQBound.kq_len 63) + 1)%Z |- _ => rewrite (slot_eq _ Hr) by reflexivity end
        | rewrite slot_ne by reflexivity ].
Ltac fr_rd := first [ vm_slot | fr_mem | kq_fr ].
(** a cell written back with what it held *)
Ltac vm_restore :=
  match goal with |- context [upd 63 ?i ?o ?m] =>
    rewrite (upd_same i o m) by (repeat fr_rd; reflexivity) end.
(** a test of two written numbers: what a value's tag gives when it is known *)
Ltac vm_lit :=
  match goal with |- context [PrimInt63.eqb ?x ?y] =>
    let r := eval cbv in (PrimInt63.eqb x y) in
    lazymatch r with
    | true => change (PrimInt63.eqb x y) with true
    | false => change (PrimInt63.eqb x y) with false
    end end.
(** (step 82) a counter as a number, at every counter: the machine's numbers are modulo [wB] *)
Lemma nr_O : Uint63.of_Z (Z.of_nat 0) = 0%uint63.
Proof. reflexivity. Qed.
Lemma nr_S : forall n, Uint63.of_Z (Z.of_nat (S n)) = PrimInt63.add (Uint63.of_Z (Z.of_nat n)) 1%uint63.
Proof.
  intros n. apply Uint63.to_Z_inj. rewrite Uint63.add_spec, !Uint63.of_Z_spec.
  rewrite Nat2Z.inj_succ. change (Uint63.to_Z 1%uint63) with 1%Z. unfold Z.succ. rewrite Z.add_mod_idemp_l by (compute; discriminate). reflexivity.
Qed.
Lemma nr_add : forall a b, Uint63.of_Z (Z.of_nat (a + b)) = PrimInt63.add (Uint63.of_Z (Z.of_nat a)) (Uint63.of_Z (Z.of_nat b)).
Proof.
  intros a b. apply Uint63.to_Z_inj. rewrite Uint63.add_spec, !Uint63.of_Z_spec.
  rewrite Nat2Z.inj_add. apply Z.add_mod. compute; discriminate.
Qed.
Lemma nr_mul : forall a b, Uint63.of_Z (Z.of_nat (a * b)) = PrimInt63.mul (Uint63.of_Z (Z.of_nat a)) (Uint63.of_Z (Z.of_nat b)).
Proof.
  intros a b. apply Uint63.to_Z_inj. rewrite Uint63.mul_spec, !Uint63.of_Z_spec.
  rewrite Nat2Z.inj_mul. apply Z.mul_mod. compute; discriminate.
Qed.
(** (step 101) a row's bit operations: the machine's, the same modulo a word at every counter (their low 63 bits are those of the
    operands' low 63 bits), so no bound is asked; [Nat.ldiff] the [land] of the first and the [lxor] of the second with the 63 ones *)
Lemma nr_nbit : forall a n, Nat.testbit a n = Z.testbit (Z.of_nat a) (Z.of_nat n).
Proof.
  intros a n. pose proof (Nat.testbit_spec' a n) as Hn. pose proof (Z.testbit_spec' (Z.of_nat a) (Z.of_nat n) (Nat2Z.is_nonneg n)) as Hz.
  apply (f_equal Z.of_nat) in Hn. rewrite Nat2Z.inj_mod, Nat2Z.inj_div, Nat2Z.inj_pow in Hn. change (Z.of_nat 2) with 2%Z in Hn.
  rewrite <- Hz in Hn. destruct (Nat.testbit a n), (Z.testbit (Z.of_nat a) (Z.of_nat n)); cbn in Hn; congruence.
Qed.
Lemma nr_nbits : forall x z, (forall n, Nat.testbit x n = Z.testbit z (Z.of_nat n)) -> Z.of_nat x = z.
Proof. intros x z H. apply Z.bits_inj'. intros n Hn. rewrite <- (Z2Nat.id n Hn), <- H. symmetry. apply nr_nbit. Qed.

Lemma nr_zland : forall a b, Z.of_nat (Nat.land a b) = Z.land (Z.of_nat a) (Z.of_nat b).
Proof. intros a b. apply nr_nbits. intros n. rewrite Nat.land_spec, Z.land_spec, !nr_nbit. reflexivity. Qed.
Lemma nr_zlor : forall a b, Z.of_nat (Nat.lor a b) = Z.lor (Z.of_nat a) (Z.of_nat b).
Proof. intros a b. apply nr_nbits. intros n. rewrite Nat.lor_spec, Z.lor_spec, !nr_nbit. reflexivity. Qed.
Lemma nr_zlxor : forall a b, Z.of_nat (Nat.lxor a b) = Z.lxor (Z.of_nat a) (Z.of_nat b).
Proof. intros a b. apply nr_nbits. intros n. rewrite Nat.lxor_spec, Z.lxor_spec, !nr_nbit. reflexivity. Qed.
Lemma nr_mod63 : forall z, (z mod 9223372036854775808 = Z.land z (Z.ones 63))%Z.
Proof. intros z. rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac nr_bits63 := apply Z.bits_inj'; intros i Hi;
  repeat (rewrite Z.land_spec || rewrite Z.lor_spec || rewrite Z.lxor_spec);
  destruct (Z.ltb_spec i 63); [rewrite !Z.ones_spec_low by lia | rewrite !Z.ones_spec_high by lia]; btauto.
Lemma nr_land : forall a b, Uint63.of_Z (Z.of_nat (Nat.land a b)) = PrimInt63.land (Uint63.of_Z (Z.of_nat a)) (Uint63.of_Z (Z.of_nat b)).
Proof. intros a b. apply Uint63.to_Z_inj. rewrite Uint63.land_spec', !Uint63.of_Z_spec, !nr_mod63, nr_zland. nr_bits63. Qed.
Lemma nr_lor : forall a b, Uint63.of_Z (Z.of_nat (Nat.lor a b)) = PrimInt63.lor (Uint63.of_Z (Z.of_nat a)) (Uint63.of_Z (Z.of_nat b)).
Proof. intros a b. apply Uint63.to_Z_inj. rewrite Uint63.lor_spec', !Uint63.of_Z_spec, !nr_mod63, nr_zlor. nr_bits63. Qed.
Lemma nr_lxor : forall a b, Uint63.of_Z (Z.of_nat (Nat.lxor a b)) = PrimInt63.lxor (Uint63.of_Z (Z.of_nat a)) (Uint63.of_Z (Z.of_nat b)).
Proof. intros a b. apply Uint63.to_Z_inj. rewrite Uint63.lxor_spec', !Uint63.of_Z_spec, !nr_mod63, nr_zlxor. nr_bits63. Qed.
Lemma nr_zldiff : forall a b, Z.of_nat (Nat.ldiff a b) = Z.ldiff (Z.of_nat a) (Z.of_nat b).
Proof. intros a b. apply nr_nbits. intros n. rewrite Nat.ldiff_spec, Z.ldiff_spec, !nr_nbit. reflexivity. Qed.
Lemma nr_ldiff : forall a b, Uint63.of_Z (Z.of_nat (Nat.ldiff a b)) =
  PrimInt63.land (Uint63.of_Z (Z.of_nat a)) (PrimInt63.lxor (Uint63.of_Z (Z.of_nat b)) (Uint63.of_Z 9223372036854775807)).
Proof.
  intros a b. apply Uint63.to_Z_inj. rewrite Uint63.land_spec', Uint63.lxor_spec', !Uint63.of_Z_spec, !nr_mod63, nr_zldiff.
  change 9223372036854775807%Z with (Z.ones 63).
  apply Z.bits_inj'; intros i Hi. repeat (rewrite Z.land_spec || rewrite Z.lxor_spec || rewrite Z.ldiff_spec).
  destruct (Z.ltb_spec i 63); [rewrite !Z.ones_spec_low by lia | rewrite !Z.ones_spec_high by lia]; btauto.
Qed.
(** only as written: a function of the shape of [Nat.add] is [Nat.add] up to conversion *)
(** (step 105) a number written from 5000 on ([Nat.of_num_uint] of its digits), its value in [Z]: step 94's [nu_z] of [KQR.v], which this
    file comes before, and its proof, with no axiom; [lia] given it, where the number in unary would be the number's size *)
Fixpoint nr_du_z (d : Decimal.uint) (acc : Z) : Z :=
  match d with
  | Decimal.Nil => acc | Decimal.D0 d => nr_du_z d (10 * acc) | Decimal.D1 d => nr_du_z d (10 * acc + 1) | Decimal.D2 d => nr_du_z d (10 * acc + 2)
  | Decimal.D3 d => nr_du_z d (10 * acc + 3) | Decimal.D4 d => nr_du_z d (10 * acc + 4) | Decimal.D5 d => nr_du_z d (10 * acc + 5)
  | Decimal.D6 d => nr_du_z d (10 * acc + 6) | Decimal.D7 d => nr_du_z d (10 * acc + 7) | Decimal.D8 d => nr_du_z d (10 * acc + 8)
  | Decimal.D9 d => nr_du_z d (10 * acc + 9)
  end%Z.
Fixpoint nr_hu_z (d : Hexadecimal.uint) (acc : Z) : Z :=
  match d with
  | Hexadecimal.Nil => acc | Hexadecimal.D0 d => nr_hu_z d (16 * acc) | Hexadecimal.D1 d => nr_hu_z d (16 * acc + 1)
  | Hexadecimal.D2 d => nr_hu_z d (16 * acc + 2) | Hexadecimal.D3 d => nr_hu_z d (16 * acc + 3) | Hexadecimal.D4 d => nr_hu_z d (16 * acc + 4)
  | Hexadecimal.D5 d => nr_hu_z d (16 * acc + 5) | Hexadecimal.D6 d => nr_hu_z d (16 * acc + 6) | Hexadecimal.D7 d => nr_hu_z d (16 * acc + 7)
  | Hexadecimal.D8 d => nr_hu_z d (16 * acc + 8) | Hexadecimal.D9 d => nr_hu_z d (16 * acc + 9) | Hexadecimal.Da d => nr_hu_z d (16 * acc + 10)
  | Hexadecimal.Db d => nr_hu_z d (16 * acc + 11) | Hexadecimal.Dc d => nr_hu_z d (16 * acc + 12) | Hexadecimal.Dd d => nr_hu_z d (16 * acc + 13)
  | Hexadecimal.De d => nr_hu_z d (16 * acc + 14) | Hexadecimal.Df d => nr_hu_z d (16 * acc + 15)
  end%Z.
Definition nr_nu_z (u : Number.uint) : Z := match u with Number.UIntDecimal d => nr_du_z d 0 | Number.UIntHexadecimal d => nr_hu_z d 0 end.
Lemma nr_du_z_ok : forall d acc, Z.of_nat (Nat.of_uint_acc d acc) = nr_du_z d (Z.of_nat acc).
Proof. induction d; intros acc; cbn [Nat.of_uint_acc nr_du_z]; try rewrite IHd; f_equal; rewrite ?Nat.tail_mul_spec; lia. Qed.
Lemma nr_hu_z_ok : forall d acc, Z.of_nat (Nat.of_hex_uint_acc d acc) = nr_hu_z d (Z.of_nat acc).
Proof. induction d; intros acc; cbn [Nat.of_hex_uint_acc nr_hu_z]; try rewrite IHd; f_equal; rewrite ?Nat.tail_mul_spec; lia. Qed.
Lemma nr_nu_z_ok : forall u, Z.of_nat (Nat.of_num_uint u) = nr_nu_z u.
Proof. intros [d|d]; cbn [Nat.of_num_uint nr_nu_z Nat.of_uint Nat.of_hex_uint]; [apply (nr_du_z_ok d 0) | apply (nr_hu_z_ok d 0)]. Qed.
Ltac nr_numf :=
  repeat match goal with
  | |- context [Nat.of_num_uint ?u] =>
      lazymatch goal with _ : Z.of_nat (Nat.of_num_uint u) = _ |- _ => fail
      | _ => let v := eval vm_compute in (nr_nu_z u) in pose proof (nr_nu_z_ok u : Z.of_nat (Nat.of_num_uint u) = v) end
  end.
Lemma nr_ofnum : forall u, Uint63.of_Z (Z.of_nat (Nat.of_num_uint u)) = Uint63.of_Z (nr_nu_z u).
Proof. intros u. rewrite nr_nu_z_ok. reflexivity. Qed.
Ltac nr_numeral a := lazymatch a with O => idtac | S ?b => nr_numeral b end.
Ltac kq_nr :=
  match goal with
  | |- context [Uint63.of_Z (Z.of_nat (Nat.of_num_uint ?u))] =>
      rewrite (nr_ofnum u); let w := eval vm_compute in (Uint63.of_Z (nr_nu_z u)) in change (Uint63.of_Z (nr_nu_z u)) with w
  | |- context [Uint63.of_Z (Z.of_nat (S ?a))] =>
      nr_numeral a; let v := eval vm_compute in (Uint63.of_Z (Z.of_nat (S a))) in change (Uint63.of_Z (Z.of_nat (S a))) with v
  | |- context [Uint63.of_Z (Z.of_nat (S ?a))] => rewrite (nr_S a)
  | |- context [Uint63.of_Z (Z.of_nat (Nat.add ?a ?b))] => rewrite (nr_add a b)
  | |- context [Uint63.of_Z (Z.of_nat (Nat.mul ?a ?b))] => rewrite (nr_mul a b)
  | |- context [Uint63.of_Z (Z.of_nat (Nat.land ?a ?b))] => rewrite (nr_land a b)
  | |- context [Uint63.of_Z (Z.of_nat (Nat.lor ?a ?b))] => rewrite (nr_lor a b)
  | |- context [Uint63.of_Z (Z.of_nat (Nat.lxor ?a ?b))] => rewrite (nr_lxor a b)
  | |- context [Uint63.of_Z (Z.of_nat (Nat.ldiff ?a ?b))] => rewrite (nr_ldiff a b)
  | |- context [Uint63.of_Z (Z.of_nat O)] => rewrite nr_O
  end.
(** (step 83) a counter a function gives back, used as a counter: the same counter, where its bound keeps it below [wB] *)
Lemma nc_E : forall n, (Z.of_nat n < 9223372036854775808)%Z -> Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat n))) = n.
Proof.
  intros n H. rewrite Uint63.of_Z_spec, Z.mod_small by (split; [lia | exact H]). apply Nat2Z.id.
Qed.
(** what is known of the calls in the goal: [kitc.py] sets it *)
Ltac kq_bd := idtac.
(** (step 118) a value's bound posed: rewritten by what a match took apart, reduced, split; and, where a program has one, its call taken
    apart with its bound: [kitc.py] sets them *)
Ltac nb_vh0 :=
  repeat first [
    match goal with e : ?x = ?v, H : context [?x] |- _ =>
      lazymatch type of H with _ = _ => fail | _ => rewrite e in H end end
  | progress (cbn beta iota in *)
  | match goal with H : context [match ?p with _ => _ end] |- _ =>
      lazymatch type of H with _ = _ => fail | _ =>
        tryif is_var p then destruct p
        else lazymatch p with context [match _ with _ => _ end] => fail | _ => let e := fresh "kqe" in destruct p eqn:e end end end
  | match goal with H : _ /\ _ |- _ => destruct H end ].
(** where [lia] comes next: a projection of a constructor reduced too, on the goal *)
Ltac nb_vh := nb_vh0; try simpl.
Ltac kq_vh := idtac.
Ltac kq_vd := fail.
(** (step 102) a shift left by a number below [wB]: the machine's, the same modulo a word; for a bound, the product it is *)
Lemma nr_shiftl : forall a k, (Z.of_nat k < 9223372036854775808)%Z ->
  Uint63.of_Z (Z.of_nat (Nat.shiftl a k)) = PrimInt63.lsl (Uint63.of_Z (Z.of_nat a)) (Uint63.of_Z (Z.of_nat k)).
Proof.
  intros a k H. apply Uint63.to_Z_inj. rewrite Uint63.lsl_spec, !Uint63.of_Z_spec.
  rewrite (Z.mod_small (Z.of_nat k)) by (change Uint63.wB with 9223372036854775808%Z; lia).
  rewrite Nat.shiftl_mul_pow2, Nat2Z.inj_mul, Nat2Z.inj_pow. change (Z.of_nat 2) with 2%Z.
  rewrite Z.mul_mod_idemp_l by (compute; discriminate). reflexivity.
Qed.
Ltac nc_shl :=
  repeat match goal with |- context [Nat.shiftl ?a ?k] =>
    rewrite (Nat.shiftl_mul_pow2 a k); let v := eval vm_compute in (Nat.pow 2 k) in change (Nat.pow 2 k) with v end.
Ltac nc_side := kq_bd; kq_vh; nc_shl; lia.
(** (step 104) [Nat.ldiff] as the reader writes it, the 63 ones a literal *)
Lemma nr_ldiff_l : forall a b, Uint63.of_Z (Z.of_nat (Nat.ldiff a b)) =
  PrimInt63.land (Uint63.of_Z (Z.of_nat a)) (PrimInt63.lxor (Uint63.of_Z (Z.of_nat b)) 9223372036854775807%uint63).
Proof. intros a b. rewrite nr_ldiff. reflexivity. Qed.
Ltac nc_fold :=
  match goal with
  | |- context [PrimInt63.land (Uint63.of_Z (Z.of_nat ?a)) (PrimInt63.lxor (Uint63.of_Z (Z.of_nat ?b)) 9223372036854775807%uint63)] => rewrite <- (nr_ldiff_l a b)
  | |- context [PrimInt63.land (Uint63.of_Z (Z.of_nat ?a)) (Uint63.of_Z (Z.of_nat ?b))] => rewrite <- (nr_land a b)
  | |- context [PrimInt63.lor (Uint63.of_Z (Z.of_nat ?a)) (Uint63.of_Z (Z.of_nat ?b))] => rewrite <- (nr_lor a b)
  | |- context [PrimInt63.lxor (Uint63.of_Z (Z.of_nat ?a)) (Uint63.of_Z (Z.of_nat ?b))] => rewrite <- (nr_lxor a b)
  | |- context [PrimInt63.add (Uint63.of_Z (Z.of_nat ?a)) 1%uint63] => rewrite <- (nr_S a)
  | |- context [PrimInt63.add (Uint63.of_Z (Z.of_nat ?a)) (Uint63.of_Z (Z.of_nat ?b))] => rewrite <- (nr_add a b)
  | |- context [PrimInt63.mul (Uint63.of_Z (Z.of_nat ?a)) (Uint63.of_Z (Z.of_nat ?b))] => rewrite <- (nr_mul a b)
  | |- context [PrimInt63.lsl (Uint63.of_Z (Z.of_nat ?a)) (Uint63.of_Z (Z.of_nat ?b))] => rewrite <- (nr_shiftl a b) by lia
  end.
(** what stands in a function's place back to the counter, around it the same counter, in one step: what is left of them is folded again after *)
Ltac nc_step rw :=
  match goal with |- context [Z.to_nat (Uint63.to_Z _)] =>
    rw; repeat nc_fold;
    match goal with |- context [Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat ?n)))] => rewrite (nc_E n) by nc_side end
  end.
(** a match on such a counter, what it is kept: what is under it is below it *)
Ltac nc_match :=
  match goal with |- context [match ?c with O => _ | S _ => _ end] =>
    lazymatch c with ?f _ => let e := fresh "kqe" in destruct c eqn:e end end.
Ltac kq_nc := fail.
(** a bound, by the tests of its text: [tac] says what is known of the calls *)
(** (step 101) a row's bound through its bit operations: [land] at most each operand, [ldiff] the first, [lor] and [lxor] the sum *)
Lemma nr_zland_ldiff : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (Z.land x y + Z.ldiff x y = x)%Z /\ (0 <= Z.land x y)%Z /\ (0 <= Z.ldiff x y)%Z.
Proof.
  intros x y Hx Hy. split; [| split; [apply Z.land_nonneg; lia | apply Z.ldiff_nonneg; lia]].
  rewrite <- Z.add_lor_land.
  replace (Z.land (Z.land x y) (Z.ldiff x y)) with 0%Z.
  2:{ apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_0_l, Z.land_spec, Z.land_spec, Z.ldiff_spec. destruct (Z.testbit x n), (Z.testbit y n); reflexivity. }
  rewrite Z.add_0_r. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, Z.land_spec, Z.ldiff_spec. destruct (Z.testbit x n), (Z.testbit y n); reflexivity.
Qed.
Lemma nr_zlxor_add : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (Z.lxor x y + Z.land x y = Z.lor x y)%Z.
Proof.
  intros x y Hx Hy. rewrite <- Z.add_lor_land.
  replace (Z.land (Z.lxor x y) (Z.land x y)) with 0%Z.
  2:{ apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_0_l, Z.land_spec, Z.lxor_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit y n); reflexivity. }
  rewrite Z.add_0_r. apply Z.bits_inj'. intros n Hn. rewrite !Z.lor_spec, Z.lxor_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit y n); reflexivity.
Qed.
Lemma nb_land_l : forall a b, (Nat.land a b <= a)%nat.
Proof. intros a b. apply Nat2Z.inj_le. rewrite nr_zland. destruct (nr_zland_ldiff (Z.of_nat a) (Z.of_nat b) ltac:(lia) ltac:(lia)) as (E & A & B); lia. Qed.
Lemma nb_land_r : forall a b, (Nat.land a b <= b)%nat.
Proof. intros a b. rewrite Nat.land_comm. apply nb_land_l. Qed.
Lemma nb_ldiff : forall a b, (Nat.ldiff a b <= a)%nat.
Proof. intros a b. apply Nat2Z.inj_le. rewrite nr_zldiff. destruct (nr_zland_ldiff (Z.of_nat a) (Z.of_nat b) ltac:(lia) ltac:(lia)) as (E & A & B); lia. Qed.
Lemma nb_lor : forall a b, (Nat.lor a b <= a + b)%nat.
Proof. intros a b. apply Nat2Z.inj_le. rewrite nr_zlor, Nat2Z.inj_add, <- Z.add_lor_land. pose proof (Z.land_nonneg (Z.of_nat a) (Z.of_nat b)). lia. Qed.
Lemma nb_lxor : forall a b, (Nat.lxor a b <= a + b)%nat.
Proof.
  intros a b. pose proof (nb_lor a b) as L. apply Nat2Z.inj_le in L. apply Nat2Z.inj_le. rewrite nr_zlxor. rewrite nr_zlor in L.
  pose proof (nr_zlxor_add (Z.of_nat a) (Z.of_nat b) ltac:(lia) ltac:(lia)). pose proof (Z.land_nonneg (Z.of_nat a) (Z.of_nat b)). lia.
Qed.
Ltac nb_bitf :=
  repeat match goal with
  | |- context [Nat.land ?a ?b] => lazymatch goal with _ : (Nat.land a b <= a)%nat |- _ => fail | _ => pose proof (nb_land_l a b); pose proof (nb_land_r a b) end
  | |- context [Nat.lor ?a ?b] => lazymatch goal with _ : (Nat.lor a b <= a + b)%nat |- _ => fail | _ => pose proof (nb_lor a b) end
  | |- context [Nat.lxor ?a ?b] => lazymatch goal with _ : (Nat.lxor a b <= a + b)%nat |- _ => fail | _ => pose proof (nb_lxor a b) end
  | |- context [Nat.ldiff ?a ?b] => lazymatch goal with _ : (Nat.ldiff a b <= a)%nat |- _ => fail | _ => pose proof (nb_ldiff a b) end
  end.
(** (step 102) a counter a function gives back inside an operation, inside a sum or a product: the operation at most what it is of *)
Lemma nc_shiftr_le : forall a k, (Nat.shiftr a k <= a)%nat.
Proof. intros a k. rewrite Nat.shiftr_div_pow2. apply Nat.Div0.div_le_upper_bound. pose proof (Nat.pow_nonzero 2 k ltac:(lia)). nia. Qed.
Lemma nc_div_le : forall a b, (Nat.div a b <= a)%nat.
Proof. intros a [|b]; [cbn; lia | apply Nat.Div0.div_le_upper_bound; nia]. Qed.
Lemma nc_mod_le : forall a b, (Nat.modulo a b <= a)%nat.
Proof. intros a b. apply Nat.Div0.mod_le. Qed.
Lemma nc_div2_le : forall a, (Nat.div2 a <= a)%nat.
Proof. intros a. rewrite Nat.div2_div. apply nc_div_le. Qed.
Lemma nc_clearbit_le : forall a k, (Nat.clearbit a k <= a)%nat.
Proof. intros a k. rewrite Nat.clearbit_spec'. apply nb_ldiff. Qed.
Lemma nc_setbit_le : forall a k, (Nat.setbit a k <= a + Nat.pow 2 k)%nat.
Proof. intros a k. unfold Nat.setbit. rewrite Nat.shiftl_1_l. apply nb_lor. Qed.
(** (step 103) and of these *)
Lemma nc_log2_le : forall a, (Nat.log2 a <= a)%nat.
Proof. intros a. apply Nat.log2_le_lin; lia. Qed.
Lemma nc_sqrt_le : forall a, (Nat.sqrt a <= a)%nat.
Proof. intros a. apply Nat.sqrt_le_lin. Qed.
Lemma nc_gcd_le : forall a b, (Nat.gcd a b <= a + b)%nat.
Proof.
  intros [|a] b; [cbn; lia|]. pose proof (Nat.divide_pos_le (Nat.gcd (S a) b) (S a) ltac:(lia) (Nat.gcd_divide_l (S a) b)). lia.
Qed.
Lemma nc_b2n_le : forall b, (Nat.b2n b <= 1)%nat.
Proof. intros [|]; cbn; lia. Qed.
(** (step 105) [setbit]'s bound in [Z], its [2^k] not a unary number *)
Lemma nc_setbit_lez : forall a k, (Z.of_nat (Nat.setbit a k) <= Z.of_nat a + 2 ^ Z.of_nat k)%Z.
Proof. intros a k. pose proof (nc_setbit_le a k) as H. apply Nat2Z.inj_le in H. rewrite Nat2Z.inj_add, Nat2Z.inj_pow in H. exact H. Qed.
Ltac nc_opf :=
  repeat match goal with
  | |- context [Nat.log2 ?a] => lazymatch goal with _ : (Nat.log2 a <= a)%nat |- _ => fail | _ => pose proof (nc_log2_le a) end
  | |- context [Nat.sqrt ?a] => lazymatch goal with _ : (Nat.sqrt a <= a)%nat |- _ => fail | _ => pose proof (nc_sqrt_le a) end
  | |- context [Nat.gcd ?a ?b] => lazymatch goal with _ : (Nat.gcd a b <= a + b)%nat |- _ => fail | _ => pose proof (nc_gcd_le a b) end
  | |- context [Nat.b2n ?b] => lazymatch goal with _ : (Nat.b2n b <= 1)%nat |- _ => fail | _ => pose proof (nc_b2n_le b) end
  | |- context [Nat.shiftr ?a ?k] => lazymatch goal with _ : (Nat.shiftr a k <= a)%nat |- _ => fail | _ => pose proof (nc_shiftr_le a k) end
  | |- context [Nat.div ?a ?b] => lazymatch goal with _ : (Nat.div a b <= a)%nat |- _ => fail | _ => pose proof (nc_div_le a b) end
  | |- context [Nat.modulo ?a ?b] => lazymatch goal with _ : (Nat.modulo a b <= a)%nat |- _ => fail | _ => pose proof (nc_mod_le a b) end
  | |- context [Nat.div2 ?a] => lazymatch goal with _ : (Nat.div2 a <= a)%nat |- _ => fail | _ => pose proof (nc_div2_le a) end
  | |- context [Nat.clearbit ?a ?k] => lazymatch goal with _ : (Nat.clearbit a k <= a)%nat |- _ => fail | _ => pose proof (nc_clearbit_le a k) end
  | |- context [Nat.setbit ?a ?k] =>
      lazymatch goal with _ : (Z.of_nat (Nat.setbit a k) <= _)%Z |- _ => fail
      | _ => let v := eval vm_compute in (2 ^ Z.of_nat k)%Z in pose proof (nc_setbit_lez a k : (Z.of_nat (Nat.setbit a k) <= Z.of_nat a + v)%Z) end
  | |- context [Nat.double ?a] => lazymatch goal with _ : Nat.double a = _ |- _ => fail | _ => pose proof (Nat.double_twice a) end
  end.
Ltac nc_side ::= kq_bd; kq_vh; nc_shl; nb_bitf; nc_opf; nr_numf; lia.
(** (step 104) where only the value modulo a word of a counter is used ([land] with a number below a word, [testbit] below 63, [even], [odd],
    [mod] by a divisor of [2^63]): the same at the row's number, whatever the counter is, so no bound of it is asked *)
Lemma nc_low_of : forall x, Uint63.of_Z (Z.of_nat (Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat x))))) = Uint63.of_Z (Z.of_nat x).
Proof.
  intros x. rewrite Z2Nat.id by (pose proof (Uint63.to_Z_bounded (Uint63.of_Z (Z.of_nat x))); lia). apply Uint63.of_to_Z.
Qed.
Lemma nc_zlow : forall x, Z.of_nat (Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat x)))) = (Z.of_nat x mod 9223372036854775808)%Z.
Proof.
  intros x. rewrite Z2Nat.id by (pose proof (Uint63.to_Z_bounded (Uint63.of_Z (Z.of_nat x))); lia). rewrite Uint63.of_Z_spec. reflexivity.
Qed.
Lemma nc_land_low : forall x y, (Z.of_nat y < 9223372036854775808)%Z ->
  Nat.land x y = Nat.land (Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat x)))) y.
Proof.
  intros x y H. set (x' := Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat x)))).
  rewrite <- (nc_E (Nat.land x y)) by (pose proof (nb_land_r x y); lia).
  rewrite <- (nc_E (Nat.land x' y)) by (pose proof (nb_land_r x' y); lia).
  rewrite !nr_land. unfold x'. rewrite nc_low_of. reflexivity.
Qed.
Lemma nc_land_low_l : forall x y, (Z.of_nat y < 9223372036854775808)%Z ->
  Nat.land y x = Nat.land y (Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat x)))).
Proof. intros x y H. rewrite !(Nat.land_comm y). apply nc_land_low. exact H. Qed.
Lemma nc_testbit_low : forall x i, (Z.of_nat i < 63)%Z ->
  Nat.testbit x i = Nat.testbit (Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat x)))) i.
Proof.
  intros x i H. rewrite !nr_nbit, nc_zlow. change 9223372036854775808%Z with (2 ^ 63)%Z.
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.
Lemma nc_odd_low : forall x, Nat.odd x = Nat.odd (Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat x)))).
Proof. intros x. rewrite <- !Nat.bit0_odd. apply nc_testbit_low. lia. Qed.
Lemma nc_even_low : forall x, Nat.even x = Nat.even (Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat x)))).
Proof. intros x. rewrite <- !Nat.negb_odd, nc_odd_low. reflexivity. Qed.
Lemma nc_mod_low : forall x m, (0 < Z.of_nat m)%Z -> (9223372036854775808 mod Z.of_nat m = 0)%Z ->
  Nat.modulo x m = Nat.modulo (Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat x)))) m.
Proof.
  intros x m H0 H1. apply Nat2Z.inj. rewrite !Nat2Z.inj_mod, nc_zlow.
  symmetry. apply Z.mod_mod_divide. apply Z.mod_divide; [lia | exact H1].
Qed.
Ltac nc_low_rw n :=
  first [ rewrite <- (nc_land_low n) by nc_side | rewrite <- (nc_land_low_l n) by nc_side
        | rewrite <- (nc_testbit_low n) by lia | rewrite <- (nc_even_low n) | rewrite <- (nc_odd_low n)
        | rewrite <- (nc_mod_low n) by first [lia | vm_compute; reflexivity] ].
Ltac nc_step rw ::=
  match goal with |- context [Z.to_nat (Uint63.to_Z _)] =>
    rw; repeat nc_fold;
    match goal with |- context [Z.to_nat (Uint63.to_Z (Uint63.of_Z (Z.of_nat ?n)))] => first [rewrite (nc_E n) by nc_side | nc_low_rw n] end
  end.
Ltac nb_step tac :=
  repeat (cbn beta iota zeta;
          first [ solve [tac; nb_bitf; nr_numf; lia]
                | match goal with |- context [match ?c with _ => _ end] =>
                    lazymatch c with context [match _ with _ => _ end] => fail | _ => destruct c end end ]).
(** (step 118) a value's bound, each of its counters: what its matches take apart, with their equations, so that the bounds posed of
    the calls taken apart are of their parts *)
Ltac nb_stepv tac :=
  repeat (cbn beta iota zeta;
          first [ exact I
                | match goal with |- _ /\ _ => split end
                | solve [tac; nb_vh; nb_bitf; nr_numf; lia]
                | match goal with |- context [match ?c with _ => _ end] =>
                    lazymatch c with context [match _ with _ => _ end] => fail | _ => let e := fresh "kqe" in destruct c eqn:e end end ]).
(** a program's lemmas of a function read as a pair, for when what is known of the pair has been used: [kitc.py] sets it *)
Ltac kq_rw2 := fail.
Ltac kq_vm0 :=
  first [ rewrite KQMAuto.upd_upd_r
        | vm_restore
        | vm_slot
        | kq_fr
        | vm_lit
        | kq_nr
        | vm_call_pair
        | kq_rw2
        | vm_case
        | match goal with |- context [match ?c with _ => _ end] => is_var c; destruct c end
        (* (step 116) a projection of a constructor reduced first *)
        | match goal with |- context [match ?c with _ => _ end] =>
            lazymatch c with ?f ?x => let h := vm_head x in is_constructor h; let c2 := eval cbn in c in lazymatch x with context [c2] => progress (change c with c2) end end end
        | match goal with |- context [?f ?x] => is_proj (f x); let h := vm_head x in is_constructor h; let c2 := eval cbn in (f x) in progress (change (f x) with c2) end
        | match goal with |- context [match ?c with _ => _ end] =>
            lazymatch c with context [match _ with _ => _ end] => fail | _ => idtac end;
            lazymatch type of c with bool => fail | nat => fail | _ => destruct c end end ].
(** switched on by a program with such a function *)
Ltac kq_vm := fail.
(** a function that leaves the slot block alone, by induction on its counter: each end is [rd 63 j] of what it was given *)
Ltac fr_step IH :=
  repeat (cbn beta iota zeta delta [fst snd proj1_sig]; kq_unf;
          first [ kq_fr
                | progress (rewrite ?IH by vm_side)
                | fr_mem
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | vm_call_pair
                | vm_case
                | kq_convoy
                | match goal with |- context [match ?c with exist _ _ _ => _ end] => destruct c end
                | match goal with |- context [if ?c then _ else _] => lazymatch c with context [match _ with _ => _ end] => fail | _ => let e := fresh "kqe" in destruct c eqn:e end end
                | match goal with |- context [if ?c then _ else _] => match c with context [match ?v with _ => _ end] => is_var v; destruct v end end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | match goal with |- context [match ?c with pair _ _ => _ end] => destruct c end
                | reflexivity
                (* (step 99) a dead branch: a test's answer that its case contradicts, `(S m =? 0) = true` *)
                | match goal with e : _ = _ |- _ => solve [cbn in e; discriminate e] end
                | match goal with |- context [match ?c with _ => _ end] => is_var c; destruct c end ]).
(** (step 61) a fixpoint with its own call under a choice in an operand, and the same with the choice floated out: equal at each counter, test by test *)
Ltac own_step IH :=
  repeat (cbn beta iota zeta delta [fst snd proj1_sig]; kq_unf;
          first [ prim_rw
                | kq_guard
                | kq_nc
                | kq_rw
                | progress (rewrite ?IH by vm_side)
                | kq_vd
                | kq_vm
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | match goal with |- context [match ?c with pair _ _ => _ end] => lazymatch c with context [match _ with _ => _ end] => fail | PrimInt63.diveucl_21 _ _ _ => fail | _ => destruct c end end
                | kq_convoy
                | match goal with |- context [match ?c with exist _ _ _ => _ end] => destruct c end
                | match goal with |- context [if ?c then _ else _] => lazymatch c with context [match _ with _ => _ end] => fail | _ => let e := fresh "kqe" in destruct c eqn:e end end
                | match goal with |- context [if ?c then _ else _] => match c with context [match ?v with _ => _ end] => is_var v; destruct v end end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | match goal with |- context [match ?c with pair _ _ => _ end] => destruct c end
                | reflexivity
                (* (step 99) a dead branch: a test's answer that its case contradicts, `(S m =? 0) = true` *)
                | match goal with e : _ = _ |- _ => solve [cbn in e; discriminate e] end
                | match goal with |- context [match ?c with _ => _ end] => is_var c; destruct c end ]).

(** (step 82) a function giving back a counter, and the number in its place: its own call made a number on the right *)
Ltac nr_step IH :=
  repeat (cbn beta iota zeta delta [fst snd proj1_sig]; kq_unf;
          first [ prim_rw
                | kq_rw
                | progress (rewrite <- ?IH)
                | kq_vm
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | kq_convoy
                | match goal with |- context [if ?c then _ else _] => lazymatch c with context [match _ with _ => _ end] => fail | _ => let e := fresh "kqe" in destruct c eqn:e end end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | reflexivity
                (* (step 99) a dead branch: a test's answer that its case contradicts, `(S m =? 0) = true` *)
                | match goal with e : _ = _ |- _ => solve [cbn in e; discriminate e] end
                | match goal with |- context [match ?c with _ => _ end] => is_var c; destruct c end ]).
(** (step 114) a row giving back a value with counter fields: its statement [F xs = cv (f xs)] at the successor, the hypothesis
    rewritten forward (the row's call becomes the function's value made numbers), each value matched on destructed, the counters'
    numbers by [kq_nr] *)
Ltac nv_step IH :=
  repeat (cbn beta iota zeta delta [fst snd proj1_sig]; kq_unf;
          first [ prim_rw
                | kq_rw
                | progress (rewrite ?IH)
                | kq_nr
                | reflexivity
                | (* (step 116) a projection of a constructor, [rcn (mkrn c v)]: reduced, so that what is taken apart is [c]'s; a primitive one anywhere *)
                  match goal with |- context [match ?c with _ => _ end] =>
                    lazymatch c with ?f ?x => let h := vm_head x in is_constructor h; let c2 := eval cbn in c in lazymatch x with context [c2] => progress (change c with c2) end end end
                | match goal with |- context [?f ?x] => is_proj (f x); let h := vm_head x in is_constructor h; let c2 := eval cbn in (f x) in progress (change (f x) with c2) end
                | match goal with |- context [match ?c with _ => _ end] =>
                    lazymatch c with context [match _ with _ => _ end] => fail | _ => let e := fresh "kqe" in destruct c eqn:e end end
                | match goal with e : _ = _ |- _ => solve [cbn in e; discriminate e] end ]).
(** (step 111) the same, the induction hypotheses' rewriting given: a block's rows proved together, one hypothesis per member *)
Ltac nr_stepT rw :=
  repeat (cbn beta iota zeta delta [fst snd proj1_sig]; kq_unf;
          first [ prim_rw
                | kq_rw
                | progress rw
                | kq_vm
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | kq_convoy
                | match goal with |- context [if ?c then _ else _] => lazymatch c with context [match _ with _ => _ end] => fail | _ => let e := fresh "kqe" in destruct c eqn:e end end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | reflexivity
                (* (step 99) a dead branch: a test's answer that its case contradicts, `(S m =? 0) = true` *)
                | match goal with e : _ = _ |- _ => solve [cbn in e; discriminate e] end
                | match goal with |- context [match ?c with _ => _ end] => is_var c; destruct c end ]).
(** (step 61) a fixpoint with its own call on a counter deeper than the predecessor, and a budget function above it: equal at every budget above the counter *)
Ltac deep_step IH pr :=
  repeat (cbn beta iota zeta; pr;
          first [ exfalso; lia
                | kq_rw
                | progress (rewrite ?IH by lia)
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with pair _ _ => _ end] => destruct c end
                | reflexivity ]).

Definition kq_no_ih : True := I.
Ltac own_step0 :=
  repeat (cbn beta iota zeta delta [fst snd proj1_sig]; kq_unf;
          first [ prim_rw
                | kq_guard
                | kq_nc
                | kq_rw
                | kq_vd
                | kq_vm
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | match goal with |- context [match ?c with pair _ _ => _ end] => lazymatch c with context [match _ with _ => _ end] => fail | PrimInt63.diveucl_21 _ _ _ => fail | _ => destruct c end end
                | kq_convoy
                | match goal with |- context [match ?c with exist _ _ _ => _ end] => destruct c end
                | match goal with |- context [if ?c then _ else _] => lazymatch c with context [match _ with _ => _ end] => fail | _ => let e := fresh "kqe" in destruct c eqn:e end end
                | match goal with |- context [if ?c then _ else _] => match c with context [match ?v with _ => _ end] => is_var v; destruct v end end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | match goal with |- context [match ?c with pair _ _ => _ end] => destruct c end
                | reflexivity
                (* (step 99) a dead branch: a test's answer that its case contradicts, `(S m =? 0) = true` *)
                | match goal with e : _ = _ |- _ => solve [cbn in e; discriminate e] end
                | match goal with |- context [match ?c with _ => _ end] => is_var c; destruct c end ]).
(** (step 77) the same, a call's pair taken apart as its two parts, so that the same call on both sides is the same two parts whatever is taken apart first *)
Ltac pr_call :=
  match goal with |- context [match ?c with pair _ _ => _ end] =>
    lazymatch c with context [match _ with _ => _ end] => fail | PrimInt63.diveucl_21 _ _ _ => fail | pair _ _ => fail | _ => rewrite (surjective_pairing c) end end.
Ltac own_step0p :=
  repeat (cbn beta iota zeta delta [fst snd proj1_sig]; kq_unf;
          first [ prim_rw
                | kq_guard
                | kq_rw
                | match goal with e : ?c = ?v |- context [?c] => lazymatch c with ?f _ => rewrite e | ?f _ _ => rewrite e end end
                | pr_call
                | kq_convoy
                | match goal with |- context [match ?c with exist _ _ _ => _ end] => destruct c end
                | match goal with |- context [if ?c then _ else _] => lazymatch c with context [match _ with _ => _ end] => fail | _ => let e := fresh "kqe" in destruct c eqn:e end end
                | match goal with |- context [if ?c then _ else _] => match c with context [match ?v with _ => _ end] => is_var v; destruct v end end
                | match goal with |- context [if ?c then _ else _] => let e := fresh "kqe" in destruct c eqn:e end
                | match goal with |- context [match ?c with O => _ | S _ => _ end] => destruct c end
                | reflexivity
                (* (step 99) a dead branch: a test's answer that its case contradicts, `(S m =? 0) = true` *)
                | match goal with e : _ = _ |- _ => solve [cbn in e; discriminate e] end
                | match goal with |- context [match ?c with _ => _ end] => is_var c; destruct c end ]).
