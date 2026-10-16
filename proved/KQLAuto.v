(** One tactic that proves, for a kit-style Rocq function and its KQL
    translation, that the KQL function computes the Rocq function.

    The statement for a function [g] with parameters [x1 .. xn] (each a
    [nat] counter, sent to KQL as the 63-bit [ofn x], or an [i63]) and
    possibly a memory [M]:

      forall x1 .. xn M, Z.of_nat (the sum of the nat parameters) < wB ->
        run P g [args] M RESULT MEMORY

    where a function returning [i63] gives RESULT = g x1 .. M and
    MEMORY = M, and a function returning a memory gives RESULT = 0 and
    MEMORY = g x1 .. M.  [kql_prove] proves it by induction on the
    recursion argument, walking the KQL body one construct at a time;
    each callee's statement must already be proved and is passed in. *)

From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps.
From KQC Require Import KQL.
Import ListNotations.

(** ** Counters: a [nat] held as a 63-bit integer *)

Definition ofn (n : nat) : i63 := of_Z (Z.of_nat n).

Lemma ofn_phi : forall n, (Z.of_nat n < wB)%Z -> to_Z (ofn n) = Z.of_nat n.
Proof. intros n H. unfold ofn. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma ofn_S_ne0 : forall n, (Z.of_nat (S n) < wB)%Z -> PrimInt63.eqb (ofn (S n)) 0%uint63 = false.
Proof.
  intros n H. destruct (PrimInt63.eqb (ofn (S n)) 0%uint63) eqn:E; auto.
  apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite ofn_phi in E by auto.
  change (to_Z 0%uint63) with 0%Z in E. lia.
Qed.

Lemma ofn_0 : ofn 0 = 0%uint63.
Proof. reflexivity. Qed.

Lemma ofn_pred : forall n, (Z.of_nat (S n) < wB)%Z -> PrimInt63.sub (ofn (S n)) 1%uint63 = ofn n.
Proof.
  intros n H. apply to_Z_inj. rewrite sub_spec, !ofn_phi by lia.
  change (to_Z 1%uint63) with 1%Z. rewrite Z.mod_small; lia.
Qed.

Lemma ofn_succ : forall n, (Z.of_nat (S n) < wB)%Z -> PrimInt63.add (ofn n) 1%uint63 = ofn (S n).
Proof.
  intros n H. apply to_Z_inj. rewrite add_spec, !ofn_phi by lia.
  change (to_Z 1%uint63) with 1%Z. rewrite Z.mod_small; lia.
Qed.

(** ** Derived rules: a call and a loop, through [run] *)

Lemma E_call_run : forall P f rho M x g args vs w M1 k v M',
  avals rho args = Some vs ->
  run P g vs M w M1 ->
  eval P f (PTree.set x w rho) M1 k v M' ->
  eval P f rho M (Ecall x g args k) v M'.
Proof.
  intros P f rho M x g args vs w M1 k v M' A (fg & rho' & F & B & EV) K.
  eapply E_call; eauto.
Qed.

Lemma E_loop_run : forall P g f rho M args vs v M',
  run P g vs M v M' ->
  find P g = Some f ->
  avals rho args = Some vs ->
  eval P f rho M (Eloop args) v M'.
Proof.
  intros P g f rho M args vs v M' (fg & rho' & F' & B & EV) F A.
  rewrite F in F'. inv F'. eapply E_loop; eauto.
Qed.

Lemma run_intro : forall P g f vs rho M v M',
  find P g = Some f ->
  bind (kparams f) vs (PTree.empty _) = Some rho ->
  eval P f rho M (kbody f) v M' ->
  run P g vs M v M'.
Proof. intros. exists f, rho. auto. Qed.

(** ** The tactic *)

(** Side conditions on counters. *)
Ltac kql_bound := first [ lia | vm_compute; reflexivity ].

(** A counter test decided by the case of the induction, else a case split
    on the test itself (the Rocq side has the same test). *)
Lemma eqb00 : PrimInt63.eqb 0%uint63 0%uint63 = true.
Proof. reflexivity. Qed.

Ltac kql_test :=
  cbn [cmp_sem];
  first
    [ rewrite ofn_0, eqb00; cbn beta iota
    | rewrite ofn_S_ne0 by kql_bound; cbn beta iota
    | match goal with
      | |- context [ if PrimInt63.eqb ?a ?b then _ else _ ] => destruct (PrimInt63.eqb a b)
      | |- context [ if PrimInt63.ltb ?a ?b then _ else _ ] => destruct (PrimInt63.ltb a b)
      | |- context [ if PrimInt63.leb ?a ?b then _ else _ ] => destruct (PrimInt63.leb a b)
      end ].

(** After an arithmetic step, a counter that moved is written back as a counter. *)
Ltac kql_norm :=
  cbn [binop_sem];
  repeat first [ rewrite ofn_pred by kql_bound | rewrite ofn_succ by kql_bound ].

(** A call or a loop: some hypothesis in the context proves it -- a callee's
    statement (put there with [pose proof]) or the induction hypothesis. *)
Ltac kql_call :=
  match goal with
  | H : _ |- run _ _ _ _ _ _ => eapply H; kql_bound
  end.

Ltac kql_walk :=
  repeat
    match goal with
    | |- eval _ _ _ _ (Eret _) _ _ => apply E_ret; exact eq_refl
    | |- eval _ _ _ _ (Eop _ _ _ _ _) _ _ => eapply E_op; [reflexivity | reflexivity | kql_norm]
    | |- eval _ _ _ _ (Eload _ _ _ _) _ _ => eapply E_load; [reflexivity | reflexivity | ]
    | |- eval _ _ _ _ (Estore _ _ _ _) _ _ => eapply E_store; [reflexivity | reflexivity | reflexivity | ]
    | |- eval _ _ _ _ (Eif _ _ _ _ _) _ _ => eapply E_if; [reflexivity | reflexivity | kql_test]
    | |- eval _ _ _ _ (Ecall _ _ _ _) _ _ => eapply E_call_run; [reflexivity | kql_call | ]
    | |- eval _ _ _ _ (Eloop _) _ _ => eapply E_loop_run; [kql_call | reflexivity | reflexivity]
    end.

Ltac kql_head t := match t with ?f _ => kql_head f | _ => t end.

(** Enter a function: its KQL body on the left, its Rocq definition opened
    one step on the right. *)
Ltac kql_enter :=
  intros; eapply run_intro; [reflexivity | reflexivity | simpl kbody ];
  match goal with
  | |- eval _ _ _ _ _ ?v ?m =>
      first [ let h := kql_head v in progress cbn [h]
            | let h := kql_head m in progress cbn [h]
            | idtac ]
  end.

(** [kql_prove d]: induction on the recursion argument [d] (the first
    variable of the goal), then the walk.  [kql_prove0]: no recursion. *)
Ltac kql_prove :=
  let d := fresh "d" in
  intros d; induction d; kql_enter; kql_walk.

Ltac kql_prove0 := kql_enter; kql_walk.
