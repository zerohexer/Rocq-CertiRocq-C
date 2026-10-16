From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps.
From MetaRocq.Template Require Import All.
From compcert Require Import Integers Smallstep Behaviors Errors.
From compcert Require Asm.
From KQC Require Import KQL KQLGen KQLAuto KQLTrans KQLBack KQLTop.
Import ListNotations.

(* A plain Rocq program: fill a block from an lcg, sort it in place, checksum. *)
Definition A := 40%positive.
Definition NN : Z := 10000.
Definition N : nat := 10000.

Open Scope uint63_scope.
Definition step (s : i63) : i63 := (s * 1103515245 + 12345) land 2147483647.

Fixpoint fill (k : nat) (i s : i63) (M : kmem) : kmem :=
  match k with
  | O => M
  | S k => fill k (i + 1) (step s) (wr M NN A i (s land 1048575))
  end.

Fixpoint inner (j : nat) (key : i63) (M : kmem) : kmem :=
  match j with
  | O => wr M NN A 0 key
  | S j' =>
      let x := rd M NN A (ofn j') in
      if key <? x then inner j' key (wr M NN A (ofn (S j')) x)
      else wr M NN A (ofn (S j')) key
  end.

Fixpoint outer (k i : nat) (M : kmem) : kmem :=
  match k with
  | O => M
  | S k => outer k (S i) (inner i (rd M NN A (ofn i)) M)
  end.

Fixpoint csum (k i : nat) (acc : i63) (M : kmem) : i63 :=
  match k with
  | O => acc
  | S k => csum k (S i) (acc + rd M NN A (ofn i) * ofn (S i)) M
  end.

Definition result : i63 := csum N 0 0 (outer (N - 1) 1 (fill N 0 1 mem0)).
Close Scope uint63_scope.

MetaRocq Run (kql_translate result "sort_prog").

Lemma csum_ok : csum_stmt. Proof. kql_auto. Qed.
Lemma inner_ok : inner_stmt. Proof. kql_auto. Qed.
Lemma outer_ok : outer_stmt. Proof. pose proof inner_ok as H1; hnf in H1. kql_auto. Qed.
Lemma fill_ok : fill_stmt. Proof. kql_auto. Qed.
Lemma result_ok : result_stmt.
Proof.
  pose proof fill_ok as H1; pose proof outer_ok as H2; pose proof csum_ok as H3; hnf in H1, H2, H3.
  kql_auto.
Qed.

Theorem sort_compiled : forall tp,
  transf_clight2_program (tr_program sort_prog 20%positive 1004%positive []) = OK tp ->
  program_behaves (Asm.semantics tp) (Terminates Events.E0 (Int.repr (to_Z result))).
Proof.
  intros tp T. destruct (result_ok mem0 ltac:(vm_compute; reflexivity)) as (M' & R).
  eapply kql_compiled_correct; eauto.
  - repeat constructor; cbv; intuition discriminate.
  - intros g f F. unfold find in F. simpl in F.
    repeat match type of F with
           | context [peq g ?x] => destruct (peq g x); [inv F | ]
           end; try discriminate;
    repeat constructor; simpl; intuition discriminate.
  - intros h n S. unfold asize in S. simpl in S. destruct (peq h A); inv S. unfold NN. lia.
Qed.
Print Assumptions sort_compiled.
