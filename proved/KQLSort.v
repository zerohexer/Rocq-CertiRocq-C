(** In-place insertion sort on a memory block, as a kit program:
    fill the block from the lcg, sort it in place, return a weighted
    checksum.  The Rocq definitions use KQL's own memory operations; the
    KQL program is proved to compute them, and then compiled end to end. *)

From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps Integers Smallstep Behaviors Errors.
From compcert Require Asm.
From KQC Require Import KQL KQLGen KQLArith KQLBack KQLTop KQLAuto KQLEx.
Import ListNotations.

Definition A := 40%positive.
Definition NN : Z := 10000.
Definition N : nat := 10000.

Open Scope uint63_scope.

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

Definition result : i63 :=
  csum N 0 0 (outer (N - 1) 1 (fill N 0 1 mem0)).

Close Scope uint63_scope.

(** ** The KQL program *)

Definition p1 := 1%positive.
Definition p2 := 2%positive.
Definition p3 := 3%positive.
Definition l4 := 4%positive.
Definition l5 := 5%positive.
Definition l6 := 6%positive.
Definition l7 := 7%positive.
Definition l8 := 8%positive.
Definition l9 := 9%positive.
Definition l10 := 10%positive.

Definition f_fill := 41%positive.
Definition f_outer := 42%positive.
Definition f_inner := 43%positive.
Definition f_sum := 44%positive.
Definition f_go := 45%positive.

(* fill(k, i, s) *)
Definition fill_fn : fn :=
  mkfn [p1; p2; p3]
    (Eif Ceq (Avar p1) (Aint 0) (Eret (Aint 0))
       (Eop l4 Bland (Avar p3) (Aint 1048575)
        (Estore A (Avar p2) (Avar l4)
         (Eop l5 Bsub (Avar p1) (Aint 1)
          (Eop l6 Badd (Avar p2) (Aint 1)
           (Eop l7 Bmul (Avar p3) (Aint 1103515245)
            (Eop l8 Badd (Avar l7) (Aint 12345)
             (Eop l9 Bland (Avar l8) (Aint 2147483647)
              (Eloop [Avar l5; Avar l6; Avar l9]))))))))).

(* inner(j, key) *)
Definition inner_fn : fn :=
  mkfn [p1; p2]
    (Eif Ceq (Avar p1) (Aint 0)
       (Estore A (Aint 0) (Avar p2) (Eret (Aint 0)))
       (Eop l4 Bsub (Avar p1) (Aint 1)
        (Eload l5 A (Avar l4)
         (Eif Clt (Avar p2) (Avar l5)
            (Estore A (Avar p1) (Avar l5) (Eloop [Avar l4; Avar p2]))
            (Estore A (Avar p1) (Avar p2) (Eret (Aint 0))))))).

(* outer(k, i) *)
Definition outer_fn : fn :=
  mkfn [p1; p2]
    (Eif Ceq (Avar p1) (Aint 0) (Eret (Aint 0))
       (Eload l4 A (Avar p2)
        (Ecall l5 f_inner [Avar p2; Avar l4]
         (Eop l6 Bsub (Avar p1) (Aint 1)
          (Eop l7 Badd (Avar p2) (Aint 1)
           (Eloop [Avar l6; Avar l7])))))).

(* sum(k, i, acc) *)
Definition sum_fn : fn :=
  mkfn [p1; p2; p3]
    (Eif Ceq (Avar p1) (Aint 0) (Eret (Avar p3))
       (Eload l4 A (Avar p2)
        (Eop l5 Badd (Avar p2) (Aint 1)
         (Eop l6 Bmul (Avar l4) (Avar l5)
          (Eop l7 Badd (Avar p3) (Avar l6)
           (Eop l8 Bsub (Avar p1) (Aint 1)
            (Eloop [Avar l8; Avar l5; Avar l7]))))))).

Definition go_fn : fn :=
  mkfn []
    (Ecall l4 f_fill [Aint (ofn N); Aint 0; Aint 1]
     (Ecall l5 f_outer [Aint (ofn (N - 1)); Aint (ofn 1)]
      (Ecall l6 f_sum [Aint (ofn N); Aint (ofn 0); Aint 0]
       (Eret (Avar l6))))).

Definition P_sort : prog :=
  mkprog [(f_fill, fill_fn); (f_outer, outer_fn); (f_inner, inner_fn);
          (f_sum, sum_fn); (f_go, go_fn)]
         [(A, NN)].

(** ** Each function computes its Rocq definition *)

Ltac step := first [ eapply E_op | eapply E_store | eapply E_load ]; try reflexivity.

Lemma fill_eval : forall k i s M, (Z.of_nat k < wB)%Z ->
  eval P_sort fill_fn (env3 (ofn k) i s) M (kbody fill_fn) 0%uint63 (fill k i s M).
Proof.
  induction k as [|k IH]; intros i s M H; simpl kbody.
  - eapply E_if; try reflexivity. rewrite ofn_0. simpl. apply E_ret. reflexivity.
  - eapply E_if; try reflexivity. simpl. rewrite ofn_S_ne0 by auto.
    do 7 step. eapply E_loop; try reflexivity. simpl binop_sem. rewrite ofn_pred by auto.
    apply IH. lia.
Qed.

Lemma inner_eval : forall j key M, (Z.of_nat j < wB)%Z ->
  eval P_sort inner_fn (env2 (ofn j) key) M (kbody inner_fn) 0%uint63 (inner j key M).
Proof.
  induction j as [|j IH]; intros key M H; simpl kbody.
  - eapply E_if; try reflexivity. rewrite ofn_0. simpl.
    step. apply E_ret. reflexivity.
  - eapply E_if; try reflexivity. simpl. rewrite ofn_S_ne0 by auto.
    step. simpl binop_sem. rewrite ofn_pred by auto. step.
    eapply E_if; try reflexivity. simpl cmp_sem. cbn [inner].
    destruct (PrimInt63.ltb key (rd M NN A (ofn j))).
    + step. eapply E_loop; try reflexivity. apply IH. lia.
    + step. apply E_ret. reflexivity.
Qed.

Lemma outer_eval : forall k i M, (Z.of_nat (k + i) < wB)%Z ->
  eval P_sort outer_fn (env2 (ofn k) (ofn i)) M (kbody outer_fn) 0%uint63 (outer k i M).
Proof.
  induction k as [|k IH]; intros i M H; simpl kbody.
  - eapply E_if; try reflexivity. rewrite ofn_0. simpl. apply E_ret. reflexivity.
  - eapply E_if; try reflexivity. simpl. rewrite ofn_S_ne0 by lia.
    step. eapply E_call with (fg := inner_fn); try reflexivity.
    + apply inner_eval. lia.
    + step. step. eapply E_loop; try reflexivity. simpl binop_sem.
      rewrite ofn_pred, ofn_succ by lia. apply IH. lia.
Qed.

Lemma sum_eval : forall k i acc M, (Z.of_nat (k + i) < wB)%Z ->
  eval P_sort sum_fn (env3 (ofn k) (ofn i) acc) M (kbody sum_fn) (csum k i acc M) M.
Proof.
  induction k as [|k IH]; intros i acc M H; simpl kbody.
  - eapply E_if; try reflexivity. rewrite ofn_0. simpl. apply E_ret. reflexivity.
  - eapply E_if; try reflexivity. simpl. rewrite ofn_S_ne0 by lia.
    do 5 step. eapply E_loop; try reflexivity. simpl binop_sem.
    rewrite ofn_pred, ofn_succ by lia. apply IH. lia.
Qed.

Lemma go_run : run P_sort f_go [] mem0 result
                 (outer (N - 1) 1 (fill N 0 1 mem0)).
Proof.
  exists go_fn, (PTree.empty _). split. reflexivity. split. reflexivity. simpl kbody.
  eapply E_call with (fg := fill_fn) (rho' := env3 (ofn N) 0%uint63 1%uint63); try reflexivity.
  { apply fill_eval. vm_compute. reflexivity. }
  eapply E_call with (fg := outer_fn) (rho' := env2 (ofn (N - 1)) (ofn 1)); try reflexivity.
  { apply outer_eval. vm_compute. reflexivity. }
  eapply E_call with (fg := sum_fn) (rho' := env3 (ofn N) (ofn 0) 0%uint63); try reflexivity.
  { apply sum_eval. vm_compute. reflexivity. }
  (* [exact eq_refl], not [reflexivity]: the latter evaluates the sort. *)
  apply E_ret. exact eq_refl.
Qed.

Definition sort_c := tr_program P_sort m_main f_go [].

Theorem sort_compiled : forall tp,
  transf_clight2_program sort_c = OK tp ->
  program_behaves (Asm.semantics tp)
    (Terminates Events.E0 (Int.repr (to_Z result))).
Proof.
  intros tp T. eapply kql_compiled_correct; eauto.
  - simpl. repeat constructor; simpl; intuition discriminate.
  - intros g f F. unfold find in F. simpl in F.
    repeat match type of F with
           | context [peq g ?x] => destruct (peq g x); [inv F | ]
           end; try discriminate;
    repeat constructor; simpl; intuition discriminate.
  - intros h n S. unfold asize in S. simpl in S. destruct (peq h A); inv S. unfold NN. lia.
  - apply go_run.
Qed.
