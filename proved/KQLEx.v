(** Two kit programs in KQL, each proved equal to its Rocq definition,
    then compiled end to end. *)

From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps Integers Smallstep Behaviors Errors.
From compcert Require Asm.
From KQC Require Import KQL KQLGen KQLArith KQLBack KQLTop KQLAuto.
Import ListNotations.

(** ** lcg: the kit's benchmark, 2^24 steps by binary splitting *)

Open Scope uint63_scope.

Definition step (s : i63) : i63 := (s * 1103515245 + 12345) land 2147483647.
Fixpoint rep (d : nat) (s : i63) : i63 :=
  match d with O => step s | S d => rep d (rep d s) end.

Close Scope uint63_scope.

Definition v_d := 1%positive.
Definition v_s := 2%positive.
Definition v_t1 := 3%positive.
Definition v_t2 := 4%positive.
Definition v_t3 := 5%positive.
Definition v_d1 := 6%positive.
Definition v_r := 7%positive.
Definition f_rep := 10%positive.

Definition rep_fn : fn :=
  mkfn [v_d; v_s]
    (Eif Ceq (Avar v_d) (Aint 0)
       (Eop v_t1 Bmul (Avar v_s) (Aint 1103515245)
        (Eop v_t2 Badd (Avar v_t1) (Aint 12345)
         (Eop v_t3 Bland (Avar v_t2) (Aint 2147483647)
          (Eret (Avar v_t3)))))
       (Eop v_d1 Bsub (Avar v_d) (Aint 1)
        (Ecall v_r f_rep [Avar v_d1; Avar v_s]
         (Eloop [Avar v_d1; Avar v_r])))).

Definition P_lcg : prog := mkprog [(f_rep, rep_fn)] [].

Definition env2 (a b : i63) : env := PTree.set v_s b (PTree.set v_d a (PTree.empty _)).

Lemma rep_eval : forall d s M, (Z.of_nat d < wB)%Z ->
  eval P_lcg rep_fn (env2 (ofn d) s) M (kbody rep_fn) (rep d s) M.
Proof.
  induction d as [|d IH]; intros s M H; simpl kbody.
  - eapply E_if; try reflexivity. rewrite ofn_0. simpl.
    eapply E_op; try reflexivity. eapply E_op; try reflexivity. eapply E_op; try reflexivity.
    apply E_ret. reflexivity.
  - eapply E_if; try reflexivity. simpl. rewrite ofn_S_ne0 by auto.
    eapply E_op; try reflexivity. simpl binop_sem. rewrite ofn_pred by auto.
    eapply E_call with (fg := rep_fn) (vs := [ofn d; s]); try reflexivity.
    + apply IH. lia.
    + eapply E_loop with (vs := [ofn d; rep d s]); try reflexivity.
      apply IH. lia.
Qed.

Lemma rep_run : forall d s M, (Z.of_nat d < wB)%Z -> run P_lcg f_rep [ofn d; s] M (rep d s) M.
Proof.
  intros d s M H. exists rep_fn, (env2 (ofn d) s). split. reflexivity. split. reflexivity.
  apply rep_eval; auto.
Qed.

Definition m_main := 20%positive.

Definition lcg_c := tr_program P_lcg m_main f_rep [ofn 24; 1%uint63].

Theorem lcg_compiled : forall tp,
  transf_clight2_program lcg_c = OK tp ->
  program_behaves (Asm.semantics tp)
    (Terminates Events.E0 (Int.repr (to_Z (rep 24 1%uint63)))).
Proof.
  intros tp T. eapply kql_compiled_correct; eauto.
  - simpl. repeat constructor; simpl; intuition discriminate.
  - intros g f F. unfold find in F. simpl in F. destruct (peq g f_rep); inv F.
    repeat constructor; simpl; intuition discriminate.
  - intros h n S. discriminate.
  - apply rep_run. reflexivity.
Qed.

(** ** A counted loop with an accumulator: sum of squares *)

Open Scope uint63_scope.
Fixpoint sumsq (k : nat) (i acc : i63) : i63 :=
  match k with O => acc | S k => sumsq k (i + 1) (acc + i * i) end.
Close Scope uint63_scope.

Definition v_k := 1%positive.
Definition v_i := 2%positive.
Definition v_a := 3%positive.
Definition v_k1 := 4%positive.
Definition v_i1 := 5%positive.
Definition v_sq := 6%positive.
Definition v_a1 := 7%positive.
Definition f_sumsq := 11%positive.

Definition sumsq_fn : fn :=
  mkfn [v_k; v_i; v_a]
    (Eif Ceq (Avar v_k) (Aint 0)
       (Eret (Avar v_a))
       (Eop v_k1 Bsub (Avar v_k) (Aint 1)
        (Eop v_i1 Badd (Avar v_i) (Aint 1)
         (Eop v_sq Bmul (Avar v_i) (Avar v_i)
          (Eop v_a1 Badd (Avar v_a) (Avar v_sq)
           (Eloop [Avar v_k1; Avar v_i1; Avar v_a1])))))).

Definition P_sumsq : prog := mkprog [(f_sumsq, sumsq_fn)] [].

Definition env3 (a b c : i63) : env :=
  PTree.set v_a c (PTree.set v_i b (PTree.set v_k a (PTree.empty _))).

Lemma sumsq_eval : forall k i a M, (Z.of_nat k < wB)%Z ->
  eval P_sumsq sumsq_fn (env3 (ofn k) i a) M (kbody sumsq_fn) (sumsq k i a) M.
Proof.
  induction k as [|k IH]; intros i a M H; simpl kbody.
  - eapply E_if; try reflexivity. rewrite ofn_0. simpl. apply E_ret. reflexivity.
  - eapply E_if; try reflexivity. simpl. rewrite ofn_S_ne0 by auto.
    eapply E_op; try reflexivity. eapply E_op; try reflexivity.
    eapply E_op; try reflexivity. eapply E_op; try reflexivity.
    eapply E_loop; try reflexivity. simpl binop_sem. rewrite ofn_pred by auto.
    apply IH. lia.
Qed.

Lemma sumsq_run : forall k i a M, (Z.of_nat k < wB)%Z ->
  run P_sumsq f_sumsq [ofn k; i; a] M (sumsq k i a) M.
Proof.
  intros k i a M H. exists sumsq_fn, (env3 (ofn k) i a). split. reflexivity. split. reflexivity.
  apply sumsq_eval; auto.
Qed.
