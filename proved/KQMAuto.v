(** One tactic that proves, for a kit-style Rocq function and its KQL
    translation, that the KQL function computes the Rocq function on the
    kit's memory.  The statement for a function [g] (see KQMTrans.v):

      forall x1 .. xn M, Z.of_nat (the sum of the counters) < wB ->
        runk P g [args] M RESULT MEMORY

    or, for a function that gives a number and writes the memory (the
    memory is then lost to the caller), the same under [exists M'].
    [kqm_prove] proves it by induction on the first counter and walks the
    KQL body one construct at a time. *)

From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps AST.
From KQC Require Import KQL KQLAuto KQMSem.
Import ListNotations.

(** ** Derived rules: a call and a loop, through [runk] *)

Lemma K_call_run : forall P f rho M x g args vs w M1 k v M',
  avals rho args = Some vs ->
  runk P g vs M w M1 ->
  evalk P f (PTree.set x w rho) M1 k v M' ->
  evalk P f rho M (Ecall x g args k) v M'.
Proof.
  intros P f rho M x g args vs w M1 k v M' A (fg & rho' & F & B & EV) K.
  eapply K_call; eauto.
Qed.

(** a call whose end memory is not known (the callee writes and gives a number): the memory is lost *)
Lemma K_call_ex : forall P f rho M x g args vs w k v M',
  avals rho args = Some vs ->
  (exists M1, runk P g vs M w M1) ->
  (forall M1, runk P g vs M w M1 -> evalk P f (PTree.set x w rho) M1 k v M') ->
  evalk P f rho M (Ecall x g args k) v M'.
Proof.
  intros P f rho M x g args vs w k v M' A (M1 & R) K.
  eapply K_call_run; eauto.
Qed.

Lemma K_loop_run : forall P g f rho M args vs v M',
  runk P g vs M v M' ->
  find P g = Some f ->
  avals rho args = Some vs ->
  evalk P f rho M (Eloop args) v M'.
Proof.
  intros P g f rho M args vs v M' (fg & rho' & F' & B & EV) F A.
  rewrite F in F'. inv F'. eapply K_loop; eauto.
Qed.

Lemma runk_intro : forall P g f vs rho M v M',
  find P g = Some f ->
  bind (kparams f) vs (PTree.empty _) = Some rho ->
  evalk P f rho M (kbody f) v M' ->
  runk P g vs M v M'.
Proof. intros. exists f, rho. auto. Qed.

(** ** The same with the end memory hidden: for a function that writes the memory and gives a number *)

Definition evalx (P : prog) (f : fn) (rho : env) (M : kmemt) (e : exp) (v : i63) : Prop :=
  exists M', evalk P f rho M e v M'.
Definition runx (P : prog) (g : AST.ident) (vs : list i63) (M : kmemt) (v : i63) : Prop :=
  exists M', runk P g vs M v M'.

Section X.
Variable P : prog.
Variable f : fn.

Lemma X_ret : forall rho M a v, aval rho a = Some v -> evalx P f rho M (Eret a) v.
Proof. intros. exists M. apply K_ret; auto. Qed.

Lemma X_op : forall rho M x o a b va vb k v,
  aval rho a = Some va -> aval rho b = Some vb ->
  evalx P f (PTree.set x (binop_sem o va vb) rho) M k v -> evalx P f rho M (Eop x o a b k) v.
Proof. intros * A B (M' & E). exists M'. eapply K_op; eauto. Qed.

Lemma X_if : forall rho M c a b t e va vb v,
  aval rho a = Some va -> aval rho b = Some vb ->
  evalx P f rho M (if cmp_sem c va vb then t else e) v -> evalx P f rho M (Eif c a b t e) v.
Proof. intros * A B (M' & E). exists M'. eapply K_if; eauto. Qed.

Lemma X_sel : forall rho M x c a b t e va vb vt ve k v,
  aval rho a = Some va -> aval rho b = Some vb -> aval rho t = Some vt -> aval rho e = Some ve ->
  evalx P f (PTree.set x (if cmp_sem c va vb then vt else ve) rho) M k v ->
  evalx P f rho M (Esel x c a b t e k) v.
Proof. intros * A B T E (M' & H). exists M'. eapply K_sel; eauto. Qed.

Lemma X_ld : forall rho M x h i vh vi k v,
  aval rho h = Some vh -> aval rho i = Some vi ->
  evalx P f (PTree.set x (krd vh vi M) rho) M k v -> evalx P f rho M (Ekld x h i k) v.
Proof. intros * A B (M' & E). exists M'. eapply K_ld; eauto. Qed.

Lemma X_st : forall rho M h i a vh vi va k v,
  aval rho h = Some vh -> aval rho i = Some vi -> aval rho a = Some va ->
  evalx P f rho (kupd vh vi va M) k v -> evalx P f rho M (Ekst h i a k) v.
Proof. intros * A B C (M' & E). exists M'. eapply K_st; eauto. Qed.

Lemma X_ld32 : forall rho M x h i vh vi k v,
  aval rho h = Some vh -> aval rho i = Some vi ->
  evalx P f (PTree.set x (krd32 vh vi M) rho) M k v -> evalx P f rho M (Ekld32 x h i k) v.
Proof. intros * A B (M' & E). exists M'. eapply K_ld32; eauto. Qed.

Lemma X_st32 : forall rho M h i a vh vi va k v,
  aval rho h = Some vh -> aval rho i = Some vi -> aval rho a = Some va ->
  evalx P f rho (kupd32 vh vi va M) k v -> evalx P f rho M (Ekst32 h i a k) v.
Proof. intros * A B C (M' & E). exists M'. eapply K_st32; eauto. Qed.

Lemma X_call_run : forall rho M x g args vs w M1 k v,
  avals rho args = Some vs -> runk P g vs M w M1 ->
  evalx P f (PTree.set x w rho) M1 k v -> evalx P f rho M (Ecall x g args k) v.
Proof. intros * A R (M' & E). exists M'. eapply K_call_run; eauto. Qed.

Lemma X_call_ex : forall rho M x g args vs w k v,
  avals rho args = Some vs -> runx P g vs M w ->
  (forall M1, runk P g vs M w M1 -> evalx P f (PTree.set x w rho) M1 k v) ->
  evalx P f rho M (Ecall x g args k) v.
Proof.
  intros * A (M1 & R) K. destruct (K M1 R) as (M' & E). exists M'. eapply K_call_run; eauto.
Qed.

Lemma X_loop_run : forall g rho M args vs v,
  runx P g vs M v -> find P g = Some f -> avals rho args = Some vs ->
  evalx P f rho M (Eloop args) v.
Proof. intros * (M' & R) F A. exists M'. eapply K_loop_run; eauto. Qed.
End X.

Lemma runx_intro : forall P g f vs rho M v,
  find P g = Some f -> bind (kparams f) vs (PTree.empty _) = Some rho ->
  evalx P f rho M (kbody f) v -> runx P g vs M v.
Proof. intros * F B (M' & E). exists M'. eapply runk_intro; eauto. Qed.

(** ** The tactic *)

(** reduce the choices of the KQL text (a comparison of numbers written in the program included) *)
Ltac kqm_red := cbv beta iota delta [cmp_sem binop_sem andb orb negb
  PrimInt63.ltsb PrimInt63.lesb PrimInt63.eqb PrimInt63.ltb PrimInt63.leb
  PrimInt63.land PrimInt63.lor PrimInt63.lxor PrimInt63.add PrimInt63.sub PrimInt63.mul].

(** a test already split on is known: every later copy of it in the goal is replaced by its outcome *)
Ltac kqm_known :=
  repeat match goal with
         | H : ?c = _ |- _ =>
             lazymatch type of c with
             | bool => progress rewrite H
             end
         end;
  kqm_red.

(** the bound on every counter of a statement *)
Definition cb : Z := 4611686018427387904.
Lemma wB_num : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Ltac kqm_bound := first [ (pose proof wB_num; unfold cb in *; lia) | (vm_compute; reflexivity) ].

Lemma eqb00 : PrimInt63.eqb 0%uint63 0%uint63 = true.
Proof. reflexivity. Qed.

(** a test: the counter cases of the induction decide their own tests; any other test is split in the goal *)
Ltac kqm_test :=
  kqm_red;
  first
    [ rewrite ofn_0, eqb00; kqm_red
    | rewrite ofn_S_ne0 by kqm_bound; kqm_red
    | match goal with
      | |- evalk _ _ _ _ (if ?b then _ else _) _ _ => destruct b eqn:?; kqm_red; kqm_known
      end
    | idtac ].

Ltac kqm_norm :=
  kqm_red; try kqm_known;
  repeat first [ rewrite ofn_pred by kqm_bound | rewrite ofn_succ by kqm_bound ].

(** a call or a loop: some hypothesis in the context proves it -- a callee's statement (put there with
    [pose proof]) or the induction hypothesis *)
Ltac kqm_call :=
  match goal with
  | H : _ |- runk _ _ _ _ _ _ => eapply H; kqm_bound
  end.

Ltac kqm_call_ex :=
  match goal with
  | H : _ |- exists M1, runk _ _ _ _ _ M1 => eapply H; kqm_bound
  end.

(** the value of a chosen number against the Rocq text: equal as they stand, or after a split on each test *)
Ltac kqm_inner c := lazymatch c with context [if ?d then _ else _] => kqm_inner d | _ => c end.
Ltac kqm_fin :=
  first [ exact eq_refl
        | kqm_red;
          repeat (first [ exact eq_refl
                        | match goal with
                          | |- context [if ?c then _ else _] =>
                              let d := kqm_inner c in (match type of d with bool => idtac end); destruct d; kqm_red
                          end ]);
          first [ exact eq_refl | reflexivity ] ].

(** split on every test left in the goal (innermost first), the way [kqm_fin] does at a return: a merged choice of
    arguments is compared with the Rocq text that chooses between two calls *)
Ltac kqm_splitall :=
  kqm_red;
  repeat (match goal with
          | |- context [if ?c then _ else _] =>
              let d := kqm_inner c in (match type of d with bool => idtac end); destruct d; kqm_red; try kqm_known
          end).

Ltac kqm_walk :=
  repeat
    match goal with
    | |- evalk _ _ _ _ (Eret _) _ _ => apply K_ret; kqm_fin
    | |- evalk _ _ _ _ (Eop _ _ _ _ _) _ _ => eapply K_op; [reflexivity | reflexivity | kqm_norm]
    | |- evalk _ _ _ _ (Ekld _ _ _ _) _ _ => eapply K_ld; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekst _ _ _ _) _ _ => eapply K_st; [reflexivity | reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekld32 _ _ _ _) _ _ => eapply K_ld32; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekst32 _ _ _ _) _ _ => eapply K_st32; [reflexivity | reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Eif _ _ _ _ _) _ _ => eapply K_if; [reflexivity | reflexivity | kqm_test]
    | |- evalk _ _ _ _ (Esel _ _ _ _ _ _ _) _ _ => eapply K_sel; [reflexivity | reflexivity | reflexivity | reflexivity | kqm_norm]
    | |- evalk _ _ _ _ (Ecall _ _ _ _) _ _ =>
        first [ eapply K_call_run; [reflexivity | kqm_call | ]
              | eapply K_call_ex; [reflexivity | kqm_call_ex | intros ?M1 ?R] ]
    | |- evalk _ _ _ _ (Eloop _) _ _ =>
        first [ eapply K_loop_run; [kqm_call | reflexivity | reflexivity]
              | kqm_splitall; (eapply K_loop_run; [kqm_call | reflexivity | reflexivity]) ]
    end.

(** the helpers a program's translation wrote out, opened in the Rocq text as well (the program's file sets this) *)
Ltac kqm_unf := idtac.

Ltac kqm_head t := match t with ?f _ => kqm_head f | _ => t end.

(** Enter a function: its KQL body on the left, its Rocq definition opened one step on the right. *)
Ltac kqm_enter :=
  eapply runk_intro; [reflexivity | reflexivity | simpl kbody ];
  match goal with
  | |- evalk _ _ _ _ _ ?v ?m =>
      first [ let h := kqm_head v in progress cbn [h]
            | let h := kqm_head v in progress unfold h
            | let h := kqm_head m in progress cbn [h]
            | let h := kqm_head m in progress unfold h
            | idtac ]
  end;
  kqm_unf.

(** [kqm_prove]: induction on the recursion argument (the first variable of the goal), then the walk;
    [kqm_prove0]: no recursion. *)
Ltac kqm_prove :=
  let d := fresh "d" in
  intros d; induction d; intros; kqm_enter; kqm_walk.

Ltac kqm_prove0 := intros; kqm_enter; kqm_walk.

(** the same walk for a function that writes the memory and gives a number: the end memory is hidden *)
Ltac kqx_test :=
  kqm_red;
  first
    [ rewrite ofn_0, eqb00; kqm_red
    | rewrite ofn_S_ne0 by kqm_bound; kqm_red
    | match goal with
      | |- evalx _ _ _ _ (if ?b then _ else _) _ => destruct b eqn:?; kqm_red; kqm_known
      end
    | idtac ].

Ltac kqx_call :=
  match goal with
  | H : _ |- runx _ _ _ _ _ => eapply H; kqm_bound
  end.

Ltac kqx_walk :=
  repeat
    match goal with
    | |- evalx _ _ _ _ (Eret _) _ => apply X_ret; kqm_fin
    | |- evalx _ _ _ _ (Eop _ _ _ _ _) _ => eapply X_op; [reflexivity | reflexivity | kqm_norm]
    | |- evalx _ _ _ _ (Ekld _ _ _ _) _ => eapply X_ld; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekst _ _ _ _) _ => eapply X_st; [reflexivity | reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekld32 _ _ _ _) _ => eapply X_ld32; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekst32 _ _ _ _) _ => eapply X_st32; [reflexivity | reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Eif _ _ _ _ _) _ => eapply X_if; [reflexivity | reflexivity | kqx_test]
    | |- evalx _ _ _ _ (Esel _ _ _ _ _ _ _) _ => eapply X_sel; [reflexivity | reflexivity | reflexivity | reflexivity | kqm_norm]
    | |- evalx _ _ _ _ (Ecall _ _ _ _) _ =>
        first [ eapply X_call_run; [reflexivity | kqm_call | ]
              | eapply X_call_ex; [reflexivity | kqx_call | intros ?M1 ?R] ]
    | |- evalx _ _ _ _ (Eloop _) _ =>
        first [ eapply X_loop_run; [kqx_call | reflexivity | reflexivity]
              | kqm_splitall; (eapply X_loop_run; [kqx_call | reflexivity | reflexivity]) ]
    end.

Ltac kqx_enter :=
  eapply runx_intro; [reflexivity | reflexivity | simpl kbody ];
  match goal with
  | |- evalx _ _ _ _ _ ?v =>
      first [ let h := kqm_head v in progress cbn [h]
            | let h := kqm_head v in progress unfold h
            | idtac ]
  end;
  kqm_unf.

Ltac kqx_prove :=
  let d := fresh "d" in
  intros d; induction d; intros; kqx_enter; kqx_walk.

Ltac kqx_prove0 := intros; kqx_enter; kqx_walk.
