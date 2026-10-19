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

(** a return whose memory is compared with the text's afterwards (the two are equal, not always the same term) *)
Lemma K_ret_m : forall P f rho M M' a v,
  aval rho a = Some v -> M = M' -> evalk P f rho M (Eret a) v M'.
Proof. intros. subst. apply K_ret; auto. Qed.

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

Lemma X_hw : forall rho M o args vs k v,
  length args = hw_arity o -> avals rho args = Some vs ->
  evalx P f rho (hw_sem o vs M) k v -> evalx P f rho M (Ehw o args k) v.
Proof. intros * L A (M' & E). exists M'. eapply K_hw; eauto. Qed.

Lemma X_hwf : forall rho M o x a va k v,
  aval rho a = Some va ->
  evalx P f (PTree.set x (hwf_sem o va) rho) M k v -> evalx P f rho M (Ehwf o x a k) v.
Proof. intros * A (M' & E). exists M'. eapply K_hwf; eauto. Qed.

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
(** a choice on [a && b], [a || b], [negb a] is the same as choices on [a] and [b]: the translator writes it that way, the
    goal is rewritten to match, so no case split is needed to compare them (the splits multiply: one per test) *)
Lemma if_andb_l : forall (T : Type) (a b : bool) (x y : T), (if andb a b then x else y) = (if a then (if b then x else y) else y).
Proof. intros. destruct a; reflexivity. Qed.
Lemma if_orb_l : forall (T : Type) (a b : bool) (x y : T), (if orb a b then x else y) = (if a then x else (if b then x else y)).
Proof. intros. destruct a; reflexivity. Qed.
Lemma if_negb_l : forall (T : Type) (a : bool) (x y : T), (if negb a then x else y) = (if a then y else x).
Proof. intros. destruct a; reflexivity. Qed.
Lemma if_andb_u : forall (T : Type) (a b : bool) (x y : T), (if (if a then b else false) then x else y) = (if a then (if b then x else y) else y).
Proof. intros. destruct a; reflexivity. Qed.
Lemma if_orb_u : forall (T : Type) (a b : bool) (x y : T), (if (if a then true else b) then x else y) = (if a then x else (if b then x else y)).
Proof. intros. destruct a; reflexivity. Qed.
Lemma if_negb_u : forall (T : Type) (a : bool) (x y : T), (if (if a then false else true) then x else y) = (if a then y else x).
Proof. intros. destruct a; reflexivity. Qed.
Ltac kqm_ifs :=
  repeat first [ rewrite if_andb_l | rewrite if_orb_l | rewrite if_negb_l
               | rewrite if_andb_u | rewrite if_orb_u | rewrite if_negb_u ].

Ltac kqm_red0 := cbv beta iota delta [cmp_sem binop_sem hw_sem hwf_sem andb orb negb
  PrimInt63.ltsb PrimInt63.lesb PrimInt63.eqb PrimInt63.ltb PrimInt63.leb
  PrimInt63.land PrimInt63.lor PrimInt63.lxor PrimInt63.add PrimInt63.sub PrimInt63.mul].
Ltac kqm_red := kqm_red0.

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

(** a function later in the file has a lower bound, so that its callers' counters plus a few stay inside the callee's *)
Definition cbk (i : nat) : Z := (cb - 64 * Z.of_nat i)%Z.

(** [kq_nat x] for a number written in the program (a budget, [kq_nat 100000000]): its value, without building the number *)
Lemma kq_nat_go_val : forall k (x : i63),
  (0 <= Sint63.to_Z x < 2 ^ Z.of_nat k)%Z -> Z.of_nat (KQ.KQRun.kq_nat_go k x) = Sint63.to_Z x.
Proof.
  induction k as [|k IH]; intros x [H0 H1].
  - cbn in H1. cbn. lia.
  - cbn [KQ.KQRun.kq_nat_go].
    destruct (PrimInt63.lesb x 0%uint63) eqn:E.
    + apply Sint63.leb_spec in E. change (Sint63.to_Z 0%uint63) with 0%Z in E.
      assert (E2 : (Sint63.to_Z x <= 0)%Z) by exact E. cbn. lia.
    + assert (E' : (0 < Sint63.to_Z x)%Z).
      { destruct (Z.eq_dec (Sint63.to_Z x) 0) as [Z0 | Z0]; [ | lia].
        exfalso. assert (PrimInt63.lesb x 0%uint63 = true) as T.
        { apply Sint63.leb_spec. change (Sint63.to_Z 0%uint63) with 0%Z.
          assert (Hle : (Sint63.to_Z x <= 0)%Z) by lia. exact Hle. }
        congruence. }
      pose proof (Sint63Axioms.asr_spec x 1%uint63) as A.
      change (Sint63.to_Z 1%uint63) with 1%Z in A. change (2 ^ 1)%Z with 2%Z in A.
      rewrite Nat2Z.inj_succ in H1. rewrite Z.pow_succ_r in H1 by lia.
      assert (Hsh : (0 <= Sint63.to_Z (PrimInt63.asr x 1%uint63) < 2 ^ Z.of_nat k)%Z).
      { rewrite A. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      pose proof (IH _ Hsh) as IHv. rewrite A in IHv.
      assert (Hx : Uint63.to_Z x = Sint63.to_Z x).
      { symmetry. apply sZ_small. apply ge0_iff. lia. }
      assert (HL : Uint63.to_Z (PrimInt63.land x 1%uint63) = Z.land (Uint63.to_Z x) 1%Z).
      { rewrite Uint63.land_spec'. reflexivity. }
      assert (HM : Z.land (Sint63.to_Z x) 1%Z = (Sint63.to_Z x) mod 2).
      { change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. }
      rewrite Hx in HL. rewrite HM in HL.
      pose proof (Z.div_mod (Sint63.to_Z x) 2 ltac:(lia)) as DM.
      pose proof (Z.mod_pos_bound (Sint63.to_Z x) 2 ltac:(lia)) as MB.
      destruct (PrimInt63.eqb (PrimInt63.land x 1%uint63) 1%uint63) eqn:P.
      * apply Uint63.eqb_spec in P. rewrite P in HL. change (Uint63.to_Z 1%uint63) with 1%Z in HL.
        rewrite Nat2Z.inj_succ, Nat2Z.inj_add, IHv. lia.
      * assert (Q : Uint63.to_Z (PrimInt63.land x 1%uint63) <> 1%Z).
        { intro Hc. assert (Hc' : PrimInt63.land x 1%uint63 = 1%uint63) by (apply Uint63.to_Z_inj; exact Hc).
          apply Uint63.eqb_spec in Hc'. congruence. }
        rewrite Nat2Z.inj_add, IHv. lia.
Qed.

Local Strategy 0 [KQ.KQRun.kq_nat].
Lemma kq_nat_val : forall x : i63, (0 <= Sint63.to_Z x < 2 ^ 62)%Z -> Z.of_nat (KQ.KQRun.kq_nat x) = Sint63.to_Z x.
Proof.
  intros x H. unfold KQ.KQRun.kq_nat. apply kq_nat_go_val.
  change (Z.of_nat 63) with 63%Z. split; [lia | ]. destruct H as [_ H]. eapply Z.lt_trans; [exact H | ]. vm_compute. reflexivity.
Qed.

Local Strategy opaque [KQ.KQRun.kq_nat].

(** a budget written as a number is looked up first: [lia] on a goal that holds [kq_nat 100000000] is not safe *)
Ltac kqm_bound := first
  [ (match goal with
     | |- context [Z.of_nat (KQ.KQRun.kq_nat ?x)] =>
         rewrite (kq_nat_val x) by (vm_compute; split; [ (intros; discriminate) | reflexivity ]); vm_compute; reflexivity
     end)
  | (match goal with
     | |- context [Z.of_nat (KQ.KQRun.kq_nat_go 63 ?x)] =>
         rewrite (kq_nat_go_val 63 x) by (vm_compute; split; [ (intros; discriminate) | reflexivity ]); vm_compute; reflexivity
     end)
  | (pose proof wB_num; try unfold cbk in *; unfold cb in *; lia)
  | (vm_compute; reflexivity) ].

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
(** The hypothesis is chosen by the callee's number [g], which both must show: a hypothesis for another function is
    never tried (trying it makes Rocq unfold the program's function table to see the two differ). *)
Ltac kqm_call :=
  match goal with
  | |- runk _ ?g _ _ _ _ =>
      tryif is_evar g then (match goal with H : _ |- _ => eapply H; kqm_bound end)
      else (match goal with H : context [runk _ g _ _ _ _] |- _ => eapply H; kqm_bound end)
  end.

Ltac kqm_call_ex :=
  match goal with
  | |- exists M1, runk _ ?g _ _ _ M1 =>
      tryif is_evar g then (match goal with H : _ |- _ => eapply H; kqm_bound end)
      else (match goal with H : context [runk _ g _ _ _ _] |- _ => eapply H; kqm_bound end)
  end.

(** the value of a chosen number against the Rocq text: equal as they stand, or after a split on each test *)
Ltac kqm_inner c := lazymatch c with context [if ?d then _ else _] => kqm_inner d | _ => c end.
Ltac kqm_fin :=
  first [ (kqm_ifs; kqm_red; exact eq_refl)
        | exact eq_refl
        | kqm_ifs; kqm_red;
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
    | H : false = true |- _ => discriminate H
    | H : true = false |- _ => discriminate H
    | |- evalk _ _ _ _ (Eret _) _ _ => eapply K_ret_m; [ kqm_fin | kqm_fin ]
    | |- evalk _ _ _ _ (Eop _ _ _ _ _) _ _ => eapply K_op; [reflexivity | reflexivity | kqm_norm]
    | |- evalk _ _ _ _ (Ekld _ _ _ _) _ _ => eapply K_ld; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekst _ _ _ _) _ _ => eapply K_st; [reflexivity | reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekld32 _ _ _ _) _ _ => eapply K_ld32; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekst32 _ _ _ _) _ _ => eapply K_st32; [reflexivity | reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ehw _ _ _) _ _ => eapply K_hw; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ehwf _ _ _ _) _ _ => eapply K_hwf; [reflexivity | ]
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
      first [ let h := kqm_head v in progress unfold h
            | let h := kqm_head v in progress cbn [h]
            | let h := kqm_head m in progress unfold h
            | let h := kqm_head m in progress cbn [h]
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
  | |- runx _ ?g _ _ _ =>
      tryif is_evar g then (match goal with H : _ |- _ => eapply H; kqm_bound end)
      else (match goal with H : context [runx _ g _ _ _] |- _ => eapply H; kqm_bound end)
  end.

Ltac kqx_walk :=
  repeat
    match goal with
    | H : false = true |- _ => discriminate H
    | H : true = false |- _ => discriminate H
    | |- evalx _ _ _ _ (Eret _) _ => apply X_ret; kqm_fin
    | |- evalx _ _ _ _ (Eop _ _ _ _ _) _ => eapply X_op; [reflexivity | reflexivity | kqm_norm]
    | |- evalx _ _ _ _ (Ekld _ _ _ _) _ => eapply X_ld; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekst _ _ _ _) _ => eapply X_st; [reflexivity | reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekld32 _ _ _ _) _ => eapply X_ld32; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekst32 _ _ _ _) _ => eapply X_st32; [reflexivity | reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ehw _ _ _) _ => eapply X_hw; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ehwf _ _ _ _) _ => eapply X_hwf; [reflexivity | ]
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
      first [ let h := kqm_head v in progress unfold h
            | let h := kqm_head v in progress cbn [h]
            | idtac ]
  end;
  kqm_unf.

Ltac kqx_prove :=
  let d := fresh "d" in
  intros d; induction d; intros; kqx_enter; kqx_walk.

Ltac kqx_prove0 := intros; kqx_enter; kqx_walk.
