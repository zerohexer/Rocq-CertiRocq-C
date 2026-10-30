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
From KQC Require Import KQL KQLAuto KQMSem KQTArith KQMNames.
Import ListNotations.

(** ** The laws of the kit's memory, as rewrite rules on its own functions *)

Lemma upd_upd_r : forall h i v w s, KQ.KQRun.upd h i v (KQ.KQRun.upd h i w s) = KQ.KQRun.upd h i v s.
Proof. intros. exact (KQ.KQSpec.upd_upd KQ.KQSpec.real KQ.KQSpec.real_laws h i v w s). Qed.
Lemma upd_rd_id_r : forall h i s, KQ.KQRun.upd h i (KQ.KQRun.rd h i s) s = s.
Proof. intros. exact (KQ.KQSpec.upd_rd_id KQ.KQSpec.real KQ.KQSpec.real_laws h i s). Qed.
Lemma size_upd_r : forall h i v h' s, KQ.KQRun.kq_size h' (KQ.KQRun.upd h i v s) = KQ.KQRun.kq_size h' s.
Proof. intros. exact (KQ.KQSpec.size_upd KQ.KQSpec.real KQ.KQSpec.real_laws h i v h' s). Qed.
Lemma size_upd32_r : forall h i v h' s, KQ.KQRun.kq_size h' (KQ.KQRun.upd32 h i v s) = KQ.KQRun.kq_size h' s.
Proof. intros. exact (KQ.KQSpec.size_upd32 KQ.KQSpec.real KQ.KQSpec.real_laws h i v h' s). Qed.
(** the slot block (63): a cell just written holds what was written, when the block has room *)
Lemma rd_slot0 : forall (v : i63) s, (1 < Sint63.to_Z (KQ.KQRun.kq_size 63%uint63 s))%Z ->
  KQ.KQRun.rd 63%uint63 0%uint63 (KQ.KQRun.upd 63%uint63 0%uint63 v s) = v.
Proof.
  intros v s H. apply (KQ.KQSpec.rd_upd_eq KQ.KQSpec.real KQ.KQSpec.real_laws).
  unfold KQ.KQSpec.cell. cbn [KQ.KQSpec.Size KQ.KQSpec.real].
  assert (E : PrimInt63.ltsb 0%uint63 (KQ.KQRun.kq_size 63%uint63 s) = true).
  { apply (proj2 (Sint63.ltb_spec _ _)). apply Z.compare_lt_iff. assert (Z0 : Sint63.to_Z 0%uint63 = 0%Z) by reflexivity. lia. }
  rewrite E. reflexivity.
Qed.

(** with a function that gives back two numbers (the second goes through the slot block): the laws are used on the memory
    the proof walks and the pairs are taken apart; switched on by the program's file when it has such a function *)
(** a block is never smaller than it was when the program started (KQSpec.v len_size) *)
Lemma size_ge_len : forall (h : i63) s, (Sint63.to_Z (KQ.KQBound.kq_len h) <= Sint63.to_Z (KQ.KQRun.kq_size h s))%Z.
Proof.
  intros h s. pose proof (KQ.KQSpec.len_size KQ.KQSpec.real KQ.KQSpec.real_laws h s) as H.
  apply KQ.KQSpec.le_Z in H. exact H.
Qed.
Ltac kqm_size :=
  first [ assumption
        | (match goal with |- (1 < Sint63.to_Z (KQ.KQRun.kq_size ?h ?s))%Z => pose proof (size_ge_len h s); Stdlib.micromega.Lia.lia end)
        | (repeat (rewrite size_upd_r || rewrite size_upd32_r); first [assumption | lia]) ].
Ltac kqm_laws := idtac.
Ltac kqm_pairs := idtac.
Ltac kqm_laws_on :=
  repeat (rewrite upd_upd_r || rewrite upd_rd_id_r || rewrite rd_slot0 by kqm_size).
Ltac kqm_pairs_on :=
  repeat match goal with
         | |- context [match ?p with _ => _ end] =>
             match type of p with bool => fail 1 | nat => fail 1 | _ => destruct p end
         end.

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

Lemma X_w64 : forall rho M o xl xh al ah bl bh (ra rb : KQ.KQRun.u64) k v,
  xl <> xh -> aval rho al = Some (KQ.KQRun.w_lo ra) -> aval rho ah = Some (KQ.KQRun.w_hi ra) ->
  aval rho bl = Some (KQ.KQRun.w_lo rb) -> aval rho bh = Some (KQ.KQRun.w_hi rb) ->
  evalx P f (PTree.set xh (KQ.KQRun.w_hi (KQ.KQRun.w64_op o ra rb))
              (PTree.set xl (KQ.KQRun.w_lo (KQ.KQRun.w64_op o ra rb)) rho)) M k v ->
  evalx P f rho M (Ew64 o xl xh al ah bl bh k) v.
Proof. intros * N A B C D (M' & E). exists M'. eapply K_w64; eauto. Qed.
Lemma X_ld8 : forall rho M x h i vh vi k v,
  aval rho h = Some vh -> aval rho i = Some vi ->
  evalx P f (PTree.set x (KQ.KQRun.rd8 vh vi M) rho) M k v -> evalx P f rho M (Ekld8 x h i k) v.
Proof. intros * A B (M' & E). exists M'. eapply K_ld8; eauto. Qed.
Lemma X_size : forall rho M x h vh k v,
  aval rho h = Some vh ->
  evalx P f (PTree.set x (KQ.KQRun.kq_size vh M) rho) M k v -> evalx P f rho M (Eksize x h k) v.
Proof. intros * A (M' & E). exists M'. eapply K_size; eauto. Qed.
Lemma X_st8 : forall rho M h i a vh vi va k v,
  aval rho h = Some vh -> aval rho i = Some vi -> aval rho a = Some va ->
  evalx P f rho (KQ.KQRun.upd8 vh vi va M) k v -> evalx P f rho M (Ekst8 h i a k) v.
Proof. intros * A B C (M' & E). exists M'. eapply K_st8; eauto. Qed.
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

Lemma X_hwf : forall rho M o x args vs k v,
  length args = hwf_arity o -> avals rho args = Some vs ->
  evalx P f (PTree.set x (hwf_sem o vs) rho) M k v -> evalx P f rho M (Ehwf o x args k) v.
Proof. intros * L A (M' & E). exists M'. eapply K_hwf; eauto. Qed.

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

(** a boolean a function gives back is the number 1 or 0 its KQL returns; the statement says so with [kq_b2i] *)
Definition kq_b2i (b : bool) : i63 := if b then 1%uint63 else 0%uint63.
(** a test of such a number against 0 is the test of the boolean itself *)
Lemma b2i_eqb0 : forall (c : bool) (T : Type) (x y : T),
  (if PrimInt63.eqb (if c then 1%uint63 else 0%uint63) 0%uint63 then x else y) = (if c then y else x).
Proof. intros. destruct c; reflexivity. Qed.

Ltac kqm_red0 := cbv beta iota delta [kq_b2i cmp_sem binop_sem hw_sem hwf_sem andb orb negb fst snd KQ.KQRun.rd16 KQ.KQRun.upd16
  KQ.KQRun.u64_add KQ.KQRun.u64_sub KQ.KQRun.u64_mul KQ.KQRun.u64_and KQ.KQRun.u64_or KQ.KQRun.u64_xor KQ.KQRun.u64_shl
  KQ.KQRun.u64_shr KQ.KQRun.u64_ltb KQ.KQRun.u64_leb KQ.KQRun.u64_eqb KQ.KQRun.u64_of_int KQ.KQRun.u64_to_int KQ.KQRun.u64_of_halves
  KQ.KQRun.u64_lo32 KQ.KQRun.u64_hi32 KQ.KQRun.w_lo KQ.KQRun.w_hi
  PrimInt63.ltsb PrimInt63.lesb PrimInt63.eqb PrimInt63.ltb PrimInt63.leb
  PrimInt63.land PrimInt63.lor PrimInt63.lxor PrimInt63.add PrimInt63.sub PrimInt63.mul].
Ltac kqm_red := kqm_red0; kqm_laws.

(** a test already split on is known: every later copy of it in the goal is replaced by its outcome *)
Ltac kqm_known :=
  progress (repeat match goal with
         | H : ?c = _ |- _ =>
             lazymatch type of c with
             | bool => lazymatch goal with |- context [c] => progress rewrite H end
             end
         end);
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
Definition cap60 : i63 := 1152921504606846976%uint63.
Lemma lesb_le : forall a b : i63, (Sint63.to_Z a <= Sint63.to_Z b)%Z -> PrimInt63.lesb a b = true.
Proof. intros a b H. apply Sint63.leb_spec. exact H. Qed.
Lemma lesb_le_inv : forall a b : i63, PrimInt63.lesb a b = true -> (Sint63.to_Z a <= Sint63.to_Z b)%Z.
Proof. intros a b H. apply Sint63.leb_spec in H. exact H. Qed.
Lemma ltsb_lt : forall a b : i63, (Sint63.to_Z a < Sint63.to_Z b)%Z -> PrimInt63.ltsb a b = true.
Proof. intros a b H. apply Sint63.ltb_spec. exact H. Qed.
Lemma ltsb_lt_inv : forall a b : i63, PrimInt63.ltsb a b = true -> (Sint63.to_Z a < Sint63.to_Z b)%Z.
Proof. intros a b H. apply Sint63.ltb_spec in H. exact H. Qed.
Lemma cap60_val : Sint63.to_Z cap60 = 1152921504606846976%Z.
Proof. reflexivity. Qed.
Lemma kq_nat_val : forall x : i63, (0 <= Sint63.to_Z x <= 2 ^ 60)%Z -> Z.of_nat (KQ.KQRun.kq_nat x) = Sint63.to_Z x.
Proof.
  intros x H. unfold KQ.KQRun.kq_nat.
  assert (E : (PrimInt63.lesb x cap60) = true).
  { apply lesb_le. rewrite cap60_val. destruct H as [_ H]. change (2 ^ 60)%Z with 1152921504606846976%Z in H. lia. }
  change 1152921504606846976%uint63 with cap60. rewrite E. apply kq_nat_go_val.
  change (Z.of_nat 63) with 63%Z. split; [lia | ]. destruct H as [_ H]. eapply Z.le_lt_trans; [exact H | ]. vm_compute. reflexivity.
Qed.

Lemma kq_nat_go_S : forall k x, KQ.KQRun.kq_nat_go (S k) x =
  match PrimInt63.lesb x 0%uint63 with
  | true => O
  | false => let h := KQ.KQRun.kq_nat_go k (PrimInt63.asr x 1%uint63) in
             match PrimInt63.eqb (PrimInt63.land x 1%uint63) 1%uint63 with true => S (Nat.add h h) | false => Nat.add h h end
  end.
Proof. intros. reflexivity. Qed.

(** the clamped number *)
Definition clampb (x : i63) : i63 := if (PrimInt63.lesb x cap60) then x else cap60.
Lemma clampb_le : forall x, (Sint63.to_Z (clampb x) <= 2 ^ 60)%Z.
Proof.
  intros x. unfold clampb. destruct (PrimInt63.lesb x cap60) eqn:E.
  - apply lesb_le_inv in E. rewrite cap60_val in E. change (2 ^ 60)%Z with 1152921504606846976%Z. lia.
  - rewrite cap60_val. change (2 ^ 60)%Z with 1152921504606846976%Z. lia.
Qed.
Lemma kq_nat_clamp : forall x, KQ.KQRun.kq_nat x = KQ.KQRun.kq_nat_go 63 (clampb x).
Proof. intros x. reflexivity. Qed.

(** whatever the number, the counter is at most 2^60 *)
Lemma kq_nat_le : forall x : i63, (Z.of_nat (KQ.KQRun.kq_nat x) <= 2 ^ 60)%Z.
Proof.
  intros x. rewrite kq_nat_clamp. pose proof (clampb_le x) as Hy. pose proof (sZ_bound (clampb x)) as SB.
  set (y := clampb x) in *. clearbody y.
  destruct (PrimInt63.lesb y 0%uint63) eqn:E.
  - change 63%nat with (S 62%nat). rewrite kq_nat_go_S, E. cbn. lia.
  - assert (E' : (0 < Sint63.to_Z y)%Z).
    { destruct (Z_le_gt_dec (Sint63.to_Z y) 0) as [H | H]; [ | lia ].
      exfalso. assert (PrimInt63.lesb y 0%uint63 = true) as T.
      { apply lesb_le. change (Sint63.to_Z 0%uint63) with 0%Z. lia. }
      congruence. }
    rewrite kq_nat_go_val.
    + lia.
    + change (Z.of_nat 63) with 63%Z. split; [lia | ]. eapply Z.le_lt_trans; [exact Hy | ]. vm_compute. reflexivity.
Qed.

(** a counter worked out while the program runs is below the bound of any function placed early in the file *)
Lemma kq_nat_cbk : forall (x : i63) (i : nat), Nat.leb i 1000000 = true -> (Z.of_nat (KQ.KQRun.kq_nat x) < cbk i)%Z.
Proof.
  intros x i H. apply Nat.leb_le in H. pose proof (kq_nat_le x) as P.
  assert (Hi : (Z.of_nat i <= 1000000)%Z) by (change 1000000%Z with (Z.of_nat 1000000); apply Nat2Z.inj_le; exact H).
  unfold cbk, cb. change (2 ^ 60)%Z with 1152921504606846976%Z in P. lia.
Qed.

(** the budget atom is the counter [kq_nat n] (KQL.v [bud]) *)
Lemma bud_ofn : forall n : i63, bud n = ofn (KQ.KQRun.kq_nat n).
Proof.
  intros n. unfold bud, ofn. change 1152921504606846976%uint63 with cap60.
  destruct (PrimInt63.lesb n 0%uint63) eqn:E.
  - rewrite kq_nat_clamp. change 63%nat with (S 62%nat). 
    assert (Ec : PrimInt63.lesb (clampb n) 0%uint63 = true).
    { unfold clampb. destruct (PrimInt63.lesb n cap60) eqn:E2; [exact E | ].
      exfalso. apply lesb_le_inv in E. change (Sint63.to_Z 0%uint63) with 0%Z in E.
      assert (T : PrimInt63.lesb n cap60 = true) by (apply lesb_le; rewrite cap60_val; lia).
      congruence. }
    rewrite kq_nat_go_S, Ec. reflexivity.
  - assert (E' : (0 < Sint63.to_Z n)%Z).
    { destruct (Z_le_gt_dec (Sint63.to_Z n) 0) as [H | H]; [ | lia ].
      exfalso. assert (PrimInt63.lesb n 0%uint63 = true) as T.
      { apply lesb_le. change (Sint63.to_Z 0%uint63) with 0%Z. lia. }
      congruence. }
    pose proof (sZ_bound n) as SB.
    destruct (PrimInt63.lesb n cap60) eqn:E2.
    + assert (Hn : (Sint63.to_Z n <= 2 ^ 60)%Z).
      { apply lesb_le_inv in E2. rewrite cap60_val in E2. change (2 ^ 60)%Z with 1152921504606846976%Z. lia. }
      rewrite (kq_nat_val n) by lia.
      symmetry. exact (Sint63.of_to_Z n).
    + assert (Hn : (2 ^ 60 < Sint63.to_Z n)%Z).
      { destruct (Z_le_gt_dec (Sint63.to_Z n) (2 ^ 60)) as [H | H]; [ | lia ].
        exfalso. assert (PrimInt63.lesb n cap60 = true) as T.
        { apply lesb_le. rewrite cap60_val. change (2 ^ 60)%Z with 1152921504606846976%Z in H. lia. }
        congruence. }
      change cap60 with cap60.
      assert (Hc : clampb n = cap60) by (unfold clampb; rewrite E2; reflexivity).
      assert (Hv : Z.of_nat (KQ.KQRun.kq_nat n) = 1152921504606846976%Z).
      { rewrite kq_nat_clamp, Hc. rewrite kq_nat_go_val.
        - exact cap60_val.
        - rewrite cap60_val. split; [lia | ]. vm_compute. reflexivity. }
      rewrite Hv. symmetry. exact (Sint63.of_to_Z cap60).
Qed.

(** the program's expression for a budget worked out while it runs: clamped from below by 0 and from above by 2^60 *)
Lemma bud_if : forall n : i63,
  (if PrimInt63.ltsb cap60 (if PrimInt63.lesb n 0%uint63 then 0%uint63 else n) then cap60
   else (if PrimInt63.lesb n 0%uint63 then 0%uint63 else n)) = ofn (KQ.KQRun.kq_nat n).
Proof.
  intros n. rewrite <- bud_ofn. unfold bud. change 1152921504606846976%uint63 with cap60.
  destruct (PrimInt63.lesb n 0%uint63) eqn:E.
  - reflexivity.
  - assert (E' : (0 < Sint63.to_Z n)%Z).
    { destruct (Z_le_gt_dec (Sint63.to_Z n) 0) as [H | H]; [ | lia ].
      exfalso. assert (PrimInt63.lesb n 0%uint63 = true) as T.
      { apply lesb_le. change (Sint63.to_Z 0%uint63) with 0%Z. lia. }
      congruence. }
    destruct (PrimInt63.lesb n cap60) eqn:E2.
    + apply lesb_le_inv in E2. rewrite cap60_val in E2.
      destruct (PrimInt63.ltsb cap60 n) eqn:E3; [ | reflexivity].
      apply ltsb_lt_inv in E3. rewrite cap60_val in E3. exfalso. lia.
    + destruct (PrimInt63.ltsb cap60 n) eqn:E3; [reflexivity | ].
      exfalso. apply Bool.not_true_iff_false in E3. assert (E3' : ~ (Sint63.to_Z cap60 < Sint63.to_Z n)%Z) by (intro Hc; apply E3; apply ltsb_lt; exact Hc). rewrite cap60_val in E3'. 
      assert (T : PrimInt63.lesb n cap60 = true).
      { apply lesb_le. rewrite cap60_val. lia. }
      congruence.
Qed.
Local Strategy opaque [KQ.KQRun.kq_nat].

(** a budget written as a number is looked up first: [lia] on a goal that holds [kq_nat 100000000] is not safe *)
Ltac kqm_bound := first
  [ (match goal with |- (1 < Sint63.to_Z (KQ.KQBound.kq_len _))%Z => assumption end)
  | (match goal with |- _ /\ _ => split; kqm_bound end)
  | (match goal with |- (1 < Sint63.to_Z (KQ.KQRun.kq_size _ _))%Z => kqm_size end)
  | (match goal with |- (Z.of_nat (KQ.KQRun.kq_nat ?x) < cbk ?i)%Z => apply (kq_nat_cbk x i); vm_compute; reflexivity end)
  | (match goal with |- context [Z.of_nat (KQ.KQRun.kq_nat ?x)] => pose proof (kq_nat_le x); pose proof wB_num; try unfold cbk in *; unfold cb in *; lia end)
  | (match goal with
     | |- context [Z.of_nat (KQ.KQRun.kq_nat ?x)] =>
         rewrite (kq_nat_val x) by (vm_compute; split; intros; discriminate); vm_compute; reflexivity
     end)
  | (match goal with
     | |- context [Z.of_nat (KQ.KQRun.kq_nat_go 63 ?x)] =>
         rewrite (kq_nat_go_val 63 x) by (vm_compute; split; [ (intros; discriminate) | reflexivity ]); vm_compute; reflexivity
     end)
  | (pose proof wB_num; try unfold cbk in *; unfold cb in *; lia)
  | (vm_compute; reflexivity) ].

(* a counter worked out while the program runs is bounded for any number *)
Lemma kqm_bound_lit : (Z.of_nat (KQ.KQRun.kq_nat 100000000) < cbk 3)%Z.
Proof. kqm_bound. Qed.
Lemma kqm_bound_runtime : forall x : i63, (Z.of_nat (KQ.KQRun.kq_nat x) < cbk 2)%Z.
Proof. intros x. kqm_bound. Qed.

Lemma eqb00 : PrimInt63.eqb 0%uint63 0%uint63 = true.
Proof. reflexivity. Qed.

(** a test: the counter cases of the induction decide their own tests; any other test is split in the goal *)
Ltac kqm_test :=
  kqm_red;
  first
    [ rewrite ofn_0, eqb00; kqm_red
    | rewrite ofn_S_ne0 by kqm_bound; kqm_red
    | (* a test of a boolean held as 1 or 0: the test of the boolean (the shape is looked at first, so this costs nothing
         when it does not apply) *)
      lazymatch goal with
      | |- evalk _ _ _ _ (if PrimInt63.eqb (if _ then 1%uint63 else 0%uint63) 0%uint63 then _ else _) _ _ => rewrite b2i_eqb0
      end;
      match goal with
      | |- evalk _ _ _ _ (if ?b then _ else _) _ _ => destruct b eqn:?; kqm_red; try kqm_known
      end
    | match goal with
      | |- evalk _ _ _ _ (if ?b then _ else _) _ _ => destruct b eqn:?; kqm_red; try kqm_known
      end
    | idtac ].

(** the counter rewrites are tried only where a counter is added to or taken from: asking Rocq to rewrite scans (and
    unifies against) every addition of the goal, which is most of the time of a long run of arithmetic *)
Ltac kqm_norm :=
  kqm_red; try kqm_known;
  tryif (match goal with _ : nat |- _ => idtac end) then
  repeat first [ (lazymatch goal with |- context [PrimInt63.sub (KQLAuto.ofn (S _)) _] => rewrite ofn_pred by kqm_bound end)
               | (lazymatch goal with |- context [PrimInt63.add (KQLAuto.ofn _) _] => rewrite ofn_succ by kqm_bound end) ]
  else idtac.

(** a call or a loop: some hypothesis in the context proves it -- a callee's statement (put there with
    [pose proof]) or the induction hypothesis *)
(** The hypothesis is chosen by the callee's number [g], which both must show: a hypothesis for another function is
    never tried (trying it makes Rocq unfold the program's function table to see the two differ). *)
Ltac kqm_call :=
  try rewrite !bud_ofn; try rewrite !bud_if;
  match goal with
  | |- runk _ ?g _ _ _ _ =>
      tryif is_evar g then (match goal with H : _ |- _ => eapply H; kqm_bound end)
      else (match goal with H : context [runk _ g _ _ _ _] |- _ => eapply H; kqm_bound end)
  end.

Ltac kqm_call_ex :=
  try rewrite !bud_ofn; try rewrite !bud_if;
  match goal with
  | |- exists M1, runk _ ?g _ _ _ M1 =>
      tryif is_evar g then (match goal with H : _ |- _ => eapply H; kqm_bound end)
      else (match goal with H : context [runk _ g _ _ _ _] |- _ => eapply H; kqm_bound end)
  end.

(** a test just split on (E : test = outcome) is also put into the earlier hypotheses that mention it: one that then
    says [false = true] closes the branch (a test repeated in the Rocq text that the walk had already chosen on) *)
Ltac kqm_hyps_known :=
  repeat match goal with
         | E : ?c = _ |- _ =>
             lazymatch type of c with bool => idtac end;
             match goal with
             | H : context [c] |- _ =>
                 assert_fails (constr_eq E H);
                 progress rewrite E in H;
                 cbv beta iota delta [cmp_sem binop_sem hw_sem hwf_sem andb orb negb
                   PrimInt63.ltsb PrimInt63.lesb PrimInt63.eqb PrimInt63.ltb PrimInt63.leb
                   PrimInt63.land PrimInt63.lor PrimInt63.lxor PrimInt63.add PrimInt63.sub PrimInt63.mul] in H
             end
         end;
  try (match goal with H : false = true |- _ => discriminate H end).

(** the value of a chosen number against the Rocq text: equal as they stand, or after a split on each test *)
(** a test already split on is known also where it is written differently but is the same by computation (a u64 built from
    its two numbers against the u64 itself) *)
Ltac kqm_known_conv :=
  repeat match goal with
         | E : ?c = ?b |- context [if ?c' then _ else _] =>
             lazymatch type of c with bool => idtac end;
             tryif constr_eq c c' then fail else
             (let Ec := fresh "Ec" in assert (Ec : c' = b) by (exact E); rewrite Ec; clear Ec)
         end.

Ltac kqm_inner c := lazymatch c with context [if ?d then _ else _] => kqm_inner d | _ => c end.
Ltac kqm_fin :=
  kqm_red; kqm_pairs; kqm_red;
  first [ (try kqm_known; kqm_ifs; kqm_red; try kqm_known; exact eq_refl)
        | exact eq_refl
        | try kqm_known; kqm_ifs; kqm_red; try kqm_known;
          repeat (first [ exact eq_refl
                        | match goal with
                          | |- context [if ?c then _ else _] =>
                              let d := kqm_inner c in (match type of d with bool => idtac end); destruct d eqn:?E; kqm_red; try kqm_known; try kqm_known_conv; kqm_hyps_known
                          end ]);
          first [ exact eq_refl | reflexivity ] ].

(** split on every test left in the goal (innermost first), the way [kqm_fin] does at a return: a merged choice of
    arguments is compared with the Rocq text that chooses between two calls *)
Ltac kqm_splitall :=
  kqm_red; kqm_pairs; kqm_red;
  repeat (match goal with
          | |- context [if ?c then _ else _] =>
              let d := kqm_inner c in (match type of d with bool => idtac end); destruct d; kqm_red; try kqm_known
          end).

(** the arguments of a loop are the numbers the callee's statement names: equal as they stand, or one by one (the numbers of a
    u64 are long terms, which are compared one at a time) *)
Ltac kqm_unf := idtac.
Ltac kqm_unf_nz := idtac.
Ltac kqm_avals := first [ reflexivity | (cbn [KQL.avals KQL.aval]; apply f_equal; repeat (apply f_equal2); first [reflexivity | (kqm_unf; kqm_fin) | kqm_fin]) ].

(** a 64-bit operation: each operand is the record both of whose numbers are fields of it (a result of an earlier operation, a
    parameter), or two numbers written as they are (a constant, a number computed apart) *)
Ltac kqm_w64k :=
  kqm_red;
  first [ eapply K_w64; [discriminate | reflexivity | reflexivity | reflexivity | reflexivity | ]
        | eapply K_w64 with (ra := KQ.KQRun.mk_u64 _ _); [discriminate | reflexivity | reflexivity | reflexivity | reflexivity | ]
        | eapply K_w64 with (rb := KQ.KQRun.mk_u64 _ _); [discriminate | reflexivity | reflexivity | reflexivity | reflexivity | ]
        | eapply K_w64 with (ra := KQ.KQRun.mk_u64 _ _) (rb := KQ.KQRun.mk_u64 _ _); [discriminate | reflexivity | reflexivity | reflexivity | reflexivity | ] ].
Ltac kqm_w64x :=
  kqm_red;
  first [ eapply X_w64; [discriminate | reflexivity | reflexivity | reflexivity | reflexivity | ]
        | eapply X_w64 with (ra := KQ.KQRun.mk_u64 _ _); [discriminate | reflexivity | reflexivity | reflexivity | reflexivity | ]
        | eapply X_w64 with (rb := KQ.KQRun.mk_u64 _ _); [discriminate | reflexivity | reflexivity | reflexivity | reflexivity | ]
        | eapply X_w64 with (ra := KQ.KQRun.mk_u64 _ _) (rb := KQ.KQRun.mk_u64 _ _); [discriminate | reflexivity | reflexivity | reflexivity | reflexivity | ] ].

Ltac kqm_step :=
    match goal with
    | H : false = true |- _ => discriminate H
    | H : true = false |- _ => discriminate H
    | |- evalk _ _ _ _ (Eret _) _ _ => eapply K_ret_m; [ kqm_fin | kqm_fin ]
    | |- evalk _ _ _ _ (Eop _ _ _ _ _) _ _ => eapply K_op; [reflexivity | reflexivity | kqm_norm]
    | |- evalk _ _ _ _ (Ekld _ _ _ _) _ _ => eapply K_ld; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekst _ _ _ _) _ _ => eapply K_st; [reflexivity | reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekld32 _ _ _ _) _ _ => eapply K_ld32; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekst32 _ _ _ _) _ _ => eapply K_st32; [reflexivity | reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ew64 _ _ _ _ _ _ _ _) _ _ => kqm_w64k
    | |- evalk _ _ _ _ (Ekld8 _ _ _ _) _ _ => eapply K_ld8; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ekst8 _ _ _ _) _ _ => eapply K_st8; [reflexivity | reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Eksize _ _ _) _ _ => eapply K_size; [reflexivity | ]
    | |- evalk _ _ _ _ (Ehw _ _ _) _ _ => eapply K_hw; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Ehwf _ _ _ _) _ _ => eapply K_hwf; [reflexivity | reflexivity | ]
    | |- evalk _ _ _ _ (Eif _ _ _ _ _) _ _ => eapply K_if; [reflexivity | reflexivity | kqm_test]
    | |- evalk _ _ _ _ (Esel _ _ _ _ _ _ _) _ _ => eapply K_sel; [reflexivity | reflexivity | reflexivity | reflexivity | kqm_norm]
    | |- evalk _ _ _ _ (Ecall _ _ _ _) _ _ =>
        first [ eapply K_call_run; [reflexivity | kqm_call | ]
              | eapply K_call_ex; [reflexivity | kqm_call_ex | intros ?M1 ?R] ]
    | |- evalk _ _ _ _ (Eloop _) _ _ =>
        first [ eapply K_loop_run; [kqm_call | reflexivity | kqm_avals]
              | kqm_splitall; (eapply K_loop_run; [kqm_call | reflexivity | kqm_avals]) ]
    end.

(** A run of bindings [PTree.set x v (PTree.set y w ..)] is looked up by working all of it out, every time: the longer a
    function, the longer each step.  So the chain is worked out into a tree once in a while (the values stay as they are),
    and a lookup walks a tree and at most a few bindings above it. *)
Ltac kqm_rho_depth r :=
  lazymatch r with
  | Maps.PTree.set _ _ ?r' => let d := kqm_rho_depth r' in constr:(S d)
  | _ => constr:(0%nat)
  end.
Ltac kqm_compact_rho r :=
  let d := kqm_rho_depth r in
  let big := eval vm_compute in (Nat.leb 24%nat d) in
  lazymatch big with
  | true => let r' := eval cbv beta iota delta [Maps.PTree.set Maps.PTree.set' Maps.PTree.set0 Maps.PTree.empty] in r in change r with r'
  | false => idtac
  end.
Ltac kqm_compact :=
  try (lazymatch goal with
       | |- evalk _ _ ?r _ _ _ _ => kqm_compact_rho r
       | |- evalx _ _ ?r _ _ _ => kqm_compact_rho r
       end).
(** the walk's own memory, when it is the memory of a named [let] of the text (KQMNames.v), takes its name *)
Ltac kqm_share_mem M :=
  tryif is_var M then idtac else
  match goal with
  | s := _ : KQ.KQRun.mem |- _ => change M with s
  end.
Ltac kqm_share :=
  try (lazymatch goal with
       | |- evalk _ _ _ ?M _ _ _ => kqm_share_mem M
       | |- evalx _ _ _ ?M _ _ => kqm_share_mem M
       end).
Ltac kqm_walk := repeat (kqm_compact; kqm_share; kqm_step).

(** the helpers a program's translation wrote out, opened in the Rocq text as well (the program's file sets this) *)
(** the program's file sets this to open its functions that give back two numbers (their statements say [fst] / [snd] of them) *)
Ltac kqm_unf2 := idtac.

Ltac kqm_head t := match t with ?f _ => kqm_head f | _ => t end.
(** the function a statement is about: the head of its value, inside [kq_b2i] for a function giving back a boolean *)
Ltac kqm_vhead v := lazymatch v with kq_b2i ?c => kqm_head c | _ => kqm_head v end.

(** Enter a function: its KQL body on the left, its Rocq definition opened one step on the right. *)
(** how the function of a statement is opened: unfolded, or (when pairs are taken apart in the goal, which would change a
    copy of the function's own text) one step by [cbn], so that its recursive calls stay the function *)
Ltac kqm_uh h := unfold h.
Ltac kqm_enter :=
  eapply runk_intro; [reflexivity | reflexivity | simpl kbody ];
  match goal with
  | |- evalk _ _ _ _ _ ?v ?m =>
      first [ let h := kqm_vhead v in progress kqm_uh h
            | let h := kqm_vhead v in progress cbn [h]
            | let h := kqm_head m in progress unfold h
            | let h := kqm_head m in progress cbn [h]
            | idtac ]
  end;
  kqm_unf; kqm_unf2.

(** a function that does not recurse: its text is opened without working its [let]s out, and the memories of its [let]s
    are named (KQMNames.v) before the rest is written out *)
Ltac kqm_enter0 :=
  eapply runk_intro; [reflexivity | reflexivity | simpl kbody ];
  match goal with
  | |- evalk _ _ _ _ _ ?v ?m =>
      first [ let h := kqm_vhead v in progress cbv beta iota delta [h]
            | let h := kqm_head m in progress cbv beta iota delta [h]
            | idtac ]
  end;
  kqm_unf_nz; kqm_name_lets; kqm_unf; kqm_unf2.

(** [kqm_prove]: induction on the recursion argument (the first variable of the goal), then the walk;
    [kqm_prove0]: no recursion. *)
Ltac kqm_prove :=
  let d := fresh "d" in
  intros d; induction d; intros; kqm_enter; kqm_walk.

(** the plain walk first; if it takes long (a run of steps each of which reads the memory it writes makes the text double
    per step), the walk with the memories of the text named *)
Ltac kqm_prove0 :=
  first [ timeout 150 (solve [ intros; kqm_enter; kqm_walk ])
        | solve [ intros; kqm_enter0; kqm_walk ] ].

(** the same walk for a function that writes the memory and gives a number: the end memory is hidden *)
Ltac kqx_test :=
  kqm_red;
  first
    [ rewrite ofn_0, eqb00; kqm_red
    | rewrite ofn_S_ne0 by kqm_bound; kqm_red
    | (* a test of a boolean held as 1 or 0: the test of the boolean (the shape is looked at first, so this costs nothing
         when it does not apply) *)
      lazymatch goal with
      | |- evalx _ _ _ _ (if PrimInt63.eqb (if _ then 1%uint63 else 0%uint63) 0%uint63 then _ else _) _ => rewrite b2i_eqb0
      end;
      match goal with
      | |- evalx _ _ _ _ (if ?b then _ else _) _ => destruct b eqn:?; kqm_red; try kqm_known
      end
    | match goal with
      | |- evalx _ _ _ _ (if ?b then _ else _) _ => destruct b eqn:?; kqm_red; try kqm_known
      end
    | idtac ].

Ltac kqx_call :=
  try rewrite !bud_ofn; try rewrite !bud_if;
  match goal with
  | |- runx _ ?g _ _ _ =>
      tryif is_evar g then (match goal with H : _ |- _ => eapply H; kqm_bound end)
      else (match goal with H : context [runx _ g _ _ _] |- _ => eapply H; kqm_bound end)
  end.

Ltac kqx_step :=
    match goal with
    | H : false = true |- _ => discriminate H
    | H : true = false |- _ => discriminate H
    | |- evalx _ _ _ _ (Eret _) _ => apply X_ret; kqm_fin
    | |- evalx _ _ _ _ (Eop _ _ _ _ _) _ => eapply X_op; [reflexivity | reflexivity | kqm_norm]
    | |- evalx _ _ _ _ (Ekld _ _ _ _) _ => eapply X_ld; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekst _ _ _ _) _ => eapply X_st; [reflexivity | reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekld32 _ _ _ _) _ => eapply X_ld32; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekst32 _ _ _ _) _ => eapply X_st32; [reflexivity | reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ew64 _ _ _ _ _ _ _ _) _ => kqm_w64x
    | |- evalx _ _ _ _ (Ekld8 _ _ _ _) _ => eapply X_ld8; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ekst8 _ _ _ _) _ => eapply X_st8; [reflexivity | reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Eksize _ _ _) _ => eapply X_size; [reflexivity | ]
    | |- evalx _ _ _ _ (Ehw _ _ _) _ => eapply X_hw; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Ehwf _ _ _ _) _ => eapply X_hwf; [reflexivity | reflexivity | ]
    | |- evalx _ _ _ _ (Eif _ _ _ _ _) _ => eapply X_if; [reflexivity | reflexivity | kqx_test]
    | |- evalx _ _ _ _ (Esel _ _ _ _ _ _ _) _ => eapply X_sel; [reflexivity | reflexivity | reflexivity | reflexivity | kqm_norm]
    | |- evalx _ _ _ _ (Ecall _ _ _ _) _ =>
        first [ eapply X_call_run; [reflexivity | kqm_call | ]
              | eapply X_call_ex; [reflexivity | kqx_call | intros ?M1 ?R] ]
    | |- evalx _ _ _ _ (Eloop _) _ =>
        first [ eapply X_loop_run; [kqx_call | reflexivity | kqm_avals]
              | kqm_splitall; (eapply X_loop_run; [kqx_call | reflexivity | kqm_avals]) ]
    end.
Ltac kqx_walk := repeat (kqm_compact; kqm_share; kqx_step).

Ltac kqx_enter :=
  eapply runx_intro; [reflexivity | reflexivity | simpl kbody ];
  match goal with
  | |- evalx _ _ _ _ _ ?v =>
      first [ let h := kqm_vhead v in progress kqm_uh h
            | let h := kqm_vhead v in progress cbn [h]
            | idtac ]
  end;
  kqm_unf; kqm_unf2.

Ltac kqx_enter0 :=
  eapply runx_intro; [reflexivity | reflexivity | simpl kbody ];
  match goal with
  | |- evalx _ _ _ _ _ ?v =>
      first [ let h := kqm_vhead v in progress cbv beta iota delta [h]
            | idtac ]
  end;
  kqm_unf_nz; kqm_name_lets; kqm_unf; kqm_unf2.

Ltac kqx_prove :=
  let d := fresh "d" in
  intros d; induction d; intros; kqx_enter; kqx_walk.

Ltac kqx_prove0 :=
  first [ timeout 150 (solve [ intros; kqx_enter; kqx_walk ])
        | solve [ intros; kqx_enter0; kqx_walk ] ].
