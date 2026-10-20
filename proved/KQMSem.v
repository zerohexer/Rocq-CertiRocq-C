(** KQM: KQL programs over the kit's memory.

    The kit's memory (KQRun.v) is an abstract type with reads and writes;
    what it promises is the laws of KQSpec.v.  Here a KQL function runs on
    such a memory: [Ekld] reads a cell with [rd], [Ekst] writes one with
    [upd], and the semantics asks nothing else of the memory.  A block
    number and a cell number are run-time numbers.

    In C the memory is two global tables set by the loader (trusted): the
    address and the size of each of 64 blocks.  [kmrel M m] says a Clight
    memory [m] holds the abstract memory [M] in that layout. *)

From Stdlib Require Import ZArith List Uint63 Lia Bool.
From Stdlib Require Sint63.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Cop Clight ClightBigstep.
From KQC Require Import KQL KQLSigned.
Require KQ.KQRun KQ.KQBound KQ.KQSpec KQ.hw.Runtime KQ.hw.User.
Import ListNotations.

Local Open Scope Z_scope.

Notation kmemt := KQ.KQRun.mem.
Notation krd := KQ.KQRun.rd.
Notation kupd := KQ.KQRun.upd.
Notation ksize := KQ.KQRun.kq_size.
Notation krd32 := KQ.KQRun.rd32.
Notation kupd32 := KQ.KQRun.upd32.
Notation klen32 := KQ.KQBound.kq_len32.

(** ** The semantics *)

Definition hw_sem (o : hwop) (vs : list i63) (M : kmemt) : kmemt :=
  match o, vs with
  | HLoad, [a0 ; a1 ; a2 ; a3] => KQ.KQRun.hw_load a0 a1 a2 a3 M
  | HStore, [a0 ; a1 ; a2] => KQ.KQRun.hw_store a0 a1 a2 M
  | HStore64, [a0 ; a1 ; a2] => KQ.KQRun.hw_store64 a0 a1 a2 M
  | HAtomic, [a0 ; a1 ; a2 ; a3 ; a4 ; a5] => KQ.KQRun.hw_atomic a0 a1 a2 a3 a4 a5 M
  | HAtomic64, [a0 ; a1 ; a2 ; a3 ; a4 ; a5] => KQ.KQRun.hw_atomic64 a0 a1 a2 a3 a4 a5 M
  | HCas, [a0 ; a1 ; a2 ; a3 ; a4 ; a5] => KQ.KQRun.hw_cas a0 a1 a2 a3 a4 a5 M
  | HCas64, [a0 ; a1 ; a2 ; a3 ; a4 ; a5 ; a6] => KQ.KQRun.hw_cas64 a0 a1 a2 a3 a4 a5 a6 M
  | HALoad, [a0 ; a1 ; a2 ; a3] => KQ.KQRun.hw_aload a0 a1 a2 a3 M
  | HAStore, [a0 ; a1 ; a2] => KQ.KQRun.hw_astore a0 a1 a2 M
  | HAStore64, [a0 ; a1 ; a2] => KQ.KQRun.hw_astore64 a0 a1 a2 M
  | HFence, [a0] => KQ.KQRun.hw_fence a0 M
  | HCopy, [a0 ; a1 ; a2] => KQ.KQRun.hw_copy a0 a1 a2 M
  | HFill, [a0 ; a1 ; a2] => KQ.KQRun.hw_fill a0 a1 a2 M
  | HCmp, [a0 ; a1 ; a2 ; a3 ; a4] => KQ.KQRun.hw_cmp a0 a1 a2 a3 a4 M
  | HCall, [a0 ; a1 ; a2 ; a3] => KQ.KQRun.hw_call a0 a1 a2 a3 M
  | HRun, [a0 ; a1 ; a2 ; a3 ; a4 ; a5 ; a6 ; a7 ; a8 ; a9] => KQ.KQRun.hw_run a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 M
  | HCodeSync, [a0 ; a1] => KQ.KQRun.hw_code_sync a0 a1 M
  | HIrqTake, [a0 ; a1] => KQ.hw.Runtime.hw_irq_take a0 a1 M
  | HUser, [a0 ; a1 ; a2 ; a3 ; a4] => KQ.hw.User.hw_user a0 a1 a2 a3 a4 M
  | HGrow, [a0 ; a1] => KQ.KQRun.kq_grow a0 a1 M
  | _, _ => M
  end.

Definition hwf_sem (o : hwfop) (vs : list i63) : i63 :=
  match o, vs with
  | FAddr, [v] => KQ.KQRun.hw_addr v
  | FIrqInfo, [v] => KQ.hw.Runtime.hw_irq_info v
  | FIrqEntry, [v] => KQ.hw.Runtime.hw_irq_entry v
  | FCpuCode, [v] => KQ.hw.Runtime.hw_cpu_code v
  | FSym, [v] => KQ.hw.Runtime.hw_sym v
  | FUser, [a0 ; a1 ; a2 ; a3 ; a4] => KQ.hw.User.hw_userf a0 a1 a2 a3 a4
  | _, _ => 0%uint63
  end.

Inductive evalk (P : prog) : fn -> env -> kmemt -> exp -> i63 -> kmemt -> Prop :=
| K_ret : forall f rho M a v,
    aval rho a = Some v ->
    evalk P f rho M (Eret a) v M
| K_op : forall f rho M x o a b va vb k v M',
    aval rho a = Some va -> aval rho b = Some vb ->
    evalk P f (PTree.set x (binop_sem o va vb) rho) M k v M' ->
    evalk P f rho M (Eop x o a b k) v M'
| K_if : forall f rho M c a b t e va vb v M',
    aval rho a = Some va -> aval rho b = Some vb ->
    evalk P f rho M (if cmp_sem c va vb then t else e) v M' ->
    evalk P f rho M (Eif c a b t e) v M'
| K_sel : forall f rho M x c a b t e va vb vt ve k v M',
    aval rho a = Some va -> aval rho b = Some vb -> aval rho t = Some vt -> aval rho e = Some ve ->
    evalk P f (PTree.set x (if cmp_sem c va vb then vt else ve) rho) M k v M' ->
    evalk P f rho M (Esel x c a b t e k) v M'
| K_call : forall f rho M x g args vs fg rho' w M1 k v M',
    find P g = Some fg ->
    avals rho args = Some vs ->
    bind (kparams fg) vs (PTree.empty _) = Some rho' ->
    evalk P fg rho' M (kbody fg) w M1 ->
    evalk P f (PTree.set x w rho) M1 k v M' ->
    evalk P f rho M (Ecall x g args k) v M'
| K_ld : forall f rho M x h i vh vi k v M',
    aval rho h = Some vh -> aval rho i = Some vi ->
    evalk P f (PTree.set x (krd vh vi M) rho) M k v M' ->
    evalk P f rho M (Ekld x h i k) v M'
| K_st : forall f rho M h i a vh vi va k v M',
    aval rho h = Some vh -> aval rho i = Some vi -> aval rho a = Some va ->
    evalk P f rho (kupd vh vi va M) k v M' ->
    evalk P f rho M (Ekst h i a k) v M'
| K_ld32 : forall f rho M x h i vh vi k v M',
    aval rho h = Some vh -> aval rho i = Some vi ->
    evalk P f (PTree.set x (krd32 vh vi M) rho) M k v M' ->
    evalk P f rho M (Ekld32 x h i k) v M'
| K_st32 : forall f rho M h i a vh vi va k v M',
    aval rho h = Some vh -> aval rho i = Some vi -> aval rho a = Some va ->
    evalk P f rho (kupd32 vh vi va M) k v M' ->
    evalk P f rho M (Ekst32 h i a k) v M'
| K_ld8 : forall f rho M x h i vh vi k v M',
    aval rho h = Some vh -> aval rho i = Some vi ->
    evalk P f (PTree.set x (KQ.KQRun.rd8 vh vi M) rho) M k v M' ->
    evalk P f rho M (Ekld8 x h i k) v M'
| K_st8 : forall f rho M h i a vh vi va k v M',
    aval rho h = Some vh -> aval rho i = Some vi -> aval rho a = Some va ->
    evalk P f rho (KQ.KQRun.upd8 vh vi va M) k v M' ->
    evalk P f rho M (Ekst8 h i a k) v M'
| K_w64 : forall f rho M o xl xh al ah bl bh (ra rb : KQ.KQRun.u64) k v M',
    xl <> xh ->
    aval rho al = Some (KQ.KQRun.w_lo ra) -> aval rho ah = Some (KQ.KQRun.w_hi ra) ->
    aval rho bl = Some (KQ.KQRun.w_lo rb) -> aval rho bh = Some (KQ.KQRun.w_hi rb) ->
    evalk P f (PTree.set xh (KQ.KQRun.w_hi (KQ.KQRun.w64_op o ra rb))
                (PTree.set xl (KQ.KQRun.w_lo (KQ.KQRun.w64_op o ra rb)) rho)) M k v M' ->
    evalk P f rho M (Ew64 o xl xh al ah bl bh k) v M'
| K_size : forall f rho M x h vh k v M',
    aval rho h = Some vh ->
    evalk P f (PTree.set x (ksize vh M) rho) M k v M' ->
    evalk P f rho M (Eksize x h k) v M'
| K_hw : forall f rho M o args vs k v M',
    length args = hw_arity o -> avals rho args = Some vs ->
    evalk P f rho (hw_sem o vs M) k v M' ->
    evalk P f rho M (Ehw o args k) v M'
| K_hwf : forall f rho M qo qx qargs qvs k v M',
    length qargs = hwf_arity qo -> avals rho qargs = Some qvs ->
    evalk P f (PTree.set qx (hwf_sem qo qvs) rho) M k v M' ->
    evalk P f rho M (Ehwf qo qx qargs k) v M'
| K_loop : forall f rho M args vs rho' v M',
    avals rho args = Some vs ->
    bind (kparams f) vs (PTree.empty _) = Some rho' ->
    evalk P f rho' M (kbody f) v M' ->
    evalk P f rho M (Eloop args) v M'.

(** Running function [g] of [P] on [vs] from memory [M]. *)
Definition runk (P : prog) (g : ident) (vs : list i63) (M : kmemt) (v : i63) (M' : kmemt) : Prop :=
  exists fg rho, find P g = Some fg /\
    bind (kparams fg) vs (PTree.empty _) = Some rho /\ evalk P fg rho M (kbody fg) v M'.

(** ** What the kit's laws give *)

Definition lawsK := KQ.KQSpec.real_laws.

Lemma of_Z_phi : forall z, 0 <= z < 2 ^ 63 -> to_Z (of_Z z) = z.
Proof. intros z H. rewrite Uint63.of_Z_spec. apply Z.mod_small. rewrite wB63. exact H. Qed.

Lemma sZ_small : forall x : i63, to_Z x < 2 ^ 62 -> Sint63.to_Z x = to_Z x.
Proof. intros x H. rewrite sZ_cases. destruct (Z.ltb_spec (to_Z x) (2 ^ 62)); lia. Qed.

Lemma sZ_big : forall x : i63, 2 ^ 62 <= to_Z x -> Sint63.to_Z x = to_Z x - 2 ^ 63.
Proof. intros x H. rewrite sZ_cases. destruct (Z.ltb_spec (to_Z x) (2 ^ 62)); lia. Qed.

Lemma ge0_iff : forall x : i63, (0 <= Sint63.to_Z x) <-> to_Z x < 2 ^ 62.
Proof.
  intros x. pose proof (phi_range x). destruct (Z_lt_ge_dec (to_Z x) (2 ^ 62)) as [L | L].
  - rewrite (sZ_small x L). lia.
  - rewrite (sZ_big x ltac:(lia)). lia.
Qed.

(** a cell number or a block number is in a range exactly when its unsigned value is *)
Lemma in_range : forall (x : i63) n, 0 <= n <= 2 ^ 62 -> (0 <= Sint63.to_Z x < n <-> to_Z x < n).
Proof.
  intros x n Hn. pose proof (phi_range x). destruct (Z_lt_ge_dec (to_Z x) (2 ^ 62)) as [L | L].
  - rewrite (sZ_small x L). lia.
  - rewrite (sZ_big x ltac:(lia)). lia.
Qed.

Lemma nonneg2_true : forall h i : i63,
  KQ.KQSpec.nonneg2 h i = true <-> (0 <= Sint63.to_Z h /\ 0 <= Sint63.to_Z i).
Proof.
  intros h i. unfold KQ.KQSpec.nonneg2. rewrite Bool.andb_true_iff, !KQ.KQSpec.le_Z.
  change (Sint63.to_Z 0%uint63) with 0. tauto.
Qed.

(** a read outside the memory gives 0 *)
Lemma krd_out : forall (vh vi : i63) (M : kmemt),
  ~ (0 <= Sint63.to_Z vh < 64 /\ 0 <= Sint63.to_Z vi < Sint63.to_Z (ksize vh M)) -> krd vh vi M = 0%uint63.
Proof.
  intros vh vi M N.
  destruct (KQ.KQSpec.nonneg2 vh vi) eqn:NN.
  - apply nonneg2_true in NN as [Nh Ni].
    apply (KQ.KQSpec.rd_out KQ.KQSpec.real lawsK vh vi M).
    + apply nonneg2_true. tauto.
    + apply KQ.KQSpec.le_Z.
      destruct (Z_lt_ge_dec (Sint63.to_Z vh) 64) as [L | L].
      * change (Sint63.to_Z (ksize vh M)) with (Sint63.to_Z (KQ.KQSpec.Size KQ.KQSpec.real vh M)) in N.
        lia.
      * assert (Hs : KQ.KQSpec.Size KQ.KQSpec.real vh M = 0%uint63).
        { apply (KQ.KQSpec.size_hi KQ.KQSpec.real lawsK). apply KQ.KQSpec.le_Z. change (Sint63.to_Z 64%uint63) with 64. lia. }
        rewrite Hs. change (Sint63.to_Z 0%uint63) with 0. lia.
  - apply (KQ.KQSpec.rd_neg KQ.KQSpec.real lawsK vh vi M). exact NN.
Qed.

(** a block number outside 0 .. 63 has size 0 *)
Lemma ksize_out : forall (vh : i63) (M : kmemt), ~ (0 <= Sint63.to_Z vh < 64) -> ksize vh M = 0%uint63.
Proof.
  intros vh M N.
  destruct (Z_lt_ge_dec (Sint63.to_Z vh) 0) as [Lh | Lh].
  - apply (KQ.KQSpec.size_neg KQ.KQSpec.real lawsK). apply KQ.KQSpec.lt_Z.
    change (Sint63.to_Z 0%uint63) with 0. lia.
  - apply (KQ.KQSpec.size_hi KQ.KQSpec.real lawsK). apply KQ.KQSpec.le_Z.
    change (Sint63.to_Z 64%uint63) with 64. lia.
Qed.

(** a write outside the memory changes nothing *)
Lemma kupd_out : forall (vh vi v : i63) (M : kmemt),
  ~ (0 <= Sint63.to_Z vh < 64 /\ 0 <= Sint63.to_Z vi < Sint63.to_Z (ksize vh M)) -> kupd vh vi v M = M.
Proof.
  intros vh vi v M N.
  destruct (KQ.KQSpec.nonneg2 vh vi) eqn:NN.
  - apply nonneg2_true in NN as [Nh Ni].
    apply (KQ.KQSpec.upd_out KQ.KQSpec.real lawsK vh vi v M).
    + apply nonneg2_true. tauto.
    + apply KQ.KQSpec.le_Z.
      destruct (Z_lt_ge_dec (Sint63.to_Z vh) 64) as [L | L].
      * change (Sint63.to_Z (ksize vh M)) with (Sint63.to_Z (KQ.KQSpec.Size KQ.KQSpec.real vh M)) in N.
        lia.
      * assert (Hs : KQ.KQSpec.Size KQ.KQSpec.real vh M = 0%uint63).
        { apply (KQ.KQSpec.size_hi KQ.KQSpec.real lawsK). apply KQ.KQSpec.le_Z. change (Sint63.to_Z 64%uint63) with 64. lia. }
        rewrite Hs. change (Sint63.to_Z 0%uint63) with 0. lia.
  - apply (KQ.KQSpec.upd_neg KQ.KQSpec.real lawsK vh vi v M). exact NN.
Qed.

Lemma krd_upd_eq : forall (vh vi v : i63) (M : kmemt),
  0 <= Sint63.to_Z vh < 64 -> 0 <= Sint63.to_Z vi < Sint63.to_Z (ksize vh M) ->
  krd vh vi (kupd vh vi v M) = v.
Proof.
  intros vh vi v M [H1 H2] [H3 H4].
  apply (KQ.KQSpec.rd_upd_eq KQ.KQSpec.real lawsK vh vi v M).
  unfold KQ.KQSpec.cell. rewrite !Bool.andb_true_iff. rewrite !KQ.KQSpec.le_Z, KQ.KQSpec.lt_Z.
  change (Sint63.to_Z 0%uint63) with 0. split; [split; lia | ].
  change (Sint63.to_Z (ksize vh M)) with (Sint63.to_Z (KQ.KQSpec.Size KQ.KQSpec.real vh M)) in H4. exact H4.
Qed.

Lemma krd_upd_ne : forall (vh vi v vh' vi' : i63) (M : kmemt),
  ~ (vh = vh' /\ vi = vi') -> krd vh' vi' (kupd vh vi v M) = krd vh' vi' M.
Proof.
  intros vh vi v vh' vi' M N.
  apply (KQ.KQSpec.rd_upd_ne KQ.KQSpec.real lawsK vh vi vh' vi' v M).
  unfold KQ.KQSpec.other. rewrite Bool.negb_true_iff, Bool.andb_false_iff.
  destruct (PrimInt63.eqb vh vh') eqn:E1; [ | now left].
  destruct (PrimInt63.eqb vi vi') eqn:E2; [ | now right].
  exfalso. apply N. split; apply Uint63.eqb_spec; assumption.
Qed.

Lemma ksize_upd : forall (vh vi v h' : i63) (M : kmemt), ksize h' (kupd vh vi v M) = ksize h' M.
Proof. intros. apply (KQ.KQSpec.size_upd KQ.KQSpec.real lawsK). Qed.


(** ** The narrow blocks: cells of 4 bytes, a family of blocks of its own *)

Lemma klen32_range : forall h : i63, 0 <= Sint63.to_Z (klen32 h).
Proof.
  intros h. pose proof (KQ.KQSpec.len32_nonneg KQ.KQSpec.real lawsK h) as H.
  apply KQ.KQSpec.le_Z in H. change (Sint63.to_Z 0%uint63) with 0 in H. exact H.
Qed.

Lemma klen32_hi : forall h : i63, 64 <= Sint63.to_Z h -> klen32 h = 0%uint63.
Proof.
  intros h H. apply (KQ.KQSpec.len32_hi KQ.KQSpec.real lawsK). apply KQ.KQSpec.le_Z.
  change (Sint63.to_Z 64%uint63) with 64. lia.
Qed.

(** a narrow read outside the memory gives 0 *)
Lemma krd32_out : forall (vh vi : i63) (M : kmemt),
  ~ (0 <= Sint63.to_Z vh < 64 /\ 0 <= Sint63.to_Z vi < Sint63.to_Z (klen32 vh)) -> krd32 vh vi M = 0%uint63.
Proof.
  intros vh vi M N.
  destruct (KQ.KQSpec.nonneg2 vh vi) eqn:NN.
  - apply nonneg2_true in NN as [Nh Ni].
    apply (KQ.KQSpec.rd32_out KQ.KQSpec.real lawsK vh vi M).
    + apply nonneg2_true. tauto.
    + apply KQ.KQSpec.le_Z.
      destruct (Z_lt_ge_dec (Sint63.to_Z vh) 64) as [L | L].
      * change (Sint63.to_Z (klen32 vh)) with (Sint63.to_Z (KQ.KQSpec.Len32 KQ.KQSpec.real vh)) in N. lia.
      * change (KQ.KQSpec.Len32 KQ.KQSpec.real vh) with (klen32 vh). rewrite (klen32_hi vh ltac:(lia)). change (Sint63.to_Z 0%uint63) with 0. lia.
  - apply (KQ.KQSpec.rd32_neg KQ.KQSpec.real lawsK vh vi M). exact NN.
Qed.

(** a narrow write outside the memory changes nothing *)
Lemma kupd32_out : forall (vh vi v : i63) (M : kmemt),
  ~ (0 <= Sint63.to_Z vh < 64 /\ 0 <= Sint63.to_Z vi < Sint63.to_Z (klen32 vh)) -> kupd32 vh vi v M = M.
Proof.
  intros vh vi v M N.
  destruct (KQ.KQSpec.nonneg2 vh vi) eqn:NN.
  - apply nonneg2_true in NN as [Nh Ni].
    apply (KQ.KQSpec.upd32_out KQ.KQSpec.real lawsK vh vi v M).
    + apply nonneg2_true. tauto.
    + apply KQ.KQSpec.le_Z.
      destruct (Z_lt_ge_dec (Sint63.to_Z vh) 64) as [L | L].
      * change (Sint63.to_Z (klen32 vh)) with (Sint63.to_Z (KQ.KQSpec.Len32 KQ.KQSpec.real vh)) in N. lia.
      * change (KQ.KQSpec.Len32 KQ.KQSpec.real vh) with (klen32 vh). rewrite (klen32_hi vh ltac:(lia)). change (Sint63.to_Z 0%uint63) with 0. lia.
  - apply (KQ.KQSpec.upd32_neg KQ.KQSpec.real lawsK vh vi v M). exact NN.
Qed.

Lemma krd32_upd32_eq : forall (vh vi v : i63) (M : kmemt),
  0 <= Sint63.to_Z vh < 64 -> 0 <= Sint63.to_Z vi < Sint63.to_Z (klen32 vh) ->
  krd32 vh vi (kupd32 vh vi v M) = KQ.KQSpec.sx32 v.
Proof.
  intros vh vi v M [H1 H2] [H3 H4].
  apply (KQ.KQSpec.rd32_upd32_eq KQ.KQSpec.real lawsK vh vi v M).
  rewrite Bool.andb_true_iff. split.
  - apply nonneg2_true. lia.
  - apply KQ.KQSpec.lt_Z. change (Sint63.to_Z (KQ.KQSpec.Len32 KQ.KQSpec.real vh)) with (Sint63.to_Z (klen32 vh)). exact H4.
Qed.

Lemma krd32_upd32_ne : forall (vh vi v vh' vi' : i63) (M : kmemt),
  ~ (vh = vh' /\ vi = vi') -> krd32 vh' vi' (kupd32 vh vi v M) = krd32 vh' vi' M.
Proof.
  intros vh vi v vh' vi' M N.
  apply (KQ.KQSpec.rd32_upd32_ne KQ.KQSpec.real lawsK vh vi vh' vi' v M).
  unfold KQ.KQSpec.other. rewrite Bool.negb_true_iff, Bool.andb_false_iff.
  destruct (PrimInt63.eqb vh vh') eqn:E1; [ | now left].
  destruct (PrimInt63.eqb vi vi') eqn:E2; [ | now right].
  exfalso. apply N. split; apply Uint63.eqb_spec; assumption.
Qed.

Lemma krd32_upd : forall (vh vi v vh' vi' : i63) (M : kmemt), krd32 vh' vi' (kupd vh vi v M) = krd32 vh' vi' M.
Proof. intros. apply (KQ.KQSpec.rd32_upd KQ.KQSpec.real lawsK). Qed.

Lemma krd_upd32 : forall (vh vi v vh' vi' : i63) (M : kmemt), krd vh' vi' (kupd32 vh vi v M) = krd vh' vi' M.
Proof. intros. apply (KQ.KQSpec.rd_upd32 KQ.KQSpec.real lawsK). Qed.

Lemma ksize_upd32 : forall (vh vi v h' : i63) (M : kmemt), ksize h' (kupd32 vh vi v M) = ksize h' M.
Proof. intros. apply (KQ.KQSpec.size_upd32 KQ.KQSpec.real lawsK). Qed.
