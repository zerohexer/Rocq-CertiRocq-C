(* KQSpecDemo.v -- PROOFS ABOUT KERNEL CODE, against KQSpec.v's laws: the hardware is trusted (the laws), the logic is
   proved, for every number a device could give back.
     1  a byte from a device, used as the index of a table of 256 entries: in bounds, whatever the device sends;
     2  a store to a device changes no cell of the program;
     3  the page-table fill of hw/fault.body and hw/kernel.body: entry k of the table is 2 MB * k + 131 (present,
        writable, 2 MB) for every k < 512, and its high half 0. *)
From Stdlib Require Import ZArith List Lia Sint63 Bool.
Require Import KQ.KQRun KQ.KQBound KQ.KQSpec.
Open Scope sint63_scope.
Open Scope bool_scope.
Notation Z_ := Sint63.to_Z.

(* ---- 1  a device byte as a table index *)
Definition lookup (a : int) (s : mem) : int :=
  let s1 := hw_load 1 a 0 1 s in rd32 4 (rd 0 1 s1) s1.
Theorem lookup_index_in_bounds : forall a s,
  (1 <? kq_len 0) = true -> (256 <=? kq_len32 4) = true ->
  let x := rd 0 1 (hw_load 1 a 0 1 s) in (0 <=? x) && (x <? kq_len32 4) = true.
Proof.
  intros a s L0 L4 x.
  assert (B : in_lim 1 x = true).
  { apply (load_lim real real_laws); [reflexivity | ]. unfold cell. cbn [Size real].
    (* block 0 had more than 1 cell at the start, and a block never shrinks *)
    pose proof (len_size real real_laws 0 s) as LS. cbn [Len Size real] in LS.
    assert (L1 : (1 <? kq_size 0 s) = true) by (apply lt_Z; apply lt_Z in L0; apply le_Z in LS; lia).
    rewrite L1. reflexivity. }
  unfold in_lim, lim in B. cbn in B. apply andb_prop in B as [B0 B1].
  rewrite B0. cbn [andb]. apply lt_Z. apply lt_Z in B1. apply le_Z in L4. change (Z_ 256) with 256%Z in *. lia.
Qed.

(* ---- 2  a store to a device changes no cell *)
Theorem store_keeps_cells : forall w a v h i s, rd h i (hw_store w a v s) = rd h i s.
Proof. intros. exact (store_rd real real_laws w a v h i s). Qed.

(* ---- 3  the page-table fill *)
Local Notation PD0 := 2.
Fixpoint pd_fill (f : nat) (k : int) (s : mem) : mem :=
  match f with
  | O => s
  | S f => if 512 <=? k then s
           else pd_fill f (k + 1) (upd32 PD0 (2 * k + 1) 0 (upd32 PD0 (2 * k) (k * 2097152 + 131) s))
  end.

Lemma Z2 (j : int) : (0 <= Z_ j <= 512)%Z -> Z_ (2 * j) = (2 * Z_ j)%Z /\ Z_ (2 * j + 1) = (2 * Z_ j + 1)%Z.
Proof.
  intro B. assert (E : Z_ (2 * j) = (2 * Z_ j)%Z) by (rewrite mul_Z; change (Z_ 2) with 2%Z; lia).
  split; [exact E | ]. rewrite add_Z; rewrite E; change (Z_ 1) with 1%Z; lia.
Qed.
Lemma other_PD0 (x y : int) : Z_ x <> Z_ y -> other PD0 x PD0 y = true.
Proof. intro D. unfold other. rewrite Uint63.eqb_refl. cbn [andb]. apply eq_Z_false in D. rewrite D. reflexivity. Qed.
Lemma ok_PD0 (x : int) : (0 <= Z_ x < 1024)%Z -> (1024 <=? kq_len32 PD0) = true ->
  nonneg2 PD0 x && (x <? kq_len32 PD0) = true.
Proof.
  intros B L. unfold nonneg2. apply le_Z in L. change (Z_ 1024) with 1024%Z in L.
  replace (0 <=? PD0) with true by reflexivity. replace (0 <=? x) with true by (symmetry; apply le_Z; change (Z_ 0) with 0%Z; lia).
  cbn [andb]. apply lt_Z. lia.
Qed.
Lemma entry_small (k : int) : (0 <= Z_ k < 512)%Z -> sx32 (k * 2097152 + 131) = k * 2097152 + 131.
Proof.
  intro B. apply sx32_small. rewrite add_Z; rewrite mul_Z; change (Z_ 2097152) with 2097152%Z; change (Z_ 131) with 131%Z; lia.
Qed.

Lemma pd_fill_inv : forall f k s, (1024 <=? kq_len32 PD0) = true ->
  (0 <= Z_ k <= 512)%Z -> (512 <= Z_ k + Z.of_nat f)%Z ->
  (forall j, (Z_ k <= Z_ j < 512)%Z ->
      rd32 PD0 (2 * j) (pd_fill f k s) = j * 2097152 + 131 /\ rd32 PD0 (2 * j + 1) (pd_fill f k s) = 0)
  /\ (forall j, (0 <= Z_ j < Z_ k)%Z ->
      rd32 PD0 (2 * j) (pd_fill f k s) = rd32 PD0 (2 * j) s /\ rd32 PD0 (2 * j + 1) (pd_fill f k s) = rd32 PD0 (2 * j + 1) s).
Proof.
  induction f as [ | f IH]; intros k s L Bk Bf.
  - cbn [pd_fill]. split; [intros j Bj; lia | intros j Bj; split; reflexivity].
  - cbn [pd_fill]. destruct (512 <=? k) eqn:E.
    + apply le_Z in E. change (Z_ 512) with 512%Z in E. split; [intros j Bj; lia | intros j Bj; split; reflexivity].
    + apply le_Z_false in E. change (Z_ 512) with 512%Z in E.
      set (s1 := upd32 PD0 (2 * k + 1) 0 (upd32 PD0 (2 * k) (k * 2097152 + 131) s)).
      assert (Ek1 : Z_ (k + 1) = (Z_ k + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
      destruct (IH (k + 1) s1 L ltac:(lia) ltac:(lia)) as [Up Down].
      destruct (Z2 k ltac:(lia)) as [K2 K21].
      (* s1, cell by cell *)
      assert (S1 : forall j, (0 <= Z_ j <= 512)%Z -> Z_ j <> Z_ k ->
                     rd32 PD0 (2 * j) s1 = rd32 PD0 (2 * j) s /\ rd32 PD0 (2 * j + 1) s1 = rd32 PD0 (2 * j + 1) s).
      { intros j Bj D. destruct (Z2 j Bj) as [J2 J21]. unfold s1. split.
        - rewrite (rd32_upd32_ne real real_laws) by (apply other_PD0; lia).
          rewrite (rd32_upd32_ne real real_laws) by (apply other_PD0; lia). reflexivity.
        - rewrite (rd32_upd32_ne real real_laws) by (apply other_PD0; lia).
          rewrite (rd32_upd32_ne real real_laws) by (apply other_PD0; lia). reflexivity. }
      split.
      * intros j Bj. destruct (Z.eq_dec (Z_ j) (Z_ k)) as [Ejk | Ejk].
        -- apply Sint63.to_Z_inj in Ejk. subst j. destruct (Down k ltac:(lia)) as [D1 D2]. rewrite D1, D2. unfold s1. split.
           ++ rewrite (rd32_upd32_ne real real_laws) by (apply other_PD0; lia).
              rewrite (rd32_upd32_eq real real_laws) by (apply ok_PD0; [lia | exact L]). apply entry_small. lia.
           ++ rewrite (rd32_upd32_eq real real_laws) by (apply ok_PD0; [lia | exact L]). apply (sx32_small 0). change (Z_ 0) with 0%Z; lia.
        -- apply Up. lia.
      * intros j Bj. destruct (Down j ltac:(lia)) as [D1 D2]. rewrite D1, D2. apply S1; lia.
Qed.

Lemma kq_nat_512 : kq_nat 512 = 512%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem pd_fill_entries : forall s, (1024 <=? kq_len32 PD0) = true ->
  forall j, (0 <=? j) && (j <? 512) = true ->
  rd32 PD0 (2 * j) (pd_fill (kq_nat 512) 0 s) = j * 2097152 + 131
  /\ rd32 PD0 (2 * j + 1) (pd_fill (kq_nat 512) 0 s) = 0.
Proof.
  intros s L j Bj. apply andb_prop in Bj as [B0 B1]. apply le_Z in B0. apply lt_Z in B1.
  change (Z_ 0) with 0%Z in B0. change (Z_ 512) with 512%Z in B1.
  rewrite kq_nat_512. destruct (pd_fill_inv 512 0 s L ltac:(change (Z_ 0) with 0%Z; lia) ltac:(change (Z_ 0) with 0%Z; cbn; lia)) as [Up _].
  apply Up. change (Z_ 0) with 0%Z. lia.
Qed.
