(** KQM: KQL programs over the kit's memory -- the Clight side (masked numbers).  The semantics is KQMSem.v. *)

From Stdlib Require Import ZArith List Uint63 Lia Bool.
From Stdlib Require Sint63.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Cop Clight ClightBigstep.
From KQC Require Import KQL KQLGen KQTArith KQLSigned KQLProof.
From KQC Require Export KQMSem.
Require KQ.KQRun KQ.KQSpec.
Import ListNotations.

Local Open Scope Z_scope.

(** ** The memory in C: two tables *)

Section KMEM.
Variable cp : Clight.program.
Let ge := Clight.globalenv cp.

(** Block [k] has [n] cells at the address [bk k]; the tables hold the address and the size of each block.
    The cells' blocks are apart from each other and from the tables. *)
Definition ktab (M : kmemt) (m : Memory.Mem.mem) (bt bl : block) (bk : Z -> block) : Prop :=
    Genv.find_symbol ge kq_tab = Some bt /\ Genv.find_symbol ge kq_lens = Some bl /\ bt <> bl /\
    (forall k, 0 <= k < 64 ->
       let n := Sint63.to_Z (ksize (of_Z k) M) in
       0 <= n < 2 ^ 31 /\
       Mem.load Mint32 m bl (4 * k) = Some (Vint (Int.repr (2 * n))) /\
       (forall j, 0 <= j < n ->
          Mem.load Mint64 m (bk k) (8 * j) = Some (enc (krd (of_Z k) (of_Z j) M)) /\
          Mem.valid_access m Mint64 (bk k) (8 * j) Writable) /\
       (0 < n -> Mem.load Mint64 m bt (8 * k) = Some (Vptr (bk k) Ptrofs.zero) /\ bk k <> bt /\ bk k <> bl)) /\
    (forall k k', 0 <= k < 64 -> 0 <= k' < 64 -> k <> k' ->
       0 < Sint63.to_Z (ksize (of_Z k) M) -> 0 < Sint63.to_Z (ksize (of_Z k') M) -> bk k <> bk k').

(** The narrow blocks (cells of 4 bytes, KQRun.v rd32 / upd32): the same layout with tables of their own.  A cell holds the
    number as a signed 32-bit number; the sizes do not change. *)
Definition ktab2 (M : kmemt) (m : Memory.Mem.mem) (bt bl : block) (bk : Z -> block) : Prop :=
    Genv.find_symbol ge kq_tab32 = Some bt /\ Genv.find_symbol ge kq_lens32 = Some bl /\ bt <> bl /\
    (forall k, 0 <= k < 64 ->
       let n := Sint63.to_Z (klen32 (of_Z k)) in
       0 <= n < 2 ^ 31 /\
       Mem.load Mint32 m bl (4 * k) = Some (Vint (Int.repr (2 * n))) /\
       (forall j, 0 <= j < n ->
          (exists i, Mem.load Mint32 m (bk k) (4 * j) = Some (Vint i) /\
                     Int.signed i = Sint63.to_Z (krd32 (of_Z k) (of_Z j) M)) /\
          Mem.valid_access m Mint32 (bk k) (4 * j) Writable) /\
       (0 < n -> Mem.load Mint64 m bt (8 * k) = Some (Vptr (bk k) Ptrofs.zero) /\ bk k <> bt /\ bk k <> bl)) /\
    (forall k k', 0 <= k < 64 -> 0 <= k' < 64 -> k <> k' ->
       0 < Sint63.to_Z (klen32 (of_Z k)) -> 0 < Sint63.to_Z (klen32 (of_Z k')) -> bk k <> bk k').

(** the two families and their tables are apart *)
Definition ksep (M : kmemt) (bt bl : block) (bk : Z -> block) (bt2 bl2 : block) (bk2 : Z -> block) : Prop :=
  bt <> bt2 /\ bt <> bl2 /\ bl <> bt2 /\ bl <> bl2 /\
  (forall k, 0 <= k < 64 -> 0 < Sint63.to_Z (ksize (of_Z k) M) -> bk k <> bt2 /\ bk k <> bl2) /\
  (forall k, 0 <= k < 64 -> 0 < Sint63.to_Z (klen32 (of_Z k)) -> bk2 k <> bt /\ bk2 k <> bl) /\
  (forall k k', 0 <= k < 64 -> 0 <= k' < 64 ->
     0 < Sint63.to_Z (ksize (of_Z k) M) -> 0 < Sint63.to_Z (klen32 (of_Z k')) -> bk k <> bk2 k').

Definition kmrel (M : kmemt) (m : Memory.Mem.mem) : Prop :=
  exists bt bl bk bt2 bl2 bk2, ktab M m bt bl bk /\ ktab2 M m bt2 bl2 bk2 /\ ksep M bt bl bk bt2 bl2 bk2.

Lemma ksep_size : forall M M' bt bl bk bt2 bl2 bk2,
  ksep M bt bl bk bt2 bl2 bk2 -> (forall h, ksize h M' = ksize h M) -> ksep M' bt bl bk bt2 bl2 bk2.
Proof.
  intros M M' bt bl bk bt2 bl2 bk2 (A & B & C & D & E & F & G) H. unfold ksep. setoid_rewrite H.
  refine (conj A (conj B (conj C (conj D (conj E (conj F G)))))).
Qed.

(** a write into a block foreign to the tables of the first family leaves them as they are *)
Lemma ktab_frame : forall M M' m m' bt bl bk chunk b ofs v,
  ktab M m bt bl bk ->
  (forall h j, krd h j M' = krd h j M) -> (forall h, ksize h M' = ksize h M) ->
  Mem.store chunk m b ofs v = Some m' ->
  b <> bt -> b <> bl -> (forall k, 0 <= k < 64 -> 0 < Sint63.to_Z (ksize (of_Z k) M) -> b <> bk k) ->
  ktab M' m' bt bl bk.
Proof.
  intros M M' m m' bt bl bk chunk b ofs v (Ft & Fl & Hne & T & Dis) Hr Hs ST Nt Nl Nk.
  refine (conj Ft (conj Fl (conj Hne (conj _ _)))).
  - intros k Rk. pose proof (T k Rk) as Tk. cbv zeta in Tk. destruct Tk as (Bn & Hl & Hc & Hbk). cbv zeta. rewrite Hs.
    refine (conj Bn (conj _ (conj _ _))).
    + rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [exact Hl | left; exact (not_eq_sym Nl)].
    + intros j Rj. destruct (Hc j Rj) as (Ld & VA). split.
      * assert (Hpos : 0 < Sint63.to_Z (ksize (of_Z k) M)) by lia.
        rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [ | left; exact (not_eq_sym (Nk k Rk Hpos))].
        rewrite Hr. exact Ld.
      * exact (Mem.store_valid_access_1 _ _ _ _ _ _ ST _ _ _ _ VA).
    + intros Hp. destruct (Hbk Hp) as (Ht' & N1 & N2). refine (conj _ (conj N1 N2)).
      rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [exact Ht' | left; exact (not_eq_sym Nt)].
  - intros k1 k2 R1 R2 Ne P1 P2. rewrite Hs in P1, P2. exact (Dis k1 k2 R1 R2 Ne P1 P2).
Qed.

Lemma ktab2_frame : forall M M' m m' bt bl bk chunk b ofs v,
  ktab2 M m bt bl bk ->
  (forall h j, krd32 h j M' = krd32 h j M) ->
  Mem.store chunk m b ofs v = Some m' ->
  b <> bt -> b <> bl -> (forall k, 0 <= k < 64 -> 0 < Sint63.to_Z (klen32 (of_Z k)) -> b <> bk k) ->
  ktab2 M' m' bt bl bk.
Proof.
  intros M M' m m' bt bl bk chunk b ofs v (Ft & Fl & Hne & T & Dis) Hr ST Nt Nl Nk.
  refine (conj Ft (conj Fl (conj Hne (conj _ _)))).
  - intros k Rk. pose proof (T k Rk) as Tk. cbv zeta in Tk. destruct Tk as (Bn & Hl & Hc & Hbk). cbv zeta.
    refine (conj Bn (conj _ (conj _ _))).
    + rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [exact Hl | left; exact (not_eq_sym Nl)].
    + intros j Rj. destruct (Hc j Rj) as ((i & Ld & Hi) & VA). split.
      * assert (Hpos : 0 < Sint63.to_Z (klen32 (of_Z k))) by lia.
        exists i. rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [ | left; exact (not_eq_sym (Nk k Rk Hpos))].
        rewrite Hr. split; [exact Ld | exact Hi].
      * exact (Mem.store_valid_access_1 _ _ _ _ _ _ ST _ _ _ _ VA).
    + intros Hp. destruct (Hbk Hp) as (Ht' & N1 & N2). refine (conj _ (conj N1 N2)).
      rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [exact Ht' | left; exact (not_eq_sym Nt)].
  - exact Dis.
Qed.

Lemma sx32_signed : forall v : i63,
  Sint63.to_Z (KQ.KQSpec.sx32 v) = Int.signed (Int.repr (to_Z v)).
Proof.
  intros v. pose proof (phi_range v). unfold KQ.KQSpec.sx32.
  set (u := PrimInt63.land v 4294967295%uint63).
  assert (Hu : to_Z u = to_Z v mod 2 ^ 32).
  { unfold u. rewrite Uint63.land_spec'. change (to_Z 4294967295%uint63) with (Z.ones 32).
    rewrite Z.land_ones by lia. reflexivity. }
  assert (Hr : Int.unsigned (Int.repr (to_Z v)) = to_Z v mod 2 ^ 32) by (rewrite Int.unsigned_repr_eq; reflexivity).
  pose proof (Z.mod_pos_bound (to_Z v) (2 ^ 32) ltac:(lia)) as B.
  assert (Hsu : Sint63.to_Z u = to_Z u) by (rewrite sZ_cases; destruct (Z.ltb_spec (to_Z u) (2 ^ 62)); lia).
  unfold Int.signed. rewrite Hr. change Int.half_modulus with (2 ^ 31). change Int.modulus with (2 ^ 32).
  destruct (PrimInt63.ltsb u 2147483648%uint63) eqn:L.
  - apply sltb_iff in L. change (Sint63.to_Z 2147483648%uint63) with (2 ^ 31) in L.
    destruct (zlt (to_Z v mod 2 ^ 32) (2 ^ 31)); [ | lia]. rewrite Hsu, Hu. reflexivity.
  - assert (Hn : ~ Sint63.to_Z u < 2 ^ 31).
    { intro C. assert (PrimInt63.ltsb u 2147483648%uint63 = true) by (apply sltb_iff; exact C). congruence. }
    destruct (zlt (to_Z v mod 2 ^ 32) (2 ^ 31)); [lia | ].
    rewrite sZ_cases, Uint63.sub_spec. change (to_Z 4294967296%uint63) with (2 ^ 32). change wB with (2 ^ 63).
    assert (E : (to_Z u - 2 ^ 32) mod 2 ^ 63 = to_Z u - 2 ^ 32 + 2 ^ 63)
      by (symmetry; apply Z.mod_unique_pos with (q := -1); lia).
    rewrite E. destruct (Z.ltb_spec (to_Z u - 2 ^ 32 + 2 ^ 63) (2 ^ 62)); lia.
Qed.

Lemma mul_off : forall sz j, sz = 1 \/ sz = 4 \/ sz = 8 -> 0 <= j < 2 ^ 40 ->
  Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_int64 (Int64.repr j)) = Ptrofs.repr (sz * j).
Proof.
  intros sz j Hs H. unfold Ptrofs.mul, Ptrofs.of_int64.
  rewrite (Int64.unsigned_repr j) by (unfold Int64.max_unsigned; rewrite mod64; lia).
  rewrite !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; rewrite ptrofs_mod; destruct Hs; subst; lia).
  reflexivity.
Qed.

Lemma uns_off40 : forall sz j, sz = 1 \/ sz = 4 \/ sz = 8 -> 0 <= j < 2 ^ 40 -> Ptrofs.unsigned (Ptrofs.repr (sz * j)) = sz * j.
Proof.
  intros sz j Hs H. apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned. rewrite ptrofs_mod. destruct Hs; subst; lia.
Qed.

Lemma eval_ltu : forall le m A B x y,
  eval_expr ge empty_env le m A (Vlong x) -> eval_expr ge empty_env le m B (Vlong y) ->
  typeof A = tyl -> typeof B = tyl ->
  eval_expr ge empty_env le m (cmpe Olt A B) (Val.of_bool (Int64.ltu x y)).
Proof.
  intros. eapply eval_bin; [exact H | exact H0 | exact H1 | exact H2 | ].
  simpl. unfold sem_cmp, sem_binarith. simpl. rewrite !cast_ll. reflexivity.
Qed.

Lemma eval_glob : forall le m id b ty,
  Genv.find_symbol ge id = Some b -> access_mode ty = By_reference ->
  eval_expr ge empty_env le m (Evar id ty) (Vptr b Ptrofs.zero).
Proof.
  intros. eapply eval_Elvalue. apply eval_Evar_global; [apply PTree.gempty | exact H].
  apply deref_loc_reference. exact H0.
Qed.

Lemma eval_add_ptr : forall le m A I b ofs j elem rty sz,
  eval_expr ge empty_env le m A (Vptr b ofs) -> eval_expr ge empty_env le m I (Vlong (Int64.repr j)) ->
  typeof I = tyl -> classify_add (typeof A) tyl = add_case_pl elem -> sizeof (Clight.genv_cenv ge) elem = sz ->
  (sz = 1 \/ sz = 4 \/ sz = 8) -> 0 <= j < 2 ^ 40 ->
  eval_expr ge empty_env le m (Ebinop Oadd A I rty) (Vptr b (Ptrofs.add ofs (Ptrofs.repr (sz * j)))).
Proof.
  intros le m A I b ofs j elem rty sz EA EI TI CL SZ Hs R.
  econstructor; eauto. rewrite TI. cbn [sem_binary_operation]. unfold sem_add. rewrite CL. unfold sem_add_ptr_long.
  rewrite SZ, mul_off by assumption. reflexivity.
Qed.

Lemma eval_deref_val : forall le m A ty chunk b ofs v,
  eval_expr ge empty_env le m A (Vptr b ofs) -> access_mode ty = By_value chunk ->
  Mem.load chunk m b (Ptrofs.unsigned ofs) = Some v ->
  eval_expr ge empty_env le m (Ederef A ty) v.
Proof.
  intros. eapply eval_Elvalue. apply eval_Ederef. exact H.
  eapply deref_loc_value; [exact H0 | exact H1].
Qed.

(** the size of block [k] *)
Lemma eval_kld_len : forall le m H (k n : Z) bl,
  eval_expr ge empty_env le m H (Vlong (Int64.repr k)) -> typeof H = tyl ->
  0 <= k < 64 -> 0 <= n < 2 ^ 32 -> Genv.find_symbol ge kq_lens = Some bl ->
  Mem.load Mint32 m bl (4 * k) = Some (Vint (Int.repr n)) ->
  eval_expr ge empty_env le m (kld_len H) (Vlong (Int64.repr n)).
Proof.
  intros le m H k n bl EH TH Rk Rn Fl Ld. unfold kld_len.
  econstructor.
  - eapply eval_deref_val.
    + eapply eval_add_ptr; [ eapply eval_glob; [exact Fl | reflexivity] | exact EH | exact TH | reflexivity | reflexivity | auto | lia ].
    + reflexivity.
    + rewrite Ptrofs.add_zero_l, uns_off40 by (auto || lia). exact Ld.
  - simpl. unfold sem_cast. simpl. f_equal. f_equal.
    rewrite Int.unsigned_repr by (unfold Int.max_unsigned; change Int.modulus with 4294967296; lia).
    reflexivity.
Qed.

Lemma cell_off_val : forall vi : i63, to_Z vi < 2 ^ 36 ->
  Int64.sub (Int64.mul (tg vi) (Int64.repr 4)) (Int64.repr 4) = Int64.repr (8 * to_Z vi).
Proof.
  intros vi H. pose proof (phi_range vi). apply uinj.
  rewrite usub, umul, uns_tg, (uns_small 4) by lia.
  rewrite (uns_small (8 * to_Z vi)) by lia.
  rewrite (Z.mod_small ((2 * to_Z vi + 1) * 4)) by lia.
  replace ((2 * to_Z vi + 1) * 4 - 4) with (8 * to_Z vi) by ring.
  apply Z.mod_small. lia.
Qed.

Lemma mul_off1 : forall j, 0 <= j < 2 ^ 40 ->
  Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr j)) = Ptrofs.repr j.
Proof.
  intros j H. unfold Ptrofs.mul, Ptrofs.of_int64.
  rewrite (Int64.unsigned_repr j) by (unfold Int64.max_unsigned; rewrite mod64; lia).
  rewrite !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; rewrite ptrofs_mod; lia).
  rewrite Z.mul_1_l. reflexivity.
Qed.

(** the address of the cell of block [k] at the tagged number [I] of [vi] *)
Lemma eval_kld_addr : forall le m H I (k : Z) (vi : i63) bt bk,
  eval_expr ge empty_env le m H (Vlong (Int64.repr k)) -> typeof H = tyl ->
  eval_expr ge empty_env le m I (enc vi) -> typeof I = tyl ->
  0 <= k < 64 -> to_Z vi < 2 ^ 36 -> Genv.find_symbol ge kq_tab = Some bt ->
  Mem.load Mint64 m bt (8 * k) = Some (Vptr bk Ptrofs.zero) ->
  eval_expr ge empty_env le m (kld_addr H I) (Vptr bk (Ptrofs.repr (8 * to_Z vi))).
Proof.
  intros le m H I k vi bt bk EH TH EI TI Rk Rj Ft Lt. pose proof (phi_range vi).
  unfold kld_addr, kld_base.
  assert (EB : eval_expr ge empty_env le m
                 (Ederef (Ebinop Oadd (Evar kq_tab (Tarray tptr kq_nblocks noattr)) H (Tpointer tptr noattr)) tptr)
                 (Vptr bk Ptrofs.zero)).
  { eapply eval_deref_val.
    - eapply eval_add_ptr; [ eapply eval_glob; [exact Ft | reflexivity] | exact EH | exact TH | reflexivity | reflexivity | auto | lia ].
    - reflexivity.
    - rewrite Ptrofs.add_zero_l, uns_off40 by (auto || lia). exact Lt. }
  assert (EO : eval_expr ge empty_env le m (cell_off I) (Vlong (Int64.repr (8 * to_Z vi)))).
  { rewrite <- (cell_off_val vi Rj). unfold cell_off.
    eapply eval_bin; [ | apply eval_Econst_long | reflexivity | reflexivity | reflexivity ].
    eapply eval_bin; [ exact EI | apply eval_Econst_long | exact TI | reflexivity | reflexivity ]. }
  assert (EA : eval_expr ge empty_env le m (Ebinop Oadd (Ecast (kld_base H) tcp) (cell_off I) tcp)
                 (Vptr bk (Ptrofs.add Ptrofs.zero (Ptrofs.repr (1 * (8 * to_Z vi)))))).
  { eapply eval_add_ptr with (elem := tchar); [ | exact EO | reflexivity | reflexivity | reflexivity | auto | lia ].
    eapply eval_Ecast; [exact EB | reflexivity]. }
  replace (Ptrofs.add Ptrofs.zero (Ptrofs.repr (1 * (8 * to_Z vi)))) with (Ptrofs.repr (8 * to_Z vi)) in EA
    by (rewrite Ptrofs.add_zero_l, Z.mul_1_l; reflexivity).
  eapply eval_Ecast; [exact EA | reflexivity].
Qed.

(** a cell of block [k] *)
Lemma eval_kld_cell : forall le m H I (k : Z) (vi : i63) bt bk v,
  eval_expr ge empty_env le m H (Vlong (Int64.repr k)) -> typeof H = tyl ->
  eval_expr ge empty_env le m I (enc vi) -> typeof I = tyl ->
  0 <= k < 64 -> to_Z vi < 2 ^ 36 -> Genv.find_symbol ge kq_tab = Some bt ->
  Mem.load Mint64 m bt (8 * k) = Some (Vptr bk Ptrofs.zero) ->
  Mem.load Mint64 m bk (8 * to_Z vi) = Some v ->
  eval_expr ge empty_env le m (kld_cell H I) v.
Proof.
  intros le m H I k vi bt bk v EH TH EI TI Rk Rj Ft Lt Lc. pose proof (phi_range vi). unfold kld_cell.
  eapply eval_deref_val.
  - eapply eval_kld_addr; eassumption.
  - reflexivity.
  - rewrite uns_off40 by (auto || lia). exact Lc.
Qed.

(** the table facts of block [k] *)
Lemma kmrel_get : forall M m, kmrel M m -> exists bt bl bk,
  Genv.find_symbol ge kq_tab = Some bt /\ Genv.find_symbol ge kq_lens = Some bl /\
  forall k, 0 <= k < 64 -> exists n,
    n = Sint63.to_Z (ksize (of_Z k) M) /\ 0 <= n < 2 ^ 31 /\
    Mem.load Mint32 m bl (4 * k) = Some (Vint (Int.repr (2 * n))) /\
    (forall j, 0 <= j < n -> Mem.load Mint64 m (bk k) (8 * j) = Some (enc (krd (of_Z k) (of_Z j) M)) /\
                             Mem.valid_access m Mint64 (bk k) (8 * j) Writable) /\
    (0 < n -> Mem.load Mint64 m bt (8 * k) = Some (Vptr (bk k) Ptrofs.zero)).
Proof.
  intros M m (bt & bl & bk & bt2 & bl2 & bk2 & (Ft & Fl & Hne & T & Dis) & _). exists bt, bl, bk. split; [exact Ft | split; [exact Fl | ]].
  intros k Rk. specialize (T k Rk). cbv zeta in T. destruct T as (Hn & Hl & Hc & Hbk).
  exists (Sint63.to_Z (ksize (of_Z k) M)).
  refine (conj eq_refl (conj Hn (conj Hl (conj Hc _)))).
  intros Hp. exact (proj1 (Hbk Hp)).
Qed.

Lemma eval_kidx : forall le m rho i vi, agree rho le -> aval rho i = Some vi ->
  eval_expr ge empty_env le m (sh1 (tr_atom i)) (Vlong (Int64.repr (to_Z vi))).
Proof.
  intros le m rho i vi AG Hi. rewrite <- (shr1_t vi).
  eapply eval_sh1; [eapply eval_atom; eauto | apply typeof_atom].
Qed.

Lemma exec_kld : forall le m rho M x h i vh vi,
  agree rho le -> kmrel M m -> aval rho h = Some vh -> aval rho i = Some vi ->
  exec_stmt function_entry2 ge empty_env le m
    (kit_guard (tr_atom h) (tr_atom i) (Sset (tv x) (kld_cell (sh1 (tr_atom h)) (tr_atom i))) (Sset (tv x) c1))
    E0 (PTree.set (tv x) (enc (krd vh vi M)) le) m Out_normal.
Proof.
  intros le m rho M x h i vh vi AG KM Hh Hi.
  assert (EH := eval_atom cp empty_env le m rho AG h vh Hh).
  assert (EI := eval_atom cp empty_env le m rho AG i vi Hi).
  assert (EHs := eval_kidx le m rho h vh AG Hh).
  assert (EIs := eval_kidx le m rho i vi AG Hi).
  pose proof (phi_range vh) as Rh. pose proof (phi_range vi) as Ri.
  assert (E128 : eval_expr ge empty_env le m (c64 128) (Vlong (Int64.repr 128))) by apply eval_Econst_long.
  unfold kit_guard.
  eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EH | exact E128 | apply typeof_atom | reflexivity] | apply bool_of | ].
  simpl. rewrite lt128_t.
  destruct (Z_lt_ge_dec (to_Z vh) kq_nblocks) as [Lh | Lh].
  - assert (Eh : (to_Z vh <? 64) = true) by (apply Z.ltb_lt; exact Lh). rewrite Eh.
    destruct (kmrel_get M m KM) as (bt & bl & bk & Ft & Fl & T).
    destruct (T (to_Z vh) ltac:(unfold kq_nblocks in Lh; lia)) as (n & Hn & Bn & Hl & Hc & Ht).
    rewrite Uint63.of_to_Z in Hn. rewrite Uint63.of_to_Z in Hc.
    set (len := kld_len (sh1 (tr_atom h))).
    assert (EL : eval_expr ge empty_env le m len (Vlong (Int64.repr (2 * n)))).
    { eapply eval_kld_len; [exact EHs | reflexivity | unfold kq_nblocks in Lh; lia | lia | exact Fl | exact Hl]. }
    eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EI | exact EL | apply typeof_atom | reflexivity] | apply bool_of | ].
    rewrite (lt_n_t vi n) by lia.
    destruct (Z_lt_ge_dec (to_Z vi) n) as [Li | Li].
    + assert (Ei : (to_Z vi <? n) = true) by (apply Z.ltb_lt; exact Li). rewrite Ei.
      apply exec_Sset.
      destruct (Hc (to_Z vi) ltac:(lia)) as (Ld & _).
      rewrite Uint63.of_to_Z in Ld.
      eapply eval_kld_cell; [exact EHs | reflexivity | exact EI | apply typeof_atom | unfold kq_nblocks in Lh; lia | lia | exact Ft | exact (Ht ltac:(lia)) | exact Ld].
    + assert (Ei : (to_Z vi <? n) = false) by (apply Z.ltb_ge; lia). rewrite Ei.
      apply exec_Sset.
      rewrite (krd_out vh vi M).
      * unfold enc. rewrite tg_zero. apply eval_c1.
      * intros [A1 A2]. rewrite <- Hn in A2.
        apply (in_range vi n ltac:(lia)) in A2. lia.
  - assert (Eh : (to_Z vh <? 64) = false) by (apply Z.ltb_ge; unfold kq_nblocks in Lh; lia). rewrite Eh.
    apply exec_Sset.
    rewrite (krd_out vh vi M).
    + unfold enc. rewrite tg_zero. apply eval_c1.
    + intros [A1 A2]. apply (in_range vh kq_nblocks ltac:(unfold kq_nblocks; lia)) in A1. lia.
Qed.

Lemma of_Z_inj : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> of_Z a = of_Z b -> a = b.
Proof. intros a b Ha Hb E. rewrite <- (of_Z_phi a Ha), <- (of_Z_phi b Hb), E. reflexivity. Qed.

Lemma sZ_of_Z : forall k, 0 <= k < 2 ^ 62 -> Sint63.to_Z (of_Z k) = k.
Proof. intros k H. rewrite sZ_small; rewrite of_Z_phi; lia. Qed.

(** a write inside a block keeps the table relation *)
Lemma ktab_store : forall M m bt bl bk k j va m',
  ktab M m bt bl bk -> 0 <= k < 64 ->
  0 <= j < Sint63.to_Z (ksize (of_Z k) M) ->
  Mem.store Mint64 m (bk k) (8 * j) (enc va) = Some m' ->
  ktab (kupd (of_Z k) (of_Z j) va M) m' bt bl bk.
Proof.
  intros M m bt bl bk k j va m' (Ft & Fl & Hne & T & Dis) Rk Rj ST.
  assert (SZ : forall k', ksize (of_Z k') (kupd (of_Z k) (of_Z j) va M) = ksize (of_Z k') M) by (intros; apply ksize_upd).
  pose proof (T k Rk) as Tk. cbv zeta in Tk. destruct Tk as (Bk & Hlk & Hck & Hbk).
  assert (Hpos : 0 < Sint63.to_Z (ksize (of_Z k) M)) by lia.
  destruct (Hbk Hpos) as (Htk & Nt & Nl).
  assert (Rj62 : 0 <= j < 2 ^ 62) by (pose proof Bk; lia).
  refine (conj Ft (conj Fl (conj Hne (conj _ _)))).
  - intros k' Rk'. pose proof (T k' Rk') as Tk'. cbv zeta in Tk'. destruct Tk' as (Bn & Hl & Hc & Hbk').
    cbv zeta. rewrite SZ.
    refine (conj Bn (conj _ (conj _ _))).
    + rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [exact Hl | left; exact (not_eq_sym Nl)].
    + intros j' Rj'. destruct (Hc j' Rj') as (Ld & VA). split.
      * destruct (Z.eq_dec k' k) as [Ek | Ek].
        -- subst k'. destruct (Z.eq_dec j' j) as [Ej | Ej].
           ++ subst j'. rewrite (Mem.load_store_same _ _ _ _ _ _ ST). simpl.
              rewrite (krd_upd_eq (of_Z k) (of_Z j) va M).
              ** reflexivity.
              ** rewrite sZ_of_Z by lia. lia.
              ** rewrite sZ_of_Z by lia. lia.
           ++ rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [ | right; change (size_chunk Mint64) with 8; destruct (Z_lt_ge_dec j' j); [left | right]; lia].
              rewrite (krd_upd_ne (of_Z k) (of_Z j) va (of_Z k) (of_Z j') M); [exact Ld | ].
              intros [_ E]. apply Ej. symmetry in E. apply of_Z_inj in E; lia.
        -- rewrite (Mem.load_store_other _ _ _ _ _ _ ST).
           ++ rewrite (krd_upd_ne (of_Z k) (of_Z j) va (of_Z k') (of_Z j') M); [exact Ld | ].
              intros [E _]. apply Ek. apply of_Z_inj in E; lia.
           ++ left. apply not_eq_sym. apply Dis; [exact Rk | exact Rk' | exact (fun E => Ek (eq_sym E)) | exact Hpos | lia].
      * exact (Mem.store_valid_access_1 _ _ _ _ _ _ ST _ _ _ _ VA).
    + intros Hp. destruct (Hbk' Hp) as (Ht' & N1 & N2).
      refine (conj _ (conj N1 N2)).
      rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [exact Ht' | left; exact (not_eq_sym Nt)].
  - intros k1 k2 R1 R2 Ne P1 P2. rewrite SZ in P1, P2. exact (Dis k1 k2 R1 R2 Ne P1 P2).
Qed.

(** the same, for a block and a cell given as numbers *)
Lemma ktab_store_at : forall M m bt bl bk (vh vi va : i63) m',
  ktab M m bt bl bk -> to_Z vh < 64 -> 0 <= to_Z vi < Sint63.to_Z (ksize vh M) ->
  Mem.store Mint64 m (bk (to_Z vh)) (8 * to_Z vi) (enc va) = Some m' ->
  ktab (kupd vh vi va M) m' bt bl bk.
Proof.
  intros M m bt bl bk vh vi va m' KT Lh Li ST.
  pose proof (phi_range vh) as Rh.
  assert (Hv : ktab (kupd (of_Z (to_Z vh)) (of_Z (to_Z vi)) va M) m' bt bl bk).
  { eapply ktab_store; [exact KT | lia | | exact ST]. rewrite Uint63.of_to_Z. exact Li. }
  rewrite !Uint63.of_to_Z in Hv. exact Hv.
Qed.

(** a store through the tables: a write inside a block, or nothing *)
Lemma exec_kst : forall le m rho M h i a vh vi va,
  agree rho le -> kmrel M m -> aval rho h = Some vh -> aval rho i = Some vi -> aval rho a = Some va ->
  exists m', exec_stmt function_entry2 ge empty_env le m
    (kit_guard (tr_atom h) (tr_atom i) (Sassign (kld_cell (sh1 (tr_atom h)) (tr_atom i)) (tr_atom a)) Sskip)
    E0 le m' Out_normal /\ kmrel (kupd vh vi va M) m'.
Proof.
  intros le m rho M h i a vh vi va AG KM Hh Hi Ha.
  assert (EH := eval_atom cp empty_env le m rho AG h vh Hh).
  assert (EI := eval_atom cp empty_env le m rho AG i vi Hi).
  assert (EA := eval_atom cp empty_env le m rho AG a va Ha).
  assert (EHs := eval_kidx le m rho h vh AG Hh).
  assert (EIs := eval_kidx le m rho i vi AG Hi).
  pose proof (phi_range vh) as Rh. pose proof (phi_range vi) as Ri.
  assert (E128 : eval_expr ge empty_env le m (c64 128) (Vlong (Int64.repr 128))) by apply eval_Econst_long.
  (* the writes that change nothing *)
  assert (Nop : ~ (0 <= Sint63.to_Z vh < 64 /\ 0 <= Sint63.to_Z vi < Sint63.to_Z (ksize vh M)) ->
                kmrel (kupd vh vi va M) m) by (intros N; rewrite (kupd_out vh vi va M N); exact KM).
  pose proof KM as KM0.
  destruct KM as (bt & bl & bk & bt2 & bl2 & bk2 & TAB & TAB2 & SEP). pose proof TAB as TAB0.
  destruct TAB as (Ft & Fl & Hne & T & Dis).
  unfold kit_guard.
  destruct (Z_lt_ge_dec (to_Z vh) kq_nblocks) as [Lh | Lh].
  - pose proof (T (to_Z vh) ltac:(unfold kq_nblocks in Lh; lia)) as Tk. cbv zeta in Tk.
    destruct Tk as (Bn & Hl & Hc & Hbk).
    rewrite Uint63.of_to_Z in Bn, Hl, Hc, Hbk.
    set (n := Sint63.to_Z (ksize vh M)) in *.
    assert (EL : eval_expr ge empty_env le m (kld_len (sh1 (tr_atom h))) (Vlong (Int64.repr (2 * n)))).
    { eapply eval_kld_len; [exact EHs | reflexivity | unfold kq_nblocks in Lh; lia | lia | exact Fl | exact Hl]. }
    assert (Eh : (to_Z vh <? 64) = true) by (apply Z.ltb_lt; unfold kq_nblocks in Lh; lia).
    destruct (Z_lt_ge_dec (to_Z vi) n) as [Li | Li].
    + (* a cell inside the block *)
      destruct (Hc (to_Z vi) ltac:(lia)) as (Ld & VA).
      rewrite Uint63.of_to_Z in Ld.
      destruct (Mem.valid_access_store m Mint64 (bk (to_Z vh)) (8 * to_Z vi) (enc va) VA) as (m' & ST).
      exists m'. split.
      * eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EH | exact E128 | apply typeof_atom | reflexivity] | apply bool_of | ].
        simpl. rewrite lt128_t, Eh.
        eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EI | exact EL | apply typeof_atom | reflexivity] | apply bool_of | ].
        rewrite (lt_n_t vi n) by lia.
        assert (Ei : (to_Z vi <? n) = true) by (apply Z.ltb_lt; exact Li). rewrite Ei.
        eapply exec_Sassign.
        -- apply eval_Ederef. eapply eval_kld_addr; [exact EHs | reflexivity | exact EI | apply typeof_atom | unfold kq_nblocks in Lh; lia | lia | exact Ft | exact (proj1 (Hbk ltac:(lia)))].
        -- exact EA.
        -- rewrite typeof_atom. reflexivity.
        -- eapply assign_loc_value; [reflexivity | ]. unfold Mem.storev.
           rewrite uns_off40 by (auto || lia). exact ST.
      * destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
        assert (Rk : 0 <= to_Z vh < 64) by (unfold kq_nblocks in Lh; lia).
        assert (Hpos : 0 < Sint63.to_Z (ksize (of_Z (to_Z vh)) M)) by (rewrite Uint63.of_to_Z; lia).
        destruct (S5 (to_Z vh) Rk Hpos) as (N1 & N2).
        exists bt, bl, bk, bt2, bl2, bk2. refine (conj _ (conj _ _)).
        -- eapply ktab_store_at; [ exact TAB0 | unfold kq_nblocks in Lh; lia | lia | exact ST ].
        -- eapply ktab2_frame; [ exact TAB2 | intros; apply krd32_upd | exact ST | exact N1 | exact N2 | ].
           intros k' Rk' Hp'. exact (S7 (to_Z vh) k' Rk Rk' Hpos Hp').
        -- eapply ksep_size; [ exact (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 S7)))))) | intros; apply ksize_upd ].
    + (* past the end *)
      exists m. split.
      * eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EH | exact E128 | apply typeof_atom | reflexivity] | apply bool_of | ].
        simpl. rewrite lt128_t, Eh.
        eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EI | exact EL | apply typeof_atom | reflexivity] | apply bool_of | ].
        rewrite (lt_n_t vi n) by lia.
        assert (Ei : (to_Z vi <? n) = false) by (apply Z.ltb_ge; lia). rewrite Ei. constructor.
      * apply Nop. intros [A1 A2]. apply (in_range vi n ltac:(lia)) in A2. lia.
  - exists m. split.
    + eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EH | exact E128 | apply typeof_atom | reflexivity] | apply bool_of | ].
      simpl. rewrite lt128_t.
      assert (Eh : (to_Z vh <? 64) = false) by (apply Z.ltb_ge; unfold kq_nblocks in Lh; lia). rewrite Eh. constructor.
    + apply Nop. intros [A1 A2]. apply (in_range vh kq_nblocks ltac:(unfold kq_nblocks; lia)) in A1. lia.
Qed.

(** ** The narrow blocks *)

Lemma cell_off32_val : forall vi : i63, to_Z vi < 2 ^ 36 ->
  Int64.sub (Int64.mul (tg vi) (Int64.repr 2)) (Int64.repr 2) = Int64.repr (4 * to_Z vi).
Proof.
  intros vi H. pose proof (phi_range vi). apply uinj.
  rewrite usub, umul, uns_tg, (uns_small 2) by lia.
  rewrite (uns_small (4 * to_Z vi)) by lia.
  rewrite (Z.mod_small ((2 * to_Z vi + 1) * 2)) by lia.
  replace ((2 * to_Z vi + 1) * 2 - 2) with (4 * to_Z vi) by ring.
  apply Z.mod_small. lia.
Qed.

(** the limit of narrow block [k] *)
Lemma eval_kld_len32 : forall le m H (k n : Z) bl,
  eval_expr ge empty_env le m H (Vlong (Int64.repr k)) -> typeof H = tyl ->
  0 <= k < 64 -> 0 <= n < 2 ^ 32 -> Genv.find_symbol ge kq_lens32 = Some bl ->
  Mem.load Mint32 m bl (4 * k) = Some (Vint (Int.repr n)) ->
  eval_expr ge empty_env le m (kld_len32 H) (Vlong (Int64.repr n)).
Proof.
  intros le m H k n bl EH TH Rk Rn Fl Ld. unfold kld_len32.
  econstructor.
  - eapply eval_deref_val.
    + eapply eval_add_ptr; [ eapply eval_glob; [exact Fl | reflexivity] | exact EH | exact TH | reflexivity | reflexivity | auto | lia ].
    + reflexivity.
    + rewrite Ptrofs.add_zero_l, uns_off40 by (auto || lia). exact Ld.
  - simpl. unfold sem_cast. simpl. f_equal. f_equal.
    rewrite Int.unsigned_repr by (unfold Int.max_unsigned; change Int.modulus with 4294967296; lia).
    reflexivity.
Qed.

Lemma eval_kld_addr32 : forall le m H I (k : Z) (vi : i63) bt bk,
  eval_expr ge empty_env le m H (Vlong (Int64.repr k)) -> typeof H = tyl ->
  eval_expr ge empty_env le m I (enc vi) -> typeof I = tyl ->
  0 <= k < 64 -> to_Z vi < 2 ^ 36 -> Genv.find_symbol ge kq_tab32 = Some bt ->
  Mem.load Mint64 m bt (8 * k) = Some (Vptr bk Ptrofs.zero) ->
  eval_expr ge empty_env le m (kld_addr32 H I) (Vptr bk (Ptrofs.repr (4 * to_Z vi))).
Proof.
  intros le m H I k vi bt bk EH TH EI TI Rk Rj Ft Lt. pose proof (phi_range vi).
  unfold kld_addr32, kld_base32.
  assert (EB : eval_expr ge empty_env le m
                 (Ederef (Ebinop Oadd (Evar kq_tab32 (Tarray tptr32 kq_nblocks noattr)) H (Tpointer tptr32 noattr)) tptr32)
                 (Vptr bk Ptrofs.zero)).
  { eapply eval_deref_val.
    - eapply eval_add_ptr; [ eapply eval_glob; [exact Ft | reflexivity] | exact EH | exact TH | reflexivity | reflexivity | auto | lia ].
    - reflexivity.
    - rewrite Ptrofs.add_zero_l, uns_off40 by (auto || lia). exact Lt. }
  assert (EO : eval_expr ge empty_env le m (cell_off32 I) (Vlong (Int64.repr (4 * to_Z vi)))).
  { rewrite <- (cell_off32_val vi Rj). unfold cell_off32.
    eapply eval_bin; [ | apply eval_Econst_long | reflexivity | reflexivity | reflexivity ].
    eapply eval_bin; [ exact EI | apply eval_Econst_long | exact TI | reflexivity | reflexivity ]. }
  assert (EA : eval_expr ge empty_env le m (Ebinop Oadd (Ecast (kld_base32 H) tcp) (cell_off32 I) tcp)
                 (Vptr bk (Ptrofs.add Ptrofs.zero (Ptrofs.repr (1 * (4 * to_Z vi)))))).
  { eapply eval_add_ptr with (elem := tchar); [ | exact EO | reflexivity | reflexivity | reflexivity | auto | lia ].
    eapply eval_Ecast; [exact EB | reflexivity]. }
  replace (Ptrofs.add Ptrofs.zero (Ptrofs.repr (1 * (4 * to_Z vi)))) with (Ptrofs.repr (4 * to_Z vi)) in EA
    by (rewrite Ptrofs.add_zero_l, Z.mul_1_l; reflexivity).
  eapply eval_Ecast; [exact EA | reflexivity].
Qed.

Lemma eval_kld_cell32 : forall le m H I (k : Z) (vi : i63) bt bk v,
  eval_expr ge empty_env le m H (Vlong (Int64.repr k)) -> typeof H = tyl ->
  eval_expr ge empty_env le m I (enc vi) -> typeof I = tyl ->
  0 <= k < 64 -> to_Z vi < 2 ^ 36 -> Genv.find_symbol ge kq_tab32 = Some bt ->
  Mem.load Mint64 m bt (8 * k) = Some (Vptr bk Ptrofs.zero) ->
  Mem.load Mint32 m bk (4 * to_Z vi) = Some v ->
  eval_expr ge empty_env le m (kld_cell32 H I) v.
Proof.
  intros le m H I k vi bt bk v EH TH EI TI Rk Rj Ft Lt Lc. pose proof (phi_range vi). unfold kld_cell32.
  eapply eval_deref_val.
  - eapply eval_kld_addr32; eassumption.
  - reflexivity.
  - rewrite uns_off40 by (auto || lia). exact Lc.
Qed.

Lemma kmrel_get2 : forall M m, kmrel M m -> exists bt bl bk,
  Genv.find_symbol ge kq_tab32 = Some bt /\ Genv.find_symbol ge kq_lens32 = Some bl /\
  forall k, 0 <= k < 64 -> exists n,
    n = Sint63.to_Z (klen32 (of_Z k)) /\ 0 <= n < 2 ^ 31 /\
    Mem.load Mint32 m bl (4 * k) = Some (Vint (Int.repr (2 * n))) /\
    (forall j, 0 <= j < n ->
       (exists i, Mem.load Mint32 m (bk k) (4 * j) = Some (Vint i) /\
                  Int.signed i = Sint63.to_Z (krd32 (of_Z k) (of_Z j) M)) /\
       Mem.valid_access m Mint32 (bk k) (4 * j) Writable) /\
    (0 < n -> Mem.load Mint64 m bt (8 * k) = Some (Vptr (bk k) Ptrofs.zero)).
Proof.
  intros M m (bt0 & bl0 & bk0 & bt & bl & bk & _ & (Ft & Fl & Hne & T & Dis) & _). exists bt, bl, bk.
  split; [exact Ft | split; [exact Fl | ]].
  intros k Rk. specialize (T k Rk). cbv zeta in T. destruct T as (Hn & Hl & Hc & Hbk).
  exists (Sint63.to_Z (klen32 (of_Z k))).
  refine (conj eq_refl (conj Hn (conj Hl (conj Hc _)))).
  intros Hp. exact (proj1 (Hbk Hp)).
Qed.

Lemma exec_kld32 : forall le m rho M x h i vh vi,
  agree rho le -> kmrel M m -> aval rho h = Some vh -> aval rho i = Some vi ->
  exec_stmt function_entry2 ge empty_env le m
    (kit_guard32 (tr_atom h) (tr_atom i)
       (Sset (tv x) (tagup (Ecast (kld_cell32 (sh1 (tr_atom h)) (tr_atom i)) tls))) (Sset (tv x) c1))
    E0 (PTree.set (tv x) (enc (krd32 vh vi M)) le) m Out_normal.
Proof.
  intros le m rho M x h i vh vi AG KM Hh Hi.
  assert (EH := eval_atom cp empty_env le m rho AG h vh Hh).
  assert (EI := eval_atom cp empty_env le m rho AG i vi Hi).
  assert (EHs := eval_kidx le m rho h vh AG Hh).
  pose proof (phi_range vh) as Rh. pose proof (phi_range vi) as Ri.
  assert (E128 : eval_expr ge empty_env le m (c64 128) (Vlong (Int64.repr 128))) by apply eval_Econst_long.
  unfold kit_guard32.
  eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EH | exact E128 | apply typeof_atom | reflexivity] | apply bool_of | ].
  simpl. rewrite lt128_t.
  destruct (Z_lt_ge_dec (to_Z vh) kq_nblocks) as [Lh | Lh].
  - assert (Eh : (to_Z vh <? 64) = true) by (apply Z.ltb_lt; exact Lh). rewrite Eh.
    destruct (kmrel_get2 M m KM) as (bt & bl & bk & Ft & Fl & T).
    destruct (T (to_Z vh) ltac:(unfold kq_nblocks in Lh; lia)) as (n & Hn & Bn & Hl & Hc & Ht).
    rewrite Uint63.of_to_Z in Hn. rewrite Uint63.of_to_Z in Hc.
    assert (EL : eval_expr ge empty_env le m (kld_len32 (sh1 (tr_atom h))) (Vlong (Int64.repr (2 * n)))).
    { eapply eval_kld_len32; [exact EHs | reflexivity | unfold kq_nblocks in Lh; lia | lia | exact Fl | exact Hl]. }
    eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EI | exact EL | apply typeof_atom | reflexivity] | apply bool_of | ].
    rewrite (lt_n_t vi n) by lia.
    destruct (Z_lt_ge_dec (to_Z vi) n) as [Li | Li].
    + assert (Ei : (to_Z vi <? n) = true) by (apply Z.ltb_lt; exact Li). rewrite Ei.
      apply exec_Sset.
      destruct (Hc (to_Z vi) ltac:(lia)) as ((iv & Ld & Hs) & _).
      rewrite !Uint63.of_to_Z in Hs.
      assert (EC : eval_expr ge empty_env le m (kld_cell32 (sh1 (tr_atom h)) (tr_atom i)) (Vint iv)).
      { eapply eval_kld_cell32; [exact EHs | reflexivity | exact EI | apply typeof_atom | unfold kq_nblocks in Lh; lia | lia | exact Ft | exact (Ht ltac:(lia)) | exact Ld]. }
      assert (ECast : eval_expr ge empty_env le m (Ecast (kld_cell32 (sh1 (tr_atom h)) (tr_atom i)) tls)
                        (Vlong (Int64.repr (Int.signed iv)))).
      { eapply eval_Ecast; [exact EC | reflexivity]. }
      assert (Eq : enc (krd32 vh vi M) = Vlong (Int64.or (Int64.shl (Int64.repr (Int.signed iv)) Int64.one) Int64.one)).
      { unfold enc. rewrite (up_t (Int.signed iv) (krd32 vh vi M)); [reflexivity | ].
        rewrite Hs. symmetry. apply phi_sZ. }
      rewrite Eq. apply eval_tagup; [exact ECast | right; reflexivity].
    + assert (Ei : (to_Z vi <? n) = false) by (apply Z.ltb_ge; lia). rewrite Ei.
      apply exec_Sset.
      rewrite (krd32_out vh vi M).
      * unfold enc. rewrite tg_zero. apply eval_c1.
      * intros [A1 A2]. rewrite <- Hn in A2.
        apply (in_range vi n ltac:(lia)) in A2. lia.
  - assert (Eh : (to_Z vh <? 64) = false) by (apply Z.ltb_ge; unfold kq_nblocks in Lh; lia). rewrite Eh.
    apply exec_Sset.
    rewrite (krd32_out vh vi M).
    + unfold enc. rewrite tg_zero. apply eval_c1.
    + intros [A1 A2]. apply (in_range vh kq_nblocks ltac:(unfold kq_nblocks; lia)) in A1. lia.
Qed.

(** a write inside a narrow block keeps the table relation *)
Lemma ktab2_store : forall M m bt bl bk k j va m',
  ktab2 M m bt bl bk -> 0 <= k < 64 ->
  0 <= j < Sint63.to_Z (klen32 (of_Z k)) ->
  Mem.store Mint32 m (bk k) (4 * j) (Vint (Int.repr (to_Z va))) = Some m' ->
  ktab2 (kupd32 (of_Z k) (of_Z j) va M) m' bt bl bk.
Proof.
  intros M m bt bl bk k j va m' (Ft & Fl & Hne & T & Dis) Rk Rj ST.
  pose proof (T k Rk) as Tk. cbv zeta in Tk. destruct Tk as (Bk & Hlk & Hck & Hbk).
  assert (Hpos : 0 < Sint63.to_Z (klen32 (of_Z k))) by lia.
  destruct (Hbk Hpos) as (Htk & Nt & Nl).
  assert (Rj62 : 0 <= j < 2 ^ 62) by (pose proof Bk; lia).
  refine (conj Ft (conj Fl (conj Hne (conj _ _)))).
  - intros k' Rk'. pose proof (T k' Rk') as Tk'. cbv zeta in Tk'. destruct Tk' as (Bn & Hl & Hc & Hbk').
    cbv zeta.
    refine (conj Bn (conj _ (conj _ _))).
    + rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [exact Hl | left; exact (not_eq_sym Nl)].
    + intros j' Rj'. destruct (Hc j' Rj') as ((i & Ld & Hs) & VA). split.
      * destruct (Z.eq_dec k' k) as [Ek | Ek].
        -- subst k'. destruct (Z.eq_dec j' j) as [Ej | Ej].
           ++ subst j'. exists (Int.repr (to_Z va)). rewrite (Mem.load_store_same _ _ _ _ _ _ ST). simpl.
              split; [reflexivity | ].
              rewrite (krd32_upd32_eq (of_Z k) (of_Z j) va M).
              ** symmetry. apply sx32_signed.
              ** rewrite sZ_of_Z by lia. lia.
              ** rewrite sZ_of_Z by lia. lia.
           ++ exists i. rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [ | right; change (size_chunk Mint32) with 4; destruct (Z_lt_ge_dec j' j); [left | right]; lia].
              rewrite (krd32_upd32_ne (of_Z k) (of_Z j) va (of_Z k) (of_Z j') M); [split; [exact Ld | exact Hs] | ].
              intros [_ E]. apply Ej. symmetry in E. apply of_Z_inj in E; lia.
        -- exists i. rewrite (Mem.load_store_other _ _ _ _ _ _ ST).
           ++ rewrite (krd32_upd32_ne (of_Z k) (of_Z j) va (of_Z k') (of_Z j') M); [split; [exact Ld | exact Hs] | ].
              intros [E _]. apply Ek. apply of_Z_inj in E; lia.
           ++ left. apply not_eq_sym. apply Dis; [exact Rk | exact Rk' | exact (fun E => Ek (eq_sym E)) | exact Hpos | lia].
      * exact (Mem.store_valid_access_1 _ _ _ _ _ _ ST _ _ _ _ VA).
    + intros Hp. destruct (Hbk' Hp) as (Ht' & N1 & N2).
      refine (conj _ (conj N1 N2)).
      rewrite (Mem.load_store_other _ _ _ _ _ _ ST); [exact Ht' | left; exact (not_eq_sym Nt)].
  - exact Dis.
Qed.

Lemma ktab2_store_at : forall M m bt bl bk (vh vi va : i63) m',
  ktab2 M m bt bl bk -> to_Z vh < 64 -> 0 <= to_Z vi < Sint63.to_Z (klen32 vh) ->
  Mem.store Mint32 m (bk (to_Z vh)) (4 * to_Z vi) (Vint (Int.repr (to_Z va))) = Some m' ->
  ktab2 (kupd32 vh vi va M) m' bt bl bk.
Proof.
  intros M m bt bl bk vh vi va m' KT Lh Li ST.
  pose proof (phi_range vh) as Rh.
  assert (Hv : ktab2 (kupd32 (of_Z (to_Z vh)) (of_Z (to_Z vi)) va M) m' bt bl bk).
  { eapply ktab2_store; [exact KT | lia | | exact ST]. rewrite Uint63.of_to_Z. exact Li. }
  rewrite !Uint63.of_to_Z in Hv. exact Hv.
Qed.

(** a store through the narrow tables: a write inside a block, or nothing *)
Lemma exec_kst32 : forall le m rho M h i a vh vi va,
  agree rho le -> kmrel M m -> aval rho h = Some vh -> aval rho i = Some vi -> aval rho a = Some va ->
  exists m', exec_stmt function_entry2 ge empty_env le m
    (kit_guard32 (tr_atom h) (tr_atom i)
       (Sassign (kld_cell32 (sh1 (tr_atom h)) (tr_atom i)) (Ecast (sh1 (tr_atom a)) tint32)) Sskip)
    E0 le m' Out_normal /\ kmrel (kupd32 vh vi va M) m'.
Proof.
  intros le m rho M h i a vh vi va AG KM Hh Hi Ha.
  assert (EH := eval_atom cp empty_env le m rho AG h vh Hh).
  assert (EI := eval_atom cp empty_env le m rho AG i vi Hi).
  assert (EA := eval_atom cp empty_env le m rho AG a va Ha).
  assert (EHs := eval_kidx le m rho h vh AG Hh).
  assert (EAs := eval_kidx le m rho a va AG Ha).
  pose proof (phi_range vh) as Rh. pose proof (phi_range vi) as Ri. pose proof (phi_range va) as Ra.
  assert (E128 : eval_expr ge empty_env le m (c64 128) (Vlong (Int64.repr 128))) by apply eval_Econst_long.
  assert (Nop : ~ (0 <= Sint63.to_Z vh < 64 /\ 0 <= Sint63.to_Z vi < Sint63.to_Z (klen32 vh)) ->
                kmrel (kupd32 vh vi va M) m) by (intros N; rewrite (kupd32_out vh vi va M N); exact KM).
  pose proof KM as KM0.
  destruct KM as (bt1 & bl1 & bk1 & bt & bl & bk & TAB1 & TAB & SEP). pose proof TAB as TAB0.
  destruct TAB as (Ft & Fl & Hne & T & Dis).
  unfold kit_guard32.
  destruct (Z_lt_ge_dec (to_Z vh) kq_nblocks) as [Lh | Lh].
  - pose proof (T (to_Z vh) ltac:(unfold kq_nblocks in Lh; lia)) as Tk. cbv zeta in Tk.
    destruct Tk as (Bn & Hl & Hc & Hbk).
    rewrite Uint63.of_to_Z in Bn, Hl, Hc, Hbk.
    set (n := Sint63.to_Z (klen32 vh)) in *.
    assert (EL : eval_expr ge empty_env le m (kld_len32 (sh1 (tr_atom h))) (Vlong (Int64.repr (2 * n)))).
    { eapply eval_kld_len32; [exact EHs | reflexivity | unfold kq_nblocks in Lh; lia | lia | exact Fl | exact Hl]. }
    assert (Eh : (to_Z vh <? 64) = true) by (apply Z.ltb_lt; unfold kq_nblocks in Lh; lia).
    destruct (Z_lt_ge_dec (to_Z vi) n) as [Li | Li].
    + (* a cell inside the block *)
      destruct (Hc (to_Z vi) ltac:(lia)) as (_ & VA).
      destruct (Mem.valid_access_store m Mint32 (bk (to_Z vh)) (4 * to_Z vi) (Vint (Int.repr (to_Z va))) VA) as (m' & ST).
      exists m'. split.
      * eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EH | exact E128 | apply typeof_atom | reflexivity] | apply bool_of | ].
        simpl. rewrite lt128_t, Eh.
        eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EI | exact EL | apply typeof_atom | reflexivity] | apply bool_of | ].
        rewrite (lt_n_t vi n) by lia.
        assert (Ei : (to_Z vi <? n) = true) by (apply Z.ltb_lt; exact Li). rewrite Ei.
        eapply exec_Sassign.
        -- apply eval_Ederef. eapply eval_kld_addr32; [exact EHs | reflexivity | exact EI | apply typeof_atom | unfold kq_nblocks in Lh; lia | lia | exact Ft | exact (proj1 (Hbk ltac:(lia)))].
        -- eapply eval_Ecast; [exact EAs | reflexivity].
        -- reflexivity.
        -- eapply assign_loc_value; [reflexivity | ]. unfold Mem.storev.
           rewrite uns_off40 by (auto || lia).
           cbn [cast_int_int]. rewrite uns_phi. exact ST.
      * destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
        assert (Rk : 0 <= to_Z vh < 64) by (unfold kq_nblocks in Lh; lia).
        assert (Hpos : 0 < Sint63.to_Z (klen32 (of_Z (to_Z vh)))) by (rewrite Uint63.of_to_Z; lia).
        destruct (S6 (to_Z vh) Rk Hpos) as (N1 & N2).
        exists bt1, bl1, bk1, bt, bl, bk. refine (conj _ (conj _ _)).
        -- eapply ktab_frame; [ exact TAB1 | intros; apply krd_upd32 | intros; apply ksize_upd32 | exact ST | exact N1 | exact N2 | ].
           intros k' Rk' Hp'. apply not_eq_sym. exact (S7 k' (to_Z vh) Rk' Rk Hp' Hpos).
        -- eapply ktab2_store_at; [ exact TAB0 | unfold kq_nblocks in Lh; lia | lia | exact ST ].
        -- eapply ksep_size; [ exact (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 S7)))))) | intros; apply ksize_upd32 ].
    + (* past the end *)
      exists m. split.
      * eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EH | exact E128 | apply typeof_atom | reflexivity] | apply bool_of | ].
        simpl. rewrite lt128_t, Eh.
        eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EI | exact EL | apply typeof_atom | reflexivity] | apply bool_of | ].
        rewrite (lt_n_t vi n) by lia.
        assert (Ei : (to_Z vi <? n) = false) by (apply Z.ltb_ge; lia). rewrite Ei. constructor.
      * apply Nop. intros [A1 A2]. apply (in_range vi n ltac:(lia)) in A2. lia.
  - exists m. split.
    + eapply exec_Sifthenelse; [ eapply eval_ltu; [exact EH | exact E128 | apply typeof_atom | reflexivity] | apply bool_of | ].
      simpl. rewrite lt128_t.
      assert (Eh : (to_Z vh <? 64) = false) by (apply Z.ltb_ge; unfold kq_nblocks in Lh; lia). rewrite Eh. constructor.
    + apply Nop. intros [A1 A2]. apply (in_range vh kq_nblocks ltac:(unfold kq_nblocks; lia)) in A1. lia.
Qed.

End KMEM.


(** ** The simulation *)

Section KSIM.
Variable P : prog.
Variable cp : Clight.program.
Let ge := Clight.globalenv cp.

(** the functions of [P] are in [cp], translated *)
Hypothesis cp_funs : forall g f, find P g = Some f ->
  exists b, Genv.find_symbol ge g = Some b /\
            Genv.find_funct_ptr ge b = Some (Internal (tr_fn P f)).
Hypothesis params_norepet : forall g f, find P g = Some f -> list_norepet (kparams f).

(** The machine's operations are external functions of [cp] ([hw_defs]).  What is ASSUMED of their C bodies (hw/kq_hw.h):
    called on the numbers of a run from a Clight memory that holds the kit's memory [M], each one finishes with no
    event and leaves a Clight memory that holds the memory the abstract operation gives ([hw_sem]): the cell it was
    told to fill holds what it read, no other cell of any block changes.  The devices' own behaviour is not modelled. *)
Hypothesis hw_funs : forall o, exists b, Genv.find_symbol ge (hwid o) = Some b /\ Genv.find_funct_ptr ge b = Some (External (hw_ef o) (tylist (hw_arity o)) tyl cc_default).
Hypothesis hw_law : forall o vs M m, length vs = hw_arity o -> kmrel cp M m ->
  (exists vres m1, external_call (hw_ef o) ge (map enc vs) m E0 vres m1) /\ (forall t vres m1, external_call (hw_ef o) ge (map enc vs) m t vres m1 -> t = E0 /\ kmrel cp (hw_sem o vs M) m1).

Notation execk := (exec_stmt function_entry2 ge).
Notation funcallk := (eval_funcall function_entry2 ge).

Definition LOOPK (f : fn) (le : temp_env) (m : Memory.Mem.mem) (v : i63) (M' : kmemt) : Prop :=
  exists le' m', execk empty_env le m (Sloop (tr_exp P (kparams f) (kbody f)) Sskip)
                      E0 le' m' (Out_return (Some (enc v, tyl))) /\ kmrel cp M' m'.

Definition SIMRK (f : fn) (le : temp_env) (m : Memory.Mem.mem) (s : statement) (v : i63) (M' : kmemt) : Prop :=
  exists le1 m1 out, execk empty_env le m s E0 le1 m1 out /\
    ((out = Out_return (Some (enc v, tyl)) /\ kmrel cp M' m1) \/
     (out = Out_continue /\ LOOPK f le1 m1 v M')).

Lemma to_loopk : forall f le m v M',
  SIMRK f le m (tr_exp P (kparams f) (kbody f)) v M' -> LOOPK f le m v M'.
Proof.
  intros f le m v M' (le1 & m1 & out & X & [[R MR] | [R L]]); subst.
  - exists le1, m1. split; auto. eapply exec_Sloop_stop1; eauto. constructor.
  - destruct L as (le2 & m2 & X2 & MR). exists le2, m2. split; auto.
    change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop; eauto.
    constructor. constructor.
Qed.

Lemma funcall_okk : forall fg vs rho w M M1 m,
  list_norepet (kparams fg) ->
  bind (kparams fg) vs (PTree.empty _) = Some rho ->
  (forall le m, agree rho le -> kmrel cp M m -> SIMRK fg le m (tr_exp P (kparams fg) (kbody fg)) w M1) ->
  kmrel cp M m ->
  exists m1, funcallk m (Internal (tr_fn P fg)) (map enc vs) E0 m1 (enc w) /\ kmrel cp M1 m1.
Proof.
  intros fg vs rho w M M1 m NR B IH MR.
  destruct (entry_ok P cp fg vs rho m NR B) as (le & EN & AG).
  destruct (to_loopk fg le m w M1 (IH le m AG MR)) as (le' & m' & X & MR').
  exists m'. split; auto.
  econstructor; [exact EN | exact X | simpl; split; [discriminate | reflexivity] | reflexivity].
Qed.

Theorem simk : forall f rho M e v M', evalk P f rho M e v M' ->
  forall le m, agree rho le -> kmrel cp M m -> SIMRK f le m (tr_exp P (kparams f) e) v M'.
Proof.
  induction 1; intros le m AG MR; cbn [tr_exp].
  - (* ret *)
    exists le, m, (Out_return (Some (enc v, tyl))). split; auto.
    rewrite <- (typeof_atom a). apply exec_Sreturn_some. eapply eval_atom; eauto.
  - (* op *)
    destruct (IHevalk _ m (agree_set rho le x _ AG) MR) as (le1 & m1 & out & X & R).
    exists le1, m1, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto. eapply exec_op; eauto.
  - (* if *)
    destruct (IHevalk le m AG MR) as (le1 & m1 & out & X & R).
    exists le1, m1, out. split; auto.
    eapply exec_Sifthenelse. eapply eval_cmp; eauto. rewrite typeof_cmpe. apply bool_of.
    destruct (cmp_sem c va vb); auto.
  - (* sel *)
    destruct (IHevalk _ m (agree_set rho le x _ AG) MR) as (le1 & m1 & out & X & R).
    exists le1, m1, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
    eapply exec_Sifthenelse. eapply eval_cmp; eauto. rewrite typeof_cmpe. apply bool_of.
    destruct (cmp_sem c va vb); apply exec_Sset; eapply eval_atom; eauto.
  - (* call *)
    destruct (funcall_okk fg vs rho' w M M1 m (params_norepet g fg H) H1
                (fun le m AG MR => IHevalk1 le m AG MR) MR) as (m1 & FC & MR1).
    destruct (IHevalk2 _ m1 (agree_set rho le x w AG) MR1) as (le2 & m2 & out & X & R).
    exists le2, m2, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto. eapply exec_call; eauto.
  - (* kit load *)
    destruct (IHevalk _ m (agree_set rho le x _ AG) MR) as (le1 & m1 & out & X & R).
    exists le1, m1, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto. eapply exec_kld; eauto.
  - (* kit store *)
    destruct (exec_kst cp le m rho M h i a vh vi va AG MR H H0 H1) as (m1 & XS & MR1).
    destruct (IHevalk le m1 AG MR1) as (le2 & m2 & out & X & R).
    exists le2, m2, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
  - (* narrow load *)
    destruct (IHevalk _ m (agree_set rho le x _ AG) MR) as (le1 & m1 & out & X & R).
    exists le1, m1, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto. eapply exec_kld32; eauto.
  - (* narrow store *)
    destruct (exec_kst32 cp le m rho M h i a vh vi va AG MR H H0 H1) as (m1 & XS & MR1).
    destruct (IHevalk le m1 AG MR1) as (le2 & m2 & out & X & R).
    exists le2, m2, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
  - (* machine operation *)
    destruct (hw_funs o) as (b & FS & FP).
    pose proof (avals_length _ _ _ H0) as LEN.
    assert (LV : length vs = hw_arity o) by (rewrite <- LEN; exact H).
    destruct (hw_law o vs M m LV MR) as ((vres & m1 & EC) & SEM).
    destruct (SEM E0 vres m1 EC) as (_ & MR1).
    destruct (IHevalk le m1 AG MR1) as (le2 & m2 & out & X & R).
    exists le2, m2, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
    change le with (set_opttemp None vres le).
    eapply exec_Scall with (vf := Vptr b Ptrofs.zero) (tyargs := tylist (length args)).
    + reflexivity.
    + eapply eval_Elvalue. apply eval_Evar_global; [apply PTree.gempty | exact FS].
      apply deref_loc_reference. reflexivity.
    + eapply eval_atoms; eauto.
    + rewrite Genv.find_funct_find_funct_ptr. exact FP.
    + simpl. rewrite H. reflexivity.
    + eapply eval_funcall_external. exact EC.
  - (* loop *)
    destruct (exec_scratch cp rho args vs 0 le m AG H) as (le1 & X1 & AG1 & SC).
    destruct (exec_params cp (kparams f) vs 0 (PTree.empty _) rho' le1 m (agree_empty le1) H0 SC)
      as (le2 & X2 & AG2).
    exists le2, m, Out_continue. split.
    + change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
      change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto. constructor.
    + right. split; auto. apply to_loopk. eapply IHevalk; eauto.
Qed.

(** A run of function [g] on the kit's memory is a Clight call of its translation: from any Clight memory
    that holds the abstract memory, the call ends in one that holds the memory the run ends with. *)
Theorem runk_funcall : forall g vs M v M', runk P g vs M v M' ->
  exists fg b, Genv.find_symbol ge g = Some b /\
    Genv.find_funct_ptr ge b = Some (Internal (tr_fn P fg)) /\
    length (kparams fg) = length vs /\
    forall m, kmrel cp M m ->
      exists m', funcallk m (Internal (tr_fn P fg)) (map enc vs) E0 m' (enc v) /\ kmrel cp M' m'.
Proof.
  intros g vs M v M' (fg & rho & F & B & EV).
  destruct (cp_funs g fg F) as (b & FS & FP).
  exists fg, b. split; auto. split; auto. split. eapply bind_length; eauto.
  intros m MR. eapply funcall_okk; eauto. intros le m0 AG MR0. eapply simk; eauto.
Qed.

End KSIM.
