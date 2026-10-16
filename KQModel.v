(* KQModel.v -- THE LAWS CANNOT CONTRADICT EACH OTHER: every operation of KQSpec.v's record defined in Rocq, and every
   law proved for those definitions.  So the one axiom `real_laws` (the real operations obey the laws) asks for nothing
   impossible: if it led to a contradiction, the same proof would go through for this model, where every law is a
   theorem.  The model is as plain as it can be -- a device always gives back 0, a store only records itself -- because
   the laws promise no more than that: SOME number of the right size, no cell changed. *)
From Stdlib Require Import ZArith List Lia Sint63 Bool.
Require Import KQ.KQRun KQ.KQSpec.
Import ListNotations.
Open Scope sint63_scope.
Open Scope bool_scope.

Record st := mkSt { W : int -> int -> int; N : int -> int -> int; T : list hw_ev; Z : int -> int }.
Definition mlen (h : int) : int := if (0 <=? h) && (h <? 4) then 4096 else 0.
Definition mlen32 (h : int) : int := if (0 <=? h) && (h <? 8) then 1024 else 0.
(* a block's size: its size at the start, or what it was grown to (blocks 0 .. 63; Z records it) *)
Definition msize (h : int) (z : int -> int) : int :=
  let g := if (0 <=? h) && (h <? 64) then z h else 0 in if mlen h <? g then g else mlen h.
Definition okc (h i : int) (z : int -> int) : bool := (0 <=? h) && (0 <=? i) && (i <? msize h z).
Definition okn (h i : int) : bool := (0 <=? h) && (0 <=? i) && (i <? mlen32 h).
Definition mrd (h i : int) (s : st) : int := if okc h i (Z s) then W s h i else 0.
Definition mupd (h i v : int) (s : st) : st :=
  if okc h i (Z s) then mkSt (fun h' i' => if (h =? h') && (i =? i') then v else W s h' i') (N s) (T s) (Z s) else s.
Definition mrd32 (h i : int) (s : st) : int := if okn h i then N s h i else 0.
Definition mupd32 (h i v : int) (s : st) : st :=
  if okn h i then mkSt (W s) (fun h' i' => if (h =? h') && (i =? i') then sx32 v else N s h' i') (T s) (Z s) else s.
Definition tr (e : hw_ev) (s : st) : st := mkSt (W s) (N s) (T s ++ [e]) (Z s).
(* growing: the cells from the old size on are zeroed, the new size is recorded *)
Definition mgrow (h n : int) (s : st) : st :=
  if growable h n then
    let o := msize h (Z s) in
    mkSt (fun h' i' => if (h =? h') && (o <=? i') then 0 else W s h' i') (N s) (T s)
         (fun h' => if h =? h' then (if o <? n then n else o) else Z s h')
  else s.
Definition mload (w a h i : int) (s : st) : st := tr (EvLoad w a 0 0) (mupd h i 0 (if w =? 8 then mupd h (i + 1) 0 s else s)).
Definition maload (w a h i : int) (s : st) : st := mupd h i 0 (if w =? 8 then mupd h (i + 1) 0 s else s).
Definition model : ops :=
  mkOps st mrd mupd mlen (fun h s => msize h (Z s)) mgrow mrd32 mupd32 mlen32 mload
        (fun w a v s => tr (EvStore w a v 0) s) (fun a lo hi s => tr (EvStore 8 a lo hi) s)
        (fun op w a v h i s => mupd h i 0 s) (fun op a lo hi h i s => mupd h i 0 (mupd h (i + 1) 0 s))
        (fun w a o n h i s => mupd h i 0 (mupd h (i + 1) 0 s))
        (fun a ol oh nl nh h i s => mupd h i 0 (mupd h (i + 1) 0 (mupd h (i + 2) 0 s)))
        maload (fun w a v s => s) (fun a lo hi s => s) (fun k s => tr (EvFence k) s)
        (fun d x n s => s) (fun d b n s => s) (fun x y n h i s => mupd h i 0 s) (fun a x h i s => s)
        (fun h => 0) T.

(* ---- the memory of the model *)
Lemma mrd_upd (h i v h' i' : int) (s : st) :
  mrd h' i' (mupd h i v s) = if okc h i (Z s) && ((h =? h') && (i =? i')) then v else mrd h' i' s.
Proof.
  unfold mupd. destruct (okc h i (Z s)) eqn:O; [ | reflexivity]. cbn [andb].
  unfold mrd; cbn [W Z]. destruct ((h =? h') && (i =? i')) eqn:E; [ | reflexivity].
  apply andb_prop in E as [E1 E2]. apply Uint63.eqb_spec in E1, E2. subst h' i'. rewrite O. reflexivity.
Qed.
Lemma mrd32_upd32 (h i v h' i' : int) (s : st) :
  mrd32 h' i' (mupd32 h i v s) = if okn h i && ((h =? h') && (i =? i')) then sx32 v else mrd32 h' i' s.
Proof.
  unfold mupd32. destruct (okn h i) eqn:O; [ | reflexivity]. cbn [andb].
  unfold mrd32; cbn [N]. destruct ((h =? h') && (i =? i')) eqn:E; [ | reflexivity].
  apply andb_prop in E as [E1 E2]. apply Uint63.eqb_spec in E1, E2. subst h' i'. rewrite O. reflexivity.
Qed.
Lemma mrd32_upd (h i v h' i' : int) (s : st) : mrd32 h' i' (mupd h i v s) = mrd32 h' i' s.
Proof. unfold mupd. destruct (okc h i (Z s)); reflexivity. Qed.
Lemma mrd_upd32 (h i v h' i' : int) (s : st) : mrd h' i' (mupd32 h i v s) = mrd h' i' s.
Proof. unfold mupd32. destruct (okn h i); reflexivity. Qed.
Lemma T_upd (h i v : int) (s : st) : T (mupd h i v s) = T s.
Proof. unfold mupd. destruct (okc h i (Z s)); reflexivity. Qed.
Lemma T_upd32 (h i v : int) (s : st) : T (mupd32 h i v s) = T s.
Proof. unfold mupd32. destruct (okn h i); reflexivity. Qed.
Lemma mrd_tr (e : hw_ev) (h i : int) (s : st) : mrd h i (tr e s) = mrd h i s.
Proof. reflexivity. Qed.
Lemma mrd32_tr (e : hw_ev) (h i : int) (s : st) : mrd32 h i (tr e s) = mrd32 h i s.
Proof. reflexivity. Qed.
(* a cell the model last wrote with 0 reads 0, whatever else was written to other cells after *)
Lemma mrd_upd0_same (h i : int) (s : st) : mrd h i (mupd h i 0 s) = 0.
Proof. rewrite mrd_upd. destruct (okc h i (Z s)) eqn:O; cbn [andb]; [rewrite !Uint63.eqb_refl; reflexivity | unfold mrd; rewrite O; reflexivity]. Qed.
Lemma mrd_upd0_keep (h i h' i' : int) (s : st) : mrd h' i' s = 0 -> mrd h' i' (mupd h i 0 s) = 0.
Proof. intro Z0. rewrite mrd_upd. destruct (okc h i (Z s) && ((h =? h') && (i =? i'))); [reflexivity | exact Z0]. Qed.
Lemma mrd_upd_other (h i h' i' v : int) (s : st) : other h i h' i' = true -> mrd h' i' (mupd h i v s) = mrd h' i' s.
Proof. unfold other. intro O. rewrite mrd_upd. destruct ((h =? h') && (i =? i')); [discriminate | ]. rewrite andb_false_r. reflexivity. Qed.
Lemma mrd32_upd32_other (h i h' i' v : int) (s : st) : other h i h' i' = true -> mrd32 h' i' (mupd32 h i v s) = mrd32 h' i' s.
Proof. unfold other. intro O. rewrite mrd32_upd32. destruct ((h =? h') && (i =? i')); [discriminate | ]. rewrite andb_false_r. reflexivity. Qed.
Lemma in_lim_0 (w : int) : in_lim w 0 = true.
Proof. unfold in_lim, lim. destruct (w =? 1); [reflexivity | ]. destruct (w =? 2); reflexivity. Qed.
Lemma lt_of_le_false (x y : int) : (y <=? x) = true -> (x <? y) = false.
Proof. intro L. apply le_Z in L. apply lt_Z_false. lia. Qed.

(* ---- the sizes of the model *)
Lemma Z_upd (h i v : int) (s : st) : Z (mupd h i v s) = Z s.
Proof. unfold mupd. destruct (okc h i (Z s)); reflexivity. Qed.
Lemma Z_upd32 (h i v : int) (s : st) : Z (mupd32 h i v s) = Z s.
Proof. unfold mupd32. destruct (okn h i); reflexivity. Qed.
(* a size depends on its own block's entry only *)
Lemma msize_ext (h : int) (z1 z2 : int -> int) : z1 h = z2 h -> msize h z1 = msize h z2.
Proof. intro E. unfold msize. rewrite E. reflexivity. Qed.
Lemma msize_ge (h : int) (z : int -> int) : (mlen h <=? msize h z) = true.
Proof.
  unfold msize. destruct ((0 <=? h) && (h <? 64)); [ | ]; cbv zeta.
  - destruct (mlen h <? z h) eqn:L; [apply lt_Z in L; apply le_Z; lia | apply le_Z; lia].
  - destruct (mlen h <? 0) eqn:L; [apply lt_Z in L; apply le_Z; lia | apply le_Z; lia].
Qed.
Lemma mgrow_size (h n : int) (s : st) : growable h n = true ->
  msize h (Z (mgrow h n s)) = (if msize h (Z s) <? n then n else msize h (Z s)).
Proof.
  intro G. unfold mgrow. rewrite G. cbn [Z]. unfold growable in G.
  apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
  set (o := msize h (Z s)). pose proof (msize_ge h (Z s)) as Mo. fold o in Mo.
  unfold msize at 1. rewrite G1, G2. cbn [andb]. rewrite Uint63.eqb_refl. cbv zeta.
  destruct (o <? n) eqn:On.
  - destruct (mlen h <? n) eqn:L; [reflexivity | ]. apply lt_Z in On. apply lt_Z_false in L. apply le_Z in Mo. lia.
  - destruct (mlen h <? o) eqn:L; [reflexivity | ]. apply lt_Z_false in L. apply le_Z in Mo.
    apply Sint63.to_Z_inj. lia.
Qed.
Lemma mgrow_size_ne (h n h' : int) (s : st) : (h =? h') = false -> msize h' (Z (mgrow h n s)) = msize h' (Z s).
Proof. intro E. unfold mgrow. destruct (growable h n); [ | reflexivity]. cbn [Z]. apply msize_ext. rewrite E. reflexivity. Qed.
(* growing changes no read: a cell inside the old size keeps its number, one past it read 0 before and reads 0 now *)
Lemma mrd_grow (h n h' i' : int) (s : st) : mrd h' i' (mgrow h n s) = mrd h' i' s.
Proof.
  destruct (growable h n) eqn:G; [ | unfold mgrow; rewrite G; reflexivity].
  destruct (h =? h') eqn:E.
  - apply Uint63.eqb_spec in E. subst h'. unfold mrd, okc.
    rewrite (mgrow_size h n s G). unfold mgrow at 1. rewrite G. cbn [W]. rewrite Uint63.eqb_refl. cbn [andb].
    set (o := msize h (Z s)).
    destruct ((0 <=? h) && (0 <=? i')) eqn:P; cbn [andb]; [ | reflexivity].
    destruct (o <=? i') eqn:Oi.
    + destruct (i' <? o) eqn:L2; [apply lt_Z in L2; apply le_Z in Oi; lia | ].
      destruct (i' <? (if o <? n then n else o)); reflexivity.
    + destruct (i' <? o) eqn:L2.
      * assert (L3 : (i' <? (if o <? n then n else o)) = true).
        { destruct (o <? n) eqn:On; [apply lt_Z in On; apply lt_Z in L2; apply lt_Z; lia | exact L2]. }
        rewrite L3. reflexivity.
      * apply le_Z_false in Oi. apply lt_Z_false in L2. lia.
  - unfold mrd, okc. rewrite (mgrow_size_ne h n h' s E). unfold mgrow at 1. rewrite G. cbn [W]. rewrite E. reflexivity.
Qed.

(* ---- every law *)
Theorem model_laws : laws model.
Proof.
  constructor; cbn [Rd Upd Len Size Grow Rd32 Upd32 Len32 Load Store Store64 Atomic Atomic64 Cas Cas64 ALoad AStore AStore64
                    Fence Copy Fill Cmp Call Addr Trace model].
  - intro h. unfold mlen. destruct ((0 <=? h) && (h <? 4)); reflexivity.
  - intro h. unfold mlen32. destruct ((0 <=? h) && (h <? 8)); reflexivity.
  - intros h i s N0 L. unfold mrd, okc. unfold nonneg2 in N0. rewrite N0, (lt_of_le_false _ _ L). reflexivity.
  - intros h i v s N0 L. unfold mupd, okc. unfold nonneg2 in N0. rewrite N0, (lt_of_le_false _ _ L). reflexivity.
  - intros h i s N0. unfold mrd, okc. unfold nonneg2 in N0. rewrite N0. reflexivity.
  - intros h i v s N0. unfold mupd, okc. unfold nonneg2 in N0. rewrite N0. reflexivity.
  - intros h i v s C. rewrite mrd_upd. change (cell model h i s) with (okc h i (Z s)) in C. rewrite C, !Uint63.eqb_refl. reflexivity.
  - intros h i h' i' v s O. apply mrd_upd_other, O.
  - intros h i s N0 L. unfold mrd32, okn. unfold nonneg2 in N0. rewrite N0, (lt_of_le_false _ _ L). reflexivity.
  - intros h i v s N0 L. unfold mupd32, okn. unfold nonneg2 in N0. rewrite N0, (lt_of_le_false _ _ L). reflexivity.
  - intros h i s N0. unfold mrd32, okn. unfold nonneg2 in N0. rewrite N0. reflexivity.
  - intros h i v s N0. unfold mupd32, okn. unfold nonneg2 in N0. rewrite N0. reflexivity.
  - intros h i v s C. rewrite mrd32_upd32. change (nonneg2 h i && (i <? mlen32 h)) with (okn h i) in C.
    rewrite C, !Uint63.eqb_refl. reflexivity.
  - intros h i h' i' v s O. apply mrd32_upd32_other, O.
  - intros. apply mrd32_upd.
  - intros. apply mrd_upd32.
  - intros. apply T_upd.
  - intros. apply T_upd32.
  (* loads *)
  - intros w a h i s _ _. unfold mload. rewrite mrd_tr, mrd_upd0_same. apply in_lim_0.
  - intros a h i s _ _. unfold mload. cbn [PrimInt63.eqb]. rewrite !mrd_tr, mrd_upd0_same.
    rewrite (mrd_upd0_keep _ _ _ _ _ (mrd_upd0_same _ _ _)). reflexivity.
  - intros w a h i h' i' s O1 O2. unfold mload. rewrite mrd_tr, mrd_upd_other by exact O1.
    destruct (w =? 8); [cbn [negb orb] in O2; apply mrd_upd_other, O2 | reflexivity].
  - intros. unfold mload. rewrite mrd32_tr, !mrd32_upd. destruct (w =? 8); [apply mrd32_upd | reflexivity].
  - intros w a h i s. unfold mload. cbn [T tr]. rewrite T_upd. rewrite mrd_tr, mrd_upd0_same.
    destruct (w =? 8) eqn:E; [ | reflexivity].
    rewrite mrd_tr, (mrd_upd0_keep _ _ _ _ _ (mrd_upd0_same _ _ _)), T_upd. reflexivity.
  - intros w a h i s _ _. unfold maload. rewrite mrd_upd0_same. apply in_lim_0.
  - intros a h i s _ _. unfold maload. cbn [PrimInt63.eqb]. rewrite mrd_upd0_same.
    rewrite (mrd_upd0_keep _ _ _ _ _ (mrd_upd0_same _ _ _)). reflexivity.
  - intros w a h i h' i' s O1 O2. unfold maload. rewrite mrd_upd_other by exact O1.
    destruct (w =? 8); [cbn [negb orb] in O2; apply mrd_upd_other, O2 | reflexivity].
  - intros. unfold maload. rewrite !mrd32_upd. destruct (w =? 8); [apply mrd32_upd | reflexivity].
  (* stores *)
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  (* atomics *)
  - intros. rewrite mrd_upd0_same. apply in_lim_0.
  - intros op w a v h i h' i' s O. apply mrd_upd_other, O.
  - intros. apply mrd32_upd.
  - intros. rewrite mrd_upd0_same, (mrd_upd0_keep _ _ _ _ _ (mrd_upd0_same _ _ _)). reflexivity.
  - intros op a lo hi h i h' i' s O1 O2. rewrite (mrd_upd_other _ _ _ _ _ _ O1). apply mrd_upd_other, O2.
  - intros. rewrite !mrd32_upd. reflexivity.
  - intros. rewrite mrd_upd0_same. apply in_lim_0.
  - intros. cbn zeta. rewrite (mrd_upd0_keep _ _ _ _ _ (mrd_upd0_same _ _ _)). reflexivity.
  - intros w a o n h i h' i' s O1 O2. rewrite (mrd_upd_other _ _ _ _ _ _ O1). apply mrd_upd_other, O2.
  - intros. rewrite !mrd32_upd. reflexivity.
  - intros. cbn zeta. rewrite (mrd_upd0_keep _ _ _ _ _ (mrd_upd0_keep _ _ _ _ _ (mrd_upd0_same _ _ _))). reflexivity.
  - intros a ol oh nl nh h i h' i' s O1 O2 O3.
    rewrite (mrd_upd_other _ _ _ _ _ _ O1), (mrd_upd_other _ _ _ _ _ _ O2). apply mrd_upd_other, O3.
  - intros. rewrite !mrd32_upd. reflexivity.
  (* fences, bytes in bulk *)
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros. cbn zeta. rewrite mrd_upd0_same. reflexivity.
  - intros x y n h i h' i' s O. apply mrd_upd_other, O.
  - intros. apply mrd32_upd.
  (* sizes *)
  - intros h s. apply msize_ge.
  - intros h n s G. apply mgrow_size, G.
  - intros h n h' s E. apply mgrow_size_ne, E.
  - intros h n s G. unfold mgrow. rewrite G. reflexivity.
  - intros. apply mrd_grow.
  - intros h n h' i' s. unfold mgrow. destruct (growable h n); reflexivity.
  - intros h n s. unfold mgrow. destruct (growable h n); reflexivity.
  - intros. rewrite Z_upd. reflexivity.
  - intros. rewrite Z_upd32. reflexivity.
  - intros. unfold mload. cbn [Z tr]. rewrite Z_upd. destruct (w =? 8); [rewrite Z_upd | ]; reflexivity.
  - intros. unfold maload. rewrite Z_upd. destruct (w =? 8); [rewrite Z_upd | ]; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros. rewrite Z_upd. reflexivity.
  - intros. rewrite !Z_upd. reflexivity.
  - intros. rewrite !Z_upd. reflexivity.
  - intros. rewrite !Z_upd. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros. rewrite Z_upd. reflexivity.
Qed.

Theorem laws_satisfiable : exists m : ops, laws m.
Proof. exists model. exact model_laws. Qed.
