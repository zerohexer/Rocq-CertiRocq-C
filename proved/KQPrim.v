(** Rocq's machine numbers: what its axioms only relate to others, proved equal to the kit's ordinary functions, from those axioms alone
    (Rocq-C-solution.md §12.T, F66).  [Print Assumptions] of each theorem here lists Rocq's own integer axioms and nothing else. *)
From Stdlib Require Import ZArith Lia Uint63.
From KQ Require KQRun.
Local Open Scope Z_scope.
Notation P := to_Z.
Notation kq_mh := KQRun.kq_mh.
Notation kq_h0x := KQRun.kq_h0x.
Notation kq_h0r := KQRun.kq_h0r.
Notation kq_h0 := KQRun.kq_h0.
Notation kq_t0x := KQRun.kq_t0x.
Notation kq_t0r := KQRun.kq_t0r.
Notation kq_t0 := KQRun.kq_t0.
Notation kq_d21 := KQRun.kq_d21.

Lemma P_bound : forall x, 0 <= P x < 9223372036854775808.
Proof. intros x. exact (to_Z_bounded x). Qed.
Lemma add_ok : forall a b, P a + P b < 9223372036854775808 -> P (PrimInt63.add a b) = P a + P b.
Proof.
  intros a b H. pose proof (P_bound a). pose proof (P_bound b).
  change (P (PrimInt63.add a b)) with (P (a + b)%uint63). rewrite add_spec. apply Z.mod_small. change wB with 9223372036854775808. lia.
Qed.
Lemma mul_ok : forall a b, P a * P b < 9223372036854775808 -> P (PrimInt63.mul a b) = P a * P b.
Proof.
  intros a b H. pose proof (P_bound a). pose proof (P_bound b).
  change (P (PrimInt63.mul a b)) with (P (a * b)%uint63). rewrite mul_spec. apply Z.mod_small. change wB with 9223372036854775808.
  split; [apply Z.mul_nonneg_nonneg; lia | exact H].
Qed.
Lemma lsr_21 : forall a, P (PrimInt63.lsr a 21%uint63) = P a / 2097152.
Proof. intros a. change (P (PrimInt63.lsr a 21%uint63)) with (P (a >> 21)%uint63). rewrite lsr_spec. reflexivity. Qed.
Lemma lsr_42 : forall a, P (PrimInt63.lsr a 42%uint63) = P a / 4398046511104.
Proof. intros a. change (P (PrimInt63.lsr a 42%uint63)) with (P (a >> 42)%uint63). rewrite lsr_spec. reflexivity. Qed.
Lemma mod_B : forall a, P (PrimInt63.mod a 2097152%uint63) = P a mod 2097152.
Proof. intros a. change (P (PrimInt63.mod a 2097152%uint63)) with (P (a mod 2097152)%uint63). rewrite mod_spec. reflexivity. Qed.

(** the sum of the columns *)
Lemma mh_Z : forall X0 X1 X2 Y0 Y1 Y2 : Z,
  0 <= X0 < 2097152 -> 0 <= X1 < 2097152 -> 0 <= X2 < 2097152 -> 0 <= Y0 < 2097152 -> 0 <= Y1 < 2097152 -> 0 <= Y2 < 2097152 ->
  let T0 := X0 * Y0 in
  let T1 := X0 * Y1 + X1 * Y0 + T0 / 2097152 in
  let T2 := X0 * Y2 + X1 * Y1 + X2 * Y0 + T1 / 2097152 in
  let T3 := X1 * Y2 + X2 * Y1 + T2 / 2097152 in
  (X2 * 4398046511104 + X1 * 2097152 + X0) * (Y2 * 4398046511104 + Y1 * 2097152 + Y0) / 9223372036854775808
    = T3 + X2 * Y2 * 2097152.
Proof.
  intros X0 X1 X2 Y0 Y1 Y2 H0 H1 H2 H3 H4 H5 T0 T1 T2 T3.
  assert (E0 : T0 = 2097152 * (T0 / 2097152) + T0 mod 2097152) by (apply Z.div_mod; lia).
  assert (E1 : T1 = 2097152 * (T1 / 2097152) + T1 mod 2097152) by (apply Z.div_mod; lia).
  assert (E2 : T2 = 2097152 * (T2 / 2097152) + T2 mod 2097152) by (apply Z.div_mod; lia).
  assert (R0 : 0 <= T0 mod 2097152 < 2097152) by (apply Z.mod_pos_bound; lia).
  assert (R1 : 0 <= T1 mod 2097152 < 2097152) by (apply Z.mod_pos_bound; lia).
  assert (R2 : 0 <= T2 mod 2097152 < 2097152) by (apply Z.mod_pos_bound; lia).
  symmetry. apply (Z.div_unique_pos _ _ _ (T0 mod 2097152 + 2097152 * (T1 mod 2097152) + 4398046511104 * (T2 mod 2097152))); [lia |].
  unfold T3. subst T0 T1 T2. cbv zeta in *.
  set (A0 := X0 * Y0) in *.
  set (Q0 := A0 / 2097152) in *. set (M0 := A0 mod 2097152) in *.
  set (Q1 := (X0 * Y1 + X1 * Y0 + Q0) / 2097152) in *. set (M1 := (X0 * Y1 + X1 * Y0 + Q0) mod 2097152) in *.
  set (Q2 := (X0 * Y2 + X1 * Y1 + X2 * Y0 + Q1) / 2097152) in *. set (M2 := (X0 * Y2 + X1 * Y1 + X2 * Y0 + Q1) mod 2097152) in *.
  subst A0. ring_simplify. ring_simplify in E0. ring_simplify in E1. ring_simplify in E2. lia.
Qed.

Lemma split3 : forall x, P x = (P x / 4398046511104) * 4398046511104 + ((P x / 2097152) mod 2097152) * 2097152 + P x mod 2097152
  /\ 0 <= P x / 4398046511104 < 2097152 /\ 0 <= (P x / 2097152) mod 2097152 < 2097152 /\ 0 <= P x mod 2097152 < 2097152.
Proof.
  intros x. pose proof (P_bound x) as B. Z.div_mod_to_equations. lia.
Qed.

Lemma kq_mh_spec : forall x y, P (kq_mh x y) = P x * P y / 9223372036854775808.
Proof.
  intros x y. unfold kq_mh.
  destruct (split3 x) as (Sx & Bx2 & Bx1 & Bx0). destruct (split3 y) as (Sy & By2 & By1 & By0).
  set (X2 := P x / 4398046511104) in *. set (X1 := (P x / 2097152) mod 2097152) in *. set (X0 := P x mod 2097152) in *.
  set (Y2 := P y / 4398046511104) in *. set (Y1 := (P y / 2097152) mod 2097152) in *. set (Y0 := P y mod 2097152) in *.
  rewrite Sx, Sy.
  rewrite (mh_Z X0 X1 X2 Y0 Y1 Y2) by assumption. cbv zeta.
  assert (Vx0 : P (PrimInt63.mod x 2097152%uint63) = X0) by apply mod_B.
  assert (Vx1 : P (PrimInt63.mod (PrimInt63.lsr x 21%uint63) 2097152%uint63) = X1) by (rewrite mod_B, lsr_21; reflexivity).
  assert (Vx2 : P (PrimInt63.lsr x 42%uint63) = X2) by apply lsr_42.
  assert (Vy0 : P (PrimInt63.mod y 2097152%uint63) = Y0) by apply mod_B.
  assert (Vy1 : P (PrimInt63.mod (PrimInt63.lsr y 21%uint63) 2097152%uint63) = Y1) by (rewrite mod_B, lsr_21; reflexivity).
  assert (Vy2 : P (PrimInt63.lsr y 42%uint63) = Y2) by apply lsr_42.
  set (x0 := PrimInt63.mod x 2097152%uint63) in *. set (x1 := PrimInt63.mod (PrimInt63.lsr x 21%uint63) 2097152%uint63) in *. set (x2 := PrimInt63.lsr x 42%uint63) in *.
  set (y0 := PrimInt63.mod y 2097152%uint63) in *. set (y1 := PrimInt63.mod (PrimInt63.lsr y 21%uint63) 2097152%uint63) in *. set (y2 := PrimInt63.lsr y 42%uint63) in *.
  assert (Mb : forall a b, 0 <= a < 2097152 -> 0 <= b < 2097152 -> 0 <= a * b <= 4398042316801).
  { intros a b Ha Hb. split; [apply Z.mul_nonneg_nonneg; lia |]. change 4398042316801 with (2097151 * 2097151). apply Z.mul_le_mono_nonneg; lia. }
  pose proof (Mb _ _ Bx0 By0) as M00. pose proof (Mb _ _ Bx0 By1) as M01. pose proof (Mb _ _ Bx0 By2) as M02.
  pose proof (Mb _ _ Bx1 By0) as M10. pose proof (Mb _ _ Bx1 By1) as M11. pose proof (Mb _ _ Bx1 By2) as M12.
  pose proof (Mb _ _ Bx2 By0) as M20. pose proof (Mb _ _ Bx2 By1) as M21. pose proof (Mb _ _ Bx2 By2) as M22.
  assert (E00 : P (PrimInt63.mul x0 y0) = X0 * Y0) by (rewrite mul_ok; rewrite ?Vx0, ?Vy0; lia).
  assert (E01 : P (PrimInt63.mul x0 y1) = X0 * Y1) by (rewrite mul_ok; rewrite ?Vx0, ?Vy1; lia).
  assert (E02 : P (PrimInt63.mul x0 y2) = X0 * Y2) by (rewrite mul_ok; rewrite ?Vx0, ?Vy2; lia).
  assert (E10 : P (PrimInt63.mul x1 y0) = X1 * Y0) by (rewrite mul_ok; rewrite ?Vx1, ?Vy0; lia).
  assert (E11 : P (PrimInt63.mul x1 y1) = X1 * Y1) by (rewrite mul_ok; rewrite ?Vx1, ?Vy1; lia).
  assert (E12 : P (PrimInt63.mul x1 y2) = X1 * Y2) by (rewrite mul_ok; rewrite ?Vx1, ?Vy2; lia).
  assert (E20 : P (PrimInt63.mul x2 y0) = X2 * Y0) by (rewrite mul_ok; rewrite ?Vx2, ?Vy0; lia).
  assert (E21 : P (PrimInt63.mul x2 y1) = X2 * Y1) by (rewrite mul_ok; rewrite ?Vx2, ?Vy1; lia).
  assert (E22 : P (PrimInt63.mul x2 y2) = X2 * Y2) by (rewrite mul_ok; rewrite ?Vx2, ?Vy2; lia).
  (* the columns, each small *)
  assert (D0 : 0 <= X0 * Y0 / 2097152 <= 2097151) by (Z.div_mod_to_equations; lia).
  assert (T1v : P (PrimInt63.add (PrimInt63.add (PrimInt63.mul x0 y1) (PrimInt63.mul x1 y0)) (PrimInt63.lsr (PrimInt63.mul x0 y0) 21%uint63)) = X0 * Y1 + X1 * Y0 + X0 * Y0 / 2097152).
  { assert (A2 : P (PrimInt63.add (PrimInt63.mul x0 y1) (PrimInt63.mul x1 y0)) = X0 * Y1 + X1 * Y0) by (rewrite add_ok; rewrite ?E01, ?E10; lia).
    rewrite add_ok; rewrite ?A2, ?lsr_21, ?E00; lia. }
  set (t1 := PrimInt63.add (PrimInt63.add (PrimInt63.mul x0 y1) (PrimInt63.mul x1 y0)) (PrimInt63.lsr (PrimInt63.mul x0 y0) 21%uint63)) in *.
  set (V1 := X0 * Y1 + X1 * Y0 + X0 * Y0 / 2097152) in *.
  assert (D1 : 0 <= V1 / 2097152 <= 8388607) by (Z.div_mod_to_equations; lia).
  assert (T2v : P (PrimInt63.add (PrimInt63.add (PrimInt63.add (PrimInt63.mul x0 y2) (PrimInt63.mul x1 y1)) (PrimInt63.mul x2 y0)) (PrimInt63.lsr t1 21%uint63)) = X0 * Y2 + X1 * Y1 + X2 * Y0 + V1 / 2097152).
  { assert (A2 : P (PrimInt63.add (PrimInt63.mul x0 y2) (PrimInt63.mul x1 y1)) = X0 * Y2 + X1 * Y1) by (rewrite add_ok; rewrite ?E02, ?E11; lia).
    assert (A3 : P (PrimInt63.add (PrimInt63.add (PrimInt63.mul x0 y2) (PrimInt63.mul x1 y1)) (PrimInt63.mul x2 y0)) = X0 * Y2 + X1 * Y1 + X2 * Y0) by (rewrite add_ok; rewrite ?A2, ?E20; lia).
    rewrite add_ok; rewrite ?A3, ?lsr_21, ?T1v; lia. }
  set (t2 := PrimInt63.add (PrimInt63.add (PrimInt63.add (PrimInt63.mul x0 y2) (PrimInt63.mul x1 y1)) (PrimInt63.mul x2 y0)) (PrimInt63.lsr t1 21%uint63)) in *.
  set (V2 := X0 * Y2 + X1 * Y1 + X2 * Y0 + V1 / 2097152) in *.
  assert (D2 : 0 <= V2 / 2097152 <= 8388607) by (Z.div_mod_to_equations; lia).
  assert (T3v : P (PrimInt63.add (PrimInt63.add (PrimInt63.mul x1 y2) (PrimInt63.mul x2 y1)) (PrimInt63.lsr t2 21%uint63)) = X1 * Y2 + X2 * Y1 + V2 / 2097152).
  { assert (A2 : P (PrimInt63.add (PrimInt63.mul x1 y2) (PrimInt63.mul x2 y1)) = X1 * Y2 + X2 * Y1) by (rewrite add_ok; rewrite ?E12, ?E21; lia).
    rewrite add_ok; rewrite ?A2, ?lsr_21, ?T2v; lia. }
  set (t3 := PrimInt63.add (PrimInt63.add (PrimInt63.mul x1 y2) (PrimInt63.mul x2 y1)) (PrimInt63.lsr t2 21%uint63)) in *.
  (* the sum is below wB: the product of two numbers below wB, over wB *)
  assert (Tot : X1 * Y2 + X2 * Y1 + V2 / 2097152 + X2 * Y2 * 2097152 < 9223372036854775808).
  { pose proof (mh_Z X0 X1 X2 Y0 Y1 Y2 Bx0 Bx1 Bx2 By0 By1 By2) as W. cbv zeta in W. fold V1 V2 in W. rewrite <- W.
    rewrite <- Sx, <- Sy. pose proof (P_bound x). pose proof (P_bound y). apply Z.div_lt_upper_bound; [lia |]. change (9223372036854775808 * 9223372036854775808) with (9223372036854775808 * 9223372036854775808). apply Z.mul_lt_mono_nonneg; lia. }
  assert (C22 : P (PrimInt63.mul (PrimInt63.mul x2 y2) 2097152%uint63) = X2 * Y2 * 2097152).
  { rewrite mul_ok; rewrite E22; change (P 2097152%uint63) with 2097152; lia. }
  rewrite add_ok; rewrite T3v, C22; [reflexivity | exact Tot].
Qed.

(** the high half of a product *)
Lemma kq_mulhi_eq : forall x y, fst (PrimInt63.mulc x y) = kq_mh x y.
Proof.
  intros x y. apply to_Z_inj. rewrite kq_mh_spec.
  pose proof (mulc_spec x y) as S. pose proof (P_bound (snd (PrimInt63.mulc x y))) as L. pose proof (P_bound (fst (PrimInt63.mulc x y))) as H.
  change (wB) with 9223372036854775808 in S.
  rewrite S. apply (Z.div_unique_pos _ _ _ (P (snd (PrimInt63.mulc x y)))); [lia | lia].
Qed.

(** the zeros above a number *)
Definition H0Inv (X : Z) (x r : int) (rem : Z) : Prop :=
  0 < X /\ P x = X * 2 ^ P r /\ 4611686018427387904 <= P x * 2 ^ rem /\ 0 <= P r <= 63 - rem.

Lemma eqb0_true : forall a, PrimInt63.eqb a 0%uint63 = true -> P a = 0.
Proof. intros a H. change (PrimInt63.eqb a 0%uint63) with (a =? 0)%uint63 in H. apply eqb_spec in H. subst a. reflexivity. Qed.
Lemma eqb0_false : forall a, PrimInt63.eqb a 0%uint63 = false -> P a <> 0.
Proof.
  intros a H E. assert (A : a = 0%uint63) by (apply to_Z_inj; rewrite E; reflexivity).
  subst a. discriminate H.
Qed.
Lemma pw63 : forall s, 0 <= s <= 63 -> 2 ^ (63 - s) * 2 ^ s = 9223372036854775808.
Proof. intros s H. rewrite <- Z.pow_add_r by lia. replace (63 - s + s) with 63 by lia. reflexivity. Qed.
Lemma P_lsr : forall a b, P (PrimInt63.lsr a b) = P a / 2 ^ P b.
Proof. intros a b. exact (lsr_spec a b). Qed.
Lemma P_lsl : forall a b, P (PrimInt63.lsl a b) = (P a * 2 ^ P b) mod 9223372036854775808.
Proof. intros a b. exact (lsl_spec a b). Qed.

Lemma h0_step : forall X x r si ti s, P si = s -> P ti = 63 - s -> 1 <= s <= 32 -> H0Inv X x r (2 * s - 1) ->
  H0Inv X (kq_h0x ti si x) (kq_h0r ti si x r) (s - 1).
Proof.
  intros X x r si ti s Es Et Hs (PX & Ex & Lo & Br). unfold kq_h0x, kq_h0r, H0Inv.
  pose proof (P_bound x) as Bx. pose proof (pw63 s ltac:(lia)) as W.
  assert (Ps : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (Pt : 0 < 2 ^ (63 - s)) by (apply Z.pow_pos_nonneg; lia).
  assert (Pm : 0 < 2 ^ (s - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Dbl : 2 ^ (2 * s - 1) = 2 ^ s * 2 ^ (s - 1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  destruct (PrimInt63.eqb (PrimInt63.lsr x ti) 0%uint63) eqn:C.
  - apply eqb0_true in C. rewrite P_lsr, Et in C.
    assert (Lt : P x < 2 ^ (63 - s)).
    { apply Z.div_small_iff in C; [lia | lia]. }
    assert (Sh : P (PrimInt63.lsl x si) = P x * 2 ^ s).
    { rewrite P_lsl, Es. apply Z.mod_small. split; [apply Z.mul_nonneg_nonneg; lia |]. rewrite <- W. apply Z.mul_lt_mono_pos_r; lia. }
    assert (Ar : P (PrimInt63.add r si) = P r + s) by (rewrite add_ok; rewrite ?Es; lia).
    rewrite Sh, Ar. repeat split; try lia.
    rewrite Ex, Z.pow_add_r by lia. ring.
  - apply eqb0_false in C. rewrite P_lsr, Et in C.
    assert (Ge : 2 ^ (63 - s) <= P x).
    { destruct (Z_lt_le_dec (P x) (2 ^ (63 - s))) as [L|L]; [|exact L]. exfalso. apply C. apply Z.div_small. lia. }
    repeat split; try lia.
    assert (Z : 2 ^ (63 - s) * 2 ^ (s - 1) = 4611686018427387904).
    { rewrite <- Z.pow_add_r by lia. replace (63 - s + (s - 1)) with 62 by lia. reflexivity. }
    rewrite <- Z. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma pow_uniq : forall X a b, 0 < X -> 0 <= a -> 0 <= b ->
  4611686018427387904 <= 2 ^ a * X < 9223372036854775808 -> 4611686018427387904 <= 2 ^ b * X < 9223372036854775808 -> a = b.
Proof.
  assert (K : forall X a b, 0 < X -> 0 <= a -> a < b -> 4611686018427387904 <= 2 ^ a * X -> 2 ^ b * X < 9223372036854775808 -> False).
  { intros X a b PX Ha Lt L U.
    assert (M : 2 ^ (a + 1) <= 2 ^ b) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.pow_add_r in M by lia. change (2 ^ 1) with 2 in M.
    assert (A : 2 ^ a * 2 * X <= 2 ^ b * X) by (apply Z.mul_le_mono_nonneg_r; lia). nia. }
  intros X a b PX Ha Hb [L1 U1] [L2 U2].
  destruct (Z.lt_trichotomy a b) as [Lt|[Eq|Gt]]; [exfalso; exact (K X a b PX Ha Lt L1 U2) | exact Eq | exfalso; exact (K X b a PX Hb ltac:(lia) L2 U1)].
Qed.

Lemma kq_h0_eq : forall x, PrimInt63.head0 x = kq_h0 x.
Proof.
  intros x. destruct (PrimInt63.eqb x 0%uint63) eqn:Z0.
  - change (PrimInt63.eqb x 0%uint63) with (x =? 0)%uint63 in Z0. apply eqb_spec in Z0. subst x. reflexivity.
  - apply eqb0_false in Z0. pose proof (P_bound x) as Bx.
    assert (I0 : H0Inv (P x) x 0%uint63 63).
    { unfold H0Inv. change (P 0%uint63) with 0. change (2 ^ 0) with 1. change (2 ^ 63) with 9223372036854775808. repeat split; lia. }
    unfold kq_h0. cbv zeta.
    set (x1 := kq_h0x 31%uint63 32%uint63 x). set (r1 := kq_h0r 31%uint63 32%uint63 x 0%uint63).
    set (x2 := kq_h0x 47%uint63 16%uint63 x1). set (r2 := kq_h0r 47%uint63 16%uint63 x1 r1).
    set (x3 := kq_h0x 55%uint63 8%uint63 x2). set (r3 := kq_h0r 55%uint63 8%uint63 x2 r2).
    set (x4 := kq_h0x 59%uint63 4%uint63 x3). set (r4 := kq_h0r 59%uint63 4%uint63 x3 r3).
    set (x5 := kq_h0x 61%uint63 2%uint63 x4). set (r5 := kq_h0r 61%uint63 2%uint63 x4 r4).
    set (r6 := kq_h0r 62%uint63 1%uint63 x5 r5).
    pose proof (h0_step (P x) x 0%uint63 32%uint63 31%uint63 32 eq_refl eq_refl ltac:(lia) I0) as I1. fold x1 r1 in I1. change (32 - 1) with 31 in I1.
    pose proof (h0_step (P x) x1 r1 16%uint63 47%uint63 16 eq_refl eq_refl ltac:(lia) I1) as I2. fold x2 r2 in I2. change (16 - 1) with 15 in I2.
    pose proof (h0_step (P x) x2 r2 8%uint63 55%uint63 8 eq_refl eq_refl ltac:(lia) I2) as I3. fold x3 r3 in I3. change (8 - 1) with 7 in I3.
    pose proof (h0_step (P x) x3 r3 4%uint63 59%uint63 4 eq_refl eq_refl ltac:(lia) I3) as I4. fold x4 r4 in I4. change (4 - 1) with 3 in I4.
    pose proof (h0_step (P x) x4 r4 2%uint63 61%uint63 2 eq_refl eq_refl ltac:(lia) I4) as I5. fold x5 r5 in I5. change (2 - 1) with 1 in I5.
    pose proof (h0_step (P x) x5 r5 1%uint63 62%uint63 1 eq_refl eq_refl ltac:(lia) I5) as I6. fold r6 in I6. change (1 - 1) with 0 in I6.
    destruct I6 as (PX & E6 & L6 & B6). change (2 ^ 0) with 1 in L6.
    set (x6 := kq_h0x 62%uint63 1%uint63 x5) in *.
    pose proof (P_bound x6) as U6.
    pose proof (head0_spec x ltac:(lia)) as H.
    pose proof (P_bound (PrimInt63.head0 x)) as Bh.
    apply to_Z_inj. change (Z.div wB 2) with 4611686018427387904 in H. change wB with 9223372036854775808 in H.
    apply (pow_uniq (P x)); try lia.
Qed.

(** the zeros below a number *)
Definition T0Inv (X : Z) (x r : int) (rem : Z) : Prop :=
  0 < X /\ X = P x * 2 ^ P r /\ P x mod 2 ^ (rem + 1) <> 0 /\ 0 <= P r <= 63 - rem.
Lemma t0_test : forall x t s, P t = 63 - s -> 1 <= s <= 32 ->
  (PrimInt63.eqb (PrimInt63.lsl x t) 0%uint63 = true <-> P x mod 2 ^ s = 0).
Proof.
  intros x t s Et Hs. pose proof (P_bound x) as Bx. pose proof (pw63 s ltac:(lia)) as W.
  assert (Ps : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (Pt : 0 < 2 ^ (63 - s)) by (apply Z.pow_pos_nonneg; lia).
  assert (V : P (PrimInt63.lsl x t) = (P x mod 2 ^ s) * 2 ^ (63 - s)).
  { rewrite P_lsl, Et. rewrite (Z.div_mod (P x) (2 ^ s)) at 1 by lia.
    pose proof (Z.mod_pos_bound (P x) (2 ^ s) ltac:(lia)) as M.
    set (q := P x / 2 ^ s) in *. set (m := P x mod 2 ^ s) in *.
    replace ((2 ^ s * q + m) * 2 ^ (63 - s)) with (m * 2 ^ (63 - s) + q * (2 ^ (63 - s) * 2 ^ s)) by ring.
    rewrite W, Z.mod_add by lia. apply Z.mod_small. split; [apply Z.mul_nonneg_nonneg; lia |].
    rewrite <- W, Z.mul_comm. apply Z.mul_lt_mono_pos_l; lia. }
  split.
  - intros H. apply eqb0_true in H. rewrite V in H. apply Z.mul_eq_0 in H. destruct H; lia.
  - intros H. assert (Z0 : P (PrimInt63.lsl x t) = 0) by (rewrite V, H; ring).
    destruct (PrimInt63.eqb (PrimInt63.lsl x t) 0%uint63) eqn:C; [reflexivity | exfalso].
    apply eqb0_false in C. apply C. exact Z0.
Qed.
Lemma t0_step : forall X x r si ti s, P si = s -> P ti = 63 - s -> 1 <= s <= 32 -> T0Inv X x r (2 * s - 1) ->
  T0Inv X (kq_t0x si ti x) (kq_t0r si ti x r) (s - 1).
Proof.
  intros X x r si ti s Es Et Hs (PX & Ex & Nz & Br). unfold kq_t0x, kq_t0r, T0Inv.
  pose proof (P_bound x) as Bx. pose proof (t0_test x ti s Et Hs) as T.
  assert (Ps : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  replace (2 * s - 1 + 1) with (s + s) in Nz by lia. replace (s - 1 + 1) with s by lia.
  destruct (PrimInt63.eqb (PrimInt63.lsl x ti) 0%uint63) eqn:C.
  - clear C; pose proof (proj1 T eq_refl) as C.
    assert (Dv : P x = 2 ^ s * (P x / 2 ^ s)) by (rewrite (Z.div_mod (P x) (2 ^ s)) at 1 by lia; lia).
    assert (Sh : P (PrimInt63.lsr x si) = P x / 2 ^ s) by (rewrite P_lsr, Es; reflexivity).
    assert (Ar : P (PrimInt63.add r si) = P r + s) by (rewrite add_ok; rewrite ?Es; lia).
    rewrite Sh, Ar. repeat split; try lia.
    + rewrite Ex, Z.pow_add_r by lia. rewrite Dv at 1. ring.
    + intros M. apply Nz. rewrite Dv.
      assert (Dq : P x / 2 ^ s = 2 ^ s * (P x / 2 ^ s / 2 ^ s)) by (rewrite (Z.div_mod (P x / 2 ^ s) (2 ^ s)) at 1 by lia; lia).
      rewrite Dq, Z.pow_add_r by lia. rewrite Z.mul_assoc. rewrite Z.mul_comm. apply Z.mod_mul.
      assert (0 < 2 ^ s * 2 ^ s) by nia. lia.
  - assert (Nm : P x mod 2 ^ s <> 0) by (intros M; pose proof (proj2 T M); discriminate).
    repeat split; try lia.
Qed.
Lemma odd_uniq : forall X a b y z, 0 <= a -> 0 <= b -> 0 <= y -> 0 <= z -> X = (2 * y + 1) * 2 ^ a -> X = (2 * z + 1) * 2 ^ b -> a = b.
Proof.
  assert (K : forall a b y z, 0 <= a -> a < b -> 0 <= y -> 0 <= z -> (2 * y + 1) * 2 ^ a = (2 * z + 1) * 2 ^ b -> False).
  { intros a b y z Ha Lt Hy Hz E.
    assert (B : b = a + 1 + (b - a - 1)) by lia. rewrite B in E. rewrite !Z.pow_add_r in E by lia. change (2 ^ 1) with 2 in E.
    assert (Pa : 0 < 2 ^ a) by (apply Z.pow_pos_nonneg; lia).
    assert (C : 2 * y + 1 = (2 * z + 1) * (2 * 2 ^ (b - a - 1))).
    { apply (Z.mul_cancel_r _ _ (2 ^ a)); [lia |]. rewrite E. ring. }
    set (w := (2 * z + 1) * 2 ^ (b - a - 1)) in *. assert (D : 2 * y + 1 = 2 * w) by (rewrite C; unfold w; ring). lia. }
  intros X a b y z Ha Hb Hy Hz E1 E2.
  destruct (Z.lt_trichotomy a b) as [Lt|[Eq|Gt]]; [exfalso; exact (K a b y z Ha Lt Hy Hz (eq_trans (eq_sym E1) E2)) | exact Eq | exfalso; exact (K b a z y Hb ltac:(lia) Hz Hy (eq_trans (eq_sym E2) E1))].
Qed.
Lemma kq_t0_eq : forall x, PrimInt63.tail0 x = kq_t0 x.
Proof.
  intros x. destruct (PrimInt63.eqb x 0%uint63) eqn:Z0.
  - change (PrimInt63.eqb x 0%uint63) with (x =? 0)%uint63 in Z0. apply eqb_spec in Z0. subst x. reflexivity.
  - apply eqb0_false in Z0. pose proof (P_bound x) as Bx.
    assert (I0 : T0Inv (P x) x 0%uint63 63).
    { unfold T0Inv. change (P 0%uint63) with 0. change (2 ^ 0) with 1. change (63 + 1) with 64. repeat split; try lia.
      rewrite Z.mod_small; [lia | change (2 ^ 64) with 18446744073709551616; lia]. }
    unfold kq_t0. cbv zeta.
    set (x1 := kq_t0x 32%uint63 31%uint63 x). set (r1 := kq_t0r 32%uint63 31%uint63 x 0%uint63).
    set (x2 := kq_t0x 16%uint63 47%uint63 x1). set (r2 := kq_t0r 16%uint63 47%uint63 x1 r1).
    set (x3 := kq_t0x 8%uint63 55%uint63 x2). set (r3 := kq_t0r 8%uint63 55%uint63 x2 r2).
    set (x4 := kq_t0x 4%uint63 59%uint63 x3). set (r4 := kq_t0r 4%uint63 59%uint63 x3 r3).
    set (x5 := kq_t0x 2%uint63 61%uint63 x4). set (r5 := kq_t0r 2%uint63 61%uint63 x4 r4).
    set (r6 := kq_t0r 1%uint63 62%uint63 x5 r5).
    pose proof (t0_step (P x) x 0%uint63 32%uint63 31%uint63 32 eq_refl eq_refl ltac:(lia) I0) as I1. fold x1 r1 in I1. change (32 - 1) with 31 in I1.
    pose proof (t0_step (P x) x1 r1 16%uint63 47%uint63 16 eq_refl eq_refl ltac:(lia) I1) as I2. fold x2 r2 in I2. change (16 - 1) with 15 in I2.
    pose proof (t0_step (P x) x2 r2 8%uint63 55%uint63 8 eq_refl eq_refl ltac:(lia) I2) as I3. fold x3 r3 in I3. change (8 - 1) with 7 in I3.
    pose proof (t0_step (P x) x3 r3 4%uint63 59%uint63 4 eq_refl eq_refl ltac:(lia) I3) as I4. fold x4 r4 in I4. change (4 - 1) with 3 in I4.
    pose proof (t0_step (P x) x4 r4 2%uint63 61%uint63 2 eq_refl eq_refl ltac:(lia) I4) as I5. fold x5 r5 in I5. change (2 - 1) with 1 in I5.
    pose proof (t0_step (P x) x5 r5 1%uint63 62%uint63 1 eq_refl eq_refl ltac:(lia) I5) as I6. fold r6 in I6. change (1 - 1) with 0 in I6.
    destruct I6 as (PX & E6 & N6 & B6). change (0 + 1) with 1 in N6. change (2 ^ 1) with 2 in N6.
    set (x6 := kq_t0x 1%uint63 62%uint63 x5) in *.
    pose proof (P_bound x6) as U6.
    destruct (tail0_spec x ltac:(lia)) as (y & Hy & Ey).
    pose proof (P_bound (PrimInt63.tail0 x)) as Bh.
    assert (Od : P x6 = 2 * (P x6 / 2) + 1).
    { rewrite (Z.div_mod (P x6) 2) at 1 by lia. pose proof (Z.mod_pos_bound (P x6) 2 ltac:(lia)). lia. }
    assert (Q : 0 <= P x6 / 2) by (apply Z.div_pos; lia).
    apply to_Z_inj. apply (odd_uniq (P x) _ _ y (P x6 / 2)); try lia.
Qed.

(** a number of two digits over a third, the first below the third: shift and subtract *)
Notation kq_d21_go := KQRun.kq_d21g.
Lemma kq_nat63 : KQRun.kq_nat 63%uint63 = 63%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma kq_d21_k : forall k m : nat, k = m -> forall c q r l, kq_d21_go k c q r l = kq_d21_go m c q r l.
Proof. intros k m -> c q r l. reflexivity. Qed.
Lemma kq_d21_go_eq : forall a b c, kq_d21 a b c = kq_d21_go 63 c 0%uint63 a b.
Proof. intros a b c. exact (kq_d21_k (KQRun.kq_nat 63%uint63) 63%nat kq_nat63 c 0%uint63 a b). Qed.

Lemma P_shl1 : forall a, P (PrimInt63.lsl a 1%uint63) = (2 * P a) mod 9223372036854775808.
Proof. intros a. rewrite P_lsl. change (2 ^ P 1%uint63) with 2. rewrite Z.mul_comm. reflexivity. Qed.
Lemma P_shr62 : forall a, P (PrimInt63.lsr a 62%uint63) = P a / 4611686018427387904.
Proof. intros a. rewrite P_lsr. reflexivity. Qed.
Lemma P_add : forall a b, P (PrimInt63.add a b) = (P a + P b) mod 9223372036854775808.
Proof. intros a b. exact (add_spec a b). Qed.
Lemma P_sub : forall a b, P (PrimInt63.sub a b) = (P a - P b) mod 9223372036854775808.
Proof. intros a b. exact (sub_spec a b). Qed.
Lemma P_ltb : forall a b, PrimInt63.ltb a b = true <-> P a < P b.
Proof. intros a b. exact (ltb_spec a b). Qed.

(** one round *)
Lemma d21_round : forall (c q r l : int) (Hi N w e : Z),
  0 < w -> 0 < e -> w * e = 4611686018427387904 -> 0 <= N -> P r < P c ->
  P q < e -> N / (2 * w) = P q * P c + P r -> P l = (N mod (2 * w)) * e ->
  let n := PrimInt63.add (PrimInt63.lsl r 1%uint63) (PrimInt63.lsr l 62%uint63) in
  let q' := if andb (PrimInt63.eqb (PrimInt63.lsr r 62%uint63) 0%uint63) (PrimInt63.ltb n c) then PrimInt63.lsl q 1%uint63 else PrimInt63.add (PrimInt63.lsl q 1%uint63) 1%uint63 in
  let r' := if andb (PrimInt63.eqb (PrimInt63.lsr r 62%uint63) 0%uint63) (PrimInt63.ltb n c) then n else PrimInt63.sub n c in
  P r' < P c /\ P q' < 2 * e /\ N / w = P q' * P c + P r' /\ P (PrimInt63.lsl l 1%uint63) = (N mod w) * (2 * e).
Proof.
  intros c q r l Hi N w e Pw Pe Wbase HN Rc Qe EHi El n q' r'.
  pose proof (P_bound r) as Br. pose proof (P_bound c) as Bc. pose proof (P_bound q) as Bq. pose proof (P_bound l) as Bl.
  (* the top digit of what is left *)
  set (M := N mod (2 * w)) in *.
  assert (BM : 0 <= M < 2 * w) by (apply Z.mod_pos_bound; lia).
  assert (Dn : N = 2 * w * (N / (2 * w)) + M) by (apply Z.div_mod; lia).
  set (B := M / w) in *. set (M' := M mod w) in *.
  assert (DM : M = w * B + M') by (apply Z.div_mod; lia).
  assert (BM' : 0 <= M' < w) by (apply Z.mod_pos_bound; lia).
  assert (BB : 0 <= B <= 1) by (split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  (* what the program reads of [l] *)
  assert (Top : P (PrimInt63.lsr l 62%uint63) = B).
  { rewrite P_shr62, El, <- Wbase. rewrite (Z.mul_comm w e). rewrite Z.mul_comm. rewrite Z.div_mul_cancel_l by lia. reflexivity. }
  assert (Nw : N / w = 2 * (N / (2 * w)) + B).
  { symmetry. apply (Z.div_unique_pos _ _ _ M'); [lia |]. rewrite Dn at 1. rewrite DM. ring. }
  assert (Nm : N mod w = M').
  { symmetry. apply (Z.mod_unique_pos _ _ (2 * (N / (2 * w)) + B)); [lia |]. rewrite Dn at 1. rewrite DM. ring. }
  assert (Sl : P (PrimInt63.lsl l 1%uint63) = (N mod w) * (2 * e)).
  { rewrite P_shl1, El, Nm, DM.
    replace (2 * ((w * B + M') * e)) with (M' * (2 * e) + B * 2 * (w * e)) by ring. rewrite Wbase.
    replace (B * 2 * 4611686018427387904) with (B * 9223372036854775808) by ring. rewrite Z.mod_add by lia.
    apply Z.mod_small. split; [apply Z.mul_nonneg_nonneg; lia |].
    apply (Z.lt_le_trans _ (w * (2 * e))); [apply Z.mul_lt_mono_pos_r; lia | nia]. }
  set (v := 2 * P r + B) in *.
  assert (Nmod : P n = v mod 9223372036854775808).
  { unfold n. rewrite P_add, P_shl1, Top. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
  assert (Qv : P (PrimInt63.lsl q 1%uint63) = 2 * P q).
  { rewrite P_shl1. apply Z.mod_small. assert (e <= 4611686018427387904) by nia. lia. }
  assert (Qv1 : P (PrimInt63.add (PrimInt63.lsl q 1%uint63) 1%uint63) = 2 * P q + 1).
  { rewrite P_add, Qv. change (P 1%uint63) with 1. apply Z.mod_small. assert (e <= 4611686018427387904) by nia. lia. }
  assert (Else : P (PrimInt63.sub n c) = v - P c -> P r' = v - P c -> True) by auto.
  assert (Sv : P c <= v -> P (PrimInt63.sub n c) = v - P c).
  { intros Ge. rewrite P_sub, Nmod. rewrite Zminus_mod_idemp_l. apply Z.mod_small. lia. }
  unfold q', r'.
  destruct (PrimInt63.eqb (PrimInt63.lsr r 62%uint63) 0%uint63) eqn:T.
  - apply eqb0_true in T. rewrite P_shr62 in T.
    assert (Rs : P r < 4611686018427387904) by (apply Z.div_small_iff in T; lia).
    assert (Pn : P n = v) by (rewrite Nmod; apply Z.mod_small; lia).
    cbn [andb]. destruct (PrimInt63.ltb n c) eqn:Lt.
    + apply P_ltb in Lt. rewrite Qv. repeat split; try lia.
    + assert (Ge : P c <= v).
      { destruct (Z_lt_le_dec v (P c)) as [L|L]; [|exact L]. exfalso. assert (X : PrimInt63.ltb n c = true) by (apply P_ltb; lia). congruence. }
      rewrite Qv1, (Sv Ge). repeat split; try lia.
  - apply eqb0_false in T. rewrite P_shr62 in T.
    assert (Rs : 4611686018427387904 <= P r) by (destruct (Z_lt_le_dec (P r) 4611686018427387904) as [L|L]; [exfalso; apply T; apply Z.div_small; lia | exact L]).
    cbn [andb]. rewrite Qv1, Sv by lia. repeat split; try lia.
Qed.

Lemma d21_go : forall k (c q r l : int) (N : Z), (Nat.le k 63) -> 0 <= N -> P r < P c ->
  P q < 2 ^ (63 - Z.of_nat k) -> N / 2 ^ Z.of_nat k = P q * P c + P r -> P l = (N mod 2 ^ Z.of_nat k) * 2 ^ (63 - Z.of_nat k) ->
  P (fst (kq_d21_go k c q r l)) * P c + P (snd (kq_d21_go k c q r l)) = N /\ P (snd (kq_d21_go k c q r l)) < P c.
Proof.
  induction k as [|k IH]; intros c q r l N Hk HN Rc Qe EHi El.
  - cbn [kq_d21_go fst snd]. change (Z.of_nat 0) with 0 in *. change (2 ^ 0) with 1 in EHi. rewrite Z.div_1_r in EHi. split; lia.
  - rewrite Nat2Z.inj_succ in *. unfold Z.succ in *.
    set (K := Z.of_nat k) in *. assert (BK : 0 <= K <= 62) by (unfold K; lia).
    set (w := 2 ^ K). set (e := 2 ^ (63 - (K + 1))).
    assert (Pw : 0 < w) by (apply Z.pow_pos_nonneg; lia).
    assert (Pe : 0 < e) by (apply Z.pow_pos_nonneg; lia).
    assert (Wb : w * e = 4611686018427387904).
    { unfold w, e. rewrite <- Z.pow_add_r by lia. replace (K + (63 - (K + 1))) with 62 by lia. reflexivity. }
    assert (Tw : 2 ^ (K + 1) = 2 * w) by (rewrite Z.pow_add_r by lia; unfold w; change (2 ^ 1) with 2; ring).
    assert (Te : 2 ^ (63 - K) = 2 * e).
    { unfold e. replace (63 - K) with (63 - (K + 1) + 1) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. ring. }
    rewrite Tw in EHi, El.
    fold e in Qe, El.
    pose proof (d21_round c q r l 0 N w e Pw Pe Wb HN Rc Qe EHi El) as R. cbv zeta in R.
    destruct R as (R1 & R2 & R3 & R4).
    cbn [kq_d21_go].
    destruct (andb (PrimInt63.eqb (PrimInt63.lsr r 62%uint63) 0%uint63)
                   (PrimInt63.ltb (PrimInt63.add (PrimInt63.lsl r 1%uint63) (PrimInt63.lsr l 62%uint63)) c)) eqn:C.
    + apply IH with (N := N); try assumption; try lia. rewrite Te. exact R4.
    + apply IH with (N := N); try assumption; try lia. rewrite Te. exact R4.
Qed.

Lemma kq_d21_eq : forall a b c, PrimInt63.ltb a c = true -> PrimInt63.diveucl_21 a b c = kq_d21 a b c.
Proof.
  intros a b c Lt. apply P_ltb in Lt.
  pose proof (P_bound a) as Ba. pose proof (P_bound b) as Bb. pose proof (P_bound c) as Bc.
  set (N := P a * 9223372036854775808 + P b).
  assert (HN : 0 <= N) by (unfold N; lia).
  assert (E1 : N / 9223372036854775808 = P a).
  { symmetry. apply (Z.div_unique_pos _ _ _ (P b)); [lia | unfold N; ring]. }
  assert (E2 : N mod 9223372036854775808 = P b).
  { symmetry. apply (Z.mod_unique_pos _ _ (P a)); [lia | unfold N; ring]. }
  pose proof (d21_go 63 c 0%uint63 a b N ltac:(lia) HN Lt) as G.
  change (Z.of_nat 63) with 63 in G. change (2 ^ (63 - 63)) with 1 in G. change (2 ^ 63) with 9223372036854775808 in G. change (P 0%uint63) with 0 in G.
  destruct (G ltac:(lia) ltac:(rewrite E1; ring) ltac:(rewrite E2; ring)) as (G1 & G2).
  rewrite kq_d21_go_eq. pose proof (diveucl_21_spec a b c) as S.
  destruct (PrimInt63.diveucl_21 a b c) as [q r]. destruct (kq_d21_go 63 c 0%uint63 a b) as [q' r']. cbn [fst snd] in G1, G2.
  pose proof (Z_div_mod (P a * wB + P b) (P c) ltac:(lia)) as D.
  destruct (Z.div_eucl (P a * wB + P b) (P c)) as [q1 r1].
  destruct (S Lt) as [S1 S2]. destruct D as [D1 D2].
  pose proof (P_bound r') as Br'. pose proof (P_bound q') as Bq'.
  change wB with 9223372036854775808 in D1.
  assert (U : q1 = P q' /\ r1 = P r').
  { apply (Z.div_mod_unique (P c)); [left; lia | left; lia |]. rewrite <- D1. fold N. rewrite <- G1. ring. }
  destruct U as [U1 U2]. f_equal; apply to_Z_inj; congruence.
Qed.

Lemma kq_d21_le : forall a b c, PrimInt63.leb c a = false -> PrimInt63.diveucl_21 a b c = kq_d21 a b c.
Proof.
  intros a b c L. apply kq_d21_eq. apply P_ltb.
  assert (N : ~ (P c <= P a)) by (intros H; apply leb_spec in H; change (PrimInt63.leb c a) with (c <=? a)%uint63 in L; rewrite L in H; discriminate). lia.
Qed.

(** the pair [mulc] gives *)
Lemma kq_mulc_def : forall x y : int, PrimInt63.mulc x y = (kq_mh x y, PrimInt63.mul x y).
Proof.
  intros x y. rewrite <- kq_mulhi_eq. destruct (PrimInt63.mulc x y) as [h l] eqn:E. cbn [fst]. f_equal.
  apply to_Z_inj. change (P (PrimInt63.mul x y)) with (P (x * y)%uint63). rewrite mul_spec.
  pose proof (mulc_spec x y) as S. rewrite E in S. cbn [fst snd] in S. rewrite S.
  pose proof (to_Z_bounded l) as [L1 L2].
  rewrite Z.add_comm, Z_mod_plus_full. rewrite Z.mod_small; [reflexivity | lia].
Qed.
