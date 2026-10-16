(** The kit's signed operations, written with the unsigned ones KQL has.
    A signed number [x] is [φ x] below 2^62 and [φ x - 2^63] from 2^62 on;
    adding 2^62 (mod 2^63) maps the signed order onto the unsigned one. *)

From Stdlib Require Import ZArith Uint63 Sint63 Lia.
Local Open Scope Z_scope.

Notation sZ := Sint63.to_Z.

Definition m62 : PrimInt63.int := 4611686018427387904%uint63.
Definition max63 : PrimInt63.int := 9223372036854775807%uint63.

Lemma m62_phi : φ m62%uint63 = 2 ^ 62.
Proof. reflexivity. Qed.

Lemma wB63 : wB = 2 ^ 63.
Proof. reflexivity. Qed.

Lemma sZ_cases : forall x, sZ x = if φ x%uint63 <? 2 ^ 62 then φ x%uint63 else φ x%uint63 - 2 ^ 63.
Proof.
  intros x. pose proof (Uint63.to_Z_bounded x) as B. rewrite wB63 in B.
  unfold Sint63Axioms.to_Z.
  destruct (PrimInt63.ltb x Sint63Axioms.min_int) eqn:L.
  - apply Uint63.ltb_spec in L. change (φ Sint63Axioms.min_int%uint63) with (2 ^ 62) in L.
    destruct (Z.ltb_spec (φ x%uint63) (2 ^ 62)); lia.
  - assert (L' : ~ φ x%uint63 < 2 ^ 62).
    { intro C. assert (PrimInt63.ltb x Sint63Axioms.min_int = true) by (apply Uint63.ltb_spec; exact C).
      congruence. }
    destruct (Z.ltb_spec (φ x%uint63) (2 ^ 62)); [lia|].
    rewrite Uint63.sub_spec. change (φ 0%uint63) with 0. rewrite wB63.
    rewrite Z_mod_nz_opp_full.
    + rewrite Z.mod_small by lia. lia.
    + rewrite Z.mod_small by lia. lia.
Qed.

Lemma shift_phi : forall x, φ (PrimInt63.add x m62)%uint63 = sZ x + 2 ^ 62.
Proof.
  intros x. rewrite Uint63.add_spec, m62_phi, wB63, sZ_cases.
  pose proof (Uint63.to_Z_bounded x) as B. rewrite wB63 in B.
  destruct (Z.ltb_spec (φ x%uint63) (2 ^ 62)).
  - apply Z.mod_small. lia.
  - replace (φ x%uint63 + 2 ^ 62) with ((φ x%uint63 - 2 ^ 63 + 2 ^ 62) + 1 * 2 ^ 63) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma sltb_iff : forall x y, PrimInt63.ltsb x y = true <-> sZ x < sZ y.
Proof. intros. rewrite Sint63Axioms.ltb_spec. apply Z.compare_lt_iff. Qed.

Lemma sleb_iff : forall x y, PrimInt63.lesb x y = true <-> sZ x <= sZ y.
Proof. intros. rewrite Sint63Axioms.leb_spec. apply Z.compare_le_iff. Qed.

Lemma ltsb_via : forall x y,
  PrimInt63.ltsb x y = PrimInt63.ltb (PrimInt63.add x m62) (PrimInt63.add y m62).
Proof.
  intros x y. destruct (PrimInt63.ltsb x y) eqn:E; symmetry.
  - apply sltb_iff in E. apply Uint63.ltb_spec. rewrite !shift_phi. lia.
  - destruct (PrimInt63.ltb (PrimInt63.add x m62) (PrimInt63.add y m62)) eqn:F; auto.
    apply Uint63.ltb_spec in F. rewrite !shift_phi in F.
    assert (PrimInt63.ltsb x y = true) by (apply sltb_iff; lia). congruence.
Qed.

Lemma lesb_via : forall x y,
  PrimInt63.lesb x y = PrimInt63.leb (PrimInt63.add x m62) (PrimInt63.add y m62).
Proof.
  intros x y. destruct (PrimInt63.lesb x y) eqn:E; symmetry.
  - apply sleb_iff in E. apply Uint63.leb_spec. rewrite !shift_phi. lia.
  - destruct (PrimInt63.leb (PrimInt63.add x m62) (PrimInt63.add y m62)) eqn:F; auto.
    apply Uint63.leb_spec in F. rewrite !shift_phi in F.
    assert (PrimInt63.lesb x y = true) by (apply sleb_iff; lia). congruence.
Qed.

Lemma phi_of_sZ : forall x, φ x%uint63 = sZ x mod 2 ^ 63.
Proof. intros x. rewrite <- Sint63.to_Z_mod_Uint63to_Z. reflexivity. Qed.

(** [asr x p]: for a shift below 63 two logical shifts and a subtraction;
    otherwise all ones or zero by the sign, and zero for a negative shift. *)
Definition asr_kq (x p : PrimInt63.int) : PrimInt63.int :=
  let u := PrimInt63.add x m62 in
  if PrimInt63.ltb p 63%uint63 then PrimInt63.sub (PrimInt63.lsr u p) (PrimInt63.lsr m62 p)
  else if PrimInt63.ltb p m62 then (if PrimInt63.ltb u m62 then max63 else 0%uint63)
  else 0%uint63.

Lemma asr_via : forall x p, PrimInt63.asr x p = asr_kq x p.
Proof.
  intros x p. apply Uint63.to_Z_inj. rewrite phi_of_sZ, Sint63Axioms.asr_spec.
  pose proof (Uint63.to_Z_bounded p) as Bp. rewrite wB63 in Bp.
  pose proof (Uint63.to_Z_bounded x) as Bx0. rewrite wB63 in Bx0.
  assert (Bx : - 2 ^ 62 <= sZ x < 2 ^ 62)
    by (rewrite sZ_cases; destruct (Z.ltb_spec (φ x%uint63) (2 ^ 62)); lia).
  unfold asr_kq.
  destruct (PrimInt63.ltb p 63%uint63) eqn:L1.
  - apply Uint63.ltb_spec in L1. change (φ 63%uint63) with 63 in L1.
    assert (sZ p = φ p%uint63) by (rewrite sZ_cases; destruct (Z.ltb_spec (φ p%uint63) (2 ^ 62)); lia).
    rewrite H, Uint63.sub_spec, !Uint63.lsr_spec, shift_phi, m62_phi, wB63.
    replace (2 ^ 62) with (2 ^ (62 - φ p%uint63) * 2 ^ φ p%uint63) at 1
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Z.div_add by (apply Z.pow_nonzero; lia).
    replace (2 ^ 62) with (2 ^ (62 - φ p%uint63) * 2 ^ φ p%uint63)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
    f_equal. lia.
  - apply Z.nlt_ge in L1 || (assert (~ φ p%uint63 < 63) by
      (intro C; assert (PrimInt63.ltb p 63%uint63 = true) by (apply Uint63.ltb_spec; exact C); congruence)).
    destruct (PrimInt63.ltb p m62) eqn:L2.
    + apply Uint63.ltb_spec in L2. rewrite m62_phi in L2.
      assert (Hp : sZ p = φ p%uint63) by (rewrite sZ_cases; destruct (Z.ltb_spec (φ p%uint63) (2 ^ 62)); lia).
      assert (Hp63 : 63 <= φ p%uint63) by (destruct (Z.ltb_spec (φ p%uint63) 63); [|lia];
        assert (PrimInt63.ltb p 63%uint63 = true) by (apply Uint63.ltb_spec; exact H0); congruence).
      rewrite Hp.
      assert (Big : 2 ^ 63 <= 2 ^ φ p%uint63) by (apply Z.pow_le_mono_r; lia).
      destruct (PrimInt63.ltb (PrimInt63.add x m62) m62) eqn:L3.
      * apply Uint63.ltb_spec in L3. rewrite shift_phi, m62_phi in L3.
        replace (sZ x / 2 ^ φ p%uint63) with (-1).
        -- reflexivity.
        -- apply Z.div_unique with (r := sZ x + 2 ^ φ p%uint63); [left; lia | lia].
      * assert (H4 : ~ φ (PrimInt63.add x m62)%uint63 < φ m62%uint63).
        { intro C. assert (PrimInt63.ltb (PrimInt63.add x m62) m62 = true) by (apply Uint63.ltb_spec; exact C).
          congruence. }
        rewrite shift_phi, m62_phi in H4.
        rewrite Z.div_small by lia. reflexivity.
    + assert (H5 : ~ φ p%uint63 < φ m62%uint63).
      { intro C. assert (PrimInt63.ltb p m62 = true) by (apply Uint63.ltb_spec; exact C). congruence. }
      rewrite m62_phi in H5.
      assert (sZ p < 0) by (rewrite sZ_cases; destruct (Z.ltb_spec (φ p%uint63) (2 ^ 62)); lia).
      rewrite Z.pow_neg_r by lia. rewrite Zdiv_0_r. reflexivity.
Qed.
