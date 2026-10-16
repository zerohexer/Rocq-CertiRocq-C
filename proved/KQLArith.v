(** The 63-bit operations against their 64-bit Clight counterparts. *)

From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Cop Clight.
From KQC Require Import KQL KQLGen.
Import ListNotations.

Local Open Scope Z_scope.

Definition enc (v : i63) : val := Vlong (Int64.repr (to_Z v)).

Lemma phi_range : forall v : i63, 0 <= to_Z v < 2 ^ 63.
Proof. intros v. pose proof (to_Z_bounded v). exact H. Qed.

Lemma mod64 : Int64.modulus = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma uns_phi : forall v : i63, Int64.unsigned (Int64.repr (to_Z v)) = to_Z v.
Proof.
  intros v. apply Int64.unsigned_repr. pose proof (phi_range v).
  unfold Int64.max_unsigned. rewrite mod64. lia.
Qed.

Lemma uns_small : forall z, 0 <= z < 2 ^ 63 -> Int64.unsigned (Int64.repr z) = z.
Proof.
  intros z H. apply Int64.unsigned_repr. unfold Int64.max_unsigned. rewrite mod64. lia.
Qed.

Lemma mask_repr : forall z,
  Int64.and (Int64.repr z) (Int64.repr mask63) = Int64.repr (z mod 2 ^ 63).
Proof.
  intros z. unfold Int64.and. rewrite Int64.unsigned_repr_eq, mod64.
  rewrite (uns_small mask63) by (unfold mask63; lia).
  replace mask63 with (Z.ones 63) by reflexivity.
  rewrite Z.land_ones by lia. f_equal.
  symmetry. apply Zmod_div_mod; try lia. exists 2. reflexivity.
Qed.

Lemma wB63 : wB = 2 ^ 63.
Proof. reflexivity. Qed.

Lemma enc_inj_eq : forall a b : i63,
  Int64.eq (Int64.repr (to_Z a)) (Int64.repr (to_Z b)) = PrimInt63.eqb a b.
Proof.
  intros a b. unfold Int64.eq. rewrite !uns_phi.
  destruct (zeq (to_Z a) (to_Z b)) as [E|E].
  - symmetry. apply Uint63.eqb_spec. rewrite <- (of_to_Z a), <- (of_to_Z b), E. reflexivity.
  - symmetry. destruct (PrimInt63.eqb a b) eqn:Q; auto.
    apply Uint63.eqb_spec in Q. subst. congruence.
Qed.

Lemma enc_ltu : forall a b : i63,
  Int64.ltu (Int64.repr (to_Z a)) (Int64.repr (to_Z b)) = PrimInt63.ltb a b.
Proof.
  intros a b. unfold Int64.ltu. rewrite !uns_phi.
  destruct (zlt (to_Z a) (to_Z b)) as [L|L].
  - symmetry. apply Uint63Axioms.ltb_spec. exact L.
  - symmetry. destruct (PrimInt63.ltb a b) eqn:Q; auto. apply Uint63Axioms.ltb_spec in Q. lia.
Qed.

Lemma enc_leu : forall a b : i63,
  negb (Int64.ltu (Int64.repr (to_Z b)) (Int64.repr (to_Z a))) = PrimInt63.leb a b.
Proof.
  intros a b. unfold Int64.ltu. rewrite !uns_phi.
  destruct (zlt (to_Z b) (to_Z a)) as [L|L]; simpl.
  - symmetry. destruct (PrimInt63.leb a b) eqn:Q; auto. apply Uint63Axioms.leb_spec in Q. lia.
  - symmetry. apply Uint63Axioms.leb_spec. lia.
Qed.

(** Each operation, as the Clight value computed by its translation. *)

Lemma add_enc : forall a b : i63,
  Int64.and (Int64.add (Int64.repr (to_Z a)) (Int64.repr (to_Z b))) (Int64.repr mask63)
  = Int64.repr (to_Z (PrimInt63.add a b)).
Proof.
  intros. rewrite Int64.add_unsigned, !uns_phi, mask_repr, add_spec. reflexivity.
Qed.

Lemma sub_enc : forall a b : i63,
  Int64.and (Int64.sub (Int64.repr (to_Z a)) (Int64.repr (to_Z b))) (Int64.repr mask63)
  = Int64.repr (to_Z (PrimInt63.sub a b)).
Proof.
  intros. unfold Int64.sub. rewrite !uns_phi, mask_repr, sub_spec. reflexivity.
Qed.

Lemma mul_enc : forall a b : i63,
  Int64.and (Int64.mul (Int64.repr (to_Z a)) (Int64.repr (to_Z b))) (Int64.repr mask63)
  = Int64.repr (to_Z (PrimInt63.mul a b)).
Proof.
  intros. unfold Int64.mul. rewrite !uns_phi, mask_repr, mul_spec. reflexivity.
Qed.

Lemma land_enc : forall a b : i63,
  Int64.and (Int64.repr (to_Z a)) (Int64.repr (to_Z b)) = Int64.repr (to_Z (PrimInt63.land a b)).
Proof. intros. unfold Int64.and. rewrite !uns_phi, land_spec'. reflexivity. Qed.

Lemma lor_enc : forall a b : i63,
  Int64.or (Int64.repr (to_Z a)) (Int64.repr (to_Z b)) = Int64.repr (to_Z (PrimInt63.lor a b)).
Proof. intros. unfold Int64.or. rewrite !uns_phi, lor_spec'. reflexivity. Qed.

Lemma lxor_enc : forall a b : i63,
  Int64.xor (Int64.repr (to_Z a)) (Int64.repr (to_Z b)) = Int64.repr (to_Z (PrimInt63.lxor a b)).
Proof. intros. unfold Int64.xor. rewrite !uns_phi, lxor_spec'. reflexivity. Qed.

Lemma div_enc : forall a b : i63,
  Int64.divu (Int64.repr (to_Z a)) (Int64.repr (to_Z b)) = Int64.repr (to_Z (PrimInt63.div a b)).
Proof. intros. unfold Int64.divu. rewrite !uns_phi, div_spec. reflexivity. Qed.

Lemma div0_enc : forall a b : i63, PrimInt63.eqb b 0 = true ->
  Int64.repr 0 = Int64.repr (to_Z (PrimInt63.div a b)).
Proof.
  intros a b H. apply Uint63.eqb_spec in H. subst b. rewrite div_spec. simpl.
  rewrite Zdiv_0_r. reflexivity.
Qed.

Lemma mod_enc : forall a b : i63,
  Int64.modu (Int64.repr (to_Z a)) (Int64.repr (to_Z b)) = Int64.repr (to_Z (PrimInt63.mod a b)).
Proof. intros. unfold Int64.modu. rewrite !uns_phi, mod_spec. reflexivity. Qed.

Lemma mod0_enc : forall a b : i63, PrimInt63.eqb b 0 = true ->
  Int64.repr (to_Z a) = Int64.repr (to_Z (PrimInt63.mod a b)).
Proof.
  intros a b H. apply Uint63.eqb_spec in H. subst b. rewrite mod_spec. simpl.
  rewrite Zmod_0_r. reflexivity.
Qed.

Lemma c63_phi : to_Z 63%uint63 = 63.
Proof. reflexivity. Qed.

Lemma lsl_enc : forall a b : i63, to_Z b < 63 ->
  Int64.and (Int64.shl (Int64.repr (to_Z a)) (Int64.repr (to_Z b))) (Int64.repr mask63)
  = Int64.repr (to_Z (PrimInt63.lsl a b)).
Proof.
  intros a b H. unfold Int64.shl. rewrite !uns_phi, mask_repr, lsl_spec.
  rewrite Z.shiftl_mul_pow2 by (pose proof (phi_range b); lia). reflexivity.
Qed.

Lemma lsl_big : forall a b : i63, 63 <= to_Z b ->
  Int64.repr 0 = Int64.repr (to_Z (PrimInt63.lsl a b)).
Proof.
  intros a b H. rewrite lsl_spec, wB63. f_equal.
  replace (2 ^ to_Z b) with (2 ^ (to_Z b - 63) * 2 ^ 63)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_assoc, Z_mod_mult. reflexivity.
Qed.

Lemma lsr_enc : forall a b : i63, to_Z b < 63 ->
  Int64.shru (Int64.repr (to_Z a)) (Int64.repr (to_Z b)) = Int64.repr (to_Z (PrimInt63.lsr a b)).
Proof.
  intros a b H. unfold Int64.shru. rewrite !uns_phi, lsr_spec.
  rewrite Z.shiftr_div_pow2 by (pose proof (phi_range b); lia). reflexivity.
Qed.

Lemma lsr_big : forall a b : i63, 63 <= to_Z b ->
  Int64.repr 0 = Int64.repr (to_Z (PrimInt63.lsr a b)).
Proof.
  intros a b H. rewrite lsr_spec. f_equal. symmetry. apply Z.div_small.
  pose proof (phi_range a). split. lia.
  apply Z.lt_le_trans with (2 ^ 63). lia. apply Z.pow_le_mono_r; lia.
Qed.

Lemma ltu_63 : forall b : i63,
  Int64.ltu (Int64.repr (to_Z b)) (Int64.repr 63) = (to_Z b <? 63).
Proof.
  intros b. unfold Int64.ltu. rewrite uns_phi, (uns_small 63) by lia.
  destruct (zlt (to_Z b) 63); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma ltu_iword : forall b : i63, to_Z b < 63 ->
  Int64.ltu (Int64.repr (to_Z b)) Int64.iwordsize = true.
Proof.
  intros b H. unfold Int64.ltu. rewrite uns_phi.
  change (Int64.unsigned Int64.iwordsize) with 64. destruct (zlt (to_Z b) 64); auto. lia.
Qed.

Lemma eq_zero : forall b : i63,
  Int64.eq (Int64.repr (to_Z b)) (Int64.repr 0) = PrimInt63.eqb b 0.
Proof. intros. exact (enc_inj_eq b 0%uint63). Qed.
