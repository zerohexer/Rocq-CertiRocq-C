(** KQTArith: the 63-bit numbers as the kit holds them -- the word [2n + 1] -- and what C does to such words.

    A number [v] is the 64-bit word [tg v = 2 * phi v + 1] (phi: the unsigned value).  Then
      - [+] is [a + b - 1], [-] is [a - b + 1]: no mask, the high bit just falls off;
      - the unsigned order of the numbers is the unsigned order of the words, the signed order the signed order;
      - [land], [lor] are the same on the words, [lxor] is [(a ^ b) | 1];
      - a shift amount, a divisor are [b >> 1].  *)

From Stdlib Require Import ZArith List Uint63 Lia Zquot.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Cop Clight.
From KQC Require Import KQL KQLSigned.
Import ListNotations.

Local Open Scope Z_scope.

Definition tg (v : i63) : Int64.int := Int64.repr (2 * to_Z v + 1).
Definition enc (v : i63) : val := Vlong (tg v).

Lemma uinj : forall a b : Int64.int, Int64.unsigned a = Int64.unsigned b -> a = b.
Proof. intros a b H. rewrite <- (Int64.repr_unsigned a), <- (Int64.repr_unsigned b), H. reflexivity. Qed.

Lemma mod64 : Int64.modulus = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma uns_repr : forall z, Int64.unsigned (Int64.repr z) = z mod 2 ^ 64.
Proof. intros z. rewrite Int64.unsigned_repr_eq, mod64. reflexivity. Qed.

Lemma uns_tg : forall v, Int64.unsigned (tg v) = 2 * to_Z v + 1.
Proof.
  intros v. pose proof (phi_range v). unfold tg. rewrite uns_repr. apply Z.mod_small. lia.
Qed.

Lemma uns_small : forall z, 0 <= z < 2 ^ 64 -> Int64.unsigned (Int64.repr z) = z.
Proof. intros z H. rewrite uns_repr. apply Z.mod_small. lia. Qed.

Lemma tg_inj : forall a b, tg a = tg b -> a = b.
Proof.
  intros a b H. apply (f_equal Int64.unsigned) in H. rewrite !uns_tg in H.
  apply to_Z_inj. lia.
Qed.

(** ** a word is determined by its residue *)

Lemma dbl_mod : forall z, (2 * z + 1) mod 2 ^ 64 = 2 * (z mod 2 ^ 63) + 1.
Proof.
  intros z. symmetry. apply Z.mod_unique_pos with (q := z / 2 ^ 63).
  - pose proof (Z.mod_pos_bound z (2 ^ 63) ltac:(lia)). lia.
  - pose proof (Z.div_mod z (2 ^ 63) ltac:(lia)). lia.
Qed.

(** [X] is the word of a number whose value is [z] modulo 2^63 *)
Lemma tg_of : forall (X : Int64.int) (w : i63) z,
  Int64.unsigned X = (2 * z + 1) mod 2 ^ 64 -> z mod 2 ^ 63 = to_Z w -> X = tg w.
Proof.
  intros X w z H E. apply uinj. rewrite H, dbl_mod, E, uns_tg. reflexivity.
Qed.

(** the unsigned value of the C operations, as Z arithmetic modulo 2^64 *)
Lemma uadd : forall x y, Int64.unsigned (Int64.add x y) = (Int64.unsigned x + Int64.unsigned y) mod 2 ^ 64.
Proof. intros. unfold Int64.add. apply uns_repr. Qed.
Lemma usub : forall x y, Int64.unsigned (Int64.sub x y) = (Int64.unsigned x - Int64.unsigned y) mod 2 ^ 64.
Proof. intros. unfold Int64.sub. apply uns_repr. Qed.
Lemma umul : forall x y, Int64.unsigned (Int64.mul x y) = (Int64.unsigned x * Int64.unsigned y) mod 2 ^ 64.
Proof. intros. unfold Int64.mul. apply uns_repr. Qed.
Lemma uone : Int64.unsigned Int64.one = 1.
Proof. reflexivity. Qed.

Ltac mods := repeat (rewrite ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r,
                         ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r).

Lemma add_t : forall a b : i63,
  Int64.sub (Int64.add (tg a) (tg b)) Int64.one = tg (PrimInt63.add a b).
Proof.
  intros a b. eapply tg_of with (z := to_Z a + to_Z b).
  - rewrite usub, uadd, !uns_tg, uone. mods. f_equal. lia.
  - rewrite Uint63.add_spec. reflexivity.
Qed.

Lemma sub_t : forall a b : i63,
  Int64.add (Int64.sub (tg a) (tg b)) Int64.one = tg (PrimInt63.sub a b).
Proof.
  intros a b. eapply tg_of with (z := to_Z a - to_Z b).
  - rewrite uadd, usub, !uns_tg, uone. mods. f_equal. lia.
  - rewrite Uint63.sub_spec. reflexivity.
Qed.

Lemma shr1_t : forall a : i63, Int64.shru (tg a) Int64.one = Int64.repr (to_Z a).
Proof.
  intros a. pose proof (phi_range a). unfold Int64.shru. rewrite uns_tg, uone.
  f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  symmetry. apply Z.div_unique with (r := 1); [left; lia | lia].
Qed.

Lemma uns_phi : forall a : i63, Int64.unsigned (Int64.repr (to_Z a)) = to_Z a.
Proof. intros a. pose proof (phi_range a). apply uns_small. lia. Qed.

Lemma mul_t : forall a b : i63,
  Int64.add (Int64.mul (Int64.sub (tg a) Int64.one) (Int64.shru (tg b) Int64.one)) Int64.one
  = tg (PrimInt63.mul a b).
Proof.
  intros a b. rewrite shr1_t. eapply tg_of with (z := to_Z a * to_Z b).
  - pose proof (phi_range a). rewrite uadd, umul, usub, uns_phi, uns_tg, uone. mods.
    replace (2 * to_Z a + 1 - 1) with (2 * to_Z a) by lia.
    rewrite (Z.mod_small (2 * to_Z a)) by lia. f_equal. ring.
  - rewrite Uint63.mul_spec. reflexivity.
Qed.

(** ** bit operations *)

Lemma land_odd : forall x y, 0 <= x -> 0 <= y -> Z.land (2 * x + 1) (2 * y + 1) = 2 * Z.land x y + 1.
Proof.
  intros x y Hx Hy. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.eq_dec n 0) as [E | E].
  - subst. rewrite !Z.testbit_odd_0. reflexivity.
  - assert (Hp : n = Z.succ (Z.pred n)) by lia. rewrite Hp.
    rewrite !Z.testbit_odd_succ by lia. rewrite Z.land_spec. reflexivity.
Qed.

Lemma lor_odd : forall x y, 0 <= x -> 0 <= y -> Z.lor (2 * x + 1) (2 * y + 1) = 2 * Z.lor x y + 1.
Proof.
  intros x y Hx Hy. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
  destruct (Z.eq_dec n 0) as [E | E].
  - subst. rewrite !Z.testbit_odd_0. reflexivity.
  - assert (Hp : n = Z.succ (Z.pred n)) by lia. rewrite Hp.
    rewrite !Z.testbit_odd_succ by lia. rewrite Z.lor_spec. reflexivity.
Qed.

Lemma lxor_odd : forall x y, 0 <= x -> 0 <= y -> Z.lxor (2 * x + 1) (2 * y + 1) = 2 * Z.lxor x y.
Proof.
  intros x y Hx Hy. apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec.
  destruct (Z.eq_dec n 0) as [E | E].
  - subst. rewrite !Z.testbit_odd_0. rewrite Z.testbit_even_0. reflexivity.
  - assert (Hp : n = Z.succ (Z.pred n)) by lia. rewrite Hp.
    rewrite !Z.testbit_odd_succ by lia. rewrite Z.testbit_even_succ by lia. rewrite Z.lxor_spec. reflexivity.
Qed.

Lemma uand : forall x y, Int64.unsigned (Int64.and x y) = (Z.land (Int64.unsigned x) (Int64.unsigned y)) mod 2 ^ 64.
Proof. intros. unfold Int64.and. apply uns_repr. Qed.
Lemma uor : forall x y, Int64.unsigned (Int64.or x y) = (Z.lor (Int64.unsigned x) (Int64.unsigned y)) mod 2 ^ 64.
Proof. intros. unfold Int64.or. apply uns_repr. Qed.
Lemma uxor : forall x y, Int64.unsigned (Int64.xor x y) = (Z.lxor (Int64.unsigned x) (Int64.unsigned y)) mod 2 ^ 64.
Proof. intros. unfold Int64.xor. apply uns_repr. Qed.

Lemma phi_lt : forall w : i63, to_Z w mod 2 ^ 63 = to_Z w.
Proof. intros w. pose proof (phi_range w). apply Z.mod_small. lia. Qed.

Lemma land_t : forall a b : i63, Int64.and (tg a) (tg b) = tg (PrimInt63.land a b).
Proof.
  intros a b. pose proof (phi_range a). pose proof (phi_range b).
  eapply tg_of with (z := Z.land (to_Z a) (to_Z b)).
  - rewrite uand, !uns_tg, land_odd by lia. reflexivity.
  - rewrite <- Uint63.land_spec'. apply phi_lt.
Qed.

Lemma lor_t : forall a b : i63, Int64.or (tg a) (tg b) = tg (PrimInt63.lor a b).
Proof.
  intros a b. pose proof (phi_range a). pose proof (phi_range b).
  eapply tg_of with (z := Z.lor (to_Z a) (to_Z b)).
  - rewrite uor, !uns_tg, lor_odd by lia. reflexivity.
  - rewrite <- Uint63.lor_spec'. apply phi_lt.
Qed.

Lemma lxor_t : forall a b : i63, Int64.or (Int64.xor (tg a) (tg b)) Int64.one = tg (PrimInt63.lxor a b).
Proof.
  intros a b. pose proof (phi_range a). pose proof (phi_range b).
  eapply tg_of with (z := Z.lxor (to_Z a) (to_Z b)).
  - rewrite uor, uxor, !uns_tg, uone, lxor_odd by lia.
    (* (2 * (a ^ b) mod 2^64) | 1 *)
    assert (Hx : 0 <= Z.lxor (to_Z a) (to_Z b) < 2 ^ 63).
    { rewrite <- Uint63.lxor_spec'. apply phi_range. }
    rewrite (Z.mod_small (2 * Z.lxor (to_Z a) (to_Z b))) by lia.
    f_equal. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
    destruct (Z.eq_dec n 0) as [E | E].
    + subst. rewrite Z.testbit_even_0, Z.testbit_odd_0. reflexivity.
    + assert (Hp : n = Z.succ (Z.pred n)) by lia. rewrite Hp.
      rewrite Z.testbit_odd_succ by lia. rewrite Z.testbit_even_succ by lia.
      replace (Z.testbit 1 (Z.succ (Z.pred n))) with false.
      * now rewrite orb_false_r.
      * symmetry. rewrite <- Hp. apply Z.bits_above_log2; [lia | change (Z.log2 1) with 0; lia].
  - rewrite <- Uint63.lxor_spec'. apply phi_lt.
Qed.

(** ** comparisons *)

Lemma sgn_tg : forall a : i63, Int64.signed (tg a) = 2 * Sint63.to_Z a + 1.
Proof.
  intros a. pose proof (phi_range a). unfold Int64.signed. rewrite uns_tg.
  rewrite (sZ_cases a). change Int64.half_modulus with (2 ^ 63).
  destruct (Z.ltb_spec (to_Z a) (2 ^ 62)) as [L | L].
  - destruct (zlt (2 * to_Z a + 1) (2 ^ 63)); [reflexivity | lia].
  - destruct (zlt (2 * to_Z a + 1) (2 ^ 63)); [lia | ]. rewrite mod64. lia.
Qed.

Lemma eq_t : forall a b : i63, Int64.eq (tg a) (tg b) = PrimInt63.eqb a b.
Proof.
  intros a b. unfold Int64.eq. rewrite !uns_tg.
  destruct (zeq (2 * to_Z a + 1) (2 * to_Z b + 1)) as [E | E].
  - symmetry. apply Uint63.eqb_spec. apply to_Z_inj. lia.
  - symmetry. destruct (PrimInt63.eqb a b) eqn:Q; auto. apply Uint63.eqb_spec in Q. subst. congruence.
Qed.

Lemma ltu_t : forall a b : i63, Int64.ltu (tg a) (tg b) = PrimInt63.ltb a b.
Proof.
  intros a b. unfold Int64.ltu. rewrite !uns_tg.
  destruct (zlt (2 * to_Z a + 1) (2 * to_Z b + 1)) as [L | L].
  - symmetry. apply Uint63Axioms.ltb_spec. lia.
  - symmetry. destruct (PrimInt63.ltb a b) eqn:Q; auto. apply Uint63Axioms.ltb_spec in Q. lia.
Qed.

Lemma leu_t : forall a b : i63, negb (Int64.ltu (tg b) (tg a)) = PrimInt63.leb a b.
Proof.
  intros a b. unfold Int64.ltu. rewrite !uns_tg.
  destruct (zlt (2 * to_Z b + 1) (2 * to_Z a + 1)) as [L | L]; simpl.
  - symmetry. destruct (PrimInt63.leb a b) eqn:Q; auto. apply Uint63Axioms.leb_spec in Q. lia.
  - symmetry. apply Uint63Axioms.leb_spec. lia.
Qed.

Lemma slt_t : forall a b : i63, Int64.lt (tg a) (tg b) = PrimInt63.ltsb a b.
Proof.
  intros a b. unfold Int64.lt. rewrite !sgn_tg.
  destruct (zlt (2 * Sint63.to_Z a + 1) (2 * Sint63.to_Z b + 1)) as [L | L].
  - symmetry. apply sltb_iff. lia.
  - symmetry. destruct (PrimInt63.ltsb a b) eqn:Q; auto. apply sltb_iff in Q. lia.
Qed.

Lemma sle_t : forall a b : i63, negb (Int64.lt (tg b) (tg a)) = PrimInt63.lesb a b.
Proof.
  intros a b. unfold Int64.lt. rewrite !sgn_tg.
  destruct (zlt (2 * Sint63.to_Z b + 1) (2 * Sint63.to_Z a + 1)) as [L | L]; simpl.
  - symmetry. destruct (PrimInt63.lesb a b) eqn:Q; auto. apply sleb_iff in Q. lia.
  - symmetry. apply sleb_iff. lia.
Qed.

Lemma tg_zero : tg 0%uint63 = Int64.one.
Proof. reflexivity. Qed.

Lemma isone_t : forall b : i63, Int64.eq (tg b) Int64.one = PrimInt63.eqb b 0%uint63.
Proof. intros b. rewrite <- tg_zero. apply eq_t. Qed.

(** ** shifts *)

Lemma lor_even1 : forall q, 0 <= q -> Z.lor (2 * q) 1 = 2 * q + 1.
Proof.
  intros q Hq. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
  destruct (Z.eq_dec n 0) as [E | E].
  - subst. rewrite Z.testbit_even_0, Z.testbit_odd_0. reflexivity.
  - assert (Hp : n = Z.succ (Z.pred n)) by lia. rewrite Hp.
    rewrite Z.testbit_odd_succ by lia. rewrite Z.testbit_even_succ by lia.
    replace (Z.testbit 1 (Z.succ (Z.pred n))) with false.
    + now rewrite orb_false_r.
    + symmetry. rewrite <- Hp. apply Z.bits_above_log2; [lia | change (Z.log2 1) with 0; lia].
Qed.

(** the tagged word of a number [q] below 2^63, from [(q << 1) | 1] *)
Lemma tag_up : forall q : Z, 0 <= q < 2 ^ 63 ->
  Int64.unsigned (Int64.or (Int64.shl (Int64.repr q) Int64.one) Int64.one) = 2 * q + 1.
Proof.
  intros q H. rewrite uor, uone. unfold Int64.shl. rewrite uone.
  rewrite (uns_small q) by lia. rewrite uns_repr. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite Z.mul_comm. rewrite (Z.mod_small (2 * q)) by lia.
  rewrite lor_even1 by lia. apply Z.mod_small. lia.
Qed.

Lemma lsl_t : forall a b : i63, to_Z b < 63 ->
  Int64.add (Int64.shl (Int64.sub (tg a) Int64.one) (Int64.shru (tg b) Int64.one)) Int64.one
  = tg (PrimInt63.lsl a b).
Proof.
  intros a b H. pose proof (phi_range a). pose proof (phi_range b).
  rewrite shr1_t. eapply tg_of with (z := to_Z a * 2 ^ to_Z b).
  - rewrite uadd, !uone. unfold Int64.shl. rewrite usub, uns_tg, uone, uns_phi.
    rewrite uns_repr. rewrite Z.shiftl_mul_pow2 by lia. mods.
    replace (2 * to_Z a + 1 - 1) with (2 * to_Z a) by lia.
    rewrite (Z.mod_small (2 * to_Z a)) by lia. f_equal. ring.
  - rewrite Uint63.lsl_spec. reflexivity.
Qed.

Lemma lsl_big_t : forall a b : i63, 63 <= to_Z b -> Int64.one = tg (PrimInt63.lsl a b).
Proof.
  intros a b H. pose proof (phi_range a). pose proof (phi_range b).
  rewrite <- tg_zero. f_equal. apply to_Z_inj. rewrite Uint63.lsl_spec. change (to_Z 0%uint63) with 0.
  symmetry. replace (2 ^ to_Z b) with (2 ^ (to_Z b - 63) * 2 ^ 63) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_assoc. change wB with (2 ^ 63). apply Z_mod_mult.
Qed.

Lemma lsr_t : forall a b : i63, to_Z b < 63 ->
  Int64.or (Int64.shl (Int64.shru (Int64.shru (tg a) Int64.one) (Int64.shru (tg b) Int64.one)) Int64.one) Int64.one
  = tg (PrimInt63.lsr a b).
Proof.
  intros a b H. pose proof (phi_range a). pose proof (phi_range b).
  rewrite !shr1_t. apply uinj. rewrite uns_tg.
  assert (P0 : 0 < 2 ^ to_Z b) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 <= to_Z a / 2 ^ to_Z b < 2 ^ 63).
  { split; [apply Z.div_pos; lia | ].
    apply Z.le_lt_trans with (to_Z a); [apply Z.div_le_upper_bound; [lia | nia] | lia]. }
  assert (Hs : Int64.shru (Int64.repr (to_Z a)) (Int64.repr (to_Z b)) = Int64.repr (to_Z a / 2 ^ to_Z b)).
  { unfold Int64.shru. rewrite !uns_phi. f_equal. apply Z.shiftr_div_pow2. lia. }
  rewrite Hs. rewrite tag_up by exact Hq. rewrite Uint63.lsr_spec. reflexivity.
Qed.

Lemma lsr_big_t : forall a b : i63, 63 <= to_Z b -> Int64.one = tg (PrimInt63.lsr a b).
Proof.
  intros a b H. pose proof (phi_range a). pose proof (phi_range b).
  rewrite <- tg_zero. f_equal. apply to_Z_inj. rewrite Uint63.lsr_spec. change (to_Z 0%uint63) with 0.
  symmetry. apply Z.div_small. split; [lia | ].
  apply Z.lt_le_trans with (2 ^ 63); [lia | apply Z.pow_le_mono_r; lia].
Qed.

(** [(t << 1) | 1] for any integer [t] is the tagged word of the number whose value is [t] mod 2^63 *)
Lemma up_t : forall (t : Z) (w : i63), t mod 2 ^ 63 = to_Z w ->
  Int64.or (Int64.shl (Int64.repr t) Int64.one) Int64.one = tg w.
Proof.
  intros t w E. pose proof (phi_range w). apply uinj. rewrite uns_tg, uor, uone.
  unfold Int64.shl. rewrite uone, uns_repr, uns_repr. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  assert (He : (((t mod 2 ^ 64) * 2) mod 2 ^ 64) = 2 * (t mod 2 ^ 63)).
  { rewrite Z.mul_mod_idemp_l by lia. rewrite Z.mul_comm.
    replace (2 ^ 64) with (2 * 2 ^ 63) by reflexivity. apply Z.mul_mod_distr_l; lia. }
  rewrite He. rewrite lor_even1 by (pose proof (Z.mod_pos_bound t (2 ^ 63) ltac:(lia)); lia).
  rewrite Z.mod_small; [lia | ]. pose proof (Z.mod_pos_bound t (2 ^ 63) ltac:(lia)). lia.
Qed.

Lemma shr1s_t : forall a : i63, Int64.shr (tg a) Int64.one = Int64.repr (Sint63.to_Z a).
Proof.
  intros a. unfold Int64.shr. rewrite sgn_tg, uone. f_equal.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  symmetry. apply Z.div_unique with (r := 1); [left; lia | lia].
Qed.

Lemma sZ_bound : forall a : i63, - 2 ^ 62 <= Sint63.to_Z a < 2 ^ 62.
Proof.
  intros a. pose proof (phi_range a). rewrite (sZ_cases a).
  destruct (Z.ltb_spec (to_Z a) (2 ^ 62)); lia.
Qed.

Lemma signed_small : forall z, - 2 ^ 62 <= z < 2 ^ 62 -> Int64.signed (Int64.repr z) = z.
Proof.
  intros z H. apply Int64.signed_repr. unfold Int64.min_signed, Int64.max_signed.
  change Int64.half_modulus with (2 ^ 63). lia.
Qed.

Lemma phi_sZ : forall w : i63, to_Z w = Sint63.to_Z w mod 2 ^ 63.
Proof. intros w. apply phi_of_sZ. Qed.

(** logical shift right by a number below 63 *)
Lemma lsr_t2 : forall a b : i63, to_Z b < 63 ->
  Int64.or (Int64.shl (Int64.shru (Int64.shru (tg a) Int64.one) (Int64.shru (tg b) Int64.one)) Int64.one) Int64.one
  = tg (PrimInt63.lsr a b).
Proof.
  intros a b H. pose proof (phi_range a). pose proof (phi_range b).
  rewrite !shr1_t. unfold Int64.shru at 1. rewrite !uns_phi.
  apply up_t.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Uint63.lsr_spec.
  assert (P0 : 0 < 2 ^ to_Z b) by (apply Z.pow_pos_nonneg; lia).
  apply Z.mod_small. split; [apply Z.div_pos; lia | ].
  apply Z.le_lt_trans with (to_Z a); [apply Z.div_le_upper_bound; [lia | nia] | lia].
Qed.

Lemma sZ_small : forall x : i63, to_Z x < 2 ^ 62 -> Sint63.to_Z x = to_Z x.
Proof. intros x H. rewrite sZ_cases. destruct (Z.ltb_spec (to_Z x) (2 ^ 62)); lia. Qed.

(** arithmetic shift right by a number below 63 *)
Lemma asr_t : forall a b : i63, to_Z b < 63 ->
  Int64.or (Int64.shl (Int64.shr (Int64.shr (tg a) Int64.one) (Int64.shru (tg b) Int64.one)) Int64.one) Int64.one
  = tg (PrimInt63.asr a b).
Proof.
  intros a b H. pose proof (phi_range a). pose proof (phi_range b). pose proof (sZ_bound a).
  rewrite shr1s_t, shr1_t. unfold Int64.shr at 1. rewrite (signed_small (Sint63.to_Z a)) by lia.
  rewrite uns_phi.
  apply up_t.
  rewrite (phi_sZ (PrimInt63.asr a b)), Sint63Axioms.asr_spec. rewrite Z.shiftr_div_pow2 by lia.
  assert (Hp : Sint63.to_Z b = to_Z b) by (rewrite sZ_small; [reflexivity | lia]).
  rewrite Hp. reflexivity.
Qed.

(** arithmetic shift right by 63 or more, below 2^62: the sign *)
Lemma asr_big_t : forall a b : i63, 63 <= to_Z b -> to_Z b < 2 ^ 62 ->
  Int64.or (Int64.shr (tg a) (Int64.repr 63)) Int64.one = tg (PrimInt63.asr a b).
Proof.
  intros a b H1 H2. pose proof (phi_range a). pose proof (phi_range b). pose proof (sZ_bound a).
  apply uinj. rewrite uns_tg, uor, uone. unfold Int64.shr. rewrite sgn_tg, (uns_small 63) by lia.
  assert (Hb : Sint63.to_Z b = to_Z b) by (rewrite sZ_small; [reflexivity | lia]).
  assert (Hs : Sint63.to_Z (PrimInt63.asr a b) = Sint63.to_Z a / 2 ^ to_Z b)
    by (rewrite Sint63Axioms.asr_spec, Hb; reflexivity).
  assert (P : 2 ^ 63 <= 2 ^ to_Z b) by (apply Z.pow_le_mono_r; lia).
  assert (Hneg : Sint63.to_Z a < 0 -> Sint63.to_Z a / 2 ^ to_Z b = -1 /\ (2 * Sint63.to_Z a + 1) / 2 ^ 63 = -1).
  { intros N. split.
    - symmetry; apply Z.div_unique with (r := Sint63.to_Z a + 2 ^ to_Z b); [left; lia | lia].
    - symmetry; apply Z.div_unique with (r := 2 * Sint63.to_Z a + 1 + 2 ^ 63); [left; lia | lia]. }
  assert (Hpos : 0 <= Sint63.to_Z a -> Sint63.to_Z a / 2 ^ to_Z b = 0 /\ (2 * Sint63.to_Z a + 1) / 2 ^ 63 = 0).
  { intros N. split; apply Z.div_small; lia. }
  assert (Hd : Z.shiftr (2 * Sint63.to_Z a + 1) 63 = Sint63.to_Z a / 2 ^ to_Z b).
  { rewrite Z.shiftr_div_pow2 by lia.
    destruct (Z_lt_ge_dec (Sint63.to_Z a) 0) as [N | N].
    - destruct (Hneg N) as [E1 E2]. rewrite E1, E2. reflexivity.
    - destruct (Hpos ltac:(lia)) as [E1 E2]. rewrite E1, E2. reflexivity. }
  rewrite Hd, <- Hs. rewrite uns_repr.
  assert (Hm : (Sint63.to_Z (PrimInt63.asr a b)) mod 2 ^ 64 = Sint63.to_Z (PrimInt63.asr a b) mod 2 ^ 64) by reflexivity.
  (* the word is all ones (value -1) or zero; or 1 *)
  assert (Hv : Sint63.to_Z (PrimInt63.asr a b) = -1 \/ Sint63.to_Z (PrimInt63.asr a b) = 0).
  { rewrite Hs. destruct (Z_lt_ge_dec (Sint63.to_Z a) 0) as [N | N]; [left | right].
    - exact (proj1 (Hneg N)).
    - exact (proj1 (Hpos ltac:(lia))). }
  rewrite phi_sZ. destruct Hv as [V | V]; rewrite V.
  - change (-1 mod 2 ^ 64) with (2 ^ 64 - 1). change (-1 mod 2 ^ 63) with (2 ^ 63 - 1).
    replace (Z.lor (2 ^ 64 - 1) 1) with (2 ^ 64 - 1) by (vm_compute; reflexivity). reflexivity.
  - change (0 mod 2 ^ 64) with 0. change (0 mod 2 ^ 63) with 0. reflexivity.
Qed.

Lemma ltb_63_iff' : forall b : i63, PrimInt63.ltb b 63%uint63 = true <-> to_Z b < 63.
Proof. intros b. rewrite Uint63Axioms.ltb_spec. change (to_Z 63%uint63) with 63. tauto. Qed.

Lemma ltb_m62_iff' : forall b : i63, PrimInt63.ltb b m62 = true <-> to_Z b < 2 ^ 62.
Proof. intros b. rewrite Uint63Axioms.ltb_spec, m62_phi. tauto. Qed.

(** arithmetic shift right by 2^62 or more: zero *)
Lemma asr_huge_t : forall a b : i63, 2 ^ 62 <= to_Z b -> Int64.one = tg (PrimInt63.asr a b).
Proof.
  intros a b H. rewrite <- tg_zero. f_equal. rewrite asr_via. unfold asr_kq.
  assert (L : PrimInt63.ltb b 63%uint63 = false).
  { destruct (PrimInt63.ltb b 63%uint63) eqn:E; auto. apply ltb_63_iff' in E. pose proof (phi_range b). lia. }
  rewrite L.
  assert (L2 : PrimInt63.ltb b m62 = false).
  { destruct (PrimInt63.ltb b m62) eqn:E; auto. apply ltb_m62_iff' in E. lia. }
  rewrite L2. reflexivity.
Qed.

(** ** division, remainder *)

Lemma div_t : forall a b : i63,
  Int64.or (Int64.shl (Int64.divu (Int64.shru (tg a) Int64.one) (Int64.shru (tg b) Int64.one)) Int64.one) Int64.one
  = tg (PrimInt63.div a b).
Proof.
  intros a b. rewrite !shr1_t. unfold Int64.divu. rewrite !uns_phi.
  apply up_t. pose proof (phi_range (PrimInt63.div a b)) as R. rewrite Uint63.div_spec in R |- *.
  apply Z.mod_small. exact R.
Qed.

Lemma mod_t : forall a b : i63,
  Int64.or (Int64.shl (Int64.modu (Int64.shru (tg a) Int64.one) (Int64.shru (tg b) Int64.one)) Int64.one) Int64.one
  = tg (PrimInt63.mod a b).
Proof.
  intros a b. rewrite !shr1_t. unfold Int64.modu. rewrite !uns_phi.
  apply up_t. pose proof (phi_range (PrimInt63.mod a b)) as R. rewrite Uint63.mod_spec in R |- *.
  apply Z.mod_small. exact R.
Qed.

Lemma mods_t : forall a b : i63,
  Int64.or (Int64.shl (Int64.mods (Int64.shr (tg a) Int64.one) (Int64.shr (tg b) Int64.one)) Int64.one) Int64.one
  = tg (PrimInt63.mods a b).
Proof.
  intros a b. rewrite !shr1s_t. unfold Int64.mods.
  pose proof (sZ_bound a). pose proof (sZ_bound b).
  rewrite !signed_small by lia.
  apply up_t. rewrite (phi_sZ (PrimInt63.mods a b)), Sint63Axioms.mod_spec. reflexivity.
Qed.

(** What Rocq leaves open and its own computation settles: the smallest number divided by -1.  [Sint63Axioms.div_spec]
    excludes it; the quotient 2^62 does not fit, and [vm_compute] gives the smallest number back
    (tests: [Eval vm_compute in Sint63.to_Z (divs min_int (0 - 1))]).  Assumed here as the one fact about the primitive. *)
Axiom divs_min_neg1 : forall x y : i63, Sint63.to_Z x = - 2 ^ 62 -> Sint63.to_Z y = -1 ->
  Sint63.to_Z (PrimInt63.divs x y) = - 2 ^ 62.

Lemma sZ_min : Sint63.to_Z Sint63Axioms.min_int = - 2 ^ 62.
Proof. reflexivity. Qed.

Lemma divs_t : forall a b : i63,
  Int64.or (Int64.shl (Int64.divs (Int64.shr (tg a) Int64.one) (Int64.shr (tg b) Int64.one)) Int64.one) Int64.one
  = tg (PrimInt63.divs a b).
Proof.
  intros a b. rewrite !shr1s_t. unfold Int64.divs.
  pose proof (sZ_bound a). pose proof (sZ_bound b).
  rewrite !signed_small by lia.
  apply up_t. rewrite (phi_sZ (PrimInt63.divs a b)).
  destruct (Z.eq_dec (Sint63.to_Z b) (-1)) as [Hb | Hb].
  - destruct (Z.eq_dec (Sint63.to_Z a) (- 2 ^ 62)) as [Ha | Ha].
    + rewrite (divs_min_neg1 a b Ha Hb), Ha, Hb. reflexivity.
    + rewrite Sint63Axioms.div_spec by (left; rewrite sZ_min; exact Ha). reflexivity.
  - rewrite Sint63Axioms.div_spec by (right; exact Hb). reflexivity.
Qed.

(** the guards: the tagged word of a number against a literal *)
Lemma ltu_lit_t : forall (b : i63) n, 0 <= n < 2 ^ 64 ->
  Int64.ltu (tg b) (Int64.repr n) = (2 * to_Z b + 1 <? n).
Proof.
  intros b n H. unfold Int64.ltu. rewrite uns_tg, (uns_small n) by lia.
  destruct (zlt (2 * to_Z b + 1) n); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma lt127_t : forall b : i63, Int64.ltu (tg b) (Int64.repr 127) = (to_Z b <? 63).
Proof.
  intros b. rewrite ltu_lit_t by lia.
  destruct (Z.ltb_spec (2 * to_Z b + 1) 127), (Z.ltb_spec (to_Z b) 63); try reflexivity; lia.
Qed.

Lemma lt263_t : forall b : i63, Int64.ltu (tg b) (Int64.repr (2 ^ 63)) = (to_Z b <? 2 ^ 62).
Proof.
  intros b. rewrite ltu_lit_t by lia.
  destruct (Z.ltb_spec (2 * to_Z b + 1) (2 ^ 63)), (Z.ltb_spec (to_Z b) (2 ^ 62)); try reflexivity; lia.
Qed.

Lemma lt128_t : forall b : i63, Int64.ltu (tg b) (Int64.repr 128) = (to_Z b <? 64).
Proof.
  intros b. rewrite ltu_lit_t by lia.
  destruct (Z.ltb_spec (2 * to_Z b + 1) 128), (Z.ltb_spec (to_Z b) 64); try reflexivity; lia.
Qed.

Lemma lt_n_t : forall (i : i63) n, 0 <= n < 2 ^ 31 ->
  Int64.ltu (tg i) (Int64.repr (2 * n)) = (to_Z i <? n).
Proof.
  intros i n H. rewrite ltu_lit_t by lia.
  destruct (Z.ltb_spec (2 * to_Z i + 1) (2 * n)), (Z.ltb_spec (to_Z i) n); try reflexivity; lia.
Qed.

Lemma eq_zero_t : forall b : i63, Int64.eq (Int64.repr (to_Z b)) Int64.zero = PrimInt63.eqb b 0%uint63.
Proof.
  intros b. unfold Int64.eq. rewrite uns_phi. change (Int64.unsigned Int64.zero) with 0.
  destruct (zeq (to_Z b) 0) as [E | E].
  - symmetry. apply Uint63.eqb_spec. apply to_Z_inj. rewrite E. reflexivity.
  - symmetry. destruct (PrimInt63.eqb b 0%uint63) eqn:Q; auto. apply Uint63.eqb_spec in Q. subst. exfalso. apply E. reflexivity.
Qed.

Lemma eqb_zero_div : forall a b : i63, PrimInt63.eqb b 0%uint63 = true -> PrimInt63.div a b = 0%uint63.
Proof.
  intros a b H. apply Uint63.eqb_spec in H. subst b. apply to_Z_inj. rewrite Uint63.div_spec. change (to_Z 0%uint63) with 0.
  rewrite Zdiv_0_r. reflexivity.
Qed.

Lemma eqb_zero_mod : forall a b : i63, PrimInt63.eqb b 0%uint63 = true -> PrimInt63.mod a b = a.
Proof.
  intros a b H. apply Uint63.eqb_spec in H. subst b. apply to_Z_inj. rewrite Uint63.mod_spec. change (to_Z 0%uint63) with 0.
  rewrite Zmod_0_r. reflexivity.
Qed.

Lemma eqb_zero_mods : forall a b : i63, PrimInt63.eqb b 0%uint63 = true -> PrimInt63.mods a b = a.
Proof.
  intros a b H. apply Uint63.eqb_spec in H. subst b.
  apply Sint63.to_Z_inj. rewrite Sint63Axioms.mod_spec. change (Sint63.to_Z 0%uint63) with 0. apply Zrem_0_r.
Qed.

Lemma eqb_zero_divs : forall a b : i63, PrimInt63.eqb b 0%uint63 = true -> PrimInt63.divs a b = 0%uint63.
Proof.
  intros a b H. apply Uint63.eqb_spec in H. subst b.
  apply Sint63.to_Z_inj. rewrite Sint63Axioms.div_spec by (right; discriminate).
  change (Sint63.to_Z 0%uint63) with 0. rewrite Zquot.Zquot_0_r. reflexivity.
Qed.

Lemma ltu_iword_t : forall b : i63, to_Z b < 63 -> Int64.ltu (Int64.shru (tg b) Int64.one) Int64.iwordsize = true.
Proof.
  intros b H. rewrite shr1_t. unfold Int64.ltu. rewrite uns_phi.
  change (Int64.unsigned Int64.iwordsize) with 64. destruct (zlt (to_Z b) 64); auto. lia.
Qed.

Lemma mods_guard : forall a b : i63, PrimInt63.eqb b 0%uint63 = false ->
  Int64.eq (Int64.shr (tg b) Int64.one) Int64.zero = false /\
  Int64.eq (Int64.shr (tg a) Int64.one) (Int64.repr Int64.min_signed) = false.
Proof.
  intros a b Hb. pose proof (sZ_bound a). pose proof (sZ_bound b). rewrite !shr1s_t. split.
  - rewrite Int64.eq_signed, signed_small by lia. change (Int64.signed Int64.zero) with 0.
    destruct (zeq (Sint63.to_Z b) 0) as [E0 | E0]; [ | reflexivity].
    exfalso. assert (b = 0%uint63) by (apply Sint63.to_Z_inj; rewrite E0; reflexivity). subst. discriminate.
  - rewrite Int64.eq_signed, signed_small by lia.
    rewrite Int64.signed_repr by (unfold Int64.min_signed, Int64.max_signed; change Int64.half_modulus with (2 ^ 63); lia).
    destruct (zeq (Sint63.to_Z a) Int64.min_signed) as [E0 | E0]; [ | reflexivity].
    exfalso. unfold Int64.min_signed in E0. change Int64.half_modulus with (2 ^ 63) in E0. lia.
Qed.
