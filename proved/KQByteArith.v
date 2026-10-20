(** The arithmetic of a byte of a narrow cell: [rd8] and [upd8] (KQRun.v) in numbers. *)

From Stdlib Require Import ZArith Lia Uint63 Sint63 Znumtheory Zdiv.
From compcert Require Import Coqlib Integers.
From KQC Require Import KQLSigned KQTArith.

Notation i63 := PrimInt63.int.
Local Open Scope Z_scope.

Lemma land_ones8 : forall a : Z, Z.land a 255 = a mod 256.
Proof. intros a. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_ones2 : forall a : Z, Z.land a 3 = a mod 4.
Proof. intros a. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(** the shift amount of byte [i] *)
Lemma shamt : forall i : i63,
  φ (PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63)%uint63 = (φ i%uint63 mod 4) * 8.
Proof.
  intros i. rewrite Uint63.mul_spec, Uint63.land_spec'. change (φ 3%uint63) with 3. change (φ 8%uint63) with 8.
  rewrite land_ones2. pose proof (Z.mod_pos_bound (φ i%uint63) 4 ltac:(lia)).
  apply Z.mod_small. rewrite wB63. lia.
Qed.

(** the low byte of a signed number *)
Lemma low_byte : forall y : i63, φ (PrimInt63.land y 255%uint63)%uint63 = sZ y mod 256.
Proof.
  intros y. rewrite Uint63.land_spec'. change (φ 255%uint63) with 255. rewrite land_ones8.
  rewrite (phi_of_sZ y). rewrite <- (Zmod_div_mod 256 (2 ^ 63) (sZ y)) by (try lia; exists (2 ^ 55); reflexivity).
  reflexivity.
Qed.

Lemma sZ_small' : forall x : i63, φ x%uint63 < 2 ^ 62 -> sZ x = φ x%uint63.
Proof. intros x H. rewrite sZ_cases. destruct (Z.ltb_spec (φ x%uint63) (2 ^ 62)); lia. Qed.

Lemma sZ_bound' : forall a : i63, - 2 ^ 62 <= sZ a < 2 ^ 62.
Proof. intros a. exact (sZ_bound a). Qed.

Lemma eq_of_mod : forall a b : Z, - 2 ^ 62 <= a < 2 ^ 62 -> - 2 ^ 62 <= b < 2 ^ 62 -> a mod 2 ^ 63 = b mod 2 ^ 63 -> a = b.
Proof.
  intros a b Ha Hb H.
  assert (D : (a - b) mod 2 ^ 63 = 0) by (rewrite Zminus_mod, H; rewrite Z.sub_diag; reflexivity).
  apply Z.mod_divide in D; [ | lia]. destruct D as [k Hk]. 
  assert (k = 0) by (nia). lia.
Qed.

Lemma asr_val : forall (x n : i63), φ n%uint63 < 62 -> sZ (PrimInt63.asr x n) = sZ x / 2 ^ φ n%uint63.
Proof.
  intros x n H. rewrite Sint63Axioms.asr_spec. rewrite (sZ_small' n) by lia. reflexivity.
Qed.

(** the byte [(s / 2^k) mod 256] of the number [x] *)
Lemma rd8_arith : forall x i : i63,
  φ (PrimInt63.land (PrimInt63.asr x (PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63)) 255%uint63)%uint63
  = (sZ x / 2 ^ ((φ i%uint63 mod 4) * 8)) mod 256.
Proof.
  intros x i. rewrite low_byte. rewrite asr_val.
  - rewrite shamt. reflexivity.
  - rewrite shamt. pose proof (Z.mod_pos_bound (φ i%uint63) 4 ltac:(lia)). lia.
Qed.

(** [upd8]'s new number *)
Lemma upd8_arith : forall x i v : i63, - 2 ^ 31 <= sZ x < 2 ^ 31 ->
  sZ (PrimInt63.add (PrimInt63.sub x (PrimInt63.lsl (PrimInt63.land (PrimInt63.asr x (PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63)) 255%uint63)
                                                   (PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63)))
                    (PrimInt63.lsl (PrimInt63.land v 255%uint63) (PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63)))
  = sZ x - ((sZ x / 2 ^ ((φ i%uint63 mod 4) * 8)) mod 256) * 2 ^ ((φ i%uint63 mod 4) * 8)
    + (sZ v mod 256) * 2 ^ ((φ i%uint63 mod 4) * 8).
Proof.
  intros x i v Hx.
  pose proof (Z.mod_pos_bound (φ i%uint63) 4 ltac:(lia)) as Hm.
  set (s := (φ i%uint63 mod 4) * 8) in *.
  assert (Hs : 0 <= s <= 24) by lia.
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)) as Hp0.
  assert (Hp1 : 2 ^ s <= 2 ^ 24) by (apply Z.pow_le_mono_r; lia).
  assert (Hp : 1 <= 2 ^ s <= 2 ^ 24) by lia.
  pose proof (rd8_arith x i) as E. fold s in E.
  pose proof (Z.mod_pos_bound (sZ x / 2 ^ s) 256 ltac:(lia)) as Be.
  pose proof (Z.mod_pos_bound (sZ v) 256 ltac:(lia)) as Bv.
  assert (Ev : φ (PrimInt63.land v 255%uint63)%uint63 = sZ v mod 256) by apply low_byte.
  set (e := (sZ x / 2 ^ s) mod 256) in *.
  set (b := sZ v mod 256) in *.
  assert (Pe : e * 2 ^ s < 2 ^ 32) by (nia).
  assert (Pb : b * 2 ^ s < 2 ^ 32) by (nia).
  assert (L1 : φ (PrimInt63.lsl (PrimInt63.land (PrimInt63.asr x (PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63)) 255%uint63)
                                (PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63))%uint63 = e * 2 ^ s).
  { rewrite Uint63.lsl_spec, E, shamt. fold s. rewrite wB63. apply Z.mod_small. nia. }
  assert (L2 : φ (PrimInt63.lsl (PrimInt63.land v 255%uint63) (PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63))%uint63 = b * 2 ^ s).
  { rewrite Uint63.lsl_spec, Ev, shamt. fold s. rewrite wB63. apply Z.mod_small. nia. }
  set (T := sZ x - e * 2 ^ s + b * 2 ^ s).
  apply eq_of_mod.
  - apply sZ_bound.
  - unfold T. nia.
  - rewrite <- phi_of_sZ. rewrite Uint63.add_spec, Uint63.sub_spec, L1, L2, phi_of_sZ.
    rewrite wB63. unfold T.
    set (E1 := e * 2 ^ s). set (F1 := b * 2 ^ s). 
    rewrite Z.add_mod_idemp_l by lia.
    replace (sZ x mod 2 ^ 63 - E1 + F1) with (sZ x mod 2 ^ 63 + (F1 - E1)) by ring.
    rewrite Z.add_mod_idemp_l by lia.
    f_equal. ring.
Qed.

(** the signed and the unsigned reading of a 32-bit number have the same bytes *)
Lemma modsub256 : forall q k : Z, (q - 256 * k) mod 256 = q mod 256.
Proof. intros q k. replace (q - 256 * k) with (q + (- k) * 256) by ring. apply Z.mod_add; lia. Qed.

Lemma byte_signed : forall (iv : Int.int) (bb : Z), 0 <= bb < 4 ->
  (Int.unsigned iv / 2 ^ (8 * bb)) mod 256 = (Int.signed iv / 2 ^ (8 * bb)) mod 256.
Proof.
  intros iv bb Rb. unfold Int.signed. destruct (zlt (Int.unsigned iv) Int.half_modulus); [reflexivity | ].
  change Int.modulus with (2 ^ 32).
  assert (Hb : 0 < 2 ^ (8 * bb)) by (apply Z.pow_pos_nonneg; lia).
  assert (E : Int.unsigned iv - 2 ^ 32 = Int.unsigned iv + (- 2 ^ (32 - 8 * bb)) * 2 ^ (8 * bb)).
  { rewrite Z.mul_opp_l, <- Z.pow_add_r by lia. replace (32 - 8 * bb + 8 * bb) with 32 by lia. ring. }
  rewrite E, Z.div_add by lia.
  assert (Rb' : bb = 0 \/ bb = 1 \/ bb = 2 \/ bb = 3) by lia.
  destruct Rb' as [-> | [-> | [-> | ->]]].
  - replace (- 2 ^ (32 - 8 * 0)) with (-16777216 * 256) by reflexivity. symmetry. apply Z.mod_add; lia.
  - replace (- 2 ^ (32 - 8 * 1)) with (-65536 * 256) by reflexivity. symmetry. apply Z.mod_add; lia.
  - replace (- 2 ^ (32 - 8 * 2)) with (-256 * 256) by reflexivity. symmetry. apply Z.mod_add; lia.
  - replace (- 2 ^ (32 - 8 * 3)) with (-1 * 256) by reflexivity. symmetry. apply Z.mod_add; lia.
Qed.

(** the number the C store leaves in a cell is the one the abstract [upd8] gives *)
Lemma store_cell_eq : forall (iv : Int.int) (x v new : i63) (vb bb : Z),
  0 <= bb < 4 -> Int.signed iv = sZ x -> vb mod 256 = sZ v mod 256 ->
  sZ new = sZ x - ((sZ x / 2 ^ (8 * bb)) mod 256) * 2 ^ (8 * bb) + (sZ v mod 256) * 2 ^ (8 * bb) ->
  Int.repr (Int.unsigned iv - ((Int.unsigned iv / 2 ^ (8 * bb)) mod 256) * 2 ^ (8 * bb) + (vb mod 256) * 2 ^ (8 * bb))
  = Int.repr (φ new%uint63).
Proof.
  intros iv x v new vb bb Rb Hs Hv Hn.
  rewrite (byte_signed iv bb Rb), Hs, Hv.
  destruct (Int.eqm_signed_unsigned iv) as [k1 Hk1]. rewrite Hs in Hk1. change Int.modulus with (2 ^ 32) in Hk1.
  pose proof (phi_of_sZ new) as Hp0. rewrite Z.mod_eq in Hp0 by lia.
  remember (sZ new / 2 ^ 63) as q.
  apply Int.eqm_samerepr. exists (2 ^ 31 * q - k1).
  change Int.modulus with (2 ^ 32).
  rewrite Hp0, Hn. lia.
Qed.

Lemma lt8_t : forall (i : i63) n, 0 <= n < 2 ^ 31 ->
  Int64.ltu (tg i) (Int64.repr (8 * n)) = (φ i%uint63 <? 4 * n).
Proof.
  intros i n H. rewrite ltu_lit_t by lia.
  destruct (Z.ltb_spec (2 * φ i%uint63 + 1) (8 * n)), (Z.ltb_spec (φ i%uint63) (4 * n)); try reflexivity; lia.
Qed.

Lemma asr2_val : forall vi : i63, φ vi%uint63 < 2 ^ 62 -> sZ (PrimInt63.asr vi 2%uint63) = φ vi%uint63 / 4
  /\ PrimInt63.asr vi 2%uint63 = Uint63.of_Z (φ vi%uint63 / 4).
Proof.
  intros vi H. 
  assert (S : sZ (PrimInt63.asr vi 2%uint63) = φ vi%uint63 / 4).
  { rewrite (asr_val vi 2%uint63) by (change (φ 2%uint63) with 2; lia). change (φ 2%uint63) with 2.
    rewrite (sZ_small' vi H). reflexivity. }
  split; [exact S | ].
  apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec.
  pose proof (phi_range vi) as Rv.
  assert (B : 0 <= φ vi%uint63 / 4 < 2 ^ 60).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | replace (4 * 2 ^ 60) with (2 ^ 62) by reflexivity; lia]]. }
  rewrite Z.mod_small by (rewrite wB63; lia).
  pose proof (phi_of_sZ (PrimInt63.asr vi 2%uint63)) as P. rewrite S in P. rewrite P. apply Z.mod_small. lia.
Qed.
