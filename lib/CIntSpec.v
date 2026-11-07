(* lib/CIntSpec.v -- WHAT lib/CInt.v COMPUTES, against Z.  Rests on Rocq's axioms of its machine numbers and nothing else
   (hw/spec.sh prints the assumptions of each).

   phi is a number of the system read as unsigned (0 .. 2^63), Z_ as signed; u64_val a u64 as a number below 2^64.  For a narrow
   type of w bits an unsigned operation gives the result modulo 2^w, a signed one the result wrapped into -2^(w-1) .. 2^(w-1) - 1
   (sw).  The function each theorem names is what the C of a program using it computes, by the verified compiler's theorem. *)
From Stdlib Require Import ZArith Lia Sint63 Bool.
Require Import KQ.KQRun KQ.lib.CInt.
Open Scope Z_scope.
Notation phi := Uint63.to_Z.
Notation Z_ := Sint63.to_Z.

Lemma wB_eq : wB = 2 ^ 63.
Proof. reflexivity. Qed.
Lemma phi_bounds (x : int) : 0 <= phi x < 2 ^ 63.
Proof. exact (Uint63.to_Z_bounded x). Qed.
Lemma phi_land_ones (x m : int) (k : Z) : 0 <= k -> phi m = Z.ones k -> phi (PrimInt63.land x m) = phi x mod 2 ^ k.
Proof. intros K M. rewrite Uint63.land_spec', M. apply Z.land_ones. exact K. Qed.
Lemma mod_pow (w v z : Z) : 0 <= w <= v -> (z mod 2 ^ v) mod 2 ^ w = z mod 2 ^ w.
Proof.
  intros W.
  assert (P : 2 ^ v = 2 ^ (v - w) * 2 ^ w) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Nz : 2 ^ w <> 0) by (apply Z.pow_nonzero; lia).
  assert (Nv : 2 ^ v <> 0) by (apply Z.pow_nonzero; lia).
  pose proof (Z.div_mod z (2 ^ v) Nv) as D.
  assert (E : z = z mod 2 ^ v + (z / 2 ^ v * 2 ^ (v - w)) * 2 ^ w).
  { rewrite <- Z.mul_assoc, <- P. rewrite Z.mul_comm in D. lia. }
  rewrite E at 2. rewrite Z.mod_add by exact Nz. reflexivity.
Qed.
Lemma mod_W (w z : Z) : 0 <= w <= 63 -> (z mod 2 ^ 63) mod 2 ^ w = z mod 2 ^ w.
Proof. apply mod_pow. Qed.
Lemma phi_Z (x : int) : phi x = Z_ x mod 2 ^ 63.
Proof. rewrite <- wB_eq. symmetry. apply Sint63.to_Z_mod_Uint63to_Z. Qed.
Lemma Z_small (x : int) : phi x < 2 ^ 62 -> Z_ x = phi x.
Proof.
  intro L. pose proof (phi_Z x) as M. pose proof (Sint63.to_Z_bounded x) as B. rewrite Sint63.to_Z_min, Sint63.to_Z_max in B.
  rewrite wB_eq in B. replace (2 ^ 63 / 2) with (2 ^ 62) in B by reflexivity.
  destruct (Z_le_gt_dec 0 (Z_ x)) as [P | P].
  - rewrite Z.mod_small in M; lia.
  - assert (E : Z_ x + 2 ^ 63 = Z_ x mod 2 ^ 63) by (apply Z.mod_unique_pos with (q := (-1)%Z); lia).
    lia.
Qed.
(* a number of the system wrapped into w bits *)
Definition sw (w z : Z) : Z := ((z + 2 ^ (w - 1)) mod 2 ^ w) - 2 ^ (w - 1).
Lemma sw_mod (w z : Z) : 1 <= w <= 63 -> sw w (z mod 2 ^ 63) = sw w z.
Proof.
  intros W. unfold sw. f_equal.
  rewrite Z.add_mod by (apply Z.pow_nonzero; lia).
  rewrite mod_W by lia. rewrite <- Z.add_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
(* the cut every signed type uses *)
Lemma sw_cut (w : Z) (x m h f : int) : 1 <= w <= 32 -> phi m = Z.ones w -> phi h = 2 ^ (w - 1) -> phi f = 2 ^ w ->
  Z_ (let y := PrimInt63.land x m in if (y <? h)%sint63 then y else (y - f)%sint63) = sw w (phi x).
Proof.
  intros W M H F.
  assert (Pw : 2 ^ w = 2 * 2 ^ (w - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Up : 2 ^ w <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (Hp : 0 < 2 ^ (w - 1)) by (apply Z.pow_pos_nonneg; lia).
  cbv zeta. set (y := PrimInt63.land x m).
  assert (Y : phi y = phi x mod 2 ^ w) by (apply phi_land_ones; lia).
  assert (Yb : 0 <= phi y < 2 ^ w) by (rewrite Y; apply Z.mod_pos_bound; lia).
  assert (Zy : Z_ y = phi y) by (apply Z_small; lia).
  assert (Zh : Z_ h = 2 ^ (w - 1)) by (rewrite Z_small; lia).
  assert (Zf : Z_ f = 2 ^ w) by (rewrite Z_small; lia).
  assert (Mo : (phi x + 2 ^ (w - 1)) mod 2 ^ w = (phi y + 2 ^ (w - 1)) mod 2 ^ w).
  { rewrite Y. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
  unfold sw. rewrite Mo.
  destruct (Sint63.ltbP y h) as [L | L]; rewrite Zy, Zh in L.
  - rewrite Z.mod_small by lia. rewrite Zy. lia.
  - assert (E : (phi y + 2 ^ (w - 1)) mod 2 ^ w = phi y + 2 ^ (w - 1) - 2 ^ w).
    { symmetry. apply Z.mod_unique_pos with (q := 1); lia. }
    rewrite E.
    rewrite Sint63.sub_spec. rewrite Zy, Zf. unfold Sint63.cmod. rewrite wB_eq.
    replace (2 ^ 63 / 2)%Z with (2 ^ 62) by reflexivity.
    rewrite Z.mod_small by lia. lia.
Qed.

(* ---- 8 bits *)
Theorem u8_of_spec (x : int) : phi (u8_of x) = phi x mod 2 ^ 8.
Proof. unfold u8_of. apply phi_land_ones; [lia | reflexivity]. Qed.
Theorem i8_of_spec (x : int) : Z_ (i8_of x) = sw 8 (phi x).
Proof. unfold i8_of. apply (sw_cut 8); try lia; reflexivity. Qed.
Theorem u8_add_spec (a b : int) : phi (u8_add a b) = (phi a + phi b) mod 2 ^ 8.
Proof. unfold u8_add. rewrite u8_of_spec, Uint63.add_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u8_sub_spec (a b : int) : phi (u8_sub a b) = (phi a - phi b) mod 2 ^ 8.
Proof. unfold u8_sub. rewrite u8_of_spec, Uint63.sub_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u8_mul_spec (a b : int) : phi (u8_mul a b) = (phi a * phi b) mod 2 ^ 8.
Proof. unfold u8_mul. rewrite u8_of_spec, Uint63.mul_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u8_not_spec (a : int) : phi (u8_not a) = (255 - phi a) mod 2 ^ 8.
Proof. unfold u8_not. rewrite u8_of_spec, Uint63.sub_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u8_and_spec (a b : int) : phi (u8_and a b) = Z.land (phi a) (phi b) mod 2 ^ 8.
Proof. unfold u8_and. rewrite u8_of_spec, Uint63.land_spec'. reflexivity. Qed.
Theorem u8_or_spec (a b : int) : phi (u8_or a b) = Z.lor (phi a) (phi b) mod 2 ^ 8.
Proof. unfold u8_or. rewrite u8_of_spec, Uint63.lor_spec'. reflexivity. Qed.
Theorem u8_xor_spec (a b : int) : phi (u8_xor a b) = Z.lxor (phi a) (phi b) mod 2 ^ 8.
Proof. unfold u8_xor. rewrite u8_of_spec, Uint63.lxor_spec'. reflexivity. Qed.
Lemma u8_amount (n : int) : phi (PrimInt63.land n 7%uint63) = phi n mod 8.
Proof. rewrite (phi_land_ones n 7%uint63 3) by (lia || reflexivity). reflexivity. Qed.
Theorem u8_shl_spec (a n : int) : phi (u8_shl a n) = (phi a * 2 ^ (phi n mod 8)) mod 2 ^ 8.
Proof.
  unfold u8_shl. rewrite u8_of_spec, Uint63.lsl_spec, wB_eq, mod_W by lia. rewrite u8_of_spec, u8_amount.
  rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.
Theorem u8_shr_spec (a n : int) : phi (u8_shr a n) = phi a / 2 ^ (phi n mod 8).
Proof. unfold u8_shr. rewrite Uint63.lsr_spec, u8_amount. reflexivity. Qed.
Theorem u8_div_spec (a b : int) : phi (u8_div a b) = phi a / phi b.
Proof. exact (Uint63.div_spec a b). Qed.
Theorem u8_mod_spec (a b : int) : phi (u8_mod a b) = phi a mod phi b.
Proof. exact (Uint63.mod_spec a b). Qed.
Theorem u8_ltb_spec (a b : int) : u8_ltb a b = (phi a <? phi b).
Proof. unfold u8_ltb. destruct (Uint63.ltbP a b) as [L | L]; symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia. Qed.
Theorem u8_leb_spec (a b : int) : u8_leb a b = (phi a <=? phi b).
Proof. unfold u8_leb. destruct (Uint63.lebP a b) as [L | L]; symmetry; [apply Z.leb_le | apply Z.leb_gt]; lia. Qed.
Theorem i8_add_spec (a b : int) : Z_ (i8_add a b) = sw 8 (Z_ a + Z_ b).
Proof.
  unfold i8_add. rewrite i8_of_spec, Uint63.add_spec, wB_eq, !phi_Z.
  rewrite <- Z.add_mod by lia. apply sw_mod. lia.
Qed.
Theorem i8_sub_spec (a b : int) : Z_ (i8_sub a b) = sw 8 (Z_ a - Z_ b).
Proof.
  unfold i8_sub. rewrite i8_of_spec, Uint63.sub_spec, wB_eq, !phi_Z.
  rewrite <- Zminus_mod. apply sw_mod. lia.
Qed.
Theorem i8_mul_spec (a b : int) : Z_ (i8_mul a b) = sw 8 (Z_ a * Z_ b).
Proof.
  unfold i8_mul. rewrite i8_of_spec, Uint63.mul_spec, wB_eq, !phi_Z.
  rewrite <- Z.mul_mod by lia. apply sw_mod. lia.
Qed.
Theorem i8_not_spec (a : int) : Z_ (i8_not a) = sw 8 (255 - Z_ a).
Proof.
  unfold i8_not. rewrite i8_of_spec, Uint63.sub_spec, wB_eq, !phi_Z.
  change (Z_ 255%sint63) with 255.
  rewrite <- Zminus_mod. apply sw_mod. lia.
Qed.
Theorem i8_and_spec (a b : int) : Z_ (i8_and a b) = sw 8 (Z.land (phi a) (phi b)).
Proof. unfold i8_and. rewrite i8_of_spec, Uint63.land_spec'. reflexivity. Qed.
Theorem i8_or_spec (a b : int) : Z_ (i8_or a b) = sw 8 (Z.lor (phi a) (phi b)).
Proof. unfold i8_or. rewrite i8_of_spec, Uint63.lor_spec'. reflexivity. Qed.
Theorem i8_xor_spec (a b : int) : Z_ (i8_xor a b) = sw 8 (Z.lxor (phi a) (phi b)).
Proof. unfold i8_xor. rewrite i8_of_spec, Uint63.lxor_spec'. reflexivity. Qed.
Theorem i8_shl_spec (a n : int) : Z_ (i8_shl a n) = sw 8 (phi a * 2 ^ (phi n mod 8)).
Proof.
  unfold i8_shl. rewrite i8_of_spec, Uint63.lsl_spec, wB_eq, u8_of_spec, u8_amount, sw_mod by lia.
  unfold sw. f_equal. rewrite Z.add_mod by lia. rewrite Z.mul_mod_idemp_l by lia.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Theorem i8_shr_spec (a n : int) : Z_ (i8_shr a n) = Z_ a / 2 ^ (phi n mod 8).
Proof.
  unfold i8_shr. rewrite Sint63.asr_spec, (Z_small (PrimInt63.land n 7%uint63)), u8_amount; [reflexivity | ].
  rewrite u8_amount. assert (0 <= phi n mod 8 < 8) by (apply Z.mod_pos_bound; lia). lia.
Qed.
Theorem i8_div_spec (a b : int) : Z_ (i8_div a b) = sw 8 (Z.quot (Z_ a) (Z_ b)).
Proof.
  unfold i8_div. destruct (Uint63.eqbP b (-1)%sint63) as [E | E].
  - apply Uint63.to_Z_inj in E. subst b. rewrite i8_of_spec, Uint63.sub_spec, wB_eq, !phi_Z.
    change (Z_ 0%sint63) with 0. change (Z_ (-1)%sint63) with (-1).
    rewrite <- Zminus_mod. rewrite sw_mod by lia.
    f_equal. change (Z.quot (Z_ a) (-1)) with (Z.quot (Z_ a) (Z.opp 1)). rewrite Z.quot_opp_r by lia. rewrite Z.quot_1_r. lia.
  - assert (N : Z_ a <> Z_ Sint63.min_int \/ Z_ b <> (-1)).
    { right. intro C. apply E. f_equal. apply Sint63.to_Z_inj. rewrite C. reflexivity. }
    rewrite i8_of_spec, phi_Z.
    rewrite sw_mod by lia. f_equal. apply Sint63.div_spec. exact N.
Qed.
Theorem i8_mod_spec (a b : int) : Z_ (i8_mod a b) = sw 8 (Z.rem (Z_ a) (Z_ b)).
Proof.
  unfold i8_mod. destruct (Uint63.eqbP b (-1)%sint63) as [E | E].
  - apply Uint63.to_Z_inj in E. subst b.
    change (Z_ (-1)%sint63) with (Z.opp 1). rewrite Z.rem_opp_r by lia. rewrite Z.rem_1_r. reflexivity.
  - rewrite i8_of_spec, phi_Z.
    rewrite sw_mod by lia. f_equal. apply Sint63.mod_spec.
Qed.
Theorem i8_ltb_spec (a b : int) : i8_ltb a b = (Z_ a <? Z_ b).
Proof. unfold i8_ltb. destruct (Sint63.ltbP a b) as [L | L]; symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia. Qed.
Theorem i8_leb_spec (a b : int) : i8_leb a b = (Z_ a <=? Z_ b).
Proof. unfold i8_leb. destruct (Sint63.lebP a b) as [L | L]; symmetry; [apply Z.leb_le | apply Z.leb_gt]; lia. Qed.

(* ---- 16 bits *)
Theorem u16_of_spec (x : int) : phi (u16_of x) = phi x mod 2 ^ 16.
Proof. unfold u16_of. apply phi_land_ones; [lia | reflexivity]. Qed.
Theorem i16_of_spec (x : int) : Z_ (i16_of x) = sw 16 (phi x).
Proof. unfold i16_of. apply (sw_cut 16); try lia; reflexivity. Qed.
Theorem u16_add_spec (a b : int) : phi (u16_add a b) = (phi a + phi b) mod 2 ^ 16.
Proof. unfold u16_add. rewrite u16_of_spec, Uint63.add_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u16_sub_spec (a b : int) : phi (u16_sub a b) = (phi a - phi b) mod 2 ^ 16.
Proof. unfold u16_sub. rewrite u16_of_spec, Uint63.sub_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u16_mul_spec (a b : int) : phi (u16_mul a b) = (phi a * phi b) mod 2 ^ 16.
Proof. unfold u16_mul. rewrite u16_of_spec, Uint63.mul_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u16_not_spec (a : int) : phi (u16_not a) = (65535 - phi a) mod 2 ^ 16.
Proof. unfold u16_not. rewrite u16_of_spec, Uint63.sub_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u16_and_spec (a b : int) : phi (u16_and a b) = Z.land (phi a) (phi b) mod 2 ^ 16.
Proof. unfold u16_and. rewrite u16_of_spec, Uint63.land_spec'. reflexivity. Qed.
Theorem u16_or_spec (a b : int) : phi (u16_or a b) = Z.lor (phi a) (phi b) mod 2 ^ 16.
Proof. unfold u16_or. rewrite u16_of_spec, Uint63.lor_spec'. reflexivity. Qed.
Theorem u16_xor_spec (a b : int) : phi (u16_xor a b) = Z.lxor (phi a) (phi b) mod 2 ^ 16.
Proof. unfold u16_xor. rewrite u16_of_spec, Uint63.lxor_spec'. reflexivity. Qed.
Lemma u16_amount (n : int) : phi (PrimInt63.land n 15%uint63) = phi n mod 16.
Proof. rewrite (phi_land_ones n 15%uint63 4) by (lia || reflexivity). reflexivity. Qed.
Theorem u16_shl_spec (a n : int) : phi (u16_shl a n) = (phi a * 2 ^ (phi n mod 16)) mod 2 ^ 16.
Proof.
  unfold u16_shl. rewrite u16_of_spec, Uint63.lsl_spec, wB_eq, mod_W by lia. rewrite u16_of_spec, u16_amount.
  rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.
Theorem u16_shr_spec (a n : int) : phi (u16_shr a n) = phi a / 2 ^ (phi n mod 16).
Proof. unfold u16_shr. rewrite Uint63.lsr_spec, u16_amount. reflexivity. Qed.
Theorem u16_div_spec (a b : int) : phi (u16_div a b) = phi a / phi b.
Proof. exact (Uint63.div_spec a b). Qed.
Theorem u16_mod_spec (a b : int) : phi (u16_mod a b) = phi a mod phi b.
Proof. exact (Uint63.mod_spec a b). Qed.
Theorem u16_ltb_spec (a b : int) : u16_ltb a b = (phi a <? phi b).
Proof. unfold u16_ltb. destruct (Uint63.ltbP a b) as [L | L]; symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia. Qed.
Theorem u16_leb_spec (a b : int) : u16_leb a b = (phi a <=? phi b).
Proof. unfold u16_leb. destruct (Uint63.lebP a b) as [L | L]; symmetry; [apply Z.leb_le | apply Z.leb_gt]; lia. Qed.
Theorem i16_add_spec (a b : int) : Z_ (i16_add a b) = sw 16 (Z_ a + Z_ b).
Proof.
  unfold i16_add. rewrite i16_of_spec, Uint63.add_spec, wB_eq, !phi_Z.
  rewrite <- Z.add_mod by lia. apply sw_mod. lia.
Qed.
Theorem i16_sub_spec (a b : int) : Z_ (i16_sub a b) = sw 16 (Z_ a - Z_ b).
Proof.
  unfold i16_sub. rewrite i16_of_spec, Uint63.sub_spec, wB_eq, !phi_Z.
  rewrite <- Zminus_mod. apply sw_mod. lia.
Qed.
Theorem i16_mul_spec (a b : int) : Z_ (i16_mul a b) = sw 16 (Z_ a * Z_ b).
Proof.
  unfold i16_mul. rewrite i16_of_spec, Uint63.mul_spec, wB_eq, !phi_Z.
  rewrite <- Z.mul_mod by lia. apply sw_mod. lia.
Qed.
Theorem i16_not_spec (a : int) : Z_ (i16_not a) = sw 16 (65535 - Z_ a).
Proof.
  unfold i16_not. rewrite i16_of_spec, Uint63.sub_spec, wB_eq, !phi_Z.
  change (Z_ 65535%sint63) with 65535.
  rewrite <- Zminus_mod. apply sw_mod. lia.
Qed.
Theorem i16_and_spec (a b : int) : Z_ (i16_and a b) = sw 16 (Z.land (phi a) (phi b)).
Proof. unfold i16_and. rewrite i16_of_spec, Uint63.land_spec'. reflexivity. Qed.
Theorem i16_or_spec (a b : int) : Z_ (i16_or a b) = sw 16 (Z.lor (phi a) (phi b)).
Proof. unfold i16_or. rewrite i16_of_spec, Uint63.lor_spec'. reflexivity. Qed.
Theorem i16_xor_spec (a b : int) : Z_ (i16_xor a b) = sw 16 (Z.lxor (phi a) (phi b)).
Proof. unfold i16_xor. rewrite i16_of_spec, Uint63.lxor_spec'. reflexivity. Qed.
Theorem i16_shl_spec (a n : int) : Z_ (i16_shl a n) = sw 16 (phi a * 2 ^ (phi n mod 16)).
Proof.
  unfold i16_shl. rewrite i16_of_spec, Uint63.lsl_spec, wB_eq, u16_of_spec, u16_amount, sw_mod by lia.
  unfold sw. f_equal. rewrite Z.add_mod by lia. rewrite Z.mul_mod_idemp_l by lia.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Theorem i16_shr_spec (a n : int) : Z_ (i16_shr a n) = Z_ a / 2 ^ (phi n mod 16).
Proof.
  unfold i16_shr. rewrite Sint63.asr_spec, (Z_small (PrimInt63.land n 15%uint63)), u16_amount; [reflexivity | ].
  rewrite u16_amount. assert (0 <= phi n mod 16 < 16) by (apply Z.mod_pos_bound; lia). lia.
Qed.
Theorem i16_div_spec (a b : int) : Z_ (i16_div a b) = sw 16 (Z.quot (Z_ a) (Z_ b)).
Proof.
  unfold i16_div. destruct (Uint63.eqbP b (-1)%sint63) as [E | E].
  - apply Uint63.to_Z_inj in E. subst b. rewrite i16_of_spec, Uint63.sub_spec, wB_eq, !phi_Z.
    change (Z_ 0%sint63) with 0. change (Z_ (-1)%sint63) with (-1).
    rewrite <- Zminus_mod. rewrite sw_mod by lia.
    f_equal. change (Z.quot (Z_ a) (-1)) with (Z.quot (Z_ a) (Z.opp 1)). rewrite Z.quot_opp_r by lia. rewrite Z.quot_1_r. lia.
  - assert (N : Z_ a <> Z_ Sint63.min_int \/ Z_ b <> (-1)).
    { right. intro C. apply E. f_equal. apply Sint63.to_Z_inj. rewrite C. reflexivity. }
    rewrite i16_of_spec, phi_Z.
    rewrite sw_mod by lia. f_equal. apply Sint63.div_spec. exact N.
Qed.
Theorem i16_mod_spec (a b : int) : Z_ (i16_mod a b) = sw 16 (Z.rem (Z_ a) (Z_ b)).
Proof.
  unfold i16_mod. destruct (Uint63.eqbP b (-1)%sint63) as [E | E].
  - apply Uint63.to_Z_inj in E. subst b.
    change (Z_ (-1)%sint63) with (Z.opp 1). rewrite Z.rem_opp_r by lia. rewrite Z.rem_1_r. reflexivity.
  - rewrite i16_of_spec, phi_Z.
    rewrite sw_mod by lia. f_equal. apply Sint63.mod_spec.
Qed.
Theorem i16_ltb_spec (a b : int) : i16_ltb a b = (Z_ a <? Z_ b).
Proof. unfold i16_ltb. destruct (Sint63.ltbP a b) as [L | L]; symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia. Qed.
Theorem i16_leb_spec (a b : int) : i16_leb a b = (Z_ a <=? Z_ b).
Proof. unfold i16_leb. destruct (Sint63.lebP a b) as [L | L]; symmetry; [apply Z.leb_le | apply Z.leb_gt]; lia. Qed.

(* ---- 32 bits *)
Theorem u32_of_spec (x : int) : phi (u32_of x) = phi x mod 2 ^ 32.
Proof. unfold u32_of. apply phi_land_ones; [lia | reflexivity]. Qed.
Theorem i32_of_spec (x : int) : Z_ (i32_of x) = sw 32 (phi x).
Proof. unfold i32_of. apply (sw_cut 32); try lia; reflexivity. Qed.
Theorem u32_add_spec (a b : int) : phi (u32_add a b) = (phi a + phi b) mod 2 ^ 32.
Proof. unfold u32_add. rewrite u32_of_spec, Uint63.add_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u32_sub_spec (a b : int) : phi (u32_sub a b) = (phi a - phi b) mod 2 ^ 32.
Proof. unfold u32_sub. rewrite u32_of_spec, Uint63.sub_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u32_mul_spec (a b : int) : phi (u32_mul a b) = (phi a * phi b) mod 2 ^ 32.
Proof. unfold u32_mul. rewrite u32_of_spec, Uint63.mul_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u32_not_spec (a : int) : phi (u32_not a) = (4294967295 - phi a) mod 2 ^ 32.
Proof. unfold u32_not. rewrite u32_of_spec, Uint63.sub_spec, wB_eq, mod_W by lia. reflexivity. Qed.
Theorem u32_and_spec (a b : int) : phi (u32_and a b) = Z.land (phi a) (phi b) mod 2 ^ 32.
Proof. unfold u32_and. rewrite u32_of_spec, Uint63.land_spec'. reflexivity. Qed.
Theorem u32_or_spec (a b : int) : phi (u32_or a b) = Z.lor (phi a) (phi b) mod 2 ^ 32.
Proof. unfold u32_or. rewrite u32_of_spec, Uint63.lor_spec'. reflexivity. Qed.
Theorem u32_xor_spec (a b : int) : phi (u32_xor a b) = Z.lxor (phi a) (phi b) mod 2 ^ 32.
Proof. unfold u32_xor. rewrite u32_of_spec, Uint63.lxor_spec'. reflexivity. Qed.
Lemma u32_amount (n : int) : phi (PrimInt63.land n 31%uint63) = phi n mod 32.
Proof. rewrite (phi_land_ones n 31%uint63 5) by (lia || reflexivity). reflexivity. Qed.
Theorem u32_shl_spec (a n : int) : phi (u32_shl a n) = (phi a * 2 ^ (phi n mod 32)) mod 2 ^ 32.
Proof.
  unfold u32_shl. rewrite u32_of_spec, Uint63.lsl_spec, wB_eq, mod_W by lia. rewrite u32_of_spec, u32_amount.
  rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.
Theorem u32_shr_spec (a n : int) : phi (u32_shr a n) = phi a / 2 ^ (phi n mod 32).
Proof. unfold u32_shr. rewrite Uint63.lsr_spec, u32_amount. reflexivity. Qed.
Theorem u32_div_spec (a b : int) : phi (u32_div a b) = phi a / phi b.
Proof. exact (Uint63.div_spec a b). Qed.
Theorem u32_mod_spec (a b : int) : phi (u32_mod a b) = phi a mod phi b.
Proof. exact (Uint63.mod_spec a b). Qed.
Theorem u32_ltb_spec (a b : int) : u32_ltb a b = (phi a <? phi b).
Proof. unfold u32_ltb. destruct (Uint63.ltbP a b) as [L | L]; symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia. Qed.
Theorem u32_leb_spec (a b : int) : u32_leb a b = (phi a <=? phi b).
Proof. unfold u32_leb. destruct (Uint63.lebP a b) as [L | L]; symmetry; [apply Z.leb_le | apply Z.leb_gt]; lia. Qed.
Theorem i32_add_spec (a b : int) : Z_ (i32_add a b) = sw 32 (Z_ a + Z_ b).
Proof.
  unfold i32_add. rewrite i32_of_spec, Uint63.add_spec, wB_eq, !phi_Z.
  rewrite <- Z.add_mod by lia. apply sw_mod. lia.
Qed.
Theorem i32_sub_spec (a b : int) : Z_ (i32_sub a b) = sw 32 (Z_ a - Z_ b).
Proof.
  unfold i32_sub. rewrite i32_of_spec, Uint63.sub_spec, wB_eq, !phi_Z.
  rewrite <- Zminus_mod. apply sw_mod. lia.
Qed.
Theorem i32_mul_spec (a b : int) : Z_ (i32_mul a b) = sw 32 (Z_ a * Z_ b).
Proof.
  unfold i32_mul. rewrite i32_of_spec, Uint63.mul_spec, wB_eq, !phi_Z.
  rewrite <- Z.mul_mod by lia. apply sw_mod. lia.
Qed.
Theorem i32_not_spec (a : int) : Z_ (i32_not a) = sw 32 (4294967295 - Z_ a).
Proof.
  unfold i32_not. rewrite i32_of_spec, Uint63.sub_spec, wB_eq, !phi_Z.
  change (Z_ 4294967295%sint63) with 4294967295.
  rewrite <- Zminus_mod. apply sw_mod. lia.
Qed.
Theorem i32_and_spec (a b : int) : Z_ (i32_and a b) = sw 32 (Z.land (phi a) (phi b)).
Proof. unfold i32_and. rewrite i32_of_spec, Uint63.land_spec'. reflexivity. Qed.
Theorem i32_or_spec (a b : int) : Z_ (i32_or a b) = sw 32 (Z.lor (phi a) (phi b)).
Proof. unfold i32_or. rewrite i32_of_spec, Uint63.lor_spec'. reflexivity. Qed.
Theorem i32_xor_spec (a b : int) : Z_ (i32_xor a b) = sw 32 (Z.lxor (phi a) (phi b)).
Proof. unfold i32_xor. rewrite i32_of_spec, Uint63.lxor_spec'. reflexivity. Qed.
Theorem i32_shl_spec (a n : int) : Z_ (i32_shl a n) = sw 32 (phi a * 2 ^ (phi n mod 32)).
Proof.
  unfold i32_shl. rewrite i32_of_spec, Uint63.lsl_spec, wB_eq, u32_of_spec, u32_amount, sw_mod by lia.
  unfold sw. f_equal. rewrite Z.add_mod by lia. rewrite Z.mul_mod_idemp_l by lia.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Theorem i32_shr_spec (a n : int) : Z_ (i32_shr a n) = Z_ a / 2 ^ (phi n mod 32).
Proof.
  unfold i32_shr. rewrite Sint63.asr_spec, (Z_small (PrimInt63.land n 31%uint63)), u32_amount; [reflexivity | ].
  rewrite u32_amount. assert (0 <= phi n mod 32 < 32) by (apply Z.mod_pos_bound; lia). lia.
Qed.
Theorem i32_div_spec (a b : int) : Z_ (i32_div a b) = sw 32 (Z.quot (Z_ a) (Z_ b)).
Proof.
  unfold i32_div. destruct (Uint63.eqbP b (-1)%sint63) as [E | E].
  - apply Uint63.to_Z_inj in E. subst b. rewrite i32_of_spec, Uint63.sub_spec, wB_eq, !phi_Z.
    change (Z_ 0%sint63) with 0. change (Z_ (-1)%sint63) with (-1).
    rewrite <- Zminus_mod. rewrite sw_mod by lia.
    f_equal. change (Z.quot (Z_ a) (-1)) with (Z.quot (Z_ a) (Z.opp 1)). rewrite Z.quot_opp_r by lia. rewrite Z.quot_1_r. lia.
  - assert (N : Z_ a <> Z_ Sint63.min_int \/ Z_ b <> (-1)).
    { right. intro C. apply E. f_equal. apply Sint63.to_Z_inj. rewrite C. reflexivity. }
    rewrite i32_of_spec, phi_Z.
    rewrite sw_mod by lia. f_equal. apply Sint63.div_spec. exact N.
Qed.
Theorem i32_mod_spec (a b : int) : Z_ (i32_mod a b) = sw 32 (Z.rem (Z_ a) (Z_ b)).
Proof.
  unfold i32_mod. destruct (Uint63.eqbP b (-1)%sint63) as [E | E].
  - apply Uint63.to_Z_inj in E. subst b.
    change (Z_ (-1)%sint63) with (Z.opp 1). rewrite Z.rem_opp_r by lia. rewrite Z.rem_1_r. reflexivity.
  - rewrite i32_of_spec, phi_Z.
    rewrite sw_mod by lia. f_equal. apply Sint63.mod_spec.
Qed.
Theorem i32_ltb_spec (a b : int) : i32_ltb a b = (Z_ a <? Z_ b).
Proof. unfold i32_ltb. destruct (Sint63.ltbP a b) as [L | L]; symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia. Qed.
Theorem i32_leb_spec (a b : int) : i32_leb a b = (Z_ a <=? Z_ b).
Proof. unfold i32_leb. destruct (Sint63.lebP a b) as [L | L]; symmetry; [apply Z.leb_le | apply Z.leb_gt]; lia. Qed.

(* ---- 64 bits *)
Notation V := u64_val.
Lemma V_bounds (a : u64) : 0 <= V a < 2 ^ 64.
Proof.
  unfold u64_val. pose proof (phi_bounds (w_lo a)).
  assert (0 <= phi (w_hi a) mod 2 < 2) by (apply Z.mod_pos_bound; lia). lia.
Qed.
Lemma V_of_Z (z : Z) : V (u64_of_Z z) = z mod 2 ^ 64.
Proof.
  unfold u64_val, u64_of_Z. cbn [w_lo w_hi]. rewrite !Uint63.of_Z_spec, wB_eq.
  rewrite <- (mod_pow 63 64 z) by lia.
  set (Y := z mod 2 ^ 64).
  assert (Yb : 0 <= Y < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (Qb : 0 <= Y / 2 ^ 63 < 2).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small (Y mod 2 ^ 63)) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small (Y / 2 ^ 63) (2 ^ 63)) by lia.
  rewrite (Z.mod_small (Y / 2 ^ 63) 2) by lia.
  pose proof (Z.div_mod Y (2 ^ 63) ltac:(lia)). lia.
Qed.
Lemma V_mk (n : int) : V (mk_u64 n 0%uint63) = phi n.
Proof. unfold u64_val. cbn [w_lo w_hi]. change (phi 0%uint63) with 0. change (0 mod 2) with 0. lia. Qed.
Theorem u64_add_spec (a b : u64) : V (u64_add a b) = (V a + V b) mod 2 ^ 64.
Proof. unfold u64_add. rewrite w64_op_unfold, V_of_Z. reflexivity. Qed.
Theorem u64_sub_spec (a b : u64) : V (u64_sub a b) = (V a - V b) mod 2 ^ 64.
Proof. unfold u64_sub. rewrite w64_op_unfold, V_of_Z. reflexivity. Qed.
Theorem u64_mul_spec (a b : u64) : V (u64_mul a b) = (V a * V b) mod 2 ^ 64.
Proof. unfold u64_mul. rewrite w64_op_unfold, V_of_Z. reflexivity. Qed.
Theorem u64_and_spec (a b : u64) : V (u64_and a b) = Z.land (V a) (V b) mod 2 ^ 64.
Proof. unfold u64_and. rewrite w64_op_unfold, V_of_Z. reflexivity. Qed.
Theorem u64_or_spec (a b : u64) : V (u64_or a b) = Z.lor (V a) (V b) mod 2 ^ 64.
Proof. unfold u64_or. rewrite w64_op_unfold, V_of_Z. reflexivity. Qed.
Theorem u64_shl_spec (a : u64) (n : int) : V (u64_shl a n) = (V a * 2 ^ (phi n mod 64)) mod 2 ^ 64.
Proof.
  unfold u64_shl. rewrite w64_op_unfold, V_of_Z. cbn [w64_z]. rewrite V_mk.
  rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.
Lemma div_pow_lt (x k : Z) : 0 <= k -> 0 <= x < 2 ^ 64 -> 0 <= x / 2 ^ k < 2 ^ 64.
Proof.
  intros K X. assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia].
Qed.
Theorem u64_shr_spec (a : u64) (n : int) : V (u64_shr a n) = V a / 2 ^ (phi n mod 64).
Proof.
  unfold u64_shr. rewrite w64_op_unfold, V_of_Z. cbn [w64_z]. rewrite V_mk.
  assert (K : 0 <= phi n mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  rewrite Z.shiftr_div_pow2 by lia. apply Z.mod_small. apply div_pow_lt; [lia | apply V_bounds].
Qed.
Theorem u64_ltb_spec (a b : u64) : u64_ltb a b = (V a <? V b).
Proof. unfold u64_ltb. rewrite w64_op_unfold. cbn [w64_z]. destruct (V a <? V b); reflexivity. Qed.
Theorem u64_leb_spec (a b : u64) : u64_leb a b = (V a <=? V b).
Proof. unfold u64_leb. rewrite w64_op_unfold. cbn [w64_z]. destruct (V a <=? V b); reflexivity. Qed.
Theorem u64_eqb_spec (a b : u64) : u64_eqb a b = (V a =? V b).
Proof. unfold u64_eqb. rewrite w64_op_unfold. cbn [w64_z]. destruct (V a =? V b); reflexivity. Qed.
Lemma top_spec (r : u64) : u64_top r = (2 ^ 63 <=? V r).
Proof.
  unfold u64_top. pose proof (phi_bounds (w_lo r)) as L.
  assert (Hb : 0 <= phi (w_hi r) mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  assert (E : phi (PrimInt63.land (w_hi r) 1%uint63) = phi (w_hi r) mod 2).
  { rewrite (phi_land_ones (w_hi r) 1%uint63 1) by (lia || reflexivity). reflexivity. }
  unfold u64_val.
  destruct (Uint63.eqbP (PrimInt63.land (w_hi r) 1%uint63) 1%uint63) as [Q | Q]; rewrite E in Q; change (phi 1%uint63) with 1 in Q.
  - symmetry. apply Z.leb_le. lia.
  - symmetry. apply Z.leb_gt. lia.
Qed.
(* the parts of a sum of two numbers one above the other do not overlap *)
Lemma lor_disjoint (a b k : Z) : 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b -> Z.lor a (b * 2 ^ k) = a + b * 2 ^ k.
Proof.
  intros K A B. rewrite <- Z.shiftl_mul_pow2 by exact K.
  assert (D : Z.land a (Z.shiftl b k) = 0).
  { apply Z.bits_inj_0. intro n. rewrite Z.land_spec.
    destruct (Z.lt_ge_cases n k) as [L | G].
    - rewrite Z.shiftl_spec_low by exact L. apply Bool.andb_false_r.
    - assert (T : Z.testbit a n = false).
      { rewrite <- (Z.mod_small a (2 ^ k)) by exact A.
        destruct (Z.lt_ge_cases n 0) as [N | N].
        - apply Z.testbit_neg_r. exact N.
        - apply Z.mod_pow2_bits_high. split; lia. }
      rewrite T. reflexivity. }
  pose proof (Z.add_lor_land a (Z.shiftl b k)) as E. rewrite D in E. lia.
Qed.
Lemma V_zero : V (mk_u64 0 0) = 0.
Proof. apply V_mk. Qed.
Theorem u64_divu_spec (a b : u64) : V (u64_divu a b) = V a / V b.
Proof.
  unfold u64_divu. rewrite w64_op_unfold, V_of_Z. cbn [w64_z]. pose proof (V_bounds a) as A. pose proof (V_bounds b) as B.
  apply Z.mod_small. destruct (Z.eq_dec (V b) 0) as [Z0 | Z0].
  - rewrite Z0, Zdiv_0_r. lia.
  - split; [apply Z.div_pos; lia | ]. apply Z.le_lt_trans with (V a); [ | lia].
    apply Z.div_le_upper_bound; nia.
Qed.
Theorem u64_modu_spec (a b : u64) : V (u64_modu a b) = V a mod V b.
Proof.
  unfold u64_modu. rewrite w64_op_unfold, V_of_Z. cbn [w64_z]. pose proof (V_bounds a) as A. pose proof (V_bounds b) as B.
  apply Z.mod_small. destruct (Z.eq_dec (V b) 0) as [Z0 | Z0].
  - rewrite Z0, Zmod_0_r. exact A.
  - pose proof (Z.mod_pos_bound (V a) (V b) ltac:(lia)). lia.
Qed.

(* ---- the halves; the high half of a product *)
Lemma lo32_V (a : u64) : phi (u64_lo32 a) = V a mod 2 ^ 32.
Proof.
  unfold u64_lo32. rewrite (phi_land_ones (w_lo a) 4294967295%uint63 32) by (lia || reflexivity).
  unfold u64_val. replace (2 ^ 63 * (phi (w_hi a) mod 2)) with ((phi (w_hi a) mod 2) * 2147483648 * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma hi32_V (a : u64) : phi (u64_hi32 a) = V a / 2 ^ 32.
Proof.
  unfold u64_hi32. pose proof (phi_bounds (w_lo a)) as L.
  assert (E1 : phi (PrimInt63.land (w_hi a) 1%uint63) = phi (w_hi a) mod 2).
  { rewrite (phi_land_ones (w_hi a) 1%uint63 1) by (lia || reflexivity). reflexivity. }
  assert (B : 0 <= phi (w_hi a) mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  rewrite Uint63.lor_spec', Uint63.lsr_spec, Uint63.lsl_spec, E1, wB_eq.
  change (phi 32%uint63) with 32. change (phi 31%uint63) with 31.
  assert (Q : 0 <= phi (w_lo a) / 2 ^ 32 < 2 ^ 31).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite Z.mod_small by lia. rewrite lor_disjoint by lia.
  unfold u64_val. replace (2 ^ 63 * (phi (w_hi a) mod 2)) with ((phi (w_hi a) mod 2) * 2147483648 * 2 ^ 32) by lia.
  rewrite Z.div_add by lia. lia.
Qed.
Lemma mul32 (x y : Z) : 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 0 <= x * y <= 18446744065119617025.
Proof.
  intros X Y. split; [nia | ].
  assert (x <= 4294967295) by lia. assert (y <= 4294967295) by lia.
  apply Z.le_trans with (4294967295 * 4294967295); [apply Z.mul_le_mono_nonneg; lia | lia].
Qed.
(* the product of two numbers of two halves of 32 bits, and the carries *)
Lemma mulhi_Z (x y al ah bl bh : Z) :
  x = ah * 2 ^ 32 + al -> y = bh * 2 ^ 32 + bl -> 0 <= al < 2 ^ 32 -> 0 <= ah < 2 ^ 32 -> 0 <= bl < 2 ^ 32 -> 0 <= bh < 2 ^ 32 ->
  let t := al * bl in
  let m1 := ah * bl + t / 2 ^ 32 in
  let m2 := al * bh + m1 mod 2 ^ 32 in
  x * y / 2 ^ 64 = ah * bh + m1 / 2 ^ 32 + m2 / 2 ^ 32 /\
  0 <= t < 2 ^ 64 /\ 0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= ah * bh + m1 / 2 ^ 32 + m2 / 2 ^ 32 < 2 ^ 64.
Proof.
  intros Ex Ey Al Ah Bl Bh t m1 m2.
  assert (Et : t = al * bl) by reflexivity. assert (E1 : m1 = ah * bl + t / 2 ^ 32) by reflexivity.
  assert (E2 : m2 = al * bh + m1 mod 2 ^ 32) by reflexivity. clearbody t m1 m2.
  assert (Pt : 0 <= t <= 18446744065119617025) by (rewrite Et; apply mul32; lia).
  assert (Tq : 0 <= t / 2 ^ 32 <= 4294967295).
  { split; [apply Z.div_pos; lia | ]. assert (t / 2 ^ 32 < 2 ^ 32) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Pq : 0 <= ah * bl <= 18446744065119617025) by (apply mul32; lia).
  assert (Pw : 0 <= al * bh <= 18446744065119617025) by (apply mul32; lia).
  assert (Pp : 0 <= ah * bh <= 18446744065119617025) by (apply mul32; lia).
  assert (Mb : 0 <= m1 <= 18446744069414584320) by lia.
  assert (Mm : 0 <= m1 mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Nb : 0 <= m2 <= 18446744069414584320) by lia.
  assert (M1q : 0 <= m1 / 2 ^ 32 <= 4294967295).
  { split; [apply Z.div_pos; lia | ]. assert (m1 / 2 ^ 32 < 2 ^ 32) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (M2q : 0 <= m2 / 2 ^ 32 <= 4294967295).
  { split; [apply Z.div_pos; lia | ]. assert (m2 / 2 ^ 32 < 2 ^ 32) by (apply Z.div_lt_upper_bound; lia). lia. }
  pose proof (Z.div_mod t (2 ^ 32) ltac:(lia)) as Dt. pose proof (Z.div_mod m1 (2 ^ 32) ltac:(lia)) as D1.
  pose proof (Z.div_mod m2 (2 ^ 32) ltac:(lia)) as D2.
  assert (Rt : 0 <= t mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (R2 : 0 <= m2 mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (XY : x * y = (ah * bh) * 2 ^ 64 + (ah * bl) * 2 ^ 32 + (al * bh) * 2 ^ 32 + t) by (rewrite Ex, Ey, Et; ring).
  assert (Hi : 0 <= ah * bh + m1 / 2 ^ 32 + m2 / 2 ^ 32 < 2 ^ 64).
  { (* the whole product is below 2^64 * 2^64 *)
    assert (Xb : 0 <= x < 2 ^ 64) by lia. assert (Yb : 0 <= y < 2 ^ 64) by lia.
    assert (Whole : x * y = (ah * bh + m1 / 2 ^ 32 + m2 / 2 ^ 32) * 2 ^ 64 + (m2 mod 2 ^ 32 * 2 ^ 32 + t mod 2 ^ 32)).
    { lia. }
    assert (Xy : x * y < 2 ^ 64 * 2 ^ 64) by nia. split; [lia | ].
    destruct (Z.lt_ge_cases (ah * bh + m1 / 2 ^ 32 + m2 / 2 ^ 32) (2 ^ 64)) as [Lt | Ge]; [exact Lt | exfalso].
    assert (Rr : 0 <= m2 mod 2 ^ 32 * 2 ^ 32 + t mod 2 ^ 32) by lia. lia. }
  repeat split; try lia.
  symmetry. apply Z.div_unique_pos with (r := m2 mod 2 ^ 32 * 2 ^ 32 + t mod 2 ^ 32); [lia | ].
  lia.
Qed.
Lemma mod64_small (z : Z) : 0 <= z < 2 ^ 64 -> z mod 2 ^ 64 = z.
Proof. apply Z.mod_small. Qed.
Theorem u64_mulhi_spec (a b : u64) : V (u64_mulhi a b) = V a * V b / 2 ^ 64.
Proof.
  unfold u64_mulhi. cbv zeta.
  pose proof (V_bounds a) as Ab. pose proof (V_bounds b) as Bb.
  assert (Al : V (mk_u64 (u64_lo32 a) 0) = V a mod 2 ^ 32) by (rewrite V_mk; apply lo32_V).
  assert (Ah : V (mk_u64 (u64_hi32 a) 0) = V a / 2 ^ 32) by (rewrite V_mk; apply hi32_V).
  assert (Bl : V (mk_u64 (u64_lo32 b) 0) = V b mod 2 ^ 32) by (rewrite V_mk; apply lo32_V).
  assert (Bh : V (mk_u64 (u64_hi32 b) 0) = V b / 2 ^ 32) by (rewrite V_mk; apply hi32_V).
  pose proof (Z.div_mod (V a) (2 ^ 32) ltac:(lia)) as Ea. pose proof (Z.div_mod (V b) (2 ^ 32) ltac:(lia)) as Eb.
  assert (Alb : 0 <= V a mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Blb : 0 <= V b mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Ahb : 0 <= V a / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Bhb : 0 <= V b / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (mulhi_Z (V a) (V b) (V a mod 2 ^ 32) (V a / 2 ^ 32) (V b mod 2 ^ 32) (V b / 2 ^ 32)) as [Eq [Bt [B1 [B2 Bh2]]]];
    try lia.
  cbv zeta in Eq, Bt, B1, B2, Bh2.
  set (AL := mk_u64 (u64_lo32 a) 0) in *. set (AH := mk_u64 (u64_hi32 a) 0) in *.
  set (BL := mk_u64 (u64_lo32 b) 0) in *. set (BH := mk_u64 (u64_hi32 b) 0) in *.
  assert (S32 : forall u, V (u64_shr u 32) = V u / 2 ^ 32).
  { intro u. rewrite u64_shr_spec. reflexivity. }
  assert (Vt : V (u64_mul AL BL) = V a mod 2 ^ 32 * (V b mod 2 ^ 32)).
  { rewrite u64_mul_spec, Al, Bl. apply mod64_small. lia. }
  assert (Pab : 0 <= V a / 2 ^ 32 * (V b mod 2 ^ 32) <= 18446744065119617025) by (apply mul32; lia).
  assert (Pcd : 0 <= V a mod 2 ^ 32 * (V b / 2 ^ 32) <= 18446744065119617025) by (apply mul32; lia).
  assert (Pef : 0 <= V a / 2 ^ 32 * (V b / 2 ^ 32) <= 18446744065119617025) by (apply mul32; lia).
  assert (Vm1 : V (u64_add (u64_mul AH BL) (u64_shr (u64_mul AL BL) 32)) =
                V a / 2 ^ 32 * (V b mod 2 ^ 32) + V a mod 2 ^ 32 * (V b mod 2 ^ 32) / 2 ^ 32).
  { rewrite u64_add_spec, u64_mul_spec, S32, Vt, Ah, Bl. rewrite (mod64_small (V a / 2 ^ 32 * (V b mod 2 ^ 32))) by lia.
    apply mod64_small. lia. }
  set (M1 := u64_add (u64_mul AH BL) (u64_shr (u64_mul AL BL) 32)) in *.
  assert (Vmask : V (u64_and M1 (mk_u64 4294967295 0)) = V M1 mod 2 ^ 32).
  { rewrite u64_and_spec, V_mk. change (phi 4294967295%uint63) with (Z.ones 32).
    rewrite Z.land_ones by lia. apply mod64_small.
    assert (0 <= V M1 mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia). lia. }
  assert (Vm2 : V (u64_add (u64_mul AL BH) (u64_and M1 (mk_u64 4294967295 0))) =
                V a mod 2 ^ 32 * (V b / 2 ^ 32) + V M1 mod 2 ^ 32).
  { rewrite u64_add_spec, u64_mul_spec, Vmask, Al, Bh. rewrite (mod64_small (V a mod 2 ^ 32 * (V b / 2 ^ 32))) by lia.
    apply mod64_small. rewrite Vm1. lia. }
  set (M2 := u64_add (u64_mul AL BH) (u64_and M1 (mk_u64 4294967295 0))) in *.
  rewrite u64_add_spec, u64_add_spec, u64_mul_spec, S32, S32, Ah, Bh, Vm1, Vm2.
  rewrite (mod64_small (V a / 2 ^ 32 * (V b / 2 ^ 32))) by lia.
  rewrite Eq. rewrite Vm1.
  set (u := V a / 2 ^ 32 * (V b mod 2 ^ 32) + V a mod 2 ^ 32 * (V b mod 2 ^ 32) / 2 ^ 32) in *.
  set (w := V a mod 2 ^ 32 * (V b / 2 ^ 32) + u mod 2 ^ 32) in *.
  set (p := V a / 2 ^ 32 * (V b / 2 ^ 32)) in *.
  assert (Qa : 0 <= u / 2 ^ 32) by (apply Z.div_pos; lia).
  assert (Qb : 0 <= w / 2 ^ 32) by (apply Z.div_pos; lia).
  rewrite (Z.mod_small (p + u / 2 ^ 32)) by lia. apply Z.mod_small. lia.
Qed.

(* ---- int64_t: the bits of a u64 read in two's complement *)
Definition sv (a : u64) : Z := if V a <? 2 ^ 63 then V a else V a - 2 ^ 64.
Lemma sv_sw (a : u64) : sv a = sw 64 (V a).
Proof.
  pose proof (V_bounds a) as B. unfold sv, sw. change (64 - 1) with 63.
  destruct (Z.ltb_spec (V a) (2 ^ 63)) as [L | L].
  - rewrite Z.mod_small by lia. lia.
  - assert (E : (V a + 2 ^ 63) mod 2 ^ 64 = V a + 2 ^ 63 - 2 ^ 64).
    { symmetry. apply Z.mod_unique_pos with (q := 1); lia. }
    rewrite E. lia.
Qed.
Lemma sw_congr (x y : Z) : x mod 2 ^ 64 = y mod 2 ^ 64 -> sw 64 x = sw 64 y.
Proof.
  intro E. unfold sw. f_equal. rewrite (Z.add_mod x), (Z.add_mod y) by lia. rewrite E. reflexivity.
Qed.
Lemma sv_mod (a : u64) : sv a mod 2 ^ 64 = V a mod 2 ^ 64.
Proof.
  unfold sv. destruct (V a <? 2 ^ 63); [reflexivity | ].
  replace (V a - 2 ^ 64) with (V a + (-1) * 2 ^ 64) by lia. apply Z.mod_add. lia.
Qed.
Lemma sw_V_mod (x : Z) : sw 64 (x mod 2 ^ 64) = sw 64 x.
Proof. apply sw_congr. apply Z.mod_mod. lia. Qed.
Theorem i64_add_spec (a b : u64) : sv (i64_add a b) = sw 64 (sv a + sv b).
Proof.
  rewrite sv_sw. unfold i64_add. rewrite u64_add_spec, sw_V_mod. apply sw_congr.
  rewrite (Z.add_mod (sv a)), (Z.add_mod (V a)) by lia. rewrite !sv_mod. reflexivity.
Qed.
Theorem i64_sub_spec (a b : u64) : sv (i64_sub a b) = sw 64 (sv a - sv b).
Proof.
  rewrite sv_sw. unfold i64_sub. rewrite u64_sub_spec, sw_V_mod. apply sw_congr.
  rewrite (Zminus_mod (sv a)), (Zminus_mod (V a)). rewrite !sv_mod. reflexivity.
Qed.
Theorem i64_mul_spec (a b : u64) : sv (i64_mul a b) = sw 64 (sv a * sv b).
Proof.
  rewrite sv_sw. unfold i64_mul. rewrite u64_mul_spec, sw_V_mod. apply sw_congr.
  rewrite (Z.mul_mod (sv a)), (Z.mul_mod (V a)) by lia. rewrite !sv_mod. reflexivity.
Qed.
Lemma neg_spec (a : u64) : i64_neg a = (2 ^ 63 <=? V a).
Proof. exact (top_spec a). Qed.
Theorem i64_ltb_spec (a b : u64) : i64_ltb a b = (sv a <? sv b).
Proof.
  pose proof (V_bounds a). pose proof (V_bounds b).
  unfold i64_ltb. rewrite !neg_spec, u64_ltb_spec. unfold sv.
  destruct (Z.leb_spec (2 ^ 63) (V a)); destruct (Z.leb_spec (2 ^ 63) (V b));
  destruct (Z.ltb_spec (V a) (2 ^ 63)); destruct (Z.ltb_spec (V b) (2 ^ 63)); try lia;
  destruct (Z.ltb_spec (V a) (V b)); symmetry;
  try (apply Z.ltb_lt; lia); try (apply Z.ltb_ge; lia).
Qed.
Theorem i64_leb_spec (a b : u64) : i64_leb a b = (sv a <=? sv b).
Proof. unfold i64_leb. rewrite i64_ltb_spec, Z.leb_antisym. reflexivity. Qed.
Lemma abs_spec (a : u64) : V (i64_abs a) = Z.abs (sv a).
Proof.
  pose proof (V_bounds a) as B. unfold i64_abs. rewrite neg_spec. unfold sv.
  destruct (Z.leb_spec (2 ^ 63) (V a)) as [L | L].
  - rewrite u64_sub_spec, V_zero.
    destruct (Z.ltb_spec (V a) (2 ^ 63)) as [M | M]; [lia | ].
    rewrite Z.abs_neq by lia.
    symmetry. apply Z.mod_unique_pos with (q := (-1)%Z); lia.
  - destruct (Z.ltb_spec (V a) (2 ^ 63)) as [M | M]; [ | lia]. rewrite Z.abs_eq by lia. reflexivity.
Qed.
Lemma neg_sv (a : u64) : i64_neg a = (sv a <? 0).
Proof.
  pose proof (V_bounds a) as B. rewrite neg_spec. unfold sv.
  destruct (Z.leb_spec (2 ^ 63) (V a)) as [L | L]; destruct (Z.ltb_spec (V a) (2 ^ 63)) as [M | M]; lia.
Qed.
Lemma quot_abs (x y : Z) : Z.quot x y = if xorb (x <? 0) (y <? 0) then - (Z.abs x / Z.abs y) else Z.abs x / Z.abs y.
Proof.
  destruct (Z.eq_dec y 0) as [Y0 | Y0].
  { subst y. rewrite Z.abs_0, Zdiv_0_r. destruct x; reflexivity. }
  destruct (Z.ltb_spec x 0) as [X | X]; destruct (Z.ltb_spec y 0) as [Y | Y]; cbn [xorb].
  - replace x with (- (- x)) at 1 by lia. replace y with (- (- y)) at 1 by lia.
    rewrite Z.quot_opp_l, Z.quot_opp_r by lia. rewrite Z.opp_involutive.
    rewrite Z.quot_div_nonneg by lia. rewrite Z.abs_neq, (Z.abs_neq y) by lia. reflexivity.
  - replace x with (- (- x)) at 1 by lia. rewrite Z.quot_opp_l by lia.
    rewrite Z.quot_div_nonneg by lia. rewrite Z.abs_neq, (Z.abs_eq y) by lia. reflexivity.
  - replace y with (- (- y)) at 1 by lia. rewrite Z.quot_opp_r by lia.
    rewrite Z.quot_div_nonneg by lia. rewrite Z.abs_eq, (Z.abs_neq y) by lia. reflexivity.
  - rewrite Z.quot_div_nonneg by lia. rewrite Z.abs_eq, (Z.abs_eq y) by lia. reflexivity.
Qed.
Lemma rem_abs (x y : Z) : Z.rem x y = if x <? 0 then - (Z.abs x mod Z.abs y) else Z.abs x mod Z.abs y.
Proof.
  destruct (Z.eq_dec y 0) as [Y0 | Y0].
  { subst y. destruct x; reflexivity. }
  destruct (Z.ltb_spec x 0) as [X | X]; destruct (Z.ltb_spec y 0) as [Y | Y].
  - replace x with (- (- x)) at 1 by lia. replace y with (- (- y)) at 1 by lia.
    rewrite Z.rem_opp_l, Z.rem_opp_r by lia.
    rewrite Z.rem_mod_nonneg by lia. rewrite Z.abs_neq, (Z.abs_neq y) by lia. reflexivity.
  - replace x with (- (- x)) at 1 by lia. rewrite Z.rem_opp_l by lia.
    rewrite Z.rem_mod_nonneg by lia. rewrite Z.abs_neq, (Z.abs_eq y) by lia. reflexivity.
  - replace y with (- (- y)) at 1 by lia. rewrite Z.rem_opp_r by lia.
    rewrite Z.rem_mod_nonneg by lia. rewrite Z.abs_eq, (Z.abs_neq y) by lia. reflexivity.
  - rewrite Z.rem_mod_nonneg by lia. rewrite Z.abs_eq, (Z.abs_eq y) by lia. reflexivity.
Qed.
Theorem i64_div_spec (a b : u64) : sv (i64_div a b) = sw 64 (Z.quot (sv a) (sv b)).
Proof.
  unfold i64_div. cbv zeta. rewrite quot_abs, !neg_sv. rewrite sv_sw.
  destruct (xorb (sv a <? 0) (sv b <? 0)).
  - rewrite u64_sub_spec, V_zero, sw_V_mod, u64_divu_spec, !abs_spec. f_equal.
  - rewrite u64_divu_spec, !abs_spec. reflexivity.
Qed.
Theorem i64_mod_spec (a b : u64) : sv (i64_mod a b) = sw 64 (Z.rem (sv a) (sv b)).
Proof.
  unfold i64_mod. cbv zeta. rewrite rem_abs, !neg_sv. rewrite sv_sw.
  destruct (sv a <? 0).
  - rewrite u64_sub_spec, V_zero, sw_V_mod, u64_modu_spec, !abs_spec. f_equal.
  - rewrite u64_modu_spec, !abs_spec. reflexivity.
Qed.
(* below 0 a division by a power of two rounds down, as the bits shifted do *)
Lemma div_neg (s d : Z) : s < 0 -> 0 < d -> s / d = -1 - (-1 - s) / d.
Proof.
  intros S D. pose proof (Z.div_mod (-1 - s) d ltac:(lia)) as E.
  assert (R : 0 <= (-1 - s) mod d < d) by (apply Z.mod_pos_bound; lia).
  symmetry. apply Z.div_unique_pos with (r := d - 1 - (-1 - s) mod d); [lia | ].
  set (q := (-1 - s) / d) in *. set (r := (-1 - s) mod d) in *. nia.
Qed.
Lemma V_ones : V (mk_u64 (-1) 1) = 2 ^ 64 - 1.
Proof. reflexivity. Qed.
Lemma sv_hi (x : u64) : 2 ^ 63 <= V x -> sv x = V x - 2 ^ 64.
Proof. intro L. unfold sv. destruct (Z.ltb_spec (V x) (2 ^ 63)); lia. Qed.
Lemma sv_lo (x : u64) : V x < 2 ^ 63 -> sv x = V x.
Proof. intro L. unfold sv. destruct (Z.ltb_spec (V x) (2 ^ 63)); lia. Qed.
Theorem i64_shr_spec (a : u64) (n : int) : sv (i64_shr a n) = sv a / 2 ^ (phi n mod 64).
Proof.
  pose proof (V_bounds a) as B.
  unfold i64_shr. cbv zeta. rewrite neg_spec.
  assert (K : phi (PrimInt63.land n 63%uint63) = phi n mod 64).
  { rewrite (phi_land_ones n 63%uint63 6) by (lia || reflexivity). reflexivity. }
  assert (Kb : 0 <= phi n mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (K2 : phi (PrimInt63.land n 63%uint63) mod 64 = phi n mod 64) by (rewrite K; apply Z.mod_small; lia).
  assert (Pk : 0 < 2 ^ (phi n mod 64)) by (apply Z.pow_pos_nonneg; lia).
  set (k := phi n mod 64) in *.
  destruct (Z.leb_spec (2 ^ 63) (V a)) as [L | L].
  - set (t := 2 ^ 64 - 1 - V a).
    assert (Tl : 0 <= t < 2 ^ 63) by (unfold t; lia).
    assert (Tq : 0 <= t / 2 ^ k <= t).
    { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | ]].
      rewrite <- (Z.mul_1_l t) at 1. apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Vs : V (u64_sub (mk_u64 (-1) 1) (u64_shr (u64_sub (mk_u64 (-1) 1) a) (PrimInt63.land n 63%uint63))) = 2 ^ 64 - 1 - t / 2 ^ k).
    { rewrite u64_sub_spec, u64_shr_spec, u64_sub_spec, V_ones, K2. fold t.
      rewrite (Z.mod_small t) by lia. apply Z.mod_small. lia. }
    rewrite sv_hi by (rewrite Vs; lia). rewrite Vs, sv_hi by lia.
    rewrite (div_neg (V a - 2 ^ 64) (2 ^ k)) by lia.
    replace (-1 - (V a - 2 ^ 64)) with t by (unfold t; lia). lia.
  - assert (Tq : 0 <= V a / 2 ^ k <= V a).
    { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | ]].
      rewrite <- (Z.mul_1_l (V a)) at 1. apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Vs : V (u64_shr a (PrimInt63.land n 63%uint63)) = V a / 2 ^ k) by (rewrite u64_shr_spec, K2; reflexivity).
    rewrite sv_lo by (rewrite Vs; lia). rewrite Vs, sv_lo by lia. reflexivity.
Qed.

(* ---- rotations *)
Lemma pow_split (w k : Z) : 0 <= k <= w -> 2 ^ w = 2 ^ (w - k) * 2 ^ k.
Proof. intro K. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
Lemma rot_lt (X w k : Z) : 0 < k -> k <= w -> 0 <= X < 2 ^ w -> 0 <= X / 2 ^ (w - k) < 2 ^ k.
Proof.
  intros K0 K1 B. assert (P : 0 < 2 ^ (w - k)) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | rewrite <- pow_split by lia; lia]].
Qed.
Theorem rotl32_spec (x n : int) :
  let X := phi x mod 2 ^ 32 in let k := phi n mod 32 in
  phi (rotl32 x n) = (X * 2 ^ k + X / 2 ^ (32 - k)) mod 2 ^ 32.
Proof.
  intros X k. unfold rotl32. cbv zeta.
  rewrite u32_of_spec, Uint63.lor_spec', Uint63.lsl_spec, Uint63.lsr_spec, u32_of_spec, wB_eq, u32_amount.
  fold X. fold k.
  assert (Xb : 0 <= X < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Kb : 0 <= k < 32) by (apply Z.mod_pos_bound; lia).
  assert (A : phi (PrimInt63.land (32 - PrimInt63.land n 31) 31)%sint63 = (32 - k) mod 32).
  { rewrite u32_amount. f_equal. change (32 - PrimInt63.land n 31)%sint63 with (PrimInt63.sub 32 (PrimInt63.land n 31)).
    rewrite Uint63.sub_spec, u32_amount, wB_eq. change (phi 32%uint63) with 32. apply Z.mod_small. lia. }
  rewrite A.
  destruct (Z.eq_dec k 0) as [K0 | K0].
  - rewrite K0. change ((32 - 0) mod 32) with 0. change (2 ^ 0) with 1. rewrite Z.mul_1_r, Z.div_1_r.
    rewrite (Z.mod_small X (2 ^ 63)) by lia. rewrite Z.lor_diag. change (32 - 0) with 32. rewrite (Z.div_small X (2 ^ 32)) by lia.
    rewrite Z.add_0_r. reflexivity.
  - rewrite (Z.mod_small (32 - k) 32) by lia.
    assert (Pk : 2 ^ k <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
    assert (Pp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (Sm : 0 <= X * 2 ^ k < 2 ^ 63) by nia.
    rewrite (Z.mod_small (X * 2 ^ k)) by lia.
    pose proof (rot_lt X 32 k ltac:(lia) ltac:(lia) ltac:(lia)) as R.
    rewrite Z.lor_comm, lor_disjoint by lia. rewrite Z.add_comm. reflexivity.
Qed.
Theorem rotr32_spec (x n : int) :
  let X := phi x mod 2 ^ 32 in let k := phi n mod 32 in
  phi (rotr32 x n) = (X / 2 ^ k + X * 2 ^ (32 - k)) mod 2 ^ 32.
Proof.
  intros X k. unfold rotr32. rewrite rotl32_spec. cbv zeta. fold X.
  assert (Kb : 0 <= k < 32) by (apply Z.mod_pos_bound; lia).
  assert (A : phi (32 - PrimInt63.land n 31)%sint63 mod 32 = (32 - k) mod 32).
  { change (32 - PrimInt63.land n 31)%sint63 with (PrimInt63.sub 32 (PrimInt63.land n 31)).
    rewrite Uint63.sub_spec, u32_amount, wB_eq. change (phi 32%uint63) with 32. fold k. rewrite (Z.mod_small (32 - k) (2 ^ 63)) by lia. reflexivity. }
  rewrite A. destruct (Z.eq_dec k 0) as [K0 | K0].
  - rewrite K0. change ((32 - 0) mod 32) with 0. change (32 - 0) with 32. change (2 ^ 0) with 1. rewrite Z.mul_1_r, Z.div_1_r.
    assert (Xb : 0 <= X < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    rewrite (Z.div_small X (2 ^ 32)) by lia. rewrite Z.add_0_r, Z.mod_add by lia. reflexivity.
  - rewrite (Z.mod_small (32 - k) 32) by lia. replace (32 - (32 - k)) with k by lia. rewrite Z.add_comm. reflexivity.
Qed.
Theorem rotl64_spec (x : u64) (n : int) :
  let k := phi n mod 64 in V (rotl64 x n) = (V x * 2 ^ k + V x / 2 ^ (64 - k)) mod 2 ^ 64.
Proof.
  intros k. unfold rotl64. cbv zeta. pose proof (V_bounds x) as B.
  assert (Kb : 0 <= k < 64) by (apply Z.mod_pos_bound; lia).
  assert (K1 : phi (PrimInt63.land n 63%uint63) = k).
  { rewrite (phi_land_ones n 63%uint63 6) by (lia || reflexivity). reflexivity. }
  assert (K2 : phi (PrimInt63.land (64 - PrimInt63.land n 63) 63)%sint63 = (64 - k) mod 64).
  { rewrite (phi_land_ones _ 63%uint63 6) by (lia || reflexivity). change (2 ^ 6) with 64. f_equal.
    change (64 - PrimInt63.land n 63)%sint63 with (PrimInt63.sub 64 (PrimInt63.land n 63%uint63)).
    rewrite Uint63.sub_spec, K1, wB_eq. change (phi 64%uint63) with 64. apply Z.mod_small. lia. }
  rewrite u64_or_spec, u64_shl_spec, u64_shr_spec, K1, K2. rewrite (Z.mod_small k 64) by lia.
  destruct (Z.eq_dec k 0) as [K0 | K0].
  - rewrite K0. change ((64 - 0) mod 64 mod 64) with 0. change (64 - 0) with 64. change (2 ^ 0) with 1.
    rewrite Z.mul_1_r, Z.div_1_r. rewrite (Z.mod_small (V x) (2 ^ 64)) by lia. rewrite Z.lor_diag.
    rewrite (Z.div_small (V x) (2 ^ 64)) by lia. rewrite Z.add_0_r. reflexivity.
  - rewrite (Z.mod_small (64 - k) 64) by lia. rewrite (Z.mod_small (64 - k) 64) by lia.
    pose proof (rot_lt (V x) 64 k ltac:(lia) ltac:(lia) ltac:(lia)) as R.
    assert (Pp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (Pq : 0 < 2 ^ (64 - k)) by (apply Z.pow_pos_nonneg; lia).
    assert (Sp : (V x * 2 ^ k) mod 2 ^ 64 = (V x mod 2 ^ (64 - k)) * 2 ^ k).
    { rewrite (pow_split 64 k) by lia. apply Z.mul_mod_distr_r; lia. }
    assert (Ym : 0 <= V x mod 2 ^ (64 - k)) by (apply Z.mod_pos_bound; lia).
    rewrite Sp, Z.lor_comm, lor_disjoint by lia.
    rewrite (Z.add_mod (V x * 2 ^ k)) by lia. rewrite Sp.
    rewrite (Z.mod_small (V x / 2 ^ (64 - k))) by (assert (2 ^ k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia).
    rewrite Z.add_comm. reflexivity.
Qed.
Theorem rotr64_spec (x : u64) (n : int) :
  let k := phi n mod 64 in V (rotr64 x n) = (V x / 2 ^ k + V x * 2 ^ (64 - k)) mod 2 ^ 64.
Proof.
  intros k. unfold rotr64. rewrite rotl64_spec. cbv zeta.
  assert (Kb : 0 <= k < 64) by (apply Z.mod_pos_bound; lia).
  assert (K1 : phi (PrimInt63.land n 63%uint63) = k).
  { rewrite (phi_land_ones n 63%uint63 6) by (lia || reflexivity). reflexivity. }
  assert (A : phi (64 - PrimInt63.land n 63)%sint63 mod 64 = (64 - k) mod 64).
  { change (64 - PrimInt63.land n 63)%sint63 with (PrimInt63.sub 64 (PrimInt63.land n 63%uint63)).
    rewrite Uint63.sub_spec, K1, wB_eq. change (phi 64%uint63) with 64. rewrite (Z.mod_small (64 - k) (2 ^ 63)) by lia. reflexivity. }
  rewrite A. destruct (Z.eq_dec k 0) as [K0 | K0].
  - rewrite K0. change ((64 - 0) mod 64) with 0. change (64 - 0) with 64. change (2 ^ 0) with 1. rewrite Z.mul_1_r, Z.div_1_r.
    pose proof (V_bounds x) as Xb.
    rewrite (Z.div_small (V x) (2 ^ 64)) by lia. rewrite Z.add_0_r, Z.mod_add by lia. reflexivity.
  - rewrite (Z.mod_small (64 - k) 64) by lia. replace (64 - (64 - k)) with k by lia. rewrite Z.add_comm. reflexivity.
Qed.

(* ---- bytes in the other order *)
Definition byte (z i : Z) : Z := (z / 2 ^ (8 * i)) mod 2 ^ 8.
Lemma byte_bounds (z i : Z) : 0 <= byte z i < 2 ^ 8.
Proof. apply Z.mod_pos_bound. lia. Qed.
Lemma div_mod_pow (z a b : Z) : 0 <= a -> 0 <= b -> (z mod 2 ^ (a + b)) / 2 ^ a = (z / 2 ^ a) mod 2 ^ b.
Proof.
  intros A B. assert (Pa : 0 < 2 ^ a) by (apply Z.pow_pos_nonneg; lia). assert (Pb : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (Pab : 2 ^ (a + b) = 2 ^ b * 2 ^ a) by (rewrite Z.pow_add_r by lia; ring).
  pose proof (Z.div_mod z (2 ^ (a + b)) ltac:(lia)) as D.
  assert (Rb : 0 <= z mod 2 ^ (a + b) < 2 ^ (a + b)) by (apply Z.mod_pos_bound; lia).
  set (r := z mod 2 ^ (a + b)) in *. set (q := z / 2 ^ (a + b)) in *.
  assert (Q : z / 2 ^ a = r / 2 ^ a + q * 2 ^ b).
  { rewrite D, Pab. replace (2 ^ b * 2 ^ a * q + r) with (r + (q * 2 ^ b) * 2 ^ a) by ring. apply Z.div_add. lia. }
  rewrite Q, Z.mod_add by lia. symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | rewrite Z.mul_comm, <- Pab; lia]].
Qed.
Lemma byte_lo (z i j : Z) : 0 <= i -> i < j -> byte (z mod 2 ^ (8 * j)) i = byte z i.
Proof.
  intros I J. unfold byte. replace (8 * j) with (8 * i + (8 * (j - i))) by lia.
  rewrite div_mod_pow by lia. apply mod_pow. lia.
Qed.
Lemma byte_hi (z i j : Z) : 0 <= i -> 0 <= j -> byte (z / 2 ^ (8 * j)) i = byte z (i + j).
Proof.
  intros I J. unfold byte. rewrite Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
  rewrite <- Z.pow_add_r by lia. do 2 f_equal. f_equal. lia.
Qed.
Theorem bswap16_spec (x : int) : phi (bswap16 x) = byte (phi x) 0 * 2 ^ 8 + byte (phi x) 1.
Proof.
  unfold bswap16.
  rewrite Uint63.lor_spec', Uint63.lsl_spec, wB_eq, (phi_land_ones x 255%uint63 8) by (lia || reflexivity).
  rewrite (phi_land_ones _ 255%uint63 8) by (lia || reflexivity). rewrite Uint63.lsr_spec.
  change (phi 8%uint63) with 8.
  assert (B0 := byte_bounds (phi x) 0). assert (B1 := byte_bounds (phi x) 1).
  unfold byte in *. change (2 ^ (8 * 0)) with 1 in *. change (2 ^ (8 * 1)) with (2 ^ 8) in *.
  rewrite Z.div_1_r in *. rewrite (Z.mod_small (_ * 2 ^ 8)) by lia.
  rewrite Z.lor_comm, lor_disjoint by lia. lia.
Qed.
Lemma bswap16_bound (x : int) : 0 <= phi (bswap16 x) < 2 ^ 16.
Proof. rewrite bswap16_spec. assert (B0 := byte_bounds (phi x) 0). assert (B1 := byte_bounds (phi x) 1). lia. Qed.
Theorem bswap32_spec (x : int) :
  phi (bswap32 x) = byte (phi x) 0 * 2 ^ 24 + byte (phi x) 1 * 2 ^ 16 + byte (phi x) 2 * 2 ^ 8 + byte (phi x) 3.
Proof.
  unfold bswap32. pose proof (bswap16_bound (PrimInt63.land x 65535)%uint63) as Lb.
  pose proof (bswap16_bound (PrimInt63.land (PrimInt63.lsr x 16%uint63) 65535%uint63)) as Hb.
  assert (L : phi (PrimInt63.land x 65535%uint63) = phi x mod 2 ^ (8 * 2)).
  { apply phi_land_ones; [lia | reflexivity]. }
  assert (H : phi (PrimInt63.land (PrimInt63.lsr x 16%uint63) 65535%uint63) = (phi x / 2 ^ (8 * 2)) mod 2 ^ (8 * 2)).
  { rewrite (phi_land_ones _ 65535%uint63 16) by (lia || reflexivity). rewrite Uint63.lsr_spec. reflexivity. }
  rewrite Uint63.lor_spec', Uint63.lsl_spec, wB_eq. change (phi 16%uint63) with 16.
  rewrite (Z.mod_small (_ * 2 ^ 16)) by lia.
  rewrite Z.lor_comm, lor_disjoint by lia.
  rewrite !bswap16_spec, L, H.
  rewrite !byte_lo by lia. rewrite !byte_hi by lia. change (0 + 2) with 2. change (1 + 2) with 3. lia.
Qed.
Lemma bswap32_bound (x : int) : 0 <= phi (bswap32 x) < 2 ^ 32.
Proof.
  rewrite bswap32_spec. assert (B0 := byte_bounds (phi x) 0). assert (B1 := byte_bounds (phi x) 1).
  assert (B2 := byte_bounds (phi x) 2). assert (B3 := byte_bounds (phi x) 3). lia.
Qed.
Lemma halves_V (h l : int) : phi h < 2 ^ 32 -> phi l < 2 ^ 32 -> V (u64_of_halves h l) = phi h * 2 ^ 32 + phi l.
Proof.
  intros H L. pose proof (phi_bounds h). pose proof (phi_bounds l).
  unfold u64_val, u64_of_halves. cbn [w_lo w_hi].
  rewrite Uint63.lor_spec', Uint63.lsl_spec, Uint63.lsr_spec, wB_eq.
  rewrite (phi_land_ones h 2147483647%uint63 31) by (lia || reflexivity).
  rewrite (phi_land_ones l 4294967295%uint63 32) by (lia || reflexivity).
  rewrite (phi_land_ones h 4294967295%uint63 32) by (lia || reflexivity).
  change (phi 32%uint63) with 32. change (phi 31%uint63) with 31.
  rewrite (Z.mod_small (phi l)) by lia. rewrite (Z.mod_small (phi h) (2 ^ 32)) by lia.
  assert (Lm : 0 <= phi h mod 2 ^ 31 < 2 ^ 31) by (apply Z.mod_pos_bound; lia).
  assert (Q : 0 <= phi h / 2 ^ 31 < 2) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.div_mod (phi h) (2 ^ 31) ltac:(lia)) as D.
  rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite Z.lor_comm, lor_disjoint by lia.
  rewrite (Z.mod_small (phi h / 2 ^ 31) 2) by lia. lia.
Qed.
Theorem bswap64_spec (x : u64) :
  V (bswap64 x) = byte (V x) 0 * 2 ^ 56 + byte (V x) 1 * 2 ^ 48 + byte (V x) 2 * 2 ^ 40 + byte (V x) 3 * 2 ^ 32
                + byte (V x) 4 * 2 ^ 24 + byte (V x) 5 * 2 ^ 16 + byte (V x) 6 * 2 ^ 8 + byte (V x) 7.
Proof.
  unfold bswap64. pose proof (bswap32_bound (u64_lo32 x)). pose proof (bswap32_bound (u64_hi32 x)).
  rewrite halves_V by lia. rewrite !bswap32_spec.
  rewrite lo32_V, hi32_V.
  replace (2 ^ 32) with (2 ^ (8 * 4)) by reflexivity.
  rewrite !byte_lo by lia. rewrite !byte_hi by lia.
  change (0 + 4) with 4. change (1 + 4) with 5. change (2 + 4) with 6. change (3 + 4) with 7.
  change (2 ^ (8 * 4)) with 4294967296. lia.
Qed.

(* ---- the zeros above the highest bit, below the lowest *)
Theorem clz32_zero (x : int) : phi x mod 2 ^ 32 = 0 -> phi (clz32 x) = 32.
Proof.
  intro Z0. unfold clz32. cbv zeta.
  destruct (Uint63.eqbP (u32_of x) 0%uint63) as [E | E]; [reflexivity | ].
  exfalso. apply E. rewrite u32_of_spec, Z0. reflexivity.
Qed.
Theorem clz32_spec (x : int) : 0 < phi x mod 2 ^ 32 ->
  0 <= phi (clz32 x) < 32 /\ 2 ^ 31 <= 2 ^ phi (clz32 x) * (phi x mod 2 ^ 32) < 2 ^ 32.
Proof.
  intro P. unfold clz32. cbv zeta.
  assert (Xb : 0 <= phi x mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  destruct (Uint63.eqbP (u32_of x) 0%uint63) as [E | E].
  { exfalso. rewrite u32_of_spec in E. change (phi 0%uint63) with 0 in E. lia. }
  pose proof (Uint63.head0_spec (u32_of x)) as H. rewrite u32_of_spec in H. specialize (H P).
  rewrite wB_eq in H. change (2 ^ 63 / 2) with (2 ^ 62) in H.
  set (X := phi x mod 2 ^ 32) in *. set (h := phi (PrimInt63.head0 (u32_of x))) in *.
  assert (Hb : 0 <= h) by (unfold h; pose proof (phi_bounds (PrimInt63.head0 (u32_of x))); lia).
  assert (H31 : 31 <= h).
  { destruct (Z.lt_ge_cases h 31) as [L | L]; [exfalso | exact L].
    assert (2 ^ h <= 2 ^ 30) by (apply Z.pow_le_mono_r; lia). nia. }
  assert (H62 : h <= 62).
  { destruct (Z.lt_ge_cases 62 h) as [L | L]; [exfalso | exact L].
    assert (2 ^ 63 <= 2 ^ h) by (apply Z.pow_le_mono_r; lia). nia. }
  assert (S : phi (PrimInt63.head0 (u32_of x) - 31)%sint63 = h - 31).
  { change (PrimInt63.head0 (u32_of x) - 31)%sint63 with (PrimInt63.sub (PrimInt63.head0 (u32_of x)) 31%uint63).
    rewrite Uint63.sub_spec, wB_eq. change (phi 31%uint63) with 31. apply Z.mod_small. unfold h. lia. }
  rewrite S. split; [lia | ].
  assert (Pw : 2 ^ h = 2 ^ (h - 31) * 2 ^ 31) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Pw in H. set (c := 2 ^ (h - 31) * X).
  assert (Hc : 2 ^ (h - 31) * 2 ^ 31 * X = c * 2 ^ 31) by (unfold c; ring).
  rewrite Hc in H. lia.
Qed.
Theorem ctz32_zero (x : int) : phi x mod 2 ^ 32 = 0 -> phi (ctz32 x) = 32.
Proof.
  intro Z0. unfold ctz32. cbv zeta.
  destruct (Uint63.eqbP (u32_of x) 0%uint63) as [E | E]; [reflexivity | ].
  exfalso. apply E. rewrite u32_of_spec, Z0. reflexivity.
Qed.
Theorem ctz32_spec (x : int) : 0 < phi x mod 2 ^ 32 ->
  0 <= phi (ctz32 x) < 32 /\ exists y, 0 <= y /\ phi x mod 2 ^ 32 = (2 * y + 1) * 2 ^ phi (ctz32 x).
Proof.
  intro P. unfold ctz32. cbv zeta.
  assert (Xb : 0 <= phi x mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  destruct (Uint63.eqbP (u32_of x) 0%uint63) as [E | E].
  { exfalso. rewrite u32_of_spec in E. change (phi 0%uint63) with 0 in E. lia. }
  pose proof (Uint63.tail0_spec (u32_of x)) as H. rewrite u32_of_spec in H. destruct (H P) as [y [Y Q]].
  pose proof (phi_bounds (PrimInt63.tail0 (u32_of x))) as Tb.
  split; [ | exists y; split; [exact Y | exact Q]].
  destruct (Z.lt_ge_cases (phi (PrimInt63.tail0 (u32_of x))) 32) as [L | L]; [lia | exfalso].
  assert (2 ^ 32 <= 2 ^ phi (PrimInt63.tail0 (u32_of x))) by (apply Z.pow_le_mono_r; lia). nia.
Qed.
Lemma V_split (x : u64) : V x = (V x / 2 ^ 32) * 2 ^ 32 + V x mod 2 ^ 32.
Proof. pose proof (Z.div_mod (V x) (2 ^ 32) ltac:(lia)). lia. Qed.
Theorem clz64_spec (x : u64) : 0 < V x -> 2 ^ 63 <= 2 ^ phi (clz64 x) * V x < 2 ^ 64.
Proof.
  intro P. pose proof (V_bounds x) as B. pose proof (V_split x) as S. unfold clz64.
  assert (Lb : 0 <= V x mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Hb : 0 <= V x / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (LL : phi (u64_lo32 x) mod 2 ^ 32 = V x mod 2 ^ 32) by (rewrite lo32_V; apply Z.mod_mod; lia).
  assert (HH : phi (u64_hi32 x) mod 2 ^ 32 = V x / 2 ^ 32) by (rewrite hi32_V; apply Z.mod_small; lia).
  destruct (Uint63.eqbP (u64_hi32 x) 0%uint63) as [E | E].
  - rewrite hi32_V in E. change (phi 0%uint63) with 0 in E. rewrite E in S.
    assert (Xl : 0 < phi (u64_lo32 x) mod 2 ^ 32) by (rewrite LL; lia).
    destruct (clz32_spec (u64_lo32 x) Xl) as [Cb [C1 C2]]. rewrite LL in C1, C2.
    set (c := phi (clz32 (u64_lo32 x))) in *.
    assert (Sc : phi (32 + clz32 (u64_lo32 x))%sint63 = 32 + c).
    { change (32 + clz32 (u64_lo32 x))%sint63 with (PrimInt63.add 32 (clz32 (u64_lo32 x))).
      rewrite Uint63.add_spec, wB_eq. change (phi 32%uint63) with 32. apply Z.mod_small. unfold c. lia. }
    rewrite Sc, Z.pow_add_r by lia.
    replace (V x) with (V x mod 2 ^ 32) by lia.
    set (u := 2 ^ c * (V x mod 2 ^ 32)) in *.
    replace (2 ^ 32 * 2 ^ c * (V x mod 2 ^ 32)) with (2 ^ 32 * u) by (unfold u; ring). lia.
  - assert (Xh : 0 < phi (u64_hi32 x) mod 2 ^ 32).
    { rewrite HH. assert (N : V x / 2 ^ 32 <> 0).
      { intro C. apply E. rewrite hi32_V, C. reflexivity. }
      lia. }
    destruct (clz32_spec (u64_hi32 x) Xh) as [Cb [C1 C2]]. rewrite HH in C1, C2.
    set (c := phi (clz32 (u64_hi32 x))) in *.
    set (H := V x / 2 ^ 32) in *. set (L := V x mod 2 ^ 32) in *.
    assert (Pc : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
    assert (Pl : 2 ^ c <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
    (* the multiples of 2^c below 2^32 *)
    assert (Up : 2 ^ c * H + 2 ^ c <= 2 ^ 32).
    { assert (D : 2 ^ 32 = 2 ^ (32 - c) * 2 ^ c) by (apply pow_split; lia).
      assert (Hu : H < 2 ^ (32 - c)).
      { apply Z.mul_lt_mono_pos_r with (p := 2 ^ c); [lia | ]. rewrite <- D. lia. }
      rewrite D. nia. }
    rewrite S. nia.
Qed.
Theorem ctz64_spec (x : u64) : 0 < V x -> exists y, 0 <= y /\ V x = (2 * y + 1) * 2 ^ phi (ctz64 x).
Proof.
  intro P. pose proof (V_bounds x) as B. pose proof (V_split x) as S. unfold ctz64.
  assert (Lb : 0 <= V x mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Hb : 0 <= V x / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (LL : phi (u64_lo32 x) mod 2 ^ 32 = V x mod 2 ^ 32) by (rewrite lo32_V; apply Z.mod_mod; lia).
  assert (HH : phi (u64_hi32 x) mod 2 ^ 32 = V x / 2 ^ 32) by (rewrite hi32_V; apply Z.mod_small; lia).
  destruct (Uint63.eqbP (u64_lo32 x) 0%uint63) as [E | E].
  - rewrite lo32_V in E. change (phi 0%uint63) with 0 in E. rewrite E in S.
    assert (Xh : 0 < phi (u64_hi32 x) mod 2 ^ 32) by (rewrite HH; lia).
    destruct (ctz32_spec (u64_hi32 x) Xh) as [Cb [y [Y Q]]]. rewrite HH in Q.
    set (c := phi (ctz32 (u64_hi32 x))) in *.
    assert (Sc : phi (32 + ctz32 (u64_hi32 x))%sint63 = 32 + c).
    { change (32 + ctz32 (u64_hi32 x))%sint63 with (PrimInt63.add 32 (ctz32 (u64_hi32 x))).
      rewrite Uint63.add_spec, wB_eq. change (phi 32%uint63) with 32. apply Z.mod_small. unfold c. lia. }
    exists y. split; [exact Y | ]. rewrite Sc, Z.pow_add_r by lia. transitivity (V x / 2 ^ 32 * 2 ^ 32 + 0); [exact S | ]. rewrite Q. ring.
  - assert (Xl : 0 < phi (u64_lo32 x) mod 2 ^ 32).
    { rewrite LL. assert (N : V x mod 2 ^ 32 <> 0).
      { intro C. apply E. rewrite lo32_V, C. reflexivity. }
      lia. }
    destruct (ctz32_spec (u64_lo32 x) Xl) as [Cb [y [Y Q]]]. rewrite LL in Q.
    set (c := phi (ctz32 (u64_lo32 x))) in *.
    assert (D : 2 ^ 32 = 2 ^ (32 - c) * 2 ^ c) by (apply pow_split; lia).
    assert (Ppos : 0 < 2 ^ (31 - c)) by (apply Z.pow_pos_nonneg; lia).
    assert (D2 : 2 ^ (32 - c) = 2 * 2 ^ (31 - c)).
    { replace (32 - c) with (Z.succ (31 - c)) by lia. apply Z.pow_succ_r. lia. }
    set (H := V x / 2 ^ 32) in *.
    exists (y + H * 2 ^ (31 - c)). split.
    + assert (0 <= H * 2 ^ (31 - c)) by nia. lia.
    + transitivity (H * 2 ^ 32 + V x mod 2 ^ 32); [exact S | ]. rewrite Q. rewrite D. rewrite D2. ring.
Qed.

(* ---- the bits set.  popcount32 adds in parallel, so each of its steps acts on the two halves of 16 bits apart; on 16 bits
   the steps are checked by computation, on all 65536 values, and the two halves are put together by arithmetic *)
Fixpoint pc (z : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => pc z k + (z / 2 ^ Z.of_nat k) mod 2
  end.
Lemma pc_lo (z k : Z) (n : nat) : Z.of_nat n <= k -> pc (z mod 2 ^ k) n = pc z n.
Proof.
  induction n as [ | n IH]; intro N; [reflexivity | ]. cbn [pc]. rewrite IH by lia.
  f_equal. replace k with (Z.of_nat n + (k - Z.of_nat n)) by lia.
  rewrite div_mod_pow by lia.
  assert (Z1 : 2 = 2 ^ 1) by reflexivity. rewrite Z1 at 1 3. rewrite Z1. rewrite mod_pow by lia. reflexivity.
Qed.
Lemma pc_hi (z : Z) (k n : nat) : pc z (k + n) = pc z k + pc (z / 2 ^ Z.of_nat k) n.
Proof.
  induction n as [ | n IH]; [cbn [pc]; rewrite Nat.add_0_r; lia | ].
  rewrite Nat.add_succ_r. cbn [pc]. rewrite IH.
  rewrite Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
  rewrite <- Z.pow_add_r by lia. rewrite Nat2Z.inj_add. lia.
Qed.
Lemma land_split (x m k : Z) : 0 <= k ->
  Z.land x m = Z.land (x mod 2 ^ k) (m mod 2 ^ k) + Z.land (x / 2 ^ k) (m / 2 ^ k) * 2 ^ k.
Proof.
  intro K.
  rewrite <- (Z.shiftr_div_pow2 x k), <- (Z.shiftr_div_pow2 m k) by lia. rewrite <- Z.shiftr_land, Z.shiftr_div_pow2 by lia.
  rewrite <- !Z.land_ones by lia.
  assert (E : Z.land (Z.land x (Z.ones k)) (Z.land m (Z.ones k)) = Z.land (Z.land x m) (Z.ones k)).
  { apply Z.bits_inj'. intros n N. rewrite !Z.land_spec.
    destruct (Z.testbit x n), (Z.testbit m n), (Z.testbit (Z.ones k) n); reflexivity. }
  rewrite E, Z.land_ones by lia.
  assert (P : 2 ^ k <> 0) by (apply Z.pow_nonzero; lia).
  pose proof (Z.div_mod (Z.land x m) (2 ^ k) P). lia.
Qed.
Lemma land_hi (x y m n k : Z) : 0 <= k -> 0 <= x < 2 ^ k -> 0 <= m < 2 ^ k ->
  Z.land (x + y * 2 ^ k) (m + n * 2 ^ k) = Z.land x m + Z.land y n * 2 ^ k.
Proof.
  intros K X M. assert (P : 2 ^ k <> 0) by (apply Z.pow_nonzero; lia).
  rewrite (land_split _ _ k) by exact K.
  rewrite !Z.mod_add by exact P. rewrite !Z.div_add by exact P.
  rewrite !Z.mod_small by lia. rewrite !Z.div_small by lia. reflexivity.
Qed.
Lemma land_low (w t k m : Z) : 0 <= k -> 0 <= m < 2 ^ k -> Z.land (w + t * 2 ^ k) m = Z.land w m.
Proof.
  intros K M. assert (P : 2 ^ k <> 0) by (apply Z.pow_nonzero; lia).
  rewrite (land_split (w + t * 2 ^ k) m k), (land_split w m k) by exact K.
  rewrite Z.mod_add by exact P. rewrite (Z.div_small m) by lia. rewrite !Z.land_0_r. reflexivity.
Qed.
Lemma shift_split (L H s m : Z) : 0 <= s <= 16 -> 0 <= m < 2 ^ (16 - s) -> 0 <= L < 2 ^ 16 -> 0 <= H ->
  Z.land ((L + H * 2 ^ 16) / 2 ^ s) (m + m * 2 ^ 16) = Z.land (L / 2 ^ s) m + Z.land (H / 2 ^ s) m * 2 ^ 16.
Proof.
  intros S M Lb Hb.
  assert (Ps : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia). assert (Pt : 0 < 2 ^ (16 - s)) by (apply Z.pow_pos_nonneg; lia).
  assert (Sp : 2 ^ 16 = 2 ^ (16 - s) * 2 ^ s) by (apply pow_split; lia).
  pose proof (Z.div_mod H (2 ^ s) ltac:(lia)) as D.
  assert (Rb : 0 <= H mod 2 ^ s < 2 ^ s) by (apply Z.mod_pos_bound; lia).
  assert (Q : (L + H * 2 ^ 16) / 2 ^ s = (L / 2 ^ s + (H mod 2 ^ s) * 2 ^ (16 - s)) + (H / 2 ^ s) * 2 ^ 16).
  { replace (L + H * 2 ^ 16) with (L + (H * 2 ^ (16 - s)) * 2 ^ s) by (rewrite Sp; ring).
    rewrite Z.div_add by lia. rewrite D at 1. rewrite Sp. ring. }
  assert (Lq : L / 2 ^ s < 2 ^ (16 - s)).
  { apply Z.div_lt_upper_bound; [lia | ]. rewrite Z.mul_comm, <- Sp. lia. }
  assert (Lp : 0 <= L / 2 ^ s) by (apply Z.div_pos; lia).
  assert (Low : L / 2 ^ s + (H mod 2 ^ s) * 2 ^ (16 - s) < 2 ^ 16) by nia.
  assert (Lq0 : 0 <= (H mod 2 ^ s) * 2 ^ (16 - s)) by nia.
  assert (M16 : 0 <= m < 2 ^ 16) by (split; [lia | ]; rewrite Sp; nia).
  rewrite Q, land_hi by (lia || nia).
  rewrite land_low by (lia || nia). reflexivity.
Qed.
Definition zA (m x : Z) : Z := x - Z.land (x / 2) m.
Definition zB (m x : Z) : Z := Z.land x m + Z.land (x / 4) m.
Definition zC (m x : Z) : Z := Z.land (x + x / 16) m.
Lemma zA_split (L H : Z) : 0 <= L < 2 ^ 16 -> 0 <= H < 2 ^ 16 ->
  zA 1431655765 (L + H * 2 ^ 16) = zA 21845 L + zA 21845 H * 2 ^ 16.
Proof.
  intros Lb Hb. unfold zA.
  pose proof (shift_split L H 1 21845 ltac:(lia) ltac:(lia) Lb ltac:(lia)) as E.
  change (2 ^ 1) with 2 in E. replace (21845 + 21845 * 2 ^ 16) with 1431655765 in E by reflexivity. rewrite E. lia.
Qed.
Lemma zB_split (u v : Z) : 0 <= u < 2 ^ 16 -> 0 <= v < 2 ^ 16 ->
  zB 858993459 (u + v * 2 ^ 16) = zB 13107 u + zB 13107 v * 2 ^ 16.
Proof.
  intros Ub Vb. unfold zB.
  pose proof (shift_split u v 2 13107 ltac:(lia) ltac:(lia) Ub ltac:(lia)) as E.
  change (2 ^ 2) with 4 in E. replace (13107 + 13107 * 2 ^ 16) with 858993459 in E by reflexivity. rewrite E.
  replace 858993459 with (13107 + 13107 * 2 ^ 16) at 1 by reflexivity.
  rewrite land_hi by lia. lia.
Qed.
Lemma zC_split (u v : Z) : 0 <= u <= 17476 -> 0 <= v < 2 ^ 16 -> v mod 16 <= 4 ->
  zC 252645135 (u + v * 2 ^ 16) = zC 3855 u + zC 3855 v * 2 ^ 16.
Proof.
  intros Ub Vb Vm. unfold zC. change 16 with (2 ^ 4) in Vm.
  pose proof (Z.div_mod v (2 ^ 4) ltac:(lia)) as D.
  assert (Rb : 0 <= v mod 2 ^ 4 < 2 ^ 4) by (apply Z.mod_pos_bound; lia).
  assert (Qu : 0 <= u / 16 <= 1093) by (split; [apply Z.div_pos; lia | ]; apply Z.div_le_upper_bound; lia).
  assert (Q : (u + v * 2 ^ 16) + (u + v * 2 ^ 16) / 16 =
              ((u + u / 16) + (v mod 2 ^ 4) * 2 ^ 12) + (v + v / 16) * 2 ^ 16).
  { replace (u + v * 2 ^ 16) with (u + (v * 2 ^ 12) * 16) by lia. rewrite Z.div_add by lia.
    change (2 ^ 4) with 16 in *. lia. }
  rewrite Q. replace 252645135 with (3855 + 3855 * 2 ^ 16) by reflexivity.
  rewrite land_hi by lia. rewrite land_low by lia. reflexivity.
Qed.
(* all 65536 values *)
Definition chk1 (L : Z) : bool :=
  let a := zA 21845 L in let b := zB 13107 a in let c := zC 3855 b in
  (0 <=? a) && (a <? 65536) && (0 <=? b) && (b <=? 17476) && (b mod 16 <=? 4) && (0 <=? c) && (c mod 256 <=? 8) && (c / 256 <=? 8)
  && (c mod 256 + c / 256 =? pc L 16).
Fixpoint chk (n : nat) (z : Z) : bool :=
  match n with
  | O => true
  | S k => chk1 z && chk k (z + 1)
  end.
Lemma chk_sound (n : nat) : forall z w, chk n z = true -> z <= w < z + Z.of_nat n -> chk1 w = true.
Proof.
  induction n as [ | n IH]; intros z w C R; [lia | ]. cbn [chk] in C. apply andb_prop in C. destruct C as [C1 C2].
  destruct (Z.eq_dec w z) as [E | E]; [rewrite E; exact C1 | ].
  apply (IH (z + 1)); [exact C2 | lia].
Qed.
Lemma chk_all : chk 65536 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk_at (w : Z) : 0 <= w < 2 ^ 16 ->
  let a := zA 21845 w in let b := zB 13107 a in let c := zC 3855 b in
  0 <= a < 65536 /\ 0 <= b <= 17476 /\ b mod 16 <= 4 /\ 0 <= c /\ c mod 256 <= 8 /\ c / 256 <= 8 /\ c mod 256 + c / 256 = pc w 16.
Proof.
  intros W a b c. pose proof (chk_sound 65536 0 w chk_all) as C.
  assert (T : chk1 w = true) by (apply C; change (Z.of_nat 65536) with 65536; lia).
  unfold chk1 in T. cbv zeta in T. fold a in T. fold b in T. fold c in T.
  repeat (apply andb_prop in T; destruct T as [T ?]).
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
                       | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
                       | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
  repeat split; lia.
Qed.
(* the multiplication adds the four bytes into the top one *)
Lemma sum_bytes (p0 p1 q0 q1 : Z) : 0 <= p0 <= 8 -> 0 <= p1 <= 8 -> 0 <= q0 <= 8 -> 0 <= q1 <= 8 ->
  ((((p0 + p1 * 2 ^ 8) + (q0 + q1 * 2 ^ 8) * 2 ^ 16) * 16843009) mod 2 ^ 32 / 2 ^ 24) mod 2 ^ 8 = p0 + p1 + q0 + q1.
Proof.
  intros P0 P1 Q0 Q1.
  set (S := p0 + p1 + q0 + q1). set (A := p0 + (p0 + p1) * 2 ^ 8 + (p0 + p1 + q0) * 2 ^ 16).
  set (R := p1 + q0 + q1 + (q0 + q1) * 2 ^ 8 + q1 * 2 ^ 16).
  assert (E : ((p0 + p1 * 2 ^ 8) + (q0 + q1 * 2 ^ 8) * 2 ^ 16) * 16843009 = (A + S * 2 ^ 24) + R * 2 ^ 32).
  { unfold A, S, R. ring. }
  assert (Ab : 0 <= A < 2 ^ 24) by (unfold A; lia). assert (Sb : 0 <= S <= 32) by (unfold S; lia).
  rewrite E, Z.mod_add by lia. rewrite (Z.mod_small (A + S * 2 ^ 24)) by lia. rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.
Theorem popcount32_spec (x : int) : phi (popcount32 x) = pc (phi x mod 2 ^ 32) 32.
Proof.
  unfold popcount32. cbv zeta. set (X := phi x mod 2 ^ 32).
  assert (Xb : 0 <= X < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Ux : phi (u32_of x) = X) by apply u32_of_spec.
  set (y := u32_of x) in *.
  set (L := X mod 2 ^ 16). set (H := X / 2 ^ 16).
  assert (Lb : 0 <= L < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
  assert (Hb : 0 <= H < 2 ^ 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Sx : X = L + H * 2 ^ 16) by (pose proof (Z.div_mod X (2 ^ 16) ltac:(lia)); unfold L, H; lia).
  destruct (chk_at L Lb) as [La [Lb2 [Ln [Lc [Lm [Lq Ls]]]]]]. destruct (chk_at H Hb) as [Ha [Hb2 [Hn [Hc [Hm [Hq Hs]]]]]].
  cbv zeta in *.
  set (ua := zA 21845 L) in *. set (va := zA 21845 H) in *.
  set (ub := zB 13107 ua) in *. set (vb := zB 13107 va) in *.
  set (uc := zC 3855 ub) in *. set (vc := zC 3855 vb) in *.
  (* the first step *)
  assert (Pa : phi (y - PrimInt63.land (PrimInt63.lsr y 1) 1431655765)%sint63 = ua + va * 2 ^ 16).
  { change (y - PrimInt63.land (PrimInt63.lsr y 1) 1431655765)%sint63 with
           (PrimInt63.sub y (PrimInt63.land (PrimInt63.lsr y 1%uint63) 1431655765%uint63)).
    rewrite Uint63.sub_spec, Uint63.land_spec', Uint63.lsr_spec, Ux, wB_eq.
    change (phi 1%uint63) with 1. change (2 ^ 1) with 2. change (phi 1431655765%uint63) with 1431655765.
    assert (Z1 : X - Z.land (X / 2) 1431655765 = ua + va * 2 ^ 16).
    { unfold ua, va. rewrite <- zA_split by lia. unfold zA. rewrite <- Sx. reflexivity. }
    rewrite Z1. apply Z.mod_small. lia. }
  set (a := (y - PrimInt63.land (PrimInt63.lsr y 1) 1431655765)%sint63) in *.
  (* the second *)
  assert (Pb : phi (PrimInt63.land a 858993459 + PrimInt63.land (PrimInt63.lsr a 2) 858993459)%sint63 = ub + vb * 2 ^ 16).
  { change (PrimInt63.land a 858993459 + PrimInt63.land (PrimInt63.lsr a 2) 858993459)%sint63 with
           (PrimInt63.add (PrimInt63.land a 858993459%uint63) (PrimInt63.land (PrimInt63.lsr a 2%uint63) 858993459%uint63)).
    rewrite Uint63.add_spec, !Uint63.land_spec', Uint63.lsr_spec, Pa, wB_eq.
    change (phi 2%uint63) with 2. change (2 ^ 2) with 4. change (phi 858993459%uint63) with 858993459.
    assert (Z2 : Z.land (ua + va * 2 ^ 16) 858993459 + Z.land ((ua + va * 2 ^ 16) / 4) 858993459 = ub + vb * 2 ^ 16).
    { unfold ub, vb. rewrite <- zB_split by lia. reflexivity. }
    rewrite Z2. apply Z.mod_small. lia. }
  set (b := (PrimInt63.land a 858993459 + PrimInt63.land (PrimInt63.lsr a 2) 858993459)%sint63) in *.
  (* the third *)
  assert (Pc : phi (PrimInt63.land (b + PrimInt63.lsr b 4) 252645135)%sint63 = uc + vc * 2 ^ 16).
  { change (PrimInt63.land (b + PrimInt63.lsr b 4) 252645135)%sint63 with
           (PrimInt63.land (PrimInt63.add b (PrimInt63.lsr b 4%uint63)) 252645135%uint63).
    rewrite Uint63.land_spec', Uint63.add_spec, Uint63.lsr_spec, Pb, wB_eq.
    change (phi 4%uint63) with 4. change (2 ^ 4) with 16. change (phi 252645135%uint63) with 252645135.
    assert (Q : 0 <= (ub + vb * 2 ^ 16) / 16 <= ub + vb * 2 ^ 16) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    rewrite (Z.mod_small (ub + vb * 2 ^ 16 + (ub + vb * 2 ^ 16) / 16)) by lia.
    unfold uc, vc. rewrite <- zC_split by lia. reflexivity. }
  set (c := PrimInt63.land (b + PrimInt63.lsr b 4) 252645135%sint63) in *.
  (* the last *)
  assert (Ds : pc X 32 = pc L 16 + pc H 16).
  { change 32%nat with (16 + 16)%nat. rewrite pc_hi. unfold L. rewrite pc_lo by lia. reflexivity. }
  rewrite Ds, <- Ls, <- Hs.
  rewrite (phi_land_ones _ 255%uint63 8) by (lia || reflexivity). rewrite Uint63.lsr_spec, u32_of_spec.
  change (phi 24%uint63) with 24.
  change (c * 16843009)%sint63 with (PrimInt63.mul c 16843009%uint63).
  rewrite Uint63.mul_spec, wB_eq, mod_W, Pc by lia. change (phi 16843009%uint63) with 16843009.
  pose proof (Z.div_mod uc 256 ltac:(lia)) as Du. pose proof (Z.div_mod vc 256 ltac:(lia)) as Dv.
  assert (M1 : 0 <= uc mod 256 < 256) by (apply Z.mod_pos_bound; lia). assert (M2 : 0 <= vc mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Q1 : 0 <= uc / 256) by (apply Z.div_pos; lia). assert (Q2 : 0 <= vc / 256) by (apply Z.div_pos; lia).
  pose proof (sum_bytes (uc mod 256) (uc / 256) (vc mod 256) (vc / 256)) as SB.
  replace (uc mod 256 + uc / 256 * 2 ^ 8) with uc in SB by lia. replace (vc mod 256 + vc / 256 * 2 ^ 8) with vc in SB by lia.
  rewrite SB by lia. lia.
Qed.
Theorem popcount64_spec (x : u64) : phi (popcount64 x) = pc (V x) 64.
Proof.
  unfold popcount64. change (popcount32 (u64_lo32 x) + popcount32 (u64_hi32 x))%sint63 with
    (PrimInt63.add (popcount32 (u64_lo32 x)) (popcount32 (u64_hi32 x))).
  pose proof (V_bounds x) as B.
  assert (Hb : 0 <= V x / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Uint63.add_spec, !popcount32_spec, lo32_V, hi32_V, wB_eq.
  rewrite Z.mod_mod by lia. rewrite (Z.mod_small (V x / 2 ^ 32)) by lia.
  change 64%nat with (32 + 32)%nat. rewrite pc_hi. change (Z.of_nat 32) with 32.
  rewrite pc_lo by lia.
  (* a count of 64 bits is small *)
  assert (Bd : forall z n, 0 <= pc z n <= Z.of_nat n).
  { intros z n. induction n as [ | n IH]; [cbn; lia | ]. cbn [pc].
    assert (0 <= (z / 2 ^ Z.of_nat n) mod 2 < 2) by (apply Z.mod_pos_bound; lia). lia. }
  pose proof (Bd (V x) 32%nat). pose proof (Bd (V x / 2 ^ 32) 32%nat). change (Z.of_nat 32) with 32 in *.
  apply Z.mod_small. lia.
Qed.

(* every theorem above, for the gate's look at what they rest on (proved/make.sh) *)
Definition cint_all := (u8_of_spec,
  i8_of_spec,
  u8_add_spec,
  u8_sub_spec,
  u8_mul_spec,
  u8_not_spec,
  u8_and_spec,
  u8_or_spec,
  u8_xor_spec,
  u8_shl_spec,
  u8_shr_spec,
  u8_div_spec,
  u8_mod_spec,
  u8_ltb_spec,
  u8_leb_spec,
  i8_add_spec,
  i8_sub_spec,
  i8_mul_spec,
  i8_not_spec,
  i8_and_spec,
  i8_or_spec,
  i8_xor_spec,
  i8_shl_spec,
  i8_shr_spec,
  i8_div_spec,
  i8_mod_spec,
  i8_ltb_spec,
  i8_leb_spec,
  u16_of_spec,
  i16_of_spec,
  u16_add_spec,
  u16_sub_spec,
  u16_mul_spec,
  u16_not_spec,
  u16_and_spec,
  u16_or_spec,
  u16_xor_spec,
  u16_shl_spec,
  u16_shr_spec,
  u16_div_spec,
  u16_mod_spec,
  u16_ltb_spec,
  u16_leb_spec,
  i16_add_spec,
  i16_sub_spec,
  i16_mul_spec,
  i16_not_spec,
  i16_and_spec,
  i16_or_spec,
  i16_xor_spec,
  i16_shl_spec,
  i16_shr_spec,
  i16_div_spec,
  i16_mod_spec,
  i16_ltb_spec,
  i16_leb_spec,
  u32_of_spec,
  i32_of_spec,
  u32_add_spec,
  u32_sub_spec,
  u32_mul_spec,
  u32_not_spec,
  u32_and_spec,
  u32_or_spec,
  u32_xor_spec,
  u32_shl_spec,
  u32_shr_spec,
  u32_div_spec,
  u32_mod_spec,
  u32_ltb_spec,
  u32_leb_spec,
  i32_add_spec,
  i32_sub_spec,
  i32_mul_spec,
  i32_not_spec,
  i32_and_spec,
  i32_or_spec,
  i32_xor_spec,
  i32_shl_spec,
  i32_shr_spec,
  i32_div_spec,
  i32_mod_spec,
  i32_ltb_spec,
  i32_leb_spec,
  u64_add_spec,
  u64_sub_spec,
  u64_mul_spec,
  u64_and_spec,
  u64_or_spec,
  u64_shl_spec,
  u64_shr_spec,
  u64_ltb_spec,
  u64_leb_spec,
  u64_eqb_spec,
  u64_divu_spec,
  u64_modu_spec,
  u64_mulhi_spec,
  i64_add_spec,
  i64_sub_spec,
  i64_mul_spec,
  i64_ltb_spec,
  i64_leb_spec,
  i64_div_spec,
  i64_mod_spec,
  i64_shr_spec,
  rotl32_spec,
  rotr32_spec,
  rotl64_spec,
  rotr64_spec,
  bswap16_spec,
  bswap32_spec,
  bswap64_spec,
  clz32_zero,
  clz32_spec,
  ctz32_zero,
  ctz32_spec,
  clz64_spec,
  ctz64_spec,
  popcount32_spec,
  popcount64_spec).
