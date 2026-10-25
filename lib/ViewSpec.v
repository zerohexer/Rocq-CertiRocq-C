(* lib/ViewSpec.v -- WHAT THE VIEWS GUARANTEE (lib/View.v), proved against the memory's laws (KQSpec.v):
   writing 64 bits leaves every other 32-bit cell alone, and reading 64 bits back gives the number written. *)
From Stdlib Require Import ZArith Lia Sint63 Bool.
Require Import KQ.KQRun KQ.KQBound KQ.KQSpec KQ.lib.View.
Open Scope sint63_scope.
Open Scope bool_scope.
Notation Z_ := Sint63.to_Z.

(* a write of the 64 bits at 8 i changes no cell but 2 i and 2 i + 1 *)
Theorem view_upd64_frame (h i : int) (v : u64) (h' j : int) (s : mem) :
  other h (2 * i) h' j = true -> other h (2 * i + 1) h' j = true ->
  rd32 h' j (view_upd64 h i v s) = rd32 h' j s.
Proof.
  intros O1 O2. unfold view_upd64.
  rewrite (rd32_upd32_ne real real_laws h (2 * i + 1) h' j _ _ O2).
  exact (rd32_upd32_ne real real_laws h (2 * i) h' j _ _ O1).
Qed.

(* the wide cells are not touched either *)
Theorem view_upd64_rd (h i : int) (v : u64) (h' j : int) (s : mem) :
  rd h' j (view_upd64 h i v s) = rd h' j s.
Proof.
  unfold view_upd64.
  rewrite (rd_upd32 real real_laws h (2 * i + 1) _ h' j _).
  exact (rd_upd32 real real_laws h (2 * i) _ h' j s).
Qed.

(* ---- 64 bits written and read back: the u64 comes back (as the number it stands for) *)
Notation phi := Uint63.to_Z.

Lemma phi_bounds (x : int) : (0 <= phi x < 9223372036854775808)%Z.
Proof. exact (Uint63.to_Z_bounded x). Qed.

Lemma Z_small (x : int) : (phi x < 4611686018427387904)%Z -> Z_ x = phi x.
Proof.
  intro L. pose proof (Sint63.to_Z_mod_Uint63to_Z x) as M. pose proof (to_Z_bounds x) as B.
  change wB with 9223372036854775808%Z in M.
  destruct (Z_le_gt_dec 0 (Z_ x)) as [P | P].
  - rewrite Z.mod_small in M; lia.
  - assert (E : (Z_ x + 9223372036854775808 = Z_ x mod 9223372036854775808)%Z)
      by (apply Z.mod_unique_pos with (q := (-1)%Z); lia).
    lia.
Qed.

Lemma phi_land_ones (x m : int) (k : Z) : (0 <= k)%Z -> phi m = Z.ones k -> phi (PrimInt63.land x m) = (phi x mod 2 ^ k)%Z.
Proof. intros K M. rewrite Uint63.land_spec', M. apply Z.land_ones. exact K. Qed.

(* the parts of a sum of two numbers one above the other do not overlap *)
Lemma lor_disjoint (a b k : Z) : (0 <= k)%Z -> (0 <= a < 2 ^ k)%Z -> (0 <= b)%Z -> Z.lor a (b * 2 ^ k) = (a + b * 2 ^ k)%Z.
Proof.
  intros K A B. rewrite <- Z.shiftl_mul_pow2 by exact K.
  assert (D : Z.land a (Z.shiftl b k) = 0%Z).
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

Lemma phi_hi32 (v : u64) :
  phi (u64_hi32 v) = (phi (w_lo v) / 2 ^ 32 + (phi (w_hi v) mod 2) * 2 ^ 31)%Z.
Proof.
  unfold u64_hi32.
  pose proof (phi_bounds (w_lo v)) as LB.
  rewrite Uint63.lor_spec', Uint63.lsr_spec, Uint63.lsl_spec.
  assert (E1 : phi (PrimInt63.land (w_hi v) 1%uint63) = (phi (w_hi v) mod 2)%Z).
  { rewrite (phi_land_ones (w_hi v) 1%uint63 1%Z) by (lia || reflexivity). reflexivity. }
  rewrite E1. change (phi 32%uint63) with 32%Z. change (phi 31%uint63) with 31%Z.
  assert (B : (0 <= phi (w_hi v) mod 2 < 2)%Z) by (apply Z.mod_pos_bound; lia).
  assert (Q : (0 <= phi (w_lo v) / 2 ^ 32 < 2 ^ 31)%Z).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite Z.mod_small by (change wB with 9223372036854775808%Z; lia).
  apply lor_disjoint; lia.
Qed.

Lemma phi_lo32 (v : u64) : phi (u64_lo32 v) = (phi (w_lo v) mod 2 ^ 32)%Z.
Proof.
  unfold u64_lo32. rewrite (phi_land_ones (w_lo v) 4294967295%uint63 32%Z) by (lia || reflexivity). reflexivity.
Qed.

(* sx32 of a number below 2^32 is that number, or that number less 2^32 -- both the same modulo 2^32 and, one bit
   narrower, modulo 2^31 *)
Lemma sx32_mod (x : int) : (0 <= phi x < 2 ^ 32)%Z ->
  (phi (sx32 x) mod 2 ^ 32 = phi x)%Z /\ (phi (sx32 x) mod 2 ^ 31 = phi x mod 2 ^ 31)%Z.
Proof.
  intros X. unfold sx32.
  assert (U : phi (PrimInt63.land x 4294967295%uint63) = phi x).
  { rewrite (phi_land_ones x 4294967295%uint63 32%Z) by (lia || reflexivity). apply Z.mod_small. lia. }
  set (u := PrimInt63.land x 4294967295%uint63) in *.
  destruct (u <? 2147483648) eqn:C.
  - rewrite U. split; [apply Z.mod_small; lia | reflexivity].
  - assert (Uge : (2147483648 <= phi u)%Z).
    { apply lt_Z_false in C. rewrite (Z_small u) in C by lia. change (Z_ 2147483648) with 2147483648%Z in C. lia. }
    assert (S : phi (u - 4294967296%uint63) = (phi u - 4294967296 + 9223372036854775808)%Z).
    { rewrite Uint63.sub_spec. change (phi 4294967296%uint63) with 4294967296%Z. change wB with 9223372036854775808%Z.
      rewrite U in *. symmetry. apply Z.mod_unique_pos with (q := (-1)%Z); lia. }
    rewrite S, U.
    split.
    + replace (phi x - 4294967296 + 9223372036854775808)%Z with (phi x + 2147483647 * 2 ^ 32)%Z
        by (change (2 ^ 32)%Z with 4294967296%Z; lia).
      rewrite Z.mod_add by (change (2 ^ 32)%Z with 4294967296%Z; lia). apply Z.mod_small. lia.
    + replace (phi x - 4294967296 + 9223372036854775808)%Z with (phi x + 4294967294 * 2 ^ 31)%Z
        by (change (2 ^ 31)%Z with 2147483648%Z; lia).
      rewrite Z.mod_add by (change (2 ^ 31)%Z with 2147483648%Z; lia). reflexivity.
Qed.

Lemma halves_val (v : u64) :
  u64_val (u64_of_halves (sx32 (u64_hi32 v)) (sx32 (u64_lo32 v))) = u64_val v.
Proof.
  pose proof (phi_bounds (w_lo v)) as LB.
  set (L := phi (w_lo v)) in *. set (B := (phi (w_hi v) mod 2)%Z).
  assert (Bb : (0 <= B < 2)%Z) by (unfold B; apply Z.mod_pos_bound; lia).
  assert (Hv : phi (u64_hi32 v) = (L / 2 ^ 32 + B * 2 ^ 31)%Z) by (unfold L, B; apply phi_hi32).
  assert (Lv : phi (u64_lo32 v) = (L mod 2 ^ 32)%Z) by (unfold L; apply phi_lo32).
  assert (Q : (0 <= L / 2 ^ 32 < 2 ^ 31)%Z).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; change wB with 9223372036854775808%Z in LB; lia]. }
  assert (R : (0 <= L mod 2 ^ 32 < 2 ^ 32)%Z) by (apply Z.mod_pos_bound; lia).
  destruct (sx32_mod (u64_hi32 v)) as [Hm32 Hm31]; [rewrite Hv; lia | ].
  destruct (sx32_mod (u64_lo32 v)) as [Lm32 Lm31]; [rewrite Lv; lia | ].
  rewrite Hv in Hm32, Hm31. rewrite Lv in Lm32.
  unfold u64_val, u64_of_halves. cbn [w_lo w_hi].
  rewrite Uint63.lor_spec', Uint63.lsl_spec, Uint63.lsr_spec.
  rewrite (phi_land_ones (sx32 (u64_hi32 v)) 2147483647%uint63 31%Z) by (lia || reflexivity).
  rewrite (phi_land_ones (sx32 (u64_lo32 v)) 4294967295%uint63 32%Z) by (lia || reflexivity).
  rewrite (phi_land_ones (sx32 (u64_hi32 v)) 4294967295%uint63 32%Z) by (lia || reflexivity).
  rewrite Hm32, Lm32, Hm31. change (phi 32%uint63) with 32%Z. change (phi 31%uint63) with 31%Z.
  change wB with 9223372036854775808%Z.
  assert (M1 : ((L / 2 ^ 32 + B * 2 ^ 31) mod 2 ^ 31 = L / 2 ^ 32)%Z).
  { rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (M2 : ((L / 2 ^ 32 + B * 2 ^ 31) / 2 ^ 31 = B)%Z).
  { symmetry. apply Z.div_unique_pos with (r := (L / 2 ^ 32)%Z); lia. }
  rewrite M1, M2.
  rewrite (Z.mod_small ((L / 2 ^ 32) * 2 ^ 32)) by (change wB with 9223372036854775808%Z in LB; lia).
  rewrite Z.lor_comm, lor_disjoint by lia.
  assert (E : (L mod 2 ^ 32 + L / 2 ^ 32 * 2 ^ 32 = L)%Z) by (pose proof (Z.div_mod L (2 ^ 32) ltac:(lia)); lia).
  rewrite E. rewrite (Z.mod_small B 2) by lia. reflexivity.
Qed.

(* a 64-bit cell written and read back is the number written (as the number a u64 stands for) *)
Theorem view_rd64_upd64 (h i : int) (v : u64) (s : mem) :
  (0 <= Z_ h)%Z -> (0 <= Z_ i)%Z -> (2 * Z_ i + 1 < Z_ (kq_len32 h))%Z -> (Z_ i < 1073741824)%Z ->
  u64_val (view_rd64 h i (view_upd64 h i v s)) = u64_val v.
Proof.
  intros H0 I0 IL IB. unfold view_rd64, view_upd64.
  assert (E1 : Z_ (2 * i + 1) = (2 * Z_ i + 1)%Z).
  { rewrite add_Z; [|rewrite mul_Z; [change (Z_ 2) with 2%Z; change (Z_ 1) with 1%Z; lia | change (Z_ 2) with 2%Z; lia]].
    rewrite mul_Z by (change (Z_ 2) with 2%Z; lia). change (Z_ 2) with 2%Z; change (Z_ 1) with 1%Z; lia. }
  assert (E0 : Z_ (2 * i) = (2 * Z_ i)%Z).
  { rewrite mul_Z by (change (Z_ 2) with 2%Z; lia). change (Z_ 2) with 2%Z. lia. }
  assert (R1 : rd32 h (2 * i + 1) (upd32 h (2 * i + 1) (u64_hi32 v) (upd32 h (2 * i) (u64_lo32 v) s)) = sx32 (u64_hi32 v)).
  { apply (rd32_upd32_eq real real_laws). apply andb_true_iff. split.
    - unfold nonneg2. apply andb_true_iff. split; apply le_Z; change (Z_ 0) with 0%Z; lia.
    - apply lt_Z. cbn [Len32 real]. rewrite E1. lia. }
  assert (R0 : rd32 h (2 * i) (upd32 h (2 * i + 1) (u64_hi32 v) (upd32 h (2 * i) (u64_lo32 v) s)) = sx32 (u64_lo32 v)).
  { rewrite (rd32_upd32_ne real real_laws h (2 * i + 1) h (2 * i) _ _).
    - apply (rd32_upd32_eq real real_laws). apply andb_true_iff. split.
      + unfold nonneg2. apply andb_true_iff. split; apply le_Z; change (Z_ 0) with 0%Z; lia.
      + apply lt_Z. cbn [Len32 real]. rewrite E0. lia.
    - unfold other. rewrite Bool.negb_true_iff, Bool.andb_false_iff. right. apply eq_Z_false. rewrite E0, E1. lia. }
  rewrite R1, R0. apply halves_val.
Qed.
