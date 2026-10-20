(** Bytes of a 4-byte cell in CompCert's memory: a cell that holds [Vint i] as a 32-bit number, read and written one byte
    at a time (little-endian, the machine's layout). *)

From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Import ListNotations.

Local Open Scope Z_scope.

Lemma byte_range : forall x : byte, 0 <= Byte.unsigned x < 256.
Proof. intros x. pose proof (Byte.unsigned_range x). change Byte.modulus with 256 in H. exact H. Qed.

Lemma decode4 : forall x0 x1 x2 x3 : byte,
  decode_int [x0; x1; x2; x3] = Byte.unsigned x0 + Byte.unsigned x1 * 256 + Byte.unsigned x2 * 65536 + Byte.unsigned x3 * 16777216.
Proof.
  intros. unfold decode_int, rev_if_be. replace Archi.big_endian with false by reflexivity. cbn [int_of_bytes]. ring.
Qed.

(** the four bytes of a cell *)
Lemma cell_bytes : forall m b o i,
  (4 | o) -> Mem.load Mint32 m b o = Some (Vint i) ->
  exists x0 x1 x2 x3 : byte,
    Mem.loadbytes m b o 4 = Some [Byte x0; Byte x1; Byte x2; Byte x3] /\
    Int.unsigned i = Byte.unsigned x0 + Byte.unsigned x1 * 256 + Byte.unsigned x2 * 65536 + Byte.unsigned x3 * 16777216.
Proof.
  intros m b o i Hal Ld.
  destruct (Mem.load_loadbytes _ _ _ _ _ Ld) as (bytes & LB & Dec). change (size_chunk Mint32) with 4 in LB.
  pose proof (Mem.loadbytes_length _ _ _ _ _ LB) as Len. change (Z.to_nat 4) with 4%nat in Len.
  destruct bytes as [|c0 [|c1 [|c2 [|c3 [|c4 r]]]]]; simpl in Len; try discriminate.
  unfold decode_val in Dec.
  destruct (proj_bytes [c0; c1; c2; c3]) as [bl | ] eqn:PB; [ | simpl in Dec; discriminate].
  apply inj_proj_bytes in PB.
  destruct bl as [|x0 [|x1 [|x2 [|x3 [|x4 r2]]]]]; simpl in PB; try discriminate.
  injection PB as E0 E1 E2 E3. subst c0 c1 c2 c3.
  exists x0, x1, x2, x3. split; [exact LB | ].
  simpl in Dec. injection Dec as Di. rewrite Di, decode4.
  pose proof (byte_range x0). pose proof (byte_range x1). pose proof (byte_range x2). pose proof (byte_range x3).
  apply Int.unsigned_repr. unfold Int.max_unsigned. change Int.modulus with 4294967296. lia.
Qed.

(** one byte of the four *)
Lemma loadbytes_one : forall m b o l bb,
  Mem.loadbytes m b o 4 = Some l -> 0 <= bb < 4 ->
  exists y, Mem.loadbytes m b (o + bb) 1 = Some [y] /\ nth_error l (Z.to_nat bb) = Some y.
Proof.
  intros m b o l bb LB Rb.
  assert (E : 4 = bb + (1 + (3 - bb))) by lia. rewrite E in LB.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ LB ltac:(lia) ltac:(lia)) as (b1 & b2 & L1 & L2 & Eq).
  destruct (Mem.loadbytes_split _ _ _ _ _ _ L2 ltac:(lia) ltac:(lia)) as (c1 & c2 & M1 & M2 & Eq2).
  pose proof (Mem.loadbytes_length _ _ _ _ _ L1) as Lb1.
  pose proof (Mem.loadbytes_length _ _ _ _ _ M1) as Lc1.
  destruct c1 as [|y [|z r]]; simpl in Lc1; try (change (Z.to_nat 1) with 1%nat in Lc1; discriminate).
  exists y. split; [exact M1 | ].
  rewrite Eq, Eq2. 
  rewrite nth_error_app2 by lia. rewrite Lb1. replace (Z.to_nat bb - Z.to_nat bb)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma zero_ext8_small : forall u, 0 <= u < 256 -> Int.zero_ext 8 (Int.repr u) = Int.repr u.
Proof.
  intros u H. apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_zero_ext by lia. destruct (zlt i 8); [reflexivity | ].
  rewrite Int.testbit_repr by lia. symmetry.
  apply Z.testbit_false; [lia | ]. rewrite Z.div_small; [reflexivity | ].
  split; [lia | ]. eapply Z.lt_le_trans; [exact (proj2 H) | ].
  change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia.
Qed.

(** the four bytes of a number, taken out again *)
Lemma byte_extract : forall a b c d : Z, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  ((a + b * 256 + c * 65536 + d * 16777216) mod 256 = a) /\
  (((a + b * 256 + c * 65536 + d * 16777216) / 256) mod 256 = b) /\
  (((a + b * 256 + c * 65536 + d * 16777216) / 65536) mod 256 = c) /\
  (((a + b * 256 + c * 65536 + d * 16777216) / 16777216) mod 256 = d).
Proof.
  intros a b c d Ha Hb Hc Hd. set (U := a + b * 256 + c * 65536 + d * 16777216).
  assert (E1 : U / 256 = b + c * 256 + d * 65536) by (symmetry; apply Z.div_unique with (r := a); [lia | unfold U; lia]).
  assert (E1m : U mod 256 = a) by (symmetry; apply Z.mod_unique with (q := b + c * 256 + d * 65536); [lia | unfold U; lia]).
  assert (E2 : U / 65536 = c + d * 256) by (symmetry; apply Z.div_unique with (r := a + b * 256); [lia | unfold U; lia]).
  assert (E3 : U / 16777216 = d) by (symmetry; apply Z.div_unique with (r := a + b * 256 + c * 65536); [lia | unfold U; lia]).
  rewrite E1, E2, E3. refine (conj E1m (conj _ (conj _ _))).
  - symmetry; apply Z.mod_unique with (q := c + d * 256); [lia | lia].
  - symmetry; apply Z.mod_unique with (q := d); [lia | lia].
  - apply Z.mod_small; lia.
Qed.

(** a byte of a cell read as a number of its own *)
Lemma load_byte_in_cell : forall m b o i bb,
  (4 | o) -> 0 <= bb < 4 -> Mem.load Mint32 m b o = Some (Vint i) ->
  Mem.load Mint8unsigned m b (o + bb) = Some (Vint (Int.repr ((Int.unsigned i / 2 ^ (8 * bb)) mod 256))).
Proof.
  intros m b o i bb Hal Rb Ld.
  destruct (cell_bytes _ _ _ _ Hal Ld) as (x0 & x1 & x2 & x3 & LB & U).
  destruct (loadbytes_one _ _ _ _ bb LB Rb) as (y & L1 & Ny).
  pose proof (byte_range x0). pose proof (byte_range x1). pose proof (byte_range x2). pose proof (byte_range x3).
  assert (Hy : exists x, y = Byte x /\ Byte.unsigned x = (Int.unsigned i / 2 ^ (8 * bb)) mod 256).
  { destruct (byte_extract _ _ _ _ (byte_range x0) (byte_range x1) (byte_range x2) (byte_range x3)) as (B0 & B1 & B2 & B3).
    assert (Rb' : bb = 0 \/ bb = 1 \/ bb = 2 \/ bb = 3) by lia.
    destruct Rb' as [-> | [-> | [-> | ->]]]; simpl in Ny; injection Ny as <-; rewrite U.
    - exists x0. split; [reflexivity | ]. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r. symmetry. exact B0.
    - exists x1. split; [reflexivity | ]. change (2 ^ (8 * 1)) with 256. symmetry. exact B1.
    - exists x2. split; [reflexivity | ]. change (2 ^ (8 * 2)) with 65536. symmetry. exact B2.
    - exists x3. split; [reflexivity | ]. change (2 ^ (8 * 3)) with 16777216. symmetry. exact B3. }
  destruct Hy as (x & -> & Ux).
  rewrite (Mem.loadbytes_load Mint8unsigned m b (o + bb) [Byte x] L1 (Z.divide_1_l _)).
  unfold decode_val. simpl. 
  unfold decode_int, rev_if_be. replace Archi.big_endian with false by reflexivity. cbn [int_of_bytes].
  rewrite Z.mul_0_l, Z.add_0_r, Ux. rewrite zero_ext8_small; [reflexivity | ]. apply Z.mod_pos_bound; lia.
Qed.

(** after a one-byte store, a byte of the four reads as it did, except the one written *)
Lemma piece_after_store : forall m b o l bb t nb m' x,
  Mem.loadbytes m b o 4 = Some l -> Mem.storebytes m b (o + bb) [Byte nb] = Some m' ->
  0 <= bb < 4 -> 0 <= t < 4 -> nth_error l (Z.to_nat t) = Some (Byte x) ->
  Mem.loadbytes m' b (o + t) 1 = Some [Byte (if Z.eq_dec t bb then nb else x)].
Proof.
  intros m b o l bb t nb m' x LB ST Rb Rt Nt.
  destruct (Z.eq_dec t bb) as [E | E].
  - subst t. exact (Mem.loadbytes_storebytes_same _ _ _ _ _ ST).
  - rewrite (Mem.loadbytes_storebytes_disjoint _ _ _ _ _ ST b (o + t) 1 ltac:(lia)).
    + destruct (loadbytes_one _ _ _ _ t LB Rt) as (y & L1 & Ny). rewrite Nt in Ny. injection Ny as <-. exact L1.
    + right. intros z [A B] [C D]. simpl in *. lia.
Qed.

Lemma byte_repr_unsigned : forall v : int, Byte.unsigned (Byte.repr (Int.unsigned v)) = Int.unsigned v mod 256.
Proof. intros v. rewrite Byte.unsigned_repr_eq. reflexivity. Qed.

(** a byte of a cell stored: the cell holds the number with that byte replaced *)
Lemma store_byte_in_cell : forall m b o i bb v m',
  (4 | o) -> 0 <= bb < 4 -> Mem.load Mint32 m b o = Some (Vint i) ->
  Mem.store Mint8unsigned m b (o + bb) (Vint v) = Some m' ->
  Mem.load Mint32 m' b o = Some (Vint (Int.repr
    (Int.unsigned i - ((Int.unsigned i / 2 ^ (8 * bb)) mod 256) * 2 ^ (8 * bb) + (Int.unsigned v mod 256) * 2 ^ (8 * bb)))).
Proof.
  intros m b o i bb v m' Hal Rb Ld ST.
  destruct (cell_bytes _ _ _ _ Hal Ld) as (x0 & x1 & x2 & x3 & LB & U).
  pose proof (Mem.store_storebytes _ _ _ _ _ _ ST) as ST'.
  change (encode_val Mint8unsigned (Vint v)) with (inj_bytes (encode_int 1 (Int.unsigned v))) in ST'.
  unfold encode_int, rev_if_be in ST'. replace Archi.big_endian with false in ST' by reflexivity.
  cbn [bytes_of_int inj_bytes List.map] in ST'.
  set (nb := Byte.repr (Int.unsigned v)) in *.
  pose proof (byte_range x0). pose proof (byte_range x1). pose proof (byte_range x2). pose proof (byte_range x3).
  pose proof (byte_range nb) as Rnb. 
  pose proof (byte_repr_unsigned v) as Unb. fold nb in Unb.
  destruct (byte_extract _ _ _ _ (byte_range x0) (byte_range x1) (byte_range x2) (byte_range x3)) as (B0 & B1 & B2 & B3).
  assert (P0 := piece_after_store _ _ _ _ bb 0 nb m' x0 LB ST' Rb ltac:(lia) eq_refl).
  assert (P1 := piece_after_store _ _ _ _ bb 1 nb m' x1 LB ST' Rb ltac:(lia) eq_refl).
  assert (P2 := piece_after_store _ _ _ _ bb 2 nb m' x2 LB ST' Rb ltac:(lia) eq_refl).
  assert (P3 := piece_after_store _ _ _ _ bb 3 nb m' x3 LB ST' Rb ltac:(lia) eq_refl).
  replace (o + 0) with o in P0 by lia.
  set (y0 := if Z.eq_dec 0 bb then nb else x0) in *.
  set (y1 := if Z.eq_dec 1 bb then nb else x1) in *.
  set (y2 := if Z.eq_dec 2 bb then nb else x2) in *.
  set (y3 := if Z.eq_dec 3 bb then nb else x3) in *.
  assert (C01 := Mem.loadbytes_concat _ _ _ 1 1 _ _ P0 P1 ltac:(lia) ltac:(lia)).
  assert (C012 := Mem.loadbytes_concat _ _ _ 2 1 _ _ C01 P2 ltac:(lia) ltac:(lia)).
  assert (C0123 := Mem.loadbytes_concat _ _ _ 3 1 _ _ C012 P3 ltac:(lia) ltac:(lia)).
  assert (Cb : Mem.loadbytes m' b o (size_chunk Mint32) = Some (inj_bytes [y0; y1; y2; y3])) by exact C0123.
  rewrite (Mem.loadbytes_load Mint32 m' b o _ Cb Hal).
  unfold decode_val. rewrite proj_inj_bytes. simpl. rewrite decode4.
  f_equal. f_equal.
  assert (Rb' : bb = 0 \/ bb = 1 \/ bb = 2 \/ bb = 3) by lia.
  destruct Rb' as [-> | [-> | [-> | ->]]]; subst y0 y1 y2 y3; cbn [Z.eq_dec]; simpl;
    rewrite U, Unb;
    repeat match goal with |- context [2 ^ (8 * ?n)] => let v := eval vm_compute in (2 ^ (8 * n)) in change (2 ^ (8 * n)) with v end;
    try change (Z.pow_pos 2 8) with 256; try change (Z.pow_pos 2 16) with 65536; try change (Z.pow_pos 2 24) with 16777216;
    try rewrite Z.div_1_r; try rewrite B0; try rewrite B1; try rewrite B2; try rewrite B3; f_equal; ring.
Qed.
