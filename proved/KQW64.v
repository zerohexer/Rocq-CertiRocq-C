(** 64-bit unsigned numbers (KQRun.v u64): what C's [unsigned long long] operations do, in numbers. *)

From Stdlib Require Import ZArith Lia Uint63.
From compcert Require Import Coqlib Integers.
From KQC Require Import KQLSigned KQTArith.
Require KQ.KQRun.

Local Open Scope Z_scope.

(** the C operation on two words *)
Definition w64_int (o : KQ.KQRun.w64op) (x y : Int64.int) : Int64.int :=
  match o with
  | KQ.KQRun.W_add => Int64.add x y
  | KQ.KQRun.W_sub => Int64.sub x y
  | KQ.KQRun.W_mul => Int64.mul x y
  | KQ.KQRun.W_and => Int64.and x y
  | KQ.KQRun.W_or => Int64.or x y
  | KQ.KQRun.W_xor => Int64.xor x y
  | KQ.KQRun.W_shl => Int64.shl x (Int64.and y (Int64.repr 63))
  | KQ.KQRun.W_shr => Int64.shru x (Int64.and y (Int64.repr 63))
  | KQ.KQRun.W_ltu => if Int64.ltu x y then Int64.one else Int64.zero
  | KQ.KQRun.W_leu => if Int64.ltu y x then Int64.zero else Int64.one
  | KQ.KQRun.W_eq => if Int64.eq x y then Int64.one else Int64.zero
  end.

Lemma int64_range : forall x : Int64.int, 0 <= Int64.unsigned x < 2 ^ 64.
Proof. intros x. pose proof (Int64.unsigned_range x). change Int64.modulus with (2 ^ 64) in H. exact H. Qed.

Lemma and63 : forall y : Int64.int, Int64.unsigned (Int64.and y (Int64.repr 63)) = Int64.unsigned y mod 64.
Proof.
  intros y. rewrite uand, (uns_small 63) by lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
  pose proof (int64_range y). rewrite (Z.mod_small (Int64.unsigned y mod 2 ^ 6)); [reflexivity | ].
  pose proof (Z.mod_pos_bound (Int64.unsigned y) (2 ^ 6) ltac:(lia)). lia.
Qed.

Lemma w64_int_val : forall o (x y : Int64.int),
  Int64.unsigned (w64_int o x y) = (KQ.KQRun.w64_z o (Int64.unsigned x) (Int64.unsigned y)) mod 2 ^ 64.
Proof.
  intros o x y. pose proof (int64_range x) as Rx. pose proof (int64_range y) as Ry.
  destruct o; cbn [w64_int KQ.KQRun.w64_z].
  - apply uadd.
  - apply usub.
  - apply umul.
  - apply uand.
  - apply uor.
  - apply uxor.
  - unfold Int64.shl. rewrite Int64.unsigned_repr_eq. change Int64.modulus with (2 ^ 64). rewrite and63. reflexivity.
  - unfold Int64.shru. rewrite Int64.unsigned_repr_eq. change Int64.modulus with (2 ^ 64). rewrite and63. reflexivity.
  - unfold Int64.ltu. destruct (zlt (Int64.unsigned x) (Int64.unsigned y)); cbn.
    + destruct (Z.ltb_spec (Int64.unsigned x) (Int64.unsigned y)); [ | lia]. reflexivity.
    + destruct (Z.ltb_spec (Int64.unsigned x) (Int64.unsigned y)); [lia | ]. reflexivity.
  - unfold Int64.ltu. destruct (zlt (Int64.unsigned y) (Int64.unsigned x)); cbn.
    + destruct (Z.leb_spec (Int64.unsigned x) (Int64.unsigned y)); [lia | ]. reflexivity.
    + destruct (Z.leb_spec (Int64.unsigned x) (Int64.unsigned y)); [ | lia]. reflexivity.
  - unfold Int64.eq. destruct (zeq (Int64.unsigned x) (Int64.unsigned y)); cbn.
    + destruct (Z.eqb_spec (Int64.unsigned x) (Int64.unsigned y)); [ | contradiction]. reflexivity.
    + destruct (Z.eqb_spec (Int64.unsigned x) (Int64.unsigned y)); [contradiction | ]. reflexivity.
Qed.

(** the word of a pair of numbers *)
Lemma pack_val : forall (l h : PrimInt63.int),
  Int64.unsigned (Int64.add (Int64.shl (Int64.repr (Uint63.to_Z h)) (Int64.repr 63)) (Int64.repr (Uint63.to_Z l)))
  = Uint63.to_Z l + 2 ^ 63 * (Uint63.to_Z h mod 2).
Proof.
  intros l h. pose proof (phi_range l) as Rl. pose proof (phi_range h) as Rh.
  set (hv := Uint63.to_Z h) in *. set (lv := Uint63.to_Z l) in *.
  rewrite uadd. unfold Int64.shl. rewrite Int64.unsigned_repr_eq. change Int64.modulus with (2 ^ 64).
  rewrite (uns_small 63) by lia. rewrite uns_repr.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (uns_small lv) by lia.
  assert (E1 : (hv mod 2 ^ 64 * 2 ^ 63) mod 2 ^ 64 = 2 ^ 63 * (hv mod 2)).
  { rewrite (Z.mod_small hv (2 ^ 64)) by lia.
    rewrite (Z.div_mod hv 2) at 1 by lia.
    replace ((2 * (hv / 2) + hv mod 2) * 2 ^ 63) with (2 ^ 63 * (hv mod 2) + (hv / 2) * 2 ^ 64) by (change (2 ^ 64) with (2 * 2 ^ 63); ring).
    rewrite Z.mod_add by lia. apply Z.mod_small.
    pose proof (Z.mod_pos_bound hv 2 ltac:(lia)). lia. }
  rewrite E1, Z.add_comm. apply Z.mod_small.
  pose proof (Z.mod_pos_bound hv 2 ltac:(lia)). lia.
Qed.

(** the low 63 bits and the bit above, of a word *)
Lemma unpack_lo : forall r : Int64.int,
  Int64.unsigned (Int64.and r (Int64.repr (2 ^ 63 - 1))) = Int64.unsigned r mod 2 ^ 63.
Proof.
  intros r. pose proof (int64_range r). rewrite uand, (uns_small (2 ^ 63 - 1)) by lia.
  replace (2 ^ 63 - 1) with (Z.ones 63) by reflexivity. rewrite Z.land_ones by lia.
  apply Z.mod_small. pose proof (Z.mod_pos_bound (Int64.unsigned r) (2 ^ 63) ltac:(lia)). lia.
Qed.

Lemma unpack_hi : forall r : Int64.int,
  Int64.unsigned (Int64.shru r (Int64.repr 63)) = Int64.unsigned r / 2 ^ 63.
Proof.
  intros r. pose proof (int64_range r). unfold Int64.shru. rewrite Int64.unsigned_repr_eq. change Int64.modulus with (2 ^ 64).
  rewrite (uns_small 63) by lia. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.mod_small. split; [apply Z.div_pos; lia | ].
  apply Z.div_lt_upper_bound; [lia | replace (2 ^ 63 * 2 ^ 64) with (2 ^ 127) by reflexivity; lia].
Qed.
