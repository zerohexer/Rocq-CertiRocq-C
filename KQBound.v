(* KQBound.v -- A READ OR A WRITE THAT ASKS NOTHING, AND THE PROOF THAT IT MAY.

   `rd h i s` gives 0 for a cell outside block h, so the machine tests every read ("is i inside the block?"), and
   every write likewise.  `rd_u` / `upd_u` (and `rd32_u` / `upd32_u` for narrow blocks) ARE `rd` / `upd`: the same
   functions in Rocq, equal by computation.  The machine does them WITHOUT the test (sup/v4/kq_io.h).  That is right
   only where the cell is inside its block, so the translator (KQFast.v) writes them only where it has a PROOF of it:
   for each loop it changes, it also writes a copy of the loop that carries the proof at every such read and write
   (`rd_p`, `upd_p`: they take the proof as an argument), Rocq's type checker checks that copy, and the kernel checks
   that the loop that is compiled is that copy with its proofs taken out.  The copy is never compiled.

   The proofs are about loops that count: a parameter that goes up by one every round, a budget that is the number of
   rounds left, and cells at that parameter plus a constant.  The loop is called only when one test at its start --
   "is the last cell it will reach inside the block?" (`kq_fits`) -- says yes; otherwise the loop with the tests is
   called.  Everything below is proved once, here; per loop the translator only puts these lemmas together. *)
From Stdlib Require Import ZArith Lia Uint63 Bool.
Require Import KQ.KQRun.
Open Scope sint63_scope.

(* the length of a block: no operation changes it (0 when there is no such block) *)
Axiom kq_len   : int -> int.
Axiom kq_len32 : int -> int.

Definition rd_u (h i : int) (s : mem) : int := rd h i s.
Definition upd_u (h i v : int) (s : mem) : mem := upd h i v s.
Definition rd32_u (h i : int) (s : mem) : int := rd32 h i s.
Definition upd32_u (h i v : int) (s : mem) : mem := upd32 h i v s.

(* the cell i is inside the block of length L *)
Definition in_len (L i : int) : Prop := PrimInt63.ltb i L = true.
Definition rd_p (h i : int) (s : mem) (H : in_len (kq_len h) i) : int := rd_u h i s.
Definition upd_p (h i v : int) (s : mem) (H : in_len (kq_len h) i) : mem := upd_u h i v s.
Definition rd32_p (h i : int) (s : mem) (H : in_len (kq_len32 h) i) : int := rd32_u h i s.
Definition upd32_p (h i v : int) (s : mem) (H : in_len (kq_len32 h) i) : mem := upd32_u h i v s.

(* the cells e, e + 1, .., e + n - 1 are all inside the block of length L *)
Definition fits (L e : int) (n : nat) : Prop := (Uint63.to_Z e + Z.of_nat n <= Uint63.to_Z L)%Z.
(* the test the program makes once, at the start of the loop (the machine computes it without Z: sup/v4/kq_io.h) *)
Definition kq_fits (L e : int) (n : nat) : bool := Z.leb (Uint63.to_Z e + Z.of_nat n) (Uint63.to_Z L).

Lemma kq_fits_ok L e n : kq_fits L e n = true -> fits L e n.
Proof. unfold kq_fits, fits. intro H. apply Z.leb_le. exact H. Qed.

Lemma fits_now L e n : fits L e (S n) -> in_len L e.
Proof.
  unfold fits, in_len. intro H. apply Uint63.ltb_spec. rewrite Nat2Z.inj_succ in H. lia.
Qed.

Lemma succ_no_wrap x : (Uint63.to_Z x + 1 < Uint63.wB)%Z -> Uint63.to_Z (x + 1) = (Uint63.to_Z x + 1)%Z.
Proof.
  intro H. rewrite Uint63.add_spec. rewrite Uint63.to_Z_1. apply Z.mod_small.
  pose proof (Uint63.to_Z_bounded x). lia.
Qed.

Lemma fits_next0 L e n : fits L e (S n) -> fits L (e + 1) n.
Proof.
  unfold fits. intro H. rewrite Nat2Z.inj_succ in H.
  pose proof (Uint63.to_Z_bounded L). rewrite succ_no_wrap by lia. lia.
Qed.

Lemma fits_next L e d n : fits L (e + d) (S n) -> fits L ((e + 1) + d) n.
Proof.
  intro H. assert (E : (e + 1) + d = (e + d) + 1).
  { rewrite <- !Uint63.add_assoc. f_equal. apply Uint63.add_comm. }
  rewrite E. apply fits_next0. exact H.
Qed.

(* the same, for the other ways of writing the two additions: the step as `1 + e`, the cell as `d + e` *)
Lemma fits_next0l L e n : fits L e (S n) -> fits L (1 + e) n.
Proof. intro H. rewrite Uint63.add_comm. apply fits_next0. exact H. Qed.
Lemma fits_nextl L e d n : fits L (e + d) (S n) -> fits L ((1 + e) + d) n.
Proof. intro H. rewrite (Uint63.add_comm 1 e). apply fits_next. exact H. Qed.
Lemma fits_nextr L e d n : fits L (d + e) (S n) -> fits L (d + (e + 1)) n.
Proof.
  intro H. assert (E : d + (e + 1) = (d + e) + 1) by (rewrite Uint63.add_assoc; reflexivity).
  rewrite E. apply fits_next0. exact H.
Qed.
Lemma fits_nextrl L e d n : fits L (d + e) (S n) -> fits L (d + (1 + e)) n.
Proof. intro H. rewrite (Uint63.add_comm 1 e). apply fits_nextr. exact H. Qed.

(* the start test: one `kq_fits` for every cell the loop reaches, joined by && *)
Lemma andb_l a b : a && b = true -> a = true.
Proof. destruct a; [reflexivity | discriminate]. Qed.
Lemma andb_r a b : a && b = true -> b = true.
Proof. destruct a; [exact (fun h => h) | discriminate]. Qed.
