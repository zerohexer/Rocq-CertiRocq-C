(* proved/KQLoopExamples.v -- PROOFS ABOUT PROGRAMS WRITTEN WITH A MEASURE (proved/examples/wfix.body): the termination argument
   is one tactic, the equation is a theorem, and a property is proved by induction on the measure.  The Rocq text below is the
   text of the program. *)
From Stdlib Require Import ZArith Lia Sint63.
Require Import KQ.KQRun KQ.KQSpec KQ.lib.Loop KQ.lib.LoopSpec.
From KQC Require Import KQMAuto KQLoopSpec.
Open Scope sint63_scope.
Notation Z_ := Sint63.to_Z.
Set Default Timeout 60.

(* ---- 1 + 2 + .. + n, with a call that is not the last step *)
Definition tri_F : (int -> int) -> int -> int := fun rec x => if 0 <? x then x + rec (x - 1) else 0.
Definition tri_meas : int -> int := fun x => x.
Definition tri_P : int -> Prop := fun x => (0 <= Z_ x <= 1000)%Z.

Lemma tri_dec : wfix1_dec tri_meas tri_F tri_P.
Proof. wfix1_dec_tac ltac:(unfold tri_meas, tri_P in *; wf_side). Qed.

(* the equation of the recursive function *)
Corollary tri_eq : forall x, tri_P x -> wfix1 tri_meas tri_F x = tri_F (wfix1 tri_meas tri_F) x.
Proof.
  intros x Px. unfold tri_P in Px.
  apply (wfix1_eq tri_meas tri_F tri_P tri_dec); [exact Px | unfold tri_meas; lia | unfold tri_meas; lia].
Qed.


(* what it computes, by induction on the measure: twice the sum is n * (n + 1) *)
Theorem tri_closed : forall x, tri_P x -> (2 * Z_ (wfix1 tri_meas tri_F x) = Z_ x * (Z_ x + 1))%Z.
Proof.
  intros x Px.
  refine (wfix1_ind tri_meas tri_F tri_P (fun x v => (2 * Z_ v = Z_ x * (Z_ x + 1))%Z) tri_dec _ x Px _ _);
    [ | unfold tri_meas, tri_P in *; lia | unfold tri_meas, tri_P in *; lia ].
  intros y Py M0 M1 r IH. unfold tri_F. cbv beta. unfold tri_P, tri_meas in *.
  destruct (0 <? y) eqn:E.
  - apply lt_Z in E. change (Z_ 0) with 0%Z in E.
    assert (Y1 : Z_ (y - 1) = (Z_ y - 1)%Z) by (apply sub1_Z; lia).
    pose proof (IH (y - 1) ltac:(rewrite Y1; lia) ltac:(rewrite Y1; lia)) as H. rewrite Y1 in H.
    assert (B : ((Z_ y - 1) * (Z_ y - 1 + 1) <= 1000000)%Z) by nia.
    assert (Hadd : Z_ (y + r (y - 1)) = (Z_ y + Z_ (r (y - 1)%sint63))%Z)
      by (pose proof (to_Z_bounds y); rewrite add_Z; [ reflexivity | nia ]).
    rewrite Hadd. nia.
  - apply lt_Z_false in E. change (Z_ 0) with 0%Z in *. assert (Z_ y = 0)%Z by lia. rewrite H. nia.
Qed.

(* ---- Euclid's gcd *)
Definition gcd_F : (int -> int -> int) -> int -> int -> int := fun rec x y => if 0 <? y then rec y (Sint63.rem x y) else x.
Definition gcd_meas : int -> int -> int := fun x y => y.
Definition gcd_P : int -> int -> Prop := fun x y => (0 <= Z_ x /\ 0 <= Z_ y < 2 ^ 60)%Z.

Lemma gcd_dec : wfix2_dec gcd_meas gcd_F gcd_P.
Proof. wfix2_dec_tac ltac:(unfold gcd_meas, gcd_P in *; wf_side). Qed.

Corollary gcd_eq : forall x y, gcd_P x y -> wfix2 gcd_meas gcd_F x y = gcd_F (wfix2 gcd_meas gcd_F) x y.
Proof.
  intros x y Pxy. unfold gcd_P in Pxy.
  apply (wfix2_eq gcd_meas gcd_F gcd_P gcd_dec); [exact Pxy | unfold gcd_meas; lia | unfold gcd_meas; lia].
Qed.

(* what it computes: the greatest common divisor *)
Theorem gcd_correct : forall x y, gcd_P x y -> Z_ (wfix2 gcd_meas gcd_F x y) = Z.gcd (Z_ x) (Z_ y).
Proof.
  intros x y Pxy.
  refine (wfix2_ind gcd_meas gcd_F gcd_P (fun x y v => Z_ v = Z.gcd (Z_ x) (Z_ y)) gcd_dec _ x y Pxy _ _);
    [ | unfold gcd_meas, gcd_P in *; lia | unfold gcd_meas, gcd_P in *; lia ].
  intros a b Pab M0 M1 r IH. unfold gcd_F. cbv beta. unfold gcd_P, gcd_meas in *.
  destruct (0 <? b) eqn:E.
  - apply lt_Z in E. change (Z_ 0) with 0%Z in E.
    pose proof (rem_range a b ltac:(lia) E) as R.
    pose proof (IH b (Sint63.rem a b) ltac:(lia) ltac:(lia)) as H. rewrite H.
    rewrite Sint63.mod_spec. rewrite Z.rem_mod_nonneg by lia.
    rewrite (Z.gcd_comm (Z_ b)). rewrite Z.gcd_mod by lia. apply Z.gcd_comm.
  - apply lt_Z_false in E. change (Z_ 0) with 0%Z in E. assert (Z_ b = 0)%Z by lia. rewrite H.
    rewrite Z.gcd_0_r. rewrite Z.abs_eq by lia. reflexivity.
Qed.
