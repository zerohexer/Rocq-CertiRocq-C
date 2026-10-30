(** ConvMemo.v -- the conversion memo of our fork of Rocq's kernel (rocq-fork/conv-memo-v9.1.1.patch), proved correct
    over a model of the kernel's closure machine (Rocq-C-solution.md D28, §12.R).

    The kernel compares two terms as a graph of mutable cells (kernel/cClosure.ml, [fconstr]).  The memo gives a cell an
    identity on demand ([uid]: the next value of a counter; 0 means "none yet"), and records, for one conversion check, the
    outcome of comparing two cells at two lifts for a problem (conversion or cumulativity).  Reduction rewrites a cell in
    place with a reduct of its term ([update]) and keeps its identity; a cell built anew, or copied, carries identity 0.

    The model: [cells] maps an identity to the current term of its cell (a cell without identity is not in it: building or
    copying a cell changes nothing here); [assign] is [uid]; [reduce] is [update]; [record] stores the outcome the kernel's
    own comparison gave.  The theorem: in every state reached, every stored outcome is the true one for the current terms
    of the two cells -- so an outcome taken from the table ([lookup]) is the one the comparison would give.

    Assumed, as the kernel already assumes them: the relation compared is invariant under reduction on either side (at any
    lift), and the comparison the kernel runs when the table has no answer gives the true outcome when the outcomes it is
    given for its sub-problems are true (those come from this table, true by [lookup_correct], or from the comparison
    itself).  Not modelled, and checked in the OCaml instead (§12.R (2)): every cell literal carries identity 0, the counter
    is the only place an identity is given, [update] writes only the term and the mark, the table exists only for checked
    conversion (a fixed environment and universe graph: the relation does not change during a check). *)

From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Section Memo.

(** the terms compared, the lifts (relocations), the relation decided ([pb]: false for conversion, true for
    cumulativity), one step of in-place reduction, and the term a cell denotes at a lift *)
Variables T L : Type.
Variable rel : bool -> T -> T -> Prop.
Variable red : T -> T -> Prop.
Variable lift : L -> T -> T.
Variable L_eq_dec : forall a b : L, {a = b} + {a <> b}.

(** a reduct compares as its redex, on either side, at any lift *)
Hypothesis rel_red_l : forall pb l t t' u, red t t' -> (rel pb (lift l t) u <-> rel pb (lift l t') u).
Hypothesis rel_red_r : forall pb l t t' u, red t t' -> (rel pb u (lift l t) <-> rel pb u (lift l t')).

(** a key: the two identities, the two lifts, the problem *)
Definition key : Type := (nat * nat * L * L * bool)%type.

Record state := mkst { cells : nat -> option T; next : nat; table : list (key * bool) }.

(** an outcome is true of the current terms of the two cells *)
Definition holds (st : state) (k : key) (b : bool) : Prop :=
  let '(i, j, l1, l2, pb) := k in
  exists t u, cells st i = Some t /\ cells st j = Some u /\ (b = true <-> rel pb (lift l1 t) (lift l2 u)).

Definition key_eq_dec : forall a b : key, {a = b} + {a <> b}.
Proof.
  intros [[[[i j] l1] l2] p] [[[[i' j'] l1'] l2'] p'].
  destruct (Nat.eq_dec i i'), (Nat.eq_dec j j'), (L_eq_dec l1 l1'), (L_eq_dec l2 l2'), (Bool.bool_dec p p'); subst;
    first [left; reflexivity | right; intro H; inversion H; subst; congruence].
Defined.

Fixpoint lookup (k : key) (tb : list (key * bool)) : option bool :=
  match tb with [] => None | (k', b) :: r => if key_eq_dec k k' then Some b else lookup k r end.

Definition upd (f : nat -> option T) (i : nat) (v : option T) : nat -> option T :=
  fun j => if Nat.eqb j i then v else f j.

(** [uid] on a cell without identity, holding [t]: it gets the counter's next value *)
Definition assign (st : state) (t : T) : state :=
  mkst (upd (cells st) (S (next st)) (Some t)) (S (next st)) (table st).
(** [update]: the term of cell [i] replaced in place by [t'] *)
Definition reduce (st : state) (i : nat) (t' : T) : state :=
  mkst (upd (cells st) i (Some t')) (next st) (table st).
(** [record]: an outcome stored *)
Definition record (st : state) (k : key) (b : bool) : state :=
  mkst (cells st) (next st) ((k, b) :: table st).

(** the states a check goes through: from the empty table, cells get identities, are reduced in place (by a reduct of
    their term), and the outcomes the kernel's comparison gives are stored *)
Inductive reach : state -> Prop :=
| R_init : reach (mkst (fun _ => None) 0 [])
| R_assign : forall st t, reach st -> reach (assign st t)
| R_reduce : forall st i t t', reach st -> cells st i = Some t -> red t t' -> reach (reduce st i t')
| R_record : forall st k b, reach st -> holds st k b -> reach (record st k b).

Definition inv (st : state) : Prop :=
  (forall i, cells st i <> None -> 1 <= i <= next st) /\ (forall k b, In (k, b) (table st) -> holds st k b).

Lemma lookup_in : forall k tb b, lookup k tb = Some b -> In (k, b) tb.
Proof.
  intros k tb. induction tb as [|[k' b'] r IH]; simpl; intros b H; [discriminate|].
  destruct (key_eq_dec k k') as [E|N].
  - subst. injection H as <-. left. reflexivity.
  - right. auto.
Qed.

Lemma inv_init : inv (mkst (fun _ => None) 0 []).
Proof. split; simpl; [intros i H; congruence | intros k b []]. Qed.

Lemma inv_assign : forall st t, inv st -> inv (assign st t).
Proof.
  intros st t [D Tb]. split.
  - intros i H. unfold assign, upd in *; simpl in *. destruct (Nat.eqb i (S (next st))) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + specialize (D i H). lia.
  - intros [[[[i j] l1] l2] pb] b Hin. simpl in Hin. destruct (Tb _ _ Hin) as (t1 & u1 & C1 & C2 & R).
    assert (Ni : i <> S (next st)) by (assert (1 <= i <= next st) by (apply D; congruence); lia).
    assert (Nj : j <> S (next st)) by (assert (1 <= j <= next st) by (apply D; congruence); lia).
    exists t1, u1. unfold assign, upd; simpl.
    rewrite (proj2 (Nat.eqb_neq _ _) Ni), (proj2 (Nat.eqb_neq _ _) Nj). auto.
Qed.

Lemma inv_reduce : forall st i t t', inv st -> cells st i = Some t -> red t t' -> inv (reduce st i t').
Proof.
  intros st i t t' [D Tb] Ci Rd. split.
  - intros j H. unfold reduce, upd in *; simpl in *. destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. subst j. apply D. congruence.
    + apply D. exact H.
  - intros [[[[i1 j1] l1] l2] pb] b Hin. simpl in Hin. destruct (Tb _ _ Hin) as (t1 & u1 & C1 & C2 & R).
    unfold reduce, upd; simpl.
    destruct (Nat.eqb i1 i) eqn:E1, (Nat.eqb j1 i) eqn:E2.
    + apply Nat.eqb_eq in E1, E2. subst. rewrite Ci in C1, C2. injection C1 as <-. injection C2 as <-.
      exists t', t'. split; [reflexivity|]. split; [reflexivity|].
      rewrite R, (rel_red_l pb l1 t t' (lift l2 t) Rd), (rel_red_r pb l2 t t' (lift l1 t') Rd). tauto.
    + apply Nat.eqb_eq in E1. subst. rewrite Ci in C1. injection C1 as <-.
      exists t', u1. split; [reflexivity|]. split; [exact C2|].
      rewrite R, (rel_red_l pb l1 t t' (lift l2 u1) Rd). tauto.
    + apply Nat.eqb_eq in E2. subst. rewrite Ci in C2. injection C2 as <-.
      exists t1, t'. split; [exact C1|]. split; [reflexivity|].
      rewrite R, (rel_red_r pb l2 t t' (lift l1 t1) Rd). tauto.
    + exists t1, u1. auto.
Qed.

Lemma inv_record : forall st k b, inv st -> holds st k b -> inv (record st k b).
Proof.
  intros st k b [D Tb] H. split; [exact D|].
  intros k' b' [E|Hin]; [injection E as -> ->; exact H | exact (Tb _ _ Hin)].
Qed.

Theorem reach_inv : forall st, reach st -> inv st.
Proof.
  induction 1.
  - apply inv_init.
  - apply inv_assign; auto.
  - eapply inv_reduce; eauto.
  - apply inv_record; auto.
Qed.

(** THE THEOREM: an outcome taken from the table is true of the current terms of the two cells *)
Theorem lookup_correct : forall st k b, reach st -> lookup k (table st) = Some b -> holds st k b.
Proof. intros st k b R Hl. apply (proj2 (reach_inv st R)). apply lookup_in. exact Hl. Qed.

(** the table never holds two outcomes for one key, so which entry a lookup finds does not matter *)
Theorem table_functional : forall st k b b', reach st -> In (k, b) (table st) -> In (k, b') (table st) -> b = b'.
Proof.
  intros st [[[[i j] l1] l2] pb] b b' R H1 H2. destruct (reach_inv st R) as [_ Tb].
  destruct (Tb _ _ H1) as (t1 & u1 & C1 & D1 & R1). destruct (Tb _ _ H2) as (t2 & u2 & C2 & D2 & R2).
  rewrite C1 in C2. injection C2 as <-. rewrite D1 in D2. injection D2 as <-.
  destruct b, b'; auto; [symmetry; apply R2, R1 | apply R1, R2]; reflexivity.
Qed.

(** the key of a problem: the kernel strips the [FLIFT n] wrappers of a cell into its lift ([strip_flift], [el_shft]),
    and the cell under the wrapper at the shifted lift denotes the same term -- so the key's outcome is the problem's *)
Variable shft : nat -> L -> L.
Variable flift : nat -> T -> T.        (* the term of a cell [FLIFT (n, v)], [v] holding the given term *)
Hypothesis lift_flift : forall n l t, lift l (flift n t) = lift (shft n l) t.

Corollary lookup_correct_flift : forall st i j n1 n2 l1 l2 pb b, reach st ->
  lookup (i, j, shft n1 l1, shft n2 l2, pb) (table st) = Some b ->
  exists t u, cells st i = Some t /\ cells st j = Some u /\ (b = true <-> rel pb (lift l1 (flift n1 t)) (lift l2 (flift n2 u))).
Proof.
  intros st i j n1 n2 l1 l2 pb b R Hl. destruct (lookup_correct _ _ _ R Hl) as (t & u & C1 & C2 & H).
  exists t, u. rewrite !lift_flift. auto.
Qed.

End Memo.

Print Assumptions lookup_correct.
Print Assumptions table_functional.
