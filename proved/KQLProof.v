(** Correctness of the generator: every KQL evaluation is matched by a
    big-step Clight execution (parameters as temporaries, CompCert's
    [function_entry2]) that returns the encoded value, with the KQL
    memory blocks held in the global arrays. *)

From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Cop Clight ClightBigstep.
From KQC Require Import KQL KQLGen KQLArith.
Import ListNotations.

(** ** Generic facts *)

Lemma tv_inj : forall x y, tv x = tv y -> x = y.
Proof. unfold tv; intros; congruence. Qed.

Lemma sc_inj : forall i j, sc i = sc j -> i = j.
Proof. unfold sc; intros i j H. injection H. apply SuccNat2Pos.inj. Qed.

Lemma tv_sc : forall x i, tv x <> sc i.
Proof. unfold tv, sc; congruence. Qed.

Lemma typeof_atom : forall a, typeof (tr_atom a) = tyl.
Proof. destruct a; reflexivity. Qed.

Lemma bind_length : forall xs vs rho rho', bind xs vs rho = Some rho' -> length xs = length vs.
Proof.
  induction xs; destruct vs; simpl; intros; try discriminate; auto.
  f_equal. eauto.
Qed.

Lemma avals_length : forall rho l vs, avals rho l = Some vs -> length l = length vs.
Proof.
  induction l; simpl; intros vs H. inv H; auto.
  destruct (aval rho a); try discriminate. destruct (avals rho l) eqn:E; try discriminate.
  inv H. simpl. f_equal. eauto.
Qed.

Lemma assoc_in : forall A (l : list (ident * A)) g f, assoc l g = Some f -> In (g, f) l.
Proof.
  induction l as [|[h fh] l IH]; simpl; intros g f H. discriminate.
  destruct (peq g h). inv H. auto. right. eauto.
Qed.

(** ** Agreement between a KQL environment and a Clight temporary environment *)

Definition agree (rho : env) (le : temp_env) : Prop :=
  forall x v, rho ! x = Some v -> le ! (tv x) = Some (enc v).

Lemma agree_empty : forall le, agree (PTree.empty _) le.
Proof. intros le x v H. rewrite PTree.gempty in H. discriminate. Qed.

Lemma agree_set : forall rho le x v,
  agree rho le -> agree (PTree.set x v rho) (PTree.set (tv x) (enc v) le).
Proof.
  intros rho le x v A y w H. rewrite PTree.gsspec in H. destruct (peq y x).
  - subst. inv H. apply PTree.gss.
  - rewrite PTree.gso. auto. intro E. apply tv_inj in E. auto.
Qed.

Lemma agree_set_sc : forall rho le i v, agree rho le -> agree rho (PTree.set (sc i) v le).
Proof.
  intros rho le i v A y w H. rewrite PTree.gso. auto. apply tv_sc.
Qed.

Local Open Scope Z_scope.

Section SIM.

Variable P : prog.
Variable cp : Clight.program.
Let ge := Clight.globalenv cp.

(** The functions of [P] are in [cp], translated. *)
Hypothesis cp_funs : forall g f, find P g = Some f ->
  exists b, Genv.find_symbol ge g = Some b /\
            Genv.find_funct_ptr ge b = Some (Internal (tr_fn P f)).
Hypothesis params_norepet : forall g f, find P g = Some f -> list_norepet (kparams f).
Hypothesis sizes : forall h n, asize P h = Some n -> 0 < n <= 2 ^ 28.

Notation exec := (ClightBigstep.exec_stmt function_entry2 ge).
Notation funcall := (ClightBigstep.eval_funcall function_entry2 ge).

Section EXPR.
Variables (e : Clight.env) (le : temp_env) (m : mem) (rho : KQL.env).
Hypothesis AG : agree rho le.

Lemma eval_atom : forall a v, aval rho a = Some v -> eval_expr ge e le m (tr_atom a) (enc v).
Proof.
  destruct a; simpl; intros v H.
  - apply eval_Etempvar. auto.
  - inv H. apply eval_Econst_long.
Qed.

Lemma eval_atoms : forall l vs, avals rho l = Some vs ->
  eval_exprlist ge e le m (map tr_atom l) (tylist (length l)) (map enc vs).
Proof.
  induction l as [|a l IH]; simpl; intros vs H.
  - inv H. constructor.
  - destruct (aval rho a) eqn:A; try discriminate.
    destruct (avals rho l) eqn:L; try discriminate. inv H. simpl.
    econstructor. eapply eval_atom; eauto. rewrite typeof_atom. reflexivity. auto.
Qed.

Lemma eval_bin : forall op A B x y v ty,
  eval_expr ge e le m A (Vlong x) -> eval_expr ge e le m B (Vlong y) ->
  typeof A = tyl -> typeof B = tyl ->
  sem_binary_operation ge op (Vlong x) tyl (Vlong y) tyl m = Some v ->
  eval_expr ge e le m (Ebinop op A B ty) v.
Proof.
  intros. econstructor; eauto. rewrite H1, H2. auto.
Qed.

Lemma eval_cmp : forall c a b va vb,
  aval rho a = Some va -> aval rho b = Some vb ->
  eval_expr ge e le m (cmpe (tr_cmp c) (tr_atom a) (tr_atom b)) (Val.of_bool (cmp_sem c va vb)).
Proof.
  intros c a b va vb Ha Hb.
  eapply eval_bin; try apply eval_atom; eauto; try apply typeof_atom.
  destruct c; simpl.
  - rewrite <- enc_inj_eq. reflexivity.
  - rewrite <- enc_ltu. reflexivity.
  - rewrite <- enc_leu. reflexivity.
Qed.

End EXPR.

Lemma bool_of : forall b m, bool_val (Val.of_bool b) tyb m = Some b.
Proof. destruct b; reflexivity. Qed.

Lemma cast_ll : forall x m, sem_cast (Vlong x) tyl (Tlong Unsigned noattr) m = Some (Vlong x).
Proof. reflexivity. Qed.

Ltac ev := repeat first [ eapply eval_bin | eassumption | apply eval_Econst_long | reflexivity ].

Lemma exec_op : forall le m rho x o a b va vb,
  agree rho le -> aval rho a = Some va -> aval rho b = Some vb ->
  exec empty_env le m (tr_op x o (tr_atom a) (tr_atom b))
       E0 (PTree.set (tv x) (enc (binop_sem o va vb)) le) m Out_normal.
Proof.
  intros le m rho x o a b va vb AG Ha Hb.
  assert (EA := eval_atom empty_env le m rho AG a va Ha).
  assert (EB := eval_atom empty_env le m rho AG b vb Hb).
  pose proof (typeof_atom a) as TA. pose proof (typeof_atom b) as TB.
  assert (Z0 : eval_expr ge empty_env le m (c64 0) (Vlong (Int64.repr 0))) by apply eval_Econst_long.
  assert (Z63 : eval_expr ge empty_env le m (c64 63) (Vlong (Int64.repr 63))) by apply eval_Econst_long.
  unfold enc in *.
  destruct o; simpl; unfold tr_op.
  - apply exec_Sset. rewrite <- add_enc. ev.
  - apply exec_Sset. rewrite <- sub_enc. ev.
  - apply exec_Sset. rewrite <- mul_enc. ev.
  - apply exec_Sset. rewrite <- land_enc. ev.
  - apply exec_Sset. rewrite <- lor_enc. ev.
  - apply exec_Sset. rewrite <- lxor_enc. ev.
  - eapply exec_Sifthenelse. ev. apply bool_of.
    simpl. rewrite eq_zero. destruct (PrimInt63.eqb vb 0) eqn:Z.
    + apply exec_Sset. rewrite <- (div0_enc va vb Z). apply eval_Econst_long.
    + apply exec_Sset. rewrite <- div_enc. eapply eval_bin; eauto.
      simpl. unfold sem_div, sem_binarith. simpl. rewrite !cast_ll.
      change Int64.zero with (Int64.repr 0). rewrite eq_zero, Z. reflexivity.
  - eapply exec_Sifthenelse. ev. apply bool_of.
    simpl. rewrite eq_zero. destruct (PrimInt63.eqb vb 0) eqn:Z.
    + apply exec_Sset. rewrite <- (mod0_enc va vb Z). auto.
    + apply exec_Sset. rewrite <- mod_enc. eapply eval_bin; eauto.
      simpl. unfold sem_mod, sem_binarith. simpl. rewrite !cast_ll.
      change Int64.zero with (Int64.repr 0). rewrite eq_zero, Z. reflexivity.
  - eapply exec_Sifthenelse. ev. apply bool_of.
    simpl. rewrite ltu_63. destruct (Z.ltb_spec (to_Z vb) 63) as [L|L].
    + apply exec_Sset. rewrite <- (lsl_enc va vb L).
      eapply eval_bin; [ | apply eval_Econst_long | reflexivity | reflexivity | reflexivity ].
      eapply eval_bin; eauto.
      simpl. unfold sem_shl, sem_shift. simpl. rewrite ltu_iword by auto. reflexivity.
    + apply exec_Sset. rewrite <- (lsl_big va vb L). apply eval_Econst_long.
  - eapply exec_Sifthenelse. ev. apply bool_of.
    simpl. rewrite ltu_63. destruct (Z.ltb_spec (to_Z vb) 63) as [L|L].
    + apply exec_Sset. rewrite <- (lsr_enc va vb L).
      eapply eval_bin; eauto.
      simpl. unfold sem_shr, sem_shift. simpl. rewrite ltu_iword by auto. reflexivity.
    + apply exec_Sset. rewrite <- (lsr_big va vb L). apply eval_Econst_long.
Qed.

(** ** Memory blocks *)

Definition mrel (M : kmem) (m : mem) : Prop :=
  forall h n, asize P h = Some n ->
  exists b, Genv.find_symbol ge h = Some b /\
    forall j, 0 <= j < n ->
      Mem.load Mint64 m b (8 * j) = Some (enc (M h j)) /\
      Mem.valid_access m Mint64 b (8 * j) Writable.

Lemma ptrofs_mod : Ptrofs.modulus = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma offset_ok : forall j, 0 <= j < 2 ^ 28 ->
  Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr j)))
  = Ptrofs.repr (8 * j).
Proof.
  intros j H. rewrite Ptrofs.add_zero_l. unfold Ptrofs.mul, Ptrofs.of_int64.
  rewrite (Int64.unsigned_repr j) by (unfold Int64.max_unsigned; rewrite mod64; lia).
  rewrite !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; rewrite ptrofs_mod; lia).
  reflexivity.
Qed.

Lemma uns_off : forall j, 0 <= j < 2 ^ 28 -> Ptrofs.unsigned (Ptrofs.repr (8 * j)) = 8 * j.
Proof.
  intros. apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned. rewrite ptrofs_mod. lia.
Qed.

Lemma ltu_n : forall (i : i63) n, 0 < n <= 2 ^ 28 ->
  Int64.ltu (Int64.repr (to_Z i)) (Int64.repr n) = inb n i.
Proof.
  intros i n H. unfold Int64.ltu, inb. rewrite uns_phi, (uns_small n) by lia.
  destruct (zlt (to_Z i) n); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma eval_cell_addr : forall le m h n b i vi,
  Genv.find_symbol ge h = Some b ->
  eval_expr ge empty_env le m (tr_atom i) (enc vi) -> to_Z vi < 2 ^ 28 ->
  eval_expr ge empty_env le m (Ebinop Oadd (Evar h (tarr n)) (tr_atom i) (Tpointer tyl noattr))
            (Vptr b (Ptrofs.repr (8 * to_Z vi))).
Proof.
  intros le m h n b i vi FS EI L.
  econstructor.
  - eapply eval_Elvalue. apply eval_Evar_global; [apply PTree.gempty | exact FS].
    apply deref_loc_reference. reflexivity.
  - exact EI.
  - rewrite typeof_atom. simpl. unfold sem_add. simpl.
    rewrite offset_ok by (pose proof (phi_range vi); lia). reflexivity.
Qed.

Lemma exec_load : forall le m rho M x h i n vi,
  agree rho le -> mrel M m -> asize P h = Some n -> aval rho i = Some vi ->
  exec empty_env le m
    (Sifthenelse (cmpe Olt (tr_atom i) (c64 n))
       (Sset (tv x) (cell h n (tr_atom i))) (Sset (tv x) (c64 0)))
    E0 (PTree.set (tv x) (enc (rd M n h vi)) le) m Out_normal.
Proof.
  intros le m rho M x h i n vi AG MR SZ Hi.
  pose proof (sizes h n SZ) as SN.
  assert (EI := eval_atom empty_env le m rho AG i vi Hi).
  eapply exec_Sifthenelse.
  - eapply eval_bin; [exact EI | apply eval_Econst_long | apply typeof_atom | reflexivity | reflexivity].
  - apply bool_of.
  - simpl. rewrite ltu_n by auto. unfold rd. destruct (inb n vi) eqn:IN.
    + apply exec_Sset. unfold inb in IN. apply Z.ltb_lt in IN.
      destruct (MR h n SZ) as (b & FS & CELLS).
      pose proof (phi_range vi) as PR.
      destruct (CELLS (to_Z vi)) as (LD & _). lia.
      eapply eval_Elvalue.
      * apply eval_Ederef. eapply eval_cell_addr; eauto. lia.
      * eapply deref_loc_value. reflexivity. unfold Mem.loadv. rewrite uns_off by lia. exact LD.
    + apply exec_Sset. apply eval_Econst_long.
Qed.

Lemma mrel_store : forall M m h n b j v m',
  mrel M m -> asize P h = Some n -> Genv.find_symbol ge h = Some b -> 0 <= j < n ->
  Mem.store Mint64 m b (8 * j) (enc v) = Some m' ->
  mrel (upd M h j v) m'.
Proof.
  intros M m h n b j v m' MR SZ FS J ST h' n' SZ'.
  destruct (MR h' n' SZ') as (b' & FS' & CELLS).
  exists b'. split; auto. intros j' J'.
  destruct (CELLS j' J') as (LD & VA). split.
  - unfold upd. destruct (peq h' h) as [E|E].
    + subst h'. rewrite FS in FS'. inv FS'. destruct (Z.eq_dec j' j) as [E|E].
      * subst j'. erewrite Mem.load_store_same by eauto. reflexivity.
      * rewrite (Mem.load_store_other _ _ _ _ _ _ ST). exact LD.
        right. change (size_chunk Mint64) with 8. destruct (zlt j' j); [left | right]; lia.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ ST). exact LD.
      left. eapply Genv.global_addresses_distinct; eauto.
  - eapply Mem.store_valid_access_1; eauto.
Qed.

Lemma exec_store : forall le m rho M h i a n vi va,
  agree rho le -> mrel M m -> asize P h = Some n -> aval rho i = Some vi -> aval rho a = Some va ->
  exists m', exec empty_env le m
    (Sifthenelse (cmpe Olt (tr_atom i) (c64 n))
       (Sassign (cell h n (tr_atom i)) (tr_atom a)) Sskip)
    E0 le m' Out_normal /\ mrel (wr M n h vi va) m'.
Proof.
  intros le m rho M h i a n vi va AG MR SZ Hi Ha.
  pose proof (sizes h n SZ) as SN.
  assert (EI := eval_atom empty_env le m rho AG i vi Hi).
  assert (EA := eval_atom empty_env le m rho AG a va Ha).
  unfold wr. destruct (inb n vi) eqn:IN.
  - unfold inb in IN. apply Z.ltb_lt in IN. pose proof (phi_range vi) as PR.
    destruct (MR h n SZ) as (b & FS & CELLS).
    destruct (CELLS (to_Z vi)) as (_ & VA). lia.
    destruct (Mem.valid_access_store m Mint64 b (8 * to_Z vi) (enc va) VA) as (m' & ST).
    exists m'. split.
    + eapply exec_Sifthenelse.
      * eapply eval_bin; [exact EI | apply eval_Econst_long | apply typeof_atom | reflexivity | reflexivity].
      * apply bool_of.
      * simpl. rewrite ltu_n by auto.
        assert (inb n vi = true) as -> by (unfold inb; apply Z.ltb_lt; lia).
        eapply exec_Sassign.
        -- apply eval_Ederef. eapply eval_cell_addr; eauto. lia.
        -- exact EA.
        -- rewrite typeof_atom. reflexivity.
        -- eapply assign_loc_value. reflexivity. unfold Mem.storev. rewrite uns_off by lia. exact ST.
    + eapply mrel_store; eauto. lia.
  - exists m. split; auto.
    eapply exec_Sifthenelse.
    + eapply eval_bin; [exact EI | apply eval_Econst_long | apply typeof_atom | reflexivity | reflexivity].
    + apply bool_of.
    + simpl. rewrite ltu_n, IN by auto. constructor.
Qed.

(** ** The loop: [Eloop]'s assignments *)

Lemma scratch_keep : forall args k le0 m t le0' m' out i,
  exec empty_env le0 m (set_scratch k args) t le0' m' out -> (i < k)%nat ->
  le0' ! (sc i) = le0 ! (sc i).
Proof.
  induction args as [|a args IH]; simpl; intros k le0 m t le0' m' out i X L.
  - inv X. auto.
  - inv X.
    + match goal with H: exec _ _ _ (Sset _ _) _ _ _ _ |- _ => inv H end.
      match goal with H: exec _ _ _ (set_scratch _ _) _ _ _ _ |- _ =>
        rewrite (IH _ _ _ _ _ _ _ i H) by lia end.
      rewrite PTree.gso. auto. intro E. apply sc_inj in E. lia.
    + match goal with H: exec _ _ _ (Sset _ _) _ _ _ _ |- _ => inv H end. congruence.
Qed.

Lemma exec_scratch : forall rho args vs i le m,
  agree rho le -> avals rho args = Some vs ->
  exists le', exec empty_env le m (set_scratch i args) E0 le' m Out_normal /\
    agree rho le' /\
    (forall j v, nth_error vs j = Some v -> le' ! (sc (i + j)) = Some (enc v)).
Proof.
  intros rho. induction args as [|a args IH]; simpl; intros vs i le m AG H.
  - inv H. exists le. split. constructor. split. auto.
    intros j v N. destruct j; discriminate.
  - destruct (aval rho a) as [va|] eqn:Ha; try discriminate.
    destruct (avals rho args) as [vs'|] eqn:Hl; try discriminate. inv H.
    set (le1 := PTree.set (sc i) (enc va) le).
    destruct (IH vs' (S i) le1 m) as (le' & X & AG' & SC); auto.
    { apply agree_set_sc; auto. }
    exists le'. split.
    { change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
      apply exec_Sset. eapply eval_atom; eauto. }
    split. auto.
    intros j v N. destruct j as [|j]; simpl in N.
    + inv N. rewrite Nat.add_0_r. rewrite (scratch_keep args (S i) le1 m E0 le' m Out_normal i X) by lia.
      apply PTree.gss.
    + replace (i + S j)%nat with (S i + j)%nat by lia. auto.
Qed.

Lemma exec_params : forall ps vs i rho0 rho' le m,
  agree rho0 le -> bind ps vs rho0 = Some rho' ->
  (forall j v, nth_error vs j = Some v -> le ! (sc (i + j)) = Some (enc v)) ->
  exists le', exec empty_env le m (set_params i ps) E0 le' m Out_normal /\ agree rho' le'.
Proof.
  induction ps as [|p ps IH]; destruct vs as [|v vs]; simpl; intros i rho0 rho' le m AG B SC;
    try discriminate.
  - inv B. exists le. split. constructor. auto.
  - destruct (IH vs (S i) (PTree.set p v rho0) rho' (PTree.set (tv p) (enc v) le) m)
      as (le' & X & AG'); auto.
    { apply agree_set; auto. }
    { intros j w N. rewrite PTree.gso by apply not_eq_sym, tv_sc.
      replace (S i + j)%nat with (i + S j)%nat by lia. apply SC. auto. }
    exists le'. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
    apply exec_Sset. apply eval_Etempvar. rewrite <- (Nat.add_0_r i). apply SC. reflexivity.
Qed.

(** ** Function entry *)

Lemma bind_temps : forall ps vs rho0 rho' le0,
  agree rho0 le0 -> bind ps vs rho0 = Some rho' ->
  exists le', bind_parameter_temps (map (fun p => (p, tyl)) (map tv ps)) (map enc vs) le0 = Some le'
              /\ agree rho' le'.
Proof.
  induction ps as [|p ps IH]; destruct vs as [|v vs]; simpl; intros rho0 rho' le0 AG B;
    try discriminate.
  - inv B. eauto.
  - eapply IH; eauto. apply agree_set; auto.
Qed.

Lemma type_of_params_tr : forall ps,
  type_of_params (map (fun p => (p, tyl)) (map tv ps)) = tylist (length ps).
Proof. induction ps; simpl; congruence. Qed.

Lemma notin_spec : forall ps t, notin ps t = true -> ~ In t ps.
Proof.
  unfold notin. intros ps t H I. apply negb_true_iff in H.
  assert (existsb (Pos.eqb t) ps = true).
  { apply existsb_exists. exists t. split; auto. apply Pos.eqb_refl. }
  congruence.
Qed.

Lemma entry_ok : forall f vs rho m,
  list_norepet (kparams f) ->
  bind (kparams f) vs (PTree.empty _) = Some rho ->
  exists le, function_entry2 ge (tr_fn P f) (map enc vs) m empty_env le m /\ agree rho le.
Proof.
  intros f vs rho m NR B.
  destruct (bind_temps (kparams f) vs (PTree.empty _) rho
              (create_undef_temps (fn_temps (tr_fn P f)))) as (le & BT & AG); auto.
  { apply agree_empty. }
  exists le. split; auto. constructor; simpl.
  - constructor.
  - unfold var_names. rewrite map_map. simpl. rewrite map_id.
    apply list_map_norepet; auto. intros x y _ _ D E. apply tv_inj in E. auto.
  - unfold var_names. rewrite !map_map. simpl. rewrite map_id.
    intros x y Hx Hy E. subst y. apply in_app_or in Hy. destruct Hy as [Hy|Hy].
    + apply filter_In in Hy. destruct Hy as [_ Hy]. apply notin_spec in Hy. auto.
    + apply in_map_iff in Hx. destruct Hx as (p & <- & _).
      apply in_map_iff in Hy. destruct Hy as (j & E & _). symmetry in E. revert E. apply tv_sc.
  - constructor.
  - exact BT.
Qed.

(** ** The simulation *)

Definition LOOP (f : fn) (le : temp_env) (m : mem) (v : i63) (M' : kmem) : Prop :=
  exists le' m', exec empty_env le m (Sloop (tr_exp P (kparams f) (kbody f)) Sskip)
                      E0 le' m' (Out_return (Some (enc v, tyl))) /\ mrel M' m'.

Definition SIMR (f : fn) (le : temp_env) (m : mem) (s : statement) (v : i63) (M' : kmem) : Prop :=
  exists le1 m1 out, exec empty_env le m s E0 le1 m1 out /\
    ((out = Out_return (Some (enc v, tyl)) /\ mrel M' m1) \/
     (out = Out_continue /\ LOOP f le1 m1 v M')).

Lemma to_loop : forall f le m v M',
  SIMR f le m (tr_exp P (kparams f) (kbody f)) v M' -> LOOP f le m v M'.
Proof.
  intros f le m v M' (le1 & m1 & out & X & [[R MR] | [R L]]); subst.
  - exists le1, m1. split; auto. eapply exec_Sloop_stop1; eauto. constructor.
  - destruct L as (le2 & m2 & X2 & MR). exists le2, m2. split; auto.
    change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop; eauto.
    constructor. constructor.
Qed.

Lemma funcall_ok : forall fg vs rho w M M1 m,
  list_norepet (kparams fg) ->
  bind (kparams fg) vs (PTree.empty _) = Some rho ->
  (forall le m, agree rho le -> mrel M m -> SIMR fg le m (tr_exp P (kparams fg) (kbody fg)) w M1) ->
  mrel M m ->
  exists m1, funcall m (Internal (tr_fn P fg)) (map enc vs) E0 m1 (enc w) /\ mrel M1 m1.
Proof.
  intros fg vs rho w M M1 m NR B IH MR.
  destruct (entry_ok fg vs rho m NR B) as (le & EN & AG).
  destruct (to_loop fg le m w M1 (IH le m AG MR)) as (le' & m' & X & MR').
  exists m'. split; auto.
  econstructor; [exact EN | exact X | simpl; split; [discriminate | reflexivity] | reflexivity].
Qed.

Lemma exec_call : forall le m m1 rho x g args vs fg rho' w,
  agree rho le -> find P g = Some fg -> avals rho args = Some vs ->
  bind (kparams fg) vs (PTree.empty _) = Some rho' ->
  funcall m (Internal (tr_fn P fg)) (map enc vs) E0 m1 (enc w) ->
  exec empty_env le m (Scall (Some (tv x)) (Evar g (funty (length args))) (map tr_atom args))
       E0 (PTree.set (tv x) (enc w) le) m1 Out_normal.
Proof.
  intros le m m1 rho x g args vs fg rho' w AG F A B FC.
  destruct (cp_funs g fg F) as (b & FS & FP).
  change (PTree.set (tv x) (enc w) le) with (set_opttemp (Some (tv x)) (enc w) le).
  eapply exec_Scall with (vf := Vptr b Ptrofs.zero) (tyargs := tylist (length args)).
  - reflexivity.
  - eapply eval_Elvalue. apply eval_Evar_global; [apply PTree.gempty | exact FS].
    apply deref_loc_reference. reflexivity.
  - eapply eval_atoms; eauto.
  - rewrite Genv.find_funct_find_funct_ptr. exact FP.
  - change (type_of_fundef (Internal (tr_fn P fg))) with
      (Tfunction (type_of_params (map (fun p => (p, tyl)) (map tv (kparams fg)))) tyl cc_default).
    rewrite type_of_params_tr. apply bind_length in B. apply avals_length in A.
    rewrite B, <- A. reflexivity.
  - exact FC.
Qed.

Theorem sim : forall f rho M e v M', eval P f rho M e v M' ->
  forall le m, agree rho le -> mrel M m -> SIMR f le m (tr_exp P (kparams f) e) v M'.
Proof.
  induction 1; intros le m AG MR; cbn [tr_exp].
  - (* ret *)
    exists le, m, (Out_return (Some (enc v, tyl))). split; auto.
    rewrite <- (typeof_atom a). apply exec_Sreturn_some. eapply eval_atom; eauto.
  - (* op *)
    destruct (IHeval _ m (agree_set rho le x _ AG) MR) as (le1 & m1 & out & X & R).
    exists le1, m1, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto. eapply exec_op; eauto.
  - (* if *)
    destruct (IHeval le m AG MR) as (le1 & m1 & out & X & R).
    exists le1, m1, out. split; auto.
    eapply exec_Sifthenelse. eapply eval_cmp; eauto. apply bool_of.
    destruct (cmp_sem c va vb); auto.
  - (* call *)
    destruct (funcall_ok fg vs rho' w M M1 m (params_norepet g fg H) H1
                (fun le m AG MR => IHeval1 le m AG MR) MR) as (m1 & FC & MR1).
    destruct (IHeval2 _ m1 (agree_set rho le x w AG) MR1) as (le2 & m2 & out & X & R).
    exists le2, m2, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto. eapply exec_call; eauto.
  - (* load *)
    rewrite H.
    destruct (IHeval _ m (agree_set rho le x _ AG) MR) as (le1 & m1 & out & X & R).
    exists le1, m1, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto. eapply exec_load; eauto.
  - (* store *)
    rewrite H.
    destruct (exec_store le m rho M h i a n vi va AG MR H H0 H1) as (m1 & XS & MR1).
    destruct (IHeval le m1 AG MR1) as (le2 & m2 & out & X & R).
    exists le2, m2, out. split; auto.
    change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
  - (* loop *)
    destruct (exec_scratch rho args vs 0 le m AG H) as (le1 & X1 & AG1 & SC).
    destruct (exec_params (kparams f) vs 0 (PTree.empty _) rho' le1 m (agree_empty le1) H0 SC)
      as (le2 & X2 & AG2).
    exists le2, m, Out_continue. split.
    + change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
      change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto. constructor.
    + right. split; auto. apply to_loop. eapply IHeval; eauto.
Qed.

(** A run of function [g] is a Clight call of its translation. *)
Theorem run_funcall : forall g vs M v M', run P g vs M v M' ->
  exists fg b, Genv.find_symbol ge g = Some b /\
    Genv.find_funct_ptr ge b = Some (Internal (tr_fn P fg)) /\
    length (kparams fg) = length vs /\
    forall m, mrel M m ->
      exists m', funcall m (Internal (tr_fn P fg)) (map enc vs) E0 m' (enc v) /\ mrel M' m'.
Proof.
  intros g vs M v M' (fg & rho & F & B & EV).
  destruct (cp_funs g fg F) as (b & FS & FP).
  exists fg, b. split; auto. split; auto. split. eapply bind_length; eauto.
  intros m MR. eapply funcall_ok; eauto. intros le m0 AG MR0. eapply sim; eauto.
Qed.

End SIM.
