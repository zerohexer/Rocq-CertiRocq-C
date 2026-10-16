(** End to end: a KQL run, generated to Clight and compiled by CompCert's
    back end, is an Asm program that terminates with the run's result
    (its low 32 bits, the exit code of [main]). *)

From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Cop Clight ClightBigstep Smallstep Behaviors Errors.
From compcert Require Asm.
From KQC Require Import KQL KQLGen KQLArith KQLProof KQLBack.
Import ListNotations.

Section TOP.

Variables (P : prog) (mainid g0 : ident) (args0 : list i63).
Let cp := tr_program P mainid g0 args0.
Let ge := Clight.globalenv cp.
Local Open Scope Z_scope.

(** Three checks on the source program, all decidable. *)
Hypothesis NAMES : list_norepet (map fst (pfuns P) ++ map fst (parrs P) ++ [mainid]).
Hypothesis PARAMS : forall g f, find P g = Some f -> list_norepet (kparams f).
Hypothesis SIZES : forall h n, asize P h = Some n -> 0 < n <= 2 ^ 28.

Lemma defs_names : prog_defs_names cp = map fst (pfuns P) ++ map fst (parrs P) ++ [mainid].
Proof.
  unfold prog_defs_names, cp, tr_program, tr_defs, tr_arrs. simpl.
  rewrite !map_app, !map_map. reflexivity.
Qed.

Lemma lookup_any : forall id g, In (id, g) (prog_defs cp) ->
  exists b, Genv.find_symbol ge id = Some b /\ Genv.find_def ge b = Some g.
Proof.
  intros id g I.
  change (In (id, g) (AST.prog_defs (program_of_program cp))) in I.
  apply (prog_defmap_norepet (program_of_program cp)) in I; [| rewrite defs_names; exact NAMES].
  apply Genv.find_def_symbol in I. exact I.
Qed.

Lemma lookup_def : forall id fd, In (id, Gfun fd) (prog_defs cp) ->
  exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some fd.
Proof.
  intros id fd I.
  change (In (id, Gfun fd) (AST.prog_defs (program_of_program cp))) in I.
  apply (prog_defmap_norepet (program_of_program cp)) in I; [| rewrite defs_names; exact NAMES].
  apply Genv.find_def_symbol in I. destruct I as (b & A & B).
  exists b. split. exact A. apply Genv.find_funct_ptr_iff. exact B.
Qed.

Lemma cp_funs : forall g f, find P g = Some f ->
  exists b, Genv.find_symbol ge g = Some b /\
            Genv.find_funct_ptr ge b = Some (Internal (tr_fn P f)).
Proof.
  intros g f F. apply lookup_def. simpl. apply in_or_app. left.
  unfold tr_defs. apply in_map_iff. exists (g, f). split; auto. apply assoc_in; auto.
Qed.

(** The zeroed global arrays are KQL's initial memory. *)
Lemma init_mrel : forall m0, Genv.init_mem cp = Some m0 -> mrel P cp mem0 m0.
Proof.
  intros m0 IM h n SZ.
  pose proof (SIZES h n SZ) as SN.
  destruct (lookup_any h (Gvar (arr_var n))) as (b & FS & FD).
  { simpl. apply in_or_app. right. apply in_or_app. left.
    unfold tr_arrs. apply in_map_iff. exists (h, n). split; auto. apply assoc_in; auto. }
  exists b. split; auto.
  assert (FV : Genv.find_var_info (Genv.globalenv cp) b = Some (arr_var n)).
  { apply Genv.find_var_info_iff. exact FD. }
  destruct (Genv.init_mem_characterization _ _ FV IM) as (RP & _ & LS & _).
  destruct (LS eq_refl) as (RZ & _).
  intros j J. split.
  - rewrite (RZ Mint64 (8 * j)). reflexivity. lia.
    change (size_chunk Mint64) with 8. lia.
    exists j. change (align_chunk Mint64) with 8. lia.
  - split.
    + intros ofs O. apply RP. change (size_chunk Mint64) with 8 in O.
      unfold arr_var, init_data_list_size, init_data_size. cbn [gvar_init]. lia.
    + exists j. change (align_chunk Mint64) with 8. lia.
Qed.

Lemma eval_consts : forall e le m (l : list i63),
  eval_exprlist ge e le m (map (fun n => c64 (to_Z n)) l) (tylist (length l)) (map enc l).
Proof.
  induction l; simpl; econstructor; eauto. apply eval_Econst_long. reflexivity.
Qed.

Lemma cast_l2i : forall x m,
  sem_cast (Vlong x) tyl type_int32s m = Some (Vint (Int.repr (Int64.unsigned x))).
Proof. reflexivity. Qed.

Theorem prog_terminates : forall v M', run P g0 args0 mem0 v M' ->
  Clight2.bigstep_program_terminates cp E0 (Int.repr (to_Z v)).
Proof.
  intros v M' R.
  pose proof cp_funs as CF.
  destruct (Genv.init_mem_exists cp) as (m0 & IM).
  { intros id gv I. simpl in I. apply in_app_or in I. destruct I as [I|I].
    - exfalso. unfold tr_defs in I. apply in_map_iff in I. destruct I as (x & E & _). discriminate.
    - apply in_app_or in I. destruct I as [I|[I|[]]].
      + unfold tr_arrs in I. apply in_map_iff in I. destruct I as (x & E & _). inv E.
        split; cbn. split; [apply Z.divide_0_r | trivial]. intros i o [H|[]]; discriminate.
      + discriminate. }
  destruct (lookup_def mainid (Internal (main_fn g0 args0))) as (bm & MS & MF).
  { simpl. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
  destruct (run_funcall P cp CF PARAMS SIZES g0 args0 mem0 v M' R) as (fg & b & FS & FP & LEN & FC).
  destruct (FC m0 (init_mrel m0 IM)) as (m1 & FC1 & _).
  econstructor; [exact IM | exact MS | exact MF | reflexivity | ].
  set (le0 := create_undef_temps [(rtemp, tyl)]).
  set (le1 := PTree.set rtemp (enc v) le0).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (m1 := m0) (le2 := le1) (m2 := m1)
    (out := Out_return (Some (Vint (Int.repr (to_Z v)), type_int32s))).
  - constructor; simpl; try constructor. intros x y Hx. destruct Hx.
  - change E0 with (E0 ** E0). eapply exec_Sseq_1.
    + change le1 with (set_opttemp (Some rtemp) (enc v) le0).
      eapply exec_Scall with (vf := Vptr b Ptrofs.zero) (tyargs := tylist (length args0)).
      * reflexivity.
      * eapply eval_Elvalue. apply eval_Evar_global; [apply PTree.gempty | exact FS].
        apply deref_loc_reference. reflexivity.
      * apply eval_consts.
      * rewrite Genv.find_funct_find_funct_ptr. exact FP.
      * change (type_of_fundef (Internal (tr_fn P fg))) with
          (Tfunction (type_of_params (map (fun p => (p, tyl)) (map tv (kparams fg)))) tyl cc_default).
        rewrite type_of_params_tr. rewrite LEN. reflexivity.
      * exact FC1.
    + replace (Int.repr (to_Z v)) with (Int.repr (Int64.unsigned (Int64.repr (to_Z v))))
        by (rewrite uns_phi; reflexivity).
      change type_int32s with (typeof (Ecast (Etempvar rtemp tyl) type_int32s)).
      apply exec_Sreturn_some. econstructor. apply eval_Etempvar. apply PTree.gss.
      apply cast_l2i.
  - simpl. split. discriminate. reflexivity.
  - reflexivity.
Qed.

Theorem prog_behaves : forall v M', run P g0 args0 mem0 v M' ->
  program_behaves (Clight.semantics2 cp) (Terminates E0 (Int.repr (to_Z v))).
Proof.
  intros v M' R. eapply behavior_bigstep_terminates.
  apply Clight2.bigstep_semantics_sound. eapply prog_terminates; eauto.
Qed.

(** The headline: if CompCert's back end accepts the generated program,
    the assembly program terminates with the run's result. *)
Theorem kql_compiled_correct : forall v M' tp,
  run P g0 args0 mem0 v M' ->
  transf_clight2_program cp = OK tp ->
  program_behaves (Asm.semantics tp) (Terminates E0 (Int.repr (to_Z v))).
Proof.
  intros v M' tp R T. eapply transf_clight2_terminates; eauto. eapply prog_behaves; eauto.
Qed.

End TOP.
