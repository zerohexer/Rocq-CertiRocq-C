(** End to end for kit programs: a KQL program over the kit's memory, generated to Clight, runs in Clight to what
    the KQL run says, from any Clight memory that holds the kit's memory in the two tables the loader sets.

    Proved: the generated Clight functions compute what their Rocq definitions compute (KQMTrans.v statements,
    KQMAuto.v proofs, [kit_function_correct] here).  Trusted: the loader that fills the tables (kq_tab, kq_lens)
    from the program's starting memory, and the laws of the kit's memory (KQSpec.v, [real_laws]). *)

From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Cop Clight ClightBigstep.
From KQC Require Import KQL KQLGen KQTArith KQLProof KQM.
Import ListNotations.

Local Open Scope Z_scope.

Definition kit_tab_var : globvar type :=
  {| gvar_info := Tarray tptr kq_nblocks noattr; gvar_init := [Init_space (8 * kq_nblocks)];
     gvar_readonly := false; gvar_volatile := false |}.
Definition kit_lens_var : globvar type :=
  {| gvar_info := Tarray t32 kq_nblocks noattr; gvar_init := [Init_space (4 * kq_nblocks)];
     gvar_readonly := false; gvar_volatile := false |}.

Definition kit_tab32_var : globvar type :=
  {| gvar_info := Tarray tptr32 kq_nblocks noattr; gvar_init := [Init_space (8 * kq_nblocks)];
     gvar_readonly := false; gvar_volatile := false |}.
Definition kit_lens32_var : globvar type :=
  {| gvar_info := Tarray t32 kq_nblocks noattr; gvar_init := [Init_space (4 * kq_nblocks)];
     gvar_readonly := false; gvar_volatile := false |}.

(** the program's functions and the four tables (the blocks of 8-byte cells, the narrow blocks) *)
Definition tr_kit_program (P : prog) : Clight.program :=
  {| prog_defs := tr_defs P ++ hw_defs ++ hwf_defs ++ [(kq_tab, Gvar kit_tab_var); (kq_lens, Gvar kit_lens_var);
                                (kq_tab32, Gvar kit_tab32_var); (kq_lens32, Gvar kit_lens32_var)];
     prog_public := [];
     prog_main := 1%positive;
     prog_types := [];
     prog_comp_env := PTree.empty _;
     prog_comp_env_eq := eq_refl |}.

(** two checks on the program, both decided by computation *)
Definition names_ok (P : prog) : bool :=
  if list_norepet_dec peq (map fst (pfuns P) ++ map hwid hw_all ++ map hwfid hwf_all ++ [kq_tab; kq_lens; kq_tab32; kq_lens32]) then true else false.
Definition params_ok (P : prog) : bool :=
  forallb (fun gf => if list_norepet_dec peq (kparams (snd gf)) then true else false) (pfuns P).

Lemma params_ok_sound : forall P, params_ok P = true ->
  forall g f, find P g = Some f -> list_norepet (kparams f).
Proof.
  intros P H g f F. unfold params_ok in H. rewrite forallb_forall in H.
  specialize (H (g, f) (assoc_in _ _ _ _ F)). simpl in H.
  destruct (list_norepet_dec peq (kparams f)); [exact l | discriminate].
Qed.

Section TOP.
Variable P : prog.
Hypothesis NAMES : names_ok P = true.
Hypothesis PARAMS : params_ok P = true.

Let cp := tr_kit_program P.
Let ge := Clight.globalenv cp.

Lemma defs_names : prog_defs_names cp = map fst (pfuns P) ++ map hwid hw_all ++ map hwfid hwf_all ++ [kq_tab; kq_lens; kq_tab32; kq_lens32].
Proof.
  unfold prog_defs_names, cp, tr_kit_program, tr_defs, hw_defs, hwf_defs. simpl.
  rewrite !map_app, !map_map. reflexivity.
Qed.

Lemma norepet : list_norepet (map fst (pfuns P) ++ map hwid hw_all ++ map hwfid hwf_all ++ [kq_tab; kq_lens; kq_tab32; kq_lens32]).
Proof. unfold names_ok in NAMES. destruct (list_norepet_dec peq _); [exact l | discriminate]. Qed.

Lemma lookup_def : forall id fd, In (id, Gfun fd) (prog_defs cp) ->
  exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some fd.
Proof.
  intros id fd I.
  change (In (id, Gfun fd) (AST.prog_defs (program_of_program cp))) in I.
  apply (prog_defmap_norepet (program_of_program cp)) in I; [| rewrite defs_names; exact norepet].
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

Lemma hw_funs : forall o, exists b, Genv.find_symbol ge (hwid o) = Some b /\
  Genv.find_funct_ptr ge b = Some (External (hw_ef o) (tylist (hw_arity o)) tyl cc_default).
Proof.
  intros o. apply lookup_def.
  assert (Hin : In (hwid o, Gfun (External (hw_ef o) (tylist (hw_arity o)) tyl cc_default)) hw_defs).
  { unfold hw_defs. apply in_map_iff. exists o. split; [reflexivity | ]. destruct o; simpl; tauto. }
  change (prog_defs cp) with (tr_defs P ++ hw_defs ++ hwf_defs ++ [(kq_tab, Gvar kit_tab_var); (kq_lens, Gvar kit_lens_var);
                                                      (kq_tab32, Gvar kit_tab32_var); (kq_lens32, Gvar kit_lens32_var)]).
  apply in_or_app. right. apply in_or_app. left. exact Hin.
Qed.

Lemma hwf_funs : forall o, exists b, Genv.find_symbol ge (hwfid o) = Some b /\ Genv.find_funct_ptr ge b = Some (External (hwf_ef o) (tylist (hwf_arity o)) tyl cc_default).
Proof.
  intros o. apply lookup_def.
  assert (Hin : In (hwfid o, Gfun (External (hwf_ef o) (tylist (hwf_arity o)) tyl cc_default)) hwf_defs).
  { unfold hwf_defs. apply in_map_iff. exists o. split; [reflexivity | ]. destruct o; simpl; tauto. }
  change (prog_defs cp) with (tr_defs P ++ hw_defs ++ hwf_defs ++ [(kq_tab, Gvar kit_tab_var); (kq_lens, Gvar kit_lens_var);
                                                      (kq_tab32, Gvar kit_tab32_var); (kq_lens32, Gvar kit_lens32_var)]).
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin.
Qed.

(** The generated function [g] of the program, called on [vs] from any Clight memory that holds the kit's
    memory [M], ends with the result and a Clight memory that holds the memory the KQL run ends with. *)
Theorem kit_function_correct :
  (forall o vs M m, length vs = hwf_arity o -> kmrel cp M m ->
    (exists m1, external_call (hwf_ef o) ge (map enc vs) m E0 (enc (hwf_sem o vs)) m1) /\
    (forall t vres m1, external_call (hwf_ef o) ge (map enc vs) m t vres m1 -> t = E0 /\ vres = enc (hwf_sem o vs) /\ kmrel cp M m1)) ->
  (forall o vs M m, length vs = hw_arity o -> kmrel cp M m ->
    (exists vres m1, external_call (hw_ef o) ge (map enc vs) m E0 vres m1) /\
    (forall t vres m1, external_call (hw_ef o) ge (map enc vs) m t vres m1 -> t = E0 /\ kmrel cp (hw_sem o vs M) m1)) ->
  forall g vs M v M', runk P g vs M v M' ->
  exists fg b, Genv.find_symbol ge g = Some b /\
    Genv.find_funct_ptr ge b = Some (Internal (tr_fn P fg)) /\
    length (kparams fg) = length vs /\
    forall m, kmrel cp M m ->
      exists m', eval_funcall function_entry2 ge m (Internal (tr_fn P fg)) (map enc vs) E0 m' (enc v) /\
                 kmrel cp M' m'.
Proof.
  intros HWF HW g vs M v M' R.
  exact (runk_funcall P cp cp_funs (params_ok_sound P PARAMS) hw_funs hwf_funs HWF HW g vs M v M' R).
Qed.

End TOP.
