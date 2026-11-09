(** (step 96) A program's end theorem: what its entry's theorem ([KQR.callee_ok], the KQL function computes the Rocq function)
    says of the KQL run, said of the Clight program the generator makes ([kit_function_correct]).  Assumed by its statement, as by
    [kit_function_correct]'s: the machine operations behave as their laws say ([hw_ok]), and the Clight memory holds the kit's
    ([kmrel], what the loader sets). *)
From Stdlib Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Cop Clight ClightBigstep.
From KQC Require Import KQL KQLGen KQTArith KQLProof KQM KQMTop KQMSem.
From KQC Require KQR.
Import ListNotations.

(** the machine operations as [kit_function_correct] asks them *)
Definition hw_ok (P : prog) : Prop :=
  (forall (o : hwfop) (vs : list i63) (M : kmemt) (m : mem), length vs = hwf_arity o -> kmrel (tr_kit_program P) M m ->
    (exists m1, external_call (hwf_ef o) (globalenv (tr_kit_program P)) (map enc vs) m E0 (enc (hwf_sem o vs)) m1) /\
    (forall t vres m1, external_call (hwf_ef o) (globalenv (tr_kit_program P)) (map enc vs) m t vres m1 ->
       t = E0 /\ vres = enc (hwf_sem o vs) /\ kmrel (tr_kit_program P) M m1)) /\
  (forall (o : hwop) (vs : list i63) (M : kmemt) (m : mem), length vs = hw_arity o -> kmrel (tr_kit_program P) M m ->
    (exists vres m1, external_call (hw_ef o) (globalenv (tr_kit_program P)) (map enc vs) m E0 vres m1) /\
    (forall t vres m1, external_call (hw_ef o) (globalenv (tr_kit_program P)) (map enc vs) m t vres m1 ->
       t = E0 /\ kmrel (tr_kit_program P) (hw_sem o vs M) m1)).

(** the Clight function [g] of the generated program, called on [vs] from any Clight memory holding [M], gives [v] and a Clight
    memory holding [M'] *)
Definition endk (P : prog) (g : ident) (vs : list i63) (M : kmemt) (v : i63) (M' : kmemt) : Prop :=
  exists (fg : fn) (b : block),
    Genv.find_symbol (globalenv (tr_kit_program P)) g = Some b /\
    Genv.find_funct_ptr (globalenv (tr_kit_program P)) b = Some (Internal (tr_fn P fg)) /\
    length (kparams fg) = length vs /\
    forall m, kmrel (tr_kit_program P) M m ->
      exists m', eval_funcall function_entry2 (globalenv (tr_kit_program P)) m (Internal (tr_fn P fg)) (map enc vs) E0 m' (enc v) /\
                 kmrel (tr_kit_program P) M' m'.

Theorem callee_end : forall {RTs : KQR.RecTypes} (P : prog) (id : ident) (B : Z) (gs : KQR.sig) (h : KQR.ftype gs),
  KQR.callee_ok P id B gs h -> names_ok P = true -> params_ok P = true -> hw_ok P -> KQR.slot_room ->
  forall cvs vs M, length cvs = KQR.sn gs -> map KQR.kind_of vs = KQR.sk gs -> KQR.cfits gs B cvs ->
    if KQR.sw gs then exists M', endk P id (map KQLAuto.ofn cvs ++ flat_map KQR.vflat vs) M (KQR.calln gs h cvs vs M) (KQR.callmw gs h cvs vs M M')
    else endk P id (map KQLAuto.ofn cvs ++ flat_map KQR.vflat vs) M (KQR.calln gs h cvs vs M)
           (if KQR.sr gs then KQR.callm gs h cvs vs M else match KQR.sq gs with Some _ => KQR.callm gs h cvs vs M | None => M end).
Proof.
  intros RTs P id B gs h C N Pa [HWF HW] R cvs vs M L K F. specialize (C R cvs vs M L K F).
  destruct (KQR.sw gs).
  - destruct C as [M' Hr]. exists M'. exact (kit_function_correct P N Pa HWF HW _ _ _ _ _ Hr).
  - exact (kit_function_correct P N Pa HWF HW _ _ _ _ _ C).
Qed.
