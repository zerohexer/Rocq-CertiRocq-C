(** CompCert's back end from Clight (parameters as temporaries) to Asm,
    composed from CompCert's own pass theorems.  [transf_clight_program]
    starts with SimplLocals, which turns addressable parameters into
    temporaries; our generator already emits temporaries, so we enter the
    pipeline one pass later, at C#minor generation. *)

From compcert Require Import Coqlib Errors AST Linking Smallstep Behaviors Compopts.
From compcert Require Clight Csharpminor Cminor Asm.
From compcert Require Cshmgen Cminorgen Selection RTLgen Tailcall Inlining Renumber
  Constprop CSE Deadcode Unusedglob Allocation Tunneling Linearize CleanupLabels Debugvar
  Stacking Asmgen.
From compcert Require Cshmgenproof Cminorgenproof Selectionproof RTLgenproof
  Tailcallproof Inliningproof Renumberproof Constpropproof CSEproof Deadcodeproof
  Unusedglobproof Allocproof Tunnelingproof Linearizeproof CleanupLabelsproof Debugvarproof
  Stackingproof Asmgenproof.
From compcert Require Import Compiler.

Definition transf_clight2_program (p : Clight.program) : Errors.res Asm.program :=
  OK p
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ transf_cminor_program.

Lemma total_if_fsim :
  forall (A : Type) (sem : A -> semantics) (flag : unit -> bool) (f : A -> A) (p : A),
  (forall q, forward_simulation (sem q) (sem (f q))) ->
  forward_simulation (sem p) (sem (total_if flag f p)).
Proof.
  intros. unfold total_if. destruct (flag tt). auto. apply forward_simulation_identity.
Qed.

Lemma partial_if_fsim :
  forall (A : Type) (sem : A -> semantics) (flag : unit -> bool) (f : A -> res A) (p tp : A),
  (forall q tq, f q = OK tq -> forward_simulation (sem q) (sem tq)) ->
  partial_if flag f p = OK tp ->
  forward_simulation (sem p) (sem tp).
Proof.
  intros. unfold partial_if in *. destruct (flag tt). eauto. inv H0. apply forward_simulation_identity.
Qed.

Theorem transf_cminor_fsim : forall p tp,
  transf_cminor_program p = OK tp -> forward_simulation (Cminor.semantics p) (Asm.semantics tp).
Proof.
  intros p4 tp T.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Renumber.transf_program p8) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct. apply Selectionproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct. apply RTLgenproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    apply total_if_fsim. intros q. apply Tailcallproof.transf_program_correct.
    apply Tailcallproof.transf_program_match.
  eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct. apply Inliningproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply Renumberproof.transf_program_correct. apply Renumberproof.transf_program_match.
  eapply compose_forward_simulations.
    apply total_if_fsim. intros q. apply Constpropproof.transf_program_correct.
    apply Constpropproof.transf_program_match.
  eapply compose_forward_simulations.
    apply total_if_fsim. intros q. apply Renumberproof.transf_program_correct.
    apply Renumberproof.transf_program_match.
  eapply compose_forward_simulations.
    eapply partial_if_fsim; [ | exact P12 ]. intros q tq E.
    apply CSEproof.transf_program_correct. apply CSEproof.transf_program_match; auto.
  eapply compose_forward_simulations.
    eapply partial_if_fsim; [ | exact P13 ]. intros q tq E.
    apply Deadcodeproof.transf_program_correct. apply Deadcodeproof.transf_program_match; auto.
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct. apply Unusedglobproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct. apply Allocproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct. apply Tunnelingproof.transf_program_match.
  eapply compose_forward_simulations.
    eapply Linearizeproof.transf_program_correct. apply Linearizeproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply CleanupLabelsproof.transf_program_correct. apply CleanupLabelsproof.transf_program_match.
  eapply compose_forward_simulations.
    eapply partial_if_fsim; [ | exact P19 ]. intros q tq E.
    apply Debugvarproof.transf_program_correct. apply Debugvarproof.transf_program_match; auto.
  eapply compose_forward_simulations.
    eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    apply Stackingproof.transf_program_match; eauto.
  eapply Asmgenproof.transf_program_correct. apply Asmgenproof.transf_program_match; eauto.
Qed.

Theorem transf_clight2_fsim : forall p tp,
  transf_clight2_program p = OK tp -> forward_simulation (Clight.semantics2 p) (Asm.semantics tp).
Proof.
  intros p tp T. unfold transf_clight2_program in T. simpl in T.
  destruct (Cshmgen.transl_program p) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  eapply compose_forward_simulations.
    eapply Cshmgenproof.transl_program_correct. apply Cshmgenproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply Cminorgenproof.transl_program_correct. apply Cminorgenproof.transf_program_match; eauto.
  apply transf_cminor_fsim; auto.
Qed.

(** A terminating Clight program compiles to an Asm program with the same
    terminating behaviour. *)
Theorem transf_clight2_terminates : forall p tp t r,
  transf_clight2_program p = OK tp ->
  program_behaves (Clight.semantics2 p) (Terminates t r) ->
  program_behaves (Asm.semantics tp) (Terminates t r).
Proof.
  intros p tp t r T B.
  destruct (forward_simulation_behavior_improves (transf_clight2_fsim p tp T) B)
    as (beh & B2 & [E | (t' & E & _)]).
  - subst. auto.
  - discriminate.
Qed.
