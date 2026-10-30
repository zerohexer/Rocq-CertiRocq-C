(** KQR.v -- the verified compiler by reflection (Rocq-C-solution.md §1.12, §12.V): the spike.

    [sexp] is a syntax of a fragment (numbers, operations, tests, lets, reads of the memory, a recursive call on the counter's
    predecessor); [denote_fun] gives the Rocq function a syntax tree stands for, reduced to exactly the shape of the user's
    [Fixpoint], so that the per-program check [f = denote_fun ..] is the kernel's computation alone (measured at the end).
    [compile_fun] makes the KQL function, and [compile_fun_ok] -- proved once, for every syntax tree -- says the KQL computes
    the meaning. *)

From Stdlib Require Import List Uint63 ZArith Lia.
From Stdlib Require FinFun.
From compcert Require Import Coqlib Maps AST.
From KQC Require Import KQL KQLAuto KQMSem.
Require KQ.KQRun.
Import ListNotations.

Notation mem := KQ.KQRun.mem.

Inductive sexp : Type :=
| SVar (i : nat)                     (* a number: the i-th of the function's numbers and lets, the nearest first *)
| SInt (n : i63)
| SOp (o : binop) (a b : sexp)
| SIf (c : cmpop) (a b : sexp) (t e : sexp)
| SLet (e1 e2 : sexp)                (* let x := e1 in e2; x is SVar 0 in e2 *)
| SRd (h i : sexp)                   (* rd h i s, s the function's memory *)
| SRec (args : sexps)                (* the function itself on the counter's predecessor, these numbers, the memory *)
with sexps : Type :=
| SNil
| SCons (e : sexp) (r : sexps).

Scheme sexp_mut := Induction for sexp Sort Prop
with sexps_mut := Induction for sexps Sort Prop.

(** a function of [k] numbers and a memory *)
Fixpoint nfun (k : nat) : Type := match k with O => mem -> i63 | S k => i63 -> nfun k end.

(** [abs k F] is [fun x1 .. xk s => F [xk; ..; x1] s]: the parameters are bound before anything else, as in the user's text *)
Fixpoint abs (k : nat) : (list i63 -> mem -> i63) -> nfun k :=
  match k with
  | O => fun F s => F [] s
  | S k => fun F x => abs k (fun env s => F (env ++ [x]) s)
  end.

(** [app k g [v1; ..; vk] s] is [g v1 .. vk s] *)
Fixpoint app (k : nat) : nfun k -> list i63 -> mem -> i63 :=
  match k with
  | O => fun g _ s => g s
  | S k => fun g l s => match l with x :: l => app k (g x) l s | [] => app k (g 0%uint63) [] s end
  end.

Fixpoint denote_e (rec : list i63 -> i63) (env : list i63) (s : mem) (e : sexp) {struct e} : i63 :=
  match e with
  | SVar i => nth i env 0%uint63
  | SInt n => n
  | SOp o a b => binop_sem o (denote_e rec env s a) (denote_e rec env s b)
  | SIf c a b t f => if cmp_sem c (denote_e rec env s a) (denote_e rec env s b) then denote_e rec env s t else denote_e rec env s f
  | SLet e1 e2 => let x := denote_e rec env s e1 in denote_e rec (x :: env) s e2
  | SRd h i => KQ.KQRun.rd (denote_e rec env s h) (denote_e rec env s i) s
  | SRec args => rec (denote_es rec env s args)
  end
with denote_es (rec : list i63 -> i63) (env : list i63) (s : mem) (es : sexps) {struct es} : list i63 :=
  match es with
  | SNil => []
  | SCons e r => denote_e rec env s e :: denote_es rec env s r
  end.

(** a function recursive on a counter: [k] numbers, a memory; [e0] when the counter is 0, [e1] otherwise *)
Definition denote_fun (k : nat) (e0 e1 : sexp) : nat -> nfun k :=
  fix go (n : nat) : nfun k :=
    abs k (fun env s => match n with
                        | O => denote_e (fun _ => 0%uint63) env s e0
                        | S m => denote_e (fun args => app k (go m) args s) env s e1
                        end).

(* ================================================================ compile *)
Section C.
Variable g : ident.     (* the function's own name in the program *)
Variable mv : ident.    (* the variable holding the counter's predecessor *)

(** a number, worked out in A-normal form; [K] gets the atom holding it and the next free variable *)
Fixpoint cexp (e : sexp) (env : list atom) (nxt : ident) (K : atom -> ident -> exp) {struct e} : exp :=
  match e with
  | SVar i => K (nth i env (Aint 0%uint63)) nxt
  | SInt n => K (Aint n) nxt
  | SOp o a b => cexp a env nxt (fun A n1 => cexp b env n1 (fun B n2 => Eop n2 o A B (K (Avar n2) (Pos.succ n2))))
  | SIf c a b t f => cexp a env nxt (fun A n1 => cexp b env n1 (fun B n2 => Eif c A B (cexp t env n2 K) (cexp f env n2 K)))
  | SLet e1 e2 => cexp e1 env nxt (fun A n1 => cexp e2 (A :: env) n1 K)
  | SRd h i => cexp h env nxt (fun H n1 => cexp i env n1 (fun I n2 => Ekld n2 H I (K (Avar n2) (Pos.succ n2))))
  | SRec args => cexps args env nxt (fun As n => Ecall n g (Avar mv :: As) (K (Avar n) (Pos.succ n)))
  end
with cexps (es : sexps) (env : list atom) (nxt : ident) (K : list atom -> ident -> exp) {struct es} : exp :=
  match es with
  | SNil => K [] nxt
  | SCons e r => cexp e env nxt (fun A n1 => cexps r env n1 (fun As n2 => K (A :: As) n2))
  end.

(** the body in tail position: a test is a branch, the recursive call a loop *)
Fixpoint ctail (e : sexp) (env : list atom) (nxt : ident) {struct e} : exp :=
  match e with
  | SIf c a b t f => cexp a env nxt (fun A n1 => cexp b env n1 (fun B n2 => Eif c A B (ctail t env n2) (ctail f env n2)))
  | SLet e1 e2 => cexp e1 env nxt (fun A n1 => ctail e2 (A :: env) n1)
  | SRec args => cexps args env nxt (fun As _ => Eloop (Avar mv :: As))
  | _ => cexp e env nxt (fun A _ => Eret A)
  end.
End C.

Fixpoint len_s (es : sexps) : nat := match es with SNil => O | SCons _ es => S (len_s es) end.

(** well formed: a recursive call has [k] numbers, and is allowed only where [r] says (not when the counter is 0) *)
Fixpoint wf (r : bool) (k : nat) (e : sexp) {struct e} : bool :=
  match e with
  | SVar _ | SInt _ => true
  | SOp _ a b | SLet a b | SRd a b => wf r k a && wf r k b
  | SIf _ a b t f => wf r k a && wf r k b && wf r k t && wf r k f
  | SRec args => r && Nat.eqb (len_s args) k && wfs r k args
  end
with wfs (r : bool) (k : nat) (es : sexps) {struct es} : bool :=
  match es with SNil => true | SCons e es => wf r k e && wfs r k es end.

(** the function: parameters 1 (the counter) and 2 .. k+1 (the numbers); k+2 holds the counter's predecessor *)
Definition params (k : nat) : list ident := map Pos.of_succ_nat (seq 0 (S k)).
Definition env0 (k : nat) : list atom := map (fun i => Avar (Pos.of_succ_nat i)) (rev (seq 1 k)).
Definition compile_fun (g : ident) (k : nat) (e0 e1 : sexp) : fn :=
  let mv := Pos.of_succ_nat (S k) in
  mkfn (params k)
       (Eif Ceq (Avar 1%positive) (Aint 0%uint63)
            (ctail g mv e0 (env0 k) (Pos.succ mv))
            (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63) (ctail g mv e1 (env0 k) (Pos.succ mv)))).

(* ================================================================ the theorem, proved once for every syntax tree *)

(** a KQL atom whose variable, if any, is below [n] *)
Definition atom_lt (a : atom) (n : ident) : Prop := match a with Avar x => Pos.lt x n | _ => True end.
(** [rho'] has what [rho] has below [n] *)
Definition agree (rho rho' : env) (n : ident) : Prop := forall x, Pos.lt x n -> rho' ! x = rho ! x.
(** the atoms of [envA] hold the numbers of [denv] (both read with 0 past their end) *)
Definition env_ok (rho : env) (envA : list atom) (denv : list i63) : Prop :=
  forall i, aval rho (nth i envA (Aint 0%uint63)) = Some (nth i denv 0%uint63).
Definition lt_all (envA : list atom) (n : ident) : Prop := forall i, atom_lt (nth i envA (Aint 0%uint63)) n.

Lemma aval_agree : forall rho rho' n a, agree rho rho' n -> atom_lt a n -> aval rho' a = aval rho a.
Proof. intros rho rho' n [x|i|i] A L; simpl in *; auto. Qed.

Lemma atom_lt_mono : forall a n n', atom_lt a n -> Pos.le n n' -> atom_lt a n'.
Proof. intros [x|i|i] n n' L Le; simpl in *; auto. lia. Qed.

Lemma lt_all_mono : forall envA n n', lt_all envA n -> Pos.le n n' -> lt_all envA n'.
Proof. intros envA n n' L Le i. eapply atom_lt_mono; eauto. Qed.

Lemma agree_refl : forall rho n, agree rho rho n.
Proof. intros rho n x _. reflexivity. Qed.

Lemma agree_trans : forall rho rho1 rho2 n n', agree rho rho1 n -> agree rho1 rho2 n' -> Pos.le n n' -> agree rho rho2 n.
Proof. intros rho rho1 rho2 n n' A1 A2 Le x Lx. rewrite A2 by lia. apply A1; auto. Qed.

Lemma agree_set : forall rho x v n, Pos.le n x -> agree rho (PTree.set x v rho) n.
Proof. intros rho x v n Le y Ly. rewrite PTree.gso; auto. intro E; subst; lia. Qed.

Lemma agree_set1 : forall rho rho1 x v nxt, agree rho rho1 nxt -> Pos.le nxt x -> agree rho (PTree.set x v rho1) nxt.
Proof. intros rho rho1 x v nxt A L y Ly. rewrite PTree.gso by (intro; subst; lia). apply A; auto. Qed.

Lemma agree_set2 : forall rho rho1 rho2 x v nxt n1, agree rho rho1 nxt -> agree rho1 rho2 n1 -> Pos.le nxt n1 -> Pos.le n1 x ->
  agree rho (PTree.set x v rho2) nxt.
Proof. intros rho rho1 rho2 x v nxt n1 A1 A2 L1 L2 y Ly. rewrite PTree.gso by (intro; subst; lia). rewrite A2 by lia. apply A1; auto. Qed.

Lemma agree_3 : forall rho rho1 rho2 rho3 nxt n1 n2, agree rho rho1 nxt -> agree rho1 rho2 n1 -> agree rho2 rho3 n2 ->
  Pos.le nxt n1 -> Pos.le n1 n2 -> agree rho rho3 nxt.
Proof. intros rho rho1 rho2 rho3 nxt n1 n2 A1 A2 A3 L1 L2 y Ly. rewrite A3 by lia. rewrite A2 by lia. apply A1; auto. Qed.

Lemma env_ok_agree : forall rho rho' envA denv n, env_ok rho envA denv -> lt_all envA n -> agree rho rho' n -> env_ok rho' envA denv.
Proof. intros rho rho' envA denv n E L A i. rewrite (aval_agree rho rho' n); auto. Qed.

Lemma env_ok_cons : forall rho envA denv a v, env_ok rho envA denv -> aval rho a = Some v -> env_ok rho (a :: envA) (v :: denv).
Proof. intros rho envA denv a v E A [|i]; simpl; auto. Qed.

Lemma lt_all_cons : forall envA a n, lt_all envA n -> atom_lt a n -> lt_all (a :: envA) n.
Proof. intros envA a n L A [|i]; simpl; auto. Qed.

Combined Scheme sexp_comb from sexp_mut, sexps_mut.

Section Sim.
Variables (P : prog) (f : fn) (g mv : ident) (M : kmemt) (r : bool) (k : nat) (rec : list i63 -> i63) (vm : i63).
(** the recursive call, where it is allowed, computes [rec] *)
Hypothesis Hrec : r = true -> forall vs, length vs = k -> runk P g (vm :: vs) M (rec vs) M.

Lemma len_denote_es : forall es denv, length (denote_es rec denv M es) = len_s es.
Proof. induction es; intros denv; simpl; auto. Qed.

Definition inv (rho : env) (envA : list atom) (denv : list i63) (nxt : ident) : Prop :=
  env_ok rho envA denv /\ lt_all envA nxt /\ Pos.lt mv nxt /\ (r = true -> rho ! mv = Some vm).

Lemma inv_step : forall rho rho' envA denv nxt n', inv rho envA denv nxt -> agree rho rho' nxt -> Pos.le nxt n' ->
  inv rho' envA denv n'.
Proof.
  intros rho rho' envA denv nxt n' (E & L & Mv & R) A Le. split; [|split; [|split]].
  - eapply env_ok_agree; eauto.
  - eapply lt_all_mono; eauto.
  - lia.
  - intro Rt. rewrite A by auto. auto.
Qed.

Lemma cexp_all :
  (forall e envA denv nxt K rho v M', wf r k e = true -> inv rho envA denv nxt ->
     (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' -> aval rho' a = Some (denote_e rec denv M e) ->
        evalk P f rho' M (K a n') v M') ->
     evalk P f rho M (cexp g mv e envA nxt K) v M')
  /\
  (forall es envA denv nxt K rho v M', wfs r k es = true -> inv rho envA denv nxt ->
     (forall rho' n' As, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') As ->
        avals rho' As = Some (denote_es rec denv M es) -> evalk P f rho' M (K As n') v M') ->
     evalk P f rho M (cexps g mv es envA nxt K) v M').
Proof.
  apply sexp_comb.
  - (* SVar *) intros i envA denv nxt K rho v M' W Iv HK. simpl.
    destruct Iv as (E & L & _ & _). apply HK; [apply agree_refl | lia | apply L | apply E].
  - (* SInt *) intros n envA denv nxt K rho v M' W Iv HK. simpl. apply HK; [apply agree_refl | lia | exact Logic.I | reflexivity].
  - (* SOp *) intros o a IHa b IHb envA denv nxt K rho v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [Wa Wb].
    apply IHa with (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHb with (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_op.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SIf *) intros c a IHa b IHb t IHt e IHe envA denv nxt K rho v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    apply IHa with (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHb with (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + assert (I2 : inv rho2 envA denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      destruct (cmp_sem c (denote_e rec denv M a) (denote_e rec denv M b)) eqn:C.
      * apply IHt with (denv := denv); auto. intros rho3 n3 a3 A3 Le3 L3 V3.
        apply HK; [| lia | exact L3 | exact V3].
        eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia.
      * apply IHe with (denv := denv); auto. intros rho3 n3 a3 A3 Le3 L3 V3.
        apply HK; [| lia | exact L3 | exact V3].
        eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia.
  - (* SLet *) intros e1 IH1 e2 IH2 envA denv nxt K rho v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W1 W2].
    apply IH1 with (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH2 with (denv := denote_e rec denv M e1 :: denv); auto.
    + destruct (inv_step rho rho1 envA denv nxt n1 Iv A1 Le1) as (E & L & Mv & R).
      split; [|split; [|split]]; auto using env_ok_cons, lt_all_cons.
    + intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | exact V2].
  - (* SRd *) intros h IHh i IHi envA denv nxt K rho v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [Wh Wi].
    apply IHh with (denv := denv); auto. intros rho1 n1 H A1 Le1 LH VH.
    apply IHi with (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 J A2 Le2 LJ VJ.
    eapply K_ld.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SRec *) intros args IHs envA denv nxt K rho v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [Wr Wk].
    apply IHs with (denv := denv); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    destruct (Hrec Wr (denote_es rec denv M args)) as (fg & rho' & F & B & EV).
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    destruct (inv_step rho rho1 envA denv nxt n1 Iv A1 Le1) as (_ & _ & Mv1 & R1).
    eapply K_call; eauto.
    + simpl. rewrite (R1 Wr), VAs. reflexivity.
    + apply HK.
      * eapply (agree_set1 rho rho1); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SNil *) intros envA denv nxt K rho v M' W Iv HK. simpl. apply HK; [apply agree_refl | lia | constructor | reflexivity].
  - (* SCons *) intros e IHe es IHes envA denv nxt K rho v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [We Wes].
    apply IHe with (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHes with (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 As A2 Le2 LAs VAs. apply HK.
    + eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
    + lia.
    + constructor; auto. eapply atom_lt_mono; eauto.
    + simpl. rewrite (aval_agree rho1 rho2 n1), VA, VAs; auto.
Qed.

Definition cexp_ok := proj1 cexp_all.
Definition cexps_ok := proj2 cexp_all.

(** in tail position: the function's body ends with the value of [e] and the memory it started with *)
Hypothesis Hf : find P g = Some f.

Lemma ctail_ok : forall e envA denv nxt rho, wf r k e = true -> inv rho envA denv nxt ->
  evalk P f rho M (ctail g mv e envA nxt) (denote_e rec denv M e) M.
Proof.
  induction e; intros envA denv nxt rho W Iv; cbn [ctail] in *; cbn [wf] in W.
  - apply cexp_ok with (denv := denv); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (denv := denv); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (denv := denv); auto. intros. apply K_ret. auto.
  - (* SIf *) apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    apply cexp_ok with (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + assert (I2 : inv rho2 envA denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      cbn [denote_e]. destruct (cmp_sem c (denote_e rec denv M e1) (denote_e rec denv M e2)); auto.
  - (* SLet *) apply andb_true_iff in W as [W1 W2].
    apply cexp_ok with (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_e]. apply IHe2; auto.
    destruct (inv_step rho rho1 envA denv nxt n1 Iv A1 Le1) as (E & L & Mv & R).
    split; [|split; [|split]]; auto using env_ok_cons, lt_all_cons.
  - apply cexp_ok with (denv := denv); auto. intros. apply K_ret. auto.
  - (* SRec *) apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [Wr Wk].
    apply cexps_ok with (denv := denv); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    destruct (Hrec Wr (denote_es rec denv M args)) as (fg & rho' & F & B & EV).
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    rewrite Hf in F. injection F as <-.
    destruct (inv_step rho rho1 envA denv nxt n1 Iv A1 Le1) as (_ & _ & Mv1 & R1).
    cbn [denote_e]. eapply K_loop; eauto. simpl. rewrite (R1 Wr), VAs. reflexivity.
Qed.
End Sim.

(* ---------------------------------------------------------------- the function *)
Local Open Scope nat_scope.

Lemma app_abs : forall k F vs s, length vs = k -> app k (abs k F) vs s = F (rev vs) s.
Proof.
  induction k as [|k IH]; intros F vs s L; destruct vs as [|v vs]; simpl in *; try discriminate; auto.
  all: injection L as L; rewrite IH by auto; reflexivity.
Qed.

Lemma bind_some : forall xs vs rho, length xs = length vs -> exists rho', bind xs vs rho = Some rho'.
Proof. induction xs as [|x xs IH]; intros [|v vs] rho L; simpl in *; try discriminate; eauto. Qed.

Lemma bind_notin : forall xs vs rho rho' y, bind xs vs rho = Some rho' -> ~ In y xs -> rho' ! y = rho ! y.
Proof.
  induction xs as [|x xs IH]; intros [|v vs] rho rho' y B N; simpl in *; try discriminate.
  - injection B as <-. reflexivity.
  - rewrite (IH vs _ _ y B) by tauto. rewrite PTree.gso; auto.
Qed.

Lemma bind_nth : forall xs vs rho rho' j, NoDup xs -> bind xs vs rho = Some rho' -> j < length xs ->
  rho' ! (nth j xs 1%positive) = Some (nth j vs 0%uint63).
Proof.
  induction xs as [|x xs IH]; intros [|v vs] rho rho' j ND B L; simpl in *; try discriminate; try lia.
  inversion ND; subst. destruct j as [|j].
  - rewrite (bind_notin xs vs _ _ x B) by auto. apply PTree.gss.
  - apply (IH vs (PTree.set x v rho) rho' j); auto. lia.
Qed.

Lemma params_nth : forall k j, j <= k -> nth j (params k) 1%positive = Pos.of_succ_nat j.
Proof.
  intros k j L. unfold params. rewrite nth_indep with (d' := Pos.of_succ_nat 0) by (rewrite map_length, seq_length; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma params_nodup : forall k, NoDup (params k).
Proof.
  intro k. unfold params. apply FinFun.Injective_map_NoDup; [| apply seq_NoDup].
  intros a b E. apply SuccNat2Pos.inj; auto.
Qed.

Lemma params_length : forall k, length (params k) = S k.
Proof. intro k. unfold params. rewrite map_length, seq_length. reflexivity. Qed.

Lemma env0_nth : forall k i, i < k -> nth i (env0 k) (Aint 0%uint63) = Avar (Pos.of_succ_nat (k - i)).
Proof.
  intros k i L. unfold env0.
  rewrite nth_indep with (d' := Avar (Pos.of_succ_nat 0)) by (rewrite map_length, rev_length, seq_length; lia).
  rewrite map_nth with (d := 0). rewrite rev_nth by (rewrite seq_length; lia). rewrite seq_length, seq_nth by lia.
  f_equal. f_equal. lia.
Qed.

Lemma env0_out : forall k i, k <= i -> nth i (env0 k) (Aint 0%uint63) = Aint 0%uint63.
Proof. intros k i L. apply nth_overflow. unfold env0. rewrite map_length, rev_length, seq_length. lia. Qed.

Lemma env0_lt : forall k, lt_all (env0 k) (Pos.of_succ_nat (S k)).
Proof.
  intros k i. destruct (Nat.lt_ge_cases i k) as [L|L].
  - rewrite env0_nth by auto. simpl. apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
  - rewrite env0_out by auto. simpl. auto.
Qed.

(** the parameters bound: the counter in 1, the numbers in 2 .. k+1, read by [env0] in the order of [denote_fun] *)
Lemma bind_params : forall k n vs, length vs = k ->
  exists rho0, bind (params k) (ofn n :: vs) (PTree.empty _) = Some rho0 /\
    rho0 ! 1%positive = Some (ofn n) /\ env_ok rho0 (env0 k) (rev vs).
Proof.
  intros k n vs L. destruct (bind_some (params k) (ofn n :: vs) (PTree.empty _)) as [rho0 B].
  { rewrite params_length. simpl. lia. }
  exists rho0. split; auto. split.
  - pose proof (bind_nth _ _ _ _ 0 (params_nodup k) B) as N. rewrite params_nth in N by lia. apply N. rewrite params_length. lia.
  - intro i. destruct (Nat.lt_ge_cases i k) as [Li|Li].
    + rewrite env0_nth by auto. simpl.
      pose proof (bind_nth _ _ _ _ (k - i) (params_nodup k) B) as N. rewrite params_nth in N by lia.
      rewrite N by (rewrite params_length; lia).
      replace (k - i) with (S (length vs - S i)) by lia. simpl. rewrite rev_nth by lia. reflexivity.
    + rewrite env0_out by auto. simpl. rewrite nth_overflow; auto. rewrite rev_length. lia.
Qed.

Theorem compile_fun_ok : forall P g k e0 e1,
  find P g = Some (compile_fun g k e0 e1) -> wf false k e0 = true -> wf true k e1 = true ->
  forall n vs M, length vs = k -> (Z.of_nat n < wB)%Z ->
  runk P g (ofn n :: vs) M (app k (denote_fun k e0 e1 n) vs M) M.
Proof.
  intros P g k e0 e1 Hf W0 W1.
  set (mv := Pos.of_succ_nat (S k)).
  assert (Lmv : lt_all (env0 k) mv) by apply env0_lt.
  induction n as [|m IH]; intros vs M L B.
  - destruct (bind_params k 0 vs L) as (rho0 & Bd & R1 & E).
    exists (compile_fun g k e0 e1), rho0. split; [exact Hf|]. split; [exact Bd|].
    change (app k (denote_fun k e0 e1 0) vs M) with (app k (abs k (fun env s => denote_e (fun _ => 0%uint63) env s e0)) vs M).
    rewrite app_abs by auto. simpl kbody.
    eapply K_if; [simpl; eauto | reflexivity | ]. rewrite ofn_0. simpl.
    apply (ctail_ok P _ g mv M false k (fun _ => 0%uint63) 0%uint63); auto; try discriminate.
    split; [|split; [|split]]; auto; try discriminate.
    + eapply lt_all_mono; eauto. lia.
    + lia.
  - destruct (bind_params k (S m) vs L) as (rho0 & Bd & R1 & E).
    exists (compile_fun g k e0 e1), rho0. split; [exact Hf|]. split; [exact Bd|].
    change (app k (denote_fun k e0 e1 (S m)) vs M)
      with (app k (abs k (fun env s => denote_e (fun args => app k (denote_fun k e0 e1 m) args s) env s e1)) vs M).
    rewrite app_abs by auto. simpl kbody.
    eapply K_if; [simpl; eauto | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
    eapply K_op; [simpl; eauto | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
    apply (ctail_ok P _ g mv M true k (fun args => app k (denote_fun k e0 e1 m) args M) (ofn m)); auto.
    + intros _ vs' L'. apply IH; auto. lia.
    + split; [|split; [|split]].
      * eapply env_ok_agree; eauto. apply agree_set. apply Pos.le_refl.
      * eapply lt_all_mono; eauto. lia.
      * lia.
      * intros _. apply PTree.gss.
Qed.


(* ================================================================ the measurement: the per-program check *)
Local Open Scope uint63_scope.

(* a counted loop, as a user writes it *)
Fixpoint sum (n : nat) (i acc : i63) (s : mem) : i63 :=
  match n with
  | O => acc
  | S m => sum m (PrimInt63.add i 1) (PrimInt63.add acc (KQ.KQRun.rd 0 i s)) s
  end.

(* its syntax: the numbers nearest first -- acc is SVar 0, i is SVar 1 *)
Definition sum_s0 := SVar 0.
Definition sum_s1 := SRec (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SOp Badd (SVar 0) (SRd (SInt 0) (SVar 1))) SNil)).

(* the per-program check: the kernel compares the user's function with the meaning of its syntax *)
Time Lemma sum_is : sum = denote_fun 2 sum_s0 sum_s1.
Proof. Time exact eq_refl. Time Qed.

(* end to end, the way a user's program gets its theorem: the KQL function is [compile_fun] of the syntax; its statement follows
   from [compile_fun_ok] and the kernel's computation alone -- no tactic searches anything *)
Definition sum_fn := compile_fun 1000%positive 2 sum_s0 sum_s1.
Definition sum_P := mkprog [(1000%positive, sum_fn)] [].
Time Lemma sum_ok : forall n i acc M, (Z.of_nat n < wB)%Z -> runk sum_P 1000%positive [ofn n; i; acc] M (sum n i acc M) M.
Proof.
  intros n i acc M B.
  change (sum n i acc M) with (app 2 (denote_fun 2 sum_s0 sum_s1 n) [i; acc] M).
  exact (compile_fun_ok sum_P 1000%positive 2 sum_s0 sum_s1 eq_refl eq_refl eq_refl n [i; acc] M eq_refl B).
Time Qed.

(* a wrong syntax (1 replaced by 2) is refused *)
Time Fail Definition sum_wrong : sum = denote_fun 2 sum_s0 (SRec (SCons (SOp Badd (SVar 1) (SInt 2)) (SCons (SOp Badd (SVar 0) (SRd (SInt 0) (SVar 1))) SNil))) := eq_refl.

Fixpoint long (n : nat) (a : i63) (s : mem) : i63 :=
  match n with
  | O => a
  | S m =>
    let x1 := PrimInt63.mul a (KQ.KQRun.rd 0 1 s) in
    let x2 := PrimInt63.lxor x1 (KQ.KQRun.rd 0 2 s) in
    let x3 := PrimInt63.add x2 (KQ.KQRun.rd 0 3 s) in
    let x4 := PrimInt63.mul x3 (KQ.KQRun.rd 0 4 s) in
    let x5 := PrimInt63.lxor x4 (KQ.KQRun.rd 0 5 s) in
    let x6 := PrimInt63.add x5 (KQ.KQRun.rd 0 6 s) in
    let x7 := PrimInt63.mul x6 (KQ.KQRun.rd 0 7 s) in
    let x8 := PrimInt63.lxor x7 (KQ.KQRun.rd 0 8 s) in
    let x9 := PrimInt63.add x8 (KQ.KQRun.rd 0 9 s) in
    let x10 := PrimInt63.mul x9 (KQ.KQRun.rd 0 10 s) in
    let x11 := PrimInt63.lxor x10 (KQ.KQRun.rd 0 11 s) in
    let x12 := PrimInt63.add x11 (KQ.KQRun.rd 0 12 s) in
    let x13 := PrimInt63.mul x12 (KQ.KQRun.rd 0 13 s) in
    let x14 := PrimInt63.lxor x13 (KQ.KQRun.rd 0 14 s) in
    let x15 := PrimInt63.add x14 (KQ.KQRun.rd 0 15 s) in
    let x16 := PrimInt63.mul x15 (KQ.KQRun.rd 0 16 s) in
    let x17 := PrimInt63.lxor x16 (KQ.KQRun.rd 0 17 s) in
    let x18 := PrimInt63.add x17 (KQ.KQRun.rd 0 18 s) in
    let x19 := PrimInt63.mul x18 (KQ.KQRun.rd 0 19 s) in
    let x20 := PrimInt63.lxor x19 (KQ.KQRun.rd 0 20 s) in
    let x21 := PrimInt63.add x20 (KQ.KQRun.rd 0 21 s) in
    let x22 := PrimInt63.mul x21 (KQ.KQRun.rd 0 22 s) in
    let x23 := PrimInt63.lxor x22 (KQ.KQRun.rd 0 23 s) in
    let x24 := PrimInt63.add x23 (KQ.KQRun.rd 0 24 s) in
    let x25 := PrimInt63.mul x24 (KQ.KQRun.rd 0 25 s) in
    let x26 := PrimInt63.lxor x25 (KQ.KQRun.rd 0 26 s) in
    let x27 := PrimInt63.add x26 (KQ.KQRun.rd 0 27 s) in
    let x28 := PrimInt63.mul x27 (KQ.KQRun.rd 0 28 s) in
    let x29 := PrimInt63.lxor x28 (KQ.KQRun.rd 0 29 s) in
    let x30 := PrimInt63.add x29 (KQ.KQRun.rd 0 30 s) in
    let x31 := PrimInt63.mul x30 (KQ.KQRun.rd 0 31 s) in
    let x32 := PrimInt63.lxor x31 (KQ.KQRun.rd 0 32 s) in
    let x33 := PrimInt63.add x32 (KQ.KQRun.rd 0 33 s) in
    let x34 := PrimInt63.mul x33 (KQ.KQRun.rd 0 34 s) in
    let x35 := PrimInt63.lxor x34 (KQ.KQRun.rd 0 35 s) in
    let x36 := PrimInt63.add x35 (KQ.KQRun.rd 0 36 s) in
    let x37 := PrimInt63.mul x36 (KQ.KQRun.rd 0 37 s) in
    let x38 := PrimInt63.lxor x37 (KQ.KQRun.rd 0 38 s) in
    let x39 := PrimInt63.add x38 (KQ.KQRun.rd 0 39 s) in
    let x40 := PrimInt63.mul x39 (KQ.KQRun.rd 0 40 s) in
    let x41 := PrimInt63.lxor x40 (KQ.KQRun.rd 0 41 s) in
    let x42 := PrimInt63.add x41 (KQ.KQRun.rd 0 42 s) in
    let x43 := PrimInt63.mul x42 (KQ.KQRun.rd 0 43 s) in
    let x44 := PrimInt63.lxor x43 (KQ.KQRun.rd 0 44 s) in
    let x45 := PrimInt63.add x44 (KQ.KQRun.rd 0 45 s) in
    let x46 := PrimInt63.mul x45 (KQ.KQRun.rd 0 46 s) in
    let x47 := PrimInt63.lxor x46 (KQ.KQRun.rd 0 47 s) in
    let x48 := PrimInt63.add x47 (KQ.KQRun.rd 0 48 s) in
    let x49 := PrimInt63.mul x48 (KQ.KQRun.rd 0 49 s) in
    let x50 := PrimInt63.lxor x49 (KQ.KQRun.rd 0 50 s) in
    let x51 := PrimInt63.add x50 (KQ.KQRun.rd 0 51 s) in
    let x52 := PrimInt63.mul x51 (KQ.KQRun.rd 0 52 s) in
    let x53 := PrimInt63.lxor x52 (KQ.KQRun.rd 0 53 s) in
    let x54 := PrimInt63.add x53 (KQ.KQRun.rd 0 54 s) in
    let x55 := PrimInt63.mul x54 (KQ.KQRun.rd 0 55 s) in
    let x56 := PrimInt63.lxor x55 (KQ.KQRun.rd 0 56 s) in
    let x57 := PrimInt63.add x56 (KQ.KQRun.rd 0 57 s) in
    let x58 := PrimInt63.mul x57 (KQ.KQRun.rd 0 58 s) in
    let x59 := PrimInt63.lxor x58 (KQ.KQRun.rd 0 59 s) in
    let x60 := PrimInt63.add x59 (KQ.KQRun.rd 0 60 s) in
    let x61 := PrimInt63.mul x60 (KQ.KQRun.rd 0 61 s) in
    let x62 := PrimInt63.lxor x61 (KQ.KQRun.rd 0 62 s) in
    let x63 := PrimInt63.add x62 (KQ.KQRun.rd 0 63 s) in
    let x64 := PrimInt63.mul x63 (KQ.KQRun.rd 0 64 s) in
    let x65 := PrimInt63.lxor x64 (KQ.KQRun.rd 0 65 s) in
    let x66 := PrimInt63.add x65 (KQ.KQRun.rd 0 66 s) in
    let x67 := PrimInt63.mul x66 (KQ.KQRun.rd 0 67 s) in
    let x68 := PrimInt63.lxor x67 (KQ.KQRun.rd 0 68 s) in
    let x69 := PrimInt63.add x68 (KQ.KQRun.rd 0 69 s) in
    let x70 := PrimInt63.mul x69 (KQ.KQRun.rd 0 70 s) in
    let x71 := PrimInt63.lxor x70 (KQ.KQRun.rd 0 71 s) in
    let x72 := PrimInt63.add x71 (KQ.KQRun.rd 0 72 s) in
    let x73 := PrimInt63.mul x72 (KQ.KQRun.rd 0 73 s) in
    let x74 := PrimInt63.lxor x73 (KQ.KQRun.rd 0 74 s) in
    let x75 := PrimInt63.add x74 (KQ.KQRun.rd 0 75 s) in
    let x76 := PrimInt63.mul x75 (KQ.KQRun.rd 0 76 s) in
    let x77 := PrimInt63.lxor x76 (KQ.KQRun.rd 0 77 s) in
    let x78 := PrimInt63.add x77 (KQ.KQRun.rd 0 78 s) in
    let x79 := PrimInt63.mul x78 (KQ.KQRun.rd 0 79 s) in
    let x80 := PrimInt63.lxor x79 (KQ.KQRun.rd 0 80 s) in
    let x81 := PrimInt63.add x80 (KQ.KQRun.rd 0 81 s) in
    let x82 := PrimInt63.mul x81 (KQ.KQRun.rd 0 82 s) in
    let x83 := PrimInt63.lxor x82 (KQ.KQRun.rd 0 83 s) in
    let x84 := PrimInt63.add x83 (KQ.KQRun.rd 0 84 s) in
    let x85 := PrimInt63.mul x84 (KQ.KQRun.rd 0 85 s) in
    let x86 := PrimInt63.lxor x85 (KQ.KQRun.rd 0 86 s) in
    let x87 := PrimInt63.add x86 (KQ.KQRun.rd 0 87 s) in
    let x88 := PrimInt63.mul x87 (KQ.KQRun.rd 0 88 s) in
    let x89 := PrimInt63.lxor x88 (KQ.KQRun.rd 0 89 s) in
    let x90 := PrimInt63.add x89 (KQ.KQRun.rd 0 90 s) in
    let x91 := PrimInt63.mul x90 (KQ.KQRun.rd 0 91 s) in
    let x92 := PrimInt63.lxor x91 (KQ.KQRun.rd 0 92 s) in
    let x93 := PrimInt63.add x92 (KQ.KQRun.rd 0 93 s) in
    let x94 := PrimInt63.mul x93 (KQ.KQRun.rd 0 94 s) in
    let x95 := PrimInt63.lxor x94 (KQ.KQRun.rd 0 95 s) in
    let x96 := PrimInt63.add x95 (KQ.KQRun.rd 0 96 s) in
    let x97 := PrimInt63.mul x96 (KQ.KQRun.rd 0 97 s) in
    let x98 := PrimInt63.lxor x97 (KQ.KQRun.rd 0 98 s) in
    let x99 := PrimInt63.add x98 (KQ.KQRun.rd 0 99 s) in
    let x100 := PrimInt63.mul x99 (KQ.KQRun.rd 0 100 s) in
    let x101 := PrimInt63.lxor x100 (KQ.KQRun.rd 0 101 s) in
    let x102 := PrimInt63.add x101 (KQ.KQRun.rd 0 102 s) in
    let x103 := PrimInt63.mul x102 (KQ.KQRun.rd 0 103 s) in
    let x104 := PrimInt63.lxor x103 (KQ.KQRun.rd 0 104 s) in
    let x105 := PrimInt63.add x104 (KQ.KQRun.rd 0 105 s) in
    let x106 := PrimInt63.mul x105 (KQ.KQRun.rd 0 106 s) in
    let x107 := PrimInt63.lxor x106 (KQ.KQRun.rd 0 107 s) in
    let x108 := PrimInt63.add x107 (KQ.KQRun.rd 0 108 s) in
    let x109 := PrimInt63.mul x108 (KQ.KQRun.rd 0 109 s) in
    let x110 := PrimInt63.lxor x109 (KQ.KQRun.rd 0 110 s) in
    let x111 := PrimInt63.add x110 (KQ.KQRun.rd 0 111 s) in
    let x112 := PrimInt63.mul x111 (KQ.KQRun.rd 0 112 s) in
    let x113 := PrimInt63.lxor x112 (KQ.KQRun.rd 0 113 s) in
    let x114 := PrimInt63.add x113 (KQ.KQRun.rd 0 114 s) in
    let x115 := PrimInt63.mul x114 (KQ.KQRun.rd 0 115 s) in
    let x116 := PrimInt63.lxor x115 (KQ.KQRun.rd 0 116 s) in
    let x117 := PrimInt63.add x116 (KQ.KQRun.rd 0 117 s) in
    let x118 := PrimInt63.mul x117 (KQ.KQRun.rd 0 118 s) in
    let x119 := PrimInt63.lxor x118 (KQ.KQRun.rd 0 119 s) in
    let x120 := PrimInt63.add x119 (KQ.KQRun.rd 0 120 s) in
    let x121 := PrimInt63.mul x120 (KQ.KQRun.rd 0 121 s) in
    let x122 := PrimInt63.lxor x121 (KQ.KQRun.rd 0 122 s) in
    let x123 := PrimInt63.add x122 (KQ.KQRun.rd 0 123 s) in
    let x124 := PrimInt63.mul x123 (KQ.KQRun.rd 0 124 s) in
    let x125 := PrimInt63.lxor x124 (KQ.KQRun.rd 0 125 s) in
    let x126 := PrimInt63.add x125 (KQ.KQRun.rd 0 126 s) in
    let x127 := PrimInt63.mul x126 (KQ.KQRun.rd 0 127 s) in
    let x128 := PrimInt63.lxor x127 (KQ.KQRun.rd 0 128 s) in
    let x129 := PrimInt63.add x128 (KQ.KQRun.rd 0 129 s) in
    let x130 := PrimInt63.mul x129 (KQ.KQRun.rd 0 130 s) in
    let x131 := PrimInt63.lxor x130 (KQ.KQRun.rd 0 131 s) in
    let x132 := PrimInt63.add x131 (KQ.KQRun.rd 0 132 s) in
    let x133 := PrimInt63.mul x132 (KQ.KQRun.rd 0 133 s) in
    let x134 := PrimInt63.lxor x133 (KQ.KQRun.rd 0 134 s) in
    let x135 := PrimInt63.add x134 (KQ.KQRun.rd 0 135 s) in
    let x136 := PrimInt63.mul x135 (KQ.KQRun.rd 0 136 s) in
    let x137 := PrimInt63.lxor x136 (KQ.KQRun.rd 0 137 s) in
    let x138 := PrimInt63.add x137 (KQ.KQRun.rd 0 138 s) in
    let x139 := PrimInt63.mul x138 (KQ.KQRun.rd 0 139 s) in
    let x140 := PrimInt63.lxor x139 (KQ.KQRun.rd 0 140 s) in
    let x141 := PrimInt63.add x140 (KQ.KQRun.rd 0 141 s) in
    let x142 := PrimInt63.mul x141 (KQ.KQRun.rd 0 142 s) in
    let x143 := PrimInt63.lxor x142 (KQ.KQRun.rd 0 143 s) in
    let x144 := PrimInt63.add x143 (KQ.KQRun.rd 0 144 s) in
    let x145 := PrimInt63.mul x144 (KQ.KQRun.rd 0 145 s) in
    let x146 := PrimInt63.lxor x145 (KQ.KQRun.rd 0 146 s) in
    let x147 := PrimInt63.add x146 (KQ.KQRun.rd 0 147 s) in
    let x148 := PrimInt63.mul x147 (KQ.KQRun.rd 0 148 s) in
    let x149 := PrimInt63.lxor x148 (KQ.KQRun.rd 0 149 s) in
    let x150 := PrimInt63.add x149 (KQ.KQRun.rd 0 150 s) in
    let x151 := PrimInt63.mul x150 (KQ.KQRun.rd 0 151 s) in
    let x152 := PrimInt63.lxor x151 (KQ.KQRun.rd 0 152 s) in
    let x153 := PrimInt63.add x152 (KQ.KQRun.rd 0 153 s) in
    let x154 := PrimInt63.mul x153 (KQ.KQRun.rd 0 154 s) in
    let x155 := PrimInt63.lxor x154 (KQ.KQRun.rd 0 155 s) in
    let x156 := PrimInt63.add x155 (KQ.KQRun.rd 0 156 s) in
    let x157 := PrimInt63.mul x156 (KQ.KQRun.rd 0 157 s) in
    let x158 := PrimInt63.lxor x157 (KQ.KQRun.rd 0 158 s) in
    let x159 := PrimInt63.add x158 (KQ.KQRun.rd 0 159 s) in
    let x160 := PrimInt63.mul x159 (KQ.KQRun.rd 0 160 s) in
    let x161 := PrimInt63.lxor x160 (KQ.KQRun.rd 0 161 s) in
    let x162 := PrimInt63.add x161 (KQ.KQRun.rd 0 162 s) in
    let x163 := PrimInt63.mul x162 (KQ.KQRun.rd 0 163 s) in
    let x164 := PrimInt63.lxor x163 (KQ.KQRun.rd 0 164 s) in
    let x165 := PrimInt63.add x164 (KQ.KQRun.rd 0 165 s) in
    let x166 := PrimInt63.mul x165 (KQ.KQRun.rd 0 166 s) in
    let x167 := PrimInt63.lxor x166 (KQ.KQRun.rd 0 167 s) in
    let x168 := PrimInt63.add x167 (KQ.KQRun.rd 0 168 s) in
    let x169 := PrimInt63.mul x168 (KQ.KQRun.rd 0 169 s) in
    let x170 := PrimInt63.lxor x169 (KQ.KQRun.rd 0 170 s) in
    let x171 := PrimInt63.add x170 (KQ.KQRun.rd 0 171 s) in
    let x172 := PrimInt63.mul x171 (KQ.KQRun.rd 0 172 s) in
    let x173 := PrimInt63.lxor x172 (KQ.KQRun.rd 0 173 s) in
    let x174 := PrimInt63.add x173 (KQ.KQRun.rd 0 174 s) in
    let x175 := PrimInt63.mul x174 (KQ.KQRun.rd 0 175 s) in
    let x176 := PrimInt63.lxor x175 (KQ.KQRun.rd 0 176 s) in
    let x177 := PrimInt63.add x176 (KQ.KQRun.rd 0 177 s) in
    let x178 := PrimInt63.mul x177 (KQ.KQRun.rd 0 178 s) in
    let x179 := PrimInt63.lxor x178 (KQ.KQRun.rd 0 179 s) in
    let x180 := PrimInt63.add x179 (KQ.KQRun.rd 0 180 s) in
    let x181 := PrimInt63.mul x180 (KQ.KQRun.rd 0 181 s) in
    let x182 := PrimInt63.lxor x181 (KQ.KQRun.rd 0 182 s) in
    let x183 := PrimInt63.add x182 (KQ.KQRun.rd 0 183 s) in
    let x184 := PrimInt63.mul x183 (KQ.KQRun.rd 0 184 s) in
    let x185 := PrimInt63.lxor x184 (KQ.KQRun.rd 0 185 s) in
    let x186 := PrimInt63.add x185 (KQ.KQRun.rd 0 186 s) in
    let x187 := PrimInt63.mul x186 (KQ.KQRun.rd 0 187 s) in
    let x188 := PrimInt63.lxor x187 (KQ.KQRun.rd 0 188 s) in
    let x189 := PrimInt63.add x188 (KQ.KQRun.rd 0 189 s) in
    let x190 := PrimInt63.mul x189 (KQ.KQRun.rd 0 190 s) in
    let x191 := PrimInt63.lxor x190 (KQ.KQRun.rd 0 191 s) in
    let x192 := PrimInt63.add x191 (KQ.KQRun.rd 0 192 s) in
    let x193 := PrimInt63.mul x192 (KQ.KQRun.rd 0 193 s) in
    let x194 := PrimInt63.lxor x193 (KQ.KQRun.rd 0 194 s) in
    let x195 := PrimInt63.add x194 (KQ.KQRun.rd 0 195 s) in
    let x196 := PrimInt63.mul x195 (KQ.KQRun.rd 0 196 s) in
    let x197 := PrimInt63.lxor x196 (KQ.KQRun.rd 0 197 s) in
    let x198 := PrimInt63.add x197 (KQ.KQRun.rd 0 198 s) in
    let x199 := PrimInt63.mul x198 (KQ.KQRun.rd 0 199 s) in
    let x200 := PrimInt63.lxor x199 (KQ.KQRun.rd 0 200 s) in
    let x201 := PrimInt63.add x200 (KQ.KQRun.rd 0 201 s) in
    let x202 := PrimInt63.mul x201 (KQ.KQRun.rd 0 202 s) in
    let x203 := PrimInt63.lxor x202 (KQ.KQRun.rd 0 203 s) in
    let x204 := PrimInt63.add x203 (KQ.KQRun.rd 0 204 s) in
    let x205 := PrimInt63.mul x204 (KQ.KQRun.rd 0 205 s) in
    let x206 := PrimInt63.lxor x205 (KQ.KQRun.rd 0 206 s) in
    let x207 := PrimInt63.add x206 (KQ.KQRun.rd 0 207 s) in
    let x208 := PrimInt63.mul x207 (KQ.KQRun.rd 0 208 s) in
    let x209 := PrimInt63.lxor x208 (KQ.KQRun.rd 0 209 s) in
    let x210 := PrimInt63.add x209 (KQ.KQRun.rd 0 210 s) in
    let x211 := PrimInt63.mul x210 (KQ.KQRun.rd 0 211 s) in
    let x212 := PrimInt63.lxor x211 (KQ.KQRun.rd 0 212 s) in
    let x213 := PrimInt63.add x212 (KQ.KQRun.rd 0 213 s) in
    let x214 := PrimInt63.mul x213 (KQ.KQRun.rd 0 214 s) in
    let x215 := PrimInt63.lxor x214 (KQ.KQRun.rd 0 215 s) in
    let x216 := PrimInt63.add x215 (KQ.KQRun.rd 0 216 s) in
    let x217 := PrimInt63.mul x216 (KQ.KQRun.rd 0 217 s) in
    let x218 := PrimInt63.lxor x217 (KQ.KQRun.rd 0 218 s) in
    let x219 := PrimInt63.add x218 (KQ.KQRun.rd 0 219 s) in
    let x220 := PrimInt63.mul x219 (KQ.KQRun.rd 0 220 s) in
    let x221 := PrimInt63.lxor x220 (KQ.KQRun.rd 0 221 s) in
    let x222 := PrimInt63.add x221 (KQ.KQRun.rd 0 222 s) in
    let x223 := PrimInt63.mul x222 (KQ.KQRun.rd 0 223 s) in
    let x224 := PrimInt63.lxor x223 (KQ.KQRun.rd 0 224 s) in
    let x225 := PrimInt63.add x224 (KQ.KQRun.rd 0 225 s) in
    let x226 := PrimInt63.mul x225 (KQ.KQRun.rd 0 226 s) in
    let x227 := PrimInt63.lxor x226 (KQ.KQRun.rd 0 227 s) in
    let x228 := PrimInt63.add x227 (KQ.KQRun.rd 0 228 s) in
    let x229 := PrimInt63.mul x228 (KQ.KQRun.rd 0 229 s) in
    let x230 := PrimInt63.lxor x229 (KQ.KQRun.rd 0 230 s) in
    let x231 := PrimInt63.add x230 (KQ.KQRun.rd 0 231 s) in
    let x232 := PrimInt63.mul x231 (KQ.KQRun.rd 0 232 s) in
    let x233 := PrimInt63.lxor x232 (KQ.KQRun.rd 0 233 s) in
    let x234 := PrimInt63.add x233 (KQ.KQRun.rd 0 234 s) in
    let x235 := PrimInt63.mul x234 (KQ.KQRun.rd 0 235 s) in
    let x236 := PrimInt63.lxor x235 (KQ.KQRun.rd 0 236 s) in
    let x237 := PrimInt63.add x236 (KQ.KQRun.rd 0 237 s) in
    let x238 := PrimInt63.mul x237 (KQ.KQRun.rd 0 238 s) in
    let x239 := PrimInt63.lxor x238 (KQ.KQRun.rd 0 239 s) in
    let x240 := PrimInt63.add x239 (KQ.KQRun.rd 0 240 s) in
    let x241 := PrimInt63.mul x240 (KQ.KQRun.rd 0 241 s) in
    let x242 := PrimInt63.lxor x241 (KQ.KQRun.rd 0 242 s) in
    let x243 := PrimInt63.add x242 (KQ.KQRun.rd 0 243 s) in
    let x244 := PrimInt63.mul x243 (KQ.KQRun.rd 0 244 s) in
    let x245 := PrimInt63.lxor x244 (KQ.KQRun.rd 0 245 s) in
    let x246 := PrimInt63.add x245 (KQ.KQRun.rd 0 246 s) in
    let x247 := PrimInt63.mul x246 (KQ.KQRun.rd 0 247 s) in
    let x248 := PrimInt63.lxor x247 (KQ.KQRun.rd 0 248 s) in
    let x249 := PrimInt63.add x248 (KQ.KQRun.rd 0 249 s) in
    let x250 := PrimInt63.mul x249 (KQ.KQRun.rd 0 250 s) in
    let x251 := PrimInt63.lxor x250 (KQ.KQRun.rd 0 251 s) in
    let x252 := PrimInt63.add x251 (KQ.KQRun.rd 0 252 s) in
    let x253 := PrimInt63.mul x252 (KQ.KQRun.rd 0 253 s) in
    let x254 := PrimInt63.lxor x253 (KQ.KQRun.rd 0 254 s) in
    let x255 := PrimInt63.add x254 (KQ.KQRun.rd 0 255 s) in
    let x256 := PrimInt63.mul x255 (KQ.KQRun.rd 0 256 s) in
    let x257 := PrimInt63.lxor x256 (KQ.KQRun.rd 0 257 s) in
    let x258 := PrimInt63.add x257 (KQ.KQRun.rd 0 258 s) in
    let x259 := PrimInt63.mul x258 (KQ.KQRun.rd 0 259 s) in
    let x260 := PrimInt63.lxor x259 (KQ.KQRun.rd 0 260 s) in
    let x261 := PrimInt63.add x260 (KQ.KQRun.rd 0 261 s) in
    let x262 := PrimInt63.mul x261 (KQ.KQRun.rd 0 262 s) in
    let x263 := PrimInt63.lxor x262 (KQ.KQRun.rd 0 263 s) in
    let x264 := PrimInt63.add x263 (KQ.KQRun.rd 0 264 s) in
    let x265 := PrimInt63.mul x264 (KQ.KQRun.rd 0 265 s) in
    let x266 := PrimInt63.lxor x265 (KQ.KQRun.rd 0 266 s) in
    let x267 := PrimInt63.add x266 (KQ.KQRun.rd 0 267 s) in
    let x268 := PrimInt63.mul x267 (KQ.KQRun.rd 0 268 s) in
    let x269 := PrimInt63.lxor x268 (KQ.KQRun.rd 0 269 s) in
    let x270 := PrimInt63.add x269 (KQ.KQRun.rd 0 270 s) in
    let x271 := PrimInt63.mul x270 (KQ.KQRun.rd 0 271 s) in
    let x272 := PrimInt63.lxor x271 (KQ.KQRun.rd 0 272 s) in
    let x273 := PrimInt63.add x272 (KQ.KQRun.rd 0 273 s) in
    let x274 := PrimInt63.mul x273 (KQ.KQRun.rd 0 274 s) in
    let x275 := PrimInt63.lxor x274 (KQ.KQRun.rd 0 275 s) in
    let x276 := PrimInt63.add x275 (KQ.KQRun.rd 0 276 s) in
    let x277 := PrimInt63.mul x276 (KQ.KQRun.rd 0 277 s) in
    let x278 := PrimInt63.lxor x277 (KQ.KQRun.rd 0 278 s) in
    let x279 := PrimInt63.add x278 (KQ.KQRun.rd 0 279 s) in
    let x280 := PrimInt63.mul x279 (KQ.KQRun.rd 0 280 s) in
    let x281 := PrimInt63.lxor x280 (KQ.KQRun.rd 0 281 s) in
    let x282 := PrimInt63.add x281 (KQ.KQRun.rd 0 282 s) in
    let x283 := PrimInt63.mul x282 (KQ.KQRun.rd 0 283 s) in
    let x284 := PrimInt63.lxor x283 (KQ.KQRun.rd 0 284 s) in
    let x285 := PrimInt63.add x284 (KQ.KQRun.rd 0 285 s) in
    let x286 := PrimInt63.mul x285 (KQ.KQRun.rd 0 286 s) in
    let x287 := PrimInt63.lxor x286 (KQ.KQRun.rd 0 287 s) in
    let x288 := PrimInt63.add x287 (KQ.KQRun.rd 0 288 s) in
    let x289 := PrimInt63.mul x288 (KQ.KQRun.rd 0 289 s) in
    let x290 := PrimInt63.lxor x289 (KQ.KQRun.rd 0 290 s) in
    let x291 := PrimInt63.add x290 (KQ.KQRun.rd 0 291 s) in
    let x292 := PrimInt63.mul x291 (KQ.KQRun.rd 0 292 s) in
    let x293 := PrimInt63.lxor x292 (KQ.KQRun.rd 0 293 s) in
    let x294 := PrimInt63.add x293 (KQ.KQRun.rd 0 294 s) in
    let x295 := PrimInt63.mul x294 (KQ.KQRun.rd 0 295 s) in
    let x296 := PrimInt63.lxor x295 (KQ.KQRun.rd 0 296 s) in
    let x297 := PrimInt63.add x296 (KQ.KQRun.rd 0 297 s) in
    let x298 := PrimInt63.mul x297 (KQ.KQRun.rd 0 298 s) in
    let x299 := PrimInt63.lxor x298 (KQ.KQRun.rd 0 299 s) in
    let x300 := PrimInt63.add x299 (KQ.KQRun.rd 0 300 s) in
    long m x300 s
  end.

Definition long_s1 := (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 1))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 2))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 3))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 4))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 5))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 6))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 7))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 8))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 9))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 10))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 11))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 12))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 13))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 14))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 15))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 16))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 17))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 18))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 19))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 20))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 21))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 22))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 23))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 24))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 25))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 26))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 27))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 28))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 29))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 30))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 31))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 32))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 33))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 34))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 35))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 36))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 37))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 38))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 39))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 40))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 41))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 42))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 43))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 44))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 45))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 46))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 47))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 48))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 49))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 50))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 51))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 52))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 53))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 54))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 55))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 56))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 57))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 58))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 59))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 60))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 61))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 62))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 63))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 64))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 65))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 66))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 67))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 68))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 69))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 70))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 71))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 72))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 73))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 74))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 75))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 76))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 77))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 78))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 79))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 80))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 81))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 82))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 83))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 84))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 85))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 86))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 87))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 88))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 89))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 90))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 91))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 92))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 93))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 94))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 95))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 96))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 97))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 98))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 99))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 100))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 101))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 102))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 103))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 104))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 105))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 106))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 107))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 108))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 109))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 110))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 111))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 112))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 113))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 114))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 115))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 116))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 117))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 118))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 119))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 120))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 121))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 122))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 123))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 124))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 125))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 126))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 127))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 128))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 129))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 130))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 131))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 132))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 133))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 134))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 135))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 136))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 137))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 138))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 139))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 140))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 141))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 142))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 143))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 144))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 145))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 146))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 147))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 148))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 149))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 150))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 151))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 152))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 153))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 154))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 155))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 156))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 157))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 158))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 159))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 160))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 161))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 162))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 163))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 164))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 165))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 166))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 167))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 168))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 169))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 170))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 171))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 172))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 173))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 174))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 175))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 176))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 177))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 178))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 179))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 180))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 181))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 182))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 183))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 184))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 185))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 186))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 187))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 188))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 189))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 190))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 191))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 192))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 193))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 194))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 195))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 196))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 197))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 198))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 199))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 200))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 201))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 202))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 203))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 204))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 205))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 206))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 207))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 208))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 209))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 210))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 211))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 212))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 213))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 214))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 215))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 216))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 217))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 218))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 219))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 220))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 221))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 222))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 223))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 224))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 225))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 226))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 227))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 228))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 229))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 230))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 231))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 232))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 233))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 234))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 235))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 236))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 237))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 238))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 239))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 240))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 241))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 242))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 243))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 244))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 245))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 246))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 247))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 248))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 249))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 250))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 251))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 252))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 253))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 254))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 255))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 256))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 257))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 258))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 259))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 260))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 261))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 262))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 263))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 264))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 265))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 266))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 267))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 268))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 269))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 270))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 271))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 272))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 273))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 274))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 275))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 276))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 277))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 278))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 279))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 280))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 281))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 282))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 283))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 284))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 285))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 286))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 287))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 288))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 289))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 290))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 291))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 292))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 293))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 294))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 295))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 296))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 297))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 298))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 299))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 300))) (SRec (SCons (SVar 0) SNil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Time Lemma long_is : long = denote_fun 1 (SVar 0) long_s1.
Proof. Time exact eq_refl. Time Qed.

Definition long_fn := compile_fun 1001%positive 1 (SVar 0) long_s1.
Definition long_P := mkprog [(1001%positive, long_fn)] [].
Time Lemma long_ok : forall n a M, (Z.of_nat n < wB)%Z -> runk long_P 1001%positive [ofn n; a] M (long n a M) M.
Proof.
  intros n a M B.
  change (long n a M) with (app 1 (denote_fun 1 (SVar 0) long_s1 n) [a] M).
  exact (compile_fun_ok long_P 1001%positive 1 (SVar 0) long_s1 eq_refl eq_refl eq_refl n [a] M eq_refl B).
Time Qed.

Print Assumptions sum_ok.
