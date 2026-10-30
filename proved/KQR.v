(** KQR.v -- the verified compiler by reflection (Rocq-C-solution.md §1.12, §12.V).

    [sexp] is a syntax of a fragment: numbers, operations, tests, lets, reads of the memory, the recursive call on the
    counter's predecessor, calls of the program's other functions.  A function has a signature (a counter or not, [k] numbers,
    a memory or not) and a body (recursive on the counter, or plain).  [denote_f] gives the Rocq function a syntax tree stands
    for, reduced to exactly the shape of the user's text, with the meanings of the callees as parameters -- at the
    per-program check they are the user's own functions -- so that the check [f = denote_f ..] is the kernel's computation
    alone.  [compile_f] makes the KQL function; [compile_f_ok] -- proved once, for every syntax tree -- says: if the callees'
    KQL compute their meanings, the function's KQL computes its meaning (the modular shape of today's per-function
    statements). *)

From Stdlib Require Import List Uint63 ZArith Lia.
From Stdlib Require FinFun.
From compcert Require Import Coqlib Maps AST.
From KQC Require Import KQL KQLAuto KQMSem.
Require KQ.KQRun.
Import ListNotations.

Notation mem := KQ.KQRun.mem.

(** the counter given to a callee: none, this function's counter, its predecessor *)
Inductive ncnt := NNone | NCnt | NPred.

Inductive sexp : Type :=
| SVar (i : nat)                     (* a number: the i-th of the function's numbers and lets, the nearest first *)
| SInt (n : i63)
| SOp (o : binop) (a b : sexp)
| SIf (c : cmpop) (a b : sexp) (t e : sexp)
| SLet (e1 e2 : sexp)                (* let x := e1 in e2; x is SVar 0 in e2 *)
| SRd (h i : sexp)                   (* rd h i s, s the function's memory *)
| SRec (args : sexps)                (* the function itself on the counter's predecessor, these numbers, the memory *)
| SCall (f : nat) (c : ncnt) (args : sexps)   (* function f of the program, with that counter, these numbers, the memory *)
with sexps : Type :=
| SNil
| SCons (e : sexp) (r : sexps).

Scheme sexp_mut := Induction for sexp Sort Prop
with sexps_mut := Induction for sexps Sort Prop.
Combined Scheme sexp_comb from sexp_mut, sexps_mut.

(** a function's signature: a counter first or not, [sk] numbers, a memory last or not *)
Record sig := mksig { sc : bool; sk : nat; sm : bool }.

Fixpoint ntype (k : nat) (m : bool) : Type :=
  match k with O => if m then (mem -> i63) else i63 | S k => i63 -> ntype k m end.

Definition ftype (g : sig) : Type := if sc g then nat -> ntype (sk g) (sm g) else ntype (sk g) (sm g).

(** a memory for the meaning of a function that takes none: never read (a well formed body reads no memory then) *)
Definition dummy_mem : mem := KQ.KQRun.kq_input 0%uint63.

(** [absn k m F] is [fun x1 .. xk (s) => F [xk; ..; x1] s]: the parameters bound before anything else, as in the user's text *)
Fixpoint absn (k : nat) (m : bool) {struct k} : (list i63 -> mem -> i63) -> ntype k m :=
  match k as k0 return (list i63 -> mem -> i63) -> ntype k0 m with
  | O => if m as m0 return (list i63 -> mem -> i63) -> ntype O m0 then (fun F s => F [] s) else (fun F => F [] dummy_mem)
  | S k => fun F x => absn k m (fun env s => F (env ++ [x]) s)
  end.

(** [appn k m g [v1; ..; vk] s] is [g v1 .. vk (s)] *)
Fixpoint appn (k : nat) (m : bool) {struct k} : ntype k m -> list i63 -> mem -> i63 :=
  match k as k0 return ntype k0 m -> list i63 -> mem -> i63 with
  | O => if m as m0 return ntype O m0 -> list i63 -> mem -> i63 then (fun g _ s => g s) else (fun g _ _ => g)
  | S k => fun g l s => match l with x :: l => appn k m (g x) l s | [] => appn k m (g 0%uint63) [] s end
  end.

(** a call of a function of signature [g] *)
Definition callf (g : sig) : ftype g -> nat -> list i63 -> mem -> i63 :=
  match g as g0 return ftype g0 -> nat -> list i63 -> mem -> i63 with
  | mksig c k m => if c as c0 return ftype (mksig c0 k m) -> nat -> list i63 -> mem -> i63
                   then (fun h n vs s => appn k m (h n) vs s)
                   else (fun h _ vs s => appn k m h vs s)
  end.

(** a callee: its signature and its meaning *)
Definition callee := { g : sig & ftype g }.

Definition cval (c : ncnt) (cn cm : nat) : nat := match c with NNone => O | NCnt => cn | NPred => cm end.

Fixpoint denote_e (cs : list callee) (cn cm : nat) (rec : list i63 -> i63) (env : list i63) (s : mem) (e : sexp) {struct e} : i63 :=
  match e with
  | SVar i => nth i env 0%uint63
  | SInt n => n
  | SOp o a b => binop_sem o (denote_e cs cn cm rec env s a) (denote_e cs cn cm rec env s b)
  | SIf c a b t f => if cmp_sem c (denote_e cs cn cm rec env s a) (denote_e cs cn cm rec env s b)
                     then denote_e cs cn cm rec env s t else denote_e cs cn cm rec env s f
  | SLet e1 e2 => let x := denote_e cs cn cm rec env s e1 in denote_e cs cn cm rec (x :: env) s e2
  | SRd h i => KQ.KQRun.rd (denote_e cs cn cm rec env s h) (denote_e cs cn cm rec env s i) s
  | SRec args => rec (denote_es cs cn cm rec env s args)
  | SCall f c args =>
      match nth_error cs f with
      | Some (existT _ g h) => callf g h (cval c cn cm) (denote_es cs cn cm rec env s args) s
      | None => 0%uint63
      end
  end
with denote_es (cs : list callee) (cn cm : nat) (rec : list i63 -> i63) (env : list i63) (s : mem) (es : sexps) {struct es}
  : list i63 :=
  match es with
  | SNil => []
  | SCons e r => denote_e cs cn cm rec env s e :: denote_es cs cn cm rec env s r
  end.

(** a function's body: recursive on the counter ([e0] when it is 0, [e1] otherwise), or plain *)
Inductive fbody := FRec (e0 e1 : sexp) | FPlain (e : sexp).

Definition denote_f (cs : list callee) (g : sig) (b : fbody) : ftype g :=
  match g as g0 return ftype g0 with
  | mksig c k m =>
      if c as c0 return ftype (mksig c0 k m) then
        match b with
        | FRec e0 e1 =>
            fix go (n : nat) : ntype k m :=
              absn k m (fun env s => match n with
                                     | O => denote_e cs n O (fun _ => 0%uint63) env s e0
                                     | S n' => denote_e cs n n' (fun args => appn k m (go n') args s) env s e1
                                     end)
        | FPlain e => fun n => absn k m (fun env s => denote_e cs n O (fun _ => 0%uint63) env s e)
        end
      else
        match b with
        | FPlain e => absn k m (fun env s => denote_e cs O O (fun _ => 0%uint63) env s e)
        | FRec _ _ => absn k m (fun _ _ => 0%uint63)
        end
  end.

(* ================================================================ compile *)
Section C.
Variable gidf : nat -> ident.   (* the KQL name of the program's function i *)
Variable g : ident.             (* the function's own name *)
Variable mv : ident.            (* the variable holding the counter's predecessor *)

Definition catoms (c : ncnt) : list atom :=
  match c with NNone => [] | NCnt => [Avar 1%positive] | NPred => [Avar mv] end.

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
  | SCall f c args => cexps args env nxt (fun As n => Ecall n (gidf f) (catoms c ++ As) (K (Avar n) (Pos.succ n)))
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

Definition cnt_ok (c : ncnt) (scg hasc haspred : bool) : bool :=
  match c with NNone => negb scg | NCnt => scg && hasc | NPred => scg && haspred end.

(** well formed, in a function whose callees have the signatures [sigs]: the recursive call only where [r] allows it, with [k]
    numbers; a counter given only where there is one; the memory read, or given to a callee, only where there is one ([mok]) *)
Fixpoint wf (sigs : list sig) (r hasc haspred mok : bool) (k : nat) (e : sexp) {struct e} : bool :=
  match e with
  | SVar _ | SInt _ => true
  | SOp _ a b | SLet a b => wf sigs r hasc haspred mok k a && wf sigs r hasc haspred mok k b
  | SRd a b => mok && wf sigs r hasc haspred mok k a && wf sigs r hasc haspred mok k b
  | SIf _ a b t f => wf sigs r hasc haspred mok k a && wf sigs r hasc haspred mok k b
                     && wf sigs r hasc haspred mok k t && wf sigs r hasc haspred mok k f
  | SRec args => r && haspred && Nat.eqb (len_s args) k && wfs sigs r hasc haspred mok k args
  | SCall f c args =>
      match nth_error sigs f with
      | Some gs => Nat.eqb (len_s args) (sk gs) && implb (sm gs) mok && cnt_ok c (sc gs) hasc haspred
                   && wfs sigs r hasc haspred mok k args
      | None => false
      end
  end
with wfs (sigs : list sig) (r hasc haspred mok : bool) (k : nat) (es : sexps) {struct es} : bool :=
  match es with SNil => true | SCons e es => wf sigs r hasc haspred mok k e && wfs sigs r hasc haspred mok k es end.

Definition wf_f (sigs : list sig) (gs : sig) (b : fbody) : bool :=
  match b with
  | FRec e0 e1 => sc gs && wf sigs false true false (sm gs) (sk gs) e0 && wf sigs true true true (sm gs) (sk gs) e1
  | FPlain e => wf sigs false (sc gs) false (sm gs) (sk gs) e
  end.

(** the function: the counter in 1 (if there is one), then the numbers; the next variable holds the counter's predecessor *)
Definition ibase (c : bool) : nat := if c then 1 else 0.
Definition params (c : bool) (k : nat) : list ident := map Pos.of_succ_nat (seq 0 (k + ibase c)).
Definition env0 (c : bool) (k : nat) : list atom := map (fun i => Avar (Pos.of_succ_nat (ibase c + i))) (rev (seq 0 k)).
Definition pmv (gs : sig) : ident := Pos.of_succ_nat (sk gs + ibase (sc gs)).

Definition compile_f (gidf : nat -> ident) (j : nat) (gs : sig) (b : fbody) : fn :=
  let mv := pmv gs in
  mkfn (params (sc gs) (sk gs))
       match b with
       | FRec e0 e1 =>
           Eif Ceq (Avar 1%positive) (Aint 0%uint63)
               (ctail gidf (gidf j) mv e0 (env0 (sc gs) (sk gs)) (Pos.succ mv))
               (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63) (ctail gidf (gidf j) mv e1 (env0 (sc gs) (sk gs)) (Pos.succ mv)))
       | FPlain e => ctail gidf (gidf j) mv e (env0 (sc gs) (sk gs)) (Pos.succ mv)
       end.

(** what a function's theorem says, and what a caller assumes of a callee *)
Definition callee_ok (P : prog) (id : ident) (gs : sig) (h : ftype gs) : Prop :=
  forall n vs M, length vs = sk gs -> (Z.of_nat n < wB)%Z ->
    runk P id ((if sc gs then [ofn n] else []) ++ vs) M (callf gs h n vs M) M.

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

Lemma avals_app : forall rho l1 l2 v1 v2, avals rho l1 = Some v1 -> avals rho l2 = Some v2 -> avals rho (l1 ++ l2) = Some (v1 ++ v2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 v1 v2 A1 A2; simpl in *.
  - injection A1 as <-. exact A2.
  - destruct (aval rho a) eqn:Ea; [|discriminate]. destruct (avals rho l1) eqn:El; [|discriminate].
    injection A1 as <-. rewrite (IH l2 l v2 eq_refl A2). reflexivity.
Qed.

Definition callees_ok (P : prog) (gidf : nat -> ident) (cs : list callee) : Prop :=
  forall f, match nth_error cs f with Some (existT _ gs h) => callee_ok P (gidf f) gs h | None => True end.

Lemma no_callees : forall P gidf, callees_ok P gidf [].
Proof. intros P gidf [|f]; exact Logic.I. Qed.

Lemma nth_sigs : forall (cs : list callee) f, nth_error (map (@projT1 _ _) cs) f = option_map (@projT1 _ _) (nth_error cs f).
Proof. induction cs as [|c cs IH]; intros [|f]; simpl; auto. Qed.

Lemma len_denote_es : forall cs cn cm rec denv s es, length (denote_es cs cn cm rec denv s es) = len_s es.
Proof. intros cs cn cm rec denv s es. induction es; simpl; auto. Qed.

(** a function without a memory never reads one: its meaning is the same for any memory *)
Lemma appn_false : forall k (x : ntype k false) vs s s', appn k false x vs s = appn k false x vs s'.
Proof. induction k as [|k IH]; intros x vs s s'; simpl; auto. destruct vs; apply IH. Qed.

Lemma callf_nomem : forall gs h n vs s s', sm gs = false -> callf gs h n vs s = callf gs h n vs s'.
Proof. intros [c k m] h n vs s s' E; simpl in E; subst m. destruct c; apply appn_false. Qed.

Lemma denote_nomem :
  (forall e cs cn cm rec env s s' r hasc haspred k, wf (map (@projT1 _ _) cs) r hasc haspred false k e = true ->
     denote_e cs cn cm rec env s e = denote_e cs cn cm rec env s' e)
  /\
  (forall es cs cn cm rec env s s' r hasc haspred k, wfs (map (@projT1 _ _) cs) r hasc haspred false k es = true ->
     denote_es cs cn cm rec env s es = denote_es cs cn cm rec env s' es).
Proof.
  apply sexp_comb.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros o a IHa b IHb cs cn cm rec env s s' r hasc haspred k W. simpl in *. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa cs cn cm rec env s s' r hasc haspred k Wa), (IHb cs cn cm rec env s s' r hasc haspred k Wb). reflexivity.
  - intros c a IHa b IHb t IHt e IHe cs cn cm rec env s s' r hasc haspred k W. simpl in *.
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ s s' _ _ _ _ Wa), (IHb _ _ _ _ _ s s' _ _ _ _ Wb), (IHt _ _ _ _ _ s s' _ _ _ _ Wt),
            (IHe _ _ _ _ _ s s' _ _ _ _ Wf). reflexivity.
  - intros e1 IH1 e2 IH2 cs cn cm rec env s s' r hasc haspred k W. simpl in *. apply andb_true_iff in W as [W1 W2].
    rewrite (IH1 _ _ _ _ _ s s' _ _ _ _ W1). apply (IH2 _ _ _ _ _ s s' _ _ _ _ W2).
  - intros h IHh i IHi cs cn cm rec env s s' r hasc haspred k W. simpl in W. discriminate.
  - intros args IHs cs cn cm rec env s s' r hasc haspred k W. simpl in *. apply andb_true_iff in W as [W Ws].
    rewrite (IHs _ _ _ _ _ s s' _ _ _ _ Ws). reflexivity.
  - intros fi c args IHs cs cn cm rec env s s' r hasc haspred k W. cbn [wf] in W. rewrite nth_sigs in W. cbn [denote_e].
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [Wk Wm].
    rewrite (IHs _ _ _ _ _ s s' _ _ _ _ Ws). apply callf_nomem. destruct (sm gs); [discriminate | reflexivity].
  - intros; reflexivity.
  - intros e IHe es IHes cs cn cm rec env s s' r hasc haspred k W. simpl in *. apply andb_true_iff in W as [We Wes].
    rewrite (IHe _ _ _ _ _ s s' _ _ _ _ We), (IHes _ _ _ _ _ s s' _ _ _ _ Wes). reflexivity.
Qed.

(** the meaning depends on the recursive call's meaning only through its values *)
Lemma denote_rec_ext :
  (forall e cs cn cm rec1 rec2 env s, (forall l, rec1 l = rec2 l) -> denote_e cs cn cm rec1 env s e = denote_e cs cn cm rec2 env s e)
  /\
  (forall es cs cn cm rec1 rec2 env s, (forall l, rec1 l = rec2 l) -> denote_es cs cn cm rec1 env s es = denote_es cs cn cm rec2 env s es).
Proof.
  apply sexp_comb.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros o a IHa b IHb cs cn cm r1 r2 env s E. simpl. rewrite (IHa cs cn cm r1 r2 env s E), (IHb cs cn cm r1 r2 env s E). reflexivity.
  - intros c a IHa b IHb t IHt e IHe cs cn cm r1 r2 env s E. simpl.
    rewrite (IHa _ _ _ _ _ _ _ E), (IHb _ _ _ _ _ _ _ E), (IHt _ _ _ _ _ _ _ E), (IHe _ _ _ _ _ _ _ E). reflexivity.
  - intros e1 IH1 e2 IH2 cs cn cm r1 r2 env s E. simpl. rewrite (IH1 _ _ _ _ _ _ _ E). apply (IH2 _ _ _ _ _ _ _ E).
  - intros h IHh i IHi cs cn cm r1 r2 env s E. simpl. rewrite (IHh _ _ _ _ _ _ _ E), (IHi _ _ _ _ _ _ _ E). reflexivity.
  - intros args IHs cs cn cm r1 r2 env s E. simpl. rewrite (IHs _ _ _ _ _ _ _ E). apply E.
  - intros fi c args IHs cs cn cm r1 r2 env s E. simpl. rewrite (IHs _ _ _ _ _ _ _ E). reflexivity.
  - intros; reflexivity.
  - intros e IHe es IHes cs cn cm r1 r2 env s E. simpl. rewrite (IHe _ _ _ _ _ _ _ E), (IHes _ _ _ _ _ _ _ E). reflexivity.
Qed.

Section Sim.
Variables (P : prog) (f : fn) (gidf : nat -> ident) (g mv : ident) (M : kmemt).
Variables (cs : list callee) (r hasc haspred mok : bool) (k : nat) (rec : list i63 -> i63) (cn cm : nat).
(** the recursive call, where it is allowed, computes [rec]; the callees compute their meanings; the counters are in range *)
Hypothesis Hrec : r = true -> forall vs, length vs = k -> runk P g (ofn cm :: vs) M (rec vs) M.
Hypothesis Hcs : callees_ok P gidf cs.
Hypothesis Hbn : hasc = true -> (Z.of_nat cn < wB)%Z.
Hypothesis Hbm : haspred = true -> (Z.of_nat cm < wB)%Z.

Let sigs := map (@projT1 _ _) cs.

Definition inv (rho : env) (envA : list atom) (denv : list i63) (nxt : ident) : Prop :=
  env_ok rho envA denv /\ lt_all envA nxt /\ Pos.lt mv nxt /\
  (hasc = true -> rho ! 1%positive = Some (ofn cn)) /\ (haspred = true -> rho ! mv = Some (ofn cm)).

Lemma inv_step : forall rho rho' envA denv nxt n', inv rho envA denv nxt -> agree rho rho' nxt -> Pos.le nxt n' ->
  inv rho' envA denv n'.
Proof.
  intros rho rho' envA denv nxt n' (E & L & Mv & C & R) A Le. split; [|split; [|split; [|split]]].
  - eapply env_ok_agree; eauto.
  - eapply lt_all_mono; eauto.
  - lia.
  - intro Hc. rewrite A by lia. auto.
  - intro Hp. rewrite A by auto. auto.
Qed.

Lemma catoms_ok : forall c gs rho nxt, inv rho [] [] nxt -> cnt_ok c (sc gs) hasc haspred = true ->
  avals rho (catoms mv c) = Some (if sc gs then [ofn (cval c cn cm)] else []) /\ (Z.of_nat (cval c cn cm) < wB)%Z.
Proof.
  intros c gs rho nxt (_ & _ & _ & C & R) W. destruct c; simpl in *.
  - destruct (sc gs); simpl in W; [discriminate|]. split; [reflexivity|]. unfold wB. simpl. lia.
  - apply andb_true_iff in W as [S1 S2]. rewrite S1. rewrite (C S2). split; auto.
  - apply andb_true_iff in W as [S1 S2]. rewrite S1. rewrite (R S2). split; auto.
Qed.

Lemma cexp_all :
  (forall e envA denv nxt K rho v M', wf sigs r hasc haspred mok k e = true -> inv rho envA denv nxt ->
     (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' -> aval rho' a = Some (denote_e cs cn cm rec denv M e) ->
        evalk P f rho' M (K a n') v M') ->
     evalk P f rho M (cexp gidf g mv e envA nxt K) v M')
  /\
  (forall es envA denv nxt K rho v M', wfs sigs r hasc haspred mok k es = true -> inv rho envA denv nxt ->
     (forall rho' n' As, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') As ->
        avals rho' As = Some (denote_es cs cn cm rec denv M es) -> evalk P f rho' M (K As n') v M') ->
     evalk P f rho M (cexps gidf g mv es envA nxt K) v M').
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
      destruct (cmp_sem c (denote_e cs cn cm rec denv M a) (denote_e cs cn cm rec denv M b)) eqn:C.
      * apply IHt with (denv := denv); auto. intros rho3 n3 a3 A3 Le3 L3 V3.
        apply HK; [| lia | exact L3 | exact V3].
        eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia.
      * apply IHe with (denv := denv); auto. intros rho3 n3 a3 A3 Le3 L3 V3.
        apply HK; [| lia | exact L3 | exact V3].
        eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia.
  - (* SLet *) intros e1 IH1 e2 IH2 envA denv nxt K rho v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W1 W2].
    apply IH1 with (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH2 with (denv := denote_e cs cn cm rec denv M e1 :: denv); auto.
    + destruct (inv_step rho rho1 envA denv nxt n1 Iv A1 Le1) as (E & L & Mv & C & R).
      split; [|split; [|split; [|split]]]; auto using env_ok_cons, lt_all_cons.
    + intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | exact V2].
  - (* SRd *) intros h IHh i IHi envA denv nxt K rho v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
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
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wp].
    apply IHs with (denv := denv); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    destruct (Hrec Wr (denote_es cs cn cm rec denv M args)) as (fg & rho' & F & B & EV).
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    destruct (inv_step rho rho1 envA denv nxt n1 Iv A1 Le1) as (_ & _ & Mv1 & C1 & R1).
    eapply K_call; eauto.
    + simpl. rewrite (R1 Wp), VAs. reflexivity.
    + apply HK.
      * eapply (agree_set1 rho rho1); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SCall *) intros fi c args IHs envA denv nxt K rho v M' W Iv HK. simpl in *.
    unfold sigs in W. rewrite nth_sigs in W. pose proof (Hcs fi) as Hc.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [Wk Wm].
    apply IHs with (denv := denv); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    destruct (inv_step rho rho1 envA denv nxt n1 Iv A1 Le1) as (E1 & L1 & Mv1 & C1 & R1).
    destruct (catoms_ok c gs rho1 n1) as (CA & CB); auto. { split; [|split; [|split; [|split]]]; auto; intro i; destruct i; simpl; auto. }
    destruct (Hc (cval c cn cm) (denote_es cs cn cm rec denv M args) M) as (fg & rho' & F & B & EV); auto.
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    eapply K_call; eauto.
    + apply avals_app; eauto.
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

Lemma ctail_ok : forall e envA denv nxt rho, wf sigs r hasc haspred mok k e = true -> inv rho envA denv nxt ->
  evalk P f rho M (ctail gidf g mv e envA nxt) (denote_e cs cn cm rec denv M e) M.
Proof.
  induction e; intros envA denv nxt rho W Iv; cbn [ctail] in *.
  - apply cexp_ok with (denv := denv); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (denv := denv); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (denv := denv); auto. intros. apply K_ret. auto.
  - (* SIf *) cbn [wf] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    apply cexp_ok with (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + assert (I2 : inv rho2 envA denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      cbn [denote_e]. destruct (cmp_sem c (denote_e cs cn cm rec denv M e1) (denote_e cs cn cm rec denv M e2)); auto.
  - (* SLet *) cbn [wf] in W. apply andb_true_iff in W as [W1 W2].
    apply cexp_ok with (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_e]. apply IHe2; auto.
    destruct (inv_step rho rho1 envA denv nxt n1 Iv A1 Le1) as (E & L & Mv & C & R).
    split; [|split; [|split; [|split]]]; auto using env_ok_cons, lt_all_cons.
  - apply cexp_ok with (denv := denv); auto. intros. apply K_ret. auto.
  - (* SRec *) cbn [wf] in W. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wp].
    apply cexps_ok with (denv := denv); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    destruct (Hrec Wr (denote_es cs cn cm rec denv M args)) as (fg & rho' & F & B & EV).
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    rewrite Hf in F. injection F as <-.
    destruct (inv_step rho rho1 envA denv nxt n1 Iv A1 Le1) as (_ & _ & Mv1 & C1 & R1).
    cbn [denote_e]. eapply K_loop; eauto. simpl. rewrite (R1 Wp), VAs. reflexivity.
  - apply cexp_ok with (denv := denv); auto. intros. apply K_ret. auto.
Qed.
End Sim.

(* ---------------------------------------------------------------- the function *)
Local Open Scope nat_scope.

Lemma appn_absn : forall k m F vs s, length vs = k -> appn k m (absn k m F) vs s = F (rev vs) (if m then s else dummy_mem).
Proof.
  induction k as [|k IH]; intros m F vs s L; destruct vs as [|v vs]; simpl in *; try discriminate.
  - destruct m; reflexivity.
  - injection L as L. rewrite IH by auto. reflexivity.
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

Lemma params_nth : forall c k j, j < k + ibase c -> nth j (params c k) 1%positive = Pos.of_succ_nat j.
Proof.
  intros c k j L. unfold params. rewrite nth_indep with (d' := Pos.of_succ_nat 0) by (rewrite map_length, seq_length; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma params_nodup : forall c k, NoDup (params c k).
Proof.
  intros c k. unfold params. apply FinFun.Injective_map_NoDup; [| apply seq_NoDup].
  intros a b E. apply SuccNat2Pos.inj; auto.
Qed.

Lemma params_length : forall c k, length (params c k) = k + ibase c.
Proof. intros c k. unfold params. rewrite map_length, seq_length. reflexivity. Qed.

Lemma env0_nth : forall c k i, i < k -> nth i (env0 c k) (Aint 0%uint63) = Avar (Pos.of_succ_nat (ibase c + (k - 1 - i))).
Proof.
  intros c k i L. unfold env0.
  rewrite nth_indep with (d' := Avar (Pos.of_succ_nat (ibase c + 0))) by (rewrite map_length, rev_length, seq_length; lia).
  rewrite map_nth with (d := 0). rewrite rev_nth by (rewrite seq_length; lia). rewrite seq_length, seq_nth by lia.
  f_equal. f_equal. lia.
Qed.

Lemma env0_out : forall c k i, k <= i -> nth i (env0 c k) (Aint 0%uint63) = Aint 0%uint63.
Proof. intros c k i L. apply nth_overflow. unfold env0. rewrite map_length, rev_length, seq_length. lia. Qed.

Lemma env0_lt : forall gs, lt_all (env0 (sc gs) (sk gs)) (pmv gs).
Proof.
  intros [c k m] i. unfold pmv. simpl. destruct (Nat.lt_ge_cases i k) as [L|L].
  - rewrite env0_nth by auto. simpl. apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. unfold ibase. destruct c; lia.
  - rewrite env0_out by auto. simpl. auto.
Qed.

(** the parameters bound: the counter in 1 (if any), the numbers after it, read by [env0] in the order of [denote_f] *)
Lemma bind_params : forall c k n vs, length vs = k ->
  exists rho0, bind (params c k) ((if c then [ofn n] else []) ++ vs) (PTree.empty _) = Some rho0 /\
    (c = true -> rho0 ! 1%positive = Some (ofn n)) /\ env_ok rho0 (env0 c k) (rev vs).
Proof.
  intros c k n vs L. destruct (bind_some (params c k) ((if c then [ofn n] else []) ++ vs) (PTree.empty _)) as [rho0 B].
  { rewrite params_length, app_length. unfold ibase. destruct c; simpl; lia. }
  exists rho0. split; auto. split.
  - intro Hc. subst c. pose proof (bind_nth _ _ _ _ 0 (params_nodup true k) B) as N. rewrite params_nth in N by (unfold ibase; lia).
    apply N. rewrite params_length. unfold ibase. lia.
  - intro i. destruct (Nat.lt_ge_cases i k) as [Li|Li].
    + rewrite env0_nth by auto. simpl.
      pose proof (bind_nth _ _ _ _ (ibase c + (k - 1 - i)) (params_nodup c k) B) as N.
      rewrite params_nth in N by (unfold ibase; destruct c; lia).
      rewrite N by (rewrite params_length; unfold ibase; destruct c; lia).
      rewrite rev_nth by lia. unfold ibase. destruct c; simpl.
      * f_equal. f_equal. lia.
      * f_equal. f_equal. lia.
    + rewrite env0_out by auto. simpl. rewrite nth_overflow; auto. rewrite rev_length. lia.
Qed.

Theorem compile_f_ok : forall P cs gidf j gs b,
  find P (gidf j) = Some (compile_f gidf j gs b) -> wf_f (map (@projT1 _ _) cs) gs b = true -> callees_ok P gidf cs ->
  callee_ok P (gidf j) gs (denote_f cs gs b).
Proof.
  intros P cs gidf j [c k m] b Hf W Hcs. unfold callee_ok. simpl sc. simpl sk. simpl sm.
  set (mv := pmv (mksig c k m)).
  assert (Lmv : lt_all (env0 c k) mv) by apply (env0_lt (mksig c k m)).
  destruct b as [e0 e1 | e]; simpl in W.
  - (* recursive on the counter *)
    destruct c; simpl in W; [|discriminate]. apply andb_true_iff in W as [W0 W1].
    assert (Mvgt : Pos.lt 1 mv).
    { unfold mv, pmv. simpl. apply Pos2Nat.inj_lt. rewrite SuccNat2Pos.id_succ. simpl. lia. }
    induction n as [|n' IH]; intros vs M L B.
    + destruct (bind_params true k 0 vs L) as (rho0 & Bd & R1 & E).
      exists (compile_f gidf j (mksig true k m) (FRec e0 e1)), rho0. split; [exact Hf|]. split; [exact Bd|].
      change (callf (mksig true k m) (denote_f cs (mksig true k m) (FRec e0 e1)) 0 vs M)
        with (appn k m (absn k m (fun env s => denote_e cs 0 0 (fun _ => 0%uint63) env s e0)) vs M).
      rewrite appn_absn by auto. simpl kbody.
      eapply K_if; [simpl; eauto | reflexivity | ]. rewrite ofn_0. simpl.
      assert (EQ : denote_e cs 0 0 (fun _ => 0%uint63) (rev vs) (if m then M else dummy_mem) e0
                   = denote_e cs 0 0 (fun _ => 0%uint63) (rev vs) M e0).
      { destruct m; [reflexivity|]. eapply (proj1 denote_nomem); eauto. }
      rewrite EQ.
      refine (ctail_ok P _ gidf (gidf j) mv M cs false true false m k (fun _ => 0%uint63) 0 0 _ Hcs _ _ Hf _ _ _ _ _ W0 _).
      * intros Habs; discriminate Habs.
      * intros _. reflexivity.
      * intros Habs; discriminate Habs.
      * split; [|split; [|split; [|split]]].
        -- exact E.
        -- eapply lt_all_mono; eauto. lia.
        -- lia.
        -- intros _. apply R1; reflexivity.
        -- intros Habs; discriminate Habs.
    + destruct (bind_params true k (S n') vs L) as (rho0 & Bd & R1 & E).
      exists (compile_f gidf j (mksig true k m) (FRec e0 e1)), rho0. split; [exact Hf|]. split; [exact Bd|].
      set (dfn := denote_f cs (mksig true k m) (FRec e0 e1)).
      change (callf (mksig true k m) dfn (S n') vs M)
        with (appn k m (absn k m (fun env s => denote_e cs (S n') n' (fun args => appn k m (dfn n') args s) env s e1)) vs M).
      rewrite appn_absn by auto. simpl kbody.
      eapply K_if; [simpl; eauto | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
      eapply K_op; [simpl; eauto | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      assert (EQ : denote_e cs (S n') n' (fun args => appn k m (dfn n') args (if m then M else dummy_mem)) (rev vs)
                     (if m then M else dummy_mem) e1
                   = denote_e cs (S n') n' (fun args => appn k m (dfn n') args M) (rev vs) M e1).
      { destruct m; [reflexivity|].
        rewrite (proj1 denote_rec_ext e1 cs (S n') n' _ (fun args => appn k false (dfn n') args M)) by (intro; apply appn_false).
        eapply (proj1 denote_nomem); eauto. }
      rewrite EQ.
      refine (ctail_ok P _ gidf (gidf j) mv M cs true true true m k (fun args => appn k m (dfn n') args M) (S n') n'
                       _ Hcs _ _ Hf _ _ _ _ _ W1 _).
      * intros _ vs' L'. apply (IH vs' M L'). lia.
      * intros _. lia.
      * intros _. lia.
      * split; [|split; [|split; [|split]]].
        -- eapply env_ok_agree; [exact E | exact Lmv | apply agree_set; apply Pos.le_refl].
        -- eapply lt_all_mono; eauto. lia.
        -- lia.
        -- intros _. rewrite PTree.gso by (intro Hx; rewrite Hx in Mvgt; lia). apply R1; reflexivity.
        -- intros _. apply PTree.gss.
  - (* plain *)
    intros n vs M L B.
    destruct (bind_params c k n vs L) as (rho0 & Bd & R1 & E).
    exists (compile_f gidf j (mksig c k m) (FPlain e)), rho0. split; [exact Hf|]. split; [exact Bd|].
    assert (V : callf (mksig c k m) (denote_f cs (mksig c k m) (FPlain e)) n vs M
                = denote_e cs (if c then n else 0) 0 (fun _ => 0%uint63) (rev vs) M e).
    { destruct c.
      - change (callf (mksig true k m) (denote_f cs (mksig true k m) (FPlain e)) n vs M)
          with (appn k m (absn k m (fun env s => denote_e cs n 0 (fun _ => 0%uint63) env s e)) vs M).
        rewrite appn_absn by auto. destruct m; [reflexivity|]. eapply (proj1 denote_nomem); eauto.
      - change (callf (mksig false k m) (denote_f cs (mksig false k m) (FPlain e)) n vs M)
          with (appn k m (absn k m (fun env s => denote_e cs 0 0 (fun _ => 0%uint63) env s e)) vs M).
        rewrite appn_absn by auto. destruct m; [reflexivity|]. eapply (proj1 denote_nomem); eauto. }
    rewrite V. simpl kbody.
    refine (ctail_ok P _ gidf (gidf j) mv M cs false c false m k (fun _ => 0%uint63) (if c then n else 0) 0
                     _ Hcs _ _ Hf _ _ _ _ _ W _).
    + intros Habs; discriminate Habs.
    + intros Hc. subst c. exact B.
    + intros Habs; discriminate Habs.
    + split; [|split; [|split; [|split]]].
      * exact E.
      * eapply lt_all_mono; eauto. lia.
      * lia.
      * intros Hc. subst c. apply R1; reflexivity.
      * intros Habs; discriminate Habs.
Qed.


(* ================================================================ the measurement: the per-program check, end to end *)
Local Open Scope uint63_scope.

(* the KQL name of the program's function i: 1000 + i *)
Definition gid1 (i : nat) : ident := Pos.of_succ_nat (999 + i).

(* a counted loop, as a user writes it *)
Fixpoint sum (n : nat) (i acc : i63) (s : mem) : i63 :=
  match n with
  | O => acc
  | S m => sum m (PrimInt63.add i 1) (PrimInt63.add acc (KQ.KQRun.rd 0 i s)) s
  end.

(* its syntax: the numbers nearest first -- acc is SVar 0, i is SVar 1 *)
Definition sum_g := mksig true 2 true.
Definition sum_s0 := SVar 0.
Definition sum_s1 := SRec (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SOp Badd (SVar 0) (SRd (SInt 0) (SVar 1))) SNil)).
Definition sum_b := FRec sum_s0 sum_s1.

(* the per-program check: the kernel compares the user's function with the meaning of its syntax *)
Time Lemma sum_is : sum = denote_f [] sum_g sum_b.
Proof. Time exact eq_refl. Time Qed.

(* end to end: the KQL function is [compile_f] of the syntax; its statement is [compile_f_ok] and the kernel's computation *)
Definition sum_P := mkprog [(gid1 0, compile_f gid1 0 sum_g sum_b)] [].
Time Lemma sum_ok : callee_ok sum_P (gid1 0) sum_g sum.
Proof. Time exact (compile_f_ok sum_P [] gid1 0 sum_g sum_b eq_refl eq_refl (no_callees sum_P gid1)). Time Qed.

(* a wrong syntax (1 replaced by 2) is refused *)
Time Fail Definition sum_wrong : sum = denote_f [] sum_g (FRec sum_s0 (SRec (SCons (SOp Badd (SVar 1) (SInt 2)) (SCons (SOp Badd (SVar 0) (SRd (SInt 0) (SVar 1))) SNil)))) := eq_refl.

(* calls: a helper without memory, and a loop calling it; the helper's theorem is the callee assumption of the loop's *)
Definition h (a b : i63) : i63 := PrimInt63.add (PrimInt63.mul a 2) b.
Definition h_g := mksig false 2 false.
Definition h_b := FPlain (SOp Badd (SOp Bmul (SVar 1) (SInt 2)) (SVar 0)).
Fixpoint loop (n : nat) (i acc : i63) (s : mem) : i63 :=
  match n with O => acc | S m => loop m (PrimInt63.add i 1) (h acc (KQ.KQRun.rd 0 i s)) s end.
Definition loop_g := mksig true 2 true.
Definition loop_b := FRec (SVar 0) (SRec (SCons (SOp Badd (SVar 1) (SInt 1))
                                  (SCons (SCall 0 NNone (SCons (SVar 0) (SCons (SRd (SInt 0) (SVar 1)) SNil))) SNil))).
Definition hl_P := mkprog [(gid1 0, compile_f gid1 0 h_g h_b); (gid1 1, compile_f gid1 1 loop_g loop_b)] [].
Time Lemma h_ok : callee_ok hl_P (gid1 0) h_g h.
Proof. Time exact (compile_f_ok hl_P [] gid1 0 h_g h_b eq_refl eq_refl (no_callees hl_P gid1)). Time Qed.
Time Lemma loop_ok : callee_ok hl_P (gid1 1) loop_g loop.
Proof.
  refine (compile_f_ok hl_P [existT ftype h_g h] gid1 1 loop_g loop_b eq_refl eq_refl _).
  intros [|[|f]]; simpl; [exact h_ok | exact Logic.I | exact Logic.I].
Time Qed.

(* a loop whose body is 300 lets, each with a read of the memory *)
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
Definition long_g := mksig true 1 true.
Definition long_b := FRec (SVar 0) long_s1.
Time Lemma long_is : long = denote_f [] long_g long_b.
Proof. Time exact eq_refl. Time Qed.
Definition long_P := mkprog [(gid1 0, compile_f gid1 0 long_g long_b)] [].
Time Lemma long_ok : callee_ok long_P (gid1 0) long_g long.
Proof. Time exact (compile_f_ok long_P [] gid1 0 long_g long_b eq_refl eq_refl (no_callees long_P gid1)). Time Qed.
