(** Rocq-C-solution.md §12.V, step 143: a function giving back a counter, as a syntax of its own; its row -- the function made a
    number -- made from that syntax by a function over S; that the row means the function made a number ([ofn] of it), proved once,
    so that a program's row is checked by conversion as a function is, with no tactic *)
From Stdlib Require Import List Uint63 ZArith Lia Bool.
From KQC Require Import KQL KQLAuto KQR.
From KQC Require KQRWf.
Import ListNotations.

Section K.
Context {RTs : RecTypes} {RLs : @RecLaws RTs}.

(** the counter given back: the function itself on its counter's predecessor and these, a counter of S, and arithmetic of them that
    is the same modulo a word (the operations of [row_ke]) *)
Inductive kexp : Type :=
| KRecC (cs : scnts) (args : sexps)
| KCnt (c : scnt)
| KSucc (a : kexp)
| KPlus (a b : kexp)
| KMulK (l : bool) (k : nat) (a : kexp)     (* k * a, k first if l *)
| KBitK (o : nbop) (a b : kexp).            (* land, lor, lxor *)

(** a counter function's body: the counter given back, at the end of the lets, tests and counter matches of S's sorts *)
Inductive sbk : Type :=
| KRet (a : kexp)
| KLet (e : sexp) (k : sbk)
| KLetB (b : sbool) (k : sbk)
| KLetC (c : scnt) (k : sbk)
| KIf (c : cmpop) (x y : sexp) (t f : sbk)
| KIfB (b : sbool) (t f : sbk)
| KMatch (c : nat) (k0 k1 : sbk).

(** the meaning: [reck] the function itself; inside S's numbers, the function itself is that made a number *)
Definition krec (reck : list nat -> list val -> mem -> nat) : list nat -> list val -> mem -> i63 :=
  fun cvs args s => ofn (reck cvs args s).

Fixpoint denote_ke (cs : list callee) (reck : list nat -> list val -> mem -> nat)
  (cenv : list nat) (benv : list bool) (renv : list val) (env : list i63) (s : mem) (a : kexp) {struct a} : nat :=
  match a with
  | KRecC ccs args => reck (denote_cs cs (krec reck) cenv benv renv env s ccs) (denote_es cs (krec reck) cenv benv renv env s args) s
  | KCnt c => denote_c cs (krec reck) cenv benv renv env s c
  | KSucc a => S (denote_ke cs reck cenv benv renv env s a)
  | KPlus a b => (denote_ke cs reck cenv benv renv env s a + denote_ke cs reck cenv benv renv env s b)%nat
  | KMulK l k a => if l then Nat.mul k (denote_ke cs reck cenv benv renv env s a) else Nat.mul (denote_ke cs reck cenv benv renv env s a) k
  | KBitK o a b => nbop_nat o (denote_ke cs reck cenv benv renv env s a) (denote_ke cs reck cenv benv renv env s b)
  end.

Fixpoint denote_kb (cs : list callee) (reck : list nat -> list val -> mem -> nat)
  (cenv : list nat) (benv : list bool) (renv : list val) (env : list i63) (s : mem) (k : sbk) {struct k} : nat :=
  match k with
  | KRet a => denote_ke cs reck cenv benv renv env s a
  | KLet e k => let v := denote_e cs (krec reck) cenv benv renv env s e in denote_kb cs reck cenv benv renv (v :: env) s k
  | KLetB b k => let v := denote_b cs (krec reck) cenv benv renv env s b in denote_kb cs reck cenv (v :: benv) renv env s k
  | KLetC c k => let w := denote_c cs (krec reck) cenv benv renv env s c in denote_kb cs reck (w :: cenv) benv renv env s k
  | KIf c x y t f => if cmp_sem c (denote_e cs (krec reck) cenv benv renv env s x) (denote_e cs (krec reck) cenv benv renv env s y)
                     then denote_kb cs reck cenv benv renv env s t else denote_kb cs reck cenv benv renv env s f
  | KIfB b t f => if denote_b cs (krec reck) cenv benv renv env s b then denote_kb cs reck cenv benv renv env s t
                  else denote_kb cs reck cenv benv renv env s f
  | KMatch c k0 k1 => match nth c cenv O with O => denote_kb cs reck cenv benv renv env s k0
                                            | S p => denote_kb cs reck (p :: cenv) benv renv env s k1 end
  end.

Definition kzero : list nat -> list val -> mem -> nat := fun _ _ _ => O.

(** a function giving back a counter, recursive on its first counter ([b0] at 0, [b1] otherwise), as S's functions of numbers *)
Definition denote_kf (cs : list callee) (x : nat) (k : list kind) (m : bool) (b0 b1 : sbk) : ctype (S x) (ntypeT k m nat) :=
  fix go (n : nat) : ctype x (ntypeT k m nat) :=
    absc x _ (fun cenv => absnT k m nat (fun env benv renv s =>
      match n with
      | O => denote_kb cs kzero (cenv ++ [n]) benv renv env s b0
      | S n' => denote_kb cs (fun cvs args s' => appnT k m nat (appc x _ (go n') cvs) args s') (n' :: cenv ++ [n]) benv renv env s b1
      end)).

(** the row: each construct the machine's *)
Definition kop (o : nbop) : option binop := match o with NLand => Some Bland | NLor => Some Blor | NLxor => Some Blxor | _ => None end.
Fixpoint row_ke (a : kexp) : option sexp :=
  match a with
  | KRecC ccs args => Some (SRec ccs args)
  | KCnt c => Some (SOfC c)
  | KSucc a => option_map (fun e => SOp Badd e (SInt 1%uint63)) (row_ke a)
  | KPlus a b => match row_ke a, row_ke b with Some x, Some y => Some (SOp Badd x y) | _, _ => None end
  | KMulK l k a => option_map (fun e => if l then SOp Bmul (SInt (ofn k)) e else SOp Bmul e (SInt (ofn k))) (row_ke a)
  | KBitK o a b => match kop o, row_ke a, row_ke b with Some op, Some x, Some y => Some (SOp op x y) | _, _, _ => None end
  end.
Fixpoint row_kb (k : sbk) : option sexp :=
  match k with
  | KRet a => row_ke a
  | KLet e k => option_map (SLet e) (row_kb k)
  | KLetB b k => option_map (SLetB b) (row_kb k)
  | KLetC c k => option_map (SLetC c) (row_kb k)
  | KIf c x y t f => match row_kb t, row_kb f with Some t', Some f' => Some (SIf c x y t' f') | _, _ => None end
  | KIfB b t f => match row_kb t, row_kb f with Some t', Some f' => Some (SIfB b t' f') | _, _ => None end
  | KMatch c k0 k1 => match row_kb k0, row_kb k1 with Some e0, Some e1 => Some (SMatch c e0 e1) | _, _ => None end
  end.

(** what the machine's operations are of numbers made of counters: Rocq's axioms of them alone (KQRWf) *)
Lemma ofn_add_k : forall a b, binop_sem Badd (ofn a) (ofn b) = ofn (a + b).
Proof. intros a b. unfold ofn. rewrite KQRWf.nr_add. reflexivity. Qed.
Lemma ofn_succ_k : forall a, binop_sem Badd (ofn a) 1%uint63 = ofn (S a).
Proof. intros a. unfold ofn. rewrite KQRWf.nr_S. reflexivity. Qed.
Lemma ofn_mul_k : forall a b, binop_sem Bmul (ofn a) (ofn b) = ofn (a * b).
Proof. intros a b. unfold ofn. rewrite KQRWf.nr_mul. reflexivity. Qed.
Lemma ofn_bit_k : forall o op a b, kop o = Some op -> binop_sem op (ofn a) (ofn b) = ofn (nbop_nat o a b).
Proof.
  intros [| | | | |] op a b E; cbn [kop] in E; try discriminate E; injection E as <-; unfold ofn; cbn [nbop_nat binop_sem].
  - rewrite KQRWf.nr_land. reflexivity.
  - rewrite KQRWf.nr_lor. reflexivity.
  - rewrite KQRWf.nr_lxor. reflexivity.
Qed.

(** the row's body means the counter's made a number, where its own call does: [rec] the row's, [reck] the function's *)
Section Body.
Variable cs : list callee.
Variables (nx : nat) (kk : list kind).
Variable rec : list nat -> list val -> mem -> i63.
Variable reck : list nat -> list val -> mem -> nat.
Hypothesis Hr : forall cvs l s', length cvs = nx -> map kind_of l = kk -> rec cvs l s' = krec reck cvs l s'.
Let ext := @denote_rec_ext RTs RLs.

Lemma row_ke_ok : forall a e sigs r mok rk cenv benv renv env s, row_ke a = Some e -> wf sigs r mok nx kk rk e = true ->
  fst sigs = map (@projT1 _ _) cs -> rtyped renv rk ->
  denote_e cs rec cenv benv renv env s e = ofn (denote_ke cs reck cenv benv renv env s a).
Proof.
  induction a as [ccs args | c | a IH | a IHa b IHb | l n a IH | o a IHa b IHb];
    intros e sigs r mok rk cenv benv renv env s E W Hs T; cbn [row_ke] in E.
  - injection E as <-. cbn [denote_e denote_ke]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0. cbn [wf] in W.
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W _].
    apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [_ Wn]. apply Nat.eqb_eq in Wn. apply kinds_eqb_eq in Wk.
    rewrite (proj1 (proj2 (proj2 (proj2 ext))) ccs cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wc T).
    rewrite (proj1 (proj2 ext) args cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Ws T).
    apply Hr; [rewrite len_denote_cs; exact Wn | erewrite kinds_denote_es by eassumption; exact Wk].
  - injection E as <-. cbn [denote_e denote_ke]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0. cbn [wf] in W.
    apply andb_true_iff in W as [_ Wc].
    rewrite (proj1 (proj2 (proj2 ext)) c cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wc T). reflexivity.
  - destruct (row_ke a) as [e1|] eqn:E1; cbn in E; [|discriminate E]. injection E as <-. cbn [wf] in W.
    apply andb_true_iff in W as [W1 _]. cbn [denote_e denote_ke].
    rewrite (IH e1 sigs r mok rk cenv benv renv env s eq_refl W1 Hs T). apply ofn_succ_k.
  - destruct (row_ke a) as [x|] eqn:Ea; [|discriminate E]. destruct (row_ke b) as [y|] eqn:Eb; [|discriminate E].
    injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [Wa Wb]. cbn [denote_e denote_ke].
    rewrite (IHa x sigs r mok rk cenv benv renv env s eq_refl Wa Hs T), (IHb y sigs r mok rk cenv benv renv env s eq_refl Wb Hs T).
    apply ofn_add_k.
  - destruct (row_ke a) as [e1|] eqn:E1; cbn in E; [|discriminate E]. injection E as <-. cbn [denote_ke].
    destruct l; cbn [wf] in W; cbn [denote_e].
    + apply andb_true_iff in W as [_ W1]. rewrite (IH e1 sigs r mok rk cenv benv renv env s eq_refl W1 Hs T). apply ofn_mul_k.
    + apply andb_true_iff in W as [W1 _]. rewrite (IH e1 sigs r mok rk cenv benv renv env s eq_refl W1 Hs T). apply ofn_mul_k.
  - destruct (kop o) as [op|] eqn:Eo; [|discriminate E]. destruct (row_ke a) as [x|] eqn:Ea; [|discriminate E].
    destruct (row_ke b) as [y|] eqn:Eb; [|discriminate E]. injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [Wa Wb].
    cbn [denote_e denote_ke].
    rewrite (IHa x sigs r mok rk cenv benv renv env s eq_refl Wa Hs T), (IHb y sigs r mok rk cenv benv renv env s eq_refl Wb Hs T).
    apply ofn_bit_k; exact Eo.
Qed.

Lemma row_kb_ok : forall k e sigs r mok rk cenv benv renv env s, row_kb k = Some e -> wf sigs r mok nx kk rk e = true ->
  fst sigs = map (@projT1 _ _) cs -> rtyped renv rk ->
  denote_e cs rec cenv benv renv env s e = ofn (denote_kb cs reck cenv benv renv env s k).
Proof.
  induction k as [a | e1 k IH | b k IH | c k IH | o x y t IHt f IHf | b t IHt f IHf | c k0 IH0 k1 IH1];
    intros e sigs r mok rk cenv benv renv env s E W Hs T; cbn [row_kb] in E.
  - cbn [denote_kb]. exact (row_ke_ok a e sigs r mok rk cenv benv renv env s E W Hs T).
  - destruct (row_kb k) as [e2|] eqn:E2; cbn in E; [|discriminate E]. injection E as <-. cbn [wf] in W.
    apply andb_true_iff in W as [W1 W2]. cbn [denote_e denote_kb]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0.
    rewrite (proj1 ext e1 cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr W1 T).
    exact (IH e2 _ r mok rk cenv benv renv _ s eq_refl W2 eq_refl T).
  - destruct (row_kb k) as [e2|] eqn:E2; cbn in E; [|discriminate E]. injection E as <-. cbn [wf] in W.
    apply andb_true_iff in W as [W1 W2]. cbn [denote_e denote_kb]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0.
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 ext)))) b cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr W1 T).
    exact (IH e2 _ r mok rk cenv _ renv env s eq_refl W2 eq_refl T).
  - destruct (row_kb k) as [e2|] eqn:E2; cbn in E; [|discriminate E]. injection E as <-. cbn [wf] in W.
    apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [W1 _]. cbn [denote_e denote_kb]. destruct sigs as [s0 cb0].
    cbn [fst] in Hs. subst s0.
    rewrite (proj1 (proj2 (proj2 ext)) c cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr W1 T).
    exact (IH e2 _ r mok rk _ benv renv env s eq_refl W2 eq_refl T).
  - destruct (row_kb t) as [t'|] eqn:Et; [|discriminate E]. destruct (row_kb f) as [f'|] eqn:Ef; [|discriminate E].
    injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt].
    apply andb_true_iff in W as [Wx Wy]. cbn [denote_e denote_kb]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0.
    rewrite (proj1 ext x cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wx T).
    rewrite (proj1 ext y cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wy T).
    destruct (cmp_sem o _ _); [exact (IHt t' _ r mok rk cenv benv renv env s eq_refl Wt eq_refl T)
                              | exact (IHf f' _ r mok rk cenv benv renv env s eq_refl Wf eq_refl T)].
  - destruct (row_kb t) as [t'|] eqn:Et; [|discriminate E]. destruct (row_kb f) as [f'|] eqn:Ef; [|discriminate E].
    injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wb Wt].
    cbn [denote_e denote_kb]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0.
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 ext)))) b cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wb T).
    destruct (denote_b _ _ _ _ _ _ _ b); [exact (IHt t' _ r mok rk cenv benv renv env s eq_refl Wt eq_refl T)
                                          | exact (IHf f' _ r mok rk cenv benv renv env s eq_refl Wf eq_refl T)].
  - destruct (row_kb k0) as [e0|] eqn:E0; [|discriminate E]. destruct (row_kb k1) as [e1|] eqn:E1; [|discriminate E].
    injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [W0 W1]. cbn [denote_e denote_kb].
    destruct (nth c cenv O); [exact (IH0 e0 sigs r mok rk cenv benv renv env s eq_refl W0 Hs T)
                             | exact (IH1 e1 _ r mok rk _ benv renv env s eq_refl W1 Hs T)].
Qed.
End Body.

(** the counter function made a number at its results *)
Fixpoint nmapT (ks : list kind) (m : bool) (A B : Type) (f : A -> B) {struct ks} : ntypeT ks m A -> ntypeT ks m B :=
  match ks as k0 return ntypeT k0 m A -> ntypeT k0 m B with
  | [] => if m as m0 return ntypeT [] m0 A -> ntypeT [] m0 B then (fun g s => f (g s)) else (fun g => f g)
  | KNum :: ks => fun g x => nmapT ks m A B f (g x)
  | KBool :: ks => fun g x => nmapT ks m A B f (g x)
  | KRec ri :: ks => fun g x => nmapT ks m A B f (g x)
  end.
Lemma appnT_nmapT : forall ks m A B (f : A -> B) h vs s, appnT ks m B (nmapT ks m A B f h) vs s = f (appnT ks m A h vs s).
Proof.
  induction ks as [|[| |ri] ks IH]; intros m A B f h vs s; cbn [nmapT appnT].
  - destruct m; reflexivity.
  - destruct vs as [|[x|b|ri x] vs]; apply IH.
  - destruct vs as [|[x|b|ri x] vs]; apply IH.
  - destruct vs as [|v vs]; apply IH.
Qed.
Lemma appc_cmapT : forall x A B (f : A -> B) h l, appc x B (cmapT x A B f h) l = f (appc x A h l).
Proof. induction x as [|x IH]; intros A B f h l; [reflexivity | destruct l as [|c l]; cbn [cmapT appc]; apply IH]. Qed.

(** no record among the parameters (step 143): the records' kinds of the meaning's lists none *)
Definition norecs (ks : list kind) : bool := forallb (fun kd => match kd with KRec _ => false | _ => true end) ks.

Lemma eqN_absn : forall ks m (F : list i63 -> list bool -> list val -> mem -> i63) (G : list i63 -> list bool -> list val -> mem -> nat),
  norecs ks = true -> (forall env benv s, F env benv [] s = ofn (G env benv [] s)) ->
  eqN ks m _ (absnT ks m i63 F) (nmapT ks m nat i63 ofn (absnT ks m nat G)).
Proof.
  induction ks as [|[| |ri] ks IH]; intros m F G N HFG; cbn [norecs forallb] in N.
  - destruct m; cbn [absnT nmapT eqN]; [intros s; apply HFG | apply HFG].
  - cbn [absnT nmapT eqN]. intros a. apply IH; [exact N | intros env benv s; apply HFG].
  - cbn [absnT nmapT eqN]. intros a. apply IH; [exact N | intros env benv s; apply HFG].
  - discriminate N.
Qed.
Lemma eqC_absc : forall x ks m (F : list nat -> ntypeT ks m i63) (G : list nat -> ntypeT ks m nat),
  (forall l, eqN ks m _ (F l) (nmapT ks m nat i63 ofn (G l))) ->
  eqC x _ (eqN ks m _) (absc x _ F) (cmapT x _ _ (nmapT ks m nat i63 ofn) (absc x _ G)).
Proof.
  induction x as [|x IH]; intros ks m F G H; cbn [absc cmapT eqC]; [apply H | intros c; apply IH; intros l; apply H].
Qed.
Lemma kq_step : forall x ks m (h : ctype x (ntypeT ks m i63)) (g : ctype x (ntypeT ks m nat)) cvs l s,
  eqC x _ (eqN ks m _) h (cmapT x _ _ (nmapT ks m nat i63 ofn) g) -> appnT ks m i63 (appc x _ h cvs) l s = ofn (appnT ks m nat (appc x _ g cvs) l s).
Proof.
  intros x ks m h g cvs l s H. rewrite (appnT_eqN ks m _ _ _ l s (appc_eqC x _ (eqN ks m _) _ _ cvs H)), appc_cmapT, appnT_nmapT. reflexivity.
Qed.
Lemma rk0_norecs : forall ks, norecs ks = true -> rk0 ks = [].
Proof.
  intros ks N. unfold rk0. induction ks as [|[| |ri] ks IH]; cbn [norecs forallb] in N; try discriminate N; [reflexivity | |];
    cbn [flat_map app]; apply IH; exact N.
Qed.

(** a row made by [row_kb] means the counter function made a number, at every counter and argument *)
Theorem row_of_ok : forall cs x k m w bo vw b0 b1 e0 e1, row_kb b0 = Some e0 -> row_kb b1 = Some e1 -> norecs k = true ->
  wf_f (map (@projT1 _ _) cs) (mksig9 (S x) k m false w None bo vw false) (FRec e0 e1) = true ->
  eqC (S x) _ (eqN k m _) (denote_f cs (mksig9 (S x) k m false w None bo vw false) (FRec e0 e1))
                          (cmapT (S x) _ _ (nmapT k m nat i63 ofn) (denote_kf cs x k m b0 b1)).
Proof.
  intros cs x k m w bo vw b0 b1 e0 e1 E0 E1 N W.
  unfold wf_f in W. cbn [sb sv sq sn sr sw sm sk] in W.
  apply andb_true_iff in W as [_ W]. apply andb_true_iff in W as [W W1]. apply andb_true_iff in W as [_ W0].
  pose proof (rk0_norecs k N) as R0. rewrite R0 in W0, W1.
  assert (T : rtyped [] []) by reflexivity.
  cbn [denote_f denote_f0 denote_kf eqC cmapT]. intros n. induction n as [|n IH]; cbn beta iota.
  - apply eqC_absc. intros l. apply eqN_absn; [exact N|]. intros env benv s.
    apply (row_kb_ok cs x k dnum kzero (fun _ _ _ _ _ => eq_refl) b0 e0 (wctx (map (@projT1 _ _) cs) (mksig9 (S x) k m false w None bo vw false) false)
             false m [] (l ++ [O]) benv [] env s E0 W0 eq_refl T).
  - apply eqC_absc. intros l. apply eqN_absn; [exact N|]. intros env benv s.
    refine (row_kb_ok cs x k _ _ _ b1 e1 (wctx (map (@projT1 _ _) cs) (mksig9 (S x) k m false w None bo vw false) true)
             true m [] (n :: l ++ [S n]) benv [] env s E1 W1 eq_refl T).
    intros cvs l' s' _ _. unfold krec. exact (kq_step x k m _ _ cvs l' s' IH).
Qed.


(** the counter body of a row [row_kb] made, read back from the row (so that a program's proof needs only the row's syntax tree):
    [row_kb] of it is the row again, which the proof checks by computation *)
Fixpoint unrow_ke (e : sexp) : option kexp :=
  match e with
  | SRec ccs args => Some (KRecC ccs args)
  | SOfC c => Some (KCnt c)
  | SOp Badd a (SInt i) => if PrimInt63.eqb i 1%uint63 then option_map KSucc (unrow_ke a) else None
  | SOp Badd a b => match unrow_ke a, unrow_ke b with Some x, Some y => Some (KPlus x y) | _, _ => None end
  | SOp Bmul (SInt n) a => option_map (KMulK true (Z.to_nat (Uint63.to_Z n))) (unrow_ke a)
  | SOp Bmul a (SInt n) => option_map (KMulK false (Z.to_nat (Uint63.to_Z n))) (unrow_ke a)
  | SOp Bland a b => match unrow_ke a, unrow_ke b with Some x, Some y => Some (KBitK NLand x y) | _, _ => None end
  | SOp Blor a b => match unrow_ke a, unrow_ke b with Some x, Some y => Some (KBitK NLor x y) | _, _ => None end
  | SOp Blxor a b => match unrow_ke a, unrow_ke b with Some x, Some y => Some (KBitK NLxor x y) | _, _ => None end
  | _ => None
  end.
Fixpoint unrow_kb (e : sexp) : option sbk :=
  match e with
  | SLet e1 e2 => option_map (KLet e1) (unrow_kb e2)
  | SLetB b e2 => option_map (KLetB b) (unrow_kb e2)
  | SLetC c e2 => option_map (KLetC c) (unrow_kb e2)
  | SIf c x y t f => match unrow_kb t, unrow_kb f with Some t', Some f' => Some (KIf c x y t' f') | _, _ => None end
  | SIfB b t f => match unrow_kb t, unrow_kb f with Some t', Some f' => Some (KIfB b t' f') | _, _ => None end
  | SMatch c e0 e1 => match unrow_kb e0, unrow_kb e1 with Some k0, Some k1 => Some (KMatch c k0 k1) | _, _ => None end
  | _ => option_map KRet (unrow_ke e)
  end.
Definition kdflt : sbk := KRet (KCnt CO).
Definition unrow_kb0 (b : fbody) : sbk := match b with FRec e0 _ => match unrow_kb e0 with Some k => k | None => kdflt end | _ => kdflt end.
Definition unrow_kb1 (b : fbody) : sbk := match b with FRec _ e1 => match unrow_kb e1 with Some k => k | None => kdflt end | _ => kdflt end.
End K.

(** a program's row of a counter function: the function made a number at its results; its statement [C .. = ofn (cnt ..)] holds by
    conversion.  Its parameters hold no record (the rows made so), so its type is the same at every program's record types *)
Definition krow (x : nat) (k : list kind) (m : bool) (f : ctype (S x) (@ntypeT no_recs k m nat)) : ctype (S x) (@ntypeT no_recs k m i63) :=
  cmapT (S x) _ _ (@nmapT no_recs k m nat i63 ofn) f.
