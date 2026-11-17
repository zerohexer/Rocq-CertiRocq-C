(** Rocq-C-solution.md §12.V, step 143: a function giving back a counter, as a syntax of its own; its row -- the function made a
    number -- made from that syntax by a function over S; that the row means the function made a number ([ofn] of it), proved once,
    so that a program's row is checked by conversion as a function is, with no tactic *)
From Stdlib Require Import List Uint63 ZArith Lia Bool.
From KQC Require Import KQL KQLAuto KQR.
From KQC Require KQRWf.
Import ListNotations.

Section K.
Context {RTs : RecTypes} {KFs : @KFuns RTs} {RLs : @RecLaws RTs}.

(** the counter given back: the function itself on its counter's predecessor and these, a counter of S, and arithmetic of them that
    is the same modulo a word (the operations of [row_ke]) *)
Inductive kexp : Type :=
| KRecC (cs : scnts) (args : sexps)
| KCnt (c : scnt)
| KSucc (a : kexp)
| KPlus (a b : kexp)
| KMulK (l : bool) (k : nat) (a : kexp)     (* k * a, k first if l *)
| KBitK (o : nbop) (a b : kexp).            (* land, lor, lxor, ldiff (step 144) *)

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
  | KBitK NLdiff a b =>
      (* (step 144) the first's bits not in the second: the first and the second's complement within the 63 bits *)
      match row_ke a, row_ke b with Some x, Some y => Some (SOp Bland x (SOp Blxor y (SInt 9223372036854775807%uint63))) | _, _ => None end
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
Let ext := @denote_rec_ext RTs KFs RLs.

Lemma row_ke_ok : forall a e sigs r mok rk cenv benv renv env s, row_ke a = Some e -> wf sigs r mok nx kk rk e = true ->
  fst sigs = map (@projT1 _ _) cs -> rtyped renv rk ->
  denote_e cs rec cenv benv renv env s e = ofn (denote_ke cs reck cenv benv renv env s a).
Proof.
  induction a as [ccs args | c | a IH | a IHa b IHb | l n a IH | o a IHa b IHb];
    intros e sigs r mok rk cenv benv renv env s E W Hs T; cbn [row_ke] in E.
  - injection E as <-. simpl denote_e; cbn [denote_ke]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0. cbn [wf] in W.
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W _].
    apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [_ Wn]. apply Nat.eqb_eq in Wn. apply kinds_eqb_eq in Wk.
    rewrite (proj1 (proj2 (proj2 (proj2 ext))) ccs cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wc T).
    rewrite (proj1 (proj2 ext) args cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Ws T).
    apply Hr; [rewrite len_denote_cs; exact Wn | erewrite kinds_denote_es by eassumption; exact Wk].
  - injection E as <-. simpl denote_e; cbn [denote_ke]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0. cbn [wf] in W.
    apply andb_true_iff in W as [_ Wc].
    rewrite (proj1 (proj2 (proj2 ext)) c cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wc T). reflexivity.
  - destruct (row_ke a) as [e1|] eqn:E1; cbn in E; [|discriminate E]. injection E as <-. cbn [wf] in W.
    apply andb_true_iff in W as [W1 _]. simpl denote_e; cbn [denote_ke].
    rewrite (IH e1 sigs r mok rk cenv benv renv env s eq_refl W1 Hs T). apply ofn_succ_k.
  - destruct (row_ke a) as [x|] eqn:Ea; [|discriminate E]. destruct (row_ke b) as [y|] eqn:Eb; [|discriminate E].
    injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [Wa Wb]. simpl denote_e; cbn [denote_ke].
    rewrite (IHa x sigs r mok rk cenv benv renv env s eq_refl Wa Hs T), (IHb y sigs r mok rk cenv benv renv env s eq_refl Wb Hs T).
    apply ofn_add_k.
  - destruct (row_ke a) as [e1|] eqn:E1; cbn in E; [|discriminate E]. injection E as <-. cbn [denote_ke].
    destruct l; cbn [wf] in W; cbn [denote_e].
    + apply andb_true_iff in W as [_ W1]. rewrite (IH e1 sigs r mok rk cenv benv renv env s eq_refl W1 Hs T). apply ofn_mul_k.
    + apply andb_true_iff in W as [W1 _]. rewrite (IH e1 sigs r mok rk cenv benv renv env s eq_refl W1 Hs T). apply ofn_mul_k.
  - destruct o.
    4:{ destruct (row_ke a) as [x|] eqn:Ea; [|discriminate E]. destruct (row_ke b) as [y|] eqn:Eb; [|discriminate E].
        cbn in E. injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [Wa Wb]. apply andb_true_iff in Wb as [Wb _].
        simpl denote_e; cbn [denote_ke].
        rewrite (IHa x sigs r mok rk cenv benv renv env s eq_refl Wa Hs T), (IHb y sigs r mok rk cenv benv renv env s eq_refl Wb Hs T).
        unfold ofn. cbn [nbop_nat]. rewrite KQRWf.nr_ldiff. reflexivity. }
    all: destruct (kop _) as [op|] eqn:Eo; [|discriminate E]; destruct (row_ke a) as [x|] eqn:Ea; [|discriminate E];
      destruct (row_ke b) as [y|] eqn:Eb; [|discriminate E]; injection E as <-; cbn [wf] in W; apply andb_true_iff in W as [Wa Wb];
      simpl denote_e; cbn [denote_ke];
      rewrite (IHa x sigs r mok rk cenv benv renv env s eq_refl Wa Hs T), (IHb y sigs r mok rk cenv benv renv env s eq_refl Wb Hs T);
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
    apply andb_true_iff in W as [W1 W2]. simpl denote_e; cbn [denote_kb]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0.
    rewrite (proj1 ext e1 cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr W1 T).
    exact (IH e2 _ r mok rk cenv benv renv _ s eq_refl W2 eq_refl T).
  - destruct (row_kb k) as [e2|] eqn:E2; cbn in E; [|discriminate E]. injection E as <-. cbn [wf] in W.
    apply andb_true_iff in W as [W1 W2]. simpl denote_e; cbn [denote_kb]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0.
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 ext)))) b cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr W1 T).
    exact (IH e2 _ r mok rk cenv _ renv env s eq_refl W2 eq_refl T).
  - destruct (row_kb k) as [e2|] eqn:E2; cbn in E; [|discriminate E]. injection E as <-. cbn [wf] in W.
    apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [W1 _]. simpl denote_e; cbn [denote_kb]. destruct sigs as [s0 cb0].
    cbn [fst] in Hs. subst s0.
    rewrite (proj1 (proj2 (proj2 ext)) c cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr W1 T).
    exact (IH e2 _ r mok rk _ benv renv env s eq_refl W2 eq_refl T).
  - destruct (row_kb t) as [t'|] eqn:Et; [|discriminate E]. destruct (row_kb f) as [f'|] eqn:Ef; [|discriminate E].
    injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt].
    apply andb_true_iff in W as [Wx Wy]. simpl denote_e; cbn [denote_kb]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0.
    rewrite (proj1 ext x cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wx T).
    rewrite (proj1 ext y cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wy T).
    destruct (cmp_sem o _ _); [exact (IHt t' _ r mok rk cenv benv renv env s eq_refl Wt eq_refl T)
                              | exact (IHf f' _ r mok rk cenv benv renv env s eq_refl Wf eq_refl T)].
  - destruct (row_kb t) as [t'|] eqn:Et; [|discriminate E]. destruct (row_kb f) as [f'|] eqn:Ef; [|discriminate E].
    injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wb Wt].
    simpl denote_e; cbn [denote_kb]. destruct sigs as [s0 cb0]. cbn [fst] in Hs. subst s0.
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 ext)))) b cs rec (krec reck) cenv benv renv env s r mok nx kk rk cb0 Hr Wb T).
    destruct (denote_b _ _ _ _ _ _ _ b); [exact (IHt t' _ r mok rk cenv benv renv env s eq_refl Wt eq_refl T)
                                          | exact (IHf f' _ r mok rk cenv benv renv env s eq_refl Wf eq_refl T)].
  - destruct (row_kb k0) as [e0|] eqn:E0; [|discriminate E]. destruct (row_kb k1) as [e1|] eqn:E1; [|discriminate E].
    injection E as <-. cbn [wf] in W. apply andb_true_iff in W as [W0 W1]. simpl denote_e; cbn [denote_kb].
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
  | SOp Bland a (SOp Blxor b (SInt m)) =>
      if PrimInt63.eqb m 9223372036854775807%uint63
      then match unrow_ke a, unrow_ke b with Some x, Some y => Some (KBitK NLdiff x y) | _, _ => None end
      else None
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

(** (step 145) the bound of a function giving back a counter, computed from its syntax by a function and proved once ([kbound],
    [kbound_ok]): at most [W] times its first counter, plus its other counters, plus [C], as step 83's rule reads it off the text
    ([KQRReify.nb_go]).  A round adds at most [W] to the result and to the sum of the counters it hands on; the bounds of the
    counters of S are [clinf]'s.  In place of the proof per program by [KQRWf.nb_step]: a program's bound is checked by conversion *)

(** what [clinf]'s bound needs of the counters in scope, their range left out: the lets' and matches' bounds, then the function's
    counters [pv] *)
Definition cbl (bs : list cbe) (pv cenv : list nat) : Prop :=
  skipn (length bs) cenv = pv /\ (forall i, (i < length bs)%nat -> (Z.of_nat (nth i cenv O) <= leval (snd (nth i bs cbe0)) pv)%Z).
Lemma cbl_cons : forall bs pv cenv o p, cbl bs pv cenv -> (Z.of_nat p <= leval (snd o) pv)%Z -> cbl (o :: bs) pv (p :: cenv).
Proof. intros bs pv cenv o p [C2 C3] L. split; [exact C2|]. intros [|i] Hi; cbn [nth length] in *; [exact L | apply C3; lia]. Qed.
Lemma linat_le : forall bs pv cenv i, cbl bs pv cenv -> (Z.of_nat (nth i cenv O) <= leval (linat bs i) pv)%Z.
Proof.
  intros bs pv cenv i [C2 C3]. unfold linat. destruct (Nat.ltb i (length bs)) eqn:L.
  - apply Nat.ltb_lt in L. apply C3; exact L.
  - apply Nat.ltb_ge in L. rewrite leval_unit. rewrite <- C2. rewrite nth_skipn_nat. replace (length bs + (i - length bs))%nat with i by lia. lia.
Qed.
(** [clinf_bound]'s proof, the range of the counters not used *)
Lemma clinf_le : forall bs pv c cs rec cenv benv renv denv M, cbl bs pv cenv ->
  (Z.of_nat (denote_c cs rec cenv benv renv denv M c) <= leval (clinf bs c) pv)%Z.
Proof.
  intros bs pv c. induction c as [i | | c IH | e | c IH | a IHa b IHb | a IHa b IHb | a IHa b IHb | a IHa b IHb | c IH | l w c IH | e | e | a IHa b IHb | a IHa b IHb | b a IHa d IHb | o a IHa b IHb | w c IH | o fi a IHa b IHb | k | u | l w c IH | a b | fi vs args]; intros cs rec cenv benv renv denv M Cb; simpl denote_c; cbn [clinf].
  - eapply linat_le; eauto.
  - rewrite leval_zero. lia.
  - rewrite leval_shift. specialize (IH cs rec cenv benv renv denv M Cb). lia.
  - pose proof (KQMAuto.kq_nat_le (denote_e cs rec cenv benv renv denv M e)) as K60. change (2 ^ 60)%Z with 1152921504606846976%Z in K60.
    unfold leval. cbn [fst snd evc]. pose proof (cnat_max_bound cs rec cenv benv renv denv M e). lia.
  - specialize (IH cs rec cenv benv renv denv M Cb). pose proof (Nat.le_pred_l (denote_c cs rec cenv benv renv denv M c)). lia.
  - rewrite leval_add. specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb). lia.
  - unfold lmin. specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb).
    destruct (_ && _)%bool; lia.
  - rewrite leval_add. specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb). lia.
  - specialize (IHa cs rec cenv benv renv denv M Cb). lia.
  - specialize (IH cs rec cenv benv renv denv M Cb).
    pose proof (Nat.div2_decr (denote_c cs rec cenv benv renv denv M c) (denote_c cs rec cenv benv renv denv M c) (Nat.le_succ_diag_r _)). lia.
  - rewrite leval_scale. specialize (IH cs rec cenv benv renv denv M Cb). destruct l; rewrite Nat2Z.inj_mul; nia.
  - unfold leval. cbn [fst snd evc]. pose proof (to_nat_s63 (denote_e cs rec cenv benv renv denv M e)). lia.
  - unfold leval. cbn [fst snd evc]. pose proof (to_nat_u63 (denote_e cs rec cenv benv renv denv M e)). lia.
  - rewrite leval_add. specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb).
    pose proof (ndiv_le (denote_c cs rec cenv benv renv denv M a) (denote_c cs rec cenv benv renv denv M b)). lia.
  - rewrite leval_add. specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb).
    pose proof (nmod_le (denote_c cs rec cenv benv renv denv M a) (denote_c cs rec cenv benv renv denv M b)). lia.
  - rewrite leval_add. specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb). destruct (denote_b cs rec cenv benv renv denv M b); lia.
  - rewrite leval_add. specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb).
    pose proof (nbop_le_add o (denote_c cs rec cenv benv renv denv M a) (denote_c cs rec cenv benv renv denv M b)). lia.
  - rewrite leval_scale. specialize (IH cs rec cenv benv renv denv M Cb). rewrite z_shiftl. pose proof (Z.pow_nonneg 2 (Z.of_nat w) ltac:(lia)). nia.
  - rewrite leval_add. specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb).
    pose proof (nlop_le o (denote_c cs rec cenv benv renv denv M a) (denote_c cs rec cenv benv renv denv M b)). lia.
  - unfold leval. cbn [fst snd evc]. lia.
  - unfold leval. cbn [fst snd evc]. rewrite nu_z_ok. lia.
  - rewrite leval_scale. specialize (IH cs rec cenv benv renv denv M Cb). rewrite <- nu_z_ok. destruct l; rewrite Nat2Z.inj_mul; nia.
  - unfold leval. cbn [fst snd evc]. rewrite cpw_ok. lia.
  - rewrite leval_shift, leval_add, leval_scale, leval_fold_linat.
    pose proof (kfn_le_lin fi vs (denote_es cs rec cenv benv renv denv M args) M cenv (fun i => leval (linat bs i) pv) (fun i => linat_le bs pv cenv i Cb)) as K.
    cbv beta in K. lia.
Qed.

(** the sum of counters *)
Definition zsum (l : list nat) : Z := Z.of_nat (fold_right Nat.add O l).
Lemma zsum_cons : forall c l, zsum (c :: l) = (Z.of_nat c + zsum l)%Z.
Proof. intros c l. unfold zsum. cbn [fold_right]. lia. Qed.
Lemma zsum_snoc : forall l c, zsum (l ++ [c]) = (zsum l + Z.of_nat c)%Z.
Proof. induction l as [|a l IH]; intros c; cbn [app]; [unfold zsum; cbn; lia | rewrite !zsum_cons, IH; lia]. Qed.
Lemma zsum_nonneg : forall l, (0 <= zsum l)%Z.
Proof. intros l. unfold zsum. lia. Qed.

(** a value bounded where its function's counters are [pv]: below a linear bound, or (through own calls) below one plus [Q] *)
Definition kbv : Type := (option linf * option linf)%type.
Definition obnd (pv : list nat) (o : option linf) (z : Z) : Prop := match o with Some L => (z <= leval L pv)%Z | None => False end.
Definition kv_ok (pv : list nat) (Q : Z) (v : nat) (a : kbv) : Prop := obnd pv (fst a) (Z.of_nat v) \/ obnd pv (snd a) (Z.of_nat v - Q).
Fixpoint zmx (a b : list Z) : list Z :=
  match a, b with
  | [], _ => map (Z.max 0) b
  | _, [] => map (Z.max 0) a
  | x :: a', y :: b' => Z.max x y :: zmx a' b'
  end.
Definition lmx (a b : linf) : linf := (zmx (fst a) (fst b), Z.max (snd a) (snd b)).
Definition omx (a b : option linf) : option linf :=
  match a, b with Some x, Some y => Some (lmx x y) | Some x, None => Some x | None, y => y end.
Definition oadd (a b : option linf) : option linf := match a, b with Some x, Some y => Some (ladd x y) | _, _ => None end.
Definition kjoin (a b : kbv) : kbv := (omx (fst a) (fst b), omx (snd a) (snd b)).
(** a sum: two own calls in one round are none *)
Definition kplus (a b : kbv) : option kbv :=
  match snd a, snd b with
  | Some _, Some _ => None
  | _, _ => Some (oadd (fst a) (fst b), omx (oadd (snd a) (fst b)) (oadd (fst a) (snd b)))
  end.
Definition kshift (a : kbv) : kbv := (option_map (lshift 1) (fst a), option_map (lshift 1) (snd a)).
Definition klit (a : kexp) : bool := match a with KCnt (CLit _) | KCnt (CNumU _) => true | _ => false end.
Definition lsumc (bs : list cbe) (ccs : scnts) : linf := fold_right (fun c acc => ladd (clinf bs c) acc) lzero (lc ccs).
(** [r]: the own call is the recursion (else, at the counter's 0, the function's 0) *)
Fixpoint ke_abs (r : bool) (bs : list cbe) (a : kexp) {struct a} : option kbv :=
  match a with
  | KRecC ccs _ => Some (if r then (None, Some (lsumc bs ccs)) else (Some lzero, None))
  | KCnt c => Some (Some (clinf bs c), None)
  | KSucc a => option_map kshift (ke_abs r bs a)
  | KPlus a b => match ke_abs r bs a, ke_abs r bs b with Some x, Some y => kplus x y | _, _ => None end
  | KMulK _ k a =>
      match k with
      | O => Some (Some lzero, None)
      | S O => ke_abs r bs a
      | _ => match ke_abs r bs a with Some (ba, None) => Some (option_map (lscale (Z.of_nat k)) ba, None) | _ => None end
      end
  | KBitK o a b =>
      match o with
      | NLand => if klit b then ke_abs r bs b else ke_abs r bs a
      | NLdiff | NShiftr => ke_abs r bs a
      | _ => match ke_abs r bs a, ke_abs r bs b with Some x, Some y => kplus x y | _, _ => None end
      end
  end.
Fixpoint kb_abs (r : bool) (bs : list cbe) (k : sbk) {struct k} : option kbv :=
  match k with
  | KRet a => ke_abs r bs a
  | KLet _ k => kb_abs r bs k
  | KLetB _ k => kb_abs r bs k
  | KLetC c k => kb_abs r ((None, clinf bs c) :: bs) k
  | KIf _ _ _ t f => match kb_abs r bs t, kb_abs r bs f with Some x, Some y => Some (kjoin x y) | _, _ => None end
  | KIfB _ t f => match kb_abs r bs t, kb_abs r bs f with Some x, Some y => Some (kjoin x y) | _, _ => None end
  | KMatch c k0 k1 => match kb_abs r bs k0, kb_abs r ((None, linat bs c) :: bs) k1 with Some x, Some y => Some (kjoin x y) | _, _ => None end
  end.
(** the coefficients of the other counters at most 1; the first counter's coefficient (the [x]-th, the first counter last) *)
Fixpoint cy1 (x : nat) (l : list Z) : bool := match x, l with O, _ => true | _, [] => true | S x, c :: l => (c <=? 1)%Z && cy1 x l end.
Definition cxat (x : nat) (l : list Z) : Z := nth x l 0%Z.
Definition kb_ok1 (x : nat) (o : option linf) : bool := match o with Some L => cy1 x (fst L) | None => true end.
Definition kb_ok2 (x : nat) (o : option linf) : bool := match o with Some L => cy1 x (fst L) && (cxat x (fst L) <=? 0)%Z | None => true end.
Definition oxat (x : nat) (o : option linf) : Z := match o with Some L => cxat x (fst L) | None => 0%Z end.
Definition osnd (o : option linf) : Z := match o with Some L => snd L | None => 0%Z end.
(** the bound: [W] at least 1, the most a round adds, and the first counter's coefficient; [C] the most at no own call *)
Definition kbound (x : nat) (b0 b1 : sbk) : option (Z * Z) :=
  match kb_abs false [] b0, kb_abs true [(None, lunit x)] b1 with
  | Some (Some L0, None), Some (o1, s1) =>
      if cy1 x (fst L0) && kb_ok1 x o1 && kb_ok2 x s1
      then Some (Z.max 1 (Z.max (cxat x (fst L0)) (Z.max (oxat x o1) (osnd s1))), Z.max 0 (Z.max (snd L0) (osnd o1)))
      else None
  | _, _ => None
  end.

(** the facts of the operations on bounds *)
Lemma evc_max0 : forall a pv, (evc a pv <= evc (map (Z.max 0) a) pv)%Z.
Proof. induction a as [|x a IH]; intros [|v pv]; cbn [map evc]; try lia. specialize (IH pv). pose proof (Z.le_max_r 0 x). nia. Qed.
Lemma evc_max0_nonneg : forall a pv, (0 <= evc (map (Z.max 0) a) pv)%Z.
Proof. induction a as [|x a IH]; intros [|v pv]; cbn [map evc]; try lia. specialize (IH pv). pose proof (Z.le_max_l 0 x). nia. Qed.
Lemma evc_zmx_l : forall a b pv, (evc a pv <= evc (zmx a b) pv)%Z.
Proof.
  induction a as [|x a IH]; intros b pv; cbn [zmx].
  - cbn [evc]. apply evc_max0_nonneg.
  - destruct b as [|y b]; [apply evc_max0|]. destruct pv as [|v pv]; cbn [evc]; [lia|]. specialize (IH b pv). pose proof (Z.le_max_l x y). nia.
Qed.
Lemma evc_zmx_r : forall a b pv, (evc b pv <= evc (zmx a b) pv)%Z.
Proof.
  induction a as [|x a IH]; intros b pv; cbn [zmx]; [apply evc_max0|].
  destruct b as [|y b]; [cbn [evc]; apply (evc_max0_nonneg (x :: a))|]. destruct pv as [|v pv]; cbn [evc]; [lia|]. specialize (IH b pv).
  pose proof (Z.le_max_r x y). nia.
Qed.
Lemma obnd_le : forall pv o z z', (z' <= z)%Z -> obnd pv o z -> obnd pv o z'.
Proof. intros pv [L|] z z' H B; cbn [obnd] in *; [lia | exact B]. Qed.
Lemma obnd_some : forall pv o z, obnd pv o z -> exists L, o = Some L.
Proof. intros pv [L|] z B; [eauto | destruct B]. Qed.
Lemma obnd_omx_l : forall pv a b z, obnd pv a z -> obnd pv (omx a b) z.
Proof.
  intros pv [x|] [y|] z B; cbn [omx obnd] in *; try exact B; try (exfalso; exact B).
  unfold lmx, leval in *. cbn [fst snd]. pose proof (evc_zmx_l (fst x) (fst y) pv). lia.
Qed.
Lemma obnd_omx_r : forall pv a b z, obnd pv b z -> obnd pv (omx a b) z.
Proof.
  intros pv [x|] [y|] z B; cbn [omx obnd] in *; try exact B; try (exfalso; exact B).
  unfold lmx, leval in *. cbn [fst snd]. pose proof (evc_zmx_r (fst x) (fst y) pv). lia.
Qed.
Lemma obnd_add : forall pv a b z1 z2, obnd pv a z1 -> obnd pv b z2 -> obnd pv (oadd a b) (z1 + z2).
Proof. intros pv [x|] [y|] z1 z2 B1 B2; cbn [oadd obnd] in *; try (exfalso; exact B1); try (exfalso; exact B2). rewrite leval_add. lia. Qed.
Lemma kv_le : forall pv Q v v' a, (v <= v')%nat -> kv_ok pv Q v' a -> kv_ok pv Q v a.
Proof.
  intros pv Q v v' a H [B|B]; [left; apply (obnd_le pv _ (Z.of_nat v')) | right; apply (obnd_le pv _ (Z.of_nat v' - Q))]; try exact B; lia.
Qed.
Lemma kv_join_l : forall pv Q v a b, kv_ok pv Q v a -> kv_ok pv Q v (kjoin a b).
Proof. intros pv Q v a b [B|B]; [left | right]; apply obnd_omx_l; exact B. Qed.
Lemma kv_join_r : forall pv Q v a b, kv_ok pv Q v b -> kv_ok pv Q v (kjoin a b).
Proof. intros pv Q v a b [B|B]; [left | right]; apply obnd_omx_r; exact B. Qed.
Lemma kv_plus : forall pv Q va vb a b c, kv_ok pv Q va a -> kv_ok pv Q vb b -> kplus a b = Some c -> kv_ok pv Q (va + vb) c.
Proof.
  intros pv Q va vb [ba sa] [bb sb] c Ba Bb E. unfold kv_ok in *. cbn [fst snd] in Ba, Bb.
  assert (K : sa = None \/ sb = None) by (destruct sa, sb; cbn in E; [discriminate E | right; reflexivity | left; reflexivity | left; reflexivity]).
  assert (E' : c = (oadd ba bb, omx (oadd sa bb) (oadd ba sb))) by (unfold kplus in E; cbn [fst snd] in E; destruct sa, sb; try discriminate E; injection E as <-; reflexivity).
  subst c. cbn [fst snd]. destruct Ba as [Ba|Ba], Bb as [Bb|Bb].
  - left. eapply obnd_le; [|exact (obnd_add pv _ _ _ _ Ba Bb)]. lia.
  - right. apply obnd_omx_r. eapply obnd_le; [|exact (obnd_add pv _ _ _ _ Ba Bb)]. lia.
  - right. apply obnd_omx_l. eapply obnd_le; [|exact (obnd_add pv _ _ _ _ Ba Bb)]. lia.
  - exfalso. destruct K as [-> | ->]; cbn [obnd] in *; [destruct Ba | destruct Bb].
Qed.
Lemma kv_shift : forall pv Q v a, kv_ok pv Q v a -> kv_ok pv Q (S v) (kshift a).
Proof.
  intros pv Q v [[x|] [y|]] [B|B]; unfold kshift, kv_ok in *; cbn [fst snd option_map obnd] in *; try (exfalso; exact B);
    rewrite ?leval_shift; lia.
Qed.
Lemma lsumc_ok : forall bs pv ccs cs rec cenv benv renv env s, cbl bs pv cenv ->
  (zsum (denote_cs cs rec cenv benv renv env s ccs) <= leval (lsumc bs ccs) pv)%Z.
Proof.
  intros bs pv. induction ccs as [|c ccs IH]; intros cs rec cenv benv renv env s Cb; unfold lsumc in *; simpl denote_cs; cbn [lc fold_right].
  - rewrite leval_zero. reflexivity.
  - rewrite zsum_cons, leval_add. pose proof (clinf_le bs pv c cs rec cenv benv renv env s Cb). specialize (IH cs rec cenv benv renv env s Cb). lia.
Qed.

(** the bound of a value of the syntax: [reck] the function's own call, below the sum of the counters it is given plus [Q] where it
    is the recursion, 0 where it is the function at the counter's 0 *)
Lemma ke_abs_ok : forall cs (reck : list nat -> list val -> mem -> nat) r pv Q,
  (r = true -> forall cvs args s, (Z.of_nat (reck cvs args s) <= zsum cvs + Q)%Z) -> (r = false -> forall cvs args s, reck cvs args s = O) ->
  forall a bs A cenv benv renv env s, cbl bs pv cenv -> ke_abs r bs a = Some A -> kv_ok pv Q (denote_ke cs reck cenv benv renv env s a) A.
Proof.
  intros cs reck r pv Q H1 H0.
  induction a as [ccs args | c | a IH | a IHa b IHb | l k a IH | o a IHa b IHb]; intros bs A cenv benv renv env s Cb E; cbn [ke_abs] in E;
    cbn [denote_ke].
  - injection E as <-. destruct r.
    + right. cbn [fst snd obnd]. pose proof (H1 eq_refl (denote_cs cs (krec reck) cenv benv renv env s ccs) (denote_es cs (krec reck) cenv benv renv env s args) s).
      pose proof (lsumc_ok bs pv ccs cs (krec reck) cenv benv renv env s Cb). lia.
    + left. cbn [fst snd obnd]. rewrite (H0 eq_refl). rewrite leval_zero. lia.
  - injection E as <-. left. cbn [fst obnd]. exact (clinf_le bs pv c cs (krec reck) cenv benv renv env s Cb).
  - destruct (ke_abs r bs a) as [A'|] eqn:Ea; cbn [option_map] in E; [|discriminate E]. injection E as <-.
    apply kv_shift. exact (IH bs A' cenv benv renv env s Cb Ea).
  - destruct (ke_abs r bs a) as [x|] eqn:Ea; [|discriminate E]. destruct (ke_abs r bs b) as [y|] eqn:Eb; [|discriminate E].
    exact (kv_plus pv Q _ _ x y A (IHa bs x cenv benv renv env s Cb Ea) (IHb bs y cenv benv renv env s Cb Eb) E).
  - assert (M : forall w, (if l then Nat.mul k w else Nat.mul w k) = (k * w)%nat) by (intros w; destruct l; lia). rewrite M.
    destruct k as [|[|k]]; cbn beta iota in E.
    + injection E as <-. left. cbn [fst obnd]. rewrite leval_zero. lia.
    + rewrite Nat.mul_1_l. exact (IH bs A cenv benv renv env s Cb E).
    + destruct (ke_abs r bs a) as [[ba [sa|]]|] eqn:Ea; cbn beta iota in E; try discriminate E. injection E as <-.
      destruct (IH bs (ba, None) cenv benv renv env s Cb Ea) as [B|B]; [|destruct B]. left.
      destruct ba as [L|]; cbn [fst obnd option_map] in *; [|destruct B]. rewrite leval_scale. nia.
  - destruct o; cbn [nbop_nat]; cbn beta iota in E.
    + destruct (klit b).
      * eapply kv_le; [|exact (IHb bs A cenv benv renv env s Cb E)]. rewrite Nat.land_comm. apply nland_le.
      * eapply kv_le; [|exact (IHa bs A cenv benv renv env s Cb E)]. apply nland_le.
    + destruct (ke_abs r bs a) as [x|] eqn:Ea; [|discriminate E]. destruct (ke_abs r bs b) as [y|] eqn:Eb; [|discriminate E].
      eapply kv_le; [|exact (kv_plus pv Q _ _ x y A (IHa bs x cenv benv renv env s Cb Ea) (IHb bs y cenv benv renv env s Cb Eb) E)].
      pose proof (nbop_le_add NLor (denote_ke cs reck cenv benv renv env s a) (denote_ke cs reck cenv benv renv env s b)). cbn [nbop_nat] in *. lia.
    + destruct (ke_abs r bs a) as [x|] eqn:Ea; [|discriminate E]. destruct (ke_abs r bs b) as [y|] eqn:Eb; [|discriminate E].
      eapply kv_le; [|exact (kv_plus pv Q _ _ x y A (IHa bs x cenv benv renv env s Cb Ea) (IHb bs y cenv benv renv env s Cb Eb) E)].
      pose proof (nbop_le_add NLxor (denote_ke cs reck cenv benv renv env s a) (denote_ke cs reck cenv benv renv env s b)). cbn [nbop_nat] in *. lia.
    + eapply kv_le; [|exact (IHa bs A cenv benv renv env s Cb E)]. apply nldiff_le.
    + eapply kv_le; [|exact (IHa bs A cenv benv renv env s Cb E)]. apply nshiftr_le.
    + destruct (ke_abs r bs a) as [x|] eqn:Ea; [|discriminate E]. destruct (ke_abs r bs b) as [y|] eqn:Eb; [|discriminate E].
      eapply kv_le; [|exact (kv_plus pv Q _ _ x y A (IHa bs x cenv benv renv env s Cb Ea) (IHb bs y cenv benv renv env s Cb Eb) E)].
      pose proof (nbop_le_add NClear (denote_ke cs reck cenv benv renv env s a) (denote_ke cs reck cenv benv renv env s b)). cbn [nbop_nat] in *. lia.
Qed.
Lemma kb_abs_ok : forall cs (reck : list nat -> list val -> mem -> nat) r pv Q,
  (r = true -> forall cvs args s, (Z.of_nat (reck cvs args s) <= zsum cvs + Q)%Z) -> (r = false -> forall cvs args s, reck cvs args s = O) ->
  forall k bs A cenv benv renv env s, cbl bs pv cenv -> kb_abs r bs k = Some A -> kv_ok pv Q (denote_kb cs reck cenv benv renv env s k) A.
Proof.
  intros cs reck r pv Q H1 H0.
  induction k as [a | e1 k IH | b k IH | c k IH | o x y t IHt f IHf | b t IHt f IHf | c k0 IH0 k1 IH1];
    intros bs A cenv benv renv env s Cb E; cbn [kb_abs] in E; cbn [denote_kb].
  - exact (ke_abs_ok cs reck r pv Q H1 H0 a bs A cenv benv renv env s Cb E).
  - exact (IH bs A cenv benv renv _ s Cb E).
  - exact (IH bs A cenv _ renv env s Cb E).
  - eapply (IH ((None, clinf bs c) :: bs) A _ benv renv env s); [|exact E]. apply cbl_cons; [exact Cb|]. cbn [snd]. apply clinf_le with (1 := Cb).
  - destruct (kb_abs r bs t) as [u|] eqn:Et; [|discriminate E]. destruct (kb_abs r bs f) as [w|] eqn:Ef; [|discriminate E].
    injection E as <-. destruct (cmp_sem o _ _); [apply kv_join_l; exact (IHt bs u cenv benv renv env s Cb Et)
                                                 | apply kv_join_r; exact (IHf bs w cenv benv renv env s Cb Ef)].
  - destruct (kb_abs r bs t) as [u|] eqn:Et; [|discriminate E]. destruct (kb_abs r bs f) as [w|] eqn:Ef; [|discriminate E].
    injection E as <-. destruct (denote_b _ _ _ _ _ _ _ b); [apply kv_join_l; exact (IHt bs u cenv benv renv env s Cb Et)
                                                          | apply kv_join_r; exact (IHf bs w cenv benv renv env s Cb Ef)].
  - destruct (kb_abs r bs k0) as [u|] eqn:E0; [|discriminate E]. destruct (kb_abs r _ k1) as [w|] eqn:E1; [|discriminate E].
    injection E as <-. pose proof (linat_le bs pv cenv c Cb) as Lc. destruct (nth c cenv O) as [|p] eqn:Ec.
    + apply kv_join_l. exact (IH0 bs u cenv benv renv env s Cb E0).
    + apply kv_join_r. apply (IH1 ((None, linat bs c) :: bs) w (p :: cenv) benv renv env s); [|exact E1]. apply cbl_cons; [exact Cb|]. cbn [snd]. lia.
Qed.

(** a linear bound whose coefficients of the other counters are at most 1, at the function's counters [l] and its first [z] *)
Lemma evc_cy1 : forall x c l z, length l = x -> cy1 x c = true -> (evc c (l ++ [z]) <= zsum l + cxat x c * Z.of_nat z)%Z.
Proof.
  induction x as [|x IH]; intros c l z L C.
  - destruct l; [|discriminate L]. destruct c as [|a c]; cbn [app evc cxat nth]; unfold zsum; cbn [fold_right]; [lia|]. destruct c; cbn [evc]; lia.
  - destruct l as [|y l]; [discriminate L|]. injection L as L. destruct c as [|a c].
    + cbn [app evc]. unfold cxat. cbn [nth]. pose proof (zsum_nonneg (y :: l)). lia.
    + cbn [cy1] in C. apply andb_true_iff in C as [C1 C]. apply Z.leb_le in C1. cbn [app evc]. rewrite zsum_cons.
      specialize (IH c l z L C). unfold cxat in *. cbn [nth]. nia.
Qed.

(** a function's counters, from its curried form: [absc]'s list at most the counters given *)
Lemma appc_absc_any : forall x T F cvs, exists l, length l = x /\ (zsum l <= zsum cvs)%Z /\ appc x T (absc x T F) cvs = F l.
Proof.
  induction x as [|x IH]; intros T F cvs.
  - exists []. split; [reflexivity|]. split; [apply zsum_nonneg | reflexivity].
  - destruct cvs as [|c cvs]; cbn [absc appc].
    + destruct (IH T (fun l => F (l ++ [O])) []) as (l & L & Z1 & E). exists (l ++ [O]).
      split; [rewrite length_app, L; cbn; lia|]. split; [rewrite zsum_snoc; cbn [Z.of_nat]; lia | exact E].
    + destruct (IH T (fun l => F (l ++ [c])) cvs) as (l & L & Z1 & E). exists (l ++ [c]).
      split; [rewrite length_app, L; cbn; lia|]. split; [rewrite zsum_snoc, zsum_cons; lia | exact E].
Qed.
Lemma appnT_absnT_any : forall ks m T G vs s, exists env benv renv s', appnT ks m T (absnT ks m T G) vs s = G env benv renv s'.
Proof.
  induction ks as [|[| |ri] ks IH]; intros m T G vs s.
  - destruct m; cbn [absnT appnT]; eauto.
  - cbn [absnT appnT]. destruct vs as [|v vs]; try destruct v;
    match goal with |- context [appnT ?ks' ?m' ?T' (absnT ?ks' ?m' ?T' ?G') ?vs' ?s0] =>
      destruct (IH m' T' G' vs' s0) as (e & b0 & r0 & s1 & ->) end; eauto.
  - cbn [absnT appnT]. destruct vs as [|v vs]; try destruct v;
    match goal with |- context [appnT ?ks' ?m' ?T' (absnT ?ks' ?m' ?T' ?G') ?vs' ?s0] =>
      destruct (IH m' T' G' vs' s0) as (e & b0 & r0 & s1 & ->) end; eauto.
  - cbn [absnT appnT]. destruct vs as [|v vs]; try destruct v;
    match goal with |- context [appnT ?ks' ?m' ?T' (absnT ?ks' ?m' ?T' ?G') ?vs' ?s0] =>
      destruct (IH m' T' G' vs' s0) as (e & b0 & r0 & s1 & ->) end; eauto.
Qed.
Lemma denote_kf_O : forall cs x k m b0 b1, denote_kf cs x k m b0 b1 O =
  absc x _ (fun cenv => absnT k m nat (fun env benv renv s => denote_kb cs kzero (cenv ++ [O]) benv renv env s b0)).
Proof. reflexivity. Qed.
Lemma denote_kf_S : forall cs x k m b0 b1 n, denote_kf cs x k m b0 b1 (S n) =
  absc x _ (fun cenv => absnT k m nat (fun env benv renv s =>
    denote_kb cs (fun cvs args s' => appnT k m nat (appc x _ (denote_kf cs x k m b0 b1 n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s b1)).
Proof. reflexivity. Qed.

(** the bound, at every counter and argument *)
Lemma kbound_list : forall cs x k m b0 b1 W C, kbound x b0 b1 = Some (W, C) ->
  forall n cvs vs s, (Z.of_nat (appnT k m nat (appc x _ (denote_kf cs x k m b0 b1 n) cvs) vs s) <= zsum cvs + W * Z.of_nat n + C)%Z.
Proof.
  intros cs x k m b0 b1 W C E. unfold kbound in E.
  destruct (kb_abs false [] b0) as [[[L0|] [s0|]]|] eqn:E0; try discriminate E.
  destruct (kb_abs true [(None, lunit x)] b1) as [[o1 s1]|] eqn:E1; [|discriminate E].
  destruct (cy1 x (fst L0) && kb_ok1 x o1 && kb_ok2 x s1) eqn:CK; [|discriminate E].
  apply andb_true_iff in CK as [CK C2]. apply andb_true_iff in CK as [C0 C1]. injection E as EW EC.
  induction n as [|n IH]; intros cvs vs s.
  - rewrite denote_kf_O.
    match goal with |- context [appc x ?T (absc x ?T ?F) cvs] => destruct (appc_absc_any x T F cvs) as (l & L & Zl & ->) end. cbv beta.
    match goal with |- context [appnT k m nat (absnT k m nat ?G) vs s] => destruct (appnT_absnT_any k m nat G vs s) as (env & benv & renv & s' & ->) end.
    cbv beta.
    assert (Cb : cbl [] (l ++ [O]) (l ++ [O])) by (split; [reflexivity | intros i Hi; cbn [length] in Hi; lia]).
    destruct (kb_abs_ok cs kzero false (l ++ [O]) 0%Z (fun H => ltac:(discriminate H)) (fun _ _ _ _ => eq_refl) b0 [] _ (l ++ [O]) benv renv env s' Cb E0)
      as [B|B]; cbn [fst snd obnd] in B; [|destruct B].
    unfold leval in B. pose proof (evc_cy1 x (fst L0) l O L C0). lia.
  - rewrite denote_kf_S.
    match goal with |- context [appc x ?T (absc x ?T ?F) cvs] => destruct (appc_absc_any x T F cvs) as (l & L & Zl & ->) end. cbv beta.
    match goal with |- context [appnT k m nat (absnT k m nat ?G) vs s] => destruct (appnT_absnT_any k m nat G vs s) as (env & benv & renv & s' & ->) end.
    cbv beta.
    assert (Cb : cbl [(None, lunit x)] (l ++ [S n]) (n :: l ++ [S n])).
    { split; [reflexivity|]. intros [|i] Hi; cbn [length] in Hi; [|lia]. cbn [nth snd]. rewrite leval_unit, <- L, nth_middle. lia. }
    destruct (kb_abs_ok cs (fun cvs args s' => appnT k m nat (appc x _ (denote_kf cs x k m b0 b1 n) cvs) args s') true (l ++ [S n]) (W * Z.of_nat n + C)%Z
                        (fun _ cvs' args s'' => ltac:(pose proof (IH cvs' args s''); lia)) (fun H => ltac:(discriminate H))
                        b1 _ _ _ benv renv env s' Cb E1) as [B|B]; cbn [fst snd] in B.
    + destruct o1 as [L1|]; cbn [obnd kb_ok1 oxat osnd] in B, C1, EW, EC; [|destruct B]. unfold leval in B. pose proof (evc_cy1 x (fst L1) l (S n) L C1).
      assert (W1 : (cxat x (fst L1) <= W)%Z) by lia. assert (C1' : (snd L1 <= C)%Z) by lia. nia.
    + destruct s1 as [S1|]; cbn [obnd kb_ok2 osnd] in B, C2, EW; [|destruct B]. apply andb_true_iff in C2 as [C2 C3]. apply Z.leb_le in C3.
      unfold leval in B. pose proof (evc_cy1 x (fst S1) l (S n) L C2).
      assert (W2 : (snd S1 <= W)%Z) by lia. nia.
Qed.
Lemma kbound_pos : forall x b0 b1 W C, kbound x b0 b1 = Some (W, C) -> (1 <= W)%Z /\ (0 <= C)%Z.
Proof.
  intros x b0 b1 W C E. unfold kbound in E.
  destruct (kb_abs false [] b0) as [[[L0|] [s0|]]|]; try discriminate E. destruct (kb_abs true [(None, lunit x)] b1) as [[o1 s1]|]; [|discriminate E].
  destruct (cy1 x (fst L0) && kb_ok1 x o1 && kb_ok2 x s1); [|discriminate E]. injection E as <- <-. lia.
Qed.

(** the bound as the reader states it, by conversion: at every counter and argument, [W] times the first counter plus the other
    counters plus [C] ([K] what comes before the counters left) *)
Fixpoint kbn (ks : list kind) (m : bool) {struct ks} : ntypeT ks m nat -> nat -> Prop :=
  match ks as k0 return ntypeT k0 m nat -> nat -> Prop with
  | [] => if m as m0 return ntypeT [] m0 nat -> nat -> Prop then (fun g B => forall s, (g s <= B)%nat) else (fun g B => (g <= B)%nat)
  | KNum :: ks => fun g B => forall a, kbn ks m (g a) B
  | KBool :: ks => fun g B => forall a, kbn ks m (g a) B
  | KRec ri :: ks => fun g B => forall a, kbn ks m (g a) B
  end.
Fixpoint kbc (x : nat) (ks : list kind) (m : bool) (cst : nat) {struct x} : ctype x (ntypeT ks m nat) -> (nat -> nat) -> Prop :=
  match x as x0 return ctype x0 (ntypeT ks m nat) -> (nat -> nat) -> Prop with
  | O => fun h K => kbn ks m h (K cst)
  | S x => fun h K => forall c, kbc x ks m cst (h c) (fun r => K (Nat.add c r))
  end.
(** [w] times the first counter, then the rest: a function written out, no constant of ours, so that the kernel compares the reader's
    [Nat.add] with [Nat.add] and each written number with its own, never unfolding a large one (measured: a constant there makes it
    work a number of 2^62 out in unary) *)
Definition kbstmt (x : nat) (ks : list kind) (m : bool) (w c : nat) (f : ctype (S x) (ntypeT ks m nat)) : Prop :=
  forall n, kbc x ks m c (f n) (fun r => Nat.add (Nat.mul w n) r).
Lemma kbn_intro : forall ks m g B, (forall vs s, (appnT ks m nat g vs s <= B)%nat) -> kbn ks m g B.
Proof.
  induction ks as [|[| |ri] ks IH]; intros m g B H.
  - destruct m; cbn [kbn]; [intros s; exact (H [] s) | exact (H [] dummy_mem)].
  - cbn [kbn]. intros a. apply IH. intros vs s. exact (H (VNum a :: vs) s).
  - cbn [kbn]. intros a. apply IH. intros vs s. exact (H (VBool a :: vs) s).
  - cbn [kbn]. intros a. apply IH. intros vs s. pose proof (H (VRec ri a :: vs) s) as Ha. cbn [appnT] in Ha. rewrite to_rt_same in Ha. exact Ha.
Qed.
Lemma kbc_intro : forall x ks m cst h K, (forall cvs vs s, (appnT ks m nat (appc x _ h cvs) vs s <= K (fold_right Nat.add cst cvs))%nat) ->
  kbc x ks m cst h K.
Proof.
  induction x as [|x IH]; intros ks m cst h K H; cbn [kbc].
  - apply kbn_intro. intros vs s. exact (H [] vs s).
  - intros c. apply IH. intros cvs vs s. exact (H (c :: cvs) vs s).
Qed.
Lemma fold_add : forall cst l, fold_right Nat.add cst l = (fold_right Nat.add O l + cst)%nat.
Proof. intros cst. induction l as [|a l IH]; cbn [fold_right]; lia. Qed.

(** a program's bound of a function giving back a counter: [kbound] of its syntax, by conversion with what the reader states *)
Definition kbound_some (o : option (Z * Z)) : bool := match o with Some _ => true | None => false end.
Definition kbW (o : option (Z * Z)) : Z := match o with Some (w, _) => w | None => 0%Z end.
Definition kbC (o : option (Z * Z)) : Z := match o with Some (_, c) => c | None => 0%Z end.
Theorem kbound_ok : forall cs x k m b0 b1, kbound_some (kbound x b0 b1) = true ->
  kbstmt x k m (Z.to_nat (kbW (kbound x b0 b1))) (Z.to_nat (kbC (kbound x b0 b1))) (denote_kf cs x k m b0 b1).
Proof.
  intros cs x k m b0 b1 H. destruct (kbound x b0 b1) as [[W C]|] eqn:E; [|discriminate H]. cbn [kbW kbC].
  pose proof (kbound_pos x b0 b1 W C E) as [P1 P2]. pose proof (kbound_list cs x k m b0 b1 W C E) as B.
  intros n. apply kbc_intro. intros cvs vs s. rewrite fold_add. specialize (B n cvs vs s). unfold zsum in B.
  apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add, Nat2Z.inj_mul, !Z2Nat.id by lia. lia.
Qed.
End K.

(** a program's row of a counter function: the function made a number at its results; its statement [C .. = ofn (cnt ..)] holds by
    conversion.  Its parameters hold no record (the rows made so), so its type is the same at every program's record types *)
Definition krow (x : nat) (k : list kind) (m : bool) (f : ctype (S x) (@ntypeT no_recs k m nat)) : ctype (S x) (@ntypeT no_recs k m i63) :=
  cmapT (S x) _ _ (@nmapT no_recs k m nat i63 ofn) f.
