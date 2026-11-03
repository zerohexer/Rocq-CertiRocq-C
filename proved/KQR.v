(** KQR.v -- the verified compiler by reflection (Rocq-C-solution.md §1.12, §12.V).

    [sexp] is a syntax of numbers: operations, tests, lets, reads of the memory, the recursive call, calls of the program's
    other functions, a match on a counter, tests and lets of booleans.  [sbool] is a syntax of booleans: comparisons,
    boolean variables, [true], [false], [&&], [||], [negb].  [scnt] is a syntax of counters: a counter variable, 0, a successor, the counter of
    a number ([kq_nat]).  [smem] is a syntax of memories: the newest memory, a write, lets, tests, the recursive call and calls
    of functions that give back a memory, each given the memory made before it, a match on a counter.  A function has a
    signature (its counters first, [k] numbers, a memory or not, a number or a memory as its result) and a body (recursive on
    its first counter, or plain).  [denote_f] gives the Rocq function a syntax tree stands for, reduced to exactly the shape of
    the user's text, with the meanings of the callees as parameters -- at the per-program check they are the user's own
    functions -- so that the check [f = denote_f ..] is the kernel's computation alone.  [compile_f] makes the KQL function;
    [compile_f_ok] -- proved once, for every syntax tree -- says: if the callees' KQL compute their meanings, the function's
    KQL computes its meaning (the modular shape of today's per-function statements).

    The memory is linear by construction of the syntax: only the newest memory can be named ([MCur], and the memory every
    read and call is given), so the one memory of KQL, written in place, is always the newest memory of the Rocq text.
    A counter is held in KQL as its machine number [ofn n]; function [j] of a program takes its counters below [cbz j], a
    bound that falls as [j] grows, so a caller's counter plus a few successors is still below its callee's bound. *)

From Stdlib Require Import List Uint63 ZArith Lia.
From Stdlib Require FinFun Eqdep_dec.
From compcert Require Import Coqlib Maps AST.
From KQC Require Import KQL KQLAuto KQMSem.
From KQC Require KQMAuto.
Require KQ.KQRun KQ.KQBound.
Import ListNotations.

Notation mem := KQ.KQRun.mem.

(** the kinds of a function's parameters after its counters, in the user's order, and the values a call gives them; a
    boolean is held in KQL as the number 1 or 0 *)
Inductive kind := KNum | KBool | KRec (ri : nat).
Definition b2i (b : bool) : i63 := if b then 1%uint63 else 0%uint63.

(** a record type of the program: its number of fields, its constructor on the list of its fields, its match (the user's own
    match, so that a field is the user's projection: [fst p] is [match p with (a, b) => a end]) *)
Record rops (T : Type) := mkrops { rn : nat; rtg : option (list nat); rmk : list i63 -> T; relim : forall P : Type, T -> (list i63 -> P) -> P }.
Arguments mkrops {T} rn rtg rmk relim.
Arguments rn {T} r.
Arguments rtg {T} r.
Arguments rmk {T} r l.
Arguments relim {T} r {P} x k.
(** the program's record types, given to the meaning as the callees are: type [i] is [RT i], with its operations [RO i]
    and a value of it [Rd i] *)
Class RecTypes := { RT : nat -> Type; RO : forall i, rops (RT i); Rd : forall i, RT i;
  (* a record holding records taken apart and built one level (step 43): its number fields and its record fields (each with
     its type), each in their order; [RJ i] the types of its record fields *)
  RS : forall i (P : Type), RT i -> (list i63 -> list (sigT RT) -> P) -> P;
  RB : forall i, list i63 -> list (sigT RT) -> RT i;
  RJ : nat -> list nat }.
(** the record types of a program without records holding records: the one-level match and constructor are [relim] and [rmk] *)
Definition mkrecs (Tr : nat -> Type) (Ro : forall i, rops (Tr i)) (Dr : forall i, Tr i) : RecTypes :=
  {| RT := Tr; RO := Ro; Rd := Dr; RS := fun i P x k => relim (Ro i) x (fun l => k l []); RB := fun i l _ => rmk (Ro i) l;
     RJ := fun _ => [] |}.
(** a list in a constructor's form (step 28): for a record ([rtg = None]), any; for a data type held as its tag and its fields
    ([rtg = Some ws]: constructor [c] carries [nth c ws] numbers), the tag a constructor's number and the fields after its own 0 *)
Fixpoint zeros_from (w : nat) (l : list i63) : bool :=
  match l with
  | [] => true
  | x :: r => match w with O => PrimInt63.eqb x 0%uint63 && zeros_from O r | S w' => zeros_from w' r end
  end.
Definition canon (g : option (list nat)) (l : list i63) : bool :=
  match g with
  | None => true
  | Some ws => match l with
               | t :: fs => existsb (fun c => PrimInt63.eqb t (ofn c) && zeros_from (nth c ws O) fs) (seq 0 (length ws))
               | [] => false
               end
  end.
(** what the proof needs of them: the match gives the fields to its continuation, there are [rn] of them, and the constructor
    on [rn] numbers in a constructor's form has those as its fields; for each program, proof terms by a dependent match *)
Class RecLaws `{RecTypes} : Prop := {
  rl_nat : forall i (x : RT i) (P : Type) (k : list i63 -> P), relim (RO i) x k = k (relim (RO i) x (fun l => l));
  rl_len : forall i (x : RT i), length (relim (RO i) x (fun l => l)) = rn (RO i);
  rl_mk : forall i l, rtg (RO i) = None -> length l = rn (RO i) -> relim (RO i) (rmk (RO i) l) (fun l => l) = l;
  rl_mk_tag : forall i ws c rest, rtg (RO i) = Some ws -> (c < length ws)%nat -> length rest = Nat.pred (rn (RO i)) ->
    zeros_from (nth c ws O) rest = true -> relim (RO i) (rmk (RO i) (ofn c :: rest)) (fun l => l) = ofn c :: rest;
  (* the one-level match gives its fields to its continuation; the number fields, then the record fields' numbers, are the
     record's numbers; the record fields are of the types [RJ]; the one-level constructor on such fields has them as its numbers *)
  rs_nat : forall i (x : RT i) (P : Type) (k : list i63 -> list (sigT RT) -> P),
    RS i P x k = k (fst (RS i _ x (fun l rs => (l, rs)))) (snd (RS i _ x (fun l rs => (l, rs))));
  rs_flat : forall i (x : RT i), fst (RS i _ x (fun l rs => (l, rs)))
    ++ concat (map (fun r => relim (RO (projT1 r)) (projT2 r) (fun l => l)) (snd (RS i _ x (fun l rs => (l, rs)))))
    = relim (RO i) x (fun l => l);
  rs_kinds : forall i (x : RT i), map (@projT1 _ _) (snd (RS i _ x (fun l rs => (l, rs)))) = RJ i;
  rb_mk : forall i l rs, rtg (RO i) = None -> map (@projT1 _ _) rs = RJ i ->
    (length l + fold_right (fun r a => rn (RO (projT1 r)) + a) O rs)%nat = rn (RO i) ->
    relim (RO i) (RB i l rs) (fun l => l) = l ++ concat (map (fun r => relim (RO (projT1 r)) (projT2 r) (fun l => l)) rs) }.
(** the laws of a program without records holding records: those of its matches and constructors *)
Lemma laws_of {Tr : nat -> Type} {Ro : forall i, rops (Tr i)} {Dr : forall i, Tr i} :
  (forall i (x : Tr i) (P : Type) (k : list i63 -> P), relim (Ro i) x k = k (relim (Ro i) x (fun l => l))) ->
  (forall i (x : Tr i), length (relim (Ro i) x (fun l => l)) = rn (Ro i)) ->
  (forall i l, rtg (Ro i) = None -> length l = rn (Ro i) -> relim (Ro i) (rmk (Ro i) l) (fun l => l) = l) ->
  (forall i ws c rest, rtg (Ro i) = Some ws -> (c < length ws)%nat -> length rest = Nat.pred (rn (Ro i)) ->
    zeros_from (nth c ws O) rest = true -> relim (Ro i) (rmk (Ro i) (ofn c :: rest)) (fun l => l) = ofn c :: rest) ->
  @RecLaws (mkrecs Tr Ro Dr).
Proof.
  intros H1 H2 H3 H4. split; cbn [RT RO RS RB RJ mkrecs]; [exact H1 | exact H2 | exact H3 | exact H4 | | | |].
  - intros i x P k. rewrite (H1 i x _ (fun l => k l [])), (H1 i x _ (fun l => (l, []))). reflexivity.
  - intros i x. rewrite (H1 i x _ (fun l => (l, []))). cbn. apply app_nil_r.
  - intros i x. rewrite (H1 i x _ (fun l => (l, []))). reflexivity.
  - intros i l rs G Hk Hl. destruct rs as [|r rs]; [|discriminate Hk]. cbn in Hl |- *. rewrite app_nil_r. apply H3; [exact G | lia].
Qed.

Section Recs.
Context {RTs : RecTypes}.

Inductive val := VNum (n : i63) | VBool (b : bool) | VRec (ri : nat) (x : RT ri).
Definition kind_of (v : val) : kind := match v with VNum _ => KNum | VBool _ => KBool | VRec ri _ => KRec ri end.
Definition ofv (v : val) : i63 := match v with VNum n => n | VBool b => b2i b | VRec _ _ => 0%uint63 end.
(** the numbers a value is passed as: one, or a record's fields *)
Definition vflat (v : val) : list i63 :=
  match v with VNum n => [n] | VBool b => [b2i b] | VRec ri x => relim (RO ri) x (fun l => l) end.
(** a value taken apart: a record's fields given to [F] by its own match *)
Definition rmatch {P : Type} (v : val) (F : list i63 -> P) : P :=
  match v with VRec ri x => relim (RO ri) x F | _ => F (vflat v) end.
(** a value taken apart one level (step 43): a record's number fields and its record fields given to [F] by its own one-level
    match *)
Definition vrec (r : sigT RT) : val := VRec (projT1 r) (projT2 r).
Definition rsplit {P : Type} (v : val) (F : list i63 -> list val -> P) : P :=
  match v with VRec ri x => RS ri P x (fun l rs => F l (map vrec rs)) | _ => F (vflat v) [] end.
(** the records of a list of values, with their types *)
Definition vrecs_t (vs : list val) : list (sigT RT) :=
  flat_map (fun v => match v with VRec ri x => [existT RT ri x] | _ => [] end) vs.
(** the numbers and the booleans of a list of values *)
Definition vnums (vs : list val) : list i63 := flat_map (fun v => match v with VNum n => [n] | _ => [] end) vs.
Definition vbools (vs : list val) : list bool := flat_map (fun v => match v with VBool b => [b] | _ => [] end) vs.
Definition vrecs (vs : list val) : list val := filter (fun v => match v with VRec _ _ => true | _ => false end) vs.
(** how many numbers a parameter of a kind is passed as *)
Definition kw (k : kind) : nat := match k with KRec ri => rn (RO ri) | _ => 1 end.
Definition wsum (ks : list kind) : nat := fold_right (fun k a => (kw k + a)%nat) O ks.
(** the value of record type [i] a value stands for (a value of another kind: [Rd i]) *)
Fixpoint ndec (a b : nat) {struct a} : {a = b} + {a <> b} :=
  match a, b with
  | O, O => left eq_refl
  | S a', S b' => match ndec a' b' with left e => left (f_equal S e) | right ne => right (fun h : S a' = S b' => ne (f_equal Nat.pred h)) end
  | O, S b' => right (O_S b')
  | S a', O => right (fun h : S a' = O => O_S a' (eq_sym h))
  end.
Definition to_rt (i : nat) (v : val) : RT i :=
  match v with VRec j x => match ndec j i with left e => eq_rect j RT x i e | right _ => Rd i end | _ => Rd i end.
(** a record of type [j] out of a record with its type (a program's one-level constructor, step 43) *)
Definition tk {T : nat -> Type} (d : forall i, T i) (j : nat) (r : sigT T) : T j :=
  match r with existT _ i x => match ndec i j with left e => eq_rect i T x j e | right _ => d j end end.
(** the u64 whose halves are the first two numbers of a list (a record of the program's type for [u64] taken apart) *)
Definition u64_of_l (l : list i63) : KQ.KQRun.u64 := KQ.KQRun.mk_u64 (nth 0 l 0%uint63) (nth 1 l 0%uint63).
Definition kind_eqb (a b : kind) : bool :=
  match a, b with KNum, KNum | KBool, KBool => true | KRec a, KRec b => Nat.eqb a b | _, _ => false end.
Fixpoint kinds_eqb (a b : list kind) : bool :=
  match a, b with [], [] => true | x :: a, y :: b => kind_eqb x y && kinds_eqb a b | _, _ => false end.

Inductive sexp : Type :=
| SVar (i : nat)                     (* a number: the i-th of the function's numbers and lets, the nearest first *)
| SInt (n : i63)
| SOp (o : binop) (a b : sexp)
| SIf (c : cmpop) (a b : sexp) (t e : sexp)
| SLet (e1 e2 : sexp)                (* let x := e1 in e2; x is SVar 0 in e2 *)
| SRd (h i : sexp)                   (* rd h i s, s the newest memory *)
| SRec (cs : scnts) (args : sexps)   (* the function itself on its counter's predecessor, these counters, numbers, memory *)
| SCall (f : nat) (cs : scnts) (args : sexps)   (* function f of the program on these counters, numbers, the memory *)
| SMatch (c : nat) (e0 e1 : sexp)    (* match on counter variable c: e0 at 0, e1 otherwise (the predecessor is CVar 0) *)
| SIfB (b : sbool) (t e : sexp)      (* if b then t else e, a test that is not one comparison *)
| SLetB (b : sbool) (e : sexp)       (* let x := b in e, x a boolean: BVar 0 in e *)
| SRd32 (h i : sexp)                 (* rd32 h i s: cell i of narrow block h (4-byte cells), s the newest memory *)
| SLetC (c : scnt) (e : sexp)        (* let w := c in e, w a counter: CVar 0 in e *)
| SFld (i j : nat)                   (* field j of the i-th record variable *)
| SLetR (x : srec) (e : sexp)        (* let w := x in e, w a record: the record variable 0 in e *)
| SMatchR (x : srec) (e : sexp)      (* let '(a, b, ..) := x in e: its fields the numbers 0 .. in e, the last one first *)
| SHwf (o : hwfop) (args : sexps)    (* a number the machine gives, without a memory (hwf_sem: hw_addr, hw_irq_info, ..) *)
| SSize (h : sexp)                   (* kq_size h s: the size of block h now, s the newest memory *)
| SRd8 (h i : sexp)                  (* rd8 h i s: byte i of narrow block h (one byte access), s the newest memory *)
(* a record of type ri taken apart one level (step 43): its number fields the numbers 0 .., its record fields the record
   variables 0 .., the last ones first *)
| SSplitR (ri : nat) (x : srec) (e : sexp)
with sexps : Type :=                 (* a call's arguments: numbers and booleans *)
| SNil
| SCons (e : sexp) (r : sexps)
| SConsB (b : sbool) (r : sexps)
| SConsR (x : srec) (r : sexps)
with scnt : Type :=
| CVar (i : nat)                     (* the i-th counter variable, the nearest first *)
| CO
| CS (c : scnt)
| CNat (e : sexp)                    (* kq_nat e: the counter of a number, at most 2^60 *)
| CPred (c : scnt)                   (* Nat.pred c (step 30) *)
| CAdd (a b : scnt)                  (* a + b, Nat.add of two counters (step 33) *)
with scnts : Type :=
| CNil
| CCons (c : scnt) (r : scnts)
with sbool : Type :=
| BCmp (c : cmpop) (a b : sexp)      (* a comparison of two numbers *)
| BVar (i : nat)                     (* the i-th boolean variable, the nearest first *)
| BTrue
| BFalse
| BAnd (x y : sbool)                 (* x && y *)
| BOr (x y : sbool)                  (* x || y *)
| BNot (x : sbool)                   (* negb x *)
| BIfCmp (c : cmpop) (a b : sexp) (x y : sbool)   (* if a c b then x else y (step 22) *)
| BMatchCnt (c : nat) (x0 x1 : sbool)   (* match on counter variable c: x0 at 0, x1 otherwise (the predecessor is CVar 0) *)
| BCall (f : nat) (cs : scnts) (args : sexps)   (* function f of the program, giving back a boolean (step 24) *)
| BCmpC (c : cmpop) (a b : scnt)     (* Nat.eqb, Nat.ltb, Nat.leb of two counters (step 30) *)
(* the constructs of the number sort, in the boolean sort (step 36) *)
| BxIfB (b x y : sbool)              (* if b then x else y, b a boolean *)
| BxLet (e : sexp) (x : sbool)       (* let v := e in x, v a number: SVar 0 in x *)
| BxLetB (b x : sbool)               (* let c := b in x, c a boolean: BVar 0 in x *)
| BxLetC (c : scnt) (x : sbool)      (* let w := c in x, w a counter: CVar 0 in x *)
| BxLetR (r : srec) (x : sbool)      (* let w := r in x, w a record: RVar 0 in x *)
| BxMatchR (r : srec) (x : sbool)    (* let '(a, b, ..) := r in x: r's fields the numbers 0 .. in x, the last one first *)
| BxSplitR (ri : nat) (r : srec) (x : sbool)   (* r, of type ri, taken apart one level (step 43) *)
with srec : Type :=                  (* a record *)
| RVar (i : nat)                     (* the i-th record variable *)
| RMk (ri : nat) (es : sexps)        (* the constructor of record type ri on these numbers *)
| RCall (ri f : nat) (cs : scnts) (args : sexps)    (* function f of the program, giving back a record of type ri *)
| RW64 (ri : nat) (o : KQ.KQRun.w64op) (a b : srec)    (* w64_op o a b, a u64 of the program's type ri (KQRun.v) *)
| RLet (e : sexp) (x : srec)         (* let v := e in x, v a number: SVar 0 in x (a helper giving a record, written out) *)
| RLetR (y x : srec)                 (* let w := y in x, w a record: RVar 0 in x *)
| RIf (ri : nat) (c : cmpop) (a b : sexp) (x y : srec)   (* if a c b then x else y, records of type ri (step 21) *)
| RMatchR (ri : nat) (x y : srec)    (* let '(a, b, ..) := x in y, y of type ri: x's fields the numbers 0 .. in y, the last one first *)
(* the constructs of the number sort, in the record sort (step 36) *)
| RIfB (ri : nat) (b : sbool) (x y : srec)   (* if b then x else y, b a boolean, records of type ri *)
| RLetB (b : sbool) (x : srec)       (* let c := b in x, c a boolean: BVar 0 in x *)
| RLetC (c : scnt) (x : srec)        (* let w := c in x, w a counter: CVar 0 in x *)
| RMatchCnt (ri : nat) (c : nat) (x y : srec)    (* match on counter variable c, records of type ri: x at 0, y otherwise *)
| RSplitR (ri rj : nat) (x y : srec)   (* x, of type rj, taken apart one level in y, of type ri (step 43) *)
| RMkR (ri : nat) (ns rs : sexps).     (* the one-level constructor of record type ri on these numbers and records (step 43) *)

Scheme sexp_mut := Induction for sexp Sort Prop
with sexps_mut := Induction for sexps Sort Prop
with scnt_mut := Induction for scnt Sort Prop
with scnts_mut := Induction for scnts Sort Prop
with sbool_mut := Induction for sbool Sort Prop
with srec_mut := Induction for srec Sort Prop.
Combined Scheme sexp_comb from sexp_mut, sexps_mut, scnt_mut, scnts_mut, sbool_mut, srec_mut.

(** a memory.  The numbers inside one construct are worked out on the memory the construct starts from -- what the Rocq
    text means, since they name that memory -- then the memory it is given, then its own step *)
Inductive smem : Type :=
| MCur                               (* the newest memory *)
| MUpd (h i v : sexp) (m : smem)     (* upd h i v m *)
| MLet (e : sexp) (m : smem)         (* let x := e in m *)
| MLetM (m1 m2 : smem)               (* let s2 := m1 in m2: s2 is the newest memory in m2 *)
| MIf (c : cmpop) (a b : sexp) (m1 m2 : smem)
| MRec (cs : scnts) (args : sexps) (m : smem)   (* the function itself, its counters after the first, numbers, memory m *)
| MCall (f : nat) (cs : scnts) (args : sexps) (m : smem)   (* function f, giving back a memory, on the memory m *)
| MMatch (c : nat) (m0 m1 : smem)    (* match on counter variable c *)
| MIfB (b : sbool) (m1 m2 : smem)    (* if b then m1 else m2, a test that is not one comparison *)
| MLetB (b : sbool) (m : smem)       (* let x := b in m, x a boolean *)
| MUpd32 (h i v : sexp) (m : smem)   (* upd32 h i v m *)
| MLetC (c : scnt) (m : smem)        (* let w := c in m, w a counter *)
| MHw (o : hwop) (args : sexps) (m : smem)    (* a machine operation on the memory m (hw_sem: hw_store, kq_grow, ..) *)
| MUpd8 (h i v : sexp) (m : smem)   (* upd8 h i v m: one byte *)
| MLetR (x : srec) (m : smem)        (* let w := x in m, w a record: the record variable 0 in m *)
| MMatchR (x : srec) (m : smem)      (* let '(a, b, ..) := x in m: its fields the numbers 0 .. in m, the last one first *)
| MSplitR (ri : nat) (x : srec) (m : smem)    (* x, of type ri, taken apart one level (step 43) *)
| MMatchP (p : spv) (m : smem)       (* let '(x, s2) := p in m: x the nearest number, s2 the newest memory (step 44) *)
| MLetP (p : spv) (m : smem)         (* let w := p in m, read through fst w (the nearest number) and snd w (the newest memory) *)
| MCallP (f : nat) (cs : scnts) (args : sexps) (p : spv)   (* function f, giving back a memory, given the pair p (step 44) *)
(* a number and a memory (step 26): built (the number worked out on the memory before the memory's writes), given back by a
    function of the program or by the function itself, chosen by a test or a counter's match, after lets, or made from another
    one taken apart; one mutual type with the memory (step 44) *)
with spv : Type :=
| PvMk (e : sexp) (m : smem)                                (* (e, m) *)
| PvCall (f : nat) (cs : scnts) (args : sexps) (m : smem)   (* function f, giving back a number and a memory, on the memory m *)
| PvRec (cs : scnts) (args : sexps) (m : smem)              (* the function itself, on the memory m *)
| PvLet (e : sexp) (p : spv)
| PvLetB (c : sbool) (p : spv)
| PvLetC (c : scnt) (p : spv)
| PvLetR (x : srec) (p : spv)
| PvMatchR (x : srec) (p : spv)
| PvLetM (m : smem) (p : spv)                               (* let s2 := m in p *)
| PvIf (c : cmpop) (x y : sexp) (t f : spv)
| PvIfB (c : sbool) (t f : spv)
| PvMatch (c : nat) (p0 p1 : spv)
| PvMatchP (p q : spv)                                      (* let '(x, s2) := p in q: x the nearest number, s2 the newest memory *)
| PvSplitR (ri : nat) (x : srec) (p : spv)                  (* x, of type ri, taken apart one level (step 43) *)
| PvCallP (f : nat) (cs : scnts) (args : sexps) (p : spv).  (* function f, giving back a number and a memory, given the pair p *)

Scheme smem_mut := Induction for smem Sort Prop
with spv_mut := Induction for spv Sort Prop.
Combined Scheme smem_comb from smem_mut, spv_mut.

(** a function's signature: [sn] counters first, then parameters of the kinds [sk] in the user's order, a memory last or
    not, a memory as the result or a number, and for a number: whether the function writes the memory ([sw]: its KQL ends
    with some memory, not the one it was given); or a value of another kind as the result ([sq = Some k]): a record of type
    [ri] ([Some (KRec ri)]: a number function whose KQL returns the record's first field and writes the others into the slot
    block), or a boolean ([Some KBool], step 24: its KQL returns 1 or 0) *)
(** a polynomial in a function's counters (step 39): monomials, each a coefficient and the counters it multiplies (their
    positions, the first counter 0) *)
Definition poly : Type := list (nat * list nat).
Record sig := mksig9 { sn : nat; sk : list kind; sm : bool; sr : bool; sw : bool; sq : option kind; sb : option Z; sv : list poly;
                       sp : bool }.
(* sp (step 44): the last number and the memory one parameter, a pair (for a signature that takes a memory); a signature without it *)
Notation mksig8 x k m r w q b v := (mksig9 x k m r w q b v false).
(* a signature with the pair: it takes a memory and its last parameter is a number *)
Definition last_num (ks : list kind) : bool := match rev ks with KNum :: _ => true | _ => false end.
(* sv (steps 37 to 39): none, each counter below the function's bound; else polynomials in the counters, every counter a
   monomial of its own with a coefficient of at least 1 in one of them, and each polynomial at the counters below the bound --
   for a function whose recursion grows counters *)
Definition mksig7 (x : nat) (k : list kind) (m r w : bool) (q : option kind) (b : option Z) : sig := mksig8 x k m r w q b [].
(* sb: the bound on the function's counters when it is given (step 33: per function, worked out for the program); none, the
   bound of its index ([cbz]) *)
Definition mksig (x : nat) (k : list kind) (m r w : bool) (q : option kind) : sig := mksig7 x k m r w q None.
(** [k] numbers *)
Definition nk (k : nat) : list kind := repeat KNum k.
(** whether a function gives back a record *)
Definition isq (gs : sig) : bool := match sq gs with Some _ => true | None => false end.

Definition rty (r : bool) : Type := if r then mem else i63.
(** the result: a record of type [ri], a boolean, or a memory, or a number *)
Definition rtq (r : bool) (q : option kind) : Type :=
  match q with Some (KRec ri) => RT ri | Some KBool => bool | Some KNum => (i63 * mem)%type | None => rty r end.

(** the function's type, its parameters after its counters of the kinds [ks], a memory or not, a result of type [T] *)
Fixpoint ntypeT (ks : list kind) (m : bool) (T : Type) : Type :=
  match ks with
  | [] => if m then (mem -> T) else T
  | KNum :: ks => i63 -> ntypeT ks m T
  | KBool :: ks => bool -> ntypeT ks m T
  | KRec ri :: ks => RT ri -> ntypeT ks m T
  end.
Notation ntype ks m r := (ntypeT ks m (rty r)).

Fixpoint ctype (x : nat) (T : Type) : Type := match x with O => T | S x => nat -> ctype x T end.

(** a function whose last number and memory are one parameter, a pair (step 44): its type *)
Fixpoint ntypeTP (ks : list kind) (T : Type) : Type :=
  match ks with
  | [] => T
  | KNum :: ks' => match ks' with [] => (i63 * mem)%type -> T | _ :: _ => i63 -> ntypeTP ks' T end
  | KBool :: ks' => bool -> ntypeTP ks' T
  | KRec ri :: ks' => RT ri -> ntypeTP ks' T
  end.

Definition ftype (g : sig) : Type :=
  ctype (sn g) (if (if sp g then sm g else false) then ntypeTP (sk g) (rtq (sr g) (sq g)) else ntypeT (sk g) (sm g) (rtq (sr g) (sq g))).

(** a memory for the meaning of a function that takes none: never read (a well formed body reads no memory then) *)
Definition dummy_mem : mem := KQ.KQRun.kq_input 0%uint63.

(** [absnT ks m T F] is [fun x1 .. xk (s) => F env benv renv s]: the parameters bound before anything else, as in the user's
    text, the numbers into [env], the booleans into [benv], the records into [renv], each the last one first *)
Fixpoint absnT (ks : list kind) (m : bool) (T : Type) {struct ks} : (list i63 -> list bool -> list val -> mem -> T) -> ntypeT ks m T :=
  match ks as k0 return (list i63 -> list bool -> list val -> mem -> T) -> ntypeT k0 m T with
  | [] => if m as m0 return (list i63 -> list bool -> list val -> mem -> T) -> ntypeT [] m0 T then (fun F s => F [] [] [] s)
          else (fun F => F [] [] [] dummy_mem)
  | KNum :: ks => fun F x => absnT ks m T (fun env benv renv s => F (env ++ [x]) benv renv s)
  | KBool :: ks => fun F x => absnT ks m T (fun env benv renv s => F env (benv ++ [x]) renv s)
  | KRec ri :: ks => fun F x => absnT ks m T (fun env benv renv s => F env benv (renv ++ [VRec ri x]) s)
  end.
Notation absn ks m r := (absnT ks m (rty r)).

(** [appnT ks m T g [v1; ..; vk] s] is [g v1 .. vk (s)] *)
Fixpoint appnT (ks : list kind) (m : bool) (T : Type) {struct ks} : ntypeT ks m T -> list val -> mem -> T :=
  match ks as k0 return ntypeT k0 m T -> list val -> mem -> T with
  | [] => if m as m0 return ntypeT [] m0 T -> list val -> mem -> T then (fun g _ s => g s) else (fun g _ _ => g)
  | KNum :: ks => fun g l s => match l with VNum x :: l => appnT ks m T (g x) l s | _ :: l => appnT ks m T (g 0%uint63) l s
                                            | [] => appnT ks m T (g 0%uint63) [] s end
  | KBool :: ks => fun g l s => match l with VBool x :: l => appnT ks m T (g x) l s | _ :: l => appnT ks m T (g false) l s
                                             | [] => appnT ks m T (g false) [] s end
  | KRec ri :: ks => fun g l s => match l with v :: l => appnT ks m T (g (to_rt ri v)) l s | [] => appnT ks m T (g (Rd ri)) [] s end
  end.
Notation appn ks m r := (appnT ks m (rty r)).

(** a function with the pair (step 44) applied to numbers and a memory: the last number and the memory the pair; on the two
    components: its pair built of them; a function of the components as one of the pair *)
Fixpoint appnTP (ks : list kind) (T : Type) {struct ks} : ntypeTP ks T -> list val -> mem -> T :=
  match ks as k0 return ntypeTP k0 T -> list val -> mem -> T with
  | [] => fun g _ _ => g
  | KNum :: ks' => fun g l s =>
      (match ks' as k1 return (ntypeTP (KNum :: k1) T -> (ntypeTP k1 T -> list val -> mem -> T) -> T) with
       | [] => fun g _ => g (match l with VNum x :: _ => x | _ => 0%uint63 end, s)
       | _ :: _ => fun g rec => match l with VNum x :: l => rec (g x) l s | _ :: l => rec (g 0%uint63) l s | [] => rec (g 0%uint63) [] s end
       end) g (appnTP ks' T)
  | KBool :: ks' => fun g l s => match l with VBool x :: l => appnTP ks' T (g x) l s | _ :: l => appnTP ks' T (g false) l s
                                             | [] => appnTP ks' T (g false) [] s end
  | KRec ri :: ks' => fun g l s => match l with v :: l => appnTP ks' T (g (to_rt ri v)) l s | [] => appnTP ks' T (g (Rd ri)) [] s end
  end.
Fixpoint unpairT (ks : list kind) (T : Type) {struct ks} : ntypeTP ks T -> ntypeT ks true T :=
  match ks as k0 return ntypeTP k0 T -> ntypeT k0 true T with
  | [] => fun g _ => g
  | KNum :: ks' => fun g =>
      (match ks' as k1 return (ntypeTP (KNum :: k1) T -> (ntypeTP k1 T -> ntypeT k1 true T) -> ntypeT (KNum :: k1) true T) with
       | [] => fun g _ x s => g (x, s)
       | _ :: _ => fun g rec x => rec (g x)
       end) g (unpairT ks' T)
  | KBool :: ks' => fun g x => unpairT ks' T (g x)
  | KRec ri :: ks' => fun g x => unpairT ks' T (g x)
  end.
Fixpoint pairT (ks : list kind) (m : bool) (T : Type) {struct ks} : ntypeT ks m T -> ntypeTP ks T :=
  match ks as k0 return ntypeT k0 m T -> ntypeTP k0 T with
  | [] => if m as m0 return ntypeT [] m0 T -> ntypeTP [] T then fun g => g dummy_mem else fun g => g
  | KNum :: ks' => fun g =>
      (match ks' as k1 return (ntypeT (KNum :: k1) m T -> (ntypeT k1 m T -> ntypeTP k1 T) -> ntypeTP (KNum :: k1) T) with
       | [] => fun g _ pr => (if m as m0 return (i63 -> ntypeT [] m0 T) -> T then fun g => g (fst pr) (snd pr) else fun g => g (fst pr)) g
       | _ :: _ => fun g rec x => rec (g x)
       end) g (pairT ks' m T)
  | KBool :: ks' => fun g x => pairT ks' m T (g x)
  | KRec ri :: ks' => fun g x => pairT ks' m T (g x)
  end.
Fixpoint appnTPP (ks : list kind) (T : Type) {struct ks} : ntypeTP ks T -> list val -> (i63 * mem) -> T :=
  match ks as k0 return ntypeTP k0 T -> list val -> (i63 * mem) -> T with
  | [] => fun g _ _ => g
  | KNum :: ks' => fun g l pr =>
      (match ks' as k1 return (ntypeTP (KNum :: k1) T -> (ntypeTP k1 T -> list val -> (i63 * mem) -> T) -> T) with
       | [] => fun g _ => g pr
       | _ :: _ => fun g rec => match l with VNum x :: l => rec (g x) l pr | _ :: l => rec (g 0%uint63) l pr | [] => rec (g 0%uint63) [] pr end
       end) g (appnTPP ks' T)
  | KBool :: ks' => fun g l pr => match l with VBool x :: l => appnTPP ks' T (g x) l pr | _ :: l => appnTPP ks' T (g false) l pr
                                              | [] => appnTPP ks' T (g false) [] pr end
  | KRec ri :: ks' => fun g l pr => match l with v :: l => appnTPP ks' T (g (to_rt ri v)) l pr | [] => appnTPP ks' T (g (Rd ri)) [] pr end
  end.
Fixpoint cmapT (x : nat) (A B : Type) (f : A -> B) {struct x} : ctype x A -> ctype x B :=
  match x as x0 return ctype x0 A -> ctype x0 B with O => f | S x => fun h c => cmapT x A B f (h c) end.

(** the same for counters: [absc x T F] is [fun c1 .. cx => F [cx; ..; c1]], [appc x T h [c1; ..; cx]] is [h c1 .. cx] *)
Fixpoint absc (x : nat) (T : Type) {struct x} : (list nat -> T) -> ctype x T :=
  match x as x0 return (list nat -> T) -> ctype x0 T with
  | O => fun F => F []
  | S x => fun F c => absc x T (fun l => F (l ++ [c]))
  end.

Fixpoint appc (x : nat) (T : Type) {struct x} : ctype x T -> list nat -> T :=
  match x as x0 return ctype x0 T -> list nat -> T with
  | O => fun h _ => h
  | S x => fun h l => match l with c :: l => appc x T (h c) l | [] => appc x T (h O) [] end
  end.

(** a call of a function of signature [g] on its counters, its numbers, the memory *)
Definition callf (g : sig) : ftype g -> list nat -> list val -> mem -> rtq (sr g) (sq g) :=
  match g as g0 return ftype g0 -> list nat -> list val -> mem -> rtq (sr g0) (sq g0) with
  | mksig9 x k m r w q b v p =>
      if (if p then m else false) as p0 return ctype x (if p0 then ntypeTP k (rtq r q) else ntypeT k m (rtq r q)) -> list nat -> list val -> mem -> rtq r q then
        fun h cvs vs s => appnTP k (rtq r q) (appc x (ntypeTP k (rtq r q)) h cvs) vs s
      else fun h cvs vs s => appnT k m (rtq r q) (appc x (ntypeT k m (rtq r q)) h cvs) vs s
  end.

(** a mutual block (step 17): the members, number functions of one signature, are one function with one counter more, the
    selector, last among its counters.  Its meaning applies member [i] of [hs] at the first counter [n] -- the choice the head
    of the meaning, the application in each branch, as a match on the selector stands in a body's meaning *)
Fixpoint sel_app (x : nat) (k : list kind) (m : bool) (hs : list (nat -> ctype x (ntype k m false))) (i n : nat) (cvs : list nat)
  (vs : list val) (s : mem) {struct hs} : i63 :=
  match hs with
  | [] => 0%uint63
  | [h] => appn k m false (appc x _ (h n) cvs) vs s
  | h :: hs' => match i with O => appn k m false (appc x _ (h n) cvs) vs s | S i' => sel_app x k m hs' i' n cvs vs s end
  end.
(** the values of a body's parameters, the last one first, from its numbers, booleans and records *)
Fixpoint vals_rev (ks : list kind) (env : list i63) (benv : list bool) (renv : list val) : list val :=
  match ks with
  | [] => []
  | KNum :: ks => VNum (hd 0%uint63 env) :: vals_rev ks (tl env) benv renv
  | KBool :: ks => VBool (hd false benv) :: vals_rev ks env (tl benv) renv
  | KRec _ :: ks => hd (VNum 0%uint63) renv :: vals_rev ks env benv (tl renv)
  end.
Definition blk (x : nat) (k : list kind) (m : bool) (hs : list (nat -> ctype x (ntype k m false))) : nat -> ctype (S x) (ntype k m false) :=
  fun n => absc (S x) _ (fun cenv => absn k m false (fun env benv renv s =>
    sel_app x k m hs (hd O cenv) n (rev (tl cenv)) (rev (vals_rev (rev k) env benv renv)) s)).
(** a mutual block of any signatures (step 45): each member seen through its view, a function of the block's counters (the
    selector apart) and parameters that gives the member its own in its own order; the result of any type; the first member
    apart, so the choice needs no default *)
Fixpoint sel_appT (x : nat) (k : list kind) (m : bool) (T : Type) (h0 : nat -> ctype x (ntypeT k m T))
  (hs : list (nat -> ctype x (ntypeT k m T))) (i n : nat) (cvs : list nat) (vs : list val) (s : mem) {struct hs} : T :=
  match hs with
  | [] => appnT k m T (appc x _ (h0 n) cvs) vs s
  | h1 :: hs' => match i with O => appnT k m T (appc x _ (h0 n) cvs) vs s | S i' => sel_appT x k m T h1 hs' i' n cvs vs s end
  end.
Definition blkT (x : nat) (k : list kind) (m : bool) (T : Type) (h0 : nat -> ctype x (ntypeT k m T))
  (hs : list (nat -> ctype x (ntypeT k m T))) : nat -> ctype (S x) (ntypeT k m T) :=
  fun n => absc (S x) _ (fun cenv => absnT k m T (fun env benv renv s =>
    sel_appT x k m T h0 hs (hd O cenv) n (rev (tl cenv)) (rev (vals_rev (rev k) env benv renv)) s)).

(** the slot block's cells [j ..] written with these numbers, the last one first *)
Fixpoint wslot (j : nat) (vs : list i63) (s : mem) : mem :=
  match vs with [] => s | v :: vs => KQ.KQRun.upd 63%uint63 (KQLAuto.ofn j) v (wslot (S j) vs s) end.

(** a call's number (0 for a function giving back a memory, as its KQL returns) and the memory after it *)
(** a record given back: its first field returned, the others in the slot block *)
Definition calln (g : sig) (h : ftype g) (cvs : list nat) (vs : list val) (s : mem) : i63 :=
  (match sq g as q return rtq (sr g) q -> i63 with
   | Some (KRec ri) => fun x => hd 0%uint63 (relim (RO ri) x (fun l => l))
   | Some KBool => b2i
   | Some KNum => fun x => fst x
   | None => if sr g as r return rty r -> i63 then fun _ => 0%uint63 else fun x => x
   end) (callf g h cvs vs s).
Definition callm (g : sig) (h : ftype g) (cvs : list nat) (vs : list val) (s : mem) : mem :=
  (match sq g as q return rtq (sr g) q -> mem with
   | Some (KRec ri) => fun x => wslot O (tl (relim (RO ri) x (fun l => l))) s
   | Some KBool => fun _ => s
   | Some KNum => fun x => snd x
   | None => if sr g as r return rty r -> mem then fun x => x else fun _ => s
   end) (callf g h cvs vs s).

(** the value a call gives back, when it is a record *)
Definition vrec_of (g : sig) : rtq (sr g) (sq g) -> val :=
  match sq g as q return rtq (sr g) q -> val with Some (KRec ri) => fun x => VRec ri x | _ => fun _ => VNum 0%uint63 end.

(** a comparison of two counters (step 30): the user's own functions *)
Definition cmpn (c : cmpop) (a b : nat) : bool := match c with Ceq => Nat.eqb a b | Clt => Nat.ltb a b | Cle => Nat.leb a b | _ => false end.

(** the value a call gives back, when it is a boolean (step 24) *)
Definition boolf (g : sig) : rtq (sr g) (sq g) -> bool :=
  match sq g as q return rtq (sr g) q -> bool with Some KBool => fun x => x | _ => fun _ => false end.

(** a call given a whole number-and-memory pair for the last number and the memory (step 44): the function applied to the pair;
    its number and its memory after it *)
Definition callfp (g : sig) : ftype g -> list nat -> list val -> (i63 * mem) -> rtq (sr g) (sq g) :=
  match g as g0 return ftype g0 -> list nat -> list val -> (i63 * mem) -> rtq (sr g0) (sq g0) with
  | mksig9 x k m r w q b v p =>
      if (if p then m else false) as p0 return ctype x (if p0 then ntypeTP k (rtq r q) else ntypeT k m (rtq r q)) -> list nat -> list val -> (i63 * mem) -> rtq r q then
        fun h cvs vs pr => appnTPP k (rtq r q) (appc x (ntypeTP k (rtq r q)) h cvs) vs pr
      else fun h cvs vs pr => appnT k m (rtq r q) (appc x (ntypeT k m (rtq r q)) h cvs) (vs ++ [VNum (fst pr)]) (snd pr)
  end.
Definition callnp (g : sig) (h : ftype g) (cvs : list nat) (vs : list val) (pr : i63 * mem) : i63 :=
  (match sq g as q return rtq (sr g) q -> i63 with
   | Some (KRec ri) => fun x => hd 0%uint63 (relim (RO ri) x (fun l => l))
   | Some KBool => b2i
   | Some KNum => fun x => fst x
   | None => if sr g as r return rty r -> i63 then fun _ => 0%uint63 else fun x => x
   end) (callfp g h cvs vs pr).
Definition callmp (g : sig) (h : ftype g) (cvs : list nat) (vs : list val) (pr : i63 * mem) : mem :=
  (match sq g as q return rtq (sr g) q -> mem with
   | Some (KRec ri) => fun x => wslot O (tl (relim (RO ri) x (fun l => l))) (snd pr)
   | Some KBool => fun _ => snd pr
   | Some KNum => fun x => snd x
   | None => if sr g as r return rty r -> mem then fun x => x else fun _ => snd pr
   end) (callfp g h cvs vs pr).

(** the number and the memory a call gives back, when it gives back both (step 26) *)
Definition pvf (g : sig) : rtq (sr g) (sq g) -> (i63 * mem)%type :=
  match sq g as q return rtq (sr g) q -> (i63 * mem)%type with Some KNum => fun x => x | _ => fun _ => (0%uint63, dummy_mem) end.

(** a callee: its signature and its meaning *)
Definition callee := { g : sig & ftype g }.

Fixpoint denote_e (cs : list callee) (rec : list nat -> list val -> mem -> i63) (cenv : list nat) (benv : list bool) (renv : list val)
  (env : list i63) (s : mem) (e : sexp) {struct e} : i63 :=
  match e with
  | SVar i => nth i env 0%uint63
  | SInt n => n
  | SOp o a b => binop_sem o (denote_e cs rec cenv benv renv env s a) (denote_e cs rec cenv benv renv env s b)
  | SIf c a b t f => if cmp_sem c (denote_e cs rec cenv benv renv env s a) (denote_e cs rec cenv benv renv env s b)
                     then denote_e cs rec cenv benv renv env s t else denote_e cs rec cenv benv renv env s f
  | SLet e1 e2 => let x := denote_e cs rec cenv benv renv env s e1 in denote_e cs rec cenv benv renv (x :: env) s e2
  | SRd h i => KQ.KQRun.rd (denote_e cs rec cenv benv renv env s h) (denote_e cs rec cenv benv renv env s i) s
  | SRec ccs args => rec (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s
  | SCall f ccs args =>
      match nth_error cs f with
      | Some (existT _ g h) => calln g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s
      | None => 0%uint63
      end
  | SMatch c e0 e1 =>
      match nth c cenv O with O => denote_e cs rec cenv benv renv env s e0 | S p => denote_e cs rec (p :: cenv) benv renv env s e1 end
  | SIfB b t f => if denote_b cs rec cenv benv renv env s b then denote_e cs rec cenv benv renv env s t else denote_e cs rec cenv benv renv env s f
  | SLetB b e => let x := denote_b cs rec cenv benv renv env s b in denote_e cs rec cenv (x :: benv) renv env s e
  | SRd32 h i => KQ.KQRun.rd32 (denote_e cs rec cenv benv renv env s h) (denote_e cs rec cenv benv renv env s i) s
  | SLetC c e => let w := denote_c cs rec cenv benv renv env s c in denote_e cs rec (w :: cenv) benv renv env s e
  | SFld i j => rmatch (nth i renv (VNum 0%uint63)) (fun l => nth j l 0%uint63)
  | SLetR x e => let w := denote_r cs rec cenv benv renv env s x in denote_e cs rec cenv benv (w :: renv) env s e
  | SMatchR x e => rmatch (denote_r cs rec cenv benv renv env s x) (fun l => denote_e cs rec cenv benv renv (rev l ++ env) s e)
  | SSplitR sj x e => rsplit (denote_r cs rec cenv benv renv env s x) (fun l rs => denote_e cs rec cenv benv (rev rs ++ renv) (rev l ++ env) s e)
  | SHwf o args => hwf_sem o (vnums (denote_es cs rec cenv benv renv env s args))
  | SSize h => KQ.KQRun.kq_size (denote_e cs rec cenv benv renv env s h) s
  | SRd8 h i => KQ.KQRun.rd8 (denote_e cs rec cenv benv renv env s h) (denote_e cs rec cenv benv renv env s i) s
  end
with denote_es (cs : list callee) (rec : list nat -> list val -> mem -> i63) (cenv : list nat) (benv : list bool) (renv : list val)
  (env : list i63) (s : mem) (es : sexps) {struct es} : list val :=
  match es with
  | SNil => []
  | SCons e r => VNum (denote_e cs rec cenv benv renv env s e) :: denote_es cs rec cenv benv renv env s r
  | SConsB b r => VBool (denote_b cs rec cenv benv renv env s b) :: denote_es cs rec cenv benv renv env s r
  | SConsR x r => denote_r cs rec cenv benv renv env s x :: denote_es cs rec cenv benv renv env s r
  end
with denote_c (cs : list callee) (rec : list nat -> list val -> mem -> i63) (cenv : list nat) (benv : list bool) (renv : list val)
  (env : list i63) (s : mem) (c : scnt) {struct c} : nat :=
  match c with
  | CVar i => nth i cenv O
  | CO => O
  | CS c => S (denote_c cs rec cenv benv renv env s c)
  | CNat e => KQ.KQRun.kq_nat (denote_e cs rec cenv benv renv env s e)
  | CPred c => Nat.pred (denote_c cs rec cenv benv renv env s c)
  | CAdd a b => (denote_c cs rec cenv benv renv env s a + denote_c cs rec cenv benv renv env s b)%nat
  end
with denote_cs (cs : list callee) (rec : list nat -> list val -> mem -> i63) (cenv : list nat) (benv : list bool) (renv : list val)
  (env : list i63) (s : mem) (ccs : scnts) {struct ccs} : list nat :=
  match ccs with
  | CNil => []
  | CCons c r => denote_c cs rec cenv benv renv env s c :: denote_cs cs rec cenv benv renv env s r
  end
with denote_b (cs : list callee) (rec : list nat -> list val -> mem -> i63) (cenv : list nat) (benv : list bool) (renv : list val)
  (env : list i63) (s : mem) (b : sbool) {struct b} : bool :=
  match b with
  | BCmp c x y => cmp_sem c (denote_e cs rec cenv benv renv env s x) (denote_e cs rec cenv benv renv env s y)
  | BVar i => nth i benv false
  | BTrue => true
  | BFalse => false
  | BAnd x y => andb (denote_b cs rec cenv benv renv env s x) (denote_b cs rec cenv benv renv env s y)
  | BOr x y => orb (denote_b cs rec cenv benv renv env s x) (denote_b cs rec cenv benv renv env s y)
  | BNot x => negb (denote_b cs rec cenv benv renv env s x)
  | BIfCmp c a b x y => if cmp_sem c (denote_e cs rec cenv benv renv env s a) (denote_e cs rec cenv benv renv env s b)
                        then denote_b cs rec cenv benv renv env s x else denote_b cs rec cenv benv renv env s y
  | BMatchCnt c x0 x1 => match nth c cenv O with
                         | O => denote_b cs rec cenv benv renv env s x0
                         | S p => denote_b cs rec (p :: cenv) benv renv env s x1
                         end
  | BCall f ccs args =>
      match nth_error cs f with
      | Some (existT _ g h) => boolf g (callf g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s)
      | None => false
      end
  | BCmpC c a b => cmpn c (denote_c cs rec cenv benv renv env s a) (denote_c cs rec cenv benv renv env s b)
  | BxIfB b x y => if denote_b cs rec cenv benv renv env s b then denote_b cs rec cenv benv renv env s x else denote_b cs rec cenv benv renv env s y
  | BxLet e x => let v := denote_e cs rec cenv benv renv env s e in denote_b cs rec cenv benv renv (v :: env) s x
  | BxLetB b x => let c := denote_b cs rec cenv benv renv env s b in denote_b cs rec cenv (c :: benv) renv env s x
  | BxLetC c x => let w := denote_c cs rec cenv benv renv env s c in denote_b cs rec (w :: cenv) benv renv env s x
  | BxLetR r x => let w := denote_r cs rec cenv benv renv env s r in denote_b cs rec cenv benv (w :: renv) env s x
  | BxMatchR r x => rmatch (denote_r cs rec cenv benv renv env s r) (fun l => denote_b cs rec cenv benv renv (rev l ++ env) s x)
  | BxSplitR sj r x => rsplit (denote_r cs rec cenv benv renv env s r) (fun l rs => denote_b cs rec cenv benv (rev rs ++ renv) (rev l ++ env) s x)
  end
with denote_r (cs : list callee) (rec : list nat -> list val -> mem -> i63) (cenv : list nat) (benv : list bool) (renv : list val)
  (env : list i63) (s : mem) (x : srec) {struct x} : val :=
  match x with
  | RVar i => nth i renv (VNum 0%uint63)
  | RMk ri es => VRec ri (rmk (RO ri) (vnums (denote_es cs rec cenv benv renv env s es)))
  | RCall _ f ccs args =>
      match nth_error cs f with
      | Some (existT _ g h) => vrec_of g (callf g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s)
      | None => VNum 0%uint63
      end
  | RW64 ri o a b =>
      let w := KQ.KQRun.w64_op o (rmatch (denote_r cs rec cenv benv renv env s a) u64_of_l) (rmatch (denote_r cs rec cenv benv renv env s b) u64_of_l) in
      VRec ri (rmk (RO ri) [KQ.KQRun.w_lo w; KQ.KQRun.w_hi w])
  | RLet e x => let v := denote_e cs rec cenv benv renv env s e in denote_r cs rec cenv benv renv (v :: env) s x
  | RLetR y x => let w := denote_r cs rec cenv benv renv env s y in denote_r cs rec cenv benv (w :: renv) env s x
  (* the test and the match inside the record value: taken apart, it is the user's match on the user's test *)
  | RIf ri c a b x y => VRec ri (if cmp_sem c (denote_e cs rec cenv benv renv env s a) (denote_e cs rec cenv benv renv env s b)
                                 then to_rt ri (denote_r cs rec cenv benv renv env s x) else to_rt ri (denote_r cs rec cenv benv renv env s y))
  | RMatchR ri x y => VRec ri (rmatch (denote_r cs rec cenv benv renv env s x)
                                      (fun l => to_rt ri (denote_r cs rec cenv benv renv (rev l ++ env) s y)))
  | RIfB ri b x y => VRec ri (if denote_b cs rec cenv benv renv env s b
                              then to_rt ri (denote_r cs rec cenv benv renv env s x) else to_rt ri (denote_r cs rec cenv benv renv env s y))
  | RLetB b x => let c := denote_b cs rec cenv benv renv env s b in denote_r cs rec cenv (c :: benv) renv env s x
  | RLetC c x => let w := denote_c cs rec cenv benv renv env s c in denote_r cs rec (w :: cenv) benv renv env s x
  | RMatchCnt ri c x y => VRec ri (match nth c cenv O with
                                   | O => to_rt ri (denote_r cs rec cenv benv renv env s x)
                                   | S p => to_rt ri (denote_r cs rec (p :: cenv) benv renv env s y)
                                   end)
  | RSplitR ri _ x y => VRec ri (rsplit (denote_r cs rec cenv benv renv env s x)
                                        (fun l rs => to_rt ri (denote_r cs rec cenv benv (rev rs ++ renv) (rev l ++ env) s y)))
  | RMkR ri ns rs => VRec ri (RB ri (vnums (denote_es cs rec cenv benv renv env s ns)) (vrecs_t (denote_es cs rec cenv benv renv env s rs)))
  end.

Definition dpair : list nat -> list val -> mem -> (i63 * mem)%type := fun _ _ s => (0%uint63, s).

Fixpoint denote_m (cs : list callee) (rec : list nat -> list val -> mem -> i63) (recm : list nat -> list val -> mem -> mem)
  (cenv : list nat) (benv : list bool) (renv : list val) (env : list i63) (s : mem) (m : smem) {struct m} : mem :=
  match m with
  | MCur => s
  | MUpd h i v m => KQ.KQRun.upd (denote_e cs rec cenv benv renv env s h) (denote_e cs rec cenv benv renv env s i)
                                 (denote_e cs rec cenv benv renv env s v) (denote_m cs rec recm cenv benv renv env s m)
  | MLet e m => let x := denote_e cs rec cenv benv renv env s e in denote_m cs rec recm cenv benv renv (x :: env) s m
  | MLetM m1 m2 => let s2 := denote_m cs rec recm cenv benv renv env s m1 in denote_m cs rec recm cenv benv renv env s2 m2
  | MIf c a b m1 m2 => if cmp_sem c (denote_e cs rec cenv benv renv env s a) (denote_e cs rec cenv benv renv env s b)
                       then denote_m cs rec recm cenv benv renv env s m1 else denote_m cs rec recm cenv benv renv env s m2
  | MRec ccs args m => recm (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args)
                            (denote_m cs rec recm cenv benv renv env s m)
  | MCall f ccs args m =>
      match nth_error cs f with
      | Some (existT _ g h) => callm g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args)
                                     (denote_m cs rec recm cenv benv renv env s m)
      | None => s
      end
  | MMatch c m0 m1 =>
      match nth c cenv O with
      | O => denote_m cs rec recm cenv benv renv env s m0
      | S p => denote_m cs rec recm (p :: cenv) benv renv env s m1
      end
  | MIfB b m1 m2 => if denote_b cs rec cenv benv renv env s b then denote_m cs rec recm cenv benv renv env s m1
                    else denote_m cs rec recm cenv benv renv env s m2
  | MLetB b m => let x := denote_b cs rec cenv benv renv env s b in denote_m cs rec recm cenv (x :: benv) renv env s m
  | MUpd32 h i v m => KQ.KQRun.upd32 (denote_e cs rec cenv benv renv env s h) (denote_e cs rec cenv benv renv env s i)
                                     (denote_e cs rec cenv benv renv env s v) (denote_m cs rec recm cenv benv renv env s m)
  | MLetC c m => let w := denote_c cs rec cenv benv renv env s c in denote_m cs rec recm (w :: cenv) benv renv env s m
  | MHw o args m => hw_sem o (vnums (denote_es cs rec cenv benv renv env s args)) (denote_m cs rec recm cenv benv renv env s m)
  | MUpd8 h i v m => KQ.KQRun.upd8 (denote_e cs rec cenv benv renv env s h) (denote_e cs rec cenv benv renv env s i)
                                   (denote_e cs rec cenv benv renv env s v) (denote_m cs rec recm cenv benv renv env s m)
  | MLetR x m => let w := denote_r cs rec cenv benv renv env s x in denote_m cs rec recm cenv benv (w :: renv) env s m
  | MMatchR x m => rmatch (denote_r cs rec cenv benv renv env s x) (fun l => denote_m cs rec recm cenv benv renv (rev l ++ env) s m)
  | MSplitR sj x m => rsplit (denote_r cs rec cenv benv renv env s x) (fun l rs => denote_m cs rec recm cenv benv (rev rs ++ renv) (rev l ++ env) s m)
  | MMatchP p m => let '(v, s2) := denote_pv cs rec recm dpair cenv benv renv env s p in denote_m cs rec recm cenv benv renv (v :: env) s2 m
  | MLetP p m => let w := denote_pv cs rec recm dpair cenv benv renv env s p in denote_m cs rec recm cenv benv renv (fst w :: env) (snd w) m
  | MCallP f ccs args p =>
      match nth_error cs f with
      | Some (existT _ g h) => callmp g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args)
                                      (denote_pv cs rec recm dpair cenv benv renv env s p)
      | None => s
      end
  end
(* a pair's meaning: the pair itself, [recp] the recursive call's *)
with denote_pv (cs : list callee) (rec : list nat -> list val -> mem -> i63) (recm : list nat -> list val -> mem -> mem)
  (recp : list nat -> list val -> mem -> (i63 * mem)%type) (cenv : list nat) (benv : list bool) (renv : list val) (env : list i63)
  (s : mem) (p : spv) {struct p} : (i63 * mem)%type :=
  match p with
  | PvMk e m => (denote_e cs rec cenv benv renv env s e, denote_m cs rec recm cenv benv renv env s m)
  | PvCall f ccs args m =>
      match nth_error cs f with
      | Some (existT _ g h) => pvf g (callf g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args)
                                             (denote_m cs rec recm cenv benv renv env s m))
      | None => (0%uint63, s)
      end
  | PvRec ccs args m => recp (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args)
                             (denote_m cs rec recm cenv benv renv env s m)
  | PvLet e p => let v := denote_e cs rec cenv benv renv env s e in denote_pv cs rec recm recp cenv benv renv (v :: env) s p
  | PvLetB c p => let v := denote_b cs rec cenv benv renv env s c in denote_pv cs rec recm recp cenv (v :: benv) renv env s p
  | PvLetC c p => let w := denote_c cs rec cenv benv renv env s c in denote_pv cs rec recm recp (w :: cenv) benv renv env s p
  | PvLetR x p => let w := denote_r cs rec cenv benv renv env s x in denote_pv cs rec recm recp cenv benv (w :: renv) env s p
  | PvMatchR x p => rmatch (denote_r cs rec cenv benv renv env s x) (fun l => denote_pv cs rec recm recp cenv benv renv (rev l ++ env) s p)
  | PvSplitR sj x p => rsplit (denote_r cs rec cenv benv renv env s x) (fun l rs => denote_pv cs rec recm recp cenv benv (rev rs ++ renv) (rev l ++ env) s p)
  | PvCallP f ccs args p =>
      match nth_error cs f with
      | Some (existT _ g h) => pvf g (callfp g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args)
                                             (denote_pv cs rec recm recp cenv benv renv env s p))
      | None => (0%uint63, s)
      end
  | PvLetM m p => let s2 := denote_m cs rec recm cenv benv renv env s m in denote_pv cs rec recm recp cenv benv renv env s2 p
  | PvIf c x y t f => if cmp_sem c (denote_e cs rec cenv benv renv env s x) (denote_e cs rec cenv benv renv env s y)
                      then denote_pv cs rec recm recp cenv benv renv env s t else denote_pv cs rec recm recp cenv benv renv env s f
  | PvIfB c t f => if denote_b cs rec cenv benv renv env s c then denote_pv cs rec recm recp cenv benv renv env s t
                   else denote_pv cs rec recm recp cenv benv renv env s f
  | PvMatch c p0 p1 => match nth c cenv O with O => denote_pv cs rec recm recp cenv benv renv env s p0
                                             | S n => denote_pv cs rec recm recp (n :: cenv) benv renv env s p1 end
  | PvMatchP p q => let '(x, s2) := denote_pv cs rec recm recp cenv benv renv env s p in
                    denote_pv cs rec recm recp cenv benv renv (x :: env) s2 q
  end.

(** a number made after memories: the memories first ([let s2 := m in ..], each the newest in what follows), then the number
    read from the newest one; lets of numbers and booleans and tests on the way; or, at the end, the recursive call or a call
    of a number function that writes, given a memory made from the newest one (its numbers worked out on the memory before) *)



Inductive sx : Type :=
| XRet (e : sexp)                    (* the number, from the newest memory *)
| XLetM (m : smem) (x : sx)          (* let s2 := m in x *)
| XLet (e : sexp) (x : sx)           (* let v := e in x *)
| XLetB (b : sbool) (x : sx)         (* let v := b in x, v a boolean *)
| XIf (c : cmpop) (a b : sexp) (x1 x2 : sx)
| XIfB (b : sbool) (x1 x2 : sx)
| XMatch (c : nat) (x0 x1 : sx)
| XLetC (c : scnt) (x : sx)
| XRec (cs : scnts) (args : sexps) (m : smem)            (* the function itself (it writes), on the memory m *)
| XCall (f : nat) (cs : scnts) (args : sexps) (m : smem)   (* function f, a number function that writes, on the memory m *)
| XLetR (r : srec) (x : sx)          (* let w := r in x, w a record *)
| XMatchR (r : srec) (x : sx)        (* let '(a, b, ..) := r in x *)
| XMatchP (p : spv) (x : sx)         (* let '(v, s2) := p in x: v the nearest number, s2 the newest memory (step 26) *)
| XLetP (p : spv) (x : sx)           (* let w := p in x, read through fst w (the nearest number) and snd w (the newest memory) *)
| XSplitR (ri : nat) (r : srec) (x : sx)    (* r, of type ri, taken apart one level (step 43) *)
| XCallP (f : nat) (cs : scnts) (args : sexps) (p : spv)    (* function f, a number function, given the pair p (step 44) *)
(* (step 47) a call whose result, a number or a boolean ([bq]), the nearest of its kind in x, x run after it: of function f on
   the memory m; of the function itself; of function f given the pair p.  After a call that writes, x reads no memory *)
| XBind (bq : bool) (f : nat) (cs : scnts) (args : sexps) (m : smem) (x : sx)
| XBindR (cs : scnts) (args : sexps) (m : smem) (x : sx)
| XBindP (bq : bool) (f : nat) (cs : scnts) (args : sexps) (p : spv) (x : sx).

(** a call's result given to what follows it (step 47): a number to [kn], a boolean to [kb] *)
Definition xres (g : sig) : rtq (sr g) (sq g) -> (i63 -> i63) -> (bool -> i63) -> i63 :=
  match sq g as q return rtq (sr g) q -> (i63 -> i63) -> (bool -> i63) -> i63 with
  | Some KBool => fun b _ kb => kb b
  | None => if sr g as r return rtq r None -> (i63 -> i63) -> (bool -> i63) -> i63 then fun _ _ _ => 0%uint63 else fun v kn _ => kn v
  | _ => fun _ _ _ => 0%uint63
  end.

Fixpoint denote_x (cs : list callee) (rec : list nat -> list val -> mem -> i63) (recm : list nat -> list val -> mem -> mem)
  (recx : list nat -> list val -> mem -> i63) (cenv : list nat) (benv : list bool) (renv : list val) (env : list i63) (s : mem) (x : sx) {struct x} : i63 :=
  match x with
  | XRet e => denote_e cs rec cenv benv renv env s e
  | XLetM m x => let s2 := denote_m cs rec recm cenv benv renv env s m in denote_x cs rec recm recx cenv benv renv env s2 x
  | XLet e x => let v := denote_e cs rec cenv benv renv env s e in denote_x cs rec recm recx cenv benv renv (v :: env) s x
  | XLetB b x => let v := denote_b cs rec cenv benv renv env s b in denote_x cs rec recm recx cenv (v :: benv) renv env s x
  | XIf c a b x1 x2 => if cmp_sem c (denote_e cs rec cenv benv renv env s a) (denote_e cs rec cenv benv renv env s b)
                       then denote_x cs rec recm recx cenv benv renv env s x1 else denote_x cs rec recm recx cenv benv renv env s x2
  | XIfB b x1 x2 => if denote_b cs rec cenv benv renv env s b then denote_x cs rec recm recx cenv benv renv env s x1
                    else denote_x cs rec recm recx cenv benv renv env s x2
  | XMatch c x0 x1 => match nth c cenv O with O => denote_x cs rec recm recx cenv benv renv env s x0
                                            | S p => denote_x cs rec recm recx (p :: cenv) benv renv env s x1 end
  | XLetC c x => let w := denote_c cs rec cenv benv renv env s c in denote_x cs rec recm recx (w :: cenv) benv renv env s x
  | XRec ccs args m => recx (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args)
                            (denote_m cs rec recm cenv benv renv env s m)
  | XCall f ccs args m =>
      match nth_error cs f with
      | Some (existT _ g h) => calln g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args)
                                     (denote_m cs rec recm cenv benv renv env s m)
      | None => 0%uint63
      end
  | XLetR r x => let w := denote_r cs rec cenv benv renv env s r in denote_x cs rec recm recx cenv benv (w :: renv) env s x
  | XMatchR r x => rmatch (denote_r cs rec cenv benv renv env s r) (fun l => denote_x cs rec recm recx cenv benv renv (rev l ++ env) s x)
  | XSplitR sj r x => rsplit (denote_r cs rec cenv benv renv env s r) (fun l rs => denote_x cs rec recm recx cenv benv (rev rs ++ renv) (rev l ++ env) s x)
  | XCallP f ccs args p =>
      match nth_error cs f with
      | Some (existT _ g h) => callnp g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args)
                                      (denote_pv cs rec recm dpair cenv benv renv env s p)
      | None => 0%uint63
      end
  | XMatchP p x => let '(v, s2) := denote_pv cs rec recm dpair cenv benv renv env s p in denote_x cs rec recm recx cenv benv renv (v :: env) s2 x
  | XBind _ f ccs args m x =>
      match nth_error cs f with
      | Some (existT _ g h) =>
          let s2 := denote_m cs rec recm cenv benv renv env s m in
          xres g (callf g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s2)
               (fun v => denote_x cs rec recm recx cenv benv renv (v :: env) s2 x) (fun b => denote_x cs rec recm recx cenv (b :: benv) renv env s2 x)
      | None => 0%uint63
      end
  | XBindR ccs args m x =>
      let s2 := denote_m cs rec recm cenv benv renv env s m in
      denote_x cs rec recm recx cenv benv renv (recx (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s2 :: env) s2 x
  | XBindP _ f ccs args p x =>
      match nth_error cs f with
      | Some (existT _ g h) =>
          let pr := denote_pv cs rec recm dpair cenv benv renv env s p in
          xres g (callfp g h (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) pr)
               (fun v => denote_x cs rec recm recx cenv benv renv (v :: env) (snd pr) x) (fun b => denote_x cs rec recm recx cenv (b :: benv) renv env (snd pr) x)
      | None => 0%uint63
      end
  | XLetP p x => let w := denote_pv cs rec recm dpair cenv benv renv env s p in denote_x cs rec recm recx cenv benv renv (fst w :: env) (snd w) x
  end.

(** a record given back: the body of a function whose result is a record of type [ri] -- the record at the end (built, or
    given by a call), the function itself at the end (a loop), the function itself taken apart or bound by a let before
    the end, and the lets, tests and counter match of the other bodies *)
Inductive sbr : Type :=
| BRet (x : srec)                                  (* the record x *)
| BRec (cs : scnts) (args : sexps)                 (* the function itself, at the end *)
| BMatchRec (cs : scnts) (args : sexps) (b : sbr)  (* the function itself taken apart: its fields are the nearest numbers in b *)
| BLetRec (cs : scnts) (args : sexps) (b : sbr)    (* let w := the function itself in b, w the nearest record variable *)
| BLet (e : sexp) (b : sbr)
| BLetB (c : sbool) (b : sbr)
| BLetC (c : scnt) (b : sbr)
| BLetR (x : srec) (b : sbr)
| BMatchR (x : srec) (b : sbr)
| BIf (c : cmpop) (x y : sexp) (t f : sbr)
| BIfB (c : sbool) (t f : sbr)
| BMatch (c : nat) (b0 b1 : sbr)
| BSplitR (rj : nat) (x : srec) (b : sbr).   (* x, of type rj, taken apart one level (step 43) *)

(** its meaning: the record value itself, [recr] the recursive call's (so a match on the recursive call is the user's) *)
Fixpoint denote_br (cs : list callee) (rec : list nat -> list val -> mem -> i63) (ri : nat) (recr : list nat -> list val -> mem -> RT ri)
  (cenv : list nat) (benv : list bool) (renv : list val) (env : list i63) (s : mem) (b : sbr) {struct b} : RT ri :=
  match b with
  | BRet x => to_rt ri (denote_r cs rec cenv benv renv env s x)
  | BRec ccs args => recr (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s
  | BMatchRec ccs args b => relim (RO ri) (recr (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s)
                                  (fun l => denote_br cs rec ri recr cenv benv renv (rev l ++ env) s b)
  | BLetRec ccs args b => let w := recr (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s in
                          denote_br cs rec ri recr cenv benv (VRec ri w :: renv) env s b
  | BLet e b => let v := denote_e cs rec cenv benv renv env s e in denote_br cs rec ri recr cenv benv renv (v :: env) s b
  | BLetB c b => let v := denote_b cs rec cenv benv renv env s c in denote_br cs rec ri recr cenv (v :: benv) renv env s b
  | BLetC c b => let w := denote_c cs rec cenv benv renv env s c in denote_br cs rec ri recr (w :: cenv) benv renv env s b
  | BLetR x b => let w := denote_r cs rec cenv benv renv env s x in denote_br cs rec ri recr cenv benv (w :: renv) env s b
  | BMatchR x b => rmatch (denote_r cs rec cenv benv renv env s x) (fun l => denote_br cs rec ri recr cenv benv renv (rev l ++ env) s b)
  | BSplitR sj x b => rsplit (denote_r cs rec cenv benv renv env s x) (fun l rs => denote_br cs rec ri recr cenv benv (rev rs ++ renv) (rev l ++ env) s b)
  | BIf c x y t f => if cmp_sem c (denote_e cs rec cenv benv renv env s x) (denote_e cs rec cenv benv renv env s y)
                     then denote_br cs rec ri recr cenv benv renv env s t else denote_br cs rec ri recr cenv benv renv env s f
  | BIfB c t f => if denote_b cs rec cenv benv renv env s c then denote_br cs rec ri recr cenv benv renv env s t
                  else denote_br cs rec ri recr cenv benv renv env s f
  | BMatch c b0 b1 => match nth c cenv O with O => denote_br cs rec ri recr cenv benv renv env s b0
                                            | S p => denote_br cs rec ri recr (p :: cenv) benv renv env s b1 end
  end.

(** a function's body giving back a boolean (step 24): a boolean at the end, the function itself at the end (a loop), its
    negation at the end (the call, then [lxor 1]), and the lets, tests and counter match of the other tail sorts *)
Inductive sbb : Type :=
| BbRet (b : sbool)                                (* the boolean b *)
| BbRec (cs : scnts) (args : sexps)                (* the function itself, at the end *)
| BbNotRec (cs : scnts) (args : sexps)             (* negb of the function itself, at the end *)
| BbLet (e : sexp) (b : sbb)
| BbLetB (c : sbool) (b : sbb)
| BbLetC (c : scnt) (b : sbb)
| BbLetR (x : srec) (b : sbb)
| BbMatchR (x : srec) (b : sbb)
| BbIf (c : cmpop) (x y : sexp) (t f : sbb)
| BbIfB (c : sbool) (t f : sbb)
| BbMatch (c : nat) (b0 b1 : sbb)
| BbSplitR (ri : nat) (x : srec) (b : sbb).   (* x, of type ri, taken apart one level (step 43) *)

(** its meaning: the boolean itself, [recb] the recursive call's *)
Fixpoint denote_bb (cs : list callee) (rec : list nat -> list val -> mem -> i63) (recb : list nat -> list val -> mem -> bool)
  (cenv : list nat) (benv : list bool) (renv : list val) (env : list i63) (s : mem) (b : sbb) {struct b} : bool :=
  match b with
  | BbRet x => denote_b cs rec cenv benv renv env s x
  | BbRec ccs args => recb (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s
  | BbNotRec ccs args => negb (recb (denote_cs cs rec cenv benv renv env s ccs) (denote_es cs rec cenv benv renv env s args) s)
  | BbLet e b => let v := denote_e cs rec cenv benv renv env s e in denote_bb cs rec recb cenv benv renv (v :: env) s b
  | BbLetB c b => let v := denote_b cs rec cenv benv renv env s c in denote_bb cs rec recb cenv (v :: benv) renv env s b
  | BbLetC c b => let w := denote_c cs rec cenv benv renv env s c in denote_bb cs rec recb (w :: cenv) benv renv env s b
  | BbLetR x b => let w := denote_r cs rec cenv benv renv env s x in denote_bb cs rec recb cenv benv (w :: renv) env s b
  | BbMatchR x b => rmatch (denote_r cs rec cenv benv renv env s x) (fun l => denote_bb cs rec recb cenv benv renv (rev l ++ env) s b)
  | BbSplitR sj x b => rsplit (denote_r cs rec cenv benv renv env s x) (fun l rs => denote_bb cs rec recb cenv benv (rev rs ++ renv) (rev l ++ env) s b)
  | BbIf c x y t f => if cmp_sem c (denote_e cs rec cenv benv renv env s x) (denote_e cs rec cenv benv renv env s y)
                      then denote_bb cs rec recb cenv benv renv env s t else denote_bb cs rec recb cenv benv renv env s f
  | BbIfB c t f => if denote_b cs rec cenv benv renv env s c then denote_bb cs rec recb cenv benv renv env s t
                   else denote_bb cs rec recb cenv benv renv env s f
  | BbMatch c b0 b1 => match nth c cenv O with O => denote_bb cs rec recb cenv benv renv env s b0
                                             | S p => denote_bb cs rec recb (p :: cenv) benv renv env s b1 end
  end.

(** a function's body: a number, recursive on the first counter ([e0] when it is 0, [e1] otherwise) or plain; or a memory,
    the same; or a number made after memories, the same *)
Inductive fbody := FRec (e0 e1 : sexp) | FPlain (e : sexp) | FRecM (m0 m1 : smem) | FPlainM (m : smem) | FPlainX (x : sx)
                 | FRecX (x0 x1 : sx) | FRecR (b0 b1 : sbr) | FPlainR (b : sbr) | FRecB (b0 b1 : sbb) | FPlainB (b : sbb) | FRecP (p0 p1 : spv) | FPlainP (p : spv).

(** the parts of a recursive body (for the statement of a function given as a term, [compile_f_okr]) *)
Definition fr0 (b : fbody) : sexp := match b with FRec e0 _ => e0 | _ => SInt 0%uint63 end.
Definition fr1 (b : fbody) : sexp := match b with FRec _ e1 => e1 | _ => SInt 0%uint63 end.
Definition fm0 (b : fbody) : smem := match b with FRecM m0 _ => m0 | _ => MCur end.
Definition fm1 (b : fbody) : smem := match b with FRecM _ m1 => m1 | _ => MCur end.
Definition fx0 (b : fbody) : sx := match b with FRecX x0 _ => x0 | _ => XRet (SInt 0%uint63) end.
Definition fx1 (b : fbody) : sx := match b with FRecX _ x1 => x1 | _ => XRet (SInt 0%uint63) end.
(* the parts of a boolean's, a record's, a number-and-memory's recursive body (step 41: their copies' theorems) *)
Definition fbb0 (b : fbody) : sbb := match b with FRecB b0 _ => b0 | _ => BbRet BFalse end.
Definition fbb1 (b : fbody) : sbb := match b with FRecB _ b1 => b1 | _ => BbRet BFalse end.
Definition fbr0 (b : fbody) : sbr := match b with FRecR b0 _ => b0 | _ => BRet (RVar 0) end.
Definition fbr1 (b : fbody) : sbr := match b with FRecR _ b1 => b1 | _ => BRet (RVar 0) end.
Definition fpv0 (b : fbody) : spv := match b with FRecP p0 _ => p0 | _ => PvMk (SInt 0%uint63) MCur end.
Definition fpv1 (b : fbody) : spv := match b with FRecP _ p1 => p1 | _ => PvMk (SInt 0%uint63) MCur end.

Definition dnum : list nat -> list val -> mem -> i63 := fun _ _ _ => 0%uint63.
Definition dmem : list nat -> list val -> mem -> mem := fun _ _ s => s.
Definition drec (ri : nat) : list nat -> list val -> mem -> RT ri := fun _ _ _ => Rd ri.
Definition dbool : list nat -> list val -> mem -> bool := fun _ _ _ => false.

(* the signature on the two components *)
Definition fcomp (g : sig) : sig := mksig8 (sn g) (sk g) (sm g) (sr g) (sw g) (sq g) (sb g) (sv g).
Definition denote_f0 (cs : list callee) (g : sig) (b : fbody) : ftype (fcomp g) :=
  match g as g0 return ftype (fcomp g0) with
  | mksig9 x k m r w q b0 sv0 _ =>
      match q as q0 return ftype (mksig8 x k m r w q0 b0 sv0) with
      | Some KBool =>
        match x as x0 return ftype (mksig8 x0 k m r w (Some KBool) b0 sv0) with
        | O => match b with
               | FPlainB bb => absnT k m bool (fun env benv renv s => denote_bb cs dnum dbool [] benv renv env s bb)
               | _ => absnT k m bool (fun _ _ _ _ => false)
               end
        | S x' =>
            match b with
            | FRecB b0 b1 =>
                fix go (n : nat) : ctype x' (ntypeT k m bool) :=
                  absc x' _ (fun cenv => absnT k m bool (fun env benv renv s =>
                    match n with
                    | O => denote_bb cs dnum dbool (cenv ++ [n]) benv renv env s b0
                    | S n' => denote_bb cs dnum (fun cvs args s' => appnT k m bool (appc x' _ (go n') cvs) args s')
                                        (n' :: cenv ++ [n]) benv renv env s b1
                    end))
            | FPlainB bb => fun n => absc x' _ (fun cenv => absnT k m bool (fun env benv renv s =>
                              denote_bb cs dnum dbool (cenv ++ [n]) benv renv env s bb))
            | _ => fun _ => absc x' _ (fun _ => absnT k m bool (fun _ _ _ _ => false))
            end
        end
      | Some KNum =>
        match x as x0 return ftype (mksig8 x0 k m r w (Some KNum) b0 sv0) with
        | O => match b with
               | FPlainP pp => absnT k m (i63 * mem) (fun env benv renv s => denote_pv cs dnum dmem dpair [] benv renv env s pp)
               | _ => absnT k m (i63 * mem) (fun _ _ _ s => (0%uint63, s))
               end
        | S x' =>
            match b with
            | FRecP p0 p1 =>
                fix go (n : nat) : ctype x' (ntypeT k m (i63 * mem)) :=
                  absc x' _ (fun cenv => absnT k m (i63 * mem) (fun env benv renv s =>
                    match n with
                    | O => denote_pv cs dnum dmem dpair (cenv ++ [n]) benv renv env s p0
                    | S n' => denote_pv cs dnum dmem (fun cvs args s' => appnT k m (i63 * mem) (appc x' _ (go n') cvs) args s')
                                        (n' :: cenv ++ [n]) benv renv env s p1
                    end))
            | FPlainP pp => fun n => absc x' _ (fun cenv => absnT k m (i63 * mem) (fun env benv renv s =>
                              denote_pv cs dnum dmem dpair (cenv ++ [n]) benv renv env s pp))
            | _ => fun _ => absc x' _ (fun _ => absnT k m (i63 * mem) (fun _ _ _ s => (0%uint63, s)))
            end
        end
      | Some (KRec ri) =>
        match x as x0 return ftype (mksig8 x0 k m r w (Some (KRec ri)) b0 sv0) with
        | O => match b with
               | FPlainR bb => absnT k m (RT ri) (fun env benv renv s => denote_br cs dnum ri (drec ri) [] benv renv env s bb)
               | _ => absnT k m (RT ri) (fun _ _ _ _ => Rd ri)
               end
        | S x' =>
            match b with
            | FRecR b0 b1 =>
                fix go (n : nat) : ctype x' (ntypeT k m (RT ri)) :=
                  absc x' _ (fun cenv => absnT k m (RT ri) (fun env benv renv s =>
                    match n with
                    | O => denote_br cs dnum ri (drec ri) (cenv ++ [n]) benv renv env s b0
                    | S n' => denote_br cs dnum ri (fun cvs args s' => appnT k m (RT ri) (appc x' _ (go n') cvs) args s')
                                        (n' :: cenv ++ [n]) benv renv env s b1
                    end))
            | FPlainR bb => fun n => absc x' _ (fun cenv => absnT k m (RT ri) (fun env benv renv s =>
                              denote_br cs dnum ri (drec ri) (cenv ++ [n]) benv renv env s bb))
            | _ => fun _ => absc x' _ (fun _ => absnT k m (RT ri) (fun _ _ _ _ => Rd ri))
            end
        end
      | None =>
      if r as r0 return ftype (mksig x k m r0 w None) then
        match x as x0 return ftype (mksig x0 k m true w None) with
        | O => match b with
               | FPlainM e => absn k m true (fun env benv renv s => denote_m cs dnum dmem [] benv renv env s e)
               | _ => absn k m true (fun _ _ _ s => s)
               end
        | S x' =>
            match b with
            | FRecM m0 m1 =>
                fix go (n : nat) : ctype x' (ntype k m true) :=
                  absc x' _ (fun cenv => absn k m true (fun env benv renv s =>
                    match n with
                    | O => denote_m cs dnum dmem (cenv ++ [n]) benv renv env s m0
                    | S n' => denote_m cs dnum (fun cvs args s' => appn k m true (appc x' _ (go n') cvs) args s')
                                       (n' :: cenv ++ [n]) benv renv env s m1
                    end))
            | FPlainM e => fun n => absc x' _ (fun cenv => absn k m true (fun env benv renv s => denote_m cs dnum dmem (cenv ++ [n]) benv renv env s e))
            | _ => fun _ => absc x' _ (fun _ => absn k m true (fun _ _ _ s => s))
            end
        end
      else
        match x as x0 return ftype (mksig x0 k m false w None) with
        | O => match b with
               | FPlain e => absn k m false (fun env benv renv s => denote_e cs dnum [] benv renv env s e)
               | FPlainX xx => absn k m false (fun env benv renv s => denote_x cs dnum dmem dnum [] benv renv env s xx)
               | _ => absn k m false (fun _ _ _ _ => 0%uint63)
               end
        | S x' =>
            match b with
            | FRec e0 e1 =>
                fix go (n : nat) : ctype x' (ntype k m false) :=
                  absc x' _ (fun cenv => absn k m false (fun env benv renv s =>
                    match n with
                    | O => denote_e cs dnum (cenv ++ [n]) benv renv env s e0
                    | S n' => denote_e cs (fun cvs args s' => appn k m false (appc x' _ (go n') cvs) args s')
                                       (n' :: cenv ++ [n]) benv renv env s e1
                    end))
            | FPlain e => fun n => absc x' _ (fun cenv => absn k m false (fun env benv renv s => denote_e cs dnum (cenv ++ [n]) benv renv env s e))
            | FPlainX xx => fun n => absc x' _ (fun cenv => absn k m false (fun env benv renv s => denote_x cs dnum dmem dnum (cenv ++ [n]) benv renv env s xx))
            | FRecX x0 x1 =>
                fix go (n : nat) : ctype x' (ntype k m false) :=
                  absc x' _ (fun cenv => absn k m false (fun env benv renv s =>
                    match n with
                    | O => denote_x cs dnum dmem dnum (cenv ++ [n]) benv renv env s x0
                    | S n' => denote_x cs dnum dmem (fun cvs args s' => appn k m false (appc x' _ (go n') cvs) args s')
                                       (n' :: cenv ++ [n]) benv renv env s x1
                    end))
            | _ => fun _ => absc x' _ (fun _ => absn k m false (fun _ _ _ _ => 0%uint63))
            end
        end
      end
  end.
(** a function's meaning: its body's, on the two components; with the pair (step 44), the function of the pair made of it *)
Definition denote_f (cs : list callee) (g : sig) (b : fbody) : ftype g :=
  match g as g0 return ftype g0 with
  | mksig9 x k m r w q b0 sv0 p =>
      if (if p then m else false) as p0 return ctype x (if p0 then ntypeTP k (rtq r q) else ntypeT k m (rtq r q)) then
        cmapT x _ _ (pairT k m (rtq r q)) (denote_f0 cs (mksig8 x k m r w q b0 sv0) b)
      else denote_f0 cs (mksig8 x k m r w q b0 sv0) b
  end.

(* ================================================================ compile *)
Definition cap60 : i63 := 1152921504606846976%uint63.

(** a choice between two numbers that are both worked out and one taken with a conditional move, no jump (the
    translator's [choice_ok], D17): arithmetic, variables, reads of the memory and such choices, at most three reads in the
    two numbers.  A choice with a call, a let or a match stays a jump; so does the end of a function (a loop's tests) *)
Fixpoint spec (e : sexp) : bool :=
  match e with
  | SVar _ | SInt _ | SFld _ _ => true
  | SOp _ a b | SRd a b | SRd32 a b => spec a && spec b
  | SIf _ a b t f => spec a && spec b && spec t && spec f
  | SIfB b t f => specb b && spec t && spec f
  | _ => false
  end
with specb (b : sbool) : bool :=
  match b with
  | BCmp _ x y => spec x && spec y
  | BVar _ | BTrue | BFalse => true
  | BAnd x y | BOr x y => specb x && specb y
  | BNot x => specb x
  | BIfCmp _ _ _ _ _ | BMatchCnt _ _ _ | BCall _ _ _ | BCmpC _ _ _ | BxIfB _ _ _ | BxLet _ _ | BxLetB _ _ | BxLetC _ _
  | BxLetR _ _ | BxMatchR _ _ | BxSplitR _ _ _ => false
  end.
Fixpoint nrd (e : sexp) : nat :=
  match e with
  | SRd a b | SRd32 a b => S (nrd a + nrd b)
  | SOp _ a b => nrd a + nrd b
  | SIf _ a b t f => nrd a + nrd b + nrd t + nrd f
  | SIfB b t f => nrdb b + nrd t + nrd f
  | _ => O
  end
with nrdb (b : sbool) : nat :=
  match b with
  | BCmp _ x y => nrd x + nrd y
  | BAnd x y | BOr x y => nrdb x + nrdb y
  | BNot x => nrdb x
  | _ => O
  end.
Definition choice_ok (t f : sexp) : bool := spec t && spec f && Nat.leb (nrd t + nrd f) 3.

Fixpoint len_s (es : sexps) : nat := match es with SNil => O | SCons _ es | SConsB _ es | SConsR _ es => S (len_s es) end.

(** the type of a record, the record variables in scope having the types [rk] (the nearest first) *)
Fixpoint rtype (rk : list nat) (x : srec) : nat :=
  match x with
  | RVar i => nth i rk O
  | RMk ri _ | RCall ri _ _ _ | RW64 ri _ _ _ => ri
  | RLet _ x => rtype rk x
  | RLetR y x => rtype (rtype rk y :: rk) x
  | RIf ri _ _ _ _ _ | RMatchR ri _ _ | RIfB ri _ _ _ | RMatchCnt ri _ _ _ | RSplitR ri _ _ _ | RMkR ri _ _ => ri
  | RLetB _ x | RLetC _ x => rtype rk x
  end.
Fixpoint kinds_s (rk : list nat) (es : sexps) : list kind :=
  match es with SNil => [] | SCons _ es => KNum :: kinds_s rk es | SConsB _ es => KBool :: kinds_s rk es
              | SConsR x es => KRec (rtype rk x) :: kinds_s rk es end.
Fixpoint len_c (cs : scnts) : nat := match cs with CNil => O | CCons _ cs => S (len_c cs) end.
Fixpoint cdepth (c : scnt) : nat := match c with CS c => S (cdepth c) | CPred c => cdepth c | _ => O end.
Fixpoint all_c (p : scnt -> bool) (cs : scnts) : bool := match cs with CNil => true | CCons c r => p c && all_c p r end.
Fixpoint all_s (p : sexp -> bool) (es : sexps) : bool :=
  match es with SNil => true | SCons e r => p e && all_s p r | SConsB _ r | SConsR _ r => all_s p r end.

(** [if c then f a.. else f b..] at the end of [f], both calls on the newest memory, becomes one call whose arguments are
    chosen by conditional moves (the translator's merging of calls, D17): arguments that are plain arithmetic (no read, no
    call), each chosen when the two differ ([same_e]: the same variable or the same number) *)
Definition simple (e : sexp) : bool := spec e && Nat.eqb (nrd e) 0.
Definition simple_c (c : scnt) : bool := match c with CVar _ | CO => true | CNat e => simple e | CS _ | CPred _ | CAdd _ _ => false end.
Definition binop_eqb (o1 o2 : binop) : bool :=
  match o1, o2 with
  | Badd, Badd | Bsub, Bsub | Bmul, Bmul | Bland, Bland | Blor, Blor | Blxor, Blxor | Bdiv, Bdiv | Bmod, Bmod
  | Blsl, Blsl | Blsr, Blsr | Basr, Basr | Bmods, Bmods | Bdivs, Bdivs => true
  | _, _ => false
  end.
(** the same arithmetic on both sides: worked out once (a conditional move between two equal values would make the next
    round of a loop wait for the test) *)
Fixpoint same_e (x y : sexp) : bool :=
  match x, y with
  | SVar i, SVar j => Nat.eqb i j
  | SInt n, SInt m => PrimInt63.eqb n m
  | SOp o a b, SOp o' a' b' => binop_eqb o o' && same_e a a' && same_e b b'
  | _, _ => false
  end.
Definition same_c (x y : scnt) : bool := match x, y with CVar i, CVar j => Nat.eqb i j | CO, CO => true | _, _ => false end.

(** a chain of tests in tail position whose every end is a call of the function itself becomes one call, its arguments
    chosen by conditional moves (the translator's merge, §1.5, D17): the tests worked out once, an argument the same at
    every end worked out once, the others -- plain arithmetic -- worked out at each end and chosen along the tests.  At an
    end, the call's arguments are items (its counters, its numbers) and, for a memory, the cells and values of the writes
    the call is given ([upd h i v ..] down to the newest memory: written once, the values chosen) *)
Inductive item := ICnt (c : scnt) | INum (e : sexp).
Inductive mtree := MLeaf (call ws : list item) | MNodeC (c : cmpop) (a b : sexp) (t f : mtree) | MNodeB (b : sbool) (t f : mtree).
Fixpoint items_c (cs : scnts) : list item := match cs with CNil => [] | CCons c r => ICnt c :: items_c r end.
Fixpoint items_s (es : sexps) : option (list item) :=
  match es with SNil => Some [] | SCons e r => option_map (cons (INum e)) (items_s r) | SConsB _ _ | SConsR _ _ => None end.
Fixpoint skel (m : smem) : option (list item) :=
  match m with MCur => Some [] | MUpd h i v m => option_map (fun l => INum h :: INum i :: INum v :: l) (skel m) | _ => None end.
Fixpoint mt_e (e : sexp) : option mtree :=
  match e with
  | SRec ccs args => option_map (fun l => MLeaf (items_c ccs ++ l) []) (items_s args)
  | SIf c a b t f => match mt_e t, mt_e f with Some t', Some f' => Some (MNodeC c a b t' f') | _, _ => None end
  | SIfB b t f => match mt_e t, mt_e f with Some t', Some f' => Some (MNodeB b t' f') | _, _ => None end
  | _ => None
  end.
Fixpoint mt_m (m : smem) : option mtree :=
  match m with
  | MRec ccs args mm => match items_s args, skel mm with Some l, Some w => Some (MLeaf (items_c ccs ++ l) w) | _, _ => None end
  | MIf c a b m1 m2 => match mt_m m1, mt_m m2 with Some t', Some f' => Some (MNodeC c a b t' f') | _, _ => None end
  | MIfB b m1 m2 => match mt_m m1, mt_m m2 with Some t', Some f' => Some (MNodeB b t' f') | _, _ => None end
  | _ => None
  end.
Fixpoint mt_first (T : mtree) : list item * list item :=
  match T with MLeaf c w => (c, w) | MNodeC _ _ _ t _ | MNodeB _ t _ => mt_first t end.
Fixpoint mt_all (p : list item -> list item -> bool) (T : mtree) : bool :=
  match T with MLeaf c w => p c w | MNodeC _ _ _ t f | MNodeB _ t f => mt_all p t && mt_all p f end.
Definition ith (l : list item) (i : nat) : item := nth i l (INum (SInt 0%uint63)).
Definition same_i (x y : item) : bool := match x, y with ICnt a, ICnt b => same_c a b | INum a, INum b => same_e a b | _, _ => false end.
Definition simple_i (x : item) : bool := match x with ICnt c => simple_c c | INum e => simple e end.
Definition mt_npos (T : mtree) : nat := length (fst (mt_first T) ++ snd (mt_first T)).
Definition mt_ncall (T : mtree) : nat := length (fst (mt_first T)).
(** every end of the same shape; at each place the same item at every end, or plain arithmetic at every end *)
Definition mt_ok (T : mtree) : bool :=
  let l0 := fst (mt_first T) ++ snd (mt_first T) in
  mt_all (fun c w => Nat.eqb (length c) (mt_ncall T) && Nat.eqb (length (c ++ w)) (length l0)) T
  && forallb (fun i => mt_all (fun c w => same_i (ith (c ++ w) i) (ith l0 i)) T || mt_all (fun c w => simple_i (ith (c ++ w) i)) T)
             (seq 0 (length l0)).
(** the tree once its tests are worked out: a node holds the atoms of its comparison *)
Inductive atree := ALeaf (call ws : list item) | ANode (c : cmpop) (A B : atom) (t f : atree).
Fixpoint at_first (At : atree) : list item * list item := match At with ALeaf c w => (c, w) | ANode _ _ _ t _ => at_first t end.
Fixpoint at_all (p : list item -> list item -> bool) (At : atree) : bool :=
  match At with ALeaf c w => p c w | ANode _ _ _ t f => at_all p t && at_all p f end.
(** the memory those writes make *)
Fixpoint wmem (vs : list i63) (M : mem) : mem := match vs with h :: i :: v :: r => KQ.KQRun.upd h i v (wmem r M) | _ => M end.
(** the writes a merged call is given, the innermost first *)
Fixpoint cwrites (ws : list atom) (k : exp) : exp := match ws with ah :: ai :: av :: r => cwrites r (Ekst ah ai av k) | _ => k end.

(** the largest variable a piece of KQL binds, and the first one after it: the second arm of a test starts there, so that
    no variable is bound twice in a function, as in the translator's numbering (measured: the same KQL with variables reused
    across the arms of tests compiled 1.2x slower, the C compiler's registers chosen worse, CF868F) *)
Fixpoint maxv (e : exp) : ident :=
  match e with
  | Eret _ | Eloop _ => 1%positive
  | Eop x _ _ _ k | Esel x _ _ _ _ _ k | Ecall x _ _ k | Eload x _ _ k | Ekld x _ _ k | Ekld32 x _ _ k | Ekld8 x _ _ k
  | Eksize x _ k | Ehwf _ x _ k => Pos.max x (maxv k)
  | Ew64 _ xl xh _ _ _ _ k => Pos.max xl (Pos.max xh (maxv k))
  | Eif _ _ _ t f => Pos.max (maxv t) (maxv f)
  | Estore _ _ _ k | Ekst _ _ _ k | Ekst32 _ _ _ k | Ekst8 _ _ _ k | Ehw _ _ k => maxv k
  end.
Definition after (n : ident) (e : exp) : ident := Pos.succ (Pos.max n (maxv e)).

(** the slot block's cells [0 .. m - 1] read into fresh variables; the saved values written back, cell 0 first *)
Fixpoint cslot_go (j m : nat) (nxt : ident) (K : list atom -> ident -> exp) {struct m} : exp :=
  match m with
  | O => K [] nxt
  | S m => Ekld nxt (Aint 63%uint63) (Aint (KQLAuto.ofn j)) (cslot_go (S j) m (Pos.succ nxt) (fun As n => K (Avar nxt :: As) n))
  end.
Definition cslot (m : nat) (nxt : ident) (K : list atom -> ident -> exp) : exp := cslot_go O m nxt K.
Fixpoint cback (j : nat) (Os : list atom) (k : exp) : exp :=
  match Os with [] => k | o :: Os => Ekst (Aint 63%uint63) (Aint (KQLAuto.ofn j)) o (cback (S j) Os k) end.
(** a call of [h] giving back a record of [S m] fields: the slot block's cells [0 .. m-1] saved, the call, the cells read
    (the fields after the first), the saved values written back; [K] gets the fields' atoms *)
Definition ccallr (h : ident) (Xs : list atom) (m : nat) (nxt : ident) (K : list atom -> ident -> exp) : exp :=
  cslot m nxt (fun Os n1 => Ecall n1 h Xs (cslot m (Pos.succ n1) (fun Fs n2 => cback O Os (K (Avar n1 :: Fs) n2)))).
(** the fields after the first written into the slot block's cells [j ..], the last one first *)
Fixpoint cput (j : nat) (As : list atom) (k : exp) : exp :=
  match As with [] => k | a :: As => cput (S j) As (Ekst (Aint 63%uint63) (Aint (KQLAuto.ofn j)) a k) end.

(** a record taken apart one level (step 43): its number fields' words first, then each record field's *)
Definition rnn (ri : nat) : nat := (rn (RO ri) - fold_right (fun j a => rn (RO j) + a) O (RJ ri))%nat.
Fixpoint slices {A : Type} (ws : list nat) (As : list A) : list (list A) :=
  match ws with [] => [] | w :: ws => firstn w As :: slices ws (skipn w As) end.
Definition rsl {A : Type} (ri : nat) (As : list A) : list (list A) := slices (map (fun j => rn (RO j)) (RJ ri)) (skipn (rnn ri) As).

Section C.
Variable gidf : nat -> ident.   (* the KQL name of the program's function i *)
Variable g : ident.             (* the function's own name *)
Variable mv : ident.            (* the variable holding the first counter's predecessor *)

(** a number, worked out in A-normal form; [K] gets the atom holding it and the next free variable.  The atoms of the counters,
    the booleans (each holding 1 or 0) and the numbers in scope, the nearest first *)
Fixpoint cexp (e : sexp) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : atom -> ident -> exp) {struct e} : exp :=
  match e with
  | SVar i => K (nth i env (Aint 0%uint63)) nxt
  | SInt n => K (Aint n) nxt
  | SOp o a b => cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 => Eop n2 o A B (K (Avar n2) (Pos.succ n2))))
  | SIf c a b t f => cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                       if choice_ok t f then
                         cexp t cenv benv renv env n2 (fun T n3 => cexp f cenv benv renv env n3 (fun F n4 =>
                           Esel n4 c A B T F (K (Avar n4) (Pos.succ n4))))
                       else let tc := cexp t cenv benv renv env n2 K in Eif c A B tc (cexp f cenv benv renv env (after n2 tc) K)))
  | SLet e1 e2 => cexp e1 cenv benv renv env nxt (fun A n1 => cexp e2 cenv benv renv (A :: env) n1 K)
  | SRd h i => cexp h cenv benv renv env nxt (fun H n1 => cexp i cenv benv renv env n1 (fun I n2 => Ekld n2 H I (K (Avar n2) (Pos.succ n2))))
  | SRec ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                       Ecall n2 g (Avar mv :: Cs ++ As) (K (Avar n2) (Pos.succ n2))))
  | SCall f ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                          Ecall n2 (gidf f) (Cs ++ As) (K (Avar n2) (Pos.succ n2))))
  | SMatch c e0 e1 => let t0 := cexp e0 cenv benv renv env nxt K in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (cexp e1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0)) K))
  | SIfB b t f => if choice_ok t f then
                    cexp t cenv benv renv env nxt (fun T n1 => cexp f cenv benv renv env n1 (fun F n2 => csel b cenv benv renv env n2 T F K))
                  else ccond b cenv benv renv env nxt (fun n => cexp t cenv benv renv env n K) (fun n => cexp f cenv benv renv env n K)
  | SLetB b e => cbval b cenv benv renv env nxt (fun A n1 => cexp e cenv (A :: benv) renv env n1 K)
  | SRd32 h i => cexp h cenv benv renv env nxt (fun H n1 => cexp i cenv benv renv env n1 (fun I n2 => Ekld32 n2 H I (K (Avar n2) (Pos.succ n2))))
  | SLetC c e => ccnt c cenv benv renv env nxt (fun A n1 => cexp e (A :: cenv) benv renv env n1 K)
  | SFld i j => K (nth j (nth i renv [Aint 0%uint63]) (Aint 0%uint63)) nxt
  | SLetR x e => crec x cenv benv renv env nxt (fun As n1 => cexp e cenv benv (As :: renv) env n1 K)
  | SMatchR x e => crec x cenv benv renv env nxt (fun As n1 => cexp e cenv benv renv (rev As ++ env) n1 K)
  | SSplitR sj x e => crec x cenv benv renv env nxt (fun As n1 => cexp e cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1 K)
  | SHwf o args => cexps args cenv benv renv env nxt (fun As n1 => Ehwf o n1 As (K (Avar n1) (Pos.succ n1)))
  | SSize h => cexp h cenv benv renv env nxt (fun H n1 => Eksize n1 H (K (Avar n1) (Pos.succ n1)))
  | SRd8 h i => cexp h cenv benv renv env nxt (fun H n1 => cexp i cenv benv renv env n1 (fun I n2 => Ekld8 n2 H I (K (Avar n2) (Pos.succ n2))))
  end
with cexps (es : sexps) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : list atom -> ident -> exp) {struct es} : exp :=
  match es with
  | SNil => K [] nxt
  | SCons e r => cexp e cenv benv renv env nxt (fun A n1 => cexps r cenv benv renv env n1 (fun As n2 => K (A :: As) n2))
  | SConsB b r => cbval b cenv benv renv env nxt (fun A n1 => cexps r cenv benv renv env n1 (fun As n2 => K (A :: As) n2))
  | SConsR x r => crec x cenv benv renv env nxt (fun As n1 => cexps r cenv benv renv env n1 (fun Bs n2 => K (As ++ Bs) n2))
  end
with ccnt (c : scnt) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : atom -> ident -> exp) {struct c} : exp :=
  match c with
  | CVar i => K (nth i cenv (Aint 0%uint63)) nxt
  | CO => K (Aint 0%uint63) nxt
  | CS c => ccnt c cenv benv renv env nxt (fun A n1 => Eop n1 Badd A (Aint 1%uint63) (K (Avar n1) (Pos.succ n1)))
  | CNat e => cexp e cenv benv renv env nxt (fun A n1 =>
                Esel n1 Csle A (Aint 0%uint63) (Aint 0%uint63) A
                  (Esel (Pos.succ n1) Cslt (Aint cap60) (Avar n1) (Aint cap60) (Avar n1)
                     (K (Avar (Pos.succ n1)) (Pos.succ (Pos.succ n1)))))
  | CPred c => ccnt c cenv benv renv env nxt (fun A n1 =>
                 Eop n1 Bsub A (Aint 1%uint63)
                   (Esel (Pos.succ n1) Ceq A (Aint 0%uint63) (Aint 0%uint63) (Avar n1)
                      (K (Avar (Pos.succ n1)) (Pos.succ (Pos.succ n1)))))
  | CAdd a b => ccnt a cenv benv renv env nxt (fun A n1 => ccnt b cenv benv renv env n1 (fun B n2 =>
                  Eop n2 Badd A B (K (Avar n2) (Pos.succ n2))))
  end
with ccnts (ccs : scnts) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : list atom -> ident -> exp) {struct ccs} : exp :=
  match ccs with
  | CNil => K [] nxt
  | CCons c r => ccnt c cenv benv renv env nxt (fun A n1 => ccnts r cenv benv renv env n1 (fun As n2 => K (A :: As) n2))
  end
(** a boolean as a test: jumps, [KT] where it holds and [KF] where it does not, each given the next free variable; [a && b]
    tests [b] only where [a] held (C's short-circuit) *)
with ccond (b : sbool) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (KT KF : ident -> exp) {struct b} : exp :=
  match b with
  | BCmp c x y => cexp x cenv benv renv env nxt (fun A n1 => cexp y cenv benv renv env n1 (fun B n2 => Eif c A B (KT n2) (KF (after n2 (KT n2)))))
  | BVar i => Eif Ceq (nth i benv (Aint 0%uint63)) (Aint 0%uint63) (KF nxt) (KT (after nxt (KF nxt)))
  | BTrue => KT nxt
  | BFalse => KF nxt
  | BAnd x y => ccond x cenv benv renv env nxt (fun n => ccond y cenv benv renv env n KT KF) KF
  | BOr x y => ccond x cenv benv renv env nxt KT (fun n => ccond y cenv benv renv env n KT KF)
  | BNot x => ccond x cenv benv renv env nxt KF KT
  | BIfCmp c a b x y => cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                          let tc := ccond x cenv benv renv env n2 KT KF in Eif c A B tc (ccond y cenv benv renv env (after n2 tc) KT KF)))
  | BMatchCnt c x0 x1 => let t0 := ccond x0 cenv benv renv env nxt KT KF in
                         Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                           (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                                (ccond x1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0)) KT KF))
  | BCall f ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                          Ecall n2 (gidf f) (Cs ++ As)
                            (Eif Ceq (Avar n2) (Aint 0%uint63) (KF (Pos.succ n2)) (KT (after (Pos.succ n2) (KF (Pos.succ n2)))))))
  | BCmpC c x y => ccnt x cenv benv renv env nxt (fun A n1 => ccnt y cenv benv renv env n1 (fun B n2 => Eif c A B (KT n2) (KF (after n2 (KT n2)))))
  | BxIfB b x y => ccond b cenv benv renv env nxt (fun n => ccond x cenv benv renv env n KT KF) (fun n => ccond y cenv benv renv env n KT KF)
  | BxLet e x => cexp e cenv benv renv env nxt (fun A n1 => ccond x cenv benv renv (A :: env) n1 KT KF)
  | BxLetB b x => cbval b cenv benv renv env nxt (fun A n1 => ccond x cenv (A :: benv) renv env n1 KT KF)
  | BxLetC c x => ccnt c cenv benv renv env nxt (fun A n1 => ccond x (A :: cenv) benv renv env n1 KT KF)
  | BxLetR r x => crec r cenv benv renv env nxt (fun As n1 => ccond x cenv benv (As :: renv) env n1 KT KF)
  | BxMatchR r x => crec r cenv benv renv env nxt (fun As n1 => ccond x cenv benv renv (rev As ++ env) n1 KT KF)
  | BxSplitR sj r x => crec r cenv benv renv env nxt (fun As n1 => ccond x cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1 KT KF)
  end
(** a boolean as a value, 1 or 0, with no jump: a comparison by a conditional move, [&&] [||] [negb] by [land] [lor]
    [lxor 1] of the parts' values *)
with cbval (b : sbool) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : atom -> ident -> exp) {struct b} : exp :=
  match b with
  | BCmp c x y => cexp x cenv benv renv env nxt (fun A n1 => cexp y cenv benv renv env n1 (fun B n2 =>
                    Esel n2 c A B (Aint 1%uint63) (Aint 0%uint63) (K (Avar n2) (Pos.succ n2))))
  | BVar i => K (nth i benv (Aint 0%uint63)) nxt
  | BTrue => K (Aint 1%uint63) nxt
  | BFalse => K (Aint 0%uint63) nxt
  | BAnd x y => cbval x cenv benv renv env nxt (fun A n1 => cbval y cenv benv renv env n1 (fun B n2 =>
                  Eop n2 Bland A B (K (Avar n2) (Pos.succ n2))))
  | BOr x y => cbval x cenv benv renv env nxt (fun A n1 => cbval y cenv benv renv env n1 (fun B n2 =>
                 Eop n2 Blor A B (K (Avar n2) (Pos.succ n2))))
  | BNot x => cbval x cenv benv renv env nxt (fun A n1 => Eop n1 Blxor A (Aint 1%uint63) (K (Avar n1) (Pos.succ n1)))
  | BIfCmp c a b x y => cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                          let tc := cbval x cenv benv renv env n2 K in Eif c A B tc (cbval y cenv benv renv env (after n2 tc) K)))
  | BMatchCnt c x0 x1 => let t0 := cbval x0 cenv benv renv env nxt K in
                         Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                           (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                                (cbval x1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0)) K))
  | BCall f ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                          Ecall n2 (gidf f) (Cs ++ As) (K (Avar n2) (Pos.succ n2))))
  | BCmpC c x y => ccnt x cenv benv renv env nxt (fun A n1 => ccnt y cenv benv renv env n1 (fun B n2 =>
                     Esel n2 c A B (Aint 1%uint63) (Aint 0%uint63) (K (Avar n2) (Pos.succ n2))))
  | BxIfB b x y => ccond b cenv benv renv env nxt (fun n => cbval x cenv benv renv env n K) (fun n => cbval y cenv benv renv env n K)
  | BxLet e x => cexp e cenv benv renv env nxt (fun A n1 => cbval x cenv benv renv (A :: env) n1 K)
  | BxLetB b x => cbval b cenv benv renv env nxt (fun A n1 => cbval x cenv (A :: benv) renv env n1 K)
  | BxLetC c x => ccnt c cenv benv renv env nxt (fun A n1 => cbval x (A :: cenv) benv renv env n1 K)
  | BxLetR r x => crec r cenv benv renv env nxt (fun As n1 => cbval x cenv benv (As :: renv) env n1 K)
  | BxMatchR r x => crec r cenv benv renv env nxt (fun As n1 => cbval x cenv benv renv (rev As ++ env) n1 K)
  | BxSplitR sj r x => crec r cenv benv renv env nxt (fun As n1 => cbval x cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1 K)
  end
(** a choice of [T] or [F] on a boolean, with no jump, as the translator makes it (§1.5): on a comparison or a boolean
    variable a conditional move; on [&&], [||], [negb] choices on the parts -- [if a && b then T else F] is
    [if a then (if b then T else F) else F] -- so no boolean value is worked out *)
with csel (b : sbool) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (T F : atom) (K : atom -> ident -> exp) {struct b} : exp :=
  match b with
  | BCmp c x y => cexp x cenv benv renv env nxt (fun A n1 => cexp y cenv benv renv env n1 (fun B n2 =>
                    Esel n2 c A B T F (K (Avar n2) (Pos.succ n2))))
  | BVar i => Esel nxt Ceq (nth i benv (Aint 0%uint63)) (Aint 0%uint63) F T (K (Avar nxt) (Pos.succ nxt))
  | BTrue => K T nxt
  | BFalse => K F nxt
  | BAnd x y => csel y cenv benv renv env nxt T F (fun V n1 => csel x cenv benv renv env n1 V F K)
  | BOr x y => csel y cenv benv renv env nxt T F (fun V n1 => csel x cenv benv renv env n1 T V K)
  | BNot x => csel x cenv benv renv env nxt F T K
  | BIfCmp c a b x y => cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                          let tc := csel x cenv benv renv env n2 T F K in Eif c A B tc (csel y cenv benv renv env (after n2 tc) T F K)))
  | BMatchCnt c x0 x1 => let t0 := csel x0 cenv benv renv env nxt T F K in
                         Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                           (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                                (csel x1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0)) T F K))
  | BCall f ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                          Ecall n2 (gidf f) (Cs ++ As)
                            (Esel (Pos.succ n2) Ceq (Avar n2) (Aint 0%uint63) F T (K (Avar (Pos.succ n2)) (Pos.succ (Pos.succ n2))))))
  | BCmpC c x y => ccnt x cenv benv renv env nxt (fun A n1 => ccnt y cenv benv renv env n1 (fun B n2 =>
                     Esel n2 c A B T F (K (Avar n2) (Pos.succ n2))))
  | BxIfB b x y => ccond b cenv benv renv env nxt (fun n => csel x cenv benv renv env n T F K) (fun n => csel y cenv benv renv env n T F K)
  | BxLet e x => cexp e cenv benv renv env nxt (fun A n1 => csel x cenv benv renv (A :: env) n1 T F K)
  | BxLetB b x => cbval b cenv benv renv env nxt (fun A n1 => csel x cenv (A :: benv) renv env n1 T F K)
  | BxLetC c x => ccnt c cenv benv renv env nxt (fun A n1 => csel x (A :: cenv) benv renv env n1 T F K)
  | BxLetR r x => crec r cenv benv renv env nxt (fun As n1 => csel x cenv benv (As :: renv) env n1 T F K)
  | BxMatchR r x => crec r cenv benv renv env nxt (fun As n1 => csel x cenv benv renv (rev As ++ env) n1 T F K)
  | BxSplitR sj r x => crec r cenv benv renv env nxt (fun As n1 => csel x cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1 T F K)
  end
(** a record: its fields' atoms *)
with crec (x : srec) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : list atom -> ident -> exp)
  {struct x} : exp :=
  match x with
  | RVar i => K (nth i renv [Aint 0%uint63]) nxt
  | RMk _ es => cexps es cenv benv renv env nxt K
  | RMkR _ ns rs => cexps ns cenv benv renv env nxt (fun As n1 => cexps rs cenv benv renv env n1 (fun Bs n2 => K (As ++ Bs) n2))
  | RCall ri f ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                            ccallr (gidf f) (Cs ++ As) (Nat.pred (rn (RO ri))) n2 K))
  | RW64 _ o a b => crec a cenv benv renv env nxt (fun As n1 => crec b cenv benv renv env n1 (fun Bs n2 =>
                      Ew64 o n2 (Pos.succ n2) (nth 0 As (Aint 0%uint63)) (nth 1 As (Aint 0%uint63)) (nth 0 Bs (Aint 0%uint63)) (nth 1 Bs (Aint 0%uint63))
                        (K [Avar n2; Avar (Pos.succ n2)] (Pos.succ (Pos.succ n2)))))
  | RLet e x => cexp e cenv benv renv env nxt (fun A n1 => crec x cenv benv renv (A :: env) n1 K)
  | RLetR y x => crec y cenv benv renv env nxt (fun As n1 => crec x cenv benv (As :: renv) env n1 K)
  | RIf _ c a b x y => cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                       let tc := crec x cenv benv renv env n2 K in Eif c A B tc (crec y cenv benv renv env (after n2 tc) K)))
  | RMatchR _ x y => crec x cenv benv renv env nxt (fun As n1 => crec y cenv benv renv (rev As ++ env) n1 K)
  | RSplitR _ sj x y => crec x cenv benv renv env nxt (fun As n1 => crec y cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1 K)
  | RIfB _ b x y => ccond b cenv benv renv env nxt (fun n => crec x cenv benv renv env n K) (fun n => crec y cenv benv renv env n K)
  | RLetB b x => cbval b cenv benv renv env nxt (fun A n1 => crec x cenv (A :: benv) renv env n1 K)
  | RLetC c x => ccnt c cenv benv renv env nxt (fun A n1 => crec x (A :: cenv) benv renv env n1 K)
  | RMatchCnt _ c x y => let t0 := crec x cenv benv renv env nxt K in
                         Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                           (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                                (crec y (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0)) K))
  end.

(** a merged call: the tests, then the arguments place by place -- an item the same at every end once, the others at each
    end and chosen along the tests *)
Fixpoint ctests (T : mtree) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : atree -> ident -> exp) {struct T} : exp :=
  match T with
  | MLeaf c w => K (ALeaf c w) nxt
  | MNodeC c a b t f => cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                          ctests t cenv benv renv env n2 (fun At n3 => ctests f cenv benv renv env n3 (fun Af n4 => K (ANode c A B At Af) n4))))
  | MNodeB b t f => cbval b cenv benv renv env nxt (fun V n1 =>
                      ctests t cenv benv renv env n1 (fun At n2 => ctests f cenv benv renv env n2 (fun Af n3 => K (ANode Ceq V (Aint 0%uint63) Af At) n3)))
  end.
Definition citem (x : item) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : atom -> ident -> exp) : exp :=
  match x with ICnt c => ccnt c cenv benv renv env nxt K | INum e => cexp e cenv benv renv env nxt K end.
Fixpoint cpick (At : atree) (i : nat) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : atom -> ident -> exp) {struct At} : exp :=
  match At with
  | ALeaf c w => citem (ith (c ++ w) i) cenv benv renv env nxt K
  | ANode c A B t f => cpick t i cenv benv renv env nxt (fun X n1 => cpick f i cenv benv renv env n1 (fun Y n2 =>
                         Esel n2 c A B X Y (K (Avar n2) (Pos.succ n2))))
  end.
Fixpoint cposs (At : atree) (i n : nat) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : list atom -> ident -> exp) {struct n} : exp :=
  match n with
  | O => K [] nxt
  | S n =>
      let x := ith (fst (at_first At) ++ snd (at_first At)) i in
      if at_all (fun c w => same_i (ith (c ++ w) i) x) At
      then citem x cenv benv renv env nxt (fun X n1 => cposs At (S i) n cenv benv renv env n1 (fun Xs n2 => K (X :: Xs) n2))
      else cpick At i cenv benv renv env nxt (fun X n1 => cposs At (S i) n cenv benv renv env n1 (fun Xs n2 => K (X :: Xs) n2))
  end.
Definition cmt (T : mtree) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : list atom -> ident -> exp) : exp :=
  ctests T cenv benv renv env nxt (fun At n1 => cposs At 0 (mt_npos T) cenv benv renv env n1 K).
(** a test in tail position: the merged call when it is such a chain, the code [k] otherwise *)
Definition mrg_e (e : sexp) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (k : exp) : exp :=
  match mt_e e with
  | Some T => if mt_ok T then cmt T cenv benv renv env nxt (fun Xs _ => Eloop (Avar mv :: Xs)) else k
  | None => k
  end.
Definition mrg_m (m : smem) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (k : exp) : exp :=
  match mt_m m with
  | Some T => if mt_ok T then cmt T cenv benv renv env nxt (fun Xs _ => cwrites (skipn (mt_ncall T) Xs) (Eloop (Avar mv :: firstn (mt_ncall T) Xs)))
              else k
  | None => k
  end.

(** the body in tail position: a test is a branch, the recursive call a loop *)
Fixpoint ctail (e : sexp) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) {struct e} : exp :=
  match e with
  | SIf c a b t f => mrg_e (SIf c a b t f) cenv benv renv env nxt (cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                       let tc := ctail t cenv benv renv env n2 in Eif c A B tc (ctail f cenv benv renv env (after n2 tc)))))
  | SLet e1 e2 => cexp e1 cenv benv renv env nxt (fun A n1 => ctail e2 cenv benv renv (A :: env) n1)
  | SRec ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As _ => Eloop (Avar mv :: Cs ++ As)))
  | SMatch c e0 e1 => let t0 := ctail e0 cenv benv renv env nxt in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (ctail e1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0))))
  | SIfB b t f => mrg_e (SIfB b t f) cenv benv renv env nxt
                    (ccond b cenv benv renv env nxt (fun n => ctail t cenv benv renv env n) (fun n => ctail f cenv benv renv env n))
  | SLetB b e => cbval b cenv benv renv env nxt (fun A n1 => ctail e cenv (A :: benv) renv env n1)
  | SLetC c e => ccnt c cenv benv renv env nxt (fun A n1 => ctail e (A :: cenv) benv renv env n1)
  | SLetR x e => crec x cenv benv renv env nxt (fun As n1 => ctail e cenv benv (As :: renv) env n1)
  | SMatchR x e => crec x cenv benv renv env nxt (fun As n1 => ctail e cenv benv renv (rev As ++ env) n1)
  | SSplitR sj x e => crec x cenv benv renv env nxt (fun As n1 => ctail e cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1)
  | _ => cexp e cenv benv renv env nxt (fun A _ => Eret A)
  end.

(** a memory, made in KQL's one memory: the numbers first, then the memory given, then the construct's own step (a write,
    a call); [K] gets the next free variable *)
Fixpoint cmem (m : smem) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : ident -> exp) {struct m} : exp :=
  match m with
  | MCur => K nxt
  | MUpd h i v m => cexp h cenv benv renv env nxt (fun H n1 => cexp i cenv benv renv env n1 (fun I n2 => cexp v cenv benv renv env n2 (fun V n3 =>
                      cmem m cenv benv renv env n3 (fun n4 => Ekst H I V (K n4)))))
  | MLet e m => cexp e cenv benv renv env nxt (fun A n1 => cmem m cenv benv renv (A :: env) n1 K)
  | MLetM m1 m2 => cmem m1 cenv benv renv env nxt (fun n1 => cmem m2 cenv benv renv env n1 K)
  | MIf c a b m1 m2 => cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                         let tc := cmem m1 cenv benv renv env n2 K in Eif c A B tc (cmem m2 cenv benv renv env (after n2 tc) K)))
  | MRec ccs args m => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 => cmem m cenv benv renv env n2 (fun n3 =>
                         Ecall n3 g (Avar mv :: Cs ++ As) (K (Pos.succ n3)))))
  | MCall f ccs args m => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 => cmem m cenv benv renv env n2 (fun n3 =>
                            Ecall n3 (gidf f) (Cs ++ As) (K (Pos.succ n3)))))
  | MMatch c m0 m1 => let t0 := cmem m0 cenv benv renv env nxt K in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (cmem m1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0)) K))
  | MIfB b m1 m2 => ccond b cenv benv renv env nxt (fun n => cmem m1 cenv benv renv env n K) (fun n => cmem m2 cenv benv renv env n K)
  | MLetB b m => cbval b cenv benv renv env nxt (fun A n1 => cmem m cenv (A :: benv) renv env n1 K)
  | MUpd32 h i v m => cexp h cenv benv renv env nxt (fun H n1 => cexp i cenv benv renv env n1 (fun I n2 => cexp v cenv benv renv env n2 (fun V n3 =>
                        cmem m cenv benv renv env n3 (fun n4 => Ekst32 H I V (K n4)))))
  | MLetC c m => ccnt c cenv benv renv env nxt (fun A n1 => cmem m (A :: cenv) benv renv env n1 K)
  | MHw o args m => cexps args cenv benv renv env nxt (fun As n1 => cmem m cenv benv renv env n1 (fun n2 => Ehw o As (K n2)))
  | MUpd8 h i v m => cexp h cenv benv renv env nxt (fun H n1 => cexp i cenv benv renv env n1 (fun I n2 => cexp v cenv benv renv env n2 (fun V n3 =>
                       cmem m cenv benv renv env n3 (fun n4 => Ekst8 H I V (K n4)))))
  | MLetR x m => crec x cenv benv renv env nxt (fun As n1 => cmem m cenv benv (As :: renv) env n1 K)
  | MMatchR x m => crec x cenv benv renv env nxt (fun As n1 => cmem m cenv benv renv (rev As ++ env) n1 K)
  | MSplitR sj x m => crec x cenv benv renv env nxt (fun As n1 => cmem m cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1 K)
  | MMatchP p m | MLetP p m => cpv p cenv benv renv env nxt (fun A n1 => cmem m cenv benv renv (A :: env) n1 K)
  | MCallP f ccs args p => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 => cpv p cenv benv renv env n2 (fun A n3 => Ecall n3 (gidf f) (Cs ++ As ++ [A]) (K (Pos.succ n3)))))
  end
(* a number and a memory where it is taken apart (step 26): the continuation gets the number's atom, the KQL memory is the
    pair's memory *)
with cpv (p : spv) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) (K : atom -> ident -> exp) {struct p} : exp :=
  match p with
  | PvMk e m => cexp e cenv benv renv env nxt (fun A n1 => cmem m cenv benv renv env n1 (fun n2 => K A n2))
  | PvCall f ccs args m => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                             cmem m cenv benv renv env n2 (fun n3 => Ecall n3 (gidf f) (Cs ++ As) (K (Avar n3) (Pos.succ n3)))))
  | PvRec ccs args m => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                          cmem m cenv benv renv env n2 (fun n3 => Ecall n3 g (Avar mv :: Cs ++ As) (K (Avar n3) (Pos.succ n3)))))
  | PvLet e p => cexp e cenv benv renv env nxt (fun A n1 => cpv p cenv benv renv (A :: env) n1 K)
  | PvLetB c p => cbval c cenv benv renv env nxt (fun A n1 => cpv p cenv (A :: benv) renv env n1 K)
  | PvLetC c p => ccnt c cenv benv renv env nxt (fun A n1 => cpv p (A :: cenv) benv renv env n1 K)
  | PvLetR x p => crec x cenv benv renv env nxt (fun As n1 => cpv p cenv benv (As :: renv) env n1 K)
  | PvMatchR x p => crec x cenv benv renv env nxt (fun As n1 => cpv p cenv benv renv (rev As ++ env) n1 K)
  | PvSplitR sj x p => crec x cenv benv renv env nxt (fun As n1 => cpv p cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1 K)
  | PvCallP f ccs args p => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 => cpv p cenv benv renv env n2 (fun A n3 => Ecall n3 (gidf f) (Cs ++ As ++ [A]) (K (Avar n3) (Pos.succ n3)))))
  | PvLetM m p => cmem m cenv benv renv env nxt (fun n1 => cpv p cenv benv renv env n1 K)
  | PvIf c x y t f => cexp x cenv benv renv env nxt (fun A n1 => cexp y cenv benv renv env n1 (fun B n2 =>
                        let tc := cpv t cenv benv renv env n2 K in Eif c A B tc (cpv f cenv benv renv env (after n2 tc) K)))
  | PvIfB c t f => ccond c cenv benv renv env nxt (fun n => cpv t cenv benv renv env n K) (fun n => cpv f cenv benv renv env n K)
  | PvMatch c p0 p1 => let t0 := cpv p0 cenv benv renv env nxt K in
                       Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                         (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                              (cpv p1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0)) K))
  | PvMatchP p q => cpv p cenv benv renv env nxt (fun A n1 => cpv q cenv benv renv (A :: env) n1 K)
  end.

(** a memory in tail position: a test is a branch, the recursive call a loop, the end returns 0 with the memory made *)
Fixpoint ctailm (m : smem) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) {struct m} : exp :=
  match m with
  | MIf c a b m1 m2 => mrg_m (MIf c a b m1 m2) cenv benv renv env nxt (cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                         let tc := ctailm m1 cenv benv renv env n2 in Eif c A B tc (ctailm m2 cenv benv renv env (after n2 tc)))))
  | MLet e m => cexp e cenv benv renv env nxt (fun A n1 => ctailm m cenv benv renv (A :: env) n1)
  | MLetM m1 m2 => cmem m1 cenv benv renv env nxt (fun n1 => ctailm m2 cenv benv renv env n1)
  | MRec ccs args m => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                         cmem m cenv benv renv env n2 (fun _ => Eloop (Avar mv :: Cs ++ As))))
  | MMatch c m0 m1 => let t0 := ctailm m0 cenv benv renv env nxt in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (ctailm m1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0))))
  | MIfB b m1 m2 => mrg_m (MIfB b m1 m2) cenv benv renv env nxt
                      (ccond b cenv benv renv env nxt (fun n => ctailm m1 cenv benv renv env n) (fun n => ctailm m2 cenv benv renv env n))
  | MLetB b m => cbval b cenv benv renv env nxt (fun A n1 => ctailm m cenv (A :: benv) renv env n1)
  | MLetC c m => ccnt c cenv benv renv env nxt (fun A n1 => ctailm m (A :: cenv) benv renv env n1)
  | MLetR x m => crec x cenv benv renv env nxt (fun As n1 => ctailm m cenv benv (As :: renv) env n1)
  | MMatchR x m => crec x cenv benv renv env nxt (fun As n1 => ctailm m cenv benv renv (rev As ++ env) n1)
  | MSplitR sj x m => crec x cenv benv renv env nxt (fun As n1 => ctailm m cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1)
  | MMatchP p m | MLetP p m => cpv p cenv benv renv env nxt (fun A n1 => ctailm m cenv benv renv (A :: env) n1)
  | _ => cmem m cenv benv renv env nxt (fun _ => Eret (Aint 0%uint63))
  end.

(** a number made after memories, in tail position: the memories by [cmem], the tests as branches, the end returns the number *)
(** in tail position: the number returned after the memory's writes; the function itself at the end a loop *)
Fixpoint ctailp (p : spv) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) {struct p} : exp :=
  match p with
  | PvMk e m => cexp e cenv benv renv env nxt (fun A n1 => cmem m cenv benv renv env n1 (fun _ => Eret A))
  | PvCall f ccs args m => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                             cmem m cenv benv renv env n2 (fun n3 => Ecall n3 (gidf f) (Cs ++ As) (Eret (Avar n3)))))
  | PvRec ccs args m => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                          cmem m cenv benv renv env n2 (fun _ => Eloop (Avar mv :: Cs ++ As))))
  | PvLet e p => cexp e cenv benv renv env nxt (fun A n1 => ctailp p cenv benv renv (A :: env) n1)
  | PvLetB c p => cbval c cenv benv renv env nxt (fun A n1 => ctailp p cenv (A :: benv) renv env n1)
  | PvLetC c p => ccnt c cenv benv renv env nxt (fun A n1 => ctailp p (A :: cenv) benv renv env n1)
  | PvLetR x p => crec x cenv benv renv env nxt (fun As n1 => ctailp p cenv benv (As :: renv) env n1)
  | PvMatchR x p => crec x cenv benv renv env nxt (fun As n1 => ctailp p cenv benv renv (rev As ++ env) n1)
  | PvSplitR sj x p => crec x cenv benv renv env nxt (fun As n1 => ctailp p cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1)
  | PvCallP f ccs args p => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 => cpv p cenv benv renv env n2 (fun A n3 => Ecall n3 (gidf f) (Cs ++ As ++ [A]) (Eret (Avar n3)))))
  | PvLetM m p => cmem m cenv benv renv env nxt (fun n1 => ctailp p cenv benv renv env n1)
  | PvIf c x y t f => cexp x cenv benv renv env nxt (fun A n1 => cexp y cenv benv renv env n1 (fun B n2 =>
                        let tc := ctailp t cenv benv renv env n2 in Eif c A B tc (ctailp f cenv benv renv env (after n2 tc))))
  | PvIfB c t f => ccond c cenv benv renv env nxt (fun n => ctailp t cenv benv renv env n) (fun n => ctailp f cenv benv renv env n)
  | PvMatch c p0 p1 => let t0 := ctailp p0 cenv benv renv env nxt in
                       Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                         (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                              (ctailp p1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0))))
  | PvMatchP p q => cpv p cenv benv renv env nxt (fun A n1 => ctailp q cenv benv renv (A :: env) n1)
  end.

Fixpoint ctailx (x : sx) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) {struct x} : exp :=
  match x with
  | XRet e => cexp e cenv benv renv env nxt (fun A _ => Eret A)
  | XLetM m x => cmem m cenv benv renv env nxt (fun n1 => ctailx x cenv benv renv env n1)
  | XLet e x => cexp e cenv benv renv env nxt (fun A n1 => ctailx x cenv benv renv (A :: env) n1)
  | XLetB b x => cbval b cenv benv renv env nxt (fun A n1 => ctailx x cenv (A :: benv) renv env n1)
  | XIf c a b x1 x2 => cexp a cenv benv renv env nxt (fun A n1 => cexp b cenv benv renv env n1 (fun B n2 =>
                         let tc := ctailx x1 cenv benv renv env n2 in Eif c A B tc (ctailx x2 cenv benv renv env (after n2 tc))))
  | XIfB b x1 x2 => ccond b cenv benv renv env nxt (fun n => ctailx x1 cenv benv renv env n) (fun n => ctailx x2 cenv benv renv env n)
  | XMatch c x0 x1 => let t0 := ctailx x0 cenv benv renv env nxt in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (ctailx x1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0))))
  | XLetC c x => ccnt c cenv benv renv env nxt (fun A n1 => ctailx x (A :: cenv) benv renv env n1)
  | XRec ccs args m => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                         cmem m cenv benv renv env n2 (fun _ => Eloop (Avar mv :: Cs ++ As))))
  | XCall f ccs args m => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                            cmem m cenv benv renv env n2 (fun n3 => Ecall n3 (gidf f) (Cs ++ As) (Eret (Avar n3)))))
  | XLetR r x => crec r cenv benv renv env nxt (fun As n1 => ctailx x cenv benv (As :: renv) env n1)
  | XMatchR r x => crec r cenv benv renv env nxt (fun As n1 => ctailx x cenv benv renv (rev As ++ env) n1)
  | XSplitR sj r x => crec r cenv benv renv env nxt (fun As n1 => ctailx x cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1)
  | XCallP f ccs args p => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 => cpv p cenv benv renv env n2 (fun A n3 => Ecall n3 (gidf f) (Cs ++ As ++ [A]) (Eret (Avar n3)))))
  | XMatchP p x | XLetP p x => cpv p cenv benv renv env nxt (fun A n1 => ctailx x cenv benv renv (A :: env) n1)
  | XBind bq f ccs args m x => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                                 cmem m cenv benv renv env n2 (fun n3 => Ecall n3 (gidf f) (Cs ++ As)
                                   (if bq then ctailx x cenv (Avar n3 :: benv) renv env (Pos.succ n3) else ctailx x cenv benv renv (Avar n3 :: env) (Pos.succ n3)))))
  | XBindR ccs args m x => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                             cmem m cenv benv renv env n2 (fun n3 => Ecall n3 g (Avar mv :: Cs ++ As) (ctailx x cenv benv renv (Avar n3 :: env) (Pos.succ n3)))))
  | XBindP bq f ccs args p x => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                                  cpv p cenv benv renv env n2 (fun A n3 => Ecall n3 (gidf f) (Cs ++ As ++ [A])
                                    (if bq then ctailx x cenv (Avar n3 :: benv) renv env (Pos.succ n3) else ctailx x cenv benv renv (Avar n3 :: env) (Pos.succ n3)))))
  end.

(** a record given back, in tail position: at the end its fields after the first into the slot block and the first returned;
    the recursive call at the end a loop, elsewhere a call whose fields are read back from the slot block *)
Fixpoint ctailr (ri : nat) (b : sbr) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) {struct b} : exp :=
  match b with
  | BRet x => crec x cenv benv renv env nxt (fun As _ => cput O (tl As) (Eret (hd (Aint 0%uint63) As)))
  | BRec ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As _ => Eloop (Avar mv :: Cs ++ As)))
  | BMatchRec ccs args b => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                              ccallr g (Avar mv :: Cs ++ As) (Nat.pred (rn (RO ri))) n2 (fun Fs n3 => ctailr ri b cenv benv renv (rev Fs ++ env) n3)))
  | BLetRec ccs args b => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                            ccallr g (Avar mv :: Cs ++ As) (Nat.pred (rn (RO ri))) n2 (fun Fs n3 => ctailr ri b cenv benv (Fs :: renv) env n3)))
  | BLet e b => cexp e cenv benv renv env nxt (fun A n1 => ctailr ri b cenv benv renv (A :: env) n1)
  | BLetB c b => cbval c cenv benv renv env nxt (fun A n1 => ctailr ri b cenv (A :: benv) renv env n1)
  | BLetC c b => ccnt c cenv benv renv env nxt (fun A n1 => ctailr ri b (A :: cenv) benv renv env n1)
  | BLetR x b => crec x cenv benv renv env nxt (fun As n1 => ctailr ri b cenv benv (As :: renv) env n1)
  | BMatchR x b => crec x cenv benv renv env nxt (fun As n1 => ctailr ri b cenv benv renv (rev As ++ env) n1)
  | BSplitR sj x b => crec x cenv benv renv env nxt (fun As n1 => ctailr ri b cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1)
  | BIf c x y t f => cexp x cenv benv renv env nxt (fun A n1 => cexp y cenv benv renv env n1 (fun B n2 =>
                       let tc := ctailr ri t cenv benv renv env n2 in Eif c A B tc (ctailr ri f cenv benv renv env (after n2 tc))))
  | BIfB c t f => ccond c cenv benv renv env nxt (fun n => ctailr ri t cenv benv renv env n) (fun n => ctailr ri f cenv benv renv env n)
  | BMatch c b0 b1 => let t0 := ctailr ri b0 cenv benv renv env nxt in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (ctailr ri b1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0))))
  end.
(** in tail position, a boolean given back (step 24): returned as 1 or 0; the function itself at the end a loop, its negation
    the call and [lxor 1] *)
Fixpoint ctailb (b : sbb) (cenv benv : list atom) (renv : list (list atom)) (env : list atom) (nxt : ident) {struct b} : exp :=
  match b with
  | BbRet x => cbval x cenv benv renv env nxt (fun A _ => Eret A)
  | BbRec ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As _ => Eloop (Avar mv :: Cs ++ As)))
  | BbNotRec ccs args => ccnts ccs cenv benv renv env nxt (fun Cs n1 => cexps args cenv benv renv env n1 (fun As n2 =>
                           Ecall n2 g (Avar mv :: Cs ++ As) (Eop (Pos.succ n2) Blxor (Avar n2) (Aint 1%uint63) (Eret (Avar (Pos.succ n2))))))
  | BbLet e b => cexp e cenv benv renv env nxt (fun A n1 => ctailb b cenv benv renv (A :: env) n1)
  | BbLetB c b => cbval c cenv benv renv env nxt (fun A n1 => ctailb b cenv (A :: benv) renv env n1)
  | BbLetC c b => ccnt c cenv benv renv env nxt (fun A n1 => ctailb b (A :: cenv) benv renv env n1)
  | BbLetR x b => crec x cenv benv renv env nxt (fun As n1 => ctailb b cenv benv (As :: renv) env n1)
  | BbMatchR x b => crec x cenv benv renv env nxt (fun As n1 => ctailb b cenv benv renv (rev As ++ env) n1)
  | BbSplitR sj x b => crec x cenv benv renv env nxt (fun As n1 => ctailb b cenv benv (rev (rsl sj As) ++ renv) (rev (firstn (rnn sj) As) ++ env) n1)
  | BbIf c x y t f => cexp x cenv benv renv env nxt (fun A n1 => cexp y cenv benv renv env n1 (fun B n2 =>
                        let tc := ctailb t cenv benv renv env n2 in Eif c A B tc (ctailb f cenv benv renv env (after n2 tc))))
  | BbIfB c t f => ccond c cenv benv renv env nxt (fun n => ctailb t cenv benv renv env n) (fun n => ctailb f cenv benv renv env n)
  | BbMatch c b0 b1 => let t0 := ctailb b0 cenv benv renv env nxt in
                       Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                         (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                              (ctailb b1 (Avar (after nxt t0) :: cenv) benv renv env (Pos.succ (after nxt t0))))
  end.
End C.

(** a callee's counters nest S at most 2^20 deep; the recursive call's counters after the first are not grown *)
Fixpoint noadd (c : scnt) : bool := match c with CAdd _ _ => false | CS c | CPred c => noadd c | _ => true end.
Definition shallow (c : scnt) : bool := (Z.of_nat (cdepth c) <=? 1048576)%Z && noadd c.
Definition flat (c : scnt) : bool := Nat.eqb (cdepth c) 0 && noadd c.
(** a counter bound by a let joins the function's counters, all below its bound: a variable or a budget with no successor
    over it, or one built of [O], [S] and budgets only, at most 2^20 successors deep *)
Fixpoint cfree (c : scnt) : bool := match c with CS c | CPred c => cfree c | CAdd a b => cfree a && cfree b | CVar _ => false | _ => true end.
Definition letc_ok (c : scnt) : bool := flat c || (cfree c && shallow c).

(** well formed, in a function whose callees have the signatures [sigs]: the recursive call only where [r] allows it, with
    [nx] counters after the first and [k] numbers; the memory read, or given to a callee, only where there is one ([mok]); a
    callee called for a number gives back a number *)
(** a record built in a constructor's form (step 28), read off the syntax: the tag a written constructor number, the fields after
    the constructor's own written zeros *)
Fixpoint zeros_s (w : nat) (es : sexps) : bool :=
  match es with
  | SNil => true
  | SCons e r => match w with O => match e with SInt x => PrimInt63.eqb x 0%uint63 | _ => false end && zeros_s O r | S w' => zeros_s w' r end
  | _ => false
  end.
Definition canon_s (g : option (list nat)) (es : sexps) : bool :=
  match g with
  | None => true
  | Some ws => match es with
               | SCons (SInt t) fs => existsb (fun c => PrimInt63.eqb t (ofn c) && zeros_s (nth c ws O) fs) (seq 0 (length ws))
               | _ => false
               end
  end.

(** the bound on the counters of function [j] of a program: its own when its signature gives one (step 33), else its index's *)
Definition cbz (j : nat) : Z := (4611686018427387904 - Z.of_nat j * 1048576)%Z.
Definition fbound (gs : sig) (j : nat) : Z := match sb gs with Some b => b | None => cbz j end.
(** the largest value of a counter whose variables are below [B] *)
(** a budget's largest value: a written number its value when it is in [kq_nat]'s range, any other 2^60 (step 37) *)
Definition cnat_max (e : sexp) : Z :=
  match e with
  | SInt j => if (0 <=? Sint63.to_Z j)%Z && (Sint63.to_Z j <=? 1152921504606846976)%Z then Sint63.to_Z j else 1152921504606846976%Z
  | _ => 1152921504606846976%Z
  end.
Fixpoint cmax (B : Z) (c : scnt) : Z :=
  match c with
  | CVar _ => (B - 1)%Z | CO => 0%Z | CS c => (cmax B c + 1)%Z | CNat e => cnat_max e | CPred c => cmax B c
  | CAdd a b => (cmax B a + cmax B b)%Z
  end.
(** [wf]'s first argument: the callees' signatures, the function's own bound if it has one, and the bounds of the counters in
    scope (step 35), the nearest first -- none for a counter below the function's own bound (a parameter, a let or a match of
    such), else its own.  The function's counters' bound is at most [ub] (its index is at least its callees' number) *)
(** a linear bound (step 37): coefficients over the function's counters, as the counter environment holds them below the
    counters bound since (the first counter last), and a constant *)
Definition linf : Type := (list Z * Z)%type.
Definition lzero : linf := ([], 0%Z).
Fixpoint lunitc (j : nat) : list Z := match j with O => [1%Z] | S j => 0%Z :: lunitc j end.
Definition lunit (j : nat) : linf := (lunitc j, 0%Z).
Fixpoint addc (a b : list Z) : list Z := match a, b with [], _ => b | _, [] => a | x :: a', y :: b' => (x + y)%Z :: addc a' b' end.
Definition ladd (a b : linf) : linf := (addc (fst a) (fst b), (snd a + snd b)%Z).
Definition lshift (z : Z) (a : linf) : linf := (fst a, (snd a + z)%Z).
Definition lscale (w : Z) (a : linf) : linf := (map (Z.mul w) (fst a), (w * snd a)%Z).
Fixpoint evc (cs : list Z) (pv : list nat) : Z := match cs, pv with x :: cs', v :: pv' => (x * Z.of_nat v + evc cs' pv')%Z | _, _ => 0%Z end.
Definition leval (a : linf) (pv : list nat) : Z := (evc (fst a) pv + snd a)%Z.
(** what [wf] knows of a counter variable: a bound of its own (none: the function's), and a linear bound *)
Definition cbe : Type := (option Z * linf)%type.
Definition cbe0 : cbe := (None, lzero).
Definition linat (bs : list cbe) (i : nat) : linf := if Nat.ltb i (length bs) then snd (nth i bs cbe0) else lunit (i - length bs).
Fixpoint clinf (bs : list cbe) (c : scnt) : linf :=
  match c with
  | CVar i => linat bs i | CO => lzero | CS c => lshift 1 (clinf bs c)
  | CNat e => ([], cnat_max e)
  | CPred c => clinf bs c | CAdd a b => ladd (clinf bs a) (clinf bs b)
  end.
Definition wfctx : Type := (list sig * ((option Z * list poly) * list cbe))%type.
Definition ub (sigs : wfctx) : Z :=
  match fst (fst (snd sigs)) with Some b => b | None => cbz (length (fst sigs)) end.
Definition cbv (B : Z) (o : option Z) : Z := match o with Some b => b | None => B end.
(** the largest value of a counter, each variable below its own bound ([B]: the function's) *)
Fixpoint cmaxv (B : Z) (bs : list cbe) (c : scnt) : Z :=
  match c with
  | CVar i => Z.max 0 (cbv B (fst (nth i bs cbe0)) - 1) | CO => 0%Z | CS c => (cmaxv B bs c + 1)%Z | CNat e => cnat_max e
  | CPred c => cmaxv B bs c | CAdd a b => (cmaxv B bs a + cmaxv B bs b)%Z
  end.
(** a counter whose variables are all below the function's own bound *)
Fixpoint pvars (bs : list cbe) (c : scnt) : bool :=
  match c with
  | CVar i => match fst (nth i bs cbe0) with None => true | Some _ => false end
  | CS c | CPred c => pvars bs c | CAdd a b => pvars bs a && pvars bs b | _ => true
  end.
Definition pushc (sigs : wfctx) (o : cbe) : wfctx :=
  (fst sigs, (fst (snd sigs), o :: snd (snd sigs))).
(** a let of a counter: below the function's bound when [letc_ok] says so (step 9) of a counter whose variables are below it,
    else below its own *)
Definition lbnd (sigs : wfctx) (c : scnt) : option Z :=
  if letc_ok c && pvars (snd (snd sigs)) c && (cmaxv (ub sigs) (snd (snd sigs)) c <? ub sigs)%Z then None
  else Some (cmaxv (ub sigs) (snd (snd sigs)) c + 1)%Z.
Definition letc_okv (sigs : wfctx) (c : scnt) : bool :=
  (letc_ok c && pvars (snd (snd sigs)) c && (cmaxv (ub sigs) (snd (snd sigs)) c <? ub sigs)%Z)
  || (cmaxv (ub sigs) (snd (snd sigs)) c + 1 <=? 4611686018427387904)%Z.
(** what a let of a counter pushes: its bound ([lbnd]) and its linear bound; what a match on a counter pushes for the
    predecessor: the matched variable's, less one *)
Definition cpush_let (sigs : wfctx) (c : scnt) : cbe := (lbnd sigs c, clinf (snd (snd sigs)) c).
Definition cpush_match (sigs : wfctx) (c : nat) : cbe := (fst (nth c (snd (snd sigs)) cbe0), lshift (-1) (linat (snd (snd sigs)) c)).
Fixpoint lc (ccs : scnts) : list scnt := match ccs with CNil => [] | CCons c r => c :: lc r end.
(** the recursion of a function whose counters have a weighted-sum bound (step 37): the weighted sum of the counters given, the
    predecessor first, is at most the current one -- coefficient by coefficient over the linear bounds, none on the first counter *)
Fixpoint coefs_le (a w : list Z) : bool :=
  match a, w with [], _ => true | x :: a', [] => (x <=? 0)%Z && coefs_le a' [] | x :: a', y :: w' => (x <=? y)%Z && coefs_le a' w' end.
Definition pot_ok (ws : list nat) (bs : list cbe) (ccs : scnts) : bool :=
  let wt := map Z.of_nat (tl ws) in
  let tot := fold_right ladd lzero (map (fun q => lscale (fst q) (snd q)) (combine wt (map (clinf bs) (lc ccs)))) in
  Nat.eqb (len_c ccs) (length (tl ws)) && coefs_le (fst tot) (rev wt) && (snd tot <=? Z.of_nat (hd O ws))%Z.
(** a linear bound at most one of the function's counters: no coefficient below 0, their sum at most 1, no constant above 0 *)
Definition lin1 (l : linf) : bool :=
  forallb (fun z => (0 <=? z)%Z) (fst l) && (fold_right Z.add 0%Z (fst l) <=? 1)%Z && (snd l <=? 0)%Z.
(** a polynomial at numbers; a weight vector as a polynomial of degree 1 *)
Fixpoint prodz (xs : list Z) (l : list nat) : Z := match l with [] => 1%Z | i :: l' => (nth i xs 0%Z * prodz xs l')%Z end.
Definition pevalz (P : poly) (xs : list Z) : Z := fold_right (fun m a => (Z.of_nat (fst m) * prodz xs (snd m) + a)%Z) 0%Z P.
Definition lpoly (ws : list nat) : poly := map (fun iw => (snd iw, [fst iw])) (combine (seq 0 (length ws)) ws).
(** polynomials with integer coefficients over the recursion's variables (step 39): the predecessor (variable 0) and the
    other counters (variable [j] the counter [j]); a polynomial in the counters at polynomials, expanded *)
Definition zpoly : Type := list (Z * list nat).
Definition zeval (A : zpoly) (v : list Z) : Z := fold_right (fun m a => (fst m * prodz v (snd m) + a)%Z) 0%Z A.
Definition zmul (A B : zpoly) : zpoly := flat_map (fun a => map (fun b => ((fst a * fst b)%Z, snd a ++ snd b)) B) A.
Definition zprod (As : list zpoly) : zpoly := fold_right zmul [(1%Z, [])] As.
Definition zsubst (P : poly) (s : nat -> zpoly) : zpoly := flat_map (fun m => zmul [(Z.of_nat (fst m), [])] (zprod (map s (snd m)))) P.
Definition zneg (A : zpoly) : zpoly := map (fun m => ((- fst m)%Z, snd m)) A.
(** a linear bound over the counters at the body's start (the other counters, the last first, then the first counter) as a
    polynomial in the recursion's variables: the first counter is the predecessor's successor *)
Definition zlin (n : nat) (l : linf) : zpoly :=
  (snd l, []) :: flat_map (fun ia : nat * Z => if Nat.ltb (fst ia) (Nat.pred n) then [(snd ia, [(Nat.pred n - fst ia)%nat])]
                                     else if Nat.eqb (fst ia) (Nat.pred n) then [(snd ia, [O]); (snd ia, [])] else [])
                          (combine (seq 0 (length (fst l))) (fst l)).
(** no coefficient below 0 once equal monomials are summed (each monomial's counters sorted) *)
Fixpoint ins (x : nat) (l : list nat) : list nat := match l with [] => [x] | y :: l' => if Nat.leb x y then x :: l else y :: ins x l' end.
Fixpoint isort (l : list nat) : list nat := match l with [] => [] | x :: l' => ins x (isort l') end.
Definition zcoef (A : zpoly) (k : list nat) : Z :=
  fold_right (fun m a => if list_eq_dec Nat.eq_dec (isort (snd m)) k then (fst m + a)%Z else a) 0%Z A.
Definition znonneg (A : zpoly) : bool :=
  forallb (fun k => (0 <=? zcoef A k)%Z) (nodup (list_eq_dec Nat.eq_dec) (map (fun m => isort (snd m)) A)).
(** the recursion keeps a polynomial from growing (step 39): at the start of the body against the recursive call's counters,
    the first counter the predecessor's successor and each other counter given at most its linear bound -- the difference
    expanded over the predecessor and the other counters, no coefficient below 0 *)
Definition ppot_ok (P : poly) (bs : list cbe) (ccs : scnts) : bool :=
  let n := S (len_c ccs) in
  let sold i := if Nat.eqb i O then [(1%Z, [O]); (1%Z, [])] else if Nat.ltb i n then [(1%Z, [i])] else [] in
  let snew i := if Nat.eqb i O then [(1%Z, [O])] else match nth_error (lc ccs) (Nat.pred i) with Some c => zlin n (clinf bs c) | None => [] end in
  znonneg (zsubst P sold ++ zneg (zsubst P snew)).
(** the recursive call's counters: without weights, each a flat variable at the function's bound or at most one of the
    function's counters (its linear bound); with them, keeping each polynomial from growing; each a machine number *)
Definition rec_ok (sigs : wfctx) (ccs : scnts) : bool :=
  match snd (fst (snd sigs)) with
  | [] => all_c (fun c => (flat c && pvars (snd (snd sigs)) c && (cmaxv (ub sigs) (snd (snd sigs)) c <? ub sigs)%Z
                           || lin1 (clinf (snd (snd sigs)) c))
                          && (cmaxv (ub sigs) (snd (snd sigs)) c <? 9223372036854775808)%Z) ccs
  | vs => forallb (fun P => ppot_ok P (snd (snd sigs)) ccs) vs
          && all_c (fun c => (cmaxv (ub sigs) (snd (snd sigs)) c <? 9223372036854775808)%Z) ccs
  end.
(** a call (steps 37 to 39): each counter given below the callee's bound, or each of its polynomials at them, each counter a machine number *)
Fixpoint wdot (ws : list nat) (zs : list Z) : Z := match ws, zs with w :: ws', z :: zs' => (Z.of_nat w * z + wdot ws' zs')%Z | _, _ => 0%Z end.
Definition cfits_b (gs : sig) (B : Z) (sigs : wfctx) (ccs : scnts) : bool :=
  match sv gs with
  | [] => all_c (fun c => (cmaxv (ub sigs) (snd (snd sigs)) c <? B)%Z && (B <=? 4611686018427387904)%Z) ccs
  | vs => forallb (fun P => (pevalz P (map (cmaxv (ub sigs) (snd (snd sigs))) (lc ccs)) <? B)%Z) vs
          && all_c (fun c => (cmaxv (ub sigs) (snd (snd sigs)) c <? 9223372036854775808)%Z) ccs && (B <=? 4611686018427387904)%Z
  end.
Fixpoint wf (sigs : wfctx) (r mok : bool) (nx : nat) (k : list kind) (rk : list nat) (e : sexp) {struct e} : bool :=
  match e with
  | SVar _ | SInt _ => true
  | SOp _ a b | SLet a b => wf sigs r mok nx k rk a && wf sigs r mok nx k rk b
  | SRd a b | SRd32 a b | SRd8 a b => mok && wf sigs r mok nx k rk a && wf sigs r mok nx k rk b
  | SIf _ a b t f => wf sigs r mok nx k rk a && wf sigs r mok nx k rk b && wf sigs r mok nx k rk t && wf sigs r mok nx k rk f
  | SRec ccs args => r && Nat.eqb (len_c ccs) nx && kinds_eqb (kinds_s rk args) k && rec_ok sigs ccs
                     && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args
  | SCall f ccs args =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (sk gs) && implb (sm gs) mok && negb (sr gs)
                   && negb (sw gs || isq gs) && cfits_b gs (fbound gs f) sigs ccs && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args
      | None => false
      end
  | SMatch c e0 e1 => wf sigs r mok nx k rk e0 && wf (pushc sigs (cpush_match sigs c)) r mok nx k rk e1
  | SIfB b t f => wfb sigs r mok nx k rk b && wf sigs r mok nx k rk t && wf sigs r mok nx k rk f
  | SLetB b e => wfb sigs r mok nx k rk b && wf sigs r mok nx k rk e
  | SLetC c e => wfc sigs r mok nx k rk c && letc_okv sigs c && wf (pushc sigs (cpush_let sigs c)) r mok nx k rk e
  | SFld _ _ => true
  | SLetR x e => wfr sigs r mok nx k rk x && wf sigs r mok nx k (rtype rk x :: rk) e
  | SMatchR x e => wfr sigs r mok nx k rk x && wf sigs r mok nx k rk e
  | SSplitR sj x e => Nat.eqb (rtype rk x) sj && wfr sigs r mok nx k rk x && wf sigs r mok nx k (rev (RJ sj) ++ rk) e
  | SHwf o args => Nat.eqb (len_s args) (hwf_arity o) && forallb (kind_eqb KNum) (kinds_s rk args) && wfs sigs r mok nx k rk args
  | SSize h => mok && wf sigs r mok nx k rk h
  end
with wfs (sigs : wfctx) (r mok : bool) (nx : nat) (k : list kind) (rk : list nat) (es : sexps) {struct es} : bool :=
  match es with SNil => true | SCons e es => wf sigs r mok nx k rk e && wfs sigs r mok nx k rk es
             | SConsB b es => wfb sigs r mok nx k rk b && wfs sigs r mok nx k rk es
             | SConsR x es => wfr sigs r mok nx k rk x && wfs sigs r mok nx k rk es end
with wfc (sigs : wfctx) (r mok : bool) (nx : nat) (k : list kind) (rk : list nat) (c : scnt) {struct c} : bool :=
  match c with CVar _ | CO => true | CS c | CPred c => wfc sigs r mok nx k rk c | CAdd a b => wfc sigs r mok nx k rk a && wfc sigs r mok nx k rk b
             | CNat e => wf sigs r mok nx k rk e end
with wfcs (sigs : wfctx) (r mok : bool) (nx : nat) (k : list kind) (rk : list nat) (cs : scnts) {struct cs} : bool :=
  match cs with CNil => true | CCons c cs => wfc sigs r mok nx k rk c && wfcs sigs r mok nx k rk cs end
with wfb (sigs : wfctx) (r mok : bool) (nx : nat) (k : list kind) (rk : list nat) (b : sbool) {struct b} : bool :=
  match b with
  | BCmp _ x y => wf sigs r mok nx k rk x && wf sigs r mok nx k rk y
  | BVar _ | BTrue | BFalse => true
  | BAnd x y | BOr x y => wfb sigs r mok nx k rk x && wfb sigs r mok nx k rk y
  | BNot x => wfb sigs r mok nx k rk x
  | BIfCmp _ a b x y => wf sigs r mok nx k rk a && wf sigs r mok nx k rk b && wfb sigs r mok nx k rk x && wfb sigs r mok nx k rk y
  | BMatchCnt c x0 x1 => wfb sigs r mok nx k rk x0 && wfb (pushc sigs (cpush_match sigs c)) r mok nx k rk x1
  (* a call of a function giving back a boolean (step 24): it keeps the memory *)
  | BCall f ccs args =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (sk gs) && implb (sm gs) mok && negb (sr gs)
                   && negb (sw gs) && match sq gs with Some KBool => true | _ => false end
                   && cfits_b gs (fbound gs f) sigs ccs && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args
      | None => false
      end
  (* a comparison of two counters (step 30): equal, less, at most *)
  | BCmpC c x y => match c with Ceq | Clt | Cle => true | _ => false end
                   && (cmaxv (ub sigs) (snd (snd sigs)) x <? 9223372036854775808)%Z && (cmaxv (ub sigs) (snd (snd sigs)) y <? 9223372036854775808)%Z
                   && wfc sigs r mok nx k rk x && wfc sigs r mok nx k rk y
  | BxIfB b x y => wfb sigs r mok nx k rk b && wfb sigs r mok nx k rk x && wfb sigs r mok nx k rk y
  | BxLet e x => wf sigs r mok nx k rk e && wfb sigs r mok nx k rk x
  | BxLetB b x => wfb sigs r mok nx k rk b && wfb sigs r mok nx k rk x
  | BxLetC c x => wfc sigs r mok nx k rk c && letc_okv sigs c && wfb (pushc sigs (cpush_let sigs c)) r mok nx k rk x
  | BxLetR y x => wfr sigs r mok nx k rk y && wfb sigs r mok nx k (rtype rk y :: rk) x
  | BxMatchR y x => wfr sigs r mok nx k rk y && wfb sigs r mok nx k rk x
  | BxSplitR sj y x => Nat.eqb (rtype rk y) sj && wfr sigs r mok nx k rk y && wfb sigs r mok nx k (rev (RJ sj) ++ rk) x
  end
(** a record: built of as many numbers as its type has fields *)
with wfr (sigs : wfctx) (r mok : bool) (nx : nat) (k : list kind) (rk : list nat) (x : srec) {struct x} : bool :=
  match x with
  | RVar i => Nat.ltb i (length rk)        (* a record variable in scope: its type is known *)
  | RMk ri es => canon_s (rtg (RO ri)) es && Nat.eqb (len_s es) (rn (RO ri)) && forallb (kind_eqb KNum) (kinds_s rk es) && wfs sigs r mok nx k rk es
  (* a call of a function giving back a record of type ri, read from the memory or not; a record of at least one field and
     at most 2^20 *)
  | RCall ri f ccs args =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (sk gs) && implb (sm gs) mok && negb (sr gs)
                   && negb (sw gs) && match sq gs with Some (KRec rj) => Nat.eqb ri rj | _ => false end
                   && Nat.leb 1 (rn (RO ri)) && (Z.of_nat (rn (RO ri)) <=? 1048576)%Z
                   && cfits_b gs (fbound gs f) sigs ccs && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args
      | None => false
      end
  (* a u64 operation: the result and both operands of types of two fields *)
  | RW64 ri _ a b => match rtg (RO ri) with None => true | Some _ => false end && Nat.eqb (rn (RO ri)) 2 && Nat.eqb (rn (RO (rtype rk a))) 2 && Nat.eqb (rn (RO (rtype rk b))) 2
                     && wfr sigs r mok nx k rk a && wfr sigs r mok nx k rk b
  | RLet e x => wf sigs r mok nx k rk e && wfr sigs r mok nx k rk x
  | RLetR y x => wfr sigs r mok nx k rk y && wfr sigs r mok nx k (rtype rk y :: rk) x
  | RIf ri _ a b x y => Nat.eqb (rtype rk x) ri && Nat.eqb (rtype rk y) ri && wf sigs r mok nx k rk a && wf sigs r mok nx k rk b
                        && wfr sigs r mok nx k rk x && wfr sigs r mok nx k rk y
  | RMatchR ri x y => Nat.eqb (rtype rk y) ri && wfr sigs r mok nx k rk x && wfr sigs r mok nx k rk y
  | RIfB ri b x y => Nat.eqb (rtype rk x) ri && Nat.eqb (rtype rk y) ri && wfb sigs r mok nx k rk b
                     && wfr sigs r mok nx k rk x && wfr sigs r mok nx k rk y
  | RLetB b x => wfb sigs r mok nx k rk b && wfr sigs r mok nx k rk x
  | RLetC c x => wfc sigs r mok nx k rk c && letc_okv sigs c && wfr (pushc sigs (cpush_let sigs c)) r mok nx k rk x
  | RMatchCnt ri c x y => Nat.eqb (rtype rk x) ri && Nat.eqb (rtype rk y) ri && wfr sigs r mok nx k rk x
                          && wfr (pushc sigs (cpush_match sigs c)) r mok nx k rk y
  | RSplitR ri sj x y => Nat.eqb (rtype rk x) sj && Nat.eqb (rtype (rev (RJ sj) ++ rk) y) ri && wfr sigs r mok nx k rk x
                         && wfr sigs r mok nx k (rev (RJ sj) ++ rk) y
  (* the one-level constructor of a record (not a data type): its numbers, then records of the types of its record fields *)
  | RMkR ri ns rs => match rtg (RO ri) with None => true | Some _ => false end && forallb (kind_eqb KNum) (kinds_s rk ns)
                     && kinds_eqb (kinds_s rk rs) (map KRec (RJ ri)) && Nat.eqb (len_s ns + fold_right (fun j a => rn (RO j) + a) O (RJ ri))%nat (rn (RO ri))
                     && wfs sigs r mok nx k rk ns && wfs sigs r mok nx k rk rs
  end.

(** a memory: its numbers as above; the recursive call only where [rm] allows it; a callee called for a memory takes one and
    gives one back *)
Fixpoint wfm (sigs : wfctx) (r rm mok : bool) (nx : nat) (k : list kind) (rk : list nat) (m : smem) {struct m} : bool :=
  match m with
  | MCur => true
  | MUpd h i v m | MUpd32 h i v m | MUpd8 h i v m => wf sigs r mok nx k rk h && wf sigs r mok nx k rk i && wf sigs r mok nx k rk v && wfm sigs r rm mok nx k rk m
  | MLet e m => wf sigs r mok nx k rk e && wfm sigs r rm mok nx k rk m
  | MLetM m1 m2 => wfm sigs r rm mok nx k rk m1 && wfm sigs r rm mok nx k rk m2
  | MIf _ a b m1 m2 => wf sigs r mok nx k rk a && wf sigs r mok nx k rk b && wfm sigs r rm mok nx k rk m1 && wfm sigs r rm mok nx k rk m2
  | MRec ccs args m => rm && Nat.eqb (len_c ccs) nx && kinds_eqb (kinds_s rk args) k && rec_ok sigs ccs
                       && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args && wfm sigs r rm mok nx k rk m
  | MCall f ccs args m =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (sk gs) && sm gs && sr gs && negb (sw gs || isq gs) && cfits_b gs (fbound gs f) sigs ccs
                   && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args && wfm sigs r rm mok nx k rk m
      | None => false
      end
  | MMatch c m0 m1 => wfm sigs r rm mok nx k rk m0 && wfm (pushc sigs (cpush_match sigs c)) r rm mok nx k rk m1
  | MIfB b m1 m2 => wfb sigs r mok nx k rk b && wfm sigs r rm mok nx k rk m1 && wfm sigs r rm mok nx k rk m2
  | MLetB b m => wfb sigs r mok nx k rk b && wfm sigs r rm mok nx k rk m
  | MLetC c m => wfc sigs r mok nx k rk c && letc_okv sigs c && wfm (pushc sigs (cpush_let sigs c)) r rm mok nx k rk m
  | MHw o args m => Nat.eqb (len_s args) (hw_arity o) && forallb (kind_eqb KNum) (kinds_s rk args) && wfs sigs r mok nx k rk args
                    && wfm sigs r rm mok nx k rk m
  | MLetR x m => wfr sigs r mok nx k rk x && wfm sigs r rm mok nx k (rtype rk x :: rk) m
  | MMatchR x m => wfr sigs r mok nx k rk x && wfm sigs r rm mok nx k rk m
  | MSplitR sj x m => Nat.eqb (rtype rk x) sj && wfr sigs r mok nx k rk x && wfm sigs r rm mok nx k (rev (RJ sj) ++ rk) m
  | MMatchP p m | MLetP p m => wfpv sigs r rm mok false nx k rk p && wfm sigs r rm mok nx k rk m
  | MCallP f ccs args p =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (removelast (sk gs)) && sp gs && sm gs && last_num (sk gs)
                   && sr gs && negb (sw gs || isq gs) && cfits_b gs (fbound gs f) sigs ccs
                   && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args && wfpv sigs r rm mok false nx k rk p
      | None => false
      end
  end
(* a number and a memory: its numbers and memories as a number made after memories reads them; the recursive call where [rp]
    allows it; a callee giving back a number and a memory takes one *)
with wfpv (sigs : wfctx) (r rm mok rp : bool) (nx : nat) (k : list kind) (rk : list nat) (p : spv) {struct p} : bool :=
  match p with
  | PvMk e m => wf sigs r mok nx k rk e && wfm sigs r rm mok nx k rk m
  | PvCall f ccs args m =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (sk gs) && sm gs && negb (sr gs) && negb (sw gs)
                   && match sq gs with Some KNum => true | _ => false end
                   && cfits_b gs (fbound gs f) sigs ccs && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args
                   && wfm sigs r rm mok nx k rk m
      | None => false
      end
  | PvRec ccs args m => rp && Nat.eqb (len_c ccs) nx && kinds_eqb (kinds_s rk args) k && rec_ok sigs ccs
                        && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args && wfm sigs r rm mok nx k rk m
  | PvLet e p => wf sigs r mok nx k rk e && wfpv sigs r rm mok rp nx k rk p
  | PvLetB c p => wfb sigs r mok nx k rk c && wfpv sigs r rm mok rp nx k rk p
  | PvLetC c p => wfc sigs r mok nx k rk c && letc_okv sigs c && wfpv (pushc sigs (cpush_let sigs c)) r rm mok rp nx k rk p
  | PvLetR x p => wfr sigs r mok nx k rk x && wfpv sigs r rm mok rp nx k (rtype rk x :: rk) p
  | PvMatchR x p => wfr sigs r mok nx k rk x && wfpv sigs r rm mok rp nx k rk p
  | PvSplitR sj x p => Nat.eqb (rtype rk x) sj && wfr sigs r mok nx k rk x && wfpv sigs r rm mok rp nx k (rev (RJ sj) ++ rk) p
  | PvCallP f ccs args p =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (removelast (sk gs)) && sp gs && sm gs && last_num (sk gs)
                   && negb (sr gs) && negb (sw gs) && match sq gs with Some KNum => true | _ => false end && cfits_b gs (fbound gs f) sigs ccs
                   && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args && wfpv sigs r rm mok rp nx k rk p
      | None => false
      end
  | PvLetM m p => wfm sigs r rm mok nx k rk m && wfpv sigs r rm mok rp nx k rk p
  | PvIf _ x y t f => wf sigs r mok nx k rk x && wf sigs r mok nx k rk y && wfpv sigs r rm mok rp nx k rk t && wfpv sigs r rm mok rp nx k rk f
  | PvIfB c t f => wfb sigs r mok nx k rk c && wfpv sigs r rm mok rp nx k rk t && wfpv sigs r rm mok rp nx k rk f
  | PvMatch c p0 p1 => wfpv sigs r rm mok rp nx k rk p0 && wfpv (pushc sigs (cpush_match sigs c)) r rm mok rp nx k rk p1
  | PvMatchP p q => wfpv sigs r rm mok rp nx k rk p && wfpv sigs r rm mok rp nx k rk q
  end.

(** a number made after memories: its numbers and memories as above; at the end the recursive call where [rx] allows it, with
    [nx] counters after the first and [k] numbers, or a call of a number function that writes *)

(** after a call that writes (step 47): a number that reads no memory and calls no function itself (checked as such, and as a
    number of the body: the code of the one, the meaning of the other) *)
Definition xfree (sigs : wfctx) (nx : nat) (k : list kind) (rk : list nat) (x : sx) : bool :=
  match x with XRet e => wf sigs false false nx k rk e && wf sigs false true nx k rk e | _ => false end.
(** the result a call gives: a number, or a boolean when [bq] *)
Definition resq (bq : bool) (gs : sig) : bool :=
  negb (sr gs) && match sq gs with None => negb bq | Some KBool => bq | _ => false end.
Fixpoint wfx (sigs : wfctx) (rx : bool) (nx : nat) (k : list kind) (rk : list nat) (x : sx) {struct x} : bool :=
  match x with
  | XRet e => wf sigs false true nx k rk e
  | XLetM m x => wfm sigs false false true nx k rk m && wfx sigs rx nx k rk x
  | XLet e x => wf sigs false true nx k rk e && wfx sigs rx nx k rk x
  | XLetB b x => wfb sigs false true nx k rk b && wfx sigs rx nx k rk x
  | XIf _ a b x1 x2 => wf sigs false true nx k rk a && wf sigs false true nx k rk b && wfx sigs rx nx k rk x1 && wfx sigs rx nx k rk x2
  | XIfB b x1 x2 => wfb sigs false true nx k rk b && wfx sigs rx nx k rk x1 && wfx sigs rx nx k rk x2
  | XMatch c x0 x1 => wfx sigs rx nx k rk x0 && wfx (pushc sigs (cpush_match sigs c)) rx nx k rk x1
  | XLetC c x => wfc sigs false true nx k rk c && letc_okv sigs c && wfx (pushc sigs (cpush_let sigs c)) rx nx k rk x
  | XRec ccs args m => rx && Nat.eqb (len_c ccs) nx && kinds_eqb (kinds_s rk args) k && rec_ok sigs ccs
                       && wfcs sigs false true nx k rk ccs && wfs sigs false true nx k rk args && wfm sigs false false true nx k rk m
  | XCall f ccs args m =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (sk gs) && sm gs && negb (sr gs) && sw gs
                   && cfits_b gs (fbound gs f) sigs ccs && wfcs sigs false true nx k rk ccs && wfs sigs false true nx k rk args
                   && wfm sigs false false true nx k rk m
      | None => false
      end
  | XLetR r x => wfr sigs false true nx k rk r && wfx sigs rx nx k (rtype rk r :: rk) x
  | XMatchR r x => wfr sigs false true nx k rk r && wfx sigs rx nx k rk x
  | XSplitR sj r x => Nat.eqb (rtype rk r) sj && wfr sigs false true nx k rk r && wfx sigs rx nx k (rev (RJ sj) ++ rk) x
  | XCallP f ccs args p =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (removelast (sk gs)) && sp gs && sm gs && last_num (sk gs)
                   && negb (sr gs) && negb (isq gs) && cfits_b gs (fbound gs f) sigs ccs
                   && wfcs sigs false true nx k rk ccs && wfs sigs false true nx k rk args && wfpv sigs false false true false nx k rk p
      | None => false
      end
  | XMatchP p x | XLetP p x => wfpv sigs false false true false nx k rk p && wfx sigs rx nx k rk x
  | XBind bq f ccs args m x =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (sk gs) && negb (sp gs) && resq bq gs
                   && cfits_b gs (fbound gs f) sigs ccs && wfcs sigs false true nx k rk ccs && wfs sigs false true nx k rk args
                   && wfm sigs false false true nx k rk m && (if sw gs then negb bq && xfree sigs nx k rk x else wfx sigs rx nx k rk x)
      | None => false
      end
  | XBindR ccs args m x => rx && Nat.eqb (len_c ccs) nx && kinds_eqb (kinds_s rk args) k && rec_ok sigs ccs
                           && wfcs sigs false true nx k rk ccs && wfs sigs false true nx k rk args && wfm sigs false false true nx k rk m
                           && xfree sigs nx k rk x
  | XBindP bq f ccs args p x =>
      match nth_error (fst sigs) f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && kinds_eqb (kinds_s rk args) (removelast (sk gs)) && sp gs && sm gs && last_num (sk gs)
                   && resq bq gs && cfits_b gs (fbound gs f) sigs ccs
                   && wfcs sigs false true nx k rk ccs && wfs sigs false true nx k rk args && wfpv sigs false false true false nx k rk p
                   && (if sw gs then negb bq && xfree sigs nx k rk x else wfx sigs rx nx k rk x)
      | None => false
      end
  end.

(** a record given back, of type [ri]: its numbers as above (the memory where [mok]); the recursive call where [rb] allows it;
    at the end a record of type [ri]: built, given by a call, or a record variable of that type *)
Fixpoint wfbr (sigs : wfctx) (r rb mok : bool) (nx : nat) (k : list kind) (rk : list nat) (ri : nat) (b : sbr) {struct b} : bool :=
  match b with
  | BRet x => Nat.eqb (rtype rk x) ri && wfr sigs r mok nx k rk x
  | BRec ccs args => rb && Nat.eqb (len_c ccs) nx && kinds_eqb (kinds_s rk args) k && rec_ok sigs ccs
                     && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args
  | BMatchRec ccs args b =>
      rb && Nat.eqb (len_c ccs) nx && kinds_eqb (kinds_s rk args) k && rec_ok sigs ccs
      && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args && wfbr sigs r rb mok nx k rk ri b
  | BLetRec ccs args b =>
      rb && Nat.eqb (len_c ccs) nx && kinds_eqb (kinds_s rk args) k && rec_ok sigs ccs
      && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args && wfbr sigs r rb mok nx k (ri :: rk) ri b
  | BLet e b => wf sigs r mok nx k rk e && wfbr sigs r rb mok nx k rk ri b
  | BLetB c b => wfb sigs r mok nx k rk c && wfbr sigs r rb mok nx k rk ri b
  | BLetC c b => wfc sigs r mok nx k rk c && letc_okv sigs c && wfbr (pushc sigs (cpush_let sigs c)) r rb mok nx k rk ri b
  | BLetR x b => wfr sigs r mok nx k rk x && wfbr sigs r rb mok nx k (rtype rk x :: rk) ri b
  | BMatchR x b => wfr sigs r mok nx k rk x && wfbr sigs r rb mok nx k rk ri b
  | BSplitR sj x b => Nat.eqb (rtype rk x) sj && wfr sigs r mok nx k rk x && wfbr sigs r rb mok nx k (rev (RJ sj) ++ rk) ri b
  | BIf _ x y t f => wf sigs r mok nx k rk x && wf sigs r mok nx k rk y && wfbr sigs r rb mok nx k rk ri t && wfbr sigs r rb mok nx k rk ri f
  | BIfB c t f => wfb sigs r mok nx k rk c && wfbr sigs r rb mok nx k rk ri t && wfbr sigs r rb mok nx k rk ri f
  | BMatch c b0 b1 => wfbr sigs r rb mok nx k rk ri b0 && wfbr (pushc sigs (cpush_match sigs c)) r rb mok nx k rk ri b1
  end.

Fixpoint wfbb (sigs : wfctx) (r rb mok : bool) (nx : nat) (k : list kind) (rk : list nat) (b : sbb) {struct b} : bool :=
  match b with
  | BbRet x => wfb sigs r mok nx k rk x
  | BbRec ccs args | BbNotRec ccs args => rb && Nat.eqb (len_c ccs) nx && kinds_eqb (kinds_s rk args) k && rec_ok sigs ccs
                     && wfcs sigs r mok nx k rk ccs && wfs sigs r mok nx k rk args
  | BbLet e b => wf sigs r mok nx k rk e && wfbb sigs r rb mok nx k rk b
  | BbLetB c b => wfb sigs r mok nx k rk c && wfbb sigs r rb mok nx k rk b
  | BbLetC c b => wfc sigs r mok nx k rk c && letc_okv sigs c && wfbb (pushc sigs (cpush_let sigs c)) r rb mok nx k rk b
  | BbLetR x b => wfr sigs r mok nx k rk x && wfbb sigs r rb mok nx k (rtype rk x :: rk) b
  | BbMatchR x b => wfr sigs r mok nx k rk x && wfbb sigs r rb mok nx k rk b
  | BbSplitR sj x b => Nat.eqb (rtype rk x) sj && wfr sigs r mok nx k rk x && wfbb sigs r rb mok nx k (rev (RJ sj) ++ rk) b
  | BbIf _ x y t f => wf sigs r mok nx k rk x && wf sigs r mok nx k rk y && wfbb sigs r rb mok nx k rk t && wfbb sigs r rb mok nx k rk f
  | BbIfB c t f => wfb sigs r mok nx k rk c && wfbb sigs r rb mok nx k rk t && wfbb sigs r rb mok nx k rk f
  | BbMatch c b0 b1 => wfbb sigs r rb mok nx k rk b0 && wfbb (pushc sigs (cpush_match sigs c)) r rb mok nx k rk b1
  end.

(** blocks shared with another processor (step 18): in a program that lists them, a plain access to a narrow block names it
    by a number written where it is used, not one of them (the translator's rule, §9.4); nothing asked when none is listed.
    A check beside the theorem, as [wf] is: the sequential meaning describes such a program only if it holds *)
Definition sh_blk (sh : list i63) (h : sexp) : bool :=
  match sh with
  | [] => true
  | _ => match h with SInt n => negb (existsb (PrimInt63.eqb n) sh) | _ => false end
  end.
Fixpoint sh_e (sh : list i63) (e : sexp) {struct e} : bool :=
  match e with
  | SVar _ | SInt _ | SFld _ _ => true
  | SOp _ a b | SLet a b | SRd a b => sh_e sh a && sh_e sh b
  | SRd32 a b | SRd8 a b => sh_blk sh a && sh_e sh a && sh_e sh b
  | SIf _ a b t f => sh_e sh a && sh_e sh b && sh_e sh t && sh_e sh f
  | SRec ccs args | SCall _ ccs args => sh_cs sh ccs && sh_es sh args
  | SMatch _ e0 e1 => sh_e sh e0 && sh_e sh e1
  | SIfB b t f => sh_b sh b && sh_e sh t && sh_e sh f
  | SLetB b e => sh_b sh b && sh_e sh e
  | SLetC c e => sh_c sh c && sh_e sh e
  | SLetR x e | SMatchR x e | SSplitR _ x e => sh_r sh x && sh_e sh e
  | SHwf _ args => sh_es sh args
  | SSize h => sh_e sh h
  end
with sh_es (sh : list i63) (es : sexps) {struct es} : bool :=
  match es with
  | SNil => true
  | SCons e r => sh_e sh e && sh_es sh r
  | SConsB b r => sh_b sh b && sh_es sh r
  | SConsR x r => sh_r sh x && sh_es sh r
  end
with sh_c (sh : list i63) (c : scnt) {struct c} : bool :=
  match c with CVar _ | CO => true | CS c | CPred c => sh_c sh c | CAdd a b => sh_c sh a && sh_c sh b | CNat e => sh_e sh e end
with sh_cs (sh : list i63) (cs : scnts) {struct cs} : bool :=
  match cs with CNil => true | CCons c r => sh_c sh c && sh_cs sh r end
with sh_b (sh : list i63) (b : sbool) {struct b} : bool :=
  match b with
  | BCmp _ x y => sh_e sh x && sh_e sh y
  | BVar _ | BTrue | BFalse => true
  | BAnd x y | BOr x y => sh_b sh x && sh_b sh y
  | BNot x => sh_b sh x
  | BIfCmp _ a b x y => sh_e sh a && sh_e sh b && sh_b sh x && sh_b sh y
  | BMatchCnt _ x0 x1 => sh_b sh x0 && sh_b sh x1
  | BCall _ ccs args => sh_cs sh ccs && sh_es sh args
  | BCmpC _ x y => sh_c sh x && sh_c sh y
  | BxIfB b x y => sh_b sh b && sh_b sh x && sh_b sh y
  | BxLet e x => sh_e sh e && sh_b sh x
  | BxLetB b x => sh_b sh b && sh_b sh x
  | BxLetC c x => sh_c sh c && sh_b sh x
  | BxLetR y x | BxMatchR y x | BxSplitR _ y x => sh_r sh y && sh_b sh x
  end
with sh_r (sh : list i63) (x : srec) {struct x} : bool :=
  match x with
  | RVar _ => true
  | RMk _ es => sh_es sh es
  | RCall _ _ ccs args => sh_cs sh ccs && sh_es sh args
  | RW64 _ _ a b => sh_r sh a && sh_r sh b
  | RLet e x => sh_e sh e && sh_r sh x
  | RLetR y x => sh_r sh y && sh_r sh x
  | RIf _ _ a b x y => sh_e sh a && sh_e sh b && sh_r sh x && sh_r sh y
  | RMatchR _ x y | RSplitR _ _ x y => sh_r sh x && sh_r sh y
  | RMkR _ ns rs => sh_es sh ns && sh_es sh rs
  | RIfB _ b x y => sh_b sh b && sh_r sh x && sh_r sh y
  | RLetB b x => sh_b sh b && sh_r sh x
  | RLetC c x => sh_c sh c && sh_r sh x
  | RMatchCnt _ _ x y => sh_r sh x && sh_r sh y
  end.
Fixpoint sh_m (sh : list i63) (m : smem) {struct m} : bool :=
  match m with
  | MCur => true
  | MUpd h i v m => sh_e sh h && sh_e sh i && sh_e sh v && sh_m sh m
  | MUpd32 h i v m | MUpd8 h i v m => sh_blk sh h && sh_e sh h && sh_e sh i && sh_e sh v && sh_m sh m
  | MLet e m => sh_e sh e && sh_m sh m
  | MLetM m1 m2 => sh_m sh m1 && sh_m sh m2
  | MIf _ a b m1 m2 => sh_e sh a && sh_e sh b && sh_m sh m1 && sh_m sh m2
  | MRec ccs args m | MCall _ ccs args m => sh_cs sh ccs && sh_es sh args && sh_m sh m
  | MMatch _ m0 m1 => sh_m sh m0 && sh_m sh m1
  | MIfB b m1 m2 => sh_b sh b && sh_m sh m1 && sh_m sh m2
  | MLetB b m => sh_b sh b && sh_m sh m
  | MLetC c m => sh_c sh c && sh_m sh m
  | MHw _ args m => sh_es sh args && sh_m sh m
  | MLetR x m | MMatchR x m | MSplitR _ x m => sh_r sh x && sh_m sh m
  | MMatchP p m | MLetP p m => sh_pv sh p && sh_m sh m
  | MCallP _ ccs args p => sh_cs sh ccs && sh_es sh args && sh_pv sh p
  end
with sh_pv (sh : list i63) (p : spv) {struct p} : bool :=
  match p with
  | PvMk e m => sh_e sh e && sh_m sh m
  | PvCall _ ccs args m | PvRec ccs args m => sh_cs sh ccs && sh_es sh args && sh_m sh m
  | PvCallP _ ccs args p => sh_cs sh ccs && sh_es sh args && sh_pv sh p
  | PvLet e p => sh_e sh e && sh_pv sh p
  | PvLetB c p => sh_b sh c && sh_pv sh p
  | PvLetC c p => sh_c sh c && sh_pv sh p
  | PvLetR x p | PvMatchR x p | PvSplitR _ x p => sh_r sh x && sh_pv sh p
  | PvLetM m p => sh_m sh m && sh_pv sh p
  | PvIf _ x y t f => sh_e sh x && sh_e sh y && sh_pv sh t && sh_pv sh f
  | PvIfB c t f => sh_b sh c && sh_pv sh t && sh_pv sh f
  | PvMatch _ p0 p1 => sh_pv sh p0 && sh_pv sh p1
  | PvMatchP p q => sh_pv sh p && sh_pv sh q
  end.
Fixpoint sh_x (sh : list i63) (x : sx) {struct x} : bool :=
  match x with
  | XRet e => sh_e sh e
  | XLetM m x => sh_m sh m && sh_x sh x
  | XLet e x => sh_e sh e && sh_x sh x
  | XLetB b x => sh_b sh b && sh_x sh x
  | XIf _ a b x1 x2 => sh_e sh a && sh_e sh b && sh_x sh x1 && sh_x sh x2
  | XIfB b x1 x2 => sh_b sh b && sh_x sh x1 && sh_x sh x2
  | XMatch _ x0 x1 => sh_x sh x0 && sh_x sh x1
  | XLetC c x => sh_c sh c && sh_x sh x
  | XRec ccs args m | XCall _ ccs args m => sh_cs sh ccs && sh_es sh args && sh_m sh m
  | XCallP _ ccs args p => sh_cs sh ccs && sh_es sh args && sh_pv sh p
  | XBind _ _ ccs args m x | XBindR ccs args m x => sh_cs sh ccs && sh_es sh args && sh_m sh m && sh_x sh x
  | XBindP _ _ ccs args p x => sh_cs sh ccs && sh_es sh args && sh_pv sh p && sh_x sh x
  | XLetR r x | XMatchR r x | XSplitR _ r x => sh_r sh r && sh_x sh x
  | XMatchP p x | XLetP p x => sh_pv sh p && sh_x sh x
  end.
Fixpoint sh_br (sh : list i63) (b : sbr) {struct b} : bool :=
  match b with
  | BRet x => sh_r sh x
  | BRec ccs args => sh_cs sh ccs && sh_es sh args
  | BMatchRec ccs args b | BLetRec ccs args b => sh_cs sh ccs && sh_es sh args && sh_br sh b
  | BLet e b => sh_e sh e && sh_br sh b
  | BLetB c b => sh_b sh c && sh_br sh b
  | BLetC c b => sh_c sh c && sh_br sh b
  | BLetR x b | BMatchR x b | BSplitR _ x b => sh_r sh x && sh_br sh b
  | BIf _ x y t f => sh_e sh x && sh_e sh y && sh_br sh t && sh_br sh f
  | BIfB c t f => sh_b sh c && sh_br sh t && sh_br sh f
  | BMatch _ b0 b1 => sh_br sh b0 && sh_br sh b1
  end.
Fixpoint sh_bb (sh : list i63) (b : sbb) {struct b} : bool :=
  match b with
  | BbRet x => sh_b sh x
  | BbRec ccs args | BbNotRec ccs args => sh_cs sh ccs && sh_es sh args
  | BbLet e b => sh_e sh e && sh_bb sh b
  | BbLetB c b => sh_b sh c && sh_bb sh b
  | BbLetC c b => sh_c sh c && sh_bb sh b
  | BbLetR x b | BbMatchR x b | BbSplitR _ x b => sh_r sh x && sh_bb sh b
  | BbIf _ x y t f => sh_e sh x && sh_e sh y && sh_bb sh t && sh_bb sh f
  | BbIfB c t f => sh_b sh c && sh_bb sh t && sh_bb sh f
  | BbMatch _ b0 b1 => sh_bb sh b0 && sh_bb sh b1
  end.
Definition sh_ok (sh : list i63) (b : fbody) : bool :=
  match b with
  | FRec e0 e1 => sh_e sh e0 && sh_e sh e1
  | FPlain e => sh_e sh e
  | FRecM m0 m1 => sh_m sh m0 && sh_m sh m1
  | FPlainM m => sh_m sh m
  | FPlainX x => sh_x sh x
  | FRecX x0 x1 => sh_x sh x0 && sh_x sh x1
  | FRecR b0 b1 => sh_br sh b0 && sh_br sh b1
  | FPlainR b => sh_br sh b
  | FRecB b0 b1 => sh_bb sh b0 && sh_bb sh b1
  | FPlainB b => sh_bb sh b
  | FRecP p0 p1 => sh_pv sh p0 && sh_pv sh p1
  | FPlainP p => sh_pv sh p
  end.

(** the types of a function's record parameters, the last one first (as the meaning binds them) *)
Definition rk0 (ks : list kind) : list nat := rev (flat_map (fun k => match k with KRec ri => [ri] | _ => [] end) ks).

(** a function's own bound, when it has one (step 33; step 40: from what its callers give it, however small): at least 1, a
    machine number's room above it *)
Definition bok (o : option Z) : bool :=
  match o with Some b => (0 <? b)%Z && (b <=? 4611686018427387904)%Z | None => true end.
(** what [wf] starts a body with: the callees, the own bound and weights; in a recursive body the first counter's predecessor,
    its linear bound the first counter's less one (step 37) *)
Definition wctx (sigs : list sig) (gs : sig) (rc : bool) : wfctx :=
  (sigs, ((sb gs, sv gs), if rc then [(None, lshift (-1) (lunit (Nat.pred (sn gs))))] else [])).
Definition swok0 (gs : sig) : bool :=
  match sv gs with
  | [] => true
  | vs => forallb (fun i => existsb (fun P => existsb (fun m => Nat.leb 1 (fst m) && list_eq_dec Nat.eq_dec (snd m) [i]) P) vs) (seq 0 (sn gs))
  end.
(* a function's own signature: its body is read on the two components (step 44) *)
Definition swok (gs : sig) : bool := swok0 gs && negb (sp gs).
Definition wf_f (sigs : list sig) (gs : sig) (b : fbody) : bool :=
  bok (sb gs) && swok gs &&
  match sq gs with
  | Some KNum =>
      negb (sr gs) && negb (sw gs) && sm gs &&
      match b with
      | FRecP p0 p1 => negb (Nat.eqb (sn gs) 0) && wfpv (wctx sigs gs false) false false true false (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) p0
                       && wfpv (wctx sigs gs true) false false true true (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) p1
      | FPlainP pp => wfpv (wctx sigs gs false) false false true false 0 (sk gs) (rk0 (sk gs)) pp
      | _ => false
      end
  | Some KBool =>
      negb (sr gs) && negb (sw gs) &&
      match b with
      | FRecB b0 b1 => negb (Nat.eqb (sn gs) 0) && wfbb (wctx sigs gs false) false false (sm gs) (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) b0
                       && wfbb (wctx sigs gs true) false true (sm gs) (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) b1
      | FPlainB bb => wfbb (wctx sigs gs false) false false (sm gs) 0 (sk gs) (rk0 (sk gs)) bb
      | _ => false
      end
  | Some (KRec ri) =>
      Nat.leb 1 (rn (RO ri)) && (Z.of_nat (rn (RO ri)) <=? 1048576)%Z && negb (sr gs) && negb (sw gs) &&
      match b with
      | FRecR b0 b1 => negb (Nat.eqb (sn gs) 0) && wfbr (wctx sigs gs false) false false (sm gs) (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) ri b0
                       && wfbr (wctx sigs gs true) false true (sm gs) (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) ri b1
      | FPlainR bb => wfbr (wctx sigs gs false) false false (sm gs) 0 (sk gs) (rk0 (sk gs)) ri bb
      | _ => false
      end
  | None =>
  match b with
  | FRec e0 e1 => negb (Nat.eqb (sn gs) 0) && negb (sr gs) && negb (sw gs) && wf (wctx sigs gs false) false (sm gs) (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) e0
                  && wf (wctx sigs gs true) true (sm gs) (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) e1
  | FPlain e => negb (sr gs) && negb (sw gs) && wf (wctx sigs gs false) false (sm gs) 0 (sk gs) (rk0 (sk gs)) e
  | FRecM m0 m1 => negb (Nat.eqb (sn gs) 0) && sr gs && negb (sw gs) && sm gs && wfm (wctx sigs gs false) false false true (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) m0
                   && wfm (wctx sigs gs true) false true true (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) m1
  | FPlainM m => sr gs && negb (sw gs) && sm gs && wfm (wctx sigs gs false) false false true 0 (sk gs) (rk0 (sk gs)) m
  | FPlainX x => negb (sr gs) && sw gs && sm gs && wfx (wctx sigs gs false) false 0 (sk gs) (rk0 (sk gs)) x
  | FRecX x0 x1 => negb (Nat.eqb (sn gs) 0) && negb (sr gs) && sw gs && sm gs && wfx (wctx sigs gs false) false (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) x0
                   && wfx (wctx sigs gs true) true (Nat.pred (sn gs)) (sk gs) (rk0 (sk gs)) x1
  | FRecR _ _ | FPlainR _ | FRecB _ _ | FPlainB _ | FRecP _ _ | FPlainP _ => false
  end end.

(** the function: the counters in 1 .. sn, then the numbers; the next variable holds the first counter's predecessor *)
Definition params (n : nat) (ks : list kind) : list ident := map Pos.of_succ_nat (seq 0 (wsum ks + n)).
Definition cenv0 (n : nat) : list atom := map (fun i => Avar (Pos.of_succ_nat i)) (rev (seq 0 n)).
(** the parameters after the counters with their places, and the atoms of those of one kind, the last one first *)
Fixpoint kpos (ks : list kind) (p : nat) : list (kind * nat) := match ks with [] => [] | k :: ks => (k, p) :: kpos ks (p + kw k) end.
Definition katoms (c : kind) (n : nat) (ks : list kind) : list atom :=
  rev (map (fun kp => Avar (Pos.of_succ_nat (snd kp))) (filter (fun kp => kind_eqb (fst kp) c) (kpos ks n))).
Definition env0 (n : nat) (ks : list kind) : list atom := katoms KNum n ks.
Definition benv0 (n : nat) (ks : list kind) : list atom := katoms KBool n ks.
(** the atoms of the record parameters, one list per record (its fields), the last one first *)
Definition is_rk (k : kind) : bool := match k with KRec _ => true | _ => false end.
Definition renv0 (n : nat) (ks : list kind) : list (list atom) :=
  rev (map (fun kp => map (fun q => Avar (Pos.of_succ_nat q)) (seq (snd kp) (kw (fst kp)))) (filter (fun kp => is_rk (fst kp)) (kpos ks n))).
Definition pmv (gs : sig) : ident := Pos.of_succ_nat (wsum (sk gs) + sn gs).

(** the record type a function gives back *)
Definition sqi (gs : sig) : nat := match sq gs with Some (KRec ri) => ri | _ => O end.

Definition compile_f (gidf : nat -> ident) (j : nat) (gs : sig) (b : fbody) : fn :=
  let mv := pmv gs in
  mkfn (params (sn gs) (sk gs))
       match b with
       | FRec e0 e1 =>
           Eif Ceq (Avar 1%positive) (Aint 0%uint63)
               (ctail gidf (gidf j) mv e0 (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv))
               (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63)
                    (ctail gidf (gidf j) mv e1 (Avar mv :: cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)))
       | FPlain e => ctail gidf (gidf j) mv e (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)
       | FRecM m0 m1 =>
           Eif Ceq (Avar 1%positive) (Aint 0%uint63)
               (ctailm gidf (gidf j) mv m0 (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv))
               (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63)
                    (ctailm gidf (gidf j) mv m1 (Avar mv :: cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)))
       | FPlainM m => ctailm gidf (gidf j) mv m (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)
       | FPlainX x => ctailx gidf (gidf j) mv x (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)
       | FRecX x0 x1 =>
           Eif Ceq (Avar 1%positive) (Aint 0%uint63)
               (ctailx gidf (gidf j) mv x0 (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv))
               (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63)
                    (ctailx gidf (gidf j) mv x1 (Avar mv :: cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)))
       | FRecR b0 b1 =>
           Eif Ceq (Avar 1%positive) (Aint 0%uint63)
               (ctailr gidf (gidf j) mv (sqi gs) b0 (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv))
               (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63)
                    (ctailr gidf (gidf j) mv (sqi gs) b1 (Avar mv :: cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)))
       | FPlainR bb => ctailr gidf (gidf j) mv (sqi gs) bb (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)
       | FRecB b0 b1 =>
           Eif Ceq (Avar 1%positive) (Aint 0%uint63)
               (ctailb gidf (gidf j) mv b0 (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv))
               (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63)
                    (ctailb gidf (gidf j) mv b1 (Avar mv :: cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)))
       | FPlainB bb => ctailb gidf (gidf j) mv bb (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)
       | FRecP p0 p1 =>
           Eif Ceq (Avar 1%positive) (Aint 0%uint63)
               (ctailp gidf (gidf j) mv p0 (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv))
               (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63)
                    (ctailp gidf (gidf j) mv p1 (Avar mv :: cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)))
       | FPlainP pp => ctailp gidf (gidf j) mv pp (cenv0 (sn gs)) (benv0 (sn gs) (sk gs)) (renv0 (sn gs) (sk gs)) (env0 (sn gs) (sk gs)) (Pos.succ mv)
       end.


(** the slot block has room for every record a function of the program gives back: its fields after the first *)
Definition slot_room : Prop :=
  forall i, (1 < rn (RO i))%nat -> (Z.of_nat (rn (RO i)) <= Sint63.to_Z (KQ.KQBound.kq_len 63%uint63) + 1)%Z.

(** what a function's theorem says, and what a caller assumes of a callee: on counters below its bound, a function giving
    back a number keeps the memory; a function giving back a memory returns 0 and leaves that memory; a function giving back a
    number that writes the memory gives it with some end memory ([runx]) *)
(** the counters given to a function (step 37): each below its bound, or their weighted sum *)
Fixpoint dotw (ws cvs : list nat) : nat := match ws, cvs with w :: ws', c :: cvs' => w * c + dotw ws' cvs' | _, _ => O end.
Definition cfits (gs : sig) (B : Z) (cvs : list nat) : Prop :=
  match sv gs with [] => Forall (fun c => (Z.of_nat c < B)%Z) cvs | vs => Forall (fun P => (pevalz P (map Z.of_nat cvs) < B)%Z) vs end.
Definition callee_ok (P : prog) (id : ident) (B : Z) (gs : sig) (h : ftype gs) : Prop :=
  slot_room -> forall cvs vs M, length cvs = sn gs -> map kind_of vs = sk gs -> cfits gs B cvs ->
    if sw gs then exists M', runk P id (map ofn cvs ++ flat_map vflat vs) M (calln gs h cvs vs M) M'
    else runk P id (map ofn cvs ++ flat_map vflat vs) M (calln gs h cvs vs M)
           (if sr gs then callm gs h cvs vs M else match sq gs with Some _ => callm gs h cvs vs M | None => M end).

Definition callees_ok (P : prog) (gidf : nat -> ident) (cs : list callee) : Prop :=
  forall f, match nth_error cs f with Some (existT _ gs h) => callee_ok P (gidf f) (fbound gs f) gs h | None => True end.


(* ================================================================ the theorem, proved once for every syntax tree *)

(** a KQL atom whose variable, if any, is below [n] *)
(** a function with the pair (step 44): called on numbers and a memory it is the function of the components; given the
    numbers and the pair's number, the function given the pair *)
Lemma appc_cmapT : forall x A B (f : A -> B) h cvs, appc x B (cmapT x A B f h) cvs = f (appc x A h cvs).
Proof. induction x as [|x IH]; intros A B f h cvs; [reflexivity | destruct cvs as [|c cvs]; cbn [appc cmapT]; apply IH]. Qed.
Lemma appnTP_unpair : forall ks T g vs s, appnTP ks T g vs s = appnT ks true T (unpairT ks T g) vs s.
Proof.
  induction ks as [|[| |ri] ks IH]; intros T g vs s; cbn [appnTP appnT unpairT].
  - reflexivity.
  - destruct ks as [|k2 ks2].
    + destruct vs as [|[x| |] vs]; reflexivity.
    + destruct vs as [|[x|b|ri x] vs]; apply IH.
  - destruct vs as [|[x|b|ri x] vs]; apply IH.
  - destruct vs as [|v vs]; apply IH.
Qed.
Lemma last_num_split : forall ks, last_num ks = true -> ks = removelast ks ++ [KNum].
Proof.
  intros ks H. unfold last_num in H. destruct (rev ks) as [|k r] eqn:E; [discriminate|]. destruct k; try discriminate.
  rewrite <- (rev_involutive ks), E. cbn [rev]. rewrite removelast_last. reflexivity.
Qed.
Lemma appnTP_snoc : forall ks T g vs x s, map kind_of vs = removelast ks -> last_num ks = true ->
  appnTP ks T g (vs ++ [VNum x]) s = appnTPP ks T g vs (x, s).
Proof.
  intros ks T g vs x s Hk Hl. pose proof (last_num_split ks Hl) as Hs. clear Hl.
  revert vs Hk g Hs. induction ks as [|k ks IH]; intros vs Hk g Hs; [discriminate Hs|].
  destruct ks as [|k2 ks2].
  - cbn in Hs. inversion Hs; subst. destruct vs as [|v vs]; [|discriminate Hk]. reflexivity.
  - cbn [removelast app] in Hk, Hs. destruct vs as [|v vs]; [discriminate Hk|]. cbn [map] in Hk. injection Hk as Hv Hk.
    assert (Hs' : k2 :: ks2 = removelast (k2 :: ks2) ++ [KNum]) by (injection Hs; auto).
    destruct v as [n|b|ri y]; cbn [kind_of] in Hv; subst k; cbn [app appnTP appnTPP]; apply IH; auto.
Qed.
(** a call given the whole pair is the call given its number and memory *)
Lemma callf_snoc : forall gs h cvs vs pr, sp gs = true -> sm gs = true -> last_num (sk gs) = true -> map kind_of vs = removelast (sk gs) ->
  callf gs h cvs (vs ++ [VNum (fst pr)]) (snd pr) = callfp gs h cvs vs pr.
Proof.
  intros [x k m r w q b v p] h cvs vs [y t] P M L K. cbn [sp sm sk fst snd] in *. subst p m. cbn [callf callfp].
  apply appnTP_snoc; assumption.
Qed.
Lemma callnp_snoc : forall gs h cvs vs pr, sp gs = true -> sm gs = true -> last_num (sk gs) = true -> map kind_of vs = removelast (sk gs) ->
  calln gs h cvs (vs ++ [VNum (fst pr)]) (snd pr) = callnp gs h cvs vs pr.
Proof. intros gs h cvs vs pr P M L K. unfold calln, callnp. rewrite (callf_snoc gs h cvs vs pr P M L K). reflexivity. Qed.
Lemma callmp_snoc : forall gs h cvs vs pr, sp gs = true -> sm gs = true -> last_num (sk gs) = true -> map kind_of vs = removelast (sk gs) ->
  callm gs h cvs (vs ++ [VNum (fst pr)]) (snd pr) = callmp gs h cvs vs pr.
Proof. intros gs h cvs vs pr P M L K. unfold callm, callmp. rewrite (callf_snoc gs h cvs vs pr P M L K). reflexivity. Qed.
Lemma kinds_snoc : forall ks vs x, last_num ks = true -> map kind_of vs = removelast ks -> map kind_of (vs ++ [VNum x]) = ks.
Proof. intros ks vs x L K. rewrite map_app, K. cbn [map kind_of]. symmetry. apply last_num_split; exact L. Qed.

Definition atom_lt (a : atom) (n : ident) : Prop := match a with Avar x => Pos.lt x n | _ => True end.
(** [rho'] has what [rho] has below [n] *)
Context {RLs : RecLaws}.
Definition agree (rho rho' : env) (n : ident) : Prop := forall x, Pos.lt x n -> rho' ! x = rho ! x.
(** the atoms of [envA] hold the numbers of [denv], those of [cenvA] the counters of [cenv] (all read with 0 past the end) *)
Definition env_ok (rho : env) (envA : list atom) (denv : list i63) : Prop :=
  forall i, aval rho (nth i envA (Aint 0%uint63)) = Some (nth i denv 0%uint63).
Definition cenv_ok (rho : env) (cenvA : list atom) (cenv : list nat) : Prop :=
  forall i, aval rho (nth i cenvA (Aint 0%uint63)) = Some (ofn (nth i cenv O)).
(** a boolean is held as the number 1 or 0; the atoms of [benvA] hold the booleans of [benv] *)
Definition benv_ok (rho : env) (benvA : list atom) (benv : list bool) : Prop :=
  forall i, aval rho (nth i benvA (Aint 0%uint63)) = Some (b2i (nth i benv false)).
Definition lt_all (envA : list atom) (n : ident) : Prop := forall i, atom_lt (nth i envA (Aint 0%uint63)) n.
(** the atoms of each record variable hold its fields *)
Definition renv_ok (rho : env) (renvA : list (list atom)) (renv : list val) : Prop :=
  Forall2 (fun As v => avals rho As = Some (vflat v)) renvA renv.
Definition rlt_all (renvA : list (list atom)) (n : ident) : Prop := Forall (Forall (fun a => atom_lt a n)) renvA.
Definition cbound (B : Z) (cenv : list nat) : Prop := forall i, (Z.of_nat (nth i cenv O) < B)%Z.

Lemma aval_agree : forall rho rho' n a, agree rho rho' n -> atom_lt a n -> aval rho' a = aval rho a.
Proof. intros rho rho' n [x|i|i] A L; simpl in *; auto. Qed.

Lemma avals_agree : forall rho rho' n As, agree rho rho' n -> Forall (fun a => atom_lt a n) As -> avals rho' As = avals rho As.
Proof.
  induction As as [|a As IH]; intros A F; simpl; auto.
  inversion F; subst. rewrite (aval_agree rho rho' n a), IH; auto.
Qed.

Lemma atom_lt_mono : forall a n n', atom_lt a n -> Pos.le n n' -> atom_lt a n'.
Proof. intros [x|i|i] n n' L Le; simpl in *; auto. lia. Qed.

Lemma lt_all_mono : forall envA n n', lt_all envA n -> Pos.le n n' -> lt_all envA n'.
Proof. intros envA n n' L Le i. eapply atom_lt_mono; eauto. Qed.

Lemma Forall_atom_mono : forall As n n', Forall (fun a => atom_lt a n) As -> Pos.le n n' -> Forall (fun a => atom_lt a n') As.
Proof. intros As n n' F Le. eapply Forall_impl; [|exact F]. intros a H. exact (atom_lt_mono a n n' H Le). Qed.

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

Lemma agree_4 : forall rho rho1 rho2 rho3 rho4 nxt n1 n2 n3, agree rho rho1 nxt -> agree rho1 rho2 n1 -> agree rho2 rho3 n2 ->
  agree rho3 rho4 n3 -> Pos.le nxt n1 -> Pos.le n1 n2 -> Pos.le n2 n3 -> agree rho rho4 nxt.
Proof. intros rho rho1 rho2 rho3 rho4 nxt n1 n2 n3 A1 A2 A3 A4 L1 L2 L3 y Ly. rewrite A4 by lia. rewrite A3 by lia. rewrite A2 by lia. apply A1; auto. Qed.

Lemma env_ok_agree : forall rho rho' envA denv n, env_ok rho envA denv -> lt_all envA n -> agree rho rho' n -> env_ok rho' envA denv.
Proof. intros rho rho' envA denv n E L A i. rewrite (aval_agree rho rho' n); auto. Qed.

Lemma cenv_ok_agree : forall rho rho' cenvA cenv n, cenv_ok rho cenvA cenv -> lt_all cenvA n -> agree rho rho' n -> cenv_ok rho' cenvA cenv.
Proof. intros rho rho' cenvA cenv n E L A i. rewrite (aval_agree rho rho' n); auto. Qed.

Lemma env_ok_cons : forall rho envA denv a v, env_ok rho envA denv -> aval rho a = Some v -> env_ok rho (a :: envA) (v :: denv).
Proof. intros rho envA denv a v E A [|i]; simpl; auto. Qed.

Lemma cenv_ok_cons : forall rho cenvA cenv a v, cenv_ok rho cenvA cenv -> aval rho a = Some (ofn v) -> cenv_ok rho (a :: cenvA) (v :: cenv).
Proof. intros rho cenvA cenv a v E A [|i]; simpl; auto. Qed.

Lemma renv_ok_agree : forall rho rho' renvA renv n, renv_ok rho renvA renv -> rlt_all renvA n -> agree rho rho' n -> renv_ok rho' renvA renv.
Proof.
  intros rho rho' renvA renv n R L A. induction R as [|As v renvA renv H R IH]; constructor.
  - rewrite (avals_agree rho rho' n As A); [exact H | inversion L; auto].
  - apply IH. inversion L; auto.
Qed.
Lemma rlt_all_mono : forall renvA n n', rlt_all renvA n -> Pos.le n n' -> rlt_all renvA n'.
Proof. intros renvA n n' L Le. induction L as [|As renvA H L IH]; constructor; auto. eapply Forall_atom_mono; eauto. Qed.
Lemma benv_ok_agree : forall rho rho' benvA benv n, benv_ok rho benvA benv -> lt_all benvA n -> agree rho rho' n -> benv_ok rho' benvA benv.
Proof. intros rho rho' benvA benv n E L A i. rewrite (aval_agree rho rho' n); auto. Qed.

Lemma benv_ok_cons : forall rho benvA benv a v, benv_ok rho benvA benv -> aval rho a = Some (b2i v) -> benv_ok rho (a :: benvA) (v :: benv).
Proof. intros rho benvA benv a v E A [|i]; simpl; auto. Qed.

Lemma benv_ok_nil : forall rho, benv_ok rho [] [].
Proof. intros rho [|i]; reflexivity. Qed.

(** the operations on booleans held as 1 or 0 *)
Lemma b2i_land : forall x y, binop_sem Bland (b2i x) (b2i y) = b2i (andb x y).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma b2i_lor : forall x y, binop_sem Blor (b2i x) (b2i y) = b2i (orb x y).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma b2i_lxor : forall x, binop_sem Blxor (b2i x) 1%uint63 = b2i (negb x).
Proof. intros [|]; reflexivity. Qed.
Lemma b2i_eq0 : forall x, cmp_sem Ceq (b2i x) 0%uint63 = negb x.
Proof. intros [|]; reflexivity. Qed.

Lemma lt_all_nil : forall n, lt_all [] n.
Proof. intros n [|i]; exact Logic.I. Qed.

Lemma lt_all_cons : forall envA a n, lt_all envA n -> atom_lt a n -> lt_all (a :: envA) n.
Proof. intros envA a n L A [|i]; simpl; auto. Qed.

Lemma cbound_cons : forall B cenv v, cbound B cenv -> (Z.of_nat v < B)%Z -> cbound B (v :: cenv).
Proof. intros B cenv v C L [|i]; simpl; auto. Qed.

Lemma avals_app : forall rho l1 l2 v1 v2, avals rho l1 = Some v1 -> avals rho l2 = Some v2 -> avals rho (l1 ++ l2) = Some (v1 ++ v2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 v1 v2 A1 A2; simpl in *.
  - injection A1 as <-. exact A2.
  - destruct (aval rho a) eqn:Ea; [|discriminate]. destruct (avals rho l1) eqn:El; [|discriminate].
    injection A1 as <-. rewrite (IH l2 l v2 eq_refl A2). reflexivity.
Qed.

Lemma no_callees : forall P gidf, callees_ok P gidf [].
Proof. intros P gidf [|f]; exact Logic.I. Qed.

(** record variables: their atoms, a field's atom, the fields as numbers bound by a match *)
Lemma avals_nth : forall rho As vs j, avals rho As = Some vs -> aval rho (nth j As (Aint 0%uint63)) = Some (nth j vs 0%uint63).
Proof.
  induction As as [|a As IH]; intros vs j H; simpl in H.
  - injection H as <-. destruct j; reflexivity.
  - destruct (aval rho a) eqn:E1; [|discriminate]. destruct (avals rho As) eqn:E2; [|discriminate]. injection H as <-.
    destruct j; simpl; auto.
Qed.
Lemma avals_length : forall rho As vs, avals rho As = Some vs -> length As = length vs.
Proof.
  induction As as [|a As IH]; intros vs H; simpl in H; [injection H as <-; reflexivity|].
  destruct (aval rho a); [|discriminate]. destruct (avals rho As) eqn:E; [|discriminate]. injection H as <-. simpl. f_equal. apply IH; reflexivity.
Qed.
Lemma avals_rev : forall rho As vs, avals rho As = Some vs -> avals rho (rev As) = Some (rev vs).
Proof.
  induction As as [|a As IH]; intros vs H; simpl in H; [injection H as <-; reflexivity|].
  destruct (aval rho a) eqn:E1; [|discriminate]. destruct (avals rho As) eqn:E2; [|discriminate]. injection H as <-.
  simpl. apply avals_app; [apply IH; reflexivity | simpl; rewrite E1; reflexivity].
Qed.
Lemma renv_nth : forall rho renvA renv i, renv_ok rho renvA renv ->
  avals rho (nth i renvA [Aint 0%uint63]) = Some (vflat (nth i renv (VNum 0%uint63))).
Proof. intros rho renvA renv i R. revert i. induction R as [|As v renvA renv H R IH]; intros [|i]; simpl; auto. Qed.
Lemma rlt_nth : forall renvA n i, rlt_all renvA n -> Forall (fun a => atom_lt a n) (nth i renvA [Aint 0%uint63]).
Proof.
  intros renvA n i L. revert i. induction L as [|As renvA H L IH]; intros [|i]; simpl; auto; repeat constructor.
Qed.
Lemma Forall_nth_atom : forall As n j, Forall (fun a => atom_lt a n) As -> atom_lt (nth j As (Aint 0%uint63)) n.
Proof. intros As n j F. revert j. induction F as [|a As H F IH]; intros [|j]; simpl; auto. Qed.
Lemma env_ok_app : forall rho Bs ws envA denv, avals rho Bs = Some ws -> env_ok rho envA denv -> env_ok rho (Bs ++ envA) (ws ++ denv).
Proof.
  intros rho Bs ws envA denv V E i. pose proof (avals_length rho Bs ws V) as L.
  destruct (Nat.lt_ge_cases i (length Bs)) as [Li|Li].
  - rewrite !app_nth1 by lia. apply avals_nth; exact V.
  - rewrite !app_nth2 by lia. rewrite L. apply E.
Qed.
Lemma lt_all_app : forall Bs envA n, Forall (fun a => atom_lt a n) Bs -> lt_all envA n -> lt_all (Bs ++ envA) n.
Proof.
  intros Bs envA n F L i. destruct (Nat.lt_ge_cases i (length Bs)) as [Li|Li].
  - rewrite app_nth1 by lia. apply Forall_nth_atom; exact F.
  - rewrite app_nth2 by lia. apply L.
Qed.
(** a record built of numbers: its values are the numbers *)
Lemma flat_nums : forall cs rec cenv benv renv denv M es rk, forallb (kind_eqb KNum) (kinds_s rk es) = true ->
  flat_map vflat (denote_es cs rec cenv benv renv denv M es) = vnums (denote_es cs rec cenv benv renv denv M es) /\
  length (vnums (denote_es cs rec cenv benv renv denv M es)) = len_s es.
Proof.
  intros cs rec cenv benv renv denv M es rk. induction es as [|e es IH|b es IH|x es IH]; intros H; cbn [kinds_s forallb kind_eqb] in H;
    try discriminate; [split; reflexivity|].
  destruct (IH H) as [H1 H2]. cbn [denote_es flat_map vflat vnums]. split; [f_equal; exact H1 | simpl; f_equal; exact H2].
Qed.
Arguments flat_nums cs rec cenv benv renv denv M es {rk} _.
(** built in a constructor's form, a record or a data type gives its fields back (step 28) *)
Lemma rl_mk_c : forall i l, length l = rn (RO i) -> canon (rtg (RO i)) l = true -> relim (RO i) (rmk (RO i) l) (fun l => l) = l.
Proof.
  intros i l L C. destruct (rtg (RO i)) as [ws|] eqn:G; [| apply rl_mk; assumption].
  cbn [canon] in C. destruct l as [|t rest]; [discriminate C|].
  apply existsb_exists in C as (c & Hin & C). apply in_seq in Hin. apply andb_true_iff in C as [Ht Hz].
  apply eqb_correct in Ht. subst t. apply (rl_mk_tag i ws c rest G); [lia | simpl in L; lia | exact Hz].
Qed.
(** a record built in a constructor's form, read off the syntax, is in that form (step 28) *)
Lemma zeros_s_ok : forall cs rec cenv benv renv denv M es w, zeros_s w es = true ->
  zeros_from w (vnums (denote_es cs rec cenv benv renv denv M es)) = true.
Proof.
  intros cs rec cenv benv renv denv M es. induction es as [|e es IH|b es IH|x es IH]; intros w H; cbn [zeros_s] in H; try discriminate H.
  - reflexivity.
  - cbn [denote_es vnums flat_map]. destruct w as [|w].
    + destruct e; try (rewrite Bool.andb_false_l in H; discriminate H). apply andb_true_iff in H as [H0 H1].
      cbn [app denote_e zeros_from]. rewrite H0. apply (IH O H1).
    + apply (IH w H).
Qed.
Lemma canon_s_ok : forall cs rec cenv benv renv denv M es g, canon_s g es = true ->
  canon g (vnums (denote_es cs rec cenv benv renv denv M es)) = true.
Proof.
  intros cs rec cenv benv renv denv M es [ws|] H; [|reflexivity]. cbn [canon_s] in H.
  destruct es as [|e fs|b fs|x fs]; try discriminate H. destruct e; try discriminate H.
  cbn [denote_es vnums flat_map app denote_e canon]. fold (vnums (denote_es cs rec cenv benv renv denv M fs)).
  apply existsb_exists in H as (c & Hc & H). apply existsb_exists. exists c. split; [exact Hc|].
  apply andb_true_iff in H as [H0 H1]. rewrite H0. apply (zeros_s_ok _ _ _ _ _ _ _ _ _ H1).
Qed.


Lemma nth_sigs : forall (cs : list callee) f, nth_error (map (@projT1 _ _) cs) f = option_map (@projT1 _ _) (nth_error cs f).
Proof. induction cs as [|c cs IH]; intros [|f]; simpl; auto. Qed.

Lemma len_denote_es : forall cs rec cenv benv renv denv s es, length (denote_es cs rec cenv benv renv denv s es) = len_s es.
Proof. intros cs rec cenv benv renv denv s es. induction es; simpl; auto. Qed.
(** a call giving back a record, well formed: what [wfr] checks of it, one fact each *)
Lemma wfr_call_inv : forall sigs r mok nx k rk ri fi ccs args, wfr sigs r mok nx k rk (RCall ri fi ccs args) = true ->
  exists gs, nth_error (fst sigs) fi = Some gs /\ Nat.eqb (len_c ccs) (sn gs) = true /\ kinds_eqb (kinds_s rk args) (sk gs) = true /\
    implb (sm gs) mok = true /\ sr gs = false /\ sw gs = false /\ sq gs = Some (KRec ri) /\ (1 <= rn (RO ri))%nat /\ (Z.of_nat (rn (RO ri)) <= 1048576)%Z /\
    cfits_b gs (fbound gs fi) sigs ccs = true
    /\ wfcs sigs r mok nx k rk ccs = true /\ wfs sigs r mok nx k rk args = true.
Proof.
  intros sigs r mok nx k rk ri fi ccs args W. cbn [wfr] in W. destruct (nth_error (fst sigs) fi) as [gs|]; [|discriminate W].
  exists gs. destruct (sq gs) as [[| |rj]|] eqn:Q;
    try (cbv iota in W; repeat (rewrite Bool.andb_false_r in W || rewrite Bool.andb_false_l in W); discriminate W).
  - rewrite !andb_true_iff in W. destruct W as [[[[[[[[[[A1 A2] A3] A4] A5] A6] A7] A8] A9] A10] A11].
    apply Nat.eqb_eq in A6. subst rj. apply Nat.leb_le in A7. apply Z.leb_le in A8.
    apply negb_true_iff in A4. apply negb_true_iff in A5.
    repeat split; auto.
Qed.
(** the value a call gives back, when it is a record of type [ri] *)
Lemma vrec_of_kind : forall g (x : rtq (sr g) (sq g)) ri, sq g = Some (KRec ri) -> kind_of (vrec_of g x) = KRec ri.
Proof. intros [gx gk gm gr gw gq gb gv] x ri Q. simpl in *. subst gq. reflexivity. Qed.

(** a value of record type [i], cast to the type and taken apart, is its fields *)
Lemma to_rt_same : forall i x, to_rt i (VRec i x) = x.
Proof.
  intros i x. unfold to_rt. destruct (ndec i i) as [e|ne]; [| contradiction ne; reflexivity].
  rewrite (Eqdep_dec.UIP_refl_nat i e). reflexivity.
Qed.
Lemma to_rt_vflat : forall ri v, kind_of v = KRec ri -> relim (RO ri) (to_rt ri v) (fun l => l) = vflat v.
Proof. intros ri [n|b|rj x] K; cbn [kind_of] in K; try discriminate. injection K as ->. rewrite to_rt_same. reflexivity. Qed.

(** a record given back at the end of a body: built, or given by a call, of the type the function gives back *)
(** the record values in scope have the types [rk] says (step 16) *)
Definition rtyped (renv : list val) (rk : list nat) : Prop := map kind_of renv = map KRec rk.
Lemma rtyped_nth : forall renv rk i, rtyped renv rk -> (i < length rk)%nat -> kind_of (nth i renv (VNum 0%uint63)) = KRec (nth i rk O).
Proof.
  unfold rtyped. induction renv as [|v renv IH]; intros rk i T L; destruct rk as [|ri rk]; cbn [map length] in *; try discriminate T; try lia.
  injection T as T1 T2. destruct i as [|i]; cbn [nth]; [exact T1 | apply IH; [exact T2 | lia]].
Qed.
Lemma rtyped_cons : forall renv rk v ri, rtyped renv rk -> kind_of v = KRec ri -> rtyped (v :: renv) (ri :: rk).
Proof. unfold rtyped. intros renv rk v ri T K. cbn [map]. rewrite T, K. reflexivity. Qed.

Lemma rmatch_eq : forall (P : Type) v (F : list i63 -> P), rmatch v F = F (vflat v).
Proof. intros P [n|b|ri x] F; cbn [rmatch vflat]; [reflexivity | reflexivity | apply rl_nat]. Qed.
(** a value taken apart one level (step 43): its fields given to the continuation *)
Definition rsplit_p (v : val) : list i63 * list val := rsplit v (fun l rs => (l, rs)).
Lemma rsplit_eq : forall (P : Type) v (F : list i63 -> list val -> P), rsplit v F = F (fst (rsplit_p v)) (snd (rsplit_p v)).
Proof.
  intros P [n|b|ri x] F; unfold rsplit_p; cbn [rsplit]; [reflexivity | reflexivity |].
  rewrite (rs_nat ri x _ (fun l rs => F l (map vrec rs))), (rs_nat ri x _ (fun l rs => (l, map vrec rs))). reflexivity.
Qed.

(** a record's type, its variables in scope having the types [rk] *)
Lemma kind_denote_r : forall cbo, forall r mok nx k rk cs rec cenv benv renv denv s x, wfr (map (@projT1 _ _) cs, cbo) r mok nx k rk x = true ->
  rtyped renv rk -> kind_of (denote_r cs rec cenv benv renv denv s x) = KRec (rtype rk x).
Proof. intros cbo.
  intros r mok nx k rk cs rec cenv benv renv denv s x. revert cbo rk cenv benv renv denv.
  induction x as [i | rj es | rj fi ccs args | rj o a IHa b IHb | e x IH | y IHy x IHx | rj c a b x IHx y IHy | rj x IHx y IHy
                 | rj b x IHx y IHy | b x IHx | c x IHx | rj c x IHx y IHy | rj sj x IHx y IHy | rj ns rs];
    intros cbo rk cenv benv renv denv W T; cbn [rtype].
  - cbn [wfr] in W. apply Nat.ltb_lt in W. cbn [denote_r]. apply rtyped_nth; assumption.
  - reflexivity.
  - destruct (wfr_call_inv _ _ _ _ _ _ _ _ _ _ W) as (gs & Eg & _ & _ & _ & _ & _ & Q & _).
    cbn [fst] in Eg; rewrite nth_sigs in Eg. cbn [denote_r]. unfold callee in *. destruct (nth_error cs fi) as [[gs' h]|]; [|discriminate Eg].
    simpl in Eg. injection Eg as <-. apply vrec_of_kind; exact Q.
  - reflexivity.
  - cbn [wfr] in W. apply andb_true_iff in W as [_ Wx]. cbn [denote_r]. eapply IH; [exact Wx | exact T].
  - cbn [wfr] in W. apply andb_true_iff in W as [Wy Wx]. cbn [denote_r].
    eapply IHx; [exact Wx | apply rtyped_cons; [exact T | eapply IHy; [exact Wy | exact T]]].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [wfr] in W. apply andb_true_iff in W as [_ Wx]. cbn [denote_r]. eapply IHx; [exact Wx | exact T].
  - cbn [wfr] in W. apply andb_true_iff in W as [_ Wx]. cbn [denote_r]. eapply IHx; [exact Wx | exact T].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(** a record given back at the end of a body, of the type the function gives back *)
Lemma kind_denote_br : forall cbo, forall r mok nx k rk cs rec cenv benv renv denv s x ri,
  Nat.eqb (rtype rk x) ri && wfr (map (@projT1 _ _) cs, cbo) r mok nx k rk x = true -> rtyped renv rk ->
  wfr (map (@projT1 _ _) cs, cbo) r mok nx k rk x = true /\ kind_of (denote_r cs rec cenv benv renv denv s x) = KRec ri.
Proof. intros cbo.
  intros r mok nx k rk cs rec cenv benv renv denv s x ri W T. apply andb_true_iff in W as [E W]. apply Nat.eqb_eq in E.
  split; [exact W|]. rewrite <- E. eapply kind_denote_r; eauto.
Qed.
(** the record fields of a record taken apart one level (step 43): of the types [RJ] *)
Lemma rsplit_typed : forall v sj renv rk, kind_of v = KRec sj -> rtyped renv rk ->
  rtyped (rev (snd (rsplit_p v)) ++ renv) (rev (RJ sj) ++ rk).
Proof.
  intros v sj renv rk K T. destruct v as [n|b|ri x]; cbn [kind_of] in K; try discriminate. injection K as ->.
  unfold rtyped in *. unfold rsplit_p. cbn [rsplit]. rewrite (rs_nat sj x _ (fun l rs => (l, map vrec rs))). cbn [snd].
  rewrite !map_app, !map_rev, T. f_equal. f_equal. rewrite <- (rs_kinds sj x), !map_map. reflexivity.
Qed.

(** the first atom and the others *)
Lemma avals_hd_tl : forall rho As vs, avals rho As = Some vs ->
  aval rho (hd (Aint 0%uint63) As) = Some (hd 0%uint63 vs) /\ avals rho (tl As) = Some (tl vs).
Proof.
  intros rho [|a As] vs V; cbn [avals] in V.
  - injection V as <-. split; reflexivity.
  - destruct (aval rho a) as [va|] eqn:Va; [|discriminate]. destruct (avals rho As) as [ws|] eqn:Ws; [|discriminate].
    injection V as <-. split; assumption.
Qed.

(** two continuations of a record's match that agree on its fields *)
Lemma relim_ext : forall ri (x : RT ri) (Pt : Type) (k1 k2 : list i63 -> Pt),
  k1 (relim (RO ri) x (fun l => l)) = k2 (relim (RO ri) x (fun l => l)) -> relim (RO ri) x k1 = relim (RO ri) x k2.
Proof. intros ri x Pt k1 k2 H. rewrite (rl_nat ri x Pt k1), (rl_nat ri x Pt k2). exact H. Qed.

Lemma kinds_denote_es : forall cbo, forall r mok nx k rk cs rec cenv benv renv denv s es, wfs (map (@projT1 _ _) cs, cbo) r mok nx k rk es = true ->
  rtyped renv rk -> map kind_of (denote_es cs rec cenv benv renv denv s es) = kinds_s rk es.
Proof. intros cbo.
  intros r mok nx k rk cs rec cenv benv renv denv s es W T. revert W.
  induction es as [| e es IH | b es IH | x es IH]; intros W; cbn [wfs] in W; simpl.
  - reflexivity.
  - apply andb_true_iff in W as [_ W]. f_equal. apply IH; exact W.
  - apply andb_true_iff in W as [_ W]. f_equal. apply IH; exact W.
  - apply andb_true_iff in W as [W1 W]. f_equal; [eapply kind_denote_r; eauto | apply IH; exact W].
Qed.
(** a value taken apart: its fields given to [F] *)

Lemma kind_eqb_eq : forall a b, kind_eqb a b = true -> a = b.
Proof. intros [| | a] [| | b]; simpl; try congruence. intro H. apply Nat.eqb_eq in H. subst. reflexivity. Qed.
Lemma kinds_eqb_eq : forall a b, kinds_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; simpl in H; try discriminate; auto.
  apply andb_true_iff in H as [H1 H2]. f_equal; [apply kind_eqb_eq | apply IH]; auto.
Qed.

Lemma len_denote_cs : forall cs rec cenv benv renv denv s ccs, length (denote_cs cs rec cenv benv renv denv s ccs) = len_c ccs.
Proof. intros cs rec cenv benv renv denv s ccs. induction ccs; simpl; auto. Qed.

(** the second arm of a test starts after the first arm's variables *)
Lemma after_le : forall n e, Pos.le n (after n e).
Proof. intros n e. unfold after. lia. Qed.
Lemma after_lt : forall n e, Pos.lt n (after n e).
Proof. intros n e. unfold after. lia. Qed.

Lemma agree_mono : forall rho rho' n n', agree rho rho' n' -> Pos.le n n' -> agree rho rho' n.
Proof. intros rho rho' n n' A L x Lx. apply A. lia. Qed.

(** [n <= after n e] for every [after] in sight, then [lia] *)
Ltac add_after :=
  repeat match goal with
  | H : context [after ?n ?e] |- _ => lazymatch goal with _ : Pos.le n (after n e) |- _ => fail | _ => pose proof (after_le n e) end
  | |- context [after ?n ?e] => lazymatch goal with _ : Pos.le n (after n e) |- _ => fail | _ => pose proof (after_le n e) end
  end.
Ltac lia_a := first [add_after; lia | unfold after in *; lia].
Ltac afterle := first [apply after_le | lia_a].

(** the tests the merging of calls makes *)
Lemma binop_eqb_eq : forall o1 o2, binop_eqb o1 o2 = true -> o1 = o2.
Proof. intros [] []; simpl; intro H; try discriminate; reflexivity. Qed.
Lemma same_e_eq : forall x y, same_e x y = true -> x = y.
Proof.
  induction x; intros y H; destruct y; simpl in H; try discriminate.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - apply eqb_correct in H. subst. reflexivity.
  - apply andb_true_iff in H as [H Hb]. apply andb_true_iff in H as [Ho Ha].
    apply binop_eqb_eq in Ho. subst. rewrite (IHx1 _ Ha), (IHx2 _ Hb). reflexivity.
Qed.
Lemma same_c_eq : forall x y, same_c x y = true -> x = y.
Proof. intros x y H. destruct x; destruct y; simpl in H; try discriminate; try reflexivity. apply Nat.eqb_eq in H. subst. reflexivity. Qed.
Lemma appnT_false : forall k T (x : ntypeT k false T) vs s s', appnT k false T x vs s = appnT k false T x vs s'.
Proof. induction k as [|[| | ri] k IH]; intros T x vs s s'; simpl; auto; destruct vs as [|[] vs]; apply IH. Qed.
Lemma appn_false : forall k r (x : ntype k false r) vs s s', appn k false r x vs s = appn k false r x vs s'.
Proof. intros k r. apply appnT_false. Qed.

Lemma calln_nomem : forall gs h cvs vs s s', sm gs = false -> calln gs h cvs vs s = calln gs h cvs vs s'.
Proof.
  intros [x k m r w q b v p] h cvs vs s s' E; simpl in E; subst m. unfold calln, callf. cbn [sr sq].
  destruct p; cbn iota beta; destruct q as [[| |ri]|].
  - f_equal. apply appnT_false.
  - f_equal. apply appnT_false.
  - f_equal. f_equal. apply appnT_false.
  - destruct r; simpl; try reflexivity. apply appnT_false.
  - f_equal. apply appnT_false.
  - f_equal. apply appnT_false.
  - f_equal. f_equal. apply appnT_false.
  - destruct r; simpl; try reflexivity. apply appnT_false.
Qed.

Lemma callf_nomem : forall g (h : ftype g) cvs vs s s', sm g = false -> callf g h cvs vs s = callf g h cvs vs s'.
Proof. intros [x k m r w q b v p] h cvs vs s s' E; simpl in E; subst m. unfold callf. destruct p; apply appnT_false. Qed.

(** ** The slot block (step 12, part 3): a record's fields after the first are given back in its cells, which the caller
    saved and writes back afterwards, cell 0 first -- the laws [upd_upd], [upd_rd_id], [rd_upd_ne], [rd_upd_eq] of the kit's
    memory ([KQSpec.real_laws]) *)
Lemma size_wslot : forall vs j s h, KQ.KQRun.kq_size h (wslot j vs s) = KQ.KQRun.kq_size h s.
Proof. induction vs as [|v vs IH]; intros j s h; cbn [wslot]; [reflexivity|]. rewrite ksize_upd. apply IH. Qed.

Lemma ofn_sZ : forall i, (Z.of_nat i <= 1048576)%Z -> Sint63.to_Z (ofn i) = Z.of_nat i.
Proof.
  intros i L. assert (W : (Z.of_nat i < wB)%Z) by (rewrite KQMAuto.wB_num; lia).
  assert (P62 : (2 ^ 62 = 4611686018427387904)%Z) by reflexivity.
  pose proof (ofn_phi i W) as E. rewrite sZ_small; rewrite E; [reflexivity | lia].
Qed.

Lemma ofn_inj : forall a b, (Z.of_nat a <= 1048576)%Z -> (Z.of_nat b <= 1048576)%Z -> ofn a = ofn b -> a = b.
Proof. intros a b La Lb E. apply Nat2Z.inj. rewrite <- (ofn_sZ a La), <- (ofn_sZ b Lb), E. reflexivity. Qed.

Lemma rd_wslot_lt : forall vs j i s, (i < j)%nat -> (Z.of_nat (j + length vs) <= 1048576)%Z ->
  KQ.KQRun.rd 63%uint63 (ofn i) (wslot j vs s) = KQ.KQRun.rd 63%uint63 (ofn i) s.
Proof.
  induction vs as [|v vs IH]; intros j i s Lt Le; cbn [wslot length] in *; [reflexivity|].
  rewrite krd_upd_ne.
  - apply IH; lia.
  - intros [_ E]. apply ofn_inj in E; lia.
Qed.

(** the saved cells written back, cell [j] first *)
Fixpoint ubk (j : nat) (os : list i63) (s : mem) : mem :=
  match os with [] => s | o :: os => ubk (S j) os (KQ.KQRun.upd 63%uint63 (ofn j) o s) end.

Lemma wback : forall vs j s, (Z.of_nat (j + length vs) <= 1048576)%Z ->
  ubk j (map (fun i => KQ.KQRun.rd 63%uint63 (ofn i) s) (seq j (length vs))) (wslot j vs s) = s.
Proof.
  induction vs as [|v vs IH]; intros j s Le; cbn [ubk map seq wslot length] in *; [reflexivity|].
  rewrite KQMAuto.upd_upd_r. rewrite <- (rd_wslot_lt vs (S j) j s) by lia. rewrite KQMAuto.upd_rd_id_r. apply IH. lia.
Qed.

(** the cells read back after the writes: the fields *)
Lemma rd_wslot_seq : forall vs j s, (Z.of_nat (j + length vs) <= 1048576)%Z ->
  (vs <> [] -> Z.of_nat (j + length vs) <= Sint63.to_Z (KQ.KQBound.kq_len 63%uint63))%Z ->
  map (fun i => KQ.KQRun.rd 63%uint63 (ofn i) (wslot j vs s)) (seq j (length vs)) = vs.
Proof.
  induction vs as [|v vs IH]; intros j s Le Lk0; cbn [map seq length wslot] in *; [reflexivity|].
  assert (Lk : (Z.of_nat (j + S (length vs)) <= Sint63.to_Z (KQ.KQBound.kq_len 63%uint63))%Z) by (apply Lk0; discriminate).
  f_equal.
  - apply krd_upd_eq.
    + change (Sint63.to_Z 63%uint63) with 63%Z. lia.
    + rewrite ofn_sZ by lia. rewrite size_wslot. pose proof (KQMAuto.size_ge_len 63%uint63 s). lia.
  - transitivity (map (fun i => KQ.KQRun.rd 63%uint63 (ofn i) (wslot (S j) vs s)) (seq (S j) (length vs))); [| apply IH; [lia | intros _; lia]].
    apply map_ext_in. intros i Hi. apply in_seq in Hi.
    rewrite krd_upd_ne; [reflexivity|]. intros [_ E]. apply ofn_inj in E; lia.
Qed.

Lemma denote_nomem :
  (forall e cs rec cenv benv renv env s s' r nx k rk cbo, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wf (map (@projT1 _ _) cs, cbo) r false nx k rk e = true -> denote_e cs rec cenv benv renv env s e = denote_e cs rec cenv benv renv env s' e)
  /\
  (forall es cs rec cenv benv renv env s s' r nx k rk cbo, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wfs (map (@projT1 _ _) cs, cbo) r false nx k rk es = true -> denote_es cs rec cenv benv renv env s es = denote_es cs rec cenv benv renv env s' es)
  /\
  (forall c cs rec cenv benv renv env s s' r nx k rk cbo, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wfc (map (@projT1 _ _) cs, cbo) r false nx k rk c = true -> denote_c cs rec cenv benv renv env s c = denote_c cs rec cenv benv renv env s' c)
  /\
  (forall ccs cs rec cenv benv renv env s s' r nx k rk cbo, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wfcs (map (@projT1 _ _) cs, cbo) r false nx k rk ccs = true -> denote_cs cs rec cenv benv renv env s ccs = denote_cs cs rec cenv benv renv env s' ccs)
  /\
  (forall b cs rec cenv benv renv env s s' r nx k rk cbo, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wfb (map (@projT1 _ _) cs, cbo) r false nx k rk b = true -> denote_b cs rec cenv benv renv env s b = denote_b cs rec cenv benv renv env s' b)
  /\
  (forall x cs rec cenv benv renv env s s' r nx k rk cbo, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wfr (map (@projT1 _ _) cs, cbo) r false nx k rk x = true -> denote_r cs rec cenv benv renv env s x = denote_r cs rec cenv benv renv env s' x).
Proof.
  apply sexp_comb.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros o a IHa b IHb cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wa), (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb). reflexivity.
  - intros c a IHa b IHb t IHt e IHe cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *.
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wa), (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb), (IHt _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wt),
            (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wf). reflexivity.
  - intros e1 IH1 e2 IH2 cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [W1 W2].
    rewrite (IH1 _ _ _ _ _ _ s s' _ _ _ _ _ Hr W1). apply (IH2 _ _ _ _ _ _ s s' _ _ _ _ _ Hr W2).
  - intros h IHh i IHi cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in W. discriminate.
  - intros ccs IHc args IHs cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *.
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (IHc _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wc), (IHs _ _ _ _ _ _ s s' _ _ _ _ _ Hr Ws). apply Hr.
  - intros fi ccs IHc args IHs cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wf] in W. cbn [fst] in W; rewrite nth_sigs in W. cbn [denote_e].
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wsh].
    apply andb_true_iff in W as [W Wsw]. apply andb_true_iff in W as [W Wr]. apply andb_true_iff in W as [W Wm].
    rewrite (IHc _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wc), (IHs _ _ _ _ _ _ s s' _ _ _ _ _ Hr Ws). apply calln_nomem.
    destruct (sm gs); [discriminate | reflexivity].
  - intros c e0 IH0 e1 IH1 cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O); [apply (IH0 _ _ _ _ _ _ s s' _ _ _ _ _ Hr W0) | apply (IH1 _ _ _ _ _ _ s s' _ _ _ _ _ Hr W1)].
  - intros b IHb t IHt e IHe cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wb Wt].
    rewrite (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb), (IHt _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wt), (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr We). reflexivity.
  - intros b IHb e IHe cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [Wb We].
    rewrite (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb). apply (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr We).
  - intros h IHh i IHi cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in W. discriminate.
  - intros c IHc e IHe cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wc _].
    rewrite (IHc _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wc). apply (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr We).
  - intros; reflexivity.
  - intros x IHx e IHe cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_e wf] in *. apply andb_true_iff in W as [Wx We].
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx). apply (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr We).
  - intros x IHx e IHe cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_e wf] in *. apply andb_true_iff in W as [Wx We].
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), !rmatch_eq. apply (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr We).
  - intros o args IHa cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_e wf] in *. apply andb_true_iff in W as [_ Wa].
    rewrite (IHa _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wa). reflexivity.
  - intros h IHh cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in W. discriminate.
  - intros h IHh i IHi cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in W. discriminate.
  - intros sj x IHx e IHe cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_e wf] in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [_ Wx].
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), !rsplit_eq. apply (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr We).
  - intros; reflexivity.
  - intros e IHe es IHes cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [We Wes].
    rewrite (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr We), (IHes _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wes). reflexivity.
  - intros b IHb es IHes cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [Wb Wes].
    rewrite (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb), (IHes _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wes). reflexivity.
  - intros x IHx es IHes cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_es wfs] in *. apply andb_true_iff in W as [Wx Wes].
    assert (Wx' : wfr (map (@projT1 _ _) cs, cbo) r false nx k rk x = true) by exact Wx.
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx'), (IHes _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wes). reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros c IH cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. rewrite (IH _ _ _ _ _ _ s s' _ _ _ _ _ Hr W). reflexivity.
  - intros e IH cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. rewrite (IH _ _ _ _ _ _ s s' _ _ _ _ _ Hr W). reflexivity.
  - intros c IH cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. rewrite (IH _ _ _ _ _ _ s s' _ _ _ _ _ Hr W). reflexivity.
  - intros a IHa b IHb cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wa), (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb). reflexivity.
  - intros; reflexivity.
  - intros c IHc ccs IHs cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [Wc Ws].
    rewrite (IHc _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wc), (IHs _ _ _ _ _ _ s s' _ _ _ _ _ Hr Ws). reflexivity.
  - intros c x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr W). reflexivity.
  - intros c a IHa b IHb x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wa), (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb), (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx),
            (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros c x0 IH0 x1 IH1 cs rec cenv benv renv env s s' r nx k rk cbo Hr W. simpl in *. apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O); [apply (IH0 _ _ _ _ _ _ s s' _ _ _ _ _ Hr W0) | apply (IH1 _ _ _ _ _ _ s s' _ _ _ _ _ Hr W1)].
  - intros fi ccs IHc args IHs cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wfb] in W. cbn [fst] in W; rewrite nth_sigs in W. cbn [denote_b].
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wsh].
    apply andb_true_iff in W as [W Wq]. apply andb_true_iff in W as [W Wsw]. apply andb_true_iff in W as [W Wr]. apply andb_true_iff in W as [W Wm].
    rewrite (IHc _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wc), (IHs _ _ _ _ _ _ s s' _ _ _ _ _ Hr Ws). f_equal. apply callf_nomem.
    destruct (sm gs); [discriminate | reflexivity].
  - intros c x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros b IHb x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [Wb Wx].
    rewrite (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb), (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros e IHe x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wfb denote_b] in *. apply andb_true_iff in W as [We Wx].
    rewrite (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr We). apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros b IHb x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wb Wx].
    rewrite (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb). apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros c IHc x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wfb denote_b] in *. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc _].
    rewrite (IHc _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wc). apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros y IHy x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wy Wx].
    rewrite (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros y IHy x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wy Wx].
    rewrite (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy), !rmatch_eq. apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros sj y IHy x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [_ Wy].
    rewrite (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy), !rsplit_eq. apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros; reflexivity.
  - intros ri es IHes cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *. apply andb_true_iff in W as [_ Wes].
    rewrite (IHes _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wes). reflexivity.
  - intros ri fi ccs IHc args IHs cs rec cenv benv renv env s s' r nx k rk cbo Hr W.
    destruct (wfr_call_inv _ _ _ _ _ _ _ _ _ _ W) as (gs & E & _ & _ & Wm & _ & _ & _ & _ & _ & _ & Wc & Ws).
    cbn [fst] in E; rewrite nth_sigs in E. cbn [denote_r]. unfold callee in *. destruct (nth_error cs fi) as [[gs' h]|]; [|reflexivity].
    simpl in E. injection E as <-.
    rewrite (IHc _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wc), (IHs _ _ _ _ _ _ s s' _ _ _ _ _ Hr Ws). f_equal. apply callf_nomem.
    destruct (sm gs'); [discriminate Wm | reflexivity].
  - intros ri o a IHa b IHb cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [_ Wa].
    rewrite (IHa _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wa), (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb). reflexivity.
  - intros e IHe x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *. apply andb_true_iff in W as [We Wx].
    rewrite (IHe _ _ _ _ _ _ s s' _ _ _ _ _ Hr We). apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros y IHy x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *. apply andb_true_iff in W as [Wy Wx].
    rewrite (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros ri c a IHa b IHb x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Wb].
    apply andb_true_iff in W as [_ Wa].
    rewrite (IHa _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wa), (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb), (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx),
            (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros ri x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), !rmatch_eq, (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros ri b IHb x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [_ Wb].
    rewrite (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb), (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros b IHb x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *. apply andb_true_iff in W as [Wb Wx].
    rewrite (IHb _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wb). apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros c IHc x IHx cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc _].
    rewrite (IHc _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wc). apply (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx).
  - intros ri c x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    destruct (nth c cenv O); [rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx) | rewrite (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy)]; reflexivity.
  - intros ri sj x IHx y IHy cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    rewrite (IHx _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wx), !rsplit_eq, (IHy _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wy). reflexivity.
  - intros ri ns IHns rs IHrs cs rec cenv benv renv env s s' r nx k rk cbo Hr W. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wrs]. apply andb_true_iff in W as [_ Wns].
    rewrite (IHns _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wns), (IHrs _ _ _ _ _ _ s s' _ _ _ _ _ Hr Wrs). reflexivity.
Qed.

(** a record given back reads no memory where its function has none *)
Lemma denote_br_nomem : forall b cs rec ri recr cenv benv renv env s s' r rb nx k rk cbo,
  (forall cvs l, rec cvs l s = rec cvs l s') -> (forall cvs l, recr cvs l s = recr cvs l s') ->
  wfbr (map (@projT1 _ _) cs, cbo) r rb false nx k rk ri b = true ->
  denote_br cs rec ri recr cenv benv renv env s b = denote_br cs rec ri recr cenv benv renv env s' b.
Proof.
  destruct denote_nomem as (DE & DES & DC & DCS & DB & DR).
  induction b as [x | ccs args | ccs args b IH | ccs args b IH | e b IH | c b IH | c b IH | x b IH | x b IH
                 | c x y t IHt u IHu | c t IHt u IHu | c b0 IH0 b1 IH1 | sj x b IH];
    intros cs rec ri recr cenv benv renv env s s' r rb nx k rk cbo Hr Hrr W; cbn [wfbr] in W; cbn [denote_br].
  - apply andb_true_iff in W as [_ Wx].
    rewrite (DR x cs rec cenv benv renv env s s' r nx k rk cbo Hr Wx). reflexivity.
  - apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (DCS ccs cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc), (DES args cs rec cenv benv renv env s s' r nx k rk cbo Hr Ws). apply Hrr.
  - apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (DCS ccs cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc), (DES args cs rec cenv benv renv env s s' r nx k rk cbo Hr Ws), Hrr.
    apply relim_ext. apply (IH cs rec ri recr cenv benv renv _ s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (DCS ccs cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc), (DES args cs rec cenv benv renv env s s' r nx k rk cbo Hr Ws), Hrr.
    apply (IH cs rec ri recr cenv benv _ env s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [We Wb].
    rewrite (DE e cs rec cenv benv renv env s s' r nx k rk cbo Hr We). apply (IH cs rec ri recr cenv benv renv _ s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [Wc Wb].
    rewrite (DB c cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc). apply (IH cs rec ri recr cenv _ renv env s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [Wc _].
    rewrite (DC c cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc). apply (IH cs rec ri recr _ benv renv env s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [Wx Wb].
    rewrite (DR x cs rec cenv benv renv env s s' r nx k rk cbo Hr Wx). apply (IH cs rec ri recr cenv benv _ env s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [Wx Wb].
    rewrite (DR x cs rec cenv benv renv env s s' r nx k rk cbo Hr Wx), !rmatch_eq. apply (IH cs rec ri recr cenv benv renv _ s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wx Wy].
    rewrite (DE x cs rec cenv benv renv env s s' r nx k rk cbo Hr Wx), (DE y cs rec cenv benv renv env s s' r nx k rk cbo Hr Wy),
            (IHt cs rec ri recr cenv benv renv env s s' r rb nx k _ _ Hr Hrr Wt), (IHu cs rec ri recr cenv benv renv env s s' r rb nx k _ _ Hr Hrr Wf).
    reflexivity.
  - apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wc Wt].
    rewrite (DB c cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc),
            (IHt cs rec ri recr cenv benv renv env s s' r rb nx k _ _ Hr Hrr Wt), (IHu cs rec ri recr cenv benv renv env s s' r rb nx k _ _ Hr Hrr Wf).
    reflexivity.
  - apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O); [apply (IH0 cs rec ri recr cenv benv renv env s s' r rb nx k _ _ Hr Hrr W0)
                             | apply (IH1 cs rec ri recr _ benv renv env s s' r rb nx k _ _ Hr Hrr W1)].
  - apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [_ Wx].
    rewrite (DR x cs rec cenv benv renv env s s' r nx k rk cbo Hr Wx), !rsplit_eq. apply (IH cs rec ri recr cenv benv _ _ s s' r rb nx k _ _ Hr Hrr Wb).
Qed.

Lemma denote_bb_nomem : forall b cs rec recb cenv benv renv env s s' r rb nx k rk cbo,
  (forall cvs l, rec cvs l s = rec cvs l s') -> (forall cvs l, recb cvs l s = recb cvs l s') ->
  wfbb (map (@projT1 _ _) cs, cbo) r rb false nx k rk b = true ->
  denote_bb cs rec recb cenv benv renv env s b = denote_bb cs rec recb cenv benv renv env s' b.
Proof.
  destruct denote_nomem as (DE & DES & DC & DCS & DB & DR).
  induction b as [x | ccs args | ccs args | e b IH | c b IH | c b IH | x b IH | x b IH
                 | c x y t IHt u IHu | c t IHt u IHu | c b0 IH0 b1 IH1 | sj x b IH];
    intros cs rec recb cenv benv renv env s s' r rb nx k rk cbo Hr Hrr W; cbn [wfbb] in W; cbn [denote_bb].
  - exact (DB x cs rec cenv benv renv env s s' r nx k rk cbo Hr W).
  - apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (DCS ccs cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc), (DES args cs rec cenv benv renv env s s' r nx k rk cbo Hr Ws). apply Hrr.
  - apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (DCS ccs cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc), (DES args cs rec cenv benv renv env s s' r nx k rk cbo Hr Ws), Hrr.
    reflexivity.
  - apply andb_true_iff in W as [We Wb].
    rewrite (DE e cs rec cenv benv renv env s s' r nx k rk cbo Hr We). apply (IH cs rec recb cenv benv renv _ s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [Wc Wb].
    rewrite (DB c cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc). apply (IH cs rec recb cenv _ renv env s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [Wc _].
    rewrite (DC c cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc). apply (IH cs rec recb _ benv renv env s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [Wx Wb].
    rewrite (DR x cs rec cenv benv renv env s s' r nx k rk cbo Hr Wx). apply (IH cs rec recb cenv benv _ env s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [Wx Wb].
    rewrite (DR x cs rec cenv benv renv env s s' r nx k rk cbo Hr Wx), !rmatch_eq. apply (IH cs rec recb cenv benv renv _ s s' r rb nx k _ _ Hr Hrr Wb).
  - apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wx Wy].
    rewrite (DE x cs rec cenv benv renv env s s' r nx k rk cbo Hr Wx), (DE y cs rec cenv benv renv env s s' r nx k rk cbo Hr Wy),
            (IHt cs rec recb cenv benv renv env s s' r rb nx k _ _ Hr Hrr Wt), (IHu cs rec recb cenv benv renv env s s' r rb nx k _ _ Hr Hrr Wf).
    reflexivity.
  - apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wc Wt].
    rewrite (DB c cs rec cenv benv renv env s s' r nx k rk cbo Hr Wc),
            (IHt cs rec recb cenv benv renv env s s' r rb nx k _ _ Hr Hrr Wt), (IHu cs rec recb cenv benv renv env s s' r rb nx k _ _ Hr Hrr Wf).
    reflexivity.
  - apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O); [apply (IH0 cs rec recb cenv benv renv env s s' r rb nx k _ _ Hr Hrr W0)
                             | apply (IH1 cs rec recb _ benv renv env s s' r rb nx k _ _ Hr Hrr W1)].
  - apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [_ Wx].
    rewrite (DR x cs rec cenv benv renv env s s' r nx k rk cbo Hr Wx), !rsplit_eq. apply (IH cs rec recb cenv benv _ _ s s' r rb nx k _ _ Hr Hrr Wb).
Qed.

(** the meaning depends on the recursive call only through its values on the arguments it is given -- counters and numbers
    as many as the recursion takes ([wf]) *)
Lemma denote_rec_ext :
  (forall e cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wf (map (@projT1 _ _) cs, cbo) r mok nx k rk e = true -> rtyped renv rk -> denote_e cs rec1 cenv benv renv env s e = denote_e cs rec2 cenv benv renv env s e)
  /\
  (forall es cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfs (map (@projT1 _ _) cs, cbo) r mok nx k rk es = true -> rtyped renv rk -> denote_es cs rec1 cenv benv renv env s es = denote_es cs rec2 cenv benv renv env s es)
  /\
  (forall c cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfc (map (@projT1 _ _) cs, cbo) r mok nx k rk c = true -> rtyped renv rk -> denote_c cs rec1 cenv benv renv env s c = denote_c cs rec2 cenv benv renv env s c)
  /\
  (forall ccs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfcs (map (@projT1 _ _) cs, cbo) r mok nx k rk ccs = true -> rtyped renv rk -> denote_cs cs rec1 cenv benv renv env s ccs = denote_cs cs rec2 cenv benv renv env s ccs)
  /\
  (forall b cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfb (map (@projT1 _ _) cs, cbo) r mok nx k rk b = true -> rtyped renv rk -> denote_b cs rec1 cenv benv renv env s b = denote_b cs rec2 cenv benv renv env s b)
  /\
  (forall x cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfr (map (@projT1 _ _) cs, cbo) r mok nx k rk x = true -> rtyped renv rk -> denote_r cs rec1 cenv benv renv env s x = denote_r cs rec2 cenv benv renv env s x).
Proof.
  apply sexp_comb.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros o a IHa b IHb cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). reflexivity.
  - intros c a IHa b IHb t IHt e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHt _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wt T),
            (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wf T). reflexivity.
  - intros e1 IH1 e2 IH2 cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [W1 W2].
    rewrite (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W1 T). apply (IH2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W2 T).
  - intros h IHh i IHi cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    rewrite (IHh _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wh T), (IHi _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wi T). reflexivity.
  - intros ccs IHc args IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfl].
    apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [_ Wn]. apply Nat.eqb_eq in Wn. apply kinds_eqb_eq in Wk.
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T).
    apply Hr; [rewrite len_denote_cs; exact Wn | erewrite kinds_denote_es by eassumption; exact Wk].
  - intros fi ccs IHc args IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf] in W. cbn [fst] in W; rewrite nth_sigs in W. cbn [denote_e].
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T). reflexivity.
  - intros c e0 IH0 e1 IH1 cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O); [apply (IH0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W0 T) | apply (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W1 T)].
  - intros b IHb t IHt e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wb Wt].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHt _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wt T), (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T). reflexivity.
  - intros b IHb e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [Wb We].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T).
  - intros h IHh i IHi cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    rewrite (IHh _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wh T), (IHi _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wi T). reflexivity.
  - intros c IHc e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wc _].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T). apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T).
  - intros; reflexivity.
  - intros x IHx e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [Wx We].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T). apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - intros x IHx e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [Wx We].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), !rmatch_eq. apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T).
  - intros o args IHa cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [_ Wa].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T). reflexivity.
  - intros h IHh cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [_ Wh].
    rewrite (IHh _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wh T). reflexivity.
  - intros h IHh i IHi cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    rewrite (IHh _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wh T), (IHi _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wi T). reflexivity.
  - intros sj x IHx e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), !rsplit_eq. apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We).
    apply rsplit_typed; [rewrite <- Ex; eapply kind_denote_r; [exact Wx | exact T] | exact T].
  - intros; reflexivity.
  - intros e IHe es IHes cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfs denote_es] in *. apply andb_true_iff in W as [We Wes].
    rewrite (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T), (IHes _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wes T). reflexivity.
  - intros b IHb es IHes cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfs denote_es] in *. apply andb_true_iff in W as [Wb Wes].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHes _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wes T). reflexivity.
  - intros x IHx es IHes cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfs denote_es] in *. apply andb_true_iff in W as [Wx Wes].
    assert (Wx' : wfr (map (@projT1 _ _) cs, cbo) r mok nx k rk x = true) by exact Wx.
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx' T), (IHes _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wes T). reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros c IH cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfc denote_c] in *. rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W T). reflexivity.
  - intros e IH cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfc denote_c] in *. rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W T). reflexivity.
  - intros c IH cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfc denote_c] in *. rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W T). reflexivity.
  - intros a IHa b IHb cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfc denote_c] in *. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). reflexivity.
  - intros; reflexivity.
  - intros c IHc ccs IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfcs denote_cs] in *. apply andb_true_iff in W as [Wc Ws].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T). reflexivity.
  - intros c x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W T). reflexivity.
  - intros c a IHa b IHb x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T),
            (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros c x0 IH0 x1 IH1 cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O); [apply (IH0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W0 T) | apply (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W1 T)].
  - intros fi ccs IHc args IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb] in W. cbn [fst] in W; rewrite nth_sigs in W. cbn [denote_b].
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T). reflexivity.
  - intros c x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros b IHb x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [Wb Wx].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros e IHe x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [We Wx].
    rewrite (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros b IHb x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wb Wx].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros c IHc x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc _].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros y IHy x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wy Wx].
    rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - intros y IHy x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wy Wx].
    rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T), !rmatch_eq. apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros sj y IHy x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Ey Wy]. apply Nat.eqb_eq in Ey.
    rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T), !rsplit_eq. apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx).
    apply rsplit_typed; [rewrite <- Ey; eapply kind_denote_r; [exact Wy | exact T] | exact T].
  - intros; reflexivity.
  - intros ri es IHes cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [_ Wes].
    rewrite (IHes _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wes T). reflexivity.
  - intros ri fi ccs IHc args IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T.
    destruct (wfr_call_inv _ _ _ _ _ _ _ _ _ _ W) as (gs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wc & Ws).
    cbn [denote_r]. rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T). reflexivity.
  - intros ri o a IHa b IHb cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [_ Wa].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). reflexivity.
  - intros e IHe x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [We Wx].
    rewrite (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros y IHy x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [Wy Wx].
    rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - intros ri c a IHa b IHb x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Wb].
    apply andb_true_iff in W as [_ Wa].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T),
            (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros ri x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), !rmatch_eq, (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros ri b IHb x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [_ Wb].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros b IHb x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [Wb Wx].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros c IHc x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc _].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros ri c x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    destruct (nth c cenv O); [rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T) | rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T)]; reflexivity.
  - intros ri sj x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Ex _]. apply Nat.eqb_eq in Ex.
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), !rsplit_eq, (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy); [reflexivity |].
    apply rsplit_typed; [rewrite <- Ex; eapply kind_denote_r; [exact Wx | exact T] | exact T].
  - intros ri ns IHns rs IHrs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wrs]. apply andb_true_iff in W as [_ Wns].
    rewrite (IHns _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wns T), (IHrs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wrs T). reflexivity.
Qed.

Ltac split_w W := repeat match type of W with (_ && _) = true => let W1 := fresh "W" in apply andb_true_iff in W as [W W1] end.
Ltac split_all := repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
(** the same for a memory and its recursive call; and for a number and a memory, the memory's recursive call inside it (step 44:
    the two sorts one mutual type) *)
Lemma denote_mpv_recm_ext :
  (forall m cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo,
     (forall cvs l s', length cvs = nx -> map kind_of l = k -> recm1 cvs l s' = recm2 cvs l s') ->
     wfm (map (@projT1 _ _) cs, cbo) r rm mok nx k rk m = true -> rtyped renv rk ->
     denote_m cs rec recm1 cenv benv renv env s m = denote_m cs rec recm2 cenv benv renv env s m)
  /\
  (forall p cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo,
     (forall cvs l s', length cvs = nx -> map kind_of l = k -> recm1 cvs l s' = recm2 cvs l s') ->
     wfpv (map (@projT1 _ _) cs, cbo) r rm mok rp nx k rk p = true -> rtyped renv rk ->
     denote_pv cs rec recm1 recp cenv benv renv env s p = denote_pv cs rec recm2 recp cenv benv renv env s p).
Proof.
  apply smem_comb.
  - intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    reflexivity.
  - intros h i x m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [_ Wm]. rewrite (IH cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr Wm T). reflexivity.
  - intros e m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [_ Wm]. apply (IH cs rec recm1 recm2 cenv benv renv _ s r rm mok nx k rk _ Hr Wm T).
  - intros m1 IH1 m2 IH2; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [W1 W2]. rewrite (IH1 cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W1 T).
    apply (IH2 cs rec recm1 recm2 cenv benv renv env _ r rm mok nx k rk _ Hr W2 T).
  - intros c a b m1 IH1 m2 IH2; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [_ W1].
    rewrite (IH1 cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W1 T), (IH2 cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W2 T).
    reflexivity.
  - intros ccs args m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [_ Wn].
    apply Nat.eqb_eq in Wn. apply kinds_eqb_eq in Wk. rewrite (IH cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr Wm T).
    apply Hr; [rewrite len_denote_cs; exact Wn | erewrite kinds_denote_es by eassumption; exact Wk].
  - intros fi ccs args m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    cbn [fst] in W; rewrite nth_sigs in W. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|]; simpl in W; [|reflexivity].
    apply andb_true_iff in W as [_ Wm]. rewrite (IH cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr Wm T). reflexivity.
  - intros c m0 IH0 m1 IH1; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [W0 W1]. destruct (nth c cenv O);
      [apply (IH0 cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W0 T) | apply (IH1 cs rec recm1 recm2 _ benv renv env s r rm mok nx k rk _ Hr W1 T)].
  - intros b m1 IH1 m2 IH2; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [_ W1].
    rewrite (IH1 cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W1 T), (IH2 cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W2 T).
    reflexivity.
  - intros b m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [_ Wm]. apply (IH cs rec recm1 recm2 cenv _ renv env s r rm mok nx k rk _ Hr Wm T).
  - intros h i x m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [_ Wm]. rewrite (IH cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr Wm T). reflexivity.
  - intros c m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [_ Wm]. apply (IH cs rec recm1 recm2 _ benv renv env s r rm mok nx k rk _ Hr Wm T).
  - intros o args m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [_ Wm]. rewrite (IH cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr Wm T). reflexivity.
  - intros h i x m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [_ Wm]. rewrite (IH cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr Wm T). reflexivity.
  - intros x m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [Wx Wm]. apply (IH cs rec recm1 recm2 cenv benv _ env s r rm mok nx k _ _ Hr Wm).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - intros x m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [Wx Wm]. rewrite !rmatch_eq. apply (IH cs rec recm1 recm2 cenv benv renv _ s r rm mok nx k rk _ Hr Wm T).
  - intros sj x m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex. rewrite !rsplit_eq.
    apply (IH cs rec recm1 recm2 cenv benv _ _ s r rm mok nx k _ _ Hr Wm).
    apply rsplit_typed; [rewrite <- Ex; eapply kind_denote_r; [exact Wx | exact T] | exact T].
  - intros p IHp m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [Wp Wm]. rewrite (IHp cs rec recm1 recm2 dpair cenv benv renv env s r rm mok false nx k rk _ Hr Wp T).
    destruct (denote_pv cs rec recm2 dpair cenv benv renv env s p) as [v2 s2].
    apply (IH cs rec recm1 recm2 cenv benv renv _ s2 r rm mok nx k rk _ Hr Wm T).
  - intros p IHp m IH; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    apply andb_true_iff in W as [Wp Wm]. rewrite (IHp cs rec recm1 recm2 dpair cenv benv renv env s r rm mok false nx k rk _ Hr Wp T).
    apply (IH cs rec recm1 recm2 cenv benv renv _ _ r rm mok nx k rk _ Hr Wm T).
  - intros fi ccs args p IHp; intros cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo Hr W T; cbn [denote_m wfm] in *.
    cbn [fst] in W; rewrite nth_sigs in W. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|]; simpl in W; [|reflexivity].
    split_w W. rewrite (IHp cs rec recm1 recm2 dpair cenv benv renv env s r rm mok false nx k rk _ Hr W0 T). reflexivity.
  - intros e m IHm; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. rewrite (IHm cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W0 T). reflexivity.
  - intros fi ccs args m IHm; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    cbn [fst] in W; rewrite nth_sigs in W. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|]; simpl in W; [|reflexivity].
    split_w W. rewrite (IHm cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W0 T). reflexivity.
  - intros ccs args m IHm; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. rewrite (IHm cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W0 T). reflexivity.
  - intros e p IH; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. apply (IH cs rec recm1 recm2 recp cenv benv renv _ s r rm mok rp nx k rk _ Hr W0 T).
  - intros c p IH; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. apply (IH cs rec recm1 recm2 recp cenv _ renv env s r rm mok rp nx k rk _ Hr W0 T).
  - intros c p IH; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. apply (IH cs rec recm1 recm2 recp _ benv renv env s r rm mok rp nx k rk _ Hr W0 T).
  - intros x p IH; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. apply (IH cs rec recm1 recm2 recp cenv benv _ env s r rm mok rp nx k _ _ Hr W0).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - intros x p IH; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. rewrite !rmatch_eq. apply (IH cs rec recm1 recm2 recp cenv benv renv _ s r rm mok rp nx k rk _ Hr W0 T).
  - intros m IHm p IH; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. rewrite (IHm cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk _ Hr W T).
    apply (IH cs rec recm1 recm2 recp cenv benv renv env _ r rm mok rp nx k rk _ Hr W0 T).
  - intros c x y t IHt f IHf; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. rewrite (IHt cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk _ Hr W1 T),
                       (IHf cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk _ Hr W0 T). reflexivity.
  - intros c t IHt f IHf; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. rewrite (IHt cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk _ Hr W1 T),
                       (IHf cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk _ Hr W0 T). reflexivity.
  - intros c p0 IH0 p1 IH1; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. destruct (nth c cenv O);
      [apply (IH0 cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk _ Hr W T) | apply (IH1 cs rec recm1 recm2 recp _ benv renv env s r rm mok rp nx k rk _ Hr W0 T)].
  - intros p IHp q IHq; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. rewrite (IHp cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk _ Hr W T).
    destruct (denote_pv cs rec recm2 recp cenv benv renv env s p) as [x2 s2].
    apply (IHq cs rec recm1 recm2 recp cenv benv renv _ s2 r rm mok rp nx k rk _ Hr W0 T).
  - intros sj x p IH; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    split_w W. apply Nat.eqb_eq in W. rewrite !rsplit_eq. apply (IH cs rec recm1 recm2 recp cenv benv _ _ s r rm mok rp nx k _ _ Hr W0).
    apply rsplit_typed; [rewrite <- W; eapply kind_denote_r; [exact W1 | exact T] | exact T].
  - intros fi ccs args p IHp; intros cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
    cbn [fst] in W; rewrite nth_sigs in W. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|]; simpl in W; [|reflexivity].
    split_w W. rewrite (IHp cs rec recm1 recm2 recp cenv benv renv env s r rm mok rp nx k rk _ Hr W0 T). reflexivity.
Qed.
Lemma denote_m_recm_ext : forall m cs rec recm1 recm2 cenv benv renv env s r rm mok nx k rk cbo,
  (forall cvs l s', length cvs = nx -> map kind_of l = k -> recm1 cvs l s' = recm2 cvs l s') ->
  wfm (map (@projT1 _ _) cs, cbo) r rm mok nx k rk m = true -> rtyped renv rk ->
  denote_m cs rec recm1 cenv benv renv env s m = denote_m cs rec recm2 cenv benv renv env s m.
Proof. exact (proj1 denote_mpv_recm_ext). Qed.

(** the same for a number made after memories and its recursive call *)
(** a call's result as the code gives it (step 47): a number as it is, a boolean as 1 or 0; the memory after a call that does
    not write it, the one it was given *)
Lemma xres_calln : forall g h cvs vs s kn kb, resq false g = true -> xres g (callf g h cvs vs s) kn kb = kn (calln g h cvs vs s).
Proof.
  intros [x k m r w q b v p] h cvs vs s kn kb E. unfold resq in E; cbn [sr sq] in E.
  destruct r; [discriminate E|]. destruct q as [[| |?]|]; try discriminate E. reflexivity.
Qed.
Lemma xres_calln_b : forall g h cvs vs s kn kb, resq true g = true ->
  exists b, calln g h cvs vs s = b2i b /\ xres g (callf g h cvs vs s) kn kb = kb b.
Proof.
  intros [x k m r w q b v p] h cvs vs s kn kb E. unfold resq in E; cbn [sr sq] in E.
  destruct r; [discriminate E|]. destruct q as [[| |?]|]; try discriminate E. eexists; split; reflexivity.
Qed.
Lemma xres_callnp : forall g h cvs vs pr kn kb, resq false g = true -> xres g (callfp g h cvs vs pr) kn kb = kn (callnp g h cvs vs pr).
Proof.
  intros [x k m r w q b v p] h cvs vs pr kn kb E. unfold resq in E; cbn [sr sq] in E.
  destruct r; [discriminate E|]. destruct q as [[| |?]|]; try discriminate E. reflexivity.
Qed.
Lemma xres_callnp_b : forall g h cvs vs pr kn kb, resq true g = true ->
  exists b, callnp g h cvs vs pr = b2i b /\ xres g (callfp g h cvs vs pr) kn kb = kb b.
Proof.
  intros [x k m r w q b v p] h cvs vs pr kn kb E. unfold resq in E; cbn [sr sq] in E.
  destruct r; [discriminate E|]. destruct q as [[| |?]|]; try discriminate E. eexists; split; reflexivity.
Qed.
Lemma resq_mem : forall bq g h cvs vs s, resq bq g = true ->
  (if sr g then callm g h cvs vs s else match sq g with Some _ => callm g h cvs vs s | None => s end) = s.
Proof.
  intros bq [x k m r w q b v p] h cvs vs s E. unfold resq in E; cbn [sr sq] in *.
  destruct r; [discriminate E|]. destruct q as [[| |?]|]; try discriminate E; reflexivity.
Qed.
Lemma resq_memp : forall bq g h cvs vs pr, resq bq g = true ->
  (if sr g then callmp g h cvs vs pr else match sq g with Some _ => callmp g h cvs vs pr | None => snd pr end) = snd pr.
Proof.
  intros bq [x k m r w q b v p] h cvs vs pr E. unfold resq in E; cbn [sr sq] in *.
  destruct r; [discriminate E|]. destruct q as [[| |?]|]; try discriminate E; reflexivity.
Qed.

(** (step 47) the meaning of a number does not depend on the recursive call's where the check does not allow it *)
Lemma denote_rec_ext_r :
  (forall e cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (r = true -> forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wf (map (@projT1 _ _) cs, cbo) r mok nx k rk e = true -> rtyped renv rk -> denote_e cs rec1 cenv benv renv env s e = denote_e cs rec2 cenv benv renv env s e)
  /\
  (forall es cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (r = true -> forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfs (map (@projT1 _ _) cs, cbo) r mok nx k rk es = true -> rtyped renv rk -> denote_es cs rec1 cenv benv renv env s es = denote_es cs rec2 cenv benv renv env s es)
  /\
  (forall c cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (r = true -> forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfc (map (@projT1 _ _) cs, cbo) r mok nx k rk c = true -> rtyped renv rk -> denote_c cs rec1 cenv benv renv env s c = denote_c cs rec2 cenv benv renv env s c)
  /\
  (forall ccs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (r = true -> forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfcs (map (@projT1 _ _) cs, cbo) r mok nx k rk ccs = true -> rtyped renv rk -> denote_cs cs rec1 cenv benv renv env s ccs = denote_cs cs rec2 cenv benv renv env s ccs)
  /\
  (forall b cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (r = true -> forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfb (map (@projT1 _ _) cs, cbo) r mok nx k rk b = true -> rtyped renv rk -> denote_b cs rec1 cenv benv renv env s b = denote_b cs rec2 cenv benv renv env s b)
  /\
  (forall x cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo,
     (r = true -> forall cvs l s', length cvs = nx -> map kind_of l = k -> rec1 cvs l s' = rec2 cvs l s') ->
     wfr (map (@projT1 _ _) cs, cbo) r mok nx k rk x = true -> rtyped renv rk -> denote_r cs rec1 cenv benv renv env s x = denote_r cs rec2 cenv benv renv env s x).
Proof.
  apply sexp_comb.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros o a IHa b IHb cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). reflexivity.
  - intros c a IHa b IHb t IHt e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHt _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wt T),
            (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wf T). reflexivity.
  - intros e1 IH1 e2 IH2 cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [W1 W2].
    rewrite (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W1 T). apply (IH2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W2 T).
  - intros h IHh i IHi cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    rewrite (IHh _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wh T), (IHi _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wi T). reflexivity.
  - intros ccs IHc args IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfl].
    apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn]. apply Nat.eqb_eq in Wn. apply kinds_eqb_eq in Wk.
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T).
    apply Hr; [exact Wr | rewrite len_denote_cs; exact Wn | erewrite kinds_denote_es by eassumption; exact Wk].
  - intros fi ccs IHc args IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf] in W. cbn [fst] in W; rewrite nth_sigs in W. cbn [denote_e].
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T). reflexivity.
  - intros c e0 IH0 e1 IH1 cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O); [apply (IH0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W0 T) | apply (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W1 T)].
  - intros b IHb t IHt e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wb Wt].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHt _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wt T), (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T). reflexivity.
  - intros b IHb e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [Wb We].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T).
  - intros h IHh i IHi cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    rewrite (IHh _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wh T), (IHi _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wi T). reflexivity.
  - intros c IHc e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wc _].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T). apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T).
  - intros; reflexivity.
  - intros x IHx e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [Wx We].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T). apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - intros x IHx e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [Wx We].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), !rmatch_eq. apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T).
  - intros o args IHa cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [_ Wa].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T). reflexivity.
  - intros h IHh cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *. apply andb_true_iff in W as [_ Wh].
    rewrite (IHh _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wh T). reflexivity.
  - intros h IHh i IHi cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    rewrite (IHh _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wh T), (IHi _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wi T). reflexivity.
  - intros sj x IHx e IHe cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wf denote_e] in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), !rsplit_eq. apply (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We).
    apply rsplit_typed; [rewrite <- Ex; eapply kind_denote_r; [exact Wx | exact T] | exact T].
  - intros; reflexivity.
  - intros e IHe es IHes cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfs denote_es] in *. apply andb_true_iff in W as [We Wes].
    rewrite (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T), (IHes _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wes T). reflexivity.
  - intros b IHb es IHes cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfs denote_es] in *. apply andb_true_iff in W as [Wb Wes].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHes _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wes T). reflexivity.
  - intros x IHx es IHes cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfs denote_es] in *. apply andb_true_iff in W as [Wx Wes].
    assert (Wx' : wfr (map (@projT1 _ _) cs, cbo) r mok nx k rk x = true) by exact Wx.
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx' T), (IHes _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wes T). reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros c IH cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfc denote_c] in *. rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W T). reflexivity.
  - intros e IH cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfc denote_c] in *. rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W T). reflexivity.
  - intros c IH cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfc denote_c] in *. rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W T). reflexivity.
  - intros a IHa b IHb cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfc denote_c] in *. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). reflexivity.
  - intros; reflexivity.
  - intros c IHc ccs IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfcs denote_cs] in *. apply andb_true_iff in W as [Wc Ws].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T). reflexivity.
  - intros c x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W T). reflexivity.
  - intros c a IHa b IHb x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T),
            (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros c x0 IH0 x1 IH1 cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O); [apply (IH0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W0 T) | apply (IH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr W1 T)].
  - intros fi ccs IHc args IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb] in W. cbn [fst] in W; rewrite nth_sigs in W. cbn [denote_b].
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T). reflexivity.
  - intros c x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros b IHb x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [Wb Wx].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros e IHe x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [We Wx].
    rewrite (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros b IHb x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wb Wx].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros c IHc x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc _].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros y IHy x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wy Wx].
    rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - intros y IHy x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *. apply andb_true_iff in W as [Wy Wx].
    rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T), !rmatch_eq. apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros sj y IHy x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [wfb denote_b] in *.
    apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Ey Wy]. apply Nat.eqb_eq in Ey.
    rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T), !rsplit_eq. apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx).
    apply rsplit_typed; [rewrite <- Ey; eapply kind_denote_r; [exact Wy | exact T] | exact T].
  - intros; reflexivity.
  - intros ri es IHes cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [_ Wes].
    rewrite (IHes _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wes T). reflexivity.
  - intros ri fi ccs IHc args IHs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T.
    destruct (wfr_call_inv _ _ _ _ _ _ _ _ _ _ W) as (gs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wc & Ws).
    cbn [denote_r]. rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T), (IHs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Ws T). reflexivity.
  - intros ri o a IHa b IHb cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [_ Wa].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). reflexivity.
  - intros e IHe x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [We Wx].
    rewrite (IHe _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr We T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros y IHy x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [Wy Wx].
    rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - intros ri c a IHa b IHb x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Wb].
    apply andb_true_iff in W as [_ Wa].
    rewrite (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wa T), (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T),
            (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros ri x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), !rmatch_eq, (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros ri b IHb x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [_ Wb].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T), (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T). reflexivity.
  - intros b IHb x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [Wb Wx].
    rewrite (IHb _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wb T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros c IHc x IHx cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc _].
    rewrite (IHc _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wc T). apply (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T).
  - intros ri c x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [_ Wx].
    destruct (nth c cenv O); [rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T) | rewrite (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy T)]; reflexivity.
  - intros ri sj x IHx y IHy cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Ex _]. apply Nat.eqb_eq in Ex.
    rewrite (IHx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wx T), !rsplit_eq, (IHy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wy); [reflexivity |].
    apply rsplit_typed; [rewrite <- Ex; eapply kind_denote_r; [exact Wx | exact T] | exact T].
  - intros ri ns IHns rs IHrs cs rec1 rec2 cenv benv renv env s r mok nx k rk cbo Hr W T. cbn [denote_r wfr] in *.
    apply andb_true_iff in W as [W Wrs]. apply andb_true_iff in W as [_ Wns].
    rewrite (IHns _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wns T), (IHrs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Wrs T). reflexivity.
Qed.

(** a call's result given to what follows it (step 47): the same when what follows is *)
Lemma xres_ext : forall g a kn1 kn2 kb1 kb2, (forall v, kn1 v = kn2 v) -> (forall b, kb1 b = kb2 b) -> xres g a kn1 kb1 = xres g a kn2 kb2.
Proof.
  intros [x k m r w q b v p]; destruct q as [[| |ri]|]; intros a kn1 kn2 kb1 kb2 Hn Hb; cbn;
    [reflexivity | apply Hb | reflexivity | destruct r; [reflexivity | apply Hn]].
Qed.

Lemma denote_x_recx_ext : forall x cs rec recm recx1 recx2 cenv benv renv env s rx nx k rk cbo,
  (forall cvs l s', length cvs = nx -> map kind_of l = k -> recx1 cvs l s' = recx2 cvs l s') ->
  wfx (map (@projT1 _ _) cs, cbo) rx nx k rk x = true -> rtyped renv rk ->
  denote_x cs rec recm recx1 cenv benv renv env s x = denote_x cs rec recm recx2 cenv benv renv env s x.
Proof.
  induction x as [e | m x IH | e x IH | b x IH | c a b x1 IH1 x2 IH2 | b x1 IH1 x2 IH2 | c x0 IH0 x1 IH1 | c x IH
                 | ccs args m | fi ccs args m | rr x IH | rr x IH | pp x IH | pp x IH | sj rr x IH | fi ccs args pp
                 | bq fi ccs args m x IH | ccs args m x IH | bq fi ccs args pp x IH]; intros cs rec recm recx1 recx2 cenv benv renv env s rx nx k rk cbo Hr W T;
    cbn [denote_x wfx] in *.
  - reflexivity.
  - apply andb_true_iff in W as [_ Wx]. apply (IH cs rec recm recx1 recx2 cenv benv renv env _ rx nx k rk _ Hr Wx T).
  - apply andb_true_iff in W as [_ Wx]. apply (IH cs rec recm recx1 recx2 cenv benv renv _ s rx nx k rk _ Hr Wx T).
  - apply andb_true_iff in W as [_ Wx]. apply (IH cs rec recm recx1 recx2 cenv _ renv env s rx nx k rk _ Hr Wx T).
  - apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [_ W1].
    rewrite (IH1 cs rec recm recx1 recx2 cenv benv renv env s rx nx k rk _ Hr W1 T), (IH2 cs rec recm recx1 recx2 cenv benv renv env s rx nx k rk _ Hr W2 T).
    reflexivity.
  - apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [_ W1].
    rewrite (IH1 cs rec recm recx1 recx2 cenv benv renv env s rx nx k rk _ Hr W1 T), (IH2 cs rec recm recx1 recx2 cenv benv renv env s rx nx k rk _ Hr W2 T).
    reflexivity.
  - apply andb_true_iff in W as [W0 W1]. destruct (nth c cenv O);
      [apply (IH0 cs rec recm recx1 recx2 cenv benv renv env s rx nx k rk _ Hr W0 T) | apply (IH1 cs rec recm recx1 recx2 _ benv renv env s rx nx k rk _ Hr W1 T)].
  - apply andb_true_iff in W as [_ Wx]. apply (IH cs rec recm recx1 recx2 _ benv renv env s rx nx k rk _ Hr Wx T).
  - apply andb_true_iff in W as [W _]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W _].
    apply andb_true_iff in W as [W _]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [_ Wn].
    apply Nat.eqb_eq in Wn. apply kinds_eqb_eq in Wk. apply Hr; [rewrite len_denote_cs; exact Wn | erewrite kinds_denote_es by eassumption; exact Wk].
  - reflexivity.
  - apply andb_true_iff in W as [Wr Wx]. apply (IH cs rec recm recx1 recx2 cenv benv _ env s rx nx k _ _ Hr Wx).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - apply andb_true_iff in W as [Wr Wx]. rewrite !rmatch_eq. apply (IH cs rec recm recx1 recx2 cenv benv renv _ s rx nx k rk _ Hr Wx T).
  - apply andb_true_iff in W as [_ Wx]. destruct (denote_pv cs rec recm dpair cenv benv renv env s pp) as [v s2].
    apply (IH cs rec recm recx1 recx2 cenv benv renv _ s2 rx nx k rk _ Hr Wx T).
  - apply andb_true_iff in W as [_ Wx]. cbv zeta. apply (IH cs rec recm recx1 recx2 cenv benv renv _ _ rx nx k rk _ Hr Wx T).
  - apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Er Wr]. apply Nat.eqb_eq in Er. rewrite !rsplit_eq.
    apply (IH cs rec recm recx1 recx2 cenv benv _ _ s rx nx k _ _ Hr Wx).
    apply rsplit_typed; [rewrite <- Er; eapply kind_denote_r; [exact Wr | exact T] | exact T].
  - reflexivity.
  - (* XBind *) cbn [fst] in W. rewrite nth_error_map in W. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|]; [|reflexivity]. cbn in W.
    apply andb_true_iff in W as [_ Wx]. cbv zeta. apply xres_ext; intros;
      (destruct (sw gs); [destruct x; cbn [xfree] in Wx; rewrite ?andb_false_r in Wx; try discriminate Wx; reflexivity | eapply IH; eassumption]).
  - (* XBindR *) apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W _]. apply andb_true_iff in W as [W Ws].
    apply andb_true_iff in W as [W _]. apply andb_true_iff in W as [W _]. apply andb_true_iff in W as [W Wk].
    apply andb_true_iff in W as [_ Wn]. apply Nat.eqb_eq in Wn. apply kinds_eqb_eq in Wk. cbv zeta.
    rewrite Hr; [destruct x; cbn [xfree] in Wx; try discriminate Wx; reflexivity
                | rewrite len_denote_cs; exact Wn | erewrite kinds_denote_es by eassumption; exact Wk].
  - (* XBindP *) cbn [fst] in W. rewrite nth_error_map in W. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|]; [|reflexivity]. cbn in W.
    apply andb_true_iff in W as [_ Wx]. cbv zeta. apply xres_ext; intros;
      (destruct (sw gs); [destruct x; cbn [xfree] in Wx; rewrite ?andb_false_r in Wx; try discriminate Wx; reflexivity | eapply IH; eassumption]).
Qed.

(** the counter of a number, as the two conditional moves of [ccnt] make it *)
Lemma ofn_kq_nat : forall x, ofn (KQ.KQRun.kq_nat x) =
  (let y := if PrimInt63.lesb x 0%uint63 then 0%uint63 else x in if PrimInt63.ltsb cap60 y then cap60 else y).
Proof.
  intros x. cbv zeta.
  destruct (PrimInt63.lesb x 0%uint63) eqn:E0.
  - assert (Z0 : KQ.KQRun.kq_nat x = O).
    { rewrite KQMAuto.kq_nat_clamp. unfold KQMAuto.clampb.
      assert (Ec : PrimInt63.lesb x KQMAuto.cap60 = true).
      { apply KQMAuto.lesb_le. apply KQMAuto.lesb_le_inv in E0. rewrite KQMAuto.cap60_val.
        change (Sint63.to_Z 0%uint63) with 0%Z in E0. lia. }
      rewrite Ec. change 63%nat with (S 62%nat). rewrite KQMAuto.kq_nat_go_S, E0. reflexivity. }
    rewrite Z0, ofn_0. reflexivity.
  - apply Bool.not_true_iff_false in E0.
    assert (P : (0 < Sint63.to_Z x)%Z).
    { destruct (Z_le_gt_dec (Sint63.to_Z x) 0) as [H|H]; [|lia]. exfalso. apply E0. apply KQMAuto.lesb_le.
      change (Sint63.to_Z 0%uint63) with 0%Z. lia. }
    destruct (PrimInt63.ltsb cap60 x) eqn:E1.
    + apply KQMAuto.ltsb_lt_inv in E1. change cap60 with KQMAuto.cap60 in E1. rewrite KQMAuto.cap60_val in E1.
      assert (Ecap : KQ.KQRun.kq_nat x = KQ.KQRun.kq_nat cap60).
      { rewrite !KQMAuto.kq_nat_clamp. unfold KQMAuto.clampb.
        assert (A1 : PrimInt63.lesb x KQMAuto.cap60 = false).
        { destruct (PrimInt63.lesb x KQMAuto.cap60) eqn:Q; auto. apply KQMAuto.lesb_le_inv in Q.
          rewrite KQMAuto.cap60_val in Q. lia. }
        assert (A2 : PrimInt63.lesb cap60 KQMAuto.cap60 = true) by reflexivity.
        rewrite A1, A2. reflexivity. }
      rewrite Ecap. unfold ofn. rewrite (KQMAuto.kq_nat_val cap60) by (vm_compute; split; discriminate).
      reflexivity.
    + assert (E1' : (Sint63.to_Z x <= 1152921504606846976)%Z).
      { destruct (Z_le_gt_dec (Sint63.to_Z x) 1152921504606846976) as [H|H]; auto. exfalso.
        assert (T : PrimInt63.ltsb cap60 x = true).
        { apply KQMAuto.ltsb_lt. change cap60 with KQMAuto.cap60. rewrite KQMAuto.cap60_val. lia. }
        congruence. }
      unfold ofn. rewrite KQMAuto.kq_nat_val by (change (2 ^ 60)%Z with 1152921504606846976%Z; lia).
      rewrite (sZ_small x).
      * apply Uint63.of_to_Z.
      * apply ge0_iff. lia.
Qed.

(** the largest value of a counter (step 33): monotone in the bound of its variables, and above the counter's value *)
Lemma cmax_mono : forall c B1 B2, (B1 <= B2)%Z -> (cmax B1 c <= cmax B2 c)%Z.
Proof. induction c as [i | | c IH | e | c IH | a IHa b IHb]; intros B1 B2 L; cbn [cmax]; try specialize (IH B1 B2 L); try lia.
  specialize (IHa B1 B2 L). specialize (IHb B1 B2 L). lia. Qed.
(** a budget's largest value (step 37): at least its value, at most 2^60 *)
Lemma cnat_max_range : forall e, (0 <= cnat_max e <= 1152921504606846976)%Z.
Proof.
  intros e. destruct e; cbn [cnat_max]; try lia.
  match goal with |- context [Sint63.to_Z ?j] => destruct ((0 <=? Sint63.to_Z j)%Z && (Sint63.to_Z j <=? 1152921504606846976)%Z) eqn:E end; [|lia].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
Qed.
Lemma cnat_max_bound : forall cs rec cenv benv renv denv M e,
  (Z.of_nat (KQ.KQRun.kq_nat (denote_e cs rec cenv benv renv denv M e)) <= cnat_max e)%Z.
Proof.
  intros cs rec cenv benv renv denv M e. pose proof (KQMAuto.kq_nat_le (denote_e cs rec cenv benv renv denv M e)) as K60.
  change (2 ^ 60)%Z with 1152921504606846976%Z in K60. destruct e; cbn [cnat_max]; try lia.
  match goal with |- context [Sint63.to_Z ?j] => destruct ((0 <=? Sint63.to_Z j)%Z && (Sint63.to_Z j <=? 1152921504606846976)%Z) eqn:E end; [|lia].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2. cbn [denote_e]. rewrite KQMAuto.kq_nat_val by lia. lia.
Qed.
Ltac cn_range := repeat match goal with
  | |- context [cnat_max ?e] => lazymatch goal with _ : (0 <= cnat_max e <= _)%Z |- _ => fail | _ => pose proof (cnat_max_range e) end
  | _ : context [cnat_max ?e] |- _ => lazymatch goal with _ : (0 <= cnat_max e <= _)%Z |- _ => fail | _ => pose proof (cnat_max_range e) end
  end.
Lemma cmax_bound : forall B c cs rec cenv benv renv denv M, cbound B cenv ->
  (Z.of_nat (denote_c cs rec cenv benv renv denv M c) <= cmax B c)%Z.
Proof.
  intros B c. induction c as [i | | c IH | e | c IH | a IHa b IHb]; intros cs rec cenv benv renv denv M Cb; cbn [denote_c cmax].
  - specialize (Cb i). lia.
  - lia.
  - specialize (IH cs rec cenv benv renv denv M Cb). lia.
  - pose proof (cnat_max_bound cs rec cenv benv renv denv M e). lia.
  - specialize (IH cs rec cenv benv renv denv M Cb). pose proof (Nat.le_pred_l (denote_c cs rec cenv benv renv denv M c)). lia.
  - specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb). lia.
Qed.
Lemma cmax_depth : forall B c, noadd c = true -> (1152921504606846976 <= B - 1)%Z -> (cmax B c <= B - 1 + Z.of_nat (cdepth c))%Z.
Proof. intros B c. induction c as [i | | c IH | e | c IH | a IHa b IHb]; intros NA L; cbn [cmax cdepth noadd] in *; try discriminate NA;
  try specialize (IH NA L); cn_range; lia. Qed.
Lemma cmax_nonneg : forall B c, (1 <= B)%Z -> (0 <= cmax B c)%Z.
Proof. intros B c L. induction c as [i | | c IH | e | c IH | a IHa b IHb]; cbn [cmax]; cn_range; lia. Qed.

(** each counter below its own bound (step 35): [B] the function's, an entry of [bs] its own when it has one *)
(** each counter below its own bound; the counters bound since the body's start below their linear bounds over the function's
    counters [pv], the bottom of the environment (step 37) *)
Definition cboundv (B : Z) (bs : list cbe) (pv : list nat) (cenv : list nat) : Prop :=
  (forall i, (Z.of_nat (nth i cenv O) < cbv B (fst (nth i bs cbe0)) <= 4611686018427387904)%Z) /\
  skipn (length bs) cenv = pv /\
  (forall i, (i < length bs)%nat -> (Z.of_nat (nth i cenv O) <= leval (snd (nth i bs cbe0)) pv)%Z).
Lemma cboundv_cons : forall B bs pv cenv o p, cboundv B bs pv cenv -> (Z.of_nat p < cbv B (fst o) <= 4611686018427387904)%Z ->
  (Z.of_nat p <= leval (snd o) pv)%Z -> cboundv B (o :: bs) pv (p :: cenv).
Proof.
  intros B bs pv cenv o p (C1 & C2 & C3) L1 L2. split; [|split].
  - intros [|i]; simpl; auto.
  - simpl. exact C2.
  - intros [|i] Hi; simpl in *; [exact L2 | apply C3; lia].
Qed.
Lemma cboundv_nil : forall B cenv, cbound B cenv -> (B <= 4611686018427387904)%Z -> cboundv B [] cenv cenv.
Proof.
  intros B cenv C L. split; [|split].
  - intros i. specialize (C i). assert (E : nth i (@nil cbe) cbe0 = cbe0) by (destruct i; reflexivity). rewrite E. cbn [cbv fst cbe0]. lia.
  - reflexivity.
  - intros i Hi. simpl in Hi. lia.
Qed.
Lemma cmaxv_bound : forall B bs pv c cs rec cenv benv renv denv M, cboundv B bs pv cenv ->
  (Z.of_nat (denote_c cs rec cenv benv renv denv M c) <= cmaxv B bs c)%Z.
Proof.
  intros B bs pv c. induction c as [i | | c IH | e | c IH | a IHa b IHb]; intros cs rec cenv benv renv denv M Cb; cbn [denote_c cmaxv].
  - pose proof (proj1 Cb i). lia.
  - lia.
  - specialize (IH cs rec cenv benv renv denv M Cb). lia.
  - pose proof (cnat_max_bound cs rec cenv benv renv denv M e). lia.
  - specialize (IH cs rec cenv benv renv denv M Cb). pose proof (Nat.le_pred_l (denote_c cs rec cenv benv renv denv M c)). lia.
  - specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb). lia.
Qed.
Lemma cmaxv_mono : forall bs c B1 B2, (B1 <= B2)%Z -> (cmaxv B1 bs c <= cmaxv B2 bs c)%Z.
Proof.
  intros bs c. induction c as [i | | c IH | e | c IH | a IHa b IHb]; intros B1 B2 L; cbn [cmaxv]; try specialize (IH B1 B2 L); try lia.
  - unfold cbv. destruct (fst (nth i bs cbe0)); lia.
  - specialize (IHa B1 B2 L). specialize (IHb B1 B2 L). lia.
Qed.
Lemma cmaxv_cmax : forall B bs c, (1 <= B)%Z -> pvars bs c = true -> cmaxv B bs c = cmax B c.
Proof.
  intros B bs c L. induction c as [i | | c IH | e | c IH | a IHa b IHb]; intros P; cbn [cmaxv cmax pvars] in *; try reflexivity;
    try (rewrite IH by exact P; reflexivity).
  - destruct (fst (nth i bs cbe0)); [discriminate P | cbn [cbv]; lia].
  - apply andb_true_iff in P as [Pa Pb]. rewrite IHa, IHb by auto. reflexivity.
Qed.
Lemma cmaxv_nonneg : forall B bs c, (0 <= cmaxv B bs c)%Z.
Proof. intros B bs c. induction c as [i | | c IH | e | c IH | a IHa b IHb]; cbn [cmaxv]; cn_range; lia. Qed.

Lemma cmax_free : forall B c, cfree c = true -> noadd c = true -> (cmax B c <= 1152921504606846976 + Z.of_nat (cdepth c))%Z.
Proof. intros B c. induction c as [i | | c IH | e | c IH | a IHa b IHb]; intros F NA; cbn [cfree noadd cmax cdepth] in *; try discriminate;
  try specialize (IH F NA); cn_range; lia. Qed.

(** linear bounds (step 37) *)
Lemma evc_addc : forall a b pv, evc (addc a b) pv = (evc a pv + evc b pv)%Z.
Proof.
  induction a as [|x a IH]; intros b pv; [cbn [addc evc]; lia|].
  destruct b as [|y b]; [cbn [addc]; destruct pv; cbn [evc]; lia|].
  destruct pv as [|v pv]; cbn [addc evc]; [lia|]. rewrite IH. lia.
Qed.
Lemma leval_add : forall a b pv, leval (ladd a b) pv = (leval a pv + leval b pv)%Z.
Proof. intros [a x] [b y] pv. unfold leval, ladd. cbn [fst snd]. rewrite evc_addc. lia. Qed.
Lemma leval_shift : forall z a pv, leval (lshift z a) pv = (leval a pv + z)%Z.
Proof. intros z [a x] pv. unfold leval, lshift. cbn [fst snd]. lia. Qed.
Lemma evc_scale : forall w a pv, evc (map (Z.mul w) a) pv = (w * evc a pv)%Z.
Proof. intros w. induction a as [|x a IH]; intros pv; destruct pv as [|v pv]; cbn [map evc]; try lia. rewrite IH. ring. Qed.
Lemma leval_scale : forall w a pv, leval (lscale w a) pv = (w * leval a pv)%Z.
Proof. intros w [a x] pv. unfold leval, lscale. cbn [fst snd]. rewrite evc_scale. ring. Qed.
Lemma evc_unit : forall j pv, evc (lunitc j) pv = Z.of_nat (nth j pv O).
Proof. induction j as [|j IH]; intros [|v pv]; cbn [lunitc evc nth]; try lia. rewrite IH. lia. Qed.
Lemma leval_unit : forall j pv, leval (lunit j) pv = Z.of_nat (nth j pv O).
Proof. intros j pv. unfold leval, lunit. cbn [fst snd]. rewrite evc_unit. lia. Qed.
Lemma leval_zero : forall pv, leval lzero pv = 0%Z.
Proof. intros pv. reflexivity. Qed.
Lemma nth_skipn_nat : forall (l : list nat) m n, nth n (skipn m l) O = nth (m + n) l O.
Proof. induction l as [|x l IH]; intros [|m] n; cbn [skipn nth]; try reflexivity; try (destruct n; reflexivity). apply IH. Qed.
Lemma linat_bound : forall B bs pv cenv i, cboundv B bs pv cenv -> (Z.of_nat (nth i cenv O) <= leval (linat bs i) pv)%Z.
Proof.
  intros B bs pv cenv i (C1 & C2 & C3). unfold linat. destruct (Nat.ltb i (length bs)) eqn:L.
  - apply Nat.ltb_lt in L. apply C3; exact L.
  - apply Nat.ltb_ge in L. rewrite leval_unit. rewrite <- C2. rewrite nth_skipn_nat. replace (length bs + (i - length bs))%nat with i by lia. lia.
Qed.
Lemma clinf_bound : forall B bs pv c cs rec cenv benv renv denv M, cboundv B bs pv cenv ->
  (Z.of_nat (denote_c cs rec cenv benv renv denv M c) <= leval (clinf bs c) pv)%Z.
Proof.
  intros B bs pv c. induction c as [i | | c IH | e | c IH | a IHa b IHb]; intros cs rec cenv benv renv denv M Cb; cbn [denote_c clinf].
  - eapply linat_bound; eauto.
  - rewrite leval_zero. lia.
  - rewrite leval_shift. specialize (IH cs rec cenv benv renv denv M Cb). lia.
  - pose proof (KQMAuto.kq_nat_le (denote_e cs rec cenv benv renv denv M e)) as K60. change (2 ^ 60)%Z with 1152921504606846976%Z in K60.
    unfold leval. cbn [fst snd evc]. pose proof (cnat_max_bound cs rec cenv benv renv denv M e). lia.
  - specialize (IH cs rec cenv benv renv denv M Cb). pose proof (Nat.le_pred_l (denote_c cs rec cenv benv renv denv M c)). lia.
  - rewrite leval_add. specialize (IHa cs rec cenv benv renv denv M Cb). specialize (IHb cs rec cenv benv renv denv M Cb). lia.
Qed.
Lemma clinf_bounds : forall B bs pv ccs cs rec cenv benv renv denv M, cboundv B bs pv cenv ->
  Forall2 (fun v c => (Z.of_nat v <= leval (clinf bs c) pv)%Z) (denote_cs cs rec cenv benv renv denv M ccs) (lc ccs).
Proof.
  intros B bs pv. induction ccs as [|c ccs IH]; intros cs rec cenv benv renv denv M Cb; cbn [denote_cs lc]; constructor.
  - eapply clinf_bound; eauto.
  - apply IH; exact Cb.
Qed.
(** a linear bound at most one of the counters, each below [B]: below [B] (step 37) *)
Lemma sum_nonneg : forall a, Forall (fun z => (0 <= z)%Z) a -> (0 <= fold_right Z.add 0%Z a)%Z.
Proof. induction a as [|x a IH]; intros A; cbn [fold_right]; [lia|]. inversion A as [|? ? Hx Ha]; subst. specialize (IH Ha). lia. Qed.
Lemma evc_le_sum : forall a pv M, Forall (fun z => (0 <= z)%Z) a -> Forall (fun v => (Z.of_nat v <= M)%Z) pv -> (0 <= M)%Z ->
  (evc a pv <= M * fold_right Z.add 0%Z a)%Z.
Proof.
  induction a as [|x a IH]; intros pv M A P L; cbn [evc fold_right]; [lia|].
  inversion A as [|? ? Hx Ha]; subst. pose proof (sum_nonneg a Ha) as S0.
  destruct pv as [|v pv]; cbn [evc]; [nia|].
  inversion P as [|? ? Hv Hp]; subst. specialize (IH pv M Ha Hp L). nia.
Qed.
Lemma lin1_lt : forall l pv B, lin1 l = true -> Forall (fun v => (Z.of_nat v < B)%Z) pv -> (0 < B)%Z -> (leval l pv < B)%Z.
Proof.
  intros [a k] pv B Hl P L. unfold lin1 in Hl. cbn [fst snd] in Hl. apply andb_true_iff in Hl as [Hl Hk]. apply andb_true_iff in Hl as [Ha Hs].
  apply Z.leb_le in Hs. apply Z.leb_le in Hk.
  assert (A : Forall (fun z => (0 <= z)%Z) a).
  { apply Forall_forall. intros z Hz. rewrite forallb_forall in Ha. specialize (Ha z Hz). apply Z.leb_le in Ha. exact Ha. }
  assert (P' : Forall (fun v => (Z.of_nat v <= B - 1)%Z) pv) by (eapply Forall_impl; [|exact P]; intros v Hv; cbv beta in *; lia).
  pose proof (evc_le_sum a pv (B - 1) A P' ltac:(lia)) as E. pose proof (sum_nonneg a A). unfold leval. cbn [fst snd]. nia.
Qed.
Lemma evc_nonneg : forall w pv, Forall (fun z => (0 <= z)%Z) w -> (0 <= evc w pv)%Z.
Proof. induction w as [|x w IH]; intros [|v pv] Wn; cbn [evc]; try lia. inversion Wn as [|? ? Hx Hw]; subst. specialize (IH pv Hw). nia. Qed.
Lemma evc_mono : forall a w pv, Forall (fun z => (0 <= z)%Z) w -> coefs_le a w = true -> (evc a pv <= evc w pv)%Z.
Proof.
  induction a as [|x a IH]; intros w pv Wn C.
  - cbn [evc]. apply evc_nonneg; exact Wn.
  - destruct w as [|y w]; cbn [coefs_le] in C; apply andb_true_iff in C as [C1 C2]; apply Z.leb_le in C1.
    + destruct pv as [|v pv]; cbn [evc]; [lia|]. pose proof (IH [] pv (Forall_nil _) C2) as H. cbn [evc] in H. nia.
    + inversion Wn as [|? ? Hy Hw]; subst. destruct pv as [|v pv]; cbn [evc]; [lia|]. pose proof (IH w pv Hw C2). nia.
Qed.
Lemma evc_app_r : forall a b c, (length a <= length b)%nat -> evc a (b ++ c) = evc a b.
Proof. induction a as [|x a IH]; intros [|y b] c L; cbn [evc app length] in *; try lia. rewrite IH by lia. reflexivity. Qed.
Lemma evc_app : forall a b c d, length a = length b -> evc (a ++ c) (b ++ d) = (evc a b + evc c d)%Z.
Proof. induction a as [|x a IH]; intros [|y b] c d L; cbn [evc app length] in *; try lia. rewrite IH by lia. lia. Qed.
Lemma Forall2_mapr : forall {A B C : Type} (P : A -> C -> Prop) (f : B -> C) l1 l2,
  Forall2 (fun a b => P a (f b)) l1 l2 -> Forall2 P l1 (map f l2).
Proof. intros A B C P f l1 l2 F. induction F; constructor; auto. Qed.
(** the weighted counters the recursion is given are below the weighted sum before it *)
Lemma dotw_le_tot : forall pv wt vals ls, Forall2 (fun v l => (Z.of_nat v <= leval l pv)%Z) vals ls ->
  (Z.of_nat (dotw wt vals) <= leval (fold_right ladd lzero (map (fun q => lscale (fst q) (snd q)) (combine (map Z.of_nat wt) ls))) pv)%Z.
Proof.
  intros pv. induction wt as [|w wt IH]; intros vals ls F.
  - cbn [dotw map combine fold_right]. rewrite leval_zero. lia.
  - destruct F as [|v l vals ls Hv F]; cbn [dotw map combine fold_right]; [rewrite leval_zero; lia|].
    rewrite leval_add, leval_scale. cbn [fst snd]. specialize (IH vals ls F). nia.
Qed.
Lemma pot_sound : forall ws bs ccs vals prest cm, pot_ok ws bs ccs = true -> (1 <= length ws)%nat -> length prest = length (tl ws) ->
  Forall2 (fun v c => (Z.of_nat v <= leval (clinf bs c) (prest ++ [S cm]))%Z) vals (lc ccs) ->
  (Z.of_nat (dotw ws (cm :: vals)) <= evc (map Z.of_nat (rev ws)) (prest ++ [S cm]))%Z.
Proof.
  intros ws bs ccs vals prest cm Pk Lw Lp F.
  destruct ws as [|w1 wt]; [cbn in Lw; lia|]. cbn [tl hd] in *.
  unfold pot_ok in Pk. cbn [tl hd] in Pk. apply andb_true_iff in Pk as [Pk Pc]. apply andb_true_iff in Pk as [_ Pco].
  apply Z.leb_le in Pc.
  set (tot := fold_right ladd lzero (map (fun q => lscale (fst q) (snd q)) (combine (map Z.of_nat wt) (map (clinf bs) (lc ccs))))) in *.
  assert (A : (Z.of_nat (dotw wt vals) <= leval tot (prest ++ [S cm]))%Z).
  { apply dotw_le_tot. apply Forall2_mapr. exact F. }
  assert (Nn : Forall (fun z => (0 <= z)%Z) (rev (map Z.of_nat wt))).
  { apply Forall_rev. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (n & <- & _). lia. }
  assert (Mo : (evc (fst tot) (prest ++ [S cm]) <= evc (rev (map Z.of_nat wt)) (prest ++ [S cm]))%Z) by (apply evc_mono; assumption).
  rewrite (evc_app_r (rev (map Z.of_nat wt)) prest [S cm]) in Mo by (rewrite length_rev, length_map; lia).
  cbn [rev]. rewrite map_app, map_rev. cbn [map].
  rewrite (evc_app (rev (map Z.of_nat wt)) prest [Z.of_nat w1] [S cm]) by (rewrite length_rev, length_map; lia).
  cbn [dotw evc]. unfold leval in A. nia.
Qed.
Lemma list_cases_nat : forall (l : list nat), l = [] \/ exists x r, l = x :: r.
Proof. intros [|x r]; [left; reflexivity | right; eauto]. Qed.
Lemma list_cases_ln : forall (l : list (list nat)), l = [] \/ exists x r, l = x :: r.
Proof. intros [|x r]; [left; reflexivity | right; eauto]. Qed.
(** a counter whose weight is at least 1 is at most the weighted sum (step 38) *)
Lemma dotw_ge_nth : forall ws cvs i, (1 <= nth i ws O)%nat -> (nth i cvs O <= dotw ws cvs)%nat.
Proof.
  induction ws as [|w ws IH]; intros cvs i L; [destruct i; cbn [nth] in L; lia|].
  destruct cvs as [|c cvs]; [destruct i; cbn [nth]; lia|]. destruct i as [|i]; cbn [nth dotw] in *; [nia|].
  specialize (IH cvs i L). lia.
Qed.
Lemma len_lc : forall ccs, length (lc ccs) = len_c ccs.
Proof. induction ccs as [|c ccs IH]; cbn [lc len_c length]; congruence. Qed.
Lemma all_c_forall : forall p ccs, all_c p ccs = forallb p (lc ccs).
Proof. intros p. induction ccs as [|c ccs IH]; cbn [all_c lc forallb]; congruence. Qed.
Lemma wdot_nonneg : forall ws zs, Forall (fun z => (0 <= z)%Z) zs -> (0 <= wdot ws zs)%Z.
Proof. induction ws as [|w ws IH]; intros [|z zs] F; cbn [wdot]; try lia. inversion F as [|? ? Hz Hzs]; subst. specialize (IH zs Hzs). nia. Qed.
Lemma wdot_ge_each : forall ws zs, forallb (Nat.leb 1) ws = true -> Forall (fun z => (0 <= z)%Z) zs -> length zs = length ws ->
  Forall (fun z => (z <= wdot ws zs)%Z) zs.
Proof.
  induction ws as [|w ws IH]; intros [|z zs] Wg F L; cbn [length] in L; try discriminate; [constructor|].
  cbn [forallb] in Wg. apply andb_true_iff in Wg as [W1 Wg]. apply Nat.leb_le in W1. inversion F as [|? ? Hz Hzs]; subst.
  pose proof (wdot_nonneg ws zs Hzs). specialize (IH zs Wg Hzs ltac:(lia)). cbn [wdot]. constructor; [nia|].
  eapply Forall_impl; [| exact IH]. intros a Ha. cbn beta in Ha. nia.
Qed.
Lemma dotw_le_wdot : forall ws vals zs, Forall2 (fun v z => (Z.of_nat v <= z)%Z) vals zs -> (Z.of_nat (dotw ws vals) <= wdot ws zs)%Z.
Proof.
  induction ws as [|w ws IH]; intros vals zs F; cbn [dotw wdot]; [lia|].
  destruct F as [|v z vals zs Hv F]; cbn [dotw wdot]; [lia|]. specialize (IH vals zs F). nia.
Qed.

Lemma list_cases_any : forall {A : Type} (l : list A), l = [] \/ exists x r, l = x :: r.
Proof. intros A [|x r]; [left; reflexivity | right; eauto]. Qed.
(** polynomials (step 39): evaluation of sums, products, substitutions *)
Lemma prodz_app : forall xs l1 l2, prodz xs (l1 ++ l2) = (prodz xs l1 * prodz xs l2)%Z.
Proof. intros xs l1 l2. induction l1 as [|i l1 IH]; cbn [app prodz]; [ring|]. rewrite IH. ring. Qed.
Lemma zeval_nil : forall v, zeval [] v = 0%Z.
Proof. reflexivity. Qed.
Lemma zeval_cons : forall m A v, zeval (m :: A) v = (fst m * prodz v (snd m) + zeval A v)%Z.
Proof. reflexivity. Qed.
Lemma zeval_app : forall A B v, zeval (A ++ B) v = (zeval A v + zeval B v)%Z.
Proof. intros A B v. induction A as [|m A IH]; [reflexivity|]. cbn [app]. rewrite !zeval_cons, IH. ring. Qed.
Lemma zeval_map_mul : forall c l B v, zeval (map (fun b => ((c * fst b)%Z, l ++ snd b)) B) v = (c * prodz v l * zeval B v)%Z.
Proof.
  intros c l B v. induction B as [|b B IH]; cbn [map]; [rewrite !zeval_nil; ring|].
  rewrite !zeval_cons, IH. cbn [fst snd]. rewrite prodz_app. ring.
Qed.
Lemma zeval_zmul : forall A B v, zeval (zmul A B) v = (zeval A v * zeval B v)%Z.
Proof.
  intros A B v. unfold zmul. induction A as [|a A IH]; cbn [flat_map]; [rewrite !zeval_nil; ring|].
  rewrite zeval_app, IH, zeval_cons, (zeval_map_mul (fst a) (snd a) B v). ring.
Qed.
Lemma zeval_zprod : forall As v, zeval (zprod As) v = fold_right Z.mul 1%Z (map (fun A => zeval A v) As).
Proof.
  intros As v. induction As as [|A As IH]; [cbn; ring|]. unfold zprod in *. cbn [fold_right map].
  rewrite zeval_zmul, IH. reflexivity.
Qed.
Lemma zeval_zneg : forall A v, zeval (zneg A) v = (- zeval A v)%Z.
Proof. intros A v. induction A as [|m A IH]; [reflexivity|]. unfold zneg in *. cbn [map]. rewrite !zeval_cons, IH. cbn [fst snd]. ring. Qed.
Lemma prodz_ext : forall l xs (f : nat -> Z), (forall i, nth i xs 0%Z = f i) -> prodz xs l = fold_right Z.mul 1%Z (map f l).
Proof. induction l as [|i l IH]; intros xs f H; cbn [prodz map fold_right]; [reflexivity|]. rewrite H, (IH xs f H). reflexivity. Qed.
Lemma pevalz_zsubst : forall P s v xs, (forall i, nth i xs 0%Z = zeval (s i) v) -> zeval (zsubst P s) v = pevalz P xs.
Proof.
  intros P s v xs H. unfold zsubst, pevalz. induction P as [|m P IH]; cbn [flat_map fold_right]; [reflexivity|].
  rewrite zeval_app, IH, zeval_zmul, zeval_zprod, map_map, zeval_cons, zeval_nil. cbn [fst snd prodz].
  rewrite (prodz_ext (snd m) xs (fun i => zeval (s i) v) H). ring.
Qed.
(** a polynomial with no coefficient below 0 grows with each counter *)
Lemma prodz_mono : forall l xs ys, (forall i, (0 <= nth i xs 0 <= nth i ys 0)%Z) -> (0 <= prodz xs l <= prodz ys l)%Z.
Proof. induction l as [|i l IH]; intros xs ys H; cbn [prodz]; [lia|]. specialize (IH xs ys H). specialize (H i). nia. Qed.
Lemma pevalz_mono : forall P xs ys, (forall i, (0 <= nth i xs 0 <= nth i ys 0)%Z) -> (0 <= pevalz P xs <= pevalz P ys)%Z.
Proof. intros P xs ys H. unfold pevalz. induction P as [|m P IH]; cbn [fold_right]; [lia|]. pose proof (prodz_mono (snd m) xs ys H). nia. Qed.
(** a counter whose monomial has a coefficient of at least 1 is at most the polynomial *)
Lemma pevalz_unit : forall P c i xs, In (c, [i]) P -> (1 <= c)%nat -> (forall j, (0 <= nth j xs 0)%Z) -> (nth i xs 0 <= pevalz P xs)%Z.
Proof.
  intros P c i xs Hin Hc H. unfold pevalz.
  assert (N : forall Q, (0 <= fold_right (fun m a => (Z.of_nat (fst m) * prodz xs (snd m) + a)%Z) 0%Z Q)%Z).
  { induction Q as [|m' Q IHQ]; cbn [fold_right]; [lia|]. pose proof (prodz_mono (snd m') xs xs ltac:(intros j; split; [apply H | lia])). nia. }
  induction P as [|m P IH]; [destruct Hin|]. cbn [fold_right].
  destruct Hin as [-> | Hin].
  - cbn [fst snd prodz]. specialize (N P). specialize (H i). nia.
  - specialize (IH Hin). pose proof (prodz_mono (snd m) xs xs ltac:(intros j; split; [apply H | lia])). nia.
Qed.
(** the check: equal monomials summed (each one's counters sorted), no coefficient below 0, gives a sum at least 0 *)
Lemma prodz_ins : forall xs x l, prodz xs (ins x l) = prodz xs (x :: l).
Proof. intros xs x l. induction l as [|y l IH]; cbn [ins]; [reflexivity|]. destruct (Nat.leb x y); [reflexivity|]. cbn [prodz] in *. rewrite IH. ring. Qed.
Lemma prodz_isort : forall xs l, prodz xs (isort l) = prodz xs l.
Proof. intros xs l. induction l as [|x l IH]; cbn [isort]; [reflexivity|]. rewrite prodz_ins. cbn [prodz]. rewrite IH. reflexivity. Qed.
Definition ksum (K : list (list nat)) (A : zpoly) (v : list Z) : Z := fold_right (fun k a => (zcoef A k * prodz v k + a)%Z) 0%Z K.
Lemma ksum_nil : forall K v, ksum K [] v = 0%Z.
Proof. intros K v. unfold ksum. induction K as [|k K IH]; cbn [fold_right]; [reflexivity|]. rewrite IH. change (zcoef [] k) with 0%Z. ring. Qed.
Lemma ksum_split : forall K m A v, ksum K (m :: A) v =
  (fold_right (fun k a => ((if list_eq_dec Nat.eq_dec (isort (snd m)) k then fst m else 0) * prodz v k + a)%Z) 0%Z K + ksum K A v)%Z.
Proof.
  intros K m A v. unfold ksum. induction K as [|k K IH]; cbn [fold_right]; [reflexivity|]. rewrite IH.
  unfold zcoef at 1. cbn [fold_right]. fold (zcoef A k). destruct (list_eq_dec Nat.eq_dec (isort (snd m)) k); ring.
Qed.
Lemma ksum_one : forall K x c v, NoDup K -> In x K ->
  fold_right (fun k a => ((if list_eq_dec Nat.eq_dec x k then c else 0) * prodz v k + a)%Z) 0%Z K = (c * prodz v x)%Z.
Proof.
  induction K as [|k K IH]; intros x c v ND Hin; [destruct Hin|]. inversion ND as [|? ? Nk ND']; subst. cbn [fold_right].
  destruct (list_eq_dec Nat.eq_dec x k) as [<- | Ne].
  - assert (Z0 : forall K', ~ In x K' -> fold_right (fun k a => ((if list_eq_dec Nat.eq_dec x k then c else 0) * prodz v k + a)%Z) 0%Z K' = 0%Z).
    { induction K' as [|k' K' IHK]; intros Nx; cbn [fold_right]; [reflexivity|].
      destruct (list_eq_dec Nat.eq_dec x k') as [<- | _]; [exfalso; apply Nx; left; reflexivity|].
      rewrite IHK by (intros Hx; apply Nx; right; exact Hx). ring. }
    rewrite (Z0 K Nk). ring.
  - destruct Hin as [-> | Hin]; [contradiction|]. rewrite (IH x c v ND' Hin). ring.
Qed.
Lemma zeval_ksum : forall A K v, NoDup K -> (forall m, In m A -> In (isort (snd m)) K) -> zeval A v = ksum K A v.
Proof.
  induction A as [|m A IH]; intros K v ND HK; [rewrite ksum_nil; reflexivity|].
  rewrite zeval_cons, ksum_split, <- (IH K v ND) by (intros m' Hm'; apply HK; right; exact Hm').
  rewrite (ksum_one K (isort (snd m)) (fst m) v ND (HK m (or_introl eq_refl))), prodz_isort. ring.
Qed.
Lemma znonneg_sound : forall A v, znonneg A = true -> (forall j, (0 <= nth j v 0)%Z) -> (0 <= zeval A v)%Z.
Proof.
  intros A v Nn Hv. set (K := nodup (list_eq_dec Nat.eq_dec) (map (fun m => isort (snd m)) A)).
  rewrite (zeval_ksum A K v (NoDup_nodup _ _)) by (intros m Hm; apply nodup_In; apply in_map_iff; exists m; split; [reflexivity | exact Hm]).
  unfold znonneg in Nn. fold K in Nn. rewrite forallb_forall in Nn. unfold ksum.
  assert (G : forall K', (forall x, In x K' -> In x K) -> (0 <= fold_right (fun k a => (zcoef A k * prodz v k + a)%Z) 0%Z K')%Z).
  { induction K' as [|k K' IH]; intros Inc; cbn [fold_right]; [lia|].
    pose proof (Nn k (Inc k (or_introl eq_refl))) as C. apply Z.leb_le in C.
    pose proof (prodz_mono k v v ltac:(intros j; split; [apply Hv | lia])) as Pm.
    specialize (IH (fun x Hx => Inc x (or_intror Hx))). nia. }
  apply G. intros x Hx; exact Hx.
Qed.
(** a linear bound at the counters at the body's start, as a polynomial in the predecessor and the other counters *)
Lemma skipn_nth_cons : forall (l : list nat) k, (k < length l)%nat -> skipn k l = nth k l O :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] H; cbn [length skipn nth] in *; try lia; [reflexivity|]. apply IH. lia. Qed.
Lemma nth_ofnat_nonneg : forall l j, (0 <= nth j (map Z.of_nat l) 0)%Z.
Proof. induction l as [|x l IH]; intros [|j]; cbn [map nth]; try lia; auto. Qed.
Lemma nth_ofnat : forall l j, nth j (map Z.of_nat l) 0%Z = Z.of_nat (nth j l O).
Proof. induction l as [|x l IH]; intros [|j]; cbn [map nth]; auto. Qed.
Lemma zeval_zlin_from : forall cs k rest cm,
  zeval (flat_map (fun ia : nat * Z => if Nat.ltb (fst ia) (Nat.pred (S (length rest))) then [(snd ia, [(Nat.pred (S (length rest)) - fst ia)%nat])]
                          else if Nat.eqb (fst ia) (Nat.pred (S (length rest))) then [(snd ia, [O]); (snd ia, [])] else [])
         (combine (seq k (length cs)) cs)) (map Z.of_nat (cm :: rest)) = evc cs (skipn k (rev rest ++ [S cm])).
Proof.
  assert (Ec : forall c, evc c [] = 0%Z) by (intros [|? ?]; reflexivity).
  induction cs as [|a cs IH]; intros k rest cm; [cbn [length seq combine flat_map]; rewrite zeval_nil; reflexivity|].
  cbn [length seq combine flat_map]. rewrite zeval_app, IH. cbn [Nat.pred fst snd].
  assert (Lpv : length (rev rest ++ [S cm]) = S (length rest)) by (rewrite length_app, length_rev; cbn [length]; lia).
  destruct (Nat.lt_ge_cases k (S (length rest))) as [Hk | Hk].
  - rewrite (skipn_nth_cons (rev rest ++ [S cm]) k) by lia. cbn [evc].
    destruct (Nat.ltb k (length rest)) eqn:E1.
    + apply Nat.ltb_lt in E1. cbv beta iota. rewrite zeval_cons, zeval_nil. cbn [fst snd prodz].
      rewrite app_nth1 by (rewrite length_rev; lia). rewrite rev_nth by lia.
      replace (length rest - k)%nat with (S (length rest - S k)) by lia. cbn [map nth]. rewrite nth_ofnat. ring.
    + apply Nat.ltb_ge in E1. assert (Ek : k = length rest) by lia. subst k. rewrite Nat.eqb_refl. cbv beta iota.
      rewrite !zeval_cons, zeval_nil. cbn [fst snd prodz map nth].
      rewrite app_nth2 by (rewrite length_rev; lia). rewrite length_rev, Nat.sub_diag. cbn [nth]. rewrite Nat2Z.inj_succ. ring.
  - rewrite !skipn_all2 by lia. rewrite Ec.
    destruct (Nat.ltb k (length rest)) eqn:E1; [apply Nat.ltb_lt in E1; lia|].
    destruct (Nat.eqb k (length rest)) eqn:E2; [apply Nat.eqb_eq in E2; lia|]. cbv beta iota. rewrite zeval_nil. reflexivity.
Qed.
Lemma zeval_zlin : forall l rest cm, zeval (zlin (S (length rest)) l) (map Z.of_nat (cm :: rest)) = leval l (rev rest ++ [S cm]).
Proof.
  intros l rest cm. unfold zlin, leval. rewrite zeval_cons. cbn [fst snd prodz].
  rewrite (zeval_zlin_from (fst l) 0 rest cm). cbn [skipn]. ring.
Qed.
(** the recursion keeps a polynomial from growing *)
Lemma nth_map_err : forall (g : scnt -> Z) l j, nth j (map g l) 0%Z = match nth_error l j with Some c => g c | None => 0%Z end.
Proof. intros g l. induction l as [|c l IH]; intros [|j]; cbn [map nth nth_error]; auto. Qed.
Lemma Forall2_nth_le : forall (vals : list nat) (cs : list scnt) (g : scnt -> Z), Forall2 (fun v c => (Z.of_nat v <= g c)%Z) vals cs ->
  forall j, (0 <= nth j (map Z.of_nat vals) 0 <= nth j (map g cs) 0)%Z.
Proof. intros vals cs g. induction 1 as [|v c vals cs H F IH]; intros [|j]; cbn [map nth]; try lia; auto. Qed.
Lemma ppot_sound : forall P bs ccs vals rest cm, ppot_ok P bs ccs = true -> length rest = len_c ccs ->
  Forall2 (fun v c => (Z.of_nat v <= leval (clinf bs c) (rev rest ++ [S cm]))%Z) vals (lc ccs) ->
  (pevalz P (map Z.of_nat (cm :: vals)) <= pevalz P (map Z.of_nat (S cm :: rest)))%Z.
Proof.
  intros P bs ccs vals rest cm Pk Lr F. unfold ppot_ok in Pk. cbv zeta in Pk.
  set (v := map Z.of_nat (cm :: rest)) in *.
  pose proof (znonneg_sound _ v Pk (nth_ofnat_nonneg (cm :: rest))) as N.
  rewrite zeval_app, zeval_zneg in N.
  set (us := Z.of_nat cm :: map (fun c => leval (clinf bs c) (rev rest ++ [S cm])) (lc ccs)).
  rewrite (pevalz_zsubst P _ v (map Z.of_nat (S cm :: rest))) in N.
  2:{ intros [|i]; unfold v; cbn [Nat.eqb map nth]; [rewrite !zeval_cons, zeval_nil; cbn [fst snd prodz map nth]; lia|].
      destruct (Nat.ltb (S i) (S (len_c ccs))) eqn:E.
      - apply Nat.ltb_lt in E. rewrite zeval_cons, zeval_nil. cbn [fst snd prodz map nth]. ring.
      - apply Nat.ltb_ge in E. rewrite zeval_nil. apply nth_overflow. rewrite length_map. lia. }
  rewrite (pevalz_zsubst P _ v us) in N.
  2:{ intros [|i]; unfold us; cbn [Nat.eqb nth Nat.pred]; [unfold v; rewrite zeval_cons, zeval_nil; cbn [fst snd prodz map nth]; ring|].
      rewrite nth_map_err. destruct (nth_error (lc ccs) i) as [c|]; [|reflexivity].
      unfold v. rewrite <- Lr. symmetry. apply zeval_zlin. }
  pose proof (pevalz_mono P (map Z.of_nat (cm :: vals)) us) as M.
  assert (Hm : forall i, (0 <= nth i (map Z.of_nat (cm :: vals)) 0 <= nth i us 0)%Z).
  { intros [|i]; unfold us; cbn [map nth]; [lia|]. exact (Forall2_nth_le vals (lc ccs) _ F i). }
  specialize (M Hm). lia.
Qed.

(** a boolean's and a record's meaning depend on their recursive function at the counters and arguments the recursion gives only
    (step 41: the copies' theorems for every result kind) *)
Lemma denote_bb_recb_ext : forall b cs rec recb1 recb2 cenv benv renv env s r rb mok nx k rk cbo,
  (forall cvs l s', length cvs = nx -> map kind_of l = k -> recb1 cvs l s' = recb2 cvs l s') ->
  wfbb (map (@projT1 _ _) cs, cbo) r rb mok nx k rk b = true -> rtyped renv rk ->
  denote_bb cs rec recb1 cenv benv renv env s b = denote_bb cs rec recb2 cenv benv renv env s b.
Proof.
  induction b as [x | ccs args | ccs args | e b IH | c b IH | c b IH | x b IH | x b IH | c x y t IHt f IHf | c t IHt f IHf | c b0 IH0 b1 IH1 | sj x b IH];
    intros cs rec recb1 recb2 cenv benv renv env s r rb mok nx k rk cbo Hr W T; cbn [denote_bb wfbb] in *.
  - reflexivity.
  - split_w W. apply Nat.eqb_eq in W4. apply kinds_eqb_eq in W3.
    apply Hr; [rewrite len_denote_cs; exact W4 | erewrite kinds_denote_es by eassumption; exact W3].
  - split_w W. apply Nat.eqb_eq in W4. apply kinds_eqb_eq in W3. f_equal.
    apply Hr; [rewrite len_denote_cs; exact W4 | erewrite kinds_denote_es by eassumption; exact W3].
  - split_w W. apply (IH cs rec recb1 recb2 cenv benv renv _ s r rb mok nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec recb1 recb2 cenv _ renv env s r rb mok nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec recb1 recb2 _ benv renv env s r rb mok nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec recb1 recb2 cenv benv _ env s r rb mok nx k _ _ Hr W0).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - split_w W. rewrite !rmatch_eq. apply (IH cs rec recb1 recb2 cenv benv renv _ s r rb mok nx k rk _ Hr W0 T).
  - split_w W. rewrite (IHt cs rec recb1 recb2 cenv benv renv env s r rb mok nx k rk _ Hr W1 T),
                       (IHf cs rec recb1 recb2 cenv benv renv env s r rb mok nx k rk _ Hr W0 T). reflexivity.
  - split_w W. rewrite (IHt cs rec recb1 recb2 cenv benv renv env s r rb mok nx k rk _ Hr W1 T),
                       (IHf cs rec recb1 recb2 cenv benv renv env s r rb mok nx k rk _ Hr W0 T). reflexivity.
  - split_w W. destruct (nth c cenv O);
      [apply (IH0 cs rec recb1 recb2 cenv benv renv env s r rb mok nx k rk _ Hr W T) | apply (IH1 cs rec recb1 recb2 _ benv renv env s r rb mok nx k rk _ Hr W0 T)].
  - split_w W. apply Nat.eqb_eq in W. rewrite !rsplit_eq. apply (IH cs rec recb1 recb2 cenv benv _ _ s r rb mok nx k _ _ Hr W0).
    apply rsplit_typed; [rewrite <- W; eapply kind_denote_r; [exact W1 | exact T] | exact T].
Qed.
(** a function's theorem holds of any function that gives the same at every counters and arguments it takes (step 41) *)
Lemma callee_ok_ext : forall P id B gs (h D : ftype gs),
  (forall cvs vs M, length cvs = sn gs -> map kind_of vs = sk gs -> callf gs h cvs vs M = callf gs D cvs vs M) ->
  callee_ok P id B gs D -> callee_ok P id B gs h.
Proof.
  intros P id B gs h D E OK. unfold callee_ok in *. intros Hs cvs vs M Lc Lv Cf. specialize (OK Hs cvs vs M Lc Lv Cf).
  unfold calln, callm in *. rewrite (E cvs vs M Lc Lv). exact OK.
Qed.
Lemma denote_br_recr_ext : forall b cs rec ri recr1 recr2 cenv benv renv env s r rb mok nx k rk cbo,
  (forall cvs l s', length cvs = nx -> map kind_of l = k -> recr1 cvs l s' = recr2 cvs l s') ->
  wfbr (map (@projT1 _ _) cs, cbo) r rb mok nx k rk ri b = true -> rtyped renv rk ->
  denote_br cs rec ri recr1 cenv benv renv env s b = denote_br cs rec ri recr2 cenv benv renv env s b.
Proof.
  induction b as [x | ccs args | ccs args b IH | ccs args b IH | e b IH | c b IH | c b IH | x b IH | x b IH | c x y t IHt f IHf | c t IHt f IHf | c b0 IH0 b1 IH1 | sj x b IH];
    intros cs rec ri recr1 recr2 cenv benv renv env s r rb mok nx k rk cbo Hr W T; cbn [denote_br wfbr] in *.
  - reflexivity.
  - split_w W. apply Nat.eqb_eq in W4. apply kinds_eqb_eq in W3.
    apply Hr; [rewrite len_denote_cs; exact W4 | erewrite kinds_denote_es by eassumption; exact W3].
  - split_w W. apply Nat.eqb_eq in W5. apply kinds_eqb_eq in W4.
    rewrite (Hr _ _ s ltac:(rewrite len_denote_cs; exact W5) ltac:(erewrite kinds_denote_es by eassumption; exact W4)).
    apply relim_ext. apply (IH cs rec ri recr1 recr2 cenv benv renv _ s r rb mok nx k rk _ Hr W0 T).
  - split_w W. apply Nat.eqb_eq in W5. apply kinds_eqb_eq in W4.
    rewrite (Hr _ _ s ltac:(rewrite len_denote_cs; exact W5) ltac:(erewrite kinds_denote_es by eassumption; exact W4)).
    apply (IH cs rec ri recr1 recr2 cenv benv _ env s r rb mok nx k (ri :: rk) _ Hr W0). apply rtyped_cons; [exact T | reflexivity].
  - split_w W. apply (IH cs rec ri recr1 recr2 cenv benv renv _ s r rb mok nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec ri recr1 recr2 cenv _ renv env s r rb mok nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec ri recr1 recr2 _ benv renv env s r rb mok nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec ri recr1 recr2 cenv benv _ env s r rb mok nx k _ _ Hr W0).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - split_w W. rewrite !rmatch_eq. apply (IH cs rec ri recr1 recr2 cenv benv renv _ s r rb mok nx k rk _ Hr W0 T).
  - split_w W. rewrite (IHt cs rec ri recr1 recr2 cenv benv renv env s r rb mok nx k rk _ Hr W1 T),
                       (IHf cs rec ri recr1 recr2 cenv benv renv env s r rb mok nx k rk _ Hr W0 T). reflexivity.
  - split_w W. rewrite (IHt cs rec ri recr1 recr2 cenv benv renv env s r rb mok nx k rk _ Hr W1 T),
                       (IHf cs rec ri recr1 recr2 cenv benv renv env s r rb mok nx k rk _ Hr W0 T). reflexivity.
  - split_w W. destruct (nth c cenv O);
      [apply (IH0 cs rec ri recr1 recr2 cenv benv renv env s r rb mok nx k rk _ Hr W T) | apply (IH1 cs rec ri recr1 recr2 _ benv renv env s r rb mok nx k rk _ Hr W0 T)].
  - split_w W. apply Nat.eqb_eq in W. rewrite !rsplit_eq. apply (IH cs rec ri recr1 recr2 cenv benv _ _ s r rb mok nx k _ _ Hr W0).
    apply rsplit_typed; [rewrite <- W; eapply kind_denote_r; [exact W1 | exact T] | exact T].
Qed.
Lemma denote_pv_recp_ext : forall p cs rec recm recp1 recp2 cenv benv renv env s r rm mok rp nx k rk cbo,
  (forall cvs l s', length cvs = nx -> map kind_of l = k -> recp1 cvs l s' = recp2 cvs l s') ->
  wfpv (map (@projT1 _ _) cs, cbo) r rm mok rp nx k rk p = true -> rtyped renv rk ->
  denote_pv cs rec recm recp1 cenv benv renv env s p = denote_pv cs rec recm recp2 cenv benv renv env s p.
Proof.
  induction p as [e m | f ccs args m | ccs args m | e p IH | c p IH | c p IH | x p IH | x p IH | m p IH | c x y t IHt f IHf | c t IHt f IHf
                 | c p0 IH0 p1 IH1 | p IHp q IHq | sj x p IH | fi ccs args p IH];
    intros cs rec recm recp1 recp2 cenv benv renv env s r rm mok rp nx k rk cbo Hr W T; cbn [denote_pv wfpv] in *.
  - reflexivity.
  - reflexivity.
  - split_w W. apply Nat.eqb_eq in W5. apply kinds_eqb_eq in W4.
    apply Hr; [rewrite len_denote_cs; exact W5 | erewrite kinds_denote_es by eassumption; exact W4].
  - split_w W. apply (IH cs rec recm recp1 recp2 cenv benv renv _ s r rm mok rp nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec recm recp1 recp2 cenv _ renv env s r rm mok rp nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec recm recp1 recp2 _ benv renv env s r rm mok rp nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec recm recp1 recp2 cenv benv _ env s r rm mok rp nx k _ _ Hr W0).
    apply rtyped_cons; [exact T | eapply kind_denote_r; eauto].
  - split_w W. rewrite !rmatch_eq. apply (IH cs rec recm recp1 recp2 cenv benv renv _ s r rm mok rp nx k rk _ Hr W0 T).
  - split_w W. apply (IH cs rec recm recp1 recp2 cenv benv renv env _ r rm mok rp nx k rk _ Hr W0 T).
  - split_w W. rewrite (IHt cs rec recm recp1 recp2 cenv benv renv env s r rm mok rp nx k rk _ Hr W1 T),
                       (IHf cs rec recm recp1 recp2 cenv benv renv env s r rm mok rp nx k rk _ Hr W0 T). reflexivity.
  - split_w W. rewrite (IHt cs rec recm recp1 recp2 cenv benv renv env s r rm mok rp nx k rk _ Hr W1 T),
                       (IHf cs rec recm recp1 recp2 cenv benv renv env s r rm mok rp nx k rk _ Hr W0 T). reflexivity.
  - split_w W. destruct (nth c cenv O);
      [apply (IH0 cs rec recm recp1 recp2 cenv benv renv env s r rm mok rp nx k rk _ Hr W T) | apply (IH1 cs rec recm recp1 recp2 _ benv renv env s r rm mok rp nx k rk _ Hr W0 T)].
  - split_w W. rewrite (IHp cs rec recm recp1 recp2 cenv benv renv env s r rm mok rp nx k rk _ Hr W T).
    destruct (denote_pv cs rec recm recp2 cenv benv renv env s p) as [x2 s2].
    apply (IHq cs rec recm recp1 recp2 cenv benv renv _ s2 r rm mok rp nx k rk _ Hr W0 T).
  - split_w W. apply Nat.eqb_eq in W. rewrite !rsplit_eq. apply (IH cs rec recm recp1 recp2 cenv benv _ _ s r rm mok rp nx k _ _ Hr W0).
    apply rsplit_typed; [rewrite <- W; eapply kind_denote_r; [exact W1 | exact T] | exact T].
  - cbn [fst] in W; rewrite nth_sigs in W. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|]; simpl in W; [|reflexivity].
    split_w W. rewrite (IH cs rec recm recp1 recp2 cenv benv renv env s r rm mok rp nx k rk _ Hr W0 T). reflexivity.
Qed.

(** a record taken apart one level (step 43): the atoms of its number fields, and of each record field *)
Lemma avals_app_inv : forall rho Xs l1 l2, avals rho Xs = Some (l1 ++ l2) ->
  avals rho (firstn (length l1) Xs) = Some l1 /\ avals rho (skipn (length l1) Xs) = Some l2.
Proof.
  intros rho Xs. induction Xs as [|x Xs IH]; intros l1 l2 V.
  - destruct l1 as [|a l1]; simpl in *; [split; [reflexivity | exact V] | discriminate].
  - cbn [avals] in V. destruct (aval rho x) as [vx|] eqn:Ex; [|discriminate].
    destruct (avals rho Xs) as [vs|] eqn:Exs; [|discriminate].
    destruct l1 as [|a l1]; cbn [length firstn skipn app] in V |- *.
    + split; [reflexivity|]. cbn [avals]. rewrite Ex, Exs. exact V.
    + injection V as Ea Evs. subst a. destruct (IH l1 l2 (f_equal Some Evs)) as [H1 H2].
      cbn [avals]. rewrite Ex, H1. split; [reflexivity | exact H2].
Qed.
Lemma slices_ok : forall rho (L : list (sigT RT)) Xs,
  avals rho Xs = Some (concat (map (fun r => relim (RO (projT1 r)) (projT2 r) (fun l => l)) L)) ->
  Forall2 (fun Bs w => avals rho Bs = Some (vflat w)) (slices (map (fun r => rn (RO (projT1 r))) L) Xs) (map vrec L).
Proof.
  intros rho L. induction L as [|[j x] L IH]; intros Xs V; cbn [map slices concat] in *; [constructor|].
  cbn [projT1 projT2] in *. destruct (avals_app_inv rho Xs _ _ V) as [V1 V2]. rewrite (rl_len j x) in V1, V2.
  constructor; [exact V1 | apply IH; exact V2].
Qed.
Lemma fold_rn_map : forall (L : list (sigT RT)),
  fold_right (fun r a => (rn (RO (projT1 r)) + a)%nat) O L = fold_right (fun j a => (rn (RO j) + a)%nat) O (map (@projT1 _ _) L).
Proof. induction L as [|r L IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma len_concat_rn : forall (L : list (sigT RT)),
  length (concat (map (fun r => relim (RO (projT1 r)) (projT2 r) (fun l => l)) L)) = fold_right (fun r a => (rn (RO (projT1 r)) + a)%nat) O L.
Proof. induction L as [|[j y] L IH]; cbn [map concat fold_right projT1 projT2]; [reflexivity | rewrite app_length, rl_len, IH; reflexivity]. Qed.
Lemma split_atoms : forall rho As v sj, kind_of v = KRec sj -> avals rho As = Some (vflat v) ->
  avals rho (firstn (rnn sj) As) = Some (fst (rsplit_p v)) /\
  Forall2 (fun Bs w => avals rho Bs = Some (vflat w)) (rsl sj As) (snd (rsplit_p v)).
Proof.
  intros rho As v sj K V. destruct v as [n|b|ri x]; cbn [kind_of] in K; try discriminate. injection K as ->.
  unfold rsplit_p. cbn [rsplit]. rewrite (rs_nat sj x _ (fun l rs => (l, map vrec rs))). cbn [fst snd].
  cbn [vflat] in V. pose proof (rl_len sj x) as L0. pose proof (rs_kinds sj x) as Kj. rewrite <- (rs_flat sj x) in V, L0.
  set (R := RS sj _ x (fun l rs => (l, rs))) in *.
  assert (Ln : length (fst R) = rnn sj).
  { unfold rnn. rewrite app_length, len_concat_rn, fold_rn_map, Kj in L0. lia. }
  destruct (avals_app_inv rho As _ _ V) as [V1 V2]. rewrite Ln in V1, V2. split; [exact V1|].
  unfold rsl. rewrite <- Kj, map_map. apply slices_ok. exact V2.
Qed.
Lemma Forall_firstn_kq : forall {A : Type} (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. intros A P n l. revert n. induction l as [|a l IH]; intros [|n] F; cbn [firstn]; try constructor; inversion F; subst; auto. Qed.
Lemma Forall_skipn_kq : forall {A : Type} (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. intros A P n l. revert n. induction l as [|a l IH]; intros [|n] F; cbn [skipn]; auto; inversion F; subst; auto. Qed.
Lemma Forall_slices_kq : forall {A : Type} (P : A -> Prop) ws l, Forall P l -> Forall (Forall P) (slices ws l).
Proof.
  intros A P ws. induction ws as [|w ws IH]; intros l F; cbn [slices]; constructor;
    [apply Forall_firstn_kq; exact F | apply IH; apply Forall_skipn_kq; exact F].
Qed.
(** the one-level constructor's records: of the types asked, their numbers the records' *)
Lemma rec_vals : forall cs rec cenv benv renv denv M cbo r mok nx k rk es js,
  wfs (map (@projT1 _ _) cs, cbo) r mok nx k rk es = true -> rtyped renv rk -> kinds_eqb (kinds_s rk es) (map KRec js) = true ->
  flat_map vflat (denote_es cs rec cenv benv renv denv M es)
    = concat (map (fun r => relim (RO (projT1 r)) (projT2 r) (fun l => l)) (vrecs_t (denote_es cs rec cenv benv renv denv M es)))
  /\ map (@projT1 _ _) (vrecs_t (denote_es cs rec cenv benv renv denv M es)) = js.
Proof.
  intros cs rec cenv benv renv denv M cbo r mok nx k rk es. induction es as [|e es IH|b es IH|x es IH]; intros js W T K;
    destruct js as [|j js]; cbn [kinds_s map kinds_eqb kind_eqb andb] in K; try discriminate.
  - split; reflexivity.
  - cbn [wfs] in W. apply andb_true_iff in W as [Wx Wes]. apply andb_true_iff in K as [Kj Kes]. apply Nat.eqb_eq in Kj.
    pose proof (kind_denote_r cbo r mok nx k rk cs rec cenv benv renv denv M x Wx T) as Kx. rewrite Kj in Kx.
    destruct (IH js Wes T Kes) as [H1 H2]. unfold vrecs_t in *. cbn [denote_es flat_map].
    destruct (denote_r cs rec cenv benv renv denv M x) as [n|b|ri y]; cbn [kind_of] in Kx; try discriminate. injection Kx as <-.
    cbn [flat_map map concat vflat projT1 projT2 app]. split; [f_equal; exact H1 | f_equal; exact H2].
Qed.

(** counters below [wB] compare as their machine numbers do (step 30) *)
Lemma cmpn_ofn : forall c a b, match c with Ceq | Clt | Cle => true | _ => false end = true ->
  (Z.of_nat a < wB)%Z -> (Z.of_nat b < wB)%Z -> cmp_sem c (ofn a) (ofn b) = cmpn c a b.
Proof.
  intros c a b Hc Ha Hb. destruct c; try discriminate; cbn [cmp_sem cmpn].
  - destruct (Nat.eqb a b) eqn:E.
    + apply Nat.eqb_eq in E. subst b. apply Uint63.eqb_spec. reflexivity.
    + apply Nat.eqb_neq in E. destruct (PrimInt63.eqb (ofn a) (ofn b)) eqn:E2; [|reflexivity].
      apply Uint63.eqb_spec in E2. apply (f_equal to_Z) in E2. rewrite !ofn_phi in E2 by lia. lia.
  - destruct (Nat.ltb a b) eqn:E.
    + apply Nat.ltb_lt in E. apply Uint63.ltb_spec. rewrite !ofn_phi by lia. lia.
    + apply Nat.ltb_ge in E. destruct (PrimInt63.ltb (ofn a) (ofn b)) eqn:E2; [|reflexivity].
      apply Uint63.ltb_spec in E2. rewrite !ofn_phi in E2 by lia. lia.
  - destruct (Nat.leb a b) eqn:E.
    + apply Nat.leb_le in E. apply Uint63.leb_spec. rewrite !ofn_phi by lia. lia.
    + apply Nat.leb_gt in E. destruct (PrimInt63.leb (ofn a) (ofn b)) eqn:E2; [|reflexivity].
      apply Uint63.leb_spec in E2. rewrite !ofn_phi in E2 by lia. lia.
Qed.

(** the sum of two counters whose sum is below [wB]: the addition of their machine numbers (step 33) *)
Lemma ofn_add : forall a b, (Z.of_nat (a + b) < wB)%Z -> PrimInt63.add (ofn a) (ofn b) = ofn (a + b).
Proof. intros a b H. apply to_Z_inj. rewrite add_spec, !ofn_phi by lia. rewrite Z.mod_small; lia. Qed.

(** the predecessor of a counter below [wB]: a subtraction of 1, and 0 kept by a conditional move (step 30) *)
Lemma ofn_pred_sel : forall n, (Z.of_nat n < wB)%Z ->
  (if PrimInt63.eqb (ofn n) 0%uint63 then 0%uint63 else PrimInt63.sub (ofn n) 1%uint63) = ofn (Nat.pred n).
Proof. intros [|n] H; [reflexivity|]. rewrite ofn_S_ne0, ofn_pred by lia. reflexivity. Qed.

Section Sim.
Variables (P : prog) (f : fn) (gidf : nat -> ident) (g mv : ident).
Variables (cs : list callee) (r rm hp mok : bool) (nx : nat) (k : list kind) (j : nat).
Variables (rec : list nat -> list val -> mem -> i63) (recm : list nat -> list val -> mem -> mem) (cm : nat).
Variables (rx : bool) (recx : list nat -> list val -> mem -> i63).
(** the function's own bound, when its signature gives one (step 33; in its range, [Hbok] below); else its index's *)
Variable cbo : option Z.
Let cbj := match cbo with Some b => b | None => cbz j end.
(** the function's own weights (step 37: none, each counter below the bound; else their weighted sum), and its counters as the
    environment holds them below what the body binds *)
Variable cws : list poly.
Variable pv : list nat.
(** what the recursive call's counters (after the first, the predecessor) must satisfy *)
Let rfits (cvs : list nat) : Prop :=
  match cws with [] => Forall (fun c => (Z.of_nat c < cbj)%Z) cvs | vs => Forall (fun P => (pevalz P (map Z.of_nat (cm :: cvs)) < cbj)%Z) vs end.
(** the recursive call, where it is allowed, computes [rec] (or [recm], giving back a memory) on counters below the bound;
    the callees compute their meanings on counters below theirs; this function comes after its callees and is not one of
    the last 2^40 *)
Hypothesis Hrec : r = true -> forall cvs vs M, length cvs = nx -> map kind_of vs = k -> rfits cvs ->
  runk P g (ofn cm :: map ofn cvs ++ flat_map vflat vs) M (rec cvs vs M) M.
Hypothesis Hrecm : rm = true -> forall cvs vs M, length cvs = nx -> map kind_of vs = k -> rfits cvs ->
  runk P g (ofn cm :: map ofn cvs ++ flat_map vflat vs) M 0%uint63 (recm cvs vs M).
(** the recursive call of a number function that writes, where it is allowed ([rx]): the number [recx], with some end memory *)
Hypothesis Hrecx : rx = true -> forall cvs vs M, length cvs = nx -> map kind_of vs = k -> rfits cvs ->
  exists M', runk P g (ofn cm :: map ofn cvs ++ flat_map vflat vs) M (recx cvs vs M) M'.
Hypothesis Hrhp : r = true -> hp = true.
Hypothesis Hrxhp : rx = true -> hp = true.
Hypothesis Hrmhp : rm = true -> hp = true.
Hypothesis Hcs : callees_ok P gidf cs.
Hypothesis Hlen : (length cs <= j)%nat.
Hypothesis Hj : (Z.of_nat j < 1099511627776)%Z.
(** the slot block has room for the records the program's functions give back *)
Hypothesis Hslot : slot_room.
(** the function's own bound, when its signature gives one (step 33), in its range *)
Hypothesis Hbok : bok cbo = true.
(** a recursive body of a function with weights: each polynomial at its counters below the bound, the first counter the
    predecessor's successor *)
Hypothesis Hpv : hp = true -> cws <> [] -> exists rest0, pv = rev rest0 ++ [S cm] /\ length rest0 = nx /\
  Forall (fun P => (pevalz P (map Z.of_nat (S cm :: rest0)) < cbj)%Z) cws.
(** ... and without weights: its counters each below the bound *)
Hypothesis Hpv0 : hp = true -> cws = [] -> Forall (fun v => (Z.of_nat v < cbj)%Z) pv.

(** [wf]'s first argument (step 35): the callees' signatures, the own bound, the bounds of the counters in scope *)
Let sigsv (cbs : list cbe) : wfctx := (map (@projT1 _ _) cs, ((cbo, cws), cbs)).

Lemma cbj_pos : (0 < cbj)%Z.
Proof. unfold cbj. destruct cbo as [b|]; [unfold bok in Hbok; apply andb_true_iff in Hbok as [H1 _]; apply Z.ltb_lt in H1; lia | unfold cbz; lia]. Qed.
(** a bound left to the index has the budgets' room; a written one may be smaller (step 40), and it is the bound [wf] checks
    against *)
Lemma cbz_big : cbo = None -> (1152921504606846976 + 1048576 < cbj)%Z.
Proof. intros E. unfold cbj. rewrite E. unfold cbz; lia. Qed.
Lemma cbo_cases : unit -> (exists b, cbo = Some b) \/ cbo = None.
Proof. intros _. destruct cbo as [b|]; [left; exists b; reflexivity | right; reflexivity]. Qed.
Lemma ub_cbj : forall cbs b, cbo = Some b -> ub (sigsv cbs) = cbj.
Proof. intros cbs b E. unfold ub, sigsv, cbj. cbn [fst snd]. rewrite E. reflexivity. Qed.

Lemma cbz_small : (cbj + 1048576 < wB)%Z.
Proof.
  rewrite KQMAuto.wB_num. unfold cbj. destruct cbo as [b|]; [unfold bok in Hbok; apply andb_true_iff in Hbok as [_ H2]; apply Z.leb_le in H2; lia | unfold cbz; lia].
Qed.

(** the caller's counters are below [ub]: its own bound, or its index's at most (step 33) *)
Lemma ub_ge : forall cbs, (cbj <= ub (sigsv cbs))%Z.
Proof. intros cbs. unfold cbj, ub, sigsv. cbn [fst snd]. pose proof Hlen as HL. destruct cbo as [b|]; cbn [snd fst]. - lia. - rewrite length_map. unfold cbz. apply Nat2Z.inj_le in HL. apply Z.sub_le_mono_l. apply Z.mul_le_mono_nonneg_r; [discriminate | exact HL]. Qed.

Definition inv (cbs : list cbe) (rho : env) (cenvA benvA : list atom) (renvA : list (list atom)) (envA : list atom) (cenv : list nat)
  (benv : list bool) (renv : list val) (denv : list i63) (nxt : ident) : Prop :=
  env_ok rho envA denv /\ lt_all envA nxt /\ cenv_ok rho cenvA cenv /\ lt_all cenvA nxt /\ benv_ok rho benvA benv /\
  lt_all benvA nxt /\ cboundv cbj cbs pv cenv /\ Pos.lt mv nxt /\ (hp = true -> rho ! mv = Some (ofn cm) /\ (Z.of_nat cm < cbj)%Z) /\
  (renv_ok rho renvA renv /\ rlt_all renvA nxt).

Lemma inv_step : forall {cbs : list cbe} rho rho' cenvA benvA renvA envA cenv benv renv denv nxt n', inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt ->
  agree rho rho' nxt -> Pos.le nxt n' -> inv cbs rho' cenvA benvA renvA envA cenv benv renv denv n'.
Proof.
  intros cbs rho rho' cenvA benvA renvA envA cenv benv renv denv nxt n' (E & L & C & LC & Bv & LBv & B & Mv & H & RV & RL) A Le.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - eapply env_ok_agree; eauto.
  - eapply lt_all_mono; eauto.
  - eapply cenv_ok_agree; eauto.
  - eapply lt_all_mono; eauto.
  - eapply benv_ok_agree; eauto.
  - eapply lt_all_mono; eauto.
  - exact B.
  - lia.
  - intro Hh. destruct (H Hh) as [H1 H2]. split; [rewrite A by lia; exact H1 | exact H2].
  - eapply renv_ok_agree; eauto.
  - eapply rlt_all_mono; eauto.
Qed.

Lemma inv_let : forall {cbs : list cbe} rho cenvA benvA renvA envA cenv benv renv denv n1 a x, inv cbs rho cenvA benvA renvA envA cenv benv renv denv n1 ->
  aval rho a = Some x -> atom_lt a n1 -> inv cbs rho cenvA benvA renvA (a :: envA) cenv benv renv (x :: denv) n1.
Proof.
  intros cbs rho cenvA benvA renvA envA cenv benv renv denv n1 a x (E & L & C & LC & Bv & LBv & B & Mv & H & RV & RL) V La.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]; auto using env_ok_cons, lt_all_cons.
Qed.

Lemma inv_blet : forall {cbs : list cbe} rho cenvA benvA renvA envA cenv benv renv denv n1 a x, inv cbs rho cenvA benvA renvA envA cenv benv renv denv n1 ->
  aval rho a = Some (b2i x) -> atom_lt a n1 -> inv cbs rho cenvA (a :: benvA) renvA envA cenv (x :: benv) renv denv n1.
Proof.
  intros cbs rho cenvA benvA renvA envA cenv benv renv denv n1 a x (E & L & C & LC & Bv & LBv & B & Mv & H & RV & RL) V La.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]; auto using benv_ok_cons, lt_all_cons.
Qed.

Lemma inv_cpush : forall {cbs : list cbe} rho cenvA benvA renvA envA cenv benv renv denv nxt p o, inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt ->
  (Z.of_nat p < cbv cbj (fst o) <= 4611686018427387904)%Z -> (Z.of_nat p <= leval (snd o) pv)%Z ->
  inv (o :: cbs) (PTree.set nxt (ofn p) rho) (Avar nxt :: cenvA) benvA renvA envA (p :: cenv) benv renv denv (Pos.succ nxt).
Proof.
  intros cbs rho cenvA benvA renvA envA cenv benv renv denv nxt p o (E & L & C & LC & Bv & LBv & B & Mv & H & RV & RL) Bp Lp.
  assert (A : agree rho (PTree.set nxt (ofn p) rho) nxt) by (apply agree_set; lia).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - eapply env_ok_agree; eauto.
  - eapply lt_all_mono; eauto. lia.
  - apply cenv_ok_cons; [eapply cenv_ok_agree; eauto | simpl; apply PTree.gss].
  - apply lt_all_cons; [eapply lt_all_mono; eauto; lia | simpl; lia].
  - eapply benv_ok_agree; eauto.
  - eapply lt_all_mono; eauto. lia.
  - apply cboundv_cons; auto.
  - lia.
  - intro Hh. destruct (H Hh) as [H1 H2]. split; [rewrite A by lia; exact H1 | exact H2].
  - eapply renv_ok_agree; eauto.
  - eapply rlt_all_mono; eauto. lia.
Qed.

Lemma inv_clet : forall {cbs : list cbe} rho cenvA benvA renvA envA cenv benv renv denv n1 a x o, inv cbs rho cenvA benvA renvA envA cenv benv renv denv n1 ->
  aval rho a = Some (ofn x) -> atom_lt a n1 -> (Z.of_nat x < cbv cbj (fst o) <= 4611686018427387904)%Z -> (Z.of_nat x <= leval (snd o) pv)%Z ->
  inv (o :: cbs) rho (a :: cenvA) benvA renvA envA (x :: cenv) benv renv denv n1.
Proof.
  intros cbs rho cenvA benvA renvA envA cenv benv renv denv n1 a x o (E & L & C & LC & Bv & LBv & B & Mv & H & RV & RL) V La Bx Lx.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]; auto using cenv_ok_cons, lt_all_cons, cboundv_cons.
Qed.

(** a record bound by a let: its atoms join the record variables; a record taken apart: its fields join the numbers *)
Lemma inv_rlet : forall {cbs : list cbe} rho cenvA benvA renvA envA cenv benv renv denv n1 As w, inv cbs rho cenvA benvA renvA envA cenv benv renv denv n1 ->
  avals rho As = Some (vflat w) -> Forall (fun a => atom_lt a n1) As -> inv cbs rho cenvA benvA (As :: renvA) envA cenv benv (w :: renv) denv n1.
Proof.
  intros cbs rho cenvA benvA renvA envA cenv benv renv denv n1 As w (E & L & C & LC & Bv & LBv & B & Mv & H & RV & RL) V La.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]; auto; constructor; auto.
Qed.
(** a record taken apart one level (step 43): its record fields' atoms join the record variables *)
Lemma Forall2_rev_kq : forall {A B : Type} (R : A -> B -> Prop) l l', Forall2 R l l' -> Forall2 R (rev l) (rev l').
Proof. intros A B R l l' F. induction F as [|a b l l' H F IH]; cbn [rev]; [constructor | apply Forall2_app; [exact IH | constructor; [exact H | constructor]]]. Qed.
Lemma inv_rlets : forall {cbs : list cbe} rho cenvA benvA renvA envA cenv benv renv denv n1 Bss ws, inv cbs rho cenvA benvA renvA envA cenv benv renv denv n1 ->
  Forall2 (fun Bs w => avals rho Bs = Some (vflat w)) Bss ws -> Forall (Forall (fun a => atom_lt a n1)) Bss ->
  inv cbs rho cenvA benvA (rev Bss ++ renvA) envA cenv benv (rev ws ++ renv) denv n1.
Proof.
  intros cbs rho cenvA benvA renvA envA cenv benv renv denv n1 Bss ws (E & L & C & LC & Bv & LBv & B & Mv & H & RV & RL) V La.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]; auto.
  - unfold renv_ok in *. apply Forall2_app; [apply Forall2_rev_kq; exact V | exact RV].
  - unfold rlt_all in *. apply Forall_app; split; [apply Forall_rev; exact La | exact RL].
Qed.
Lemma inv_lets : forall {cbs : list cbe} rho cenvA benvA renvA envA cenv benv renv denv n1 As vs, inv cbs rho cenvA benvA renvA envA cenv benv renv denv n1 ->
  avals rho As = Some vs -> Forall (fun a => atom_lt a n1) As -> inv cbs rho cenvA benvA renvA (rev As ++ envA) cenv benv renv (rev vs ++ denv) n1.
Proof.
  intros cbs rho cenvA benvA renvA envA cenv benv renv denv n1 As vs (E & L & C & LC & Bv & LBv & B & Mv & H & RV & RL) V La.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]; auto.
  - apply env_ok_app; [apply avals_rev; exact V | exact E].
  - apply lt_all_app; [apply Forall_rev; exact La | exact L].
Qed.

(** the function's bound is a machine number with room (step 35: every bound pushed is at most 2^62 too) *)
Lemma cbj_le : (cbj <= 4611686018427387904)%Z.
Proof. unfold cbj. destruct cbo as [b|]; [unfold bok in Hbok; apply andb_true_iff in Hbok as [_ H2]; apply Z.leb_le in H2; lia | unfold cbz; lia]. Qed.

(** a counter [letc_ok] takes (step 9) is below the function's bound when its variables are *)
Lemma letc_cmax : forall c, (1152921504606846976 + 1048576 < cbj)%Z -> letc_ok c = true -> (cmax cbj c < cbj)%Z.
Proof.
  intros c Big L. unfold letc_ok in L. apply orb_true_iff in L as [L | L].
  - unfold flat in L. apply andb_true_iff in L as [L NA]. apply Nat.eqb_eq in L. pose proof (cmax_depth cbj c NA ltac:(lia)) as D. rewrite L in D. lia.
  - apply andb_true_iff in L as [F Sh]. unfold shallow in Sh. apply andb_true_iff in Sh as [Sh NA]. apply Z.leb_le in Sh.
    pose proof (cmax_free cbj c F NA). lia.
Qed.

(** a counter [letc_ok] takes whose variables are at the function's bound and whose largest value is below it (step 40): below
    the function's bound *)
Lemma fits_cbj : forall cbs c, letc_ok c && pvars cbs c = true -> (cmaxv (ub (sigsv cbs)) cbs c < ub (sigsv cbs))%Z -> (cmaxv cbj cbs c < cbj)%Z.
Proof.
  intros cbs c L U. destruct (cbo_cases tt) as [(b & Eo) | Eo].
  - rewrite (ub_cbj cbs b Eo) in U. exact U.
  - apply andb_true_iff in L as [E1 E2]. pose proof (cbz_big Eo) as Bg. rewrite (cmaxv_cmax cbj cbs c ltac:(lia) E2). exact (letc_cmax c Bg E1).
Qed.
(** a counter bound by a let (step 35): below the bound [lbnd] gives it, which has room *)
(** what a match on a counter pushes for the predecessor, and a let of a counter *)
Lemma match_push_ok1 : forall cbs c cenv p, cboundv cbj cbs pv cenv -> nth c cenv O = S p ->
  (Z.of_nat p < cbv cbj (fst (cpush_match (sigsv cbs) c)) <= 4611686018427387904)%Z.
Proof. intros cbs c cenv p Cb E. pose proof (proj1 Cb c) as H. rewrite E in H. unfold cpush_match. cbn [fst]. change (snd (snd (sigsv cbs))) with cbs. lia. Qed.
Lemma match_push_ok2 : forall cbs c cenv p, cboundv cbj cbs pv cenv -> nth c cenv O = S p ->
  (Z.of_nat p <= leval (snd (cpush_match (sigsv cbs) c)) pv)%Z.
Proof.
  intros cbs c cenv p Cb E. pose proof (linat_bound cbj cbs pv cenv c Cb) as H. rewrite E in H. unfold cpush_match. cbn [snd].
  change (snd (snd (sigsv cbs))) with cbs. rewrite leval_shift. lia.
Qed.
Lemma lbnd_bound : forall cbs c cenv benv renv denv M, letc_okv (sigsv cbs) c = true -> cboundv cbj cbs pv cenv ->
  (Z.of_nat (denote_c cs rec cenv benv renv denv M c) < cbv cbj (lbnd (sigsv cbs) c) <= 4611686018427387904)%Z.
Proof.
  intros cbs c cenv benv renv denv M L Cb. pose proof (cmaxv_bound cbj cbs pv c cs rec cenv benv renv denv M Cb) as D.
  pose proof (cmaxv_mono cbs c _ _ (ub_ge cbs)) as Mo. pose proof cbj_le.
  unfold letc_okv, lbnd in *. change (snd (snd (sigsv cbs))) with cbs in *.
  destruct (letc_ok c && pvars cbs c && (cmaxv (ub (sigsv cbs)) cbs c <? ub (sigsv cbs))%Z) eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E2. pose proof (fits_cbj cbs c E1 E2). cbn [cbv]. lia.
  - cbn [orb] in L. apply Z.leb_le in L. cbn [cbv]. lia.
Qed.
Lemma let_push_ok1 : forall cbs c cenv benv renv denv M, letc_okv (sigsv cbs) c = true -> cboundv cbj cbs pv cenv ->
  (Z.of_nat (denote_c cs rec cenv benv renv denv M c) < cbv cbj (fst (cpush_let (sigsv cbs) c)) <= 4611686018427387904)%Z.
Proof. intros. exact (lbnd_bound cbs c cenv benv renv denv M H H0). Qed.
Lemma let_push_ok2 : forall cbs c cenv benv renv denv M, cboundv cbj cbs pv cenv ->
  (Z.of_nat (denote_c cs rec cenv benv renv denv M c) <= leval (snd (cpush_let (sigsv cbs) c)) pv)%Z.
Proof. intros. exact (clinf_bound cbj cbs pv c cs rec cenv benv renv denv M H). Qed.
Lemma letc_okv_wb : forall cbs c, letc_okv (sigsv cbs) c = true -> (cmaxv cbj cbs c < wB)%Z.
Proof.
  intros cbs c L. pose proof (cmaxv_mono cbs c _ _ (ub_ge cbs)) as Mo. pose proof cbj_le. rewrite KQMAuto.wB_num.
  unfold letc_okv in L. change (snd (snd (sigsv cbs))) with cbs in L. apply orb_true_iff in L as [L | L].
  - apply andb_true_iff in L as [E1 E2]. apply Z.ltb_lt in E2. pose proof (fits_cbj cbs c E1 E2). lia.
  - apply Z.leb_le in L. lia.
Qed.

(** the recursive call's counters: no successor, no sum, their variables at the function's bound and their largest value below
    it (step 40) *)
Lemma flatv_cmax : forall cbs c, flat c && pvars cbs c = true -> (cmaxv (ub (sigsv cbs)) cbs c < ub (sigsv cbs))%Z -> (cmaxv cbj cbs c < cbj)%Z.
Proof.
  intros cbs c F U. destruct (cbo_cases tt) as [(b & Eo) | Eo].
  - rewrite (ub_cbj cbs b Eo) in U. exact U.
  - apply andb_true_iff in F as [F Pv]. pose proof (cbz_big Eo). rewrite (cmaxv_cmax cbj cbs c ltac:(lia) Pv).
    unfold flat in F. apply andb_true_iff in F as [F NA]. apply Nat.eqb_eq in F. pose proof (cmax_depth cbj c NA ltac:(lia)) as D. rewrite F in D. lia.
Qed.

(** the counters given to a callee are below its bound (step 33: what [wf] checks of them, through [cmaxv]) *)
Lemma cs_fit_each : forall cbs ccs cenv benv renv denv M B',
  all_c (fun c => (cmaxv (ub (sigsv cbs)) (snd (snd (sigsv cbs))) c <? B')%Z && (B' <=? 4611686018427387904)%Z) ccs = true ->
  cboundv cbj cbs pv cenv -> Forall (fun c => (Z.of_nat c < B')%Z) (denote_cs cs rec cenv benv renv denv M ccs).
Proof.
  intros cbs. induction ccs as [|c ccs IH]; intros cenv benv renv denv M B' F B; cbn [all_c denote_cs] in *; constructor.
  - apply andb_true_iff in F as [F1 F2]. apply andb_true_iff in F1 as [F1 _]. apply Z.ltb_lt in F1. change (snd (snd (sigsv cbs))) with cbs in F1.
    pose proof (cmaxv_bound cbj cbs pv c cs rec cenv benv renv denv M B) as D. pose proof (cmaxv_mono cbs c _ _ (ub_ge cbs)) as Mo. lia.
  - apply andb_true_iff in F as [F1 F2]. apply IH; auto.
Qed.
Lemma all_fit_each : forall cbs ccs B',
  all_c (fun c => (cmaxv (ub (sigsv cbs)) (snd (snd (sigsv cbs))) c <? B')%Z && (B' <=? 4611686018427387904)%Z) ccs = true ->
  all_c (fun c => (cmaxv cbj cbs c <? wB)%Z) ccs = true.
Proof.
  intros cbs. induction ccs as [|c ccs IH]; cbn [all_c]; auto. intros B' F. apply andb_true_iff in F as [F1 F2]. rewrite (IH B') by auto.
  apply andb_true_iff in F1 as [F1 F3]. apply Z.ltb_lt in F1. apply Z.leb_le in F3. change (snd (snd (sigsv cbs))) with cbs in F1.
  pose proof (cmaxv_mono cbs c _ _ (ub_ge cbs)).
  rewrite KQMAuto.wB_num. apply andb_true_iff; split; [apply Z.ltb_lt; lia | reflexivity].
Qed.
Lemma cs_le_cmaxv2 : forall cbs ccs cenv benv renv denv M, cboundv cbj cbs pv cenv ->
  Forall2 (fun v c => (Z.of_nat v <= cmaxv (ub (sigsv cbs)) cbs c)%Z) (denote_cs cs rec cenv benv renv denv M ccs) (lc ccs).
Proof.
  intros cbs. induction ccs as [|c ccs IH]; intros cenv benv renv denv M Cb; cbn [denote_cs lc]; constructor; [|apply IH; exact Cb].
  pose proof (cmaxv_bound cbj cbs pv c cs rec cenv benv renv denv M Cb). pose proof (cmaxv_mono cbs c _ _ (ub_ge cbs)). lia.
Qed.
Lemma cs_le_cmaxv : forall cbs ccs cenv benv renv denv M, cboundv cbj cbs pv cenv ->
  Forall2 (fun v z => (Z.of_nat v <= z)%Z) (denote_cs cs rec cenv benv renv denv M ccs) (map (cmaxv (ub (sigsv cbs)) cbs) (lc ccs)).
Proof.
  intros cbs. induction ccs as [|c ccs IH]; intros cenv benv renv denv M Cb; cbn [denote_cs lc map]; constructor; [|apply IH; exact Cb].
  pose proof (cmaxv_bound cbj cbs pv c cs rec cenv benv renv denv M Cb). pose proof (cmaxv_mono cbs c _ _ (ub_ge cbs)). lia.
Qed.
(** the counters given to a callee fit its bound (step 37: each, or their weighted sum) *)
Lemma cs_fit_bound : forall cbs ccs cenv benv renv denv M gs B', cfits_b gs B' (sigsv cbs) ccs = true ->
  cboundv cbj cbs pv cenv -> cfits gs B' (denote_cs cs rec cenv benv renv denv M ccs).
Proof.
  intros cbs ccs cenv benv renv denv M gs B' F Cb. unfold cfits_b, cfits in *. destruct (sv gs) as [|w ws].
  - eapply cs_fit_each; eauto.
  - apply andb_true_iff in F as [F _]. apply andb_true_iff in F as [F _]. change (snd (snd (sigsv cbs))) with cbs in F.
    rewrite forallb_forall in F. apply Forall_forall. intros P0 Hw. specialize (F P0 Hw). apply Z.ltb_lt in F.
    eapply Z.le_lt_trans; [| exact F]. apply pevalz_mono. apply Forall2_nth_le. apply cs_le_cmaxv2; exact Cb.
Qed.
Lemma all_fit_wb : forall cbs ccs gs B', cfits_b gs B' (sigsv cbs) ccs = true -> all_c (fun c => (cmaxv cbj cbs c <? wB)%Z) ccs = true.
Proof.
  intros cbs ccs gs B' F. unfold cfits_b in F. destruct (sv gs) as [|w ws].
  - eapply all_fit_each; eauto.
  - apply andb_true_iff in F as [F _]. apply andb_true_iff in F as [_ F]. change (snd (snd (sigsv cbs))) with cbs in F.
    rewrite all_c_forall in F |- *. rewrite forallb_forall in F |- *. intros c Hc. specialize (F c Hc). apply Z.ltb_lt in F.
    pose proof (cmaxv_mono cbs c _ _ (ub_ge cbs)). rewrite KQMAuto.wB_num. apply Z.ltb_lt. lia.
Qed.
(** the recursive call's counters without weights (step 37): a flat variable at the function's bound, or at most one of the
    function's counters -- each below the bound *)
Lemma rec0_fits : forall cbs c cenv benv renv denv M, hp = true -> cws = [] ->
  (flat c && pvars cbs c && (cmaxv (ub (sigsv cbs)) cbs c <? ub (sigsv cbs))%Z || lin1 (clinf cbs c)) = true -> cboundv cbj cbs pv cenv ->
  (Z.of_nat (denote_c cs rec cenv benv renv denv M c) < cbj)%Z.
Proof.
  intros cbs c cenv benv renv denv M Hh Hw F Cb. apply orb_true_iff in F as [F | F].
  - apply andb_true_iff in F as [F U]. apply Z.ltb_lt in U.
    pose proof (flatv_cmax cbs c F U). pose proof (cmaxv_bound cbj cbs pv c cs rec cenv benv renv denv M Cb). lia.
  - pose proof (clinf_bound cbj cbs pv c cs rec cenv benv renv denv M Cb). pose proof cbj_pos.
    pose proof (lin1_lt _ pv cbj F (Hpv0 Hh Hw) ltac:(lia)). lia.
Qed.
Lemma all_c_and_r : forall (p q : scnt -> bool) ccs, all_c (fun c => p c && q c) ccs = true -> all_c q ccs = true.
Proof. intros p0 q. induction ccs as [|c ccs IH]; cbn [all_c]; auto. intros F. apply andb_true_iff in F as [F1 F2]. apply andb_true_iff in F1 as [_ F1]. rewrite F1, IH by exact F2. reflexivity. Qed.
(** the recursive call's counters (step 37): flat and at the function's bound or at most one counter, or keeping the weighted sum
    from growing *)
Lemma rec_ok_wb : forall cbs ccs, rec_ok (sigsv cbs) ccs = true -> all_c (fun c => (cmaxv cbj cbs c <? wB)%Z) ccs = true.
Proof.
  intros cbs ccs R. unfold rec_ok in R. change (snd (fst (snd (sigsv cbs)))) with cws in R.
  destruct (list_cases_any cws) as [E | (w & ws & E)]; rewrite E in R; cbv beta iota in R;
    [apply all_c_and_r in R | apply andb_true_iff in R as [_ R]]; change (snd (snd (sigsv cbs))) with cbs in R;
    rewrite all_c_forall in R |- *; rewrite forallb_forall in R |- *; intros c Hc; specialize (R c Hc); apply Z.ltb_lt in R;
    pose proof (cmaxv_mono cbs c _ _ (ub_ge cbs)); rewrite KQMAuto.wB_num; apply Z.ltb_lt; lia.
Qed.
Lemma rec_ok_fits : forall cbs ccs cenv benv renv denv M, hp = true -> len_c ccs = nx -> rec_ok (sigsv cbs) ccs = true ->
  cboundv cbj cbs pv cenv -> rfits (denote_cs cs rec cenv benv renv denv M ccs).
Proof.
  intros cbs ccs cenv benv renv denv M Hh Lc R Cb. unfold rec_ok in R. change (snd (fst (snd (sigsv cbs)))) with cws in R. unfold rfits.
  destruct (list_cases_any cws) as [E | (w & ws & E)]; rewrite E in R |- *; cbv beta iota in R |- *.
  - change (snd (snd (sigsv cbs))) with cbs in R. clear Lc. revert R. induction ccs as [|c ccs IH]; cbn [all_c denote_cs]; intros R; constructor.
    + apply andb_true_iff in R as [R _]. apply andb_true_iff in R as [R _]. exact (rec0_fits cbs c cenv benv renv denv M Hh E R Cb).
    + apply andb_true_iff in R as [_ R]. exact (IH R).
  - apply andb_true_iff in R as [Pk _]. change (snd (snd (sigsv cbs))) with cbs in Pk.
    destruct (Hpv Hh ltac:(rewrite E; discriminate)) as (rest0 & Epv & Lr0 & Fv). rewrite E in Fv.
    pose proof (clinf_bounds cbj cbs pv ccs cs rec cenv benv renv denv M Cb) as F. rewrite Epv in F.
    rewrite forallb_forall in Pk. rewrite Forall_forall in Fv. apply Forall_forall. intros P0 Hw.
    specialize (Pk P0 Hw). specialize (Fv P0 Hw).
    pose proof (ppot_sound P0 cbs ccs _ rest0 cm Pk ltac:(lia) F) as Pt. lia.
Qed.
Lemma ub_le : forall cbs, (ub (sigsv cbs) <= 4611686018427387904)%Z.
Proof. intros cbs. unfold ub, sigsv. cbn [fst snd]. destruct cbo as [b|]; [unfold bok in Hbok; apply andb_true_iff in Hbok as [_ H2]; apply Z.leb_le in H2; exact H2 | unfold cbz; lia]. Qed.
(** the counters of a merged call's ends, as the merge's items ask them *)
Lemma rec_ok_items : forall cbs ccs, rec_ok (sigsv cbs) ccs = true ->
  all_c (fun c => (cmaxv (ub (sigsv cbs)) (snd (snd (sigsv cbs))) c <? 9223372036854775808)%Z) ccs = true.
Proof.
  intros cbs ccs R. unfold rec_ok in R. change (snd (fst (snd (sigsv cbs)))) with cws in R.
  destruct (list_cases_any cws) as [E | (w & ws & E)]; rewrite E in R; cbv beta iota in R.
  - exact (all_c_and_r _ _ ccs R).
  - apply andb_true_iff in R as [_ R]. exact R.
Qed.
(** a comparison of counters (step 30): each below [wB] *)
Lemma cmpc_wb : forall cbs x, (cmaxv (ub (sigsv cbs)) (snd (snd (sigsv cbs))) x <? 9223372036854775808)%Z = true -> (cmaxv cbj cbs x < wB)%Z.
Proof.
  intros cbs x S. apply Z.ltb_lt in S. change (snd (snd (sigsv cbs))) with cbs in S. pose proof (cmaxv_mono cbs x _ _ (ub_ge cbs)).
  rewrite KQMAuto.wB_num. lia.
Qed.

(** ** The slot block in KQL: cells read into fresh variables, the saved values written back, the fields written *)
Lemma cslot_go_ok : forall m j0 nxt K rho M v M',
  (forall rho' n' As, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') As ->
     avals rho' As = Some (map (fun i => KQ.KQRun.rd 63%uint63 (ofn i) M) (seq j0 m)) -> evalk P f rho' M (K As n') v M') ->
  evalk P f rho M (cslot_go j0 m nxt K) v M'.
Proof.
  induction m as [|m IH]; intros j0 nxt K rho M v M' HK; cbn [cslot_go].
  - apply HK; [apply agree_refl | lia | constructor | reflexivity].
  - eapply K_ld; [reflexivity | reflexivity |].
    apply IH. intros rho' n' As A Le LAs VAs. apply HK.
    + apply (agree_trans rho (PTree.set nxt (KQ.KQRun.rd 63%uint63 (ofn j0) M) rho) rho' nxt (Pos.succ nxt)); [apply agree_set; lia | exact A | lia].
    + lia.
    + constructor; [simpl; lia | exact LAs].
    + cbn [avals aval]. rewrite (A nxt) by lia. rewrite PTree.gss, VAs. reflexivity.
Qed.
Lemma cslot_ok : forall m nxt K rho M v M',
  (forall rho' n' As, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') As ->
     avals rho' As = Some (map (fun i => KQ.KQRun.rd 63%uint63 (ofn i) M) (seq 0 m)) -> evalk P f rho' M (K As n') v M') ->
  evalk P f rho M (cslot m nxt K) v M'.
Proof. intros m nxt K rho M v M' HK. apply cslot_go_ok. exact HK. Qed.

Lemma cback_ok : forall Os os j0 rho M kk v M', avals rho Os = Some os -> evalk P f rho (ubk j0 os M) kk v M' ->
  evalk P f rho M (cback j0 Os kk) v M'.
Proof.
  induction Os as [|o Os IH]; intros os j0 rho M kk v M' V E; cbn [cback].
  - simpl in V. injection V as <-. exact E.
  - cbn [avals] in V. destruct (aval rho o) as [vo|] eqn:Vo; [|discriminate]. destruct (avals rho Os) as [vs|] eqn:Vs; [|discriminate].
    injection V as <-. eapply K_st; [reflexivity | reflexivity | exact Vo |]. eapply IH; [exact Vs | exact E].
Qed.

Lemma cput_ok : forall As vs j0 rho M kk v M', avals rho As = Some vs -> evalk P f rho (wslot j0 vs M) kk v M' ->
  evalk P f rho M (cput j0 As kk) v M'.
Proof.
  induction As as [|a As IH]; intros vs j0 rho M kk v M' V E; cbn [cput].
  - simpl in V. injection V as <-. exact E.
  - cbn [avals] in V. destruct (aval rho a) as [va|] eqn:Va; [|discriminate]. destruct (avals rho As) as [ws|] eqn:Ws; [|discriminate].
    injection V as <-. apply (IH ws (S j0)); [exact Ws |]. eapply K_st; [reflexivity | reflexivity | exact Va | exact E].
Qed.

(** a call giving back a record: the caller's memory after it is the one before, the continuation gets the fields *)
Lemma ccallr_ok : forall h Xs xs m nxt K rho M w ws v M', runk P h xs M w (wslot O ws M) -> length ws = m ->
  (Z.of_nat m <= 1048576)%Z -> ((0 < m)%nat -> Z.of_nat m <= Sint63.to_Z (KQ.KQBound.kq_len 63%uint63))%Z ->
  avals rho Xs = Some xs -> Forall (fun a => atom_lt a nxt) Xs ->
  (forall rho' n' As, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') As -> avals rho' As = Some (w :: ws) ->
     evalk P f rho' M (K As n') v M') ->
  evalk P f rho M (ccallr h Xs m nxt K) v M'.
Proof.
  intros h Xs xs m nxt K rho M w ws v M' RK Lw Lm Lk VX LX HK. unfold ccallr.
  apply cslot_ok. intros rho1 n1 Os A1 Le1 LOs VOs.
  destruct RK as (fg & rho' & F & B & EV).
  eapply K_call; [exact F | rewrite (avals_agree rho rho1 nxt Xs A1 LX); exact VX | exact B | exact EV |].
  apply cslot_ok. intros rho2 n2 Fs A2 Le2 LFs VFs.
  assert (A12 : agree rho1 rho2 n1).
  { apply (agree_trans rho1 (PTree.set n1 w rho1) rho2 n1 (Pos.succ n1)); [apply agree_set; lia | exact A2 | lia]. }
  rewrite <- Lw in VFs. rewrite rd_wslot_seq in VFs.
  2: { simpl. lia. }
  2: { intros Hne. simpl. rewrite Lw. apply Lk. destruct ws as [|w0 ws0]; [congruence | simpl in Lw; lia]. }
  apply (cback_ok Os (map (fun i => KQ.KQRun.rd 63%uint63 (ofn i) M) (seq 0 m))).
  - rewrite (avals_agree rho1 rho2 n1 Os A12 LOs). exact VOs.
  - rewrite <- Lw. rewrite wback by (simpl; lia). apply HK.
    + apply (agree_trans rho rho1 rho2 nxt n1); [exact A1 | exact A12 | lia].
    + lia.
    + constructor; [simpl; lia | exact LFs].
    + cbn [avals aval]. rewrite (A2 n1) by lia. rewrite PTree.gss, VFs. reflexivity.
Qed.

(** a call of a function giving back a boolean (step 24): its KQL gives the boolean as 1 or 0 and keeps the memory *)
Lemma bcall_run : forall fi ccs args rk cbs cenv benv renv denv M gs h, nth_error cs fi = Some (existT _ gs h) ->
  wfb (sigsv cbs) r mok nx k rk (BCall fi ccs args) = true -> rtyped renv rk -> cboundv cbj cbs pv cenv ->
  runk P (gidf fi) (map ofn (denote_cs cs rec cenv benv renv denv M ccs) ++ flat_map vflat (denote_es cs rec cenv benv renv denv M args)) M
    (b2i (boolf gs (callf gs h (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M))) M.
Proof.
  intros fi ccs args rk cbs cenv benv renv denv M gs h E W Rt Cb.
  cbn [wfb] in W. unfold sigsv in W. cbn [fst] in W. rewrite nth_sigs, E in W. simpl in W.
  apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wsh].
  apply andb_true_iff in W as [W Wq]. apply andb_true_iff in W as [W Wsw]. apply andb_true_iff in W as [W Wr].
  apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [Wn Wk].
  assert (Hfi : (fi < j)%nat).
  { assert (fi < length cs)%nat by (apply nth_error_Some; rewrite E; discriminate). lia. }
  pose proof (Hcs fi) as Hc. unfold callee in *. rewrite E in Hc.
  destruct gs as [gx gk gm gr gw gq gb gv gp]. cbn [sq sr sw sn sk sm sb sv] in *.
  destruct gq as [[| |gri]|]; try discriminate Wq. destruct gr; [discriminate Wr|]. destruct gw; [discriminate Wsw|].
  assert (L1 : length (denote_cs cs rec cenv benv renv denv M ccs) = gx) by (rewrite len_denote_cs; apply Nat.eqb_eq; auto).
  assert (L2 : map kind_of (denote_es cs rec cenv benv renv denv M args) = gk)
    by (erewrite kinds_denote_es by eassumption; apply kinds_eqb_eq; auto).
  exact (Hc Hslot _ _ M L1 L2 (cs_fit_bound cbs ccs cenv benv renv denv M _ _ Wsh Cb)).
Qed.

Lemma cexp_all :
  (forall e cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wf (sigsv cbs) r mok nx k rk e = true -> inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
     (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' -> aval rho' a = Some (denote_e cs rec cenv benv renv denv M e) ->
        evalk P f rho' M (K a n') v M') ->
     evalk P f rho M (cexp gidf g mv e cenvA benvA renvA envA nxt K) v M')
  /\
  (forall es cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wfs (sigsv cbs) r mok nx k rk es = true -> inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
     (forall rho' n' As, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') As ->
        avals rho' As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M es)) -> evalk P f rho' M (K As n') v M') ->
     evalk P f rho M (cexps gidf g mv es cenvA benvA renvA envA nxt K) v M')
  /\
  (forall c cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wfc (sigsv cbs) r mok nx k rk c = true -> (cmaxv cbj cbs c < wB)%Z ->
     inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
     (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' ->
        aval rho' a = Some (ofn (denote_c cs rec cenv benv renv denv M c)) -> evalk P f rho' M (K a n') v M') ->
     evalk P f rho M (ccnt gidf g mv c cenvA benvA renvA envA nxt K) v M')
  /\
  (forall ccs cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wfcs (sigsv cbs) r mok nx k rk ccs = true ->
     all_c (fun c => (cmaxv cbj cbs c <? wB)%Z) ccs = true ->
     inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
     (forall rho' n' Cs, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') Cs ->
        avals rho' Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs)) -> evalk P f rho' M (K Cs n') v M') ->
     evalk P f rho M (ccnts gidf g mv ccs cenvA benvA renvA envA nxt K) v M')
  /\
  (forall b,
    (forall cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs, wfb (sigsv cbs) r mok nx k rk b = true ->
       inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
       (denote_b cs rec cenv benv renv denv M b = true -> forall rho' n', agree rho rho' nxt -> Pos.le nxt n' -> evalk P f rho' M (KT n') v M') ->
       (denote_b cs rec cenv benv renv denv M b = false -> forall rho' n', agree rho rho' nxt -> Pos.le nxt n' -> evalk P f rho' M (KF n') v M') ->
       evalk P f rho M (ccond gidf g mv b cenvA benvA renvA envA nxt KT KF) v M')
    /\
    (forall cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wfb (sigsv cbs) r mok nx k rk b = true ->
       inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
       (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' ->
          aval rho' a = Some (b2i (denote_b cs rec cenv benv renv denv M b)) -> evalk P f rho' M (K a n') v M') ->
       evalk P f rho M (cbval gidf g mv b cenvA benvA renvA envA nxt K) v M')
    /\
    (forall cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs, wfb (sigsv cbs) r mok nx k rk b = true ->
       inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
       atom_lt T nxt -> atom_lt F nxt -> aval rho T = Some tv -> aval rho F = Some fv ->
       (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' ->
          aval rho' a = Some (if denote_b cs rec cenv benv renv denv M b then tv else fv) -> evalk P f rho' M (K a n') v M') ->
       evalk P f rho M (csel gidf g mv b cenvA benvA renvA envA nxt T F K) v M'))
  /\
  (forall x cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wfr (sigsv cbs) r mok nx k rk x = true ->
     inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
     (forall rho' n' As, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') As ->
        avals rho' As = Some (vflat (denote_r cs rec cenv benv renv denv M x)) -> evalk P f rho' M (K As n') v M') ->
     evalk P f rho M (crec gidf g mv x cenvA benvA renvA envA nxt K) v M').
Proof.
  apply sexp_comb.
  - (* SVar *) intros i cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl.
    destruct Iv as (E & L & _). apply HK; [apply agree_refl | lia | apply L | apply E].
  - (* SInt *) intros n cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl.
    apply HK; [apply agree_refl | lia | exact Logic.I | reflexivity].
  - (* SOp *) intros o a IHa b IHb cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [Wa Wb].
    apply IHa with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHb with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_op.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SIf *) intros c a IHa b IHb t IHt e IHe cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    apply IHa with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHb with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    destruct (choice_ok t e) eqn:CH.
    { (* both numbers worked out, one taken by a conditional move *)
      apply IHt with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 T A3 Le3 LT VT.
      apply IHe with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho4 n4 F A4 Le4 LF VF.
      assert (LA2 : atom_lt A n2) by (eapply atom_lt_mono; [exact LA | lia]).
      assert (LA3 : atom_lt A n3) by (eapply atom_lt_mono; [exact LA | lia]).
      assert (LB3 : atom_lt B n3) by (eapply atom_lt_mono; [exact LB | lia]).
      eapply K_sel.
      - rewrite (aval_agree rho3 rho4 n3 A A4 LA3), (aval_agree rho2 rho3 n2 A A3 LA2), (aval_agree rho1 rho2 n1 A A2 LA).
        exact VA.
      - rewrite (aval_agree rho3 rho4 n3 B A4 LB3), (aval_agree rho2 rho3 n2 B A3 LB). exact VB.
      - rewrite (aval_agree rho3 rho4 n3 T A4 LT). exact VT.
      - exact VF.
      - apply HK.
        + apply (agree_set2 rho rho3 rho4 n4 _ nxt n3); [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia | exact A4 | lia | lia].
        + lia.
        + simpl. lia.
        + simpl. rewrite PTree.gss.
          destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)); reflexivity. }
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)) eqn:C.
      * apply IHt with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 a3 A3 Le3 L3 V3.
        apply HK; [| lia | exact L3 | exact V3].
        eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia.
      * apply IHe with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
        { eapply inv_step; [exact I2 | apply agree_refl | afterle]. }
        intros rho3 n3 a3 A3 Le3 L3 V3.
        apply HK; [| lia_a | exact L3 | exact V3].
        eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); [eauto | eauto | eapply agree_mono; [exact A3 | afterle] | lia | lia].
  - (* SLet *) intros e1 IH1 e2 IH2 cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [W1 W2].
    apply IH1 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH2 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denote_e cs rec cenv benv renv denv M e1 :: denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_let; auto. eapply inv_step; eauto.
    + intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | exact V2].
  - (* SRd *) intros h IHh i IHi cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    apply IHh with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 H A1 Le1 LH VH.
    apply IHi with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 J A2 Le2 LJ VJ.
    eapply K_ld.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SRec *) intros ccs IHc args IHs cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfl].
    apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply IHc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply IHs with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    destruct (Hrec Wr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). exact (rec_ok_fits cbs ccs cenv benv renv denv M (Hrhp Wr) (proj1 (Nat.eqb_eq _ _) Wn) Wfl Cb). }
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1 & _). destruct (H1 (Hrhp Wr)) as [Rm _].
    eapply K_call; eauto.
    + simpl. rewrite (A2 mv Mv1), Rm.
      rewrite (avals_app rho2 Cs As _ _ (eq_trans (avals_agree rho1 rho2 n1 Cs A2 LCs) VCs) VAs). reflexivity.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SCall *) intros fi ccs IHc args IHs cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    unfold sigsv in W. cbn [fst] in W; rewrite nth_sigs in W. pose proof (Hcs fi) as Hc.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    assert (Hfi : (fi < j)%nat).
    { assert (fi < length cs)%nat by (apply nth_error_Some; rewrite E; discriminate). lia. }
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wsh].
    apply andb_true_iff in W as [W Wsw].
    apply andb_true_iff in W as [W Wr]. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [Wn Wk].
    assert (Hc2 : forall cvs0 vs0 M0, length cvs0 = sn gs -> map kind_of vs0 = sk gs -> cfits gs (fbound gs fi) cvs0 ->
              runk P (gidf fi) (map ofn cvs0 ++ flat_map vflat vs0) M0 (calln gs h cvs0 vs0 M0) (if sr gs then callm gs h cvs0 vs0 M0 else M0)).
    { intros cvs0 vs0 M0 L1 L2 L3. pose proof (Hc Hslot cvs0 vs0 M0 L1 L2 L3) as H0. destruct (sw gs); [discriminate Wsw|]. unfold isq in Wsw. destruct (sq gs); [discriminate Wsw | exact H0]. }
    apply IHc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply IHs with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    destruct (Hc2 (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). exact (cs_fit_bound cbs ccs cenv benv renv denv M _ _ Wsh Cb). }
    destruct (sr gs); [discriminate Wr|].
    eapply K_call; eauto.
    + apply avals_app; [rewrite (avals_agree rho1 rho2 n1 Cs A2 LCs); exact VCs | exact VAs].
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SMatch *) intros c e0 IH0 e1 IH1 cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
    destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl.
      apply IH0 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (cenv := p :: cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto.
      * apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
      * intros rho3 n3 a3 A3 Le3 L3 V3. apply HK; [ | lia_a | exact L3 | exact V3 ].
        refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
  - (* SIfB *) intros b IHb t IHt e IHe cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wb Wt]. destruct IHb as [IHc [IHv IHs]].
    destruct (choice_ok t e) eqn:CH.
    + (* both numbers worked out, one taken by conditional moves on the parts of the boolean *)
      apply IHt with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 T A1 Le1 LT VT.
      apply IHe with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 F A2 Le2 LF VF.
      assert (A12 : agree rho rho2 nxt) by (eapply (agree_trans rho rho1 rho2 nxt n1); eauto).
      eapply IHs; [exact Wb | eapply inv_step; [exact Iv | exact A12 | lia] | exact Rt | eapply atom_lt_mono; [exact LT | lia] | exact LF
                  | rewrite (aval_agree rho1 rho2 n1); eauto | exact VF | ].
      intros rho3 n3 a A3 Le3 La Va. apply HK; [eapply (agree_trans rho rho2 rho3 nxt n2); [exact A12 | exact A3 | lia] | lia | exact La | ].
      rewrite Va. destruct (denote_b cs rec cenv benv renv denv M b); reflexivity.
    + (* jumps *)
      apply IHc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        apply IHt with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
        intros rho2 n2 a2 A2 Le2 L2 V2.
        apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | rewrite Hb; exact V2].
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        apply IHe with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
        intros rho2 n2 a2 A2 Le2 L2 V2.
        apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | rewrite Hb; exact V2].
  - (* SLetB *) intros b IHb e IHe cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [Wb We]. destruct IHb as [_ [IHv _]].
    apply IHv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHe with (cenv := cenv) (benv := denote_b cs rec cenv benv renv denv M b :: benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_blet; auto. eapply inv_step; eauto.
    + intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | exact V2].
  - (* SRd32 *) intros h IHh i IHi cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    apply IHh with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 H A1 Le1 LH VH.
    apply IHi with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 J A2 Le2 LJ VJ.
    eapply K_ld32.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SLetC *) intros c IHc e IHe cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wc Wl].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    eapply IHc; [exact Wc | eapply letc_okv_wb; exact Wl | exact Iv | exact Rt | ].
    intros rho1 n1 A A1 Le1 LA VA.
    eapply IHe with (cbs := cpush_let (sigsv cbs) c :: cbs); [exact We | apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto] | exact Rt | ].
    intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - (* SFld *) intros i j0 cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cexp denote_e].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RV & RL).
    apply HK; [apply agree_refl | lia | apply Forall_nth_atom, rlt_nth; exact RL | ].
    cbn [denote_e]. rewrite rmatch_eq. apply avals_nth. apply renv_nth. exact RV.
  - (* SLetR *) intros x IHx e IHe cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cexp denote_e wf] in *.
    apply andb_true_iff in W as [Wx We].
    eapply IHx; [exact Wx | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
    eapply IHe; [exact We | apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs] | apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto] |].
    intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - (* SMatchR *) intros x IHx e IHe cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cexp denote_e wf] in *.
    apply andb_true_iff in W as [Wx We].
    eapply IHx; [exact Wx | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
    eapply IHe; [exact We | apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs] | exact Rt |].
    intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | ].
    cbn [denote_e]. rewrite rmatch_eq. exact Va.
  - (* SHwf *) intros o args IHa cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cexp denote_e wf] in *.
    apply andb_true_iff in W as [W Wa]. apply andb_true_iff in W as [Wn Wk]. apply Nat.eqb_eq in Wn.
    destruct (flat_nums cs rec cenv benv renv denv M args Wk) as [F1 F2].
    eapply IHa; [exact Wa | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs. rewrite F1 in VAs.
    eapply K_hwf; [rewrite (avals_length rho1 As _ VAs), F2; exact Wn | exact VAs |].
    apply HK; [eapply agree_set1; [exact A1 | lia] | lia | simpl; lia | simpl; rewrite PTree.gss; reflexivity].
  - (* SSize *) intros h IHh cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cexp denote_e wf] in *.
    apply andb_true_iff in W as [_ Wh].
    apply IHh with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 H A1 Le1 LH VH.
    eapply K_size; [exact VH |].
    apply HK; [eapply agree_set1; [exact A1 | lia] | lia | simpl; lia | simpl; rewrite PTree.gss; reflexivity].
  - (* SRd8 *) intros h IHh i IHi cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    apply IHh with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 H A1 Le1 LH VH.
    apply IHi with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 J A2 Le2 LJ VJ.
    eapply K_ld8.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SSplitR *) intros sj x IHx e IHe cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cexp denote_e wf] in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    eapply IHx; [exact Wx | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M x) = KRec sj) by (rewrite <- Ex; eapply kind_denote_r; eauto).
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    eapply IHe; [exact We | apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs] | apply rsplit_typed; [exact Kx | exact Rt] |].
    intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | ].
    cbn [denote_e]. rewrite rsplit_eq. exact Va.
  - (* SNil *) intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl. apply HK; [apply agree_refl | lia | constructor | reflexivity].
  - (* SCons *) intros e IHe es IHes cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [We Wes].
    apply IHe with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHes with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 As A2 Le2 LAs VAs. apply HK.
    + eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
    + lia.
    + constructor; auto. eapply atom_lt_mono; eauto.
    + simpl. rewrite (aval_agree rho1 rho2 n1), VA, VAs; auto.
  - (* SConsB *) intros b IHb es IHes cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [Wb Wes].
    apply (proj1 (proj2 IHb)) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHes with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 As A2 Le2 LAs VAs. apply HK.
    + eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
    + lia.
    + constructor; auto. eapply atom_lt_mono; eauto.
    + simpl. rewrite (aval_agree rho1 rho2 n1), VA, VAs; auto.
  - (* SConsR *) intros x IHx es IHes cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cexps denote_es wfs] in *.
    apply andb_true_iff in W as [Wx Wes].
    assert (Wx' : wfr (sigsv cbs) r mok nx k rk x = true) by exact Wx.
    eapply IHx; [exact Wx' | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
    eapply IHes; [exact Wes | eapply inv_step; eauto | exact Rt |].
    intros rho2 n2 Bs A2 Le2 LBs VBs. apply HK.
    + eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
    + lia.
    + apply Forall_app; split; auto. eapply Forall_atom_mono; eauto.
    + cbn [flat_map]. apply avals_app; auto. rewrite (avals_agree rho1 rho2 n1 As A2 LAs). exact VAs.
  - (* CVar *) intros i cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W D Iv Rt HK. simpl.
    destruct Iv as (_ & _ & C & LC & _). apply HK; [apply agree_refl | lia | apply LC | apply C].
  - (* CO *) intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W D Iv Rt HK. simpl.
    apply HK; [apply agree_refl | lia | exact Logic.I | exact (f_equal Some (eq_sym ofn_0))].
  - (* CS *) intros c IH cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W D Iv Rt HK. simpl in *.
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    pose proof (cmaxv_bound cbj cbs pv c cs rec cenv benv renv denv M Cb) as Dc.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { lia. }
    intros rho1 n1 A A1 Le1 LA VA.
    eapply K_op; [exact VA | reflexivity | ].
    apply HK.
    + eapply (agree_set1 rho rho1); eauto; lia.
    + lia.
    + simpl. lia.
    + simpl. rewrite PTree.gss. simpl binop_sem. rewrite ofn_succ by lia. reflexivity.
  - (* CNat *) intros e IH cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W D Iv Rt HK. simpl in *.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    eapply K_sel; [exact VA | reflexivity | reflexivity | exact VA | ].
    eapply K_sel; [reflexivity | simpl; rewrite PTree.gss; reflexivity | reflexivity | simpl; rewrite PTree.gss; reflexivity | ].
    apply HK.
    + apply agree_set1; [apply agree_set1; [exact A1 | lia] | lia].
    + lia.
    + simpl. lia.
    + simpl. rewrite PTree.gss. rewrite ofn_kq_nat. reflexivity.
  - (* CPred *) intros c IH cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W D Iv Rt HK. simpl in *.
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    pose proof (cmaxv_bound cbj cbs pv c cs rec cenv benv renv denv M Cb) as Dc.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho1 n1 A A1 Le1 LA VA.
    eapply K_op; [exact VA | reflexivity | ].
    eapply K_sel; [rewrite (aval_agree rho1 _ n1); [exact VA | apply agree_set; lia | exact LA]
                  | reflexivity | reflexivity | simpl; rewrite PTree.gss; reflexivity | ].
    apply HK.
    + apply agree_set1; [apply agree_set1; [exact A1 | lia] | lia].
    + lia.
    + simpl. lia.
    + cbn [aval]. rewrite PTree.gss. cbn [cmp_sem binop_sem]. f_equal. apply ofn_pred_sel. lia.
  - (* CAdd *) intros a IHa b IHb cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W D Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [Wa Wb].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _). pose proof cbj_pos as Bg.
    pose proof (cmaxv_bound cbj cbs pv a cs rec cenv benv renv denv M Cb) as Da. pose proof (cmaxv_bound cbj cbs pv b cs rec cenv benv renv denv M Cb) as Db.
    pose proof (cmaxv_nonneg cbj cbs a) as Na. pose proof (cmaxv_nonneg cbj cbs b) as Nb.
    apply IHa with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { lia. }
    intros rho1 n1 A A1 Le1 LA VA.
    apply IHb with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { lia. } { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_op.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. simpl binop_sem. rewrite ofn_add by lia. reflexivity.
  - (* CNil *) intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Sh Iv Rt HK. simpl.
    apply HK; [apply agree_refl | lia | constructor | reflexivity].
  - (* CCons *) intros c IHc ccs IHs cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Sh Iv Rt HK. simpl in *.
    apply andb_true_iff in W as [Wc Ws]. apply andb_true_iff in Sh as [Sh1 Sh2].
    apply IHc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { apply Z.ltb_lt in Sh1. exact Sh1. }
    intros rho1 n1 A A1 Le1 LA VA.
    apply IHs with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 As A2 Le2 LAs VAs. apply HK.
    + eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
    + lia.
    + constructor; auto. eapply atom_lt_mono; eauto.
    + simpl. rewrite (aval_agree rho1 rho2 n1), VA, VAs; auto.
  - (* BCmp *) intros c x IHx y IHy. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHy with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      eapply K_if.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M x) (denote_e cs rec cenv benv renv denv M y)) eqn:C.
        -- apply HT; [exact C | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
        -- apply HF; [exact C | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia_a].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHy with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      eapply K_sel.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * reflexivity.
      * reflexivity.
      * apply HK.
        -- eapply (agree_set2 rho rho1 rho2); eauto; lia.
        -- lia.
        -- simpl. lia.
        -- cbn [aval]. rewrite PTree.gss. reflexivity.
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHy with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      assert (A12 : agree rho rho2 nxt) by (eapply (agree_trans rho rho1 rho2 nxt n1); eauto).
      eapply K_sel.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * rewrite (aval_agree rho rho2 nxt); eauto.
      * rewrite (aval_agree rho rho2 nxt); eauto.
      * apply HK.
        -- eapply (agree_set2 rho rho1 rho2); eauto; lia.
        -- lia.
        -- simpl. lia.
        -- cbn [aval]. rewrite PTree.gss. reflexivity.
  - (* BVar *) intros i. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond].
      pose proof Iv as (_ & _ & _ & _ & Bv & _).
      eapply K_if; [apply Bv | reflexivity | ]. rewrite b2i_eq0.
      destruct (nth i benv false) eqn:Eb; simpl.
      * apply HT; [exact Eb | apply agree_refl | lia_a].
      * apply HF; [exact Eb | apply agree_refl | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval].
      pose proof Iv as (_ & _ & _ & _ & Bv & LBv & _).
      apply HK; [apply agree_refl | lia | apply LBv | apply Bv].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel].
      pose proof Iv as (_ & _ & _ & _ & Bv & _).
      eapply K_sel; [apply Bv | reflexivity | exact VF | exact VT | ].
      apply HK.
      * apply agree_set1; [apply agree_refl | lia].
      * lia.
      * simpl. lia.
      * cbn [aval denote_b]. rewrite PTree.gss, b2i_eq0. destruct (nth i benv false); reflexivity.
  - (* BTrue *) split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond].
      apply HT; [reflexivity | apply agree_refl | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval].
      apply HK; [apply agree_refl | lia | exact Logic.I | reflexivity].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel].
      apply HK; [apply agree_refl | lia | exact LT | exact VT].
  - (* BFalse *) split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond].
      apply HF; [reflexivity | apply agree_refl | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval].
      apply HK; [apply agree_refl | lia | exact Logic.I | reflexivity].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel].
      apply HK; [apply agree_refl | lia | exact LF | exact VF].
  - (* BAnd *) intros x IHx y IHy. destruct IHx as [IHxc [IHxv IHxs]]. destruct IHy as [IHyc [IHyv IHys]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHxc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      * intros Hx rho1 n1 A1 Le1. cbv beta.
        apply IHyc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
        -- intros Hy rho2 n2 A2 Le2.
           apply HT; [simpl; rewrite Hx, Hy; reflexivity | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
        -- intros Hy rho2 n2 A2 Le2.
           apply HF; [simpl; rewrite Hx, Hy; reflexivity | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
      * intros Hx rho1 n1 A1 Le1. apply HF; [simpl; rewrite Hx; reflexivity | exact A1 | exact Le1].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHxv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHyv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      eapply K_op.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * apply HK.
        -- eapply (agree_set2 rho rho1 rho2); eauto; lia.
        -- lia.
        -- simpl. lia.
        -- cbn [aval]. rewrite PTree.gss, b2i_land. reflexivity.
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      eapply IHys; [exact Wy | exact Iv | exact Rt | exact LT | exact LF | exact VT | exact VF | ].
      intros rho1 n1 V A1 Le1 LV VV.
      eapply IHxs; [exact Wx | eapply inv_step; eauto | exact Rt | exact LV | eapply atom_lt_mono; [exact LF | lia]
                   | exact VV | rewrite (aval_agree rho rho1 nxt); eauto | ].
      intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | ].
      rewrite Va. simpl. destruct (denote_b cs rec cenv benv renv denv M x), (denote_b cs rec cenv benv renv denv M y); reflexivity.
  - (* BOr *) intros x IHx y IHy. destruct IHx as [IHxc [IHxv IHxs]]. destruct IHy as [IHyc [IHyv IHys]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHxc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      * intros Hx rho1 n1 A1 Le1. apply HT; [simpl; rewrite Hx; reflexivity | exact A1 | exact Le1].
      * intros Hx rho1 n1 A1 Le1. cbv beta.
        apply IHyc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
        -- intros Hy rho2 n2 A2 Le2.
           apply HT; [simpl; rewrite Hx, Hy; reflexivity | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
        -- intros Hy rho2 n2 A2 Le2.
           apply HF; [simpl; rewrite Hx, Hy; reflexivity | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHxv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHyv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      eapply K_op.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * apply HK.
        -- eapply (agree_set2 rho rho1 rho2); eauto; lia.
        -- lia.
        -- simpl. lia.
        -- cbn [aval]. rewrite PTree.gss, b2i_lor. reflexivity.
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      eapply IHys; [exact Wy | exact Iv | exact Rt | exact LT | exact LF | exact VT | exact VF | ].
      intros rho1 n1 V A1 Le1 LV VV.
      eapply IHxs; [exact Wx | eapply inv_step; eauto | exact Rt | eapply atom_lt_mono; [exact LT | lia] | exact LV
                   | rewrite (aval_agree rho rho1 nxt); eauto | exact VV | ].
      intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | ].
      rewrite Va. simpl. destruct (denote_b cs rec cenv benv renv denv M x), (denote_b cs rec cenv benv renv denv M y); reflexivity.
  - (* BNot *) intros x IHx. destruct IHx as [IHxc [IHxv IHxs]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W.
      apply IHxc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      * intros Hx. apply HF. simpl. rewrite Hx. reflexivity.
      * intros Hx. apply HT. simpl. rewrite Hx. reflexivity.
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W.
      apply IHxv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      eapply K_op; [exact VA | reflexivity | ].
      apply HK.
      * apply agree_set1; [exact A1 | lia].
      * lia.
      * simpl. lia.
      * cbn [aval]. rewrite PTree.gss, b2i_lxor. reflexivity.
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W.
      eapply IHxs; [exact W | exact Iv | exact Rt | exact LF | exact LT | exact VF | exact VT | ].
      intros rho1 n1 a A1 Le1 La Va. apply HK; [exact A1 | exact Le1 | exact La | ].
      rewrite Va. simpl. destruct (denote_b cs rec cenv benv renv denv M x); reflexivity.
  - (* BIfCmp *) intros c a IHa b IHb x IHx y IHy. destruct IHx as [IHxc [IHxv IHxs]]. destruct IHy as [IHyc [IHyv IHys]].
    split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wa Wb].
      apply IHa with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHb with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      eapply K_if.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)) eqn:C.
        -- apply IHxc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
           ++ intros Hx rho3 n3 A3 Le3.
              apply HT; [cbn [denote_b]; rewrite C; exact Hx | eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia | lia].
           ++ intros Hx rho3 n3 A3 Le3.
              apply HF; [cbn [denote_b]; rewrite C; exact Hx | eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia | lia].
        -- apply IHyc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
           { eapply inv_step; [exact I2 | apply agree_refl | afterle]. }
           ++ intros Hy rho3 n3 A3 Le3. apply HT; [cbn [denote_b]; rewrite C; exact Hy | | lia_a].
              eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); [eauto | eauto | eapply agree_mono; [exact A3 | afterle] | lia | lia].
           ++ intros Hy rho3 n3 A3 Le3. apply HF; [cbn [denote_b]; rewrite C; exact Hy | | lia_a].
              eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); [eauto | eauto | eapply agree_mono; [exact A3 | afterle] | lia | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wa Wb].
      apply IHa with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHb with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      eapply K_if.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)) eqn:C.
        -- apply IHxv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 a3 A3 Le3 L3 V3.
           apply HK; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia | lia | exact L3 | cbn [denote_b]; rewrite C; exact V3].
        -- apply IHyv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; [exact I2 | apply agree_refl | afterle]. }
           intros rho3 n3 a3 A3 Le3 L3 V3.
           apply HK; [ | lia_a | exact L3 | cbn [denote_b]; rewrite C; exact V3].
           eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); [eauto | eauto | eapply agree_mono; [exact A3 | afterle] | lia | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wa Wb].
      apply IHa with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHb with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      assert (A12 : agree rho rho2 nxt) by (eapply (agree_trans rho rho1 rho2 nxt n1); eauto).
      assert (VT2 : aval rho2 T = Some tv) by (rewrite (aval_agree rho rho2 nxt); eauto).
      assert (VF2 : aval rho2 F = Some fv) by (rewrite (aval_agree rho rho2 nxt); eauto).
      assert (LT2 : atom_lt T n2) by (eapply atom_lt_mono; [exact LT | lia]).
      assert (LF2 : atom_lt F n2) by (eapply atom_lt_mono; [exact LF | lia]).
      eapply K_if.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)) eqn:C.
        -- eapply IHxs; [exact Wx | exact I2 | exact Rt | exact LT2 | exact LF2 | exact VT2 | exact VF2 | ].
           intros rho3 n3 a3 A3 Le3 L3 V3.
           apply HK; [eapply (agree_trans rho rho2 rho3 nxt n2); eauto; lia | lia | exact L3 | cbn [denote_b]; rewrite C; exact V3].
        -- eapply IHys; [exact Wy | eapply inv_step; [exact I2 | apply agree_refl | afterle] | exact Rt
                        | eapply atom_lt_mono; [exact LT2 | afterle] | eapply atom_lt_mono; [exact LF2 | afterle] | exact VT2 | exact VF2 | ].
           intros rho3 n3 a3 A3 Le3 L3 V3.
           apply HK; [ | lia_a | exact L3 | cbn [denote_b]; rewrite C; exact V3].
           eapply (agree_trans rho rho2 rho3 nxt n2); [exact A12 | eapply agree_mono; [exact A3 | afterle] | lia].
  - (* BMatchCnt *) intros c x0 IH0 x1 IH1. destruct IH0 as [IH0c [IH0v IH0s]]. destruct IH1 as [IH1c [IH1v IH1s]].
    split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [W0 W1].
      pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
      destruct (nth c cenv O) as [|p] eqn:Ec.
      * assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
        eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl.
        apply IH0c with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
        -- intros Hx. apply HT. cbn [denote_b]. rewrite Ec. exact Hx.
        -- intros Hx. apply HF. cbn [denote_b]. rewrite Ec. exact Hx.
      * assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
        assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
        pose proof KQMAuto.wB_num as Sm.
        eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
        eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
        apply IH1c with (cenv := p :: cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto.
        -- apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
        -- intros Hx rho3 n3 A3 Le3. apply HT; [cbn [denote_b]; rewrite Ec; exact Hx | | lia_a].
           refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
        -- intros Hx rho3 n3 A3 Le3. apply HF; [cbn [denote_b]; rewrite Ec; exact Hx | | lia_a].
           refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [W0 W1].
      pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
      destruct (nth c cenv O) as [|p] eqn:Ec.
      * assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
        eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl.
        apply IH0v with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 a3 A3 Le3 L3 V3.
        apply HK; [exact A3 | exact Le3 | exact L3 | cbn [denote_b]; rewrite Ec; exact V3].
      * assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
        assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
        pose proof KQMAuto.wB_num as Sm.
        eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
        eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
        apply IH1v with (cenv := p :: cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto.
        -- apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
        -- intros rho3 n3 a3 A3 Le3 L3 V3. apply HK; [ | lia_a | exact L3 | cbn [denote_b]; rewrite Ec; exact V3].
           refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W.
      apply andb_true_iff in W as [W0 W1].
      pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
      destruct (nth c cenv O) as [|p] eqn:Ec.
      * assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
        eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl.
        eapply IH0s; [exact W0 | exact Iv | exact Rt | exact LT | exact LF | exact VT | exact VF | ].
        intros rho3 n3 a3 A3 Le3 L3 V3. apply HK; [exact A3 | exact Le3 | exact L3 | cbn [denote_b]; rewrite Ec; exact V3].
      * assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
        assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
        pose proof KQMAuto.wB_num as Sm.
        eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
        eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
        eapply IH1s with (cenv := p :: cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); [exact W1 | apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto] | exact Rt
                     | eapply atom_lt_mono; [exact LT | afterle] | eapply atom_lt_mono; [exact LF | afterle]
                     | rewrite (aval_agree rho _ nxt); [exact VT | apply agree_set; afterle | exact LT]
                     | rewrite (aval_agree rho _ nxt); [exact VF | apply agree_set; afterle | exact LF] | ].
        intros rho3 n3 a3 A3 Le3 L3 V3. apply HK; [ | lia_a | exact L3 | cbn [denote_b]; rewrite Ec; exact V3].
        refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
  - (* BCall *) intros fi ccs IHc args IHs. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond].
      pose proof W as W0. cbn [wfb] in W0. unfold sigsv in W0. cbn [fst] in W0; rewrite nth_sigs in W0.
      unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W0; [|discriminate W0].
      apply andb_true_iff in W0 as [W0 Ws]. apply andb_true_iff in W0 as [W0 Wc]. apply andb_true_iff in W0 as [W0 Wsh].
      pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
      pose proof (bcall_run fi ccs args rk cbs cenv benv renv denv M gs h E W Rt Cb) as RK.
      apply IHc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
      intros rho1 n1 Cs A1 Le1 LCs VCs.
      pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
      apply IHs with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      intros rho2 n2 As A2 Le2 LAs VAs.
      destruct RK as (fg & rho' & Fd & Bd & EVd). eapply K_call; [exact Fd | | exact Bd | exact EVd | ].
      * apply avals_app; [rewrite (avals_agree rho1 rho2 n1 Cs A2 LCs); exact VCs | exact VAs].
      * eapply K_if; [cbn [aval]; apply PTree.gss | reflexivity | ]. rewrite b2i_eq0.
        destruct (boolf gs (callf gs h (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M)) eqn:Eb; simpl.
        -- apply HT; [cbn [denote_b]; unfold callee; rewrite E; exact Eb | eapply (agree_set2 rho rho1 rho2); eauto; lia | lia_a].
        -- apply HF; [cbn [denote_b]; unfold callee; rewrite E; exact Eb | eapply (agree_set2 rho rho1 rho2); eauto; lia | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval].
      pose proof W as W0. cbn [wfb] in W0. unfold sigsv in W0. cbn [fst] in W0; rewrite nth_sigs in W0.
      unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W0; [|discriminate W0].
      apply andb_true_iff in W0 as [W0 Ws]. apply andb_true_iff in W0 as [W0 Wc]. apply andb_true_iff in W0 as [W0 Wsh].
      pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
      pose proof (bcall_run fi ccs args rk cbs cenv benv renv denv M gs h E W Rt Cb) as RK.
      apply IHc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
      intros rho1 n1 Cs A1 Le1 LCs VCs.
      pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
      apply IHs with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      intros rho2 n2 As A2 Le2 LAs VAs.
      destruct RK as (fg & rho' & Fd & Bd & EVd). eapply K_call; [exact Fd | | exact Bd | exact EVd | ].
      * apply avals_app; [rewrite (avals_agree rho1 rho2 n1 Cs A2 LCs); exact VCs | exact VAs].
      * apply HK.
        -- eapply (agree_set2 rho rho1 rho2); eauto; lia.
        -- lia.
        -- simpl. lia.
        -- cbn [aval denote_b]. unfold callee. rewrite PTree.gss, E. reflexivity.
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel].
      pose proof W as W0. cbn [wfb] in W0. unfold sigsv in W0. cbn [fst] in W0; rewrite nth_sigs in W0.
      unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W0; [|discriminate W0].
      apply andb_true_iff in W0 as [W0 Ws]. apply andb_true_iff in W0 as [W0 Wc]. apply andb_true_iff in W0 as [W0 Wsh].
      pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
      pose proof (bcall_run fi ccs args rk cbs cenv benv renv denv M gs h E W Rt Cb) as RK.
      apply IHc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
      intros rho1 n1 Cs A1 Le1 LCs VCs.
      pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
      apply IHs with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      intros rho2 n2 As A2 Le2 LAs VAs.
      assert (Ag : agree rho (PTree.set n2 (b2i (boolf gs (callf gs h (denote_cs cs rec cenv benv renv denv M ccs)
                                 (denote_es cs rec cenv benv renv denv M args) M))) rho2) nxt)
        by (eapply (agree_set2 rho rho1 rho2); eauto; lia).
      destruct RK as (fg & rho' & Fd & Bd & EVd). eapply K_call; [exact Fd | | exact Bd | exact EVd | ].
      * apply avals_app; [rewrite (avals_agree rho1 rho2 n1 Cs A2 LCs); exact VCs | exact VAs].
      * eapply K_sel; [cbn [aval]; apply PTree.gss | reflexivity | rewrite (aval_agree rho _ nxt F Ag LF); exact VF
                      | rewrite (aval_agree rho _ nxt T Ag LT); exact VT | ].
        apply HK.
        -- apply agree_set1; [exact Ag | lia].
        -- lia.
        -- simpl. lia.
        -- cbn [aval denote_b]. unfold callee. rewrite PTree.gss, b2i_eq0, E.
           destruct (boolf gs (callf gs h (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M)); reflexivity.
  - (* BCmpC *) intros c x IHx y IHy.
    assert (BC : forall cenv benv renv denv M rk cbs, wfb (sigsv cbs) r mok nx k rk (BCmpC c x y) = true -> cboundv cbj cbs pv cenv ->
      cmp_sem c (ofn (denote_c cs rec cenv benv renv denv M x)) (ofn (denote_c cs rec cenv benv renv denv M y))
      = denote_b cs rec cenv benv renv denv M (BCmpC c x y)).
    { intros cenv benv renv denv M rk cbs W Cb. cbn [wfb denote_b] in *.
      apply andb_true_iff in W as [W _]. apply andb_true_iff in W as [W _]. apply andb_true_iff in W as [W Sy].
      apply andb_true_iff in W as [Hc Sx]. apply cmpc_wb in Sx. apply cmpc_wb in Sy.
      pose proof (cmaxv_bound cbj cbs pv x cs rec cenv benv renv denv M Cb). pose proof (cmaxv_bound cbj cbs pv y cs rec cenv benv renv denv M Cb).
      apply cmpn_ofn; [exact Hc | lia | lia]. }
    split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF.
      pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _). pose proof (BC cenv benv renv denv M rk cbs W Cb) as E.
      cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Sy].
      apply andb_true_iff in W as [_ Sx]. apply cmpc_wb in Sx. apply cmpc_wb in Sy.
      apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHy with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      eapply K_if.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * rewrite E. destruct (denote_b cs rec cenv benv renv denv M (BCmpC c x y)) eqn:C.
        -- apply HT; [first [exact C | reflexivity] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
        -- apply HF; [first [exact C | reflexivity] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia_a].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK.
      pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _). pose proof (BC cenv benv renv denv M rk cbs W Cb) as E.
      cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Sy].
      apply andb_true_iff in W as [_ Sx]. apply cmpc_wb in Sx. apply cmpc_wb in Sy.
      apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHy with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      eapply K_sel.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * reflexivity.
      * reflexivity.
      * apply HK.
        -- eapply (agree_set2 rho rho1 rho2); eauto; lia.
        -- lia.
        -- simpl. lia.
        -- cbn [aval]. rewrite PTree.gss, E. reflexivity.
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK.
      pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _). pose proof (BC cenv benv renv denv M rk cbs W Cb) as E.
      cbn [csel]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Sy].
      apply andb_true_iff in W as [_ Sx]. apply cmpc_wb in Sx. apply cmpc_wb in Sy.
      apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHy with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      assert (A12 : agree rho rho2 nxt) by (eapply (agree_trans rho rho1 rho2 nxt n1); eauto).
      eapply K_sel.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * rewrite (aval_agree rho rho2 nxt); eauto.
      * rewrite (aval_agree rho rho2 nxt); eauto.
      * apply HK.
        -- eapply (agree_set2 rho rho1 rho2); eauto; lia.
        -- lia.
        -- simpl. lia.
        -- cbn [aval]. rewrite PTree.gss, E. reflexivity.
  - (* BxIfB *) intros b IHb x IHx y IHy. destruct IHb as [IHbc [IHbv IHbs]]. destruct IHx as [IHxc [IHxv IHxs]].
    destruct IHy as [IHyc [IHyv IHys]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [Wb Wx].
      apply IHbc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        apply IHxc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
        -- intros Hx rho2 n2 A2 Le2. apply HT; [cbn [denote_b]; rewrite Hb; exact Hx | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
        -- intros Hx rho2 n2 A2 Le2. apply HF; [cbn [denote_b]; rewrite Hb; exact Hx | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        apply IHyc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
        -- intros Hy rho2 n2 A2 Le2. apply HT; [cbn [denote_b]; rewrite Hb; exact Hy | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
        -- intros Hy rho2 n2 A2 Le2. apply HF; [cbn [denote_b]; rewrite Hb; exact Hy | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [Wb Wx].
      apply IHbc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        apply IHxv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
        intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | cbn [denote_b]; rewrite Hb; exact V2].
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        apply IHyv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
        intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | cbn [denote_b]; rewrite Hb; exact V2].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [Wb Wx].
      apply IHbc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        eapply IHxs; [exact Wx | eapply inv_step; eauto | exact Rt | eapply atom_lt_mono; [exact LT | lia] | eapply atom_lt_mono; [exact LF | lia] | rewrite (aval_agree rho rho1 nxt); eauto | rewrite (aval_agree rho rho1 nxt); eauto | ].
        intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | cbn [denote_b]; rewrite Hb; exact V2].
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        eapply IHys; [exact Wy | eapply inv_step; eauto | exact Rt | eapply atom_lt_mono; [exact LT | lia] | eapply atom_lt_mono; [exact LF | lia] | rewrite (aval_agree rho rho1 nxt); eauto | rewrite (aval_agree rho rho1 nxt); eauto | ].
        intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | cbn [denote_b]; rewrite Hb; exact V2].
  - (* BxLet *) intros e IHe x IHx. destruct IHx as [IHxc [IHxv IHxs]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W. apply andb_true_iff in W as [We Wx].
      apply IHe with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      eapply IHxc; [exact Wx | apply inv_let; [eapply inv_step; eauto | exact VA | exact LA] | exact Rt | | ].
      * intros Hx rho2 n2 A2 Le2. apply HT; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
      * intros Hx rho2 n2 A2 Le2. apply HF; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W. apply andb_true_iff in W as [We Wx].
      apply IHe with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      eapply IHxv; [exact Wx | apply inv_let; [eapply inv_step; eauto | exact VA | exact LA] | exact Rt | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W. apply andb_true_iff in W as [We Wx].
      apply IHe with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      eapply IHxs; [exact Wx | apply inv_let; [eapply inv_step; eauto | exact VA | exact LA] | exact Rt | eapply atom_lt_mono; [exact LT | lia] | eapply atom_lt_mono; [exact LF | lia] | rewrite (aval_agree rho rho1 nxt); eauto | rewrite (aval_agree rho rho1 nxt); eauto | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
  - (* BxLetB *) intros b IHb x IHx. destruct IHx as [IHxc [IHxv IHxs]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W. apply andb_true_iff in W as [Wb Wx].
      destruct IHb as [_ [IHbv _]]. apply IHbv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      eapply IHxc; [exact Wx | apply inv_blet; [eapply inv_step; eauto | exact VA | exact LA] | exact Rt | | ].
      * intros Hx rho2 n2 A2 Le2. apply HT; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
      * intros Hx rho2 n2 A2 Le2. apply HF; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W. apply andb_true_iff in W as [Wb Wx].
      destruct IHb as [_ [IHbv _]]. apply IHbv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      eapply IHxv; [exact Wx | apply inv_blet; [eapply inv_step; eauto | exact VA | exact LA] | exact Rt | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W. apply andb_true_iff in W as [Wb Wx].
      destruct IHb as [_ [IHbv _]]. apply IHbv with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
      eapply IHxs; [exact Wx | apply inv_blet; [eapply inv_step; eauto | exact VA | exact LA] | exact Rt | eapply atom_lt_mono; [exact LT | lia] | eapply atom_lt_mono; [exact LF | lia] | rewrite (aval_agree rho rho1 nxt); eauto | rewrite (aval_agree rho rho1 nxt); eauto | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
  - (* BxLetC *) intros c IHc x IHx. destruct IHx as [IHxc [IHxv IHxs]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc Wl].
      pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
      eapply IHc; [exact Wc | eapply letc_okv_wb; exact Wl | exact Iv | exact Rt | ]. intros rho1 n1 A A1 Le1 LA VA.
      eapply IHxc with (cbs := cpush_let (sigsv cbs) c :: cbs); [exact Wx | apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto] | exact Rt | | ].
      * intros Hx rho2 n2 A2 Le2. apply HT; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
      * intros Hx rho2 n2 A2 Le2. apply HF; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc Wl].
      pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
      eapply IHc; [exact Wc | eapply letc_okv_wb; exact Wl | exact Iv | exact Rt | ]. intros rho1 n1 A A1 Le1 LA VA.
      eapply IHxv with (cbs := cpush_let (sigsv cbs) c :: cbs); [exact Wx | apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto] | exact Rt | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc Wl].
      pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
      eapply IHc; [exact Wc | eapply letc_okv_wb; exact Wl | exact Iv | exact Rt | ]. intros rho1 n1 A A1 Le1 LA VA.
      eapply IHxs with (cbs := cpush_let (sigsv cbs) c :: cbs); [exact Wx | apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto] | exact Rt | eapply atom_lt_mono; [exact LT | lia] | eapply atom_lt_mono; [exact LF | lia] | rewrite (aval_agree rho rho1 nxt); eauto | rewrite (aval_agree rho rho1 nxt); eauto | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
  - (* BxLetR *) intros y IHy x IHx. destruct IHx as [IHxc [IHxv IHxs]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W. apply andb_true_iff in W as [Wy Wx].
      eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
      eapply IHxc; [exact Wx | apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs] | apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto] | | ].
      * intros Hx rho2 n2 A2 Le2. apply HT; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
      * intros Hx rho2 n2 A2 Le2. apply HF; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W. apply andb_true_iff in W as [Wy Wx].
      eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
      eapply IHxv; [exact Wx | apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs] | apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto] | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W. apply andb_true_iff in W as [Wy Wx].
      eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
      eapply IHxs; [exact Wx | apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs] | apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto] | eapply atom_lt_mono; [exact LT | lia] | eapply atom_lt_mono; [exact LF | lia] | rewrite (aval_agree rho rho1 nxt); eauto | rewrite (aval_agree rho rho1 nxt); eauto | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
  - (* BxMatchR *) intros y IHy x IHx. destruct IHx as [IHxc [IHxv IHxs]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W. apply andb_true_iff in W as [Wy Wx].
      eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
      eapply IHxc; [exact Wx | apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs] | exact Rt | | ].
      * intros Hx rho2 n2 A2 Le2. apply HT; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
      * intros Hx rho2 n2 A2 Le2. apply HF; [first [exact Hx | cbn [denote_b]; rewrite rmatch_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W. apply andb_true_iff in W as [Wy Wx].
      eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
      eapply IHxv; [exact Wx | apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs] | exact Rt | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W. apply andb_true_iff in W as [Wy Wx].
      eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
      eapply IHxs; [exact Wx | apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs] | exact Rt | eapply atom_lt_mono; [exact LT | lia] | eapply atom_lt_mono; [exact LF | lia] | rewrite (aval_agree rho rho1 nxt); eauto | rewrite (aval_agree rho rho1 nxt); eauto | ].
      intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2 | cbn [denote_b]; rewrite rmatch_eq; exact V2]].
  - (* BxSplitR *) intros sj y IHy x IHx. destruct IHx as [IHxc [IHxv IHxs]]. split; [| split].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt KT KF rho M v M' rk cbs W Iv Rt HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Ey Wy]. apply Nat.eqb_eq in Ey.
      eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
      assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M y) = KRec sj) by (rewrite <- Ey; eapply kind_denote_r; eauto).
      destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
      eapply IHxc; [exact Wx | apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs] | apply rsplit_typed; [exact Kx | exact Rt] | | ].
      * intros Hx rho2 n2 A2 Le2. apply HT; [first [exact Hx | cbn [denote_b]; rewrite rsplit_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
      * intros Hx rho2 n2 A2 Le2. apply HF; [first [exact Hx | cbn [denote_b]; rewrite rsplit_eq; exact Hx] | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Ey Wy]. apply Nat.eqb_eq in Ey.
      eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
      assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M y) = KRec sj) by (rewrite <- Ey; eapply kind_denote_r; eauto).
      destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
      eapply IHxv; [exact Wx | apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs] | apply rsplit_typed; [exact Kx | exact Rt] | ].
      intros rho2 n2 a2 A2 Le2 L2 V2'. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2' | cbn [denote_b]; rewrite rsplit_eq; exact V2']].
    + intros cenvA benvA renvA envA cenv benv renv denv nxt T F tv fv K rho M v M' rk cbs W Iv Rt LT LF VT VF HK. cbn [csel]. cbn [wfb] in W.
      apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Ey Wy]. apply Nat.eqb_eq in Ey.
      eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
      assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M y) = KRec sj) by (rewrite <- Ey; eapply kind_denote_r; eauto).
      destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
      eapply IHxs; [exact Wx | apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs] | apply rsplit_typed; [exact Kx | exact Rt] | eapply atom_lt_mono; [exact LT | lia] | eapply atom_lt_mono; [exact LF | lia] | rewrite (aval_agree rho rho1 nxt); eauto | rewrite (aval_agree rho rho1 nxt); eauto | ].
      intros rho2 n2 a2 A2 Le2 L2 V2'. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | first [exact V2' | cbn [denote_b]; rewrite rsplit_eq; exact V2']].
  - (* RVar *) intros i cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RV & RL).
    apply HK; [apply agree_refl | lia | apply rlt_nth; exact RL | apply renv_nth; exact RV].
  - (* RMk *) intros ri es IHes cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [W Wes]. apply andb_true_iff in W as [W Fn]. apply andb_true_iff in W as [Cn La]. apply Nat.eqb_eq in La.
    eapply IHes; [exact Wes | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
    apply HK; auto. cbn [vflat]. destruct (flat_nums cs rec cenv benv renv denv M es Fn) as [F1 F2].
    rewrite rl_mk_c; [ | lia | apply canon_s_ok; exact Cn]. rewrite <- F1. exact VAs.
  - (* RCall *) intros ri fi ccs IHc args IHs cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK.
    destruct (wfr_call_inv _ _ _ _ _ _ _ _ _ _ W) as (gs & E & Wn & Wk & Wm & Wr & Wsw & Q & R1 & R2 & Wsh & Wc & Ws).
    cbn [denote_r] in HK. unfold sigsv in E. cbn [fst] in E; rewrite nth_sigs in E. pose proof (Hcs fi) as Hc.
    unfold callee in *. destruct (nth_error cs fi) as [[gs' h]|] eqn:Ef; simpl in E; [|discriminate]. injection E as <-.
    assert (Hfi : (fi < j)%nat).
    { assert (fi < length cs)%nat by (apply nth_error_Some; rewrite Ef; discriminate). lia. }
    cbn [crec].
    destruct gs' as [gx gk gm gr gw gq gb gv gp]. cbn [sq sr sw sn sk sm sb sv] in Q, Wr, Wsw, Wn, Wk, Wm. subst gq gr gw.
    apply IHc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply IHs with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    set (cvs := denote_cs cs rec cenv benv renv denv M ccs) in *. set (vs := denote_es cs rec cenv benv renv denv M args) in *.
    set (X := callf (mksig9 gx gk gm false false (Some (KRec ri)) gb gv gp) h cvs vs M) in *.
    assert (LX : length (relim (RO ri) X (fun l => l)) = rn (RO ri)) by apply rl_len.
    assert (RK : runk P (gidf fi) (map ofn cvs ++ flat_map vflat vs) M (hd 0%uint63 (relim (RO ri) X (fun l => l)))
                   (wslot O (tl (relim (RO ri) X (fun l => l))) M)).
    { apply (Hc Hslot cvs vs M).
      - unfold cvs. rewrite len_denote_cs. apply Nat.eqb_eq; exact Wn.
      - unfold vs. erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; exact Wk.
      - destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). exact (cs_fit_bound cbs ccs cenv benv renv denv M _ _ Wsh Cb). }
    apply (ccallr_ok (gidf fi) (Cs ++ As) (map ofn cvs ++ flat_map vflat vs) (Nat.pred (rn (RO ri))) n2 K rho2 M
             (hd 0%uint63 (relim (RO ri) X (fun l => l))) (tl (relim (RO ri) X (fun l => l)))).
    + exact RK.
    + destruct (relim (RO ri) X (fun l => l)); simpl in *; lia.
    + lia.
    + intros Hp. pose proof (Hslot ri ltac:(lia)) as Hs. lia.
    + apply avals_app; [rewrite (avals_agree rho1 rho2 n1 Cs A2 LCs); exact VCs | exact VAs].
    + apply Forall_app; split; [eapply Forall_atom_mono; [exact LCs | lia] | exact LAs].
    + intros rho' n' Fs A' Le' LF VF. apply HK.
      * apply (agree_3 rho rho1 rho2 rho' nxt n1 n2); auto; lia.
      * lia.
      * exact LF.
      * rewrite VF. cbn [vrec_of vflat sq].
        destruct (relim (RO ri) X (fun l => l)) as [|w0 ws0]; [simpl in LX; lia | reflexivity].
  - (* RW64 *) intros ri o a IHa b IHb cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK.
    cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [W Wa]. apply andb_true_iff in W as [W Rb].
    apply andb_true_iff in W as [W Ra]. apply andb_true_iff in W as [Tg Ri]. apply Nat.eqb_eq in Ri.
    apply IHa with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    apply IHb with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 Bs A2 Le2 LBs VBs.
    rewrite <- (avals_agree rho1 rho2 n1 As A2 LAs) in VAs. rewrite !rmatch_eq in HK.
    eapply K_w64 with (ra := u64_of_l (vflat (denote_r cs rec cenv benv renv denv M a)))
                      (rb := u64_of_l (vflat (denote_r cs rec cenv benv renv denv M b))).
    + apply Pos.succ_discr.
    + exact (avals_nth rho2 As _ 0%nat VAs).
    + exact (avals_nth rho2 As _ 1%nat VAs).
    + exact (avals_nth rho2 Bs _ 0%nat VBs).
    + exact (avals_nth rho2 Bs _ 1%nat VBs).
    + apply HK.
      * eapply agree_set1; [eapply (agree_set2 rho rho1 rho2); eauto; lia | lia].
      * lia.
      * constructor; [simpl; lia | constructor; [simpl; lia | constructor]].
      * cbn [vflat]. rewrite rl_mk; [ | destruct (rtg (RO ri)); [discriminate | reflexivity] | simpl; lia]. simpl.
        rewrite PTree.gss. rewrite PTree.gso by (apply Pos.succ_discr). rewrite PTree.gss. reflexivity.
  - (* RLet *) intros e IHe x IHx cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [We Wx].
    apply IHe with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denote_e cs rec cenv benv renv denv M e :: denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_let; auto. eapply inv_step; eauto.
    + intros rho2 n2 As A2 Le2 LAs VAs. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact LAs | exact VAs].
  - (* RLetR *) intros y IHy x IHx cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [Wy Wx].
    eapply IHy; [exact Wy | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
    eapply IHx; [exact Wx | apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs] | apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto] |].
    intros rho2 n2 Bs A2 Le2 LBs VBs. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact LBs | exact VBs].
  - (* RIf *) intros ri c a IHa b IHb x IHx y IHy cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK.
    cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Wb].
    apply andb_true_iff in W as [W Wa]. apply andb_true_iff in W as [Ex Ey]. apply Nat.eqb_eq in Ex, Ey.
    apply IHa with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHb with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)) eqn:C.
      * apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 As3 A3 Le3 L3 V3.
        apply HK; [| lia | exact L3 |].
        { eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia. }
        cbn [vflat]. rewrite to_rt_vflat; [exact V3 | rewrite <- Ex; eapply kind_denote_r; eauto].
      * apply IHy with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
        { eapply inv_step; [exact I2 | apply agree_refl | afterle]. }
        intros rho3 n3 As3 A3 Le3 L3 V3.
        apply HK; [| lia_a | exact L3 |].
        { eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); [eauto | eauto | eapply agree_mono; [exact A3 | afterle] | lia | lia]. }
        cbn [vflat]. rewrite to_rt_vflat; [exact V3 | rewrite <- Ey; eapply kind_denote_r; eauto].
  - (* RMatchR *) intros ri x IHx y IHy cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [Ey Wx]. apply Nat.eqb_eq in Ey.
    eapply IHx; [exact Wx | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
    eapply IHy; [exact Wy | apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs] | exact Rt |].
    intros rho2 n2 Bs A2 Le2 LBs VBs. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact LBs | ].
    cbn [vflat]. rewrite rmatch_eq, to_rt_vflat; [exact VBs | rewrite <- Ey; eapply kind_denote_r; eauto].
  - (* RIfB *) intros ri b IHb x IHx y IHy cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Wb].
    apply andb_true_iff in W as [Ex Ey]. apply Nat.eqb_eq in Ex, Ey. destruct IHb as [IHbc _].
    apply IHbc with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta.
      apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 As2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 |].
      rewrite Hb. cbn [vflat]. rewrite to_rt_vflat; [exact V2 | rewrite <- Ex; eapply kind_denote_r; eauto].
    + intros Hb rho1 n1 A1 Le1. cbv beta.
      apply IHy with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 As2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 |].
      rewrite Hb. cbn [vflat]. rewrite to_rt_vflat; [exact V2 | rewrite <- Ey; eapply kind_denote_r; eauto].
  - (* RLetB *) intros b IHb x IHx cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *. apply andb_true_iff in W as [Wb Wx].
    destruct IHb as [_ [IHbv _]].
    eapply IHbv; [exact Wb | exact Iv | exact Rt |]. intros rho1 n1 A A1 Le1 LA VA.
    eapply IHx; [exact Wx | apply inv_blet; [eapply inv_step; eauto | exact VA | exact LA] | exact Rt |].
    intros rho2 n2 As A2 Le2 LAs VAs. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact LAs | exact VAs].
  - (* RLetC *) intros c IHc x IHx cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc Wl].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    eapply IHc; [exact Wc | eapply letc_okv_wb; exact Wl | exact Iv | exact Rt | ].
    intros rho1 n1 A A1 Le1 LA VA.
    eapply IHx with (cbs := cpush_let (sigsv cbs) c :: cbs); [exact Wx | apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto] | exact Rt |].
    intros rho2 n2 As A2 Le2 LAs VAs. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact LAs | exact VAs].
  - (* RMatchCnt *) intros ri c x IHx y IHy cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [W W1]. apply andb_true_iff in W as [W W0]. apply andb_true_iff in W as [Ex Ey]. apply Nat.eqb_eq in Ex, Ey.
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
    destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl.
      apply IHx with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      intros rho3 n3 As3 A3 Le3 L3 V3. apply HK; [exact A3 | exact Le3 | exact L3 |].
      cbn [vflat]. rewrite to_rt_vflat; [exact V3 | rewrite <- Ex; eapply kind_denote_r; eauto].
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IHy with (cenv := p :: cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto.
      * apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
      * intros rho3 n3 As3 A3 Le3 L3 V3. apply HK; [ | lia_a | exact L3 | ].
        -- refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
        -- cbn [vflat]. rewrite to_rt_vflat; [exact V3 | rewrite <- Ey; eapply kind_denote_r; eauto].
  - (* RSplitR *) intros ri sj x IHx y IHy cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [W Wy]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Ex Ey]. apply Nat.eqb_eq in Ex, Ey.
    eapply IHx; [exact Wx | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M x) = KRec sj) by (rewrite <- Ex; eapply kind_denote_r; eauto).
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    eapply IHy; [exact Wy | apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs] | apply rsplit_typed; [exact Kx | exact Rt] |].
    intros rho2 n2 Bs A2 Le2 LBs VBs. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact LBs | ].
    cbn [vflat]. rewrite rsplit_eq, to_rt_vflat; [exact VBs | rewrite <- Ey; eapply kind_denote_r; [exact Wy | apply rsplit_typed; [exact Kx | exact Rt]]].
  - (* RMkR *) intros ri ns IHns rs IHrs cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK. cbn [crec denote_r wfr] in *.
    apply andb_true_iff in W as [W Wrs]. apply andb_true_iff in W as [W Wns]. apply andb_true_iff in W as [W Wl].
    apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wg Wn]. apply Nat.eqb_eq in Wl.
    destruct (rtg (RO ri)) eqn:G; [discriminate Wg|].
    destruct (flat_nums cs rec cenv benv renv denv M ns Wn) as [F1 F2].
    destruct (rec_vals cs rec cenv benv renv denv M _ _ _ _ _ _ rs (RJ ri) Wrs Rt Wk) as [R1 R2].
    eapply IHns; [exact Wns | exact Iv | exact Rt |]. intros rho1 n1 As A1 Le1 LAs VAs.
    eapply IHrs; [exact Wrs | eapply inv_step; eauto | exact Rt |]. intros rho2 n2 Bs A2 Le2 LBs VBs.
    apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | apply Forall_app; split; [eapply Forall_impl; [|exact LAs]; intros a La; eapply atom_lt_mono; [exact La | lia] | exact LBs] |].
    cbn [vflat]. rewrite rb_mk; [ | exact G | exact R2 | rewrite fold_rn_map, R2, F2; exact Wl].
    apply avals_app; [rewrite (avals_agree rho1 rho2 n1); [rewrite <- F1; exact VAs | exact A2 | exact LAs] | rewrite <- R1; exact VBs].
Qed.

Definition cexp_ok := proj1 cexp_all.
Definition cexps_ok := proj1 (proj2 cexp_all).
Definition ccnts_ok := proj1 (proj2 (proj2 (proj2 cexp_all))).
Definition ccond_ok := fun b => proj1 (proj1 (proj2 (proj2 (proj2 (proj2 cexp_all)))) b).
Definition cbval_ok := fun b => proj1 (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 cexp_all)))) b)).
Definition csel_ok := fun b => proj2 (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 cexp_all)))) b)).
Definition ccnt_ok := proj1 (proj2 (proj2 cexp_all)).
Definition crec_ok := proj2 (proj2 (proj2 (proj2 (proj2 cexp_all)))).



Lemma pvcall_run : forall fi ccs args m rk cbs cenv benv renv denv M gs h rp, nth_error cs fi = Some (existT _ gs h) ->
  wfpv (sigsv cbs) r rm mok rp nx k rk (PvCall fi ccs args m) = true -> rtyped renv rk -> cboundv cbj cbs pv cenv -> forall M0,
  runk P (gidf fi) (map ofn (denote_cs cs rec cenv benv renv denv M ccs) ++ flat_map vflat (denote_es cs rec cenv benv renv denv M args)) M0
    (fst (pvf gs (callf gs h (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M0)))
    (snd (pvf gs (callf gs h (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M0))).
Proof.
  intros fi ccs args m rk cbs cenv benv renv denv M gs h rp E W Rt Cb M0.
  cbn [wfpv] in W. unfold sigsv in W. cbn [fst] in W. rewrite nth_sigs, E in W. simpl in W.
  apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
  apply andb_true_iff in W as [W Wsh]. apply andb_true_iff in W as [W Wq]. apply andb_true_iff in W as [W Wsw].
  apply andb_true_iff in W as [W Wr]. apply andb_true_iff in W as [W Wsm]. apply andb_true_iff in W as [Wn Wk].
  assert (Hfi : (fi < j)%nat).
  { assert (fi < length cs)%nat by (apply nth_error_Some; rewrite E; discriminate). lia. }
  pose proof (Hcs fi) as Hc. unfold callee in *. rewrite E in Hc.
  destruct gs as [gx gk gm gr gw gq gb gv gp]. cbn [sq sr sw sn sk sm sb sv] in *.
  destruct gq as [[| |gri]|]; try discriminate Wq. destruct gr; [discriminate Wr|]. destruct gw; [discriminate Wsw|].
  assert (L1 : length (denote_cs cs rec cenv benv renv denv M ccs) = gx) by (rewrite len_denote_cs; apply Nat.eqb_eq; auto).
  assert (L2 : map kind_of (denote_es cs rec cenv benv renv denv M args) = gk)
    by (erewrite kinds_denote_es by eassumption; apply kinds_eqb_eq; auto).
  exact (Hc Hslot _ _ M0 L1 L2 (cs_fit_bound cbs ccs cenv benv renv denv M _ _ Wsh Cb)).
Qed.


(** a call given the whole number-and-memory pair (step 44): the callee's theorem on the components at the pair's number and
    memory, the call on the pair *)
Lemma pcall_pre : forall fi gs h cvs vs pr, nth_error cs fi = Some (existT _ gs h) ->
  sp gs = true -> sm gs = true -> last_num (sk gs) = true ->
  length cvs = sn gs -> map kind_of vs = removelast (sk gs) -> cfits gs (fbound gs fi) cvs ->
  if sw gs then exists M', runk P (gidf fi) (map ofn cvs ++ flat_map vflat vs ++ [fst pr]) (snd pr) (callnp gs h cvs vs pr) M'
  else runk P (gidf fi) (map ofn cvs ++ flat_map vflat vs ++ [fst pr]) (snd pr) (callnp gs h cvs vs pr)
         (if sr gs then callmp gs h cvs vs pr else match sq gs with Some _ => callmp gs h cvs vs pr | None => snd pr end).
Proof.
  intros fi gs h cvs vs pr E Sp Sm Sl L1 L2 L3.
  pose proof (Hcs fi) as Hc. unfold callee in *. rewrite E in Hc.
  pose proof (Hc Hslot cvs (vs ++ [VNum (fst pr)]) (snd pr) L1 (kinds_snoc _ _ _ Sl L2) L3) as H1.
  rewrite (callnp_snoc gs h cvs vs pr Sp Sm Sl L2), (callmp_snoc gs h cvs vs pr Sp Sm Sl L2), flat_map_app in H1.
  cbn [flat_map vflat app] in H1. exact H1.
Qed.
Lemma mcallp_run : forall fi gs h cvs vs pr, nth_error cs fi = Some (existT _ gs h) ->
  sp gs = true -> sm gs = true -> last_num (sk gs) = true -> sr gs = true -> sw gs = false -> sq gs = None ->
  length cvs = sn gs -> map kind_of vs = removelast (sk gs) -> cfits gs (fbound gs fi) cvs ->
  runk P (gidf fi) (map ofn cvs ++ flat_map vflat vs ++ [fst pr]) (snd pr) (callnp gs h cvs vs pr) (callmp gs h cvs vs pr).
Proof.
  intros fi gs h cvs vs pr E Sp Sm Sl Sr Sw Sq L1 L2 L3.
  pose proof (pcall_pre fi gs h cvs vs pr E Sp Sm Sl L1 L2 L3) as H1. rewrite Sw, Sr in H1. exact H1.
Qed.
Lemma pvcallp_run : forall fi gs h cvs vs pr, nth_error cs fi = Some (existT _ gs h) ->
  sp gs = true -> sm gs = true -> last_num (sk gs) = true -> sr gs = false -> sw gs = false -> sq gs = Some KNum ->
  length cvs = sn gs -> map kind_of vs = removelast (sk gs) -> cfits gs (fbound gs fi) cvs ->
  runk P (gidf fi) (map ofn cvs ++ flat_map vflat vs ++ [fst pr]) (snd pr) (fst (pvf gs (callfp gs h cvs vs pr)))
    (snd (pvf gs (callfp gs h cvs vs pr))).
Proof.
  intros fi gs h cvs vs pr E Sp Sm Sl Sr Sw Sq L1 L2 L3.
  pose proof (pcall_pre fi gs h cvs vs pr E Sp Sm Sl L1 L2 L3) as H1.
  destruct gs as [gx gk gm gr gw gq gb gv gp]. cbn [sp sm sk sr sw sq sn] in *. subst gr gw gq. exact H1.
Qed.
Lemma xcallp_run : forall fi gs h cvs vs pr, nth_error cs fi = Some (existT _ gs h) ->
  sp gs = true -> sm gs = true -> last_num (sk gs) = true -> sr gs = false -> sq gs = None ->
  length cvs = sn gs -> map kind_of vs = removelast (sk gs) -> cfits gs (fbound gs fi) cvs ->
  exists M', runk P (gidf fi) (map ofn cvs ++ flat_map vflat vs ++ [fst pr]) (snd pr) (callnp gs h cvs vs pr) M'.
Proof.
  intros fi gs h cvs vs pr E Sp Sm Sl Sr Sq L1 L2 L3.
  pose proof (pcall_pre fi gs h cvs vs pr E Sp Sm Sl L1 L2 L3) as H1. rewrite Sr, Sq in H1.
  destruct (sw gs); [exact H1 | eexists; exact H1].
Qed.
(** a memory: KQL's memory after it is the memory the Rocq text makes; where a number and a memory is taken apart: the
    continuation gets the number's atom and the KQL memory is the pair's -- one mutual lemma, a memory taking a pair apart and
    a pair holding memories (step 44) *)
Lemma cmem_cpv_ok :
  (forall m cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wfm (sigsv cbs) r rm mok nx k rk m = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  (forall rho' n', agree rho rho' nxt -> Pos.le nxt n' -> evalk P f rho' (denote_m cs rec recm cenv benv renv denv M m) (K n') v M') ->
  evalk P f rho M (cmem gidf g mv m cenvA benvA renvA envA nxt K) v M')
  /\
  (forall p (recp : list nat -> list val -> mem -> (i63 * mem)%type) (rp : bool),
  (rp = true -> forall cvs vs M, length cvs = nx -> map kind_of vs = k -> rfits cvs ->
     runk P g (ofn cm :: map ofn cvs ++ flat_map vflat vs) M (fst (recp cvs vs M)) (snd (recp cvs vs M))) ->
  (rp = true -> hp = true) ->
  forall cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wfpv (sigsv cbs) r rm mok rp nx k rk p = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' ->
     aval rho' a = Some (fst (denote_pv cs rec recm recp cenv benv renv denv M p)) ->
     evalk P f rho' (snd (denote_pv cs rec recm recp cenv benv renv denv M p)) (K a n') v M') ->
  evalk P f rho M (cpv gidf g mv p cenvA benvA renvA envA nxt K) v M').
Proof.
  apply smem_comb.
  - intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MCur *) apply HK; [apply agree_refl | lia].
  - intros h i x m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MUpd *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wh Wi].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 H A1 Le1 LH VH.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho2 n2 J A2 Le2 LJ VJ.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 X A3 Le3 LX VX.
    pose proof (inv_step rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 I2 A3 Le3) as I3.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho4 n4 A4 Le4.
    apply K_st with (vh := denote_e cs rec cenv benv renv denv M h) (vi := denote_e cs rec cenv benv renv denv M i)
                    (va := denote_e cs rec cenv benv renv denv M x).
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2), (aval_agree rho1 rho2 n1); auto;
        eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2); auto; eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3); auto.
    + apply HK; [| lia]. apply (agree_4 rho rho1 rho2 rho3 rho4 nxt n1 n2 n3); auto.
  - intros e m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MLet *) apply andb_true_iff in W as [We Wm].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denote_e cs rec cenv benv renv denv M e :: denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_let; auto. eapply inv_step; eauto.
    + intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros m1 IH1 m2 IH2; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MLetM *) apply andb_true_iff in W as [W1 W2].
    apply IH1 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A1 Le1.
    apply IH2 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros c a b m1 IH1 m2 IH2; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MIf *) apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [W Wm1]. apply andb_true_iff in W as [Wa Wb].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      cbn [denote_m] in HK.
      destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)) eqn:C.
      * apply IH1 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
        apply HK; [| lia]. eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia.
      * apply IH2 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
        { eapply inv_step; [exact I2 | apply agree_refl | afterle]. }
        intros rho3 n3 A3 Le3.
        apply HK; [| lia_a]. eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); [eauto | eauto | eapply agree_mono; [exact A3 | afterle] | lia | lia].
  - intros ccs args m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MRec *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    destruct (Hrecm Wr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args)
                       (denote_m cs rec recm cenv benv renv denv M m)) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1 & _). destruct (H1 (Hrmhp Wr)) as [Rm _].
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    eapply K_call; eauto.
    + simpl. rewrite (A3 mv) by lia. rewrite (A2 mv Mv1), Rm, (avals_app rho3 Cs As _ _ VC3 VA3). reflexivity.
    + apply HK.
      * apply agree_set1; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto | lia].
      * lia.
  - intros fi ccs args m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MCall *) unfold sigsv in W. cbn [fst] in W; rewrite nth_sigs in W. pose proof (Hcs fi) as Hc.
    cbn [denote_m] in HK. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    assert (Hfi : (fi < j)%nat).
    { assert (fi < length cs)%nat by (apply nth_error_Some; rewrite E; discriminate). lia. }
    apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wsh]. apply andb_true_iff in W as [W Wsw]. apply andb_true_iff in W as [W Wr].
    apply andb_true_iff in W as [W Wsm]. apply andb_true_iff in W as [Wn Wk].
    assert (Hc2 : forall cvs0 vs0 M0, length cvs0 = sn gs -> map kind_of vs0 = sk gs -> cfits gs (fbound gs fi) cvs0 ->
              runk P (gidf fi) (map ofn cvs0 ++ flat_map vflat vs0) M0 (calln gs h cvs0 vs0 M0) (if sr gs then callm gs h cvs0 vs0 M0 else M0)).
    { intros cvs0 vs0 M0 L1 L2 L3. pose proof (Hc Hslot cvs0 vs0 M0 L1 L2 L3) as H0. destruct (sw gs); [discriminate Wsw|]. unfold isq in Wsw. destruct (sq gs); [discriminate Wsw | exact H0]. }
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    destruct (Hc2 (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) (denote_m cs rec recm cenv benv renv denv M m))
      as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply (cs_fit_bound cbs); eauto. }
    rewrite Wr in EV.
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    eapply K_call; eauto.
    + apply avals_app; eauto.
    + apply HK.
      * apply agree_set1; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto | lia].
      * lia.
  - intros c m0 IH0 m1 IH1; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MMatch *) apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
    cbn [denote_m] in HK.
    destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl.
      apply IH0 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (cenv := p :: cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto.
      * apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
      * intros rho3 n3 A3 Le3. apply HK; [ | lia_a ].
        refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
  - intros b m1 IH1 m2 IH2; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MIfB *) apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [Wb Wm1].
    cbn [denote_m] in HK.
    apply (ccond_ok b) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta.
      apply IH1 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 A2 Le2. rewrite Hb in HK. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros Hb rho1 n1 A1 Le1. cbv beta.
      apply IH2 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 A2 Le2. rewrite Hb in HK. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros b m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MLetB *) apply andb_true_iff in W as [Wb Wm].
    apply (cbval_ok b) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (cenv := cenv) (benv := denote_b cs rec cenv benv renv denv M b :: benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_blet; auto. eapply inv_step; eauto.
    + intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros h i x m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MUpd32 *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wh Wi].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 H A1 Le1 LH VH.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho2 n2 J A2 Le2 LJ VJ.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 X A3 Le3 LX VX.
    pose proof (inv_step rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 I2 A3 Le3) as I3.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho4 n4 A4 Le4.
    apply K_st32 with (vh := denote_e cs rec cenv benv renv denv M h) (vi := denote_e cs rec cenv benv renv denv M i)
                    (va := denote_e cs rec cenv benv renv denv M x).
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2), (aval_agree rho1 rho2 n1); auto;
        eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2); auto; eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3); auto.
    + apply HK; [| lia]. apply (agree_4 rho rho1 rho2 rho3 rho4 nxt n1 n2 n3); auto.
  - intros c m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MLetC *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [Wc Wl].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnt_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply letc_okv_wb; exact Wl. }
    intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (cenv := denote_c cs rec cenv benv renv denv M c :: cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cpush_let (sigsv cbs) c :: cbs); auto.
    + apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto].
    + intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros o args m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MHw *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Wa]. apply andb_true_iff in W as [Wn Wk].
    apply Nat.eqb_eq in Wn. destruct (flat_nums cs rec cenv benv renv denv M args Wk) as [F1 F2].
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    rewrite F1 in VAs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho2 n2 A2 Le2.
    eapply K_hw; [rewrite (avals_length rho1 As _ VAs), F2; exact Wn | rewrite (avals_agree rho1 rho2 n1 As A2 LAs); exact VAs |].
    apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros h i x m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MUpd8 *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wh Wi].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 H A1 Le1 LH VH.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho2 n2 J A2 Le2 LJ VJ.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 X A3 Le3 LX VX.
    pose proof (inv_step rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 I2 A3 Le3) as I3.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho4 n4 A4 Le4.
    apply K_st8 with (vh := denote_e cs rec cenv benv renv denv M h) (vi := denote_e cs rec cenv benv renv denv M i)
                    (va := denote_e cs rec cenv benv renv denv M x).
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2), (aval_agree rho1 rho2 n1); auto;
        eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2); auto; eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3); auto.
    + apply HK; [| lia]. apply (agree_4 rho rho1 rho2 rho3 rho4 nxt n1 n2 n3); auto.
  - intros x m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MLetR *) apply andb_true_iff in W as [Wx Wm].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    apply IH with (cenv := cenv) (benv := benv) (renv := denote_r cs rec cenv benv renv denv M x :: renv) (denv := denv) (rk := rtype rk x :: rk) (cbs := cbs); auto.
    + apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs].
    + apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto].
    + intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros x m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MMatchR *) apply andb_true_iff in W as [Wx Wm].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := rev (vflat (denote_r cs rec cenv benv renv denv M x)) ++ denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs].
    + intros rho2 n2 A2 Le2. cbn [denote_m] in HK. rewrite rmatch_eq in HK. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros sj x m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MSplitR *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M x) = KRec sj) by (rewrite <- Ex; eapply kind_denote_r; eauto).
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    apply IH with (cenv := cenv) (benv := benv) (renv := rev (snd (rsplit_p (denote_r cs rec cenv benv renv denv M x))) ++ renv)
                  (denv := rev (fst (rsplit_p (denote_r cs rec cenv benv renv denv M x))) ++ denv) (rk := rev (RJ sj) ++ rk) (cbs := cbs); auto.
    + apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs].
    + apply rsplit_typed; [exact Kx | exact Rt].
    + intros rho2 n2 A2 Le2. cbn [denote_m] in HK. rewrite rsplit_eq in HK. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros p IHp m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    apply andb_true_iff in W as [Wp Wm].
    eapply (IHp dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Wp | exact Iv | exact Rt | ].
    intros rho1 n1 A A1 Le1 LA VA. cbn [denote_m] in HK. destruct (denote_pv cs rec recm dpair cenv benv renv denv M p) as [x0 s0] eqn:Ep.
    cbn [fst snd] in VA |- *.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := x0 :: denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_let; [eapply inv_step; eauto | exact VA | exact LA].
    + intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros p IHp m IH; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    apply andb_true_iff in W as [Wp Wm].
    eapply (IHp dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Wp | exact Iv | exact Rt | ].
    intros rho1 n1 A A1 Le1 LA VA. cbn [denote_m] in HK. cbv zeta in HK.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := fst (denote_pv cs rec recm dpair cenv benv renv denv M p) :: denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_let; [eapply inv_step; eauto | exact VA | exact LA].
    + intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - intros fi ccs args p IHp; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cmem wfm] in *.
    (* MCallP *) unfold sigsv in W. cbn [fst] in W; rewrite nth_sigs in W.
    cbn [denote_m] in HK. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Wp]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wsh]. apply andb_true_iff in W as [W Wq]. apply andb_true_iff in W as [W Wr]. apply andb_true_iff in W as [W Wl].
    apply andb_true_iff in W as [W Wsm]. apply andb_true_iff in W as [W Wsp]. apply andb_true_iff in W as [Wn Wk].
    apply negb_true_iff, orb_false_iff in Wq as [Wsw Wq]. unfold isq in Wq. destruct (sq gs) eqn:Q; [discriminate Wq|].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    eapply (IHp dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Wp | exact I2 | exact Rt | ].
    intros rho3 n3 A A3 Le3 LA VA.
    destruct (mcallp_run fi gs h (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) (denote_pv cs rec recm dpair cenv benv renv denv M p) E Wsp Wsm Wl Wr Wsw Q) as (fg & rho' & F & B & EV).
      { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
      { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
      { eapply (cs_fit_bound cbs); eauto. }
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    assert (VS3 : avals rho3 (Cs ++ As ++ [A]) = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs)
                    ++ flat_map vflat (denote_es cs rec cenv benv renv denv M args) ++ [fst (denote_pv cs rec recm dpair cenv benv renv denv M p)])).
    { apply avals_app; [exact VC3 | apply avals_app; [exact VA3 | cbn [avals]; rewrite VA; reflexivity]]. }
    eapply K_call; [exact F | exact VS3 | exact B | exact EV | ].
    apply HK; [apply agree_set1; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto | lia] | lia].
  - intros e m IHm; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK.
    (* PvMk *) cbn [wfpv] in W. apply andb_true_iff in W as [We Wm].
    assert (We' : wf (sigsv cbs) r mok nx k rk e = true) by (exact We).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (exact Wm).
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHm with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 A2 Le2. apply HK.
    + eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
    + lia.
    + eapply atom_lt_mono; [exact LA | lia].
    + rewrite (aval_agree rho1 rho2 n1); [exact VA | exact A2 | exact LA].
  - intros fi ccs args m IHm; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK.
    (* PvCall *) pose proof W as W0. cbn [wfpv] in W0. unfold sigsv in W0. cbn [fst] in W0; rewrite nth_sigs in W0.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W0; [|discriminate W0].
    apply andb_true_iff in W0 as [W0 Wm]. apply andb_true_iff in W0 as [W0 Ws]. apply andb_true_iff in W0 as [W0 Wc].
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (exact Ws).
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (exact Wc).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (exact Wm).
    apply andb_true_iff in W0 as [W0 Wsh].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply IHm with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    destruct (pvcall_run fi ccs args m rk cbs cenv benv renv denv M gs h rp E W Rt Cb (denote_m cs rec recm cenv benv renv denv M m))
      as (fg & rho' & Fd & Bd & EVd).
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    eapply K_call; [exact Fd | apply avals_app; [exact VC3 | exact VA3] | exact Bd | exact EVd | ].
    apply HK.
    + apply agree_set1; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto | lia].
    + lia.
    + simpl. lia.
    + cbn [aval]. rewrite PTree.gss. reflexivity.
  - intros ccs args m IHm; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK.
    (* PvRec *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (exact Ws).
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (exact Wc).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (exact Wm).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply IHm with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    destruct (Hrecp Wr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args)
                       (denote_m cs rec recm cenv benv renv denv M m)) as (fg & rho' & Fd & Bd & EVd).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1 & _). destruct (H1 (Hrphp Wr)) as [Rm _].
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    eapply K_call; [exact Fd | | exact Bd | exact EVd | ].
    + simpl. rewrite (A3 mv) by lia. rewrite (A2 mv Mv1), Rm, (avals_app rho3 Cs As _ _ VC3 VA3). reflexivity.
    + apply HK.
      * apply agree_set1; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto | lia].
      * lia.
      * simpl. lia.
      * cbn [aval]. rewrite PTree.gss. reflexivity.
  - intros e p IH; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IH recp rp Hrecp Hrphp).
    (* PvLet *) cbn [wfpv] in W. apply andb_true_iff in W as [We Wp].
    assert (We' : wf (sigsv cbs) r mok nx k rk e = true) by (exact We).
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denote_e cs rec cenv benv renv denv M e :: denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_let; auto. eapply inv_step; eauto.
    + intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - intros c p IH; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IH recp rp Hrecp Hrphp).
    (* PvLetB *) cbn [wfpv] in W. apply andb_true_iff in W as [Wc Wp].
    assert (Wc' : wfb (sigsv cbs) r mok nx k rk c = true) by (exact Wc).
    apply (cbval_ok c) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (cenv := cenv) (benv := denote_b cs rec cenv benv renv denv M c :: benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_blet; auto. eapply inv_step; eauto.
    + intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - intros c p IH; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IH recp rp Hrecp Hrphp).
    (* PvLetC *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wp]. apply andb_true_iff in W as [Wc Wl].
    assert (Wc' : wfc (sigsv cbs) r mok nx k rk c = true) by (exact Wc).
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnt_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply letc_okv_wb; exact Wl. }
    intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (cenv := denote_c cs rec cenv benv renv denv M c :: cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cpush_let (sigsv cbs) c :: cbs); auto.
    + apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto].
    + intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - intros x p IH; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IH recp rp Hrecp Hrphp).
    (* PvLetR *) cbn [wfpv] in W. apply andb_true_iff in W as [Wx Wp].
    assert (Wx' : wfr (sigsv cbs) r mok nx k rk x = true) by (exact Wx).
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    apply IH with (cenv := cenv) (benv := benv) (renv := denote_r cs rec cenv benv renv denv M x :: renv) (denv := denv) (rk := rtype rk x :: rk) (cbs := cbs); auto.
    + apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs].
    + apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto].
    + intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - intros x p IH; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IH recp rp Hrecp Hrphp).
    (* PvMatchR *) cbn [wfpv] in W. apply andb_true_iff in W as [Wx Wp].
    assert (Wx' : wfr (sigsv cbs) r mok nx k rk x = true) by (exact Wx).
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    rewrite rmatch_eq in HK.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := rev (vflat (denote_r cs rec cenv benv renv denv M x)) ++ denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs].
    + intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - intros m IHm p IH; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IH recp rp Hrecp Hrphp).
    (* PvLetM *) cbn [wfpv] in W. apply andb_true_iff in W as [Wm Wp].
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (exact Wm).
    apply IHm with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A1 Le1.
    apply IH with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + eapply inv_step; eauto.
    + intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - intros c x y t IHt u IHu; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IHt recp rp Hrecp Hrphp). specialize (IHu recp rp Hrecp Hrphp).
    (* PvIf *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wx Wy].
    assert (Wx' : wf (sigsv cbs) r mok nx k rk x = true) by (exact Wx).
    assert (Wy' : wf (sigsv cbs) r mok nx k rk y = true) by (exact Wy).
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M x) (denote_e cs rec cenv benv renv denv M y)) eqn:C.
      * apply IHt with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 a A3 Le3 La Va.
        apply HK; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia | lia | exact La | exact Va].
      * apply IHu with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
        { eapply inv_step; [exact I2 | apply agree_refl | afterle]. }
        intros rho3 n3 a A3 Le3 La Va.
        apply HK; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); [eauto | eauto | eapply agree_mono; [exact A3 | afterle] | lia | lia] | lia_a | exact La | exact Va].
  - intros c t IHt u IHu; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IHt recp rp Hrecp Hrphp). specialize (IHu recp rp Hrecp Hrphp).
    (* PvIfB *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wc Wt].
    assert (Wc' : wfb (sigsv cbs) r mok nx k rk c = true) by (exact Wc).
    apply (ccond_ok c) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb in HK.
      apply IHt with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb in HK.
      apply IHu with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
      intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - intros c p0 IH0 p1 IH1; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IH0 recp rp Hrecp Hrphp). specialize (IH1 recp rp Hrecp Hrphp).
    (* PvMatch *) cbn [wfpv] in W. apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
    destruct (nth c cenv O) as [|pr] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl.
      apply IH0 with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S pr))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S pr) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (cenv := pr :: cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto.
      * apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
      * intros rho3 n3 a A3 Le3 La Va. apply HK; [ | lia_a | exact La | exact Va].
        refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
  - intros p IHp q IHq; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IHp recp rp Hrecp Hrphp). specialize (IHq recp rp Hrecp Hrphp).
    (* PvMatchP *) cbn [wfpv] in W. apply andb_true_iff in W as [Wp Wq].
    apply IHp with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA. cbv beta.
    destruct (denote_pv cs rec recm recp cenv benv renv denv M p) as [x0 s0] eqn:Ep.
    cbn [fst snd] in VA |- *. try rewrite Ep in HK. cbv iota in HK.
    apply IHq with (cenv := cenv) (benv := benv) (renv := renv) (denv := x0 :: denv) (rk := rk) (cbs := cbs); auto.
    + apply inv_let; auto. eapply inv_step; eauto.
    + intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - intros sj x p IH; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IH recp rp Hrecp Hrphp).
    (* PvSplitR *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wp]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    assert (Wx' : wfr (sigsv cbs) r mok nx k rk x = true) by (exact Wx).
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M x) = KRec sj) by (rewrite <- Ex; eapply kind_denote_r; eauto).
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    rewrite rsplit_eq in HK.
    apply IH with (cenv := cenv) (benv := benv) (renv := rev (snd (rsplit_p (denote_r cs rec cenv benv renv denv M x))) ++ renv)
                  (denv := rev (fst (rsplit_p (denote_r cs rec cenv benv renv denv M x))) ++ denv) (rk := rev (RJ sj) ++ rk) (cbs := cbs); auto.
    + apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs].
    + apply rsplit_typed; [exact Kx | exact Rt].
    + intros rho2 n2 a A2 Le2 La Va. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact La | exact Va].
  - intros fi ccs args p IHp; intros recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK; cbn [cpv] in *; cbn [denote_pv] in HK. specialize (IHp recp rp Hrecp Hrphp).
    (* PvCallP *) pose proof W as W0. cbn [wfpv] in W0. unfold sigsv in W0. cbn [fst] in W0; rewrite nth_sigs in W0.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W0; [|discriminate W0].
    apply andb_true_iff in W0 as [W0 Wp]. apply andb_true_iff in W0 as [W0 Ws]. apply andb_true_iff in W0 as [W0 Wc].
    apply andb_true_iff in W0 as [W0 Wsh]. apply andb_true_iff in W0 as [W0 Wq]. apply andb_true_iff in W0 as [W0 Wsw]. apply andb_true_iff in W0 as [W0 Wr]. apply andb_true_iff in W0 as [W0 Wl].
    apply andb_true_iff in W0 as [W0 Wsm]. apply andb_true_iff in W0 as [W0 Wsp]. apply andb_true_iff in W0 as [Wn Wk].
    apply negb_true_iff in Wsw, Wr. destruct (sq gs) as [[| |?]|] eqn:Q; try discriminate Wq.
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    eapply IHp; [exact Wp | exact I2 | exact Rt | ].
    intros rho3 n3 A A3 Le3 LA VA.
    pose proof (pvcallp_run fi gs h (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) (denote_pv cs rec recm recp cenv benv renv denv M p) E Wsp Wsm Wl Wr Wsw Q) as RK.
    destruct RK as (fg & rho' & Fd & Bd & EVd).
      { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
      { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
      { eapply (cs_fit_bound cbs); eauto. }
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    assert (VS3 : avals rho3 (Cs ++ As ++ [A]) = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs)
                    ++ flat_map vflat (denote_es cs rec cenv benv renv denv M args) ++ [fst (denote_pv cs rec recm recp cenv benv renv denv M p)])).
    { apply avals_app; [exact VC3 | apply avals_app; [exact VA3 | cbn [avals]; rewrite VA; reflexivity]]. }
    eapply K_call; [exact Fd | exact VS3 | exact Bd | exact EVd | ].
    apply HK.
    + apply agree_set1; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto | lia].
    + lia.
    + simpl. lia.
    + cbn [aval]. rewrite PTree.gss. reflexivity.
Qed.
Lemma cmem_ok : forall m cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wfm (sigsv cbs) r rm mok nx k rk m = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  (forall rho' n', agree rho rho' nxt -> Pos.le nxt n' -> evalk P f rho' (denote_m cs rec recm cenv benv renv denv M m) (K n') v M') ->
  evalk P f rho M (cmem gidf g mv m cenvA benvA renvA envA nxt K) v M'.
Proof. exact (proj1 cmem_cpv_ok). Qed.

(** in tail position: the function's body ends with the value of [e] and the memory it started with *)
Hypothesis Hf : find P g = Some f.


(** the loop: the function itself again, on counters and numbers held by atoms *)
Lemma loop_call_ok : forall rho Cs As cvs vs M, r = true -> length cvs = nx -> map kind_of vs = k ->
  rfits cvs -> rho ! mv = Some (ofn cm) ->
  avals rho Cs = Some (map ofn cvs) -> avals rho As = Some (flat_map vflat vs) ->
  evalk P f rho M (Eloop (Avar mv :: Cs ++ As)) (rec cvs vs M) M.
Proof.
  intros rho Cs As cvs vs M Wr Lc Lv Bd Rm VC VA.
  destruct (Hrec Wr cvs vs M Lc Lv Bd) as (fg & rho' & F & B & EV).
  rewrite Hf in F. injection F as <-.
  eapply K_loop; eauto. simpl. rewrite Rm, (avals_app rho Cs As _ _ VC VA). reflexivity.
Qed.
Lemma loopm_call_ok : forall rho Cs As cvs vs M, rm = true -> length cvs = nx -> map kind_of vs = k ->
  rfits cvs -> rho ! mv = Some (ofn cm) ->
  avals rho Cs = Some (map ofn cvs) -> avals rho As = Some (flat_map vflat vs) ->
  evalk P f rho M (Eloop (Avar mv :: Cs ++ As)) 0%uint63 (recm cvs vs M).
Proof.
  intros rho Cs As cvs vs M Wr Lc Lv Bd Rm VC VA.
  destruct (Hrecm Wr cvs vs M Lc Lv Bd) as (fg & rho' & F & B & EV).
  rewrite Hf in F. injection F as <-.
  eapply K_loop; eauto. simpl. rewrite Rm, (avals_app rho Cs As _ _ VC VA). reflexivity.
Qed.

(** the loop of a number function that writes: the function itself again, with the end memory its call reaches *)
Lemma loopx_call_ok : forall rho Cs As cvs vs M v M', runk P g (ofn cm :: map ofn cvs ++ flat_map vflat vs) M v M' ->
  rho ! mv = Some (ofn cm) -> avals rho Cs = Some (map ofn cvs) -> avals rho As = Some (flat_map vflat vs) ->
  evalk P f rho M (Eloop (Avar mv :: Cs ++ As)) v M'.
Proof.
  intros rho Cs As cvs vs M v M' RK Rm VC VA. destruct RK as (fg & rho' & F & B & EV).
  rewrite Hf in F. injection F as <-.
  eapply K_loop; eauto. simpl. rewrite Rm, (avals_app rho Cs As _ _ VC VA). reflexivity.
Qed.

(* ---------------------------------------------------------------- the merged call *)
Section Merge.
(** the bounds of the counters in scope: a chain of tests binds none (step 35) *)
Variable cbs : list cbe.
(** the value of an item; the end a chain of tests takes; well formed items and trees; the tree once its tests are worked out *)
Definition ival (cenv : list nat) (benv : list bool) (renv : list val) (denv : list i63) (M : mem) (x : item) : i63 :=
  match x with ICnt c => ofn (denote_c cs rec cenv benv renv denv M c) | INum e => denote_e cs rec cenv benv renv denv M e end.
Fixpoint mt_sel (cenv : list nat) (benv : list bool) (renv : list val) (denv : list i63) (M : mem) (T : mtree) : list item * list item :=
  match T with
  | MLeaf c w => (c, w)
  | MNodeC c a b t f => if cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)
                        then mt_sel cenv benv renv denv M t else mt_sel cenv benv renv denv M f
  | MNodeB b t f => if denote_b cs rec cenv benv renv denv M b then mt_sel cenv benv renv denv M t else mt_sel cenv benv renv denv M f
  end.
Definition wfi (rk : list nat) (x : item) : bool := match x with ICnt c => wfc (sigsv cbs) r mok nx k rk c && (cmaxv (ub (sigsv cbs)) (snd (snd (sigsv cbs))) c <? 9223372036854775808)%Z | INum e => wf (sigsv cbs) r mok nx k rk e end.
Fixpoint wf_mt (rk : list nat) (T : mtree) : bool :=
  match T with
  | MLeaf c w => forallb (wfi rk) (c ++ w)
  | MNodeC _ a b t f => wf (sigsv cbs) r mok nx k rk a && wf (sigsv cbs) r mok nx k rk b && wf_mt rk t && wf_mt rk f
  | MNodeB b t f => wfb (sigsv cbs) r mok nx k rk b && wf_mt rk t && wf_mt rk f
  end.
Fixpoint at_ok (rho : env) (n : ident) (cenv : list nat) (benv : list bool) (renv : list val) (denv : list i63) (M : mem) (T : mtree) (At : atree)
  : Prop :=
  match T, At with
  | MLeaf c w, ALeaf c' w' => c' = c /\ w' = w
  | MNodeC cc a b t f, ANode cc' X Y A1 A2 =>
      cc' = cc /\ aval rho X = Some (denote_e cs rec cenv benv renv denv M a) /\ aval rho Y = Some (denote_e cs rec cenv benv renv denv M b)
      /\ atom_lt X n /\ atom_lt Y n /\ at_ok rho n cenv benv renv denv M t A1 /\ at_ok rho n cenv benv renv denv M f A2
  | MNodeB b t f, ANode cc' X Y A1 A2 =>
      cc' = Ceq /\ Y = Aint 0%uint63 /\ aval rho X = Some (b2i (denote_b cs rec cenv benv renv denv M b)) /\ atom_lt X n
      /\ at_ok rho n cenv benv renv denv M t A2 /\ at_ok rho n cenv benv renv denv M f A1
  | _, _ => False
  end.

Lemma at_ok_mono : forall T At rho rho' n n' cenv benv renv denv M, at_ok rho n cenv benv renv denv M T At -> agree rho rho' n ->
  Pos.le n n' -> at_ok rho' n' cenv benv renv denv M T At.
Proof.
  induction T as [c w | cc a b t IHt u IHu | b t IHt u IHu]; intros At rho rho' n n' cenv benv renv denv M H A Le;
    destruct At as [c' w' | cc' X Y A1 A2]; cbn [at_ok] in *; try contradiction.
  - exact H.
  - destruct H as (E & VX & VY & LX & LY & H1 & H2).
    refine (conj E (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    + rewrite (aval_agree rho rho' n X A LX). exact VX.
    + rewrite (aval_agree rho rho' n Y A LY). exact VY.
    + eapply atom_lt_mono; eauto.
    + eapply atom_lt_mono; eauto.
    + eapply IHt; eauto.
    + eapply IHu; eauto.
  - destruct H as (E & EY & VX & LX & H1 & H2).
    refine (conj E (conj EY (conj _ (conj _ (conj _ _))))).
    + rewrite (aval_agree rho rho' n X A LX). exact VX.
    + eapply atom_lt_mono; eauto.
    + eapply IHt; eauto.
    + eapply IHu; eauto.
Qed.

Lemma at_all_eq : forall T At rho n cenv benv renv denv M p, at_ok rho n cenv benv renv denv M T At -> at_all p At = mt_all p T.
Proof.
  induction T as [c w | cc a b t IHt u IHu | b t IHt u IHu]; intros At rho n cenv benv renv denv M p H;
    destruct At as [c' w' | cc' X Y A1 A2]; cbn [at_ok at_all mt_all] in *; try contradiction.
  - destruct H as [-> ->]. reflexivity.
  - destruct H as (_ & _ & _ & _ & _ & H1 & H2). rewrite (IHt _ _ _ _ _ _ _ _ p H1), (IHu _ _ _ _ _ _ _ _ p H2). reflexivity.
  - destruct H as (_ & _ & _ & _ & H1 & H2). rewrite (IHt _ _ _ _ _ _ _ _ p H1), (IHu _ _ _ _ _ _ _ _ p H2). apply andb_comm.
Qed.

Lemma at_first_leaf : forall T At rho n cenv benv renv denv M (q : list item -> list item -> bool), at_ok rho n cenv benv renv denv M T At ->
  mt_all q T = true -> q (fst (at_first At)) (snd (at_first At)) = true.
Proof.
  induction T as [c w | cc a b t IHt u IHu | b t IHt u IHu]; intros At rho n cenv benv renv denv M q H Q;
    destruct At as [c' w' | cc' X Y A1 A2]; cbn [at_ok at_first mt_all] in *; try contradiction.
  - destruct H as [-> ->]. exact Q.
  - destruct H as (_ & _ & _ & _ & _ & H1 & H2). apply andb_true_iff in Q as [Q1 Q2]. eapply IHt; eauto.
  - destruct H as (_ & _ & _ & _ & H1 & H2). apply andb_true_iff in Q as [Q1 Q2]. eapply IHu; eauto.
Qed.

Lemma mt_all_sel : forall T (q : list item -> list item -> bool) cenv benv renv denv M, mt_all q T = true ->
  q (fst (mt_sel cenv benv renv denv M T)) (snd (mt_sel cenv benv renv denv M T)) = true.
Proof.
  induction T as [c w | cc a b t IHt u IHu | b t IHt u IHu]; intros q cenv benv renv denv M Q; cbn [mt_all mt_sel] in *.
  - exact Q.
  - apply andb_true_iff in Q as [Q1 Q2]. destruct (cmp_sem _ _ _); auto.
  - apply andb_true_iff in Q as [Q1 Q2]. destruct (denote_b _ _ _ _ renv _ _ _); auto.
Qed.

Lemma wf_mt_leaves : forall T rk, wf_mt rk T = true -> mt_all (fun c w => forallb (wfi rk) (c ++ w)) T = true.
Proof.
  induction T as [c w | cc a b t IHt u IHu | b t IHt u IHu]; intros rk W; cbn [wf_mt mt_all] in *.
  - exact W.
  - apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [W W1]. rewrite IHt, IHu; auto.
  - apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [W W1]. rewrite IHt, IHu; auto.
Qed.

Lemma wfi_ith : forall l i rk, forallb (wfi rk) l = true -> wfi rk (ith l i) = true.
Proof.
  intros l i rk F. unfold ith. destruct (Nat.lt_ge_cases i (length l)) as [L|L].
  - rewrite forallb_forall in F. apply F. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. reflexivity.
Qed.

Lemma same_i_eq : forall x y, same_i x y = true -> x = y.
Proof.
  intros [a|a] [b|b] H; cbn [same_i] in H; try discriminate.
  - f_equal. apply same_c_eq. exact H.
  - f_equal. apply same_e_eq. exact H.
Qed.

Lemma ctests_ok : forall T cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk, wf_mt rk T = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  (forall rho' n' At, agree rho rho' nxt -> Pos.le nxt n' -> at_ok rho' n' cenv benv renv denv M T At -> evalk P f rho' M (K At n') v M') ->
  evalk P f rho M (ctests gidf g mv T cenvA benvA renvA envA nxt K) v M'.
Proof.
  induction T as [c w | cc a b t IHt u IHu | b t IHt u IHu]; intros cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk W Iv Rt HK;
    cbn [ctests wf_mt] in *.
  - apply HK; [apply agree_refl | lia | split; reflexivity].
  - apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 X A1 Le1 LX VX.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 Y A2 Le2 LY VY.
    assert (A12 : agree rho rho2 nxt) by (eapply (agree_trans rho rho1 rho2 nxt n1); eauto).
    assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2) by (eapply inv_step; [exact Iv | exact A12 | lia]).
    apply IHt with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk); auto. intros rho3 n3 At A3 Le3 H1.
    apply IHu with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk); auto. { eapply inv_step; eauto. }
    intros rho4 n4 Af A4 Le4 H2.
    assert (A24 : agree rho2 rho4 n2) by (eapply (agree_trans rho2 rho3 rho4 n2 n3); eauto).
    apply HK.
    + eapply (agree_trans rho rho2 rho4 nxt n2); [exact A12 | exact A24 | lia].
    + lia.
    + cbn [at_ok]. refine (conj eq_refl (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      * rewrite (aval_agree rho2 rho4 n2 X A24) by (eapply atom_lt_mono; [exact LX | lia]).
        rewrite (aval_agree rho1 rho2 n1 X A2 LX). exact VX.
      * rewrite (aval_agree rho2 rho4 n2 Y A24 LY). exact VY.
      * eapply atom_lt_mono; [exact LX | lia].
      * eapply atom_lt_mono; [exact LY | lia].
      * eapply at_ok_mono; [exact H1 | exact A4 | lia].
      * exact H2.
  - apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wb Wt].
    apply (cbval_ok b) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 X A1 Le1 LX VX.
    apply IHt with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk); auto. { eapply inv_step; eauto. }
    intros rho2 n2 At A2 Le2 H1.
    apply IHu with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk); auto. { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    intros rho3 n3 Af A3 Le3 H2.
    assert (A13 : agree rho1 rho3 n1) by (eapply (agree_trans rho1 rho2 rho3 n1 n2); eauto).
    apply HK.
    + eapply (agree_trans rho rho1 rho3 nxt n1); [exact A1 | exact A13 | lia].
    + lia.
    + cbn [at_ok]. refine (conj eq_refl (conj eq_refl (conj _ (conj _ (conj _ _))))).
      * rewrite (aval_agree rho1 rho3 n1 X A13 LX). exact VX.
      * eapply atom_lt_mono; [exact LX | lia].
      * eapply at_ok_mono; [exact H1 | exact A3 | lia].
      * exact H2.
Qed.

Lemma citem_ok : forall x cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk, wfi rk x = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' -> aval rho' a = Some (ival cenv benv renv denv M x) ->
     evalk P f rho' M (K a n') v M') ->
  evalk P f rho M (citem gidf g mv x cenvA benvA renvA envA nxt K) v M'.
Proof.
  intros [c|e] cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk W Iv Rt HK; cbn [citem wfi ival] in *.
  - apply andb_true_iff in W as [Wc Fl].
    eapply ccnt_ok; [exact Wc | exact (cmpc_wb cbs c Fl) | exact Iv | exact Rt | exact HK].
  - eapply cexp_ok; [exact W | exact Iv | exact Rt | exact HK].
Qed.

Lemma cpick_ok : forall T At i cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk, at_ok rho nxt cenv benv renv denv M T At ->
  wf_mt rk T = true -> inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' ->
     aval rho' a = Some (ival cenv benv renv denv M (ith (fst (mt_sel cenv benv renv denv M T) ++ snd (mt_sel cenv benv renv denv M T)) i)) ->
     evalk P f rho' M (K a n') v M') ->
  evalk P f rho M (cpick gidf g mv At i cenvA benvA renvA envA nxt K) v M'.
Proof.
  induction T as [c w | cc a b t IHt u IHu | b t IHt u IHu]; intros At i cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk H W Iv Rt HK;
    destruct At as [c' w' | cc' X Y A1 A2]; cbn [at_ok wf_mt mt_sel cpick] in *; try contradiction.
  - destruct H as [-> ->]. eapply citem_ok; [apply wfi_ith; exact W | exact Iv | exact Rt | exact HK].
  - destruct H as (-> & VX & VY & LX & LY & H1 & H2).
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt].
    eapply IHt; [exact H1 | exact Wt | exact Iv | exact Rt |]. intros rho1 n1 Xa A1' Le1 LXa VXa.
    eapply IHu; [eapply at_ok_mono; eauto | exact Wf | eapply inv_step; eauto | exact Rt |].
    intros rho2 n2 Ya A2' Le2 LYa VYa.
    assert (A12 : agree rho rho2 nxt) by (eapply (agree_trans rho rho1 rho2 nxt n1); eauto).
    eapply K_sel.
    + rewrite (aval_agree rho rho2 nxt X A12 LX). exact VX.
    + rewrite (aval_agree rho rho2 nxt Y A12 LY). exact VY.
    + rewrite (aval_agree rho1 rho2 n1 Xa A2' LXa). exact VXa.
    + exact VYa.
    + apply HK.
      * apply agree_set1; [exact A12 | lia].
      * lia.
      * simpl. lia.
      * cbn [aval]. rewrite PTree.gss. destruct (cmp_sem _ _ _); reflexivity.
  - destruct H as (-> & -> & VX & LX & H1 & H2).
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wb Wt].
    eapply IHu; [exact H2 | exact Wf | exact Iv | exact Rt |]. intros rho1 n1 Xa A1' Le1 LXa VXa.
    eapply IHt; [eapply at_ok_mono; eauto | exact Wt | eapply inv_step; eauto | exact Rt |].
    intros rho2 n2 Ya A2' Le2 LYa VYa.
    assert (A12 : agree rho rho2 nxt) by (eapply (agree_trans rho rho1 rho2 nxt n1); eauto).
    eapply K_sel.
    + rewrite (aval_agree rho rho2 nxt X A12 LX). exact VX.
    + reflexivity.
    + rewrite (aval_agree rho1 rho2 n1 Xa A2' LXa). exact VXa.
    + exact VYa.
    + apply HK.
      * apply agree_set1; [exact A12 | lia].
      * lia.
      * simpl. lia.
      * cbn [aval]. rewrite PTree.gss, b2i_eq0. destruct (denote_b _ _ _ _ renv _ _ _); reflexivity.
Qed.

Lemma cposs_ok : forall n T At i cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk, at_ok rho nxt cenv benv renv denv M T At ->
  wf_mt rk T = true -> inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  (forall rho' n' Xs, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') Xs ->
     avals rho' Xs = Some (map (fun j => ival cenv benv renv denv M (ith (fst (mt_sel cenv benv renv denv M T) ++ snd (mt_sel cenv benv renv denv M T)) j))
                               (seq i n)) ->
     evalk P f rho' M (K Xs n') v M') ->
  evalk P f rho M (cposs gidf g mv At i n cenvA benvA renvA envA nxt K) v M'.
Proof.
  induction n as [|n IH]; intros T At i cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk H W Iv Rt HK; cbn [cposs]; cbv zeta.
  - apply HK; [apply agree_refl | lia | constructor | reflexivity].
  - set (x := ith (fst (at_first At) ++ snd (at_first At)) i).
    assert (Wx : wfi rk x = true).
    { unfold x. apply wfi_ith. apply (at_first_leaf T At rho nxt cenv benv renv denv M (fun c w => forallb (wfi rk) (c ++ w)) H).
      apply wf_mt_leaves. exact W. }
    assert (CONT : forall X rho1 n1, agree rho rho1 nxt -> Pos.le nxt n1 -> atom_lt X n1 ->
              aval rho1 X = Some (ival cenv benv renv denv M (ith (fst (mt_sel cenv benv renv denv M T) ++ snd (mt_sel cenv benv renv denv M T)) i)) ->
              evalk P f rho1 M (cposs gidf g mv At (S i) n cenvA benvA renvA envA n1 (fun Xs n2 => K (X :: Xs) n2)) v M').
    { intros X rho1 n1 A1 Le1 LX VX. eapply (IH T); [eapply at_ok_mono; eauto | exact W | eapply inv_step; eauto | exact Rt |].
      intros rho2 n2 Xs A2 Le2 LXs VXs. apply HK.
      + eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
      + lia.
      + constructor; [eapply atom_lt_mono; [exact LX | lia] | exact LXs].
      + cbn [avals seq map]. rewrite (aval_agree rho1 rho2 n1 X A2 LX), VX, VXs. reflexivity. }
    destruct (at_all (fun c w => same_i (ith (c ++ w) i) x) At) eqn:SH.
    + eapply citem_ok; [exact Wx | exact Iv | exact Rt |].
      intros rho1 n1 X A1 Le1 LX VX. apply CONT; auto. rewrite VX. f_equal. f_equal. symmetry.
      apply same_i_eq. rewrite (at_all_eq T At rho nxt cenv benv renv denv M _ H) in SH.
      exact (mt_all_sel T (fun c w => same_i (ith (c ++ w) i) x) cenv benv renv denv M SH).
    + eapply (cpick_ok T); [exact H | exact W | exact Iv | exact Rt |]. intros rho1 n1 X A1 Le1 LX VX. apply CONT; auto.
Qed.

Lemma map_ith_seq : forall (F : item -> i63) (l l0 : list item),
  map (fun j => F (ith (l0 ++ l) j)) (seq (length l0) (length l)) = map F l.
Proof.
  intros F l. induction l as [|x l IH]; intros l0; cbn [length seq map]; [reflexivity|].
  f_equal.
  - unfold ith. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - specialize (IH (l0 ++ [x])). rewrite <- app_assoc in IH. rewrite length_app in IH. cbn [length app] in IH.
    rewrite Nat.add_1_r in IH. exact IH.
Qed.

Lemma ival_items_c : forall ccs cenv benv renv denv M, map (ival cenv benv renv denv M) (items_c ccs) = map ofn (denote_cs cs rec cenv benv renv denv M ccs).
Proof. induction ccs as [|c rr IH]; intros; cbn [items_c map denote_cs ival]; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma ival_items_s : forall es l cenv benv renv denv M, items_s es = Some l ->
  map (ival cenv benv renv denv M) l = flat_map vflat (denote_es cs rec cenv benv renv denv M es).
Proof.
  induction es as [|e rr IH | b rr IH | x rr IH]; intros l cenv benv renv denv M IS; cbn [items_s] in IS; [injection IS as <-; reflexivity | | discriminate | discriminate].
  destruct (items_s rr) as [l'|] eqn:E; [|discriminate]. cbn [option_map] in IS. injection IS as <-.
  cbn [map denote_es ival ofv]. rewrite (IH l' cenv benv renv denv M eq_refl). reflexivity.
Qed.
Lemma kinds_items : forall es l cenv benv renv denv M {rk}, items_s es = Some l ->
  map kind_of (denote_es cs rec cenv benv renv denv M es) = kinds_s rk es.
Proof.
  induction es as [|e rr IH | b rr IH | x rr IH]; intros l cenv benv renv denv M rk IS; cbn [items_s] in IS; [reflexivity | | discriminate | discriminate].
  destruct (items_s rr) as [l'|] eqn:E; [|discriminate]. cbn [denote_es map kind_of kinds_s]. f_equal. eapply IH; eauto.
Qed.
Lemma len_flat_items : forall es l cenv benv renv denv M, items_s es = Some l ->
  length (flat_map vflat (denote_es cs rec cenv benv renv denv M es)) = len_s es.
Proof.
  induction es as [|e rr IH | b rr IH | x rr IH]; intros l cenv benv renv denv M IS; cbn [items_s] in IS; [reflexivity | | discriminate | discriminate].
  destruct (items_s rr) as [l'|] eqn:E; [|discriminate]. cbn [denote_es flat_map vflat app length len_s]. f_equal. eapply IH; eauto.
Qed.
Lemma len_items_c : forall ccs, length (items_c ccs) = len_c ccs.
Proof. induction ccs as [|c rr IH]; cbn [items_c length len_c]; auto. Qed.
Lemma len_items_s : forall es l, items_s es = Some l -> length l = len_s es.
Proof.
  induction es as [|e rr IH | b rr IH | x rr IH]; intros l IS; cbn [items_s] in IS; [injection IS as <-; reflexivity | | discriminate | discriminate].
  destruct (items_s rr) as [l'|] eqn:E; [|discriminate]. cbn [option_map] in IS. injection IS as <-.
  cbn [length len_s]. rewrite (IH l' eq_refl). reflexivity.
Qed.
Lemma wfi_items_c : forall ccs rk, wfcs (sigsv cbs) r mok nx k rk ccs = true -> all_c (fun c => (cmaxv (ub (sigsv cbs)) (snd (snd (sigsv cbs))) c <? 9223372036854775808)%Z) ccs = true -> forallb (wfi rk) (items_c ccs) = true.
Proof.
  induction ccs as [|c rr IH]; intros rk W F; cbn [items_c forallb wfcs all_c wfi] in *; auto.
  apply andb_true_iff in W as [W1 W2]. apply andb_true_iff in F as [F1 F2]. rewrite W1, F1, IH; auto.
Qed.
Lemma wfi_items_s : forall es l rk, items_s es = Some l -> wfs (sigsv cbs) r mok nx k rk es = true -> forallb (wfi rk) l = true.
Proof.
  induction es as [|e rr IH | b rr IH | x rr IH]; intros l rk IS W; cbn [items_s] in IS; [injection IS as <-; reflexivity | | discriminate | discriminate].
  destruct (items_s rr) as [l'|] eqn:E; [|discriminate]. cbn [option_map] in IS. injection IS as <-.
  cbn [wfs] in W. apply andb_true_iff in W as [W1 W2]. cbn [forallb wfi]. rewrite W1, (IH l' rk eq_refl W2). reflexivity.
Qed.

Lemma avals_split : forall rho Xs l1 l2, avals rho Xs = Some (l1 ++ l2) ->
  avals rho (firstn (length l1) Xs) = Some l1 /\ avals rho (skipn (length l1) Xs) = Some l2.
Proof.
  intros rho Xs. induction Xs as [|x Xs IH]; intros l1 l2 V.
  - destruct l1 as [|a l1]; simpl in *; [split; [reflexivity | exact V] | discriminate].
  - cbn [avals] in V. destruct (aval rho x) as [vx|] eqn:Ex; [|discriminate].
    destruct (avals rho Xs) as [vs|] eqn:Exs; [|discriminate].
    destruct l1 as [|a l1]; cbn [length firstn skipn app] in V |- *.
    + split; [reflexivity|]. cbn [avals]. rewrite Ex, Exs. exact V.
    + injection V as Ea Evs. subst a. destruct (IH l1 l2 (f_equal Some Evs)) as [H1 H2].
      cbn [avals]. rewrite Ex, H1. split; [reflexivity | exact H2].
Qed.

Lemma cwrites_ok : forall n Ws wv rho M kk v M', (length Ws <= n)%nat -> avals rho Ws = Some wv ->
  evalk P f rho (wmem wv M) kk v M' -> evalk P f rho M (cwrites Ws kk) v M'.
Proof.
  induction n as [|n IH]; intros Ws wv rho M kk v M' L V E.
  - destruct Ws as [|w Ws]; cbn [length] in L; [|lia]. cbn [avals] in V. injection V as <-. exact E.
  - destruct Ws as [|ah [|ai [|av Ws]]]; cbn [cwrites] in *.
    + cbn [avals] in V. injection V as <-. exact E.
    + cbn [avals] in V. destruct (aval rho ah); [|discriminate]. injection V as <-. exact E.
    + cbn [avals] in V. destruct (aval rho ah); [|discriminate]. destruct (aval rho ai); [|discriminate]. injection V as <-. exact E.
    + cbn [avals] in V. destruct (aval rho ah) as [vh|] eqn:Eh; [|discriminate]. destruct (aval rho ai) as [vi|] eqn:Ei; [|discriminate].
      destruct (aval rho av) as [vv|] eqn:Ev; [|discriminate]. destruct (avals rho Ws) as [vs|] eqn:Es; [|discriminate].
      injection V as <-. cbn [length] in L.
      apply (IH Ws vs rho M (Ekst ah ai av kk) v M'); [lia | exact Es |].
      eapply K_st; [exact Eh | exact Ei | exact Ev | exact E].
Qed.

Lemma skel_denote : forall mm ws cenv benv renv denv M, skel mm = Some ws ->
  denote_m cs rec recm cenv benv renv denv M mm = wmem (map (ival cenv benv renv denv M) ws) M.
Proof.
  induction mm as [| h i x mm IH | e mm IH | m1 IH1 m2 IH2 | c a b m1 IH1 m2 IH2 | ccs args mm IH | fi ccs args mm IH | c m0 IH0 m1 IH1
                 | b m1 IH1 m2 IH2 | b mm IH | h i x mm IH | c mm IH | o args mm IH | h i x mm IH | x mm IH | x mm IH | sj x mm IH | p mm IH | p mm IH | fi ccs args p]; intros ws cenv benv renv denv M Sk; cbn [skel] in Sk; try discriminate.
  - injection Sk as <-. reflexivity.
  - destruct (skel mm) as [w|] eqn:E; [|discriminate]. cbn [option_map] in Sk. injection Sk as <-.
    cbn [denote_m map wmem ival]. rewrite (IH w cenv benv renv denv M eq_refl). reflexivity.
Qed.

Lemma skel_wf : forall mm ws rk, skel mm = Some ws -> wfm (sigsv cbs) r rm mok nx k rk mm = true -> forallb (wfi rk) ws = true.
Proof.
  induction mm as [| h i x mm IH | e mm IH | m1 IH1 m2 IH2 | c a b m1 IH1 m2 IH2 | ccs args mm IH | fi ccs args mm IH | c m0 IH0 m1 IH1
                 | b m1 IH1 m2 IH2 | b mm IH | h i x mm IH | c mm IH | o args mm IH | h i x mm IH | x mm IH | x mm IH | sj x mm IH | p mm IH | p mm IH | fi ccs args p]; intros ws rk Sk W; cbn [skel] in Sk; try discriminate.
  - injection Sk as <-. reflexivity.
  - destruct (skel mm) as [w|] eqn:E; [|discriminate]. cbn [option_map] in Sk. injection Sk as <-.
    cbn [wfm] in W. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wh Wi].
    cbn [forallb wfi]. rewrite Wh, Wi, Wx. cbn [andb]. apply IH with (rk := rk); auto.
Qed.

Lemma mt_e_sel : forall e T cenv benv renv denv M rk, mt_e e = Some T -> wf (sigsv cbs) r mok nx k rk e = true ->
  wf_mt rk T = true /\
  exists ccs args l, items_s args = Some l /\ mt_sel cenv benv renv denv M T = (items_c ccs ++ l, []) /\
    denote_e cs rec cenv benv renv denv M e = rec (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M /\
    r = true /\ len_c ccs = nx /\ kinds_s rk args = k /\ rec_ok (sigsv cbs) ccs = true.
Proof.
  induction e as [i | n | o a IHa b IHb | c a IHa b IHb t IHt u IHu | e1 IH1 e2 IH2 | h IHh i IHi | ccs args | fi ccs args
                 | c e0 IH0 e1 IH1 | b t IHt u IHu | b e IHe | h IHh i IHi | c e IHe | i0 j0 | x e IHe | x e IHe | o args IHa | h IHh | h IHh i IHi | sj x e IHe]; intros T cenv benv renv denv M rk MT W;
    cbn [mt_e] in MT; try discriminate.
  - destruct (mt_e t) as [t'|] eqn:Et; [|discriminate]. destruct (mt_e u) as [u'|] eqn:Eu; [|discriminate].
    injection MT as <-. cbn [wf] in W. apply andb_true_iff in W as [W Wu]. apply andb_true_iff in W as [W Wt].
    apply andb_true_iff in W as [Wa Wb].
    destruct (IHt t' cenv benv renv denv M rk eq_refl Wt) as [WT1 S1]. destruct (IHu u' cenv benv renv denv M rk eq_refl Wu) as [WT2 S2].
    split; [cbn [wf_mt]; rewrite Wa, Wb, WT1, WT2; reflexivity|].
    cbn [mt_sel denote_e]. destruct (cmp_sem _ _ _); assumption.
  - destruct (items_s args) as [l|] eqn:IS; [|discriminate]. cbn [option_map] in MT. injection MT as <-.
    cbn [wf] in W. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply Nat.eqb_eq in Wn. apply kinds_eqb_eq in Wk. split.
    + cbn [wf_mt]. rewrite app_nil_r, forallb_app, wfi_items_c, (wfi_items_s args l rk IS); auto using rec_ok_items.
    + exists ccs, args, l. split; [exact IS|]. split; [reflexivity|]. split; [reflexivity|]. auto.
  - destruct (mt_e t) as [t'|] eqn:Et; [|discriminate]. destruct (mt_e u) as [u'|] eqn:Eu; [|discriminate].
    injection MT as <-. cbn [wf] in W. apply andb_true_iff in W as [W Wu]. apply andb_true_iff in W as [Wb Wt].
    destruct (IHt t' cenv benv renv denv M rk eq_refl Wt) as [WT1 S1]. destruct (IHu u' cenv benv renv denv M rk eq_refl Wu) as [WT2 S2].
    split; [cbn [wf_mt]; rewrite Wb, WT1, WT2; reflexivity|].
    cbn [mt_sel denote_e]. destruct (denote_b _ _ _ _ renv _ _ _); assumption.
Qed.

Lemma mt_m_sel : forall m T cenv benv renv denv M rk, mt_m m = Some T -> wfm (sigsv cbs) r rm mok nx k rk m = true ->
  wf_mt rk T = true /\
  exists ccs args l mm ws, items_s args = Some l /\ mt_sel cenv benv renv denv M T = (items_c ccs ++ l, ws) /\ skel mm = Some ws /\
    denote_m cs rec recm cenv benv renv denv M m = recm (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args)
                                                 (denote_m cs rec recm cenv benv renv denv M mm) /\
    rm = true /\ len_c ccs = nx /\ kinds_s rk args = k /\ rec_ok (sigsv cbs) ccs = true.
Proof.
  induction m as [| h i x m IH | e m IH | m1 IH1 m2 IH2 | c a b m1 IH1 m2 IH2 | ccs args m IH | fi ccs args m IH | c m0 IH0 m1 IH1
                 | b m1 IH1 m2 IH2 | b m IH | h i x m IH | c m IH | o args m IH | h i x m IH | x m IH | x m IH | sj x m IH | p m IH | p m IH | fi ccs args p]; intros T cenv benv renv denv M rk MT W; cbn [mt_m] in MT; try discriminate.
  - destruct (mt_m m1) as [t'|] eqn:E1; [|discriminate]. destruct (mt_m m2) as [u'|] eqn:E2; [|discriminate].
    injection MT as <-. cbn [wfm] in W. apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [W Wm1].
    apply andb_true_iff in W as [Wa Wb].
    destruct (IH1 t' cenv benv renv denv M rk eq_refl Wm1) as [WT1 S1]. destruct (IH2 u' cenv benv renv denv M rk eq_refl Wm2) as [WT2 S2].
    split; [cbn [wf_mt]; rewrite Wa, Wb, WT1, WT2; reflexivity|].
    cbn [mt_sel denote_m]. destruct (cmp_sem _ _ _); assumption.
  - destruct (items_s args) as [l|] eqn:IS; [|discriminate]. destruct (skel m) as [w|] eqn:Sk; [|discriminate].
    injection MT as <-.
    cbn [wfm] in W. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply Nat.eqb_eq in Wn. apply kinds_eqb_eq in Wk. split.
    + cbn [wf_mt]. rewrite !forallb_app, wfi_items_c, (wfi_items_s args l rk IS), (skel_wf m w rk Sk Wm); auto using rec_ok_items.
    + exists ccs, args, l, m, w. split; [exact IS|]. split; [reflexivity|]. split; [exact Sk|]. split; [reflexivity|]. auto.
  - destruct (mt_m m1) as [t'|] eqn:E1; [|discriminate]. destruct (mt_m m2) as [u'|] eqn:E2; [|discriminate].
    injection MT as <-. cbn [wfm] in W. apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [Wb Wm1].
    destruct (IH1 t' cenv benv renv denv M rk eq_refl Wm1) as [WT1 S1]. destruct (IH2 u' cenv benv renv denv M rk eq_refl Wm2) as [WT2 S2].
    split; [cbn [wf_mt]; rewrite Wb, WT1, WT2; reflexivity|].
    cbn [mt_sel denote_m]. destruct (denote_b _ _ _ _ renv _ _ _); assumption.
Qed.

(** the merged call computes what the chain of tests and calls computes *)
Lemma mrg_e_ok : forall e kk cenvA benvA renvA envA cenv benv renv denv nxt rho M rk, wf (sigsv cbs) r mok nx k rk e = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk -> evalk P f rho M kk (denote_e cs rec cenv benv renv denv M e) M ->
  evalk P f rho M (mrg_e gidf g mv e cenvA benvA renvA envA nxt kk) (denote_e cs rec cenv benv renv denv M e) M.
Proof.
  intros e kk cenvA benvA renvA envA cenv benv renv denv nxt rho M rk W Iv Rt PL. unfold mrg_e.
  destruct (mt_e e) as [T|] eqn:MT; [|exact PL]. destruct (mt_ok T) eqn:OK; [|exact PL].
  destruct (mt_e_sel e T cenv benv renv denv M rk MT W) as (WT & ccs & args & l & IS & SEL & DEN & Wr & Lc & Ls & Fl).
  unfold mt_ok in OK. apply andb_true_iff in OK as [LENS _].
  pose proof (mt_all_sel T _ cenv benv renv denv M LENS) as LS. rewrite SEL in LS. cbn beta in LS. cbn [fst snd] in LS.
  apply andb_true_iff in LS as [LS1 LS2]. apply Nat.eqb_eq in LS1, LS2.
  unfold cmt. eapply ctests_ok; [exact WT | exact Iv | exact Rt |].
  intros rho1 n1 At A1 Le1 H1.
  eapply (cposs_ok _ T); [exact H1 | exact WT | eapply inv_step; eauto | exact Rt |].
  intros rho2 n2 Xs A2 Le2 LXs VXs.
  rewrite SEL in VXs. cbn [fst snd] in VXs.
  assert (NP : mt_npos T = length ((items_c ccs ++ l) ++ [])) by (unfold mt_npos; lia).
  rewrite NP in VXs. pose proof (map_ith_seq (ival cenv benv renv denv M) ((items_c ccs ++ l) ++ []) []) as MS.
  cbn [app length] in MS. rewrite MS in VXs. rewrite app_nil_r, map_app, ival_items_c, (ival_items_s args l cenv benv renv denv M IS) in VXs.
  destruct (avals_split rho2 Xs _ _ VXs) as [V1 V2].
  assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2).
  { eapply inv_step; [exact Iv | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia]. }
  destruct I2 as (_ & _ & _ & _ & _ & _ & Cb & _ & H2 & _). destruct (H2 (Hrhp Wr)) as [Rm _].
  rewrite DEN. rewrite <- (firstn_skipn (length (map ofn (denote_cs cs rec cenv benv renv denv M ccs))) Xs).
  eapply loop_call_ok; [exact Wr | rewrite len_denote_cs; exact Lc | rewrite (@kinds_items args l cenv benv renv denv M rk IS); exact Ls
                       | eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto) | exact Rm | exact V1 | exact V2].
Qed.

Lemma mrg_m_ok : forall m kk cenvA benvA renvA envA cenv benv renv denv nxt rho M rk, wfm (sigsv cbs) r rm mok nx k rk m = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk -> evalk P f rho M kk 0%uint63 (denote_m cs rec recm cenv benv renv denv M m) ->
  evalk P f rho M (mrg_m gidf g mv m cenvA benvA renvA envA nxt kk) 0%uint63 (denote_m cs rec recm cenv benv renv denv M m).
Proof.
  intros m kk cenvA benvA renvA envA cenv benv renv denv nxt rho M rk W Iv Rt PL. unfold mrg_m.
  destruct (mt_m m) as [T|] eqn:MT; [|exact PL]. destruct (mt_ok T) eqn:OK; [|exact PL].
  destruct (mt_m_sel m T cenv benv renv denv M rk MT W) as (WT & ccs & args & l & mm & ws & IS & SEL & SK & DEN & Wr & Lc & Ls & Fl).
  unfold mt_ok in OK. apply andb_true_iff in OK as [LENS _].
  pose proof (mt_all_sel T _ cenv benv renv denv M LENS) as LS. rewrite SEL in LS. cbn beta in LS. cbn [fst snd] in LS.
  apply andb_true_iff in LS as [LS1 LS2]. apply Nat.eqb_eq in LS1, LS2.
  unfold cmt. eapply ctests_ok; [exact WT | exact Iv | exact Rt |].
  intros rho1 n1 At A1 Le1 H1.
  eapply (cposs_ok _ T); [exact H1 | exact WT | eapply inv_step; eauto | exact Rt |].
  intros rho2 n2 Xs A2 Le2 LXs VXs.
  rewrite SEL in VXs. cbn [fst snd] in VXs.
  assert (NP : mt_npos T = length ((items_c ccs ++ l) ++ ws)) by (unfold mt_npos; lia).
  rewrite NP in VXs. pose proof (map_ith_seq (ival cenv benv renv denv M) ((items_c ccs ++ l) ++ ws) []) as MS.
  cbn [app length] in MS. rewrite MS in VXs. rewrite !map_app, ival_items_c, (ival_items_s args l cenv benv renv denv M IS) in VXs.
  assert (LC : length (map ofn (denote_cs cs rec cenv benv renv denv M ccs) ++ flat_map vflat (denote_es cs rec cenv benv renv denv M args)) = mt_ncall T).
  { rewrite length_app, length_map, len_denote_cs, (len_flat_items args l cenv benv renv denv M IS), <- LS1, length_app, len_items_c, (len_items_s args l IS). reflexivity. }
  rewrite <- app_assoc in VXs. rewrite app_assoc in VXs.
  destruct (avals_split rho2 Xs _ _ VXs) as [V1 V2]. rewrite LC in V1, V2.
  destruct (avals_split rho2 (firstn (mt_ncall T) Xs) _ _ V1) as [V11 V12].
  assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2).
  { eapply inv_step; [exact Iv | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia]. }
  destruct I2 as (_ & _ & _ & _ & _ & _ & Cb & _ & H2 & _). destruct (H2 (Hrmhp Wr)) as [Rm _].
  eapply cwrites_ok; [apply le_n | exact V2 |].
  rewrite DEN, (skel_denote mm ws cenv benv renv denv M SK).
  rewrite <- (firstn_skipn (length (map ofn (denote_cs cs rec cenv benv renv denv M ccs))) (firstn (mt_ncall T) Xs)).
  eapply loopm_call_ok; [exact Wr | rewrite len_denote_cs; exact Lc | rewrite (@kinds_items args l cenv benv renv denv M rk IS); exact Ls
                        | eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto) | exact Rm | exact V11 | exact V12].
Qed.
End Merge.

Lemma ctail_ok : forall e cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs, wf (sigsv cbs) r mok nx k rk e = true -> inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  evalk P f rho M (ctail gidf g mv e cenvA benvA renvA envA nxt) (denote_e cs rec cenv benv renv denv M e) M.
Proof.
  induction e as [i | n | o a IHa b IHb | c a IHa b IHb t IHt u IHu | e1 IH1 e2 IH2 | h IHh i IHi | ccs args | fi ccs args
                 | c e0 IH0 e1 IH1 | b t IHt u IHu | b e IHe | h IHh i IHi | c e IHe | i0 j0 | x e IHe | x e IHe | o args IHa | h IHh | h IHh i IHi | sj x e IHe];
    intros cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs W Iv Rt; cbn [ctail] in *.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - (* SIf *) eapply mrg_e_ok; [exact W | exact Iv | exact Rt |].
    cbn [wf] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt].
    apply andb_true_iff in W as [Wa Wb].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    assert (VA2 : aval rho2 A = Some (denote_e cs rec cenv benv renv denv M a)) by (rewrite (aval_agree rho1 rho2 n1); eauto).
    eapply K_if.
    + exact VA2.
    + eauto.
    + cbn [denote_e]. assert (I2' : forall n', Pos.le n2 n' -> inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n') by (intros n' L'; eapply inv_step; [exact I2 | apply agree_refl | exact L']).
      destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)); eauto using after_le.
  - (* SLet *) cbn [wf] in W. apply andb_true_iff in W as [W1 W2].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_e]. apply IH2 with (rk := rk) (cbs := cbs); auto. apply inv_let; auto. eapply inv_step; eauto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - (* SRec *) cbn [wf] in W. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    destruct (Hrec Wr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    rewrite Hf in F. injection F as <-.
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1 & _). destruct (H1 (Hrhp Wr)) as [Rm _].
    cbn [denote_e]. eapply K_loop; eauto.
    simpl. rewrite (A2 mv Mv1), Rm.
    rewrite (avals_app rho2 Cs As _ _ (eq_trans (avals_agree rho1 rho2 n1 Cs A2 LCs) VCs) VAs). reflexivity.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - (* SMatch *) cbn [wf] in W. apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
    cbn [denote_e]. destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl. apply IH0 with (rk := rk) (cbs := cbs); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto. apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
  - (* SIfB *) eapply mrg_e_ok; [exact W | exact Iv | exact Rt |].
    cbn [wf] in W. apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wb Wt].
    apply (ccond_ok b) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. cbn [denote_e]. rewrite Hb. apply IHt with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. cbn [denote_e]. rewrite Hb. apply IHu with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
  - (* SLetB *) cbn [wf] in W. apply andb_true_iff in W as [Wb We].
    apply (cbval_ok b) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_e]. apply IHe with (rk := rk) (cbs := cbs); auto. apply inv_blet; auto. eapply inv_step; eauto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - (* SLetC *) cbn [wf] in W. apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wc Wl].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnt_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply letc_okv_wb; exact Wl. }
    intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_e]. apply IHe with (rk := rk) (cbs := cpush_let (sigsv cbs) c :: cbs); auto. apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto].
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - (* SLetR *) cbn [wf] in W. apply andb_true_iff in W as [Wx We].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    cbn [denote_e]. apply IHe with (rk := rtype rk x :: rk) (cbs := cbs); auto. apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs].
    apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto].
  - (* SMatchR *) cbn [wf] in W. apply andb_true_iff in W as [Wx We].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    cbn [denote_e]. rewrite rmatch_eq. apply IHe with (rk := rk) (cbs := cbs); auto. apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs].
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. auto.
  - (* SSplitR *) cbn [wf] in W. apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M x) = KRec sj) by (rewrite <- Ex; eapply kind_denote_r; eauto).
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    cbn [denote_e]. rewrite rsplit_eq. apply IHe with (rk := rev (RJ sj) ++ rk) (cbs := cbs); auto. apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs].
    apply rsplit_typed; [exact Kx | exact Rt].
Qed.

(** a memory in tail position: the function's body returns 0 and ends with the memory the Rocq text makes *)
Lemma ctailm_ok : forall m cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs, wfm (sigsv cbs) r rm mok nx k rk m = true -> inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  evalk P f rho M (ctailm gidf g mv m cenvA benvA renvA envA nxt) 0%uint63 (denote_m cs rec recm cenv benv renv denv M m).
Proof.
  induction m as [| h i x m IH | e m IH | m1 IH1 m2 IH2 | c a b m1 IH1 m2 IH2 | ccs args m IH | fi ccs args m IH | c m0 IH0 m1 IH1
                 | b m1 IH1 m2 IH2 | b m IH | h i x m IH | c m IH | o args m IH | h i x m IH | x m IH | x m IH | sj x m IH | p m IH | p m IH | fi ccs args p];
    intros cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs W Iv Rt; cbn [ctailm] in *.
  - apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. reflexivity.
  - apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. reflexivity.
  - (* MLet *) cbn [wfm] in W. apply andb_true_iff in W as [We Wm].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_m]. apply IH with (rk := rk) (cbs := cbs); auto. apply inv_let; auto. eapply inv_step; eauto.
  - (* MLetM *) cbn [wfm] in W. apply andb_true_iff in W as [W1 W2].
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A1 Le1.
    cbn [denote_m]. apply IH2 with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
  - (* MIf *) eapply mrg_m_ok; [exact W | exact Iv | exact Rt |].
    cbn [wfm] in W. apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [W Wm1].
    apply andb_true_iff in W as [Wa Wb].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    assert (VA2 : aval rho2 A = Some (denote_e cs rec cenv benv renv denv M a)) by (rewrite (aval_agree rho1 rho2 n1); eauto).
    eapply K_if.
    + exact VA2.
    + eauto.
    + cbn [denote_m]. assert (I2' : forall n', Pos.le n2 n' -> inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n') by (intros n' L'; eapply inv_step; [exact I2 | apply agree_refl | exact L']).
      destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)); eauto using after_le.
  - (* MRec *) cbn [wfm] in W. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws].
    apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk].
    apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    destruct (Hrecm Wr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args)
                       (denote_m cs rec recm cenv benv renv denv M m)) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    rewrite Hf in F. injection F as <-.
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1 & _). destruct (H1 (Hrmhp Wr)) as [Rm _].
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    cbn [denote_m]. eapply K_loop; eauto.
    simpl. rewrite (A3 mv) by lia. rewrite (A2 mv Mv1), Rm, (avals_app rho3 Cs As _ _ VC3 VA3). reflexivity.
  - apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. reflexivity.
  - (* MMatch *) cbn [wfm] in W. apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
    cbn [denote_m]. destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl. apply IH0 with (rk := rk) (cbs := cbs); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto. apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
  - (* MIfB *) eapply mrg_m_ok; [exact W | exact Iv | exact Rt |].
    cbn [wfm] in W. apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [Wb Wm1].
    apply (ccond_ok b) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. cbn [denote_m]. rewrite Hb. apply IH1 with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. cbn [denote_m]. rewrite Hb. apply IH2 with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
  - (* MLetB *) cbn [wfm] in W. apply andb_true_iff in W as [Wb Wm].
    apply (cbval_ok b) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_m]. apply IH with (rk := rk) (cbs := cbs); auto. apply inv_blet; auto. eapply inv_step; eauto.
  - apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. reflexivity.
  - (* MLetC *) cbn [wfm] in W. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [Wc Wl].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnt_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply letc_okv_wb; exact Wl. }
    intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_m]. apply IH with (rk := rk) (cbs := cpush_let (sigsv cbs) c :: cbs); auto. apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto].
  - apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. reflexivity.
  - apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. reflexivity.
  - (* MLetR *) cbn [wfm] in W. apply andb_true_iff in W as [Wx Wm].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    cbn [denote_m]. apply IH with (rk := rtype rk x :: rk) (cbs := cbs); auto. apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs].
    apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto].
  - (* MMatchR *) cbn [wfm] in W. apply andb_true_iff in W as [Wx Wm].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    cbn [denote_m]. rewrite rmatch_eq. apply IH with (rk := rk) (cbs := cbs); auto. apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs].
  - (* MSplitR *) cbn [wfm] in W. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M x) = KRec sj) by (rewrite <- Ex; eapply kind_denote_r; eauto).
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    cbn [denote_m]. rewrite rsplit_eq. apply IH with (rk := rev (RJ sj) ++ rk) (cbs := cbs); auto. apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs].
    apply rsplit_typed; [exact Kx | exact Rt].
  - (* MMatchP *) cbn [wfm] in W. apply andb_true_iff in W as [Wp Wm].
    eapply (proj2 cmem_cpv_ok p dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Wp | exact Iv | exact Rt | ].
    intros rho1 n1 A A1 Le1 LA VA. cbn [denote_m]. destruct (denote_pv cs rec recm dpair cenv benv renv denv M p) as [x0 s0] eqn:Ep.
    cbn [fst snd] in VA |- *.
    apply IH with (rk := rk) (cbs := cbs); auto. apply inv_let; [eapply inv_step; eauto | exact VA | exact LA].
  - (* MLetP *) cbn [wfm] in W. apply andb_true_iff in W as [Wp Wm].
    eapply (proj2 cmem_cpv_ok p dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Wp | exact Iv | exact Rt | ].
    intros rho1 n1 A A1 Le1 LA VA. cbn [denote_m]. cbv zeta.
    apply IH with (rk := rk) (cbs := cbs); auto. apply inv_let; [eapply inv_step; eauto | exact VA | exact LA].
  - (* MCallP *) apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros. apply K_ret. reflexivity.
Qed.
(** a number made after memories, in tail position (no recursive call of a number or a memory in it: [r], [rm] false; the
    memory is there: [mok]): the body ends with its number and an end memory -- the last memory made, or the one the call at
    its end reaches.  Which end memory is reached depends only on the values the meaning works with (the call's arguments,
    the memory it is given), never on the rest of KQL's variables: so it is chosen before the environment *)
(* ---------------------------------------------------------------- a number and a memory (step 26) *)
(** a call of a function giving back a number and a memory: its KQL gives the number and ends with the memory *)

(** where a number and a memory is taken apart: the continuation gets the number's atom and the KQL memory is the pair's *)
Lemma cpv_ok : forall (recp : list nat -> list val -> mem -> (i63 * mem)%type) (rp : bool),
  (rp = true -> forall cvs vs M, length cvs = nx -> map kind_of vs = k -> rfits cvs ->
     runk P g (ofn cm :: map ofn cvs ++ flat_map vflat vs) M (fst (recp cvs vs M)) (snd (recp cvs vs M))) ->
  (rp = true -> hp = true) -> r = false -> rm = false -> mok = true ->
  forall p cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs, wfpv (sigsv cbs) false false true rp nx k rk p = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' ->
     aval rho' a = Some (fst (denote_pv cs rec recm recp cenv benv renv denv M p)) ->
     evalk P f rho' (snd (denote_pv cs rec recm recp cenv benv renv denv M p)) (K a n') v M') ->
  evalk P f rho M (cpv gidf g mv p cenvA benvA renvA envA nxt K) v M'.
Proof.
  intros recp rp Hrecp Hrphp Hr0 Hrm0 Hm1 p cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs W Iv Rt HK.
  refine (proj2 cmem_cpv_ok p recp rp Hrecp Hrphp cenvA benvA renvA envA cenv benv renv denv nxt K rho M v M' rk cbs _ Iv Rt HK).
  rewrite Hr0, Hrm0, Hm1. exact W.
Qed.

(** in tail position: the body returns the pair's number and ends with its memory *)
Lemma ctailp_ok : forall (recp : list nat -> list val -> mem -> (i63 * mem)%type) (rp : bool),
  (rp = true -> forall cvs vs M, length cvs = nx -> map kind_of vs = k -> rfits cvs ->
     runk P g (ofn cm :: map ofn cvs ++ flat_map vflat vs) M (fst (recp cvs vs M)) (snd (recp cvs vs M))) ->
  (rp = true -> hp = true) -> r = false -> rm = false -> mok = true ->
  forall p cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs, wfpv (sigsv cbs) false false true rp nx k rk p = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  evalk P f rho M (ctailp gidf g mv p cenvA benvA renvA envA nxt)
    (fst (denote_pv cs rec recm recp cenv benv renv denv M p)) (snd (denote_pv cs rec recm recp cenv benv renv denv M p)).
Proof.
  intros recp rp Hrecp Hrphp Hr0 Hrm0 Hm1.
  induction p as [e m | fi ccs args m | ccs args m | e p IH | c p IH | c p IH | x p IH | x p IH | m p IH
                 | c x y t IHt u IHu | c t IHt u IHu | c p0 IH0 p1 IH1 | p IHp q IHq | sj x p IH | fi ccs args p IH];
    intros cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs W Iv Rt; cbn [ctailp denote_pv].
  - (* PvMk *) cbn [wfpv] in W. apply andb_true_iff in W as [We Wm].
    assert (We' : wf (sigsv cbs) r mok nx k rk e = true) by (rewrite Hr0, Hm1; exact We).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 A2 Le2. apply K_ret. rewrite (aval_agree rho1 rho2 n1); [exact VA | exact A2 | exact LA].
  - (* PvCall *) pose proof W as W0. cbn [wfpv] in W0. unfold sigsv in W0. cbn [fst] in W0; rewrite nth_sigs in W0.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W0; [|discriminate W0].
    apply andb_true_iff in W0 as [W0 Wm]. apply andb_true_iff in W0 as [W0 Ws]. apply andb_true_iff in W0 as [W0 Wc].
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (rewrite Hr0, Hm1; exact Ws).
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (rewrite Hr0, Hm1; exact Wc).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    apply andb_true_iff in W0 as [W0 Wsh].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    assert (Wq : wfpv (sigsv cbs) r rm mok rp nx k rk (PvCall fi ccs args m) = true) by (rewrite Hr0, Hrm0, Hm1; exact W).
    destruct (pvcall_run fi ccs args m rk cbs cenv benv renv denv M gs h rp E Wq Rt Cb (denote_m cs rec recm cenv benv renv denv M m))
      as (fg & rho' & Fd & Bd & EVd).
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    eapply K_call; [exact Fd | apply avals_app; [exact VC3 | exact VA3] | exact Bd | exact EVd | ].
    apply K_ret. cbn [aval]. apply PTree.gss.
  - (* PvRec *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (rewrite Hr0, Hm1; exact Ws).
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (rewrite Hr0, Hm1; exact Wc).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3. cbv beta.
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1 & _). destruct (H1 (Hrphp Wr)) as [Rm _].
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    apply (loopx_call_ok rho3 Cs As (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args)
             (denote_m cs rec recm cenv benv renv denv M m)); [ | | exact VC3 | exact VA3].
    + apply Hrecp; [exact Wr | | |].
      * rewrite len_denote_cs. apply Nat.eqb_eq; auto.
      * erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto.
      * destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto).
    + rewrite (A3 mv) by lia. rewrite (A2 mv Mv1). exact Rm.
  - (* PvLet *) cbn [wfpv] in W. apply andb_true_iff in W as [We Wp].
    assert (We' : wf (sigsv cbs) r mok nx k rk e = true) by (rewrite Hr0, Hm1; exact We).
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (rk := rk) (cbs := cbs); auto. apply inv_let; auto. eapply inv_step; eauto.
  - (* PvLetB *) cbn [wfpv] in W. apply andb_true_iff in W as [Wc Wp].
    assert (Wc' : wfb (sigsv cbs) r mok nx k rk c = true) by (rewrite Hr0, Hm1; exact Wc).
    apply (cbval_ok c) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (rk := rk) (cbs := cbs); auto. apply inv_blet; auto. eapply inv_step; eauto.
  - (* PvLetC *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wp]. apply andb_true_iff in W as [Wc Wl].
    assert (Wc' : wfc (sigsv cbs) r mok nx k rk c = true) by (rewrite Hr0, Hm1; exact Wc).
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnt_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply letc_okv_wb; exact Wl. }
    intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (rk := rk) (cbs := cpush_let (sigsv cbs) c :: cbs); auto. apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto].
  - (* PvLetR *) cbn [wfpv] in W. apply andb_true_iff in W as [Wx Wp].
    assert (Wx' : wfr (sigsv cbs) r mok nx k rk x = true) by (rewrite Hr0, Hm1; exact Wx).
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    apply IH with (rk := rtype rk x :: rk) (cbs := cbs); auto. apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs].
    apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto].
  - (* PvMatchR *) cbn [wfpv] in W. apply andb_true_iff in W as [Wx Wp].
    assert (Wx' : wfr (sigsv cbs) r mok nx k rk x = true) by (rewrite Hr0, Hm1; exact Wx).
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    rewrite rmatch_eq. apply IH with (rk := rk) (cbs := cbs); auto. apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs].
  - (* PvLetM *) cbn [wfpv] in W. apply andb_true_iff in W as [Wm Wp].
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A1 Le1.
    apply IH with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
  - (* PvIf *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wx Wy].
    assert (Wx' : wf (sigsv cbs) r mok nx k rk x = true) by (rewrite Hr0, Hm1; exact Wx).
    assert (Wy' : wf (sigsv cbs) r mok nx k rk y = true) by (rewrite Hr0, Hm1; exact Wy).
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    assert (VA2 : aval rho2 A = Some (denote_e cs rec cenv benv renv denv M x)) by (rewrite (aval_agree rho1 rho2 n1); eauto).
    eapply K_if.
    + exact VA2.
    + eauto.
    + assert (I2' : forall n', Pos.le n2 n' -> inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n') by (intros n' L'; eapply inv_step; [exact I2 | apply agree_refl | exact L']).
      destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M x) (denote_e cs rec cenv benv renv denv M y)); eauto using after_le.
  - (* PvIfB *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wc Wt].
    assert (Wc' : wfb (sigsv cbs) r mok nx k rk c = true) by (rewrite Hr0, Hm1; exact Wc).
    apply (ccond_ok c) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply IHt with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply IHu with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
  - (* PvMatch *) cbn [wfpv] in W. apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
    destruct (nth c cenv O) as [|pr] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl. apply IH0 with (rk := rk) (cbs := cbs); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S pr))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S pr) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto. apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
  - (* PvMatchP *) cbn [wfpv] in W. apply andb_true_iff in W as [Wp Wq].
    apply (cpv_ok recp rp Hrecp Hrphp Hr0 Hrm0 Hm1 p) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA. cbv beta.
    destruct (denote_pv cs rec recm recp cenv benv renv denv M p) as [x0 s0] eqn:Ep. cbn [fst snd] in VA |- *.
    apply IHq with (rk := rk) (cbs := cbs); auto. apply inv_let; auto. eapply inv_step; eauto.
  - (* PvSplitR *) cbn [wfpv] in W. apply andb_true_iff in W as [W Wp]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    assert (Wx' : wfr (sigsv cbs) r mok nx k rk x = true) by (rewrite Hr0, Hm1; exact Wx).
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M x) = KRec sj) by (rewrite <- Ex; eapply kind_denote_r; eauto).
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    rewrite rsplit_eq. apply IH with (rk := rev (RJ sj) ++ rk) (cbs := cbs); auto. apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs].
    apply rsplit_typed; [exact Kx | exact Rt].
  - (* PvCallP *) pose proof W as W0. cbn [wfpv] in W0. unfold sigsv in W0. cbn [fst] in W0; rewrite nth_sigs in W0.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W0; [|discriminate W0].
    apply andb_true_iff in W0 as [W0 Wp]. apply andb_true_iff in W0 as [W0 Ws]. apply andb_true_iff in W0 as [W0 Wc].
    apply andb_true_iff in W0 as [W0 Wsh]. apply andb_true_iff in W0 as [W0 Wq]. apply andb_true_iff in W0 as [W0 Wsw]. apply andb_true_iff in W0 as [W0 Wr]. apply andb_true_iff in W0 as [W0 Wl].
    apply andb_true_iff in W0 as [W0 Wsm]. apply andb_true_iff in W0 as [W0 Wsp]. apply andb_true_iff in W0 as [Wn Wk].
    apply negb_true_iff in Wsw, Wr. destruct (sq gs) as [[| |?]|] eqn:Q; try discriminate Wq.
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (rewrite Hr0, Hm1; exact Ws).
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (rewrite Hr0, Hm1; exact Wc).
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    eapply (cpv_ok recp rp Hrecp Hrphp Hr0 Hrm0 Hm1 p); [exact Wp | exact I2 | exact Rt | ].
    intros rho3 n3 A A3 Le3 LA VA.
    pose proof (pvcallp_run fi gs h (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) (denote_pv cs rec recm recp cenv benv renv denv M p) E Wsp Wsm Wl Wr Wsw Q) as RK.
    destruct RK as (fg & rho' & Fd & Bd & EVd).
      { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
      { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
      { eapply (cs_fit_bound cbs); eauto. }
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    assert (VS3 : avals rho3 (Cs ++ As ++ [A]) = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs)
                    ++ flat_map vflat (denote_es cs rec cenv benv renv denv M args) ++ [fst (denote_pv cs rec recm recp cenv benv renv denv M p)])).
    { apply avals_app; [exact VC3 | apply avals_app; [exact VA3 | cbn [avals]; rewrite VA; reflexivity]]. }
    eapply K_call; [exact Fd | exact VS3 | exact Bd | exact EVd | ].
    apply K_ret. cbn [aval]. rewrite PTree.gss. reflexivity.
Qed.

(** after a call (step 47): the invariant with the call's result at its atom, a number or a boolean *)
Lemma inv_call_res : forall {cbs : list cbe} rho rho3 cenvA benvA renvA envA cenv benv renv denv nxt n3 w,
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> agree rho rho3 nxt -> Pos.le nxt n3 ->
  inv cbs (PTree.set n3 w rho3) cenvA benvA renvA (Avar n3 :: envA) cenv benv renv (w :: denv) (Pos.succ n3).
Proof.
  intros cbs rho rho3 cenvA benvA renvA envA cenv benv renv denv nxt n3 w I A Le. apply inv_let.
  - eapply inv_step; [exact I | apply agree_set1; [exact A | exact Le] | lia].
  - cbn [aval]. apply PTree.gss.
  - cbn [atom_lt]. lia.
Qed.
Lemma inv_call_resb : forall {cbs : list cbe} rho rho3 cenvA benvA renvA envA cenv benv renv denv nxt n3 b,
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> agree rho rho3 nxt -> Pos.le nxt n3 ->
  inv cbs (PTree.set n3 (b2i b) rho3) cenvA (Avar n3 :: benvA) renvA envA cenv (b :: benv) renv denv (Pos.succ n3).
Proof.
  intros cbs rho rho3 cenvA benvA renvA envA cenv benv renv denv nxt n3 b I A Le. apply inv_blet.
  - eapply inv_step; [exact I | apply agree_set1; [exact A | exact Le] | lia].
  - cbn [aval]. apply PTree.gss.
  - cbn [atom_lt]. lia.
Qed.

Lemma ctailx_ok : forall x cenv benv renv denv M rk cbs, r = false -> rm = false -> mok = true -> wfx (sigsv cbs) rx nx k rk x = true -> rtyped renv rk ->
  cboundv cbj cbs pv cenv ->
  exists Me, forall cenvA benvA renvA envA nxt rho, inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt ->
    evalk P f rho M (ctailx gidf g mv x cenvA benvA renvA envA nxt) (denote_x cs rec recm recx cenv benv renv denv M x) Me.
Proof.
  induction x as [e | m x IH | e x IH | b x IH | c a b x1 IH1 x2 IH2 renv | b x1 IH1 x2 IH2 renv | c x0 IH0 x1 IH1 renv | c x IH
                 | ccs args m | fi ccs args m | rr x IH | rr x IH | pp x IH | pp x IH | sj rr x IH | fi ccs args pp
                 | bq fi ccs args m x IH | ccs args m x IH | bq fi ccs args pp x IH];
    intros cenv benv renv denv M rk cbs Hr0 Hrm0 Hm1 W Rt Cb; cbn [wfx] in W.
  - (* XRet *) exists M. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x].
    assert (We : wf (sigsv cbs) r mok nx k rk e = true) by (rewrite Hr0, Hm1; exact W).
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho' n' a A' Le' La Va. apply K_ret. exact Va.
  - (* XLetM *) apply andb_true_iff in W as [Wm Wx].
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    destruct (IH cenv benv renv denv (denote_m cs rec recm cenv benv renv denv M m) rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x].
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A1 Le1. cbv beta.
    apply HMe. eapply inv_step; eauto.
  - (* XLet *) apply andb_true_iff in W as [We Wx].
    assert (We' : wf (sigsv cbs) r mok nx k rk e = true) by (rewrite Hr0, Hm1; exact We).
    destruct (IH cenv benv renv (denote_e cs rec cenv benv renv denv M e :: denv) M rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply HMe. apply inv_let; auto. eapply inv_step; eauto.
  - (* XLetB *) apply andb_true_iff in W as [Wb Wx].
    assert (Wb' : wfb (sigsv cbs) r mok nx k rk b = true) by (rewrite Hr0, Hm1; exact Wb).
    destruct (IH cenv (denote_b cs rec cenv benv renv denv M b :: benv) renv denv M rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x].
    apply (cbval_ok b) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply HMe. apply inv_blet; auto. eapply inv_step; eauto.
  - (* XIf *) apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [W W1]. apply andb_true_iff in W as [Wa Wb].
    assert (Wa' : wf (sigsv cbs) r mok nx k rk a = true) by (rewrite Hr0, Hm1; exact Wa).
    assert (Wb' : wf (sigsv cbs) r mok nx k rk b = true) by (rewrite Hr0, Hm1; exact Wb).
    destruct (IH1 cenv benv renv denv M rk cbs Hr0 Hrm0 Hm1 W1 Rt Cb) as [Me1 HMe1].
    destruct (IH2 cenv benv renv denv M rk cbs Hr0 Hrm0 Hm1 W2 Rt Cb) as [Me2 HMe2].
    exists (if cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b) then Me1 else Me2).
    intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      assert (I2' : forall n', Pos.le n2 n' -> inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n') by (intros n' L'; eapply inv_step; [exact I2 | apply agree_refl | exact L']).
      destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M a) (denote_e cs rec cenv benv renv denv M b)); eauto using after_le.
  - (* XIfB *) apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [Wb W1].
    assert (Wb' : wfb (sigsv cbs) r mok nx k rk b = true) by (rewrite Hr0, Hm1; exact Wb).
    destruct (IH1 cenv benv renv denv M rk cbs Hr0 Hrm0 Hm1 W1 Rt Cb) as [Me1 HMe1].
    destruct (IH2 cenv benv renv denv M rk cbs Hr0 Hrm0 Hm1 W2 Rt Cb) as [Me2 HMe2].
    exists (if denote_b cs rec cenv benv renv denv M b then Me1 else Me2).
    intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x].
    apply (ccond_ok b) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply HMe1. eapply inv_step; eauto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply HMe2. eapply inv_step; eauto.
  - (* XMatch *) apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O) as [|p] eqn:Ec.
    + destruct (IH0 cenv benv renv denv M rk cbs Hr0 Hrm0 Hm1 W0 Rt Cb) as [Me HMe].
      exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. rewrite Ec.
      pose proof Iv as (E & L & C & LC & Bv & LBv & Cb' & Mv & H & _).
      assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl. apply HMe; auto.
    + assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Bc; rewrite Ec in Bc; exact Bc).
      destruct (IH1 (p :: cenv) benv renv denv M rk (cpush_match (sigsv cbs) c :: cbs) Hr0 Hrm0 Hm1 W1 Rt (cboundv_cons cbj cbs pv cenv (cpush_match (sigsv cbs) c) p Cb (match_push_ok1 cbs c cenv p Cb Ec) (match_push_ok2 cbs c cenv p Cb Ec))) as [Me HMe].
      exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. rewrite Ec.
      pose proof Iv as (E & L & C & LC & Bv & LBv & Cb' & Mv & H & _).
      assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply HMe. apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
  - (* XLetC *) apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wc Wl].
    assert (Wc' : wfc (sigsv cbs) r mok nx k rk c = true) by (rewrite Hr0, Hm1; exact Wc).
    pose proof (let_push_ok1 cbs c cenv benv renv denv M Wl Cb) as Bc. pose proof (let_push_ok2 cbs c cenv benv renv denv M Cb) as Bl.
    destruct (IH (denote_c cs rec cenv benv renv denv M c :: cenv) benv renv denv M rk (cpush_let (sigsv cbs) c :: cbs) Hr0 Hrm0 Hm1 Wx Rt (cboundv_cons _ _ _ _ _ _ Cb Bc Bl)) as [Me HMe].
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x].
    apply ccnt_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply letc_okv_wb; exact Wl. }
    intros rho1 n1 A A1 Le1 LA VA.
    apply HMe. apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | exact Bc | exact Bl].
  - (* XRec *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    destruct (Hrecx Wr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args)
                       (denote_m cs rec recm cenv benv renv denv M m)) as [Me RK].
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x].
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (rewrite Hr0, Hm1; exact Wc).
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (rewrite Hr0, Hm1; exact Ws).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1 & _). destruct (H1 (Hrxhp Wr)) as [Rm _].
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    eapply loopx_call_ok; [exact RK | | exact VC3 | exact VA3].
    rewrite (A3 mv) by lia. rewrite (A2 mv Mv1). exact Rm.
  - (* XCall *) unfold sigsv in W. cbn [fst] in W; rewrite nth_sigs in W. pose proof (Hcs fi) as Hc.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    assert (Hfi : (fi < j)%nat).
    { assert (fi < length cs)%nat by (apply nth_error_Some; rewrite E; discriminate). lia. }
    apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wsh]. apply andb_true_iff in W as [W Wsw]. apply andb_true_iff in W as [W Wr].
    apply andb_true_iff in W as [W Wsm]. apply andb_true_iff in W as [Wn Wk].
    unfold callee_ok in Hc. rewrite Wsw in Hc.
    destruct (Hc Hslot (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args)
                 (denote_m cs rec recm cenv benv renv denv M m)) as [Me RK].
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { eapply (cs_fit_bound cbs); eauto. }
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. unfold callee. rewrite E.
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (rewrite Hr0, Hm1; exact Wc).
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (rewrite Hr0, Hm1; exact Ws).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    destruct RK as (fg & rho' & F & B & EV).
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    eapply K_call; eauto.
    + apply avals_app; eauto.
    + apply K_ret. simpl. apply PTree.gss.
  - (* XLetR *) apply andb_true_iff in W as [Wr Wx].
    assert (Wr' : wfr (sigsv cbs) r mok nx k rk rr = true) by (rewrite Hr0, Hm1; exact Wr).
    assert (Rt' : rtyped (denote_r cs rec cenv benv renv denv M rr :: renv) (rtype rk rr :: rk))
      by (apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto]).
    destruct (IH cenv benv (denote_r cs rec cenv benv renv denv M rr :: renv) denv M (rtype rk rr :: rk) cbs Hr0 Hrm0 Hm1 Wx Rt' Cb) as [Me HMe].
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    apply HMe. apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs].
  - (* XMatchR *) apply andb_true_iff in W as [Wr Wx].
    assert (Wr' : wfr (sigsv cbs) r mok nx k rk rr = true) by (rewrite Hr0, Hm1; exact Wr).
    destruct (IH cenv benv renv (rev (vflat (denote_r cs rec cenv benv renv denv M rr)) ++ denv) M rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. rewrite rmatch_eq.
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    apply HMe. apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs].
  - (* XMatchP *) apply andb_true_iff in W as [Wp Wx].
    destruct (denote_pv cs rec recm dpair cenv benv renv denv M pp) as [x0 s0] eqn:Ep.
    destruct (IH cenv benv renv (x0 :: denv) s0 rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. rewrite Ep.
    eapply (cpv_ok dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Hr0 | exact Hrm0 | exact Hm1
                                  | exact Wp | exact Iv | exact Rt | ].
    intros rho1 n1 A A1 Le1 LA VA. rewrite Ep in VA |- *. cbn [fst snd] in VA |- *. cbv beta iota.
    apply HMe. apply inv_let; [eapply inv_step; eauto | exact VA | exact LA].
  - (* XLetP *) apply andb_true_iff in W as [Wp Wx].
    destruct (IH cenv benv renv (fst (denote_pv cs rec recm dpair cenv benv renv denv M pp) :: denv)
                 (snd (denote_pv cs rec recm dpair cenv benv renv denv M pp)) rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. cbv zeta.
    eapply (cpv_ok dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Hr0 | exact Hrm0 | exact Hm1
                                  | exact Wp | exact Iv | exact Rt | ].
    intros rho1 n1 A A1 Le1 LA VA. cbv beta.
    apply HMe. apply inv_let; [eapply inv_step; eauto | exact VA | exact LA].
  - (* XSplitR *) apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Er Wr]. apply Nat.eqb_eq in Er.
    assert (Wr' : wfr (sigsv cbs) r mok nx k rk rr = true) by (rewrite Hr0, Hm1; exact Wr).
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M rr) = KRec sj) by (rewrite <- Er; eapply kind_denote_r; eauto).
    destruct (IH cenv benv (rev (snd (rsplit_p (denote_r cs rec cenv benv renv denv M rr))) ++ renv)
                 (rev (fst (rsplit_p (denote_r cs rec cenv benv renv denv M rr))) ++ denv) M (rev (RJ sj) ++ rk) cbs Hr0 Hrm0 Hm1 Wx
                 (rsplit_typed _ sj renv rk Kx Rt) Cb) as [Me HMe].
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. rewrite rsplit_eq.
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    apply HMe. apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs].
  - (* XCallP *) unfold sigsv in W. cbn [fst] in W; rewrite nth_sigs in W.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Wpp]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wsh]. apply andb_true_iff in W as [W Wq]. apply andb_true_iff in W as [W Wr]. apply andb_true_iff in W as [W Wl].
    apply andb_true_iff in W as [W Wsm]. apply andb_true_iff in W as [W Wsp]. apply andb_true_iff in W as [Wn Wk].
    apply negb_true_iff in Wr. unfold isq in Wq. apply negb_true_iff in Wq. destruct (sq gs) eqn:Q; [discriminate Wq|].
    destruct (denote_pv cs rec recm dpair cenv benv renv denv M pp) as [x0 s0] eqn:Ep.
    destruct (xcallp_run fi gs h (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) (x0, s0)
                E Wsp Wsm Wl Wr Q) as [Me RK].
      { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
      { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
      { eapply (cs_fit_bound cbs); eauto. }
    exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. unfold callee. rewrite E, Ep.
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (rewrite Hr0, Hm1; exact Wc).
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (rewrite Hr0, Hm1; exact Ws).
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    eapply (cpv_ok dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Hr0 | exact Hrm0 | exact Hm1
                                  | exact Wpp | exact I2 | exact Rt | ].
    intros rho3 n3 A A3 Le3 LA VA. rewrite Ep in VA |- *. cbn [fst snd] in VA |- *.
    destruct RK as (fg & rho' & F & B & EV).
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat (denote_es cs rec cenv benv renv denv M args))).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    assert (VS3 : avals rho3 (Cs ++ As ++ [A]) = Some (map ofn (denote_cs cs rec cenv benv renv denv M ccs)
                    ++ flat_map vflat (denote_es cs rec cenv benv renv denv M args) ++ [fst ((x0, s0))])).
    { apply avals_app; [exact VC3 | apply avals_app; [exact VA3 | cbn [avals]; rewrite VA; reflexivity]]. }
    eapply K_call; [exact F | exact VS3 | exact B | exact EV | ].
    apply K_ret. cbn [aval]. rewrite PTree.gss. reflexivity.
  - (* XBind *) unfold sigsv in W. cbn [fst] in W; rewrite nth_sigs in W. pose proof (Hcs fi) as Hc.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    assert (Hfi : (fi < j)%nat).
    { assert (fi < length cs)%nat by (apply nth_error_Some; rewrite E; discriminate). lia. }
    apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws].
    apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfit]. apply andb_true_iff in W as [W Wq].
    apply andb_true_iff in W as [W Wsp]. apply andb_true_iff in W as [Wn Wk].
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (rewrite Hr0, Hm1; exact Wc).
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (rewrite Hr0, Hm1; exact Ws).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    assert (L1 : length (denote_cs cs rec cenv benv renv denv M ccs) = sn gs) by (rewrite len_denote_cs; apply Nat.eqb_eq; auto).
    assert (L2 : map kind_of (denote_es cs rec cenv benv renv denv M args) = sk gs)
      by (erewrite kinds_denote_es by eassumption; apply kinds_eqb_eq; auto).
    assert (L3 : cfits gs (fbound gs fi) (denote_cs cs rec cenv benv renv denv M ccs)) by (eapply (cs_fit_bound cbs); eauto).
    set (cvs := denote_cs cs rec cenv benv renv denv M ccs) in *. set (vs := denote_es cs rec cenv benv renv denv M args) in *.
    set (M2 := denote_m cs rec recm cenv benv renv denv M m) in *.
    unfold callee_ok in Hc. specialize (Hc Hslot cvs vs M2 L1 L2 L3).
    destruct (sw gs) eqn:Sw.
    + (* the callee writes: what follows reads no memory *)
      apply andb_true_iff in Wx as [Wb Wx]. destruct bq; [discriminate Wb|].
      destruct x as [e| | | | | | | | | | | | | | | | | |]; cbn [xfree] in Wx; rewrite ?andb_false_r in Wx; try discriminate Wx.
      apply andb_true_iff in Wx as [We0 We1].
      destruct Hc as [M' RK].
      assert (We' : wf (sigsv cbs) r mok nx k rk e = true) by (rewrite Hr0, Hm1; exact We1).
      assert (EQ : forall w, denote_e cs rec cenv benv renv (w :: denv) M2 e = denote_e cs rec cenv benv renv (w :: denv) M' e).
      { intros w. transitivity (denote_e cs (fun _ _ _ => 0%uint63) cenv benv renv (w :: denv) M2 e).
        { eapply (proj1 denote_rec_ext_r); [ | exact We0 | exact Rt]; intros Hff; discriminate Hff. }
        transitivity (denote_e cs (fun _ _ _ => 0%uint63) cenv benv renv (w :: denv) M' e).
        { eapply (proj1 denote_nomem); [intros; reflexivity | exact We0]. }
        symmetry. eapply (proj1 denote_rec_ext_r); [ | exact We0 | exact Rt]; intros Hff; discriminate Hff. }
      exists M'. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. unfold callee. rewrite E. cbv zeta.
      fold cvs vs M2. rewrite xres_calln by exact Wq. cbv beta. cbn [denote_x]. rewrite EQ.
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
      apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    assert (VC3 : avals rho3 Cs = Some (map ofn cvs)).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs). exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat vs)).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
      eapply KQMAuto.K_call_run; [apply avals_app; [exact VC3 | exact VA3] | exact RK | ].
      pose proof (inv_call_res rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 (calln gs h cvs vs M2) I2 A3 Le3) as I4.
      apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := calln gs h cvs vs M2 :: denv) (rk := rk) (cbs := cbs); auto.
      intros rho' n' a A' Le' La Va. apply K_ret. exact Va.
    + (* it does not: what follows on the memory the call was given *)
      rewrite (resq_mem bq gs h cvs vs M2 Wq) in Hc.
      destruct bq.
      * destruct (xres_calln_b gs h cvs vs M2 (fun v => denote_x cs rec recm recx cenv benv renv (v :: denv) M2 x)
                    (fun b => denote_x cs rec recm recx cenv (b :: benv) renv denv M2 x) Wq) as (bv & Eb & Xb).
        destruct (IH cenv (bv :: benv) renv denv M2 rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
        exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. unfold callee. rewrite E. cbv zeta.
        fold cvs vs M2. rewrite Xb.
        apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
        intros rho1 n1 Cs A1 Le1 LCs VCs.
        pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
        apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
        intros rho2 n2 As A2 Le2 LAs VAs.
        pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
        apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
        assert (VC3 : avals rho3 Cs = Some (map ofn cvs)).
        { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs). exact VCs. }
        assert (VA3 : avals rho3 As = Some (flat_map vflat vs)).
        { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
        eapply KQMAuto.K_call_run; [apply avals_app; [exact VC3 | exact VA3] | exact Hc | ].
        rewrite Eb. apply HMe. exact (inv_call_resb rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 bv I2 A3 Le3).
      * destruct (IH cenv benv renv (calln gs h cvs vs M2 :: denv) M2 rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
        exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. unfold callee. rewrite E. cbv zeta.
        fold cvs vs M2. rewrite xres_calln by exact Wq. cbv beta.
        apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
        intros rho1 n1 Cs A1 Le1 LCs VCs.
        pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
        apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
        intros rho2 n2 As A2 Le2 LAs VAs.
        pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
        apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
        assert (VC3 : avals rho3 Cs = Some (map ofn cvs)).
        { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs). exact VCs. }
        assert (VA3 : avals rho3 As = Some (flat_map vflat vs)).
        { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
        eapply KQMAuto.K_call_run; [apply avals_app; [exact VC3 | exact VA3] | exact Hc | ].
        apply HMe. exact (inv_call_res rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 _ I2 A3 Le3).
  - (* XBindR *) apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws].
    apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk].
    apply andb_true_iff in W as [Wr Wn].
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (rewrite Hr0, Hm1; exact Wc).
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (rewrite Hr0, Hm1; exact Ws).
    assert (Wm' : wfm (sigsv cbs) r rm mok nx k rk m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    set (cvs := denote_cs cs rec cenv benv renv denv M ccs) in *. set (vs := denote_es cs rec cenv benv renv denv M args) in *.
    set (M2 := denote_m cs rec recm cenv benv renv denv M m) in *.
    destruct (Hrecx Wr cvs vs M2) as [M' RK].
    { unfold cvs. rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { unfold vs. erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    destruct x as [e| | | | | | | | | | | | | | | | | |]; cbn [xfree] in Wx; try discriminate Wx.
    apply andb_true_iff in Wx as [We0 We1].
    assert (We' : wf (sigsv cbs) r mok nx k rk e = true) by (rewrite Hr0, Hm1; exact We1).
    assert (EQ : forall w, denote_e cs rec cenv benv renv (w :: denv) M2 e = denote_e cs rec cenv benv renv (w :: denv) M' e).
    { intros w. transitivity (denote_e cs (fun _ _ _ => 0%uint63) cenv benv renv (w :: denv) M2 e).
      { eapply (proj1 denote_rec_ext_r); [ | exact We0 | exact Rt]; intros Hff; discriminate Hff. }
      transitivity (denote_e cs (fun _ _ _ => 0%uint63) cenv benv renv (w :: denv) M' e).
      { eapply (proj1 denote_nomem); [intros; reflexivity | exact We0]. }
      symmetry. eapply (proj1 denote_rec_ext_r); [ | exact We0 | exact Rt]; intros Hff; discriminate Hff. }
    exists M'. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. cbv zeta. fold cvs vs M2. rewrite EQ.
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    apply cmem_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho3 n3 A3 Le3.
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1 & _). destruct (H1 (Hrxhp Wr)) as [Rm _].
    assert (VC3 : avals rho3 Cs = Some (map ofn cvs)).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs). exact VCs. }
    assert (VA3 : avals rho3 As = Some (flat_map vflat vs)).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    assert (VM : avals rho3 [Avar mv] = Some [ofn cm]).
    { cbn [avals aval]. rewrite (A3 mv) by lia. rewrite (A2 mv Mv1). rewrite Rm. reflexivity. }
    eapply KQMAuto.K_call_run; [change (Avar mv :: Cs ++ As) with ([Avar mv] ++ (Cs ++ As)); apply avals_app; [exact VM | apply avals_app; [exact VC3 | exact VA3]] | exact RK | ].
    pose proof (inv_call_res rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 (recx cvs vs M2) I2 A3 Le3) as I4.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := recx cvs vs M2 :: denv) (rk := rk) (cbs := cbs); auto.
    intros rho' n' a A' Le' La Va. apply K_ret. exact Va.
  - (* XBindP *) unfold sigsv in W. cbn [fst] in W; rewrite nth_sigs in W.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [W Wpp]. apply andb_true_iff in W as [W Ws].
    apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfit]. apply andb_true_iff in W as [W Wq].
    apply andb_true_iff in W as [W Wl]. apply andb_true_iff in W as [W Wsm]. apply andb_true_iff in W as [W Wsp].
    apply andb_true_iff in W as [Wn Wk].
    assert (Wc' : wfcs (sigsv cbs) r mok nx k rk ccs = true) by (rewrite Hr0, Hm1; exact Wc).
    assert (Ws' : wfs (sigsv cbs) r mok nx k rk args = true) by (rewrite Hr0, Hm1; exact Ws).
    assert (L1 : length (denote_cs cs rec cenv benv renv denv M ccs) = sn gs) by (rewrite len_denote_cs; apply Nat.eqb_eq; auto).
    assert (L2 : map kind_of (denote_es cs rec cenv benv renv denv M args) = removelast (sk gs))
      by (erewrite kinds_denote_es by eassumption; apply kinds_eqb_eq; auto).
    assert (L3 : cfits gs (fbound gs fi) (denote_cs cs rec cenv benv renv denv M ccs)) by (eapply (cs_fit_bound cbs); eauto).
    set (cvs := denote_cs cs rec cenv benv renv denv M ccs) in *. set (vs := denote_es cs rec cenv benv renv denv M args) in *.
    destruct (denote_pv cs rec recm dpair cenv benv renv denv M pp) as [x0 s0] eqn:Ep.
    pose proof (pcall_pre fi gs h cvs vs (x0, s0) E Wsp Wsm Wl L1 L2 L3) as Hc.
    destruct (sw gs) eqn:Sw.
    + apply andb_true_iff in Wx as [Wb Wx]. destruct bq; [discriminate Wb|].
      destruct x as [e| | | | | | | | | | | | | | | | | |]; cbn [xfree] in Wx; rewrite ?andb_false_r in Wx; try discriminate Wx.
      apply andb_true_iff in Wx as [We0 We1].
      cbn [fst snd] in Hc. destruct Hc as [M' RK].
      assert (We' : wf (sigsv cbs) r mok nx k rk e = true) by (rewrite Hr0, Hm1; exact We1).
      assert (EQ : forall w, denote_e cs rec cenv benv renv (w :: denv) s0 e = denote_e cs rec cenv benv renv (w :: denv) M' e).
      { intros w. transitivity (denote_e cs (fun _ _ _ => 0%uint63) cenv benv renv (w :: denv) s0 e).
        { eapply (proj1 denote_rec_ext_r); [ | exact We0 | exact Rt]; intros Hff; discriminate Hff. }
        transitivity (denote_e cs (fun _ _ _ => 0%uint63) cenv benv renv (w :: denv) M' e).
        { eapply (proj1 denote_nomem); [intros; reflexivity | exact We0]. }
        symmetry. eapply (proj1 denote_rec_ext_r); [ | exact We0 | exact Rt]; intros Hff; discriminate Hff. }
      exists M'. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. unfold callee. rewrite E, Ep. cbv zeta.
      fold cvs vs. rewrite xres_callnp by exact Wq. cbv beta. cbn [denote_x snd]. rewrite EQ.
      apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
      intros rho1 n1 Cs A1 Le1 LCs VCs.
      pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
      apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      intros rho2 n2 As A2 Le2 LAs VAs.
      pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
      eapply (cpv_ok dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Hr0 | exact Hrm0 | exact Hm1
                                    | exact Wpp | exact I2 | exact Rt | ].
      intros rho3 n3 A A3 Le3 LA VA. rewrite Ep in VA |- *. cbn [fst snd] in VA |- *.
      assert (VC3 : avals rho3 Cs = Some (map ofn cvs)).
      { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs). exact VCs. }
      assert (VA3 : avals rho3 As = Some (flat_map vflat vs)).
      { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
      assert (VS3 : avals rho3 (Cs ++ As ++ [A]) = Some (map ofn cvs ++ flat_map vflat vs ++ [x0])).
      { apply avals_app; [exact VC3 | apply avals_app; [exact VA3 | cbn [avals]; rewrite VA; reflexivity]]. }
      eapply KQMAuto.K_call_run; [exact VS3 | exact RK | ].
      pose proof (inv_call_res rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 (callnp gs h cvs vs (x0, s0)) I2 A3 Le3) as I4.
      apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := callnp gs h cvs vs (x0, s0) :: denv) (rk := rk) (cbs := cbs); auto.
      intros rho' n' a A' Le' La Va. apply K_ret. exact Va.
    + rewrite (resq_memp bq gs h cvs vs (x0, s0) Wq) in Hc. cbn [fst snd] in Hc.
      destruct bq.
      * destruct (xres_callnp_b gs h cvs vs (x0, s0) (fun v => denote_x cs rec recm recx cenv benv renv (v :: denv) s0 x)
                    (fun b => denote_x cs rec recm recx cenv (b :: benv) renv denv s0 x) Wq) as (bv & Eb & Xb).
        destruct (IH cenv (bv :: benv) renv denv s0 rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
        exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. unfold callee. rewrite E, Ep. cbv zeta.
        fold cvs vs. cbn [snd]. rewrite Xb.
        apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
      intros rho1 n1 Cs A1 Le1 LCs VCs.
      pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
      apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      intros rho2 n2 As A2 Le2 LAs VAs.
      pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
      eapply (cpv_ok dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Hr0 | exact Hrm0 | exact Hm1
                                    | exact Wpp | exact I2 | exact Rt | ].
      intros rho3 n3 A A3 Le3 LA VA. rewrite Ep in VA |- *. cbn [fst snd] in VA |- *.
      assert (VC3 : avals rho3 Cs = Some (map ofn cvs)).
      { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs). exact VCs. }
      assert (VA3 : avals rho3 As = Some (flat_map vflat vs)).
      { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
      assert (VS3 : avals rho3 (Cs ++ As ++ [A]) = Some (map ofn cvs ++ flat_map vflat vs ++ [x0])).
      { apply avals_app; [exact VC3 | apply avals_app; [exact VA3 | cbn [avals]; rewrite VA; reflexivity]]. }
        eapply KQMAuto.K_call_run; [exact VS3 | exact Hc | ].
        rewrite Eb. apply HMe. exact (inv_call_resb rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 bv I2 A3 Le3).
      * destruct (IH cenv benv renv (callnp gs h cvs vs (x0, s0) :: denv) s0 rk cbs Hr0 Hrm0 Hm1 Wx Rt Cb) as [Me HMe].
        exists Me. intros cenvA benvA renvA envA nxt rho Iv. cbn [ctailx denote_x]. unfold callee. rewrite E, Ep. cbv zeta.
        fold cvs vs. rewrite xres_callnp by exact Wq. cbv beta. cbn [snd].
        apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply all_fit_wb; eauto. }
      intros rho1 n1 Cs A1 Le1 LCs VCs.
      pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
      apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
      intros rho2 n2 As A2 Le2 LAs VAs.
      pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
      eapply (cpv_ok dpair false); [intros Habs; discriminate Habs | intros Habs; discriminate Habs | exact Hr0 | exact Hrm0 | exact Hm1
                                    | exact Wpp | exact I2 | exact Rt | ].
      intros rho3 n3 A A3 Le3 LA VA. rewrite Ep in VA |- *. cbn [fst snd] in VA |- *.
      assert (VC3 : avals rho3 Cs = Some (map ofn cvs)).
      { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs). exact VCs. }
      assert (VA3 : avals rho3 As = Some (flat_map vflat vs)).
      { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
      assert (VS3 : avals rho3 (Cs ++ As ++ [A]) = Some (map ofn cvs ++ flat_map vflat vs ++ [x0])).
      { apply avals_app; [exact VC3 | apply avals_app; [exact VA3 | cbn [avals]; rewrite VA; reflexivity]]. }
        eapply KQMAuto.K_call_run; [exact VS3 | exact Hc | ].
        apply HMe. exact (inv_call_res rho2 rho3 cenvA benvA renvA envA cenv benv renv denv n2 n3 _ I2 A3 Le3).
Qed.
(* ---------------------------------------------------------------- a boolean given back (step 24) *)
Variables (recb : list nat -> list val -> mem -> bool) (rbb : bool).
(** the recursive call of a function giving back a boolean, where it is allowed ([rbb]): the boolean as 1 or 0, the memory
    kept *)
Hypothesis Hrecb : rbb = true -> forall cvs vs M, length cvs = nx -> map kind_of vs = k -> rfits cvs ->
  runk P g (ofn cm :: map ofn cvs ++ flat_map vflat vs) M (b2i (recb cvs vs M)) M.
Hypothesis Hrbbhp : rbb = true -> hp = true.

(** in tail position: the function's body returns the boolean [b] means, as 1 or 0, and keeps the memory *)
Lemma ctailb_ok : forall b cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs, wfbb (sigsv cbs) r rbb mok nx k rk b = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  evalk P f rho M (ctailb gidf g mv b cenvA benvA renvA envA nxt) (b2i (denote_bb cs rec recb cenv benv renv denv M b)) M.
Proof.
  induction b as [x | ccs args | ccs args | e b IH | c b IH | c b IH | x b IH | x b IH
                 | c x y t IHt u IHu | c t IHt u IHu | c b0 IH0 b1 IH1 | sj x b IH];
    intros cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs W Iv Rt; cbn [ctailb denote_bb].
  - (* BbRet *) cbn [wfbb] in W.
    apply (cbval_ok x) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho1 n1 A A1 Le1 LA VA. apply K_ret. exact VA.
  - (* BbRec *) cbn [wfbb] in W. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & H2 & _). destruct (H2 (Hrbbhp Wr)) as [Rm _].
    apply (loopx_call_ok rho2 Cs As (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M);
      [ | exact Rm | rewrite (avals_agree rho1 rho2 n1 Cs A2 LCs); exact VCs | exact VAs].
    apply Hrecb; [exact Wr | | |].
    + rewrite len_denote_cs. apply Nat.eqb_eq; auto.
    + erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto.
    + destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto).
  - (* BbNotRec *) cbn [wfbb] in W. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & _ & H2 & _). destruct (H2 (Hrbbhp Wr)) as [Rm _].
    destruct (Hrecb Wr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) as (fg & rho' & Fd & Bd & EVd).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    eapply K_call; [exact Fd | | exact Bd | exact EVd | ].
    + cbn [avals aval]. rewrite Rm, (avals_app rho2 Cs As _ _ (eq_trans (avals_agree rho1 rho2 n1 Cs A2 LCs) VCs) VAs). reflexivity.
    + eapply K_op; [cbn [aval]; apply PTree.gss | reflexivity | ]. rewrite b2i_lxor.
      apply K_ret. cbn [aval]. apply PTree.gss.
  - (* BbLet *) cbn [wfbb] in W. apply andb_true_iff in W as [We Wb].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (rk := rk) (cbs := cbs); auto. apply inv_let; auto. eapply inv_step; eauto.
  - (* BbLetB *) cbn [wfbb] in W. apply andb_true_iff in W as [Wc Wb].
    apply (cbval_ok c) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (rk := rk) (cbs := cbs); auto. apply inv_blet; auto. eapply inv_step; eauto.
  - (* BbLetC *) cbn [wfbb] in W. apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [Wc Wl].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnt_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply letc_okv_wb; exact Wl. }
    intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (rk := rk) (cbs := cpush_let (sigsv cbs) c :: cbs); auto. apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto].
  - (* BbLetR *) cbn [wfbb] in W. apply andb_true_iff in W as [Wx Wb].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    apply IH with (rk := rtype rk x :: rk) (cbs := cbs); auto. apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs].
    apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto].
  - (* BbMatchR *) cbn [wfbb] in W. apply andb_true_iff in W as [Wx Wb].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    rewrite rmatch_eq. apply IH with (rk := rk) (cbs := cbs); auto. apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs].
  - (* BbIf *) cbn [wfbb] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wx Wy].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    assert (VA2 : aval rho2 A = Some (denote_e cs rec cenv benv renv denv M x)) by (rewrite (aval_agree rho1 rho2 n1); eauto).
    eapply K_if.
    + exact VA2.
    + eauto.
    + assert (I2' : forall n', Pos.le n2 n' -> inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n') by (intros n' L'; eapply inv_step; [exact I2 | apply agree_refl | exact L']).
      destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M x) (denote_e cs rec cenv benv renv denv M y)); eauto using after_le.
  - (* BbIfB *) cbn [wfbb] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wc Wt].
    apply (ccond_ok c) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply IHt with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply IHu with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
  - (* BbMatch *) cbn [wfbb] in W. apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
    destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl. apply IH0 with (rk := rk) (cbs := cbs); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto. apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
  - (* BbSplitR *) cbn [wfbb] in W. apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M x) = KRec sj) by (rewrite <- Ex; eapply kind_denote_r; eauto).
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    rewrite rsplit_eq. apply IH with (rk := rev (RJ sj) ++ rk) (cbs := cbs); auto. apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs].
    apply rsplit_typed; [exact Kx | exact Rt].
Qed.

(* ---------------------------------------------------------------- a record given back (step 12, part 3) *)
Variables (ri : nat) (recr : list nat -> list val -> mem -> RT ri) (rb : bool).
(** the recursive call of a function giving back a record, where it is allowed ([rb]): its first field, the slot block
    written with the others *)
Hypothesis Hrecr : rb = true -> forall cvs vs M, length cvs = nx -> map kind_of vs = k -> rfits cvs ->
  runk P g (ofn cm :: map ofn cvs ++ flat_map vflat vs) M (hd 0%uint63 (relim (RO ri) (recr cvs vs M) (fun l => l)))
    (wslot O (tl (relim (RO ri) (recr cvs vs M) (fun l => l))) M).
Hypothesis Hrbhp : rb = true -> hp = true.
Hypothesis Hri1 : (1 <= rn (RO ri))%nat.
Hypothesis Hri2 : (Z.of_nat (rn (RO ri)) <= 1048576)%Z.

(** in tail position: the function's body returns the first field of the record [b] means and ends with the slot block
    written with the others *)
Lemma ctailr_ok : forall b cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs, wfbr (sigsv cbs) r rb mok nx k rk ri b = true ->
  inv cbs rho cenvA benvA renvA envA cenv benv renv denv nxt -> rtyped renv rk ->
  evalk P f rho M (ctailr gidf g mv ri b cenvA benvA renvA envA nxt)
    (hd 0%uint63 (relim (RO ri) (denote_br cs rec ri recr cenv benv renv denv M b) (fun l => l)))
    (wslot O (tl (relim (RO ri) (denote_br cs rec ri recr cenv benv renv denv M b) (fun l => l))) M).
Proof.
  induction b as [x | ccs args | ccs args b IH | ccs args b IH | e b IH | c b IH | c b IH | x b IH | x b IH
                 | c x y t IHt u IHu | c t IHt u IHu | c b0 IH0 b1 IH1 | sj x b IH];
    intros cenvA benvA renvA envA cenv benv renv denv nxt rho M rk cbs W Iv Rt; cbn [ctailr denote_br].
  - (* BRet *) destruct (kind_denote_br ((cbo, cws), cbs) r mok nx k rk cs rec cenv benv renv denv M x ri W Rt) as [Wx Kx].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    rewrite (to_rt_vflat ri _ Kx). destruct (avals_hd_tl rho1 As _ VAs) as [Vh Vt].
    eapply cput_ok; [exact Vt |]. apply K_ret. exact Vh.
  - (* BRec *) cbn [wfbr] in W. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    destruct (Hrecr Wr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    rewrite Hf in F. injection F as <-.
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1 & _). destruct (H1 (Hrbhp Wr)) as [Rm _].
    eapply K_loop; eauto.
    simpl. rewrite (A2 mv Mv1), Rm.
    rewrite (avals_app rho2 Cs As _ _ (eq_trans (avals_agree rho1 rho2 n1 Cs A2 LCs) VCs) VAs). reflexivity.
  - (* BMatchRec *) cbn [wfbr] in W. apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [W Ws].
    apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk].
    apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    assert (RK : runk P g (ofn cm :: map ofn (denote_cs cs rec cenv benv renv denv M ccs) ++ flat_map vflat (denote_es cs rec cenv benv renv denv M args)) M
                   (hd 0%uint63 (relim (RO ri) (recr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) (fun l => l)))
                   (wslot O (tl (relim (RO ri) (recr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) (fun l => l))) M)).
    { apply Hrecr; [exact Wr | | |].
      - rewrite len_denote_cs. apply Nat.eqb_eq; auto.
      - erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto.
      - destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    set (Y := recr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) in *.
    assert (LY : length (relim (RO ri) Y (fun l => l)) = rn (RO ri)) by apply rl_len.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & Mv2 & H2 & _). destruct (H2 (Hrbhp Wr)) as [Rm _].
    rewrite (rl_nat ri Y _ (fun l => denote_br cs rec ri recr cenv benv renv (rev l ++ denv) M b)). cbv beta.
    apply (ccallr_ok g (Avar mv :: Cs ++ As) _ (Nat.pred (rn (RO ri))) n2 _ rho2 M
             (hd 0%uint63 (relim (RO ri) Y (fun l => l))) (tl (relim (RO ri) Y (fun l => l))) _ _ RK).
    + destruct (relim (RO ri) Y (fun l => l)); simpl in *; lia.
    + lia.
    + intros Hp. pose proof (Hslot ri ltac:(lia)) as Hs. lia.
    + cbn [avals aval]. rewrite Rm, (avals_app rho2 Cs As _ _ (eq_trans (avals_agree rho1 rho2 n1 Cs A2 LCs) VCs) VAs). reflexivity.
    + constructor; [simpl; lia | apply Forall_app; split; [eapply Forall_atom_mono; [exact LCs | lia] | exact LAs]].
    + intros rho3 n3 Fs A3 Le3 LF VF.
      assert (VF' : avals rho3 Fs = Some (relim (RO ri) Y (fun l => l))).
      { rewrite VF. destruct (relim (RO ri) Y (fun l => l)); [simpl in LY; lia | reflexivity]. }
      apply IH with (rk := rk) (cbs := cbs); auto. apply inv_lets; [eapply inv_step; [exact I2 | exact A3 | exact Le3] | exact VF' | exact LF].
  - (* BLetRec *) cbn [wfbr] in W. apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [W Ws].
    apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk].
    apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply rec_ok_wb; eauto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA renvA envA cenv benv renv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA renvA envA cenv benv renv denv n1 n2 I1 A2 Le2) as I2.
    assert (RK : runk P g (ofn cm :: map ofn (denote_cs cs rec cenv benv renv denv M ccs) ++ flat_map vflat (denote_es cs rec cenv benv renv denv M args)) M
                   (hd 0%uint63 (relim (RO ri) (recr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) (fun l => l)))
                   (wslot O (tl (relim (RO ri) (recr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) (fun l => l))) M)).
    { apply Hrecr; [exact Wr | | |].
      - rewrite len_denote_cs. apply Nat.eqb_eq; auto.
      - erewrite kinds_denote_es by eassumption. apply kinds_eqb_eq; auto.
      - destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). eapply rec_ok_fits; eauto; try (apply Nat.eqb_eq; eauto). }
    set (Y := recr (denote_cs cs rec cenv benv renv denv M ccs) (denote_es cs rec cenv benv renv denv M args) M) in *.
    assert (LY : length (relim (RO ri) Y (fun l => l)) = rn (RO ri)) by apply rl_len.
    pose proof I2 as (_ & _ & _ & _ & _ & _ & _ & Mv2 & H2 & _). destruct (H2 (Hrbhp Wr)) as [Rm _].
    apply (ccallr_ok g (Avar mv :: Cs ++ As) _ (Nat.pred (rn (RO ri))) n2 _ rho2 M
             (hd 0%uint63 (relim (RO ri) Y (fun l => l))) (tl (relim (RO ri) Y (fun l => l))) _ _ RK).
    + destruct (relim (RO ri) Y (fun l => l)); simpl in *; lia.
    + lia.
    + intros Hp. pose proof (Hslot ri ltac:(lia)) as Hs. lia.
    + cbn [avals aval]. rewrite Rm, (avals_app rho2 Cs As _ _ (eq_trans (avals_agree rho1 rho2 n1 Cs A2 LCs) VCs) VAs). reflexivity.
    + constructor; [simpl; lia | apply Forall_app; split; [eapply Forall_atom_mono; [exact LCs | lia] | exact LAs]].
    + intros rho3 n3 Fs A3 Le3 LF VF.
      assert (VF' : avals rho3 Fs = Some (vflat (VRec ri Y))).
      { rewrite VF. cbn [vflat]. destruct (relim (RO ri) Y (fun l => l)); [simpl in LY; lia | reflexivity]. }
      apply IH with (rk := ri :: rk) (cbs := cbs); auto. apply inv_rlet; [eapply inv_step; [exact I2 | exact A3 | exact Le3] | exact VF' | exact LF].
      apply rtyped_cons; [exact Rt | reflexivity].
  - (* BLet *) cbn [wfbr] in W. apply andb_true_iff in W as [We Wb].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (rk := rk) (cbs := cbs); auto. apply inv_let; auto. eapply inv_step; eauto.
  - (* BLetB *) cbn [wfbr] in W. apply andb_true_iff in W as [Wc Wb].
    apply (cbval_ok c) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (rk := rk) (cbs := cbs); auto. apply inv_blet; auto. eapply inv_step; eauto.
  - (* BLetC *) cbn [wfbr] in W. apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [Wc Wl].
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    apply ccnt_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply letc_okv_wb; exact Wl. }
    intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (rk := rk) (cbs := cpush_let (sigsv cbs) c :: cbs); auto. apply inv_clet; [eapply inv_step; eauto | exact VA | exact LA | eapply let_push_ok1; eauto | eapply let_push_ok2; eauto].
  - (* BLetR *) cbn [wfbr] in W. apply andb_true_iff in W as [Wx Wb].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    apply IH with (rk := rtype rk x :: rk) (cbs := cbs); auto. apply inv_rlet; [eapply inv_step; eauto | exact VAs | exact LAs].
    apply rtyped_cons; [exact Rt | eapply kind_denote_r; eauto].
  - (* BMatchR *) cbn [wfbr] in W. apply andb_true_iff in W as [Wx Wb].
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    rewrite rmatch_eq. apply IH with (rk := rk) (cbs := cbs); auto. apply inv_lets; [eapply inv_step; eauto | exact VAs | exact LAs].
  - (* BIf *) cbn [wfbr] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wx Wy].
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    assert (VA2 : aval rho2 A = Some (denote_e cs rec cenv benv renv denv M x)) by (rewrite (aval_agree rho1 rho2 n1); eauto).
    eapply K_if.
    + exact VA2.
    + eauto.
    + assert (I2' : forall n', Pos.le n2 n' -> inv cbs rho2 cenvA benvA renvA envA cenv benv renv denv n') by (intros n' L'; eapply inv_step; [exact I2 | apply agree_refl | exact L']).
      destruct (cmp_sem c (denote_e cs rec cenv benv renv denv M x) (denote_e cs rec cenv benv renv denv M y)); eauto using after_le.
  - (* BIfB *) cbn [wfbr] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [Wc Wt].
    apply (ccond_ok c) with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply IHt with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply IHu with (rk := rk) (cbs := cbs); auto. eapply inv_step; eauto.
  - (* BMatch *) cbn [wfbr] in W. apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H & _).
    destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl. apply IH0 with (rk := rk) (cbs := cbs); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbv cbj (fst (nth c cbs cbe0)) <= 4611686018427387904)%Z) by (pose proof (proj1 Cb c) as Cb'; rewrite Ec in Cb'; exact Cb').
      pose proof KQMAuto.wB_num as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (rk := rk) (cbs := cpush_match (sigsv cbs) c :: cbs); auto. apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | eapply match_push_ok1; eauto | eapply match_push_ok2; eauto].
  - (* BSplitR *) cbn [wfbr] in W. apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [Ex Wx]. apply Nat.eqb_eq in Ex.
    apply crec_ok with (cenv := cenv) (benv := benv) (renv := renv) (denv := denv) (rk := rk) (cbs := cbs); auto. intros rho1 n1 As A1 Le1 LAs VAs.
    assert (Kx : kind_of (denote_r cs rec cenv benv renv denv M x) = KRec sj) by (rewrite <- Ex; eapply kind_denote_r; eauto).
    destruct (split_atoms rho1 As _ sj Kx VAs) as [V1 V2].
    rewrite rsplit_eq. apply IH with (rk := rev (RJ sj) ++ rk) (cbs := cbs); auto. apply inv_lets; [apply inv_rlets; [eapply inv_step; eauto | exact V2 | apply Forall_slices_kq; apply Forall_skipn_kq; exact LAs] | exact V1 | apply Forall_firstn_kq; exact LAs].
    apply rsplit_typed; [exact Kx | exact Rt].
Qed.


End Sim.

(* ---------------------------------------------------------------- the function *)
Local Open Scope nat_scope.

Lemma appn_absn : forall k m T F vs s, map kind_of vs = k ->
  appnT k m T (absnT k m T F) vs s = F (rev (vnums vs)) (rev (vbools vs)) (rev (vrecs vs)) (if m then s else dummy_mem).
Proof.
  induction k as [|c k IH]; intros m T F vs s L; destruct vs as [|v vs]; cbn [map] in L; try discriminate.
  - destruct m; reflexivity.
  - injection L as Lc L. subst c. destruct v as [x|b|ri x]; cbn [kind_of appnT absnT]; rewrite IH by auto;
      cbn [vnums vbools vrecs flat_map filter rev app]; try rewrite to_rt_same; reflexivity.
Qed.

Lemma appc_absc : forall x T F l, length l = x -> appc x T (absc x T F) l = F (rev l).
Proof.
  induction x as [|x IH]; intros T F l L; destruct l as [|c l]; simpl in *; try discriminate.
  - reflexivity.
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

Lemma params_nth : forall n k j, j < wsum k + n -> nth j (params n k) 1%positive = Pos.of_succ_nat j.
Proof.
  intros n k j L. unfold params. rewrite nth_indep with (d' := Pos.of_succ_nat 0) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma params_nodup : forall n k, NoDup (params n k).
Proof.
  intros n k. unfold params. apply FinFun.Injective_map_NoDup; [| apply seq_NoDup].
  intros a b E. apply SuccNat2Pos.inj; auto.
Qed.

Lemma params_length : forall n k, length (params n k) = wsum k + n.
Proof. intros n k. unfold params. rewrite length_map, length_seq. reflexivity. Qed.

Lemma cenv0_nth : forall n i, i < n -> nth i (cenv0 n) (Aint 0%uint63) = Avar (Pos.of_succ_nat (n - 1 - i)).
Proof.
  intros n i L. unfold cenv0.
  rewrite nth_indep with (d' := Avar (Pos.of_succ_nat 0)) by (rewrite map_length, rev_length, seq_length; lia).
  rewrite map_nth with (d := 0). rewrite rev_nth by (rewrite seq_length; lia). rewrite seq_length, seq_nth by lia.
  f_equal. f_equal. lia.
Qed.

Lemma cenv0_out : forall n i, n <= i -> nth i (cenv0 n) (Aint 0%uint63) = Aint 0%uint63.
Proof. intros n i L. apply nth_overflow. unfold cenv0. rewrite map_length, rev_length, seq_length. lia. Qed.

Lemma cenv0_lt : forall gs, lt_all (cenv0 (sn gs)) (pmv gs).
Proof.
  intros [x k m r] i. unfold pmv. simpl. destruct (Nat.lt_ge_cases i x) as [L|L].
  - rewrite cenv0_nth by auto. simpl. apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
  - rewrite cenv0_out by auto. simpl. auto.
Qed.

(** the atoms of the parameters of one kind are variables after the counters and before [pmv] *)
(** the parameters' places: a value of a kind takes [kw] places *)
Lemma vflat_len : forall v, length (vflat v) = kw (kind_of v).
Proof. intros [x|b|ri x]; cbn [vflat kind_of kw length]; [reflexivity | reflexivity | apply rl_len]. Qed.
Lemma flat_len : forall vs, length (flat_map vflat vs) = wsum (map kind_of vs).
Proof.
  induction vs as [|v vs IH]; [reflexivity|]. cbn [flat_map map]. change (wsum (kind_of v :: map kind_of vs)) with (kw (kind_of v) + wsum (map kind_of vs)).
  rewrite length_app, vflat_len, IH. reflexivity.
Qed.
Lemma kpos_in : forall ks p kp, In kp (kpos ks p) -> p <= snd kp /\ snd kp + kw (fst kp) <= p + wsum ks.
Proof.
  induction ks as [|c ks IH]; intros p kp H; cbn [kpos In] in H; [contradiction|].
  change (wsum (c :: ks)) with (kw c + wsum ks). destruct H as [<- | H]; cbn [fst snd]; [lia|]. apply IH in H. lia.
Qed.
Lemma katoms_in : forall c n ks a, kw c = 1 -> In a (katoms c n ks) -> exists q, a = Avar (Pos.of_succ_nat q) /\ n <= q < n + wsum ks.
Proof.
  intros c n ks a Kc H. unfold katoms in H. apply in_rev in H. apply in_map_iff in H as (kp & <- & H).
  apply filter_In in H as [H Hc]. apply kind_eqb_eq in Hc. apply kpos_in in H. rewrite Hc, Kc in H.
  exists (snd kp). split; [reflexivity | lia].
Qed.
Lemma katoms_lt : forall c gs, kw c = 1 -> lt_all (katoms c (sn gs) (sk gs)) (pmv gs).
Proof.
  intros c [x k m r] Kc i. unfold pmv. cbn [sn sk].
  destruct (nth_in_or_default i (katoms c x k) (Aint 0%uint63)) as [H | H].
  - apply katoms_in in H as (q & E & L); [|exact Kc]. rewrite E. simpl. apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
  - rewrite H. simpl. auto.
Qed.
Lemma env0_lt : forall gs, lt_all (env0 (sn gs) (sk gs)) (pmv gs).
Proof. intro gs. apply katoms_lt; reflexivity. Qed.
Lemma benv0_lt : forall gs, lt_all (benv0 (sn gs) (sk gs)) (pmv gs).
Proof. intro gs. apply katoms_lt; reflexivity. Qed.
Lemma renv0_lt : forall gs, rlt_all (renv0 (sn gs) (sk gs)) (pmv gs).
Proof.
  intros [x k m r]. unfold renv0, rlt_all, pmv. cbn [sn sk]. apply Forall_rev. apply Forall_forall. intros As H.
  apply in_map_iff in H as (kp & <- & H). apply filter_In in H as [H _]. apply kpos_in in H.
  apply Forall_forall. intros a Ha. apply in_map_iff in Ha as (q & <- & Hq). apply in_seq in Hq.
  simpl. apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
Qed.

(** the atoms of the parameters of one kind hold the values of that kind, in order *)
Lemma katoms_num : forall vs ks p rho, map kind_of vs = ks ->
  (forall q, q < length (flat_map vflat vs) -> rho ! (Pos.of_succ_nat (p + q)) = Some (nth q (flat_map vflat vs) 0%uint63)) ->
  Forall2 (fun a x => aval rho a = Some x)
          (map (fun kp => Avar (Pos.of_succ_nat (snd kp))) (filter (fun kp => kind_eqb (fst kp) KNum) (kpos ks p))) (vnums vs).
Proof.
  induction vs as [|v vs IH]; intros ks p rho K H; destruct ks as [|c ks]; cbn [map] in K; try discriminate; [constructor|].
  injection K as Kc Ks. subst c.
  assert (H' : forall q, q < length (flat_map vflat vs) ->
                 rho ! (Pos.of_succ_nat (p + kw (kind_of v) + q)) = Some (nth q (flat_map vflat vs) 0%uint63)).
  { intros q Lq. rewrite <- vflat_len, <- Nat.add_assoc. rewrite (H (length (vflat v) + q)) by (cbn [flat_map]; rewrite length_app; lia).
    cbn [flat_map]. rewrite app_nth2 by lia. f_equal. f_equal. lia. }
  cbn [kpos filter]. destruct v as [x|b|ri x]; cbn [kind_of kind_eqb fst snd map vnums flat_map].
  - constructor; [| apply IH; auto]. simpl. pose proof (H 0 ltac:(simpl; lia)) as H0. rewrite Nat.add_0_r in H0. exact H0.
  - apply IH; auto.
  - apply IH; auto.
Qed.
Lemma katoms_bool : forall vs ks p rho, map kind_of vs = ks ->
  (forall q, q < length (flat_map vflat vs) -> rho ! (Pos.of_succ_nat (p + q)) = Some (nth q (flat_map vflat vs) 0%uint63)) ->
  Forall2 (fun a x => aval rho a = Some (b2i x))
          (map (fun kp => Avar (Pos.of_succ_nat (snd kp))) (filter (fun kp => kind_eqb (fst kp) KBool) (kpos ks p))) (vbools vs).
Proof.
  induction vs as [|v vs IH]; intros ks p rho K H; destruct ks as [|c ks]; cbn [map] in K; try discriminate; [constructor|].
  injection K as Kc Ks. subst c.
  assert (H' : forall q, q < length (flat_map vflat vs) ->
                 rho ! (Pos.of_succ_nat (p + kw (kind_of v) + q)) = Some (nth q (flat_map vflat vs) 0%uint63)).
  { intros q Lq. rewrite <- vflat_len, <- Nat.add_assoc. rewrite (H (length (vflat v) + q)) by (cbn [flat_map]; rewrite length_app; lia).
    cbn [flat_map]. rewrite app_nth2 by lia. f_equal. f_equal. lia. }
  cbn [kpos filter]. destruct v as [x|b|ri x]; cbn [kind_of kind_eqb fst snd map vbools flat_map].
  - apply IH; auto.
  - constructor; [| apply IH; auto]. simpl. pose proof (H 0 ltac:(simpl; lia)) as H0. rewrite Nat.add_0_r in H0. exact H0.
  - apply IH; auto.
Qed.
Lemma avals_seq : forall rho p m L, m <= length L ->
  (forall q, q < length L -> rho ! (Pos.of_succ_nat (p + q)) = Some (nth q L 0%uint63)) ->
  avals rho (map (fun q => Avar (Pos.of_succ_nat q)) (seq p m)) = Some (firstn m L).
Proof.
  intros rho p m. revert p. induction m as [|m IH]; intros p L Lm H; [reflexivity|]. destruct L as [|x L]; [cbn [length] in Lm; lia|].
  cbn [seq map avals firstn]. pose proof (H 0 ltac:(simpl; lia)) as H0. rewrite Nat.add_0_r in H0. cbn [aval]. rewrite H0.
  rewrite (IH (S p) L); [reflexivity | cbn [length] in Lm; lia |].
  intros q Lq. rewrite Nat.add_succ_l, <- Nat.add_succ_r. rewrite (H (S q)) by (simpl; lia). reflexivity.
Qed.
Lemma katoms_rec : forall vs ks p rho, map kind_of vs = ks ->
  (forall q, q < length (flat_map vflat vs) -> rho ! (Pos.of_succ_nat (p + q)) = Some (nth q (flat_map vflat vs) 0%uint63)) ->
  Forall2 (fun As v => avals rho As = Some (vflat v))
          (map (fun kp => map (fun q => Avar (Pos.of_succ_nat q)) (seq (snd kp) (kw (fst kp)))) (filter (fun kp => is_rk (fst kp)) (kpos ks p)))
          (vrecs vs).
Proof.
  induction vs as [|v vs IH]; intros ks p rho K H; destruct ks as [|c ks]; cbn [map] in K; try discriminate; [constructor|].
  injection K as Kc Ks. subst c.
  assert (H' : forall q, q < length (flat_map vflat vs) ->
                 rho ! (Pos.of_succ_nat (p + kw (kind_of v) + q)) = Some (nth q (flat_map vflat vs) 0%uint63)).
  { intros q Lq. rewrite <- vflat_len, <- Nat.add_assoc. rewrite (H (length (vflat v) + q)) by (cbn [flat_map]; rewrite length_app; lia).
    cbn [flat_map]. rewrite app_nth2 by lia. f_equal. f_equal. lia. }
  cbn [kpos filter]. destruct v as [x|b|ri x]; cbn [kind_of is_rk fst snd map vrecs filter].
  - apply IH; auto.
  - apply IH; auto.
  - constructor; [| apply IH; auto].
    replace (kw (KRec ri)) with (length (vflat (VRec ri x))) by apply vflat_len.
    rewrite (avals_seq rho p (length (vflat (VRec ri x))) (flat_map vflat (VRec ri x :: vs))).
    + cbn [flat_map]. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity.
    + cbn [flat_map]. rewrite length_app. lia.
    + exact H.
Qed.
Lemma Forall2_rev2 : forall (A B : Type) (R : A -> B -> Prop) l l', Forall2 R l l' -> Forall2 R (rev l) (rev l').
Proof. intros A B R l l' F. induction F; simpl; [constructor|]. apply Forall2_app; auto. Qed.
Lemma F2_env_ok : forall rho As xs, Forall2 (fun a x => aval rho a = Some x) As xs -> env_ok rho As xs.
Proof.
  intros rho As xs F i. revert i. induction F as [|a x As xs H F IH]; intros i; [destruct i; reflexivity|].
  destruct i as [|i]; [exact H | apply IH].
Qed.
Lemma F2_benv_ok : forall rho As xs, Forall2 (fun a x => aval rho a = Some (b2i x)) As xs -> benv_ok rho As xs.
Proof.
  intros rho As xs F i. revert i. induction F as [|a x As xs H F IH]; intros i; [destruct i; reflexivity|].
  destruct i as [|i]; [exact H | apply IH].
Qed.

(** the parameters bound: the counters in 1 .. n, the others after them in the user's order (a record its fields), read by
    [cenv0] / [env0] / [benv0] / [renv0] in [denote_f]'s order *)
Lemma bind_params : forall n k cvs vs, length cvs = n -> map kind_of vs = k ->
  exists rho0, bind (params n k) (map ofn cvs ++ flat_map vflat vs) (PTree.empty _) = Some rho0 /\
    cenv_ok rho0 (cenv0 n) (rev cvs) /\ env_ok rho0 (env0 n k) (rev (vnums vs)) /\ benv_ok rho0 (benv0 n k) (rev (vbools vs)) /\
    renv_ok rho0 (renv0 n k) (rev (vrecs vs)).
Proof.
  intros n k cvs vs Lc Lv.
  assert (Lk : length (flat_map vflat vs) = wsum k) by (rewrite flat_len, Lv; reflexivity).
  destruct (bind_some (params n k) (map ofn cvs ++ flat_map vflat vs) (PTree.empty _)) as [rho0 B].
  { rewrite params_length, length_app, length_map. lia. }
  assert (HV : forall q, q < length (flat_map vflat vs) -> rho0 ! (Pos.of_succ_nat (n + q)) = Some (nth q (flat_map vflat vs) 0%uint63)).
  { intros q Lq. pose proof (bind_nth _ _ _ _ (n + q) (params_nodup n k) B) as N.
    rewrite params_nth in N by lia. rewrite N by (rewrite params_length; lia).
    rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
    replace (n + q - length cvs) with q by lia. reflexivity. }
  exists rho0. split; auto. split; [|split; [|split]].
  - intro i. destruct (Nat.lt_ge_cases i n) as [Li|Li].
    + rewrite cenv0_nth by auto. simpl.
      pose proof (bind_nth _ _ _ _ (n - 1 - i) (params_nodup n k) B) as N.
      rewrite params_nth in N by lia. rewrite N by (rewrite params_length; lia).
      rewrite app_nth1 by (rewrite length_map; lia).
      rewrite nth_indep with (d' := ofn O) by (rewrite length_map; lia). rewrite map_nth.
      rewrite rev_nth by lia. f_equal. f_equal. f_equal. lia.
    + rewrite cenv0_out by auto. rewrite nth_overflow by (rewrite length_rev; lia). reflexivity.
  - apply F2_env_ok. unfold env0, katoms. apply Forall2_rev2. apply katoms_num; auto.
  - apply F2_benv_ok. unfold benv0, katoms. apply Forall2_rev2. apply katoms_bool; auto.
  - unfold renv0, renv_ok. apply Forall2_rev2. apply katoms_rec; auto.
Qed.

Lemma cenv0_first : forall x n rest rho, length rest = x -> cenv_ok rho (cenv0 (S x)) (rev (n :: rest)) ->
  rho ! 1%positive = Some (ofn n).
Proof.
  intros x n rest rho L C. specialize (C x). rewrite cenv0_nth in C by lia.
  replace (S x - 1 - x) with 0 in C by lia. simpl in C.
  rewrite app_nth2 in C by (rewrite rev_length; lia). rewrite rev_length, L, Nat.sub_diag in C. exact C.
Qed.

Lemma Forall_cbound : forall B l, (0 < B)%Z -> Forall (fun c => (Z.of_nat c < B)%Z) l -> cbound B l.
Proof.
  intros B l Hp F. induction F as [|c l Hc F IH]; intros i; simpl.
  - destruct i; simpl; lia.
  - destruct i as [|i]; [exact Hc | apply IH].
Qed.

Lemma Forall_rev_cbound : forall B l, (0 < B)%Z -> Forall (fun c => (Z.of_nat c < B)%Z) l -> cbound B (rev l).
Proof. intros B l Hp F. apply Forall_cbound; auto. apply Forall_rev. exact F. Qed.

(** a function giving back a record (step 12, part 3): its KQL returns the first field and leaves the slot block written with
    the others *)
(** the record parameters in scope at the start of a body have the types the signature gives them *)
Lemma rtyped0 : forall vs k, map kind_of vs = k -> rtyped (rev (vrecs vs)) (rk0 k).
Proof.
  unfold rtyped, rk0, vrecs. intros vs k <-. rewrite !map_rev. f_equal.
  induction vs as [|v vs IH]; [reflexivity|]. destruct v; simpl; [exact IH | exact IH | f_equal; exact IH].
Qed.

(** the bound of a function's counters has room (step 35: [cboundv] carries it) *)
Lemma cbj_le4 : forall bo j, bok bo = true -> ((match bo with Some b0 => b0 | None => cbz j end) <= 4611686018427387904)%Z.
Proof. intros bo j H. destruct bo as [b0|]; [unfold bok in H; apply andb_true_iff in H as [_ H2]; apply Z.leb_le in H2; exact H2 | unfold cbz; lia]. Qed.

(** the counters given (steps 37 to 39): each below the bound, through a polynomial where its own monomial has a coefficient
    of at least 1 *)
Lemma cfits_forall : forall gs B cvs, swok gs = true -> length cvs = sn gs -> cfits gs B cvs -> Forall (fun c => (Z.of_nat c < B)%Z) cvs.
Proof.
  intros gs B cvs Sw L C. unfold swok in Sw. apply andb_true_iff in Sw as [Sw _]. unfold swok0, cfits in *. destruct (sv gs) as [|v vs]; [exact C|].
  rewrite forallb_forall in Sw. rewrite Forall_forall in C.
  apply Forall_forall. intros c Hc. apply (In_nth cvs c O) in Hc as (i & Hi & <-).
  specialize (Sw i ltac:(apply in_seq; lia)). apply existsb_exists in Sw as (P0 & HP & Hm).
  apply existsb_exists in Hm as ([c0 l0] & Hm & Hm1). cbn [fst snd] in Hm1.
  apply andb_true_iff in Hm1 as [H1 H2]. apply Nat.leb_le in H1.
  destruct (list_eq_dec Nat.eq_dec l0 [i]) as [->|Ne]; [|cbn in H2; discriminate H2].
  pose proof (pevalz_unit P0 c0 i (map Z.of_nat cvs) Hm H1 (nth_ofnat_nonneg cvs)) as U. rewrite nth_ofnat in U.
  specialize (C P0 HP). lia.
Qed.
Lemma evc_rev_dotw : forall ws cvs, length ws = length cvs -> evc (map Z.of_nat (rev ws)) (rev cvs) = Z.of_nat (dotw ws cvs).
Proof.
  induction ws as [|w ws IH]; intros [|c cvs] L; cbn [length] in L; try discriminate; [reflexivity|].
  cbn [rev dotw]. rewrite map_app. cbn [map]. rewrite evc_app by (rewrite length_map, !length_rev; lia). rewrite IH by lia.
  cbn [evc]. lia.
Qed.
(** a recursive body of a function with weights: what the body's proof assumes of its counters *)
Lemma hpv_rec : forall (hp : bool) gs B n' rest x', swok gs = true -> sn gs = S x' -> length rest = x' -> cfits gs B (S n' :: rest) ->
  hp = true -> sv gs <> [] ->
  exists rest0, rev rest ++ [S n'] = rev rest0 ++ [S n'] /\ length rest0 = x' /\
  Forall (fun P => (pevalz P (map Z.of_nat (S n' :: rest0)) < B)%Z) (sv gs).
Proof.
  intros hp gs B n' rest x' Sw Sn L C _ Ne. unfold cfits in C. destruct (sv gs) as [|v vs]; [contradiction|].
  exists rest. split; [reflexivity|]. split; [exact L | exact C].
Qed.
(** the predecessor of the first counter, below its linear bound *)
Lemma pred_lin : forall n' rest x', length rest = x' -> (Z.of_nat n' <= leval (lshift (-1) (lunit x')) (rev rest ++ [S n']))%Z.
Proof.
  intros n' rest x' L. rewrite leval_shift, leval_unit. rewrite app_nth2 by (rewrite length_rev; lia).
  rewrite length_rev, L, Nat.sub_diag. cbn [nth]. lia.
Qed.

Lemma compile_f_ok_rec : forall P cs gidf j x k m r w ri b bo vw,
  find P (gidf j) = Some (compile_f gidf j (mksig8 x k m r w (Some (KRec ri)) bo vw) b) ->
  wf_f (map (@projT1 _ _) cs) (mksig8 x k m r w (Some (KRec ri)) bo vw) b = true -> callees_ok P gidf cs ->
  (length cs <= j)%nat -> (Z.of_nat j < 1099511627776)%Z ->
  callee_ok P (gidf j) (match bo with Some b0 => b0 | None => cbz j end) (mksig8 x k m r w (Some (KRec ri)) bo vw) (denote_f cs (mksig8 x k m r w (Some (KRec ri)) bo vw) b).
Proof.
  intros P cs gidf j x k m r w ri b bo vw Hf W Hcs Hlen Hj. cbn [wf_f] in W. apply andb_true_iff in W as [Hbok W]. apply andb_true_iff in Hbok as [Hbok Hsw]. cbn [sb] in Hbok.
  cbn [wf_f sq sr sw sn sk sm] in W.
  apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [W Ww]. apply andb_true_iff in W as [W Wr].
  apply andb_true_iff in W as [R1n R2n]. apply Nat.leb_le in R1n. apply Z.leb_le in R2n.
  destruct r; cbn in Wr; [discriminate Wr|]. destruct w; cbn in Ww; [discriminate Ww|].
  unfold callee_ok. intros Hsl. cbn [sn sk sm sr sw sq].
  set (mv := pmv (mksig8 x k m false false (Some (KRec ri)) bo vw)).
  assert (Lmv : lt_all (env0 x k) mv) by apply (env0_lt (mksig8 x k m false false (Some (KRec ri)) bo vw)).
  assert (LCmv : lt_all (cenv0 x) mv) by apply (cenv0_lt (mksig8 x k m false false (Some (KRec ri)) bo vw)).
  assert (LBmv : lt_all (benv0 x k) mv) by apply (benv0_lt (mksig8 x k m false false (Some (KRec ri)) bo vw)).
  assert (LRmv : rlt_all (renv0 x k) mv) by apply (renv0_lt (mksig8 x k m false false (Some (KRec ri)) bo vw)).
  assert (Bpos : (0 < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (unfold bok in Hbok; destruct bo as [b0|]; [apply andb_true_iff in Hbok as [H1 H2]; apply Z.ltb_lt in H1; apply Z.leb_le in H2; rewrite ?KQMAuto.wB_num; lia | unfold cbz; rewrite ?KQMAuto.wB_num; lia]).
  assert (BwB : ((match bo with Some b0 => b0 | None => cbz j end) < wB)%Z) by (unfold bok in Hbok; destruct bo as [b0|]; [apply andb_true_iff in Hbok as [H1 H2]; apply Z.ltb_lt in H1; apply Z.leb_le in H2; rewrite ?KQMAuto.wB_num; lia | unfold cbz; rewrite ?KQMAuto.wB_num; lia]).
  destruct b as [e0 e1 | e | m0 m1 | e | xx | x0 x1 | b0 b1 | bb | c0 c1 | cb | d0 d1 | db]; try discriminate Wb.
  - (* recursive on the first counter *)
    destruct x as [|x']; simpl in Wb; [discriminate Wb|]. apply andb_true_iff in Wb as [Wb0 Wb1].
    assert (Mvgt : Pos.lt 1 mv).
    { unfold mv, pmv. simpl. apply Pos2Nat.inj_lt. rewrite SuccNat2Pos.id_succ. simpl. lia. }
    intros cvs vs M Lc Lv Bd. cbv beta iota. destruct cvs as [|n rest]; [simpl in Lc; discriminate|].
    simpl in Lc. injection Lc as Lc.
    revert rest vs M Lc Lv Bd. induction n as [|n' IH]; intros rest vs M Lc Lv Bd.
    + destruct (bind_params (S x') k (0 :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      assert (V : callf (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) (denote_f cs (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) (FRecR b0 b1)) (0 :: rest) vs M
                  = denote_br cs dnum ri (drec ri) (rev rest ++ [0]) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M b0).
      { change (callf (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) (denote_f cs (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) (FRecR b0 b1)) (0 :: rest) vs M)
          with (appnT k m (RT ri) (appc x' _ (absc x' _ (fun cenv => absnT k m (RT ri) (fun env benv renv s =>
                  denote_br cs dnum ri (drec ri) (cenv ++ [0]) benv renv env s b0))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto.
        destruct m; [reflexivity|]. eapply denote_br_nomem; [intros; reflexivity | intros; reflexivity | exact Wb0]. }
      unfold calln, callm. cbn [sq sr]. rewrite V.
      exists (compile_f gidf j (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) (FRecR b0 b1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      simpl kbody.
      pose proof (cenv0_first x' 0 rest rho0 Lc C0) as R1.
      eapply K_if; [simpl; exact R1 | reflexivity | ]. rewrite ofn_0. simpl.
      refine (ctailr_ok P _ gidf (gidf j) mv cs false false false m x' k j dnum dmem 0 false dnum bo vw (rev rest ++ [0]) _ (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf ri (drec ri) false _ _ R1n R2n b0 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] Wb0 _ (rtyped0 vs k Lv)).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- exact E0.
        -- eapply lt_all_mono; eauto. lia.
        -- exact C0.
        -- eapply lt_all_mono; [exact LCmv | lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- exact (cboundv_nil _ _ (Forall_rev_cbound _ (0 :: rest) Bpos (cfits_forall _ _ (0 :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
        -- lia.
        -- intros Habs; discriminate Habs.
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
    + destruct (bind_params (S x') k (S n' :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      set (dfn := denote_f cs (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) (FRecR b0 b1)).
      assert (V : callf (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) dfn (S n' :: rest) vs M
                  = denote_br cs dnum ri (fun cvs args s' => appnT k m (RT ri) (appc x' _ (dfn n') cvs) args s') (n' :: rev rest ++ [S n'])
                      (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M b1).
      { change (callf (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) dfn (S n' :: rest) vs M)
          with (appnT k m (RT ri) (appc x' _ (absc x' _ (fun cenv => absnT k m (RT ri) (fun env benv renv s =>
                  denote_br cs dnum ri (fun cvs args s' => appnT k m (RT ri) (appc x' _ (dfn n') cvs) args s') (n' :: cenv ++ [S n'])
                    benv renv env s b1))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto.
        destruct m; [reflexivity|]. eapply denote_br_nomem; [intros; reflexivity | | exact Wb1].
        intros cvs l. cbv beta. apply appnT_false. }
      unfold calln, callm. cbn [sq sr]. rewrite V.
      exists (compile_f gidf j (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) (FRecR b0 b1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      simpl kbody.
      pose proof (cenv0_first x' (S n') rest rho0 Lc C0) as R1.
      assert (Bn : (Z.of_nat (S n') < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (pose proof (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd) as BdF'; inversion BdF'; auto).
      eapply K_if; [simpl; exact R1 | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
      eapply K_op; [simpl; exact R1 | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      refine (ctailr_ok P _ gidf (gidf j) mv cs false false true m x' k j dnum dmem n' false dnum bo vw (rev rest ++ [S n']) _ (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) _ Hcs Hlen Hj Hsl Hbok (hpv_rec true _ _ n' rest x' Hsw eq_refl Lc Bd) (fun _ _ => Forall_rev (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) Hf ri (fun cvs args s' => appnT k m (RT ri) (appc x' _ (dfn n') cvs) args s') true _ _ R1n R2n b1 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [(None, lshift (-1) (lunit x'))] Wb1 _ (rtyped0 vs k Lv)).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros _ cvs vs' M' Lc' Lv' Bd'. assert (Bn' : (Z.of_nat n' < (match bo with Some b0 => b0 | None => cbz j end))%Z) by lia.
        apply (IH cvs vs' M' Lc' Lv'). destruct vw as [|w0 ws0]; [constructor; [exact Bn' | exact Bd'] | exact Bd'].
      * intros _. reflexivity.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- eapply env_ok_agree; [exact E0 | exact Lmv | apply agree_set; apply Pos.le_refl].
        -- eapply lt_all_mono; eauto. lia.
        -- apply cenv_ok_cons; [eapply cenv_ok_agree; [exact C0 | exact LCmv | apply agree_set; apply Pos.le_refl] | simpl; apply PTree.gss].
        -- apply lt_all_cons; [eapply lt_all_mono; [exact LCmv | lia] | simpl; lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- apply cboundv_cons; [exact (cboundv_nil _ _ (Forall_rev_cbound _ (S n' :: rest) Bpos (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)) | cbn [fst cbv]; pose proof (cbj_le4 bo j Hbok); lia | exact (pred_lin n' rest x' Lc)].
        -- lia.
        -- intros _. split; [apply PTree.gss | lia].
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
  - (* plain *)
    intros cvs vs M Lc Lv Bd. cbv beta iota.
    destruct (bind_params x k cvs vs Lc Lv) as (rho0 & Bd0 & C0 & E0 & B0 & R0).
    assert (V : callf (mksig8 x k m false false (Some (KRec ri)) bo vw) (denote_f cs (mksig8 x k m false false (Some (KRec ri)) bo vw) (FPlainR bb)) cvs vs M
                = denote_br cs dnum ri (drec ri) (rev cvs) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M bb).
    { destruct x as [|x'].
      - destruct cvs; [|discriminate].
        change (callf (mksig8 0 k m false false (Some (KRec ri)) bo vw) (denote_f cs (mksig8 0 k m false false (Some (KRec ri)) bo vw) (FPlainR bb)) [] vs M)
          with (appnT k m (RT ri) (absnT k m (RT ri) (fun env benv renv s => denote_br cs dnum ri (drec ri) [] benv renv env s bb)) vs M).
        rewrite appn_absn by auto. destruct m; [reflexivity|]. eapply denote_br_nomem; [intros; reflexivity | intros; reflexivity | eauto].
      - destruct cvs as [|n rest]; [discriminate|]. simpl in Lc. injection Lc as Lc.
        change (callf (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) (denote_f cs (mksig8 (S x') k m false false (Some (KRec ri)) bo vw) (FPlainR bb)) (n :: rest) vs M)
          with (appnT k m (RT ri) (appc x' _ (absc x' _ (fun cenv => absnT k m (RT ri) (fun env benv renv s =>
                  denote_br cs dnum ri (drec ri) (cenv ++ [n]) benv renv env s bb))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto. destruct m; [reflexivity|].
        eapply denote_br_nomem; [intros; reflexivity | intros; reflexivity | eauto]. }
    unfold calln, callm. cbn [sq sr]. rewrite V.
    exists (compile_f gidf j (mksig8 x k m false false (Some (KRec ri)) bo vw) (FPlainR bb)), rho0. split; [exact Hf|]. split; [exact Bd0|].
    simpl kbody.
    refine (ctailr_ok P _ gidf (gidf j) mv cs false false false m 0 k j dnum dmem 0 false dnum bo vw (rev cvs) _ (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf ri (drec ri) false _ _ R1n R2n bb _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] Wb _ (rtyped0 vs k Lv)).
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      * exact E0.
      * eapply lt_all_mono; eauto. lia.
      * exact C0.
      * eapply lt_all_mono; [exact LCmv | lia].
      * first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
      * eapply lt_all_mono; [exact LBmv | lia].
      * exact (cboundv_nil _ _ (Forall_rev_cbound _ cvs Bpos (cfits_forall _ _ cvs Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
      * lia.
      * intros Habs; discriminate Habs.
      * first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
      * eapply rlt_all_mono; [exact LRmv | lia].
Qed.

Lemma compile_f_ok_bool : forall P cs gidf j x k m r w b bo vw,
  find P (gidf j) = Some (compile_f gidf j (mksig8 x k m r w (Some KBool) bo vw) b) ->
  wf_f (map (@projT1 _ _) cs) (mksig8 x k m r w (Some KBool) bo vw) b = true -> callees_ok P gidf cs ->
  (length cs <= j)%nat -> (Z.of_nat j < 1099511627776)%Z ->
  callee_ok P (gidf j) (match bo with Some b0 => b0 | None => cbz j end) (mksig8 x k m r w (Some KBool) bo vw) (denote_f cs (mksig8 x k m r w (Some KBool) bo vw) b).
Proof.
  intros P cs gidf j x k m r w b bo vw Hf W Hcs Hlen Hj. cbn [wf_f] in W. apply andb_true_iff in W as [Hbok W]. apply andb_true_iff in Hbok as [Hbok Hsw]. cbn [sb] in Hbok.
  cbn [wf_f sq sr sw sn sk sm] in W.
  apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [Wr Ww].
  destruct r; cbn in Wr; [discriminate Wr|]. destruct w; cbn in Ww; [discriminate Ww|].
  unfold callee_ok. intros Hsl. cbn [sn sk sm sr sw sq].
  set (mv := pmv (mksig8 x k m false false (Some KBool) bo vw)).
  assert (Lmv : lt_all (env0 x k) mv) by apply (env0_lt (mksig8 x k m false false (Some KBool) bo vw)).
  assert (LCmv : lt_all (cenv0 x) mv) by apply (cenv0_lt (mksig8 x k m false false (Some KBool) bo vw)).
  assert (LBmv : lt_all (benv0 x k) mv) by apply (benv0_lt (mksig8 x k m false false (Some KBool) bo vw)).
  assert (LRmv : rlt_all (renv0 x k) mv) by apply (renv0_lt (mksig8 x k m false false (Some KBool) bo vw)).
  assert (Bpos : (0 < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (unfold bok in Hbok; destruct bo as [b0|]; [apply andb_true_iff in Hbok as [H1 H2]; apply Z.ltb_lt in H1; apply Z.leb_le in H2; rewrite ?KQMAuto.wB_num; lia | unfold cbz; rewrite ?KQMAuto.wB_num; lia]).
  assert (BwB : ((match bo with Some b0 => b0 | None => cbz j end) < wB)%Z) by (unfold bok in Hbok; destruct bo as [b0|]; [apply andb_true_iff in Hbok as [H1 H2]; apply Z.ltb_lt in H1; apply Z.leb_le in H2; rewrite ?KQMAuto.wB_num; lia | unfold cbz; rewrite ?KQMAuto.wB_num; lia]).
  destruct b as [e0 e1 | e | m0 m1 | e | xx | x0 x1 | r0 r1 | rb | b0 b1 | bb | d0 d1 | db]; try discriminate Wb.
  - (* recursive on the first counter *)
    destruct x as [|x']; simpl in Wb; [discriminate Wb|]. apply andb_true_iff in Wb as [Wb0 Wb1].
    assert (Mvgt : Pos.lt 1 mv).
    { unfold mv, pmv. simpl. apply Pos2Nat.inj_lt. rewrite SuccNat2Pos.id_succ. simpl. lia. }
    intros cvs vs M Lc Lv Bd. cbv beta iota. destruct cvs as [|n rest]; [simpl in Lc; discriminate|].
    simpl in Lc. injection Lc as Lc.
    revert rest vs M Lc Lv Bd. induction n as [|n' IH]; intros rest vs M Lc Lv Bd.
    + destruct (bind_params (S x') k (0 :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      assert (V : callf (mksig8 (S x') k m false false (Some KBool) bo vw) (denote_f cs (mksig8 (S x') k m false false (Some KBool) bo vw) (FRecB b0 b1)) (0 :: rest) vs M
                  = denote_bb cs dnum dbool (rev rest ++ [0]) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M b0).
      { change (callf (mksig8 (S x') k m false false (Some KBool) bo vw) (denote_f cs (mksig8 (S x') k m false false (Some KBool) bo vw) (FRecB b0 b1)) (0 :: rest) vs M)
          with (appnT k m (bool) (appc x' _ (absc x' _ (fun cenv => absnT k m (bool) (fun env benv renv s =>
                  denote_bb cs dnum dbool (cenv ++ [0]) benv renv env s b0))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto.
        destruct m; [reflexivity|]. eapply denote_bb_nomem; [intros; reflexivity | intros; reflexivity | exact Wb0]. }
      unfold calln, callm. cbn [sq sr]. rewrite V.
      exists (compile_f gidf j (mksig8 (S x') k m false false (Some KBool) bo vw) (FRecB b0 b1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      simpl kbody.
      pose proof (cenv0_first x' 0 rest rho0 Lc C0) as R1.
      eapply K_if; [simpl; exact R1 | reflexivity | ]. rewrite ofn_0. simpl.
      refine (ctailb_ok P _ gidf (gidf j) mv cs false false false m x' k j dnum dmem 0 false dnum bo vw (rev rest ++ [0]) _ (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf dbool false _ _ b0 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] Wb0 _ (rtyped0 vs k Lv)).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- exact E0.
        -- eapply lt_all_mono; eauto. lia.
        -- exact C0.
        -- eapply lt_all_mono; [exact LCmv | lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- exact (cboundv_nil _ _ (Forall_rev_cbound _ (0 :: rest) Bpos (cfits_forall _ _ (0 :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
        -- lia.
        -- intros Habs; discriminate Habs.
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
    + destruct (bind_params (S x') k (S n' :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      set (dfn := denote_f cs (mksig8 (S x') k m false false (Some KBool) bo vw) (FRecB b0 b1)).
      assert (V : callf (mksig8 (S x') k m false false (Some KBool) bo vw) dfn (S n' :: rest) vs M
                  = denote_bb cs dnum (fun cvs args s' => appnT k m (bool) (appc x' _ (dfn n') cvs) args s') (n' :: rev rest ++ [S n'])
                      (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M b1).
      { change (callf (mksig8 (S x') k m false false (Some KBool) bo vw) dfn (S n' :: rest) vs M)
          with (appnT k m (bool) (appc x' _ (absc x' _ (fun cenv => absnT k m (bool) (fun env benv renv s =>
                  denote_bb cs dnum (fun cvs args s' => appnT k m (bool) (appc x' _ (dfn n') cvs) args s') (n' :: cenv ++ [S n'])
                    benv renv env s b1))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto.
        destruct m; [reflexivity|]. eapply denote_bb_nomem; [intros; reflexivity | | exact Wb1].
        intros cvs l. cbv beta. apply appnT_false. }
      unfold calln, callm. cbn [sq sr]. rewrite V.
      exists (compile_f gidf j (mksig8 (S x') k m false false (Some KBool) bo vw) (FRecB b0 b1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      simpl kbody.
      pose proof (cenv0_first x' (S n') rest rho0 Lc C0) as R1.
      assert (Bn : (Z.of_nat (S n') < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (pose proof (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd) as BdF'; inversion BdF'; auto).
      eapply K_if; [simpl; exact R1 | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
      eapply K_op; [simpl; exact R1 | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      refine (ctailb_ok P _ gidf (gidf j) mv cs false false true m x' k j dnum dmem n' false dnum bo vw (rev rest ++ [S n']) _ (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) _ Hcs Hlen Hj Hsl Hbok (hpv_rec true _ _ n' rest x' Hsw eq_refl Lc Bd) (fun _ _ => Forall_rev (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) Hf (fun cvs args s' => appnT k m bool (appc x' _ (dfn n') cvs) args s') true _ _ b1 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [(None, lshift (-1) (lunit x'))] Wb1 _ (rtyped0 vs k Lv)).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros _ cvs vs' M' Lc' Lv' Bd'. assert (Bn' : (Z.of_nat n' < (match bo with Some b0 => b0 | None => cbz j end))%Z) by lia.
        apply (IH cvs vs' M' Lc' Lv'). destruct vw as [|w0 ws0]; [constructor; [exact Bn' | exact Bd'] | exact Bd'].
      * intros _. reflexivity.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- eapply env_ok_agree; [exact E0 | exact Lmv | apply agree_set; apply Pos.le_refl].
        -- eapply lt_all_mono; eauto. lia.
        -- apply cenv_ok_cons; [eapply cenv_ok_agree; [exact C0 | exact LCmv | apply agree_set; apply Pos.le_refl] | simpl; apply PTree.gss].
        -- apply lt_all_cons; [eapply lt_all_mono; [exact LCmv | lia] | simpl; lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- apply cboundv_cons; [exact (cboundv_nil _ _ (Forall_rev_cbound _ (S n' :: rest) Bpos (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)) | cbn [fst cbv]; pose proof (cbj_le4 bo j Hbok); lia | exact (pred_lin n' rest x' Lc)].
        -- lia.
        -- intros _. split; [apply PTree.gss | lia].
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
  - (* plain *)
    intros cvs vs M Lc Lv Bd. cbv beta iota.
    destruct (bind_params x k cvs vs Lc Lv) as (rho0 & Bd0 & C0 & E0 & B0 & R0).
    assert (V : callf (mksig8 x k m false false (Some KBool) bo vw) (denote_f cs (mksig8 x k m false false (Some KBool) bo vw) (FPlainB bb)) cvs vs M
                = denote_bb cs dnum dbool (rev cvs) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M bb).
    { destruct x as [|x'].
      - destruct cvs; [|discriminate].
        change (callf (mksig8 0 k m false false (Some KBool) bo vw) (denote_f cs (mksig8 0 k m false false (Some KBool) bo vw) (FPlainB bb)) [] vs M)
          with (appnT k m (bool) (absnT k m (bool) (fun env benv renv s => denote_bb cs dnum dbool [] benv renv env s bb)) vs M).
        rewrite appn_absn by auto. destruct m; [reflexivity|]. eapply denote_bb_nomem; [intros; reflexivity | intros; reflexivity | eauto].
      - destruct cvs as [|n rest]; [discriminate|]. simpl in Lc. injection Lc as Lc.
        change (callf (mksig8 (S x') k m false false (Some KBool) bo vw) (denote_f cs (mksig8 (S x') k m false false (Some KBool) bo vw) (FPlainB bb)) (n :: rest) vs M)
          with (appnT k m (bool) (appc x' _ (absc x' _ (fun cenv => absnT k m (bool) (fun env benv renv s =>
                  denote_bb cs dnum dbool (cenv ++ [n]) benv renv env s bb))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto. destruct m; [reflexivity|].
        eapply denote_bb_nomem; [intros; reflexivity | intros; reflexivity | eauto]. }
    unfold calln, callm. cbn [sq sr]. rewrite V.
    exists (compile_f gidf j (mksig8 x k m false false (Some KBool) bo vw) (FPlainB bb)), rho0. split; [exact Hf|]. split; [exact Bd0|].
    simpl kbody.
    refine (ctailb_ok P _ gidf (gidf j) mv cs false false false m 0 k j dnum dmem 0 false dnum bo vw (rev cvs) _ (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf dbool false _ _ bb _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] Wb _ (rtyped0 vs k Lv)).
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      * exact E0.
      * eapply lt_all_mono; eauto. lia.
      * exact C0.
      * eapply lt_all_mono; [exact LCmv | lia].
      * first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
      * eapply lt_all_mono; [exact LBmv | lia].
      * exact (cboundv_nil _ _ (Forall_rev_cbound _ cvs Bpos (cfits_forall _ _ cvs Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
      * lia.
      * intros Habs; discriminate Habs.
      * first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
      * eapply rlt_all_mono; [exact LRmv | lia].
Qed.

Lemma compile_f_ok_pair : forall P cs gidf j x k m r w b bo vw,
  find P (gidf j) = Some (compile_f gidf j (mksig8 x k m r w (Some KNum) bo vw) b) ->
  wf_f (map (@projT1 _ _) cs) (mksig8 x k m r w (Some KNum) bo vw) b = true -> callees_ok P gidf cs ->
  (length cs <= j)%nat -> (Z.of_nat j < 1099511627776)%Z ->
  callee_ok P (gidf j) (match bo with Some b0 => b0 | None => cbz j end) (mksig8 x k m r w (Some KNum) bo vw) (denote_f cs (mksig8 x k m r w (Some KNum) bo vw) b).
Proof.
  intros P cs gidf j x k m r w b bo vw Hf W Hcs Hlen Hj. cbn [wf_f] in W. apply andb_true_iff in W as [Hbok W]. apply andb_true_iff in Hbok as [Hbok Hsw]. cbn [sb] in Hbok.
  cbn [wf_f sq sr sw sn sk sm] in W.
  apply andb_true_iff in W as [W Wb]. apply andb_true_iff in W as [W Wsm]. apply andb_true_iff in W as [Wr Ww].
  destruct r; cbn in Wr; [discriminate Wr|]. destruct w; cbn in Ww; [discriminate Ww|].
  unfold callee_ok. intros Hsl. cbn [sn sk sm sr sw sq].
  set (mv := pmv (mksig8 x k m false false (Some KNum) bo vw)).
  assert (Lmv : lt_all (env0 x k) mv) by apply (env0_lt (mksig8 x k m false false (Some KNum) bo vw)).
  assert (LCmv : lt_all (cenv0 x) mv) by apply (cenv0_lt (mksig8 x k m false false (Some KNum) bo vw)).
  assert (LBmv : lt_all (benv0 x k) mv) by apply (benv0_lt (mksig8 x k m false false (Some KNum) bo vw)).
  assert (LRmv : rlt_all (renv0 x k) mv) by apply (renv0_lt (mksig8 x k m false false (Some KNum) bo vw)).
  assert (Bpos : (0 < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (unfold bok in Hbok; destruct bo as [b0|]; [apply andb_true_iff in Hbok as [H1 H2]; apply Z.ltb_lt in H1; apply Z.leb_le in H2; rewrite ?KQMAuto.wB_num; lia | unfold cbz; rewrite ?KQMAuto.wB_num; lia]).
  assert (BwB : ((match bo with Some b0 => b0 | None => cbz j end) < wB)%Z) by (unfold bok in Hbok; destruct bo as [b0|]; [apply andb_true_iff in Hbok as [H1 H2]; apply Z.ltb_lt in H1; apply Z.leb_le in H2; rewrite ?KQMAuto.wB_num; lia | unfold cbz; rewrite ?KQMAuto.wB_num; lia]).
  destruct b as [e0 e1 | e | m0 m1 | e | xx | x0 x1 | r0 r1 | rb | d0 d1 | db | b0 b1 | bb]; try discriminate Wb.
  - (* recursive on the first counter *)
    destruct x as [|x']; simpl in Wb; [discriminate Wb|]. apply andb_true_iff in Wb as [Wb0 Wb1].
    assert (Mvgt : Pos.lt 1 mv).
    { unfold mv, pmv. simpl. apply Pos2Nat.inj_lt. rewrite SuccNat2Pos.id_succ. simpl. lia. }
    intros cvs vs M Lc Lv Bd. cbv beta iota. destruct cvs as [|n rest]; [simpl in Lc; discriminate|].
    simpl in Lc. injection Lc as Lc.
    revert rest vs M Lc Lv Bd. induction n as [|n' IH]; intros rest vs M Lc Lv Bd.
    + destruct (bind_params (S x') k (0 :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      assert (V : callf (mksig8 (S x') k m false false (Some KNum) bo vw) (denote_f cs (mksig8 (S x') k m false false (Some KNum) bo vw) (FRecP b0 b1)) (0 :: rest) vs M
                  = denote_pv cs dnum dmem dpair (rev rest ++ [0]) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M b0).
      { change (callf (mksig8 (S x') k m false false (Some KNum) bo vw) (denote_f cs (mksig8 (S x') k m false false (Some KNum) bo vw) (FRecP b0 b1)) (0 :: rest) vs M)
          with (appnT k m (i63 * mem) (appc x' _ (absc x' _ (fun cenv => absnT k m (i63 * mem) (fun env benv renv s =>
                  denote_pv cs dnum dmem dpair (cenv ++ [0]) benv renv env s b0))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto.
        destruct m; [reflexivity | discriminate Wsm]. }
      unfold calln, callm. cbn [sq sr]. rewrite V.
      exists (compile_f gidf j (mksig8 (S x') k m false false (Some KNum) bo vw) (FRecP b0 b1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      simpl kbody.
      pose proof (cenv0_first x' 0 rest rho0 Lc C0) as R1.
      eapply K_if; [simpl; exact R1 | reflexivity | ]. rewrite ofn_0. simpl.
      refine (ctailp_ok P _ gidf (gidf j) mv cs false false false m x' k j dnum dmem 0 false dnum bo vw (rev rest ++ [0]) _ _ (fun Hc => False_ind _ (diff_false_true Hc)) _ _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf dpair false _ _ eq_refl eq_refl Wsm b0 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] Wb0 _ (rtyped0 vs k Lv)).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- exact E0.
        -- eapply lt_all_mono; eauto. lia.
        -- exact C0.
        -- eapply lt_all_mono; [exact LCmv | lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- exact (cboundv_nil _ _ (Forall_rev_cbound _ (0 :: rest) Bpos (cfits_forall _ _ (0 :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
        -- lia.
        -- intros Habs; discriminate Habs.
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
    + destruct (bind_params (S x') k (S n' :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      set (dfn := denote_f cs (mksig8 (S x') k m false false (Some KNum) bo vw) (FRecP b0 b1)).
      assert (V : callf (mksig8 (S x') k m false false (Some KNum) bo vw) dfn (S n' :: rest) vs M
                  = denote_pv cs dnum dmem (fun cvs args s' => appnT k m (i63 * mem) (appc x' _ (dfn n') cvs) args s') (n' :: rev rest ++ [S n'])
                      (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M b1).
      { change (callf (mksig8 (S x') k m false false (Some KNum) bo vw) dfn (S n' :: rest) vs M)
          with (appnT k m (i63 * mem) (appc x' _ (absc x' _ (fun cenv => absnT k m (i63 * mem) (fun env benv renv s =>
                  denote_pv cs dnum dmem (fun cvs args s' => appnT k m (i63 * mem) (appc x' _ (dfn n') cvs) args s') (n' :: cenv ++ [S n'])
                    benv renv env s b1))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto.
        destruct m; [reflexivity | discriminate Wsm]. }
      unfold calln, callm. cbn [sq sr]. rewrite V.
      exists (compile_f gidf j (mksig8 (S x') k m false false (Some KNum) bo vw) (FRecP b0 b1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      simpl kbody.
      pose proof (cenv0_first x' (S n') rest rho0 Lc C0) as R1.
      assert (Bn : (Z.of_nat (S n') < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (pose proof (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd) as BdF'; inversion BdF'; auto).
      eapply K_if; [simpl; exact R1 | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
      eapply K_op; [simpl; exact R1 | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      refine (ctailp_ok P _ gidf (gidf j) mv cs false false true m x' k j dnum dmem n' false dnum bo vw (rev rest ++ [S n']) _ _ (fun Hc => False_ind _ (diff_false_true Hc)) _ _ Hcs Hlen Hj Hsl Hbok (hpv_rec true _ _ n' rest x' Hsw eq_refl Lc Bd) (fun _ _ => Forall_rev (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) Hf (fun cvs args s' => appnT k m (i63 * mem) (appc x' _ (dfn n') cvs) args s') true _ _ eq_refl eq_refl Wsm b1 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [(None, lshift (-1) (lunit x'))] Wb1 _ (rtyped0 vs k Lv)).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros _ cvs vs' M' Lc' Lv' Bd'. assert (Bn' : (Z.of_nat n' < (match bo with Some b0 => b0 | None => cbz j end))%Z) by lia.
        apply (IH cvs vs' M' Lc' Lv'). destruct vw as [|w0 ws0]; [constructor; [exact Bn' | exact Bd'] | exact Bd'].
      * intros _. reflexivity.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- eapply env_ok_agree; [exact E0 | exact Lmv | apply agree_set; apply Pos.le_refl].
        -- eapply lt_all_mono; eauto. lia.
        -- apply cenv_ok_cons; [eapply cenv_ok_agree; [exact C0 | exact LCmv | apply agree_set; apply Pos.le_refl] | simpl; apply PTree.gss].
        -- apply lt_all_cons; [eapply lt_all_mono; [exact LCmv | lia] | simpl; lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- apply cboundv_cons; [exact (cboundv_nil _ _ (Forall_rev_cbound _ (S n' :: rest) Bpos (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)) | cbn [fst cbv]; pose proof (cbj_le4 bo j Hbok); lia | exact (pred_lin n' rest x' Lc)].
        -- lia.
        -- intros _. split; [apply PTree.gss | lia].
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
  - (* plain *)
    intros cvs vs M Lc Lv Bd. cbv beta iota.
    destruct (bind_params x k cvs vs Lc Lv) as (rho0 & Bd0 & C0 & E0 & B0 & R0).
    assert (V : callf (mksig8 x k m false false (Some KNum) bo vw) (denote_f cs (mksig8 x k m false false (Some KNum) bo vw) (FPlainP bb)) cvs vs M
                = denote_pv cs dnum dmem dpair (rev cvs) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M bb).
    { destruct x as [|x'].
      - destruct cvs; [|discriminate].
        change (callf (mksig8 0 k m false false (Some KNum) bo vw) (denote_f cs (mksig8 0 k m false false (Some KNum) bo vw) (FPlainP bb)) [] vs M)
          with (appnT k m (i63 * mem) (absnT k m (i63 * mem) (fun env benv renv s => denote_pv cs dnum dmem dpair [] benv renv env s bb)) vs M).
        rewrite appn_absn by auto. destruct m; [reflexivity | discriminate Wsm].
      - destruct cvs as [|n rest]; [discriminate|]. simpl in Lc. injection Lc as Lc.
        change (callf (mksig8 (S x') k m false false (Some KNum) bo vw) (denote_f cs (mksig8 (S x') k m false false (Some KNum) bo vw) (FPlainP bb)) (n :: rest) vs M)
          with (appnT k m (i63 * mem) (appc x' _ (absc x' _ (fun cenv => absnT k m (i63 * mem) (fun env benv renv s =>
                  denote_pv cs dnum dmem dpair (cenv ++ [n]) benv renv env s bb))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto. destruct m; [reflexivity | discriminate Wsm]. }
    unfold calln, callm. cbn [sq sr]. rewrite V.
    exists (compile_f gidf j (mksig8 x k m false false (Some KNum) bo vw) (FPlainP bb)), rho0. split; [exact Hf|]. split; [exact Bd0|].
    simpl kbody.
    refine (ctailp_ok P _ gidf (gidf j) mv cs false false false m 0 k j dnum dmem 0 false dnum bo vw (rev cvs) _ _ (fun Hc => False_ind _ (diff_false_true Hc)) _ _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf dpair false _ _ eq_refl eq_refl Wsm bb _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] Wb _ (rtyped0 vs k Lv)).
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      * exact E0.
      * eapply lt_all_mono; eauto. lia.
      * exact C0.
      * eapply lt_all_mono; [exact LCmv | lia].
      * first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
      * eapply lt_all_mono; [exact LBmv | lia].
      * exact (cboundv_nil _ _ (Forall_rev_cbound _ cvs Bpos (cfits_forall _ _ cvs Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
      * lia.
      * intros Habs; discriminate Habs.
      * first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
      * eapply rlt_all_mono; [exact LRmv | lia].
Qed.

(** a function with the pair (step 44): its theorem from the theorem of the function on the two components *)
Lemma callee_ok_unpair : forall P id B x k r w q b v (h : ftype (mksig9 x k true r w q b v true)),
  callee_ok P id B (mksig9 x k true r w q b v false) (cmapT x _ _ (unpairT k (rtq r q)) h) ->
  callee_ok P id B (mksig9 x k true r w q b v true) h.
Proof.
  intros P id B x k r w q b v h H. unfold callee_ok in *. intros Hsl cvs vs M L K C. specialize (H Hsl cvs vs M L K C).
  assert (E : forall s, callf (mksig9 x k true r w q b v true) h cvs vs s
               = callf (mksig9 x k true r w q b v false) (cmapT x _ _ (unpairT k (rtq r q)) h) cvs vs s).
  { intros s. cbn [callf]. rewrite appc_cmapT. apply appnTP_unpair. }
  unfold calln, callm in *. cbn [sw sr sq sn sk] in *. rewrite !E. exact H.
Qed.
Theorem compile_f_ok : forall P cs gidf j gs b,
  find P (gidf j) = Some (compile_f gidf j gs b) -> wf_f (map (@projT1 _ _) cs) gs b = true -> callees_ok P gidf cs ->
  Nat.leb (length cs) j = true -> (Z.of_nat j <? 1099511627776)%Z = true ->
  callee_ok P (gidf j) (fbound gs j) gs (denote_f cs gs b).
Proof.
  intros P cs gidf j [x k m r w q bo vw sp0] b Hf W Hcs Hlen Hj. apply Nat.leb_le in Hlen. apply Z.ltb_lt in Hj.
  destruct sp0; [exfalso; revert W; unfold wf_f, swok; cbn [sp negb]; rewrite !andb_false_r; cbn; discriminate |].
  destruct q as [[| |ri]|]; [exact (compile_f_ok_pair P cs gidf j x k m r w b bo vw Hf W Hcs Hlen Hj) | exact (compile_f_ok_bool P cs gidf j x k m r w b bo vw Hf W Hcs Hlen Hj) |
    exact (compile_f_ok_rec P cs gidf j x k m r w ri b bo vw Hf W Hcs Hlen Hj)|]. cbn [wf_f sq] in W.
  apply andb_true_iff in W as [Hbok W]. apply andb_true_iff in Hbok as [Hbok Hsw]. cbn [sb] in Hbok.
  unfold callee_ok. intros Hsl. simpl sn. simpl sk. simpl sm. simpl sr. simpl sw. simpl sq.
  set (mv := pmv (mksig8 x k m r w None bo vw)).
  assert (Lmv : lt_all (env0 x k) mv) by apply (env0_lt (mksig8 x k m r w None bo vw)).
  assert (LCmv : lt_all (cenv0 x) mv) by apply (cenv0_lt (mksig8 x k m r w None bo vw)).
  assert (LBmv : lt_all (benv0 x k) mv) by apply (benv0_lt (mksig8 x k m r w None bo vw)).
  assert (LRmv : rlt_all (renv0 x k) mv) by apply (renv0_lt (mksig8 x k m r w None bo vw)).
  assert (Bpos : (0 < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (unfold bok in Hbok; destruct bo as [b0|]; [apply andb_true_iff in Hbok as [H1 H2]; apply Z.ltb_lt in H1; apply Z.leb_le in H2; rewrite ?KQMAuto.wB_num; lia | unfold cbz; rewrite ?KQMAuto.wB_num; lia]).
  assert (BwB : ((match bo with Some b0 => b0 | None => cbz j end) < wB)%Z) by (unfold bok in Hbok; destruct bo as [b0|]; [apply andb_true_iff in Hbok as [H1 H2]; apply Z.ltb_lt in H1; apply Z.leb_le in H2; rewrite ?KQMAuto.wB_num; lia | unfold cbz; rewrite ?KQMAuto.wB_num; lia]).
  destruct b as [e0 e1 | e | m0 m1 | e | xx | x0 x1 | b0 b1 | bb | c0 c1 | cb | d0 d1 | db]; simpl in W; try discriminate W.
  - (* a number, recursive on the first counter *)
    destruct x as [|x']; simpl in W; [discriminate|]. destruct r; simpl in W; [discriminate|].
    destruct w; simpl in W; [discriminate|].
    apply andb_true_iff in W as [W0 W1]. cbv beta iota.
    assert (Mvgt : Pos.lt 1 mv).
    { unfold mv, pmv. simpl. apply Pos2Nat.inj_lt. rewrite SuccNat2Pos.id_succ. simpl. lia. }
    intros cvs vs M Lc Lv Bd. destruct cvs as [|n rest]; [simpl in Lc; discriminate|].
    simpl in Lc. injection Lc as Lc.
    revert rest vs M Lc Lv Bd. induction n as [|n' IH]; intros rest vs M Lc Lv Bd.
    + destruct (bind_params (S x') k (0 :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      exists (compile_f gidf j (mksig8 (S x') k m false false None bo vw) (FRec e0 e1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      change (calln (mksig8 (S x') k m false false None bo vw) (denote_f cs (mksig8 (S x') k m false false None bo vw) (FRec e0 e1)) (0 :: rest) vs M)
        with (appn k m false (appc x' _ (absc x' _ (fun cenv => absn k m false (fun env benv renv s =>
                denote_e cs dnum (cenv ++ [0]) benv renv env s e0))) rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto. simpl kbody.
      pose proof (cenv0_first x' 0 rest rho0 Lc C0) as R1.
      eapply K_if; [simpl; exact R1 | reflexivity | ]. rewrite ofn_0. simpl.
      assert (EQ : denote_e cs dnum (rev rest ++ [0]) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) (if m then M else dummy_mem) e0
                   = denote_e cs dnum (rev rest ++ [0]) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M e0).
      { destruct m; [reflexivity|]. eapply (proj1 denote_nomem); [intros; reflexivity | eauto]. }
      rewrite EQ.
      refine (ctail_ok P _ gidf (gidf j) mv cs false false false m x' k j dnum dmem 0 false dnum bo vw (rev rest ++ [0]) _ (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf e0 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] W0 _ (rtyped0 vs k Lv)).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- exact E0.
        -- eapply lt_all_mono; eauto. lia.
        -- exact C0.
        -- eapply lt_all_mono; [exact LCmv | lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- exact (cboundv_nil _ _ (Forall_rev_cbound _ (0 :: rest) Bpos (cfits_forall _ _ (0 :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
        -- lia.
        -- intros Habs; discriminate Habs.
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
    + destruct (bind_params (S x') k (S n' :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      exists (compile_f gidf j (mksig8 (S x') k m false false None bo vw) (FRec e0 e1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      set (dfn := denote_f cs (mksig8 (S x') k m false false None bo vw) (FRec e0 e1)).
      change (calln (mksig8 (S x') k m false false None bo vw) dfn (S n' :: rest) vs M)
        with (appn k m false (appc x' _ (absc x' _ (fun cenv => absn k m false (fun env benv renv s =>
                denote_e cs (fun cvs args s' => appn k m false (appc x' _ (dfn n') cvs) args s') (n' :: cenv ++ [S n']) benv renv env s e1)))
              rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto. simpl kbody.
      pose proof (cenv0_first x' (S n') rest rho0 Lc C0) as R1.
      assert (Bn : (Z.of_nat (S n') < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (pose proof (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd) as BdF'; inversion BdF'; auto).
      eapply K_if; [simpl; exact R1 | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
      eapply K_op; [simpl; exact R1 | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      assert (EQ : denote_e cs (fun cvs args s' => appn k m false (appc x' _ (dfn n') cvs) args s') (n' :: rev rest ++ [S n'])
                     (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) (if m then M else dummy_mem) e1
                   = denote_e cs (fun cvs args s' => appn k m false (appc x' _ (dfn n') cvs) args s') (n' :: rev rest ++ [S n'])
                     (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M e1).
      { destruct m; [reflexivity|]. eapply (proj1 denote_nomem); [ | eauto].
        intros cvs l. exact (appn_false k false (appc x' _ (dfn n') cvs) l _ _). }
      rewrite EQ.
      refine (ctail_ok P _ gidf (gidf j) mv cs true false true m x' k j (fun cvs args s' => appn k m false (appc x' _ (dfn n') cvs) args s') dmem n' false dnum bo vw (rev rest ++ [S n']) _ (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) _ Hcs Hlen Hj Hsl Hbok (hpv_rec true _ _ n' rest x' Hsw eq_refl Lc Bd) (fun _ _ => Forall_rev (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) Hf e1 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [(None, lshift (-1) (lunit x'))] W1 _ (rtyped0 vs k Lv)).
      * intros _ cvs vs' M' Lc' Lv' Bd'. assert (Bn' : (Z.of_nat n' < (match bo with Some b0 => b0 | None => cbz j end))%Z) by lia.
        apply (IH cvs vs' M' Lc' Lv'). destruct vw as [|w0 ws0]; [constructor; [exact Bn' | exact Bd'] | exact Bd'].
      * intros _. reflexivity.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- eapply env_ok_agree; [exact E0 | exact Lmv | apply agree_set; apply Pos.le_refl].
        -- eapply lt_all_mono; eauto. lia.
        -- apply cenv_ok_cons; [eapply cenv_ok_agree; [exact C0 | exact LCmv | apply agree_set; apply Pos.le_refl] | simpl; apply PTree.gss].
        -- apply lt_all_cons; [eapply lt_all_mono; [exact LCmv | lia] | simpl; lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- apply cboundv_cons; [exact (cboundv_nil _ _ (Forall_rev_cbound _ (S n' :: rest) Bpos (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)) | cbn [fst cbv]; pose proof (cbj_le4 bo j Hbok); lia | exact (pred_lin n' rest x' Lc)].
        -- lia.
        -- intros _. split; [apply PTree.gss | lia].
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
  - (* a number, plain *)
    destruct r; simpl in W; [discriminate|]. destruct w; simpl in W; [discriminate|]. cbv beta iota.
    intros cvs vs M Lc Lv Bd.
    destruct (bind_params x k cvs vs Lc Lv) as (rho0 & Bd0 & C0 & E0 & B0 & R0).
    exists (compile_f gidf j (mksig8 x k m false false None bo vw) (FPlain e)), rho0. split; [exact Hf|]. split; [exact Bd0|].
    assert (V : calln (mksig8 x k m false false None bo vw) (denote_f cs (mksig8 x k m false false None bo vw) (FPlain e)) cvs vs M
                = denote_e cs dnum (rev cvs) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M e).
    { destruct x as [|x'].
      - destruct cvs; [|discriminate].
        change (calln (mksig8 0 k m false false None bo vw) (denote_f cs (mksig8 0 k m false false None bo vw) (FPlain e)) [] vs M)
          with (appn k m false (absn k m false (fun env benv renv s => denote_e cs dnum [] benv renv env s e)) vs M).
        rewrite appn_absn by auto. destruct m; [reflexivity|]. eapply (proj1 denote_nomem); [intros; reflexivity | eauto].
      - destruct cvs as [|n rest]; [discriminate|]. simpl in Lc. injection Lc as Lc.
        change (calln (mksig8 (S x') k m false false None bo vw) (denote_f cs (mksig8 (S x') k m false false None bo vw) (FPlain e)) (n :: rest) vs M)
          with (appn k m false (appc x' _ (absc x' _ (fun cenv => absn k m false (fun env benv renv s =>
                  denote_e cs dnum (cenv ++ [n]) benv renv env s e))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto. destruct m; [reflexivity|].
        eapply (proj1 denote_nomem); [intros; reflexivity | eauto]. }
    rewrite V. simpl kbody.
    refine (ctail_ok P _ gidf (gidf j) mv cs false false false m 0 k j dnum dmem 0 false dnum bo vw (rev cvs) _ (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf e _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] W _ (rtyped0 vs k Lv)).
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      * exact E0.
      * eapply lt_all_mono; eauto. lia.
      * exact C0.
      * eapply lt_all_mono; [exact LCmv | lia].
      * first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
      * eapply lt_all_mono; [exact LBmv | lia].
      * exact (cboundv_nil _ _ (Forall_rev_cbound _ cvs Bpos (cfits_forall _ _ cvs Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
      * lia.
      * intros Habs; discriminate Habs.
      * first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
      * eapply rlt_all_mono; [exact LRmv | lia].
  - (* a memory, recursive on the first counter *)
    destruct x as [|x']; simpl in W; [discriminate|]. destruct r; simpl in W; [|discriminate].
    destruct w; simpl in W; [discriminate|].
    destruct m; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W0 W1]. cbv beta iota.
    assert (Mvgt : Pos.lt 1 mv).
    { unfold mv, pmv. simpl. apply Pos2Nat.inj_lt. rewrite SuccNat2Pos.id_succ. simpl. lia. }
    intros cvs vs M Lc Lv Bd. destruct cvs as [|n rest]; [simpl in Lc; discriminate|].
    simpl in Lc. injection Lc as Lc.
    revert rest vs M Lc Lv Bd. induction n as [|n' IH]; intros rest vs M Lc Lv Bd.
    + destruct (bind_params (S x') k (0 :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      exists (compile_f gidf j (mksig8 (S x') k true true false None bo vw) (FRecM m0 m1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      change (calln (mksig8 (S x') k true true false None bo vw) (denote_f cs (mksig8 (S x') k true true false None bo vw) (FRecM m0 m1)) (0 :: rest) vs M)
        with 0%uint63.
      change (callm (mksig8 (S x') k true true false None bo vw) (denote_f cs (mksig8 (S x') k true true false None bo vw) (FRecM m0 m1)) (0 :: rest) vs M)
        with (appn k true true (appc x' _ (absc x' _ (fun cenv => absn k true true (fun env benv renv s =>
                denote_m cs dnum dmem (cenv ++ [0]) benv renv env s m0))) rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto. simpl kbody.
      pose proof (cenv0_first x' 0 rest rho0 Lc C0) as R1.
      eapply K_if; [simpl; exact R1 | reflexivity | ]. rewrite ofn_0. simpl.
      refine (ctailm_ok P _ gidf (gidf j) mv cs false false false true x' k j dnum dmem 0 false dnum bo vw (rev rest ++ [0]) _ _ (fun Hc => False_ind _ (diff_false_true Hc)) _ _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf m0 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] W0 _ (rtyped0 vs k Lv)).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- exact E0.
        -- eapply lt_all_mono; eauto. lia.
        -- exact C0.
        -- eapply lt_all_mono; [exact LCmv | lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- exact (cboundv_nil _ _ (Forall_rev_cbound _ (0 :: rest) Bpos (cfits_forall _ _ (0 :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
        -- lia.
        -- intros Habs; discriminate Habs.
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
    + destruct (bind_params (S x') k (S n' :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      exists (compile_f gidf j (mksig8 (S x') k true true false None bo vw) (FRecM m0 m1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      set (dfn := denote_f cs (mksig8 (S x') k true true false None bo vw) (FRecM m0 m1)).
      change (calln (mksig8 (S x') k true true false None bo vw) dfn (S n' :: rest) vs M) with 0%uint63.
      change (callm (mksig8 (S x') k true true false None bo vw) dfn (S n' :: rest) vs M)
        with (appn k true true (appc x' _ (absc x' _ (fun cenv => absn k true true (fun env benv renv s =>
                denote_m cs dnum (fun cvs args s' => appn k true true (appc x' _ (dfn n') cvs) args s')
                         (n' :: cenv ++ [S n']) benv renv env s m1))) rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto. simpl kbody.
      pose proof (cenv0_first x' (S n') rest rho0 Lc C0) as R1.
      assert (Bn : (Z.of_nat (S n') < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (pose proof (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd) as BdF'; inversion BdF'; auto).
      eapply K_if; [simpl; exact R1 | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
      eapply K_op; [simpl; exact R1 | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia. cbv beta iota.
      refine (ctailm_ok P _ gidf (gidf j) mv cs false true true true x' k j dnum (fun cvs args s' => appn k true true (appc x' _ (dfn n') cvs) args s') n' false dnum bo vw (rev rest ++ [S n']) _ _ (fun Hc => False_ind _ (diff_false_true Hc)) _ _ Hcs Hlen Hj Hsl Hbok (hpv_rec true _ _ n' rest x' Hsw eq_refl Lc Bd) (fun _ _ => Forall_rev (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) Hf m1 _ _ _ _ _ _ _ _ _ _ M (rk0 k) [(None, lshift (-1) (lunit x'))] W1 _ (rtyped0 vs k Lv)).
      * intros Habs; discriminate Habs.
      * intros _ cvs vs' M' Lc' Lv' Bd'. assert (Bn' : (Z.of_nat n' < (match bo with Some b0 => b0 | None => cbz j end))%Z) by lia.
        apply (IH cvs vs' M' Lc' Lv'). destruct vw as [|w0 ws0]; [constructor; [exact Bn' | exact Bd'] | exact Bd'].
      * intros Habs; discriminate Habs.
      * intros _. reflexivity.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
        -- eapply env_ok_agree; [exact E0 | exact Lmv | apply agree_set; apply Pos.le_refl].
        -- eapply lt_all_mono; eauto. lia.
        -- apply cenv_ok_cons; [eapply cenv_ok_agree; [exact C0 | exact LCmv | apply agree_set; apply Pos.le_refl] | simpl; apply PTree.gss].
        -- apply lt_all_cons; [eapply lt_all_mono; [exact LCmv | lia] | simpl; lia].
        -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
        -- eapply lt_all_mono; [exact LBmv | lia].
        -- apply cboundv_cons; [exact (cboundv_nil _ _ (Forall_rev_cbound _ (S n' :: rest) Bpos (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)) | cbn [fst cbv]; pose proof (cbj_le4 bo j Hbok); lia | exact (pred_lin n' rest x' Lc)].
        -- lia.
        -- intros _. split; [apply PTree.gss | lia].
        -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
        -- eapply rlt_all_mono; [exact LRmv | lia].
  - (* a memory, plain *)
    destruct r; simpl in W; [|discriminate]. destruct w; simpl in W; [discriminate|]. destruct m; simpl in W; [|discriminate].
    cbv beta iota.
    intros cvs vs M Lc Lv Bd.
    destruct (bind_params x k cvs vs Lc Lv) as (rho0 & Bd0 & C0 & E0 & B0 & R0).
    exists (compile_f gidf j (mksig8 x k true true false None bo vw) (FPlainM e)), rho0. split; [exact Hf|]. split; [exact Bd0|].
    change (calln (mksig8 x k true true false None bo vw) (denote_f cs (mksig8 x k true true false None bo vw) (FPlainM e)) cvs vs M) with 0%uint63.
    assert (V : callm (mksig8 x k true true false None bo vw) (denote_f cs (mksig8 x k true true false None bo vw) (FPlainM e)) cvs vs M
                = denote_m cs dnum dmem (rev cvs) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M e).
    { destruct x as [|x'].
      - destruct cvs; [|discriminate].
        change (callm (mksig8 0 k true true false None bo vw) (denote_f cs (mksig8 0 k true true false None bo vw) (FPlainM e)) [] vs M)
          with (appn k true true (absn k true true (fun env benv renv s => denote_m cs dnum dmem [] benv renv env s e)) vs M).
        rewrite appn_absn by auto. reflexivity.
      - destruct cvs as [|n rest]; [discriminate|]. simpl in Lc. injection Lc as Lc.
        change (callm (mksig8 (S x') k true true false None bo vw) (denote_f cs (mksig8 (S x') k true true false None bo vw) (FPlainM e)) (n :: rest) vs M)
          with (appn k true true (appc x' _ (absc x' _ (fun cenv => absn k true true (fun env benv renv s =>
                  denote_m cs dnum dmem (cenv ++ [n]) benv renv env s e))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto. reflexivity. }
    rewrite V. simpl kbody.
    refine (ctailm_ok P _ gidf (gidf j) mv cs false false false true 0 k j dnum dmem 0 false dnum bo vw (rev cvs) _ _ (fun Hc => False_ind _ (diff_false_true Hc)) _ _ Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf e _ _ _ _ _ _ _ _ _ _ M (rk0 k) [] W _ (rtyped0 vs k Lv)).
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      * exact E0.
      * eapply lt_all_mono; eauto. lia.
      * exact C0.
      * eapply lt_all_mono; [exact LCmv | lia].
      * first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
      * eapply lt_all_mono; [exact LBmv | lia].
      * exact (cboundv_nil _ _ (Forall_rev_cbound _ cvs Bpos (cfits_forall _ _ cvs Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
      * lia.
      * intros Habs; discriminate Habs.
      * first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
      * eapply rlt_all_mono; [exact LRmv | lia].
  - (* a number made after memories *)
    destruct r; simpl in W; [discriminate|]. destruct w; simpl in W; [|discriminate]. destruct m; simpl in W; [|discriminate].
    cbv beta iota.
    intros cvs vs M Lc Lv Bd.
    destruct (bind_params x k cvs vs Lc Lv) as (rho0 & Bd0 & C0 & E0 & B0 & R0).
    assert (V : calln (mksig8 x k true false true None bo vw) (denote_f cs (mksig8 x k true false true None bo vw) (FPlainX xx)) cvs vs M
                = denote_x cs dnum dmem dnum (rev cvs) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M xx).
    { destruct x as [|x'].
      - destruct cvs; [|discriminate].
        change (calln (mksig8 0 k true false true None bo vw) (denote_f cs (mksig8 0 k true false true None bo vw) (FPlainX xx)) [] vs M)
          with (appn k true false (absn k true false (fun env benv renv s => denote_x cs dnum dmem dnum [] benv renv env s xx)) vs M).
        rewrite appn_absn by auto. reflexivity.
      - destruct cvs as [|n rest]; [discriminate|]. simpl in Lc. injection Lc as Lc.
        change (calln (mksig8 (S x') k true false true None bo vw) (denote_f cs (mksig8 (S x') k true false true None bo vw) (FPlainX xx)) (n :: rest) vs M)
          with (appn k true false (appc x' _ (absc x' _ (fun cenv => absn k true false (fun env benv renv s =>
                  denote_x cs dnum dmem dnum (cenv ++ [n]) benv renv env s xx))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto. reflexivity. }
    rewrite V.
    destruct (ctailx_ok P _ gidf (gidf j) mv cs false false false true 0 k j dnum dmem 0 false dnum bo vw (rev cvs) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf xx (rev cvs) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M (rk0 k) [] eq_refl eq_refl eq_refl W (rtyped0 vs k Lv) (cboundv_nil _ _ (Forall_rev_cbound _ cvs Bpos (cfits_forall _ _ cvs Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok))) as [Me HMe].
    exists Me, (compile_f gidf j (mksig8 x k true false true None bo vw) (FPlainX xx)), rho0. split; [exact Hf|]. split; [exact Bd0|].
    simpl kbody. apply HMe.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      * exact E0.
      * eapply lt_all_mono; eauto. lia.
      * exact C0.
      * eapply lt_all_mono; [exact LCmv | lia].
      * first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
      * eapply lt_all_mono; [exact LBmv | lia].
      * exact (cboundv_nil _ _ (Forall_rev_cbound _ cvs Bpos (cfits_forall _ _ cvs Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
      * lia.
      * intros Habs; discriminate Habs.
      * first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
      * eapply rlt_all_mono; [exact LRmv | lia].
  - (* a number made after memories, recursive on the first counter *)
    destruct x as [|x']; simpl in W; [discriminate|]. destruct r; simpl in W; [discriminate|].
    destruct w; simpl in W; [|discriminate]. destruct m; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W0 W1]. cbv beta iota.
    assert (Mvgt : Pos.lt 1 mv).
    { unfold mv, pmv. simpl. apply Pos2Nat.inj_lt. rewrite SuccNat2Pos.id_succ. simpl. lia. }
    intros cvs vs M Lc Lv Bd. destruct cvs as [|n rest]; [simpl in Lc; discriminate|].
    simpl in Lc. injection Lc as Lc.
    revert rest vs M Lc Lv Bd. induction n as [|n' IH]; intros rest vs M Lc Lv Bd.
    + destruct (bind_params (S x') k (0 :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      change (calln (mksig8 (S x') k true false true None bo vw) (denote_f cs (mksig8 (S x') k true false true None bo vw) (FRecX x0 x1)) (0 :: rest) vs M)
        with (appn k true false (appc x' _ (absc x' _ (fun cenv => absn k true false (fun env benv renv s =>
                denote_x cs dnum dmem dnum (cenv ++ [0]) benv renv env s x0))) rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto.
      destruct (ctailx_ok P _ gidf (gidf j) mv cs false false false true x' k j dnum dmem 0 false dnum bo vw (rev rest ++ [0]) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) Hcs Hlen Hj Hsl Hbok (fun Hc => False_ind _ (diff_false_true Hc)) (fun Hc => False_ind _ (diff_false_true Hc)) Hf x0 (rev rest ++ [0]) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M (rk0 k) [] eq_refl eq_refl eq_refl W0 (rtyped0 vs k Lv) (cboundv_nil _ _ (Forall_rev_cbound _ (0 :: rest) Bpos (cfits_forall _ _ (0 :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok))) as [Me HMe].
      exists Me, (compile_f gidf j (mksig8 (S x') k true false true None bo vw) (FRecX x0 x1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      simpl kbody.
      pose proof (cenv0_first x' 0 rest rho0 Lc C0) as R1.
      eapply K_if; [simpl; exact R1 | reflexivity | ]. rewrite ofn_0. simpl.
      apply HMe.
      split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      -- exact E0.
      -- eapply lt_all_mono; eauto. lia.
      -- exact C0.
      -- eapply lt_all_mono; [exact LCmv | lia].
      -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
      -- eapply lt_all_mono; [exact LBmv | lia].
      -- exact (cboundv_nil _ _ (Forall_rev_cbound _ (0 :: rest) Bpos (cfits_forall _ _ (0 :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)).
      -- lia.
      -- intros Habs; discriminate Habs.
      -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
      -- eapply rlt_all_mono; [exact LRmv | lia].
    + destruct (bind_params (S x') k (S n' :: rest) vs) as (rho0 & Bd0 & C0 & E0 & B0 & R0); [simpl; lia | auto |].
      set (dfn := denote_f cs (mksig8 (S x') k true false true None bo vw) (FRecX x0 x1)).
      change (calln (mksig8 (S x') k true false true None bo vw) dfn (S n' :: rest) vs M)
        with (appn k true false (appc x' _ (absc x' _ (fun cenv => absn k true false (fun env benv renv s =>
                denote_x cs dnum dmem (fun cvs args s' => appn k true false (appc x' _ (dfn n') cvs) args s') (n' :: cenv ++ [S n'])
                  benv renv env s x1))) rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto.
      assert (Bn : (Z.of_nat (S n') < (match bo with Some b0 => b0 | None => cbz j end))%Z) by (pose proof (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd) as BdF'; inversion BdF'; auto).
      assert (HR : true = true -> forall cvs vs' M', length cvs = x' -> map kind_of vs' = k ->
                     match vw with [] => Forall (fun c => (Z.of_nat c < (match bo with Some b0 => b0 | None => cbz j end))%Z) cvs
                     | vs0 => Forall (fun P => (pevalz P (map Z.of_nat (n' :: cvs)) < (match bo with Some b0 => b0 | None => cbz j end))%Z) vs0 end ->
                     exists M2, runk P (gidf j) (ofn n' :: map ofn cvs ++ flat_map vflat vs') M'
                                     ((fun cvs args s' => appn k true false (appc x' _ (dfn n') cvs) args s') cvs vs' M') M2).
      { intros _ cvs vs' M' Lc' Lv' Bd'. assert (Bn' : (Z.of_nat n' < (match bo with Some b0 => b0 | None => cbz j end))%Z) by lia.
        apply (IH cvs vs' M' Lc' Lv'). destruct vw as [|w0 ws0]; [constructor; [exact Bn' | exact Bd'] | exact Bd']. }
      destruct (ctailx_ok P _ gidf (gidf j) mv cs false false true true x' k j dnum dmem n' true (fun cvs args s' => appn k true false (appc x' _ (dfn n') cvs) args s') bo vw (rev rest ++ [S n']) (fun Habs => ltac:(discriminate Habs)) (fun Habs => ltac:(discriminate Habs)) HR (fun Habs => ltac:(discriminate Habs)) (fun _ => eq_refl) (fun Habs => ltac:(discriminate Habs)) Hcs Hlen Hj Hsl Hbok (hpv_rec true _ _ n' rest x' Hsw eq_refl Lc Bd) (fun _ _ => Forall_rev (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) Hf x1 (n' :: rev rest ++ [S n']) (rev (vbools vs)) (rev (vrecs vs)) (rev (vnums vs)) M (rk0 k) [(None, lshift (-1) (lunit x'))] eq_refl eq_refl eq_refl W1 (rtyped0 vs k Lv) (cboundv_cons _ _ _ _ (None, lshift (-1) (lunit x')) n' (cboundv_nil _ _ (Forall_rev_cbound _ (S n' :: rest) Bpos (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)) ltac:(cbn [fst cbv]; pose proof (cbj_le4 bo j Hbok); lia) (pred_lin n' rest x' Lc))) as [Me HMe].
      exists Me, (compile_f gidf j (mksig8 (S x') k true false true None bo vw) (FRecX x0 x1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      simpl kbody.
      pose proof (cenv0_first x' (S n') rest rho0 Lc C0) as R1.
      eapply K_if; [simpl; exact R1 | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
      eapply K_op; [simpl; exact R1 | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply HMe.
      split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      -- eapply env_ok_agree; [exact E0 | exact Lmv | apply agree_set; apply Pos.le_refl].
      -- eapply lt_all_mono; eauto. lia.
      -- apply cenv_ok_cons; [eapply cenv_ok_agree; [exact C0 | exact LCmv | apply agree_set; apply Pos.le_refl] | simpl; apply PTree.gss].
      -- apply lt_all_cons; [eapply lt_all_mono; [exact LCmv | lia] | simpl; lia].
      -- first [exact B0 | eapply benv_ok_agree; [exact B0 | exact LBmv | apply agree_set; apply Pos.le_refl]].
      -- eapply lt_all_mono; [exact LBmv | lia].
      -- apply cboundv_cons; [exact (cboundv_nil _ _ (Forall_rev_cbound _ (S n' :: rest) Bpos (cfits_forall _ _ (S n' :: rest) Hsw ltac:(cbn [length sn] in *; lia) Bd)) (cbj_le4 bo j Hbok)) | cbn [fst cbv]; pose proof (cbj_le4 bo j Hbok); lia | exact (pred_lin n' rest x' Lc)].
      -- lia.
      -- intros _. split; [apply PTree.gss | lia].
      -- first [exact R0 | eapply renv_ok_agree; [exact R0 | exact LRmv | apply agree_set; apply Pos.le_refl]].
      -- eapply rlt_all_mono; [exact LRmv | lia].
Qed.

(** the callees' theorems, one after the other, as the callee assumption of the next function: [kitc.py --reflect] gives
    function [j] of a program the theorems of functions [0 .. j-1] this way *)
Fixpoint all_ok (P : prog) (gidf : nat -> ident) (cs : list callee) (k : nat) : Prop :=
  match cs with
  | [] => True
  | c :: r => (let '(existT _ gs h) := c in callee_ok P (gidf k) (fbound gs k) gs h) /\ all_ok P gidf r (S k)
  end.

(** a function given as a term -- a recursive function applied to the functions it was given (Rocq-C-solution.md §12.V, step
    10) -- is not a [fix] over the counter, so it is not convertible to the meaning of its tree; it has the statement when it
    satisfies the tree's two equations: at 0 the tree's meaning, at [S n] the tree's recursive body with [h n] as its recursive
    call.  Each equation is checked by conversion, per program *)
Theorem compile_f_okr : forall P cs gidf j x k m e0 e1 bo vw (h : nat -> ctype x (ntype k m false)),
  find P (gidf j) = Some (compile_f gidf j (mksig8 (S x) k m false false None bo vw) (FRec e0 e1)) ->
  wf_f (map (@projT1 _ _) cs) (mksig8 (S x) k m false false None bo vw) (FRec e0 e1) = true -> callees_ok P gidf cs ->
  Nat.leb (length cs) j = true -> (Z.of_nat j <? 1099511627776)%Z = true ->
  h 0 = denote_f cs (mksig8 (S x) k m false false None bo vw) (FRec e0 e1) 0 ->
  (forall n, h (S n) = absc x _ (fun cenv => absn k m false (fun env benv renv s =>
     denote_e cs (fun cvs args s' => appn k m false (appc x _ (h n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s e1))) ->
  callee_ok P (gidf j) (fbound (mksig8 (S x) k m false false None bo vw) j) (mksig8 (S x) k m false false None bo vw) h.
Proof.
  intros P cs gidf j x k m e0 e1 bo vw h Hf W Hcs Hlen Hj H0 HS.
  pose proof (compile_f_ok P cs gidf j _ _ Hf W Hcs Hlen Hj) as OK.
  set (D := denote_f cs (mksig8 (S x) k m false false None bo vw) (FRec e0 e1)) in *.
  cbn [wf_f sn sr sw sm sk] in W. apply andb_true_iff in W as [_ W]. apply andb_true_iff in W as [_ W1]. cbn [Nat.pred] in W1.
  assert (EQ : forall n rest vs M, length rest = x -> map kind_of vs = k ->
            appn k m false (appc x _ (h n) rest) vs M = appn k m false (appc x _ (D n) rest) vs M).
  { induction n as [|n IH]; intros rest vs M Lr Lv.
    - rewrite H0. reflexivity.
    - rewrite HS.
      change (D (S n)) with (absc x _ (fun cenv => absn k m false (fun env benv renv s =>
          denote_e cs (fun cvs args s' => appn k m false (appc x _ (D n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s e1))).
      rewrite !appc_absc by exact Lr. rewrite !appn_absn by exact Lv.
      eapply (proj1 denote_rec_ext); [| exact W1 | apply rtyped0; exact Lv].
      intros cvs l s' Lc Ll. apply IH; assumption. }
  unfold callee_ok in *. simpl sn in *. simpl sk in *. simpl sr in *. simpl sw in *.
  intros Hsl cvs vs M Lc Lv Bd. specialize (OK Hsl cvs vs M Lc Lv Bd).
  destruct cvs as [|n rest]; [discriminate|]. cbn [length] in Lc. injection Lc as Lc.
  replace (calln (mksig8 (S x) k m false false None bo vw) h (n :: rest) vs M) with (calln (mksig8 (S x) k m false false None bo vw) D (n :: rest) vs M);
    [exact OK|].
  unfold calln, callf. cbn [sr appc]. symmetry. apply EQ; assumption.
Qed.

Theorem compile_f_okrm : forall P cs gidf j x k m m0 m1 bo vw (h : nat -> ctype x (ntype k m true)),
  find P (gidf j) = Some (compile_f gidf j (mksig8 (S x) k m true false None bo vw) (FRecM m0 m1)) ->
  wf_f (map (@projT1 _ _) cs) (mksig8 (S x) k m true false None bo vw) (FRecM m0 m1) = true -> callees_ok P gidf cs ->
  Nat.leb (length cs) j = true -> (Z.of_nat j <? 1099511627776)%Z = true ->
  h 0 = denote_f cs (mksig8 (S x) k m true false None bo vw) (FRecM m0 m1) 0 ->
  (forall n, h (S n) = absc x _ (fun cenv => absn k m true (fun env benv renv s =>
     denote_m cs dnum (fun cvs args s' => appn k m true (appc x _ (h n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s m1))) ->
  callee_ok P (gidf j) (fbound (mksig8 (S x) k m true false None bo vw) j) (mksig8 (S x) k m true false None bo vw) h.
Proof.
  intros P cs gidf j x k m m0 m1 bo vw h Hf W Hcs Hlen Hj H0 HS.
  pose proof (compile_f_ok P cs gidf j _ _ Hf W Hcs Hlen Hj) as OK.
  set (D := denote_f cs (mksig8 (S x) k m true false None bo vw) (FRecM m0 m1)) in *.
  cbn [wf_f sn sr sw sm sk] in W. apply andb_true_iff in W as [_ W]. apply andb_true_iff in W as [_ W1]. cbn [Nat.pred] in W1.
  assert (EQ : forall n rest vs M, length rest = x -> map kind_of vs = k ->
            appn k m true (appc x _ (h n) rest) vs M = appn k m true (appc x _ (D n) rest) vs M).
  { induction n as [|n IH]; intros rest vs M Lr Lv.
    - rewrite H0. reflexivity.
    - rewrite HS.
      change (D (S n)) with (absc x _ (fun cenv => absn k m true (fun env benv renv s =>
          denote_m cs dnum (fun cvs args s' => appn k m true (appc x _ (D n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s m1))).
      rewrite !appc_absc by exact Lr. rewrite !appn_absn by exact Lv.
      eapply denote_m_recm_ext; [| exact W1 | apply rtyped0; exact Lv].
      intros cvs l s' Lc Ll. apply IH; assumption. }
  unfold callee_ok in *. simpl sn in *. simpl sk in *. simpl sr in *. simpl sw in *.
  intros Hsl cvs vs M Lc Lv Bd. specialize (OK Hsl cvs vs M Lc Lv Bd).
  destruct cvs as [|n rest]; [discriminate|]. cbn [length] in Lc. injection Lc as Lc.
  replace (callm (mksig8 (S x) k m true false None bo vw) h (n :: rest) vs M) with (callm (mksig8 (S x) k m true false None bo vw) D (n :: rest) vs M);
    [exact OK|].
  unfold callm, callf. cbn [sr appc]. symmetry. apply EQ; assumption.
Qed.

Theorem compile_f_okrx : forall P cs gidf j x k x0 x1 bo vw (h : nat -> ctype x (ntype k true false)),
  find P (gidf j) = Some (compile_f gidf j (mksig8 (S x) k true false true None bo vw) (FRecX x0 x1)) ->
  wf_f (map (@projT1 _ _) cs) (mksig8 (S x) k true false true None bo vw) (FRecX x0 x1) = true -> callees_ok P gidf cs ->
  Nat.leb (length cs) j = true -> (Z.of_nat j <? 1099511627776)%Z = true ->
  h 0 = denote_f cs (mksig8 (S x) k true false true None bo vw) (FRecX x0 x1) 0 ->
  (forall n, h (S n) = absc x _ (fun cenv => absn k true false (fun env benv renv s =>
     denote_x cs dnum dmem (fun cvs args s' => appn k true false (appc x _ (h n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s x1))) ->
  callee_ok P (gidf j) (fbound (mksig8 (S x) k true false true None bo vw) j) (mksig8 (S x) k true false true None bo vw) h.
Proof.
  intros P cs gidf j x k x0 x1 bo vw h Hf W Hcs Hlen Hj H0 HS.
  pose proof (compile_f_ok P cs gidf j _ _ Hf W Hcs Hlen Hj) as OK.
  set (D := denote_f cs (mksig8 (S x) k true false true None bo vw) (FRecX x0 x1)) in *.
  cbn [wf_f sn sr sw sm sk] in W. apply andb_true_iff in W as [_ W]. apply andb_true_iff in W as [_ W1]. cbn [Nat.pred] in W1.
  assert (EQ : forall n rest vs M, length rest = x -> map kind_of vs = k ->
            appn k true false (appc x _ (h n) rest) vs M = appn k true false (appc x _ (D n) rest) vs M).
  { induction n as [|n IH]; intros rest vs M Lr Lv.
    - rewrite H0. reflexivity.
    - rewrite HS.
      change (D (S n)) with (absc x _ (fun cenv => absn k true false (fun env benv renv s =>
          denote_x cs dnum dmem (fun cvs args s' => appn k true false (appc x _ (D n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s x1))).
      rewrite !appc_absc by exact Lr. rewrite !appn_absn by exact Lv.
      eapply denote_x_recx_ext; [| exact W1 | apply rtyped0; exact Lv].
      intros cvs l s' Lc Ll. apply IH; assumption. }
  unfold callee_ok in *. simpl sn in *. simpl sk in *. simpl sr in *. simpl sw in *.
  intros Hsl cvs vs M Lc Lv Bd. specialize (OK Hsl cvs vs M Lc Lv Bd).
  destruct cvs as [|n rest]; [discriminate|]. cbn [length] in Lc. injection Lc as Lc.
  replace (calln (mksig8 (S x) k true false true None bo vw) h (n :: rest) vs M) with (calln (mksig8 (S x) k true false true None bo vw) D (n :: rest) vs M);
    [exact OK|].
  unfold calln, callf. cbn [sr appc]. symmetry. apply EQ; assumption.
Qed.

(** the copies' theorems for a boolean, a record, a number and a memory (step 41): from the two equations by conversion *)
Theorem compile_f_okrb : forall P cs gidf j x k m b0 b1 bo vw (h : nat -> ctype x (ntypeT k m bool)),
  find P (gidf j) = Some (compile_f gidf j (mksig8 (S x) k m false false (Some KBool) bo vw) (FRecB b0 b1)) ->
  wf_f (map (@projT1 _ _) cs) (mksig8 (S x) k m false false (Some KBool) bo vw) (FRecB b0 b1) = true -> callees_ok P gidf cs ->
  Nat.leb (length cs) j = true -> (Z.of_nat j <? 1099511627776)%Z = true ->
  h 0 = denote_f cs (mksig8 (S x) k m false false (Some KBool) bo vw) (FRecB b0 b1) 0 ->
  (forall n, h (S n) = absc x _ (fun cenv => absnT k m bool (fun env benv renv s =>
     denote_bb cs dnum (fun cvs args s' => appnT k m bool (appc x _ (h n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s b1))) ->
  callee_ok P (gidf j) (fbound (mksig8 (S x) k m false false (Some KBool) bo vw) j) (mksig8 (S x) k m false false (Some KBool) bo vw) h.
Proof.
  intros P cs gidf j x k m b0 b1 bo vw h Hf W Hcs Hlen Hj H0 HS.
  pose proof (compile_f_ok P cs gidf j _ _ Hf W Hcs Hlen Hj) as OK.
  set (D := denote_f cs (mksig8 (S x) k m false false (Some KBool) bo vw) (FRecB b0 b1)) in *.
  unfold wf_f in W. cbn [sn sr sw sm sk sq] in W. eassert (W1 : wfbb _ _ _ _ _ _ _ b1 = true) by (split_all; eassumption).
  assert (EQ : forall n rest vs M, length rest = x -> map kind_of vs = k ->
            appnT k m bool (appc x _ (h n) rest) vs M = appnT k m bool (appc x _ (D n) rest) vs M).
  { induction n as [|n IH]; intros rest vs M Lr Lv.
    - rewrite H0. reflexivity.
    - rewrite HS.
      change (D (S n)) with (absc x _ (fun cenv => absnT k m bool (fun env benv renv s =>
          denote_bb cs dnum (fun cvs args s' => appnT k m bool (appc x _ (D n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s b1))).
      rewrite !appc_absc by exact Lr. rewrite !appn_absn by exact Lv.
      eapply denote_bb_recb_ext; [| exact W1 | apply rtyped0; exact Lv].
      intros cvs l s' Lc Ll. apply IH; assumption. }
  apply (callee_ok_ext _ _ _ (mksig8 (S x) k m false false (Some KBool) bo vw) h D); [|exact OK].
  intros [|n rest] vs M Lc Lv; [discriminate Lc|]. cbn [length sn sk] in Lc, Lv. injection Lc as Lc.
  cbn [callf appc rtq]. apply EQ; assumption.
Qed.
Theorem compile_f_okrr : forall P cs gidf j x k m b0 b1 bo vw ri (h : nat -> ctype x (ntypeT k m (RT ri))),
  find P (gidf j) = Some (compile_f gidf j (mksig8 (S x) k m false false (Some (KRec ri)) bo vw) (FRecR b0 b1)) ->
  wf_f (map (@projT1 _ _) cs) (mksig8 (S x) k m false false (Some (KRec ri)) bo vw) (FRecR b0 b1) = true -> callees_ok P gidf cs ->
  Nat.leb (length cs) j = true -> (Z.of_nat j <? 1099511627776)%Z = true ->
  h 0 = denote_f cs (mksig8 (S x) k m false false (Some (KRec ri)) bo vw) (FRecR b0 b1) 0 ->
  (forall n, h (S n) = absc x _ (fun cenv => absnT k m (RT ri) (fun env benv renv s =>
     denote_br cs dnum ri (fun cvs args s' => appnT k m (RT ri) (appc x _ (h n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s b1))) ->
  callee_ok P (gidf j) (fbound (mksig8 (S x) k m false false (Some (KRec ri)) bo vw) j) (mksig8 (S x) k m false false (Some (KRec ri)) bo vw) h.
Proof.
  intros P cs gidf j x k m b0 b1 bo vw ri h Hf W Hcs Hlen Hj H0 HS.
  pose proof (compile_f_ok P cs gidf j _ _ Hf W Hcs Hlen Hj) as OK.
  set (D := denote_f cs (mksig8 (S x) k m false false (Some (KRec ri)) bo vw) (FRecR b0 b1)) in *.
  unfold wf_f in W. cbn [sn sr sw sm sk sq] in W. eassert (W1 : wfbr _ _ _ _ _ _ _ _ b1 = true) by (split_all; eassumption).
  assert (EQ : forall n rest vs M, length rest = x -> map kind_of vs = k ->
            appnT k m (RT ri) (appc x _ (h n) rest) vs M = appnT k m (RT ri) (appc x _ (D n) rest) vs M).
  { induction n as [|n IH]; intros rest vs M Lr Lv.
    - rewrite H0. reflexivity.
    - rewrite HS.
      change (D (S n)) with (absc x _ (fun cenv => absnT k m (RT ri) (fun env benv renv s =>
          denote_br cs dnum ri (fun cvs args s' => appnT k m (RT ri) (appc x _ (D n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s b1))).
      rewrite !appc_absc by exact Lr. rewrite !appn_absn by exact Lv.
      eapply denote_br_recr_ext; [| exact W1 | apply rtyped0; exact Lv].
      intros cvs l s' Lc Ll. apply IH; assumption. }
  apply (callee_ok_ext _ _ _ (mksig8 (S x) k m false false (Some (KRec ri)) bo vw) h D); [|exact OK].
  intros [|n rest] vs M Lc Lv; [discriminate Lc|]. cbn [length sn sk] in Lc, Lv. injection Lc as Lc.
  cbn [callf appc rtq]. apply EQ; assumption.
Qed.
Theorem compile_f_okrp : forall P cs gidf j x k m b0 b1 bo vw (h : nat -> ctype x (ntypeT k m (i63 * mem))),
  find P (gidf j) = Some (compile_f gidf j (mksig8 (S x) k m false false (Some KNum) bo vw) (FRecP b0 b1)) ->
  wf_f (map (@projT1 _ _) cs) (mksig8 (S x) k m false false (Some KNum) bo vw) (FRecP b0 b1) = true -> callees_ok P gidf cs ->
  Nat.leb (length cs) j = true -> (Z.of_nat j <? 1099511627776)%Z = true ->
  h 0 = denote_f cs (mksig8 (S x) k m false false (Some KNum) bo vw) (FRecP b0 b1) 0 ->
  (forall n, h (S n) = absc x _ (fun cenv => absnT k m (i63 * mem) (fun env benv renv s =>
     denote_pv cs dnum dmem (fun cvs args s' => appnT k m (i63 * mem) (appc x _ (h n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s b1))) ->
  callee_ok P (gidf j) (fbound (mksig8 (S x) k m false false (Some KNum) bo vw) j) (mksig8 (S x) k m false false (Some KNum) bo vw) h.
Proof.
  intros P cs gidf j x k m b0 b1 bo vw h Hf W Hcs Hlen Hj H0 HS.
  pose proof (compile_f_ok P cs gidf j _ _ Hf W Hcs Hlen Hj) as OK.
  set (D := denote_f cs (mksig8 (S x) k m false false (Some KNum) bo vw) (FRecP b0 b1)) in *.
  unfold wf_f in W. cbn [sn sr sw sm sk sq] in W. eassert (W1 : wfpv _ _ _ _ _ _ _ _ b1 = true) by (split_all; eassumption).
  assert (EQ : forall n rest vs M, length rest = x -> map kind_of vs = k ->
            appnT k m (i63 * mem) (appc x _ (h n) rest) vs M = appnT k m (i63 * mem) (appc x _ (D n) rest) vs M).
  { induction n as [|n IH]; intros rest vs M Lr Lv.
    - rewrite H0. reflexivity.
    - rewrite HS.
      change (D (S n)) with (absc x _ (fun cenv => absnT k m (i63 * mem) (fun env benv renv s =>
          denote_pv cs dnum dmem (fun cvs args s' => appnT k m (i63 * mem) (appc x _ (D n) cvs) args s') (n :: cenv ++ [S n]) benv renv env s b1))).
      rewrite !appc_absc by exact Lr. rewrite !appn_absn by exact Lv.
      eapply denote_pv_recp_ext; [| exact W1 | apply rtyped0; exact Lv].
      intros cvs l s' Lc Ll. apply IH; assumption. }
  apply (callee_ok_ext _ _ _ (mksig8 (S x) k m false false (Some KNum) bo vw) h D); [|exact OK].
  intros [|n rest] vs M Lc Lv; [discriminate Lc|]. cbn [length sn sk] in Lc, Lv. injection Lc as Lc.
  cbn [callf appc rtq]. apply EQ; assumption.
Qed.


Lemma all_ok_nth : forall P gidf cs k, all_ok P gidf cs k ->
  forall f, match nth_error cs f with Some (existT _ gs h) => callee_ok P (gidf (k + f)%nat) (fbound gs (k + f)) gs h | None => True end.
Proof.
  intros P gidf cs. unfold callee in *. induction cs as [|[gs h] r IH]; intros k H f; simpl in *.
  - destruct f; exact Logic.I.
  - destruct H as [H0 H1]. destruct f as [|f]; simpl.
    + rewrite Nat.add_0_r. exact H0.
    + rewrite <- Nat.add_succ_comm. exact (IH (S k) H1 f).
Qed.

Lemma all_ok_callees : forall P gidf cs, all_ok P gidf cs 0 -> callees_ok P gidf cs.
Proof. intros P gidf cs H f. exact (all_ok_nth P gidf cs 0 H f). Qed.

End Recs.
Notation mksig8 x k m r w q b v := (mksig9 x k m r w q b v false).

(** a program with no record types *)
#[global] Instance no_recs : RecTypes | 100 :=
  mkrecs (fun _ => unit) (fun _ => mkrops 0 None (fun _ => tt) (fun P _ k => k [])) (fun _ => tt).
#[global] Instance no_recs_laws : @RecLaws no_recs.
Proof. apply laws_of; [intros i x P k; destruct x; reflexivity | intros i x; destruct x; reflexivity | intros i l E L; destruct l; [reflexivity | discriminate] | intros i ws c rest E; discriminate E]. Qed.

(** the second law for a data type, per program (step 28), after the type is chosen ([destruct i]) and its widths named
    ([injection E]): the tag's cases one by one, the fields their exact number, the written zeros put in, then by computation *)
Ltac kq_zeros := repeat match goal with
  | H : andb (PrimInt63.eqb ?x 0%uint63) _ = true |- _ =>
      let H1 := fresh in let H2 := fresh in apply andb_true_iff in H as [H1 H2]; apply eqb_correct in H1; subst x
  end.
Ltac kq_tag_case :=
  match goal with Lc : (?c < _)%nat, Lr : length ?rest = _, Hz : zeros_from _ ?rest = true |- _ =>
    cbn in Lc, Lr; repeat (destruct rest as [|? rest]; try discriminate Lr);
    repeat (destruct c as [|c]; [ cbn in Hz; kq_zeros; reflexivity | cbn in Lc ]); lia
  end.
(** a program's one-level constructor (step 43): records of the types its record fields ask, as many numbers as its number
    fields; each record taken apart, its numbers are the fields' *)
Ltac kq_rs_list :=
  repeat match goal with
  | H : map (@projT1 _ _) ?rs = [] |- _ => destruct rs; [clear H | discriminate H]
  | H : map (@projT1 _ _) ?rs = _ :: _ |- _ =>
      let r := fresh "r" in let rs' := fresh "rs" in let j := fresh "j" in let x := fresh "x" in let E := fresh "E" in
      destruct rs as [|r rs']; [discriminate H|]; destruct r as [j x]; cbn [map projT1] in H; injection H as E H; subst j
  end.
Ltac kq_rb_case :=
  match goal with Hl : (length ?l + _)%nat = _ |- _ =>
    kq_rs_list; cbn in Hl; rewrite Nat.add_comm in Hl; cbn in Hl; repeat (destruct l as [|? l]; try discriminate Hl);
    cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity
  end.
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
Definition sum_g := mksig 1 (nk 2) true false false None.
Definition sum_s0 := SVar 0.
Definition sum_s1 := SRec CNil (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SOp Badd (SVar 0) (SRd (SInt 0) (SVar 1))) SNil)).
Definition sum_b := FRec sum_s0 sum_s1.

(* the per-program check: the kernel compares the user's function with the meaning of its syntax *)
Time Lemma sum_is : sum = denote_f [] sum_g sum_b.
Proof. Time exact_no_check (eq_refl sum). Time Qed.

(* end to end: the KQL function is [compile_f] of the syntax; its statement is [compile_f_ok] and the kernel's computation *)
Definition sum_P := mkprog [(gid1 0, compile_f gid1 0 sum_g sum_b)] [].
Time Lemma sum_ok : callee_ok sum_P (gid1 0) (cbz 0) sum_g sum.
Proof. Time exact_no_check (compile_f_ok sum_P [] gid1 0 sum_g sum_b eq_refl eq_refl (no_callees sum_P gid1) eq_refl eq_refl). Time Qed.

(* a wrong syntax (1 replaced by 2) is refused *)
Time Fail Definition sum_wrong : sum = denote_f [] sum_g (FRec sum_s0 (SRec CNil (SCons (SOp Badd (SVar 1) (SInt 2)) (SCons (SOp Badd (SVar 0) (SRd (SInt 0) (SVar 1))) SNil)))) := eq_refl.

(* calls: a helper without memory, and a loop calling it; the helper's theorem is the callee assumption of the loop's *)
Definition h (a b : i63) : i63 := PrimInt63.add (PrimInt63.mul a 2) b.
Definition h_g := mksig 0 (nk 2) false false false None.
Definition h_b := FPlain (SOp Badd (SOp Bmul (SVar 1) (SInt 2)) (SVar 0)).
Fixpoint loop (n : nat) (i acc : i63) (s : mem) : i63 :=
  match n with O => acc | S m => loop m (PrimInt63.add i 1) (h acc (KQ.KQRun.rd 0 i s)) s end.
Definition loop_g := mksig 1 (nk 2) true false false None.
Definition loop_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 1) (SInt 1))
                                  (SCons (SCall 0 CNil (SCons (SVar 0) (SCons (SRd (SInt 0) (SVar 1)) SNil))) SNil))).
Definition hl_P := mkprog [(gid1 0, compile_f gid1 0 h_g h_b); (gid1 1, compile_f gid1 1 loop_g loop_b)] [].
Time Lemma h_ok : callee_ok hl_P (gid1 0) (cbz 0) h_g h.
Proof. Time exact_no_check (compile_f_ok hl_P [] gid1 0 h_g h_b eq_refl eq_refl (no_callees hl_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma loop_ok : callee_ok hl_P (gid1 1) (cbz 1) loop_g loop.
Proof.
  refine (compile_f_ok hl_P [existT ftype h_g h] gid1 1 loop_g loop_b eq_refl eq_refl _ eq_refl eq_refl).
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

Definition long_s1 := (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 1))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 2))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 3))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 4))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 5))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 6))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 7))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 8))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 9))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 10))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 11))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 12))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 13))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 14))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 15))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 16))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 17))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 18))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 19))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 20))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 21))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 22))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 23))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 24))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 25))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 26))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 27))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 28))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 29))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 30))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 31))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 32))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 33))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 34))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 35))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 36))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 37))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 38))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 39))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 40))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 41))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 42))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 43))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 44))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 45))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 46))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 47))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 48))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 49))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 50))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 51))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 52))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 53))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 54))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 55))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 56))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 57))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 58))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 59))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 60))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 61))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 62))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 63))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 64))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 65))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 66))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 67))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 68))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 69))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 70))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 71))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 72))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 73))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 74))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 75))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 76))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 77))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 78))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 79))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 80))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 81))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 82))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 83))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 84))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 85))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 86))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 87))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 88))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 89))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 90))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 91))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 92))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 93))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 94))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 95))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 96))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 97))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 98))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 99))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 100))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 101))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 102))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 103))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 104))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 105))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 106))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 107))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 108))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 109))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 110))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 111))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 112))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 113))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 114))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 115))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 116))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 117))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 118))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 119))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 120))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 121))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 122))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 123))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 124))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 125))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 126))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 127))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 128))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 129))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 130))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 131))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 132))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 133))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 134))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 135))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 136))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 137))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 138))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 139))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 140))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 141))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 142))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 143))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 144))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 145))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 146))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 147))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 148))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 149))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 150))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 151))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 152))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 153))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 154))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 155))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 156))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 157))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 158))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 159))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 160))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 161))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 162))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 163))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 164))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 165))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 166))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 167))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 168))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 169))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 170))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 171))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 172))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 173))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 174))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 175))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 176))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 177))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 178))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 179))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 180))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 181))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 182))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 183))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 184))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 185))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 186))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 187))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 188))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 189))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 190))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 191))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 192))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 193))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 194))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 195))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 196))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 197))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 198))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 199))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 200))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 201))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 202))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 203))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 204))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 205))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 206))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 207))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 208))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 209))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 210))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 211))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 212))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 213))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 214))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 215))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 216))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 217))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 218))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 219))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 220))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 221))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 222))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 223))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 224))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 225))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 226))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 227))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 228))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 229))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 230))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 231))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 232))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 233))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 234))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 235))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 236))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 237))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 238))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 239))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 240))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 241))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 242))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 243))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 244))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 245))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 246))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 247))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 248))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 249))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 250))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 251))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 252))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 253))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 254))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 255))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 256))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 257))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 258))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 259))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 260))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 261))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 262))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 263))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 264))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 265))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 266))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 267))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 268))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 269))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 270))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 271))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 272))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 273))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 274))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 275))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 276))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 277))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 278))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 279))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 280))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 281))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 282))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 283))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 284))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 285))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 286))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 287))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 288))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 289))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 290))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 291))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 292))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 293))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 294))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 295))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 296))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 297))) (SLet (SOp Bmul (SVar 0) (SRd (SInt 0) (SInt 298))) (SLet (SOp Blxor (SVar 0) (SRd (SInt 0) (SInt 299))) (SLet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 300))) (SRec CNil (SCons (SVar 0) SNil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition long_g := mksig 1 (nk 1) true false false None.
Definition long_b := FRec (SVar 0) long_s1.
Time Lemma long_is : long = denote_f [] long_g long_b.
Proof. Time exact_no_check (eq_refl long). Time Qed.
Definition long_P := mkprog [(gid1 0, compile_f gid1 0 long_g long_b)] [].
Time Lemma long_ok : callee_ok long_P (gid1 0) (cbz 0) long_g long.
Proof. Time exact_no_check (compile_f_ok long_P [] gid1 0 long_g long_b eq_refl eq_refl (no_callees long_P gid1) eq_refl eq_refl). Time Qed.

(* ---------------------------------------------------------------- memory writes *)
(* a loop filling the memory: cell i of block 0 gets 2 i, for n cells *)
Fixpoint fill (n : nat) (i : i63) (s : mem) : mem :=
  match n with O => s | S m => fill m (PrimInt63.add i 1) (KQ.KQRun.upd 0 i (PrimInt63.mul i 2) s) end.
Definition fill_g := mksig 1 (nk 1) true true false None.
Definition fill_b := FRecM MCur (MRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil) (MUpd (SInt 0) (SVar 0) (SOp Bmul (SVar 0) (SInt 2)) MCur)).
Time Lemma fill_is : fill = denote_f [] fill_g fill_b.
Proof. Time exact_no_check (eq_refl fill). Time Qed.

(* not a tail call: the cells after i first, then cell i gets itself plus the next cell (a suffix sum) *)
Fixpoint suffix (n : nat) (i : i63) (s : mem) : mem :=
  match n with
  | O => s
  | S m => let s2 := suffix m (PrimInt63.add i 1) s in
           KQ.KQRun.upd 0 i (PrimInt63.add (KQ.KQRun.rd 0 i s2) (KQ.KQRun.rd 0 (PrimInt63.add i 1) s2)) s2
  end.
Definition suffix_g := mksig 1 (nk 1) true true false None.
Definition suffix_b := FRecM MCur (MLetM (MRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil) MCur)
  (MUpd (SInt 0) (SVar 0) (SOp Badd (SRd (SInt 0) (SVar 0)) (SRd (SInt 0) (SOp Badd (SVar 0) (SInt 1)))) MCur)).

(* a plain function giving back a memory: a test, a write, a call of [fill] on the written memory *)
Definition init (n : nat) (k : i63) (s : mem) : mem :=
  if PrimInt63.ltb k 10 then fill n k (KQ.KQRun.upd 1 0 k s) else KQ.KQRun.upd 1 0 0 s.
Definition init_g := mksig 1 (nk 1) true true false None.
Definition init_b := FPlainM (MIf Clt (SVar 0) (SInt 10)
  (MCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil) (MUpd (SInt 1) (SInt 0) (SVar 0) MCur))
  (MUpd (SInt 1) (SInt 0) (SInt 0) MCur)).

(* the three get their theorems: [init]'s uses [fill]'s as the callee assumption *)
Definition mem_P := mkprog [(gid1 0, compile_f gid1 0 fill_g fill_b); (gid1 1, compile_f gid1 1 suffix_g suffix_b);
                            (gid1 2, compile_f gid1 2 init_g init_b)] [].
Time Lemma fill_ok : callee_ok mem_P (gid1 0) (cbz 0) fill_g fill.
Proof. Time exact_no_check (compile_f_ok mem_P [] gid1 0 fill_g fill_b eq_refl eq_refl (no_callees mem_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma suffix_ok : callee_ok mem_P (gid1 1) (cbz 1) suffix_g suffix.
Proof. Time exact_no_check (compile_f_ok mem_P [] gid1 1 suffix_g suffix_b eq_refl eq_refl (no_callees mem_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma init_ok : callee_ok mem_P (gid1 2) (cbz 2) init_g init.
Proof.
  refine (compile_f_ok mem_P [existT ftype fill_g fill] gid1 2 init_g init_b eq_refl eq_refl _ eq_refl eq_refl).
  intros [|[|f]]; simpl; [exact fill_ok | exact Logic.I | exact Logic.I].
Time Qed.

(* linearity is in the syntax: a body that names an older memory has no tree; a tree that writes where the text does not is
   refused by the check *)
Time Fail Definition fill_wrong : fill = denote_f [] fill_g (FRecM MCur (MRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)
  (MUpd (SInt 0) (SVar 0) (SOp Bmul (SVar 0) (SInt 3)) MCur))) := eq_refl.

(* straight-line read-modify-writes: each memory is read and then written *)
Definition chain_g := mksig 0 (nk 0) true true false None.
Definition chain10 (s : mem) : mem :=
  let s1 := KQ.KQRun.upd 0 1 (PrimInt63.add (KQ.KQRun.rd 0 0 s) 1) s in
  let s2 := KQ.KQRun.upd 0 2 (PrimInt63.add (KQ.KQRun.rd 0 1 s1) 1) s1 in
  let s3 := KQ.KQRun.upd 0 3 (PrimInt63.add (KQ.KQRun.rd 0 2 s2) 1) s2 in
  let s4 := KQ.KQRun.upd 0 4 (PrimInt63.add (KQ.KQRun.rd 0 3 s3) 1) s3 in
  let s5 := KQ.KQRun.upd 0 5 (PrimInt63.add (KQ.KQRun.rd 0 4 s4) 1) s4 in
  let s6 := KQ.KQRun.upd 0 6 (PrimInt63.add (KQ.KQRun.rd 0 5 s5) 1) s5 in
  let s7 := KQ.KQRun.upd 0 7 (PrimInt63.add (KQ.KQRun.rd 0 6 s6) 1) s6 in
  let s8 := KQ.KQRun.upd 0 8 (PrimInt63.add (KQ.KQRun.rd 0 7 s7) 1) s7 in
  let s9 := KQ.KQRun.upd 0 9 (PrimInt63.add (KQ.KQRun.rd 0 8 s8) 1) s8 in
  let s10 := KQ.KQRun.upd 0 10 (PrimInt63.add (KQ.KQRun.rd 0 9 s9) 1) s9 in
  s10.
Definition chain10_b := FPlainM (MLetM (MUpd (SInt 0) (SInt 1) (SOp Badd (SRd (SInt 0) (SInt 0)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 2) (SOp Badd (SRd (SInt 0) (SInt 1)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 3) (SOp Badd (SRd (SInt 0) (SInt 2)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 4) (SOp Badd (SRd (SInt 0) (SInt 3)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 5) (SOp Badd (SRd (SInt 0) (SInt 4)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 6) (SOp Badd (SRd (SInt 0) (SInt 5)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 7) (SOp Badd (SRd (SInt 0) (SInt 6)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 8) (SOp Badd (SRd (SInt 0) (SInt 7)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 9) (SOp Badd (SRd (SInt 0) (SInt 8)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 10) (SOp Badd (SRd (SInt 0) (SInt 9)) (SInt 1)) MCur) MCur)))))))))).
Time Lemma chain10_is : chain10 = denote_f [] chain_g chain10_b.
Proof. Time exact_no_check (eq_refl chain10). Time Qed.
Definition chain10_P := mkprog [(gid1 0, compile_f gid1 0 chain_g chain10_b)] [].
Time Lemma chain10_ok : callee_ok chain10_P (gid1 0) (cbz 0) chain_g chain10.
Proof. Time exact_no_check (compile_f_ok chain10_P [] gid1 0 chain_g chain10_b eq_refl eq_refl (no_callees chain10_P gid1) eq_refl eq_refl). Time Qed.
Definition chain20 (s : mem) : mem :=
  let s1 := KQ.KQRun.upd 0 1 (PrimInt63.add (KQ.KQRun.rd 0 0 s) 1) s in
  let s2 := KQ.KQRun.upd 0 2 (PrimInt63.add (KQ.KQRun.rd 0 1 s1) 1) s1 in
  let s3 := KQ.KQRun.upd 0 3 (PrimInt63.add (KQ.KQRun.rd 0 2 s2) 1) s2 in
  let s4 := KQ.KQRun.upd 0 4 (PrimInt63.add (KQ.KQRun.rd 0 3 s3) 1) s3 in
  let s5 := KQ.KQRun.upd 0 5 (PrimInt63.add (KQ.KQRun.rd 0 4 s4) 1) s4 in
  let s6 := KQ.KQRun.upd 0 6 (PrimInt63.add (KQ.KQRun.rd 0 5 s5) 1) s5 in
  let s7 := KQ.KQRun.upd 0 7 (PrimInt63.add (KQ.KQRun.rd 0 6 s6) 1) s6 in
  let s8 := KQ.KQRun.upd 0 8 (PrimInt63.add (KQ.KQRun.rd 0 7 s7) 1) s7 in
  let s9 := KQ.KQRun.upd 0 9 (PrimInt63.add (KQ.KQRun.rd 0 8 s8) 1) s8 in
  let s10 := KQ.KQRun.upd 0 10 (PrimInt63.add (KQ.KQRun.rd 0 9 s9) 1) s9 in
  let s11 := KQ.KQRun.upd 0 11 (PrimInt63.add (KQ.KQRun.rd 0 10 s10) 1) s10 in
  let s12 := KQ.KQRun.upd 0 12 (PrimInt63.add (KQ.KQRun.rd 0 11 s11) 1) s11 in
  let s13 := KQ.KQRun.upd 0 13 (PrimInt63.add (KQ.KQRun.rd 0 12 s12) 1) s12 in
  let s14 := KQ.KQRun.upd 0 14 (PrimInt63.add (KQ.KQRun.rd 0 13 s13) 1) s13 in
  let s15 := KQ.KQRun.upd 0 15 (PrimInt63.add (KQ.KQRun.rd 0 14 s14) 1) s14 in
  let s16 := KQ.KQRun.upd 0 16 (PrimInt63.add (KQ.KQRun.rd 0 15 s15) 1) s15 in
  let s17 := KQ.KQRun.upd 0 17 (PrimInt63.add (KQ.KQRun.rd 0 16 s16) 1) s16 in
  let s18 := KQ.KQRun.upd 0 18 (PrimInt63.add (KQ.KQRun.rd 0 17 s17) 1) s17 in
  let s19 := KQ.KQRun.upd 0 19 (PrimInt63.add (KQ.KQRun.rd 0 18 s18) 1) s18 in
  let s20 := KQ.KQRun.upd 0 20 (PrimInt63.add (KQ.KQRun.rd 0 19 s19) 1) s19 in
  s20.
Definition chain20_b := FPlainM (MLetM (MUpd (SInt 0) (SInt 1) (SOp Badd (SRd (SInt 0) (SInt 0)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 2) (SOp Badd (SRd (SInt 0) (SInt 1)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 3) (SOp Badd (SRd (SInt 0) (SInt 2)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 4) (SOp Badd (SRd (SInt 0) (SInt 3)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 5) (SOp Badd (SRd (SInt 0) (SInt 4)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 6) (SOp Badd (SRd (SInt 0) (SInt 5)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 7) (SOp Badd (SRd (SInt 0) (SInt 6)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 8) (SOp Badd (SRd (SInt 0) (SInt 7)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 9) (SOp Badd (SRd (SInt 0) (SInt 8)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 10) (SOp Badd (SRd (SInt 0) (SInt 9)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 11) (SOp Badd (SRd (SInt 0) (SInt 10)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 12) (SOp Badd (SRd (SInt 0) (SInt 11)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 13) (SOp Badd (SRd (SInt 0) (SInt 12)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 14) (SOp Badd (SRd (SInt 0) (SInt 13)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 15) (SOp Badd (SRd (SInt 0) (SInt 14)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 16) (SOp Badd (SRd (SInt 0) (SInt 15)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 17) (SOp Badd (SRd (SInt 0) (SInt 16)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 18) (SOp Badd (SRd (SInt 0) (SInt 17)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 19) (SOp Badd (SRd (SInt 0) (SInt 18)) (SInt 1)) MCur) (MLetM (MUpd (SInt 0) (SInt 20) (SOp Badd (SRd (SInt 0) (SInt 19)) (SInt 1)) MCur) MCur)))))))))))))))))))).
Time Lemma chain20_is : chain20 = denote_f [] chain_g chain20_b.
Proof. Time exact_no_check (eq_refl chain20). Time Qed.
Definition chain20_P := mkprog [(gid1 0, compile_f gid1 0 chain_g chain20_b)] [].
Time Lemma chain20_ok : callee_ok chain20_P (gid1 0) (cbz 0) chain_g chain20.
Proof. Time exact_no_check (compile_f_ok chain20_P [] gid1 0 chain_g chain20_b eq_refl eq_refl (no_callees chain20_P gid1) eq_refl eq_refl). Time Qed.


(* ---------------------------------------------------------------- counters as values *)
(* two counters: [rounds] recurses on r and gives n on, to [inner] and to itself *)
Fixpoint inner (n : nat) (acc : i63) : i63 := match n with O => acc | S m => inner m (PrimInt63.add acc 1) end.
Fixpoint rounds (r n : nat) (acc : i63) : i63 := match r with O => acc | S m => rounds m n (inner n acc) end.
Definition inner_g := mksig 1 (nk 1) false false false None.
Definition inner_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition rounds_g := mksig 2 (nk 1) false false false None.
Definition rounds_b := FRec (SVar 0) (SRec (CCons (CVar 1) CNil) (SCons (SCall 0 (CCons (CVar 1) CNil) (SCons (SVar 0) SNil)) SNil)).
(* a match on a counter inside a body, a successor of a successor given to a callee *)
Definition twice (n : nat) (a : i63) : i63 := match n with O => a | S p => inner (S (S p)) a end.
Definition twice_g := mksig 1 (nk 1) false false false None.
Definition twice_b := FPlain (SMatch 0 (SVar 0) (SCall 0 (CCons (CS (CS (CVar 0))) CNil) (SCons (SVar 0) SNil))).
(* a budget made from a number *)
Definition bud (x : i63) : i63 := inner (KQ.KQRun.kq_nat x) 0.
Definition bud_g := mksig 0 (nk 1) false false false None.
Definition bud_b := FPlain (SCall 0 (CCons (CNat (SVar 0)) CNil) (SCons (SInt 0) SNil)).
Definition cnt_P := mkprog [(gid1 0, compile_f gid1 0 inner_g inner_b); (gid1 1, compile_f gid1 1 rounds_g rounds_b);
                            (gid1 2, compile_f gid1 2 twice_g twice_b); (gid1 3, compile_f gid1 3 bud_g bud_b)] [].
Time Lemma inner_ok : callee_ok cnt_P (gid1 0) (cbz 0) inner_g inner.
Proof. Time exact_no_check (compile_f_ok cnt_P [] gid1 0 inner_g inner_b eq_refl eq_refl (no_callees cnt_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma rounds_ok : callee_ok cnt_P (gid1 1) (cbz 1) rounds_g rounds.
Proof.
  Time exact_no_check (compile_f_ok cnt_P [existT ftype inner_g inner] gid1 1 rounds_g rounds_b eq_refl eq_refl
    (all_ok_callees cnt_P gid1 [existT ftype inner_g inner] (conj inner_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma twice_ok : callee_ok cnt_P (gid1 2) (cbz 2) twice_g twice.
Proof.
  Time exact_no_check (compile_f_ok cnt_P [existT ftype inner_g inner; existT ftype rounds_g rounds] gid1 2 twice_g twice_b eq_refl eq_refl
    (all_ok_callees cnt_P gid1 [existT ftype inner_g inner; existT ftype rounds_g rounds] (conj inner_ok (conj rounds_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Time Lemma bud_ok : callee_ok cnt_P (gid1 3) (cbz 3) bud_g bud.
Proof.
  Time exact_no_check (compile_f_ok cnt_P [existT ftype inner_g inner; existT ftype rounds_g rounds; existT ftype twice_g twice]
    gid1 3 bud_g bud_b eq_refl eq_refl
    (all_ok_callees cnt_P gid1 [existT ftype inner_g inner; existT ftype rounds_g rounds; existT ftype twice_g twice]
       (conj inner_ok (conj rounds_ok (conj twice_ok Logic.I)))) eq_refl eq_refl).
Time Qed.
Print Assumptions bud_ok.
(* a counter grown at every round of a recursion: no bound of each counter holds it, refused by wf without weights (with
   them, step 37's tests at the end) *)
Fixpoint grow (r n : nat) (acc : i63) : i63 := match r with O => acc | S m => grow m (S n) acc end.
Time Fail Definition grow_wf : wf_f [] (mksig 2 (nk 1) false false false None) (FRec (SVar 0) (SRec (CCons (CS (CVar 1)) CNil) (SCons (SVar 0) SNil))) = true
  := eq_refl.

(* ---------------------------------------------------------------- a choice between two numbers: a conditional move *)
(* the smaller of two numbers written into a cell (CF295B's inner loop): both worked out, one taken, no jump (D17) *)
Fixpoint relax (n : nat) (j d : i63) (s : mem) : mem :=
  match n with
  | O => s
  | S m => let a := KQ.KQRun.rd 0 j s in let b := PrimInt63.add d (KQ.KQRun.rd 1 j s) in
           relax m (PrimInt63.add j 1) d (KQ.KQRun.upd 0 j (if PrimInt63.ltb b a then b else a) s)
  end.
Definition relax_g := mksig 1 (nk 2) true true false None.
Definition relax_b := FRecM MCur (MLet (SRd (SInt 0) (SVar 1)) (MLet (SOp Badd (SVar 1) (SRd (SInt 1) (SVar 2)))
  (MRec CNil (SCons (SOp Badd (SVar 3) (SInt 1)) (SCons (SVar 2) SNil))
        (MUpd (SInt 0) (SVar 3) (SIf Clt (SVar 0) (SVar 1) (SVar 0) (SVar 1)) MCur)))).
Check (eq_refl : choice_ok (SVar 0) (SVar 1) = true).
Definition relax_P := mkprog [(gid1 0, compile_f gid1 0 relax_g relax_b)] [].
Time Lemma relax_ok : callee_ok relax_P (gid1 0) (cbz 0) relax_g relax.
Proof. Time exact_no_check (compile_f_ok relax_P [] gid1 0 relax_g relax_b eq_refl eq_refl (no_callees relax_P gid1) eq_refl eq_refl). Time Qed.
(* the KQL has the conditional move *)
Fixpoint has_sel (e : exp) : bool :=
  match e with
  | Esel _ _ _ _ _ _ _ => true
  | Eop _ _ _ _ k | Ecall _ _ _ k | Ekld _ _ _ k | Ekst _ _ _ k => has_sel k
  | Eif _ _ _ t e => has_sel t || has_sel e
  | _ => false
  end.
Check (eq_refl : has_sel (kbody (compile_f gid1 0 relax_g relax_b)) = true).

(* ---------------------------------------------------------------- booleans *)
(* tests made of [&&], [||], [negb] choosing between two numbers: conditional moves on the parts, no jump *)
Definition chk (s : mem) : i63 :=
  PrimInt63.add (if andb (PrimInt63.ltb (KQ.KQRun.rd 0 0 s) 500) (PrimInt63.ltb (KQ.KQRun.rd 0 1 s) 500) then 0 else 1)
    (PrimInt63.add (if orb (PrimInt63.ltb (KQ.KQRun.rd 0 5 s) 500) (PrimInt63.ltb (KQ.KQRun.rd 0 6 s) 500) then 0 else 7)
       (if negb (PrimInt63.ltb (KQ.KQRun.rd 0 11 s) 500) then 0 else 31)).
Definition chk_g := mksig 0 (nk 0) true false false None.
Definition chk_b := FPlain (SOp Badd
  (SIfB (BAnd (BCmp Clt (SRd (SInt 0) (SInt 0)) (SInt 500)) (BCmp Clt (SRd (SInt 0) (SInt 1)) (SInt 500))) (SInt 0) (SInt 1))
  (SOp Badd (SIfB (BOr (BCmp Clt (SRd (SInt 0) (SInt 5)) (SInt 500)) (BCmp Clt (SRd (SInt 0) (SInt 6)) (SInt 500))) (SInt 0) (SInt 7))
            (SIfB (BNot (BCmp Clt (SRd (SInt 0) (SInt 11)) (SInt 500))) (SInt 0) (SInt 31)))).
(* a boolean let, then a test of it at the end of a loop: jumps; [&&] as the value 1 or 0 *)
Fixpoint cnt_in (n : nat) (i lo hi acc : i63) (s : mem) : i63 :=
  match n with
  | O => acc
  | S m => let x := KQ.KQRun.rd 0 i s in
           let ok := andb (PrimInt63.leb lo x) (PrimInt63.ltb x hi) in
           if ok then cnt_in m (PrimInt63.add i 1) lo hi (PrimInt63.add acc 1) s
           else cnt_in m (PrimInt63.add i 1) lo hi acc s
  end.
Definition cnt_in_g := mksig 1 (nk 4) true false false None.
Definition cnt_in_b := FRec (SVar 0) (SLet (SRd (SInt 0) (SVar 3)) (SLetB (BAnd (BCmp Cle (SVar 3) (SVar 0)) (BCmp Clt (SVar 0) (SVar 2)))
  (SIfB (BVar 0) (SRec CNil (SCons (SOp Badd (SVar 4) (SInt 1)) (SCons (SVar 3) (SCons (SVar 2) (SCons (SOp Badd (SVar 1) (SInt 1)) SNil)))))
                 (SRec CNil (SCons (SOp Badd (SVar 4) (SInt 1)) (SCons (SVar 3) (SCons (SVar 2) (SCons (SVar 1) SNil)))))))).
(* a memory chosen by [a && negb b]: jumps *)
Definition mark (v q m l : i63) (s : mem) : mem :=
  if andb (PrimInt63.leb m l) (negb (PrimInt63.eqb (KQ.KQRun.rd 1 v s) q)) then KQ.KQRun.upd 1 v q s else s.
Definition mark_g := mksig 0 (nk 4) true true false None.
Definition mark_b := FPlainM (MIfB (BAnd (BCmp Cle (SVar 1) (SVar 0)) (BNot (BCmp Ceq (SRd (SInt 1) (SVar 3)) (SVar 2))))
  (MUpd (SInt 1) (SVar 3) (SVar 2) MCur) MCur).
Definition bool_P := mkprog [(gid1 0, compile_f gid1 0 chk_g chk_b); (gid1 1, compile_f gid1 1 cnt_in_g cnt_in_b);
                             (gid1 2, compile_f gid1 2 mark_g mark_b)] [].
Time Lemma chk_ok : callee_ok bool_P (gid1 0) (cbz 0) chk_g chk.
Proof. Time exact_no_check (compile_f_ok bool_P [] gid1 0 chk_g chk_b eq_refl eq_refl (no_callees bool_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma cnt_in_ok : callee_ok bool_P (gid1 1) (cbz 1) cnt_in_g cnt_in.
Proof. Time exact_no_check (compile_f_ok bool_P [] gid1 1 cnt_in_g cnt_in_b eq_refl eq_refl (no_callees bool_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma mark_ok : callee_ok bool_P (gid1 2) (cbz 2) mark_g mark.
Proof. Time exact_no_check (compile_f_ok bool_P [] gid1 2 mark_g mark_b eq_refl eq_refl (no_callees bool_P gid1) eq_refl eq_refl). Time Qed.
Check (eq_refl : has_sel (kbody (compile_f gid1 0 chk_g chk_b)) = true).
(* the conditional moves of a code, and the bit operations that would make boolean values: [chk]'s three choices are
   2 + 2 + 1 moves on the comparisons themselves, no boolean value worked out (the translator's choices on the parts) *)
Fixpoint shape (e : exp) : nat * nat :=
  match e with
  | Esel _ _ _ _ _ _ k => let '(a, b) := shape k in (S a, b)
  | Eop _ o _ _ k => let '(a, b) := shape k in (a, match o with Bland | Blor | Blxor => S b | _ => b end)
  | Ecall _ _ _ k | Ekld _ _ _ k | Ekst _ _ _ k => shape k
  | Eif _ _ _ t e => let '(a, b) := shape t in let '(c, d) := shape e in (a + c, b + d)%nat
  | _ => (0, 0)%nat
  end.
Check (eq_refl : shape (kbody (compile_f gid1 0 chk_g chk_b)) = (5, 0)%nat).
(* a wrong tree ([||] where the text has [&&]) is refused by the check *)
Time Fail Definition chk_wrong : chk = denote_f [] chk_g (FPlain (SOp Badd
  (SIfB (BOr (BCmp Clt (SRd (SInt 0) (SInt 0)) (SInt 500)) (BCmp Clt (SRd (SInt 0) (SInt 1)) (SInt 500))) (SInt 0) (SInt 1))
  (SOp Badd (SIfB (BOr (BCmp Clt (SRd (SInt 0) (SInt 5)) (SInt 500)) (BCmp Clt (SRd (SInt 0) (SInt 6)) (SInt 500))) (SInt 0) (SInt 7))
            (SIfB (BNot (BCmp Clt (SRd (SInt 0) (SInt 11)) (SInt 500))) (SInt 0) (SInt 31))))) := eq_refl.
Print Assumptions cnt_in_ok.

(* ---------------------------------------------------------------- a written counter given to a call (F50) *)
(* the kernel compares [big] with the meaning of its tree; left to its own choice it unfolds [tw] first, and [tw] applied to
   20 is worked out round by round (two calls a round: 2^20 of them, 4.7 s and 1.2 GB measured).  The program's functions are
   unfolded last ([Strategy opaque], the order of unfolding only), and the check takes no time *)
Fixpoint tw (n : nat) (a : i63) : i63 := match n with O => a | S m => PrimInt63.add (tw m a) (tw m (PrimInt63.add a 1)) end.
Definition big (x : i63) : i63 := tw 20 x.
Definition tw_g := mksig 1 (nk 1) false false false None.
Definition tw_b := FRec (SVar 0) (SOp Badd (SRec CNil (SCons (SVar 0) SNil)) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil))).
Definition big_g := mksig 0 (nk 1) false false false None.
Definition big_b := FPlain (SCall 0 (CCons (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CO))))))))))))))))))))
  CNil) (SCons (SVar 0) SNil)).
Definition lit_P := mkprog [(gid1 0, compile_f gid1 0 tw_g tw_b); (gid1 1, compile_f gid1 1 big_g big_b)] [].
Strategy opaque [tw big].
Time Lemma tw_ok : callee_ok lit_P (gid1 0) (cbz 0) tw_g tw.
Proof. Time exact_no_check (compile_f_ok lit_P [] gid1 0 tw_g tw_b eq_refl eq_refl (no_callees lit_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma big_ok : callee_ok lit_P (gid1 1) (cbz 1) big_g big.
Proof.
  Time exact_no_check (compile_f_ok lit_P [existT ftype tw_g tw] gid1 1 big_g big_b eq_refl eq_refl
    (all_ok_callees lit_P gid1 [existT ftype tw_g tw] (conj tw_ok Logic.I)) eq_refl eq_refl).
Time Qed.


(* ---------------------------------------------------------------- a number made after memories *)
(* [mafter]: memories made by calls and lets, a test, and a number read from a memory made in place ([rd 0 2 (bump 2 s3)], which is
   [let s4 := bump 2 s3 in rd 0 2 s4] up to [let]): the KQL ends with the last memory made, the theorem says some memory *)
Definition bump (i : i63) (s : mem) : mem := KQ.KQRun.upd 0 i (PrimInt63.add (KQ.KQRun.rd 0 (PrimInt63.sub i 1) s) i) s.
Definition mafter (n : nat) (k : i63) (s : mem) : i63 :=
  let s2 := bump 1 s in
  let s3 := fill n k s2 in
  if PrimInt63.ltb (KQ.KQRun.rd 0 1 s3) 10 then KQ.KQRun.rd 0 2 (bump 2 s3) else PrimInt63.add k 1.
Definition bump_g := mksig 0 (nk 1) true true false None.
Definition bump_b := FPlainM (MUpd (SInt 0) (SVar 0) (SOp Badd (SRd (SInt 0) (SOp Bsub (SVar 0) (SInt 1))) (SVar 0)) MCur).
Definition after_g := mksig 1 (nk 1) true false true None.
Definition after_b := FPlainX (XLetM (MCall 0 CNil (SCons (SInt 1) SNil) MCur)
  (XLetM (MCall 1 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil) MCur)
    (XIf Clt (SRd (SInt 0) (SInt 1)) (SInt 10) (XLetM (MCall 0 CNil (SCons (SInt 2) SNil) MCur) (XRet (SRd (SInt 0) (SInt 2))))
         (XRet (SOp Badd (SVar 0) (SInt 1)))))).
Definition wr_P := mkprog [(gid1 0, compile_f gid1 0 bump_g bump_b); (gid1 1, compile_f gid1 1 fill_g fill_b);
                           (gid1 2, compile_f gid1 2 after_g after_b)] [].
Time Lemma bump_ok : callee_ok wr_P (gid1 0) (cbz 0) bump_g bump.
Proof. Time exact_no_check (compile_f_ok wr_P [] gid1 0 bump_g bump_b eq_refl eq_refl (no_callees wr_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma fill_ok2 : callee_ok wr_P (gid1 1) (cbz 1) fill_g fill.
Proof. Time exact_no_check (compile_f_ok wr_P [] gid1 1 fill_g fill_b eq_refl eq_refl (no_callees wr_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma after_ok : callee_ok wr_P (gid1 2) (cbz 2) after_g mafter.
Proof.
  Time exact_no_check (compile_f_ok wr_P [existT ftype bump_g bump; existT ftype fill_g fill] gid1 2 after_g after_b eq_refl eq_refl
    (all_ok_callees wr_P gid1 [existT ftype bump_g bump; existT ftype fill_g fill] (conj bump_ok (conj fill_ok2 Logic.I))) eq_refl eq_refl).
Time Qed.
Print Assumptions after_ok.
(* a call of a function that writes, from a number, is refused for now: the caller's memory would not be the text's *)
Check (eq_refl : wf_f [after_g] (mksig 1 (nk 1) true false false None) (FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil))) = false).

(* ---------------------------------------------------------------- two calls of the function itself merged into one *)
(* the smallest of the cells and where it is (CF868F's loop): [if v <? best then f .. v i s else f .. best opt s] is one
   loop step whose two differing arguments are chosen by conditional moves (D17), no jump *)
Fixpoint argmin (n : nat) (i best opt : i63) (s : mem) : i63 :=
  match n with
  | O => opt
  | S m => let v := KQ.KQRun.rd 0 i s in
           if PrimInt63.ltb v best then argmin m (PrimInt63.add i 1) v i s else argmin m (PrimInt63.add i 1) best opt s
  end.
Definition argmin_g := mksig 1 (nk 3) true false false None.
Definition argmin_b := FRec (SVar 0) (SLet (SRd (SInt 0) (SVar 2))
  (SIf Clt (SVar 0) (SVar 2) (SRec CNil (SCons (SOp Badd (SVar 3) (SInt 1)) (SCons (SVar 0) (SCons (SVar 3) SNil))))
                             (SRec CNil (SCons (SOp Badd (SVar 3) (SInt 1)) (SCons (SVar 2) (SCons (SVar 1) SNil)))))).
Definition argmin_P := mkprog [(gid1 0, compile_f gid1 0 argmin_g argmin_b)] [].
Time Lemma argmin_ok : callee_ok argmin_P (gid1 0) (cbz 0) argmin_g argmin.
Proof. Time exact_no_check (compile_f_ok argmin_P [] gid1 0 argmin_g argmin_b eq_refl eq_refl (no_callees argmin_P gid1) eq_refl eq_refl). Time Qed.
Check (eq_refl : has_sel (kbody (compile_f gid1 0 argmin_g argmin_b)) = true).

(* ---------------------------------------------------------------- narrow memory: cells of 4 bytes *)
Fixpoint acc32 (n : nat) (i : i63) (s : mem) : mem :=
  match n with
  | O => s
  | S m => acc32 m (PrimInt63.add i 1) (KQ.KQRun.upd32 1 i (PrimInt63.add (KQ.KQRun.rd32 1 (PrimInt63.sub i 1) s) i) s)
  end.
Fixpoint sum32 (n : nat) (i acc : i63) (s : mem) : i63 :=
  match n with O => acc | S m => sum32 m (PrimInt63.add i 1) (PrimInt63.add acc (KQ.KQRun.rd32 1 i s)) s end.
Definition acc32_g := mksig 1 (nk 1) true true false None.
Definition acc32_b := FRecM MCur (MRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)
  (MUpd32 (SInt 1) (SVar 0) (SOp Badd (SRd32 (SInt 1) (SOp Bsub (SVar 0) (SInt 1))) (SVar 0)) MCur)).
Definition sum32_g := mksig 1 (nk 2) true false false None.
Definition sum32_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SOp Badd (SVar 0) (SRd32 (SInt 1) (SVar 1))) SNil))).
Definition nar_P := mkprog [(gid1 0, compile_f gid1 0 acc32_g acc32_b); (gid1 1, compile_f gid1 1 sum32_g sum32_b)] [].
Time Lemma acc32_ok : callee_ok nar_P (gid1 0) (cbz 0) acc32_g acc32.
Proof. Time exact_no_check (compile_f_ok nar_P [] gid1 0 acc32_g acc32_b eq_refl eq_refl (no_callees nar_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma sum32_ok : callee_ok nar_P (gid1 1) (cbz 1) sum32_g sum32.
Proof. Time exact_no_check (compile_f_ok nar_P [] gid1 1 sum32_g sum32_b eq_refl eq_refl (no_callees nar_P gid1) eq_refl eq_refl). Time Qed.
Print Assumptions acc32_ok.

(* ---------------------------------------------------------------- a function given as a term *)
(* a recursive function that takes a function, applied to one: its meaning is not a fix over the counter, so it is not
   convertible to its tree's meaning; its statement comes from its two equations ([compile_f_okr]), each checked by
   conversion (the template unfolds one round on 0 or on S n) *)
Fixpoint tapply (n : nat) (f : i63 -> i63) (x : i63) : i63 := match n with O => x | S m => tapply m f (f x) end.
Definition tadd3 (x : i63) : i63 := PrimInt63.add x 3.
Definition tcopy : nat -> i63 -> i63 := fun n x => tapply n tadd3 x.
Definition tcopy_g := mksig 1 (nk 1) false false false None.
Definition tcopy_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 3)) SNil)).
Definition tcopy_P := mkprog [(gid1 0, compile_f gid1 0 tcopy_g tcopy_b)] [].
Time Lemma tcopy_ok : callee_ok tcopy_P (gid1 0) (cbz 0) tcopy_g tcopy.
Proof.
  Time exact_no_check (compile_f_okr tcopy_P [] gid1 0 0 (nk 1) false (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 3)) SNil)) None [] tcopy
    eq_refl eq_refl (no_callees tcopy_P gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Fail Definition tcopy_plain : tcopy = denote_f [] tcopy_g tcopy_b := eq_refl.
Print Assumptions tcopy_ok.

(* ---------------------------------------------------------------- a loop that writes and gives back a number *)
(* [deg] (the shape of CF7D's loop): each round reads a cell, writes the next one and adds to a total; the recursive call is the
   last step, given the memory written ([XRec]: a loop step).  Its end memory is the one its recursive call reaches, which that
   call's statement does not name, so the theorem says some memory.  [deg_top] calls it as its last step ([XCall]) *)
Fixpoint deg (n : nat) (i acc : i63) (s : mem) : i63 :=
  match n with
  | O => acc
  | S m => let d := PrimInt63.add (KQ.KQRun.rd 1 (PrimInt63.sub i 1) s) 1 in
           deg m (PrimInt63.add i 1) (PrimInt63.add acc d) (KQ.KQRun.upd 1 i d s)
  end.
Definition deg_top (n : nat) (s : mem) : i63 := deg n 1 0 (KQ.KQRun.upd 1 0 0 s).
Definition deg_g := mksig 1 (nk 2) true false true None.
Definition deg_b := FRecX (XRet (SVar 0)) (XLet (SOp Badd (SRd (SInt 1) (SOp Bsub (SVar 1) (SInt 1))) (SInt 1))
  (XRec CNil (SCons (SOp Badd (SVar 2) (SInt 1)) (SCons (SOp Badd (SVar 1) (SVar 0)) SNil)) (MUpd (SInt 1) (SVar 2) (SVar 0) MCur))).
Definition degt_g := mksig 1 (nk 0) true false true None.
Definition degt_b := FPlainX (XCall 0 (CCons (CVar 0) CNil) (SCons (SInt 1) (SCons (SInt 0) SNil)) (MUpd (SInt 1) (SInt 0) (SInt 0) MCur)).
Definition deg_P := mkprog [(gid1 0, compile_f gid1 0 deg_g deg_b); (gid1 1, compile_f gid1 1 degt_g degt_b)] [].
Time Lemma deg_ok : callee_ok deg_P (gid1 0) (cbz 0) deg_g deg.
Proof. Time exact_no_check (compile_f_ok deg_P [] gid1 0 deg_g deg_b eq_refl eq_refl (no_callees deg_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma degt_ok : callee_ok deg_P (gid1 1) (cbz 1) degt_g deg_top.
Proof.
  Time exact_no_check (compile_f_ok deg_P [existT ftype deg_g deg] gid1 1 degt_g degt_b eq_refl eq_refl
    (all_ok_callees deg_P gid1 [existT ftype deg_g deg] (conj deg_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions degt_ok.
(* the loop's call is a loop step, the caller's last call a call and a return *)
Check (eq_refl : match kbody (compile_f gid1 0 deg_g deg_b) with Eif _ _ _ _ (Eop _ _ _ _ (Eop _ _ _ _ (Ekld _ _ _ (Eop _ _ _ _
                   (Eop _ _ _ _ (Eop _ _ _ _ (Ekst _ _ _ (Eloop _)))))))) => true | _ => false end = true).
Check (eq_refl : match kbody (compile_f gid1 1 degt_g degt_b) with Ekst _ _ _ (Ecall _ _ _ (Eret _)) => true | _ => false end = true).
(* the recursive call inside an expression, or in a plain body, is not read in this step *)
Check (eq_refl : wf_f [] deg_g (FRecX (XRet (SVar 0)) (XRet (SOp Badd (SVar 1) (SRec CNil (SCons (SVar 1) (SCons (SVar 0) SNil)))))) = false).
Check (eq_refl : wf_f [] deg_g (FPlainX (XRec CNil (SCons (SVar 1) (SCons (SVar 0) SNil)) MCur)) = false).
(* a call of a number function that writes, in a number, is still refused: the caller's memory would not be the text's *)
Check (eq_refl : wf_f [deg_g] degt_g (FPlainX (XRet (SOp Badd (SInt 1) (SCall 0 (CCons (CVar 0) CNil) (SCons (SInt 1) (SCons (SInt 0) SNil)))))) = false).

(* a copy of a template that writes and gives back a number: its statement from its two equations ([compile_f_okrx]) *)
Fixpoint tdeg (n : nat) (f : i63 -> i63) (i acc : i63) (s : mem) : i63 :=
  match n with
  | O => acc
  | S m => tdeg m f (PrimInt63.add i 1) (PrimInt63.add acc (f (KQ.KQRun.rd 1 i s))) (KQ.KQRun.upd 1 i (f i) s)
  end.
Definition tdcopy : nat -> i63 -> i63 -> mem -> i63 := fun n i acc s => tdeg n tadd3 i acc s.
Definition tdcopy_g := mksig 1 (nk 2) true false true None.
Definition tdcopy_x1 := XRec CNil (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SOp Badd (SVar 0) (SOp Badd (SRd (SInt 1) (SVar 1)) (SInt 3))) SNil))
  (MUpd (SInt 1) (SVar 1) (SOp Badd (SVar 1) (SInt 3)) MCur).
Definition tdcopy_b := FRecX (XRet (SVar 0)) tdcopy_x1.
Definition tdcopy_P := mkprog [(gid1 0, compile_f gid1 0 tdcopy_g tdcopy_b)] [].
Time Lemma tdcopy_ok : callee_ok tdcopy_P (gid1 0) (cbz 0) tdcopy_g tdcopy.
Proof.
  Time exact_no_check (compile_f_okrx tdcopy_P [] gid1 0 0 (nk 2) (XRet (SVar 0)) tdcopy_x1 None [] tdcopy
    eq_refl eq_refl (no_callees tdcopy_P gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Print Assumptions tdcopy_ok.

(* ---------------------------------------------------------------- a boolean parameter *)
(* [bcount] counts down a loop with a boolean that says whether to add the cell, passed on to the recursive call and chosen
   by the caller ([bcall]): a boolean argument is its value, 1 or 0 *)
Fixpoint bcount (n : nat) (i acc : i63) (odd : bool) (s : mem) : i63 :=
  match n with
  | O => acc
  | S m => bcount m (PrimInt63.add i 1) (if odd then PrimInt63.add acc (KQ.KQRun.rd 0 i s) else acc) (negb odd) s
  end.
Definition bcall (n : nat) (a : i63) (s : mem) : i63 := bcount n 0 0 (PrimInt63.ltb a 5) s.
Definition bcount_g := mksig 1 [KNum; KNum; KBool] true false false None.
Definition bcount_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 1) (SInt 1))
  (SCons (SIfB (BVar 0) (SOp Badd (SVar 0) (SRd (SInt 0) (SVar 1))) (SVar 0)) (SConsB (BNot (BVar 0)) SNil)))).
Definition bcall_g := mksig 1 [KNum] true false false None.
Definition bcall_b := FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SInt 0) (SCons (SInt 0) (SConsB (BCmp Clt (SVar 0) (SInt 5)) SNil)))).
Definition bcount_P := mkprog [(gid1 0, compile_f gid1 0 bcount_g bcount_b); (gid1 1, compile_f gid1 1 bcall_g bcall_b)] [].
Time Lemma bcount_ok : callee_ok bcount_P (gid1 0) (cbz 0) bcount_g bcount.
Proof. Time exact_no_check (compile_f_ok bcount_P [] gid1 0 bcount_g bcount_b eq_refl eq_refl (no_callees bcount_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma bcall_ok : callee_ok bcount_P (gid1 1) (cbz 1) bcall_g bcall.
Proof.
  Time exact_no_check (compile_f_ok bcount_P [existT ftype bcount_g bcount] gid1 1 bcall_g bcall_b eq_refl eq_refl
    (all_ok_callees bcount_P gid1 [existT ftype bcount_g bcount] (conj bcount_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions bcall_ok.
(* the boolean passed to the recursive call is a value: no merge of calls on it, the test stays as it is *)
Check (eq_refl : mt_e (SRec CNil (SConsB BTrue SNil)) = None).

(* ---------------------------------------------------------------- machine operations (step 14) *)
(* [mmio] (hw_mmio's loop): a store to a device, a fence, a load into a cell, the cell read, the recursive call; [hsz]: a
   number the machine gives and a block's size; [hgrow]: a block grown *)
Fixpoint mmio (fuel : nat) (i acc : i63) (s : mem) : i63 :=
  match fuel with
  | O => acc
  | S f => let a := PrimInt63.add 268435456 (PrimInt63.mul 4 (PrimInt63.land i 15)) in
           let s1 := KQ.KQRun.hw_store 4 a (PrimInt63.mul i 3) s in
           let s2 := KQ.KQRun.hw_fence 0 s1 in
           let s3 := KQ.KQRun.hw_load 4 a 3 0 s2 in
           mmio f (PrimInt63.add i 1) (PrimInt63.add acc (KQ.KQRun.rd 3 0 s3)) s3
  end.
Definition hsz (s : mem) : i63 := PrimInt63.add (KQ.KQRun.hw_addr 4) (KQ.KQRun.kq_size 3 s).
Definition hgrow (n : i63) (s : mem) : mem := KQ.KQRun.kq_grow 2 n s.
Definition mmio_g := mksig 1 [KNum; KNum] true false true None.
Definition mmio_b := FRecX (XRet (SVar 0))
  (XLet (SOp Badd (SInt 268435456) (SOp Bmul (SInt 4) (SOp Bland (SVar 1) (SInt 15))))
    (XLetM (MHw HStore (SCons (SInt 4) (SCons (SVar 0) (SCons (SOp Bmul (SVar 2) (SInt 3)) SNil))) MCur)
      (XLetM (MHw HFence (SCons (SInt 0) SNil) MCur)
        (XLetM (MHw HLoad (SCons (SInt 4) (SCons (SVar 0) (SCons (SInt 3) (SCons (SInt 0) SNil)))) MCur)
          (XRec CNil (SCons (SOp Badd (SVar 2) (SInt 1)) (SCons (SOp Badd (SVar 1) (SRd (SInt 3) (SInt 0))) SNil)) MCur))))).
Definition hsz_g := mksig 0 [] true false false None.
Definition hsz_b := FPlain (SOp Badd (SHwf FAddr (SCons (SInt 4) SNil)) (SSize (SInt 3))).
Definition hgrow_g := mksig 0 [KNum] true true false None.
Definition hgrow_b := FPlainM (MHw HGrow (SCons (SInt 2) (SCons (SVar 0) SNil)) MCur).
Definition hw_P := mkprog [(gid1 0, compile_f gid1 0 mmio_g mmio_b); (gid1 1, compile_f gid1 1 hsz_g hsz_b); (gid1 2, compile_f gid1 2 hgrow_g hgrow_b)] [].
Time Lemma mmio_ok : callee_ok hw_P (gid1 0) (cbz 0) mmio_g mmio.
Proof. Time exact_no_check (compile_f_ok hw_P [] gid1 0 mmio_g mmio_b eq_refl eq_refl (no_callees hw_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma hsz_ok : callee_ok hw_P (gid1 1) (cbz 1) hsz_g hsz.
Proof.
  Time exact_no_check (compile_f_ok hw_P [existT ftype mmio_g mmio] gid1 1 hsz_g hsz_b eq_refl eq_refl
    (all_ok_callees hw_P gid1 [existT ftype mmio_g mmio] (conj mmio_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma hgrow_ok : callee_ok hw_P (gid1 2) (cbz 2) hgrow_g hgrow.
Proof.
  Time exact_no_check (compile_f_ok hw_P [existT ftype mmio_g mmio; existT ftype hsz_g hsz] gid1 2 hgrow_g hgrow_b eq_refl eq_refl
    (all_ok_callees hw_P gid1 [existT ftype mmio_g mmio; existT ftype hsz_g hsz] (conj mmio_ok (conj hsz_ok Logic.I))) eq_refl eq_refl).
Time Qed.
Print Assumptions hgrow_ok.
(* the code: each operation is one KQL instruction *)
Check (eq_refl : match kbody (compile_f gid1 2 hgrow_g hgrow_b) with Ehw HGrow _ (Eret _) => true | _ => false end = true).
(* an operation given the wrong number of arguments, and a size where there is no memory, are not well formed *)
Check (eq_refl : wf_f [] (mksig 0 [KNum] true true false None) (FPlainM (MHw HGrow (SCons (SInt 2) SNil) MCur)) = false).
Check (eq_refl : wf_f [] (mksig 0 [] false false false None) (FPlain (SSize (SInt 3))) = false).

(* ---------------------------------------------------------------- bytes (step 15) *)
(* [bsum] adds the bytes of a narrow block, [bfill] writes them: one byte access each *)
Fixpoint bsum (n : nat) (i acc : i63) (s : mem) : i63 :=
  match n with O => acc | S m => bsum m (PrimInt63.add i 1) (PrimInt63.add acc (KQ.KQRun.rd8 1 i s)) s end.
Fixpoint bfill (n : nat) (i : i63) (s : mem) : mem :=
  match n with O => s | S m => bfill m (PrimInt63.add i 1) (KQ.KQRun.upd8 1 i (PrimInt63.mul i 7) s) end.
Definition bsum_g := mksig 1 [KNum; KNum] true false false None.
Definition bsum_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SOp Badd (SVar 0) (SRd8 (SInt 1) (SVar 1))) SNil))).
Definition bfill_g := mksig 1 [KNum] true true false None.
Definition bfill_b := FRecM MCur (MRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil) (MUpd8 (SInt 1) (SVar 0) (SOp Bmul (SVar 0) (SInt 7)) MCur)).
Definition b8_P := mkprog [(gid1 0, compile_f gid1 0 bsum_g bsum_b); (gid1 1, compile_f gid1 1 bfill_g bfill_b)] [].
Time Lemma bsum_ok : callee_ok b8_P (gid1 0) (cbz 0) bsum_g bsum.
Proof. Time exact_no_check (compile_f_ok b8_P [] gid1 0 bsum_g bsum_b eq_refl eq_refl (no_callees b8_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma bfill_ok : callee_ok b8_P (gid1 1) (cbz 1) bfill_g bfill.
Proof.
  Time exact_no_check (compile_f_ok b8_P [existT ftype bsum_g bsum] gid1 1 bfill_g bfill_b eq_refl eq_refl
    (all_ok_callees b8_P gid1 [existT ftype bsum_g bsum] (conj bsum_ok Logic.I)) eq_refl eq_refl).
Time Qed.
(* the code: a byte read is one Ekld8, a byte written one Ekst8 *)
Check (eq_refl : match kbody (compile_f gid1 0 bsum_g bsum_b) with
                 | Eif _ _ _ _ (Eop _ _ _ _ (Eop _ _ _ _ (Ekld8 _ _ _ _))) => true | _ => false end = true).
Check (eq_refl : match kbody (compile_f gid1 1 bfill_g bfill_b) with
                 | Eif _ _ _ _ (Eop _ _ _ _ (Eop _ _ _ _ (Eop _ _ _ _ (Ekst8 _ _ _ _)))) => true | _ => false end = true).

(* ---------------------------------------------------------------- records and pairs *)
(* the program's record type 0 is [int * int]: its operations are the pair's own constructor and match, so a field is the
   user's [fst p] / [snd p] by computation; the laws by a dependent match *)
Section RecTest.
#[local] Instance pair_recs : RecTypes | 0 :=
  mkrecs (fun _ => (i63 * i63)%type) (fun _ => mkrops 2 None (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end)) (fun _ => (0%uint63, 0%uint63)).
#[local] Instance pair_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.

(* [pinner] (rec_pair's loop): a pair as the loop's state, its fields read, a pair built and passed to the recursive call;
   [pouter] passes a pair built in place *)
Fixpoint pinner (fuel : nat) (i : i63) (p : i63 * i63) (s : mem) : i63 :=
  match fuel with
  | O => PrimInt63.add (fst p) (snd p)
  | S f => let x := KQ.KQRun.rd 0 i s in
           pinner f (PrimInt63.add i 1) (PrimInt63.add (fst p) x, PrimInt63.land (PrimInt63.add (snd p) x) 255) s
  end.
Definition pouter (n : nat) (a : i63) (s : mem) : i63 := pinner n 0 (0, a) s.
Definition pinner_g := mksig 1 [KNum; KRec 0] true false false None.
Definition pinner_b := FRec (SOp Badd (SFld 0 0) (SFld 0 1))
  (SLet (SRd (SInt 0) (SVar 0)) (SRec CNil (SCons (SOp Badd (SVar 1) (SInt 1))
     (SConsR (RMk 0 (SCons (SOp Badd (SFld 0 0) (SVar 0)) (SCons (SOp Bland (SOp Badd (SFld 0 1) (SVar 0)) (SInt 255)) SNil))) SNil)))).
Definition pouter_g := mksig 1 [KNum] true false false None.
Definition pouter_b := FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SInt 0) (SConsR (RMk 0 (SCons (SInt 0) (SCons (SVar 0) SNil))) SNil))).
Definition pair_P := mkprog [(gid1 0, compile_f gid1 0 pinner_g pinner_b); (gid1 1, compile_f gid1 1 pouter_g pouter_b)] [].
Time Lemma pinner_ok : callee_ok pair_P (gid1 0) (cbz 0) pinner_g pinner.
Proof. Time exact_no_check (compile_f_ok pair_P [] gid1 0 pinner_g pinner_b eq_refl eq_refl (no_callees pair_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma pouter_ok : callee_ok pair_P (gid1 1) (cbz 1) pouter_g pouter.
Proof.
  Time exact_no_check (compile_f_ok pair_P [existT ftype pinner_g pinner] gid1 1 pouter_g pouter_b eq_refl eq_refl
    (all_ok_callees pair_P gid1 [existT ftype pinner_g pinner] (conj pinner_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions pouter_ok.
(* the pair is its fields in KQL: [pinner] takes three parameters (the counter, i, the pair's two fields) *)
Check (eq_refl : length (kparams (compile_f gid1 0 pinner_g pinner_b)) = 4%nat).

(* taking a pair apart, and a pair bound by a let and read through its fields *)
Definition pmatch (i : i63) (p : i63 * i63) : i63 := let '(a, b) := p in PrimInt63.add (PrimInt63.mul a b) i.
Definition plet (x y : i63) : i63 := let w := (x, PrimInt63.add y 1) in PrimInt63.sub (fst w) (snd w).
Definition pmatch_g := mksig 0 [KNum; KRec 0] false false false None.
Definition pmatch_b := FPlain (SMatchR (RVar 0) (SOp Badd (SOp Bmul (SVar 1) (SVar 0)) (SVar 2))).
Definition plet_g := mksig 0 [KNum; KNum] false false false None.
Definition plet_b := FPlain (SLetR (RMk 0 (SCons (SVar 1) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil))) (SOp Bsub (SFld 0 0) (SFld 0 1))).
Definition pm_P := mkprog [(gid1 0, compile_f gid1 0 pmatch_g pmatch_b); (gid1 1, compile_f gid1 1 plet_g plet_b)] [].
Time Lemma pmatch_ok : callee_ok pm_P (gid1 0) (cbz 0) pmatch_g pmatch.
Proof. Time exact_no_check (compile_f_ok pm_P [] gid1 0 pmatch_g pmatch_b eq_refl eq_refl (no_callees pm_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma plet_ok : callee_ok pm_P (gid1 1) (cbz 1) plet_g plet.
Proof. Time exact_no_check (compile_f_ok pm_P [] gid1 1 plet_g plet_b eq_refl eq_refl (no_callees pm_P gid1) eq_refl eq_refl). Time Qed.
(* a record variable passed as it is (step 16): [ppass] gives its pair to [pinner] *)
Definition ppass (n : nat) (p : i63 * i63) (s : mem) : i63 := pinner n 0 p s.
Definition ppass_g := mksig 1 [KRec 0] true false false None.
Definition ppass_b := FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SInt 0) (SConsR (RVar 0) SNil))).
Definition ppass_P := mkprog [(gid1 0, compile_f gid1 0 pinner_g pinner_b); (gid1 1, compile_f gid1 1 ppass_g ppass_b)] [].
Time Lemma pinner_ok2 : callee_ok ppass_P (gid1 0) (cbz 0) pinner_g pinner.
Proof. Time exact_no_check (compile_f_ok ppass_P [] gid1 0 pinner_g pinner_b eq_refl eq_refl (no_callees ppass_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma ppass_ok : callee_ok ppass_P (gid1 1) (cbz 1) ppass_g ppass.
Proof.
  Time exact_no_check (compile_f_ok ppass_P [existT ftype pinner_g pinner] gid1 1 ppass_g ppass_b eq_refl eq_refl
    (all_ok_callees ppass_P gid1 [existT ftype pinner_g pinner] (conj pinner_ok2 Logic.I)) eq_refl eq_refl).
Time Qed.
(* a record variable out of scope is refused by well-formedness *)
Check (eq_refl : wf_f [pinner_g] (mksig 1 [KRec 0] true false false None)
                   (FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SInt 0) (SConsR (RVar 1) SNil)))) = false).

(* ---- records given back (step 12, part 3).  [minmax] (pair_ret's loop): a pair at the end, the loop's last call giving it
   back; [fibp]: the function itself taken apart before the end; [prounds]: a loop taking both apart, a counter written as a
   budget; [plast]: a pair bound by a let and read through its fields, the fields given to a second call *)
Fixpoint minmax (n : nat) (i lo hi : i63) (s : mem) : i63 * i63 :=
  match n with
  | O => (lo, hi)
  | S m => let x := KQ.KQRun.rd 0 i s in
           minmax m (PrimInt63.add i 1) (if PrimInt63.ltb x lo then x else lo) (if PrimInt63.ltb hi x then x else hi) s
  end.
Fixpoint fibp (n : nat) : i63 * i63 :=
  match n with
  | O => (0, 1)
  | S m => let '(a, b) := fibp m in (b, PrimInt63.land (PrimInt63.add a b) 1048575)
  end.
Fixpoint prounds (r n : nat) (acc : i63) (s : mem) : i63 :=
  match r with
  | O => acc
  | S r' => let '(lo, hi) := minmax n (PrimInt63.land acc 255) 100000 (PrimInt63.sub 0 1) s in
            let '(fa, fb) := fibp (KQ.KQRun.kq_nat 30) in
            prounds r' n (PrimInt63.add (PrimInt63.add (PrimInt63.sub (PrimInt63.add acc hi) lo) fa) fb) s
  end.
Definition plast (n : nat) (a : i63) (s : mem) : i63 :=
  let w := minmax n a 100000 (PrimInt63.sub 0 1) s in
  let v := minmax n (snd w) (fst w) (snd w) s in
  PrimInt63.add (fst v) (snd v).
Definition minmax_g := mksig 1 [KNum; KNum; KNum] true false false (Some (KRec 0)).
Definition minmax_b := FRecR (BRet (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))))
  (BLet (SRd (SInt 0) (SVar 2)) (BRec CNil (SCons (SOp Badd (SVar 3) (SInt 1))
     (SCons (SIf Clt (SVar 0) (SVar 2) (SVar 0) (SVar 2)) (SCons (SIf Clt (SVar 1) (SVar 0) (SVar 0) (SVar 1)) SNil))))).
Definition fibp_g := mksig 1 [] false false false (Some (KRec 0)).
Definition fibp_b := FRecR (BRet (RMk 0 (SCons (SInt 0) (SCons (SInt 1) SNil))))
  (BMatchRec CNil SNil (BRet (RMk 0 (SCons (SVar 0) (SCons (SOp Bland (SOp Badd (SVar 1) (SVar 0)) (SInt 1048575)) SNil))))).
Definition prounds_g := mksig 2 [KNum] true false false None.
Definition prounds_b := FRec (SVar 0)
  (SMatchR (RCall 0 0 (CCons (CVar 1) CNil) (SCons (SOp Bland (SVar 0) (SInt 255)) (SCons (SInt 100000) (SCons (SOp Bsub (SInt 0) (SInt 1)) SNil))))
     (SMatchR (RCall 0 1 (CCons (CNat (SInt 30)) CNil) SNil)
        (SRec (CCons (CVar 1) CNil) (SCons (SOp Badd (SOp Badd (SOp Bsub (SOp Badd (SVar 4) (SVar 2)) (SVar 3)) (SVar 1)) (SVar 0)) SNil)))).
Definition plast_g := mksig 1 [KNum] true false false None.
Definition plast_b := FPlain (SLetR (RCall 0 0 (CCons (CVar 0) CNil) (SCons (SVar 0) (SCons (SInt 100000) (SCons (SOp Bsub (SInt 0) (SInt 1)) SNil))))
  (SLetR (RCall 0 0 (CCons (CVar 0) CNil) (SCons (SFld 0 1) (SCons (SFld 0 0) (SCons (SFld 0 1) SNil)))) (SOp Badd (SFld 0 0) (SFld 0 1)))).
Definition rret_P := mkprog [(gid1 0, compile_f gid1 0 minmax_g minmax_b); (gid1 1, compile_f gid1 1 fibp_g fibp_b);
                             (gid1 2, compile_f gid1 2 prounds_g prounds_b); (gid1 3, compile_f gid1 3 plast_g plast_b)] [].
Time Lemma minmax_ok : callee_ok rret_P (gid1 0) (cbz 0) minmax_g minmax.
Proof. Time exact_no_check (compile_f_ok rret_P [] gid1 0 minmax_g minmax_b eq_refl eq_refl (no_callees rret_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma fibp_ok : callee_ok rret_P (gid1 1) (cbz 1) fibp_g fibp.
Proof.
  Time exact_no_check (compile_f_ok rret_P [existT ftype minmax_g minmax] gid1 1 fibp_g fibp_b eq_refl eq_refl
    (all_ok_callees rret_P gid1 [existT ftype minmax_g minmax] (conj minmax_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma prounds_ok : callee_ok rret_P (gid1 2) (cbz 2) prounds_g prounds.
Proof.
  Time exact_no_check (compile_f_ok rret_P [existT ftype minmax_g minmax; existT ftype fibp_g fibp] gid1 2 prounds_g prounds_b eq_refl eq_refl
    (all_ok_callees rret_P gid1 [existT ftype minmax_g minmax; existT ftype fibp_g fibp] (conj minmax_ok (conj fibp_ok Logic.I))) eq_refl eq_refl).
Time Qed.
Time Lemma plast_ok : callee_ok rret_P (gid1 3) (cbz 3) plast_g plast.
Proof.
  Time exact_no_check (compile_f_ok rret_P [existT ftype minmax_g minmax; existT ftype fibp_g fibp; existT ftype prounds_g prounds] gid1 3 plast_g plast_b
    eq_refl eq_refl (all_ok_callees rret_P gid1 [existT ftype minmax_g minmax; existT ftype fibp_g fibp; existT ftype prounds_g prounds]
                       (conj minmax_ok (conj fibp_ok (conj prounds_ok Logic.I)))) eq_refl eq_refl).
Time Qed.
Print Assumptions plast_ok.
(* the code: [minmax]'s end writes the second field into the slot block and returns the first; [fibp] calls itself *)
Check (eq_refl : match kbody (compile_f gid1 0 minmax_g minmax_b) with Eif _ _ _ (Ekst _ _ _ (Eret _)) _ => true | _ => false end = true).
Check (eq_refl : match kbody (compile_f gid1 1 fibp_g fibp_b) with Eif _ _ _ _ (Eop _ _ _ _ (Ekld _ _ _ (Ecall _ _ _ _))) => true | _ => false end = true).
(* a record variable passed on and given back as it is (step 16): [pswap] passes its pair to the recursive call as it is,
   or swapped, and gives it back as it is at the end *)
Fixpoint pswap (n : nat) (p : i63 * i63) : i63 * i63 :=
  match n with
  | O => p
  | S m => if PrimInt63.ltb (fst p) (snd p) then pswap m p else pswap m (snd p, fst p)
  end.
Definition pswap_g := mksig 1 [KRec 0] false false false (Some (KRec 0)).
Definition pswap_b := FRecR (BRet (RVar 0))
  (BIf Clt (SFld 0 0) (SFld 0 1) (BRec CNil (SConsR (RVar 0) SNil)) (BRec CNil (SConsR (RMk 0 (SCons (SFld 0 1) (SCons (SFld 0 0) SNil))) SNil))).
Definition pswap_P := mkprog [(gid1 0, compile_f gid1 0 pswap_g pswap_b)] [].
Time Lemma pswap_ok : callee_ok pswap_P (gid1 0) (cbz 0) pswap_g pswap.
Proof. Time exact_no_check (compile_f_ok pswap_P [] gid1 0 pswap_g pswap_b eq_refl eq_refl (no_callees pswap_P gid1) eq_refl eq_refl). Time Qed.
Print Assumptions pswap_ok.
(* a record variable out of scope given back is refused by well-formedness *)
Check (eq_refl : wf_f [] (mksig 0 [KRec 0] false false false (Some (KRec 0))) (FPlainR (BRet (RVar 1))) = false).
(* a tree whose record has the fields the other way round is refused by the check *)
Fail Check (eq_refl : minmax = denote_f [] minmax_g (FRecR (BRet (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil)))) (BLet (SRd (SInt 0) (SVar 2)) (BRec CNil (SCons (SOp Badd (SVar 3) (SInt 1))
     (SCons (SIf Clt (SVar 0) (SVar 2) (SVar 0) (SVar 2)) (SCons (SIf Clt (SVar 1) (SVar 0) (SVar 0) (SVar 1)) SNil))))))).
(* a record chosen by a test, and a record built from a record taken apart (step 21) *)
Definition pchoose (a b : i63) : i63 :=
  let '(p, q) := (if PrimInt63.ltb a b then (a, b) else (b, a)) in PrimInt63.sub q p.
Definition pswap2 (a b : i63) : i63 :=
  let '(p, q) := (let '(x, y) := (PrimInt63.add a b, a) in (y, x)) in PrimInt63.sub p q.
Definition prif_g := mksig 0 [KNum; KNum] false false false None.
Definition pchoose_b := FPlain (SMatchR (RIf 0 Clt (SVar 1) (SVar 0) (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil)))
                                                 (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil)))) (SOp Bsub (SVar 0) (SVar 1))).
Definition pswap2_b := FPlain (SMatchR (RMatchR 0 (RMk 0 (SCons (SOp Badd (SVar 1) (SVar 0)) (SCons (SVar 1) SNil)))
                                                (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil)))) (SOp Bsub (SVar 1) (SVar 0))).
Definition prif_P := mkprog [(gid1 0, compile_f gid1 0 prif_g pchoose_b); (gid1 1, compile_f gid1 1 prif_g pswap2_b)] [].
Time Lemma pchoose_ok : callee_ok prif_P (gid1 0) (cbz 0) prif_g pchoose.
Proof. Time exact_no_check (compile_f_ok prif_P [] gid1 0 prif_g pchoose_b eq_refl eq_refl (no_callees prif_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma pswap2_ok : callee_ok prif_P (gid1 1) (cbz 1) prif_g pswap2.
Proof. Time exact_no_check (compile_f_ok prif_P [] gid1 1 prif_g pswap2_b eq_refl eq_refl (no_callees prif_P gid1) eq_refl eq_refl). Time Qed.
(* records of two types in the branches are refused *)
Check (eq_refl : wf_f [] prif_g (FPlain (SMatchR (RIf 0 Clt (SVar 1) (SVar 0) (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil)))
                                                  (RMk 1 (SCons (SVar 0) (SCons (SVar 1) SNil)))) (SVar 0))) = false).
(* ---- the constructs of the number sort in the boolean and record sorts (step 36): a test on a boolean ([xbif] as a choice,
   [xbifj] as jumps), a number let in a later operand of [&&] ([xblet]), a boolean let ([xbletb], the boolean's value), a counter
   let ([xbletc], its bound pushed), a record taken apart and a record let inside a boolean ([xbmr], [xbletr]); a record chosen by a
   test on a boolean ([xrifb]), a boolean let in a record ([xrletb]), a record chosen by a counter match ([xrmc]), a counter let
   in a record ([xrletc]) *)
Definition x12_g := mksig 1 [KNum; KNum] false false false None.
Definition x61_g := mksig7 1 [KNum; KNum] false false false None (Some 2305843009213693952%Z).
Definition xbif (a b : i63) : i63 :=
  if (if andb (PrimInt63.ltb a b) (PrimInt63.ltb b 10) then PrimInt63.eqb a b else false) then a else b.
Definition xbif_b := FPlain (SIfB (BxIfB (BAnd (BCmp Clt (SVar 1) (SVar 0)) (BCmp Clt (SVar 0) (SInt 10))) (BCmp Ceq (SVar 1) (SVar 0)) BFalse) (SVar 1) (SVar 0)).
Definition xbifj (a b : i63) : i63 :=
  if (if PrimInt63.ltb a b then PrimInt63.eqb a b else PrimInt63.ltb b a) then (let z := PrimInt63.add a 1 in PrimInt63.mul z z) else b.
Definition xbifj_b := FPlain (SIfB (BxIfB (BCmp Clt (SVar 1) (SVar 0)) (BCmp Ceq (SVar 1) (SVar 0)) (BCmp Clt (SVar 0) (SVar 1))) (SLet (SOp Badd (SVar 1) (SInt 1)) (SOp Bmul (SVar 0) (SVar 0))) (SVar 0)).
Definition xblet (a b : i63) : i63 :=
  if andb (PrimInt63.ltb a b) (let c := PrimInt63.add a 1 in PrimInt63.ltb c 10) then a else b.
Definition xblet_b := FPlain (SIfB (BAnd (BCmp Clt (SVar 1) (SVar 0)) (BxLet (SOp Badd (SVar 1) (SInt 1)) (BCmp Clt (SVar 0) (SInt 10)))) (SVar 1) (SVar 0)).
Definition xbletb (a b : i63) : i63 :=
  let d := (let c := PrimInt63.ltb a b in andb c (PrimInt63.ltb b 10)) in if d then a else b.
Definition xbletb_b := FPlain (SLetB (BxLetB (BCmp Clt (SVar 1) (SVar 0)) (BAnd (BVar 0) (BCmp Clt (SVar 0) (SInt 10)))) (SIfB (BVar 0) (SVar 1) (SVar 0))).
Definition xbletc (n : nat) (a b : i63) : i63 :=
  if (let w := (n + n)%nat in Nat.eqb w 4) then (let z := PrimInt63.add a 1 in PrimInt63.mul z z) else b.
Definition xbletc_b := FPlain (SIfB (BxLetC (CAdd (CVar 0) (CVar 0)) (BCmpC Ceq (CVar 0) (CS (CS (CS (CS CO)))))) (SLet (SOp Badd (SVar 1) (SInt 1)) (SOp Bmul (SVar 0) (SVar 0))) (SVar 0)).
Definition xbmr (a b : i63) : i63 :=
  if (let '(x, y) := (PrimInt63.add a 1, b) in PrimInt63.ltb x y) then a else b.
Definition xbmr_b := FPlain (SIfB (BxMatchR (RMk 0 (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SVar 0) SNil))) (BCmp Clt (SVar 1) (SVar 0))) (SVar 1) (SVar 0)).
Definition xbletr (a b : i63) : i63 :=
  let d := (let p := (a, b) in PrimInt63.ltb (fst p) (snd p)) in if d then a else b.
Definition xbletr_b := FPlain (SLetB (BxLetR (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (BCmp Clt (SFld 0 0) (SFld 0 1))) (SIfB (BVar 0) (SVar 1) (SVar 0))).
Definition xrifb (a b : i63) : i63 :=
  let '(p, q) := (if andb (PrimInt63.ltb a b) (PrimInt63.ltb b 10) then (a, b) else (b, a)) in PrimInt63.sub q p.
Definition xrifb_b := FPlain (SMatchR (RIfB 0 (BAnd (BCmp Clt (SVar 1) (SVar 0)) (BCmp Clt (SVar 0) (SInt 10))) (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil)))) (SOp Bsub (SVar 0) (SVar 1))).
Definition xrletb (a b : i63) : i63 :=
  let '(p, q) := (let c := PrimInt63.ltb a b in if c then (a, b) else (b, a)) in PrimInt63.sub q p.
Definition xrletb_b := FPlain (SMatchR (RLetB (BCmp Clt (SVar 1) (SVar 0)) (RIfB 0 (BVar 0) (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil))))) (SOp Bsub (SVar 0) (SVar 1))).
Definition xrmc (n : nat) (a b : i63) : i63 :=
  let '(p, q) := (match n with O => (a, b) | S _ => (b, a) end) in PrimInt63.sub q p.
Definition xrmc_b := FPlain (SMatchR (RMatchCnt 0 0 (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil)))) (SOp Bsub (SVar 0) (SVar 1))).
Definition xrletc (n : nat) (a b : i63) : i63 :=
  let '(p, q) := (let w := S n in match w with O => (a, b) | S _ => (b, a) end) in PrimInt63.sub q p.
Definition xrletc_b := FPlain (SMatchR (RLetC (CS (CVar 0)) (RMatchCnt 0 0 (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil))))) (SOp Bsub (SVar 0) (SVar 1))).
Definition x36_P := mkprog [(gid1 0, compile_f gid1 0 prif_g xbif_b); (gid1 1, compile_f gid1 1 prif_g xbifj_b); (gid1 2, compile_f gid1 2 prif_g xblet_b); (gid1 3, compile_f gid1 3 prif_g xbletb_b); (gid1 4, compile_f gid1 4 x61_g xbletc_b); (gid1 5, compile_f gid1 5 prif_g xbmr_b); (gid1 6, compile_f gid1 6 prif_g xbletr_b); (gid1 7, compile_f gid1 7 prif_g xrifb_b); (gid1 8, compile_f gid1 8 prif_g xrletb_b); (gid1 9, compile_f gid1 9 x12_g xrmc_b); (gid1 10, compile_f gid1 10 x61_g xrletc_b)] [].
Time Lemma xbif_ok : callee_ok x36_P (gid1 0) (cbz 0) prif_g xbif.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 0 prif_g xbif_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xbifj_ok : callee_ok x36_P (gid1 1) (cbz 1) prif_g xbifj.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 1 prif_g xbifj_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xblet_ok : callee_ok x36_P (gid1 2) (cbz 2) prif_g xblet.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 2 prif_g xblet_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xbletb_ok : callee_ok x36_P (gid1 3) (cbz 3) prif_g xbletb.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 3 prif_g xbletb_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xbletc_ok : callee_ok x36_P (gid1 4) 2305843009213693952%Z x61_g xbletc.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 4 x61_g xbletc_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xbmr_ok : callee_ok x36_P (gid1 5) (cbz 5) prif_g xbmr.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 5 prif_g xbmr_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xbletr_ok : callee_ok x36_P (gid1 6) (cbz 6) prif_g xbletr.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 6 prif_g xbletr_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xrifb_ok : callee_ok x36_P (gid1 7) (cbz 7) prif_g xrifb.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 7 prif_g xrifb_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xrletb_ok : callee_ok x36_P (gid1 8) (cbz 8) prif_g xrletb.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 8 prif_g xrletb_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xrmc_ok : callee_ok x36_P (gid1 9) (cbz 9) x12_g xrmc.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 9 x12_g xrmc_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma xrletc_ok : callee_ok x36_P (gid1 10) 2305843009213693952%Z x61_g xrletc.
Proof. Time exact_no_check (compile_f_ok x36_P [] gid1 10 x61_g xrletc_b eq_refl eq_refl (no_callees x36_P gid1) eq_refl eq_refl). Time Qed.
Print Assumptions xrletc_ok.
(* refused: records of two types in a test on a boolean, a counter let at the index's bound whose own bound has no room, the
   tree of a test with its branches the other way round *)
Check (eq_refl : wf_f [] prif_g (FPlain (SMatchR (RIfB 0 BTrue (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RMk 1 (SCons (SVar 0) (SCons (SVar 1) SNil)))) (SVar 0))) = false).
Check (eq_refl : wf_f [] x12_g xbletc_b = false).
Time Fail Definition xbif_wrong : xbif = denote_f [] prif_g
  (FPlain (SIfB (BxIfB (BAnd (BCmp Clt (SVar 1) (SVar 0)) (BCmp Clt (SVar 0) (SInt 10))) BFalse (BCmp Ceq (SVar 1) (SVar 0))) (SVar 1) (SVar 0))) := eq_refl.
End RecTest.

(* ---- u64 (step 16): KQRun's u64 a record type of the program, [w64_op] one KQL instruction ([Ew64]); [uadd] an operation
   given back; [ultb] a comparison as a test (u64_ltb); [ufold] (views' fold_words) a loop over a u64 passed on and given
   back as it is, operations on it; [uput] (view_upd64) a u64 bound by a let in a memory, its halves written; [uwr] a number
   made after a memory, a u64 bound by a let and one taken apart; [ulets] lets inside the operands (a helper giving a record,
   written out with its arguments bound) *)
Section U64Test.
#[local] Instance u64_recs : RecTypes | 0 :=
  mkrecs (fun _ => KQ.KQRun.u64) (fun _ => mkrops 2 None (fun l => KQ.KQRun.mk_u64 (nth 0 l 0%uint63) (nth 1 l 0%uint63))
                     (fun P v k => match v with KQ.KQRun.mk_u64 a b => k [a; b] end)) (fun _ => KQ.KQRun.mk_u64 0%uint63 0%uint63).
#[local] Instance u64_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.

Definition uadd (a b : KQ.KQRun.u64) : KQ.KQRun.u64 := KQ.KQRun.u64_add a b.
Definition ultb (a b : KQ.KQRun.u64) : i63 := if KQ.KQRun.u64_ltb a b then 1 else 0.
Fixpoint ufold (f : nat) (i n : i63) (a : KQ.KQRun.u64) (s : mem) : KQ.KQRun.u64 :=
  match f with
  | O => a
  | S f => if PrimInt63.leb n i then a
           else ufold f (PrimInt63.add i 1) n
                  (KQ.KQRun.u64_xor (KQ.KQRun.u64_add a (KQ.KQRun.mk_u64 (KQ.KQRun.rd 0 i s) 0)) (KQ.KQRun.u64_shl a 1)) s
  end.
Definition uput (i : i63) (a : KQ.KQRun.u64) (s : mem) : mem :=
  let v := KQ.KQRun.u64_mul a a in KQ.KQRun.upd 0 (PrimInt63.add i 1) (KQ.KQRun.w_hi v) (KQ.KQRun.upd 0 i (KQ.KQRun.w_lo v) s).
Definition uwr (a : KQ.KQRun.u64) (s : mem) : i63 :=
  let s2 := KQ.KQRun.upd 0 0 (KQ.KQRun.w_lo a) s in
  let w := KQ.KQRun.u64_add a a in
  let '(KQ.KQRun.mk_u64 lo hi) := KQ.KQRun.u64_mul w a in
  PrimInt63.add (PrimInt63.add (KQ.KQRun.rd 0 0 s2) (KQ.KQRun.w_hi w)) (PrimInt63.sub lo hi).

Definition ulets (i : i63) (a : KQ.KQRun.u64) : KQ.KQRun.u64 :=
  KQ.KQRun.u64_xor (let n := PrimInt63.land i 255 in KQ.KQRun.mk_u64 n 0) (let w := KQ.KQRun.u64_mul a a in KQ.KQRun.u64_add w a).

Definition uadd_g := mksig 0 [KRec 0; KRec 0] false false false (Some (KRec 0)).
Definition uadd_b := FPlainR (BRet (RW64 0 KQ.KQRun.W_add (RVar 1) (RVar 0))).
Definition ultb_g := mksig 0 [KRec 0; KRec 0] false false false None.
Definition ultb_b := FPlain (SIf Ceq (SMatchR (RW64 0 KQ.KQRun.W_ltu (RVar 1) (RVar 0)) (SVar 1)) (SInt 1) (SInt 1) (SInt 0)).
Definition ufold_g := mksig 1 [KNum; KNum; KRec 0] true false false (Some (KRec 0)).
Definition ufold_b := FRecR (BRet (RVar 0))
  (BIf Cle (SVar 0) (SVar 1) (BRet (RVar 0))
     (BRec CNil (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SVar 0)
        (SConsR (RW64 0 KQ.KQRun.W_xor (RW64 0 KQ.KQRun.W_add (RVar 0) (RMk 0 (SCons (SRd (SInt 0) (SVar 1)) (SCons (SInt 0) SNil))))
                                       (RW64 0 KQ.KQRun.W_shl (RVar 0) (RMk 0 (SCons (SInt 1) (SCons (SInt 0) SNil))))) SNil))))).
Definition uput_g := mksig 0 [KNum; KRec 0] true true false None.
Definition uput_b := FPlainM (MLetR (RW64 0 KQ.KQRun.W_mul (RVar 0) (RVar 0))
  (MUpd (SInt 0) (SOp Badd (SVar 0) (SInt 1)) (SFld 0 1) (MUpd (SInt 0) (SVar 0) (SFld 0 0) MCur))).
Definition uwr_g := mksig 0 [KRec 0] true false true None.
Definition uwr_b := FPlainX (XLetM (MUpd (SInt 0) (SInt 0) (SFld 0 0) MCur)
  (XLetR (RW64 0 KQ.KQRun.W_add (RVar 0) (RVar 0))
     (XMatchR (RW64 0 KQ.KQRun.W_mul (RVar 0) (RVar 1))
        (XRet (SOp Badd (SOp Badd (SRd (SInt 0) (SInt 0)) (SFld 0 1)) (SOp Bsub (SVar 1) (SVar 0))))))).
Definition ulets_g := mksig 0 [KNum; KRec 0] false false false (Some (KRec 0)).
Definition ulets_b := FPlainR (BRet (RW64 0 KQ.KQRun.W_xor (RLet (SOp Bland (SVar 0) (SInt 255)) (RMk 0 (SCons (SVar 0) (SCons (SInt 0) SNil))))
                                                         (RLetR (RW64 0 KQ.KQRun.W_mul (RVar 0) (RVar 0)) (RW64 0 KQ.KQRun.W_add (RVar 0) (RVar 1))))).
Definition u64_P := mkprog [(gid1 0, compile_f gid1 0 uadd_g uadd_b); (gid1 1, compile_f gid1 1 ultb_g ultb_b);
                            (gid1 2, compile_f gid1 2 ufold_g ufold_b); (gid1 3, compile_f gid1 3 uput_g uput_b);
                            (gid1 4, compile_f gid1 4 uwr_g uwr_b); (gid1 5, compile_f gid1 5 ulets_g ulets_b)] [].
Time Lemma uadd_ok : callee_ok u64_P (gid1 0) (cbz 0) uadd_g uadd.
Proof. Time exact_no_check (compile_f_ok u64_P [] gid1 0 uadd_g uadd_b eq_refl eq_refl (no_callees u64_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma ultb_ok : callee_ok u64_P (gid1 1) (cbz 1) ultb_g ultb.
Proof. Time exact_no_check (compile_f_ok u64_P [] gid1 1 ultb_g ultb_b eq_refl eq_refl (no_callees u64_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma ufold_ok : callee_ok u64_P (gid1 2) (cbz 2) ufold_g ufold.
Proof. Time exact_no_check (compile_f_ok u64_P [] gid1 2 ufold_g ufold_b eq_refl eq_refl (no_callees u64_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma uput_ok : callee_ok u64_P (gid1 3) (cbz 3) uput_g uput.
Proof. Time exact_no_check (compile_f_ok u64_P [] gid1 3 uput_g uput_b eq_refl eq_refl (no_callees u64_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma uwr_ok : callee_ok u64_P (gid1 4) (cbz 4) uwr_g uwr.
Proof. Time exact_no_check (compile_f_ok u64_P [] gid1 4 uwr_g uwr_b eq_refl eq_refl (no_callees u64_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma ulets_ok : callee_ok u64_P (gid1 5) (cbz 5) ulets_g ulets.
Proof. Time exact_no_check (compile_f_ok u64_P [] gid1 5 ulets_g ulets_b eq_refl eq_refl (no_callees u64_P gid1) eq_refl eq_refl). Time Qed.
Print Assumptions ufold_ok.
(* the operation is one instruction: [uadd]'s KQL starts with [Ew64] *)
Check (eq_refl : match kbody (compile_f gid1 0 uadd_g uadd_b) with Ew64 KQ.KQRun.W_add _ _ _ _ _ _ _ => true | _ => false end = true).
(* an operand out of scope is refused *)
Check (eq_refl : wf_f [] (mksig 0 [KRec 0; KRec 0] false false false None)
                   (FPlain (SMatchR (RW64 0 KQ.KQRun.W_add (RVar 2) (RVar 0)) (SVar 0))) = false).
(* a tree with an operation not the text's is refused by the check *)
Fail Check (eq_refl : uadd = denote_f [] uadd_g (FPlainR (BRet (RW64 0 KQ.KQRun.W_sub (RVar 1) (RVar 0))))).
End U64Test.

(* ---- a mutual block (step 17): [mping] and [mpong] (mutual's ping and pong) are one function with a selector counter, a call
   of a member on the predecessor the recursive call given the selector; its meaning [blk] of the user's own functions, its
   theorem compile_f_okr's from its two equations by conversion; each member one call of it *)
Fixpoint mping (n : nat) (a b : i63) (s : mem) : i63 :=
  match n with
  | O => a
  | S m => mpong m (PrimInt63.add a (KQ.KQRun.rd 0 (PrimInt63.land b 1023) s)) (PrimInt63.add b 3) s
  end
with mpong (n : nat) (a b : i63) (s : mem) : i63 :=
  match n with
  | O => PrimInt63.add a b
  | S m => if PrimInt63.eqb (PrimInt63.land a 1) 0 then mping m (PrimInt63.land (PrimInt63.mul a 3) 65535) (PrimInt63.add b 1) s
           else mpong m (PrimInt63.add a 5) (PrimInt63.add b 2) s
  end.
Definition mblk_g := mksig 2 (nk 2) true false false None.
Definition mblk_e0 := SMatch 0 (SVar 1) (SOp Badd (SVar 1) (SVar 0)).
Definition mblk_e1 := SMatch 1
  (SRec (CCons (CNat (SInt 1)) CNil) (SCons (SOp Badd (SVar 1) (SRd (SInt 0) (SOp Bland (SVar 0) (SInt 1023)))) (SCons (SOp Badd (SVar 0) (SInt 3)) SNil)))
  (SIf Ceq (SOp Bland (SVar 1) (SInt 1)) (SInt 0)
     (SRec (CCons (CNat (SInt 0)) CNil) (SCons (SOp Bland (SOp Bmul (SVar 1) (SInt 3)) (SInt 65535)) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)))
     (SRec (CCons (CNat (SInt 1)) CNil) (SCons (SOp Badd (SVar 1) (SInt 5)) (SCons (SOp Badd (SVar 0) (SInt 2)) SNil)))).
Definition mmem_g := mksig 1 (nk 2) true false false None.
Definition mmem_b (j : i63) := FPlain (SCall 0 (CCons (CVar 0) (CCons (CNat (SInt j)) CNil)) (SCons (SVar 1) (SCons (SVar 0) SNil))).
Definition mut_P := mkprog [(gid1 0, compile_f gid1 0 mblk_g (FRec mblk_e0 mblk_e1)); (gid1 1, compile_f gid1 1 mmem_g (mmem_b 0));
                            (gid1 2, compile_f gid1 2 mmem_g (mmem_b 1))] [].
Definition mblk := blk 0 (nk 2) true [mping; mpong].
Time Lemma mblk_ok : callee_ok mut_P (gid1 0) (cbz 0) mblk_g mblk.
Proof.
  Time exact_no_check (compile_f_okr mut_P [] gid1 0 1 (nk 2) true mblk_e0 mblk_e1 None [] mblk eq_refl eq_refl (no_callees mut_P gid1) eq_refl eq_refl
    eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma mping_ok : callee_ok mut_P (gid1 1) (cbz 1) mmem_g mping.
Proof.
  Time exact_no_check (compile_f_ok mut_P [existT ftype mblk_g mblk] gid1 1 mmem_g (mmem_b 0) eq_refl eq_refl
    (all_ok_callees mut_P gid1 [existT ftype mblk_g mblk] (conj mblk_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma mpong_ok : callee_ok mut_P (gid1 2) (cbz 2) mmem_g mpong.
Proof.
  Time exact_no_check (compile_f_ok mut_P [existT ftype mblk_g mblk] gid1 2 mmem_g (mmem_b 1) eq_refl eq_refl
    (all_ok_callees mut_P gid1 [existT ftype mblk_g mblk] (conj mblk_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions mpong_ok.
(* a call between members at the end is a loop: the block function's KQL loops (the test between two calls merged into one) *)
Fixpoint has_loop (e : exp) : bool :=
  match e with
  | Eloop _ => true
  | Eret _ => false
  | Eop _ _ _ _ k | Esel _ _ _ _ _ _ k | Ecall _ _ _ k | Eload _ _ _ k | Ekld _ _ _ k | Ekld32 _ _ _ k | Ekld8 _ _ _ k
  | Eksize _ _ k | Ehwf _ _ _ k | Ew64 _ _ _ _ _ _ _ k | Estore _ _ _ k | Ekst _ _ _ k | Ekst32 _ _ _ k | Ekst8 _ _ _ k | Ehw _ _ k => has_loop k
  | Eif _ _ _ t f => has_loop t || has_loop f
  end.
Check (eq_refl : has_loop (kbody (compile_f gid1 0 mblk_g (FRec mblk_e0 mblk_e1))) = true).

(* ---- blocks shared with another processor (step 18): a plain narrow-block access names an unshared block by a written
   number; atomics, wide blocks and a program sharing nothing are not asked *)
Check (eq_refl : sh_ok [6%uint63] (FPlainM (MUpd32 (SInt 1) (SInt 0) (SRd32 (SInt 1) (SInt 4)) MCur)) = true).
Check (eq_refl : sh_ok [6%uint63] (FPlainM (MUpd32 (SInt 6) (SInt 0) (SInt 1) MCur)) = false).
Check (eq_refl : sh_ok [6%uint63] (FPlain (SRd8 (SVar 0) (SInt 0))) = false).
Check (eq_refl : sh_ok [6%uint63] (FPlainX (XLetM (MHw HAStore (SCons (SInt 4) (SCons (SVar 0) (SCons (SInt 1) SNil))) MCur) (XRet (SRd (SInt 6) (SInt 0))))) = true).
Check (eq_refl : sh_ok [] (FPlain (SRd8 (SVar 0) (SInt 0))) = true).


(* ---- a boolean chosen by a test, or by a match on a counter, where a boolean stands (step 22): as a choice ([bpick],
   simple branches), as a jump ([bjump], a branch with a let), as a value ([bval], bound by a let); the counter's match the
   same ways ([bcnt], [bcntv]) *)
Definition bpick (a b : i63) : i63 := if (if PrimInt63.ltb a b then PrimInt63.ltb a 5 else PrimInt63.ltb b 5) then 1 else 0.
Definition bjump (a b : i63) : i63 :=
  if (if PrimInt63.ltb a b then PrimInt63.ltb a 5 else PrimInt63.ltb b 5) then (let x := PrimInt63.add a 1 in PrimInt63.mul x x) else 0.
Definition bval (a b : i63) : i63 := let c := (if PrimInt63.ltb a b then PrimInt63.ltb a 5 else PrimInt63.ltb b 5) in if c then 1 else 0.
Definition bcnt (n : nat) (a : i63) : i63 := if (match n with O => true | S _ => false end) then (let x := PrimInt63.add a 1 in x) else a.
Definition bcntv (n : nat) (a : i63) : i63 := let c := (match n with O => true | S _ => false end) in if c then a else PrimInt63.add a 1.
Definition btest := BIfCmp Clt (SVar 1) (SVar 0) (BCmp Clt (SVar 1) (SInt 5)) (BCmp Clt (SVar 0) (SInt 5)).
Definition b2_g := mksig 0 (nk 2) false false false None.
Definition b1_g := mksig 1 (nk 1) false false false None.
Definition bpick_b := FPlain (SIfB btest (SInt 1) (SInt 0)).
Definition bjump_b := FPlain (SIfB btest (SLet (SOp Badd (SVar 1) (SInt 1)) (SOp Bmul (SVar 0) (SVar 0))) (SInt 0)).
Definition bval_b := FPlain (SLetB btest (SIfB (BVar 0) (SInt 1) (SInt 0))).
Definition bcnt_b := FPlain (SIfB (BMatchCnt 0 BTrue BFalse) (SLet (SOp Badd (SVar 0) (SInt 1)) (SVar 0)) (SVar 0)).
Definition bcntv_b := FPlain (SLetB (BMatchCnt 0 BTrue BFalse) (SIfB (BVar 0) (SVar 0) (SOp Badd (SVar 0) (SInt 1)))).
Definition bsel_P := mkprog [(gid1 0, compile_f gid1 0 b2_g bpick_b); (gid1 1, compile_f gid1 1 b2_g bjump_b);
                             (gid1 2, compile_f gid1 2 b2_g bval_b); (gid1 3, compile_f gid1 3 b1_g bcnt_b);
                             (gid1 4, compile_f gid1 4 b1_g bcntv_b)] [].
Time Lemma bpick_ok : callee_ok bsel_P (gid1 0) (cbz 0) b2_g bpick.
Proof. Time exact_no_check (compile_f_ok bsel_P [] gid1 0 b2_g bpick_b eq_refl eq_refl (no_callees bsel_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma bjump_ok : callee_ok bsel_P (gid1 1) (cbz 1) b2_g bjump.
Proof. Time exact_no_check (compile_f_ok bsel_P [] gid1 1 b2_g bjump_b eq_refl eq_refl (no_callees bsel_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma bval_ok : callee_ok bsel_P (gid1 2) (cbz 2) b2_g bval.
Proof. Time exact_no_check (compile_f_ok bsel_P [] gid1 2 b2_g bval_b eq_refl eq_refl (no_callees bsel_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma bcnt_ok : callee_ok bsel_P (gid1 3) (cbz 3) b1_g bcnt.
Proof. Time exact_no_check (compile_f_ok bsel_P [] gid1 3 b1_g bcnt_b eq_refl eq_refl (no_callees bsel_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma bcntv_ok : callee_ok bsel_P (gid1 4) (cbz 4) b1_g bcntv.
Proof. Time exact_no_check (compile_f_ok bsel_P [] gid1 4 b1_g bcntv_b eq_refl eq_refl (no_callees bsel_P gid1) eq_refl eq_refl). Time Qed.
Print Assumptions bjump_ok.


(* ---- functions giving back a boolean (step 24): a loop ([qtail], the construct table's P_bool_tail_rec), a search
   ([qsearch]), [&&] and [||] around the recursive call ([qand], [qor]: by the definitions of andb and orb, a test one of
   whose branches is the call), the recursive call's negation ([qneg]); callers testing them by a jump ([qgo]), as a value
   ([qval]) and by a choice of two numbers ([qpick]) *)
Fixpoint qtail (n : nat) (a b : i63) (s : mem) : bool :=
  match n with O => PrimInt63.ltb a b | S m => qtail m (PrimInt63.add a 1) b s end.
Fixpoint qsearch (n : nat) (a b : i63) (s : mem) : bool :=
  match n with O => false | S m => if PrimInt63.eqb (KQ.KQRun.rd 0 a s) b then true else qsearch m (PrimInt63.add a 1) b s end.
Fixpoint qand (n : nat) (a b : i63) (s : mem) : bool :=
  match n with O => true | S m => andb (PrimInt63.ltb a b) (qand m (PrimInt63.add a 1) b s) end.
Fixpoint qor (n : nat) (a b : i63) (s : mem) : bool :=
  match n with O => false | S m => orb (PrimInt63.eqb a b) (qor m (PrimInt63.add a 1) b s) end.
Fixpoint qneg (n : nat) (x : i63) : bool :=
  match n with O => PrimInt63.ltb x 3 | S m => negb (qneg m (PrimInt63.add x 1)) end.
Definition qgo (n : nat) (a b : i63) (s : mem) : i63 := if qand n a b s then (let x := PrimInt63.add a 1 in PrimInt63.mul x x) else 0.
Definition qval (n : nat) (a b : i63) (s : mem) : i63 := let c := qor n a b s in if c then 1 else 0.
Definition qpick (n : nat) (a b : i63) : i63 := if qneg n a then a else b.
Definition qb_g := mksig 1 (nk 2) true false false (Some KBool).
Definition qn_g := mksig 1 (nk 1) false false false (Some KBool).
Definition qc_g := mksig 1 (nk 2) true false false None.
Definition qp_g := mksig 1 (nk 2) false false false None.
Definition qargs := SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SVar 0) SNil).
Definition qtail_b := FRecB (BbRet (BCmp Clt (SVar 1) (SVar 0))) (BbRec CNil qargs).
Definition qsearch_b := FRecB (BbRet BFalse) (BbIf Ceq (SRd (SInt 0) (SVar 1)) (SVar 0) (BbRet BTrue) (BbRec CNil qargs)).
Definition qand_b := FRecB (BbRet BTrue) (BbIf Clt (SVar 1) (SVar 0) (BbRec CNil qargs) (BbRet BFalse)).
Definition qor_b := FRecB (BbRet BFalse) (BbIf Ceq (SVar 1) (SVar 0) (BbRet BTrue) (BbRec CNil qargs)).
Definition qneg_b := FRecB (BbRet (BCmp Clt (SVar 0) (SInt 3))) (BbNotRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition qcall (f : nat) := BCall f (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil)).
Definition qgo_b := FPlain (SIfB (qcall 2) (SLet (SOp Badd (SVar 1) (SInt 1)) (SOp Bmul (SVar 0) (SVar 0))) (SInt 0)).
Definition qval_b := FPlain (SLetB (qcall 3) (SIfB (BVar 0) (SInt 1) (SInt 0))).
Definition qpick_b := FPlain (SIfB (BCall 4 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil)) (SVar 1) (SVar 0)).
Definition q_P := mkprog [(gid1 0, compile_f gid1 0 qb_g qtail_b); (gid1 1, compile_f gid1 1 qb_g qsearch_b);
                          (gid1 2, compile_f gid1 2 qb_g qand_b); (gid1 3, compile_f gid1 3 qb_g qor_b);
                          (gid1 4, compile_f gid1 4 qn_g qneg_b); (gid1 5, compile_f gid1 5 qc_g qgo_b);
                          (gid1 6, compile_f gid1 6 qc_g qval_b); (gid1 7, compile_f gid1 7 qp_g qpick_b)] [].
Time Lemma qtail_ok : callee_ok q_P (gid1 0) (cbz 0) qb_g qtail.
Proof. Time exact_no_check (compile_f_ok q_P [] gid1 0 qb_g qtail_b eq_refl eq_refl (no_callees q_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma qsearch_ok : callee_ok q_P (gid1 1) (cbz 1) qb_g qsearch.
Proof. Time exact_no_check (compile_f_ok q_P [] gid1 1 qb_g qsearch_b eq_refl eq_refl (no_callees q_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma qand_ok : callee_ok q_P (gid1 2) (cbz 2) qb_g qand.
Proof. Time exact_no_check (compile_f_ok q_P [] gid1 2 qb_g qand_b eq_refl eq_refl (no_callees q_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma qor_ok : callee_ok q_P (gid1 3) (cbz 3) qb_g qor.
Proof. Time exact_no_check (compile_f_ok q_P [] gid1 3 qb_g qor_b eq_refl eq_refl (no_callees q_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma qneg_ok : callee_ok q_P (gid1 4) (cbz 4) qn_g qneg.
Proof. Time exact_no_check (compile_f_ok q_P [] gid1 4 qn_g qneg_b eq_refl eq_refl (no_callees q_P gid1) eq_refl eq_refl). Time Qed.
Definition q_cs := [existT ftype qb_g qtail; existT ftype qb_g qsearch; existT ftype qb_g qand; existT ftype qb_g qor;
                    existT ftype qn_g qneg].
Definition q_all := all_ok_callees q_P gid1 q_cs (conj qtail_ok (conj qsearch_ok (conj qand_ok (conj qor_ok (conj qneg_ok Logic.I))))).
Time Lemma qgo_ok : callee_ok q_P (gid1 5) (cbz 5) qc_g qgo.
Proof. Time exact_no_check (compile_f_ok q_P q_cs gid1 5 qc_g qgo_b eq_refl eq_refl q_all eq_refl eq_refl). Time Qed.
Time Lemma qval_ok : callee_ok q_P (gid1 6) (cbz 6) qc_g qval.
Proof. Time exact_no_check (compile_f_ok q_P q_cs gid1 6 qc_g qval_b eq_refl eq_refl q_all eq_refl eq_refl). Time Qed.
Time Lemma qpick_ok : callee_ok q_P (gid1 7) (cbz 7) qp_g qpick.
Proof. Time exact_no_check (compile_f_ok q_P q_cs gid1 7 qp_g qpick_b eq_refl eq_refl q_all eq_refl eq_refl). Time Qed.
Print Assumptions qgo_ok.
(* the KQL: a loop where the call is at the end, a call and [lxor 1] for the negation; the caller's choice a conditional move *)
Check (eq_refl : has_loop (kbody (compile_f gid1 2 qb_g qand_b)) = true).
Check (eq_refl : has_loop (kbody (compile_f gid1 4 qn_g qneg_b)) = false).
(* refused: the recursive call in a plain body; a call of a number function as a boolean; the tree of [||] for [qand] *)
Check (eq_refl : wf_f [] qb_g (FPlainB (BbRec CNil qargs)) = false).
Check (eq_refl : wf_f [qc_g] qc_g (FPlain (SIfB (BCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil))) (SInt 1) (SInt 0))) = false).
Fail Definition qand_wrong : qand = denote_f [] qb_g qor_b := eq_refl.


(* ---- a number and a memory given back (step 26): a loop ([jtail], the construct table's P_intmem_tail_rec), a recursion
   taking its own pair apart ([jnon], P_intmem_nontail), a pair chosen by a test and taken apart where it is made ([jif],
   P_intmem_if with its helper written out), callers taking a call's pair apart by a match ([jgo]) and by a let read through
   [fst] and [snd] ([jlet]) *)
Fixpoint jtail (n : nat) (a b : i63) (s : mem) : (i63 * mem)%type :=
  match n with O => (a, s) | S m => jtail m (PrimInt63.add a 1) b (KQ.KQRun.upd 0 a b s) end.
Fixpoint jnon (n : nat) (a b : i63) (s : mem) : (i63 * mem)%type :=
  match n with O => (a, s) | S m => let '(x, s2) := jnon m a b s in (PrimInt63.add x 1, KQ.KQRun.upd 0 x b s2) end.
Definition jif (n : nat) (a b : i63) (s : mem) : i63 :=
  let '(x, s2) := (if PrimInt63.ltb a b then (a, KQ.KQRun.upd 0 a b s) else (b, s)) in PrimInt63.add x (KQ.KQRun.rd 0 0 s2).
Definition jgo (n : nat) (a b : i63) (s : mem) : i63 := let '(x, s2) := jnon n a b s in PrimInt63.add x (KQ.KQRun.rd 0 0 s2).
Definition jlet (n : nat) (a b : i63) (s : mem) : i63 := let r := jtail n a b s in PrimInt63.add (fst r) (KQ.KQRun.rd 0 0 (snd r)).
Definition jp_g := mksig 1 (nk 2) true false false (Some KNum).
Definition jx_g := mksig 1 (nk 2) true false true None.
Definition jtail_b := FRecP (PvMk (SVar 1) MCur)
  (PvRec CNil (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SVar 0) SNil)) (MUpd (SInt 0) (SVar 1) (SVar 0) MCur)).
Definition jnon_b := FRecP (PvMk (SVar 1) MCur)
  (PvMatchP (PvRec CNil (SCons (SVar 1) (SCons (SVar 0) SNil)) MCur) (PvMk (SOp Badd (SVar 0) (SInt 1)) (MUpd (SInt 0) (SVar 0) (SVar 1) MCur))).
Definition jread := XRet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 0))).
Definition jif_b := FPlainX (XMatchP (PvIf Clt (SVar 1) (SVar 0) (PvMk (SVar 1) (MUpd (SInt 0) (SVar 1) (SVar 0) MCur)) (PvMk (SVar 0) MCur)) jread).
Definition jgo_b := FPlainX (XMatchP (PvCall 1 (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil)) MCur) jread).
Definition jlet_b := FPlainX (XLetP (PvCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil)) MCur) jread).
Definition j_P := mkprog [(gid1 0, compile_f gid1 0 jp_g jtail_b); (gid1 1, compile_f gid1 1 jp_g jnon_b);
                          (gid1 2, compile_f gid1 2 jx_g jif_b); (gid1 3, compile_f gid1 3 jx_g jgo_b);
                          (gid1 4, compile_f gid1 4 jx_g jlet_b)] [].
Time Lemma jtail_ok : callee_ok j_P (gid1 0) (cbz 0) jp_g jtail.
Proof. Time exact_no_check (compile_f_ok j_P [] gid1 0 jp_g jtail_b eq_refl eq_refl (no_callees j_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma jnon_ok : callee_ok j_P (gid1 1) (cbz 1) jp_g jnon.
Proof. Time exact_no_check (compile_f_ok j_P [] gid1 1 jp_g jnon_b eq_refl eq_refl (no_callees j_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma jif_ok : callee_ok j_P (gid1 2) (cbz 2) jx_g jif.
Proof. Time exact_no_check (compile_f_ok j_P [] gid1 2 jx_g jif_b eq_refl eq_refl (no_callees j_P gid1) eq_refl eq_refl). Time Qed.
Definition j_cs := [existT ftype jp_g jtail; existT ftype jp_g jnon].
Definition j_all := all_ok_callees j_P gid1 j_cs (conj jtail_ok (conj jnon_ok Logic.I)).
Time Lemma jgo_ok : callee_ok j_P (gid1 3) (cbz 3) jx_g jgo.
Proof. Time exact_no_check (compile_f_ok j_P j_cs gid1 3 jx_g jgo_b eq_refl eq_refl j_all eq_refl eq_refl). Time Qed.
Time Lemma jlet_ok : callee_ok j_P (gid1 4) (cbz 4) jx_g jlet.
Proof. Time exact_no_check (compile_f_ok j_P j_cs gid1 4 jx_g jlet_b eq_refl eq_refl j_all eq_refl eq_refl). Time Qed.
Print Assumptions jgo_ok.
(* the KQL: the loop's call at the end a loop, the recursion taking its pair apart a call *)
Check (eq_refl : has_loop (kbody (compile_f gid1 0 jp_g jtail_b)) = true).
Check (eq_refl : has_loop (kbody (compile_f gid1 1 jp_g jnon_b)) = false).
(* refused: a function giving back a number and a memory without a memory parameter; a pair taken from a call of a number
   function; the parts of the pair the other way round *)
Check (eq_refl : wf_f [] (mksig 1 (nk 2) false false false (Some KNum)) (FRecP (PvMk (SVar 1) MCur) (PvMk (SVar 1) MCur)) = false).
Check (eq_refl : wf_f [jx_g] jx_g (FPlainX (XMatchP (PvCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil)) MCur) jread)) = false).
Fail Definition jif_wrong : jif = denote_f [] jx_g (FPlainX (XMatchP (PvIf Clt (SVar 1) (SVar 0) (PvMk (SVar 0) MCur) (PvMk (SVar 1) MCur)) jread)) := eq_refl.


(* ---- data types held as their tag and their fields (step 28): option and sum in a program's record table, each value its
   constructor's number then its fields; taken apart by a test of the tag ([dopt], [dsum]: built by a test; [dpar]: a
   parameter), given back by a recursion ([dres], the construct table's A_par_option_rec, and its caller [dgo]), kept as a
   loop's state ([dstate], A_par_option_state) *)
Definition dt_rt (i : nat) : Type := match i with O => option i63 | _ => (i63 + i63)%type end.
Definition dt_ro (i : nat) : rops (dt_rt i) :=
  match i as i0 return rops (dt_rt i0) with
  | O => mkrops 2 (Some [0; 1]%nat) (fun l => if PrimInt63.eqb (nth 0 l 0) 0 then None else Some (nth 1 l 0))
           (fun P v k => match v with None => k [0; 0] | Some x => k [1; x] end)
  | _ => mkrops 2 (Some [1; 1]%nat) (fun l => if PrimInt63.eqb (nth 0 l 0) 0 then inl (nth 1 l 0) else inr (nth 1 l 0))
           (fun P v k => match v with inl x => k [0; x] | inr y => k [1; y] end)
  end.
Definition dt_rd (i : nat) : dt_rt i := match i as i0 return dt_rt i0 with O => None | _ => inl 0 end.
Section D28.
#[local] Instance d_recs : RecTypes | 0 := mkrecs (dt_rt) (dt_ro) (dt_rd).
#[local] Instance d_laws : RecLaws.
Proof. apply laws_of.
- intros [|i] x P k; destruct x; reflexivity.
- intros [|i] x; destruct x; reflexivity.
- intros [|i] l E; discriminate E.
- intros i ws c rest E Lc Lr Hz. destruct i as [|i]; cbn in E; injection E as <-; kq_tag_case.
Qed.
Definition dopt (a : i63) : i63 := match (if PrimInt63.ltb a 7 then None else Some a) with Some x => x | None => 0 end.
Definition dsum (a : i63) : i63 := match (if PrimInt63.ltb a 5 then inl a else inr a) with inl x => x | inr y => PrimInt63.add y 1 end.
Definition dpar (o : option i63) (a : i63) : i63 := match o with Some x => PrimInt63.add x a | None => a end.
Fixpoint dres (n : nat) (x : i63) : option i63 :=
  match n with O => None | S m => if PrimInt63.eqb x 5 then Some x else dres m (PrimInt63.add x 1) end.
Definition dgo (n : nat) (a : i63) : i63 := match dres n a with Some y => y | None => 0 end.
Fixpoint dstate (n : nat) (x : i63) (o : option i63) : i63 :=
  match n with O => match o with Some y => y | None => x end | S m => dstate m (PrimInt63.add x 1) (if PrimInt63.eqb x 3 then Some x else o) end.
Definition dnone := RMk 0 (SCons (SInt 0) (SCons (SInt 0) SNil)).
Definition dsome (e : sexp) := RMk 0 (SCons (SInt 1) (SCons e SNil)).
Definition d1_g := mksig 0 (nk 1) false false false None.
Definition dopt_b := FPlain (SMatchR (RIf 0 Clt (SVar 0) (SInt 7) dnone (dsome (SVar 0))) (SIf Ceq (SVar 1) (SInt 0) (SInt 0) (SVar 0))).
Definition dsum_b := FPlain (SMatchR (RIf 1 Clt (SVar 0) (SInt 5) (RMk 1 (SCons (SInt 0) (SCons (SVar 0) SNil))) (RMk 1 (SCons (SInt 1) (SCons (SVar 0) SNil))))
                              (SIf Ceq (SVar 1) (SInt 0) (SVar 0) (SOp Badd (SVar 0) (SInt 1)))).
Definition dpar_g := mksig 0 [KRec 0; KNum] false false false None.
Definition dpar_b := FPlain (SMatchR (RVar 0) (SIf Ceq (SVar 1) (SInt 0) (SVar 2) (SOp Badd (SVar 0) (SVar 2)))).
Definition dres_g := mksig 1 (nk 1) false false false (Some (KRec 0)).
Definition dres_b := FRecR (BRet dnone) (BIf Ceq (SVar 0) (SInt 5) (BRet (dsome (SVar 0))) (BRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil))).
Definition dgo_g := mksig 1 (nk 1) false false false None.
Definition dgo_b := FPlain (SMatchR (RCall 0 3 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil)) (SIf Ceq (SVar 1) (SInt 0) (SInt 0) (SVar 0))).
Definition dstate_g := mksig 1 [KNum; KRec 0] false false false None.
Definition dstate_b := FRec (SMatchR (RVar 0) (SIf Ceq (SVar 1) (SInt 0) (SVar 2) (SVar 0)))
  (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) (SConsR (RIf 0 Ceq (SVar 0) (SInt 3) (dsome (SVar 0)) (RVar 0)) SNil))).
Definition d_P := mkprog [(gid1 0, compile_f gid1 0 d1_g dopt_b); (gid1 1, compile_f gid1 1 d1_g dsum_b);
                          (gid1 2, compile_f gid1 2 dpar_g dpar_b); (gid1 3, compile_f gid1 3 dres_g dres_b);
                          (gid1 4, compile_f gid1 4 dgo_g dgo_b); (gid1 5, compile_f gid1 5 dstate_g dstate_b)] [].
Time Lemma dopt_ok : callee_ok d_P (gid1 0) (cbz 0) d1_g dopt.
Proof. Time exact_no_check (compile_f_ok d_P [] gid1 0 d1_g dopt_b eq_refl eq_refl (no_callees d_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma dsum_ok : callee_ok d_P (gid1 1) (cbz 1) d1_g dsum.
Proof. Time exact_no_check (compile_f_ok d_P [] gid1 1 d1_g dsum_b eq_refl eq_refl (no_callees d_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma dpar_ok : callee_ok d_P (gid1 2) (cbz 2) dpar_g dpar.
Proof. Time exact_no_check (compile_f_ok d_P [] gid1 2 dpar_g dpar_b eq_refl eq_refl (no_callees d_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma dres_ok : callee_ok d_P (gid1 3) (cbz 3) dres_g dres.
Proof. Time exact_no_check (compile_f_ok d_P [] gid1 3 dres_g dres_b eq_refl eq_refl (no_callees d_P gid1) eq_refl eq_refl). Time Qed.
Definition d_cs := [existT ftype d1_g dopt; existT ftype d1_g dsum; existT ftype dpar_g dpar; existT ftype dres_g dres].
Time Lemma dgo_ok : callee_ok d_P (gid1 4) (cbz 4) dgo_g dgo.
Proof.
  Time exact_no_check (compile_f_ok d_P d_cs gid1 4 dgo_g dgo_b eq_refl eq_refl
    (all_ok_callees d_P gid1 d_cs (conj dopt_ok (conj dsum_ok (conj dpar_ok (conj dres_ok Logic.I))))) eq_refl eq_refl).
Time Qed.
Time Lemma dstate_ok : callee_ok d_P (gid1 5) (cbz 5) dstate_g dstate.
Proof. Time exact_no_check (compile_f_ok d_P [] gid1 5 dstate_g dstate_b eq_refl eq_refl (no_callees d_P gid1) eq_refl eq_refl). Time Qed.
Print Assumptions dgo_ok.
(* refused: a constructor's number not written, a field after the constructor's own not zero, a tag beyond the constructors *)
Check (eq_refl : wf_f [] d1_g (FPlain (SMatchR (RMk 0 (SCons (SVar 0) (SCons (SInt 0) SNil))) (SVar 0))) = false).
Check (eq_refl : wf_f [] d1_g (FPlain (SMatchR (RMk 0 (SCons (SInt 0) (SCons (SVar 0) SNil))) (SVar 0))) = false).
Check (eq_refl : wf_f [] d1_g (FPlain (SMatchR (RMk 0 (SCons (SInt 2) (SCons (SVar 0) SNil))) (SVar 0))) = false).
End D28.


(* ---- comparisons of counters and the predecessor (step 30): [Nat.eqb] / [Nat.ltb] of a counter and a written one chosen
   by a conditional move ([nceq], [nclt]: the construct table's A_par_nat_eqb, A_par_nat_ltb), [Nat.leb] of two counters as a
   jump ([ncle]), a comparison bound by a let ([ncv]), a comparison in a loop's tail ([nloop]: the two calls merged);
   [Nat.pred] given to a loop ([npgo] over [npk]: A_par_nat_pred) and bound by a let of a counter ([npv]) *)
Definition nceq (n : nat) (a b : i63) : i63 := if Nat.eqb n 3 then a else b.
Definition nclt (n : nat) (a b : i63) : i63 := if Nat.ltb n 10 then a else b.
Definition ncle (n m : nat) (a : i63) : i63 := if Nat.leb n m then (let x := PrimInt63.add a 1 in PrimInt63.mul x x) else a.
Definition ncv (n : nat) (a b : i63) : i63 := let c := Nat.eqb n 3 in if c then a else b.
Fixpoint nloop (n : nat) (a : i63) : i63 :=
  match n with O => a | S m => if Nat.ltb m 5 then nloop m (PrimInt63.add a 1) else nloop m (PrimInt63.add a 2) end.
Fixpoint npk (n : nat) (x : i63) : i63 := match n with O => x | S m => npk m (PrimInt63.add x 1) end.
Definition npgo (n : nat) (a b : i63) : i63 := npk (Nat.pred n) a.
Definition npv (n : nat) (a : i63) : i63 := let w := Nat.pred n in npk w (PrimInt63.add a 1).
Definition c3 := CS (CS (CS CO)).
Definition n12_g := mksig 1 (nk 2) false false false None.
Definition n21_g := mksig 2 (nk 1) false false false None.
Definition n11_g := mksig 1 (nk 1) false false false None.
Definition nceq_b := FPlain (SIfB (BCmpC Ceq (CVar 0) c3) (SVar 1) (SVar 0)).
Definition nclt_b := FPlain (SIfB (BCmpC Clt (CVar 0) (CS (CS (CS (CS (CS (CS (CS c3)))))))) (SVar 1) (SVar 0)).
Definition ncle_b := FPlain (SIfB (BCmpC Cle (CVar 1) (CVar 0)) (SLet (SOp Badd (SVar 0) (SInt 1)) (SOp Bmul (SVar 0) (SVar 0))) (SVar 0)).
Definition ncv_b := FPlain (SLetB (BCmpC Ceq (CVar 0) c3) (SIfB (BVar 0) (SVar 1) (SVar 0))).
Definition nloop_b := FRec (SVar 0) (SIfB (BCmpC Clt (CVar 0) (CS (CS c3))) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil))
                                                                     (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 2)) SNil))).
Definition npk_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition npgo_b := FPlain (SCall 5 (CCons (CPred (CVar 0)) CNil) (SCons (SVar 1) SNil)).
Definition npv_b := FPlain (SLetC (CPred (CVar 0)) (SCall 5 (CCons (CVar 0) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil))).
Definition n_P := mkprog [(gid1 0, compile_f gid1 0 n12_g nceq_b); (gid1 1, compile_f gid1 1 n12_g nclt_b);
                          (gid1 2, compile_f gid1 2 n21_g ncle_b); (gid1 3, compile_f gid1 3 n12_g ncv_b);
                          (gid1 4, compile_f gid1 4 n11_g nloop_b); (gid1 5, compile_f gid1 5 n11_g npk_b);
                          (gid1 6, compile_f gid1 6 n12_g npgo_b); (gid1 7, compile_f gid1 7 n11_g npv_b)] [].
Time Lemma nceq_ok : callee_ok n_P (gid1 0) (cbz 0) n12_g nceq.
Proof. Time exact_no_check (compile_f_ok n_P [] gid1 0 n12_g nceq_b eq_refl eq_refl (no_callees n_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma nclt_ok : callee_ok n_P (gid1 1) (cbz 1) n12_g nclt.
Proof. Time exact_no_check (compile_f_ok n_P [] gid1 1 n12_g nclt_b eq_refl eq_refl (no_callees n_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma ncle_ok : callee_ok n_P (gid1 2) (cbz 2) n21_g ncle.
Proof. Time exact_no_check (compile_f_ok n_P [] gid1 2 n21_g ncle_b eq_refl eq_refl (no_callees n_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma ncv_ok : callee_ok n_P (gid1 3) (cbz 3) n12_g ncv.
Proof. Time exact_no_check (compile_f_ok n_P [] gid1 3 n12_g ncv_b eq_refl eq_refl (no_callees n_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma nloop_ok : callee_ok n_P (gid1 4) (cbz 4) n11_g nloop.
Proof. Time exact_no_check (compile_f_ok n_P [] gid1 4 n11_g nloop_b eq_refl eq_refl (no_callees n_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma npk_ok : callee_ok n_P (gid1 5) (cbz 5) n11_g npk.
Proof. Time exact_no_check (compile_f_ok n_P [] gid1 5 n11_g npk_b eq_refl eq_refl (no_callees n_P gid1) eq_refl eq_refl). Time Qed.
Definition n_cs := [existT ftype n12_g nceq; existT ftype n12_g nclt; existT ftype n21_g ncle; existT ftype n12_g ncv;
                    existT ftype n11_g nloop; existT ftype n11_g npk].
Definition n_cs_ok := conj nceq_ok (conj nclt_ok (conj ncle_ok (conj ncv_ok (conj nloop_ok (conj npk_ok Logic.I))))).
Time Lemma npgo_ok : callee_ok n_P (gid1 6) (cbz 6) n12_g npgo.
Proof. Time exact_no_check (compile_f_ok n_P n_cs gid1 6 n12_g npgo_b eq_refl eq_refl (all_ok_callees n_P gid1 n_cs n_cs_ok) eq_refl eq_refl). Time Qed.
Time Lemma npv_ok : callee_ok n_P (gid1 7) (cbz 7) n11_g npv.
Proof.
  Time exact_no_check (compile_f_ok n_P (n_cs ++ [existT ftype n12_g npgo]) gid1 7 n11_g npv_b eq_refl eq_refl
    (all_ok_callees n_P gid1 (n_cs ++ [existT ftype n12_g npgo]) (conj nceq_ok (conj nclt_ok (conj ncle_ok (conj ncv_ok
      (conj nloop_ok (conj npk_ok (conj npgo_ok Logic.I)))))))) eq_refl eq_refl).
Time Qed.
Print Assumptions npv_ok.
Print Assumptions nceq_ok.
(* the KQL: a test at the end of a function is a jump ([nceq], as for a comparison of numbers); a choice inside an expression
   ([nsel]) one conditional move on the comparison, no bit operation; [ncle] a jump *)
Check (eq_refl : shape (kbody (compile_f gid1 0 n12_g nceq_b)) = (0, 0)%nat).
Definition nsel (n : nat) (a b : i63) : i63 := PrimInt63.add (if Nat.eqb n 3 then a else b) 1.
Definition nsel_b := FPlain (SOp Badd (SIfB (BCmpC Ceq (CVar 0) c3) (SVar 1) (SVar 0)) (SInt 1)).
Definition nsel_P := mkprog [(gid1 0, compile_f gid1 0 n12_g nsel_b)] [].
Time Lemma nsel_ok : callee_ok nsel_P (gid1 0) (cbz 0) n12_g nsel.
Proof. Time exact_no_check (compile_f_ok nsel_P [] gid1 0 n12_g nsel_b eq_refl eq_refl (no_callees nsel_P gid1) eq_refl eq_refl). Time Qed.
Check (eq_refl : shape (kbody (compile_f gid1 0 n12_g nsel_b)) = (1, 0)%nat).
Check (eq_refl : has_sel (kbody (compile_f gid1 2 n21_g ncle_b)) = false).
(* refused: a signed comparison of counters, a wrong comparison (the check), the predecessor where the text has none *)
Check (eq_refl : wf_f [] n12_g (FPlain (SIfB (BCmpC Cslt (CVar 0) c3) (SVar 1) (SVar 0))) = false).
Time Fail Definition nceq_wrong : nceq = denote_f [] n12_g (FPlain (SIfB (BCmpC Cle (CVar 0) c3) (SVar 1) (SVar 0))) := eq_refl.
Time Fail Definition npgo_wrong : npgo = denote_f [existT ftype n11_g npk] n12_g
  (FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil))) := eq_refl.


(* ---- a sum of counters given to a callee, and counter bounds per function (step 33): [ka] is proved for counters up to 2^62,
   [kgo] (its own up to 2^61) gives it [n + n] -- A_par_nat_mul's shape; the bounds are the signatures' and are checked *)
Fixpoint ka (n : nat) (x : i63) : i63 := match n with O => x | S m => ka m (PrimInt63.add x 1) end.
Definition kgo (n : nat) (a b : i63) : i63 := ka (n + n) a.
Definition ka_g := mksig7 1 (nk 1) false false false None (Some 4611686018427387904%Z).
Definition kgo_g := mksig7 1 (nk 2) false false false None (Some 2305843009213693952%Z).
Definition ka_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition kgo_b := FPlain (SCall 0 (CCons (CAdd (CVar 0) (CVar 0)) CNil) (SCons (SVar 1) SNil)).
Definition ka_P := mkprog [(gid1 0, compile_f gid1 0 ka_g ka_b); (gid1 1, compile_f gid1 1 kgo_g kgo_b)] [].
Time Lemma ka_ok : callee_ok ka_P (gid1 0) 4611686018427387904%Z ka_g ka.
Proof. Time exact_no_check (compile_f_ok ka_P [] gid1 0 ka_g ka_b eq_refl eq_refl (no_callees ka_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma kgo_ok : callee_ok ka_P (gid1 1) 2305843009213693952%Z kgo_g kgo.
Proof.
  Time exact_no_check (compile_f_ok ka_P [existT ftype ka_g ka] gid1 1 kgo_g kgo_b eq_refl eq_refl
    (all_ok_callees ka_P gid1 [existT ftype ka_g ka] (conj ka_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions kgo_ok.
(* its KQL: the sum one addition, then the call *)
Check (eq_refl : match kbody (compile_f gid1 1 kgo_g kgo_b) with Eop _ Badd _ _ (Ecall _ _ _ _) => true | _ => false end = true).
(* refused: the call at the bound of the index (n + n can reach twice it), a sum given to the recursive call, a bound out of its
   range; a sum compared is taken since step 35 (each counter its own bound) *)
Check (eq_refl : wf_f [ka_g] (mksig 1 (nk 2) false false false None) kgo_b = false).
Check (eq_refl : wf_f [] (mksig7 2 (nk 1) false false false None (Some 2305843009213693952%Z))
                       (FRec (SVar 0) (SRec (CCons (CAdd (CVar 1) (CVar 1)) CNil) (SCons (SVar 0) SNil))) = false).
Check (eq_refl : wf_f [] (mksig7 1 (nk 2) false false false None (Some 2305843009213693952%Z))
                       (FPlain (SIfB (BCmpC Ceq (CAdd (CVar 0) (CVar 0)) CO) (SVar 1) (SVar 0))) = true).
Check (eq_refl : wf_f [] (mksig7 1 (nk 1) false false false None (Some 0%Z)) ka_b = false).
(* a small bound (step 40): the function's counters below it -- taken *)
Check (eq_refl : wf_f [] (mksig7 1 (nk 1) false false false None (Some 1000%Z)) ka_b = true).
Time Fail Definition kgo_wrong : kgo = denote_f [existT ftype ka_g ka] kgo_g
  (FPlain (SCall 0 (CCons (CS (CVar 0)) CNil) (SCons (SVar 1) SNil))) := eq_refl.

(* ---- a bound for each counter variable (step 35): a sum bound by a let and given to a callee, a let of a successor, a sum
   compared, a match on a sum -- A_par_nat_let_add, _let_succ, _eqb_add, _match_add's shapes; a let's counter carries its own
   bound ([lbnd]), a match's predecessor the matched variable's *)
Definition klet (n : nat) (a b : i63) : i63 := let w := (n + n)%nat in ka w a.
Definition kls (n : nat) (a b : i63) : i63 := let w := S n in ka w a.
Definition kcmp (n : nat) (a b : i63) : i63 := if Nat.eqb (n + n) 4 then a else b.
Definition kmt (n : nat) (a b : i63) : i63 := match (n + n)%nat with O => a | S p => ka p a end.
Definition k61_g := mksig7 1 (nk 2) false false false None (Some 2305843009213693952%Z).
Definition klet_b := FPlain (SLetC (CAdd (CVar 0) (CVar 0)) (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil))).
Definition kls_b := FPlain (SLetC (CS (CVar 0)) (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil))).
Definition kcmp_b := FPlain (SIfB (BCmpC Ceq (CAdd (CVar 0) (CVar 0)) (CNat (SInt 4))) (SVar 1) (SVar 0)).
Definition kmt_b := FPlain (SLetC (CAdd (CVar 0) (CVar 0)) (SMatch 0 (SVar 1) (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil)))).
Definition k35_P := mkprog [(gid1 0, compile_f gid1 0 ka_g ka_b); (gid1 1, compile_f gid1 1 k61_g klet_b);
                            (gid1 2, compile_f gid1 2 n12_g kls_b); (gid1 3, compile_f gid1 3 n12_g kcmp_b);
                            (gid1 4, compile_f gid1 4 k61_g kmt_b)] [].
Time Lemma k35a_ok : callee_ok k35_P (gid1 0) 4611686018427387904%Z ka_g ka.
Proof. Time exact_no_check (compile_f_ok k35_P [] gid1 0 ka_g ka_b eq_refl eq_refl (no_callees k35_P gid1) eq_refl eq_refl). Time Qed.
Definition k35_cs := [existT ftype ka_g ka].
Time Lemma klet_ok : callee_ok k35_P (gid1 1) 2305843009213693952%Z k61_g klet.
Proof. Time exact_no_check (compile_f_ok k35_P k35_cs gid1 1 k61_g klet_b eq_refl eq_refl (all_ok_callees k35_P gid1 k35_cs (conj k35a_ok Logic.I)) eq_refl eq_refl). Time Qed.
Time Lemma kls_ok : callee_ok k35_P (gid1 2) (cbz 2) n12_g kls.
Proof. Time exact_no_check (compile_f_ok k35_P k35_cs gid1 2 n12_g kls_b eq_refl eq_refl (all_ok_callees k35_P gid1 k35_cs (conj k35a_ok Logic.I)) eq_refl eq_refl). Time Qed.
Time Lemma kcmp_ok : callee_ok k35_P (gid1 3) (cbz 3) n12_g kcmp.
Proof. Time exact_no_check (compile_f_ok k35_P k35_cs gid1 3 n12_g kcmp_b eq_refl eq_refl (all_ok_callees k35_P gid1 k35_cs (conj k35a_ok Logic.I)) eq_refl eq_refl). Time Qed.
Time Lemma kmt_ok : callee_ok k35_P (gid1 4) 2305843009213693952%Z k61_g kmt.
Proof. Time exact_no_check (compile_f_ok k35_P k35_cs gid1 4 k61_g kmt_b eq_refl eq_refl (all_ok_callees k35_P gid1 k35_cs (conj k35a_ok Logic.I)) eq_refl eq_refl). Time Qed.
Print Assumptions kmt_ok.
(* refused: a let of a sum at the index's bound (n + n can reach twice it, beyond a machine number's room), the recursive call given
   a let-bound sum (its counters must stay below the function's bound), a let-bound sum given to a callee whose bound it passes,
   and a tree that is not the text *)
Check (eq_refl : wf_f [ka_g] (mksig 1 (nk 2) false false false None) klet_b = false).
Check (eq_refl : wf_f [] (mksig7 2 (nk 1) false false false None (Some 2305843009213693952%Z))
                       (FRec (SVar 0) (SLetC (CAdd (CVar 1) (CVar 1)) (SRec (CCons (CVar 0) CNil) (SCons (SVar 0) SNil)))) = false).
Check (eq_refl : wf_f [mksig7 1 (nk 1) false false false None (Some 2305843009213693952%Z)] k61_g klet_b = false).
Time Fail Definition klet_wrong : klet = denote_f k35_cs k61_g
  (FPlain (SLetC (CS (CVar 0)) (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil)))) := eq_refl.

(* ---- counters grown by the recursion (step 37): A_par_nat_rec_succ's shape and its kin; the function's weights [sv] (one vector here) bound the
   counters' weighted sum, the recursion keeps it from growing (coefficient by coefficient on the counters' linear bounds) *)
Fixpoint krs (n m : nat) (x : i63) : i63 := match n with O => x | S p => krs p (S m) (PrimInt63.add x 1) end.
Fixpoint krt (n m : nat) (x : i63) : i63 := match n with O => x | S p => krt p (m + 2) (PrimInt63.add x 1) end.
Fixpoint krw (n a b : nat) (x : i63) : i63 := match n with O => x | S p => krw p (S b) a (PrimInt63.add x 1) end.
Fixpoint krl (n m : nat) (x : i63) : i63 := match n with O => x | S p => let q := S m in krl p q (PrimInt63.add x 1) end.
Definition krg (n : nat) (a : i63) : i63 := krs n n a.
Fixpoint krp (n m : nat) (x : i63) : i63 := match n with O => x | S p => krp p (S p) (PrimInt63.add x 1) end.
Definition krs_g := mksig8 2 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[1; 1]]%nat).
Definition krt_g := mksig8 2 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[2; 1]]%nat).
Definition krw_g := mksig8 3 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[1; 1; 1]]%nat).
Definition krl_g := mksig8 2 (nk 1) false false false None (Some 2305843009213693952%Z) (map lpoly [[1; 1]]%nat).
Definition krg_g := mksig7 1 (nk 1) false false false None (Some 2305843009213693952%Z).
Definition krp_g := mksig7 2 (nk 1) false false false None (Some 4611686018427387904%Z).
Definition krs_b := FRec (SVar 0) (SRec (CCons (CS (CVar 1)) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition krt_b := FRec (SVar 0) (SRec (CCons (CAdd (CVar 1) (CS (CS CO))) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition krw_b := FRec (SVar 0) (SRec (CCons (CS (CVar 1)) (CCons (CVar 2) CNil)) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition krl_b := FRec (SVar 0) (SLetC (CS (CVar 1)) (SRec (CCons (CVar 0) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil))).
Definition krg_b := FPlain (SCall 0 (CCons (CVar 0) (CCons (CVar 0) CNil)) (SCons (SVar 0) SNil)).
Definition krp_b := FRec (SVar 0) (SRec (CCons (CS (CVar 0)) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition k37_P := mkprog [(gid1 0, compile_f gid1 0 krs_g krs_b); (gid1 1, compile_f gid1 1 krt_g krt_b);
                            (gid1 2, compile_f gid1 2 krw_g krw_b); (gid1 3, compile_f gid1 3 krl_g krl_b);
                            (gid1 4, compile_f gid1 4 krg_g krg_b); (gid1 5, compile_f gid1 5 krp_g krp_b)] [].
Time Lemma krs_ok : callee_ok k37_P (gid1 0) 4611686018427387904%Z krs_g krs.
Proof. Time exact_no_check (compile_f_ok k37_P [] gid1 0 krs_g krs_b eq_refl eq_refl (no_callees k37_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma krt_ok : callee_ok k37_P (gid1 1) 4611686018427387904%Z krt_g krt.
Proof. Time exact_no_check (compile_f_ok k37_P [] gid1 1 krt_g krt_b eq_refl eq_refl (no_callees k37_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma krw_ok : callee_ok k37_P (gid1 2) 4611686018427387904%Z krw_g krw.
Proof. Time exact_no_check (compile_f_ok k37_P [] gid1 2 krw_g krw_b eq_refl eq_refl (no_callees k37_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma krl_ok : callee_ok k37_P (gid1 3) 2305843009213693952%Z krl_g krl.
Proof. Time exact_no_check (compile_f_ok k37_P [] gid1 3 krl_g krl_b eq_refl eq_refl (no_callees k37_P gid1) eq_refl eq_refl). Time Qed.
Definition k37_cs := [existT ftype krs_g krs].
Time Lemma krg_ok : callee_ok k37_P (gid1 4) 2305843009213693952%Z krg_g krg.
Proof. Time exact_no_check (compile_f_ok k37_P k37_cs gid1 4 krg_g krg_b eq_refl eq_refl (all_ok_callees k37_P gid1 k37_cs (conj krs_ok Logic.I)) eq_refl eq_refl). Time Qed.
(* without weights: the recursion given the successor of the predecessor, at most the first counter (its linear bound) *)
Time Lemma krp_ok : callee_ok k37_P (gid1 5) 4611686018427387904%Z krp_g krp.
Proof. Time exact_no_check (compile_f_ok k37_P [] gid1 5 krp_g krp_b eq_refl eq_refl (no_callees k37_P gid1) eq_refl eq_refl). Time Qed.
Print Assumptions krs_ok.
(* refused: the growth without weights (each counter below the bound cannot hold S m), weights too small for m + 2, a zero weight,
   a counter grown by the predecessor (k p (m + p) grows quadratically: no weights of degree 1 bound it), a call
   whose weighted sum passes the callee's bound, the predecessor's second successor (above the first counter), and a tree that is
   not the text *)
Check (eq_refl : wf_f [] (mksig7 2 (nk 1) false false false None (Some 4611686018427387904%Z)) krs_b = false).
Check (eq_refl : wf_f [] (mksig8 2 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[1; 1]]%nat)) krt_b = false).
Check (eq_refl : wf_f [] (mksig8 2 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[0; 1]]%nat)) krs_b = false).
(* (step 39) a weight for a counter the function does not have multiplies 0 on both sides: taken *)
Check (eq_refl : wf_f [] (mksig8 2 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[1; 1; 1]]%nat)) krs_b = true).
Check (eq_refl : wf_f [] (mksig8 2 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[1; 1]]%nat))
                       (FRec (SVar 0) (SRec (CCons (CAdd (CVar 1) (CVar 0)) CNil) (SCons (SVar 0) SNil))) = false).
Check (eq_refl : wf_f [] (mksig8 2 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[5; 1]]%nat))
                       (FRec (SVar 0) (SRec (CCons (CAdd (CVar 1) (CVar 0)) CNil) (SCons (SVar 0) SNil))) = false).
Check (eq_refl : wf_f [krs_g] (mksig7 1 (nk 1) false false false None (Some 4611686018427387904%Z)) krg_b = false).
Check (eq_refl : wf_f [] krp_g (FRec (SVar 0) (SRec (CCons (CS (CS (CVar 0))) CNil) (SCons (SVar 0) SNil))) = false).
Time Fail Definition krs_wrong : krs = denote_f [] krs_g
  (FRec (SVar 0) (SRec (CCons (CVar 1) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil))) := eq_refl.

(* ---- counters grown apart (step 38): several weighted sums, every counter with a weight of at least 1 in one; given n n n by a
   caller at the smallest bound's value, each sum fits where one weighted sum of the three would not *)
Fixpoint krd (n c d : nat) (x : i63) : i63 := match n with O => x | S p => krd p (S c) (S d) (PrimInt63.add x 1) end.
Definition krdg (n : nat) (a : i63) : i63 := krd n n n a.
Definition krd_g := mksig8 3 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[1; 1; 0]; [1; 0; 1]]%nat).
Definition krdg_g := mksig7 1 (nk 1) false false false None (Some 2305843009213693952%Z).
Definition krd_b := FRec (SVar 0) (SRec (CCons (CS (CVar 2)) (CCons (CS (CVar 1)) CNil)) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition krdg_b := FPlain (SCall 0 (CCons (CVar 0) (CCons (CVar 0) (CCons (CVar 0) CNil))) (SCons (SVar 0) SNil)).
Definition k38_P := mkprog [(gid1 0, compile_f gid1 0 krd_g krd_b); (gid1 1, compile_f gid1 1 krdg_g krdg_b)] [].
Time Lemma krd_ok : callee_ok k38_P (gid1 0) 4611686018427387904%Z krd_g krd.
Proof. Time exact_no_check (compile_f_ok k38_P [] gid1 0 krd_g krd_b eq_refl eq_refl (no_callees k38_P gid1) eq_refl eq_refl). Time Qed.
Definition k38_cs := [existT ftype krd_g krd].
Time Lemma krdg_ok : callee_ok k38_P (gid1 1) 2305843009213693952%Z krdg_g krdg.
Proof. Time exact_no_check (compile_f_ok k38_P k38_cs gid1 1 krdg_g krdg_b eq_refl eq_refl (all_ok_callees k38_P gid1 k38_cs (conj krd_ok Logic.I)) eq_refl eq_refl). Time Qed.
Print Assumptions krdg_ok.
(* refused: one weighted sum of the three (its weights add to 4: n n n at the caller's bound passes the callee's), a counter no
   vector covers, a vector whose sum grows *)
Check (eq_refl : wf_f [mksig8 3 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[2; 1; 1]]%nat)] krdg_g krdg_b = false).
Check (eq_refl : wf_f [] (mksig8 3 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[1; 1; 0]]%nat)) krd_b = false).
Check (eq_refl : wf_f [] (mksig8 3 (nk 1) false false false None (Some 4611686018427387904%Z) (map lpoly [[1; 1; 0]; [0; 0; 1]]%nat)) krd_b = false).

(* ---- counters grown by other counters (step 39): polynomial weighted sums; k p (m + p) from a written budget, the polynomial
   2m + n^2 + n (it never grows: over the predecessor the difference is 2) *)
Fixpoint krq (n m : nat) (x : i63) : i63 := match n with O => x | S p => krq p (m + p) (PrimInt63.add x 1) end.
Definition krqg (a : i63) : i63 := krq (KQ.KQRun.kq_nat 100) O a.
Definition krq_pol : poly := [(2, [1]); (1, [0; 0]); (1, [0])]%nat.
Definition krq_g := mksig8 2 (nk 1) false false false None (Some 2305843009213693952%Z) [krq_pol].
Definition krqg_g := mksig7 0 (nk 1) false false false None (Some 2305843009213693952%Z).
Definition krq_b := FRec (SVar 0) (SRec (CCons (CAdd (CVar 1) (CVar 0)) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition krqg_b := FPlain (SCall 0 (CCons (CNat (SInt 100)) (CCons CO CNil)) (SCons (SVar 0) SNil)).
Definition k39_P := mkprog [(gid1 0, compile_f gid1 0 krq_g krq_b); (gid1 1, compile_f gid1 1 krqg_g krqg_b)] [].
Time Lemma krq_ok : callee_ok k39_P (gid1 0) 2305843009213693952%Z krq_g krq.
Proof. Time exact_no_check (compile_f_ok k39_P [] gid1 0 krq_g krq_b eq_refl eq_refl (no_callees k39_P gid1) eq_refl eq_refl). Time Qed.
Definition k39_cs := [existT ftype krq_g krq].
Time Lemma krqg_ok : callee_ok k39_P (gid1 1) 2305843009213693952%Z krqg_g krqg.
Proof. Time exact_no_check (compile_f_ok k39_P k39_cs gid1 1 krqg_g krqg_b eq_refl eq_refl (all_ok_callees k39_P gid1 k39_cs (conj krq_ok Logic.I)) eq_refl eq_refl). Time Qed.
Print Assumptions krqg_ok.
(* refused: the same given n n from the data (the polynomial at the caller's bound passes the callee's: the counter outgrows a
   machine number), a degree-1 polynomial (the growth by the predecessor is not linear), a counter with no monomial of its own *)
Check (eq_refl : wf_f [krq_g] (mksig7 1 (nk 1) false false false None (Some 2305843009213693952%Z))
                       (FPlain (SCall 0 (CCons (CVar 0) (CCons (CVar 0) CNil)) (SCons (SVar 0) SNil))) = false).
Check (eq_refl : wf_f [] (mksig8 2 (nk 1) false false false None (Some 2305843009213693952%Z) [lpoly [1; 1]]%nat) krq_b = false).
Check (eq_refl : wf_f [] (mksig8 2 (nk 1) false false false None (Some 2305843009213693952%Z) [[(1, [0; 0]); (1, [0])]]%nat) krq_b = false).

(* ---- a function's bound from what its callers give it, however small (step 40): a recursive function passing small written
   counters on to one whose polynomial grows; its own bound 101, the callee's above its polynomial there (10300) *)
Fixpoint kpas (r n m : nat) (x : i63) : i63 := match r with O => krq n m x | S q => kpas q n m (PrimInt63.add x 1) end.
Definition kpasg (a : i63) : i63 := kpas (KQ.KQRun.kq_nat 3) (KQ.KQRun.kq_nat 100) O a.
Definition krq40_g := mksig8 2 (nk 1) false false false None (Some 20000%Z) [krq_pol].
Definition kpas_g := mksig7 3 (nk 1) false false false None (Some 101%Z).
Definition kpasg_g := mksig7 0 (nk 1) false false false None (Some 2305843009213693952%Z).
Definition kpas_b := FRec (SCall 0 (CCons (CVar 1) (CCons (CVar 0) CNil)) (SCons (SVar 0) SNil))
                          (SRec (CCons (CVar 2) (CCons (CVar 1) CNil)) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition kpasg_b := FPlain (SCall 1 (CCons (CNat (SInt 3)) (CCons (CNat (SInt 100)) (CCons CO CNil))) (SCons (SVar 0) SNil)).
Definition k40_P := mkprog [(gid1 0, compile_f gid1 0 krq40_g krq_b); (gid1 1, compile_f gid1 1 kpas_g kpas_b);
                            (gid1 2, compile_f gid1 2 kpasg_g kpasg_b)] [].
Time Lemma krq40_ok : callee_ok k40_P (gid1 0) 20000%Z krq40_g krq.
Proof. Time exact_no_check (compile_f_ok k40_P [] gid1 0 krq40_g krq_b eq_refl eq_refl (no_callees k40_P gid1) eq_refl eq_refl). Time Qed.
Definition k40_cs := [existT ftype krq40_g krq].
Time Lemma kpas_ok : callee_ok k40_P (gid1 1) 101%Z kpas_g kpas.
Proof. Time exact_no_check (compile_f_ok k40_P k40_cs gid1 1 kpas_g kpas_b eq_refl eq_refl (all_ok_callees k40_P gid1 k40_cs (conj krq40_ok Logic.I)) eq_refl eq_refl). Time Qed.
Definition k40_cs2 := [existT ftype krq40_g krq; existT ftype kpas_g kpas].
Time Lemma kpasg_ok : callee_ok k40_P (gid1 2) 2305843009213693952%Z kpasg_g kpasg.
Proof. Time exact_no_check (compile_f_ok k40_P k40_cs2 gid1 2 kpasg_g kpasg_b eq_refl eq_refl (all_ok_callees k40_P gid1 k40_cs2 (conj krq40_ok (conj kpas_ok Logic.I))) eq_refl eq_refl). Time Qed.
Print Assumptions kpasg_ok.
(* refused: a written budget above a small bound given to the recursion or bound by a let, a caller giving more than the bound *)
Check (eq_refl : wf_f [] (mksig7 2 (nk 1) false false false None (Some 50%Z))
                       (FRec (SVar 0) (SRec (CCons (CNat (SInt 100)) CNil) (SCons (SVar 0) SNil))) = false).
Check (eq_refl : wf_f [] (mksig7 2 (nk 1) false false false None (Some 50%Z))
                       (FRec (SVar 0) (SLetC (CNat (SInt 100)) (SRec (CCons (CVar 0) CNil) (SCons (SVar 0) SNil)))) = false).
Check (eq_refl : wf_f [krq40_g; kpas_g] kpasg_g (FPlain (SCall 1 (CCons (CNat (SInt 3)) (CCons (CNat (SInt 101)) (CCons CO CNil))) (SCons (SVar 0) SNil))) = false).
