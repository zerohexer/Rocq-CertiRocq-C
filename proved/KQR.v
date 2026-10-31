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
From Stdlib Require FinFun.
From compcert Require Import Coqlib Maps AST.
From KQC Require Import KQL KQLAuto KQMSem.
From KQC Require KQMAuto.
Require KQ.KQRun.
Import ListNotations.

Notation mem := KQ.KQRun.mem.

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
with sexps : Type :=
| SNil
| SCons (e : sexp) (r : sexps)
with scnt : Type :=
| CVar (i : nat)                     (* the i-th counter variable, the nearest first *)
| CO
| CS (c : scnt)
| CNat (e : sexp)                    (* kq_nat e: the counter of a number, at most 2^60 *)
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
| BNot (x : sbool).                  (* negb x *)

Scheme sexp_mut := Induction for sexp Sort Prop
with sexps_mut := Induction for sexps Sort Prop
with scnt_mut := Induction for scnt Sort Prop
with scnts_mut := Induction for scnts Sort Prop
with sbool_mut := Induction for sbool Sort Prop.
Combined Scheme sexp_comb from sexp_mut, sexps_mut, scnt_mut, scnts_mut, sbool_mut.

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
| MUpd32 (h i v : sexp) (m : smem).  (* upd32 h i v m *)

(** a function's signature: [sn] counters first, [sk] numbers, a memory last or not, a memory as the result or a number,
    and for a number: whether the function writes the memory ([sw]: its KQL ends with some memory, not the one it was given) *)
Record sig := mksig { sn : nat; sk : nat; sm : bool; sr : bool; sw : bool }.

Definition rty (r : bool) : Type := if r then mem else i63.

Fixpoint ntype (k : nat) (m r : bool) : Type :=
  match k with O => if m then (mem -> rty r) else rty r | S k => i63 -> ntype k m r end.

Fixpoint ctype (x : nat) (T : Type) : Type := match x with O => T | S x => nat -> ctype x T end.

Definition ftype (g : sig) : Type := ctype (sn g) (ntype (sk g) (sm g) (sr g)).

(** a memory for the meaning of a function that takes none: never read (a well formed body reads no memory then) *)
Definition dummy_mem : mem := KQ.KQRun.kq_input 0%uint63.

(** [absn k m r F] is [fun x1 .. xk (s) => F [xk; ..; x1] s]: the parameters bound before anything else, as in the user's text *)
Fixpoint absn (k : nat) (m r : bool) {struct k} : (list i63 -> mem -> rty r) -> ntype k m r :=
  match k as k0 return (list i63 -> mem -> rty r) -> ntype k0 m r with
  | O => if m as m0 return (list i63 -> mem -> rty r) -> ntype O m0 r then (fun F s => F [] s) else (fun F => F [] dummy_mem)
  | S k => fun F x => absn k m r (fun env s => F (env ++ [x]) s)
  end.

(** [appn k m r g [v1; ..; vk] s] is [g v1 .. vk (s)] *)
Fixpoint appn (k : nat) (m r : bool) {struct k} : ntype k m r -> list i63 -> mem -> rty r :=
  match k as k0 return ntype k0 m r -> list i63 -> mem -> rty r with
  | O => if m as m0 return ntype O m0 r -> list i63 -> mem -> rty r then (fun g _ s => g s) else (fun g _ _ => g)
  | S k => fun g l s => match l with x :: l => appn k m r (g x) l s | [] => appn k m r (g 0%uint63) [] s end
  end.

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
Definition callf (g : sig) : ftype g -> list nat -> list i63 -> mem -> rty (sr g) :=
  match g as g0 return ftype g0 -> list nat -> list i63 -> mem -> rty (sr g0) with
  | mksig x k m r _ => fun h cvs vs s => appn k m r (appc x (ntype k m r) h cvs) vs s
  end.

(** a call's number (0 for a function giving back a memory, as its KQL returns) and the memory after it *)
Definition calln (g : sig) (h : ftype g) (cvs : list nat) (vs : list i63) (s : mem) : i63 :=
  (if sr g as r return rty r -> i63 then fun _ => 0%uint63 else fun x => x) (callf g h cvs vs s).
Definition callm (g : sig) (h : ftype g) (cvs : list nat) (vs : list i63) (s : mem) : mem :=
  (if sr g as r return rty r -> mem then fun x => x else fun _ => s) (callf g h cvs vs s).

(** a callee: its signature and its meaning *)
Definition callee := { g : sig & ftype g }.

Fixpoint denote_e (cs : list callee) (rec : list nat -> list i63 -> mem -> i63) (cenv : list nat) (benv : list bool)
  (env : list i63) (s : mem) (e : sexp) {struct e} : i63 :=
  match e with
  | SVar i => nth i env 0%uint63
  | SInt n => n
  | SOp o a b => binop_sem o (denote_e cs rec cenv benv env s a) (denote_e cs rec cenv benv env s b)
  | SIf c a b t f => if cmp_sem c (denote_e cs rec cenv benv env s a) (denote_e cs rec cenv benv env s b)
                     then denote_e cs rec cenv benv env s t else denote_e cs rec cenv benv env s f
  | SLet e1 e2 => let x := denote_e cs rec cenv benv env s e1 in denote_e cs rec cenv benv (x :: env) s e2
  | SRd h i => KQ.KQRun.rd (denote_e cs rec cenv benv env s h) (denote_e cs rec cenv benv env s i) s
  | SRec ccs args => rec (denote_cs cs rec cenv benv env s ccs) (denote_es cs rec cenv benv env s args) s
  | SCall f ccs args =>
      match nth_error cs f with
      | Some (existT _ g h) => calln g h (denote_cs cs rec cenv benv env s ccs) (denote_es cs rec cenv benv env s args) s
      | None => 0%uint63
      end
  | SMatch c e0 e1 =>
      match nth c cenv O with O => denote_e cs rec cenv benv env s e0 | S p => denote_e cs rec (p :: cenv) benv env s e1 end
  | SIfB b t f => if denote_b cs rec cenv benv env s b then denote_e cs rec cenv benv env s t else denote_e cs rec cenv benv env s f
  | SLetB b e => let x := denote_b cs rec cenv benv env s b in denote_e cs rec cenv (x :: benv) env s e
  | SRd32 h i => KQ.KQRun.rd32 (denote_e cs rec cenv benv env s h) (denote_e cs rec cenv benv env s i) s
  end
with denote_es (cs : list callee) (rec : list nat -> list i63 -> mem -> i63) (cenv : list nat) (benv : list bool)
  (env : list i63) (s : mem) (es : sexps) {struct es} : list i63 :=
  match es with
  | SNil => []
  | SCons e r => denote_e cs rec cenv benv env s e :: denote_es cs rec cenv benv env s r
  end
with denote_c (cs : list callee) (rec : list nat -> list i63 -> mem -> i63) (cenv : list nat) (benv : list bool)
  (env : list i63) (s : mem) (c : scnt) {struct c} : nat :=
  match c with
  | CVar i => nth i cenv O
  | CO => O
  | CS c => S (denote_c cs rec cenv benv env s c)
  | CNat e => KQ.KQRun.kq_nat (denote_e cs rec cenv benv env s e)
  end
with denote_cs (cs : list callee) (rec : list nat -> list i63 -> mem -> i63) (cenv : list nat) (benv : list bool)
  (env : list i63) (s : mem) (ccs : scnts) {struct ccs} : list nat :=
  match ccs with
  | CNil => []
  | CCons c r => denote_c cs rec cenv benv env s c :: denote_cs cs rec cenv benv env s r
  end
with denote_b (cs : list callee) (rec : list nat -> list i63 -> mem -> i63) (cenv : list nat) (benv : list bool)
  (env : list i63) (s : mem) (b : sbool) {struct b} : bool :=
  match b with
  | BCmp c x y => cmp_sem c (denote_e cs rec cenv benv env s x) (denote_e cs rec cenv benv env s y)
  | BVar i => nth i benv false
  | BTrue => true
  | BFalse => false
  | BAnd x y => andb (denote_b cs rec cenv benv env s x) (denote_b cs rec cenv benv env s y)
  | BOr x y => orb (denote_b cs rec cenv benv env s x) (denote_b cs rec cenv benv env s y)
  | BNot x => negb (denote_b cs rec cenv benv env s x)
  end.

Fixpoint denote_m (cs : list callee) (rec : list nat -> list i63 -> mem -> i63) (recm : list nat -> list i63 -> mem -> mem)
  (cenv : list nat) (benv : list bool) (env : list i63) (s : mem) (m : smem) {struct m} : mem :=
  match m with
  | MCur => s
  | MUpd h i v m => KQ.KQRun.upd (denote_e cs rec cenv benv env s h) (denote_e cs rec cenv benv env s i)
                                 (denote_e cs rec cenv benv env s v) (denote_m cs rec recm cenv benv env s m)
  | MLet e m => let x := denote_e cs rec cenv benv env s e in denote_m cs rec recm cenv benv (x :: env) s m
  | MLetM m1 m2 => let s2 := denote_m cs rec recm cenv benv env s m1 in denote_m cs rec recm cenv benv env s2 m2
  | MIf c a b m1 m2 => if cmp_sem c (denote_e cs rec cenv benv env s a) (denote_e cs rec cenv benv env s b)
                       then denote_m cs rec recm cenv benv env s m1 else denote_m cs rec recm cenv benv env s m2
  | MRec ccs args m => recm (denote_cs cs rec cenv benv env s ccs) (denote_es cs rec cenv benv env s args)
                            (denote_m cs rec recm cenv benv env s m)
  | MCall f ccs args m =>
      match nth_error cs f with
      | Some (existT _ g h) => callm g h (denote_cs cs rec cenv benv env s ccs) (denote_es cs rec cenv benv env s args)
                                     (denote_m cs rec recm cenv benv env s m)
      | None => s
      end
  | MMatch c m0 m1 =>
      match nth c cenv O with
      | O => denote_m cs rec recm cenv benv env s m0
      | S p => denote_m cs rec recm (p :: cenv) benv env s m1
      end
  | MIfB b m1 m2 => if denote_b cs rec cenv benv env s b then denote_m cs rec recm cenv benv env s m1
                    else denote_m cs rec recm cenv benv env s m2
  | MLetB b m => let x := denote_b cs rec cenv benv env s b in denote_m cs rec recm cenv (x :: benv) env s m
  | MUpd32 h i v m => KQ.KQRun.upd32 (denote_e cs rec cenv benv env s h) (denote_e cs rec cenv benv env s i)
                                     (denote_e cs rec cenv benv env s v) (denote_m cs rec recm cenv benv env s m)
  end.

(** a number made after memories: the memories first ([let s2 := m in ..], each the newest in what follows), then the number
    read from the newest one; lets of numbers and booleans and tests on the way *)
Inductive sx : Type :=
| XRet (e : sexp)                    (* the number, from the newest memory *)
| XLetM (m : smem) (x : sx)          (* let s2 := m in x *)
| XLet (e : sexp) (x : sx)           (* let v := e in x *)
| XLetB (b : sbool) (x : sx)         (* let v := b in x, v a boolean *)
| XIf (c : cmpop) (a b : sexp) (x1 x2 : sx)
| XIfB (b : sbool) (x1 x2 : sx)
| XMatch (c : nat) (x0 x1 : sx).

Fixpoint denote_x (cs : list callee) (rec : list nat -> list i63 -> mem -> i63) (recm : list nat -> list i63 -> mem -> mem)
  (cenv : list nat) (benv : list bool) (env : list i63) (s : mem) (x : sx) {struct x} : i63 :=
  match x with
  | XRet e => denote_e cs rec cenv benv env s e
  | XLetM m x => let s2 := denote_m cs rec recm cenv benv env s m in denote_x cs rec recm cenv benv env s2 x
  | XLet e x => let v := denote_e cs rec cenv benv env s e in denote_x cs rec recm cenv benv (v :: env) s x
  | XLetB b x => let v := denote_b cs rec cenv benv env s b in denote_x cs rec recm cenv (v :: benv) env s x
  | XIf c a b x1 x2 => if cmp_sem c (denote_e cs rec cenv benv env s a) (denote_e cs rec cenv benv env s b)
                       then denote_x cs rec recm cenv benv env s x1 else denote_x cs rec recm cenv benv env s x2
  | XIfB b x1 x2 => if denote_b cs rec cenv benv env s b then denote_x cs rec recm cenv benv env s x1 else denote_x cs rec recm cenv benv env s x2
  | XMatch c x0 x1 => match nth c cenv O with O => denote_x cs rec recm cenv benv env s x0 | S p => denote_x cs rec recm (p :: cenv) benv env s x1 end
  end.

(** the memory the KQL of [x] ends with: the last one made *)
Fixpoint endx (cs : list callee) (rec : list nat -> list i63 -> mem -> i63) (recm : list nat -> list i63 -> mem -> mem)
  (cenv : list nat) (benv : list bool) (env : list i63) (s : mem) (x : sx) {struct x} : mem :=
  match x with
  | XRet _ => s
  | XLetM m x => endx cs rec recm cenv benv env (denote_m cs rec recm cenv benv env s m) x
  | XLet e x => endx cs rec recm cenv benv (denote_e cs rec cenv benv env s e :: env) s x
  | XLetB b x => endx cs rec recm cenv (denote_b cs rec cenv benv env s b :: benv) env s x
  | XIf c a b x1 x2 => if cmp_sem c (denote_e cs rec cenv benv env s a) (denote_e cs rec cenv benv env s b)
                       then endx cs rec recm cenv benv env s x1 else endx cs rec recm cenv benv env s x2
  | XIfB b x1 x2 => if denote_b cs rec cenv benv env s b then endx cs rec recm cenv benv env s x1 else endx cs rec recm cenv benv env s x2
  | XMatch c x0 x1 => match nth c cenv O with O => endx cs rec recm cenv benv env s x0 | S p => endx cs rec recm (p :: cenv) benv env s x1 end
  end.

(** a function's body: a number, recursive on the first counter ([e0] when it is 0, [e1] otherwise) or plain; or a memory,
    the same; or a number made after memories *)
Inductive fbody := FRec (e0 e1 : sexp) | FPlain (e : sexp) | FRecM (m0 m1 : smem) | FPlainM (m : smem) | FPlainX (x : sx).

Definition dnum : list nat -> list i63 -> mem -> i63 := fun _ _ _ => 0%uint63.
Definition dmem : list nat -> list i63 -> mem -> mem := fun _ _ s => s.

Definition denote_f (cs : list callee) (g : sig) (b : fbody) : ftype g :=
  match g as g0 return ftype g0 with
  | mksig x k m r w =>
      if r as r0 return ftype (mksig x k m r0 w) then
        match x as x0 return ftype (mksig x0 k m true w) with
        | O => match b with
               | FPlainM e => absn k m true (fun env s => denote_m cs dnum dmem [] [] env s e)
               | _ => absn k m true (fun _ s => s)
               end
        | S x' =>
            match b with
            | FRecM m0 m1 =>
                fix go (n : nat) : ctype x' (ntype k m true) :=
                  absc x' _ (fun cenv => absn k m true (fun env s =>
                    match n with
                    | O => denote_m cs dnum dmem (cenv ++ [n]) [] env s m0
                    | S n' => denote_m cs dnum (fun cvs args s' => appn k m true (appc x' _ (go n') cvs) args s')
                                       (n' :: cenv ++ [n]) [] env s m1
                    end))
            | FPlainM e => fun n => absc x' _ (fun cenv => absn k m true (fun env s => denote_m cs dnum dmem (cenv ++ [n]) [] env s e))
            | _ => fun _ => absc x' _ (fun _ => absn k m true (fun _ s => s))
            end
        end
      else
        match x as x0 return ftype (mksig x0 k m false w) with
        | O => match b with
               | FPlain e => absn k m false (fun env s => denote_e cs dnum [] [] env s e)
               | FPlainX xx => absn k m false (fun env s => denote_x cs dnum dmem [] [] env s xx)
               | _ => absn k m false (fun _ _ => 0%uint63)
               end
        | S x' =>
            match b with
            | FRec e0 e1 =>
                fix go (n : nat) : ctype x' (ntype k m false) :=
                  absc x' _ (fun cenv => absn k m false (fun env s =>
                    match n with
                    | O => denote_e cs dnum (cenv ++ [n]) [] env s e0
                    | S n' => denote_e cs (fun cvs args s' => appn k m false (appc x' _ (go n') cvs) args s')
                                       (n' :: cenv ++ [n]) [] env s e1
                    end))
            | FPlain e => fun n => absc x' _ (fun cenv => absn k m false (fun env s => denote_e cs dnum (cenv ++ [n]) [] env s e))
            | FPlainX xx => fun n => absc x' _ (fun cenv => absn k m false (fun env s => denote_x cs dnum dmem (cenv ++ [n]) [] env s xx))
            | _ => fun _ => absc x' _ (fun _ => absn k m false (fun _ _ => 0%uint63))
            end
        end
  end.

(* ================================================================ compile *)
Definition cap60 : i63 := 1152921504606846976%uint63.

(** a choice between two numbers that are both worked out and one taken with a conditional move, no jump (the
    translator's [choice_ok], D17): arithmetic, variables, reads of the memory and such choices, at most three reads in the
    two numbers.  A choice with a call, a let or a match stays a jump; so does the end of a function (a loop's tests) *)
Fixpoint spec (e : sexp) : bool :=
  match e with
  | SVar _ | SInt _ => true
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

Fixpoint len_s (es : sexps) : nat := match es with SNil => O | SCons _ es => S (len_s es) end.
Fixpoint len_c (cs : scnts) : nat := match cs with CNil => O | CCons _ cs => S (len_c cs) end.
Fixpoint cdepth (c : scnt) : nat := match c with CS c => S (cdepth c) | _ => O end.
Fixpoint all_c (p : scnt -> bool) (cs : scnts) : bool := match cs with CNil => true | CCons c r => p c && all_c p r end.
Fixpoint all_s (p : sexp -> bool) (es : sexps) : bool := match es with SNil => true | SCons e r => p e && all_s p r end.

(** [if c then f a.. else f b..] at the end of [f], both calls on the newest memory, becomes one call whose arguments are
    chosen by conditional moves (the translator's merging of calls, D17): arguments that are plain arithmetic (no read, no
    call), each chosen when the two differ ([same_e]: the same variable or the same number) *)
Definition simple (e : sexp) : bool := spec e && Nat.eqb (nrd e) 0.
Definition simple_c (c : scnt) : bool := match c with CVar _ | CO => true | CNat e => simple e | CS _ => false end.
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
Definition merge_ok (cs1 cs2 : scnts) (as1 as2 : sexps) : bool :=
  all_c simple_c cs1 && all_c simple_c cs2 && all_s simple as1 && all_s simple as2.
Definition mergeable_e (e1 e2 : sexp) : option (scnts * sexps * scnts * sexps) :=
  match e1, e2 with
  | SRec cs1 as1, SRec cs2 as2 => if merge_ok cs1 cs2 as1 as2 then Some (cs1, as1, cs2, as2) else None
  | _, _ => None
  end.
Definition mergeable_m (m1 m2 : smem) : option (scnts * sexps * scnts * sexps) :=
  match m1, m2 with
  | MRec cs1 as1 MCur, MRec cs2 as2 MCur => if merge_ok cs1 cs2 as1 as2 then Some (cs1, as1, cs2, as2) else None
  | _, _ => None
  end.

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

Section C.
Variable gidf : nat -> ident.   (* the KQL name of the program's function i *)
Variable g : ident.             (* the function's own name *)
Variable mv : ident.            (* the variable holding the first counter's predecessor *)

(** a number, worked out in A-normal form; [K] gets the atom holding it and the next free variable.  The atoms of the counters,
    the booleans (each holding 1 or 0) and the numbers in scope, the nearest first *)
Fixpoint cexp (e : sexp) (cenv benv env : list atom) (nxt : ident) (K : atom -> ident -> exp) {struct e} : exp :=
  match e with
  | SVar i => K (nth i env (Aint 0%uint63)) nxt
  | SInt n => K (Aint n) nxt
  | SOp o a b => cexp a cenv benv env nxt (fun A n1 => cexp b cenv benv env n1 (fun B n2 => Eop n2 o A B (K (Avar n2) (Pos.succ n2))))
  | SIf c a b t f => cexp a cenv benv env nxt (fun A n1 => cexp b cenv benv env n1 (fun B n2 =>
                       if choice_ok t f then
                         cexp t cenv benv env n2 (fun T n3 => cexp f cenv benv env n3 (fun F n4 =>
                           Esel n4 c A B T F (K (Avar n4) (Pos.succ n4))))
                       else let tc := cexp t cenv benv env n2 K in Eif c A B tc (cexp f cenv benv env (after n2 tc) K)))
  | SLet e1 e2 => cexp e1 cenv benv env nxt (fun A n1 => cexp e2 cenv benv (A :: env) n1 K)
  | SRd h i => cexp h cenv benv env nxt (fun H n1 => cexp i cenv benv env n1 (fun I n2 => Ekld n2 H I (K (Avar n2) (Pos.succ n2))))
  | SRec ccs args => ccnts ccs cenv benv env nxt (fun Cs n1 => cexps args cenv benv env n1 (fun As n2 =>
                       Ecall n2 g (Avar mv :: Cs ++ As) (K (Avar n2) (Pos.succ n2))))
  | SCall f ccs args => ccnts ccs cenv benv env nxt (fun Cs n1 => cexps args cenv benv env n1 (fun As n2 =>
                          Ecall n2 (gidf f) (Cs ++ As) (K (Avar n2) (Pos.succ n2))))
  | SMatch c e0 e1 => let t0 := cexp e0 cenv benv env nxt K in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (cexp e1 (Avar (after nxt t0) :: cenv) benv env (Pos.succ (after nxt t0)) K))
  | SIfB b t f => if choice_ok t f then
                    cbval b cenv benv env nxt (fun C n1 => cexp t cenv benv env n1 (fun T n2 => cexp f cenv benv env n2 (fun F n3 =>
                      Esel n3 Ceq C (Aint 0%uint63) F T (K (Avar n3) (Pos.succ n3)))))
                  else ccond b cenv benv env nxt (fun n => cexp t cenv benv env n K) (fun n => cexp f cenv benv env n K)
  | SLetB b e => cbval b cenv benv env nxt (fun A n1 => cexp e cenv (A :: benv) env n1 K)
  | SRd32 h i => cexp h cenv benv env nxt (fun H n1 => cexp i cenv benv env n1 (fun I n2 => Ekld32 n2 H I (K (Avar n2) (Pos.succ n2))))
  end
with cexps (es : sexps) (cenv benv env : list atom) (nxt : ident) (K : list atom -> ident -> exp) {struct es} : exp :=
  match es with
  | SNil => K [] nxt
  | SCons e r => cexp e cenv benv env nxt (fun A n1 => cexps r cenv benv env n1 (fun As n2 => K (A :: As) n2))
  end
with ccnt (c : scnt) (cenv benv env : list atom) (nxt : ident) (K : atom -> ident -> exp) {struct c} : exp :=
  match c with
  | CVar i => K (nth i cenv (Aint 0%uint63)) nxt
  | CO => K (Aint 0%uint63) nxt
  | CS c => ccnt c cenv benv env nxt (fun A n1 => Eop n1 Badd A (Aint 1%uint63) (K (Avar n1) (Pos.succ n1)))
  | CNat e => cexp e cenv benv env nxt (fun A n1 =>
                Esel n1 Csle A (Aint 0%uint63) (Aint 0%uint63) A
                  (Esel (Pos.succ n1) Cslt (Aint cap60) (Avar n1) (Aint cap60) (Avar n1)
                     (K (Avar (Pos.succ n1)) (Pos.succ (Pos.succ n1)))))
  end
with ccnts (ccs : scnts) (cenv benv env : list atom) (nxt : ident) (K : list atom -> ident -> exp) {struct ccs} : exp :=
  match ccs with
  | CNil => K [] nxt
  | CCons c r => ccnt c cenv benv env nxt (fun A n1 => ccnts r cenv benv env n1 (fun As n2 => K (A :: As) n2))
  end
(** a boolean as a test: jumps, [KT] where it holds and [KF] where it does not, each given the next free variable; [a && b]
    tests [b] only where [a] held (C's short-circuit) *)
with ccond (b : sbool) (cenv benv env : list atom) (nxt : ident) (KT KF : ident -> exp) {struct b} : exp :=
  match b with
  | BCmp c x y => cexp x cenv benv env nxt (fun A n1 => cexp y cenv benv env n1 (fun B n2 => Eif c A B (KT n2) (KF (after n2 (KT n2)))))
  | BVar i => Eif Ceq (nth i benv (Aint 0%uint63)) (Aint 0%uint63) (KF nxt) (KT (after nxt (KF nxt)))
  | BTrue => KT nxt
  | BFalse => KF nxt
  | BAnd x y => ccond x cenv benv env nxt (fun n => ccond y cenv benv env n KT KF) KF
  | BOr x y => ccond x cenv benv env nxt KT (fun n => ccond y cenv benv env n KT KF)
  | BNot x => ccond x cenv benv env nxt KF KT
  end
(** a boolean as a value, 1 or 0, with no jump: a comparison by a conditional move, [&&] [||] [negb] by [land] [lor]
    [lxor 1] of the parts' values *)
with cbval (b : sbool) (cenv benv env : list atom) (nxt : ident) (K : atom -> ident -> exp) {struct b} : exp :=
  match b with
  | BCmp c x y => cexp x cenv benv env nxt (fun A n1 => cexp y cenv benv env n1 (fun B n2 =>
                    Esel n2 c A B (Aint 1%uint63) (Aint 0%uint63) (K (Avar n2) (Pos.succ n2))))
  | BVar i => K (nth i benv (Aint 0%uint63)) nxt
  | BTrue => K (Aint 1%uint63) nxt
  | BFalse => K (Aint 0%uint63) nxt
  | BAnd x y => cbval x cenv benv env nxt (fun A n1 => cbval y cenv benv env n1 (fun B n2 =>
                  Eop n2 Bland A B (K (Avar n2) (Pos.succ n2))))
  | BOr x y => cbval x cenv benv env nxt (fun A n1 => cbval y cenv benv env n1 (fun B n2 =>
                 Eop n2 Blor A B (K (Avar n2) (Pos.succ n2))))
  | BNot x => cbval x cenv benv env nxt (fun A n1 => Eop n1 Blxor A (Aint 1%uint63) (K (Avar n1) (Pos.succ n1)))
  end.

(** the arguments of two calls, chosen by the test [A c B]: an argument the same in both worked out once *)
Fixpoint cmerge_s (c : cmpop) (A B : atom) (es1 es2 : sexps) (cenv benv env : list atom) (nxt : ident) (K : list atom -> ident -> exp)
  {struct es1} : exp :=
  match es1, es2 with
  | SCons e1 r1, SCons e2 r2 =>
      if same_e e1 e2 then cexp e1 cenv benv env nxt (fun X n1 => cmerge_s c A B r1 r2 cenv benv env n1 (fun Xs n2 => K (X :: Xs) n2))
      else cexp e1 cenv benv env nxt (fun X n1 => cexp e2 cenv benv env n1 (fun Y n2 =>
             Esel n2 c A B X Y (cmerge_s c A B r1 r2 cenv benv env (Pos.succ n2) (fun Xs n3 => K (Avar n2 :: Xs) n3))))
  | _, _ => K [] nxt
  end.
Fixpoint cmerge_c (c : cmpop) (A B : atom) (cs1 cs2 : scnts) (cenv benv env : list atom) (nxt : ident) (K : list atom -> ident -> exp)
  {struct cs1} : exp :=
  match cs1, cs2 with
  | CCons c1 r1, CCons c2 r2 =>
      if same_c c1 c2 then ccnt c1 cenv benv env nxt (fun X n1 => cmerge_c c A B r1 r2 cenv benv env n1 (fun Xs n2 => K (X :: Xs) n2))
      else ccnt c1 cenv benv env nxt (fun X n1 => ccnt c2 cenv benv env n1 (fun Y n2 =>
             Esel n2 c A B X Y (cmerge_c c A B r1 r2 cenv benv env (Pos.succ n2) (fun Xs n3 => K (Avar n2 :: Xs) n3))))
  | _, _ => K [] nxt
  end.

(** the body in tail position: a test is a branch, the recursive call a loop *)
Fixpoint ctail (e : sexp) (cenv benv env : list atom) (nxt : ident) {struct e} : exp :=
  match e with
  | SIf c a b t f => cexp a cenv benv env nxt (fun A n1 => cexp b cenv benv env n1 (fun B n2 =>
                       match mergeable_e t f with
                       | Some (cs1, as1, cs2, as2) =>
                           cmerge_c c A B cs1 cs2 cenv benv env n2 (fun Cs n3 => cmerge_s c A B as1 as2 cenv benv env n3 (fun As _ =>
                             Eloop (Avar mv :: Cs ++ As)))
                       | None => let tc := ctail t cenv benv env n2 in Eif c A B tc (ctail f cenv benv env (after n2 tc))
                       end))
  | SLet e1 e2 => cexp e1 cenv benv env nxt (fun A n1 => ctail e2 cenv benv (A :: env) n1)
  | SRec ccs args => ccnts ccs cenv benv env nxt (fun Cs n1 => cexps args cenv benv env n1 (fun As _ => Eloop (Avar mv :: Cs ++ As)))
  | SMatch c e0 e1 => let t0 := ctail e0 cenv benv env nxt in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (ctail e1 (Avar (after nxt t0) :: cenv) benv env (Pos.succ (after nxt t0))))
  | SIfB b t f => ccond b cenv benv env nxt (fun n => ctail t cenv benv env n) (fun n => ctail f cenv benv env n)
  | SLetB b e => cbval b cenv benv env nxt (fun A n1 => ctail e cenv (A :: benv) env n1)
  | _ => cexp e cenv benv env nxt (fun A _ => Eret A)
  end.

(** a memory, made in KQL's one memory: the numbers first, then the memory given, then the construct's own step (a write,
    a call); [K] gets the next free variable *)
Fixpoint cmem (m : smem) (cenv benv env : list atom) (nxt : ident) (K : ident -> exp) {struct m} : exp :=
  match m with
  | MCur => K nxt
  | MUpd h i v m => cexp h cenv benv env nxt (fun H n1 => cexp i cenv benv env n1 (fun I n2 => cexp v cenv benv env n2 (fun V n3 =>
                      cmem m cenv benv env n3 (fun n4 => Ekst H I V (K n4)))))
  | MLet e m => cexp e cenv benv env nxt (fun A n1 => cmem m cenv benv (A :: env) n1 K)
  | MLetM m1 m2 => cmem m1 cenv benv env nxt (fun n1 => cmem m2 cenv benv env n1 K)
  | MIf c a b m1 m2 => cexp a cenv benv env nxt (fun A n1 => cexp b cenv benv env n1 (fun B n2 =>
                         let tc := cmem m1 cenv benv env n2 K in Eif c A B tc (cmem m2 cenv benv env (after n2 tc) K)))
  | MRec ccs args m => ccnts ccs cenv benv env nxt (fun Cs n1 => cexps args cenv benv env n1 (fun As n2 => cmem m cenv benv env n2 (fun n3 =>
                         Ecall n3 g (Avar mv :: Cs ++ As) (K (Pos.succ n3)))))
  | MCall f ccs args m => ccnts ccs cenv benv env nxt (fun Cs n1 => cexps args cenv benv env n1 (fun As n2 => cmem m cenv benv env n2 (fun n3 =>
                            Ecall n3 (gidf f) (Cs ++ As) (K (Pos.succ n3)))))
  | MMatch c m0 m1 => let t0 := cmem m0 cenv benv env nxt K in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (cmem m1 (Avar (after nxt t0) :: cenv) benv env (Pos.succ (after nxt t0)) K))
  | MIfB b m1 m2 => ccond b cenv benv env nxt (fun n => cmem m1 cenv benv env n K) (fun n => cmem m2 cenv benv env n K)
  | MLetB b m => cbval b cenv benv env nxt (fun A n1 => cmem m cenv (A :: benv) env n1 K)
  | MUpd32 h i v m => cexp h cenv benv env nxt (fun H n1 => cexp i cenv benv env n1 (fun I n2 => cexp v cenv benv env n2 (fun V n3 =>
                        cmem m cenv benv env n3 (fun n4 => Ekst32 H I V (K n4)))))
  end.

(** a memory in tail position: a test is a branch, the recursive call a loop, the end returns 0 with the memory made *)
Fixpoint ctailm (m : smem) (cenv benv env : list atom) (nxt : ident) {struct m} : exp :=
  match m with
  | MIf c a b m1 m2 => cexp a cenv benv env nxt (fun A n1 => cexp b cenv benv env n1 (fun B n2 =>
                         match mergeable_m m1 m2 with
                         | Some (cs1, as1, cs2, as2) =>
                             cmerge_c c A B cs1 cs2 cenv benv env n2 (fun Cs n3 => cmerge_s c A B as1 as2 cenv benv env n3 (fun As _ =>
                               Eloop (Avar mv :: Cs ++ As)))
                         | None => let tc := ctailm m1 cenv benv env n2 in Eif c A B tc (ctailm m2 cenv benv env (after n2 tc))
                         end))
  | MLet e m => cexp e cenv benv env nxt (fun A n1 => ctailm m cenv benv (A :: env) n1)
  | MLetM m1 m2 => cmem m1 cenv benv env nxt (fun n1 => ctailm m2 cenv benv env n1)
  | MRec ccs args m => ccnts ccs cenv benv env nxt (fun Cs n1 => cexps args cenv benv env n1 (fun As n2 =>
                         cmem m cenv benv env n2 (fun _ => Eloop (Avar mv :: Cs ++ As))))
  | MMatch c m0 m1 => let t0 := ctailm m0 cenv benv env nxt in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (ctailm m1 (Avar (after nxt t0) :: cenv) benv env (Pos.succ (after nxt t0))))
  | MIfB b m1 m2 => ccond b cenv benv env nxt (fun n => ctailm m1 cenv benv env n) (fun n => ctailm m2 cenv benv env n)
  | MLetB b m => cbval b cenv benv env nxt (fun A n1 => ctailm m cenv (A :: benv) env n1)
  | _ => cmem m cenv benv env nxt (fun _ => Eret (Aint 0%uint63))
  end.

(** a number made after memories, in tail position: the memories by [cmem], the tests as branches, the end returns the number *)
Fixpoint ctailx (x : sx) (cenv benv env : list atom) (nxt : ident) {struct x} : exp :=
  match x with
  | XRet e => cexp e cenv benv env nxt (fun A _ => Eret A)
  | XLetM m x => cmem m cenv benv env nxt (fun n1 => ctailx x cenv benv env n1)
  | XLet e x => cexp e cenv benv env nxt (fun A n1 => ctailx x cenv benv (A :: env) n1)
  | XLetB b x => cbval b cenv benv env nxt (fun A n1 => ctailx x cenv (A :: benv) env n1)
  | XIf c a b x1 x2 => cexp a cenv benv env nxt (fun A n1 => cexp b cenv benv env n1 (fun B n2 =>
                         let tc := ctailx x1 cenv benv env n2 in Eif c A B tc (ctailx x2 cenv benv env (after n2 tc))))
  | XIfB b x1 x2 => ccond b cenv benv env nxt (fun n => ctailx x1 cenv benv env n) (fun n => ctailx x2 cenv benv env n)
  | XMatch c x0 x1 => let t0 := ctailx x0 cenv benv env nxt in
                      Eif Ceq (nth c cenv (Aint 0%uint63)) (Aint 0%uint63) t0
                        (Eop (after nxt t0) Bsub (nth c cenv (Aint 0%uint63)) (Aint 1%uint63)
                             (ctailx x1 (Avar (after nxt t0) :: cenv) benv env (Pos.succ (after nxt t0))))
  end.
End C.

(** a callee's counters nest S at most 2^20 deep; the recursive call's counters after the first are not grown *)
Definition shallow (c : scnt) : bool := (Z.of_nat (cdepth c) <=? 1048576)%Z.
Definition flat (c : scnt) : bool := Nat.eqb (cdepth c) 0.

(** well formed, in a function whose callees have the signatures [sigs]: the recursive call only where [r] allows it, with
    [nx] counters after the first and [k] numbers; the memory read, or given to a callee, only where there is one ([mok]); a
    callee called for a number gives back a number *)
Fixpoint wf (sigs : list sig) (r mok : bool) (nx k : nat) (e : sexp) {struct e} : bool :=
  match e with
  | SVar _ | SInt _ => true
  | SOp _ a b | SLet a b => wf sigs r mok nx k a && wf sigs r mok nx k b
  | SRd a b | SRd32 a b => mok && wf sigs r mok nx k a && wf sigs r mok nx k b
  | SIf _ a b t f => wf sigs r mok nx k a && wf sigs r mok nx k b && wf sigs r mok nx k t && wf sigs r mok nx k f
  | SRec ccs args => r && Nat.eqb (len_c ccs) nx && Nat.eqb (len_s args) k && all_c flat ccs
                     && wfcs sigs r mok nx k ccs && wfs sigs r mok nx k args
  | SCall f ccs args =>
      match nth_error sigs f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && Nat.eqb (len_s args) (sk gs) && implb (sm gs) mok && negb (sr gs)
                   && negb (sw gs) && all_c shallow ccs && wfcs sigs r mok nx k ccs && wfs sigs r mok nx k args
      | None => false
      end
  | SMatch _ e0 e1 => wf sigs r mok nx k e0 && wf sigs r mok nx k e1
  | SIfB b t f => wfb sigs r mok nx k b && wf sigs r mok nx k t && wf sigs r mok nx k f
  | SLetB b e => wfb sigs r mok nx k b && wf sigs r mok nx k e
  end
with wfs (sigs : list sig) (r mok : bool) (nx k : nat) (es : sexps) {struct es} : bool :=
  match es with SNil => true | SCons e es => wf sigs r mok nx k e && wfs sigs r mok nx k es end
with wfc (sigs : list sig) (r mok : bool) (nx k : nat) (c : scnt) {struct c} : bool :=
  match c with CVar _ | CO => true | CS c => wfc sigs r mok nx k c | CNat e => wf sigs r mok nx k e end
with wfcs (sigs : list sig) (r mok : bool) (nx k : nat) (cs : scnts) {struct cs} : bool :=
  match cs with CNil => true | CCons c cs => wfc sigs r mok nx k c && wfcs sigs r mok nx k cs end
with wfb (sigs : list sig) (r mok : bool) (nx k : nat) (b : sbool) {struct b} : bool :=
  match b with
  | BCmp _ x y => wf sigs r mok nx k x && wf sigs r mok nx k y
  | BVar _ | BTrue | BFalse => true
  | BAnd x y | BOr x y => wfb sigs r mok nx k x && wfb sigs r mok nx k y
  | BNot x => wfb sigs r mok nx k x
  end.

(** a memory: its numbers as above; the recursive call only where [rm] allows it; a callee called for a memory takes one and
    gives one back *)
Fixpoint wfm (sigs : list sig) (r rm mok : bool) (nx k : nat) (m : smem) {struct m} : bool :=
  match m with
  | MCur => true
  | MUpd h i v m | MUpd32 h i v m => wf sigs r mok nx k h && wf sigs r mok nx k i && wf sigs r mok nx k v && wfm sigs r rm mok nx k m
  | MLet e m => wf sigs r mok nx k e && wfm sigs r rm mok nx k m
  | MLetM m1 m2 => wfm sigs r rm mok nx k m1 && wfm sigs r rm mok nx k m2
  | MIf _ a b m1 m2 => wf sigs r mok nx k a && wf sigs r mok nx k b && wfm sigs r rm mok nx k m1 && wfm sigs r rm mok nx k m2
  | MRec ccs args m => rm && Nat.eqb (len_c ccs) nx && Nat.eqb (len_s args) k && all_c flat ccs
                       && wfcs sigs r mok nx k ccs && wfs sigs r mok nx k args && wfm sigs r rm mok nx k m
  | MCall f ccs args m =>
      match nth_error sigs f with
      | Some gs => Nat.eqb (len_c ccs) (sn gs) && Nat.eqb (len_s args) (sk gs) && sm gs && sr gs && negb (sw gs) && all_c shallow ccs
                   && wfcs sigs r mok nx k ccs && wfs sigs r mok nx k args && wfm sigs r rm mok nx k m
      | None => false
      end
  | MMatch _ m0 m1 => wfm sigs r rm mok nx k m0 && wfm sigs r rm mok nx k m1
  | MIfB b m1 m2 => wfb sigs r mok nx k b && wfm sigs r rm mok nx k m1 && wfm sigs r rm mok nx k m2
  | MLetB b m => wfb sigs r mok nx k b && wfm sigs r rm mok nx k m
  end.

(** a number made after memories: its numbers and memories as above, with no recursive call *)
Fixpoint wfx (sigs : list sig) (nx k : nat) (x : sx) {struct x} : bool :=
  match x with
  | XRet e => wf sigs false true nx k e
  | XLetM m x => wfm sigs false false true nx k m && wfx sigs nx k x
  | XLet e x => wf sigs false true nx k e && wfx sigs nx k x
  | XLetB b x => wfb sigs false true nx k b && wfx sigs nx k x
  | XIf _ a b x1 x2 => wf sigs false true nx k a && wf sigs false true nx k b && wfx sigs nx k x1 && wfx sigs nx k x2
  | XIfB b x1 x2 => wfb sigs false true nx k b && wfx sigs nx k x1 && wfx sigs nx k x2
  | XMatch _ x0 x1 => wfx sigs nx k x0 && wfx sigs nx k x1
  end.

Definition wf_f (sigs : list sig) (gs : sig) (b : fbody) : bool :=
  match b with
  | FRec e0 e1 => negb (Nat.eqb (sn gs) 0) && negb (sr gs) && negb (sw gs) && wf sigs false (sm gs) (Nat.pred (sn gs)) (sk gs) e0
                  && wf sigs true (sm gs) (Nat.pred (sn gs)) (sk gs) e1
  | FPlain e => negb (sr gs) && negb (sw gs) && wf sigs false (sm gs) 0 (sk gs) e
  | FRecM m0 m1 => negb (Nat.eqb (sn gs) 0) && sr gs && negb (sw gs) && sm gs && wfm sigs false false true (Nat.pred (sn gs)) (sk gs) m0
                   && wfm sigs false true true (Nat.pred (sn gs)) (sk gs) m1
  | FPlainM m => sr gs && negb (sw gs) && sm gs && wfm sigs false false true 0 (sk gs) m
  | FPlainX x => negb (sr gs) && sw gs && sm gs && wfx sigs 0 (sk gs) x
  end.

(** the function: the counters in 1 .. sn, then the numbers; the next variable holds the first counter's predecessor *)
Definition params (n k : nat) : list ident := map Pos.of_succ_nat (seq 0 (k + n)).
Definition cenv0 (n : nat) : list atom := map (fun i => Avar (Pos.of_succ_nat i)) (rev (seq 0 n)).
Definition env0 (n k : nat) : list atom := map (fun i => Avar (Pos.of_succ_nat (n + i))) (rev (seq 0 k)).
Definition pmv (gs : sig) : ident := Pos.of_succ_nat (sk gs + sn gs).

Definition compile_f (gidf : nat -> ident) (j : nat) (gs : sig) (b : fbody) : fn :=
  let mv := pmv gs in
  mkfn (params (sn gs) (sk gs))
       match b with
       | FRec e0 e1 =>
           Eif Ceq (Avar 1%positive) (Aint 0%uint63)
               (ctail gidf (gidf j) mv e0 (cenv0 (sn gs)) [] (env0 (sn gs) (sk gs)) (Pos.succ mv))
               (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63)
                    (ctail gidf (gidf j) mv e1 (Avar mv :: cenv0 (sn gs)) [] (env0 (sn gs) (sk gs)) (Pos.succ mv)))
       | FPlain e => ctail gidf (gidf j) mv e (cenv0 (sn gs)) [] (env0 (sn gs) (sk gs)) (Pos.succ mv)
       | FRecM m0 m1 =>
           Eif Ceq (Avar 1%positive) (Aint 0%uint63)
               (ctailm gidf (gidf j) mv m0 (cenv0 (sn gs)) [] (env0 (sn gs) (sk gs)) (Pos.succ mv))
               (Eop mv Bsub (Avar 1%positive) (Aint 1%uint63)
                    (ctailm gidf (gidf j) mv m1 (Avar mv :: cenv0 (sn gs)) [] (env0 (sn gs) (sk gs)) (Pos.succ mv)))
       | FPlainM m => ctailm gidf (gidf j) mv m (cenv0 (sn gs)) [] (env0 (sn gs) (sk gs)) (Pos.succ mv)
       | FPlainX x => ctailx gidf (gidf j) mv x (cenv0 (sn gs)) [] (env0 (sn gs) (sk gs)) (Pos.succ mv)
       end.

(** the bound on the counters of function [j] of a program *)
Definition cbz (j : nat) : Z := (4611686018427387904 - Z.of_nat j * 1048576)%Z.

(** what a function's theorem says, and what a caller assumes of a callee: on counters below its bound, a function giving
    back a number keeps the memory; a function giving back a memory returns 0 and leaves that memory; a function giving back a
    number that writes the memory gives it with some end memory ([runx]) *)
Definition callee_ok (P : prog) (id : ident) (B : Z) (gs : sig) (h : ftype gs) : Prop :=
  forall cvs vs M, length cvs = sn gs -> length vs = sk gs -> Forall (fun c => (Z.of_nat c < B)%Z) cvs ->
    if sw gs then exists M', runk P id (map ofn cvs ++ vs) M (calln gs h cvs vs M) M'
    else runk P id (map ofn cvs ++ vs) M (calln gs h cvs vs M) (if sr gs then callm gs h cvs vs M else M).

Definition callees_ok (P : prog) (gidf : nat -> ident) (cs : list callee) : Prop :=
  forall f, match nth_error cs f with Some (existT _ gs h) => callee_ok P (gidf f) (cbz f) gs h | None => True end.


(* ================================================================ the theorem, proved once for every syntax tree *)

(** a KQL atom whose variable, if any, is below [n] *)
Definition atom_lt (a : atom) (n : ident) : Prop := match a with Avar x => Pos.lt x n | _ => True end.
(** [rho'] has what [rho] has below [n] *)
Definition agree (rho rho' : env) (n : ident) : Prop := forall x, Pos.lt x n -> rho' ! x = rho ! x.
(** the atoms of [envA] hold the numbers of [denv], those of [cenvA] the counters of [cenv] (all read with 0 past the end) *)
Definition env_ok (rho : env) (envA : list atom) (denv : list i63) : Prop :=
  forall i, aval rho (nth i envA (Aint 0%uint63)) = Some (nth i denv 0%uint63).
Definition cenv_ok (rho : env) (cenvA : list atom) (cenv : list nat) : Prop :=
  forall i, aval rho (nth i cenvA (Aint 0%uint63)) = Some (ofn (nth i cenv O)).
(** a boolean is held as the number 1 or 0; the atoms of [benvA] hold the booleans of [benv] *)
Definition b2i (b : bool) : i63 := if b then 1%uint63 else 0%uint63.
Definition benv_ok (rho : env) (benvA : list atom) (benv : list bool) : Prop :=
  forall i, aval rho (nth i benvA (Aint 0%uint63)) = Some (b2i (nth i benv false)).
Definition lt_all (envA : list atom) (n : ident) : Prop := forall i, atom_lt (nth i envA (Aint 0%uint63)) n.
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

Lemma nth_sigs : forall (cs : list callee) f, nth_error (map (@projT1 _ _) cs) f = option_map (@projT1 _ _) (nth_error cs f).
Proof. induction cs as [|c cs IH]; intros [|f]; simpl; auto. Qed.

Lemma len_denote_es : forall cs rec cenv benv denv s es, length (denote_es cs rec cenv benv denv s es) = len_s es.
Proof. intros cs rec cenv benv denv s es. induction es; simpl; auto. Qed.

Lemma len_denote_cs : forall cs rec cenv benv denv s ccs, length (denote_cs cs rec cenv benv denv s ccs) = len_c ccs.
Proof. intros cs rec cenv benv denv s ccs. induction ccs; simpl; auto. Qed.

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
Lemma mergeable_e_spec : forall e1 e2 cs1 as1 cs2 as2, mergeable_e e1 e2 = Some (cs1, as1, cs2, as2) ->
  e1 = SRec cs1 as1 /\ e2 = SRec cs2 as2.
Proof.
  intros e1 e2 cs1 as1 cs2 as2 H. destruct e1; simpl in H; try discriminate; destruct e2; simpl in H; try discriminate.
  destruct (merge_ok _ _ _ _); [injection H as <- <- <- <-; auto | discriminate].
Qed.
Lemma mergeable_m_spec : forall m1 m2 cs1 as1 cs2 as2, mergeable_m m1 m2 = Some (cs1, as1, cs2, as2) ->
  m1 = MRec cs1 as1 MCur /\ m2 = MRec cs2 as2 MCur.
Proof.
  intros m1 m2 cs1 as1 cs2 as2 H. destruct m1; simpl in H; try discriminate. destruct m1; simpl in H; try discriminate.
  destruct m2; simpl in H; try discriminate. destruct m2; simpl in H; try discriminate.
  destruct (merge_ok _ _ _ _); [injection H as <- <- <- <-; auto | discriminate].
Qed.

(** a function without a memory never reads one: its meaning is the same for any memory *)
Lemma appn_false : forall k r (x : ntype k false r) vs s s', appn k false r x vs s = appn k false r x vs s'.
Proof. induction k as [|k IH]; intros r x vs s s'; simpl; auto. destruct vs; apply IH. Qed.

Lemma calln_nomem : forall gs h cvs vs s s', sm gs = false -> calln gs h cvs vs s = calln gs h cvs vs s'.
Proof.
  intros [x k m r] h cvs vs s s' E; simpl in E; subst m. unfold calln, callf. simpl sr.
  destruct r; simpl; try reflexivity.
  match goal with |- appn ?k false false ?y ?vs ?s = appn _ _ _ _ _ ?s' => exact (appn_false k false y vs s s') end.
Qed.

Lemma denote_nomem :
  (forall e cs rec cenv benv env s s' r nx k, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wf (map (@projT1 _ _) cs) r false nx k e = true -> denote_e cs rec cenv benv env s e = denote_e cs rec cenv benv env s' e)
  /\
  (forall es cs rec cenv benv env s s' r nx k, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wfs (map (@projT1 _ _) cs) r false nx k es = true -> denote_es cs rec cenv benv env s es = denote_es cs rec cenv benv env s' es)
  /\
  (forall c cs rec cenv benv env s s' r nx k, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wfc (map (@projT1 _ _) cs) r false nx k c = true -> denote_c cs rec cenv benv env s c = denote_c cs rec cenv benv env s' c)
  /\
  (forall ccs cs rec cenv benv env s s' r nx k, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wfcs (map (@projT1 _ _) cs) r false nx k ccs = true -> denote_cs cs rec cenv benv env s ccs = denote_cs cs rec cenv benv env s' ccs)
  /\
  (forall b cs rec cenv benv env s s' r nx k, (forall cvs l, rec cvs l s = rec cvs l s') ->
     wfb (map (@projT1 _ _) cs) r false nx k b = true -> denote_b cs rec cenv benv env s b = denote_b cs rec cenv benv env s' b).
Proof.
  apply sexp_comb.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros o a IHa b IHb cs rec cenv benv env s s' r nx k Hr W. simpl in *. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ s s' _ _ _ Hr Wa), (IHb _ _ _ _ _ s s' _ _ _ Hr Wb). reflexivity.
  - intros c a IHa b IHb t IHt e IHe cs rec cenv benv env s s' r nx k Hr W. simpl in *.
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    rewrite (IHa _ _ _ _ _ s s' _ _ _ Hr Wa), (IHb _ _ _ _ _ s s' _ _ _ Hr Wb), (IHt _ _ _ _ _ s s' _ _ _ Hr Wt),
            (IHe _ _ _ _ _ s s' _ _ _ Hr Wf). reflexivity.
  - intros e1 IH1 e2 IH2 cs rec cenv benv env s s' r nx k Hr W. simpl in *. apply andb_true_iff in W as [W1 W2].
    rewrite (IH1 _ _ _ _ _ s s' _ _ _ Hr W1). apply (IH2 _ _ _ _ _ s s' _ _ _ Hr W2).
  - intros h IHh i IHi cs rec cenv benv env s s' r nx k Hr W. simpl in W. discriminate.
  - intros ccs IHc args IHs cs rec cenv benv env s s' r nx k Hr W. simpl in *.
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    rewrite (IHc _ _ _ _ _ s s' _ _ _ Hr Wc), (IHs _ _ _ _ _ s s' _ _ _ Hr Ws). apply Hr.
  - intros fi ccs IHc args IHs cs rec cenv benv env s s' r nx k Hr W. cbn [wf] in W. rewrite nth_sigs in W. cbn [denote_e].
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wsh].
    apply andb_true_iff in W as [W Wsw]. apply andb_true_iff in W as [W Wr]. apply andb_true_iff in W as [W Wm].
    rewrite (IHc _ _ _ _ _ s s' _ _ _ Hr Wc), (IHs _ _ _ _ _ s s' _ _ _ Hr Ws). apply calln_nomem.
    destruct (sm gs); [discriminate | reflexivity].
  - intros c e0 IH0 e1 IH1 cs rec cenv benv env s s' r nx k Hr W. simpl in *. apply andb_true_iff in W as [W0 W1].
    destruct (nth c cenv O); [apply (IH0 _ _ _ _ _ s s' _ _ _ Hr W0) | apply (IH1 _ _ _ _ _ s s' _ _ _ Hr W1)].
  - intros b IHb t IHt e IHe cs rec cenv benv env s s' r nx k Hr W. simpl in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wb Wt].
    rewrite (IHb _ _ _ _ _ s s' _ _ _ Hr Wb), (IHt _ _ _ _ _ s s' _ _ _ Hr Wt), (IHe _ _ _ _ _ s s' _ _ _ Hr We). reflexivity.
  - intros b IHb e IHe cs rec cenv benv env s s' r nx k Hr W. simpl in *. apply andb_true_iff in W as [Wb We].
    rewrite (IHb _ _ _ _ _ s s' _ _ _ Hr Wb). apply (IHe _ _ _ _ _ s s' _ _ _ Hr We).
  - intros h IHh i IHi cs rec cenv benv env s s' r nx k Hr W. simpl in W. discriminate.
  - intros; reflexivity.
  - intros e IHe es IHes cs rec cenv benv env s s' r nx k Hr W. simpl in *. apply andb_true_iff in W as [We Wes].
    rewrite (IHe _ _ _ _ _ s s' _ _ _ Hr We), (IHes _ _ _ _ _ s s' _ _ _ Hr Wes). reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros c IH cs rec cenv benv env s s' r nx k Hr W. simpl in *. rewrite (IH _ _ _ _ _ s s' _ _ _ Hr W). reflexivity.
  - intros e IH cs rec cenv benv env s s' r nx k Hr W. simpl in *. rewrite (IH _ _ _ _ _ s s' _ _ _ Hr W). reflexivity.
  - intros; reflexivity.
  - intros c IHc ccs IHs cs rec cenv benv env s s' r nx k Hr W. simpl in *. apply andb_true_iff in W as [Wc Ws].
    rewrite (IHc _ _ _ _ _ s s' _ _ _ Hr Wc), (IHs _ _ _ _ _ s s' _ _ _ Hr Ws). reflexivity.
  - intros c x IHx y IHy cs rec cenv benv env s s' r nx k Hr W. simpl in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ s s' _ _ _ Hr Wx), (IHy _ _ _ _ _ s s' _ _ _ Hr Wy). reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros x IHx y IHy cs rec cenv benv env s s' r nx k Hr W. simpl in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ s s' _ _ _ Hr Wx), (IHy _ _ _ _ _ s s' _ _ _ Hr Wy). reflexivity.
  - intros x IHx y IHy cs rec cenv benv env s s' r nx k Hr W. simpl in *. apply andb_true_iff in W as [Wx Wy].
    rewrite (IHx _ _ _ _ _ s s' _ _ _ Hr Wx), (IHy _ _ _ _ _ s s' _ _ _ Hr Wy). reflexivity.
  - intros x IHx cs rec cenv benv env s s' r nx k Hr W. simpl in *. rewrite (IHx _ _ _ _ _ s s' _ _ _ Hr W). reflexivity.
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

Section Sim.
Variables (P : prog) (f : fn) (gidf : nat -> ident) (g mv : ident).
Variables (cs : list callee) (r rm hp mok : bool) (nx k j : nat).
Variables (rec : list nat -> list i63 -> mem -> i63) (recm : list nat -> list i63 -> mem -> mem) (cm : nat).
(** the recursive call, where it is allowed, computes [rec] (or [recm], giving back a memory) on counters below the bound;
    the callees compute their meanings on counters below theirs; this function comes after its callees and is not one of
    the last 2^40 *)
Hypothesis Hrec : r = true -> forall cvs vs M, length cvs = nx -> length vs = k -> Forall (fun c => (Z.of_nat c < cbz j)%Z) cvs ->
  runk P g (ofn cm :: map ofn cvs ++ vs) M (rec cvs vs M) M.
Hypothesis Hrecm : rm = true -> forall cvs vs M, length cvs = nx -> length vs = k -> Forall (fun c => (Z.of_nat c < cbz j)%Z) cvs ->
  runk P g (ofn cm :: map ofn cvs ++ vs) M 0%uint63 (recm cvs vs M).
Hypothesis Hrhp : r = true -> hp = true.
Hypothesis Hrmhp : rm = true -> hp = true.
Hypothesis Hcs : callees_ok P gidf cs.
Hypothesis Hlen : (length cs <= j)%nat.
Hypothesis Hj : (Z.of_nat j < 1099511627776)%Z.

Let sigs := map (@projT1 _ _) cs.

Lemma cbz_big : (1152921504606846976 + 1048576 < cbz j)%Z.
Proof. unfold cbz. lia. Qed.

Lemma cbz_small : (cbz j + 1048576 < wB)%Z.
Proof. rewrite KQMAuto.wB_num. unfold cbz. lia. Qed.

Lemma cbz_mono : forall fi, (fi < j)%nat -> (cbz j + 1048576 <= cbz fi)%Z.
Proof. intros fi L. unfold cbz. lia. Qed.

Definition inv (rho : env) (cenvA benvA envA : list atom) (cenv : list nat) (benv : list bool) (denv : list i63) (nxt : ident)
  : Prop :=
  env_ok rho envA denv /\ lt_all envA nxt /\ cenv_ok rho cenvA cenv /\ lt_all cenvA nxt /\ benv_ok rho benvA benv /\
  lt_all benvA nxt /\ cbound (cbz j) cenv /\ Pos.lt mv nxt /\ (hp = true -> rho ! mv = Some (ofn cm) /\ (Z.of_nat cm < cbz j)%Z).

Lemma inv_step : forall rho rho' cenvA benvA envA cenv benv denv nxt n', inv rho cenvA benvA envA cenv benv denv nxt ->
  agree rho rho' nxt -> Pos.le nxt n' -> inv rho' cenvA benvA envA cenv benv denv n'.
Proof.
  intros rho rho' cenvA benvA envA cenv benv denv nxt n' (E & L & C & LC & Bv & LBv & B & Mv & H) A Le.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - eapply env_ok_agree; eauto.
  - eapply lt_all_mono; eauto.
  - eapply cenv_ok_agree; eauto.
  - eapply lt_all_mono; eauto.
  - eapply benv_ok_agree; eauto.
  - eapply lt_all_mono; eauto.
  - exact B.
  - lia.
  - intro Hh. destruct (H Hh) as [H1 H2]. split; [rewrite A by lia; exact H1 | exact H2].
Qed.

Lemma inv_let : forall rho cenvA benvA envA cenv benv denv n1 a x, inv rho cenvA benvA envA cenv benv denv n1 ->
  aval rho a = Some x -> atom_lt a n1 -> inv rho cenvA benvA (a :: envA) cenv benv (x :: denv) n1.
Proof.
  intros rho cenvA benvA envA cenv benv denv n1 a x (E & L & C & LC & Bv & LBv & B & Mv & H) V La.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; auto using env_ok_cons, lt_all_cons.
Qed.

Lemma inv_blet : forall rho cenvA benvA envA cenv benv denv n1 a x, inv rho cenvA benvA envA cenv benv denv n1 ->
  aval rho a = Some (b2i x) -> atom_lt a n1 -> inv rho cenvA (a :: benvA) envA cenv (x :: benv) denv n1.
Proof.
  intros rho cenvA benvA envA cenv benv denv n1 a x (E & L & C & LC & Bv & LBv & B & Mv & H) V La.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; auto using benv_ok_cons, lt_all_cons.
Qed.

Lemma inv_cpush : forall rho cenvA benvA envA cenv benv denv nxt p, inv rho cenvA benvA envA cenv benv denv nxt ->
  (Z.of_nat p < cbz j)%Z ->
  inv (PTree.set nxt (ofn p) rho) (Avar nxt :: cenvA) benvA envA (p :: cenv) benv denv (Pos.succ nxt).
Proof.
  intros rho cenvA benvA envA cenv benv denv nxt p (E & L & C & LC & Bv & LBv & B & Mv & H) Bp.
  assert (A : agree rho (PTree.set nxt (ofn p) rho) nxt) by (apply agree_set; lia).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - eapply env_ok_agree; eauto.
  - eapply lt_all_mono; eauto. lia.
  - apply cenv_ok_cons; [eapply cenv_ok_agree; eauto | simpl; apply PTree.gss].
  - apply lt_all_cons; [eapply lt_all_mono; eauto; lia | simpl; lia].
  - eapply benv_ok_agree; eauto.
  - eapply lt_all_mono; eauto. lia.
  - apply cbound_cons; auto.
  - lia.
  - intro Hh. destruct (H Hh) as [H1 H2]. split; [rewrite A by lia; exact H1 | exact H2].
Qed.

(** a counter's value: its variables below the bound, each successor adds one, [kq_nat] is at most 2^60 *)
Lemma denote_c_bound : forall c cenv benv denv M, cbound (cbz j) cenv ->
  (Z.of_nat (denote_c cs rec cenv benv denv M c) < cbz j + Z.of_nat (cdepth c))%Z.
Proof.
  induction c as [i | | c IH | e]; intros cenv benv denv M B; simpl.
  - specialize (B i). lia.
  - pose proof cbz_big. lia.
  - specialize (IH cenv benv denv M B). lia.
  - pose proof (KQMAuto.kq_nat_le (denote_e cs rec cenv benv denv M e)) as K60. change (2 ^ 60)%Z with 1152921504606846976%Z in K60.
    pose proof cbz_big. lia.
Qed.

Lemma flat_shallow : forall ccs, all_c flat ccs = true -> all_c shallow ccs = true.
Proof.
  induction ccs as [|c ccs IH]; simpl; auto. intros F. apply andb_true_iff in F as [F1 F2].
  rewrite IH by auto. unfold flat in F1. apply Nat.eqb_eq in F1. unfold shallow. rewrite F1. reflexivity.
Qed.

Lemma cs_flat_bound : forall ccs cenv benv denv M, all_c flat ccs = true -> cbound (cbz j) cenv ->
  Forall (fun c => (Z.of_nat c < cbz j)%Z) (denote_cs cs rec cenv benv denv M ccs).
Proof.
  induction ccs as [|c ccs IH]; intros cenv benv denv M F B; simpl in *; constructor.
  - apply andb_true_iff in F as [F1 F2]. unfold flat in F1. apply Nat.eqb_eq in F1.
    pose proof (denote_c_bound c cenv benv denv M B) as D. rewrite F1 in D. simpl in D. lia.
  - apply andb_true_iff in F as [F1 F2]. apply IH; auto.
Qed.

Lemma cs_shallow_bound : forall ccs cenv benv denv M fi, all_c shallow ccs = true -> cbound (cbz j) cenv -> (fi < j)%nat ->
  Forall (fun c => (Z.of_nat c < cbz fi)%Z) (denote_cs cs rec cenv benv denv M ccs).
Proof.
  induction ccs as [|c ccs IH]; intros cenv benv denv M fi F B L; simpl in *; constructor.
  - apply andb_true_iff in F as [F1 F2]. unfold shallow in F1. apply Z.leb_le in F1.
    pose proof (denote_c_bound c cenv benv denv M B) as D. pose proof (cbz_mono fi L). lia.
  - apply andb_true_iff in F as [F1 F2]. apply IH; auto.
Qed.

Lemma cexp_all :
  (forall e cenvA benvA envA cenv benv denv nxt K rho M v M', wf sigs r mok nx k e = true -> inv rho cenvA benvA envA cenv benv denv nxt ->
     (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' -> aval rho' a = Some (denote_e cs rec cenv benv denv M e) ->
        evalk P f rho' M (K a n') v M') ->
     evalk P f rho M (cexp gidf g mv e cenvA benvA envA nxt K) v M')
  /\
  (forall es cenvA benvA envA cenv benv denv nxt K rho M v M', wfs sigs r mok nx k es = true -> inv rho cenvA benvA envA cenv benv denv nxt ->
     (forall rho' n' As, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') As ->
        avals rho' As = Some (denote_es cs rec cenv benv denv M es) -> evalk P f rho' M (K As n') v M') ->
     evalk P f rho M (cexps gidf g mv es cenvA benvA envA nxt K) v M')
  /\
  (forall c cenvA benvA envA cenv benv denv nxt K rho M v M', wfc sigs r mok nx k c = true -> (Z.of_nat (cdepth c) <= 1048576)%Z ->
     inv rho cenvA benvA envA cenv benv denv nxt ->
     (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' ->
        aval rho' a = Some (ofn (denote_c cs rec cenv benv denv M c)) -> evalk P f rho' M (K a n') v M') ->
     evalk P f rho M (ccnt gidf g mv c cenvA benvA envA nxt K) v M')
  /\
  (forall ccs cenvA benvA envA cenv benv denv nxt K rho M v M', wfcs sigs r mok nx k ccs = true -> all_c shallow ccs = true ->
     inv rho cenvA benvA envA cenv benv denv nxt ->
     (forall rho' n' Cs, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') Cs ->
        avals rho' Cs = Some (map ofn (denote_cs cs rec cenv benv denv M ccs)) -> evalk P f rho' M (K Cs n') v M') ->
     evalk P f rho M (ccnts gidf g mv ccs cenvA benvA envA nxt K) v M')
  /\
  (forall b,
    (forall cenvA benvA envA cenv benv denv nxt KT KF rho M v M', wfb sigs r mok nx k b = true ->
       inv rho cenvA benvA envA cenv benv denv nxt ->
       (denote_b cs rec cenv benv denv M b = true -> forall rho' n', agree rho rho' nxt -> Pos.le nxt n' -> evalk P f rho' M (KT n') v M') ->
       (denote_b cs rec cenv benv denv M b = false -> forall rho' n', agree rho rho' nxt -> Pos.le nxt n' -> evalk P f rho' M (KF n') v M') ->
       evalk P f rho M (ccond gidf g mv b cenvA benvA envA nxt KT KF) v M')
    /\
    (forall cenvA benvA envA cenv benv denv nxt K rho M v M', wfb sigs r mok nx k b = true ->
       inv rho cenvA benvA envA cenv benv denv nxt ->
       (forall rho' n' a, agree rho rho' nxt -> Pos.le nxt n' -> atom_lt a n' ->
          aval rho' a = Some (b2i (denote_b cs rec cenv benv denv M b)) -> evalk P f rho' M (K a n') v M') ->
       evalk P f rho M (cbval gidf g mv b cenvA benvA envA nxt K) v M')).
Proof.
  apply sexp_comb.
  - (* SVar *) intros i cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl.
    destruct Iv as (E & L & _). apply HK; [apply agree_refl | lia | apply L | apply E].
  - (* SInt *) intros n cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl.
    apply HK; [apply agree_refl | lia | exact Logic.I | reflexivity].
  - (* SOp *) intros o a IHa b IHb cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [Wa Wb].
    apply IHa with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHb with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_op.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SIf *) intros c a IHa b IHb t IHt e IHe cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt]. apply andb_true_iff in W as [Wa Wb].
    apply IHa with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHb with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv rho2 cenvA benvA envA cenv benv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    destruct (choice_ok t e) eqn:CH.
    { (* both numbers worked out, one taken by a conditional move *)
      apply IHt with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho3 n3 T A3 Le3 LT VT.
      apply IHe with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
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
          destruct (cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)); reflexivity. }
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + destruct (cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)) eqn:C.
      * apply IHt with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho3 n3 a3 A3 Le3 L3 V3.
        apply HK; [| lia | exact L3 | exact V3].
        eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia.
      * apply IHe with (cenv := cenv) (benv := benv) (denv := denv); auto.
        { eapply inv_step; [exact I2 | apply agree_refl | afterle]. }
        intros rho3 n3 a3 A3 Le3 L3 V3.
        apply HK; [| lia_a | exact L3 | exact V3].
        eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); [eauto | eauto | eapply agree_mono; [exact A3 | afterle] | lia | lia].
  - (* SLet *) intros e1 IH1 e2 IH2 cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W1 W2].
    apply IH1 with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH2 with (cenv := cenv) (benv := benv) (denv := denote_e cs rec cenv benv denv M e1 :: denv); auto.
    + apply inv_let; auto. eapply inv_step; eauto.
    + intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | exact V2].
  - (* SRd *) intros h IHh i IHi cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    apply IHh with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 H A1 Le1 LH VH.
    apply IHi with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 J A2 Le2 LJ VJ.
    eapply K_ld.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SRec *) intros ccs IHc args IHs cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfl].
    apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply IHc with (cenv := cenv) (benv := benv) (denv := denv); auto. { apply flat_shallow; auto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA envA cenv benv denv nxt n1 Iv A1 Le1) as I1.
    apply IHs with (cenv := cenv) (benv := benv) (denv := denv); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    destruct (Hrec Wr (denote_cs cs rec cenv benv denv M ccs) (denote_es cs rec cenv benv denv M args) M) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). apply cs_flat_bound; auto. }
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1). destruct (H1 (Hrhp Wr)) as [Rm _].
    eapply K_call; eauto.
    + simpl. rewrite (A2 mv Mv1), Rm.
      rewrite (avals_app rho2 Cs As _ _ (eq_trans (avals_agree rho1 rho2 n1 Cs A2 LCs) VCs) VAs). reflexivity.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SCall *) intros fi ccs IHc args IHs cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    unfold sigs in W. rewrite nth_sigs in W. pose proof (Hcs fi) as Hc.
    unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    assert (Hfi : (fi < j)%nat).
    { assert (fi < length cs)%nat by (apply nth_error_Some; rewrite E; discriminate). lia. }
    apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wsh].
    apply andb_true_iff in W as [W Wsw].
    apply andb_true_iff in W as [W Wr]. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [Wn Wk].
    assert (Hc2 : forall cvs0 vs0 M0, length cvs0 = sn gs -> length vs0 = sk gs -> Forall (fun c => (Z.of_nat c < cbz fi)%Z) cvs0 ->
              runk P (gidf fi) (map ofn cvs0 ++ vs0) M0 (calln gs h cvs0 vs0 M0) (if sr gs then callm gs h cvs0 vs0 M0 else M0)).
    { intros cvs0 vs0 M0 L1 L2 L3. pose proof (Hc cvs0 vs0 M0 L1 L2 L3) as H0. destruct (sw gs); [discriminate Wsw | exact H0]. }
    apply IHc with (cenv := cenv) (benv := benv) (denv := denv); auto.
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA envA cenv benv denv nxt n1 Iv A1 Le1) as I1.
    apply IHs with (cenv := cenv) (benv := benv) (denv := denv); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    destruct (Hc2 (denote_cs cs rec cenv benv denv M ccs) (denote_es cs rec cenv benv denv M args) M) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). apply cs_shallow_bound; auto. }
    destruct (sr gs); [discriminate Wr|].
    eapply K_call; eauto.
    + apply avals_app; [rewrite (avals_agree rho1 rho2 n1 Cs A2 LCs); exact VCs | exact VAs].
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SMatch *) intros c e0 IH0 e1 IH1 cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H).
    destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl.
      apply IH0 with (cenv := cenv) (benv := benv) (denv := denv); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbz j)%Z) by (specialize (Cb c); rewrite Ec in Cb; exact Cb).
      pose proof cbz_small as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (cenv := p :: cenv) (benv := benv) (denv := denv); auto.
      * apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | lia].
      * intros rho3 n3 a3 A3 Le3 L3 V3. apply HK; [ | lia_a | exact L3 | exact V3 ].
        refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
  - (* SIfB *) intros b IHb t IHt e IHe cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wb Wt]. destruct IHb as [IHc IHv].
    destruct (choice_ok t e) eqn:CH.
    + (* both numbers worked out, one taken by a conditional move on the boolean's value *)
      apply IHv with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 C A1 Le1 LC VC.
      apply IHt with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
      intros rho2 n2 T A2 Le2 LT VT.
      apply IHe with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      intros rho3 n3 F A3 Le3 LF VF.
      assert (LC2 : atom_lt C n2) by (eapply atom_lt_mono; [exact LC | lia]).
      eapply K_sel.
      * rewrite (aval_agree rho2 rho3 n2 C A3 LC2), (aval_agree rho1 rho2 n1 C A2 LC). exact VC.
      * reflexivity.
      * exact VF.
      * rewrite (aval_agree rho2 rho3 n2 T A3 LT). exact VT.
      * apply HK.
        -- apply (agree_set2 rho rho2 rho3 n3 _ nxt n2); [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | exact A3 | lia | lia].
        -- lia.
        -- simpl. lia.
        -- simpl. rewrite PTree.gss. destruct (denote_b cs rec cenv benv denv M b); reflexivity.
    + (* jumps *)
      apply IHc with (cenv := cenv) (benv := benv) (denv := denv); auto.
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        apply IHt with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
        intros rho2 n2 a2 A2 Le2 L2 V2.
        apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | rewrite Hb; exact V2].
      * intros Hb rho1 n1 A1 Le1. cbv beta.
        apply IHe with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
        intros rho2 n2 a2 A2 Le2 L2 V2.
        apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | rewrite Hb; exact V2].
  - (* SLetB *) intros b IHb e IHe cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [Wb We]. destruct IHb as [_ IHv].
    apply IHv with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHe with (cenv := cenv) (benv := denote_b cs rec cenv benv denv M b :: benv) (denv := denv); auto.
    + apply inv_blet; auto. eapply inv_step; eauto.
    + intros rho2 n2 a2 A2 Le2 L2 V2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia | exact L2 | exact V2].
  - (* SRd32 *) intros h IHh i IHi cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [W Wi]. apply andb_true_iff in W as [_ Wh].
    apply IHh with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 H A1 Le1 LH VH.
    apply IHi with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 J A2 Le2 LJ VJ.
    eapply K_ld32.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + apply HK.
      * eapply (agree_set2 rho rho1 rho2); eauto; lia.
      * lia.
      * simpl. lia.
      * simpl. rewrite PTree.gss. reflexivity.
  - (* SNil *) intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl. apply HK; [apply agree_refl | lia | constructor | reflexivity].
  - (* SCons *) intros e IHe es IHes cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. simpl in *.
    apply andb_true_iff in W as [We Wes].
    apply IHe with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IHes with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 As A2 Le2 LAs VAs. apply HK.
    + eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
    + lia.
    + constructor; auto. eapply atom_lt_mono; eauto.
    + simpl. rewrite (aval_agree rho1 rho2 n1), VA, VAs; auto.
  - (* CVar *) intros i cenvA benvA envA cenv benv denv nxt K rho M v M' W D Iv HK. simpl.
    destruct Iv as (_ & _ & C & LC & _). apply HK; [apply agree_refl | lia | apply LC | apply C].
  - (* CO *) intros cenvA benvA envA cenv benv denv nxt K rho M v M' W D Iv HK. simpl.
    apply HK; [apply agree_refl | lia | exact Logic.I | exact (f_equal Some (eq_sym ofn_0))].
  - (* CS *) intros c IH cenvA benvA envA cenv benv denv nxt K rho M v M' W D Iv HK. simpl in *.
    pose proof Iv as (_ & _ & _ & _ & _ & _ & Cb & _).
    pose proof (denote_c_bound c cenv benv denv M Cb) as Dc. pose proof cbz_small as Sm.
    apply IH with (cenv := cenv) (benv := benv) (denv := denv); auto. { lia. }
    intros rho1 n1 A A1 Le1 LA VA.
    eapply K_op; [exact VA | reflexivity | ].
    apply HK.
    + eapply (agree_set1 rho rho1); eauto; lia.
    + lia.
    + simpl. lia.
    + simpl. rewrite PTree.gss. simpl binop_sem. rewrite ofn_succ by lia. reflexivity.
  - (* CNat *) intros e IH cenvA benvA envA cenv benv denv nxt K rho M v M' W D Iv HK. simpl in *.
    apply IH with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    eapply K_sel; [exact VA | reflexivity | reflexivity | exact VA | ].
    eapply K_sel; [reflexivity | simpl; rewrite PTree.gss; reflexivity | reflexivity | simpl; rewrite PTree.gss; reflexivity | ].
    apply HK.
    + apply agree_set1; [apply agree_set1; [exact A1 | lia] | lia].
    + lia.
    + simpl. lia.
    + simpl. rewrite PTree.gss. rewrite ofn_kq_nat. reflexivity.
  - (* CNil *) intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Sh Iv HK. simpl.
    apply HK; [apply agree_refl | lia | constructor | reflexivity].
  - (* CCons *) intros c IHc ccs IHs cenvA benvA envA cenv benv denv nxt K rho M v M' W Sh Iv HK. simpl in *.
    apply andb_true_iff in W as [Wc Ws]. apply andb_true_iff in Sh as [Sh1 Sh2].
    apply IHc with (cenv := cenv) (benv := benv) (denv := denv); auto. { unfold shallow in Sh1. apply Z.leb_le in Sh1. exact Sh1. }
    intros rho1 n1 A A1 Le1 LA VA.
    apply IHs with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 As A2 Le2 LAs VAs. apply HK.
    + eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
    + lia.
    + constructor; auto. eapply atom_lt_mono; eauto.
    + simpl. rewrite (aval_agree rho1 rho2 n1), VA, VAs; auto.
  - (* BCmp *) intros c x IHx y IHy. split.
    + intros cenvA benvA envA cenv benv denv nxt KT KF rho M v M' W Iv HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHx with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHy with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      eapply K_if.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * destruct (cmp_sem c (denote_e cs rec cenv benv denv M x) (denote_e cs rec cenv benv denv M y)) eqn:C.
        -- apply HT; [exact C | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
        -- apply HF; [exact C | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia_a].
    + intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHx with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHy with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
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
  - (* BVar *) intros i. split.
    + intros cenvA benvA envA cenv benv denv nxt KT KF rho M v M' W Iv HT HF. cbn [ccond].
      pose proof Iv as (_ & _ & _ & _ & Bv & _).
      eapply K_if; [apply Bv | reflexivity | ]. rewrite b2i_eq0.
      destruct (nth i benv false) eqn:Eb; simpl.
      * apply HT; [exact Eb | apply agree_refl | lia_a].
      * apply HF; [exact Eb | apply agree_refl | lia].
    + intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. cbn [cbval].
      pose proof Iv as (_ & _ & _ & _ & Bv & LBv & _).
      apply HK; [apply agree_refl | lia | apply LBv | apply Bv].
  - (* BTrue *) split.
    + intros cenvA benvA envA cenv benv denv nxt KT KF rho M v M' W Iv HT HF. cbn [ccond].
      apply HT; [reflexivity | apply agree_refl | lia].
    + intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. cbn [cbval].
      apply HK; [apply agree_refl | lia | exact Logic.I | reflexivity].
  - (* BFalse *) split.
    + intros cenvA benvA envA cenv benv denv nxt KT KF rho M v M' W Iv HT HF. cbn [ccond].
      apply HF; [reflexivity | apply agree_refl | lia].
    + intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. cbn [cbval].
      apply HK; [apply agree_refl | lia | exact Logic.I | reflexivity].
  - (* BAnd *) intros x IHx y IHy. destruct IHx as [IHxc IHxv]. destruct IHy as [IHyc IHyv]. split.
    + intros cenvA benvA envA cenv benv denv nxt KT KF rho M v M' W Iv HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHxc with (cenv := cenv) (benv := benv) (denv := denv); auto.
      * intros Hx rho1 n1 A1 Le1. cbv beta.
        apply IHyc with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
        -- intros Hy rho2 n2 A2 Le2.
           apply HT; [simpl; rewrite Hx, Hy; reflexivity | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
        -- intros Hy rho2 n2 A2 Le2.
           apply HF; [simpl; rewrite Hx, Hy; reflexivity | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
      * intros Hx rho1 n1 A1 Le1. apply HF; [simpl; rewrite Hx; reflexivity | exact A1 | exact Le1].
    + intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHxv with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHyv with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      eapply K_op.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * apply HK.
        -- eapply (agree_set2 rho rho1 rho2); eauto; lia.
        -- lia.
        -- simpl. lia.
        -- cbn [aval]. rewrite PTree.gss, b2i_land. reflexivity.
  - (* BOr *) intros x IHx y IHy. destruct IHx as [IHxc IHxv]. destruct IHy as [IHyc IHyv]. split.
    + intros cenvA benvA envA cenv benv denv nxt KT KF rho M v M' W Iv HT HF. cbn [ccond]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHxc with (cenv := cenv) (benv := benv) (denv := denv); auto.
      * intros Hx rho1 n1 A1 Le1. apply HT; [simpl; rewrite Hx; reflexivity | exact A1 | exact Le1].
      * intros Hx rho1 n1 A1 Le1. cbv beta.
        apply IHyc with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
        -- intros Hy rho2 n2 A2 Le2.
           apply HT; [simpl; rewrite Hx, Hy; reflexivity | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
        -- intros Hy rho2 n2 A2 Le2.
           apply HF; [simpl; rewrite Hx, Hy; reflexivity | eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. cbn [cbval]. cbn [wfb] in W.
      apply andb_true_iff in W as [Wx Wy].
      apply IHxv with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
      apply IHyv with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
      intros rho2 n2 B A2 Le2 LB VB.
      eapply K_op.
      * rewrite (aval_agree rho1 rho2 n1); eauto.
      * eauto.
      * apply HK.
        -- eapply (agree_set2 rho rho1 rho2); eauto; lia.
        -- lia.
        -- simpl. lia.
        -- cbn [aval]. rewrite PTree.gss, b2i_lor. reflexivity.
  - (* BNot *) intros x IHx. destruct IHx as [IHxc IHxv]. split.
    + intros cenvA benvA envA cenv benv denv nxt KT KF rho M v M' W Iv HT HF. cbn [ccond]. cbn [wfb] in W.
      apply IHxc with (cenv := cenv) (benv := benv) (denv := denv); auto.
      * intros Hx. apply HF. simpl. rewrite Hx. reflexivity.
      * intros Hx. apply HT. simpl. rewrite Hx. reflexivity.
    + intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK. cbn [cbval]. cbn [wfb] in W.
      apply IHxv with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
      eapply K_op; [exact VA | reflexivity | ].
      apply HK.
      * apply agree_set1; [exact A1 | lia].
      * lia.
      * simpl. lia.
      * cbn [aval]. rewrite PTree.gss, b2i_lxor. reflexivity.
Qed.

Definition cexp_ok := proj1 cexp_all.
Definition cexps_ok := proj1 (proj2 cexp_all).
Definition ccnts_ok := proj1 (proj2 (proj2 (proj2 cexp_all))).
Definition ccond_ok := fun b => proj1 (proj2 (proj2 (proj2 (proj2 cexp_all))) b).
Definition cbval_ok := fun b => proj2 (proj2 (proj2 (proj2 (proj2 cexp_all))) b).
Definition ccnt_ok := proj1 (proj2 (proj2 cexp_all)).

(** the arguments of two calls chosen by the test [A c B]: each pair worked out, a pair the same worked out once *)
Lemma cmerge_s_ok : forall es1 es2 c A B va vb cenvA benvA envA cenv benv denv nxt K rho M v M',
  wfs sigs r mok nx k es1 = true -> wfs sigs r mok nx k es2 = true -> len_s es1 = len_s es2 ->
  inv rho cenvA benvA envA cenv benv denv nxt -> aval rho A = Some va -> aval rho B = Some vb -> atom_lt A nxt -> atom_lt B nxt ->
  (forall rho' n' Xs, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') Xs ->
     avals rho' Xs = Some (if cmp_sem c va vb then denote_es cs rec cenv benv denv M es1 else denote_es cs rec cenv benv denv M es2) ->
     evalk P f rho' M (K Xs n') v M') ->
  evalk P f rho M (cmerge_s gidf g mv c A B es1 es2 cenvA benvA envA nxt K) v M'.
Proof.
  induction es1 as [|e1 r1 IH]; intros es2 c A B va vb cenvA benvA envA cenv benv denv nxt K rho M v M' W1 W2 L Iv VA VB LA LB HK;
    destruct es2 as [|e2 r2]; simpl in L; try discriminate; cbn [cmerge_s].
  - apply HK; [apply agree_refl | lia | constructor | destruct (cmp_sem c va vb); reflexivity].
  - injection L as L. cbn [wfs] in W1, W2. apply andb_true_iff in W1 as [We1 Wr1]. apply andb_true_iff in W2 as [We2 Wr2].
    destruct (same_e e1 e2) eqn:SE.
    + apply same_e_eq in SE. subst e2.
      apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 X A1 Le1 LX VX.
      apply (IH r2 c A B va vb cenvA benvA envA cenv benv denv n1 _ rho1 M v M' Wr1 Wr2 L).
      * eapply inv_step; eauto.
      * rewrite (aval_agree rho rho1 nxt A A1 LA). exact VA.
      * rewrite (aval_agree rho rho1 nxt B A1 LB). exact VB.
      * eapply atom_lt_mono; eauto.
      * eapply atom_lt_mono; eauto.
      * intros rho2 n2 Xs A2 Le2 LXs VXs. apply HK.
        -- eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
        -- lia.
        -- constructor; [eapply atom_lt_mono; [exact LX | lia] | exact LXs].
        -- cbn [avals denote_es]. rewrite (aval_agree rho1 rho2 n1 X A2 LX), VX, VXs.
           destruct (cmp_sem c va vb); reflexivity.
    + apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 X A1 Le1 LX VX.
      apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
      intros rho2 n2 Y A2 Le2 LY VY.
      assert (A12 : agree rho rho2 nxt) by (eapply (agree_trans rho rho1 rho2 nxt n1); eauto).
      eapply K_sel.
      * rewrite (aval_agree rho rho2 nxt A A12 LA). exact VA.
      * rewrite (aval_agree rho rho2 nxt B A12 LB). exact VB.
      * rewrite (aval_agree rho1 rho2 n1 X A2 LX). exact VX.
      * exact VY.
      * assert (A3 : agree rho (PTree.set n2 (if cmp_sem c va vb then denote_e cs rec cenv benv denv M e1
                                                 else denote_e cs rec cenv benv denv M e2) rho2) nxt)
          by (apply agree_set1; [exact A12 | lia]).
        apply (IH r2 c A B va vb cenvA benvA envA cenv benv denv (Pos.succ n2) _ _ M v M' Wr1 Wr2 L).
        -- eapply inv_step; [exact Iv | exact A3 | lia].
        -- rewrite (aval_agree rho _ nxt A A3 LA). exact VA.
        -- rewrite (aval_agree rho _ nxt B A3 LB). exact VB.
        -- eapply atom_lt_mono; [exact LA | lia].
        -- eapply atom_lt_mono; [exact LB | lia].
        -- intros rho4 n4 Xs A4 Le4 LXs VXs. apply HK.
           ++ eapply (agree_trans rho _ rho4 nxt (Pos.succ n2)); [exact A3 | exact A4 | lia].
           ++ lia.
           ++ constructor; [simpl; lia | exact LXs].
           ++ cbn [avals aval denote_es]. rewrite (A4 n2) by lia. rewrite PTree.gss, VXs.
              destruct (cmp_sem c va vb); reflexivity.
Qed.

(** the same for counters (the recursive call's: no successor in them) *)
Lemma cmerge_c_ok : forall cs1 cs2 c A B va vb cenvA benvA envA cenv benv denv nxt K rho M v M',
  wfcs sigs r mok nx k cs1 = true -> wfcs sigs r mok nx k cs2 = true -> all_c flat cs1 = true -> all_c flat cs2 = true ->
  len_c cs1 = len_c cs2 ->
  inv rho cenvA benvA envA cenv benv denv nxt -> aval rho A = Some va -> aval rho B = Some vb -> atom_lt A nxt -> atom_lt B nxt ->
  (forall rho' n' Xs, agree rho rho' nxt -> Pos.le nxt n' -> Forall (fun a => atom_lt a n') Xs ->
     avals rho' Xs = Some (map ofn (if cmp_sem c va vb then denote_cs cs rec cenv benv denv M cs1 else denote_cs cs rec cenv benv denv M cs2)) ->
     evalk P f rho' M (K Xs n') v M') ->
  evalk P f rho M (cmerge_c gidf g mv c A B cs1 cs2 cenvA benvA envA nxt K) v M'.
Proof.
  induction cs1 as [|c1 r1 IH]; intros cs2 c A B va vb cenvA benvA envA cenv benv denv nxt K rho M v M' W1 W2 F1 F2 L Iv VA VB LA LB HK;
    destruct cs2 as [|c2 r2]; simpl in L; try discriminate; cbn [cmerge_c].
  - apply HK; [apply agree_refl | lia | constructor | destruct (cmp_sem c va vb); reflexivity].
  - injection L as L. cbn [wfcs all_c] in W1, W2, F1, F2.
    apply andb_true_iff in W1 as [Wc1 Wr1]. apply andb_true_iff in W2 as [Wc2 Wr2].
    apply andb_true_iff in F1 as [Fc1 Fr1]. apply andb_true_iff in F2 as [Fc2 Fr2].
    unfold flat in Fc1, Fc2. apply Nat.eqb_eq in Fc1, Fc2.
    assert (D1 : (Z.of_nat (cdepth c1) <= 1048576)%Z) by (rewrite Fc1; simpl; lia).
    assert (D2 : (Z.of_nat (cdepth c2) <= 1048576)%Z) by (rewrite Fc2; simpl; lia).
    destruct (same_c c1 c2) eqn:SE.
    + apply same_c_eq in SE. subst c2.
      apply ccnt_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 X A1 Le1 LX VX.
      apply (IH r2 c A B va vb cenvA benvA envA cenv benv denv n1 _ rho1 M v M' Wr1 Wr2 Fr1 Fr2 L).
      * eapply inv_step; eauto.
      * rewrite (aval_agree rho rho1 nxt A A1 LA). exact VA.
      * rewrite (aval_agree rho rho1 nxt B A1 LB). exact VB.
      * eapply atom_lt_mono; eauto.
      * eapply atom_lt_mono; eauto.
      * intros rho2 n2 Xs A2 Le2 LXs VXs. apply HK.
        -- eapply (agree_trans rho rho1 rho2 nxt n1); eauto.
        -- lia.
        -- constructor; [eapply atom_lt_mono; [exact LX | lia] | exact LXs].
        -- cbn [avals denote_cs map]. rewrite (aval_agree rho1 rho2 n1 X A2 LX), VX, VXs.
           destruct (cmp_sem c va vb); reflexivity.
    + apply ccnt_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 X A1 Le1 LX VX.
      apply ccnt_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
      intros rho2 n2 Y A2 Le2 LY VY.
      assert (A12 : agree rho rho2 nxt) by (eapply (agree_trans rho rho1 rho2 nxt n1); eauto).
      eapply K_sel.
      * rewrite (aval_agree rho rho2 nxt A A12 LA). exact VA.
      * rewrite (aval_agree rho rho2 nxt B A12 LB). exact VB.
      * rewrite (aval_agree rho1 rho2 n1 X A2 LX). exact VX.
      * exact VY.
      * assert (A3 : agree rho (PTree.set n2 (if cmp_sem c va vb then ofn (denote_c cs rec cenv benv denv M c1)
                                                 else ofn (denote_c cs rec cenv benv denv M c2)) rho2) nxt)
          by (apply agree_set1; [exact A12 | lia]).
        apply (IH r2 c A B va vb cenvA benvA envA cenv benv denv (Pos.succ n2) _ _ M v M' Wr1 Wr2 Fr1 Fr2 L).
        -- eapply inv_step; [exact Iv | exact A3 | lia].
        -- rewrite (aval_agree rho _ nxt A A3 LA). exact VA.
        -- rewrite (aval_agree rho _ nxt B A3 LB). exact VB.
        -- eapply atom_lt_mono; [exact LA | lia].
        -- eapply atom_lt_mono; [exact LB | lia].
        -- intros rho4 n4 Xs A4 Le4 LXs VXs. apply HK.
           ++ eapply (agree_trans rho _ rho4 nxt (Pos.succ n2)); [exact A3 | exact A4 | lia].
           ++ lia.
           ++ constructor; [simpl; lia | exact LXs].
           ++ cbn [avals aval denote_cs map]. rewrite (A4 n2) by lia. rewrite PTree.gss, VXs.
              destruct (cmp_sem c va vb); reflexivity.
Qed.

(** a memory: KQL's memory after it is the memory the Rocq text makes *)
Lemma cmem_ok : forall m cenvA benvA envA cenv benv denv nxt K rho M v M', wfm sigs r rm mok nx k m = true ->
  inv rho cenvA benvA envA cenv benv denv nxt ->
  (forall rho' n', agree rho rho' nxt -> Pos.le nxt n' -> evalk P f rho' (denote_m cs rec recm cenv benv denv M m) (K n') v M') ->
  evalk P f rho M (cmem gidf g mv m cenvA benvA envA nxt K) v M'.
Proof.
  induction m as [| h i x m IH | e m IH | m1 IH1 m2 IH2 | c a b m1 IH1 m2 IH2 | ccs args m IH | fi ccs args m IH | c m0 IH0 m1 IH1
                 | b m1 IH1 m2 IH2 | b m IH | h i x m IH];
    intros cenvA benvA envA cenv benv denv nxt K rho M v M' W Iv HK; cbn [cmem wfm] in *.
  - (* MCur *) apply HK; [apply agree_refl | lia].
  - (* MUpd *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wh Wi].
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 H A1 Le1 LH VH.
    pose proof (inv_step rho rho1 cenvA benvA envA cenv benv denv nxt n1 Iv A1 Le1) as I1.
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho2 n2 J A2 Le2 LJ VJ.
    pose proof (inv_step rho1 rho2 cenvA benvA envA cenv benv denv n1 n2 I1 A2 Le2) as I2.
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho3 n3 X A3 Le3 LX VX.
    pose proof (inv_step rho2 rho3 cenvA benvA envA cenv benv denv n2 n3 I2 A3 Le3) as I3.
    apply IH with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho4 n4 A4 Le4.
    apply K_st with (vh := denote_e cs rec cenv benv denv M h) (vi := denote_e cs rec cenv benv denv M i)
                    (va := denote_e cs rec cenv benv denv M x).
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2), (aval_agree rho1 rho2 n1); auto;
        eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2); auto; eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3); auto.
    + apply HK; [| lia]. apply (agree_4 rho rho1 rho2 rho3 rho4 nxt n1 n2 n3); auto.
  - (* MLet *) apply andb_true_iff in W as [We Wm].
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (cenv := cenv) (benv := benv) (denv := denote_e cs rec cenv benv denv M e :: denv); auto.
    + apply inv_let; auto. eapply inv_step; eauto.
    + intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - (* MLetM *) apply andb_true_iff in W as [W1 W2].
    apply IH1 with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A1 Le1.
    apply IH2 with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - (* MIf *) apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [W Wm1]. apply andb_true_iff in W as [Wa Wb].
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + assert (I2 : inv rho2 cenvA benvA envA cenv benv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      cbn [denote_m] in HK.
      destruct (cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)) eqn:C.
      * apply IH1 with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho3 n3 A3 Le3.
        apply HK; [| lia]. eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto; lia.
      * apply IH2 with (cenv := cenv) (benv := benv) (denv := denv); auto.
        { eapply inv_step; [exact I2 | apply agree_refl | afterle]. }
        intros rho3 n3 A3 Le3.
        apply HK; [| lia_a]. eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); [eauto | eauto | eapply agree_mono; [exact A3 | afterle] | lia | lia].
  - (* MRec *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. { apply flat_shallow; auto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA envA cenv benv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (denv := denv); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA envA cenv benv denv n1 n2 I1 A2 Le2) as I2.
    apply IH with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho3 n3 A3 Le3.
    destruct (Hrecm Wr (denote_cs cs rec cenv benv denv M ccs) (denote_es cs rec cenv benv denv M args)
                       (denote_m cs rec recm cenv benv denv M m)) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). apply cs_flat_bound; auto. }
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1). destruct (H1 (Hrmhp Wr)) as [Rm _].
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (denote_es cs rec cenv benv denv M args)).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    eapply K_call; eauto.
    + simpl. rewrite (A3 mv) by lia. rewrite (A2 mv Mv1), Rm, (avals_app rho3 Cs As _ _ VC3 VA3). reflexivity.
    + apply HK.
      * apply agree_set1; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto | lia].
      * lia.
  - (* MCall *) unfold sigs in W. rewrite nth_sigs in W. pose proof (Hcs fi) as Hc.
    cbn [denote_m] in HK. unfold callee in *. destruct (nth_error cs fi) as [[gs h]|] eqn:E; simpl in W; [|discriminate].
    assert (Hfi : (fi < j)%nat).
    { assert (fi < length cs)%nat by (apply nth_error_Some; rewrite E; discriminate). lia. }
    apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wsh]. apply andb_true_iff in W as [W Wsw]. apply andb_true_iff in W as [W Wr].
    apply andb_true_iff in W as [W Wsm]. apply andb_true_iff in W as [Wn Wk].
    assert (Hc2 : forall cvs0 vs0 M0, length cvs0 = sn gs -> length vs0 = sk gs -> Forall (fun c => (Z.of_nat c < cbz fi)%Z) cvs0 ->
              runk P (gidf fi) (map ofn cvs0 ++ vs0) M0 (calln gs h cvs0 vs0 M0) (if sr gs then callm gs h cvs0 vs0 M0 else M0)).
    { intros cvs0 vs0 M0 L1 L2 L3. pose proof (Hc cvs0 vs0 M0 L1 L2 L3) as H0. destruct (sw gs); [discriminate Wsw | exact H0]. }
    apply ccnts_ok with (cenv := cenv) (benv := benv) (denv := denv); auto.
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA envA cenv benv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (denv := denv); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA envA cenv benv denv n1 n2 I1 A2 Le2) as I2.
    apply IH with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho3 n3 A3 Le3.
    destruct (Hc2 (denote_cs cs rec cenv benv denv M ccs) (denote_es cs rec cenv benv denv M args) (denote_m cs rec recm cenv benv denv M m))
      as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). apply cs_shallow_bound; auto. }
    rewrite Wr in EV.
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (denote_es cs rec cenv benv denv M args)).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    eapply K_call; eauto.
    + apply avals_app; eauto.
    + apply HK.
      * apply agree_set1; [eapply (agree_3 rho rho1 rho2 rho3 nxt n1 n2); eauto | lia].
      * lia.
  - (* MMatch *) apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H).
    cbn [denote_m] in HK.
    destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl.
      apply IH0 with (cenv := cenv) (benv := benv) (denv := denv); auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbz j)%Z) by (specialize (Cb c); rewrite Ec in Cb; exact Cb).
      pose proof cbz_small as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1 with (cenv := p :: cenv) (benv := benv) (denv := denv); auto.
      * apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | lia].
      * intros rho3 n3 A3 Le3. apply HK; [ | lia_a ].
        refine (agree_trans rho _ rho3 nxt _ _ A3 _); [apply agree_set; afterle | lia_a].
  - (* MIfB *) apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [Wb Wm1].
    cbn [denote_m] in HK.
    apply (ccond_ok b) with (cenv := cenv) (benv := benv) (denv := denv); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta.
      apply IH1 with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
      intros rho2 n2 A2 Le2. rewrite Hb in HK. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
    + intros Hb rho1 n1 A1 Le1. cbv beta.
      apply IH2 with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
      intros rho2 n2 A2 Le2. rewrite Hb in HK. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - (* MLetB *) apply andb_true_iff in W as [Wb Wm].
    apply (cbval_ok b) with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH with (cenv := cenv) (benv := denote_b cs rec cenv benv denv M b :: benv) (denv := denv); auto.
    + apply inv_blet; auto. eapply inv_step; eauto.
    + intros rho2 n2 A2 Le2. apply HK; [eapply (agree_trans rho rho1 rho2 nxt n1); eauto | lia].
  - (* MUpd32 *) apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Wx]. apply andb_true_iff in W as [Wh Wi].
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 H A1 Le1 LH VH.
    pose proof (inv_step rho rho1 cenvA benvA envA cenv benv denv nxt n1 Iv A1 Le1) as I1.
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho2 n2 J A2 Le2 LJ VJ.
    pose proof (inv_step rho1 rho2 cenvA benvA envA cenv benv denv n1 n2 I1 A2 Le2) as I2.
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho3 n3 X A3 Le3 LX VX.
    pose proof (inv_step rho2 rho3 cenvA benvA envA cenv benv denv n2 n3 I2 A3 Le3) as I3.
    apply IH with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho4 n4 A4 Le4.
    apply K_st32 with (vh := denote_e cs rec cenv benv denv M h) (vi := denote_e cs rec cenv benv denv M i)
                    (va := denote_e cs rec cenv benv denv M x).
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2), (aval_agree rho1 rho2 n1); auto;
        eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3), (aval_agree rho2 rho3 n2); auto; eapply atom_lt_mono; eauto; lia.
    + rewrite (aval_agree rho3 rho4 n3); auto.
    + apply HK; [| lia]. apply (agree_4 rho rho1 rho2 rho3 rho4 nxt n1 n2 n3); auto.
Qed.

(** in tail position: the function's body ends with the value of [e] and the memory it started with *)
Hypothesis Hf : find P g = Some f.

(** the loop: the function itself again, on counters and numbers held by atoms *)
Lemma loop_call_ok : forall rho Cs As cvs vs M, r = true -> length cvs = nx -> length vs = k ->
  Forall (fun c => (Z.of_nat c < cbz j)%Z) cvs -> rho ! mv = Some (ofn cm) ->
  avals rho Cs = Some (map ofn cvs) -> avals rho As = Some vs ->
  evalk P f rho M (Eloop (Avar mv :: Cs ++ As)) (rec cvs vs M) M.
Proof.
  intros rho Cs As cvs vs M Wr Lc Lv Bd Rm VC VA.
  destruct (Hrec Wr cvs vs M Lc Lv Bd) as (fg & rho' & F & B & EV).
  rewrite Hf in F. injection F as <-.
  eapply K_loop; eauto. simpl. rewrite Rm, (avals_app rho Cs As _ _ VC VA). reflexivity.
Qed.
Lemma loopm_call_ok : forall rho Cs As cvs vs M, rm = true -> length cvs = nx -> length vs = k ->
  Forall (fun c => (Z.of_nat c < cbz j)%Z) cvs -> rho ! mv = Some (ofn cm) ->
  avals rho Cs = Some (map ofn cvs) -> avals rho As = Some vs ->
  evalk P f rho M (Eloop (Avar mv :: Cs ++ As)) 0%uint63 (recm cvs vs M).
Proof.
  intros rho Cs As cvs vs M Wr Lc Lv Bd Rm VC VA.
  destruct (Hrecm Wr cvs vs M Lc Lv Bd) as (fg & rho' & F & B & EV).
  rewrite Hf in F. injection F as <-.
  eapply K_loop; eauto. simpl. rewrite Rm, (avals_app rho Cs As _ _ VC VA). reflexivity.
Qed.

Lemma ctail_ok : forall e cenvA benvA envA cenv benv denv nxt rho M, wf sigs r mok nx k e = true -> inv rho cenvA benvA envA cenv benv denv nxt ->
  evalk P f rho M (ctail gidf g mv e cenvA benvA envA nxt) (denote_e cs rec cenv benv denv M e) M.
Proof.
  induction e as [i | n | o a IHa b IHb | c a IHa b IHb t IHt u IHu | e1 IH1 e2 IH2 | h IHh i IHi | ccs args | fi ccs args
                 | c e0 IH0 e1 IH1 | b t IHt u IHu | b e IHe | h IHh i IHi];
    intros cenvA benvA envA cenv benv denv nxt rho M W Iv; cbn [ctail] in *.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. auto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. auto.
  - (* SIf *) cbn [wf] in W. apply andb_true_iff in W as [W Wf]. apply andb_true_iff in W as [W Wt].
    apply andb_true_iff in W as [Wa Wb].
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv rho2 cenvA benvA envA cenv benv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    assert (VA2 : aval rho2 A = Some (denote_e cs rec cenv benv denv M a)) by (rewrite (aval_agree rho1 rho2 n1); eauto).
    destruct (mergeable_e t u) as [[[[cs1 as1] cs2] as2]|] eqn:MG.
    { (* both ends a call of the function itself: one call, its arguments chosen *)
      apply mergeable_e_spec in MG as [-> ->].
      cbn [wf] in Wt, Wf.
      apply andb_true_iff in Wt as [Wt Ws1]. apply andb_true_iff in Wt as [Wt Wc1]. apply andb_true_iff in Wt as [Wt Wfl1].
      apply andb_true_iff in Wt as [Wt Wk1]. apply andb_true_iff in Wt as [Wr Wn1].
      apply andb_true_iff in Wf as [Wf Ws2]. apply andb_true_iff in Wf as [Wf Wc2]. apply andb_true_iff in Wf as [Wf Wfl2].
      apply andb_true_iff in Wf as [Wf Wk2]. apply andb_true_iff in Wf as [_ Wn2].
      apply Nat.eqb_eq in Wn1, Wn2, Wk1, Wk2.
      assert (LA2 : atom_lt A n2) by (eapply atom_lt_mono; [exact LA | lia]).
      eapply (cmerge_c_ok cs1 cs2 c A B _ _ cenvA benvA envA cenv benv denv n2 _ rho2 M _ _ Wc1 Wc2 Wfl1 Wfl2 ltac:(lia) I2 VA2 VB LA2 LB).
      intros rho3 n3 Cs A3 Le3 LCs VCs.
      pose proof (inv_step rho2 rho3 cenvA benvA envA cenv benv denv n2 n3 I2 A3 Le3) as I3.
      eapply (cmerge_s_ok as1 as2 c A B _ _ cenvA benvA envA cenv benv denv n3 _ rho3 M _ _ Ws1 Ws2 ltac:(lia) I3).
      { rewrite (aval_agree rho2 rho3 n2 A A3 LA2). exact VA2. }
      { rewrite (aval_agree rho2 rho3 n2 B A3 LB). exact VB. }
      { eapply atom_lt_mono; [exact LA2 | lia]. }
      { eapply atom_lt_mono; [exact LB | lia]. }
      intros rho4 n4 As A4 Le4 LAs VAs.
      destruct I2 as (_ & _ & _ & _ & _ & _ & Cb2 & Mv2 & H2). destruct (H2 (Hrhp Wr)) as [Rm _].
      assert (Rm4 : rho4 ! mv = Some (ofn cm)) by (rewrite (A4 mv) by lia; rewrite (A3 mv) by lia; exact Rm).
      assert (VC4 : avals rho4 Cs = Some (map ofn (if cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)
                                                   then denote_cs cs rec cenv benv denv M cs1 else denote_cs cs rec cenv benv denv M cs2)))
        by (rewrite (avals_agree rho3 rho4 n3 Cs A4 LCs); exact VCs).
      cbn [denote_e]. revert VC4 VAs.
      destruct (cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)); intros VC4 VAs;
        (apply loop_call_ok; [exact Wr | rewrite len_denote_cs; lia | rewrite len_denote_es; lia | apply cs_flat_bound; auto
                      | exact Rm4 | exact VC4 | exact VAs]). }
    eapply K_if.
    + exact VA2.
    + eauto.
    + cbn [denote_e]. assert (I2' : forall n', Pos.le n2 n' -> inv rho2 cenvA benvA envA cenv benv denv n') by (intros n' L'; eapply inv_step; [exact I2 | apply agree_refl | exact L']).
      destruct (cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)); eauto using after_le.
  - (* SLet *) cbn [wf] in W. apply andb_true_iff in W as [W1 W2].
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_e]. apply IH2; auto. apply inv_let; auto. eapply inv_step; eauto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. auto.
  - (* SRec *) cbn [wf] in W. apply andb_true_iff in W as [W Ws]. apply andb_true_iff in W as [W Wc].
    apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk]. apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. { apply flat_shallow; auto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA envA cenv benv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (denv := denv); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    destruct (Hrec Wr (denote_cs cs rec cenv benv denv M ccs) (denote_es cs rec cenv benv denv M args) M) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). apply cs_flat_bound; auto. }
    rewrite Hf in F. injection F as <-.
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1). destruct (H1 (Hrhp Wr)) as [Rm _].
    cbn [denote_e]. eapply K_loop; eauto.
    simpl. rewrite (A2 mv Mv1), Rm.
    rewrite (avals_app rho2 Cs As _ _ (eq_trans (avals_agree rho1 rho2 n1 Cs A2 LCs) VCs) VAs). reflexivity.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. auto.
  - (* SMatch *) cbn [wf] in W. apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H).
    cbn [denote_e]. destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl. apply IH0; auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbz j)%Z) by (specialize (Cb c); rewrite Ec in Cb; exact Cb).
      pose proof cbz_small as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1; auto. apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | lia].
  - (* SIfB *) cbn [wf] in W. apply andb_true_iff in W as [W We]. apply andb_true_iff in W as [Wb Wt].
    apply (ccond_ok b) with (cenv := cenv) (benv := benv) (denv := denv); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. cbn [denote_e]. rewrite Hb. apply IHt; auto. eapply inv_step; eauto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. cbn [denote_e]. rewrite Hb. apply IHu; auto. eapply inv_step; eauto.
  - (* SLetB *) cbn [wf] in W. apply andb_true_iff in W as [Wb We].
    apply (cbval_ok b) with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_e]. apply IHe; auto. apply inv_blet; auto. eapply inv_step; eauto.
  - apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. auto.
Qed.

(** a memory in tail position: the function's body returns 0 and ends with the memory the Rocq text makes *)
Lemma ctailm_ok : forall m cenvA benvA envA cenv benv denv nxt rho M, wfm sigs r rm mok nx k m = true -> inv rho cenvA benvA envA cenv benv denv nxt ->
  evalk P f rho M (ctailm gidf g mv m cenvA benvA envA nxt) 0%uint63 (denote_m cs rec recm cenv benv denv M m).
Proof.
  induction m as [| h i x m IH | e m IH | m1 IH1 m2 IH2 | c a b m1 IH1 m2 IH2 | ccs args m IH | fi ccs args m IH | c m0 IH0 m1 IH1
                 | b m1 IH1 m2 IH2 | b m IH | h i x m IH];
    intros cenvA benvA envA cenv benv denv nxt rho M W Iv; cbn [ctailm] in *.
  - apply cmem_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. reflexivity.
  - apply cmem_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. reflexivity.
  - (* MLet *) cbn [wfm] in W. apply andb_true_iff in W as [We Wm].
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_m]. apply IH; auto. apply inv_let; auto. eapply inv_step; eauto.
  - (* MLetM *) cbn [wfm] in W. apply andb_true_iff in W as [W1 W2].
    apply cmem_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A1 Le1.
    cbn [denote_m]. apply IH2; auto. eapply inv_step; eauto.
  - (* MIf *) cbn [wfm] in W. apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [W Wm1].
    apply andb_true_iff in W as [Wa Wb].
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    assert (I2 : inv rho2 cenvA benvA envA cenv benv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
    assert (VA2 : aval rho2 A = Some (denote_e cs rec cenv benv denv M a)) by (rewrite (aval_agree rho1 rho2 n1); eauto).
    destruct (mergeable_m m1 m2) as [[[[cs1 as1] cs2] as2]|] eqn:MG.
    { (* both ends a call of the function itself: one call, its arguments chosen *)
      apply mergeable_m_spec in MG as [-> ->].
      cbn [wfm] in Wm1, Wm2.
      apply andb_true_iff in Wm1 as [Wm1 Wm1']. apply andb_true_iff in Wm1 as [Wm1 Ws1]. apply andb_true_iff in Wm1 as [Wm1 Wc1].
      apply andb_true_iff in Wm1 as [Wm1 Wfl1]. apply andb_true_iff in Wm1 as [Wm1 Wk1]. apply andb_true_iff in Wm1 as [Wr Wn1].
      apply andb_true_iff in Wm2 as [Wm2 Wm2']. apply andb_true_iff in Wm2 as [Wm2 Ws2]. apply andb_true_iff in Wm2 as [Wm2 Wc2].
      apply andb_true_iff in Wm2 as [Wm2 Wfl2]. apply andb_true_iff in Wm2 as [Wm2 Wk2]. apply andb_true_iff in Wm2 as [_ Wn2].
      apply Nat.eqb_eq in Wn1, Wn2, Wk1, Wk2.
      assert (LA2 : atom_lt A n2) by (eapply atom_lt_mono; [exact LA | lia]).
      eapply (cmerge_c_ok cs1 cs2 c A B _ _ cenvA benvA envA cenv benv denv n2 _ rho2 M _ _ Wc1 Wc2 Wfl1 Wfl2 ltac:(lia) I2 VA2 VB LA2 LB).
      intros rho3 n3 Cs A3 Le3 LCs VCs.
      pose proof (inv_step rho2 rho3 cenvA benvA envA cenv benv denv n2 n3 I2 A3 Le3) as I3.
      eapply (cmerge_s_ok as1 as2 c A B _ _ cenvA benvA envA cenv benv denv n3 _ rho3 M _ _ Ws1 Ws2 ltac:(lia) I3).
      { rewrite (aval_agree rho2 rho3 n2 A A3 LA2). exact VA2. }
      { rewrite (aval_agree rho2 rho3 n2 B A3 LB). exact VB. }
      { eapply atom_lt_mono; [exact LA2 | lia]. }
      { eapply atom_lt_mono; [exact LB | lia]. }
      intros rho4 n4 As A4 Le4 LAs VAs.
      destruct I2 as (_ & _ & _ & _ & _ & _ & Cb2 & Mv2 & H2). destruct (H2 (Hrmhp Wr)) as [Rm _].
      assert (Rm4 : rho4 ! mv = Some (ofn cm)) by (rewrite (A4 mv) by lia; rewrite (A3 mv) by lia; exact Rm).
      assert (VC4 : avals rho4 Cs = Some (map ofn (if cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)
                                                   then denote_cs cs rec cenv benv denv M cs1 else denote_cs cs rec cenv benv denv M cs2)))
        by (rewrite (avals_agree rho3 rho4 n3 Cs A4 LCs); exact VCs).
      cbn [denote_m]. revert VC4 VAs.
      destruct (cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)); intros VC4 VAs;
        (apply loopm_call_ok; [exact Wr | rewrite len_denote_cs; lia | rewrite len_denote_es; lia | apply cs_flat_bound; auto
                      | exact Rm4 | exact VC4 | exact VAs]). }
    eapply K_if.
    + exact VA2.
    + eauto.
    + cbn [denote_m]. assert (I2' : forall n', Pos.le n2 n' -> inv rho2 cenvA benvA envA cenv benv denv n') by (intros n' L'; eapply inv_step; [exact I2 | apply agree_refl | exact L']).
      destruct (cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)); eauto using after_le.
  - (* MRec *) cbn [wfm] in W. apply andb_true_iff in W as [W Wm]. apply andb_true_iff in W as [W Ws].
    apply andb_true_iff in W as [W Wc]. apply andb_true_iff in W as [W Wfl]. apply andb_true_iff in W as [W Wk].
    apply andb_true_iff in W as [Wr Wn].
    apply ccnts_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. { apply flat_shallow; auto. }
    intros rho1 n1 Cs A1 Le1 LCs VCs.
    pose proof (inv_step rho rho1 cenvA benvA envA cenv benv denv nxt n1 Iv A1 Le1) as I1.
    apply cexps_ok with (cenv := cenv) (benv := benv) (denv := denv); auto.
    intros rho2 n2 As A2 Le2 LAs VAs.
    pose proof (inv_step rho1 rho2 cenvA benvA envA cenv benv denv n1 n2 I1 A2 Le2) as I2.
    apply cmem_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho3 n3 A3 Le3.
    destruct (Hrecm Wr (denote_cs cs rec cenv benv denv M ccs) (denote_es cs rec cenv benv denv M args)
                       (denote_m cs rec recm cenv benv denv M m)) as (fg & rho' & F & B & EV).
    { rewrite len_denote_cs. apply Nat.eqb_eq; auto. }
    { rewrite len_denote_es. apply Nat.eqb_eq; auto. }
    { destruct Iv as (_ & _ & _ & _ & _ & _ & Cb & _). apply cs_flat_bound; auto. }
    rewrite Hf in F. injection F as <-.
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & Mv1 & H1). destruct (H1 (Hrmhp Wr)) as [Rm _].
    assert (VC3 : avals rho3 Cs = Some (map ofn (denote_cs cs rec cenv benv denv M ccs))).
    { rewrite (avals_agree rho2 rho3 n2 Cs A3 (Forall_atom_mono Cs n1 n2 LCs Le2)), (avals_agree rho1 rho2 n1 Cs A2 LCs).
      exact VCs. }
    assert (VA3 : avals rho3 As = Some (denote_es cs rec cenv benv denv M args)).
    { rewrite (avals_agree rho2 rho3 n2 As A3 LAs). exact VAs. }
    cbn [denote_m]. eapply K_loop; eauto.
    simpl. rewrite (A3 mv) by lia. rewrite (A2 mv Mv1), Rm, (avals_app rho3 Cs As _ _ VC3 VA3). reflexivity.
  - apply cmem_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. reflexivity.
  - (* MMatch *) cbn [wfm] in W. apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H).
    cbn [denote_m]. destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl. apply IH0; auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbz j)%Z) by (specialize (Cb c); rewrite Ec in Cb; exact Cb).
      pose proof cbz_small as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1; auto. apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | lia].
  - (* MIfB *) cbn [wfm] in W. apply andb_true_iff in W as [W Wm2]. apply andb_true_iff in W as [Wb Wm1].
    apply (ccond_ok b) with (cenv := cenv) (benv := benv) (denv := denv); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. cbn [denote_m]. rewrite Hb. apply IH1; auto. eapply inv_step; eauto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. cbn [denote_m]. rewrite Hb. apply IH2; auto. eapply inv_step; eauto.
  - (* MLetB *) cbn [wfm] in W. apply andb_true_iff in W as [Wb Wm].
    apply (cbval_ok b) with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    cbn [denote_m]. apply IH; auto. apply inv_blet; auto. eapply inv_step; eauto.
  - apply cmem_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros. apply K_ret. reflexivity.
Qed.
(** a number made after memories, in tail position: the body ends with its number and the last memory made (no recursive
    call is in it: [r], [rm] false; the memory is there: [mok]) *)
Lemma ctailx_ok : forall x cenvA benvA envA cenv benv denv nxt rho M, r = false -> rm = false -> mok = true ->
  wfx sigs nx k x = true -> inv rho cenvA benvA envA cenv benv denv nxt ->
  evalk P f rho M (ctailx gidf g mv x cenvA benvA envA nxt) (denote_x cs rec recm cenv benv denv M x)
        (endx cs rec recm cenv benv denv M x).
Proof.
  induction x as [e | m x IH | e x IH | b x IH | c a b x1 IH1 x2 IH2 | b x1 IH1 x2 IH2 | c x0 IH0 x1 IH1];
    intros cenvA benvA envA cenv benv denv nxt rho M Hr0 Hrm0 Hm1 W Iv; cbn [ctailx wfx denote_x endx] in *.
  - (* XRet *) assert (We : wf sigs r mok nx k e = true) by (rewrite Hr0, Hm1; exact W).
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho' n' a A' Le' La Va. apply K_ret. exact Va.
  - (* XLetM *) apply andb_true_iff in W as [Wm Wx].
    assert (Wm' : wfm sigs r rm mok nx k m = true) by (rewrite Hr0, Hrm0, Hm1; exact Wm).
    apply cmem_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A1 Le1. cbv beta.
    apply IH; auto. eapply inv_step; eauto.
  - (* XLet *) apply andb_true_iff in W as [We Wx].
    assert (We' : wf sigs r mok nx k e = true) by (rewrite Hr0, Hm1; exact We).
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH; auto. apply inv_let; auto. eapply inv_step; eauto.
  - (* XLetB *) apply andb_true_iff in W as [Wb Wx].
    assert (Wb' : wfb sigs r mok nx k b = true) by (rewrite Hr0, Hm1; exact Wb).
    apply (cbval_ok b) with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply IH; auto. apply inv_blet; auto. eapply inv_step; eauto.
  - (* XIf *) apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [W W1]. apply andb_true_iff in W as [Wa Wb].
    assert (Wa' : wf sigs r mok nx k a = true) by (rewrite Hr0, Hm1; exact Wa).
    assert (Wb' : wf sigs r mok nx k b = true) by (rewrite Hr0, Hm1; exact Wb).
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. intros rho1 n1 A A1 Le1 LA VA.
    apply cexp_ok with (cenv := cenv) (benv := benv) (denv := denv); auto. { eapply inv_step; eauto. }
    intros rho2 n2 B A2 Le2 LB VB.
    eapply K_if.
    + rewrite (aval_agree rho1 rho2 n1); eauto.
    + eauto.
    + assert (I2 : inv rho2 cenvA benvA envA cenv benv denv n2). { eapply inv_step; [eapply inv_step; eauto | eauto | auto]. }
      assert (I2' : forall n', Pos.le n2 n' -> inv rho2 cenvA benvA envA cenv benv denv n') by (intros n' L'; eapply inv_step; [exact I2 | apply agree_refl | exact L']).
      destruct (cmp_sem c (denote_e cs rec cenv benv denv M a) (denote_e cs rec cenv benv denv M b)); eauto using after_le.
  - (* XIfB *) apply andb_true_iff in W as [W W2]. apply andb_true_iff in W as [Wb W1].
    assert (Wb' : wfb sigs r mok nx k b = true) by (rewrite Hr0, Hm1; exact Wb).
    apply (ccond_ok b) with (cenv := cenv) (benv := benv) (denv := denv); auto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply IH1; auto. eapply inv_step; eauto.
    + intros Hb rho1 n1 A1 Le1. cbv beta. rewrite Hb. apply IH2; auto. eapply inv_step; eauto.
  - (* XMatch *) apply andb_true_iff in W as [W0 W1].
    pose proof Iv as (E & L & C & LC & Bv & LBv & Cb & Mv & H).
    destruct (nth c cenv O) as [|p] eqn:Ec.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn 0)) by (rewrite <- Ec; apply C).
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_0. simpl. apply IH0; auto.
    + assert (CC : aval rho (nth c cenvA (Aint 0%uint63)) = Some (ofn (S p))) by (rewrite <- Ec; apply C).
      assert (Bp : (Z.of_nat (S p) < cbz j)%Z) by (specialize (Cb c); rewrite Ec in Cb; exact Cb).
      pose proof cbz_small as Sm.
      eapply K_if; [exact CC | reflexivity | ]. rewrite ofn_S_ne0 by lia. simpl.
      eapply K_op; [exact CC | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      apply IH1; auto. apply inv_cpush; [eapply inv_step; [exact Iv | apply agree_refl | afterle] | lia].
Qed.
End Sim.

(* ---------------------------------------------------------------- the function *)
Local Open Scope nat_scope.

Lemma appn_absn : forall k m r F vs s, length vs = k -> appn k m r (absn k m r F) vs s = F (rev vs) (if m then s else dummy_mem).
Proof.
  induction k as [|k IH]; intros m r F vs s L; destruct vs as [|v vs]; simpl in *; try discriminate.
  - destruct m; reflexivity.
  - injection L as L. rewrite IH by auto. reflexivity.
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

Lemma params_nth : forall n k j, j < k + n -> nth j (params n k) 1%positive = Pos.of_succ_nat j.
Proof.
  intros n k j L. unfold params. rewrite nth_indep with (d' := Pos.of_succ_nat 0) by (rewrite map_length, seq_length; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma params_nodup : forall n k, NoDup (params n k).
Proof.
  intros n k. unfold params. apply FinFun.Injective_map_NoDup; [| apply seq_NoDup].
  intros a b E. apply SuccNat2Pos.inj; auto.
Qed.

Lemma params_length : forall n k, length (params n k) = k + n.
Proof. intros n k. unfold params. rewrite map_length, seq_length. reflexivity. Qed.

Lemma env0_nth : forall n k i, i < k -> nth i (env0 n k) (Aint 0%uint63) = Avar (Pos.of_succ_nat (n + (k - 1 - i))).
Proof.
  intros n k i L. unfold env0.
  rewrite nth_indep with (d' := Avar (Pos.of_succ_nat (n + 0))) by (rewrite map_length, rev_length, seq_length; lia).
  rewrite map_nth with (d := 0). rewrite rev_nth by (rewrite seq_length; lia). rewrite seq_length, seq_nth by lia.
  f_equal. f_equal. lia.
Qed.

Lemma env0_out : forall n k i, k <= i -> nth i (env0 n k) (Aint 0%uint63) = Aint 0%uint63.
Proof. intros n k i L. apply nth_overflow. unfold env0. rewrite map_length, rev_length, seq_length. lia. Qed.

Lemma cenv0_nth : forall n i, i < n -> nth i (cenv0 n) (Aint 0%uint63) = Avar (Pos.of_succ_nat (n - 1 - i)).
Proof.
  intros n i L. unfold cenv0.
  rewrite nth_indep with (d' := Avar (Pos.of_succ_nat 0)) by (rewrite map_length, rev_length, seq_length; lia).
  rewrite map_nth with (d := 0). rewrite rev_nth by (rewrite seq_length; lia). rewrite seq_length, seq_nth by lia.
  f_equal. f_equal. lia.
Qed.

Lemma cenv0_out : forall n i, n <= i -> nth i (cenv0 n) (Aint 0%uint63) = Aint 0%uint63.
Proof. intros n i L. apply nth_overflow. unfold cenv0. rewrite map_length, rev_length, seq_length. lia. Qed.

Lemma env0_lt : forall gs, lt_all (env0 (sn gs) (sk gs)) (pmv gs).
Proof.
  intros [x k m r] i. unfold pmv. simpl. destruct (Nat.lt_ge_cases i k) as [L|L].
  - rewrite env0_nth by auto. simpl. apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
  - rewrite env0_out by auto. simpl. auto.
Qed.

Lemma cenv0_lt : forall gs, lt_all (cenv0 (sn gs)) (pmv gs).
Proof.
  intros [x k m r] i. unfold pmv. simpl. destruct (Nat.lt_ge_cases i x) as [L|L].
  - rewrite cenv0_nth by auto. simpl. apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
  - rewrite cenv0_out by auto. simpl. auto.
Qed.

(** the parameters bound: the counters in 1 .. n, the numbers after them, read by [cenv0] / [env0] in [denote_f]'s order *)
Lemma bind_params : forall n k cvs vs, length cvs = n -> length vs = k ->
  exists rho0, bind (params n k) (map ofn cvs ++ vs) (PTree.empty _) = Some rho0 /\
    cenv_ok rho0 (cenv0 n) (rev cvs) /\ env_ok rho0 (env0 n k) (rev vs).
Proof.
  intros n k cvs vs Lc Lv. destruct (bind_some (params n k) (map ofn cvs ++ vs) (PTree.empty _)) as [rho0 B].
  { rewrite params_length, app_length, map_length. lia. }
  exists rho0. split; auto. split.
  - intro i. destruct (Nat.lt_ge_cases i n) as [Li|Li].
    + rewrite cenv0_nth by auto. simpl.
      pose proof (bind_nth _ _ _ _ (n - 1 - i) (params_nodup n k) B) as N.
      rewrite params_nth in N by lia. rewrite N by (rewrite params_length; lia).
      rewrite app_nth1 by (rewrite map_length; lia).
      rewrite nth_indep with (d' := ofn O) by (rewrite map_length; lia). rewrite map_nth.
      rewrite rev_nth by lia. f_equal. f_equal. f_equal. lia.
    + rewrite cenv0_out by auto. rewrite nth_overflow by (rewrite rev_length; lia). reflexivity.
  - intro i. destruct (Nat.lt_ge_cases i k) as [Li|Li].
    + rewrite env0_nth by auto. simpl.
      pose proof (bind_nth _ _ _ _ (n + (k - 1 - i)) (params_nodup n k) B) as N.
      rewrite params_nth in N by lia. rewrite N by (rewrite params_length; lia).
      rewrite app_nth2 by (rewrite map_length; lia). rewrite map_length.
      rewrite rev_nth by lia. f_equal. f_equal. lia.
    + rewrite env0_out by auto. simpl. rewrite nth_overflow; auto. rewrite rev_length. lia.
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

Theorem compile_f_ok : forall P cs gidf j gs b,
  find P (gidf j) = Some (compile_f gidf j gs b) -> wf_f (map (@projT1 _ _) cs) gs b = true -> callees_ok P gidf cs ->
  Nat.leb (length cs) j = true -> (Z.of_nat j <? 1099511627776)%Z = true ->
  callee_ok P (gidf j) (cbz j) gs (denote_f cs gs b).
Proof.
  intros P cs gidf j [x k m r w] b Hf W Hcs Hlen Hj. apply Nat.leb_le in Hlen. apply Z.ltb_lt in Hj.
  unfold callee_ok. simpl sn. simpl sk. simpl sm. simpl sr. simpl sw.
  set (mv := pmv (mksig x k m r w)).
  assert (Lmv : lt_all (env0 x k) mv) by apply (env0_lt (mksig x k m r w)).
  assert (LCmv : lt_all (cenv0 x) mv) by apply (cenv0_lt (mksig x k m r w)).
  assert (Bpos : (0 < cbz j)%Z) by (unfold cbz; lia).
  assert (BwB : (cbz j < wB)%Z) by (rewrite KQMAuto.wB_num; unfold cbz; lia).
  destruct b as [e0 e1 | e | m0 m1 | e | xx]; simpl in W.
  - (* a number, recursive on the first counter *)
    destruct x as [|x']; simpl in W; [discriminate|]. destruct r; simpl in W; [discriminate|].
    destruct w; simpl in W; [discriminate|].
    apply andb_true_iff in W as [W0 W1]. cbv beta iota.
    assert (Mvgt : Pos.lt 1 mv).
    { unfold mv, pmv. simpl. apply Pos2Nat.inj_lt. rewrite SuccNat2Pos.id_succ. simpl. lia. }
    intros cvs vs M Lc Lv Bd. destruct cvs as [|n rest]; [simpl in Lc; discriminate|].
    simpl in Lc. injection Lc as Lc.
    revert rest vs M Lc Lv Bd. induction n as [|n' IH]; intros rest vs M Lc Lv Bd.
    + destruct (bind_params (S x') k (0 :: rest) vs) as (rho0 & Bd0 & C0 & E0); [simpl; lia | auto |].
      exists (compile_f gidf j (mksig (S x') k m false false) (FRec e0 e1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      change (calln (mksig (S x') k m false false) (denote_f cs (mksig (S x') k m false false) (FRec e0 e1)) (0 :: rest) vs M)
        with (appn k m false (appc x' _ (absc x' _ (fun cenv => absn k m false (fun env s =>
                denote_e cs dnum (cenv ++ [0]) [] env s e0))) rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto. simpl kbody.
      pose proof (cenv0_first x' 0 rest rho0 Lc C0) as R1.
      eapply K_if; [simpl; exact R1 | reflexivity | ]. rewrite ofn_0. simpl.
      assert (EQ : denote_e cs dnum (rev rest ++ [0]) [] (rev vs) (if m then M else dummy_mem) e0
                   = denote_e cs dnum (rev rest ++ [0]) [] (rev vs) M e0).
      { destruct m; [reflexivity|]. eapply (proj1 denote_nomem); [intros; reflexivity | eauto]. }
      rewrite EQ.
      refine (ctail_ok P _ gidf (gidf j) mv cs false false m x' k j dnum 0 _ _ Hcs Hlen Hj Hf e0 _ _ _ _ _ _ _ _ M W0 _).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
        -- exact E0.
        -- eapply lt_all_mono; eauto. lia.
        -- exact C0.
        -- eapply lt_all_mono; [exact LCmv | lia].
        -- apply benv_ok_nil.
        -- apply lt_all_nil.
        -- exact (Forall_rev_cbound _ (0 :: rest) Bpos Bd).
        -- lia.
        -- intros Habs; discriminate Habs.
    + destruct (bind_params (S x') k (S n' :: rest) vs) as (rho0 & Bd0 & C0 & E0); [simpl; lia | auto |].
      exists (compile_f gidf j (mksig (S x') k m false false) (FRec e0 e1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      set (dfn := denote_f cs (mksig (S x') k m false false) (FRec e0 e1)).
      change (calln (mksig (S x') k m false false) dfn (S n' :: rest) vs M)
        with (appn k m false (appc x' _ (absc x' _ (fun cenv => absn k m false (fun env s =>
                denote_e cs (fun cvs args s' => appn k m false (appc x' _ (dfn n') cvs) args s') (n' :: cenv ++ [S n']) [] env s e1)))
              rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto. simpl kbody.
      pose proof (cenv0_first x' (S n') rest rho0 Lc C0) as R1.
      assert (Bn : (Z.of_nat (S n') < cbz j)%Z) by (inversion Bd; auto).
      eapply K_if; [simpl; exact R1 | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
      eapply K_op; [simpl; exact R1 | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia.
      assert (EQ : denote_e cs (fun cvs args s' => appn k m false (appc x' _ (dfn n') cvs) args s') (n' :: rev rest ++ [S n'])
                     [] (rev vs) (if m then M else dummy_mem) e1
                   = denote_e cs (fun cvs args s' => appn k m false (appc x' _ (dfn n') cvs) args s') (n' :: rev rest ++ [S n'])
                     [] (rev vs) M e1).
      { destruct m; [reflexivity|]. eapply (proj1 denote_nomem); [ | eauto].
        intros cvs l. exact (appn_false k false (appc x' _ (dfn n') cvs) l _ _). }
      rewrite EQ.
      refine (ctail_ok P _ gidf (gidf j) mv cs true true m x' k j
                (fun cvs args s' => appn k m false (appc x' _ (dfn n') cvs) args s') n' _ _ Hcs Hlen Hj Hf e1 _ _ _ _ _ _ _ _ M W1 _).
      * intros _ cvs vs' M' Lc' Lv' Bd'. assert (Bn' : (Z.of_nat n' < cbz j)%Z) by lia.
        assert (Bf : Forall (fun c => (Z.of_nat c < cbz j)%Z) (n' :: cvs)) by (constructor; auto).
        exact (IH cvs vs' M' Lc' Lv' Bf).
      * intros _. reflexivity.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
        -- eapply env_ok_agree; [exact E0 | exact Lmv | apply agree_set; apply Pos.le_refl].
        -- eapply lt_all_mono; eauto. lia.
        -- apply cenv_ok_cons; [eapply cenv_ok_agree; [exact C0 | exact LCmv | apply agree_set; apply Pos.le_refl] | simpl; apply PTree.gss].
        -- apply lt_all_cons; [eapply lt_all_mono; [exact LCmv | lia] | simpl; lia].
        -- apply benv_ok_nil.
        -- apply lt_all_nil.
        -- apply cbound_cons; [exact (Forall_rev_cbound _ (S n' :: rest) Bpos Bd) | lia].
        -- lia.
        -- intros _. split; [apply PTree.gss | lia].
  - (* a number, plain *)
    destruct r; simpl in W; [discriminate|]. destruct w; simpl in W; [discriminate|]. cbv beta iota.
    intros cvs vs M Lc Lv Bd.
    destruct (bind_params x k cvs vs Lc Lv) as (rho0 & Bd0 & C0 & E0).
    exists (compile_f gidf j (mksig x k m false false) (FPlain e)), rho0. split; [exact Hf|]. split; [exact Bd0|].
    assert (V : calln (mksig x k m false false) (denote_f cs (mksig x k m false false) (FPlain e)) cvs vs M
                = denote_e cs dnum (rev cvs) [] (rev vs) M e).
    { destruct x as [|x'].
      - destruct cvs; [|discriminate].
        change (calln (mksig 0 k m false false) (denote_f cs (mksig 0 k m false false) (FPlain e)) [] vs M)
          with (appn k m false (absn k m false (fun env s => denote_e cs dnum [] [] env s e)) vs M).
        rewrite appn_absn by auto. destruct m; [reflexivity|]. eapply (proj1 denote_nomem); [intros; reflexivity | eauto].
      - destruct cvs as [|n rest]; [discriminate|]. simpl in Lc. injection Lc as Lc.
        change (calln (mksig (S x') k m false false) (denote_f cs (mksig (S x') k m false false) (FPlain e)) (n :: rest) vs M)
          with (appn k m false (appc x' _ (absc x' _ (fun cenv => absn k m false (fun env s =>
                  denote_e cs dnum (cenv ++ [n]) [] env s e))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto. destruct m; [reflexivity|].
        eapply (proj1 denote_nomem); [intros; reflexivity | eauto]. }
    rewrite V. simpl kbody.
    refine (ctail_ok P _ gidf (gidf j) mv cs false false m 0 k j dnum 0 _ _ Hcs Hlen Hj Hf e _ _ _ _ _ _ _ _ M W _).
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
      * exact E0.
      * eapply lt_all_mono; eauto. lia.
      * exact C0.
      * eapply lt_all_mono; [exact LCmv | lia].
      * apply benv_ok_nil.
      * apply lt_all_nil.
      * exact (Forall_rev_cbound _ cvs Bpos Bd).
      * lia.
      * intros Habs; discriminate Habs.
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
    + destruct (bind_params (S x') k (0 :: rest) vs) as (rho0 & Bd0 & C0 & E0); [simpl; lia | auto |].
      exists (compile_f gidf j (mksig (S x') k true true false) (FRecM m0 m1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      change (calln (mksig (S x') k true true false) (denote_f cs (mksig (S x') k true true false) (FRecM m0 m1)) (0 :: rest) vs M)
        with 0%uint63.
      change (callm (mksig (S x') k true true false) (denote_f cs (mksig (S x') k true true false) (FRecM m0 m1)) (0 :: rest) vs M)
        with (appn k true true (appc x' _ (absc x' _ (fun cenv => absn k true true (fun env s =>
                denote_m cs dnum dmem (cenv ++ [0]) [] env s m0))) rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto. simpl kbody.
      pose proof (cenv0_first x' 0 rest rho0 Lc C0) as R1.
      eapply K_if; [simpl; exact R1 | reflexivity | ]. rewrite ofn_0. simpl.
      refine (ctailm_ok P _ gidf (gidf j) mv cs false false false true x' k j dnum dmem 0 _ _ _ _ Hcs Hlen Hj Hf m0
                        _ _ _ _ _ _ _ _ M W0 _).
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * intros Habs; discriminate Habs.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
        -- exact E0.
        -- eapply lt_all_mono; eauto. lia.
        -- exact C0.
        -- eapply lt_all_mono; [exact LCmv | lia].
        -- apply benv_ok_nil.
        -- apply lt_all_nil.
        -- exact (Forall_rev_cbound _ (0 :: rest) Bpos Bd).
        -- lia.
        -- intros Habs; discriminate Habs.
    + destruct (bind_params (S x') k (S n' :: rest) vs) as (rho0 & Bd0 & C0 & E0); [simpl; lia | auto |].
      exists (compile_f gidf j (mksig (S x') k true true false) (FRecM m0 m1)), rho0. split; [exact Hf|]. split; [exact Bd0|].
      set (dfn := denote_f cs (mksig (S x') k true true false) (FRecM m0 m1)).
      change (calln (mksig (S x') k true true false) dfn (S n' :: rest) vs M) with 0%uint63.
      change (callm (mksig (S x') k true true false) dfn (S n' :: rest) vs M)
        with (appn k true true (appc x' _ (absc x' _ (fun cenv => absn k true true (fun env s =>
                denote_m cs dnum (fun cvs args s' => appn k true true (appc x' _ (dfn n') cvs) args s')
                         (n' :: cenv ++ [S n']) [] env s m1))) rest) vs M).
      rewrite appc_absc by auto. rewrite appn_absn by auto. simpl kbody.
      pose proof (cenv0_first x' (S n') rest rho0 Lc C0) as R1.
      assert (Bn : (Z.of_nat (S n') < cbz j)%Z) by (inversion Bd; auto).
      eapply K_if; [simpl; exact R1 | reflexivity | ]. simpl cmp_sem. rewrite ofn_S_ne0 by lia.
      eapply K_op; [simpl; exact R1 | reflexivity | ]. simpl binop_sem. rewrite ofn_pred by lia. cbv beta iota.
      refine (ctailm_ok P _ gidf (gidf j) mv cs false true true true x' k j dnum
                (fun cvs args s' => appn k true true (appc x' _ (dfn n') cvs) args s') n' _ _ _ _ Hcs Hlen Hj Hf m1
                _ _ _ _ _ _ _ _ M W1 _).
      * intros Habs; discriminate Habs.
      * intros _ cvs vs' M' Lc' Lv' Bd'. assert (Bn' : (Z.of_nat n' < cbz j)%Z) by lia.
        assert (Bf : Forall (fun c => (Z.of_nat c < cbz j)%Z) (n' :: cvs)) by (constructor; auto).
        exact (IH cvs vs' M' Lc' Lv' Bf).
      * intros Habs; discriminate Habs.
      * intros _. reflexivity.
      * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
        -- eapply env_ok_agree; [exact E0 | exact Lmv | apply agree_set; apply Pos.le_refl].
        -- eapply lt_all_mono; eauto. lia.
        -- apply cenv_ok_cons; [eapply cenv_ok_agree; [exact C0 | exact LCmv | apply agree_set; apply Pos.le_refl] | simpl; apply PTree.gss].
        -- apply lt_all_cons; [eapply lt_all_mono; [exact LCmv | lia] | simpl; lia].
        -- apply benv_ok_nil.
        -- apply lt_all_nil.
        -- apply cbound_cons; [exact (Forall_rev_cbound _ (S n' :: rest) Bpos Bd) | lia].
        -- lia.
        -- intros _. split; [apply PTree.gss | lia].
  - (* a memory, plain *)
    destruct r; simpl in W; [|discriminate]. destruct w; simpl in W; [discriminate|]. destruct m; simpl in W; [|discriminate].
    cbv beta iota.
    intros cvs vs M Lc Lv Bd.
    destruct (bind_params x k cvs vs Lc Lv) as (rho0 & Bd0 & C0 & E0).
    exists (compile_f gidf j (mksig x k true true false) (FPlainM e)), rho0. split; [exact Hf|]. split; [exact Bd0|].
    change (calln (mksig x k true true false) (denote_f cs (mksig x k true true false) (FPlainM e)) cvs vs M) with 0%uint63.
    assert (V : callm (mksig x k true true false) (denote_f cs (mksig x k true true false) (FPlainM e)) cvs vs M
                = denote_m cs dnum dmem (rev cvs) [] (rev vs) M e).
    { destruct x as [|x'].
      - destruct cvs; [|discriminate].
        change (callm (mksig 0 k true true false) (denote_f cs (mksig 0 k true true false) (FPlainM e)) [] vs M)
          with (appn k true true (absn k true true (fun env s => denote_m cs dnum dmem [] [] env s e)) vs M).
        rewrite appn_absn by auto. reflexivity.
      - destruct cvs as [|n rest]; [discriminate|]. simpl in Lc. injection Lc as Lc.
        change (callm (mksig (S x') k true true false) (denote_f cs (mksig (S x') k true true false) (FPlainM e)) (n :: rest) vs M)
          with (appn k true true (appc x' _ (absc x' _ (fun cenv => absn k true true (fun env s =>
                  denote_m cs dnum dmem (cenv ++ [n]) [] env s e))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto. reflexivity. }
    rewrite V. simpl kbody.
    refine (ctailm_ok P _ gidf (gidf j) mv cs false false false true 0 k j dnum dmem 0 _ _ _ _ Hcs Hlen Hj Hf e
                      _ _ _ _ _ _ _ _ M W _).
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
      * exact E0.
      * eapply lt_all_mono; eauto. lia.
      * exact C0.
      * eapply lt_all_mono; [exact LCmv | lia].
      * apply benv_ok_nil.
      * apply lt_all_nil.
      * exact (Forall_rev_cbound _ cvs Bpos Bd).
      * lia.
      * intros Habs; discriminate Habs.
  - (* a number made after memories *)
    destruct r; simpl in W; [discriminate|]. destruct w; simpl in W; [|discriminate]. destruct m; simpl in W; [|discriminate].
    cbv beta iota.
    intros cvs vs M Lc Lv Bd.
    destruct (bind_params x k cvs vs Lc Lv) as (rho0 & Bd0 & C0 & E0).
    assert (V : calln (mksig x k true false true) (denote_f cs (mksig x k true false true) (FPlainX xx)) cvs vs M
                = denote_x cs dnum dmem (rev cvs) [] (rev vs) M xx).
    { destruct x as [|x'].
      - destruct cvs; [|discriminate].
        change (calln (mksig 0 k true false true) (denote_f cs (mksig 0 k true false true) (FPlainX xx)) [] vs M)
          with (appn k true false (absn k true false (fun env s => denote_x cs dnum dmem [] [] env s xx)) vs M).
        rewrite appn_absn by auto. reflexivity.
      - destruct cvs as [|n rest]; [discriminate|]. simpl in Lc. injection Lc as Lc.
        change (calln (mksig (S x') k true false true) (denote_f cs (mksig (S x') k true false true) (FPlainX xx)) (n :: rest) vs M)
          with (appn k true false (appc x' _ (absc x' _ (fun cenv => absn k true false (fun env s =>
                  denote_x cs dnum dmem (cenv ++ [n]) [] env s xx))) rest) vs M).
        rewrite appc_absc by auto. rewrite appn_absn by auto. reflexivity. }
    rewrite V.
    exists (endx cs dnum dmem (rev cvs) [] (rev vs) M xx).
    exists (compile_f gidf j (mksig x k true false true) (FPlainX xx)), rho0. split; [exact Hf|]. split; [exact Bd0|].
    simpl kbody.
    refine (ctailx_ok P _ gidf (gidf j) mv cs false false false true 0 k j dnum dmem 0 _ _ _ _ Hcs Hlen Hj xx
                      _ _ _ _ _ _ _ _ M eq_refl eq_refl eq_refl W _).
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + intros Habs; discriminate Habs.
    + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
      * exact E0.
      * eapply lt_all_mono; eauto. lia.
      * exact C0.
      * eapply lt_all_mono; [exact LCmv | lia].
      * apply benv_ok_nil.
      * apply lt_all_nil.
      * exact (Forall_rev_cbound _ cvs Bpos Bd).
      * lia.
      * intros Habs; discriminate Habs.
Qed.

(** the callees' theorems, one after the other, as the callee assumption of the next function: [kitc.py --reflect] gives
    function [j] of a program the theorems of functions [0 .. j-1] this way *)
Fixpoint all_ok (P : prog) (gidf : nat -> ident) (cs : list callee) (k : nat) : Prop :=
  match cs with
  | [] => True
  | c :: r => (let '(existT _ gs h) := c in callee_ok P (gidf k) (cbz k) gs h) /\ all_ok P gidf r (S k)
  end.

Lemma all_ok_nth : forall P gidf cs k, all_ok P gidf cs k ->
  forall f, match nth_error cs f with Some (existT _ gs h) => callee_ok P (gidf (k + f)%nat) (cbz (k + f)) gs h | None => True end.
Proof.
  intros P gidf cs. unfold callee in *. induction cs as [|[gs h] r IH]; intros k H f; simpl in *.
  - destruct f; exact Logic.I.
  - destruct H as [H0 H1]. destruct f as [|f]; simpl.
    + rewrite Nat.add_0_r. exact H0.
    + rewrite <- Nat.add_succ_comm. exact (IH (S k) H1 f).
Qed.

Lemma all_ok_callees : forall P gidf cs, all_ok P gidf cs 0 -> callees_ok P gidf cs.
Proof. intros P gidf cs H f. exact (all_ok_nth P gidf cs 0 H f). Qed.
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
Definition sum_g := mksig 1 2 true false false.
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
Definition h_g := mksig 0 2 false false false.
Definition h_b := FPlain (SOp Badd (SOp Bmul (SVar 1) (SInt 2)) (SVar 0)).
Fixpoint loop (n : nat) (i acc : i63) (s : mem) : i63 :=
  match n with O => acc | S m => loop m (PrimInt63.add i 1) (h acc (KQ.KQRun.rd 0 i s)) s end.
Definition loop_g := mksig 1 2 true false false.
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
Definition long_g := mksig 1 1 true false false.
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
Definition fill_g := mksig 1 1 true true false.
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
Definition suffix_g := mksig 1 1 true true false.
Definition suffix_b := FRecM MCur (MLetM (MRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil) MCur)
  (MUpd (SInt 0) (SVar 0) (SOp Badd (SRd (SInt 0) (SVar 0)) (SRd (SInt 0) (SOp Badd (SVar 0) (SInt 1)))) MCur)).

(* a plain function giving back a memory: a test, a write, a call of [fill] on the written memory *)
Definition init (n : nat) (k : i63) (s : mem) : mem :=
  if PrimInt63.ltb k 10 then fill n k (KQ.KQRun.upd 1 0 k s) else KQ.KQRun.upd 1 0 0 s.
Definition init_g := mksig 1 1 true true false.
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
Definition chain_g := mksig 0 0 true true false.
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
Definition inner_g := mksig 1 1 false false false.
Definition inner_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)).
Definition rounds_g := mksig 2 1 false false false.
Definition rounds_b := FRec (SVar 0) (SRec (CCons (CVar 1) CNil) (SCons (SCall 0 (CCons (CVar 1) CNil) (SCons (SVar 0) SNil)) SNil)).
(* a match on a counter inside a body, a successor of a successor given to a callee *)
Definition twice (n : nat) (a : i63) : i63 := match n with O => a | S p => inner (S (S p)) a end.
Definition twice_g := mksig 1 1 false false false.
Definition twice_b := FPlain (SMatch 0 (SVar 0) (SCall 0 (CCons (CS (CS (CVar 0))) CNil) (SCons (SVar 0) SNil))).
(* a budget made from a number *)
Definition bud (x : i63) : i63 := inner (KQ.KQRun.kq_nat x) 0.
Definition bud_g := mksig 0 1 false false false.
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
(* a counter grown at every round of a recursion has no bound: refused by wf *)
Fixpoint grow (r n : nat) (acc : i63) : i63 := match r with O => acc | S m => grow m (S n) acc end.
Time Fail Definition grow_wf : wf_f [] (mksig 2 1 false false false) (FRec (SVar 0) (SRec (CCons (CS (CVar 1)) CNil) (SCons (SVar 0) SNil))) = true
  := eq_refl.

(* ---------------------------------------------------------------- a choice between two numbers: a conditional move *)
(* the smaller of two numbers written into a cell (CF295B's inner loop): both worked out, one taken, no jump (D17) *)
Fixpoint relax (n : nat) (j d : i63) (s : mem) : mem :=
  match n with
  | O => s
  | S m => let a := KQ.KQRun.rd 0 j s in let b := PrimInt63.add d (KQ.KQRun.rd 1 j s) in
           relax m (PrimInt63.add j 1) d (KQ.KQRun.upd 0 j (if PrimInt63.ltb b a then b else a) s)
  end.
Definition relax_g := mksig 1 2 true true false.
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
(* tests made of [&&], [||], [negb] choosing between two numbers: conditional moves on the booleans' values, no jump *)
Definition chk (s : mem) : i63 :=
  PrimInt63.add (if andb (PrimInt63.ltb (KQ.KQRun.rd 0 0 s) 500) (PrimInt63.ltb (KQ.KQRun.rd 0 1 s) 500) then 0 else 1)
    (PrimInt63.add (if orb (PrimInt63.ltb (KQ.KQRun.rd 0 5 s) 500) (PrimInt63.ltb (KQ.KQRun.rd 0 6 s) 500) then 0 else 7)
       (if negb (PrimInt63.ltb (KQ.KQRun.rd 0 11 s) 500) then 0 else 31)).
Definition chk_g := mksig 0 0 true false false.
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
Definition cnt_in_g := mksig 1 4 true false false.
Definition cnt_in_b := FRec (SVar 0) (SLet (SRd (SInt 0) (SVar 3)) (SLetB (BAnd (BCmp Cle (SVar 3) (SVar 0)) (BCmp Clt (SVar 0) (SVar 2)))
  (SIfB (BVar 0) (SRec CNil (SCons (SOp Badd (SVar 4) (SInt 1)) (SCons (SVar 3) (SCons (SVar 2) (SCons (SOp Badd (SVar 1) (SInt 1)) SNil)))))
                 (SRec CNil (SCons (SOp Badd (SVar 4) (SInt 1)) (SCons (SVar 3) (SCons (SVar 2) (SCons (SVar 1) SNil)))))))).
(* a memory chosen by [a && negb b]: jumps *)
Definition mark (v q m l : i63) (s : mem) : mem :=
  if andb (PrimInt63.leb m l) (negb (PrimInt63.eqb (KQ.KQRun.rd 1 v s) q)) then KQ.KQRun.upd 1 v q s else s.
Definition mark_g := mksig 0 4 true true false.
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
Definition tw_g := mksig 1 1 false false false.
Definition tw_b := FRec (SVar 0) (SOp Badd (SRec CNil (SCons (SVar 0) SNil)) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil))).
Definition big_g := mksig 0 1 false false false.
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
Definition bump_g := mksig 0 1 true true false.
Definition bump_b := FPlainM (MUpd (SInt 0) (SVar 0) (SOp Badd (SRd (SInt 0) (SOp Bsub (SVar 0) (SInt 1))) (SVar 0)) MCur).
Definition after_g := mksig 1 1 true false true.
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
Check (eq_refl : wf_f [after_g] (mksig 1 1 true false false) (FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil))) = false).

(* ---------------------------------------------------------------- two calls of the function itself merged into one *)
(* the smallest of the cells and where it is (CF868F's loop): [if v <? best then f .. v i s else f .. best opt s] is one
   loop step whose two differing arguments are chosen by conditional moves (D17), no jump *)
Fixpoint argmin (n : nat) (i best opt : i63) (s : mem) : i63 :=
  match n with
  | O => opt
  | S m => let v := KQ.KQRun.rd 0 i s in
           if PrimInt63.ltb v best then argmin m (PrimInt63.add i 1) v i s else argmin m (PrimInt63.add i 1) best opt s
  end.
Definition argmin_g := mksig 1 3 true false false.
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
Definition acc32_g := mksig 1 1 true true false.
Definition acc32_b := FRecM MCur (MRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)
  (MUpd32 (SInt 1) (SVar 0) (SOp Badd (SRd32 (SInt 1) (SOp Bsub (SVar 0) (SInt 1))) (SVar 0)) MCur)).
Definition sum32_g := mksig 1 2 true false false.
Definition sum32_b := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SOp Badd (SVar 0) (SRd32 (SInt 1) (SVar 1))) SNil))).
Definition nar_P := mkprog [(gid1 0, compile_f gid1 0 acc32_g acc32_b); (gid1 1, compile_f gid1 1 sum32_g sum32_b)] [].
Time Lemma acc32_ok : callee_ok nar_P (gid1 0) (cbz 0) acc32_g acc32.
Proof. Time exact_no_check (compile_f_ok nar_P [] gid1 0 acc32_g acc32_b eq_refl eq_refl (no_callees nar_P gid1) eq_refl eq_refl). Time Qed.
Time Lemma sum32_ok : callee_ok nar_P (gid1 1) (cbz 1) sum32_g sum32.
Proof. Time exact_no_check (compile_f_ok nar_P [] gid1 1 sum32_g sum32_b eq_refl eq_refl (no_callees nar_P gid1) eq_refl eq_refl). Time Qed.
Print Assumptions acc32_ok.
