(** KQL: a small first-order language for kit-style integer programs.

    Values are Rocq's primitive 63-bit integers.  A program is a list of
    functions and a list of memory blocks (fixed-size arrays of
    integers, zero at the start).  A function body is in A-normal form:
    arithmetic on atoms, a two-way branch on a comparison, a call whose
    result is bound, a load and a store (out of range: a load gives 0,
    a store does nothing, as in the kit), a return, and [Eloop], a call
    of the function itself in tail position (compiled to a jump).  The
    semantics is big-step and relational and threads the memory. *)

From Stdlib Require Import ZArith List Uint63.
From compcert Require Import Coqlib Maps AST.
Require KQ.KQRun.
Import ListNotations.

Notation i63 := PrimInt63.int.

Inductive binop := Badd | Bsub | Bmul | Bland | Blor | Blxor | Bdiv | Bmod | Blsl | Blsr | Basr | Bmods | Bdivs.
(* Clt, Cle: the unsigned order; Cslt, Csle: the signed order *)
Inductive cmpop := Ceq | Clt | Cle | Cslt | Csle.

(* [Abud n]: a loop budget written as a number, [kq_nat n] (KQRun.v), that is [n] if positive (at most 2^60), else 0: held as that number, so
   that the program is printed without building the unary [nat] *)
Inductive atom := Avar (x : ident) | Aint (n : i63) | Abud (n : i63).

Definition bud (n : i63) : i63 := if PrimInt63.lesb n 0%uint63 then 0%uint63 else if PrimInt63.lesb n 1152921504606846976%uint63 then n else 1152921504606846976%uint63.

(** The machine's operations (KQRun.v, hw/kq_hw.h): a device access, an atomic, a fence, bytes in bulk, code at an address.
    Each takes the memory and gives it back; what one reads goes into a cell of a wide block. *)
Inductive hwop := HLoad | HStore | HStore64 | HAtomic | HAtomic64 | HCas | HCas64 | HALoad | HAStore | HAStore64 | HFence | HCopy | HFill | HCmp | HCall | HRun | HCodeSync | HIrqTake | HUser | HGrow.
(** the machine's numbers that need no memory: the address of a narrow block, what the runtime knows *)
Inductive hwfop := FAddr | FIrqInfo | FIrqEntry | FCpuCode | FSym | FUser.
Definition hw_arity (o : hwop) : nat :=
  match o with
  | HLoad => 4
  | HStore => 3
  | HStore64 => 3
  | HAtomic => 6
  | HAtomic64 => 6
  | HCas => 6
  | HCas64 => 7
  | HALoad => 4
  | HAStore => 3
  | HAStore64 => 3
  | HFence => 1
  | HCopy => 3
  | HFill => 3
  | HCmp => 5
  | HCall => 4
  | HRun => 10
  | HCodeSync => 2
  | HIrqTake => 2
  | HUser => 5
  | HGrow => 2
  end.

Definition hwf_arity (o : hwfop) : nat :=
  match o with FUser => 5 | _ => 1 end.

Inductive exp :=
| Eret (a : atom)
| Eop (x : ident) (o : binop) (a b : atom) (k : exp)
| Eif (c : cmpop) (a b : atom) (t f : exp)
| Esel (x : ident) (c : cmpop) (a b : atom) (t f : atom) (k : exp)   (* x := if a c b then t else f *)
| Ecall (x : ident) (g : ident) (args : list atom) (k : exp)
| Eload (x : ident) (h : ident) (i : atom) (k : exp)
| Estore (h : ident) (i a : atom) (k : exp)
| Ekld (x : ident) (h i : atom) (k : exp)        (* x := cell i of block h of the kit's memory (KQM.v) *)
| Ekst (h i a : atom) (k : exp)                  (* cell i of block h of the kit's memory := a *)
| Ekld32 (x : ident) (h i : atom) (k : exp)      (* x := cell i of narrow block h (4-byte cells), signed *)
| Ekst32 (h i a : atom) (k : exp)                (* cell i of narrow block h := a, kept modulo 2^32 *)
| Ew64 (o : KQ.KQRun.w64op) (xl xh : ident) (al ah bl bh : atom) (k : exp)   (* (xl, xh) := the u64 (al, ah) o the u64 (bl, bh) (KQRun.v w64_op) *)
| Ekld8 (x : ident) (h i : atom) (k : exp)       (* x := byte i of narrow block h (KQRun.v rd8) *)
| Ekst8 (h i a : atom) (k : exp)                 (* byte i of narrow block h := a mod 256 (KQRun.v upd8) *)
| Eksize (x : ident) (h : atom) (k : exp)        (* x := the size of block h of the kit's memory (KQRun.v kq_size) *)
| Ehwf (o : hwfop) (x : ident) (args : list atom) (k : exp)   (* x := a machine number of args *)
| Ehw (o : hwop) (args : list atom) (k : exp)    (* a machine operation on the kit's memory (KQM.v) *)
| Eloop (args : list atom).

Record fn := mkfn { kparams : list ident; kbody : exp }.

Record prog := mkprog { pfuns : list (ident * fn); parrs : list (ident * Z) }.

Definition binop_sem (o : binop) (a b : i63) : i63 :=
  match o with
  | Badd => PrimInt63.add a b
  | Bsub => PrimInt63.sub a b
  | Bmul => PrimInt63.mul a b
  | Bland => PrimInt63.land a b
  | Blor => PrimInt63.lor a b
  | Blxor => PrimInt63.lxor a b
  | Bdiv => PrimInt63.div a b
  | Bmod => PrimInt63.mod a b
  | Blsl => PrimInt63.lsl a b
  | Blsr => PrimInt63.lsr a b
  | Basr => PrimInt63.asr a b
  | Bmods => PrimInt63.mods a b
  | Bdivs => PrimInt63.divs a b
  end.

Definition cmp_sem (c : cmpop) (a b : i63) : bool :=
  match c with
  | Ceq => PrimInt63.eqb a b
  | Clt => PrimInt63.ltb a b
  | Cle => PrimInt63.leb a b
  | Cslt => PrimInt63.ltsb a b
  | Csle => PrimInt63.lesb a b
  end.

Definition env := PTree.t i63.

Definition aval (rho : env) (a : atom) : option i63 :=
  match a with Avar x => rho ! x | Aint n => Some n | Abud n => Some (bud n) end.

Fixpoint avals (rho : env) (l : list atom) : option (list i63) :=
  match l with
  | [] => Some []
  | a :: l => match aval rho a, avals rho l with
              | Some v, Some vs => Some (v :: vs)
              | _, _ => None end
  end.

(** Binding the parameters; the lengths must agree. *)
Fixpoint bind (xs : list ident) (vs : list i63) (rho : env) : option env :=
  match xs, vs with
  | [], [] => Some rho
  | x :: xs, v :: vs => bind xs vs (PTree.set x v rho)
  | _, _ => None
  end.

Fixpoint assoc {A} (l : list (ident * A)) (g : ident) : option A :=
  match l with
  | [] => None
  | (h, f) :: l => if peq g h then Some f else assoc l g
  end.

Definition find (P : prog) (g : ident) : option fn := assoc (pfuns P) g.
Definition asize (P : prog) (h : ident) : option Z := assoc (parrs P) h.

(** Memory: block [h], cell [j].  Only cells [0 <= j < size] matter. *)
Definition kmem := ident -> Z -> i63.
Definition mem0 : kmem := fun _ _ => 0%uint63.

Definition inb (n : Z) (i : i63) : bool := Z.ltb (to_Z i) n.

Definition rd (M : kmem) (n : Z) (h : ident) (i : i63) : i63 :=
  if inb n i then M h (to_Z i) else 0%uint63.

Definition upd (M : kmem) (h : ident) (j : Z) (v : i63) : kmem :=
  fun h' j' => if peq h' h then (if Z.eq_dec j' j then v else M h' j') else M h' j'.

Definition wr (M : kmem) (n : Z) (h : ident) (i : i63) (v : i63) : kmem :=
  if inb n i then upd M h (to_Z i) v else M.

Inductive eval (P : prog) : fn -> env -> kmem -> exp -> i63 -> kmem -> Prop :=
| E_ret : forall f rho M a v,
    aval rho a = Some v ->
    eval P f rho M (Eret a) v M
| E_op : forall f rho M x o a b va vb k v M',
    aval rho a = Some va -> aval rho b = Some vb ->
    eval P f (PTree.set x (binop_sem o va vb) rho) M k v M' ->
    eval P f rho M (Eop x o a b k) v M'
| E_if : forall f rho M c a b t e va vb v M',
    aval rho a = Some va -> aval rho b = Some vb ->
    eval P f rho M (if cmp_sem c va vb then t else e) v M' ->
    eval P f rho M (Eif c a b t e) v M'
| E_sel : forall f rho M x c a b t e va vb vt ve k v M',
    aval rho a = Some va -> aval rho b = Some vb -> aval rho t = Some vt -> aval rho e = Some ve ->
    eval P f (PTree.set x (if cmp_sem c va vb then vt else ve) rho) M k v M' ->
    eval P f rho M (Esel x c a b t e k) v M'
| E_call : forall f rho M x g args vs fg rho' w M1 k v M',
    find P g = Some fg ->
    avals rho args = Some vs ->
    bind (kparams fg) vs (PTree.empty _) = Some rho' ->
    eval P fg rho' M (kbody fg) w M1 ->
    eval P f (PTree.set x w rho) M1 k v M' ->
    eval P f rho M (Ecall x g args k) v M'
| E_load : forall f rho M x h i n vi k v M',
    asize P h = Some n -> aval rho i = Some vi ->
    eval P f (PTree.set x (rd M n h vi) rho) M k v M' ->
    eval P f rho M (Eload x h i k) v M'
| E_store : forall f rho M h i a n vi va k v M',
    asize P h = Some n -> aval rho i = Some vi -> aval rho a = Some va ->
    eval P f rho (wr M n h vi va) k v M' ->
    eval P f rho M (Estore h i a k) v M'
| E_loop : forall f rho M args vs rho' v M',
    avals rho args = Some vs ->
    bind (kparams f) vs (PTree.empty _) = Some rho' ->
    eval P f rho' M (kbody f) v M' ->
    eval P f rho M (Eloop args) v M'.

(** Running function [g] of [P] on [vs] from memory [M]. *)
Definition run (P : prog) (g : ident) (vs : list i63) (M : kmem) (v : i63) (M' : kmem) : Prop :=
  exists fg rho, find P g = Some fg /\
    bind (kparams fg) vs (PTree.empty _) = Some rho /\ eval P fg rho M (kbody fg) v M'.
