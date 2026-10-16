(** The code generator: KQL to CompCert Clight.

    A 63-bit integer is held in an unsigned 64-bit C variable with the
    top bit clear.  Wrapping operations are masked back to 63 bits;
    division by zero and over-wide shifts are guarded so the C has no
    undefined behaviour.  Variables become C temporaries (registers):
    source variable [x] is temporary [xO x]; [Eloop]'s scratch
    temporaries are [xI _], so the two never meet.  Each function body
    is wrapped in [Sloop]; [Eloop] assigns the parameters and
    [continue]s. *)

From Stdlib Require Import ZArith List Uint63.
From compcert Require Import Coqlib Maps Integers AST Ctypes Cop Clight.
From KQC Require Import KQL.
Import ListNotations.

Definition tyl : type := Tlong Unsigned noattr.
Definition tyb : type := Tint I32 Signed noattr.

Definition tv (x : ident) : ident := xO x.
Definition sc (i : nat) : ident := xI (Pos.of_succ_nat i).

Definition c64 (n : Z) : expr := Econst_long (Int64.repr n) tyl.
Definition mask63 : Z := 2 ^ 63 - 1.

Definition tr_atom (a : atom) : expr :=
  match a with
  | Avar x => Etempvar (tv x) tyl
  | Aint n => c64 (to_Z n)
  end.

Definition bin (op : Cop.binary_operation) (a b : expr) : expr := Ebinop op a b tyl.
Definition masked (e : expr) : expr := Ebinop Oand e (c64 mask63) tyl.
Definition cmpe (op : Cop.binary_operation) (a b : expr) : expr := Ebinop op a b tyb.

Definition tr_op (x : ident) (o : binop) (A B : expr) : statement :=
  let t := tv x in
  match o with
  | Badd => Sset t (masked (bin Oadd A B))
  | Bsub => Sset t (masked (bin Osub A B))
  | Bmul => Sset t (masked (bin Omul A B))
  | Bland => Sset t (bin Oand A B)
  | Blor => Sset t (bin Oor A B)
  | Blxor => Sset t (bin Oxor A B)
  | Bdiv => Sifthenelse (cmpe Oeq B (c64 0)) (Sset t (c64 0)) (Sset t (bin Odiv A B))
  | Bmod => Sifthenelse (cmpe Oeq B (c64 0)) (Sset t A) (Sset t (bin Omod A B))
  | Blsl => Sifthenelse (cmpe Olt B (c64 63)) (Sset t (masked (bin Oshl A B))) (Sset t (c64 0))
  | Blsr => Sifthenelse (cmpe Olt B (c64 63)) (Sset t (bin Oshr A B)) (Sset t (c64 0))
  end.

Definition tr_cmp (c : cmpop) : Cop.binary_operation :=
  match c with Ceq => Oeq | Clt => Olt | Cle => Ole end.

Fixpoint tylist (n : nat) : list type :=
  match n with O => [] | S n => tyl :: tylist n end.

Definition funty (n : nat) : type := Tfunction (tylist n) tyl cc_default.

Fixpoint set_scratch (i : nat) (args : list atom) : statement :=
  match args with
  | [] => Sskip
  | a :: l => Ssequence (Sset (sc i) (tr_atom a)) (set_scratch (S i) l)
  end.

Fixpoint set_params (i : nat) (ps : list ident) : statement :=
  match ps with
  | [] => Sskip
  | p :: l => Ssequence (Sset (tv p) (Etempvar (sc i) tyl)) (set_params (S i) l)
  end.

Definition tarr (n : Z) : type := Tarray tyl n noattr.

(** Cell [I] of memory block [h] (an array of [n] cells). *)
Definition cell (h : ident) (n : Z) (I : expr) : expr :=
  Ederef (Ebinop Oadd (Evar h (tarr n)) I (Tpointer tyl noattr)) tyl.

Section TR.
Variable P : prog.

Fixpoint tr_exp (ps : list ident) (e : exp) : statement :=
  match e with
  | Eret a => Sreturn (Some (tr_atom a))
  | Eop x o a b k => Ssequence (tr_op x o (tr_atom a) (tr_atom b)) (tr_exp ps k)
  | Eif c a b t f =>
      Sifthenelse (cmpe (tr_cmp c) (tr_atom a) (tr_atom b)) (tr_exp ps t) (tr_exp ps f)
  | Ecall x g args k =>
      Ssequence (Scall (Some (tv x)) (Evar g (funty (length args))) (map tr_atom args))
                (tr_exp ps k)
  | Eload x h i k =>
      match asize P h with
      | Some n =>
          Ssequence
            (Sifthenelse (cmpe Olt (tr_atom i) (c64 n))
               (Sset (tv x) (cell h n (tr_atom i))) (Sset (tv x) (c64 0)))
            (tr_exp ps k)
      | None => Sskip
      end
  | Estore h i a k =>
      match asize P h with
      | Some n =>
          Ssequence
            (Sifthenelse (cmpe Olt (tr_atom i) (c64 n))
               (Sassign (cell h n (tr_atom i)) (tr_atom a)) Sskip)
            (tr_exp ps k)
      | None => Sskip
      end
  | Eloop args => Ssequence (set_scratch 0 args) (Ssequence (set_params 0 ps) Scontinue)
  end.

Fixpoint binders (e : exp) : list ident :=
  match e with
  | Eret _ | Eloop _ => []
  | Eop x _ _ _ k | Ecall x _ _ k | Eload x _ _ k => tv x :: binders k
  | Estore _ _ _ k => binders k
  | Eif _ _ _ t f => binders t ++ binders f
  end.

Definition notin (ps : list ident) (t : ident) : bool :=
  negb (existsb (Pos.eqb t) ps).

Definition tr_fn (f : fn) : function :=
  let ps := map tv (kparams f) in
  {| fn_return := tyl;
     fn_callconv := cc_default;
     fn_params := map (fun p => (p, tyl)) ps;
     fn_vars := [];
     fn_temps := map (fun t => (t, tyl))
                   (filter (notin ps) (nodup Pos.eq_dec (binders (kbody f)))
                    ++ map sc (seq 0 (length (kparams f))));
     fn_body := Sloop (tr_exp (kparams f) (kbody f)) Sskip |}.

End TR.

Definition tr_defs (P : prog) : list (ident * globdef fundef type) :=
  map (fun gf => (fst gf, Gfun (Internal (tr_fn P (snd gf))))) (pfuns P).

(** A memory block is a zero-initialised, writable global array. *)
Definition arr_var (n : Z) : globvar type :=
  {| gvar_info := tarr n; gvar_init := [Init_space (8 * n)];
     gvar_readonly := false; gvar_volatile := false |}.

Definition tr_arrs (P : prog) : list (ident * globdef fundef type) :=
  map (fun hn => (fst hn, Gvar (arr_var (snd hn)))) (parrs P).

(** [main] calls function [g] on constant arguments and returns the low
    32 bits of the result as the exit code. *)
Definition rtemp : ident := 1%positive.

Definition main_fn (g : ident) (args : list i63) : function :=
  {| fn_return := type_int32s;
     fn_callconv := cc_default;
     fn_params := [];
     fn_vars := [];
     fn_temps := [(rtemp, tyl)];
     fn_body :=
       Ssequence
         (Scall (Some rtemp) (Evar g (funty (length args))) (map (fun n => c64 (to_Z n)) args))
         (Sreturn (Some (Ecast (Etempvar rtemp tyl) type_int32s))) |}.

Definition tr_program (P : prog) (mainid g : ident) (args : list i63) : Clight.program :=
  {| prog_defs := tr_defs P ++ tr_arrs P ++ [(mainid, Gfun (Internal (main_fn g args)))];
     prog_public := [mainid];
     prog_main := mainid;
     prog_types := [];
     prog_comp_env := PTree.empty _;
     prog_comp_env_eq := eq_refl |}.
