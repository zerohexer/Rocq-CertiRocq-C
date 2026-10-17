(** Printing the generated Clight as C text, for the subset the generator
    emits.  NOT verified: it is used to measure speed through ccomp /
    clang.  The proved route is the Clight AST itself. *)

From Stdlib Require Import ZArith List String Ascii.
From compcert Require Import Coqlib Maps Integers AST Ctypes Cop Clight.
From KQC Require Import KQL KQLGen.
Import ListNotations.
Local Open Scope string_scope.

Fixpoint digits (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | O => acc
  | S f =>
      let c := String (ascii_of_nat (48 + Z.to_nat (Z.modulo z 10))) acc in
      if Z.eqb (Z.div z 10) 0 then c else digits f (Z.div z 10) c
  end.

Definition zstr (z : Z) : string := digits 30 z "".

Definition nl := String (ascii_of_nat 10) "".

Definition tname (id : ident) : string := "t" ++ zstr (Zpos id).

Section P.
Variable mainid : ident.
Definition gname (id : ident) : string :=
  if peq id mainid then "main" else "f" ++ zstr (Zpos id).

Definition opstr (o : Cop.binary_operation) : string :=
  match o with
  | Oadd => "+" | Osub => "-" | Omul => "*" | Odiv => "/" | Omod => "%"
  | Oand => "&" | Oor => "|" | Oxor => "^" | Oshl => "<<" | Oshr => ">>"
  | Oeq => "==" | One => "!=" | Olt => "<" | Ogt => ">" | Ole => "<=" | Oge => ">="
  end.

Definition tystr (t : type) : string :=
  match t with
  | Tlong Signed _ => "long long"
  | Tlong Unsigned _ => "unsigned long long"
  | Tint _ Unsigned _ => "unsigned int"
  | Tpointer (Tint I8 _ _) _ => "char *"
  | Tpointer (Tint I32 _ _) _ => "int *"
  | Tpointer (Tlong _ _) _ => "unsigned long long *"
  | _ => "int"
  end.

Definition tyb' : type := Tint I32 Signed noattr.

Fixpoint estr (e : expr) : string :=
  match e with
  | Etempvar id _ => tname id
  | Econst_long n _ => zstr (Int64.unsigned n) ++ "ULL"
  | Ebinop o a b _ => "(" ++ estr a ++ " " ++ opstr o ++ " " ++ estr b ++ ")"
  | Ecast a t => "((" ++ tystr t ++ ")" ++ estr a ++ ")"
  | Evar id _ => gname id
  | Ederef a _ => "(*" ++ estr a ++ ")"
  | _ => "/*?*/"
  end.

(** A choice between two atoms on a comparison is the kit's [kq_sel_*] (a conditional move written out, kq_io.h), not a jump. *)
Definition atomic (e : expr) : bool :=
  match e with Etempvar _ _ | Econst_long _ _ => true | _ => false end.

Definition is_signed_cast (e : expr) : option expr :=
  match e with Ecast a (Tlong Signed _) => Some a | _ => None end.

Definition selkind (op : Cop.binary_operation) (X Y : expr) : option (string * expr * expr) :=
  match op with
  | Oeq => Some ("kq_sel_eq", X, Y)
  | Olt => match is_signed_cast X, is_signed_cast Y with
           | Some x, Some y => Some ("kq_sel_lts", x, y)
           | _, _ => Some ("kq_sel_ltu", X, Y) end
  | Ole => match is_signed_cast X, is_signed_cast Y with
           | Some x, Some y => Some ("kq_sel_les", x, y)
           | _, _ => Some ("kq_sel_leu", X, Y) end
  | _ => None
  end.

(** the guards of the kit's memory (block number below 64, cell below the size) are met nearly always *)
Definition likely (c : expr) : bool :=
  match c with
  | Ebinop Olt _ (Econst_long n _) _ => Int64.eq n (Int64.repr 128)
  | Ebinop Olt _ (Ecast (Ederef _ _) _) _ => true
  | _ => false
  end.

Fixpoint args (l : list expr) : string :=
  match l with
  | [] => ""
  | [a] => estr a
  | a :: l => estr a ++ ", " ++ args l
  end.

Fixpoint sstr (s : statement) : string :=
  match s with
  | Sskip => ""
  | Sset id e => tname id ++ " = " ++ estr e ++ ";" ++ nl
  | Sassign a e => estr a ++ " = " ++ estr e ++ ";" ++ nl
  | Ssequence a b => sstr a ++ sstr b
  | Sifthenelse (Ebinop op X Y _) (Sset t a) (Sset t' b) =>
      match selkind op X Y with
      | Some (nm, X', Y') =>
          if Pos.eqb t t' && atomic a && atomic b then
            tname t ++ " = " ++ nm ++ "(" ++ estr X' ++ ", " ++ estr Y' ++ ", " ++ estr a ++ ", " ++ estr b ++ ");" ++ nl
          else "if " ++ estr (Ebinop op X Y tyb') ++ " {" ++ nl ++ (tname t ++ " = " ++ estr a ++ ";" ++ nl) ++ "} else {" ++ nl ++ (tname t' ++ " = " ++ estr b ++ ";" ++ nl) ++ "}" ++ nl
      | None => "if " ++ estr (Ebinop op X Y tyb') ++ " {" ++ nl ++ (tname t ++ " = " ++ estr a ++ ";" ++ nl) ++ "} else {" ++ nl ++ (tname t' ++ " = " ++ estr b ++ ";" ++ nl) ++ "}" ++ nl
      end
  | Sifthenelse c a b => (if likely c then "if (__builtin_expect(" ++ estr c ++ ", 1)) {" else "if " ++ estr c ++ " {") ++ nl ++ sstr a ++ "} else {" ++ nl ++ sstr b ++ "}" ++ nl
  | Sloop a _ => "for (;;) {" ++ nl ++ sstr a ++ "}" ++ nl
  | Sreturn (Some e) => "return " ++ estr e ++ ";" ++ nl
  | Scall (Some id) f l => tname id ++ " = " ++ estr f ++ "(" ++ args l ++ ");" ++ nl
  | Scontinue => "continue;" ++ nl
  | _ => "/*?*/" ++ nl
  end.

Fixpoint params (l : list (ident * type)) : string :=
  match l with
  | [] => "void"
  | [(id, t)] => tystr t ++ " " ++ tname id
  | (id, t) :: l => tystr t ++ " " ++ tname id ++ ", " ++ params l
  end.

Definition head (id : ident) (f : function) : string :=
  tystr (fn_return f) ++ " " ++ gname id ++ "(" ++ params (fn_params f) ++ ")".

Definition fstr (id : ident) (f : function) : string :=
  head id f ++ " {" ++ nl ++
  String.concat "" (map (fun it => tystr (snd it) ++ " " ++ tname (fst it) ++ ";" ++ nl) (fn_temps f)) ++
  sstr (fn_body f) ++ "}" ++ nl.

Definition protos (l : list (ident * globdef fundef type)) : string :=
  String.concat "" (map (fun d => match snd d with
                                  | Gfun (Internal f) => head (fst d) f ++ ";" ++ nl
                                  | Gvar v => match gvar_info v with
                                              | Tarray (Tpointer (Tint _ _ _) _) n _ => "extern int *" ++ gname (fst d) ++ "[" ++ zstr n ++ "];" ++ nl
                                              | Tarray (Tpointer _ _) n _ => "extern unsigned long long *" ++ gname (fst d) ++ "[" ++ zstr n ++ "];" ++ nl
                                              | Tarray (Tint _ _ _) n _ => "extern unsigned int " ++ gname (fst d) ++ "[" ++ zstr n ++ "];" ++ nl
                                              | Tarray _ n _ =>
                                                  (if Pos.ltb 89999 (fst d) then "extern " else "") ++
                                                  "unsigned long long " ++ gname (fst d) ++ "[" ++ zstr n ++ "];" ++ nl
                                              | _ => "" end
                                  | _ => "" end) l).

Definition pstr (p : Clight.program) : string :=
  protos (prog_defs p) ++
  String.concat "" (map (fun d => match snd d with
                                  | Gfun (Internal f) => fstr (fst d) f
                                  | _ => "" end) (prog_defs p)).
End P.
