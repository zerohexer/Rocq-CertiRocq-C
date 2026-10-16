(** The translator: a kit-style Rocq program to KQL, plus the statement
    that each KQL function computes its Rocq function.

    `kql_translate main` reads [main] and every function of the same file
    it uses and defines, for each function [f], the KQL function [f_kql],
    the program [main_kqlprog], and the statement [f_stmt].  Each
    statement is then proved by [kql_auto] (KQLAuto.v) and checked by
    Rocq's kernel.  Nothing about the translator is trusted: a wrong
    translation is a statement that does not prove.

    What it reads (anything else is refused, with a message):
    - parameters: [nat] (a counter; the recursion argument comes first),
      [i63], and at most one memory [kmem], last;
    - a result of type [i63] or [kmem];
    - in a body: [match] on a [nat] parameter, [if] on a comparison of
      two numbers, [let], arithmetic of [PrimInt63], [rd]/[wr] of
      KQL.v, [ofn] of a counter, calls of the file's functions, and
      closed constants (a number written in the program);
    - a helper of the file that does not call itself is written out;
    - a memory is used only while it is the current one. *)

From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Template Require Import All.
From Stdlib Require Import ZArith Uint63 List.
From compcert Require Import Maps.
From KQC Require Import KQL KQLAuto.
Import MonadNotation ListNotations.
Open Scope bs.

(* ------------------------------------------------------------------ names *)
Definition eq_mp (a b : modpath) : bool := match ModPathComp.compare a b with Eq => true | _ => false end.
Definition kn_of (t : term) : kername := match t with tConst kn _ => kn | _ => (MPfile [], "") end.
Definition ind_of (t : term) : inductive :=
  match t with tInd i _ => i | _ => {| inductive_mind := (MPfile [], ""); inductive_ind := 0 |} end.

Definition kn_ofn := kn_of <% ofn %>.
Definition kn_rd := kn_of <% rd %>.
Definition kn_wr := kn_of <% wr %>.
Definition kn_mem0 := kn_of <% mem0 %>.
Definition kn_kmem := kn_of <% kmem %>.
Definition kn_int := kn_of <% PrimInt63.int %>.
Definition ind_nat := ind_of <% nat %>.
Definition ind_bool := ind_of <% bool %>.

Definition prim_mp : modpath := fst (kn_of <% PrimInt63.add %>).

(* KQL syntax, as terms *)
Definition q_Avar := <% Avar %>.
Definition q_Aint := <% Aint %>.
Definition q_Eret := <% Eret %>.
Definition q_Eop := <% Eop %>.
Definition q_Eif := <% Eif %>.
Definition q_Ecall := <% Ecall %>.
Definition q_Eload := <% Eload %>.
Definition q_Estore := <% Estore %>.
Definition q_Eloop := <% Eloop %>.
Definition q_mkfn := <% mkfn %>.
Definition q_mkprog := <% mkprog %>.
Definition q_atom := <% atom %>.
Definition q_ident := <% positive %>.
Definition q_fn := <% fn %>.
Definition q_cons := <% @cons %>.
Definition q_nil := <% @nil %>.
Definition q_pair := <% @pair %>.
Definition q_prod := <% @prod %>.
Definition q_Z := <% Z %>.
Definition q_i63 := <% PrimInt63.int %>.
Definition q_ofn := <% ofn %>.
Definition q_xI := <% xI %>.
Definition q_xO := <% xO %>.
Definition q_xH := <% xH %>.
Definition q_run := <% run %>.
Definition q_Zlt := <% Z.lt %>.
Definition q_Zofnat := <% Z.of_nat %>.
Definition q_natadd := <% Nat.add %>.
Definition q_wB := <% wB %>.
Definition q_kmem := <% kmem %>.
Definition q_ex := <% @ex %>.
Definition q_zero : term := tInt 0%uint63.

Definition binop_of (s : ident) : option term :=
  if s == "add" then Some <% Badd %> else if s == "sub" then Some <% Bsub %>
  else if s == "mul" then Some <% Bmul %> else if s == "land" then Some <% Bland %>
  else if s == "lor" then Some <% Blor %> else if s == "lxor" then Some <% Blxor %>
  else if s == "div" then Some <% Bdiv %> else if s == "mod" then Some <% Bmod %>
  else if s == "lsl" then Some <% Blsl %> else if s == "lsr" then Some <% Blsr %> else None.

Definition cmp_of (s : ident) : option term :=
  if s == "eqb" then Some <% Ceq %> else if s == "ltb" then Some <% Clt %>
  else if s == "leb" then Some <% Cle %> else None.

Fixpoint qpos (p : positive) : term :=
  match p with xI p => tApp q_xI [qpos p] | xO p => tApp q_xO [qpos p] | xH => q_xH end.

Fixpoint qlist (ty : term) (l : list term) : term :=
  match l with [] => tApp q_nil [ty] | x :: l => tApp q_cons [ty; x; qlist ty l] end.

Definition avar (x : positive) : term := tApp q_Avar [qpos x].
Definition aint (t : term) : term := tApp q_Aint [t].

(* ------------------------------------------------------------------ the result monad *)
Inductive tres (A : Type) := TOk (a : A) | TErr (m : string).
Arguments TOk {A}. Arguments TErr {A}.

(* ------------------------------------------------------------------ what the translator knows *)
Inductive kind := KNat | KInt | KMem.

Record finfo := mkFI {
  fi_kn : kername;            (* the Rocq function *)
  fi_id : positive;           (* its KQL name *)
  fi_kinds : list kind;       (* its parameters *)
  fi_rmem : bool;             (* it gives back a memory *)
  fi_rec : bool }.            (* it calls itself *)

(* what a variable of the text stands for *)
Inductive ent :=
| ENat (a : term)       (* a counter, held in KQL as the atom [a] = ofn of it *)
| EInt (a : term)       (* a number, the atom [a] *)
| EMem                  (* the current memory *)
| EDead                 (* a memory that was handed on: no longer usable *)
| ESelf.                (* the function being read, calling itself *)

Record st := mkSt { s_next : positive; s_arrs : list (term * term) }.

Section TR.
Variable Σ : global_env.
Variable mp : modpath.                   (* the file of the program *)
Variable fns : list finfo.
Variable self : finfo.

Definition find_fn (kn : kername) : option finfo :=
  List.find (fun f => Kername.eqb (fi_kn f) kn) fns.

(* a helper of the file that is written out where it is used *)
Definition helper_body (kn : kername) : option term :=
  if eq_mp (fst kn) mp then
    match find_fn kn with
    | Some _ => None
    | None => match lookup_env Σ kn with Some (ConstantDecl cb) => cst_body cb | _ => None end
    end
  else None.

Fixpoint closed_ok (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tRel _ | tVar _ | tEvar _ _ | tFix _ _ | tCoFix _ _ | tLambda _ _ _ | tLetIn _ _ _ _ | tCase _ _ _ _ => false
      | tApp f args => closed_ok fuel f && forallb (closed_ok fuel) args
      | tConst kn _ => match find_fn kn with Some _ => false | None => negb (Kername.eqb kn kn_mem0) end
      | _ => true
      end
  end.

(* a number written out ([S (S .. O)]) is one constant, however long *)
Fixpoint nat_lit (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tConstruct i 0 _ => Kername.eqb (inductive_mind i) (inductive_mind ind_nat)
      | tApp (tConstruct i 1 _) [n] => Kername.eqb (inductive_mind i) (inductive_mind ind_nat) && nat_lit fuel n
      | _ => false
      end
  end.

Definition fresh (s : st) : positive * st := (s_next s, mkSt (Pos.succ (s_next s)) (s_arrs s)).
(* a memory block is named by a constant of the program; two names are compared as names *)
Definition same_const (a b : term) : bool :=
  match a, b with tConst k1 _, tConst k2 _ => Kername.eqb k1 k2 | _, _ => false end.
Definition add_arr (h n : term) (s : st) : st :=
  if existsb (fun hn => same_const (fst hn) h) (s_arrs s) then s else mkSt (s_next s) ((h, n) :: s_arrs s).

Definition K := term -> st -> tres (term * st).

(* beta-reduce a helper's body against its arguments, as [let]s *)
Fixpoint beta_lets (b : term) (args : list term) : term :=
  match b, args with
  | tLambda na ty body, a :: args => tLetIn na a ty (beta_lets body (map (lift0 1) args))
  | _, [] => b
  | _, _ => mkApps b args
  end.

Fixpoint tr_int (fuel : nat) (Γ : list ent) (t : term) (s : st) (k : K) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tRel n => match nth_error Γ n with
              | Some (EInt a) => k a s
              | _ => TErr "a variable used as a number is not one"
              end
  | tInt _ => k (aint t) s
  | tLetIn na b ty body =>
      tr_int fuel Γ b s (fun a s => tr_int fuel (EInt a :: Γ) body s k)
  | tApp (tConst kn u) args =>
      if Kername.eqb kn kn_ofn then
        match args with [n] => tr_nat fuel Γ n s k | _ => TErr "ofn" end
      else if eq_mp (fst kn) prim_mp then
        match binop_of (snd kn), args with
        | Some o, [a; b] =>
            tr_int fuel Γ a s (fun A s => tr_int fuel Γ b s (fun B s =>
              let '(x, s) := fresh s in
              match k (avar x) s with
              | TOk (e, s) => TOk (tApp q_Eop [qpos x; o; A; B; e], s)
              | TErr m => TErr m
              end))
        | _, _ => TErr ("not a supported operation: " ^ snd kn)
        end
      else if Kername.eqb kn kn_rd then
        match args with
        | [tRel m; n; h; i] =>
            match nth_error Γ m with
            | Some EMem =>
                tr_int fuel Γ i s (fun I s =>
                  let '(x, s) := fresh s in
                  let s := add_arr h n s in
                  match k (avar x) s with
                  | TOk (e, s) => TOk (tApp q_Eload [qpos x; h; I; e], s)
                  | TErr m => TErr m
                  end)
            | _ => TErr "a read of a memory that is not the current one"
            end
        | _ => TErr "a read must name its memory directly"
        end
      else match find_fn kn with
      | Some f =>
          if fi_rmem f then TErr "a function giving back a memory, used as a number"
          else tr_call fuel Γ f args s (fun As s =>
                 let '(x, s) := fresh s in
                 match k (avar x) s with
                 | TOk (e, s) => TOk (tApp q_Ecall [qpos x; qpos (fi_id f); As; e], s)
                 | TErr m => TErr m
                 end)
      | None =>
          match helper_body kn with
          | Some b => tr_int fuel Γ (beta_lets b args) s k
          | None => if closed_ok 1000 t then k (aint t) s else TErr ("not readable: " ^ snd kn)
          end
      end
  | tApp (tRel n) args =>
      match nth_error Γ n with
      | Some ESelf =>
          if fi_rmem self then TErr "a call of itself giving back a memory, used as a number"
          else tr_call fuel Γ self args s (fun As s =>
                 let '(x, s) := fresh s in
                 match k (avar x) s with
                 | TOk (e, s) => TOk (tApp q_Ecall [qpos x; qpos (fi_id self); As; e], s)
                 | TErr m => TErr m
                 end)
      | _ => TErr "a call of a variable"
      end
  | tConst kn _ =>
      match helper_body kn with
      | Some b => tr_int fuel Γ b s k
      | None => if closed_ok 1000 t then k (aint t) s else TErr ("not readable: " ^ snd kn)
      end
  | _ => if closed_ok 1000 t then k (aint t) s else TErr "not a number this translator reads"
  end
  end

(* a counter, as the atom holding [ofn] of it *)
with tr_nat (fuel : nat) (Γ : list ent) (t : term) (s : st) (k : K) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tRel n => match nth_error Γ n with
              | Some (ENat a) => k a s
              | _ => TErr "a variable used as a counter is not one"
              end
  | tApp (tConstruct i 1 _) [n] =>
      if nat_lit 10000000 t then k (aint (tApp q_ofn [t])) s
      else if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then
        tr_nat fuel Γ n s (fun A s =>
          let '(x, s) := fresh s in
          match k (avar x) s with
          | TOk (e, s) => TOk (tApp q_Eop [qpos x; <% Badd %>; A; aint (tInt 1%uint63); e], s)
          | TErr m => TErr m
          end)
      else TErr "a constructor"
  | _ => if closed_ok 1000 t then k (aint (tApp q_ofn [t])) s else TErr "not a counter this translator reads"
  end
  end

(* the arguments of a call: the numbers and counters first; a memory last,
   whose work is done after them *)
with tr_call (fuel : nat) (Γ : list ent) (f : finfo) (args : list term) (s : st)
             (k : term -> st -> tres (term * st)) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  let fix go (ks : list kind) (args : list term) (acc : list term) (s : st) : tres (term * st) :=
    match ks, args with
    | [], [] => k (qlist q_atom (rev acc)) s
    | KNat :: ks, a :: args => tr_nat fuel Γ a s (fun A s => go ks args (A :: acc) s)
    | KInt :: ks, a :: args => tr_int fuel Γ a s (fun A s => go ks args (A :: acc) s)
    | [KMem], [m] => tr_mem fuel Γ m s (fun s => k (qlist q_atom (rev acc)) s)
    | _, _ => TErr "a call with the wrong arguments"
    end in
  go (fi_kinds f) args [] s
  end

(* the work of a memory expression, then [k] *)
with tr_mem (fuel : nat) (Γ : list ent) (t : term) (s : st) (k : st -> tres (term * st)) {struct fuel}
  : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tRel n => match nth_error Γ n with
              | Some EMem => k s
              | _ => TErr "a memory that is not the current one"
              end
  | tConst kn _ => if Kername.eqb kn kn_mem0 then k s else TErr "a memory constant"
  | tApp (tConst kn _) args =>
      if Kername.eqb kn kn_wr then
        match args with
        | [m; n; h; i; v] =>
            tr_int fuel Γ i s (fun I s => tr_int fuel Γ v s (fun V s =>
              tr_mem fuel Γ m s (fun s =>
                let s := add_arr h n s in
                match k s with
                | TOk (e, s) => TOk (tApp q_Estore [h; I; V; e], s)
                | TErr m => TErr m
                end)))
        | _ => TErr "wr"
        end
      else match find_fn kn with
      | Some f =>
          if fi_rmem f then
            tr_call fuel Γ f args s (fun As s =>
              let '(x, s) := fresh s in
              match k s with
              | TOk (e, s) => TOk (tApp q_Ecall [qpos x; qpos (fi_id f); As; e], s)
              | TErr m => TErr m
              end)
          else TErr "a number used as a memory"
      | None => match helper_body kn with
                | Some b => tr_mem fuel Γ (beta_lets b args) s k
                | None => TErr ("not readable: " ^ snd kn)
                end
      end
  | tApp (tRel n) args =>
      match nth_error Γ n with
      | Some ESelf =>
          if fi_rmem self then
            tr_call fuel Γ self args s (fun As s =>
              let '(x, s) := fresh s in
              match k s with
              | TOk (e, s) => TOk (tApp q_Ecall [qpos x; qpos (fi_id self); As; e], s)
              | TErr m => TErr m
              end)
          else TErr "a number used as a memory"
      | _ => TErr "a call of a variable"
      end
  | _ => TErr "not a memory this translator reads"
  end
  end.

Definition is_ind (t : term) (i : inductive) : bool :=
  match t with tInd j _ => Kername.eqb (inductive_mind j) (inductive_mind i) | _ => false end.

(* the body in tail position *)
Fixpoint tr_tail (fuel : nat) (Γ : list ent) (t : term) (s : st) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tCase ci p (tRel n) [b0; b1] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match nth_error Γ n with
        | Some (ENat a) =>
            match tr_tail fuel Γ (bbody b0) s with
            | TOk (e0, s) =>
                let '(x, s) := fresh s in
                match tr_tail fuel (ENat (avar x) :: Γ) (bbody b1) s with
                | TOk (e1, s) =>
                    TOk (tApp q_Eif [<% Ceq %>; a; aint (tInt 0%uint63); e0;
                                     tApp q_Eop [qpos x; <% Bsub %>; a; aint (tInt 1%uint63); e1]], s)
                | TErr m => TErr m
                end
            | TErr m => TErr m
            end
        | _ => TErr "a match on what is not a counter parameter"
        end
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        TErr "an if on a boolean variable"
      else TErr "a match this translator does not read"
  | tCase ci p (tApp (tConst kn _) [a; b]) [bt; bf] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) && eq_mp (fst kn) prim_mp then
        match cmp_of (snd kn) with
        | Some c =>
            tr_int fuel Γ a s (fun A s => tr_int fuel Γ b s (fun B s =>
              match tr_tail fuel Γ (bbody bt) s with
              | TOk (et, s) =>
                  match tr_tail fuel Γ (bbody bf) s with
                  | TOk (ef, s) => TOk (tApp q_Eif [c; A; B; et; ef], s)
                  | TErr m => TErr m
                  end
              | TErr m => TErr m
              end))
        | None => TErr ("a test this translator does not read: " ^ snd kn)
        end
      else TErr "a match this translator does not read"
  | tLetIn na b ty body =>
      if is_ind ty ind_nat then TErr "a let of a counter"
      else if (match ty with tConst kn _ => Kername.eqb kn kn_kmem | _ => false end) then
        (* a new memory: the work is done, the old one is dead *)
        tr_mem fuel Γ b s (fun s =>
          tr_tail fuel (EMem :: map (fun e => match e with EMem => EDead | e => e end) Γ) body s)
      else tr_int fuel Γ b s (fun B s => tr_tail fuel (EInt B :: Γ) body s)
  | tApp (tRel n) args =>
      match nth_error Γ n with
      | Some ESelf => tr_call fuel Γ self args s (fun As s => TOk (tApp q_Eloop [As], s))
      | _ => TErr "a call of a variable"
      end
  | _ =>
      if fi_rmem self then tr_mem fuel Γ t s (fun s => TOk (tApp q_Eret [aint q_zero], s))
      else tr_int fuel Γ t s (fun A s => TOk (tApp q_Eret [A], s))
  end
  end.
End TR.

(* ------------------------------------------------------------------ a function's head *)
Definition kind_of (ty : term) : option kind :=
  match ty with
  | tInd i _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then Some KNat else None
  | tConst kn _ => if Kername.eqb kn kn_int then Some KInt else if Kername.eqb kn kn_kmem then Some KMem else None
  | _ => None
  end.

Fixpoint lams (t : term) : list term * term :=
  match t with tLambda _ ty b => let '(l, r) := lams b in (ty :: l, r) | _ => ([], t) end.

Fixpoint prods_res (t : term) : term := match t with tProd _ _ b => prods_res b | _ => t end.

Definition result_mem (ty : term) : option bool :=
  match kind_of (prods_res ty) with Some KInt => Some false | Some KMem => Some true | _ => None end.

(* the parts of a function: whether it calls itself, its parameter types, its body *)
Definition fparts (b : term) : option (bool * list term * term) :=
  match b with
  | tFix [d] 0 => if Nat.eqb (rarg d) 0 then let '(l, r) := lams (dbody d) in Some (true, l, r) else None
  | tFix _ _ => None
  | _ => let '(l, r) := lams b in Some (false, l, r)
  end.

Fixpoint opt_all {A} (l : list (option A)) : option (list A) :=
  match l with [] => Some [] | Some a :: l => option_map (cons a) (opt_all l) | None :: _ => None end.

(* ------------------------------------------------------------------ the functions of the file *)
Fixpoint consts (fuel : nat) (t : term) (acc : list kername) : list kername :=
  match fuel with
  | O => acc
  | S fuel =>
      match t with
      | tConst kn _ => if existsb (Kername.eqb kn) acc then acc else kn :: acc
      | tApp f args => fold_left (fun acc a => consts fuel a acc) args (consts fuel f acc)
      | tLambda _ ty b | tProd _ ty b => consts fuel b (consts fuel ty acc)
      | tLetIn _ b ty body => consts fuel body (consts fuel ty (consts fuel b acc))
      | tCase _ p c brs => fold_left (fun acc br => consts fuel (bbody br) acc) brs
                              (consts fuel c (consts fuel (preturn p) acc))
      | tFix mfix _ => fold_left (fun acc d => consts fuel (dbody d) (consts fuel (dtype d) acc)) mfix acc
      | _ => acc
      end
  end.

Definition body_of (Σ : global_env) (kn : kername) : option (term * term) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) => option_map (fun b => (cst_type cb, b)) (cst_body cb)
  | _ => None
  end.

(* a constant of the file is a function to translate when it calls itself, or is the root *)
Definition is_fun (Σ : global_env) (mp : modpath) (root kn : kername) : bool :=
  Kername.eqb kn root ||
  (eq_mp (fst kn) mp &&
   match body_of Σ kn with Some (_, tFix _ _) => true | _ => false end).

(* every function reachable from the root, callees first *)
Fixpoint reach (fuel : nat) (Σ : global_env) (mp : modpath) (root : kername) (kn : kername)
               (done : list kername) : list kername :=
  match fuel with
  | O => done
  | S fuel =>
      if existsb (Kername.eqb kn) done then done
      else match body_of Σ kn with
           | Some (_, b) =>
               let cs := rev (consts 10000 b []) in
               let done := fold_left (fun d c =>
                             if Kername.eqb c kn then d
                             else if eq_mp (fst c) mp then reach fuel Σ mp root c d else d) cs done in
               if is_fun Σ mp root kn then List.app done [kn] else done
           | None => done
           end
  end.

Definition mk_info (Σ : global_env) (i : nat) (kn : kername) : option finfo :=
  match body_of Σ kn with
  | Some (ty, b) =>
      match fparts b, result_mem ty with
      | Some (isrec, tys, _), Some rm =>
          option_map (fun ks => mkFI kn (Pos.of_nat (1000 + i)) ks rm isrec) (opt_all (map kind_of tys))
      | _, _ => None
      end
  | None => None
  end.

(* translate one function; its parameters are KQL variables 1 .. n *)
Definition tr_fun (Σ : global_env) (mp : modpath) (fns : list finfo) (f : finfo) (s0 : list (term * term))
  : tres (term * list (term * term)) :=
  match body_of Σ (fi_kn f) with
  | Some (_, b) =>
      match fparts b with
      | Some (_, _, body) =>
          let n := length (fi_kinds f) in
          let pids := map (fun i => Pos.of_nat (S i)) (seq 0 n) in
          let ents := map (fun ik => match fst ik with
                                     | KNat => ENat (avar (snd ik))
                                     | KInt => EInt (avar (snd ik))
                                     | KMem => EMem end) (combine (fi_kinds f) pids) in
          let Γ := List.app (rev ents) (if fi_rec f then [ESelf] else []) in
          let kpids := map snd (filter (fun ik => match fst ik with KMem => false | _ => true end)
                                       (combine (fi_kinds f) pids)) in
          match tr_tail Σ mp fns f 1000 Γ body (mkSt (Pos.of_nat (S n)) s0) with
          | TOk (e, s) => TOk (tApp q_mkfn [qlist q_ident (map qpos kpids); e], s_arrs s)
          | TErr m => TErr (snd (fi_kn f) ^ ": " ^ m)
          end
      | None => TErr (snd (fi_kn f) ^ ": not a function this translator reads")
      end
  | None => TErr "no body"
  end.

(* ------------------------------------------------------------------ the statement of a function *)
(* forall x1 .. xn M, Z.of_nat (sum of counters) < wB -> run P f [args] M RES MEM *)
Definition stmt (prog : term) (f : finfo) (usesmem0 : bool) : term :=
  let ks := fi_kinds f in
  let hasM := existsb (fun k => match k with KMem => true | _ => false end) ks in
  let vks := filter (fun k => match k with KMem => false | _ => true end) ks in
  let n := length vks in
  (* binders: the value parameters, then M (the memory) *)
  let nb := S n in
  let var i d := tRel (d + nb - 1 - i) in           (* parameter i, under d more binders *)
  let mvar d := tRel d in
  let nats := map fst (filter (fun ik => match snd ik with KNat => true | _ => false end)
                               (combine (seq 0 n) vks)) in
  let sum d := match nats with
               | [] => tApp q_Zofnat [<% 0 %>]
               | i :: l => tApp q_Zofnat [fold_left (fun acc j => tApp q_natadd [acc; var j d]) l (var i d)]
               end in
  let arg i k d := match k with KNat => tApp q_ofn [var i d] | _ => var i d end in
  let args d := qlist q_i63 (map (fun ik => arg (fst ik) (snd ik) d) (combine (seq 0 n) vks)) in
  let fapp d := mkApps (tConst (fi_kn f) []) (List.app (map (fun i => var i d) (seq 0 n)) (if hasM then [mvar d] else [])) in
  let mem d := if usesmem0 then tConst kn_mem0 [] else mvar d in
  let body d :=
    if fi_rmem f then tApp q_run [prog; qpos (fi_id f); args d; mem d; q_zero; fapp d]
    else if usesmem0 then
      tApp q_ex [q_kmem; tLambda {| binder_name := nNamed "M'"; binder_relevance := Relevant |} q_kmem
                  (tApp q_run [prog; qpos (fi_id f); args (S d); tConst kn_mem0 []; lift0 1 (fapp d); tRel 0])]
    else tApp q_run [prog; qpos (fi_id f); args d; mvar d; fapp d; mvar d] in
  let core := tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                (tApp q_Zlt [sum 0; q_wB]) (body 1) in
  let withM := tProd {| binder_name := nNamed "M"; binder_relevance := Relevant |} q_kmem core in
  fold_right (fun ik acc =>
                tProd {| binder_name := nNamed ("x" ^ string_of_nat (fst ik)); binder_relevance := Relevant |}
                      (match snd ik with KNat => <% nat %> | _ => q_i63 end) acc)
             withM (combine (seq 0 n) vks).

(* ------------------------------------------------------------------ the whole program *)
Inductive kdef := KDef (id : ident) (ty body : term).
Record tout := mkOut { o_defs : list kdef; o_msg : string }.

Definition kql_gen (p : program) (prog_name : ident) : tout :=
  let '(Σ, t) := p in
  match t with
  | tConst root _ =>
      let mp := fst root in
      let kns := reach 1000 Σ mp root root [] in
      match opt_all (map (fun ik => mk_info Σ (fst ik) (snd ik)) (combine (seq 0 (length kns)) kns)) with
      | Some fns =>
          let fix go (fs : list finfo) (arrs : list (term * term)) (acc : list (finfo * term)) :=
            match fs with
            | [] => TOk (rev acc, arrs)
            | f :: fs => match tr_fun Σ mp fns f arrs with
                         | TOk (e, arrs) => go fs arrs ((f, e) :: acc)
                         | TErr m => TErr m
                         end
            end in
          match go fns [] [] with
          | TOk (tfs, arrs) =>
              let pname := prog_name in
              let pkn : kername := (mp, pname) in
              let fdefs := map (fun fe => KDef (snd (fi_kn (fst fe)) ^ "_kql") q_fn (snd fe)) tfs in
              let pfuns := qlist (tApp q_prod [q_ident; q_fn])
                             (map (fun fe => tApp q_pair [q_ident; q_fn; qpos (fi_id (fst fe));
                                                          tConst (mp, snd (fi_kn (fst fe)) ^ "_kql") []]) tfs) in
              let parrs := qlist (tApp q_prod [q_ident; q_Z])
                             (map (fun hn => tApp q_pair [q_ident; q_Z; fst hn; snd hn]) arrs) in
              let pdef := KDef pname <% prog %> (tApp q_mkprog [pfuns; parrs]) in
              let sdefs := map (fun fe =>
                             let f := fst fe in
                             let usesmem0 := Kername.eqb (fi_kn f) root &&
                                             negb (existsb (fun k => match k with KMem => true | _ => false end) (fi_kinds f)) &&
                                             negb (fi_rmem f) in
                             KDef (snd (fi_kn f) ^ "_stmt") <% Prop %> (stmt (tConst pkn []) f usesmem0)) tfs in
              mkOut (List.app fdefs (pdef :: sdefs))
                    ("KQL: " ^ string_of_nat (length tfs) ^ " functions: " ^
                     String.concat " " (map (fun fe => snd (fi_kn (fst fe))) tfs))
          | TErr m => mkOut [] ("KQL: refused: " ^ m)
          end
      | None => mkOut [] "KQL: refused: a function's parameters or result are not of a kind this translator reads"
      end
  | _ => mkOut [] "KQL: give it the name of a definition"
  end.

Polymorphic Definition unq_def@{x t u | x < t +} (id : ident) (ty body : term) : TemplateMonad@{t u} unit :=
  @tmBind@{t u} Type@{x} unit (@tmUnquoteTyped@{t u} Type@{x} ty) (fun A : Type@{x} =>
  @tmBind@{t u} A unit (@tmUnquoteTyped@{t u} A body) (fun v : A =>
  @tmBind@{t u} A unit (@tmDefinitionRed_@{t u} false id None A v) (fun _ => @tmReturn@{t u} unit tt))).

Fixpoint define_all (l : list kdef) : TemplateMonad unit :=
  match l with
  | [] => tmReturn tt
  | KDef id ty b :: l => unq_def id ty b ;; define_all l
  end.

Definition kql_define (o : tout) : TemplateMonad unit :=
  match o_defs o with
  | [] => tmFail (o_msg o)
  | l => define_all l ;; tmMsg (o_msg o)
  end.

Notation kql_translate x name :=
  (kql_define ltac:(run_template_program (tmQuoteRec x) (fun q => let t := eval vm_compute in (kql_gen q name) in exact t)))
  (only parsing).

(* ------------------------------------------------------------------ the proof of a statement *)
Ltac kql_auto :=
  hnf;
  first [ solve [ kql_prove ]
        | solve [ intros; eexists; kql_prove0 ]
        | solve [ kql_prove0 ] ].
