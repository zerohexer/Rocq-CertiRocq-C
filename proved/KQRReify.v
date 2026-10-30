(** KQRReify.v -- the reifier of the verified compiler by reflection (Rocq-C-solution.md §1.12, §12.V).

    [reify_top] reads the user's function, quoted by MetaRocq, and gives its syntax tree ([KQR.sexp]): the number of its
    numbers, the tree for a counter of 0, the tree for the rest.  It is not trusted and needs no proof: the per-program
    theorem is [KQR.compile_fun_ok] at that tree, and the kernel checks by computation that the tree means the user's
    function -- a wrong tree is refused there. *)

From Stdlib Require Import List Uint63 ZArith.
From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Template Require Import All.
From KQC Require Import KQL KQLAuto KQMSem KQR.
Require KQ.KQRun.
Import MonadNotation ListNotations.

Definition kn_of (t : term) : kername := match t with tConst kn _ => kn | _ => (MPfile [], ""%bs) end.
Definition ind_of (t : term) : inductive :=
  match t with tInd i _ => i | _ => {| inductive_mind := (MPfile [], ""%bs); inductive_ind := 0 |} end.
Definition eq_mp (a b : modpath) : bool := match ModPathComp.compare a b with Eq => true | _ => false end.

Definition prim_mp : modpath := fst (kn_of <% PrimInt63.add %>).
Definition kn_rd := kn_of <% KQ.KQRun.rd %>.
Definition kn_int := kn_of <% PrimInt63.int %>.
Definition kn_mem := kn_of <% KQ.KQRun.mem %>.
Definition ind_nat := ind_of <% nat %>.
Definition ind_bool := ind_of <% bool %>.

Definition binop_v (s : ident) : option binop :=
  if s == "add" then Some Badd else if s == "sub" then Some Bsub else if s == "mul" then Some Bmul
  else if s == "land" then Some Bland else if s == "lor" then Some Blor else if s == "lxor" then Some Blxor
  else if s == "lsl" then Some Blsl else if s == "lsr" then Some Blsr else if s == "asr" then Some Basr
  else if s == "div" then Some Bdiv else if s == "mod" then Some Bmod else if s == "divs" then Some Bdivs
  else if s == "mods" then Some Bmods else None.

Definition cmp_v (s : ident) : option cmpop :=
  if s == "eqb" then Some Ceq else if s == "ltb" then Some Clt else if s == "leb" then Some Cle
  else if s == "ltsb" then Some Cslt else if s == "lesb" then Some Csle else None.

(** what a variable of the text stands for *)
Inductive cent := CNum | CMem | CCnt | CPred | CSelf.

(** the syntax index of the number at place [i] of the context: the numbers nearer than it *)
Fixpoint num_index (ctx : list cent) (i : nat) : option nat :=
  match ctx, i with
  | CNum :: _, O => Some O
  | _ :: _, O => None
  | c :: r, S i => option_map (fun j => match c with CNum => S j | _ => j end) (num_index r i)
  | [], _ => None
  end.

Definition is_mem (ctx : list cent) (i : nat) : bool := match nth_error ctx i with Some CMem => true | _ => false end.

Fixpoint to_sexps (l : list sexp) : sexps := match l with [] => SNil | e :: l => SCons e (to_sexps l) end.

Fixpoint opt_all {A} (l : list (option A)) : option (list A) :=
  match l with [] => Some [] | Some a :: l => option_map (cons a) (opt_all l) | None :: _ => None end.

Fixpoint reify (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sexp :=
  match fuel with
  | O => None
  | S fuel =>
  match t with
  | tRel i => option_map SVar (num_index ctx i)
  | tInt n => Some (SInt n)
  | tApp (tConst kn _) args =>
      if eq_mp (fst kn) prim_mp then
        match binop_v (snd kn), args with
        | Some o, [a; b] =>
            match reify fuel ctx a, reify fuel ctx b with Some x, Some y => Some (SOp o x y) | _, _ => None end
        | _, _ => None
        end
      else if Kername.eqb kn kn_rd then
        match args with
        | [h; i; tRel m] =>
            if is_mem ctx m then
              match reify fuel ctx h, reify fuel ctx i with Some x, Some y => Some (SRd x y) | _, _ => None end
            else None
        | _ => None
        end
      else None
  | tApp (tRel fi) (tRel mi :: rest) =>
      match nth_error ctx fi, nth_error ctx mi, rev rest with
      | Some CSelf, Some CPred, tRel si :: rargs =>
          if is_mem ctx si then option_map (fun l => SRec (to_sexps l)) (opt_all (map (reify fuel ctx) (rev rargs)))
          else None
      | _, _, _ => None
      end
  | tCase ci _ c [b0; b1] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        match c with
        | tApp (tConst kn _) [a; b] =>
            match (if eq_mp (fst kn) prim_mp then cmp_v (snd kn) else None) with
            | Some cmp =>
                match reify fuel ctx a, reify fuel ctx b, reify fuel ctx (bbody b0), reify fuel ctx (bbody b1) with
                | Some x, Some y, Some t1, Some t2 => Some (SIf cmp x y t1 t2)
                | _, _, _, _ => None
                end
            | None => None
            end
        | _ => None
        end
      else None
  | tLetIn _ b (tConst kty _) body =>
      if Kername.eqb kty kn_int then
        match reify fuel ctx b, reify fuel (CNum :: ctx) body with Some x, Some y => Some (SLet x y) | _, _ => None end
      else None
  | _ => None
  end
  end.

Fixpoint lams (t : term) : list term * term :=
  match t with tLambda _ ty b => let '(l, r) := lams b in (ty :: l, r) | _ => ([], t) end.

Definition is_ty (kn : kername) (t : term) : bool := match t with tConst k _ => Kername.eqb k kn | _ => false end.

(** the user's function: [Fixpoint f (n : nat) (x1 .. xk : int) (s : mem) : int := match n with O => e0 | S m => e1 end] *)
Definition reify_top (p : program) : option (sig * fbody) :=
  match p with
  | (Σ, tConst kn _) =>
      match lookup_env Σ kn with
      | Some (ConstantDecl cb) =>
          match cst_body cb with
          | Some (tFix [d] 0) =>
              if Nat.eqb (rarg d) 0 then
                match lams (dbody d) with
                | (tInd icnt _ :: tys, tCase ci _ (tRel cnt) [b0; b1]) =>
                    let k := Nat.pred (length tys) in
                    if Kername.eqb (inductive_mind icnt) (inductive_mind ind_nat)
                       && Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat)
                       && Nat.eqb cnt (S k)
                       && forallb (is_ty kn_int) (firstn k tys) && is_ty kn_mem (last tys (tVar ""%bs))
                    then
                      let ctx := CMem :: repeat CNum k ++ [CCnt; CSelf] in
                      match reify 100000 ctx (bbody b0), reify 100000 (CPred :: ctx) (bbody b1) with
                      | Some e0, Some e1 => Some (mksig true k true, FRec e0 e1)
                      | _, _ => None
                      end
                    else None
                | _ => None
                end
              else None
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

(* ================================================================ end to end, from the user's text *)

Definition sum_src := ltac:(run_template_program (tmQuoteRec sum)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).

(* the reified tree is the one written by hand in KQR.v *)
Check (eq_refl : sum_src = (sum_g, sum_b)).

(* the per-program theorem: [compile_f_ok] at the reified tree; the kernel checks that the tree means [sum] *)
Definition sum_Pr := mkprog [(gid1 0, compile_f gid1 0 (fst sum_src) (snd sum_src))] [].
Time Lemma sum_ok_r : callee_ok sum_Pr (gid1 0) (fst sum_src) sum.
Proof. Time exact (compile_f_ok sum_Pr [] gid1 0 (fst sum_src) (snd sum_src) eq_refl eq_refl (no_callees sum_Pr gid1)). Time Qed.

Definition long_src := ltac:(run_template_program (tmQuoteRec long)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : long_src = (long_g, long_b)).
Definition long_Pr := mkprog [(gid1 0, compile_f gid1 0 (fst long_src) (snd long_src))] [].
Time Lemma long_ok_r : callee_ok long_Pr (gid1 0) (fst long_src) long.
Proof. Time exact (compile_f_ok long_Pr [] gid1 0 (fst long_src) (snd long_src) eq_refl eq_refl (no_callees long_Pr gid1)). Time Qed.

Print Assumptions long_ok_r.
