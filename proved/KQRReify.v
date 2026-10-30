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

Definition is_ent (e : cent) (ctx : list cent) (i : nat) : bool :=
  match nth_error ctx i, e with
  | Some CMem, CMem | Some CCnt, CCnt | Some CPred, CPred | Some CSelf, CSelf => true
  | _, _ => false
  end.

Fixpoint to_sexps (l : list sexp) : sexps := match l with [] => SNil | e :: l => SCons e (to_sexps l) end.

Fixpoint opt_all {A} (l : list (option A)) : option (list A) :=
  match l with [] => Some [] | Some a :: l => option_map (cons a) (opt_all l) | None :: _ => None end.

Fixpoint find_callee (kn : kername) (cs : list (kername * sig)) (i : nat) : option (nat * sig) :=
  match cs with [] => None | (k, g) :: r => if Kername.eqb k kn then Some (i, g) else find_callee kn r (S i) end.

(** the counter given to a callee, read off the argument *)
Definition read_cnt (ctx : list cent) (scg : bool) (args : list term) : option (ncnt * list term) :=
  if scg then
    match args with
    | tRel i :: rest => if is_ent CCnt ctx i then Some (NCnt, rest) else if is_ent CPred ctx i then Some (NPred, rest) else None
    | _ => None
    end
  else Some (NNone, args).

(** the numbers of a call, and the memory last when the callee takes one *)
Definition read_mem (ctx : list cent) (smg : bool) (args : list term) : option (list term) :=
  if smg then match rev args with tRel i :: rnums => if is_ent CMem ctx i then Some (rev rnums) else None | _ => None end
  else Some args.

Section R.
Variable callees : list (kername * sig).   (* the program's functions read so far, callees first *)
Variable fm : bool.                        (* the function being read takes a memory *)

Fixpoint reify (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sexp :=
  match fuel with
  | O => None
  | S fuel =>
  let reify_args (l : list term) : option sexps := option_map to_sexps (opt_all (map (reify fuel ctx) l)) in
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
            if is_ent CMem ctx m then
              match reify fuel ctx h, reify fuel ctx i with Some x, Some y => Some (SRd x y) | _, _ => None end
            else None
        | _ => None
        end
      else
        match find_callee kn callees 0 with
        | Some (f, gs) =>
            match read_cnt ctx (sc gs) args with
            | Some (c, rest) =>
                match read_mem ctx (sm gs) rest with
                | Some nums => option_map (SCall f c) (reify_args nums)
                | None => None
                end
            | None => None
            end
        | None => None
        end
  | tApp (tRel fi) (tRel mi :: rest) =>
      if is_ent CSelf ctx fi && is_ent CPred ctx mi then
        match read_mem ctx fm rest with
        | Some nums => option_map SRec (reify_args nums)
        | None => None
        end
      else None
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
End R.

Fixpoint lams (t : term) : list term * term :=
  match t with tLambda _ ty b => let '(l, r) := lams b in (ty :: l, r) | _ => ([], t) end.

Definition is_ty (kn : kername) (t : term) : bool := match t with tConst k _ => Kername.eqb k kn | _ => false end.
Definition is_nat (t : term) : bool := match t with tInd i _ => Kername.eqb (inductive_mind i) (inductive_mind ind_nat) | _ => false end.

(** a signature off the parameter types: a counter first or not, numbers, a memory last or not *)
Definition read_sig (tys : list term) : option sig :=
  let c := match tys with t :: _ => is_nat t | [] => false end in
  let rest := if c then tl tys else tys in
  let m := match rev rest with t :: _ => is_ty kn_mem t | [] => false end in
  let nums := if m then removelast rest else rest in
  if forallb (is_ty kn_int) nums then Some (mksig c (length nums) m) else None.

Definition fun_ctx (gs : sig) : list cent := (if sm gs then [CMem] else []) ++ repeat CNum (sk gs) ++ (if sc gs then [CCnt] else []).

(** one function of the program, given the ones before it *)
Definition reify_fun (Σ : global_env) (callees : list (kername * sig)) (kn : kername) : option (sig * fbody) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some (tFix [d] 0) =>
          if Nat.eqb (rarg d) 0 then
            let '(tys, body) := lams (dbody d) in
            match read_sig tys, body with
            | Some gs, tCase ci _ (tRel cnt) [b0; b1] =>
                if sc gs && Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat)
                   && Nat.eqb cnt (sk gs + (if sm gs then 1 else 0)) then
                  let ctx := fun_ctx gs ++ [CSelf] in
                  match reify callees (sm gs) 100000 ctx (bbody b0), reify callees (sm gs) 100000 (CPred :: ctx) (bbody b1) with
                  | Some e0, Some e1 => Some (gs, FRec e0 e1)
                  | _, _ => None
                  end
                else None
            | _, _ => None
            end
          else None
      | Some b =>
          let '(tys, body) := lams b in
          match read_sig tys with
          | Some gs => option_map (fun e => (gs, FPlain e)) (reify callees (sm gs) 100000 (fun_ctx gs) body)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(** the constants a term names *)
Fixpoint consts (fuel : nat) (t : term) (acc : list kername) : list kername :=
  match fuel with
  | O => acc
  | S fuel =>
      match t with
      | tConst kn _ => kn :: acc
      | tApp f args => fold_left (fun a x => consts fuel x a) args (consts fuel f acc)
      | tLambda _ ty b | tProd _ ty b => consts fuel b (consts fuel ty acc)
      | tLetIn _ b ty body => consts fuel body (consts fuel ty (consts fuel b acc))
      | tCase _ p c brs => fold_left (fun a br => consts fuel (bbody br) a) brs (consts fuel c acc)
      | tFix mfix _ => fold_left (fun a d => consts fuel (dbody d) a) mfix acc
      | _ => acc
      end
  end.

Definition body_of (Σ : global_env) (kn : kername) : option term :=
  match lookup_env Σ kn with Some (ConstantDecl cb) => cst_body cb | _ => None end.

(** the program's functions reachable from the root, callees first: the constants of the root's own file that have a body *)
Fixpoint reach (fuel : nat) (Σ : global_env) (mp : modpath) (kn : kername) (done : list kername) : list kername :=
  match fuel with
  | O => done
  | S fuel =>
      if existsb (Kername.eqb kn) done then done
      else match body_of Σ kn with
           | Some b =>
               let cs := filter (fun k => eq_mp (fst k) mp && negb (Kername.eqb k kn)) (consts 10000 b []) in
               let done' := fold_left (fun d k => reach fuel Σ mp k d) (rev cs) done in
               List.app done' [kn]
           | None => done
           end
  end.

(** the whole program: its functions callees first, each with its signature and body *)
Definition reify_prog (p : program) : option (list (kername * sig * fbody)) :=
  match p with
  | (Σ, tConst root _) =>
      let kns := reach 1000 Σ (fst root) root [] in
      fold_left (fun acc kn =>
                   match acc with
                   | Some l => match reify_fun Σ (map (fun x => (fst (fst x), snd (fst x))) l) kn with
                               | Some (gs, b) => Some (List.app l [(kn, gs, b)])
                               | None => None
                               end
                   | None => None
                   end) kns (Some [])
  | _ => None
  end.

(** compatibility: one recursive function *)
Definition reify_top (p : program) : option (sig * fbody) :=
  match reify_prog p with Some [(_, gs, b)] => Some (gs, b) | _ => None end.

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

(* a program: [loop] and the helper it calls, found and ordered callees first by [reach] *)
Definition hl_src := ltac:(run_template_program (tmQuoteRec loop)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) hl_src = [(h_g, h_b); (loop_g, loop_b)]).

(* the KQL program made from the reified functions, in order: function i is [gid1 i] *)
Fixpoint funs_of (i : nat) (l : list (kername * sig * fbody)) : list (positive * fn) :=
  match l with [] => [] | (_, gs, b) :: r => (gid1 i, compile_f gid1 i gs b) :: funs_of (S i) r end.
Definition sig_at (l : list (kername * sig * fbody)) (i : nat) : sig :=
  match nth_error l i with Some (_, gs, _) => gs | None => mksig false 0 false end.
Definition body_at (l : list (kername * sig * fbody)) (i : nat) : fbody :=
  match nth_error l i with Some (_, _, b) => b | None => FPlain (SInt 0%uint63) end.
Definition hl_Pr := mkprog (funs_of 0 hl_src) [].

(* each function's theorem, the callees' theorems before it: nothing searched, each a computation by the kernel *)
Time Lemma h_ok_r : callee_ok hl_Pr (gid1 0) (sig_at hl_src 0) h.
Proof. Time exact (compile_f_ok hl_Pr [] gid1 0 (sig_at hl_src 0) (body_at hl_src 0) eq_refl eq_refl (no_callees hl_Pr gid1)). Time Qed.
Time Lemma loop_ok_r : callee_ok hl_Pr (gid1 1) (sig_at hl_src 1) loop.
Proof.
  refine (compile_f_ok hl_Pr [existT ftype (sig_at hl_src 0) h] gid1 1 (sig_at hl_src 1) (body_at hl_src 1) eq_refl eq_refl _).
  intros [|[|f]]; simpl; [exact h_ok_r | exact Logic.I | exact Logic.I].
Time Qed.
Print Assumptions loop_ok_r.

Print Assumptions long_ok_r.
