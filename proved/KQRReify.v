(** KQRReify.v -- the reifier of the verified compiler by reflection (Rocq-C-solution.md §1.12, §12.V).

    [reify_prog] reads the user's program, quoted by MetaRocq: the functions reachable from the root, callees first, each
    with its signature (off its type) and its body as a syntax tree ([KQR.sexp] for a number, [KQR.smem] for a memory).
    It is not trusted and needs no proof: the per-program theorem is [KQR.compile_f_ok] at that tree, and the kernel checks
    by computation that the tree means the user's function -- a wrong tree is refused there.  A memory that is no longer
    the newest (a [let s2 := .. in ..] made a newer one) is dead: naming it is refused here, with its reason.  A counter
    is read as a counter expression: a counter variable (a [nat] parameter, or the predecessor a match on a counter binds),
    [O], [S c], [kq_nat e].  A function is kept only when it is well formed ([KQR.wf_f]), so a program read is a program
    [compile] takes. *)

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
Definition kn_upd := kn_of <% KQ.KQRun.upd %>.
Definition kn_int := kn_of <% PrimInt63.int %>.
Definition kn_mem := kn_of <% KQ.KQRun.mem %>.
Definition kn_kq_nat := kn_of <% KQ.KQRun.kq_nat %>.
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

(** what a variable of the text stands for: a number, the newest memory, an older memory (dead: naming it would use two
    versions of the memory), a counter (a [nat] parameter, or the predecessor a match on a counter inside the body binds),
    the predecessor of the first counter that the match a recursive function starts with binds (a counter too, and the one
    its recursive call is given first), the function itself *)
Inductive cent := CNum | CMem | CDead | CCnt | CPred | CSelf.

(** a newer memory is bound: every memory before it is dead *)
Definition kill_mem (ctx : list cent) : list cent := map (fun c => match c with CMem => CDead | c => c end) ctx.

(** the syntax index of the number at place [i] of the context: the numbers nearer than it *)
Fixpoint num_index (ctx : list cent) (i : nat) : option nat :=
  match ctx, i with
  | CNum :: _, O => Some O
  | _ :: _, O => None
  | c :: r, S i => option_map (fun j => match c with CNum => S j | _ => j end) (num_index r i)
  | [], _ => None
  end.

Definition is_cnt (c : cent) : bool := match c with CCnt | CPred => true | _ => false end.

(** the syntax index of the counter at place [i] of the context: the counters nearer than it *)
Fixpoint cnt_index (ctx : list cent) (i : nat) : option nat :=
  match ctx, i with
  | c :: _, O => if is_cnt c then Some O else None
  | c :: r, S i => option_map (fun j => if is_cnt c then S j else j) (cnt_index r i)
  | [], _ => None
  end.

Definition is_ent (e : cent) (ctx : list cent) (i : nat) : bool :=
  match nth_error ctx i, e with
  | Some CMem, CMem | Some CCnt, CCnt | Some CPred, CPred | Some CSelf, CSelf => true
  | _, _ => false
  end.

Fixpoint to_sexps (l : list sexp) : sexps := match l with [] => SNil | e :: l => SCons e (to_sexps l) end.
Fixpoint to_scnts (l : list scnt) : scnts := match l with [] => CNil | c :: l => CCons c (to_scnts l) end.

Fixpoint opt_all {A} (l : list (option A)) : option (list A) :=
  match l with [] => Some [] | Some a :: l => option_map (cons a) (opt_all l) | None :: _ => None end.

Fixpoint find_callee (kn : kername) (cs : list (kername * sig)) (i : nat) : option (nat * sig) :=
  match cs with [] => None | (k, g) :: r => if Kername.eqb k kn then Some (i, g) else find_callee kn r (S i) end.

(** the numbers of a call, and the memory last when the callee takes one *)
Definition read_mem (ctx : list cent) (smg : bool) (args : list term) : option (list term) :=
  if smg then match rev args with tRel i :: rnums => if is_ent CMem ctx i then Some (rev rnums) else None | _ => None end
  else Some args.

Section R.
Variable callees : list (kername * sig).   (* the program's functions read so far, callees first *)
Variable fm : bool.                        (* the function being read takes a memory *)
Variable fnx : nat.                        (* its counters after the first: the recursive call is given these after the
                                              predecessor *)

(** a number; and a counter: a counter variable, [O], [S c], [kq_nat e] *)
Fixpoint reify (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sexp :=
  match fuel with
  | O => None
  | S fuel =>
  let reify_args (l : list term) : option sexps := option_map to_sexps (opt_all (map (reify fuel ctx) l)) in
  let reify_cs (l : list term) : option scnts := option_map to_scnts (opt_all (map (reify_c fuel ctx) l)) in
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
            if sr gs || negb (Nat.leb (sn gs) (length args)) then None else
            match reify_cs (firstn (sn gs) args), read_mem ctx (sm gs) (skipn (sn gs) args) with
            | Some cs, Some nums => option_map (SCall f cs) (reify_args nums)
            | _, _ => None
            end
        | None => None
        end
  | tApp (tRel fi) (tRel mi :: rest) =>
      if is_ent CSelf ctx fi && is_ent CPred ctx mi && Nat.leb fnx (length rest) then
        match reify_cs (firstn fnx rest), read_mem ctx fm (skipn fnx rest) with
        | Some cs, Some nums => option_map (SRec cs) (reify_args nums)
        | _, _ => None
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
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel i =>
            match cnt_index ctx i, reify fuel ctx (bbody b0), reify fuel (CCnt :: ctx) (bbody b1) with
            | Some x, Some e0, Some e1 => Some (SMatch x e0 e1)
            | _, _, _ => None
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
  end
with reify_c (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option scnt :=
  match fuel with
  | O => None
  | S fuel =>
  match t with
  | tRel i => option_map CVar (cnt_index ctx i)
  | tConstruct i 0 _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then Some CO else None
  | tApp (tConstruct i 1 _) [c] =>
      if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then option_map CS (reify_c fuel ctx c) else None
  | tApp (tConst kn _) [e] => if Kername.eqb kn kn_kq_nat then option_map CNat (reify fuel ctx e) else None
  | _ => None
  end
  end.

(** a memory: the newest one, a write, lets, a test, a match on a counter, the recursive call or a call giving back a
    memory, on the memory written as its last argument *)
Fixpoint reify_m (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option smem :=
  match fuel with
  | O => None
  | S fuel =>
  let reify_args (l : list term) : option sexps := option_map to_sexps (opt_all (map (reify fuel ctx) l)) in
  let reify_cs (l : list term) : option scnts := option_map to_scnts (opt_all (map (reify_c fuel ctx) l)) in
  match t with
  | tRel i => if is_ent CMem ctx i then Some MCur else None
  | tApp (tConst kn _) args =>
      if Kername.eqb kn kn_upd then
        match args with
        | [h; i; v; m] =>
            match reify fuel ctx h, reify fuel ctx i, reify fuel ctx v, reify_m fuel ctx m with
            | Some a, Some b, Some c, Some d => Some (MUpd a b c d)
            | _, _, _, _ => None
            end
        | _ => None
        end
      else
        match find_callee kn callees 0 with
        | Some (f, gs) =>
            if sr gs && sm gs && Nat.leb (sn gs) (length args) then
              match rev (skipn (sn gs) args) with
              | m :: rnums =>
                  match reify_cs (firstn (sn gs) args), reify_args (rev rnums), reify_m fuel ctx m with
                  | Some cs, Some As, Some d => Some (MCall f cs As d)
                  | _, _, _ => None
                  end
              | [] => None
              end
            else None
        | None => None
        end
  | tApp (tRel fi) (tRel mi :: rest) =>
      if is_ent CSelf ctx fi && is_ent CPred ctx mi && Nat.leb fnx (length rest) then
        match rev (skipn fnx rest) with
        | m :: rnums =>
            match reify_cs (firstn fnx rest), reify_args (rev rnums), reify_m fuel ctx m with
            | Some cs, Some As, Some d => Some (MRec cs As d)
            | _, _, _ => None
            end
        | [] => None
        end
      else None
  | tCase ci _ c [b0; b1] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        match c with
        | tApp (tConst kn _) [a; b] =>
            match (if eq_mp (fst kn) prim_mp then cmp_v (snd kn) else None) with
            | Some cmp =>
                match reify fuel ctx a, reify fuel ctx b, reify_m fuel ctx (bbody b0), reify_m fuel ctx (bbody b1) with
                | Some x, Some y, Some m1, Some m2 => Some (MIf cmp x y m1 m2)
                | _, _, _, _ => None
                end
            | None => None
            end
        | _ => None
        end
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel i =>
            match cnt_index ctx i, reify_m fuel ctx (bbody b0), reify_m fuel (CCnt :: ctx) (bbody b1) with
            | Some x, Some m0, Some m1 => Some (MMatch x m0 m1)
            | _, _, _ => None
            end
        | _ => None
        end
      else None
  | tLetIn _ b (tConst kty _) body =>
      if Kername.eqb kty kn_int then
        match reify fuel ctx b, reify_m fuel (CNum :: ctx) body with Some x, Some y => Some (MLet x y) | _, _ => None end
      else if Kername.eqb kty kn_mem then
        match reify_m fuel ctx b, reify_m fuel (CMem :: kill_mem ctx) body with Some x, Some y => Some (MLetM x y) | _, _ => None end
      else None
  | _ => None
  end
  end.
End R.

Fixpoint lams (t : term) : list term * term :=
  match t with tLambda _ ty b => let '(l, r) := lams b in (ty :: l, r) | _ => ([], t) end.

Definition is_ty (kn : kername) (t : term) : bool := match t with tConst k _ => Kername.eqb k kn | _ => false end.
Definition is_nat (t : term) : bool := match t with tInd i _ => Kername.eqb (inductive_mind i) (inductive_mind ind_nat) | _ => false end.

(** the result type of a function type *)
Fixpoint ret_ty (t : term) : term := match t with tProd _ _ b => ret_ty b | _ => t end.

(** the counters a parameter list starts with, and the parameters after them *)
Fixpoint lead_nats (tys : list term) : nat * list term :=
  match tys with
  | t :: r => if is_nat t then let '(n, l) := lead_nats r in (S n, l) else (O, tys)
  | [] => (O, [])
  end.

(** a signature off the parameter types and the result type: counters first, numbers, a memory last or not, a memory or a
    number as the result *)
Definition read_sig (tys : list term) (ret : term) : option sig :=
  let '(c, rest) := lead_nats tys in
  let m := match rev rest with t :: _ => is_ty kn_mem t | [] => false end in
  let nums := if m then removelast rest else rest in
  let r := is_ty kn_mem ret in
  if forallb (is_ty kn_int) nums && (r || is_ty kn_int ret) then Some (mksig c (length nums) m r) else None.

Definition fun_ctx (gs : sig) : list cent := (if sm gs then [CMem] else []) ++ repeat CNum (sk gs) ++ repeat CCnt (sn gs).

(** one function of the program, given the ones before it, as its text reads: a recursive function starts with a match
    on its first counter *)
Definition read_fun (Σ : global_env) (callees : list (kername * sig)) (kn : kername) : option (sig * fbody) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some (tFix [d] 0) =>
          if Nat.eqb (rarg d) 0 then
            let '(tys, body) := lams (dbody d) in
            match read_sig tys (ret_ty (dtype d)), body with
            | Some gs, tCase ci _ (tRel cnt) [b0; b1] =>
                let nx := Nat.pred (sn gs) in
                if negb (Nat.eqb (sn gs) 0) && Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat)
                   && Nat.eqb cnt ((if sm gs then 1 else 0) + sk gs + nx) then
                  let ctx := fun_ctx gs ++ [CSelf] in
                  if sr gs then
                    match reify_m callees (sm gs) nx 100000 ctx (bbody b0), reify_m callees (sm gs) nx 100000 (CPred :: ctx) (bbody b1) with
                    | Some m0, Some m1 => Some (gs, FRecM m0 m1)
                    | _, _ => None
                    end
                  else
                    match reify callees (sm gs) nx 100000 ctx (bbody b0), reify callees (sm gs) nx 100000 (CPred :: ctx) (bbody b1) with
                    | Some e0, Some e1 => Some (gs, FRec e0 e1)
                    | _, _ => None
                    end
                else None
            | _, _ => None
            end
          else None
      | Some b =>
          let '(tys, body) := lams b in
          match read_sig tys (ret_ty (cst_type cb)) with
          | Some gs =>
              let nx := Nat.pred (sn gs) in
              if sr gs then option_map (fun m => (gs, FPlainM m)) (reify_m callees (sm gs) nx 100000 (fun_ctx gs) body)
              else option_map (fun e => (gs, FPlain e)) (reify callees (sm gs) nx 100000 (fun_ctx gs) body)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(** ... kept when it is well formed, the condition of [compile_f_ok]: a program read is a program compiled *)
Definition reify_fun (Σ : global_env) (callees : list (kername * sig)) (kn : kername) : option (sig * fbody) :=
  match read_fun Σ callees kn with
  | Some (gs, b) => if wf_f (map snd callees) gs b then Some (gs, b) else None
  | None => None
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

(* ---------------------------------------------------------------- why a program is not read *)

Definition add_s (x : string) (l : list string) : list string := if existsb (fun y => y == x) l then l else l ++ [x].

(** the constants the syntax reads: the integer operations and comparisons, [rd], [upd], the program's functions *)
Definition known_const (fns : list kername) (kn : kername) : bool :=
  (eq_mp (fst kn) prim_mp && (match binop_v (snd kn), cmp_v (snd kn) with None, None => false | _, _ => true end))
  || Kername.eqb kn kn_rd || Kername.eqb kn kn_upd || Kername.eqb kn kn_kq_nat || existsb (Kername.eqb kn) fns
  || Kername.eqb kn kn_int || Kername.eqb kn kn_mem.     (* as type arguments *)

Definition head_name (t : term) : string :=
  match t with
  | tConst kn _ => snd kn
  | tInd i _ => snd (inductive_mind i)
  | tApp (tConst kn _) _ => snd kn
  | tApp (tInd i _) _ => snd (inductive_mind i)
  | tProd _ _ _ => "a function"
  | _ => "a type"
  end.

(** what in a function's body lies outside the syntax: its constants, constructors, matches, projections, local
    fixpoints and lets of other types (the types of binders are not looked at) *)
Fixpoint blockers (fuel : nat) (fns : list kername) (t : term) (acc : list string) : list string :=
  match fuel with
  | O => acc
  | S fuel =>
      match t with
      | tConst kn _ => if known_const fns kn then acc else add_s (snd kn) acc
      | tApp f args => fold_left (fun a x => blockers fuel fns x a) args (blockers fuel fns f acc)
      | tLambda _ _ b => blockers fuel fns b acc
      | tLetIn _ b ty body =>
          let acc := if is_ty kn_int ty || is_ty kn_mem ty then acc else add_s ("a let of " ^ head_name ty) acc in
          blockers fuel fns body (blockers fuel fns b acc)
      | tCase ci _ c brs =>
          let i := ci_ind ci in
          let acc := if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) || Kername.eqb (inductive_mind i) (inductive_mind ind_bool)
                     then acc else add_s ("a match on " ^ snd (inductive_mind i)) acc in
          fold_left (fun a br => blockers fuel fns (bbody br) a) brs (blockers fuel fns c acc)
      | tProj _ c => blockers fuel fns c (add_s "a projection" acc)
      | tConstruct i _ _ =>      (* O and S are counters *)
          if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then acc else add_s ("a constructor of " ^ snd (inductive_mind i)) acc
      | tFix _ _ => add_s "a local fix" acc
      | _ => acc
      end
  end.

(** a read of a memory made in place: [rd h i (f .. s)], the memory a call gives back *)
Definition rd_in_place (f : term) (args : list term) : bool :=
  match f, args with
  | tConst kn _, [_; _; m] => Kername.eqb kn kn_rd && match m with tRel _ => false | _ => true end
  | _, _ => false
  end.

(** known constructs where the syntax does not read them yet.  [writes]: a write, a memory let, a read of a memory made in
    place *)
Fixpoint writes (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tConst kn _ => Kername.eqb kn kn_upd
      | tApp f args => rd_in_place f args || writes fuel f || existsb (writes fuel) args
      | tLambda _ _ b => writes fuel b
      | tLetIn _ b ty body => is_ty kn_mem ty || writes fuel b || writes fuel body
      | tCase _ _ c brs => writes fuel c || existsb (fun br => writes fuel (bbody br)) brs
      | _ => false
      end
  end.

(** a match on a counter that is not a variable (a counter worked out first, [match f x with ..]) *)
Fixpoint nat_match_value (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tApp f args => nat_match_value fuel f || existsb (nat_match_value fuel) args
      | tLambda _ _ b => nat_match_value fuel b
      | tLetIn _ b _ body => nat_match_value fuel b || nat_match_value fuel body
      | tCase ci _ c brs =>
          (Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) && match c with tRel _ => false | _ => true end)
          || nat_match_value fuel c || existsb (fun br => nat_match_value fuel (bbody br)) brs
      | _ => false
      end
  end.

Fixpoint bool_test (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tApp f args => bool_test fuel f || existsb (bool_test fuel) args
      | tLambda _ _ b => bool_test fuel b
      | tLetIn _ b _ body => bool_test fuel b || bool_test fuel body
      | tCase ci _ c brs =>
          (Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool)
           && match c with tApp (tConst kn _) [_; _] => negb (eq_mp (fst kn) prim_mp && match cmp_v (snd kn) with Some _ => true | None => false end) | _ => true end)
          || bool_test fuel c || existsb (fun br => bool_test fuel (bbody br)) brs
      | _ => false
      end
  end.

(** a function's reasons: its signature, its recursion, its constructs, their places *)
Definition why_fun (Σ : global_env) (fns bad : list kername) (callees : list (kername * sig)) (kn : kername) : list string :=
  if match read_fun Σ callees kn with Some _ => true | None => false end then
    ["read, but not well formed: a recursive call given a counter grown by S (it would have no bound), a call given fewer"
     ^ " arguments than its function takes, or a counter more than 2^20 successors deep"]
  else
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some b =>
          let '(rec, body, ty) :=
            match b with
            | tFix [d] _ => (if Nat.eqb (rarg d) 0 then "" else "recursion not on the first parameter", dbody d, dtype d)
            | tFix _ _ => ("mutual recursion", b, cst_type cb)
            | _ => (""%bs, b, cst_type cb)
            end in
          let '(tys, inner) := lams body in
          let odd := fold_left (fun a t => if is_ty kn_int t || is_ty kn_mem t || is_nat t then a else add_s (head_name t) a)
                               (tys ++ [ret_ty ty]) [] in
          let sigr := match read_sig tys (ret_ty ty), odd with
                      | Some _, _ => []
                      | None, [] => ["parameters in an order not read (a counter after a number, or the memory not last)"]
                      | None, x :: r => ["a parameter or result of type " ^ fold_left (fun a y => a ^ ", " ^ y) r x]
                      end in
          let r0 := if rec == "" then sigr else rec :: sigr in
          let r1 := blockers 100000 fns inner r0 in
          let numfn := negb (is_ty kn_mem (ret_ty ty)) in
          let r2 := if numfn && writes 100000 inner then add_s "a number function that writes the memory" r1 else r1 in
          let r3 := if nat_match_value 100000 inner then add_s "a match on a counter that is not a variable" r2 else r2 in
          let r4 := if bool_test 100000 inner then add_s "a test that is a boolean value" r3 else r3 in
          let r4 := fold_left (fun a k => if existsb (Kername.eqb k) bad then add_s ("calls " ^ snd k ^ ", not read") a else a)
                              (consts 10000 inner []) r4 in
          match r4 with [] => ["a construct in a place not read (not classified)"] | _ => r4 end
      | None => ["no body"]
      end
  | _ => ["not a constant"]
  end.

(** for each function of the program not read (in [reach]'s order), its reasons *)
Definition reify_why (p : program) : list (string * list string) :=
  match p with
  | (Σ, tConst root _) =>
      let kns := reach 1000 Σ (fst root) root [] in
      let '(_, _, out) := fold_left (fun '(acc, bad, out) kn =>
                         match reify_fun Σ acc kn with
                         | Some (gs, _) => (acc ++ [(kn, gs)], bad, out)
                         | None => (acc, bad ++ [kn], out ++ [(snd kn, why_fun Σ kns bad acc kn)])
                         end) kns ([], [], []) in
      out
  | _ => [("", ["the root is not a constant"])]
  end.

(** what [kitc.py --reflect] reads of a program: each function's name and signature, in order *)
Definition info_of (l : list (kername * sig * fbody)) :=
  map (fun x : kername * sig * fbody => let '(kn, g, _) := x in (snd kn, sn g, sk g, sm g, sr g)) l.

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
Time Lemma sum_ok_r : callee_ok sum_Pr (gid1 0) (cbz 0) (fst sum_src) sum.
Proof. Time exact_no_check (compile_f_ok sum_Pr [] gid1 0 (fst sum_src) (snd sum_src) eq_refl eq_refl (no_callees sum_Pr gid1) eq_refl eq_refl). Time Qed.

Definition long_src := ltac:(run_template_program (tmQuoteRec long)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : long_src = (long_g, long_b)).
Definition long_Pr := mkprog [(gid1 0, compile_f gid1 0 (fst long_src) (snd long_src))] [].
Time Lemma long_ok_r : callee_ok long_Pr (gid1 0) (cbz 0) (fst long_src) long.
Proof. Time exact_no_check (compile_f_ok long_Pr [] gid1 0 (fst long_src) (snd long_src) eq_refl eq_refl (no_callees long_Pr gid1) eq_refl eq_refl). Time Qed.

(* a program: [loop] and the helper it calls, found and ordered callees first by [reach] *)
Definition hl_src := ltac:(run_template_program (tmQuoteRec loop)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) hl_src = [(h_g, h_b); (loop_g, loop_b)]).

(* the KQL program made from the reified functions, in order: function i is [gid1 i] *)
Fixpoint funs_of (i : nat) (l : list (kername * sig * fbody)) : list (positive * fn) :=
  match l with [] => [] | (_, gs, b) :: r => (gid1 i, compile_f gid1 i gs b) :: funs_of (S i) r end.
Definition sig_at (l : list (kername * sig * fbody)) (i : nat) : sig :=
  match nth_error l i with Some (_, gs, _) => gs | None => mksig 0 0 false false end.
Definition body_at (l : list (kername * sig * fbody)) (i : nat) : fbody :=
  match nth_error l i with Some (_, _, b) => b | None => FPlain (SInt 0%uint63) end.
Definition hl_Pr := mkprog (funs_of 0 hl_src) [].

(* each function's theorem, the callees' theorems before it: nothing searched, each a computation by the kernel *)
Time Lemma h_ok_r : callee_ok hl_Pr (gid1 0) (cbz 0) (sig_at hl_src 0) h.
Proof. Time exact_no_check (compile_f_ok hl_Pr [] gid1 0 (sig_at hl_src 0) (body_at hl_src 0) eq_refl eq_refl (no_callees hl_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma loop_ok_r : callee_ok hl_Pr (gid1 1) (cbz 1) (sig_at hl_src 1) loop.
Proof.
  Time exact_no_check (compile_f_ok hl_Pr [existT ftype (sig_at hl_src 0) h] gid1 1 (sig_at hl_src 1) (body_at hl_src 1) eq_refl eq_refl
    (all_ok_callees hl_Pr gid1 [existT ftype (sig_at hl_src 0) h] (conj h_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions loop_ok_r.

Print Assumptions long_ok_r.

(* ---------------------------------------------------------------- memory writes, from the user's text *)
Definition fill_src := ltac:(run_template_program (tmQuoteRec fill)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : fill_src = (fill_g, fill_b)).
Definition suffix_src := ltac:(run_template_program (tmQuoteRec suffix)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : suffix_src = (suffix_g, suffix_b)).
Definition chain10_src := ltac:(run_template_program (tmQuoteRec chain10)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : chain10_src = (chain_g, chain10_b)).

(* [init] and [fill], found from [init]'s text, [fill] first; [init]'s theorem takes [fill]'s *)
Definition if_src := ltac:(run_template_program (tmQuoteRec init)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) if_src = [(fill_g, fill_b); (init_g, init_b)]).
Definition if_Pr := mkprog (funs_of 0 if_src) [].
Time Lemma fill_ok_r : callee_ok if_Pr (gid1 0) (cbz 0) (sig_at if_src 0) fill.
Proof. Time exact_no_check (compile_f_ok if_Pr [] gid1 0 (sig_at if_src 0) (body_at if_src 0) eq_refl eq_refl (no_callees if_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma init_ok_r : callee_ok if_Pr (gid1 1) (cbz 1) (sig_at if_src 1) init.
Proof.
  Time exact_no_check (compile_f_ok if_Pr [existT ftype (sig_at if_src 0) fill] gid1 1 (sig_at if_src 1) (body_at if_src 1) eq_refl eq_refl
    (all_ok_callees if_Pr gid1 [existT ftype (sig_at if_src 0) fill] (conj fill_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions init_ok_r.

(* ---------------------------------------------------------------- counters as values, from the user's text *)
(* a program of this file (the reifier reads the functions of the root's own file): [c_rounds] (two counters, the second
   given on to a callee and to the recursive call), [c_twice] (a match on a counter inside the body, [S (S p)] given to a
   callee), [c_bud] (the counter of a number), called with counters written as numerals; the trees are KQR.v's *)
Fixpoint c_inner (n : nat) (acc : i63) : i63 := match n with O => acc | S m => c_inner m (PrimInt63.add acc 1) end.
Fixpoint c_rounds (r n : nat) (acc : i63) : i63 := match r with O => acc | S m => c_rounds m n (c_inner n acc) end.
Definition c_twice (n : nat) (a : i63) : i63 := match n with O => a | S p => c_inner (S (S p)) a end.
Definition c_bud (x : i63) : i63 := c_inner (KQ.KQRun.kq_nat x) 0.
Definition cnt_all (x : i63) : i63 := PrimInt63.add (c_rounds 3 4 x) (PrimInt63.add (c_twice 2 x) (c_bud x)).
Definition cnt_all_g := mksig 0 1 false false.
Definition cnt_all_b := FPlain (SOp Badd (SCall 1 (CCons (CS (CS (CS CO))) (CCons (CS (CS (CS (CS CO)))) CNil)) (SCons (SVar 0) SNil))
                                 (SOp Badd (SCall 2 (CCons (CS (CS CO)) CNil) (SCons (SVar 0) SNil)) (SCall 3 CNil (SCons (SVar 0) SNil)))).
Definition cnt_src := ltac:(run_template_program (tmQuoteRec cnt_all)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) cnt_src
                 = [(inner_g, inner_b); (rounds_g, rounds_b); (twice_g, twice_b); (bud_g, bud_b); (cnt_all_g, cnt_all_b)]).
Definition cnt_Pr := mkprog (funs_of 0 cnt_src) [].
Time Lemma inner_ok_r : callee_ok cnt_Pr (gid1 0) (cbz 0) (sig_at cnt_src 0) c_inner.
Proof. Time exact_no_check (compile_f_ok cnt_Pr [] gid1 0 (sig_at cnt_src 0) (body_at cnt_src 0) eq_refl eq_refl (no_callees cnt_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rounds_ok_r : callee_ok cnt_Pr (gid1 1) (cbz 1) (sig_at cnt_src 1) c_rounds.
Proof.
  Time exact_no_check (compile_f_ok cnt_Pr [existT ftype (sig_at cnt_src 0) c_inner] gid1 1 (sig_at cnt_src 1) (body_at cnt_src 1)
    eq_refl eq_refl (all_ok_callees cnt_Pr gid1 [existT ftype (sig_at cnt_src 0) c_inner] (conj inner_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma twice_ok_r : callee_ok cnt_Pr (gid1 2) (cbz 2) (sig_at cnt_src 2) c_twice.
Proof.
  Time exact_no_check (compile_f_ok cnt_Pr [existT ftype (sig_at cnt_src 0) c_inner; existT ftype (sig_at cnt_src 1) c_rounds]
    gid1 2 (sig_at cnt_src 2) (body_at cnt_src 2) eq_refl eq_refl
    (all_ok_callees cnt_Pr gid1 [existT ftype (sig_at cnt_src 0) c_inner; existT ftype (sig_at cnt_src 1) c_rounds]
       (conj inner_ok_r (conj rounds_ok_r Logic.I))) eq_refl eq_refl).
Time Qed.
Time Lemma bud_ok_r : callee_ok cnt_Pr (gid1 3) (cbz 3) (sig_at cnt_src 3) c_bud.
Proof.
  Time exact_no_check (compile_f_ok cnt_Pr [existT ftype (sig_at cnt_src 0) c_inner; existT ftype (sig_at cnt_src 1) c_rounds;
                                            existT ftype (sig_at cnt_src 2) c_twice]
    gid1 3 (sig_at cnt_src 3) (body_at cnt_src 3) eq_refl eq_refl
    (all_ok_callees cnt_Pr gid1 [existT ftype (sig_at cnt_src 0) c_inner; existT ftype (sig_at cnt_src 1) c_rounds;
                                 existT ftype (sig_at cnt_src 2) c_twice]
       (conj inner_ok_r (conj rounds_ok_r (conj twice_ok_r Logic.I)))) eq_refl eq_refl).
Time Qed.
Time Lemma cnt_all_ok_r : callee_ok cnt_Pr (gid1 4) (cbz 4) (sig_at cnt_src 4) cnt_all.
Proof.
  Time exact_no_check (compile_f_ok cnt_Pr [existT ftype (sig_at cnt_src 0) c_inner; existT ftype (sig_at cnt_src 1) c_rounds;
                                            existT ftype (sig_at cnt_src 2) c_twice; existT ftype (sig_at cnt_src 3) c_bud]
    gid1 4 (sig_at cnt_src 4) (body_at cnt_src 4) eq_refl eq_refl
    (all_ok_callees cnt_Pr gid1 [existT ftype (sig_at cnt_src 0) c_inner; existT ftype (sig_at cnt_src 1) c_rounds;
                                 existT ftype (sig_at cnt_src 2) c_twice; existT ftype (sig_at cnt_src 3) c_bud]
       (conj inner_ok_r (conj rounds_ok_r (conj twice_ok_r (conj bud_ok_r Logic.I))))) eq_refl eq_refl).
Time Qed.
Print Assumptions cnt_all_ok_r.

(* a counter grown at every round of a recursion has no bound: read, but not well formed, so not kept, with its reason *)
Definition grow_src := ltac:(run_template_program (tmQuoteRec grow)
  (fun q => let r := eval vm_compute in (reify_prog q) in exact r)).
Check (eq_refl : grow_src = None).
Eval vm_compute in ltac:(run_template_program (tmQuoteRec grow) (fun q => let r := eval vm_compute in (reify_why q) in exact r)).

(* linearity: a memory used after a newer one was made has no tree *)
Definition dup (s : mem) : mem := let s2 := KQ.KQRun.upd 0 0 1 s in KQ.KQRun.upd 0 1 (KQ.KQRun.rd 0 0 s) s2.
Definition dup_src := ltac:(run_template_program (tmQuoteRec dup)
  (fun q => let r := eval vm_compute in (reify_top q) in exact r)).
Check (eq_refl : dup_src = None).

(* why a program is not read: [loop_while]'s shape (a helper over loop_two, a closure, a test that is a boolean value) *)
Definition lw_gcd (a b : int) : int := if PrimInt63.ltb 0 b then b else a.
Definition lw_pair (n : nat) (a : int) : int * int := (a, a).
Definition lw (n : nat) (i : int) (s : mem) : int := let p := lw_pair n i in fst p.
Eval vm_compute in ltac:(run_template_program (tmQuoteRec lw) (fun q => let r := eval vm_compute in (reify_why q) in exact r)).
