(** KQRReify.v -- the reifier of the verified compiler by reflection (Rocq-C-solution.md §1.12, §12.V).

    [reify_prog] reads the user's program, quoted by MetaRocq: the functions reachable from the root, callees first, each
    with its signature (off its type) and its body as a syntax tree ([KQR.sexp] for a number, [KQR.smem] for a memory).
    It is not trusted and needs no proof: the per-program theorem is [KQR.compile_f_ok] at that tree, and the kernel checks
    by computation that the tree means the user's function -- a wrong tree is refused there.  A memory that is no longer
    the newest (a [let s2 := .. in ..] made a newer one) is dead: naming it is refused here, with its reason.  A counter
    is read as a counter expression: a counter variable (a [nat] parameter, or the predecessor a match on a counter binds),
    [O], [S c], [kq_nat e]; a boolean as a boolean expression: a comparison, a boolean variable, [true], [false], [&&], [||],
    [negb].  A function is kept only when it is well formed ([KQR.wf_f]), so a program read is a program
    [compile] takes.  The program's functions are the root, its recursive definitions and the definitions too large to be
    written out; a helper -- any other definition of the program's file, of the kit ([KQRun.v]) or of [Uint63] -- is
    written out where it is used, its arguments put in or bound by a [let], as the translator does. *)

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
Definition kn_rd32 := kn_of <% KQ.KQRun.rd32 %>.
Definition kn_upd32 := kn_of <% KQ.KQRun.upd32 %>.
Definition kn_int := kn_of <% PrimInt63.int %>.
Definition kn_mem := kn_of <% KQ.KQRun.mem %>.
Definition kn_kq_nat := kn_of <% KQ.KQRun.kq_nat %>.
Definition kn_andb := kn_of <% andb %>.
Definition kn_orb := kn_of <% orb %>.
Definition kn_negb := kn_of <% negb %>.
Definition ind_nat := ind_of <% nat %>.
Definition ind_bool := ind_of <% bool %>.
Definition kn_rd8 := kn_of <% KQ.KQRun.rd8 %>.
Definition kn_upd8 := kn_of <% KQ.KQRun.upd8 %>.
Definition kn_w64_op := kn_of <% KQ.KQRun.w64_op %>.
Definition kit_mp : modpath := fst kn_rd.
Definition uint63_mp : modpath := fst (kn_of <% Uint63.opp %>).

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
    its recursive call is given first), the function itself, a boolean *)
Inductive cent := CNum | CMem | CDead | CCnt | CPred | CSelf | CBool.

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

(** the syntax index of the boolean at place [i] of the context: the booleans nearer than it *)
Fixpoint bool_index (ctx : list cent) (i : nat) : option nat :=
  match ctx, i with
  | CBool :: _, O => Some O
  | _ :: _, O => None
  | c :: r, S i => option_map (fun j => match c with CBool => S j | _ => j end) (bool_index r i)
  | [], _ => None
  end.

Definition is_nat (t : term) : bool := match t with tInd i _ => Kername.eqb (inductive_mind i) (inductive_mind ind_nat) | _ => false end.
Definition is_ty (kn : kername) (t : term) : bool := match t with tConst k _ => Kername.eqb k kn | _ => false end.
Definition is_bool (t : term) : bool := match t with tInd i _ => Kername.eqb (inductive_mind i) (inductive_mind ind_bool) | _ => false end.

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

(** does a term contain a fixpoint (the translator's [has_fix]) *)
Fixpoint has_fix (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => true
  | S fuel =>
      match t with
      | tFix _ _ | tCoFix _ _ => true
      | tApp f args => has_fix fuel f || existsb (has_fix fuel) args
      | tLambda _ ty b | tProd _ ty b => has_fix fuel ty || has_fix fuel b
      | tLetIn _ b ty body => has_fix fuel b || has_fix fuel ty || has_fix fuel body
      | tCase _ p c brs => has_fix fuel c || existsb (fun br => has_fix fuel (bbody br)) brs
      | _ => false
      end
  end.

(** a counter written as [O] / [S ..] *)
Fixpoint cnt_lit (t : term) : bool :=
  match t with
  | tConstruct i 0 _ => Kername.eqb (inductive_mind i) (inductive_mind ind_nat)
  | tApp (tConstruct i 1 _) [c] => Kername.eqb (inductive_mind i) (inductive_mind ind_nat) && cnt_lit c
  | _ => false
  end.

(** an argument put in where its parameter stands: a variable, a number, a constant or a constructor written in the program *)
Definition plain_arg (t : term) : bool :=
  match t with tRel _ | tInt _ | tConst _ _ | tConstruct _ _ _ => true | _ => cnt_lit t end.

Definition fun_or_type (ty : term) : bool := match ty with tProd _ _ _ | tSort _ => true | _ => false end.

(** a helper written out at a call, as the translator's [beta_lets]: a parameter is given its argument -- put in when the
    argument is plain or the parameter is a function or a type, bound by a [let] otherwise, so that each argument is worked
    out once and in the order of the call.  The kernel's check sees the same term up to delta, beta and zeta *)
Fixpoint wout_go (fuel : nat) (b : term) (args : list term) : term :=
  match fuel with
  | O => mkApps b args
  | S fuel =>
      match b, args with
      | tLambda na ty body, a :: args =>
          if plain_arg a || fun_or_type ty then wout_go fuel (subst [a] 0 body) args
          else tLetIn na a ty (wout_go fuel body (map (lift0 1) args))
      | _, [] => b
      | _, _ => mkApps b args
      end
  end.
Definition wout (b : term) (args : list term) : term := wout_go (S (length args)) b args.

(** a match on a counter written as [O] / [S c] takes its branch (the kernel's check: iota) *)
Definition known_branch (c : term) (b0 b1 : branch term) : option term :=
  match c with
  | tConstruct _ 0 _ => Some (bbody b0)
  | tApp (tConstruct _ 1 _) [c'] => Some (subst [c'] 0 (bbody b1))
  | _ => None
  end.

(** the lets a term starts with, and what is under them; and back *)
Fixpoint peel (fuel : nat) (t : term) : list (aname * term * term) * term :=
  match fuel with
  | O => ([], t)
  | S fuel => match t with tLetIn na e ty body => let '(bs, r) := peel fuel body in ((na, e, ty) :: bs, r) | _ => ([], t) end
  end.
Fixpoint mklets (bs : list (aname * term * term)) (t : term) : term :=
  match bs with [] => t | (na, e, ty) :: r => tLetIn na e ty (mklets r t) end.

Section R.
Variable callees : list (kername * sig).   (* the program's functions read so far, callees first *)
Variable fm : bool.                        (* the function being read takes a memory *)
Variable fnx : nat.                        (* its counters after the first: the recursive call is given these after the
                                              predecessor *)
Variable hb : kername -> option term.      (* the helpers: a definition written out where it is used, and its body *)

(** the subject of a test: helpers and functions applied to their arguments written out, and the lets the first operand of
    [&&], [||] or [negb] starts with brought to the front -- a match on a let is put inside it (the same term up to zeta), so
    they are worked out before the test, where the translator works them out; a let in a later operand stays there *)
Fixpoint bnorm (fuel : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tLetIn na e ty body => tLetIn na e ty (bnorm fuel body)
      | tConst kn _ => match hb kn with Some b => bnorm fuel b | None => t end
      | tApp (tLambda _ _ _ as f) args => bnorm fuel (wout f args)
      | tApp (tConst kn u) args =>
          if Kername.eqb kn kn_negb then
            match args with [a] => let '(bs, a0) := peel 1000 (bnorm fuel a) in mklets bs (tApp (tConst kn u) [a0]) | _ => t end
          else if Kername.eqb kn kn_andb || Kername.eqb kn kn_orb then
            match args with
            | [a; b] => let '(bs, a0) := peel 1000 (bnorm fuel a) in mklets bs (tApp (tConst kn u) [a0; lift0 (length bs) b])
            | _ => t
            end
          else match hb kn with Some b => bnorm fuel (wout b args) | None => t end
      | _ => t
      end
  end.

(** a test whose subject starts with lets: the lets, then the test *)
Definition lets_first (ci : case_info) (p : predicate term) (c : term) (brs : list (branch term)) : option term :=
  match peel 1000 c with
  | ([], _) => None
  | (bs, c0) => match lift0 (length bs) (tCase ci p c brs) with tCase ci' p' _ brs' => Some (mklets bs (tCase ci' p' c0 brs')) | _ => None end
  end.

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
  | tConst kn _ => match hb kn with Some b => reify fuel ctx b | None => None end
  | tApp (tConst kn _) args =>
      if eq_mp (fst kn) prim_mp then
        match binop_v (snd kn), args with
        | Some o, [a; b] =>
            match reify fuel ctx a, reify fuel ctx b with Some x, Some y => Some (SOp o x y) | _, _ => None end
        | _, _ => None
        end
      else if Kername.eqb kn kn_rd || Kername.eqb kn kn_rd32 then
        match args with
        | [h; i; tRel m] =>
            if is_ent CMem ctx m then
              match reify fuel ctx h, reify fuel ctx i with
              | Some x, Some y => Some (if Kername.eqb kn kn_rd then SRd x y else SRd32 x y)
              | _, _ => None
              end
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
        | None => match hb kn with Some b => reify fuel ctx (wout b args) | None => None end
        end
  | tApp (tRel fi) (tRel mi :: rest) =>
      if is_ent CSelf ctx fi && is_ent CPred ctx mi && Nat.leb fnx (length rest) then
        match reify_cs (firstn fnx rest), read_mem ctx fm (skipn fnx rest) with
        | Some cs, Some nums => option_map (SRec cs) (reify_args nums)
        | _, _ => None
        end
      else None
  | tApp (tLambda _ _ _ as f) args => reify fuel ctx (wout f args)
  | tCase ci p c0 [b0; b1] =>
      let c := if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then bnorm fuel c0 else c0 in
      match lets_first ci p c [b0; b1] with Some t' => reify fuel ctx t' | None =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        match (match c with
               | tApp (tConst kn _) [a; b] => if eq_mp (fst kn) prim_mp then option_map (fun x => (x, a, b)) (cmp_v (snd kn)) else None
               | _ => None
               end) with
        | Some (cmp, a, b) =>      (* one comparison: a test as before *)
            match reify fuel ctx a, reify fuel ctx b, reify fuel ctx (bbody b0), reify fuel ctx (bbody b1) with
            | Some x, Some y, Some t1, Some t2 => Some (SIf cmp x y t1 t2)
            | _, _, _, _ => None
            end
        | None =>
            match reify_b fuel ctx c, reify fuel ctx (bbody b0), reify fuel ctx (bbody b1) with
            | Some x, Some t1, Some t2 => Some (SIfB x t1 t2)
            | _, _, _ => None
            end
        end
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel i =>
            match cnt_index ctx i, reify fuel ctx (bbody b0), reify fuel (CCnt :: ctx) (bbody b1) with
            | Some x, Some e0, Some e1 => Some (SMatch x e0 e1)
            | _, _, _ => None
            end
        | _ => match known_branch c b0 b1 with Some t => reify fuel ctx t | None => None end
        end
      else None
      end
  | tLetIn _ b (tConst kty _) body =>
      if Kername.eqb kty kn_int then
        match reify fuel ctx b, reify fuel (CNum :: ctx) body with Some x, Some y => Some (SLet x y) | _, _ => None end
      else None
  | tLetIn _ b ty body =>
      if is_bool ty then
        match reify_b fuel ctx b, reify fuel (CBool :: ctx) body with Some x, Some y => Some (SLetB x y) | _, _ => None end
      else if is_nat ty then
        match reify_c fuel ctx b, reify fuel (CCnt :: ctx) body with Some x, Some y => Some (SLetC x y) | _, _ => None end
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
  | tConst kn _ => match hb kn with Some b => reify_c fuel ctx b | None => None end
  | tApp (tLambda _ _ _ as f) args => reify_c fuel ctx (wout f args)
  | tApp (tConst kn _) args =>
      if Kername.eqb kn kn_kq_nat then match args with [e] => option_map CNat (reify fuel ctx e) | _ => None end
      else match hb kn with Some b => reify_c fuel ctx (wout b args) | None => None end
  | _ => None
  end
  end
with reify_b (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sbool :=
  match fuel with
  | O => None
  | S fuel =>
  match t with
  | tRel i => option_map BVar (bool_index ctx i)
  | tConstruct i 0 _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then Some BTrue else None
  | tConstruct i 1 _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then Some BFalse else None
  | tConst kn _ => match hb kn with Some b => reify_b fuel ctx b | None => None end
  | tApp (tLambda _ _ _ as f) args => reify_b fuel ctx (wout f args)
  | tApp (tConst kn _) args =>
      let helper := fun _ : unit => match hb kn with Some b => reify_b fuel ctx (wout b args) | None => None end in
      match args with
      | [a] => if Kername.eqb kn kn_negb then option_map BNot (reify_b fuel ctx a) else helper tt
      | [a; b] =>
          if Kername.eqb kn kn_andb then
            match reify_b fuel ctx a, reify_b fuel ctx b with Some x, Some y => Some (BAnd x y) | _, _ => None end
          else if Kername.eqb kn kn_orb then
            match reify_b fuel ctx a, reify_b fuel ctx b with Some x, Some y => Some (BOr x y) | _, _ => None end
          else
            match (if eq_mp (fst kn) prim_mp then cmp_v (snd kn) else None) with
            | Some c => match reify fuel ctx a, reify fuel ctx b with Some x, Some y => Some (BCmp c x y) | _, _ => None end
            | None => helper tt
            end
      | _ => helper tt
      end
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
  | tConst kn _ => match hb kn with Some b => reify_m fuel ctx b | None => None end
  | tApp (tConst kn _) args =>
      if Kername.eqb kn kn_upd || Kername.eqb kn kn_upd32 then
        match args with
        | [h; i; v; m] =>
            match reify fuel ctx h, reify fuel ctx i, reify fuel ctx v, reify_m fuel ctx m with
            | Some a, Some b, Some c, Some d => Some (if Kername.eqb kn kn_upd then MUpd a b c d else MUpd32 a b c d)
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
        | None => match hb kn with Some b => reify_m fuel ctx (wout b args) | None => None end
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
  | tApp (tLambda _ _ _ as f) args => reify_m fuel ctx (wout f args)
  | tCase ci p c0 [b0; b1] =>
      let c := if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then bnorm fuel c0 else c0 in
      match lets_first ci p c [b0; b1] with Some t' => reify_m fuel ctx t' | None =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        match (match c with
               | tApp (tConst kn _) [a; b] => if eq_mp (fst kn) prim_mp then option_map (fun x => (x, a, b)) (cmp_v (snd kn)) else None
               | _ => None
               end) with
        | Some (cmp, a, b) =>
            match reify fuel ctx a, reify fuel ctx b, reify_m fuel ctx (bbody b0), reify_m fuel ctx (bbody b1) with
            | Some x, Some y, Some m1, Some m2 => Some (MIf cmp x y m1 m2)
            | _, _, _, _ => None
            end
        | None =>
            match reify_b fuel ctx c, reify_m fuel ctx (bbody b0), reify_m fuel ctx (bbody b1) with
            | Some x, Some m1, Some m2 => Some (MIfB x m1 m2)
            | _, _, _ => None
            end
        end
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel i =>
            match cnt_index ctx i, reify_m fuel ctx (bbody b0), reify_m fuel (CCnt :: ctx) (bbody b1) with
            | Some x, Some m0, Some m1 => Some (MMatch x m0 m1)
            | _, _, _ => None
            end
        | _ => match known_branch c b0 b1 with Some t => reify_m fuel ctx t | None => None end
        end
      else None
      end
  | tLetIn _ b (tConst kty _) body =>
      if Kername.eqb kty kn_int then
        match reify fuel ctx b, reify_m fuel (CNum :: ctx) body with Some x, Some y => Some (MLet x y) | _, _ => None end
      else if Kername.eqb kty kn_mem then
        match reify_m fuel ctx b, reify_m fuel (CMem :: kill_mem ctx) body with Some x, Some y => Some (MLetM x y) | _, _ => None end
      else None
  | tLetIn _ b ty body =>
      if is_bool ty then
        match reify_b fuel ctx b, reify_m fuel (CBool :: ctx) body with Some x, Some y => Some (MLetB x y) | _, _ => None end
      else if is_nat ty then
        match reify_c fuel ctx b, reify_m fuel (CCnt :: ctx) body with Some x, Some y => Some (MLetC x y) | _, _ => None end
      else None
  | _ => None
  end
  end.

Definition is_rel (t : term) : bool := match t with tRel _ => true | _ => false end.

(** a number made after memories: lets of memories, numbers and booleans, tests, and at the end a number from the newest
    memory.  A read or a call whose memory is made in place ([rd h i (f .. s)]) is read as [let s2 := f .. s in rd h i s2] --
    the same term up to [let]; its numbers are read with the older memories dead, so they may not name one *)
Fixpoint reify_x (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sx :=
  match fuel with
  | O => None
  | S fuel =>
  let fallback := option_map XRet (reify fuel ctx t) in
  let reify_args (c : list cent) (l : list term) : option sexps := option_map to_sexps (opt_all (map (reify fuel c) l)) in
  let reify_cs (c : list cent) (l : list term) : option scnts := option_map to_scnts (opt_all (map (reify_c fuel c) l)) in
  match t with
  | tLetIn _ b ty body =>
      if is_ty kn_mem ty then
        match reify_m fuel ctx b, reify_x fuel (CMem :: kill_mem ctx) body with Some m, Some x => Some (XLetM m x) | _, _ => None end
      else if is_ty kn_int ty then
        match reify fuel ctx b, reify_x fuel (CNum :: ctx) body with Some e, Some x => Some (XLet e x) | _, _ => None end
      else if is_bool ty then
        match reify_b fuel ctx b, reify_x fuel (CBool :: ctx) body with Some e, Some x => Some (XLetB e x) | _, _ => None end
      else if is_nat ty then
        match reify_c fuel ctx b, reify_x fuel (CCnt :: ctx) body with Some c, Some x => Some (XLetC c x) | _, _ => None end
      else None
  | tApp (tLambda _ _ _ as f) args => reify_x fuel ctx (wout f args)
  | tCase ci p c0 [b0; b1] =>
      let c := if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then bnorm fuel c0 else c0 in
      match lets_first ci p c [b0; b1] with Some t' => reify_x fuel ctx t' | None =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        match (match c with
               | tApp (tConst kn _) [a; b] => if eq_mp (fst kn) prim_mp then option_map (fun x => (x, a, b)) (cmp_v (snd kn)) else None
               | _ => None
               end) with
        | Some (cmp, a, b) =>
            match reify fuel ctx a, reify fuel ctx b, reify_x fuel ctx (bbody b0), reify_x fuel ctx (bbody b1) with
            | Some x, Some y, Some t1, Some t2 => Some (XIf cmp x y t1 t2)
            | _, _, _, _ => None
            end
        | None =>
            match reify_b fuel ctx c, reify_x fuel ctx (bbody b0), reify_x fuel ctx (bbody b1) with
            | Some x, Some t1, Some t2 => Some (XIfB x t1 t2)
            | _, _, _ => None
            end
        end
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel i =>
            match cnt_index ctx i, reify_x fuel ctx (bbody b0), reify_x fuel (CCnt :: ctx) (bbody b1) with
            | Some x, Some t0, Some t1 => Some (XMatch x t0 t1)
            | _, _, _ => None
            end
        | _ => match known_branch c b0 b1 with Some t => reify_x fuel ctx t | None => None end
        end
      else None
      end
  | tApp (tConst kn _) args =>
      if Kername.eqb kn kn_rd || Kername.eqb kn kn_rd32 then
        match args with
        | [h; i; m] =>
            if is_rel m then fallback else
            match reify_m fuel ctx m, reify fuel (kill_mem ctx) h, reify fuel (kill_mem ctx) i with
            | Some mm, Some x, Some y => Some (XLetM mm (XRet (if Kername.eqb kn kn_rd then SRd x y else SRd32 x y)))
            | _, _, _ => None
            end
        | _ => None
        end
      else
        match find_callee kn callees 0, rev args with
        | Some (f, gs), m :: rnums =>
            if negb (sr gs) && negb (sw gs) && sm gs && negb (is_rel m) && Nat.leb (sn gs) (length (rev rnums)) then
              let rest := rev rnums in
              match reify_m fuel ctx m, reify_cs (kill_mem ctx) (firstn (sn gs) rest), reify_args (kill_mem ctx) (skipn (sn gs) rest) with
              | Some mm, Some cs, Some As => Some (XLetM mm (XRet (SCall f cs As)))
              | _, _, _ => None
              end
            else fallback
        | None, _ => match hb kn with Some b => reify_x fuel ctx (wout b args) | None => fallback end
        | _, _ => fallback
        end
  | tConst kn _ => match hb kn with Some b => reify_x fuel ctx b | None => fallback end
  | _ => fallback
  end
  end.
End R.

Fixpoint lams (t : term) : list term * term :=
  match t with tLambda _ ty b => let '(l, r) := lams b in (ty :: l, r) | _ => ([], t) end.


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
  if forallb (is_ty kn_int) nums && (r || is_ty kn_int ret) then Some (mksig c (length nums) m r false) else None.

Definition fun_ctx (gs : sig) : list cent := (if sm gs then [CMem] else []) ++ repeat CNum (sk gs) ++ repeat CCnt (sn gs).

(** one function of the program, given the ones before it, as its text reads: a recursive function starts with a match
    on its first counter *)
Definition read_fun (Σ : global_env) (hb : kername -> option term) (callees : list (kername * sig)) (kn : kername)
  : option (sig * fbody) :=
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
                    match reify_m callees (sm gs) nx hb 100000 ctx (bbody b0), reify_m callees (sm gs) nx hb 100000 (CPred :: ctx) (bbody b1) with
                    | Some m0, Some m1 => Some (gs, FRecM m0 m1)
                    | _, _ => None
                    end
                  else
                    match reify callees (sm gs) nx hb 100000 ctx (bbody b0), reify callees (sm gs) nx hb 100000 (CPred :: ctx) (bbody b1) with
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
              if sr gs then option_map (fun m => (gs, FPlainM m)) (reify_m callees (sm gs) nx hb 100000 (fun_ctx gs) body)
              else match reify callees (sm gs) nx hb 100000 (fun_ctx gs) body with
                   | Some e => Some (gs, FPlain e)
                   | None => if sm gs then
                               option_map (fun x => (mksig (sn gs) (sk gs) true false true, FPlainX x))
                                          (reify_x callees (sm gs) nx hb 100000 (fun_ctx gs) body)
                             else None
                   end
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(** ... kept when it is well formed, the condition of [compile_f_ok]: a program read is a program compiled *)
Definition reify_fun (Σ : global_env) (hb : kername -> option term) (callees : list (kername * sig)) (kn : kername)
  : option (sig * fbody) :=
  match read_fun Σ hb callees kn with
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

(** the size of a term, as the translator counts it ([term_size]) *)
Fixpoint term_size (fuel : nat) (t : term) : nat :=
  match fuel with
  | O => 0
  | S fuel =>
      match t with
      | tApp f args => 1 + term_size fuel f + fold_left (fun a x => a + term_size fuel x) args 0
      | tLambda _ _ b => 1 + term_size fuel b
      | tLetIn _ b _ body => 1 + term_size fuel b + term_size fuel body
      | tCase _ _ c brs => 1 + term_size fuel c + fold_left (fun a br => a + term_size fuel (bbody br)) brs 0
      | _ => 1
      end
  end.

(** a definition too large to be written out at its uses, as the translator decides ([big_fun]): more than 40 nodes, its
    parameters numbers, counters, booleans or a memory, a number or a memory as its result *)
Definition inline_limit : nat := 40.
Definition big_def (Σ : global_env) (kn : kername) : bool :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some (tFix _ _) | None => false
      | Some b =>
          let r := ret_ty (cst_type cb) in
          (is_ty kn_int r || is_ty kn_mem r)
          && forallb (fun t => is_ty kn_int t || is_ty kn_mem t || is_nat t || is_bool t) (fst (lams b))
          && Nat.ltb inline_limit (term_size 100000 b)
      end
  | _ => false
  end.

(** a function of the program (the translator's [is_fun]): the root, and the definitions of its file that are a fixpoint
    or too large to be written out *)
Definition is_fn (Σ : global_env) (mp : modpath) (root kn : kername) : bool :=
  Kername.eqb kn root
  || (eq_mp (fst kn) mp && (match body_of Σ kn with Some (tFix _ _) => true | _ => false end || big_def Σ kn)).

(** the program's functions reachable from the root, callees first; the helpers they use (definitions of the file or of
    the kit that are not functions) are looked through for the functions they call, as the translator's [reach] does --
    each constant once ([seen]) *)
Fixpoint reach_go (fuel : nat) (Σ : global_env) (mp : modpath) (root kn : kername) (st : list kername * list kername)
  : list kername * list kername :=
  match fuel with
  | O => st
  | S fuel =>
      let '(done, seen) := st in
      if existsb (Kername.eqb kn) seen then st
      else match body_of Σ kn with
           | Some b =>
               let cs := filter (fun k => (eq_mp (fst k) mp || eq_mp (fst k) kit_mp) && negb (Kername.eqb k kn)) (consts 10000 b []) in
               let '(done', seen') := fold_left (fun st k => reach_go fuel Σ mp root k st) (rev cs) (done, kn :: seen) in
               (if is_fn Σ mp root kn then List.app done' [kn] else done', seen')
           | None => (done, kn :: seen)
           end
  end.
Definition reach (fuel : nat) (Σ : global_env) (mp : modpath) (root kn : kername) (done : list kername) : list kername :=
  fst (reach_go fuel Σ mp root kn (done, done)).

(** a helper, written out where it is used (the translator's [helper_body]): a definition of the program's file, of the kit
    ([KQRun.v]) or of [Uint63] that is not a function of the program and has no fixpoint.  Bytes and halfwords ([rd8],
    [upd8], and so [rd16], [upd16] over them) are left for one byte access each, as the translator makes them, not shifts of
    4-byte cells; a 64-bit operation is one instruction; a budget ([kq_nat]) is a counter of its own *)
Definition helper_of (Σ : global_env) (mp : modpath) (fns : list kername) (kn : kername) : option term :=
  if Kername.eqb kn kn_rd8 || Kername.eqb kn kn_upd8 || Kername.eqb kn kn_w64_op || Kername.eqb kn kn_kq_nat
     || existsb (Kername.eqb kn) fns then None
  else if eq_mp (fst kn) mp || eq_mp (fst kn) kit_mp || eq_mp (fst kn) uint63_mp then
    match body_of Σ kn with Some b => if has_fix 1000 b then None else Some b | None => None end
  else None.

(** the whole program: its functions callees first, each with its signature and body *)
Definition reify_prog (p : program) : option (list (kername * sig * fbody)) :=
  match p with
  | (Σ, tConst root _) =>
      let kns := reach 1000 Σ (fst root) root root [] in
      let hb := helper_of Σ (fst root) kns in
      fold_left (fun acc kn =>
                   match acc with
                   | Some l => match reify_fun Σ hb (map (fun x => (fst (fst x), snd (fst x))) l) kn with
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
  || Kername.eqb kn kn_rd || Kername.eqb kn kn_upd || Kername.eqb kn kn_rd32 || Kername.eqb kn kn_upd32
  || Kername.eqb kn kn_kq_nat || existsb (Kername.eqb kn) fns
  || Kername.eqb kn kn_andb || Kername.eqb kn kn_orb || Kername.eqb kn kn_negb
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
Fixpoint blockers (fuel : nat) (fns : list kername) (hb : kername -> option term) (t : term) (acc : list string) : list string :=
  match fuel with
  | O => acc
  | S fuel =>
      match t with
      | tConst kn _ =>
          if known_const fns kn then acc
          else match hb kn with Some b => blockers fuel fns hb b acc | None => add_s (snd kn) acc end
      | tApp f args => fold_left (fun a x => blockers fuel fns hb x a) args (blockers fuel fns hb f acc)
      | tLambda _ _ b => blockers fuel fns hb b acc
      | tLetIn _ b ty body =>
          let acc := if is_ty kn_int ty || is_ty kn_mem ty || is_bool ty || is_nat ty then acc else add_s ("a let of " ^ head_name ty) acc in
          blockers fuel fns hb body (blockers fuel fns hb b acc)
      | tCase ci _ c brs =>
          let i := ci_ind ci in
          let acc := if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) || Kername.eqb (inductive_mind i) (inductive_mind ind_bool)
                     then acc else add_s ("a match on " ^ snd (inductive_mind i)) acc in
          fold_left (fun a br => blockers fuel fns hb (bbody br) a) brs (blockers fuel fns hb c acc)
      | tProj _ c => blockers fuel fns hb c (add_s "a projection" acc)
      | tConstruct i _ _ =>      (* O and S are counters, true and false booleans *)
          if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) || Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then acc
          else add_s ("a constructor of " ^ snd (inductive_mind i)) acc
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
    place, a call of a function that gives back a memory *)
Fixpoint writes (fuel : nat) (hb : kername -> option term) (mfns : list kername) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tConst kn _ => Kername.eqb kn kn_upd || Kername.eqb kn kn_upd32 || existsb (Kername.eqb kn) mfns
                       || match hb kn with Some b => writes fuel hb mfns b | None => false end
      | tApp f args => rd_in_place f args || writes fuel hb mfns f || existsb (writes fuel hb mfns) args
      | tLambda _ _ b => writes fuel hb mfns b
      | tLetIn _ b ty body => is_ty kn_mem ty || writes fuel hb mfns b || writes fuel hb mfns body
      | tCase _ _ c brs => writes fuel hb mfns c || existsb (fun br => writes fuel hb mfns (bbody br)) brs
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

(** the head of a boolean expression the syntax reads *)
Definition bool_shape (c : term) : bool :=
  match c with
  | tRel _ | tConstruct _ _ _ => true
  | tApp (tConst kn _) _ => Kername.eqb kn kn_andb || Kername.eqb kn kn_orb || Kername.eqb kn kn_negb
                            || (eq_mp (fst kn) prim_mp && match cmp_v (snd kn) with Some _ => true | None => false end)
  | _ => false
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
           && negb (bool_shape c))
          || bool_test fuel c || existsb (fun br => bool_test fuel (bbody br)) brs
      | _ => false
      end
  end.

(** the helpers a term writes out, through the helpers they write out, each once *)
Fixpoint helpers_in (fuel : nat) (hb : kername -> option term) (t : term) (seen : list kername) : list kername :=
  match fuel with
  | O => seen
  | S fuel =>
      fold_left (fun sn k => if existsb (Kername.eqb k) sn then sn
                             else match hb k with Some b => helpers_in fuel hb b (k :: sn) | None => sn end)
                (consts 10000 t []) seen
  end.

(** a function's reasons: its signature, its recursion, its constructs, their places *)
Definition why_fun (Σ : global_env) (hb : kername -> option term) (fns bad : list kername) (callees : list (kername * sig))
  (kn : kername) : list string :=
  if match read_fun Σ hb callees kn with Some _ => true | None => false end then
    ["read, but not well formed: a recursive call given a counter grown by S (it would have no bound), a call given fewer"
     ^ " arguments than its function takes, a counter more than 2^20 successors deep, a let of a counter grown by S over a"
     ^ " variable (above the function's bound), or a call of a number function that writes the memory (not yet: the"
     ^ " caller's memory would not be the text's)"]
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
          let hs := helpers_in 50 hb inner [] in      (* the helpers written out in it: each looked at once *)
          let texts := inner :: flat_map (fun k => match hb k with Some b => [b] | None => [] end) hs in
          let nohb := fun _ : kername => @None term in
          let odd := fold_left (fun a t => if is_ty kn_int t || is_ty kn_mem t || is_nat t then a else add_s (head_name t) a)
                               (tys ++ [ret_ty ty]) [] in
          let sigr := match read_sig tys (ret_ty ty), odd with
                      | Some _, _ => []
                      | None, [] => ["parameters in an order not read (a counter after a number, or the memory not last)"]
                      | None, x :: r => ["a parameter or result of type " ^ fold_left (fun a y => a ^ ", " ^ y) r x]
                      end in
          let r0 := if rec == "" then sigr else rec :: sigr in
          let r1 := fold_left (fun a t => blockers 100000 (fns ++ hs) nohb t a) texts r0 in
          let numfn := negb (is_ty kn_mem (ret_ty ty)) in
          let isfix := match b with tFix _ _ => true | _ => false end in
          let mfns := filter (fun k => match lookup_env Σ k with
                                       | Some (ConstantDecl c) => is_ty kn_mem (ret_ty (cst_type c)) | _ => false end) fns in
          let r2 := if numfn && existsb (writes 100000 nohb mfns) texts
                    then add_s (if isfix then "a recursive function that writes the memory and gives back a number"
                                else "a number function that writes the memory where it is not read yet") r1
                    else r1 in
          let r3 := if nat_match_value 100000 inner then add_s "a match on a counter that is not a variable" r2 else r2 in
          let r4 := if bool_test 100000 inner then add_s "a test on a boolean that is not read (a call giving back a boolean)" r3 else r3 in
          let r4 := fold_left (fun a k => if existsb (Kername.eqb k) bad then add_s ("calls " ^ snd k ^ ", not read") a else a)
                              (fold_left (fun a t => consts 10000 t a) texts []) r4 in
          match r4 with [] => ["a construct in a place not read (not classified)"] | _ => r4 end
      | None => ["no body"]
      end
  | _ => ["not a constant"]
  end.

(** for each function of the program not read (in [reach]'s order), its reasons *)
Definition reify_why (p : program) : list (string * list string) :=
  match p with
  | (Σ, tConst root _) =>
      let kns := reach 1000 Σ (fst root) root root [] in
      let hb := helper_of Σ (fst root) kns in
      let '(_, _, out) := fold_left (fun '(acc, bad, out) kn =>
                         match reify_fun Σ hb acc kn with
                         | Some (gs, _) => (acc ++ [(kn, gs)], bad, out)
                         | None => (acc, bad ++ [kn], out ++ [(snd kn, why_fun Σ hb kns bad acc kn)])
                         end) kns ([], [], []) in
      out
  | _ => [("", ["the root is not a constant"])]
  end.

(** what [kitc.py --reflect] reads of a program: each function's name and signature, in order *)
Definition info_of (l : list (kername * sig * fbody)) :=
  map (fun x : kername * sig * fbody => let '(kn, g, _) := x in (snd kn, sn g, sk g, sm g, sr g, sw g)) l.

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

(* a program: [loop] and the helper [h] it calls, written out at the call -- [acc] put in, the read bound by a let -- so
   one function *)
Definition loop_wb := FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 1) (SInt 1))
                        (SCons (SLet (SRd (SInt 0) (SVar 1)) (SOp Badd (SOp Bmul (SVar 1) (SInt 2)) (SVar 0))) SNil))).
Definition hl_src := ltac:(run_template_program (tmQuoteRec loop)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) hl_src = [(loop_g, loop_wb)]).

(* the KQL program made from the reified functions, in order: function i is [gid1 i] *)
Fixpoint funs_of (i : nat) (l : list (kername * sig * fbody)) : list (positive * fn) :=
  match l with [] => [] | (_, gs, b) :: r => (gid1 i, compile_f gid1 i gs b) :: funs_of (S i) r end.
Definition sig_at (l : list (kername * sig * fbody)) (i : nat) : sig :=
  match nth_error l i with Some (_, gs, _) => gs | None => mksig 0 0 false false false end.
Definition body_at (l : list (kername * sig * fbody)) (i : nat) : fbody :=
  match nth_error l i with Some (_, _, b) => b | None => FPlain (SInt 0%uint63) end.
Definition hl_Pr := mkprog (funs_of 0 hl_src) [].

(* the function's theorem: nothing searched, a computation by the kernel, which unfolds [h] where the text calls it *)
Time Lemma loop_ok_r : callee_ok hl_Pr (gid1 0) (cbz 0) (sig_at hl_src 0) loop.
Proof. Time exact_no_check (compile_f_ok hl_Pr [] gid1 0 (sig_at hl_src 0) (body_at hl_src 0) eq_refl eq_refl (no_callees hl_Pr gid1) eq_refl eq_refl). Time Qed.
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
   given on to a callee and to the recursive call), called with counters written as numerals; the helpers [c_twice] (a
   match on a counter, [S (S p)] given to a callee) and [c_bud] (the counter of a number) written out where [cnt_all] uses
   them -- [c_twice 2 x] takes the branch of its written counter, a call of [c_inner] with [S (S (S O))] *)
Fixpoint c_inner (n : nat) (acc : i63) : i63 := match n with O => acc | S m => c_inner m (PrimInt63.add acc 1) end.
Fixpoint c_rounds (r n : nat) (acc : i63) : i63 := match r with O => acc | S m => c_rounds m n (c_inner n acc) end.
Definition c_twice (n : nat) (a : i63) : i63 := match n with O => a | S p => c_inner (S (S p)) a end.
Definition c_bud (x : i63) : i63 := c_inner (KQ.KQRun.kq_nat x) 0.
Definition cnt_all (x : i63) : i63 := PrimInt63.add (c_rounds 3 4 x) (PrimInt63.add (c_twice 2 x) (c_bud x)).
Definition cnt_all_g := mksig 0 1 false false false.
Definition cnt_all_b := FPlain (SOp Badd (SCall 1 (CCons (CS (CS (CS CO))) (CCons (CS (CS (CS (CS CO)))) CNil)) (SCons (SVar 0) SNil))
                                 (SOp Badd (SCall 0 (CCons (CS (CS (CS CO))) CNil) (SCons (SVar 0) SNil))
                                           (SCall 0 (CCons (CNat (SVar 0)) CNil) (SCons (SInt 0) SNil)))).
Definition cnt_src := ltac:(run_template_program (tmQuoteRec cnt_all)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) cnt_src
                 = [(inner_g, inner_b); (rounds_g, rounds_b); (cnt_all_g, cnt_all_b)]).
Definition cnt_Pr := mkprog (funs_of 0 cnt_src) [].
Time Lemma inner_ok_r : callee_ok cnt_Pr (gid1 0) (cbz 0) (sig_at cnt_src 0) c_inner.
Proof. Time exact_no_check (compile_f_ok cnt_Pr [] gid1 0 (sig_at cnt_src 0) (body_at cnt_src 0) eq_refl eq_refl (no_callees cnt_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rounds_ok_r : callee_ok cnt_Pr (gid1 1) (cbz 1) (sig_at cnt_src 1) c_rounds.
Proof.
  Time exact_no_check (compile_f_ok cnt_Pr [existT ftype (sig_at cnt_src 0) c_inner] gid1 1 (sig_at cnt_src 1) (body_at cnt_src 1)
    eq_refl eq_refl (all_ok_callees cnt_Pr gid1 [existT ftype (sig_at cnt_src 0) c_inner] (conj inner_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma cnt_all_ok_r : callee_ok cnt_Pr (gid1 2) (cbz 2) (sig_at cnt_src 2) cnt_all.
Proof.
  Time exact_no_check (compile_f_ok cnt_Pr [existT ftype (sig_at cnt_src 0) c_inner; existT ftype (sig_at cnt_src 1) c_rounds]
    gid1 2 (sig_at cnt_src 2) (body_at cnt_src 2) eq_refl eq_refl
    (all_ok_callees cnt_Pr gid1 [existT ftype (sig_at cnt_src 0) c_inner; existT ftype (sig_at cnt_src 1) c_rounds]
       (conj inner_ok_r (conj rounds_ok_r Logic.I))) eq_refl eq_refl).
Time Qed.
Print Assumptions cnt_all_ok_r.

(* a counter grown at every round of a recursion has no bound: read, but not well formed, so not kept, with its reason *)
Definition grow_src := ltac:(run_template_program (tmQuoteRec grow)
  (fun q => let r := eval vm_compute in (reify_prog q) in exact r)).
Check (eq_refl : grow_src = None).
Eval vm_compute in ltac:(run_template_program (tmQuoteRec grow) (fun q => let r := eval vm_compute in (reify_why q) in exact r)).

(* ---------------------------------------------------------------- booleans, from the user's text *)
(* tests made of [&&], [||], [negb] (conditional moves on their values), a boolean let tested at the end of a loop, a memory
   chosen by [a && negb b]: the reified trees are KQR.v's *)
Definition chk_src := ltac:(run_template_program (tmQuoteRec chk)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : chk_src = (chk_g, chk_b)).
Definition cnt_in_src := ltac:(run_template_program (tmQuoteRec cnt_in)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : cnt_in_src = (cnt_in_g, cnt_in_b)).
Definition mark_src := ltac:(run_template_program (tmQuoteRec mark)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : mark_src = (mark_g, mark_b)).

(* ---------------------------------------------------------------- a number made after memories, from the user's text *)
(* [mafter] makes memories by lets and calls, tests, and reads a memory made in place ([rd 0 2 (bump 2 s3)]): read as a number
   made after memories, the read in place as a memory let; the helper [bump] written out at both uses, [fill] a function *)
Definition after_wb := FPlainX (XLetM (MUpd (SInt 0) (SInt 1) (SOp Badd (SRd (SInt 0) (SOp Bsub (SInt 1) (SInt 1))) (SInt 1)) MCur)
  (XLetM (MCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil) MCur)
    (XIf Clt (SRd (SInt 0) (SInt 1)) (SInt 10)
         (XLetM (MUpd (SInt 0) (SInt 2) (SOp Badd (SRd (SInt 0) (SOp Bsub (SInt 2) (SInt 1))) (SInt 2)) MCur) (XRet (SRd (SInt 0) (SInt 2))))
         (XRet (SOp Badd (SVar 0) (SInt 1)))))).
Definition after_src := ltac:(run_template_program (tmQuoteRec mafter)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) after_src = [(fill_g, fill_b); (after_g, after_wb)]).
Definition af_Pr := mkprog (funs_of 0 after_src) [].
Time Lemma fill_ok_a : callee_ok af_Pr (gid1 0) (cbz 0) (sig_at after_src 0) fill.
Proof. Time exact_no_check (compile_f_ok af_Pr [] gid1 0 (sig_at after_src 0) (body_at after_src 0) eq_refl eq_refl (no_callees af_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma after_ok_a : callee_ok af_Pr (gid1 1) (cbz 1) (sig_at after_src 1) mafter.
Proof.
  Time exact_no_check (compile_f_ok af_Pr [existT ftype (sig_at after_src 0) fill] gid1 1 (sig_at after_src 1) (body_at after_src 1)
    eq_refl eq_refl (all_ok_callees af_Pr gid1 [existT ftype (sig_at after_src 0) fill] (conj fill_ok_a Logic.I)) eq_refl eq_refl).
Time Qed.

(* ---------------------------------------------------------------- narrow memory, from the user's text *)
Definition acc32_src := ltac:(run_template_program (tmQuoteRec acc32)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : acc32_src = (acc32_g, acc32_b)).
Definition sum32_src := ltac:(run_template_program (tmQuoteRec sum32)
  (fun q => let r := eval vm_compute in (reify_top q) in match r with Some ?x => exact x end)).
Check (eq_refl : sum32_src = (sum32_g, sum32_b)).

(* ---------------------------------------------------------------- helpers written out where they are used *)
(* the kit's helpers (KQRun.v: C's signed division and remainder corrected to Z's rounding, a parity test, a maximum, an
   absolute value, a negation, a minimum) written out at their uses: an argument that is a variable or a number put in, a
   sum bound by a let; the parity test is a test on a boolean.  One function; the kernel unfolds the helpers in the check *)
Definition hz (a b : i63) (s : mem) : i63 :=
  if KQ.KQRun.zeven a then PrimInt63.add (KQ.KQRun.zdiv a 3) (KQ.KQRun.zmod (PrimInt63.add b 1) a)
  else KQ.KQRun.zmax (KQ.KQRun.zabs (KQ.KQRun.rd 0 a s)) (KQ.KQRun.zopp (KQ.KQRun.zmin a b)).
Definition hz_src := ltac:(run_template_program (tmQuoteRec hz)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd (fst (fst x))) hz_src = ["hz"%bs]).
Definition hz_Pr := mkprog (funs_of 0 hz_src) [].
Time Lemma hz_ok_r : callee_ok hz_Pr (gid1 0) (cbz 0) (sig_at hz_src 0) hz.
Proof. Time exact_no_check (compile_f_ok hz_Pr [] gid1 0 (sig_at hz_src 0) (body_at hz_src 0) eq_refl eq_refl (no_callees hz_Pr gid1) eq_refl eq_refl). Time Qed.
Print Assumptions hz_ok_r.

(* a definition of the file larger than the translator's bound (40 nodes) stays a function of its own, called twice *)
Definition hbig (a : i63) : i63 := (PrimInt63.add (PrimInt63.mul (PrimInt63.add (PrimInt63.mul (PrimInt63.add (PrimInt63.mul (PrimInt63.add (PrimInt63.mul (PrimInt63.add (PrimInt63.mul (PrimInt63.add (PrimInt63.mul (PrimInt63.add (PrimInt63.mul (PrimInt63.add (PrimInt63.mul a 3) 1) a) 1) a) 4) a) 1) a) 5) a) 9) a) 2) a) 6).
Definition hbig2 (a : i63) : i63 := PrimInt63.add (hbig a) (hbig (PrimInt63.add a 1)).
Definition hbig_src := ltac:(run_template_program (tmQuoteRec hbig2)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd (fst (fst x))) hbig_src = ["hbig"%bs; "hbig2"%bs]).
Definition hbig_Pr := mkprog (funs_of 0 hbig_src) [].
Time Lemma hbig_ok_r : callee_ok hbig_Pr (gid1 0) (cbz 0) (sig_at hbig_src 0) hbig.
Proof. Time exact_no_check (compile_f_ok hbig_Pr [] gid1 0 (sig_at hbig_src 0) (body_at hbig_src 0) eq_refl eq_refl (no_callees hbig_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma hbig2_ok_r : callee_ok hbig_Pr (gid1 1) (cbz 1) (sig_at hbig_src 1) hbig2.
Proof.
  Time exact_no_check (compile_f_ok hbig_Pr [existT ftype (sig_at hbig_src 0) hbig] gid1 1 (sig_at hbig_src 1) (body_at hbig_src 1)
    eq_refl eq_refl (all_ok_callees hbig_Pr gid1 [existT ftype (sig_at hbig_src 0) hbig] (conj hbig_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.

(* a helper given functions -- a lambda, a partial application -- written out, and the functions applied there written out
   in turn (the translator's beta through lets); and a test on a helper giving back a boolean that starts with lets: the lets
   first, then the test *)
Definition htw (f : i63 -> i63) (x : i63) : i63 := f (f x).
Definition hho (a : i63) : i63 := PrimInt63.add (htw (fun z => PrimInt63.sub z 1) a) (htw (PrimInt63.mul 3) a).
Definition hho_b := FPlain (SOp Badd (SLet (SOp Bsub (SVar 0) (SInt 1)) (SOp Bsub (SVar 0) (SInt 1)))
                                     (SOp Bmul (SInt 3) (SOp Bmul (SInt 3) (SVar 0)))).
Definition hho_src := ltac:(run_template_program (tmQuoteRec hho)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) hho_src = [hho_b]).
Definition hho_Pr := mkprog (funs_of 0 hho_src) [].
Time Lemma hho_ok_r : callee_ok hho_Pr (gid1 0) (cbz 0) (sig_at hho_src 0) hho.
Proof. Time exact_no_check (compile_f_ok hho_Pr [] gid1 0 (sig_at hho_src 0) (body_at hho_src 0) eq_refl eq_refl (no_callees hho_Pr gid1) eq_refl eq_refl). Time Qed.
Definition hok (a : i63) (s : mem) : bool :=
  let t := PrimInt63.mul a 2 in let u := KQ.KQRun.rd 0 a s in andb (PrimInt63.ltb t 10) (PrimInt63.ltb u t).
Definition hlt (a b : i63) (s : mem) : i63 := if andb (hok a s) (PrimInt63.ltb b a) then a else PrimInt63.add b 1.
Definition hlt_b := FPlain (SLet (SOp Bmul (SVar 1) (SInt 2)) (SLet (SRd (SInt 0) (SVar 2))
  (SIfB (BAnd (BAnd (BCmp Clt (SVar 1) (SInt 10)) (BCmp Clt (SVar 0) (SVar 1))) (BCmp Clt (SVar 2) (SVar 3)))
        (SVar 3) (SOp Badd (SVar 2) (SInt 1))))).
Definition hlt_src := ltac:(run_template_program (tmQuoteRec hlt)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) hlt_src = [hlt_b]).
Definition hlt_Pr := mkprog (funs_of 0 hlt_src) [].
Time Lemma hlt_ok_r : callee_ok hlt_Pr (gid1 0) (cbz 0) (sig_at hlt_src 0) hlt.
Proof. Time exact_no_check (compile_f_ok hlt_Pr [] gid1 0 (sig_at hlt_src 0) (body_at hlt_src 0) eq_refl eq_refl (no_callees hlt_Pr gid1) eq_refl eq_refl). Time Qed.

(* a byte ([rd8]) is left for one byte access, as the translator makes it, not shifts of a 4-byte cell: not read yet *)
Definition hb8 (i : i63) (s : mem) : i63 := KQ.KQRun.rd8 1 i s.
Definition hb8_src := ltac:(run_template_program (tmQuoteRec hb8)
  (fun q => let r := eval vm_compute in (reify_prog q) in exact r)).
Check (eq_refl : hb8_src = None).
Eval vm_compute in ltac:(run_template_program (tmQuoteRec hb8) (fun q => let r := eval vm_compute in (reify_why q) in exact r)).

(* ---------------------------------------------------------------- a let of a counter, from the user's text *)
(* a counter written as a number and a budget bound by lets in a memory function, a counter variable bound in a number
   function, a counter let in a number made after memories; a let of [S n] (above the function's bound) refused *)
Fixpoint lc_fill (n : nat) (k : i63) (s : mem) : mem :=
  match n with O => s | S m => lc_fill m (PrimInt63.add k 1) (KQ.KQRun.upd 0 k k s) end.
Definition lc (n : nat) (a : i63) (s : mem) : mem := let w := 3%nat in let v := KQ.KQRun.kq_nat a in lc_fill w a (lc_fill v 1 s).
Definition lc_b := FPlainM (MLetC (CS (CS (CS CO))) (MLetC (CNat (SVar 0))
  (MCall 0 (CCons (CVar 1) CNil) (SCons (SVar 0) SNil) (MCall 0 (CCons (CVar 0) CNil) (SCons (SInt 1) SNil) MCur)))).
Definition lc_src := ltac:(run_template_program (tmQuoteRec lc)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : (length lc_src, body_at lc_src 1) = (2%nat, lc_b)).
Definition lc_Pr := mkprog (funs_of 0 lc_src) [].
Time Lemma lc_fill_ok : callee_ok lc_Pr (gid1 0) (cbz 0) (sig_at lc_src 0) lc_fill.
Proof. Time exact_no_check (compile_f_ok lc_Pr [] gid1 0 (sig_at lc_src 0) (body_at lc_src 0) eq_refl eq_refl (no_callees lc_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma lc_ok : callee_ok lc_Pr (gid1 1) (cbz 1) (sig_at lc_src 1) lc.
Proof.
  Time exact_no_check (compile_f_ok lc_Pr [existT ftype (sig_at lc_src 0) lc_fill] gid1 1 (sig_at lc_src 1) (body_at lc_src 1)
    eq_refl eq_refl (all_ok_callees lc_Pr gid1 [existT ftype (sig_at lc_src 0) lc_fill] (conj lc_fill_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Definition lcn (n : nat) (a : i63) : i63 := let w := n in c_inner w a.
Definition lcn_src := ltac:(run_template_program (tmQuoteRec lcn)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : body_at lcn_src 1 = FPlain (SLetC (CVar 0) (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil)))).
Definition lcx (a : i63) (s : mem) : i63 := let w := 2%nat in let s2 := lc_fill w a s in KQ.KQRun.rd 0 a s2.
Definition lcx_src := ltac:(run_template_program (tmQuoteRec lcx)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : body_at lcx_src 1 = FPlainX (XLetC (CS (CS CO)) (XLetM (MCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil) MCur) (XRet (SRd (SInt 0) (SVar 0)))))).
Definition lcx_Pr := mkprog (funs_of 0 lcx_src) [].
Time Lemma lc_fill_okx : callee_ok lcx_Pr (gid1 0) (cbz 0) (sig_at lcx_src 0) lc_fill.
Proof. Time exact_no_check (compile_f_ok lcx_Pr [] gid1 0 (sig_at lcx_src 0) (body_at lcx_src 0) eq_refl eq_refl (no_callees lcx_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma lcx_ok : callee_ok lcx_Pr (gid1 1) (cbz 1) (sig_at lcx_src 1) lcx.
Proof.
  Time exact_no_check (compile_f_ok lcx_Pr [existT ftype (sig_at lcx_src 0) lc_fill] gid1 1 (sig_at lcx_src 1) (body_at lcx_src 1)
    eq_refl eq_refl (all_ok_callees lcx_Pr gid1 [existT ftype (sig_at lcx_src 0) lc_fill] (conj lc_fill_okx Logic.I)) eq_refl eq_refl).
Time Qed.
Definition lcbad (n : nat) (a : i63) : i63 := let w := S n in c_inner w a.
Definition lcbad_src := ltac:(run_template_program (tmQuoteRec lcbad)
  (fun q => let r := eval vm_compute in (reify_prog q) in exact r)).
Check (eq_refl : lcbad_src = None).

(* ---------------------------------------------------------------- a chain of tests whose every end is a call of the function itself *)
(* one call, the arguments chosen by conditional moves along the tests and the cells written once with the values chosen
   (the translator's merge, §1.5): the KQL's only jump is the counter's test *)
Fixpoint mrow (n : nat) (b x p : i63) (s : mem) : mem :=
  match n with
  | O => s
  | S m => let cur := KQ.KQRun.rd 0 b s in
           if PrimInt63.eqb (PrimInt63.land x 1) 0 then mrow m (PrimInt63.sub b 1) x p (KQ.KQRun.upd 1 b p (KQ.KQRun.upd 0 b cur s))
           else if PrimInt63.eqb cur 0 then mrow m (PrimInt63.sub b 1) 0 p (KQ.KQRun.upd 1 b x (KQ.KQRun.upd 0 b x s))
           else mrow m (PrimInt63.sub b 1) (PrimInt63.lxor x cur) p (KQ.KQRun.upd 1 b cur (KQ.KQRun.upd 0 b p s))
  end.
Fixpoint mqry (n : nat) (b l res : i63) (s : mem) : i63 :=
  match n with
  | O => res
  | S m => let cur := KQ.KQRun.rd 0 b s in
           if andb (PrimInt63.leb l (KQ.KQRun.rd 1 b s)) (PrimInt63.ltb res (PrimInt63.lxor res cur))
           then mqry m (PrimInt63.sub b 1) l (PrimInt63.lxor res cur) s else mqry m (PrimInt63.sub b 1) l res s
  end.
Fixpoint sel_if (e : exp) : nat * nat :=
  match e with
  | Esel _ _ _ _ _ _ k => let '(a, b) := sel_if k in (S a, b)
  | Eop _ _ _ _ k | Ecall _ _ _ k | Ekld _ _ _ k | Ekst _ _ _ k => sel_if k
  | Eif _ _ _ t e => let '(a, b) := sel_if t in let '(c, d) := sel_if e in (a + c, S (b + d))
  | _ => (0, 0)
  end%nat.
Definition mrow_src := ltac:(run_template_program (tmQuoteRec mrow)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition mrow_Pr := mkprog (funs_of 0 mrow_src) [].
Check (eq_refl : snd (sel_if (kbody (compile_f gid1 0 (sig_at mrow_src 0) (body_at mrow_src 0)))) = 1%nat).
Eval vm_compute in sel_if (kbody (compile_f gid1 0 (sig_at mrow_src 0) (body_at mrow_src 0))).
Time Lemma mrow_ok : callee_ok mrow_Pr (gid1 0) (cbz 0) (sig_at mrow_src 0) mrow.
Proof. Time exact_no_check (compile_f_ok mrow_Pr [] gid1 0 (sig_at mrow_src 0) (body_at mrow_src 0) eq_refl eq_refl (no_callees mrow_Pr gid1) eq_refl eq_refl). Time Qed.
Definition mqry_src := ltac:(run_template_program (tmQuoteRec mqry)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition mqry_Pr := mkprog (funs_of 0 mqry_src) [].
Check (eq_refl : snd (sel_if (kbody (compile_f gid1 0 (sig_at mqry_src 0) (body_at mqry_src 0)))) = 1%nat).
Eval vm_compute in sel_if (kbody (compile_f gid1 0 (sig_at mqry_src 0) (body_at mqry_src 0))).
Time Lemma mqry_ok : callee_ok mqry_Pr (gid1 0) (cbz 0) (sig_at mqry_src 0) mqry.
Proof. Time exact_no_check (compile_f_ok mqry_Pr [] gid1 0 (sig_at mqry_src 0) (body_at mqry_src 0) eq_refl eq_refl (no_callees mqry_Pr gid1) eq_refl eq_refl). Time Qed.
Print Assumptions mrow_ok.

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
