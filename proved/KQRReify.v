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
Require KQ.KQRun KQ.hw.Runtime KQ.hw.User.
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
Definition ind_u64 := ind_of <% KQ.KQRun.u64 %>.
Definition ind_w64op := ind_of <% KQ.KQRun.w64op %>.
(** a 64-bit operation (step 16), by its constructor's number *)
Definition w64_of (t : term) : option KQ.KQRun.w64op :=
  match t with
  | tConstruct i k _ =>
      if Kername.eqb (inductive_mind i) (inductive_mind ind_w64op)
      then nth_error [KQ.KQRun.W_add; KQ.KQRun.W_sub; KQ.KQRun.W_mul; KQ.KQRun.W_and; KQ.KQRun.W_or; KQ.KQRun.W_xor;
                      KQ.KQRun.W_shl; KQ.KQRun.W_shr; KQ.KQRun.W_ltu; KQ.KQRun.W_leu; KQ.KQRun.W_eq] k
      else None
  | _ => None
  end.
Definition kit_mp : modpath := fst kn_rd.
Definition kn_ksize := kn_of <% KQ.KQRun.kq_size %>.
(** the machine's operations (step 14), as the translator's tables: the Rocq constant, the KQL operation, how many numbers it
    takes before the memory *)
Definition hw_table : list (kername * hwop * nat) :=
  [ (kn_of <% KQ.KQRun.hw_load %>, HLoad, 4); (kn_of <% KQ.KQRun.hw_store %>, HStore, 3);
    (kn_of <% KQ.KQRun.hw_store64 %>, HStore64, 3); (kn_of <% KQ.KQRun.hw_atomic %>, HAtomic, 6);
    (kn_of <% KQ.KQRun.hw_atomic64 %>, HAtomic64, 6); (kn_of <% KQ.KQRun.hw_cas %>, HCas, 6);
    (kn_of <% KQ.KQRun.hw_cas64 %>, HCas64, 7); (kn_of <% KQ.KQRun.hw_aload %>, HALoad, 4);
    (kn_of <% KQ.KQRun.hw_astore %>, HAStore, 3); (kn_of <% KQ.KQRun.hw_astore64 %>, HAStore64, 3);
    (kn_of <% KQ.KQRun.hw_fence %>, HFence, 1); (kn_of <% KQ.KQRun.hw_copy %>, HCopy, 3);
    (kn_of <% KQ.KQRun.hw_fill %>, HFill, 3); (kn_of <% KQ.KQRun.hw_cmp %>, HCmp, 5);
    (kn_of <% KQ.KQRun.hw_call %>, HCall, 4); (kn_of <% KQ.KQRun.hw_run %>, HRun, 10);
    (kn_of <% KQ.KQRun.hw_code_sync %>, HCodeSync, 2); (kn_of <% KQ.hw.Runtime.hw_irq_take %>, HIrqTake, 2);
    (kn_of <% KQ.hw.User.hw_user %>, HUser, 5); (kn_of <% KQ.KQRun.kq_grow %>, HGrow, 2) ].
(** the machine's numbers, given without a memory *)
Definition hwf_table : list (kername * hwfop * nat) :=
  [ (kn_of <% KQ.KQRun.hw_addr %>, FAddr, 1); (kn_of <% KQ.hw.Runtime.hw_irq_info %>, FIrqInfo, 1);
    (kn_of <% KQ.hw.Runtime.hw_irq_entry %>, FIrqEntry, 1); (kn_of <% KQ.hw.Runtime.hw_cpu_code %>, FCpuCode, 1);
    (kn_of <% KQ.hw.Runtime.hw_sym %>, FSym, 1); (kn_of <% KQ.hw.User.hw_userf %>, FUser, 5) ].
Definition hw_lookup (kn : kername) : option (hwop * nat) :=
  option_map (fun e => (snd (fst e), snd e)) (List.find (fun e => Kername.eqb (fst (fst e)) kn) hw_table).
Definition hwf_lookup (kn : kername) : option (hwfop * nat) :=
  option_map (fun e => (snd (fst e), snd e)) (List.find (fun e => Kername.eqb (fst (fst e)) kn) hwf_table).
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
Inductive cent := CNum | CMem | CDead | CCnt | CPred | CSelf | CBool | CFn (p : nat) (t : term) | CRec | CSib (j : nat).
(* CFn p t: the function parameter number p of a template's copy, bound to the function t given (its captured variables
   numbered 0 .. in the order they first appear: the context's entries after the copy's own, CSelf, step 13).  CSib j: member
   j of a mutual block (step 17) *)

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

(** the syntax index of the record at place [i] of the context: the records nearer than it *)
Fixpoint rec_index (ctx : list cent) (i : nat) : option nat :=
  match ctx, i with
  | CRec :: _, O => Some O
  | _ :: _, O => None
  | c :: r, S i => option_map (fun j => match c with CRec => S j | _ => j end) (rec_index r i)
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
Fixpoint to_args (l : list (option (sexp + (sbool + srec)))) : option sexps :=
  match l with
  | [] => Some SNil
  | Some (inl e) :: r => option_map (SCons e) (to_args r)
  | Some (inr (inl b)) :: r => option_map (SConsB b) (to_args r)
  | Some (inr (inr x)) :: r => option_map (SConsR x) (to_args r)
  | None :: _ => None
  end.
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

(** captures (step 13): the variables of the caller a function given names, in the order they first appear *)
Fixpoint fvs (fuel : nat) (d : nat) (t : term) (acc : list nat) : list nat :=
  match fuel with
  | O => acc
  | S fuel =>
      match t with
      | tRel i => if Nat.leb d i then (if existsb (Nat.eqb (i - d)) acc then acc else acc ++ [i - d]) else acc
      | tApp f args => fold_left (fun a x => fvs fuel d x a) args (fvs fuel d f acc)
      | tLambda _ ty b | tProd _ ty b => fvs fuel (S d) b (fvs fuel d ty acc)
      | tLetIn _ b ty body => fvs fuel (S d) body (fvs fuel d ty (fvs fuel d b acc))
      | tCase _ p c brs =>
          let acc := fold_left (fun a x => fvs fuel d x a) (pparams p) acc in
          let acc := fvs fuel (d + length (pcontext p)) (preturn p) acc in
          fold_left (fun a br => fvs fuel (d + length (bcontext br)) (bbody br) a) brs (fvs fuel d c acc)
      | tFix mfix _ => fold_left (fun a df => fvs fuel (d + length mfix) (dbody df) (fvs fuel d (dtype df) a)) mfix acc
      | tProj _ c => fvs fuel d c acc
      | tCast c _ ty => fvs fuel d ty (fvs fuel d c acc)
      | _ => acc
      end
  end.
Fixpoint idx_of (r : nat) (l : list nat) (i : nat) : option nat :=
  match l with [] => None | x :: l => if Nat.eqb x r then Some i else idx_of r l (S i) end.
(** a function given with its captured variables renumbered 0 .. in the order they first appear *)
Definition abs_caps (fv : list nat) (f : term) : term :=
  match fv with
  | [] => f
  | _ => subst (map (fun r => match idx_of r fv 0 with Some k => tRel k | None => tRel 0 end) (seq 0 (S (fold_left Nat.max fv 0)))) 0 f
  end.
Definition is_memc (c : cent) : bool := match c with CMem | CDead => true | _ => false end.
Definition cap_ok (c : cent) : bool := match c with CNum | CBool | CMem => true | _ => false end.
Definition capk_eqb (a b : list cent) : bool :=
  Nat.eqb (length a) (length b)
  && forallb (fun q => match q with (CNum, CNum) | (CBool, CBool) | (CMem, CMem) => true | _ => false end) (combine a b).
(** a copy's captured variables: the entries of its context after CSelf, the first captured the deepest *)
Fixpoint after_self (ctx : list cent) : list cent := match ctx with [] => [] | CSelf :: r => r | _ :: r => after_self r end.
(** a function given, written out in a copy's context: its captured variables are the copy's entries for them *)
Definition capsub (ctx : list cent) (t : term) : term :=
  match after_self ctx with
  | [] => t
  | cs => subst (map (fun k => tRel (length ctx - 1 - k)) (seq 0 (length cs))) 0 t
  end.

(** the recursive call of a template's copy passes its function parameters on unchanged: they are dropped ([fd]: for each
    argument after the first counter, the function parameter it must be, or none) *)
Fixpoint drop_fns (ctx : list cent) (fd : list (option nat)) (l : list term) : option (list term) :=
  match fd, l with
  | [], _ => Some l
  | _, [] => Some []
  | Some p :: fd', a :: l' =>
      match a with
      | tRel j => match nth_error ctx j with Some (CFn p' _) => if Nat.eqb p p' then drop_fns ctx fd' l' else None | _ => None end
      | _ => None
      end
  | None :: fd', a :: l' => option_map (cons a) (drop_fns ctx fd' l')
  end.

Fixpoint teq (fuel : nat) (t u : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t, u with
      | tRel i, tRel j => Nat.eqb i j
      | tInt a, tInt b => PrimInt63.eqb a b
      | tConst k _, tConst k' _ => Kername.eqb k k'
      | tInd i _, tInd i' _ => Kername.eqb (inductive_mind i) (inductive_mind i') && Nat.eqb (inductive_ind i) (inductive_ind i')
      | tConstruct i n _, tConstruct i' n' _ =>
          Kername.eqb (inductive_mind i) (inductive_mind i') && Nat.eqb (inductive_ind i) (inductive_ind i') && Nat.eqb n n'
      | tApp f l, tApp f' l' =>
          teq fuel f f' && Nat.eqb (length l) (length l') && forallb (fun q => teq fuel (fst q) (snd q)) (combine l l')
      | tLambda _ a b, tLambda _ a' b' | tProd _ a b, tProd _ a' b' => teq fuel a a' && teq fuel b b'
      | tLetIn _ a ty b, tLetIn _ a' ty' b' => teq fuel a a' && teq fuel ty ty' && teq fuel b b'
      | tCase _ _ c brs, tCase _ _ c' brs' =>
          teq fuel c c' && Nat.eqb (length brs) (length brs') && forallb (fun q => teq fuel (bbody (fst q)) (bbody (snd q))) (combine brs brs')
      | tSort _, tSort _ => true
      | _, _ => false
      end
  end.
Definition teqs (l l' : list term) : bool :=
  Nat.eqb (length l) (length l') && forallb (fun q => teq 1000 (fst q) (snd q)) (combine l l').


(** a record type of numbers (§12.V step 12): an inductive with one constructor, whose fields are numbers or parameters that
    are numbers ([prod int int]); an entry of the program's record table: its type, its inductive, its number of fields, its
    parameters *)
Definition rentry := (term * inductive * nat * list term)%type.
Definition rec_shape (Σ : global_env) (t : term) : option rentry :=
  let '(h, ps) := match t with tApp (tInd i _) ps => (Some i, ps) | tInd i _ => (Some i, []) | _ => (None, []) end in
  match h with
  | Some i =>
      match lookup_env Σ (inductive_mind i) with
      | Some (InductiveDecl mib) =>
          match ind_bodies mib with
          | [oib] =>
              match ind_ctors oib with
              | [cb] =>
                  let args := rev (cstr_args cb) in
                  let fok := forallb (fun jd => is_ty kn_int (decl_type (snd jd))
                                                || match decl_type (snd jd) with tRel k => Nat.leb (fst jd) k | _ => false end)
                                     (combine (seq 0 (length args)) args) in
                  if Nat.eqb (length ps) (ind_npars mib) && forallb (is_ty kn_int) ps && Nat.eqb (inductive_ind i) 0 && fok
                  then Some (t, i, length args, ps) else None
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.
(** the index of a record type in the table, and of the record a constructor applied to these arguments builds (with its
    number of parameters) *)
Fixpoint rindex (t : term) (rt : list rentry) (i : nat) : option nat :=
  match rt with [] => None | (u, _, _, _) :: r => if teq 1000 t u then Some i else rindex t r (S i) end.
Fixpoint cindex (ind : inductive) (args : list term) (rt : list rentry) (i : nat) : option (nat * nat) :=
  match rt with
  | [] => None
  | (_, j, n, qs) :: r =>
      if Kername.eqb (inductive_mind ind) (inductive_mind j) && Nat.eqb (inductive_ind ind) (inductive_ind j)
         && Nat.eqb (length args) (length qs + n) && teqs (firstn (length qs) args) qs
      then Some (i, length qs) else cindex ind args r (S i)
  end.

(** the index and number of fields of a record type without parameters, by its inductive (a primitive projection names it) *)
Fixpoint rind (ind : inductive) (rt : list rentry) (i : nat) : option (nat * nat) :=
  match rt with
  | [] => None
  | (_, j, n, qs) :: r =>
      if Kername.eqb (inductive_mind ind) (inductive_mind j) && Nat.eqb (inductive_ind ind) (inductive_ind j) && Nat.eqb (length qs) 0
      then Some (i, n) else rind ind r (S i)
  end.

Section R.
Variable callees : list (kername * sig).   (* the program's functions read so far, callees first *)
Variable fm : bool.                        (* the function being read takes a memory *)
Variable fnx : nat.                        (* its counters after the first: the recursive call is given these after the
                                              predecessor *)
Variable hb : kername -> option term.      (* the helpers: a definition written out where it is used, and its body *)
Variable tc : kername -> list term -> option (kername * list term).
                                           (* a call of a template given functions: its copy and the other arguments *)
Variable fd : list (option nat).           (* the function parameters the recursive call passes on (a copy) *)
Variable rt : list rentry.                 (* the program's record types *)

(** the recursive call of a copy with captures passes them on: the captured numbers and booleans after its counters, the
    captured memory last *)
Definition with_caps (ctx : list cent) (rest : list term) : list term :=
  match after_self ctx with
  | [] => rest
  | cs0 =>
      let L := length ctx in
      let cs := combine (rev cs0) (map (fun k => tRel (L - 1 - k)) (seq 0 (length cs0))) in
      firstn fnx rest ++ map snd (filter (fun p => negb (is_memc (fst p))) cs) ++ skipn fnx rest
      ++ map snd (filter (fun p => is_memc (fst p)) cs)
  end.

Definition tcall (kn : kername) (args : list term) : kername * list term :=
  match tc kn args with Some p => p | None => (kn, args) end.

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
  let reify_args (l : list term) : option sexps :=
    to_args (map (fun a => match reify fuel ctx a with Some e => Some (inl e) | None =>
                            match reify_b fuel ctx a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel ctx a) end end) l) in
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
      else if Kername.eqb kn kn_ksize then
        match args with
        | [h; tRel m] => if is_ent CMem ctx m then option_map SSize (reify fuel ctx h) else None
        | _ => None
        end
      else if match hwf_lookup kn with Some _ => true | None => false end then
        match hwf_lookup kn with
        | Some (o, n) => if Nat.eqb (length args) n then option_map (fun l => SHwf o (to_sexps l)) (opt_all (map (reify fuel ctx) args)) else None
        | None => None
        end
      else if Kername.eqb kn kn_rd || Kername.eqb kn kn_rd32 || Kername.eqb kn kn_rd8 then
        match args with
        | [h; i; tRel m] =>
            if is_ent CMem ctx m then
              match reify fuel ctx h, reify fuel ctx i with
              | Some x, Some y => Some (if Kername.eqb kn kn_rd then SRd x y else if Kername.eqb kn kn_rd32 then SRd32 x y else SRd8 x y)
              | _, _ => None
              end
            else None
        | _ => None
        end
      else
        let '(kn1, args1) := tcall kn args in
        match find_callee kn1 callees 0 with
        | Some (f, gs) =>
            let args := args1 in
            if sr gs || sw gs || isq gs || negb (Nat.leb (sn gs) (length args)) then None else
            match reify_cs (firstn (sn gs) args), read_mem ctx (sm gs) (skipn (sn gs) args) with
            | Some cs, Some nums => option_map (SCall f cs) (reify_args nums)
            | _, _ => None
            end
        | None => match hb kn with Some b => reify fuel ctx (wout b args) | None => None end
        end
  | tApp (tRel fi) args0 =>
      match nth_error ctx fi, args0 with
      | Some (CFn _ t), _ => reify fuel ctx (wout (capsub ctx t) args0)
      (* member j of a mutual block on the predecessor: the block function itself, given the selector j last *)
      | Some (CSib j), tRel mi :: rest =>
          if is_ent CPred ctx mi && Nat.leb (Nat.pred fnx) (length rest) then
            match opt_all (map (reify_c fuel ctx) (firstn (Nat.pred fnx) rest)), read_mem ctx fm (skipn (Nat.pred fnx) rest) with
            | Some cs, Some nums => option_map (SRec (to_scnts (cs ++ [CNat (SInt (Uint63.of_Z (Z.of_nat j)))]))) (reify_args nums)
            | _, _ => None
            end
          else None
      | _, tRel mi :: rest0 =>
          match option_map (with_caps ctx) (drop_fns ctx fd rest0) with
          | Some rest =>
              if is_ent CSelf ctx fi && is_ent CPred ctx mi && Nat.leb fnx (length rest) then
                match reify_cs (firstn fnx rest), read_mem ctx fm (skipn fnx rest) with
                | Some cs, Some nums => option_map (SRec cs) (reify_args nums)
                | _, _ => None
                end
              else None
          | None => None
          end
      | _, _ => None
      end
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
      else match reify_r fuel ctx b, reify fuel (CRec :: ctx) body with Some x, Some y => Some (SLetR x y) | _, _ => None end
  | tCase ci p c0 [br] =>
      (* a record taken apart; a helper giving one back is written out first, and the lets it starts with come first *)
      let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
      match lets_first ci p c [br] with Some t' => reify fuel ctx t' | None =>
        match reify_r fuel ctx c, reify fuel (repeat CNum (length (bcontext br)) ++ ctx) (bbody br) with
        | Some x, Some e => Some (SMatchR x e)
        | _, _ => None
        end
      end
  (* a field of a record of the program's types with primitive projections ([w_lo r]): of a record variable, or of a record
     taken apart (its fields the nearest numbers, the last one first) *)
  | tProj p c =>
      match c with
      | tRel i => option_map (fun r => SFld r (proj_arg p)) (rec_index ctx i)
      | _ => match rind (proj_ind p) rt 0, reify_r fuel ctx c with
             | Some (_, n), Some x => Some (SMatchR x (SVar (n - 1 - proj_arg p)))
             | _, _ => None
             end
      end
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
  | tApp (tRel i) args => match nth_error ctx i with Some (CFn _ t) => reify_c fuel ctx (wout (capsub ctx t) args) | _ => None end
  | tApp (tConst kn _) args =>
      if Kername.eqb kn kn_kq_nat then match args with [e] => option_map CNat (reify fuel ctx e) | _ => None end
      else match hb kn with Some b => reify_c fuel ctx (wout b args) | None => None end
  | _ => None
  end
  end
(** a record: a record variable, the constructor of a record type applied to numbers, or a call of a function giving back
    a record (a helper written out) *)
with reify_r (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option srec :=
  match fuel with
  | O => None
  | S fuel =>
      let reify_args (l : list term) : option sexps :=
        to_args (map (fun a => match reify fuel ctx a with Some e => Some (inl e) | None =>
                                match reify_b fuel ctx a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel ctx a) end end) l) in
      match t with
      | tRel i => option_map RVar (rec_index ctx i)
      | tApp (tConstruct ind 0 _) args =>
          match cindex ind args rt 0 with
          | Some (ri, np) => option_map (fun es => RMk ri (to_sexps es)) (opt_all (map (reify fuel ctx) (skipn np args)))
          | None => None
          end
      | tConst kn _ => match hb kn with Some b => reify_r fuel ctx b | None => None end
      | tApp (tLambda _ _ _ as f) args => reify_r fuel ctx (wout f args)
      (* a record under lets: a helper giving a record written out, its arguments bound (step 16) *)
      | tLetIn _ b ty body =>
          if is_ty kn_int ty then
            match reify fuel ctx b, reify_r fuel (CNum :: ctx) body with Some e, Some x => Some (RLet e x) | _, _ => None end
          else if is_bool ty || is_nat ty || is_ty kn_mem ty then None
          else match reify_r fuel ctx b, reify_r fuel (CRec :: ctx) body with Some y, Some x => Some (RLetR y x) | _, _ => None end
      | tApp (tConst kn _) args =>
          (* a 64-bit operation: [u64] a record type of the program *)
          if Kername.eqb kn kn_w64_op then
            match args with
            | [o; a; b] =>
                match w64_of o, rind ind_u64 rt 0, reify_r fuel ctx a, reify_r fuel ctx b with
                | Some op, Some (ri, _), Some x, Some y => Some (RW64 ri op x y)
                | _, _, _, _ => None
                end
            | _ => None
            end
          else
          let '(kn1, args1) := tcall kn args in
          match find_callee kn1 callees 0 with
          | Some (f, gs) =>
              match sq gs with
              | Some ri =>
                  if sr gs || sw gs || negb (Nat.leb (sn gs) (length args1)) then None else
                  match opt_all (map (reify_c fuel ctx) (firstn (sn gs) args1)), read_mem ctx (sm gs) (skipn (sn gs) args1) with
                  | Some cs, Some nums => option_map (RCall ri f (to_scnts cs)) (reify_args nums)
                  | _, _ => None
                  end
              | None => None
              end
          | None => match hb kn with Some b => reify_r fuel ctx (wout b args) | None => None end
          end
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
  | tApp (tRel i) args => match nth_error ctx i with Some (CFn _ t) => reify_b fuel ctx (wout (capsub ctx t) args) | _ => None end
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
  let reify_args (l : list term) : option sexps :=
    to_args (map (fun a => match reify fuel ctx a with Some e => Some (inl e) | None =>
                            match reify_b fuel ctx a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel ctx a) end end) l) in
  let reify_cs (l : list term) : option scnts := option_map to_scnts (opt_all (map (reify_c fuel ctx) l)) in
  match t with
  | tRel i => if is_ent CMem ctx i then Some MCur else None
  | tConst kn _ => match hb kn with Some b => reify_m fuel ctx b | None => None end
  | tApp (tConst kn _) args =>
      if Kername.eqb kn kn_upd || Kername.eqb kn kn_upd32 || Kername.eqb kn kn_upd8 then
        match args with
        | [h; i; v; m] =>
            match reify fuel ctx h, reify fuel ctx i, reify fuel ctx v, reify_m fuel ctx m with
            | Some a, Some b, Some c, Some d => Some (if Kername.eqb kn kn_upd then MUpd a b c d else if Kername.eqb kn kn_upd32 then MUpd32 a b c d else MUpd8 a b c d)
            | _, _, _, _ => None
            end
        | _ => None
        end
      else if match hw_lookup kn with Some _ => true | None => false end then
        match hw_lookup kn, rev args with
        | Some (o, n), m :: rnums =>
            if Nat.eqb (length rnums) n then
              match opt_all (map (reify fuel ctx) (rev rnums)), reify_m fuel ctx m with
              | Some l, Some d => Some (MHw o (to_sexps l) d)
              | _, _ => None
              end
            else None
        | _, _ => None
        end
      else
        let '(kn1, args1) := tcall kn args in
        match find_callee kn1 callees 0 with
        | Some (f, gs) =>
            let args := args1 in
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
  | tApp (tRel fi) args0 =>
      match nth_error ctx fi, args0 with
      | Some (CFn _ t), _ => reify_m fuel ctx (wout (capsub ctx t) args0)
      | _, tRel mi :: rest0 =>
          match option_map (with_caps ctx) (drop_fns ctx fd rest0) with
          | Some rest =>
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
          | None => None
          end
      | _, _ => None
      end
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
      else match reify_r fuel ctx b, reify_m fuel (CRec :: ctx) body with Some x, Some y => Some (MLetR x y) | _, _ => None end
  | tCase ci p c0 [br] =>
      (* a record taken apart *)
      let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
      match reify_r fuel ctx c, reify_m fuel (repeat CNum (length (bcontext br)) ++ ctx) (bbody br) with
      | Some x, Some m => Some (MMatchR x m)
      | _, _ => None
      end
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
  let reify_args (c : list cent) (l : list term) : option sexps :=
    to_args (map (fun a => match reify fuel c a with Some e => Some (inl e) | None =>
                            match reify_b fuel c a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel c a) end end) l) in
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
      else match reify_r fuel ctx b, reify_x fuel (CRec :: ctx) body with Some r, Some x => Some (XLetR r x) | _, _ => None end
  | tCase ci p c0 [br] =>
      (* a record taken apart, the number after it made after memories; or a number *)
      let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
      match reify_r fuel ctx c, reify_x fuel (repeat CNum (length (bcontext br)) ++ ctx) (bbody br) with
      | Some r, Some x => Some (XMatchR r x)
      | _, _ => fallback
      end
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
        let '(kn1, args1) := tcall kn args in
        match find_callee kn1 callees 0, rev args1 with
        | Some (f, gs), m :: rnums =>
            if negb (sr gs) && negb (sw gs) && sm gs && negb (is_rel m) && Nat.leb (sn gs) (length (rev rnums)) then
              let rest := rev rnums in
              match reify_m fuel ctx m, reify_cs (kill_mem ctx) (firstn (sn gs) rest), reify_args (kill_mem ctx) (skipn (sn gs) rest) with
              | Some mm, Some cs, Some As => Some (XLetM mm (XRet (SCall f cs As)))
              | _, _, _ => None
              end
            else if negb (sr gs) && sw gs && sm gs && Nat.leb (sn gs) (length (rev rnums)) then
              (* a number function that writes, called at the end: its numbers on the memory before the one it is given *)
              let rest := rev rnums in
              match reify_m fuel ctx m, reify_cs ctx (firstn (sn gs) rest), reify_args ctx (skipn (sn gs) rest) with
              | Some mm, Some cs, Some As => Some (XCall f cs As mm)
              | _, _, _ => None
              end
            else fallback
        | None, _ => match hb kn with Some b => reify_x fuel ctx (wout b args) | None => fallback end
        | _, _ => fallback
        end
  | tConst kn _ => match hb kn with Some b => reify_x fuel ctx b | None => fallback end
  | tApp (tRel fi) args0 =>
      match nth_error ctx fi, args0 with
      | Some (CFn _ t), _ => reify_x fuel ctx (wout (capsub ctx t) args0)
      | _, tRel mi :: rest0 =>
          if is_ent CSelf ctx fi then
            (* the recursive call at the end, given a memory made from the newest one *)
            match option_map (with_caps ctx) (drop_fns ctx fd rest0) with
            | Some rest =>
                if is_ent CPred ctx mi && Nat.leb fnx (length rest) then
                  match rev (skipn fnx rest) with
                  | m :: rnums =>
                      match reify_cs ctx (firstn fnx rest), reify_args ctx (rev rnums), reify_m fuel ctx m with
                      | Some cs, Some As, Some d => Some (XRec cs As d)
                      | _, _, _ => None
                      end
                  | [] => None
                  end
                else None
            | None => None
            end
          else fallback
      | _, _ => fallback
      end
  | _ => fallback
  end
  end.
(** a record given back: at the end a record (built, or given by a call), the function itself at the end, the function itself
    taken apart or bound by a let before the end, and lets, tests and a match on a counter around them *)
Fixpoint reify_br (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sbr :=
  match fuel with
  | O => None
  | S fuel =>
  let reify_args (l : list term) : option sexps :=
    to_args (map (fun a => match reify fuel ctx a with Some e => Some (inl e) | None =>
                            match reify_b fuel ctx a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel ctx a) end end) l) in
  (* the function itself: its counter's predecessor, its counters after the first, its numbers, the memory *)
  let self_call (u : term) : option (scnts * sexps) :=
    match u with
    | tApp (tRel fi) (tRel mi :: rest0) =>
        match option_map (with_caps ctx) (drop_fns ctx fd rest0) with
        | Some rest =>
            if is_ent CSelf ctx fi && is_ent CPred ctx mi && Nat.leb fnx (length rest) then
              match opt_all (map (reify_c fuel ctx) (firstn fnx rest)), read_mem ctx fm (skipn fnx rest) with
              | Some cs, Some nums => option_map (fun a => (to_scnts cs, a)) (reify_args nums)
              | _, _ => None
              end
            else None
        | None => None
        end
    | _ => None
    end in
  match self_call t with
  | Some (cs, a) => Some (BRec cs a)
  | None =>
  match t with
  | tApp (tLambda _ _ _ as f) args => reify_br fuel ctx (wout f args)
  | tApp (tConst kn _) args =>
      match find_callee (fst (tcall kn args)) callees 0, hb kn with
      | None, Some b => reify_br fuel ctx (wout b args)
      | _, _ => option_map BRet (reify_r fuel ctx t)
      end
  | tCase ci p c0 [b0; b1] =>
      let c := if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then bnorm fuel c0 else c0 in
      match lets_first ci p c [b0; b1] with Some t' => reify_br fuel ctx t' | None =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        match (match c with
               | tApp (tConst kn _) [a; b] => if eq_mp (fst kn) prim_mp then option_map (fun x => (x, a, b)) (cmp_v (snd kn)) else None
               | _ => None
               end) with
        | Some (cmp, a, b) =>
            match reify fuel ctx a, reify fuel ctx b, reify_br fuel ctx (bbody b0), reify_br fuel ctx (bbody b1) with
            | Some x, Some y, Some t1, Some t2 => Some (BIf cmp x y t1 t2)
            | _, _, _, _ => None
            end
        | None =>
            match reify_b fuel ctx c, reify_br fuel ctx (bbody b0), reify_br fuel ctx (bbody b1) with
            | Some x, Some t1, Some t2 => Some (BIfB x t1 t2)
            | _, _, _ => None
            end
        end
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel i =>
            match cnt_index ctx i, reify_br fuel ctx (bbody b0), reify_br fuel (CCnt :: ctx) (bbody b1) with
            | Some x, Some e0, Some e1 => Some (BMatch x e0 e1)
            | _, _, _ => None
            end
        | _ => match known_branch c b0 b1 with Some t => reify_br fuel ctx t | None => None end
        end
      else None
      end
  | tCase ci p c0 [br] =>
      (* a record taken apart: the function itself, or a record (a helper giving one back written out first) *)
      let inner := reify_br fuel (repeat CNum (length (bcontext br)) ++ ctx) (bbody br) in
      match self_call c0 with
      | Some (cs, a) => option_map (BMatchRec cs a) inner
      | None =>
          let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
          match lets_first ci p c [br] with Some t' => reify_br fuel ctx t' | None =>
            match reify_r fuel ctx c, inner with Some x, Some e => Some (BMatchR x e) | _, _ => None end
          end
      end
  | tLetIn _ b ty body =>
      if is_ty kn_int ty then
        match reify fuel ctx b, reify_br fuel (CNum :: ctx) body with Some x, Some y => Some (BLet x y) | _, _ => None end
      else if is_bool ty then
        match reify_b fuel ctx b, reify_br fuel (CBool :: ctx) body with Some x, Some y => Some (BLetB x y) | _, _ => None end
      else if is_nat ty then
        match reify_c fuel ctx b, reify_br fuel (CCnt :: ctx) body with Some x, Some y => Some (BLetC x y) | _, _ => None end
      else
        match self_call b with
        | Some (cs, a) => option_map (BLetRec cs a) (reify_br fuel (CRec :: ctx) body)
        | None => match reify_r fuel ctx b, reify_br fuel (CRec :: ctx) body with Some x, Some y => Some (BLetR x y) | _, _ => None end
        end
  | _ => option_map BRet (reify_r fuel ctx t)
  end
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

(** a signature off the parameter types and the result type: counters first, numbers, a memory last or not, a memory, a
    number or a record of the program's types as the result *)
Definition kind_ty (rt : list rentry) (t : term) : option kind :=
  if is_ty kn_int t then Some KNum else if is_bool t then Some KBool else option_map KRec (rindex t rt 0).
Definition read_sig (rt : list rentry) (tys : list term) (ret : term) : option sig :=
  let '(c, rest) := lead_nats tys in
  let m := match rev rest with t :: _ => is_ty kn_mem t | [] => false end in
  let nums := if m then removelast rest else rest in
  let r := is_ty kn_mem ret in
  match opt_all (map (kind_ty rt) nums) with
  | Some ks => if r || is_ty kn_int ret then Some (mksig c ks m r false None)
               else option_map (fun ri => mksig c ks m false false (Some ri)) (rindex ret rt 0)
  | None => None
  end.

Definition cent_of (k : kind) : cent := match k with KNum => CNum | KBool => CBool | KRec _ => CRec end.
Definition fun_ctx (gs : sig) : list cent := (if sm gs then [CMem] else []) ++ rev (map cent_of (sk gs)) ++ repeat CCnt (sn gs).

(** one function of the program, given the ones before it, as its text reads: a recursive function starts with a match
    on its first counter *)
Definition read_fun (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (kn : kername) : option (sig * fbody) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some (tFix [d] 0) =>
          if Nat.eqb (rarg d) 0 then
            let '(tys, body) := lams (dbody d) in
            match read_sig rt tys (ret_ty (dtype d)), body with
            | Some gs, tCase ci _ (tRel cnt) [b0; b1] =>
                let nx := Nat.pred (sn gs) in
                if negb (Nat.eqb (sn gs) 0) && Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat)
                   && Nat.eqb cnt ((if sm gs then 1 else 0) + length (sk gs) + nx) then
                  let ctx := fun_ctx gs ++ [CSelf] in
                  if isq gs then
                    match reify_br callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_br callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                    | Some r0, Some r1 => Some (gs, FRecR r0 r1)
                    | _, _ => None
                    end
                  else if sr gs then
                    match reify_m callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_m callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                    | Some m0, Some m1 => Some (gs, FRecM m0 m1)
                    | _, _ => None
                    end
                  else
                    match reify callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                    | Some e0, Some e1 => Some (gs, FRec e0 e1)
                    | _, _ =>
                        (* a number made after memories in both branches: a loop that writes and gives back a number *)
                        if sm gs then
                          match reify_x callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0),
                                reify_x callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                          | Some x0, Some x1 => Some (mksig (sn gs) (sk gs) true false true None, FRecX x0 x1)
                          | _, _ => None
                          end
                        else None
                    end
                else None
            | _, _ => None
            end
          else None
      | Some b =>
          let '(tys, body) := lams b in
          match read_sig rt tys (ret_ty (cst_type cb)) with
          | Some gs =>
              let nx := Nat.pred (sn gs) in
              if isq gs then option_map (fun r => (gs, FPlainR r)) (reify_br callees (sm gs) nx hb tc [] rt 100000 (fun_ctx gs) body)
              else if sr gs then option_map (fun m => (gs, FPlainM m)) (reify_m callees (sm gs) nx hb tc [] rt 100000 (fun_ctx gs) body)
              else match reify callees (sm gs) nx hb tc [] rt 100000 (fun_ctx gs) body with
                   | Some e => Some (gs, FPlain e)
                   | None => if sm gs then
                               option_map (fun x => (mksig (sn gs) (sk gs) true false true None, FPlainX x))
                                          (reify_x callees (sm gs) nx hb tc [] rt 100000 (fun_ctx gs) body)
                             else None
                   end
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(** record types with these numbers of fields and nothing else: well-formedness reads only a record type's number of fields *)
Definition arity_recs (ars : list nat) : RecTypes :=
  {| RT := fun _ => unit; RO := fun i => mkrops (nth i ars O) (fun _ => tt) (fun P _ k => k []); Rd := fun _ => tt |}.

(** ... kept when it is well formed, the condition of [compile_f_ok]: a program read is a program compiled *)
Definition reify_fun (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (kn : kername) : option (sig * fbody) :=
  match read_fun Σ hb tc rt callees kn with
  | Some (gs, b) => if @wf_f (arity_recs (map (fun e => snd (fst e)) rt)) (map snd callees) gs b then Some (gs, b) else None
  | None => None
  end.

(* ---------------------------------------------------------------- mutual blocks (step 17) *)
(** a mutual block's members (number functions of one signature, numbers and booleans as parameters) are one function with
    one counter more, the selector, last among its counters: its body a match on the selector over the members' bodies (each
    body lifted to make room for the selector, and under one binder more per match on the selector it stands in), a call of
    member [j] on the predecessor the recursive call given the selector [j] *)
Fixpoint nest_sel (c : nat) (es : list sexp) : sexp :=
  match es with [] => SInt 0%uint63 | [e] => e | e :: es' => SMatch c e (nest_sel 0 es') end.
Definition read_block (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (mfix : mfixpoint term) : option (sig * sig * fbody) :=
  match mfix with
  | [] | [_] => None
  | d0 :: _ =>
      let L := length mfix in
      let '(tys, _) := lams (dbody d0) in
      match read_sig rt tys (ret_ty (dtype d0)) with
      | Some gs =>
          if forallb (fun d => Nat.eqb (rarg d) 0 && teq 1000 (dtype d) (dtype d0)) mfix
             && negb (Nat.eqb (sn gs) 0) && negb (sr gs) && negb (isq gs)
             && forallb (fun k => match k with KRec _ => false | _ => true end) (sk gs) then
            let nx := Nat.pred (sn gs) in
            let nv := (if sm gs then 1 else 0) + length (sk gs) in
            let gs' := mksig (S (sn gs)) (sk gs) (sm gs) false false None in
            let ctx := fun_ctx gs' ++ map CSib (rev (seq 0 L)) in
            let brs := map (fun d => match lift 1 nv (snd (lams (dbody d))) with
                                     | tCase ci _ (tRel cnt) [b0; b1] =>
                                         if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) && Nat.eqb cnt (nv + nx + 1)
                                         then Some (bbody b0, bbody b1) else None
                                     | _ => None
                                     end) mfix in
            match opt_all brs with
            | Some bs =>
                let rd (pre : list cent) (j : nat) (t : term) :=
                  reify callees (sm gs) (sn gs) hb tc [] rt 100000 (repeat CCnt j ++ pre) (lift0 j t) in
                let jbs := combine (seq 0 L) bs in
                match opt_all (map (fun jb => rd ctx (fst jb) (fst (snd jb))) jbs),
                      opt_all (map (fun jb => rd (CPred :: ctx) (fst jb) (snd (snd jb))) jbs) with
                | Some e0s, Some e1s => Some (gs, gs', FRec (nest_sel 0 e0s) (nest_sel 1 e1s))
                | _, _ => None
                end
            | None => None
            end
          else None
      | None => None
      end
  end.
(** the block function's meaning: [blk] of the fixpoint's own bodies (a member the program does not name included), with
    the first member's type as the list's (the type [blk] asks, by conversion) *)
Definition ind_kind := ind_of <% KQR.kind %>.
Definition ind_list := ind_of <% list %>.
Definition kn_blk := kn_of <% @KQR.blk %>.
Definition kn_no_recs := kn_of <% @KQR.no_recs %>.
Fixpoint qnat (n : nat) : term := match n with O => tConstruct ind_nat 0 [] | S n => tApp (tConstruct ind_nat 1 []) [qnat n] end.
Definition qkind (k : kind) : term :=
  match k with KNum => tConstruct ind_kind 0 [] | KBool => tConstruct ind_kind 1 [] | KRec ri => tApp (tConstruct ind_kind 2 []) [qnat ri] end.
Definition qlist (A : term) (l : list term) : term :=
  fold_right (fun x acc => tApp (tConstruct ind_list 1 []) [A; x; acc]) (tApp (tConstruct ind_list 0 []) [A]) l.
Definition blk_meaning (gs : sig) (mfix : mfixpoint term) : term :=
  tApp (tConst kn_blk []) [tConst kn_no_recs []; qnat (Nat.pred (sn gs)); qlist (tInd ind_kind []) (map qkind (sk gs));
                           tConstruct ind_bool (if sm gs then 0 else 1) [];
                           qlist (match mfix with d :: _ => dtype d | [] => tVar "none"%bs end) (map (fun j => tFix mfix j) (seq 0 (length mfix)))].
(** a member: one call of the block function, its counters, the selector, its parameters *)
Fixpoint fwd_args (ks : list kind) : sexps :=
  match ks with
  | [] => SNil
  | KNum :: ks => SCons (SVar (length (filter (kind_eqb KNum) ks))) (fwd_args ks)
  | KBool :: ks => SConsB (BVar (length (filter (kind_eqb KBool) ks))) (fwd_args ks)
  | KRec ri :: ks => SConsR (RVar (length (filter (fun k => match k with KRec _ => true | _ => false end) ks))) (fwd_args ks)
  end.
Definition member_body (bi : nat) (gs : sig) (j : nat) : fbody :=
  FPlain (SCall bi (to_scnts (map CVar (rev (seq 0 (sn gs))) ++ [CNat (SInt (Uint63.of_Z (Z.of_nat j)))])) (fwd_args (sk gs))).
Definition blk_name (mp : modpath) (mfix : mfixpoint term) : kername :=
  (mp, match mfix with d :: _ => match binder_name (dname d) with nNamed s => s | nAnon => "blk"%bs end | [] => "blk"%bs end ^ "__cblk").
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
Definition kn_fst := kn_of <% @fst %>.
Definition kn_snd := kn_of <% @snd %>.
Definition helper_of (Σ : global_env) (mp : modpath) (fns : list kername) (kn : kername) : option term :=
  if Kername.eqb kn kn_fst || Kername.eqb kn kn_snd then body_of Σ kn else
  if Kername.eqb kn kn_rd8 || Kername.eqb kn kn_upd8 || Kername.eqb kn kn_w64_op || Kername.eqb kn kn_kq_nat
     || existsb (Kername.eqb kn) fns then None
  else if eq_mp (fst kn) mp || eq_mp (fst kn) kit_mp || eq_mp (fst kn) uint63_mp then
    match body_of Σ kn with Some b => if has_fix 1000 b then None else Some b | None => None end
  else None.

(* ---------------------------------------------------------------- functions given to functions *)
(** a recursive function of the program that takes functions is a template (§5.1): each call that gives it known functions
    -- closed terms -- gets a copy of its own, read with the function parameters bound to the functions given *)
Definition is_prod (t : term) : bool := match t with tProd _ _ _ => true | _ => false end.
Definition tmpl_tys (Σ : global_env) (kn : kername) : option (list term) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some (tFix [d] 0) => let tys := fst (lams (dbody d)) in if existsb is_prod tys then Some tys else None
      | _ => None
      end
  | _ => None
  end.
Definition is_tmpl (Σ : global_env) (mp : modpath) (kn : kername) : bool :=
  eq_mp (fst kn) mp && match tmpl_tys Σ kn with Some _ => true | None => false end.
Definition fn_args (tys args : list term) : list term := map snd (filter (fun p => is_prod (fst p)) (combine tys args)).
Definition nonfn_args (tys args : list term) : list term := map snd (filter (fun p => negb (is_prod (fst p))) (combine tys args)).

(** two functions given are the same copy when they are the same term (a structural comparison: MetaRocq's generic one is
    slow under [vm_compute], F2) *)
(** the copies made: the template, the functions given, the copy's name, its meaning (the template applied to them) *)
Definition copytab := list (kername * (list term * list cent) * kername * term).
Definition find_copy (T : kername) (fargs : list term) (capk : list cent) (tbl : copytab) : option kername :=
  option_map (fun e => snd (fst e)) (List.find (fun e => Kername.eqb T (fst (fst (fst e))) && teqs fargs (fst (snd (fst (fst e))))
                                                         && capk_eqb capk (snd (snd (fst (fst e))))) tbl).
(** a call of a template: the copy for its functions given, and its arguments -- the template's counters, the captured
    numbers and booleans, its other arguments, the captured memory (step 13) *)
Definition tc_of (Σ : global_env) (mp : modpath) (tbl : copytab) (kn : kername) (args : list term) : option (kername * list term) :=
  if existsb (fun e => Kername.eqb kn (fst (fst (fst e)))) tbl then   (* a template with a copy: no look-up otherwise *)
    match tmpl_tys Σ kn with
    | Some tys => if Nat.eqb (length args) (length tys) then
                    let fa := fn_args tys args in
                    let fv := fold_left (fun a f => fvs 1000 0 f a) fa [] in
                    let fa' := map (abs_caps fv) fa in
                    match List.find (fun e => Kername.eqb kn (fst (fst (fst e))) && teqs fa' (fst (snd (fst (fst e))))) tbl with
                    | Some (_, (_, capk), ckn, _) =>
                        let nonfn := nonfn_args tys args in
                        let nc := fst (lead_nats (filter (fun t => negb (is_prod t)) tys)) in
                        let cs := combine capk (map tRel fv) in
                        Some (ckn, firstn nc nonfn ++ map snd (filter (fun p => negb (is_memc (fst p))) cs) ++ skipn nc nonfn
                                   ++ map snd (filter (fun p => is_memc (fst p)) cs))
                    | None => None
                    end
                  else None
    | None => None
    end
  else None.

(** the meaning of a copy: [fun x1 .. xn => T .. f .. xi ..], the functions given in their places; with captured variables
    (step 13) [fun c1 .. b1 .. x1 .. s => T .. f ..]: the template's counters, the captured numbers and booleans, the
    template's other parameters, the captured memory *)
Definition cap_ty (c : cent) : term := match c with CBool => tInd ind_bool [] | CMem | CDead => tConst kn_mem [] | _ => tConst kn_int [] end.
Definition copy_meaning (T : kername) (tys fargs : list term) (capk : list cent) : term :=
  let nonfn := filter (fun t => negb (is_prod t)) tys in
  let nc := fst (lead_nats nonfn) in
  let cn := filter (fun c => negb (is_memc c)) capk in
  let mc := length cn in
  let cm := if existsb is_memc capk then 1 else 0 in
  let n := length nonfn + mc + cm in
  let pos i := if Nat.ltb i nc then i else i + mc in
  let capidx k := if is_memc (nth k capk CNum) then 0 else n - 1 - (nc + length (filter (fun c => negb (is_memc c)) (firstn k capk))) in
  let sb := map (fun k => tRel (capidx k)) (seq 0 (length capk)) in
  let fix args (l fa : list term) (i : nat) : list term :=
    match l with
    | [] => []
    | t :: r => if is_prod t then match fa with f :: fa' => subst sb 0 f :: args r fa' i | [] => [] end
                else tRel (n - 1 - pos i) :: args r fa (S i)
    end in
  fold_right (fun ty b => tLambda {| binder_name := nAnon; binder_relevance := Relevant |} ty b)
             (tApp (tConst T []) (args tys fargs 0))
             (firstn nc nonfn ++ map cap_ty cn ++ skipn nc nonfn ++ (if Nat.eqb cm 1 then [tConst kn_mem []] else [])).

(** the helpers that reach a template (through their own text or the helpers they write out): only these are written out
    when the call sites are looked for -- a template call in a helper is seen with the helper's arguments put in, and a
    program with no template writes out nothing (measured: writing every helper out at every call made the reifier's step
    on the kernels' programs 8 s slower) *)
Fixpoint helpers_of (fuel : nat) (hb : kername -> option term) (t : term) (seen : list kername) : list kername :=
  match fuel with
  | O => seen
  | S fuel =>
      fold_left (fun sn k => if existsb (Kername.eqb k) sn then sn
                             else match hb k with Some b => helpers_of fuel hb b (k :: sn) | None => sn end)
                (consts 10000 t []) seen
  end.
Definition tmpl_helpers (Σ : global_env) (hb : kername -> option term) (tms kns : list kername) : list kername :=
  match tms with
  | [] => []
  | _ =>
      let hs := fold_left (fun a kn => match body_of Σ kn with Some b => helpers_of 50 hb b a | None => a end) kns [] in
      let step (th : list kername) : list kername :=
        filter (fun h => match hb h with
                         | Some b => existsb (fun k => existsb (Kername.eqb k) tms || existsb (Kername.eqb k) th) (consts 10000 b [])
                         | None => false
                         end) hs in
      Nat.iter (length hs) step []
  end.

(** the calls of templates in a text, the helpers that reach a template written out: each the template, its functions
    given with their captured variables numbered in the order they first appear, and those variables' kinds (step 13: a
    number, a boolean, the memory -- read off the binders' types, [kctx], the nearest first) *)
Definition ty_cent (ty : term) : option cent :=
  if is_ty kn_int ty then Some CNum else if is_bool ty then Some CBool else if is_ty kn_mem ty then Some CMem else None.
Fixpoint sites (fuel : nat) (Σ : global_env) (tms : list kername) (hb : kername -> option term) (th : list kername)
  (kctx : list (option cent)) (t : term) (acc : list (kername * list term * list cent)) : list (kername * list term * list cent) :=
  match fuel with
  | O => acc
  | S fuel =>
      let wr (kn : kername) (args : list term) (acc : list (kername * list term * list cent)) :=
        if existsb (Kername.eqb kn) th then match hb kn with Some b => sites fuel Σ tms hb th kctx (wout b args) acc | None => acc end
        else acc in
      match t with
      | tApp (tConst kn _) args =>
          let acc := fold_left (fun a x => sites fuel Σ tms hb th kctx x a) args acc in
          match (if existsb (Kername.eqb kn) tms then tmpl_tys Σ kn else None) with
          | Some tys =>
              if Nat.eqb (length args) (length tys) then
                let fa := fn_args tys args in
                let fv := fold_left (fun a f => fvs 1000 0 f a) fa [] in
                match opt_all (map (fun r => nth r kctx None) fv) with
                | Some capk =>
                    if forallb cap_ok capk && Nat.leb (length (filter is_memc capk)) 1
                       && negb (existsb (is_ty kn_mem) tys && existsb is_memc capk)
                    then (kn, map (abs_caps fv) fa, capk) :: acc else acc
                | None => acc
                end
              else acc
          | None => wr kn args acc
          end
      | tApp (tLambda _ _ _ as f) args => sites fuel Σ tms hb th kctx (wout f args) acc
      | tApp f args => fold_left (fun a x => sites fuel Σ tms hb th kctx x a) args (sites fuel Σ tms hb th kctx f acc)
      | tConst kn _ => wr kn [] acc
      | tLambda _ ty b => sites fuel Σ tms hb th (ty_cent ty :: kctx) b acc
      | tProd _ _ b => sites fuel Σ tms hb th (None :: kctx) b acc
      | tLetIn _ b ty body => sites fuel Σ tms hb th (ty_cent ty :: kctx) body (sites fuel Σ tms hb th kctx b acc)
      | tCase _ _ c brs => fold_left (fun a br => sites fuel Σ tms hb th (repeat None (length (bcontext br)) ++ kctx) (bbody br) a) brs
                                     (sites fuel Σ tms hb th kctx c acc)
      | tFix mfix _ => fold_left (fun a d => sites fuel Σ tms hb th (repeat None (length mfix) ++ kctx) (dbody d) a) mfix acc
      | _ => acc
      end
  end.

(** a copy's parameters, nearest first: a function parameter bound to the function given *)
Fixpoint tkinds (tys fargs : list term) (p : nat) : list cent :=
  match tys with
  | [] => []
  | t :: r => if is_prod t then match fargs with f :: fa => CFn p f :: tkinds r fa (S p) | [] => [] end
              else (if is_nat t then CCnt else if is_ty kn_mem t then CMem else if is_bool t then CBool else CNum) :: tkinds r fargs p
  end.
Fixpoint tdrop (tys : list term) (p : nat) : list (option nat) :=
  match tys with [] => [] | t :: r => if is_prod t then Some p :: tdrop r (S p) else None :: tdrop r p end.

(** a template's copy, read as a recursive function: its signature without the function parameters; the recursive call
    passes them on, and they are dropped *)
Definition read_tmpl (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (kn : kername) (fargs : list term) (capk : list cent) : option (sig * fbody) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some (tFix [d] 0) =>
          let '(tys, body) := lams (dbody d) in
          match read_sig rt (filter (fun t => negb (is_prod t)) tys) (ret_ty (dtype d)), body with
          | Some gs0, tCase ci _ (tRel cnt) [b0; b1] =>
              (* the captured numbers and booleans before the template's other parameters, the captured memory last *)
              let gs := mksig (sn gs0) (map (fun c => match c with CBool => KBool | _ => KNum end) (filter (fun c => negb (is_memc c)) capk) ++ sk gs0)
                              (sm gs0 || existsb is_memc capk) (sr gs0) (sw gs0) (sq gs0) in
              let nx := Nat.pred (sn gs) in
              let fd := tdrop (tl tys) 0 in
              if Nat.eqb (rarg d) 0 && negb (Nat.eqb (sn gs) 0) && negb (isq gs) && negb (sm gs0 && existsb is_memc capk)
                 && Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat)
                 && Nat.eqb cnt (Nat.pred (length tys)) && is_nat (hd (tRel 0) tys) then
                let ctx := rev (tkinds tys fargs 0) ++ [CSelf] ++ rev capk in
                if sr gs then
                  match reify_m callees (sm gs) nx hb tc fd rt 100000 ctx (bbody b0),
                        reify_m callees (sm gs) nx hb tc fd rt 100000 (CPred :: ctx) (bbody b1) with
                  | Some m0, Some m1 => Some (gs, FRecM m0 m1)
                  | _, _ => None
                  end
                else
                  match reify callees (sm gs) nx hb tc fd rt 100000 ctx (bbody b0),
                        reify callees (sm gs) nx hb tc fd rt 100000 (CPred :: ctx) (bbody b1) with
                  | Some e0, Some e1 => Some (gs, FRec e0 e1)
                  | _, _ =>
                      if sm gs then
                        match reify_x callees (sm gs) nx hb tc fd rt 100000 ctx (bbody b0),
                              reify_x callees (sm gs) nx hb tc fd rt 100000 (CPred :: ctx) (bbody b1) with
                        | Some x0, Some x1 => Some (mksig (sn gs) (sk gs) true false true None, FRecX x0 x1)
                        | _, _ => None
                        end
                      else None
                  end
              else None
          | _, _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition callees_of (es : list (kername * sig * fbody)) : list (kername * sig) := map (fun x => (fst (fst x), snd (fst x))) es.

(** the copy for a call site, made (with the copies its functions need) if it is not yet, before the functions that call it *)
Fixpoint ensure (fuel : nat) (Σ : global_env) (mp : modpath) (hb : kername -> option term) (rt : list rentry) (th tms : list kername) (site : kername * list term * list cent)
  (st : option (list (kername * sig * fbody) * copytab)) {struct fuel} : option (list (kername * sig * fbody) * copytab) :=
  match fuel, st with
  | O, _ => None
  | _, None => None
  | S fuel, Some (es, tbl) =>
      let '(T, fargs, capk) := site in
      match find_copy T fargs capk tbl with
      | Some _ => st
      | None =>
          match tmpl_tys Σ T with
          | None => None
          | Some tys =>
              let nested := fold_left (fun a f => sites 1000 Σ tms hb th (map Some capk) f a) fargs [] in
              match fold_left (fun st s => ensure fuel Σ mp hb rt th tms s st) (rev nested) st with
              | Some (es, tbl) =>
                  let ckn := (MPfile ["kqcopy"%bs], snd T ^ "__c" ^ string_of_nat (length tbl)) in
                  match read_tmpl Σ hb (tc_of Σ mp tbl) rt (callees_of es) T fargs capk with
                  | Some (gs, b) => if wf_f (map snd (callees_of es)) gs b
                                    then Some (es ++ [(ckn, gs, b)], tbl ++ [(T, (fargs, capk), ckn, copy_meaning T tys fargs capk)])
                                    else None
                  | None => None
                  end
              | None => None
              end
          end
      end
  end.

(** the whole program: its functions callees first (a template's copies in its place), each with its signature and body;
    and the meaning of each copy *)
(** the program's record types: those of the reached functions' parameters and results, each once *)
Fixpoint prod_tys (t : term) : list term := match t with tProd _ a b => a :: prod_tys b | _ => [t] end.
(** the record types a body names (step 19): of a constructor applied (its parameters the first arguments), of a match
    (its parameters the predicate's), of a [let], of a primitive projection -- in the body and the helpers it writes out,
    each helper once *)
Definition ind_app (i : inductive) (u : Instance.t) (ps : list term) : term := match ps with [] => tInd i u | _ => tApp (tInd i u) ps end.
Definition ctor_ty (Σ : global_env) (i : inductive) (u : Instance.t) (args : list term) : term :=
  match lookup_env Σ (inductive_mind i) with
  | Some (InductiveDecl mib) => ind_app i u (firstn (ind_npars mib) args)
  | _ => tVar "none"%bs
  end.
Fixpoint body_rtys (fuel : nat) (Σ : global_env) (hb : kername -> option term) (t : term) (st : list term * list kername)
  {struct fuel} : list term * list kername :=
  match fuel with
  | O => st
  | S fuel =>
      let add (ty : term) (s : list term * list kername) := (fst s ++ [ty], snd s) in
      match t with
      | tApp (tConstruct i 0 u) args => fold_left (fun s x => body_rtys fuel Σ hb x s) args (add (ctor_ty Σ i u args) st)
      | tApp f args => fold_left (fun s x => body_rtys fuel Σ hb x s) args (body_rtys fuel Σ hb f st)
      | tLambda _ _ b => body_rtys fuel Σ hb b st
      | tLetIn _ b ty body => body_rtys fuel Σ hb body (body_rtys fuel Σ hb b (add ty st))
      | tCase ci p c brs => fold_left (fun s br => body_rtys fuel Σ hb (bbody br) s) brs
                              (body_rtys fuel Σ hb c (add (ind_app (ci_ind ci) (puinst p) (pparams p)) st))
      | tProj pr c => body_rtys fuel Σ hb c (add (tInd (proj_ind pr) []) st)
      | tFix mfix _ => fold_left (fun s d => body_rtys fuel Σ hb (dbody d) s) mfix st
      | tConst kn _ => if existsb (Kername.eqb kn) (snd st) then st else
                       match hb kn with Some b => body_rtys fuel Σ hb b (fst st, kn :: snd st) | None => st end
      | _ => st
      end
  end.
Definition rtab_of (Σ : global_env) (hb : kername -> option term) (kns : list kername) : list rentry :=
  let add_ty := fun rt t => match rec_shape Σ t with
                            | Some e => match rindex t rt 0 with Some _ => rt | None => rt ++ [e] end
                            | None => rt end in
  let sig_rt := fold_left (fun rt kn =>
    match lookup_env Σ kn with
    | Some (ConstantDecl cb) => fold_left add_ty (prod_tys (cst_type cb)) rt
    | _ => rt
    end) kns [] in
  (* the bodies' record types after the signatures': a program's record indices are those of before *)
  let btys := fst (fold_left (fun s kn => match body_of Σ kn with Some b => body_rtys 2000 Σ hb b s | None => s end) kns ([], [])) in
  fold_left add_ty btys sig_rt.
(** for kitc.py: each record type's text, its constructor's name, its number of fields *)
Definition rec_text (Σ : global_env) (e : rentry) : string * string * nat :=
  let '(t, i, n, ps) := e in
  let nm := snd (inductive_mind i) in
  let ty := match ps with [] => nm | _ => "(" ^ nm ^ fold_left (fun a _ => a ^ " PrimInt63.int") ps "" ^ ")" end in
  let cn := match lookup_env Σ (inductive_mind i) with
            | Some (InductiveDecl mib) => match ind_bodies mib with oib :: _ => match ind_ctors oib with cb :: _ => cstr_name cb | [] => "" end | [] => "" end
            | _ => "" end in
  (ty, cn, n).
Definition rec_info (p : program) : list (string * string * nat) :=
  match p with
  | (Σ, tConst root _) => let mp := fst root in let kns := reach 1000 Σ mp root root [] in
                          map (rec_text Σ) (rtab_of Σ (helper_of Σ mp kns) kns)
  | _ => []
  end.

Definition reify_prog2 (p : program) : option (list (kername * sig * fbody) * list (string * term)) :=
  match p with
  | (Σ, tConst root _) =>
      let mp := fst root in
      let kns := reach 1000 Σ mp root root [] in
      let hb := helper_of Σ mp kns in
      let rt := rtab_of Σ hb kns in
      let tms := filter (is_tmpl Σ mp) kns in
      let th := tmpl_helpers Σ hb tms kns in
      let st := fold_left (fun st kn =>
                  match st with
                  | None => None
                  | Some _ =>
                      if existsb (Kername.eqb kn) tms then st else
                      let st := match tms, body_of Σ kn with
                                | _ :: _, Some b => fold_left (fun st s => ensure 50 Σ mp hb rt th tms s st) (rev (sites 1000 Σ tms hb th [] b [])) st
                                | _, _ => st
                                end in
                      match st with
                      | Some (es, tbl) =>
                          match body_of Σ kn with
                          | Some (tFix mfix k) =>
                              if Nat.ltb 1 (length mfix) then
                                (* a member of a mutual block: the block function first (once), then the member as one call of it *)
                                let bn := blk_name mp mfix in
                                let wfok := fun cs gs b => @wf_f (arity_recs (map (fun e => snd (fst e)) rt)) (map snd cs) gs b in
                                let st1 := if existsb (fun e => Kername.eqb (fst (fst e)) bn) es then Some (es, tbl) else
                                           match read_block hb (tc_of Σ mp tbl) rt (callees_of es) mfix with
                                           | Some (gs, gs', b) => if wfok (callees_of es) gs' b
                                                                  then Some (es ++ [(bn, gs', b)], tbl ++ [(bn, ([], []), bn, blk_meaning gs mfix)])
                                                                  else None
                                           | None => None
                                           end in
                                match st1 with
                                | Some (es1, tbl1) =>
                                    match find_callee bn (callees_of es1) 0, read_block hb (tc_of Σ mp tbl1) rt (callees_of es) mfix with
                                    | Some (bi, _), Some (gs, _, _) =>
                                        let b := member_body bi gs k in
                                        if wfok (callees_of es1) gs b then Some (es1 ++ [(kn, gs, b)], tbl1) else None
                                    | _, _ => None
                                    end
                                | None => None
                                end
                              else match reify_fun Σ hb (tc_of Σ mp tbl) rt (callees_of es) kn with
                                   | Some (gs, b) => Some (es ++ [(kn, gs, b)], tbl)
                                   | None => None
                                   end
                          | _ => match reify_fun Σ hb (tc_of Σ mp tbl) rt (callees_of es) kn with
                                 | Some (gs, b) => Some (es ++ [(kn, gs, b)], tbl)
                                 | None => None
                                 end
                          end
                      | None => None
                      end
                  end) kns (Some ([], [])) in
      option_map (fun et => (fst et, map (fun e => (snd (snd (fst e)), snd e)) (snd et))) st
  | _ => None
  end.
Definition reify_prog (p : program) : option (list (kername * sig * fbody)) := option_map fst (reify_prog2 p).
Definition meaning_of (l : list (string * term)) (nm : string) : term :=
  match List.find (fun q => fst q == nm) l with Some q => snd q | None => tVar "none"%bs end.

(* ---------------------------------------------------------------- why a program is not read *)

Definition add_s (x : string) (l : list string) : list string := if existsb (fun y => y == x) l then l else l ++ [x].

(** the constants the syntax reads: the integer operations and comparisons, [rd], [upd], the program's functions *)
Definition known_const (fns : list kername) (kn : kername) : bool :=
  (eq_mp (fst kn) prim_mp && (match binop_v (snd kn), cmp_v (snd kn) with None, None => false | _, _ => true end))
  || Kername.eqb kn kn_rd || Kername.eqb kn kn_upd || Kername.eqb kn kn_rd32 || Kername.eqb kn kn_upd32 || Kername.eqb kn kn_rd8 || Kername.eqb kn kn_upd8
  || Kername.eqb kn kn_kq_nat || existsb (Kername.eqb kn) fns || Kername.eqb kn kn_ksize || Kername.eqb kn kn_w64_op
  || existsb (fun e => Kername.eqb (fst (fst e)) kn) hw_table || existsb (fun e => Kername.eqb (fst (fst e)) kn) hwf_table
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
      | tConstruct i _ _ =>      (* O and S are counters, true and false booleans, a 64-bit operation's name *)
          if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) || Kername.eqb (inductive_mind i) (inductive_mind ind_bool)
             || Kername.eqb (inductive_mind i) (inductive_mind ind_w64op) then acc
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
Definition why_fun (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (fns bad : list kername) (callees : list (kername * sig)) (kn : kername) : list string :=
  if match read_fun Σ hb tc rt callees kn with Some _ => true | None => false end then
    ["read, but not well formed: a recursive call given a counter grown by S (it would have no bound), a call given fewer"
     ^ " arguments than its function takes, a counter more than 2^20 successors deep, a let of a counter grown by S over a"
     ^ " variable (above the function's bound), or a call of a number function that writes the memory, or of the function"
     ^ " itself when it writes, inside an expression (not yet: the caller's memory would not be the text's)"]
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
                               (filter (fun t => negb (is_bool t) && match rindex t rt 0 with Some _ => false | None => true end) tys ++ [ret_ty ty]) [] in
          let sigr := match read_sig rt tys (ret_ty ty), odd with
                      | Some _, _ => []
                      | None, [] => ["parameters in an order not read (a counter after a number, or the memory not last)"]
                      | None, x :: r => ["a parameter or result of type " ^ fold_left (fun a y => a ^ ", " ^ y) r x]
                      end in
          let r0 := if rec == "" then sigr else rec :: sigr in
          let r1 := fold_left (fun a t => blockers 100000 (fns ++ hs) nohb t a) texts r0 in
          let numfn := negb (is_ty kn_mem (ret_ty ty)) in
          let mfns := filter (fun k => match lookup_env Σ k with
                                       | Some (ConstantDecl c) => is_ty kn_mem (ret_ty (cst_type c)) | _ => false end) fns in
          let r2 := if numfn && existsb (writes 100000 nohb mfns) texts
                    then add_s "a number function that writes the memory where it is not read yet" r1
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
      let mp := fst root in
      let kns := reach 1000 Σ mp root root [] in
      let hb := helper_of Σ mp kns in
      let rt := rtab_of Σ hb kns in
      let tms := filter (is_tmpl Σ mp) kns in
      let th := tmpl_helpers Σ hb tms kns in
      let '(_, _, _, out) :=
        fold_left (fun '(es, tbl, bad, out) kn =>
          if existsb (Kername.eqb kn) tms then (es, tbl, bad, out) else
          let ss := match tms, body_of Σ kn with _ :: _, Some b => rev (sites 1000 Σ tms hb th [] b []) | _, _ => [] end in
          match fold_left (fun st s => ensure 50 Σ mp hb rt th tms s st) ss (Some (es, tbl)) with
          | None =>
              let tr := flat_map (fun s => filter (fun r => negb (r == "a parameter or result of type a function"))
                                               (why_fun Σ hb (tc_of Σ mp tbl) rt kns bad (callees_of es) (fst (fst s)))) ss in
              (es, tbl, bad ++ [kn], out ++ [(snd kn, "gives functions to a recursive function whose copy for them is not read" :: tr)])
          | Some (es', tbl') =>
              match reify_fun Σ hb (tc_of Σ mp tbl') rt (callees_of es') kn with
              | Some (gs, b) => (es' ++ [(kn, gs, b)], tbl', bad, out)
              | None => (es', tbl', bad ++ [kn], out ++ [(snd kn, why_fun Σ hb (tc_of Σ mp tbl') rt kns bad (callees_of es') kn)])
              end
          end) kns ([], [], [], []) in
      out
  | _ => [("", ["the root is not a constant"])]
  end.

(** what [kitc.py --reflect] reads of a program: each function's name and signature, in order *)
Definition rletter (i : nat) : string := nth i ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"]%bs "z"%bs.
Definition kletters (ks : list kind) : string :=
  fold_right (fun k a => (match k with KNum => "I" | KBool => "B" | KRec i => rletter i end) ^ a) ""%bs ks.
Definition info_of (l : list (kername * sig * fbody)) :=
  map (fun x : kername * sig * fbody => let '(kn, g, _) := x in
         (snd kn, sn g, kletters (sk g), sm g, sr g, sw g, match sq g with Some i => rletter i | None => ""%bs end)) l.

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
Fixpoint funs_of {RTs : RecTypes} (i : nat) (l : list (kername * sig * fbody)) : list (positive * fn) :=
  match l with [] => [] | (_, gs, b) :: r => (gid1 i, compile_f gid1 i gs b) :: funs_of (S i) r end.
Definition sig_at (l : list (kername * sig * fbody)) (i : nat) : sig :=
  match nth_error l i with Some (_, gs, _) => gs | None => mksig 0 (nk 0) false false false None end.
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
Definition cnt_all_g := mksig 0 (nk 1) false false false None.
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

(* a byte ([rd8]) is one byte access, as the translator makes it, not shifts of a 4-byte cell (step 15); a halfword ([rd16])
   is written out over two; a byte written ([upd8]) is one byte store *)
Definition hb8 (i : i63) (s : mem) : i63 := PrimInt63.add (KQ.KQRun.rd8 1 i s) (KQ.KQRun.rd16 1 i s).
Definition hb8w (i : i63) (s : mem) : mem := KQ.KQRun.upd16 1 i 513 (KQ.KQRun.upd8 1 i 7 s).
Definition hb8_src := ltac:(run_template_program (tmQuoteRec hb8)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition hb8w_src := ltac:(run_template_program (tmQuoteRec hb8w)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Eval vm_compute in map snd hb8_src.
Eval vm_compute in map snd hb8w_src.
Definition hb8_Pr := mkprog (funs_of 0 hb8_src ++ funs_of 1 hb8w_src) [].
Time Lemma hb8_ok_r : callee_ok hb8_Pr (gid1 0) (cbz 0) (sig_at hb8_src 0) hb8.
Proof. Time exact_no_check (compile_f_ok hb8_Pr [] gid1 0 (sig_at hb8_src 0) (body_at hb8_src 0) eq_refl eq_refl (no_callees hb8_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma hb8w_ok_r : callee_ok hb8_Pr (gid1 1) (cbz 1) (sig_at hb8w_src 0) hb8w.
Proof.
  Time exact_no_check (compile_f_ok hb8_Pr [existT ftype (sig_at hb8_src 0) hb8] gid1 1 (sig_at hb8w_src 0) (body_at hb8w_src 0) eq_refl eq_refl
    (all_ok_callees hb8_Pr gid1 [existT ftype (sig_at hb8_src 0) hb8] (conj hb8_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.

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

(* ---------------------------------------------------------------- functions given to functions *)
(* a recursive function that takes a function (a template) gets a copy for each function it is given; the copy's meaning is
   the template applied to the function (defined from the term the reifier gives, as kitc.py does), its statement from its
   two equations ([compile_f_okr]) *)
Fixpoint rapply (n : nat) (f : i63 -> i63) (x : i63) : i63 := match n with O => x | S m => rapply m f (f x) end.
Definition radd3 (x : i63) : i63 := PrimInt63.add x 3.
Definition rmix (x : i63) : i63 := PrimInt63.land (PrimInt63.add (PrimInt63.mul x 5) 1) 65535.
Definition ruse (n : nat) (x : i63) : i63 := PrimInt63.add (rapply n radd3 x) (rapply (S n) rmix x).
Definition ruse_res := ltac:(run_template_program (tmQuoteRec ruse)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition ruse_src := fst ruse_res.
Check (eq_refl : map (fun x => (snd (fst (fst x)), snd x)) ruse_src =
  [("rapply__c0"%bs, FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 3)) SNil)));
   ("rapply__c1"%bs, FRec (SVar 0) (SRec CNil (SCons (SOp Bland (SOp Badd (SOp Bmul (SVar 0) (SInt 5)) (SInt 1)) (SInt 65535)) SNil)));
   ("ruse"%bs, FPlain (SOp Badd (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil)) (SCall 1 (CCons (CS (CVar 0)) CNil) (SCons (SVar 0) SNil))))]).
MetaRocq Run (tmMkDefinition "ruse_c0"%bs (meaning_of (snd ruse_res) "rapply__c0"%bs)).
MetaRocq Run (tmMkDefinition "ruse_c1"%bs (meaning_of (snd ruse_res) "rapply__c1"%bs)).
Definition ruse_Pr := mkprog (funs_of 0 ruse_src) [].
Time Lemma ruse_ok0 : callee_ok ruse_Pr (gid1 0) (cbz 0) (sig_at ruse_src 0) ruse_c0.
Proof.
  Time exact_no_check (compile_f_okr ruse_Pr [] gid1 0 0 (nk 1) false (fr0 (body_at ruse_src 0)) (fr1 (body_at ruse_src 0)) ruse_c0
    eq_refl eq_refl (no_callees ruse_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma ruse_ok1 : callee_ok ruse_Pr (gid1 1) (cbz 1) (sig_at ruse_src 1) ruse_c1.
Proof.
  Time exact_no_check (compile_f_okr ruse_Pr [existT ftype (sig_at ruse_src 0) ruse_c0] gid1 1 0 (nk 1) false
    (fr0 (body_at ruse_src 1)) (fr1 (body_at ruse_src 1)) ruse_c1 eq_refl eq_refl
    (all_ok_callees ruse_Pr gid1 [existT ftype (sig_at ruse_src 0) ruse_c0] (conj ruse_ok0 Logic.I)) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma ruse_ok2 : callee_ok ruse_Pr (gid1 2) (cbz 2) (sig_at ruse_src 2) ruse.
Proof.
  Time exact_no_check (compile_f_ok ruse_Pr [existT ftype (sig_at ruse_src 0) ruse_c0; existT ftype (sig_at ruse_src 1) ruse_c1]
    gid1 2 (sig_at ruse_src 2) (body_at ruse_src 2) eq_refl eq_refl
    (all_ok_callees ruse_Pr gid1 [existT ftype (sig_at ruse_src 0) ruse_c0; existT ftype (sig_at ruse_src 1) ruse_c1]
       (conj ruse_ok0 (conj ruse_ok1 Logic.I))) eq_refl eq_refl).
Time Qed.
Print Assumptions ruse_ok2.
(* the shape of the loop library's measure recursion: the template applies the function given to its own partial
   application; written out, the recursion is a call of the copy itself *)
Fixpoint rw_go (k : nat) (F : (i63 -> i63) -> i63 -> i63) (a : i63) : i63 := match k with O => 0 | S k' => F (rw_go k' F) a end.
Definition rw (a : i63) : i63 :=
  rw_go (KQ.KQRun.kq_nat (PrimInt63.add a 1)) (fun rec x => if PrimInt63.ltb 0 x then PrimInt63.add x (rec (PrimInt63.sub x 1)) else 0%uint63) a.
Definition rw_res := ltac:(run_template_program (tmQuoteRec rw)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition rw_src := fst rw_res.
Check (eq_refl : map (fun x => (snd (fst (fst x)), snd x)) rw_src =
  [("rw_go__c0"%bs, FRec (SInt 0) (SIf Clt (SInt 0) (SVar 0) (SOp Badd (SVar 0) (SRec CNil (SCons (SOp Bsub (SVar 0) (SInt 1)) SNil))) (SInt 0)));
   ("rw"%bs, FPlain (SCall 0 (CCons (CNat (SOp Badd (SVar 0) (SInt 1))) CNil) (SCons (SVar 0) SNil)))]).
MetaRocq Run (tmMkDefinition "rw_c0"%bs (meaning_of (snd rw_res) "rw_go__c0"%bs)).
Definition rw_Pr := mkprog (funs_of 0 rw_src) [].
Time Lemma rw_ok0 : callee_ok rw_Pr (gid1 0) (cbz 0) (sig_at rw_src 0) rw_c0.
Proof.
  Time exact_no_check (compile_f_okr rw_Pr [] gid1 0 0 (nk 1) false (fr0 (body_at rw_src 0)) (fr1 (body_at rw_src 0)) rw_c0
    eq_refl eq_refl (no_callees rw_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma rw_ok1 : callee_ok rw_Pr (gid1 1) (cbz 1) (sig_at rw_src 1) rw.
Proof.
  Time exact_no_check (compile_f_ok rw_Pr [existT ftype (sig_at rw_src 0) rw_c0] gid1 1 (sig_at rw_src 1) (body_at rw_src 1)
    eq_refl eq_refl (all_ok_callees rw_Pr gid1 [existT ftype (sig_at rw_src 0) rw_c0] (conj rw_ok0 Logic.I)) eq_refl eq_refl).
Time Qed.

(* ---------------------------------------------------------------- loops that write and give back a number *)
(* [rdeg] (the shape of CF7D's loop) and [rdeg_top], its caller, read from the text: the recursive call at the end given a
   written memory ([XRec]), the caller's last call ([XCall]) -- the trees of KQR.v's [deg] and [deg_top] *)
Fixpoint rdeg (n : nat) (i acc : i63) (s : mem) : i63 :=
  match n with
  | O => acc
  | S m => let d := PrimInt63.add (KQ.KQRun.rd 1 (PrimInt63.sub i 1) s) 1 in
           rdeg m (PrimInt63.add i 1) (PrimInt63.add acc d) (KQ.KQRun.upd 1 i d s)
  end.
Definition rdeg_top (n : nat) (s : mem) : i63 := rdeg n 1 0 (KQ.KQRun.upd 1 0 0 s).
Definition rdeg_src := ltac:(run_template_program (tmQuoteRec rdeg_top)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) rdeg_src = [(deg_g, deg_b); (degt_g, degt_b)]).
Definition rdeg_Pr := mkprog (funs_of 0 rdeg_src) [].
Time Lemma rdeg_ok : callee_ok rdeg_Pr (gid1 0) (cbz 0) (sig_at rdeg_src 0) rdeg.
Proof. Time exact_no_check (compile_f_ok rdeg_Pr [] gid1 0 (sig_at rdeg_src 0) (body_at rdeg_src 0) eq_refl eq_refl (no_callees rdeg_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rdeg_top_ok : callee_ok rdeg_Pr (gid1 1) (cbz 1) (sig_at rdeg_src 1) rdeg_top.
Proof.
  Time exact_no_check (compile_f_ok rdeg_Pr [existT ftype (sig_at rdeg_src 0) rdeg] gid1 1 (sig_at rdeg_src 1) (body_at rdeg_src 1)
    eq_refl eq_refl (all_ok_callees rdeg_Pr gid1 [existT ftype (sig_at rdeg_src 0) rdeg] (conj rdeg_ok Logic.I)) eq_refl eq_refl).
Time Qed.

(* [rsearch] (the shape of CF460C's search): a memory made by a call, a boolean let on it, the recursive call given that memory
   and a number chosen on the boolean *)
Fixpoint rfill (n : nat) (i : i63) (s : mem) : mem := match n with O => s | S m => rfill m (PrimInt63.add i 1) (KQ.KQRun.upd 0 i i s) end.
Fixpoint rsearch (n k : nat) (lo : i63) (s : mem) : i63 :=
  match n with
  | O => lo
  | S m => let s1 := rfill k lo s in
           let ok := PrimInt63.eqb (KQ.KQRun.rd 0 lo s1) lo in
           rsearch m k (if ok then PrimInt63.add lo 1 else lo) s1
  end.
Definition rsearch_src := ltac:(run_template_program (tmQuoteRec rsearch)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) rsearch_src =
  [(mksig 1 (nk 1) true true false None, FRecM MCur (MRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil) (MUpd (SInt 0) (SVar 0) (SVar 0) MCur)));
   (mksig 2 (nk 1) true false true None, FRecX (XRet (SVar 0))
      (XLetM (MCall 0 (CCons (CVar 1) CNil) (SCons (SVar 0) SNil) MCur)
        (XLetB (BCmp Ceq (SRd (SInt 0) (SVar 0)) (SVar 0))
          (XRec (CCons (CVar 1) CNil) (SCons (SIfB (BVar 0) (SOp Badd (SVar 0) (SInt 1)) (SVar 0)) SNil) MCur))))]).
Definition rsearch_Pr := mkprog (funs_of 0 rsearch_src) [].
Time Lemma rfill_ok : callee_ok rsearch_Pr (gid1 0) (cbz 0) (sig_at rsearch_src 0) rfill.
Proof. Time exact_no_check (compile_f_ok rsearch_Pr [] gid1 0 (sig_at rsearch_src 0) (body_at rsearch_src 0) eq_refl eq_refl (no_callees rsearch_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rsearch_ok : callee_ok rsearch_Pr (gid1 1) (cbz 1) (sig_at rsearch_src 1) rsearch.
Proof.
  Time exact_no_check (compile_f_ok rsearch_Pr [existT ftype (sig_at rsearch_src 0) rfill] gid1 1 (sig_at rsearch_src 1) (body_at rsearch_src 1)
    eq_refl eq_refl (all_ok_callees rsearch_Pr gid1 [existT ftype (sig_at rsearch_src 0) rfill] (conj rfill_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions rsearch_ok.

(* a template that writes and gives back a number: its copy is read as a loop that writes ([read_tmpl]), its statement from
   its two equations ([compile_f_okrx]), the caller's last call a call of the copy; the function given is written out, its
   argument bound by a let where it is not a variable *)
Fixpoint rtdeg (n : nat) (f : i63 -> i63) (i acc : i63) (s : mem) : i63 :=
  match n with
  | O => acc
  | S m => rtdeg m f (PrimInt63.add i 1) (PrimInt63.add acc (f (KQ.KQRun.rd 1 i s))) (KQ.KQRun.upd 1 i (f i) s)
  end.
Definition rtuse (n : nat) (s : mem) : i63 := rtdeg n radd3 0 0 s.
Definition rtuse_res := ltac:(run_template_program (tmQuoteRec rtuse)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition rtuse_src := fst rtuse_res.
Check (eq_refl : map (fun x => (snd (fst (fst x)), snd x)) rtuse_src =
  [("rtdeg__c0"%bs, FRecX (XRet (SVar 0))
      (XRec CNil (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SOp Badd (SVar 0) (SLet (SRd (SInt 1) (SVar 1)) (SOp Badd (SVar 0) (SInt 3)))) SNil))
         (MUpd (SInt 1) (SVar 1) (SOp Badd (SVar 1) (SInt 3)) MCur)));
   ("rtuse"%bs, FPlainX (XCall 0 (CCons (CVar 0) CNil) (SCons (SInt 0) (SCons (SInt 0) SNil)) MCur))]).
MetaRocq Run (tmMkDefinition "rtuse_c0"%bs (meaning_of (snd rtuse_res) "rtdeg__c0"%bs)).
Definition rtuse_Pr := mkprog (funs_of 0 rtuse_src) [].
Time Lemma rtuse_ok0 : callee_ok rtuse_Pr (gid1 0) (cbz 0) (sig_at rtuse_src 0) rtuse_c0.
Proof.
  Time exact_no_check (compile_f_okrx rtuse_Pr [] gid1 0 0 (nk 2) (fx0 (body_at rtuse_src 0)) (fx1 (body_at rtuse_src 0)) rtuse_c0
    eq_refl eq_refl (no_callees rtuse_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma rtuse_ok1 : callee_ok rtuse_Pr (gid1 1) (cbz 1) (sig_at rtuse_src 1) rtuse.
Proof.
  Time exact_no_check (compile_f_ok rtuse_Pr [existT ftype (sig_at rtuse_src 0) rtuse_c0] gid1 1 (sig_at rtuse_src 1) (body_at rtuse_src 1)
    eq_refl eq_refl (all_ok_callees rtuse_Pr gid1 [existT ftype (sig_at rtuse_src 0) rtuse_c0] (conj rtuse_ok0 Logic.I)) eq_refl eq_refl).
Time Qed.

(* ---------------------------------------------------------------- boolean parameters *)
(* the text of KQR.v's [bcount] / [bcall]: a boolean parameter passed on (negated) to the recursive call, and one chosen by
   the caller; each argument is read as a number, or else as a boolean, and well-formedness compares their kinds with the
   callee's *)
Fixpoint rbcount (n : nat) (i acc : i63) (odd : bool) (s : mem) : i63 :=
  match n with
  | O => acc
  | S m => rbcount m (PrimInt63.add i 1) (if odd then PrimInt63.add acc (KQ.KQRun.rd 0 i s) else acc) (negb odd) s
  end.
Definition rbcall (n : nat) (a : i63) (s : mem) : i63 := rbcount n 0 0 (PrimInt63.ltb a 5) s.
Definition rbcall_src := ltac:(run_template_program (tmQuoteRec rbcall)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) rbcall_src = [(bcount_g, bcount_b); (bcall_g, bcall_b)]).
Definition rbcall_Pr := mkprog (funs_of 0 rbcall_src) [].
Time Lemma rbcount_ok : callee_ok rbcall_Pr (gid1 0) (cbz 0) (sig_at rbcall_src 0) rbcount.
Proof. Time exact_no_check (compile_f_ok rbcall_Pr [] gid1 0 (sig_at rbcall_src 0) (body_at rbcall_src 0) eq_refl eq_refl (no_callees rbcall_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rbcall_ok : callee_ok rbcall_Pr (gid1 1) (cbz 1) (sig_at rbcall_src 1) rbcall.
Proof.
  Time exact_no_check (compile_f_ok rbcall_Pr [existT ftype (sig_at rbcall_src 0) rbcount] gid1 1 (sig_at rbcall_src 1) (body_at rbcall_src 1)
    eq_refl eq_refl (all_ok_callees rbcall_Pr gid1 [existT ftype (sig_at rbcall_src 0) rbcount] (conj rbcount_ok Logic.I)) eq_refl eq_refl).
Time Qed.

(* ---------------------------------------------------------------- records and pairs *)
(* a pair as a loop's state (the text of KQR.v's [pinner] / [pouter]): its type is the program's record type 0; [fst] and
   [snd] are written out, so a field is the pair taken apart *)
Fixpoint rpinner (fuel : nat) (i : i63) (p : i63 * i63) (s : mem) : i63 :=
  match fuel with
  | O => PrimInt63.add (fst p) (snd p)
  | S f => let x := KQ.KQRun.rd 0 i s in
           rpinner f (PrimInt63.add i 1) (PrimInt63.add (fst p) x, PrimInt63.land (PrimInt63.add (snd p) x) 255) s
  end.
Definition rpouter (n : nat) (a : i63) (s : mem) : i63 := rpinner n 0 (0%uint63, a) s.
Definition rpair_src := ltac:(run_template_program (tmQuoteRec rpouter)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Eval vm_compute in ltac:(run_template_program (tmQuoteRec rpouter) (fun q => let r := eval vm_compute in (rec_info q) in exact r)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) rpair_src =
  [(mksig 1 [KNum; KRec 0] true false false None,
    FRec (SOp Badd (SMatchR (RVar 0) (SVar 1)) (SMatchR (RVar 0) (SVar 0)))
      (SLet (SRd (SInt 0) (SVar 0)) (SRec CNil (SCons (SOp Badd (SVar 1) (SInt 1))
         (SConsR (RMk 0 (SCons (SOp Badd (SMatchR (RVar 0) (SVar 1)) (SVar 0))
                          (SCons (SOp Bland (SOp Badd (SMatchR (RVar 0) (SVar 0)) (SVar 0)) (SInt 255)) SNil))) SNil)))));
   (mksig 1 [KNum] true false false None,
    FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SInt 0) (SConsR (RMk 0 (SCons (SInt 0) (SCons (SVar 0) SNil))) SNil))))]).
Section RPair.
#[local] Instance rpair_recs : RecTypes | 0 :=
  {| RT := fun _ => (i63 * i63)%type;
     RO := fun _ => mkrops 2 (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end);
     Rd := fun _ => (0%uint63, 0%uint63) |}.
#[local] Instance rpair_laws : RecLaws.
Proof. split; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] L; try discriminate; reflexivity]. Qed.
Definition rpair_Pr := mkprog (funs_of 0 rpair_src) [].
Time Lemma rpinner_ok : callee_ok rpair_Pr (gid1 0) (cbz 0) (sig_at rpair_src 0) rpinner.
Proof. Time exact_no_check (@compile_f_ok rpair_recs rpair_laws rpair_Pr [] gid1 0 (sig_at rpair_src 0) (body_at rpair_src 0) eq_refl eq_refl (no_callees rpair_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rpouter_ok : callee_ok rpair_Pr (gid1 1) (cbz 1) (sig_at rpair_src 1) rpouter.
Proof.
  Time exact_no_check (@compile_f_ok rpair_recs rpair_laws rpair_Pr [existT ftype (sig_at rpair_src 0) rpinner] gid1 1 (sig_at rpair_src 1) (body_at rpair_src 1)
    eq_refl eq_refl (all_ok_callees rpair_Pr gid1 [existT ftype (sig_at rpair_src 0) rpinner] (conj rpinner_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions rpouter_ok.
End RPair.

(* a record of the program's own type as a loop's state (rec_state's shape): its projections are the program's helpers,
   written out, so a field is the record taken apart *)
Record rst := mkrst { racc : i63; rcnt : i63 }.
Fixpoint rsinner (fuel : nat) (i : i63) (r : rst) (s : mem) : i63 :=
  match fuel with
  | O => PrimInt63.add (racc r) (rcnt r)
  | S f => let x := KQ.KQRun.rd 0 i s in
           rsinner f (PrimInt63.add i 1) (mkrst (PrimInt63.add (racc r) x) (if PrimInt63.ltb x 500 then PrimInt63.add (rcnt r) 1 else rcnt r)) s
  end.
Definition rsouter (n : nat) (a : i63) (s : mem) : i63 := rsinner n 0 (mkrst 0%uint63 a) s.
Definition rst_src := ltac:(run_template_program (tmQuoteRec rsouter)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Eval vm_compute in ltac:(run_template_program (tmQuoteRec rsouter) (fun q => let r := eval vm_compute in (rec_info q) in exact r)).
Section RSt.
#[local] Instance rst_recs : RecTypes | 0 :=
  {| RT := fun _ => rst;
     RO := fun _ => mkrops 2 (fun l => mkrst (nth 0 l 0%uint63) (nth 1 l 0%uint63)) (fun P v k => match v with mkrst a b => k [a; b] end);
     Rd := fun _ => mkrst 0%uint63 0%uint63 |}.
#[local] Instance rst_laws : RecLaws.
Proof. split; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] L; try discriminate; reflexivity]. Qed.
Definition rst_Pr := mkprog (funs_of 0 rst_src) [].
Time Lemma rsinner_ok : callee_ok rst_Pr (gid1 0) (cbz 0) (sig_at rst_src 0) rsinner.
Proof. Time exact_no_check (@compile_f_ok rst_recs rst_laws rst_Pr [] gid1 0 (sig_at rst_src 0) (body_at rst_src 0) eq_refl eq_refl (no_callees rst_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rsouter_ok : callee_ok rst_Pr (gid1 1) (cbz 1) (sig_at rst_src 1) rsouter.
Proof.
  Time exact_no_check (@compile_f_ok rst_recs rst_laws rst_Pr [existT ftype (sig_at rst_src 0) rsinner] gid1 1 (sig_at rst_src 1) (body_at rst_src 1)
    eq_refl eq_refl (all_ok_callees rst_Pr gid1 [existT ftype (sig_at rst_src 0) rsinner] (conj rsinner_ok Logic.I)) eq_refl eq_refl).
Time Qed.
End RSt.

(* ---------------------------------------------------------------- machine operations *)
(* hw_mmio's loop (KQR.v's [mmio]), a machine number and a block's size, a block grown: the trees KQR.v's tests write by hand *)
Fixpoint rmmio (fuel : nat) (i acc : i63) (s : mem) : i63 :=
  match fuel with
  | O => acc
  | S f => let a := PrimInt63.add 268435456 (PrimInt63.mul 4 (PrimInt63.land i 15)) in
           let s1 := KQ.KQRun.hw_store 4 a (PrimInt63.mul i 3) s in
           let s2 := KQ.KQRun.hw_fence 0 s1 in
           let s3 := KQ.KQRun.hw_load 4 a 3 0 s2 in
           rmmio f (PrimInt63.add i 1) (PrimInt63.add acc (KQ.KQRun.rd 3 0 s3)) s3
  end.
Definition rhsz (s : mem) : i63 := PrimInt63.add (KQ.KQRun.hw_addr 4) (KQ.KQRun.kq_size 3 s).
Definition rhgrow (n : i63) (s : mem) : mem := KQ.KQRun.kq_grow 2 n s.
Definition rhw (n : nat) (s : mem) : i63 := rmmio n (rhsz s) 0 (rhgrow 5 s).
Definition rhw_src := ltac:(run_template_program (tmQuoteRec rhw)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) rhw_src =
  [(mksig 1 [KNum; KNum] true false true None,
    FRecX (XRet (SVar 0))
      (XLet (SOp Badd (SInt 268435456) (SOp Bmul (SInt 4) (SOp Bland (SVar 1) (SInt 15))))
        (XLetM (MHw HStore (SCons (SInt 4) (SCons (SVar 0) (SCons (SOp Bmul (SVar 2) (SInt 3)) SNil))) MCur)
          (XLetM (MHw HFence (SCons (SInt 0) SNil) MCur)
            (XLetM (MHw HLoad (SCons (SInt 4) (SCons (SVar 0) (SCons (SInt 3) (SCons (SInt 0) SNil)))) MCur)
              (XRec CNil (SCons (SOp Badd (SVar 2) (SInt 1)) (SCons (SOp Badd (SVar 1) (SRd (SInt 3) (SInt 0))) SNil)) MCur))))));
   (mksig 1 [] true false true None,
    FPlainX (XCall 0 (CCons (CVar 0) CNil) (SCons (SOp Badd (SHwf FAddr (SCons (SInt 4) SNil)) (SSize (SInt 3))) (SCons (SInt 0) SNil))
               (MHw HGrow (SCons (SInt 2) (SCons (SInt 5) SNil)) MCur)))]).
Definition rhw_Pr := mkprog (funs_of 0 rhw_src) [].
Time Lemma rhw_ok0 : callee_ok rhw_Pr (gid1 0) (cbz 0) (sig_at rhw_src 0) rmmio.
Proof. Time exact_no_check (compile_f_ok rhw_Pr [] gid1 0 (sig_at rhw_src 0) (body_at rhw_src 0) eq_refl eq_refl (no_callees rhw_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rhw_ok1 : callee_ok rhw_Pr (gid1 1) (cbz 1) (sig_at rhw_src 1) rhw.
Proof.
  Time exact_no_check (compile_f_ok rhw_Pr [existT ftype (sig_at rhw_src 0) rmmio] gid1 1 (sig_at rhw_src 1) (body_at rhw_src 1) eq_refl eq_refl
    (all_ok_callees rhw_Pr gid1 [existT ftype (sig_at rhw_src 0) rmmio] (conj rhw_ok0 Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions rhw_ok1.

(* ---------------------------------------------------------------- functions given that name the caller's variables *)
(* [rcap] (loops' first line): the function given to [rfold] names the caller's number [b] and its memory [s]; [rfind] (its
   second line) gives [rfind_go] a test naming the caller's [lim] and [s]: each copy takes them as parameters (the captured
   numbers before the template's own, the memory last), the call passes them *)
Fixpoint rfold (k : nat) (i acc : i63) (body : i63 -> i63 -> i63) : i63 :=
  match k with O => acc | S k' => rfold k' (PrimInt63.add i 1) (body i acc) body end.
Fixpoint rfind_go (k : nat) (i hi : i63) (p : i63 -> bool) : i63 :=
  match k with O => hi | S k' => if p i then i else rfind_go k' (PrimInt63.add i 1) hi p end.
Definition rcap (lo hi lim : i63) (s : mem) : i63 :=
  let b := 3%uint63 in
  PrimInt63.add (rfold (KQ.KQRun.kq_nat (PrimInt63.sub hi lo)) lo 0 (fun i acc => PrimInt63.add acc (PrimInt63.mul (KQ.KQRun.rd 0 i s) b)))
                (rfind_go (KQ.KQRun.kq_nat (PrimInt63.sub hi lo)) lo hi (fun i => PrimInt63.ltb lim (KQ.KQRun.rd 0 i s))).
Definition rcap_res := ltac:(run_template_program (tmQuoteRec rcap)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition rcap_src := fst rcap_res.
Eval vm_compute in map (fun x => (snd (fst (fst x)), snd (fst x), snd x)) rcap_src.
Eval vm_compute in snd rcap_res.
MetaRocq Run (tmMkDefinition "rcap_c0"%bs (meaning_of (snd rcap_res) "rfold__c0"%bs)).
MetaRocq Run (tmMkDefinition "rcap_c1"%bs (meaning_of (snd rcap_res) "rfind_go__c1"%bs)).
Print rcap_c0.
Definition rcap_Pr := mkprog (funs_of 0 rcap_src) [].
Time Lemma rcap_ok0 : callee_ok rcap_Pr (gid1 0) (cbz 0) (sig_at rcap_src 0) rcap_c0.
Proof.
  Time exact_no_check (compile_f_okr rcap_Pr [] gid1 0 0 [KNum; KNum; KNum] true (fr0 (body_at rcap_src 0)) (fr1 (body_at rcap_src 0)) rcap_c0
    eq_refl eq_refl (no_callees rcap_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma rcap_ok1 : callee_ok rcap_Pr (gid1 1) (cbz 1) (sig_at rcap_src 1) rcap_c1.
Proof.
  Time exact_no_check (compile_f_okr rcap_Pr [existT ftype (sig_at rcap_src 0) rcap_c0] gid1 1 0 [KNum; KNum; KNum] true
    (fr0 (body_at rcap_src 1)) (fr1 (body_at rcap_src 1)) rcap_c1 eq_refl eq_refl
    (all_ok_callees rcap_Pr gid1 [existT ftype (sig_at rcap_src 0) rcap_c0] (conj rcap_ok0 Logic.I)) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma rcap_ok2 : callee_ok rcap_Pr (gid1 2) (cbz 2) (sig_at rcap_src 2) rcap.
Proof.
  Time exact_no_check (compile_f_ok rcap_Pr [existT ftype (sig_at rcap_src 0) rcap_c0; existT ftype (sig_at rcap_src 1) rcap_c1]
    gid1 2 (sig_at rcap_src 2) (body_at rcap_src 2) eq_refl eq_refl
    (all_ok_callees rcap_Pr gid1 [existT ftype (sig_at rcap_src 0) rcap_c0; existT ftype (sig_at rcap_src 1) rcap_c1]
       (conj rcap_ok0 (conj rcap_ok1 Logic.I))) eq_refl eq_refl).
Time Qed.
Print Assumptions rcap_ok2.

(* ---------------------------------------------------------------- records given back *)
(* pair_ret's text: a pair at the end of a loop, the function itself taken apart before the end, a loop taking both apart
   (a counter written as a budget) *)
Fixpoint rminmax (n : nat) (i lo hi : i63) (s : mem) : i63 * i63 :=
  match n with
  | O => (lo, hi)
  | S m => let x := KQ.KQRun.rd 0 i s in
           rminmax m (PrimInt63.add i 1) (if PrimInt63.ltb x lo then x else lo) (if PrimInt63.ltb hi x then x else hi) s
  end.
Fixpoint rfibp (n : nat) : i63 * i63 :=
  match n with
  | O => (0%uint63, 1%uint63)
  | S m => let '(a, b) := rfibp m in (b, PrimInt63.land (PrimInt63.add a b) 1048575)
  end.
Fixpoint rprounds (r n : nat) (acc : i63) (s : mem) : i63 :=
  match r with
  | O => acc
  | S r' => let '(lo, hi) := rminmax n (PrimInt63.land acc 255) 100000 (PrimInt63.sub 0 1) s in
            let '(fa, fb) := rfibp (KQ.KQRun.kq_nat 30) in
            rprounds r' n (PrimInt63.add (PrimInt63.add (PrimInt63.sub (PrimInt63.add acc hi) lo) fa) fb) s
  end.
Definition rpret (r n : nat) (s : mem) : i63 := rprounds r n 0%uint63 s.
Definition rpret_src := ltac:(run_template_program (tmQuoteRec rpret)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (snd (fst x), snd x)) rpret_src =
  [(mksig 1 [KNum; KNum; KNum] true false false (Some 0%nat),
    FRecR (BRet (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))))
      (BLet (SRd (SInt 0) (SVar 2)) (BRec CNil (SCons (SOp Badd (SVar 3) (SInt 1))
         (SCons (SIf Clt (SVar 0) (SVar 2) (SVar 0) (SVar 2)) (SCons (SIf Clt (SVar 1) (SVar 0) (SVar 0) (SVar 1)) SNil))))));
   (mksig 1 [] false false false (Some 0%nat),
    FRecR (BRet (RMk 0 (SCons (SInt 0) (SCons (SInt 1) SNil))))
      (BMatchRec CNil SNil (BRet (RMk 0 (SCons (SVar 0) (SCons (SOp Bland (SOp Badd (SVar 1) (SVar 0)) (SInt 1048575)) SNil))))));
   (mksig 2 [KNum] true false false None,
    FRec (SVar 0)
      (SMatchR (RCall 0 0 (CCons (CVar 1) CNil) (SCons (SOp Bland (SVar 0) (SInt 255)) (SCons (SInt 100000) (SCons (SOp Bsub (SInt 0) (SInt 1)) SNil))))
         (SMatchR (RCall 0 1 (CCons (CNat (SInt 30)) CNil) SNil)
            (SRec (CCons (CVar 1) CNil) (SCons (SOp Badd (SOp Badd (SOp Bsub (SOp Badd (SVar 4) (SVar 2)) (SVar 3)) (SVar 1)) (SVar 0)) SNil)))));
   (mksig 2 [] true false false None, FPlain (SCall 2 (CCons (CVar 1) (CCons (CVar 0) CNil)) (SCons (SInt 0) SNil)))]).
Section RPret.
#[local] Instance rpret_recs : RecTypes | 0 :=
  {| RT := fun _ => (i63 * i63)%type;
     RO := fun _ => mkrops 2 (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end);
     Rd := fun _ => (0%uint63, 0%uint63) |}.
#[local] Instance rpret_laws : RecLaws.
Proof. split; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] L; try discriminate; reflexivity]. Qed.
Definition rpret_Pr := mkprog (funs_of 0 rpret_src) [].
Time Lemma rminmax_ok : callee_ok rpret_Pr (gid1 0) (cbz 0) (sig_at rpret_src 0) rminmax.
Proof. Time exact_no_check (@compile_f_ok rpret_recs rpret_laws rpret_Pr [] gid1 0 (sig_at rpret_src 0) (body_at rpret_src 0) eq_refl eq_refl (no_callees rpret_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rfibp_ok : callee_ok rpret_Pr (gid1 1) (cbz 1) (sig_at rpret_src 1) rfibp.
Proof.
  Time exact_no_check (@compile_f_ok rpret_recs rpret_laws rpret_Pr [existT ftype (sig_at rpret_src 0) rminmax] gid1 1 (sig_at rpret_src 1) (body_at rpret_src 1)
    eq_refl eq_refl (all_ok_callees rpret_Pr gid1 [existT ftype (sig_at rpret_src 0) rminmax] (conj rminmax_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma rprounds_ok : callee_ok rpret_Pr (gid1 2) (cbz 2) (sig_at rpret_src 2) rprounds.
Proof.
  Time exact_no_check (@compile_f_ok rpret_recs rpret_laws rpret_Pr [existT ftype (sig_at rpret_src 0) rminmax; existT ftype (sig_at rpret_src 1) rfibp]
    gid1 2 (sig_at rpret_src 2) (body_at rpret_src 2) eq_refl eq_refl
    (all_ok_callees rpret_Pr gid1 [existT ftype (sig_at rpret_src 0) rminmax; existT ftype (sig_at rpret_src 1) rfibp] (conj rminmax_ok (conj rfibp_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions rprounds_ok.
End RPret.

(* rec_ret's text: a record of the program's own type given back at the end of a loop, bound by lets, read through its
   projections, its fields given to a second call *)
Record rspan := mkrspan { rlo : i63; rhi : i63 }.
Fixpoint rscan (n : nat) (i a b : i63) (s : mem) : rspan :=
  match n with
  | O => mkrspan a b
  | S m => let x := KQ.KQRun.rd 0 i s in
           rscan m (PrimInt63.add i 1) (if PrimInt63.ltb x a then x else a) (if PrimInt63.ltb b x then x else b) s
  end.
Fixpoint rrounds (r n : nat) (acc : i63) (s : mem) : i63 :=
  match r with
  | O => acc
  | S r' => let w := rscan n (PrimInt63.land acc 127) 100000 (PrimInt63.sub 0 1) s in
            let v := rscan n (PrimInt63.land acc 63) (rhi w) (rlo w) s in
            rrounds r' n (PrimInt63.add (PrimInt63.add (PrimInt63.sub (PrimInt63.add acc (rhi w)) (rlo w)) (PrimInt63.mul (rlo v) 3)) (rhi v)) s
  end.
Definition rrret (r n : nat) (s : mem) : i63 := rrounds r n 0%uint63 s.
Definition rrret_src := ltac:(run_template_program (tmQuoteRec rrret)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Eval vm_compute in map (fun x => (snd (fst x), snd x)) rrret_src.
Section RRret.
#[local] Instance rrret_recs : RecTypes | 0 :=
  {| RT := fun _ => rspan;
     RO := fun _ => mkrops 2 (fun l => mkrspan (nth 0 l 0%uint63) (nth 1 l 0%uint63)) (fun P v k => match v with mkrspan a b => k [a; b] end);
     Rd := fun _ => mkrspan 0%uint63 0%uint63 |}.
#[local] Instance rrret_laws : RecLaws.
Proof. split; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] L; try discriminate; reflexivity]. Qed.
Definition rrret_Pr := mkprog (funs_of 0 rrret_src) [].
Time Lemma rscan_ok : callee_ok rrret_Pr (gid1 0) (cbz 0) (sig_at rrret_src 0) rscan.
Proof. Time exact_no_check (@compile_f_ok rrret_recs rrret_laws rrret_Pr [] gid1 0 (sig_at rrret_src 0) (body_at rrret_src 0) eq_refl eq_refl (no_callees rrret_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rrounds_ok : callee_ok rrret_Pr (gid1 1) (cbz 1) (sig_at rrret_src 1) rrounds.
Proof.
  Time exact_no_check (@compile_f_ok rrret_recs rrret_laws rrret_Pr [existT ftype (sig_at rrret_src 0) rscan] gid1 1 (sig_at rrret_src 1) (body_at rrret_src 1)
    eq_refl eq_refl (all_ok_callees rrret_Pr gid1 [existT ftype (sig_at rrret_src 0) rscan] (conj rscan_ok Logic.I)) eq_refl eq_refl).
Time Qed.
End RRret.

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

(* ---------------------------------------------------------------- u64 (step 16) *)
(* w64's text: a hash loop over bytes and a generator over u64 values passed on and given back as they are, a helper written
   out under lets ([urmix]), comparisons as tests; and views' memory functions: a u64 bound by a let and its halves written
   ([urv_upd64]), a u64 read from two cells ([urv_rd64]) *)
Definition urfnv_off : KQ.KQRun.u64 := KQ.KQRun.u64_of_halves 3421674724 2216829733.
Definition urfnv_prime : KQ.KQRun.u64 := KQ.KQRun.u64_of_halves 256 435.
Definition urgolden : KQ.KQRun.u64 := KQ.KQRun.u64_of_halves 2654435769 2135587861.
Definition urm1 : KQ.KQRun.u64 := KQ.KQRun.u64_of_halves 3210233709 484763065.
Definition urm2 : KQ.KQRun.u64 := KQ.KQRun.u64_of_halves 2496678331 321982955.
Fixpoint urfnv (f : nat) (i n : i63) (h : KQ.KQRun.u64) (s : mem) : KQ.KQRun.u64 :=
  match f with
  | O => h
  | S f => if PrimInt63.leb n i then h
           else urfnv f (PrimInt63.add i 1) n (KQ.KQRun.u64_mul (KQ.KQRun.u64_xor h (KQ.KQRun.u64_of_int (PrimInt63.land (KQ.KQRun.rd 0 i s) 255))) urfnv_prime) s
  end.
Definition urmix (z0 : KQ.KQRun.u64) : KQ.KQRun.u64 :=
  let z1 := KQ.KQRun.u64_mul (KQ.KQRun.u64_xor z0 (KQ.KQRun.u64_shr z0 30)) urm1 in
  let z2 := KQ.KQRun.u64_mul (KQ.KQRun.u64_xor z1 (KQ.KQRun.u64_shr z1 27)) urm2 in
  KQ.KQRun.u64_xor z2 (KQ.KQRun.u64_shr z2 31).
Definition urrotl (a : KQ.KQRun.u64) (k : i63) : KQ.KQRun.u64 := KQ.KQRun.u64_or (KQ.KQRun.u64_shl a k) (KQ.KQRun.u64_shr a (PrimInt63.sub 64 k)).
Fixpoint urstream (f : nat) (st acc : KQ.KQRun.u64) (big : i63) : KQ.KQRun.u64 :=
  match f with
  | O => acc
  | S f => let st1 := KQ.KQRun.u64_add st urgolden in
           let z := urmix st1 in
           urstream f st1 (KQ.KQRun.u64_xor (urrotl acc 13) z) (if KQ.KQRun.u64_ltb (KQ.KQRun.u64_of_halves 2147483648 0) z then PrimInt63.add big 1 else big)
  end.
Definition urw64 (n : nat) (nz : i63) (s : mem) : i63 :=
  let h := urfnv n 0 nz urfnv_off s in
  let r := urstream n h urfnv_off 0 in
  PrimInt63.add (PrimInt63.add (PrimInt63.add (KQ.KQRun.u64_lo32 r) (PrimInt63.mul (KQ.KQRun.u64_hi32 r) 1000003))
    (if KQ.KQRun.u64_eqb h r then 7 else 0)) (KQ.KQRun.u64_to_int (KQ.KQRun.u64_shr h 40)).
Definition urw64_src := ltac:(run_template_program (tmQuoteRec urw64)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Eval vm_compute in map (fun x => (snd (fst x), snd x)) urw64_src.

Definition urv_upd64 (h i : i63) (v : KQ.KQRun.u64) (s : mem) : mem :=
  KQ.KQRun.upd32 h (PrimInt63.add (PrimInt63.mul 2 i) 1) (KQ.KQRun.u64_hi32 v) (KQ.KQRun.upd32 h (PrimInt63.mul 2 i) (KQ.KQRun.u64_lo32 v) s).
Definition urv_rd64 (h i : i63) (s : mem) : KQ.KQRun.u64 :=
  KQ.KQRun.u64_of_halves (KQ.KQRun.rd32 h (PrimInt63.add (PrimInt63.mul 2 i) 1) s) (KQ.KQRun.rd32 h (PrimInt63.mul 2 i) s).
Fixpoint urvfill (f : nat) (i n : i63) (s : mem) : mem :=
  match f with
  | O => s
  | S f => if PrimInt63.leb n i then s
           else urvfill f (PrimInt63.add i 1) n (urv_upd64 0 i (KQ.KQRun.u64_mul (KQ.KQRun.u64_of_int (PrimInt63.add i 1)) urgolden) s)
  end.
Fixpoint urvfold (f : nat) (i n : i63) (a : KQ.KQRun.u64) (s : mem) : KQ.KQRun.u64 :=
  match f with
  | O => a
  | S f => if PrimInt63.leb n i then a
           else urvfold f (PrimInt63.add i 1) n (KQ.KQRun.u64_xor (KQ.KQRun.u64_add a (urv_rd64 0 i s)) (KQ.KQRun.u64_shl a 1)) s
  end.
Definition urviews (n : nat) (nz : i63) (s : mem) : i63 :=
  let s1 := urvfill n 0 nz s in
  let r := urvfold n 0 nz (KQ.KQRun.u64_of_int 1) s1 in
  let s2 := urv_upd64 0 (PrimInt63.add nz 1) (KQ.KQRun.u64_of_int (PrimInt63.sub 0 123456789)) s1 in
  PrimInt63.add (PrimInt63.add (KQ.KQRun.u64_lo32 r) (PrimInt63.mul (KQ.KQRun.u64_hi32 r) 1000003))
    (KQ.KQRun.u64_to_int (urv_rd64 0 (PrimInt63.add nz 1) s2)).
Definition urviews_src := ltac:(run_template_program (tmQuoteRec urviews)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Eval vm_compute in map (fun x => (snd (fst x), snd x)) urviews_src.
Section RU64.
#[local] Instance ru64_recs : RecTypes | 0 :=
  {| RT := fun _ => KQ.KQRun.u64;
     RO := fun _ => mkrops 2 (fun l => KQ.KQRun.mk_u64 (nth 0 l 0%uint63) (nth 1 l 0%uint63))
                     (fun P v k => match v with KQ.KQRun.mk_u64 a b => k [a; b] end);
     Rd := fun _ => KQ.KQRun.mk_u64 0%uint63 0%uint63 |}.
#[local] Instance ru64_laws : RecLaws.
Proof. split; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] L; try discriminate; reflexivity]. Qed.
Definition urw64_Pr := mkprog (funs_of 0 urw64_src) [].
Time Lemma urfnv_ok : callee_ok urw64_Pr (gid1 0) (cbz 0) (sig_at urw64_src 0) urfnv.
Proof. Time exact_no_check (@compile_f_ok ru64_recs ru64_laws urw64_Pr [] gid1 0 (sig_at urw64_src 0) (body_at urw64_src 0) eq_refl eq_refl (no_callees urw64_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma urstream_ok : callee_ok urw64_Pr (gid1 1) (cbz 1) (sig_at urw64_src 1) urstream.
Proof.
  Time exact_no_check (@compile_f_ok ru64_recs ru64_laws urw64_Pr [existT ftype (sig_at urw64_src 0) urfnv] gid1 1 (sig_at urw64_src 1) (body_at urw64_src 1)
    eq_refl eq_refl (all_ok_callees urw64_Pr gid1 [existT ftype (sig_at urw64_src 0) urfnv] (conj urfnv_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma urw64_ok : callee_ok urw64_Pr (gid1 2) (cbz 2) (sig_at urw64_src 2) urw64.
Proof.
  Time exact_no_check (@compile_f_ok ru64_recs ru64_laws urw64_Pr [existT ftype (sig_at urw64_src 0) urfnv; existT ftype (sig_at urw64_src 1) urstream]
    gid1 2 (sig_at urw64_src 2) (body_at urw64_src 2) eq_refl eq_refl
    (all_ok_callees urw64_Pr gid1 [existT ftype (sig_at urw64_src 0) urfnv; existT ftype (sig_at urw64_src 1) urstream] (conj urfnv_ok (conj urstream_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Definition urviews_Pr := mkprog (funs_of 0 urviews_src) [].
Time Lemma urvfill_ok : callee_ok urviews_Pr (gid1 0) (cbz 0) (sig_at urviews_src 0) urvfill.
Proof. Time exact_no_check (@compile_f_ok ru64_recs ru64_laws urviews_Pr [] gid1 0 (sig_at urviews_src 0) (body_at urviews_src 0) eq_refl eq_refl (no_callees urviews_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma urvfold_ok : callee_ok urviews_Pr (gid1 1) (cbz 1) (sig_at urviews_src 1) urvfold.
Proof.
  Time exact_no_check (@compile_f_ok ru64_recs ru64_laws urviews_Pr [existT ftype (sig_at urviews_src 0) urvfill] gid1 1 (sig_at urviews_src 1) (body_at urviews_src 1)
    eq_refl eq_refl (all_ok_callees urviews_Pr gid1 [existT ftype (sig_at urviews_src 0) urvfill] (conj urvfill_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma urviews_ok : callee_ok urviews_Pr (gid1 2) (cbz 2) (sig_at urviews_src 2) urviews.
Proof.
  Time exact_no_check (@compile_f_ok ru64_recs ru64_laws urviews_Pr [existT ftype (sig_at urviews_src 0) urvfill; existT ftype (sig_at urviews_src 1) urvfold]
    gid1 2 (sig_at urviews_src 2) (body_at urviews_src 2) eq_refl eq_refl
    (all_ok_callees urviews_Pr gid1 [existT ftype (sig_at urviews_src 0) urvfill; existT ftype (sig_at urviews_src 1) urvfold] (conj urvfill_ok (conj urvfold_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions urviews_ok.
End RU64.

(* ---------------------------------------------------------------- mutual recursion (step 17) *)
(* mutual's text: two functions of one Fixpoint calling each other on the counter's predecessor, read as one function with a
   selector counter (its meaning blk of the fixpoint's own bodies, its theorem compile_f_okr's) and the member called as one
   call of it *)
Fixpoint qping (n : nat) (a b : i63) (s : mem) : i63 :=
  match n with
  | O => a
  | S m => qpong m (PrimInt63.add a (KQ.KQRun.rd 0 (PrimInt63.land b 1023) s)) (PrimInt63.add b 3) s
  end
with qpong (n : nat) (a b : i63) (s : mem) : i63 :=
  match n with
  | O => PrimInt63.add a b
  | S m => if PrimInt63.eqb (PrimInt63.land a 1) 0 then qping m (PrimInt63.land (PrimInt63.mul a 3) 65535) (PrimInt63.add b 1) s
           else qpong m (PrimInt63.add a 5) (PrimInt63.add b 2) s
  end.
Fixpoint qrounds (r n : nat) (acc : i63) (s : mem) : i63 :=
  match r with
  | O => acc
  | S r' => qrounds r' n (PrimInt63.add acc (qping n acc 0 s)) s
  end.
Definition qmut_res := ltac:(run_template_program (tmQuoteRec qrounds)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition qmut_src := fst qmut_res.
Eval vm_compute in map (fun x => (snd (fst (fst x)), snd (fst x), snd x)) qmut_src.
MetaRocq Run (tmMkDefinition "qblk"%bs (meaning_of (snd qmut_res) "qping__cblk"%bs)).
Definition qmut_Pr := mkprog (funs_of 0 qmut_src) [].
Time Lemma qblk_ok : callee_ok qmut_Pr (gid1 0) (cbz 0) (sig_at qmut_src 0) qblk.
Proof.
  Time exact_no_check (compile_f_okr qmut_Pr [] gid1 0 1 (nk 2) true (fr0 (body_at qmut_src 0)) (fr1 (body_at qmut_src 0)) qblk
    eq_refl eq_refl (no_callees qmut_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma qping_ok : callee_ok qmut_Pr (gid1 1) (cbz 1) (sig_at qmut_src 1) qping.
Proof.
  Time exact_no_check (compile_f_ok qmut_Pr [existT ftype (sig_at qmut_src 0) qblk] gid1 1 (sig_at qmut_src 1) (body_at qmut_src 1)
    eq_refl eq_refl (all_ok_callees qmut_Pr gid1 [existT ftype (sig_at qmut_src 0) qblk] (conj qblk_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma qrounds_ok : callee_ok qmut_Pr (gid1 2) (cbz 2) (sig_at qmut_src 2) qrounds.
Proof.
  Time exact_no_check (compile_f_ok qmut_Pr [existT ftype (sig_at qmut_src 0) qblk; existT ftype (sig_at qmut_src 1) qping] gid1 2
    (sig_at qmut_src 2) (body_at qmut_src 2) eq_refl eq_refl
    (all_ok_callees qmut_Pr gid1 [existT ftype (sig_at qmut_src 0) qblk; existT ftype (sig_at qmut_src 1) qping] (conj qblk_ok (conj qping_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions qrounds_ok.

(* ---------------------------------------------------------------- record types from the bodies (step 19) *)
(* a pair built and taken apart inside a body (the construct table's N_nest shape), its type in no signature: the record
   table takes it from the body *)
Definition rbp (a b : i63) : i63 := PrimInt63.mul (let '(p, q) := (PrimInt63.add a b, b) in PrimInt63.sub p q) 3.
Definition rbp_src := ltac:(run_template_program (tmQuoteRec rbp)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) rbp_src =
  [FPlain (SOp Bmul (SMatchR (RMk 0 (SCons (SOp Badd (SVar 1) (SVar 0)) (SCons (SVar 0) SNil))) (SOp Bsub (SVar 1) (SVar 0))) (SInt 3))]).
Eval vm_compute in ltac:(run_template_program (tmQuoteRec rbp) (fun q => let r := eval vm_compute in (rec_info q) in exact r)).
Section RBP.
#[local] Instance rbp_recs : RecTypes | 0 :=
  {| RT := fun _ => (i63 * i63)%type;
     RO := fun _ => mkrops 2 (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end);
     Rd := fun _ => (0%uint63, 0%uint63) |}.
#[local] Instance rbp_laws : RecLaws.
Proof. split; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] L; try discriminate; reflexivity]. Qed.
Definition rbp_Pr := mkprog (funs_of 0 rbp_src) [].
Time Lemma rbp_ok : callee_ok rbp_Pr (gid1 0) (cbz 0) (sig_at rbp_src 0) rbp.
Proof.
  Time exact_no_check (@compile_f_ok rbp_recs rbp_laws rbp_Pr [] gid1 0 (sig_at rbp_src 0) (body_at rbp_src 0) eq_refl eq_refl
    (no_callees rbp_Pr gid1) eq_refl eq_refl).
Time Qed.
End RBP.
