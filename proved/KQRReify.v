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
From Corelib Require Program.Wf.
From Stdlib Require Sint63.
From Corelib Require Numbers.Cyclic.Int63.CarryType.
Import MonadNotation ListNotations.

Definition kn_of (t : term) : kername := match t with tConst kn _ => kn | _ => (MPfile [], ""%bs) end.
Definition ind_of (t : term) : inductive :=
  match t with tInd i _ => i | _ => {| inductive_mind := (MPfile [], ""%bs); inductive_ind := 0 |} end.
Definition eq_mp (a b : modpath) : bool := match ModPathComp.compare a b with Eq => true | _ => false end.
(** the file a module path stands in; a file of Rocq's libraries, of MetaRocq, or of this compiler and its kit: every other file
    is the program's (step 51) -- [KQ.lib]'s files are a user's libraries like any other *)
Fixpoint mp_file (m : modpath) : dirpath :=
  match m with MPfile d => d | MPbound d _ _ => d | MPdot m' _ => mp_file m' end.
Definition lib_file (d : dirpath) : bool :=
  match rev d with
  | r :: rest =>
      if String.eqb r "Corelib" then true else if String.eqb r "Stdlib" then true
      else if String.eqb r "MetaRocq" then true else if String.eqb r "Ltac2" then true
      else if String.eqb r "KQC" then true
      else if String.eqb r "Equations" then true
      else if String.eqb r "KQ" then match rest with x :: _ => negb (String.eqb x "lib") | [] => true end
      else false
  | [] => false
  end.
Fixpoint lib_file_of (m : modpath) : string :=
  match m with
  | MPfile (x :: _) => x
  | MPdot m' _ => lib_file_of m'
  | _ => ""%bs
  end.
Definition lib_open (kn : kername) : bool :=
  let f := lib_file_of (fst kn) in
  (* a definition the readers do not know as an operation *)
  if existsb (String.eqb f) ["Bool"%bs; "Uint63"%bs; "Uint63Axioms"%bs; "Sint63"%bs; "Sint63Axioms"%bs] then true
  else if String.eqb f "Datatypes"%bs then existsb (String.eqb (snd kn)) ["xorb"%bs; "implb"%bs; "nat_rect"%bs; "nat_rec"%bs; "nat_ind"%bs;
    "bool_rect"%bs; "bool_rec"%bs; "bool_ind"%bs; "prod_rect"%bs; "prod_rec"%bs; "prod_ind"%bs; "option_rect"%bs; "option_rec"%bs; "option_map"%bs;
    "sum_rect"%bs; "sum_rec"%bs; "unit_rect"%bs; "unit_rec"%bs; "prod_curry"%bs; "prod_uncurry"%bs]
  else if String.eqb f "Logic"%bs then existsb (String.eqb (snd kn)) ["eq_rect"%bs; "eq_rec"%bs; "eq_ind"%bs; "eq_rect_r"%bs; "eq_rec_r"%bs]
  else if String.eqb f "Nat"%bs then existsb (String.eqb (snd kn)) ["iter"%bs; "even"%bs; "odd"%bs; "double"%bs; "succ"%bs; "b2n"%bs; "square"%bs; "shiftr"%bs; "one"%bs; "zero"%bs; "two"%bs]
  else if String.eqb f "PeanoNat"%bs then String.eqb (snd kn) "b2n"%bs
  else if String.eqb f "Specif"%bs then existsb (String.eqb (snd kn)) ["proj1_sig"%bs; "sumbool_rect"%bs; "sumbool_rec"%bs]
  else false.
(** a constant of the program: of the root's module first (the common case, one comparison), else of any file not a library's
    (step 51: a nested module, another of the program's files).  Whatever it lets in is still checked: the meaning of what is
    read is compared with the function by the kernel *)
Definition in_prog (mp m : modpath) : bool := if eq_mp m mp then true else negb (lib_file (mp_file m)).
(** the name of a function made by the reifier, a definition of the file that reads the program: its kernel name in one
    identifier, so that two functions of one short name in two modules or files have two of them ([.] as ['_], ['] as ['']) *)
Fixpoint mangle_go (s : string) : string :=
  match s with
  | String.EmptyString => String.EmptyString
  | String.String c r =>
      if Byte.eqb c "."%byte then String.String "'"%byte (String.String "_"%byte (mangle_go r))
      else if Byte.eqb c "'"%byte then String.String "'"%byte (String.String "'"%byte (mangle_go r))
      else String.String c (mangle_go r)
  end.
Definition mangle (kn : kername) : string := mangle_go (string_of_kername kn).
Definition copy_mp : modpath := MPfile ["kqcopy"%bs].
(** a function's name in what kitc.py writes: the kernel's full name, which no later name can shadow; one the reifier made, its name *)
Definition fn_text (kn : kername) : string := if eq_mp (fst kn) copy_mp then snd kn else string_of_kername kn.

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
(* a local [fix] applied is read as a call of this name with the fixpoint first; the call look-up gives the fixpoint's copy
   (step 31).  Not a constant of any program: a call of it that has no copy is refused *)
Definition kn_lfix : kername := (MPfile ["kqlfix"%bs], "kqlfix"%bs).
(* the comparisons and the predecessor of counters (step 30) *)
Definition kn_nat_eqb := kn_of <% Nat.eqb %>.
Definition kn_nat_ltb := kn_of <% Nat.ltb %>.
Definition kn_nat_leb := kn_of <% Nat.leb %>.
Definition kn_nat_pred := kn_of <% Nat.pred %>.
Definition kn_nat_add := kn_of <% Nat.add %>.   (* a sum of counters (step 33) *)
Definition kn_c_min := kn_of <% Nat.min %>.
Definition kn_c_max := kn_of <% Nat.max %>.
Definition kn_c_sub := kn_of <% Nat.sub %>.
Definition kn_c_div2 := kn_of <% Nat.div2 %>.
(* (step 70) *)
Definition kn_c_mul := kn_of <% Nat.mul %>.
Definition kn_c_div := kn_of <% Nat.div %>.
Definition kn_c_mod := kn_of <% Nat.modulo %>.
Definition kn_c_even := kn_of <% Nat.even %>.
Definition kn_c_odd := kn_of <% Nat.odd %>.
Definition kn_c_pow := kn_of <% Nat.pow %>.
Definition kn_zton := kn_of <% Z.to_nat %>.
Definition kn_zofn := kn_of <% Z.of_nat %>.
Definition kn_s2z := kn_of <% Sint63.to_Z %>.
Definition kn_u2z := kn_of <% Uint63.to_Z %>.
Definition kn_ofz := kn_of <% Uint63.of_Z %>.
Definition ncmp_v (kn : kername) : option cmpop :=
  if Kername.eqb kn kn_nat_eqb then Some Ceq else if Kername.eqb kn kn_nat_ltb then Some Clt
  else if Kername.eqb kn kn_nat_leb then Some Cle else None.
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
Inductive cent := CNum | CMem | CDead | CCnt | CPred | CSelf | CBool | CFn (p : nat) (t : term) | CRec | CSib (j : nat)
  | CCntP (j : nat) | CSelfP (perm : list nat) | CRecT (t : term) | CDeadM | CRecB.
(* CRecB (step 67): a record variable holding a boolean, a value of the entry of bool *)
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

Definition is_cnt (c : cent) : bool := match c with CCnt | CPred | CCntP _ => true | _ => false end.
(* a parameter counter of a function whose parameters are in another order (step 41): its index among the parameter counters
   given, the local counters (lets, predecessors) counted before it *)
Definition is_lcnt (c : cent) : bool := match c with CCnt | CPred => true | _ => false end.

(** the syntax index of the counter at place [i] of the context: the counters nearer than it *)
Fixpoint cnt_index (ctx : list cent) (i : nat) : option nat :=
  match ctx, i with
  | CCntP j :: _, O => Some j
  | c :: _, O => if is_cnt c then Some O else None
  | c :: r, S i => option_map (fun j => if is_lcnt c then S j else j) (cnt_index r i)
  | [], _ => None
  end.

(** the syntax index of the record at place [i] of the context: the records nearer than it *)
Fixpoint rec_index (ctx : list cent) (i : nat) : option nat :=
  match ctx, i with
  | CRec :: _, O | CRecB :: _, O => Some O
  | _ :: _, O => None
  | c :: r, S i => option_map (fun j => match c with CRec | CRecB => S j | _ => j end) (rec_index r i)
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
  | Some CMem, CMem | Some CCnt, CCnt | Some CPred, CPred | Some CSelf, CSelf | Some (CSelfP _), CSelf => true
  | _, _ => false
  end.

(** the arguments of a recursive call in the order the syntax takes (step 41): the user's, put in that order *)
Fixpoint to_sexps (l : list sexp) : sexps := match l with [] => SNil | e :: l => SCons e (to_sexps l) end.
Fixpoint to_sexps_r (l : list srec) : sexps := match l with [] => SNil | x :: l => SConsR x (to_sexps_r l) end.
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
Fixpoint has_lfix (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tFix _ _ => true
      | tApp f args => has_lfix fuel f || existsb (has_lfix fuel) args
      | tLambda _ ty b | tProd _ ty b => has_lfix fuel b
      | tLetIn _ b ty body => has_lfix fuel b || has_lfix fuel body
      | tCase _ p c brs => has_lfix fuel c || existsb (fun br => has_lfix fuel (bbody br)) brs
      | _ => false
      end
  end.
(** a definition's body has a local fixpoint: inside a lambda, a let, a match -- or inside a fixpoint's own bodies *)
Definition lfix_body (b : term) : bool :=
  match b with tFix mfix _ => existsb (fun d => has_lfix 100000 (dbody d)) mfix | _ => has_lfix 100000 b end.
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

(** (step 70) the number a counter written as [O] / [S ..] is; a [Z] written in the program *)
Fixpoint cnt_val (t : term) : nat :=
  match t with tApp (tConstruct _ 1 _) [c] => S (cnt_val c) | _ => O end.
Fixpoint cnt_term (n : nat) : scnt := match n with O => CO | S m => CS (cnt_term m) end.
Fixpoint pos_lit (t : term) : option positive :=
  match t with
  | tConstruct i 2 _ => if String.eqb (snd (inductive_mind i)) "positive"%bs then Some xH else None
  | tApp (tConstruct i 0 _) [p] => if String.eqb (snd (inductive_mind i)) "positive"%bs then option_map xI (pos_lit p) else None
  | tApp (tConstruct i 1 _) [p] => if String.eqb (snd (inductive_mind i)) "positive"%bs then option_map xO (pos_lit p) else None
  | _ => None
  end.
Definition z_lit (t : term) : option Z :=
  match t with
  | tConstruct i 0 _ => if String.eqb (snd (inductive_mind i)) "Z"%bs then Some 0%Z else None
  | tApp (tConstruct i 1 _) [p] => if String.eqb (snd (inductive_mind i)) "Z"%bs then option_map Zpos (pos_lit p) else None
  | tApp (tConstruct i 2 _) [p] => if String.eqb (snd (inductive_mind i)) "Z"%bs then option_map Zneg (pos_lit p) else None
  | _ => None
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
      (* a let before the next parameter, as a section's [Let] leaves it (step 51) *)
      | tLetIn na e ty body, _ :: _ => tLetIn na e ty (wout_go fuel body (map (lift0 1) args))
      | _, [] => b
      | _, _ => mkApps b args
      end
  end.
Fixpoint spine_lets (t : term) : nat :=
  match t with tLambda _ _ b => spine_lets b | tLetIn _ _ _ b => S (spine_lets b) | _ => O end.
Definition wout (b : term) (args : list term) : term := wout_go (S (length args + spine_lets b)) b args.

(** a match on a counter written as [O] / [S c] takes its branch (the kernel's check: iota) *)
Definition known_branch (c : term) (b0 b1 : branch term) : option term :=
  match c with
  | tConstruct _ 0 _ => Some (bbody b0)
  | tApp (tConstruct _ 1 _) [c'] => Some (subst [c'] 0 (bbody b1))
  | _ => None
  end.
(** a match on a counter that is not a variable (step 35): the same term up to zeta as a let of the counter and a match on the
    variable the let binds; its bound is the let's *)
Definition let_scrut (ci : case_info) (p : predicate term) (c : term) (b0 b1 : branch term) : term :=
  tLetIn {| binder_name := nAnon; binder_relevance := Relevant |} c (tInd ind_nat [])
    (tCase ci (map_predicate_k id (fun k => lift 1 k) 0 p) (tRel 0)
       [{| bcontext := bcontext b0; bbody := lift 1 0 (bbody b0) |}; {| bcontext := bcontext b1; bbody := lift 1 1 (bbody b1) |}]).

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
Definition cap_ok (c : cent) : bool := match c with CNum | CBool | CMem | CCnt | CRecT _ => true | _ => false end.
(* a captured counter (step 42): one of the copy's counters, after the template's *)
Definition is_capc (c : cent) : bool := match c with CCnt => true | _ => false end.
Definition capk_eqb (a b : list cent) : bool :=
  Nat.eqb (length a) (length b)
  && forallb (fun q => match q with (CNum, CNum) | (CBool, CBool) | (CMem, CMem) => true | _ => false end) (combine a b).
(** a copy's captured variables: the entries of its context after CSelf, the first captured the deepest *)
Fixpoint after_self (ctx : list cent) : list cent := match ctx with [] => [] | CSelf :: r | CSelfP _ :: r => r | _ :: r => after_self r end.
(** a function given, written out in a copy's context: its captured variables are the copy's entries for them *)
Definition capsub (ctx : list cent) (t : term) : term :=
  match after_self ctx with
  | [] => t
  | cs => subst (map (fun k => tRel (length ctx - 1 - k)) (seq 0 (length cs))) 0 t
  end.
(** a function parameter of a copy, given on to another template, is the function it is bound to (step 27) *)
Definition fsub (ctx : list cent) (a : term) : term :=
  match a with tRel i => match nth_error ctx i with Some (CFn _ t) => capsub ctx t | _ => a end | _ => a end.

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
      (* a fixpoint (step 31: a local fixpoint is the key of its copy) *)
      | tFix m k, tFix m' k' =>
          Nat.eqb k k' && Nat.eqb (length m) (length m')
          && forallb (fun q => Nat.eqb (rarg (fst q)) (rarg (snd q)) && teq fuel (dtype (fst q)) (dtype (snd q))
                               && teq fuel (dbody (fst q)) (dbody (snd q))) (combine m m')
      | tSort _, tSort _ => true
      | _, _ => false
      end
  end.
(** every variable that is the newest memory as one variable: two memory parameters that are the same memory (step 53) *)
Fixpoint first_mem (ctx : list cent) (i : nat) : nat :=
  match ctx with [] => i | CMem :: _ => i | _ :: r => first_mem r (S i) end.
Fixpoint alias_norm (fuel : nat) (ctx : list cent) (m0 d : nat) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tRel i => if (if Nat.leb d i then is_ent CMem ctx (i - d) else false) then tRel (d + m0) else t
      | tApp f args => tApp (alias_norm fuel ctx m0 d f) (map (alias_norm fuel ctx m0 d) args)
      | tLetIn na b ty body => tLetIn na (alias_norm fuel ctx m0 d b) ty (alias_norm fuel ctx m0 (S d) body)
      | tLambda na ty b => tLambda na ty (alias_norm fuel ctx m0 (S d) b)
      | tCase ci p c brs =>
          tCase ci p (alias_norm fuel ctx m0 d c)
                (map (fun br => {| bcontext := bcontext br; bbody := alias_norm fuel ctx m0 (d + length (bcontext br)) (bbody br) |}) brs)
      | _ => t
      end
  end.
Definition teqs (l l' : list term) : bool :=
  Nat.eqb (length l) (length l') && forallb (fun q => teq 1000 (fst q) (snd q)) (combine l l').
(** the arguments of a recursive call in the syntax's order, read with its parameters so (step 41).  A memory parameter left out of that
    order (step 53): given the same memory as the one kept, or, one never read, itself *)
Definition self_perm (ctx : list cent) (fi : nat) (args : list term) : list term :=
  match nth_error ctx fi with
  | Some (CSelfP perm) =>
      let l := map (fun i => nth i args (tRel 0)) perm in
      if Nat.eqb (length perm) (length args) then l else
      let norm := alias_norm 1000 ctx (first_mem ctx 0) 0 in
      let m := norm (last l (tRel 0)) in
      if forallb (fun p => if existsb (Nat.eqb p) perm then true else
                           match nth_error ctx (fi - 1 - p) with
                           | Some CDeadM => match nth p args (tRel 0) with tRel i => Nat.eqb i (fi - 1 - p) | _ => false end
                           | _ => teq 1000 (norm (nth p args (tRel 0))) m
                           end) (seq 0 (length args)) then l else []
  | _ => args
  end.


(** a record type of numbers (§12.V step 12): an inductive with one constructor, whose fields are numbers or parameters that
    are numbers ([prod int int]); an entry of the program's record table: its type, its inductive, its number of fields, its
    parameters *)
Definition rentry := ((list (list (bool * nat)) * list term) * term * inductive * nat * list term * option (list nat) * list nat)%type.
(* (step 67) beside the field types: empty for a record or a data type of numbers (or records of numbers); not empty for a value holding a
   boolean or a data type: a record's one empty list, a data type's fields' slots by constructor, (true, s) number slot s, (false, s)
   record slot s; its "field types" are then its slots' types, its widths theirs *)
(* the first part (step 43): a record's field types, its parameters put in; empty for a data type *)
(* the last part: each field's width in the flat record -- 1 for a number, a record's own width for a record field (step 32);
   empty for a data type *)
(** (step 67) a data type holding other than numbers: its fields in slots, the same for every constructor: number slots, then record
    slots each of one type.  A number its place among its constructor's numbers; another field its type's next slot this constructor
    has not used, a new one if none *)
Fixpoint slot_find (q : term) (J : list term) (used : list nat) (s : nat) : option nat :=
  match J with
  | [] => None
  | u :: r => if (if teq 1000 q u then negb (existsb (Nat.eqb s) used) else false) then Some s else slot_find q r used (S s)
  end.
Definition ctor_slots (J : list term) (fts : list term) : list term * list (bool * nat) :=
  let '(J', _, _, m) := fold_left (fun st q =>
       let '(J0, used, nn, m0) := st in
       if is_ty kn_int q then (J0, used, S nn, m0 ++ [(true, nn)])
       else match slot_find q J0 used 0 with
            | Some s => (J0, s :: used, nn, m0 ++ [(false, s)])
            | None => (J0 ++ [q], length J0 :: used, nn, m0 ++ [(false, length J0)])
            end) fts (J, ([] : list nat), O, ([] : list (bool * nat))) in
  (J', m).
Fixpoint rec_shape_go (fuel : nat) (Σ : global_env) (t : term) : option rentry :=
  match fuel with
  | O => None
  | S fuel =>
  let '(h, ps) := match t with tApp (tInd i _) ps => (Some i, ps) | tInd i _ => (Some i, []) | _ => (None, []) end in
  (* a record of numbers, or one holding records of numbers (step 32): its width *)
  let recw (q : term) : option nat := if is_ty kn_int q then Some 1 else if is_bool q then Some 1
                                      else match rec_shape_go fuel Σ q with
                                           | Some (_, _, _, n, _, _, _) => Some n
                                           | _ => None end in
  (* (step 67) a field not free as numbers: a boolean, a data type, one of no number, or a record holding one *)
  let gen_q (q : term) : bool := if is_ty kn_int q then false else if is_bool q then true
                                 else match rec_shape_go fuel Σ q with
                                      | Some (mf, _, _, n, _, g, _) =>
                                          match fst mf, g with
                                          | [], None => negb (Nat.ltb 0 n)
                                          | _, _ => true
                                          end
                                      | None => false end in
  match h with
  | Some i =>
      match lookup_env Σ (inductive_mind i) with
      | Some (InductiveDecl mib) =>
          match ind_bodies mib with
          | [oib] =>
              match ind_ctors oib with
              | [cb] =>
                  let args := rev (cstr_args cb) in
                  let np := ind_npars mib in
                  (* each field a number, a parameter (a number or a record), or a record type of its own *)
                  let wd (jd : nat * context_decl) : option nat :=
                    match decl_type (snd jd) with
                    | tRel k => if Nat.leb (fst jd) k && Nat.ltb k (fst jd + np) then recw (nth (np - 1 - (k - fst jd)) ps (tRel 0)) else None
                    | ty => recw ty
                    end in
                  match opt_all (map wd (combine (seq 0 (length args)) args)) with
                  | Some fw =>
                      if Nat.eqb (length ps) np && forallb (fun q => match recw q with Some _ => true | None => false end) ps
                         && Nat.eqb (inductive_ind i) 0
                      then let fts := map (fun jd => match decl_type (snd jd) with
                                                | tRel k => nth (np - 1 - (k - fst jd)) ps (tRel 0) | ty => ty end)
                                     (combine (seq 0 (length args)) args) in
                           Some ((if existsb gen_q fts then [[]] else [], fts), t, i, fold_left Nat.add fw 0, ps, None, fw) else None
                  | None => None
                  end
              | cb0 :: _ :: _ =>
                  (* several constructors, each carrying numbers: held as its tag and its fields (step 28); not bool *)
                  let cbs := ind_ctors oib in
                  (* each field a number or one of the parameters (not an earlier field, not the type itself) *)
                  let fok := forallb (fun cb => let args := rev (cstr_args cb) in
                               forallb (fun jd => is_ty kn_int (decl_type (snd jd))
                                                  || match decl_type (snd jd) with
                                                     | tRel k => Nat.leb (fst jd) k && Nat.ltb k (fst jd + ind_npars mib) | _ => false end)
                                       (combine (seq 0 (length args)) args)) cbs in
                  let ws := map (fun cb => length (cstr_args cb)) cbs in
                  if Nat.eqb (length ps) (ind_npars mib) && forallb (is_ty kn_int) ps && Nat.eqb (inductive_ind i) 0 && fok
                     && negb (Kername.eqb (inductive_mind i) (inductive_mind ind_bool)) && negb (Kername.eqb (inductive_mind i) (inductive_mind ind_nat))
                  then Some (([], []), t, i, S (fold_left Nat.max ws O), ps, Some ws, [])
                  else if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then None
                  else if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then None
                  else
                  (* (step 67) a data type holding other than numbers: its tag, its number slots, its record slots *)
                  let np := ind_npars mib in
                  let ftys := fun cb => let args := rev (cstr_args cb) in
                     map (fun jd => match decl_type (snd jd) with
                                    | tRel k => if Nat.leb (fst jd) k && Nat.ltb k (fst jd + np) then nth (np - 1 - (k - fst jd)) ps (tRel 0) else tVar "dep"%bs
                                    | ty => ty end) (combine (seq 0 (length args)) args) in
                  let '(J, maps) := fold_left (fun st cb => let '(J0, ms) := ctor_slots (fst st) (ftys cb) in (J0, snd st ++ [ms])) cbs (([] : list term), ([] : list (list (bool * nat)))) in
                  let nsl := map (fun m => length (filter (fun p : bool * nat => fst p) m)) maps in
                  let N := fold_left Nat.max nsl O in
                  match opt_all (map recw J) with
                  | Some jw =>
                      if Nat.eqb (length ps) (ind_npars mib) && forallb (fun q => match recw q with Some _ => true | None => false end) ps && Nat.eqb (inductive_ind i) 0
                         && negb (match J with [] => true | _ => false end)
                      then Some ((maps, repeat (tConst kn_int []) N ++ J), t, i, S (N + fold_left Nat.add jw O), ps, Some nsl, repeat 1 N ++ jw)
                      else None
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | None => None
  end
  end.
Definition rec_shape (Σ : global_env) (t : term) : option rentry := rec_shape_go 10 Σ t.
(** (step 67) the entry of [bool] as a field: its one number; marked, so that everywhere else a boolean stays a boolean *)
Definition bool_entry : rentry := (([[]], []), tVar "kq_bool"%bs, ind_bool, 1, [], Some [], []).
(** a record type's constructor and its fields' types, its parameters put in (step 32) *)
Definition rfields (Σ : global_env) (t : term) : option (ident * list term) :=
  let '(h, ps) := match t with tApp (tInd i _) ps => (Some i, ps) | tInd i _ => (Some i, []) | _ => (None, []) end in
  match h with
  | Some i =>
      match lookup_env Σ (inductive_mind i) with
      | Some (InductiveDecl mib) =>
          match ind_bodies mib with
          | [oib] => match ind_ctors oib with
                     | [cb] => let args := rev (cstr_args cb) in let np := ind_npars mib in
                               Some (cstr_name cb, map (fun jd => match decl_type (snd jd) with
                                                                  | tRel k => nth (np - 1 - (k - fst jd)) ps (tRel 0) | ty => ty end)
                                                       (combine (seq 0 (length args)) args))
                     | _ => None end
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.
(** the index of a record type in the table, and of the record a constructor applied to these arguments builds (with its
    number of parameters) *)
Fixpoint rindex (t : term) (rt : list rentry) (i : nat) : option nat :=
  match rt with [] => None | (_, u, _, _, _, _, _) :: r => if teq 1000 t u then Some i else rindex t r (S i) end.
Fixpoint cindex (ind : inductive) (c : nat) (args : list term) (rt : list rentry) (i : nat) : option (nat * nat * option (nat * nat)) :=
  match rt with
  | [] => None
  | (_, _, j, n, qs, g, fw) :: r =>
      if Kername.eqb (inductive_mind ind) (inductive_mind j) && Nat.eqb (inductive_ind ind) (inductive_ind j)
         && teqs (firstn (length qs) args) qs
      then match g with
           | None => if Nat.eqb c 0 && Nat.eqb (length args) (length qs + length fw) then Some (i, length qs, None) else None
           (* a data type (step 28): constructor [c]'s fields, after its number, then zeros up to the widest *)
           | Some ws => if Nat.ltb c (length ws) && Nat.eqb (length args) (length qs + nth c ws O)
                        then Some (i, length qs, Some (c, Nat.pred n - nth c ws O)) else None
           end
      else cindex ind c args r (S i)
  end.

(** (step 67) the index of a field's type, a boolean's its entry's *)
Fixpoint rbool (rt : list rentry) (i : nat) : option nat :=
  match rt with
  | [] => None
  | (_, _, j, _, _, _, _) :: r => if Kername.eqb (inductive_mind j) (inductive_mind ind_bool) then Some i else rbool r (S i)
  end.
Definition rindex_f (q : term) (rt : list rentry) : option nat := if is_bool q then rbool rt 0 else rindex q rt 0.
(** the index of a record type and number of fields, without parameters, by its inductive (a primitive projection names it) *)
Fixpoint rind (ind : inductive) (rt : list rentry) (i : nat) : option (nat * nat) :=
  match rt with
  | [] => None
  | (_, _, j, n, qs, _, _) :: r =>
      if Kername.eqb (inductive_mind ind) (inductive_mind j) && Nat.eqb (inductive_ind ind) (inductive_ind j) && Nat.eqb (length qs) 0
      then Some (i, n) else rind ind r (S i)
  end.

(** a let read by zeta (step 20): a let binding a function, or one whose variable its body does not name, is its body with
    the binding put in -- the same term up to zeta, as a helper written out is up to delta and beta *)
Definition zeta_head (t : term) : option term :=
  match t with
  | tLetIn _ b ty body => if fun_or_type ty || noccur_between 0 1 body then Some (subst [b] 0 body) else None
  | _ => None
  end.

(** a match on a pair built in place (step 23): its branch with the two parts bound by lets -- the same term up to iota and
    zeta; the parts' types the pair's parameters (a number, a memory, ...), as the readers of lets ask *)
Definition ind_prod := ind_of <% prod %>.
Definition iota_pair (ci : case_info) (p : predicate term) (c : term) (br : branch term) : option term :=
  if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_prod) && Nat.eqb (length (bcontext br)) 2 then
    match c, pparams p with
    | tApp (tConstruct _ 0 _) [_; _; a; b], [A; B] =>
        Some (tLetIn {| binder_name := nAnon; binder_relevance := Relevant |} a A
               (tLetIn {| binder_name := nAnon; binder_relevance := Relevant |} (lift0 1 b) (lift0 1 B) (bbody br)))
    | _, _ => None
    end
  else None.

(** step 26: a number and a memory, [int * mem] *)
Definition is_pm (ty : term) : bool :=
  match ty with
  | tApp (tInd i _) [a; b] => Kername.eqb (inductive_mind i) (inductive_mind ind_prod) && is_ty kn_int a && is_ty kn_mem b
  | _ => false
  end.
Definition is_pm_case (ci : case_info) (p : predicate term) (br : branch term) : bool :=
  Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_prod) && Nat.eqb (length (bcontext br)) 2
  && match pparams p with [a; b] => is_ty kn_int a && is_ty kn_mem b | _ => false end.
(** [let r := v in body], r of type [int * mem], is read with [r] replaced by the pair of two new variables, the number below
    the memory: [fst r] and [snd r] then reduce to them (the readers' iota), and the meaning ([XLetP]) binds them to [fst v]
    and [snd v] -- the same term up to zeta and iota *)
Definition pm_split (ty body : term) : term :=
  match ty with
  | tApp (tInd i u) [a; b] => subst [tApp (tConstruct i 0 u) [a; b; tRel 1; tRel 0]] 0 (lift 2 1 body)
  | _ => body
  end.

(** step 25: a value of any inductive type built in place and taken apart.  A plain value -- a plain argument, a function, a
    type, or a constructor applied to plain values -- may be put in where it is named (its work is nothing at run time) *)
Fixpoint plain_val (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tLambda _ _ _ | tInd _ _ | tSort _ | tProd _ _ _ => true
      | tApp (tConstruct _ _ _) args | tApp (tInd _ _) args => forallb (plain_val fuel) args
      | _ => plain_arg t
      end
  end.
Definition is_con (t : term) : bool := match t with tConstruct _ _ _ | tApp (tConstruct _ _ _) _ => true | _ => false end.
(** a match on a constructor whose fields are plain is its branch with the fields put in: Rocq's own iota *)
Definition iota_go (ci : case_info) (c : term) (brs : list (branch term)) : option term :=
  let '(hd, args) := match c with tApp h a => (h, a) | _ => (c, []) end in
  match hd with
  | tConstruct ind k _ =>
      if Kername.eqb (inductive_mind ind) (inductive_mind (ci_ind ci)) then
        let fields := skipn (ci_npar ci) args in
        match nth_error brs k with
        | Some br => if Nat.eqb (length (bcontext br)) (length fields)
                        && forallb (plain_val 100) (if String.eqb (snd (inductive_mind ind)) "sig"%bs then firstn 1 fields else fields)
                     then Some (subst (rev fields) 0 (bbody br)) else None
        | None => None
        end
      else None
  | _ => None
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

(** a record taken apart (step 32): its fields as the readers' entries, the last first -- a number an entry of its own, a record
    field (a record holding records) unusable once taken apart; and the text after it.  A record holding records is taken apart
    with its inner records at once, in its fields' order and depth first (the order Rocq's nested patterns bind them, and the
    order of the flat record's numbers); otherwise it is not read *)
Definition rfw (ri : nat) : list nat := match nth_error rt ri with Some (_, _, _, _, _, None, fw) => fw | _ => [] end.
(** (step 67) a value holding a boolean or a data type: taken apart one level, never as flat numbers *)
Definition rgen (ri : nat) : bool := match nth_error rt ri with Some (mf, _, _, _, _, _, _) => match fst mf with [] => false | _ => true end | None => false end.
Definition slot_ent (q : term) : cent := if is_ty kn_int q then CNum else if is_bool q then CRecB else CRec.
Definition cty (ci : case_info) (p : predicate term) : term :=
  match pparams p with [] => tInd (ci_ind ci) (puinst p) | ps => tApp (tInd (ci_ind ci) (puinst p)) ps end.
Definition fents (fw : list nat) : list cent := rev (map (fun w => if Nat.eqb w 1 then CNum else CDead) fw).
Definition fpend (fw : list nat) : list nat :=
  map (fun i => length fw - 1 - i) (filter (fun i => Nat.ltb 1 (nth i fw 1)) (seq 0 (length fw))).
Fixpoint rbr_go (fuel : nat) (ents : list cent) (pend : list nat) (t : term) : option (list cent * term) :=
  match fuel with
  | O => None
  | S fuel =>
      match pend with
      | [] => Some (ents, t)
      | j :: rest =>
          match t with
          | tCase ci2 p2 (tRel j') [br2] =>
              match rindex (cty ci2 p2) rt 0 with
              | Some ri2 =>
                  let fw2 := rfw ri2 in
                  let k2 := length (bcontext br2) in
                  if Nat.eqb j j' && Nat.eqb (length fw2) k2 && negb (Nat.eqb k2 0)
                  then rbr_go fuel (fents fw2 ++ ents) (fpend fw2 ++ map (fun x => x + k2) rest) (bbody br2)
                  else None
              | None => None
              end
          | _ => None
          end
      end
  end.
Definition rbr (ci : case_info) (p : predicate term) (br : branch term) : option (list cent * term) :=
  let k := length (bcontext br) in
  match rindex (cty ci p) rt 0 with
  | Some ri => let fw := rfw ri in
               if rgen ri then None else
               if existsb (Nat.ltb 1) fw then (if Nat.eqb (length fw) k then rbr_go 100 (fents fw) (fpend fw) (bbody br) else None)
               else Some (repeat CNum k, bbody br)
  | None => Some (repeat CNum k, bbody br)
  end.

(** a record holding records taken apart one level (step 43): its fields' types, its record fields' types in the table; a match
    on one, not taken apart at once: its number fields numbers, its record fields records, the last first *)
Definition rftys (ri : nat) : list term := match nth_error rt ri with Some ((_, ft), _, _, _, _, None, _) => ft | _ => [] end.
Definition rbs (ci : case_info) (p : predicate term) (br : branch term) : option (nat * list cent * term) :=
  match rindex (cty ci p) rt 0 with
  | Some ri =>
      let ft := rftys ri in
      if existsb (fun q => negb (is_ty kn_int q)) ft && Nat.eqb (length ft) (length (bcontext br))
         && forallb (fun q => is_ty kn_int q || match rindex_f q rt with Some _ => true | None => false end) ft
      then Some (ri, rev (map slot_ent ft), bbody br) else None
  | None => None
  end.

(** the recursive call of a copy with captures passes them on: the captured numbers and booleans after its counters, the
    captured memory last *)
Definition with_caps (ctx : list cent) (rest : list term) : list term :=
  match after_self ctx with
  | [] => rest
  | cs0 =>
      let L := length ctx in
      let cs := combine (rev cs0) (map (fun k => tRel (L - 1 - k)) (seq 0 (length cs0))) in
      (* the captured counters after the template's counters, the other captured variables before its numbers (step 42) *)
      let isc (c : cent) := match c with CCntP _ | CCnt => true | _ => false end in
      let nt := Nat.sub fnx (length (filter (fun p => isc (fst p)) cs)) in
      firstn nt rest ++ map snd (filter (fun p => isc (fst p)) cs) ++ map snd (filter (fun p => negb (is_memc (fst p)) && negb (isc (fst p))) cs)
      ++ skipn nt rest ++ map snd (filter (fun p => is_memc (fst p)) cs)
  end.

Definition tcall (ctx : list cent) (kn : kername) (args : list term) : kername * list term :=
  let args := map (fsub ctx) args in
  match tc kn args with
  | Some p => p
  | None =>
      (* (step 53) the caller's own memory parameters, the same memory, in the places of a callee's *)
      match filter (fun c => match c with CMem => true | _ => false end) ctx with
      | _ :: _ :: _ =>
          match tc kn (map (alias_norm 1000 ctx (first_mem ctx 0) 0) args) with
          | Some p => p
          | None => (kn, args)
          end
      | _ => (kn, args)
      end
  end.

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
      | tApp (tLetIn _ _ _ _ as f) args => bnorm fuel (wout f args)
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

(** the types the readers hold as values: a number, a boolean, a counter, a memory, a record of the program's types *)
Definition held (ty : term) : bool :=
  is_ty kn_int ty || is_bool ty || is_nat ty || is_ty kn_mem ty
  || match rindex ty rt 0 with Some ri => if rgen ri then false else negb (existsb (Nat.ltb 1) (rfw ri)) | None => false end.
(** a let of a constructor of plain values, at a type the readers do not hold, is its body with the value put in (zeta) *)
Definition zeta_con (t : term) : option term :=
  match t with
  | tLetIn _ b ty body => if is_con b && plain_val 100 b && negb (held ty) then Some (subst [b] 0 body) else None
  | _ => None
  end.
(** the head of a scrutinee: a helper written out, a let read by zeta, a match on a constructor its branch *)
Fixpoint hnf_con (fuel : nat) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel =>
      match match zeta_head t with Some t' => Some t' | None => zeta_con t end with
      | Some t' => hnf_con fuel t'
      | None =>
          match t with
          | tConst kn _ => match hb kn with Some b => hnf_con fuel b | None => t end
          | tApp (tConst kn _) args => match hb kn with Some b => hnf_con fuel (wout b args) | None => t end
          | tApp (tLambda _ _ _ as f) args => hnf_con fuel (wout f args)
          | tApp (tLetIn _ _ _ _ as f) args => hnf_con fuel (wout f args)
          | tCase ci _ c brs => match iota_go ci (hnf_con fuel c) brs with Some t' => hnf_con fuel t' | None => t end
          | _ => t
          end
      end
  end.
(** a match the readers do not take apart: of a type other than [bool], [nat], [prod] and the program's records *)
Definition generic_ind (ind : inductive) : bool :=
  negb (Kername.eqb (inductive_mind ind) (inductive_mind ind_bool) || Kername.eqb (inductive_mind ind) (inductive_mind ind_nat)
        || Kername.eqb (inductive_mind ind) (inductive_mind ind_prod))
  && match rind ind rt 0 with Some (ri, _) => rgen ri | None => true end.
(** the head step of every reader: a let read by zeta (step 20), a let of a constructor put in, a match on a constructor of a
    type no reader takes apart its branch, such a match at the head of an application its branch applied (step 25) -- each the
    same term up to zeta, iota and beta, each firing only where no reader held the term before *)
Definition head_r (t : term) : option term :=
  match zeta_head t with
  | Some t' => Some t'
  | None =>
      match zeta_con t with
      | Some t' => Some t'
      | None =>
          match t with
          | tCase ci _ c brs =>
              if generic_ind (ci_ind ci) then iota_go ci (hnf_con 50 c) brs
              else if (if String.eqb (snd (inductive_mind (ci_ind ci))) "unit"%bs then true else String.eqb (snd (inductive_mind (ci_ind ci))) "sig"%bs) then iota_go ci (hnf_con 50 c) brs
              else None
          | tApp (tCase ci _ c brs) args => option_map (fun t' => mkApps t' args) (iota_go ci (hnf_con 50 c) brs)
          | tApp (tFix [_] 0 as fx) args => Some (tApp (tConst kn_lfix []) (fx :: args))
          | _ => None
          end
      end
  end.

(** a match on a data type of the program (step 28): its index and widths, the scrutinee (a helper's call written out), and
    each branch lifted to the record's fields -- the tag below them, constructor [k]'s fields its first [nth k ws] *)
Definition tag_w (ws : list nat) : nat := fold_left Nat.max ws O.
Definition tag_parts (t : term) : option (nat * list nat * term * list term) :=
  match t with
  | tCase ci p c0 brs =>
      match rindex (match pparams p with [] => tInd (ci_ind ci) (puinst p) | ps => tApp (tInd (ci_ind ci) (puinst p)) ps end) rt 0 with
      | Some ri =>
          match nth_error rt ri with
          | Some (mf, _, _, _, _, Some ws, _) =>
              if Nat.eqb (length brs) (length ws) then
                let w := tag_w ws in
                let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
                match fst mf with
                | [] => Some (ri, ws, c, map (fun br => let wc := length (bcontext br) in lift (w - wc) 0 (lift 1 wc (bbody br))) brs)
                | ms =>
                    (* (step 67) each field a slot: the tag and the slots bound, the farthest the tag *)
                    let S0 := S (length (snd mf)) in
                    Some (ri, ws, c, map (fun mb : list (bool * nat) * branch term =>
                            let mk := length (bcontext (snd mb)) in
                            subst (map (fun de => let p := nth (mk - 1 - de) (fst mb) (true, O) in
                                                  tRel (S0 - 1 - (if fst p then S (snd p) else S (w + snd p)))) (seq 0 mk)) 0
                                  (lift S0 mk (bbody (snd mb)))) (combine ms brs))
                end
              else None
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.
(** (step 67) what a match on a data type binds: its tag and its fields, or its tag and its slots *)
Definition tag_ents (ri : nat) (ws : list nat) : list cent :=
  if rgen ri then match nth_error rt ri with
                  | Some (mf, _, _, _, _, _, _) => rev (CNum :: map slot_ent (snd mf))
                  | None => []
                  end
  else repeat CNum (S (tag_w ws)).
(** the test of the tag choosing among the branches, the last one where no test held *)
Fixpoint tag_chain {A : Type} (mk : nat -> A -> A -> A) (es : list A) (k : nat) : option A :=
  match es with [] => None | [e] => Some e | e :: r => option_map (mk k e) (tag_chain mk r (S k)) end.
Definition tag_test (ws : list nat) (k : nat) : sexp * sexp := (SVar (tag_w ws), SInt (ofn k)).

(** (step 67) the data type holding other than numbers a constructor on these arguments builds: its index, its number of parameters,
    this constructor's fields' slots, its slots' types *)
Fixpoint tctor_go (ind : inductive) (c : nat) (args : list term) (es : list rentry) (i : nat) : option (nat * nat * list (bool * nat) * list term) :=
  match es with
  | [] => None
  | (mf, _, j, _, qs, g, _) :: r =>
      match fst mf, g with
      | _ :: _, Some _ =>
          if Kername.eqb (inductive_mind ind) (inductive_mind j) && Nat.eqb (inductive_ind ind) (inductive_ind j)
             && negb (Kername.eqb (inductive_mind j) (inductive_mind ind_bool))
             && teqs (firstn (length qs) args) qs && Nat.ltb c (length (fst mf))
             && Nat.eqb (length args) (length qs + length (nth c (fst mf) []))
          then Some (i, length qs, nth c (fst mf) [], snd mf) else tctor_go ind c args r (S i)
      | _, _ => tctor_go ind c args r (S i)
      end
  end.
(** a number; and a counter: a counter variable, [O], [S c], [kq_nat e] *)
(** (step 47) a number holding a call to make first -- of a function that writes, of a function given a pair not built in
    place, of the function itself -- in a place evaluated before the rest (an operand, a call's argument, a test): the call
    bound by a let, the operands of the numbers' operations that read the memory bound before it (the meaning is Rocq's, which
    no order changes; the lets are a conversion away), the rest after it with the call's result *)
Definition pair_lit (a : term) : bool :=
  match a with tApp (tConstruct i 0 _) [_; _; _; _] => Kername.eqb (inductive_mind i) (inductive_mind ind_prod) | _ => false end.
Definition bcall_q (u : term) : option bool :=
  match u with
  | tApp (tConst kn _) args =>
      match find_callee kn callees 0 with
      | Some (_, gs) =>
          if negb (sr gs) && (sw gs || (sp gs && match rev args with a :: _ => negb (pair_lit a) | [] => false end))
          then Some (match sq gs with Some KBool => true | _ => false end) else None
      | None => None
      end
  | _ => None
  end.
Definition bcall_rec (u : term) : option term :=
  match u with
  | tApp (tConst kn _) args =>
      match find_callee kn callees 0 with
      | Some (_, gs) =>
          match sq gs with
          | Some (KRec ri) =>
              if negb (sr gs) && ((sp gs && match rev args with a :: _ => negb (pair_lit a) | [] => false end) || (sw gs && sm gs && negb (sp gs)))
              then option_map (fun e => let '(_, ty, _, _, _, _, _) := e in ty) (nth_error rt ri) else None
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.
(** (step 50) a read of the memory [ism] names, or a call of a function that reads it ([isc]: its result's type), in what follows the first
    binding of [t], its arguments naming nothing bound after that binding: bound before it.  In Rocq it reads the memory before
    whatever that binding writes, so it may go first; up to zeta the same term *)
Definition hoist_core (ism : nat -> bool) (isc : kername -> option term) (t : term) : option term :=
  let is_read (d : nat) (u : term) : option term :=
    match u with
    | tApp (tConst kn _) args =>
        match rev args with
        | tRel m :: _ =>
            if Nat.leb d m then
              if ism (m - d) then
                if forallb (Nat.leb d) (fold_left (fun a x => fvs 1000 0 x a) args []) then
                  if Kername.eqb kn kn_rd then Some (tConst kn_int [])
                  else if Kername.eqb kn kn_rd32 then Some (tConst kn_int [])
                  else if Kername.eqb kn kn_rd8 then Some (tConst kn_int [])
                  else isc kn
                else None
              else None
            else None
        | _ => None
        end
    | _ => None
    end in
  let fix find (fu d : nat) (u : term) {struct fu} : option (term * term) :=
    match fu with
    | O => None
    | S fu =>
        match is_read d u with
        | Some ty => Some (subst (repeat (tRel 0) d) 0 u, ty)
        | None =>
            match u with
            | tApp _ args => fold_left (fun a x => match a with Some _ => a | None => find fu d x end) args None
            | tLetIn _ b _ body => match find fu d b with Some r => Some r | None => find fu (S d) body end
            | tCase _ _ c brs =>
                match find fu d c with
                | Some r => Some r
                | None => fold_left (fun a br => match a with Some _ => a | None => find fu (d + length (bcontext br)) (bbody br) end) brs None
                end
            | _ => None
            end
        end
    end in
  let fix repl (fu d : nat) (c u : term) {struct fu} : term :=
    match fu with
    | O => u
    | S fu =>
        if teq 1000 u (lift0 (S d) c) then tRel d else
        match u with
        | tApp f args => tApp f (map (repl fu d c) args)
        | tLetIn na b ty body => tLetIn na (repl fu d c b) ty (repl fu (S d) c body)
        | tCase ci p c0 brs =>
            tCase ci p (repl fu d c c0) (map (fun br => {| bcontext := bcontext br; bbody := repl fu (d + length (bcontext br)) c (bbody br) |}) brs)
        | _ => u
        end
    end in
  let anon := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let first := match t with
               | tLetIn _ _ _ body => find 1000 1 body
               | tCase _ _ _ [br] => find 1000 (length (bcontext br)) (bbody br)
               | _ => None
               end in
  match first with
  | Some (c, ty) => Some (tLetIn anon c ty (repl 1000 0 c (lift0 1 t)))
  | None => None
  end.
(** whether the first binding of [t] writes the memory, as far as its form says *)
Definition writes_first (ctx : list cent) (t : term) : bool :=
  let wc (b : term) :=
    match b with
    | tApp (tConst kn _) args =>
        let '(kn1, _) := tcall ctx kn args in
        match find_callee kn1 callees 0 with Some (_, gs) => sw gs | None => false end
    | _ => false
    end in
  match t with
  | tLetIn _ b ty _ => if is_ty kn_mem ty then true else if is_pm ty then true else wc b
  | tCase ci p c [br] => if is_pm_case ci p br then true else wc c
  | _ => false
  end.
Definition hoist_read (ctx : list cent) (t : term) : option term :=
  if writes_first ctx t then
    hoist_core (is_ent CMem ctx)
      (fun kn => match find_callee kn callees 0 with
                 | Some (_, gs) =>
                     if sr gs then None else if sw gs then None else
                     match sq gs with
                     | None => Some (tConst kn_int [])
                     | Some KBool => Some (tInd ind_bool [])
                     | _ => None
                     end
                 | None => None
                 end) t
  else None.
Definition kn_fst0 := kn_of <% @fst %>.
Fixpoint lam_tys (t : term) : list term := match t with tLambda _ ty b => ty :: lam_tys b | _ => [] end.
Definition bind_first (mk : bool) (ot : option term) (ctx : list cent) (t : term) : option term :=
  let res (u : term) : term := match u with tApp (tConst kn _) args => let '(kn1, args1) := tcall ctx kn args in tApp (tConst kn1 []) args1 | _ => u end in
  let bq (u : term) : option bool :=
    match u with
    | tApp (tRel fi) _ => if is_ent CSelf ctx fi then Some false else None
    | _ => match bcall_rec (res u) with Some _ => Some false | None => bcall_q (res u) end
    end in
  (* (step 54) a call giving back a number and a memory *)
  let pm_call (u : term) : bool :=
    match u with
    | tApp (tConst kn _) args =>
        let '(kn1, _) := tcall ctx kn args in
        match find_callee kn1 callees 0 with
        | Some (_, gs) => match sq gs with Some KNum => true | _ => false end
        | None => false
        end
    | _ => false
    end in
  (* (step 52, [mk]) the memory given to a read, or to a function taking a memory, when it is not a variable; (step 54) the first part of
     a call giving back a number and a memory: the call, a let of the pair *)
  let made (u : term) : option term :=
    let lastm (args : list term) := match rev args with
                                    | tRel _ :: _ | [] => None
                                    | m :: _ => Some m
                                    end in
    match u with
    | tApp (tConst kn _) args =>
        if Kername.eqb kn kn_fst0 then match args with [_; _; c] => if pm_call c then Some c else None | _ => None end
        else if Kername.eqb kn kn_rd then lastm args
        else if Kername.eqb kn kn_rd32 then lastm args
        else if Kername.eqb kn kn_rd8 then lastm args
        else if Kername.eqb kn kn_ksize then lastm args
        else let '(kn1, args1) := tcall ctx kn args in
             match find_callee kn1 callees 0 with
             | Some (_, gs) => if sm gs then lastm args1 else None
             | None =>
                 (* a helper taking a memory: the memory given it, at its parameter's place *)
                 match hb kn with
                 | Some bd =>
                     fold_left (fun acc p => match acc with
                                             | Some _ => acc
                                             | None => if is_ty kn_mem (fst p) then match snd p with tRel _ => None | m => Some m end else None
                                             end) (combine (lam_tys bd) args) None
                 | None => None
                 end
             end
    | _ => None
    end in
  let fix find (fu : nat) (u : term) {struct fu} : option term :=
    match fu with
    | O => None
    | S fu =>
        match (if mk then match made u with Some m => Some true | None => None end else bq u) with
        | Some _ => if mk then made u else Some u
        | None =>
            match u with
            | tApp _ args => fold_left (fun a x => match a with Some _ => a | None => find fu x end) args None
            | tCase _ _ c _ => find fu c
            (* a let's bound term, unless it is itself the call: a call already bound is not bound again *)
            | tLetIn _ b _ _ => match (if mk then None else bq b) with Some _ => None | None => find fu b end
            | _ => None
            end
        end
    end in
  let fix occ (fu : nat) (c u : term) {struct fu} : bool :=
    match fu with
    | O => false
    | S fu => teq 1000 u c || match u with
                             | tApp f args => occ fu c f || existsb (occ fu c) args
                             | tCase _ _ c0 brs => occ fu c c0 || existsb (fun br => occ fu c (bbody br)) brs
                             | tLambda _ _ b => occ fu c b
                             | tLetIn _ b0 _ b => occ fu c b0 || occ fu c b
                             | _ => false
                             end
    end in
  let memv (u : term) : bool := existsb (fun i => match nth_error ctx i with Some CMem => true | _ => false end) (fvs 1000 0 u []) in
  (* the term with the call a placeholder, each hoisted operand one *)
  let fix skel (fu : nat) (c u : term) (hs : list term) {struct fu} : term * list term :=
    match fu with
    | O => (u, hs)
    | S fu =>
        if teq 1000 u c then (tVar "kq_v"%bs, hs) else
        match u with
        | tApp (tConst kn _ as f) args =>
            let num_op := eq_mp (fst kn) prim_mp in
            let '(args', hs') := fold_left (fun acc a => let '(l, h) := acc in
                                   if occ 1000 c a then let '(a', h') := skel fu c a h in (l ++ [a'], h')
                                   else if num_op && memv a then (l ++ [tVar ("kq_h"%bs ^ string_of_nat (length h))], h ++ [a])
                                   else (l ++ [a], h)) args ([], hs) in
            (tApp f args', hs')
        | tApp f args =>
            let '(args', hs') := fold_left (fun acc a => let '(l, h) := acc in
                                   if occ 1000 c a then let '(a', h') := skel fu c a h in (l ++ [a'], h') else (l ++ [a], h)) args ([], hs) in
            (tApp f args', hs')
        | tCase ci p c0 brs => let '(c0', hs') := skel fu c c0 hs in (tCase ci p c0' brs, hs')
        | tLetIn na b0 ty b => let '(b0', hs') := skel fu c b0 hs in (tLetIn na b0' ty b, hs')
        | _ => (u, hs)
        end
    end in
  let fix repl (fu : nat) (k : nat) (u : term) {struct fu} : term :=
    match fu with
    | O => u
    | S fu =>
        match u with
        | tVar v => if String.eqb v "kq_v"%bs then tRel 0
                    else match List.find (fun i => String.eqb v ("kq_h"%bs ^ string_of_nat i)) (seq 0 k) with
                         | Some i => tRel (k - i) | None => u end
        | tApp f args => tApp (repl fu k f) (map (repl fu k) args)
        | tCase ci p c0 brs => tCase ci p (repl fu k c0) brs
        | tLetIn na b0 ty b => tLetIn na (repl fu k b0) ty b
        | _ => u
        end
    end in
  let fix inl (fu : nat) (u : term) {struct fu} : term :=
    match fu with
    | O => u
    | S fu =>
        match u with
        | tApp (tConst kn _ as f) args => match hb kn with Some b => inl fu (wout b args) | None => tApp f (map (inl fu) args) end
        | tApp f args => tApp f (map (inl fu) args)
        | tCase ci p c brs => tCase ci p (inl fu c) brs
        | tLetIn na b0 ty b => tLetIn na (inl fu b0) ty b
        | _ => u
        end
    end in
  (* the helpers written out only when the text as written holds no such call *)
  (* (step 54) a memory made in place hidden in a helper: the helpers written out a level at a time, the helper that takes it left standing *)
  let fix inl1 (fu : nat) (u : term) {struct fu} : term :=
    match fu with
    | O => u
    | S fu =>
        match u with
        | tApp (tConst kn _ as f) args => match hb kn with Some b => wout b args | None => tApp f (map (inl1 fu) args) end
        | tApp f args => tApp f (map (inl1 fu) args)
        | tCase ci p c brs => tCase ci p (inl1 fu c) brs
        | tLetIn na b0 ty b => tLetIn na (inl1 fu b0) ty b
        | _ => u
        end
    end in
  let fix unroll (k : nat) (u : term) {struct k} : term :=
    match k with
    | O => u
    | S k => match find 1000 u with
             | Some _ => u
             | None => let v := inl1 100 u in if teq 1000 v u then u else unroll k v
             end
    end in
  let t := if mk then unroll 100 t else match find 1000 t with Some _ => t | None => inl 100 t end in
  match find 1000 t with
  | None => None
  | Some c =>
      (* (step 48 continued) [ot]: the type of the let of the function's own call; the reader does not know its result here, and
         the let's type is not part of the meaning *)
      let own := match c with tApp (tRel _) _ => true | _ => false end in
      if (match ot with Some _ => negb own | None => false end) then None else
      let '(sk, hs) := skel 1000 c t [] in
      let k := length hs in
      let tyv := if mk then (if pm_call c then tApp (tInd ind_prod []) [tConst kn_int []; tConst kn_mem []] else tConst kn_mem []) else match ot with Some ty => ty | None => match bcall_rec (res c) with Some ty => ty | None => match bq c with Some true => tInd ind_bool [] | _ => tConst kn_int [] end end end in
      let anon := {| binder_name := nAnon; binder_relevance := Relevant |} in
      Some (fold_right (fun ih b => tLetIn anon (lift0 (fst ih) (snd ih)) (tConst kn_int []) b)
                       (tLetIn anon (lift0 k c) tyv (repl 1000 k (lift0 (S k) sk))) (combine (seq 0 k) hs))
  end.

Fixpoint reify (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sexp :=
  match fuel with
  | O => None
  | S fuel =>
  let reify_args (l : list term) : option sexps :=
    to_args (map (fun a => match reify fuel ctx a with Some e => Some (inl e) | None =>
                            match reify_b fuel ctx a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel ctx a) end end) l) in
  let reify_cs (l : list term) : option scnts := option_map to_scnts (opt_all (map (reify_c fuel ctx) l)) in
  match head_r t with Some t' => reify fuel ctx t' | None =>
  match tag_parts t with
  | Some (ri, ws, c, bs) =>
      match reify_r fuel ctx c, opt_all (map (reify fuel (tag_ents ri ws ++ ctx)) bs) with
      | Some x, Some es => option_map (if rgen ri then SSplitR ri x else SMatchR x) (tag_chain (fun k e r => SIf Ceq (fst (tag_test ws k)) (snd (tag_test ws k)) e r) es 0)
      | _, _ => None
      end
  | None =>
  match t with
  | tRel i => option_map SVar (num_index ctx i)
  | tInt n => Some (SInt n)
  | tConst kn _ => match hb kn with Some b => reify fuel ctx b | None => None end
  | tApp (tConst kn _) args =>
      (* (step 70) a counter as a number; a number written as a [Z] *)
      if Kername.eqb kn kn_ofz then
        match args with
        | [tApp (tConst k _) [c]] => if Kername.eqb k kn_zofn then option_map SOfC (reify_c fuel ctx c) else None
        | [z] => option_map (fun v => SInt (Uint63.of_Z v)) (z_lit z)
        | _ => None
        end
      else if eq_mp (fst kn) prim_mp then
        match binop_v (snd kn), args with
        | Some o, [a; b] =>
            match reify fuel ctx a, reify fuel ctx b with Some x, Some y => Some (SOp o x y) | _, _ => None end
        | _, _ =>
            match hwf_lookup kn with
            | Some (o, n) => if Nat.eqb (length args) n then option_map (fun l => SHwf o (to_sexps l)) (opt_all (map (reify fuel ctx) args)) else None
            | None => None
            end
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
        | [h; i; m0] =>
            (* the memory: the newest one, or a term reducing to it ([snd (v, s2)], step 26) *)
            match (match m0 with tRel _ => m0 | _ => hnf_con 50 m0 end) with
            | tRel m =>
                if is_ent CMem ctx m then
                  match reify fuel ctx h, reify fuel ctx i with
                  | Some x, Some y => Some (if Kername.eqb kn kn_rd then SRd x y else if Kername.eqb kn kn_rd32 then SRd32 x y else SRd8 x y)
                  | _, _ => None
                  end
                else None
            | _ => None
            end
        | _ => None
        end
      else
        let '(kn1, args1) := tcall ctx kn args in
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
  | tApp (tRel fi) args00 =>
      let args0 := self_perm ctx fi args00 in
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
  | tApp (tLetIn _ _ _ _ as f) args => reify fuel ctx (wout f args)
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
        | _ => match known_branch c b0 b1 with Some t => reify fuel ctx t | None => reify fuel ctx (let_scrut ci p c b0 b1) end
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
        match reify_r fuel ctx c, (match rbr ci p br with Some (es0, bd0) => reify fuel (es0 ++ ctx) bd0 | None => None end) with
        | Some x, Some e => Some (SMatchR x e)
        | _, _ => match iota_pair ci p c br with Some t' => reify fuel ctx t' | None =>
                  match rbs ci p br, reify_r fuel ctx c with
                  | Some (rj, es1, bd1), Some x => option_map (SSplitR rj x) (reify fuel (es1 ++ ctx) bd1)
                  | _, _ => None
                  end end
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
  | tApp (tLetIn _ _ _ _ as f) args => reify_c fuel ctx (wout f args)
  | tApp (tRel i) args => match nth_error ctx i with Some (CFn _ t) => reify_c fuel ctx (wout (capsub ctx t) args) | _ => None end
  | tApp (tConst kn _) args =>
      if Kername.eqb kn kn_kq_nat then match args with [e] => option_map CNat (reify fuel ctx e) | _ => None end
      else if Kername.eqb kn kn_nat_pred then match args with [c] => option_map KQR.CPred (reify_c fuel ctx c) | _ => None end
      else if Kername.eqb kn kn_nat_add then
        match args with [a; b] => match reify_c fuel ctx a, reify_c fuel ctx b with Some x, Some y => Some (CAdd x y) | _, _ => None end | _ => None end
      (* (step 66) *)
      else if Kername.eqb kn kn_c_min then
        match args with [a; b] => match reify_c fuel ctx a, reify_c fuel ctx b with Some x, Some y => Some (CMin x y) | _, _ => None end | _ => None end
      else if Kername.eqb kn kn_c_max then
        match args with [a; b] => match reify_c fuel ctx a, reify_c fuel ctx b with Some x, Some y => Some (CMax x y) | _, _ => None end | _ => None end
      else if Kername.eqb kn kn_c_sub then
        match args with [a; b] => match reify_c fuel ctx a, reify_c fuel ctx b with Some x, Some y => Some (CSub x y) | _, _ => None end | _ => None end
      else if Kername.eqb kn kn_c_div2 then match args with [c] => option_map CDiv2 (reify_c fuel ctx c) | _ => None end
      (* (step 70) *)
      else if Kername.eqb kn kn_c_mul then
        match args with
        | [a; b] => if cnt_lit a then option_map (CMulK true (cnt_val a)) (reify_c fuel ctx b)
                    else if cnt_lit b then option_map (CMulK false (cnt_val b)) (reify_c fuel ctx a) else None
        | _ => None end
      else if Kername.eqb kn kn_c_div then
        match args with [a; b] => match reify_c fuel ctx a, reify_c fuel ctx b with Some x, Some y => Some (CDivN x y) | _, _ => None end | _ => None end
      else if Kername.eqb kn kn_c_mod then
        match args with [a; b] => match reify_c fuel ctx a, reify_c fuel ctx b with Some x, Some y => Some (CModN x y) | _, _ => None end | _ => None end
      else if Kername.eqb kn kn_c_pow then
        match args with
        | [a; b] => if cnt_lit a && cnt_lit b then
                      let v := Nat.pow (cnt_val a) (cnt_val b) in
                      if Nat.leb v 4096 then Some (cnt_term v) else None
                    else None
        | _ => None end
      else if Kername.eqb kn kn_zton then
        match args with
        | [tApp (tConst k _) [e]] => if Kername.eqb k kn_s2z then option_map CToNat (reify fuel ctx e)
                                     else if Kername.eqb k kn_u2z then option_map CToNatU (reify fuel ctx e) else None
        | _ => None end
      else match hb kn with Some b => reify_c fuel ctx (wout b args) | None => None end
  | tCase ci p c0 [b0; b1] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        match reify_b fuel ctx c0, reify_c fuel ctx (bbody b0), reify_c fuel ctx (bbody b1) with
        | Some b, Some x, Some y => Some (CIf b x y)
        | _, _, _ => None
        end
      else None
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
      match head_r t with Some t' => reify_r fuel ctx t' | None =>
      (* a record chosen by a match on a value of a data type (step 36): taken apart, a test chain on its tag *)
      match tag_parts t, (match t with tCase _ p _ _ => rindex (preturn p) rt 0 | _ => None end) with
      | Some (ri, ws, c, bs), Some ri' =>
          match reify_r fuel ctx c, opt_all (map (reify_r fuel (tag_ents ri ws ++ ctx)) bs) with
          | Some x, Some es => option_map (if rgen ri then RSplitR ri' ri x else RMatchR ri' x) (tag_chain (fun k e r => RIf ri' Ceq (fst (tag_test ws k)) (snd (tag_test ws k)) e r) es 0)
          | _, _ => None
          end
      | _, _ =>
      match t with
      | tRel i => option_map RVar (rec_index ctx i)
      | tApp (tConstruct ind c _) args =>
      (* (step 67) a field of a value holding booleans: a boolean as a value of bool's entry, else a record *)
      let field_r (q a : term) : option srec :=
        if is_bool q then match rbool rt 0 with Some rb => option_map (RBoolV rb) (reify_b fuel ctx a) | None => None end
        else reify_r fuel ctx a in
      (* (step 67) a constructor of a data type holding other than numbers: its tag, its number slots, its record slots *)
      let rmk_t (ri c : nat) (fields : list term) (ms : list (bool * nat)) (ft : list term) : option srec :=
        let nn := length (filter (is_ty kn_int) ft) in
        let fm0 := combine ms fields in
        let nums := map snd (filter (fun p : bool * nat * term => fst (fst p)) fm0) in
        match opt_all (map (reify fuel ctx) nums),
              opt_all (map (fun sq : nat * term =>
                 match List.find (fun p : bool * nat * term => if fst (fst p) then false else Nat.eqb (snd (fst p)) (fst sq)) fm0 with
                 | Some p => field_r (snd sq) (snd p)
                 | None => option_map RDflt (rindex_f (snd sq) rt)
                 end) (combine (seq 0 (length ft - nn)) (skipn nn ft))) with
        | Some ns, Some rs => Some (RMkR ri (to_sexps (SInt (ofn c) :: ns ++ repeat (SInt (ofn 0)) (nn - length ns))) (to_sexps_r rs))
        | _, _ => None
        end in
          match tctor_go ind c args rt 0 with
          | Some (ri, np, ms, ft) => rmk_t ri c (skipn np args) ms ft
          | None =>
          (* a record's constructor; a data type's (step 28): its number, its fields, zeros up to the widest *)
          match cindex ind c args rt 0 with
          | Some (ri, np, tg) =>
              if rgen ri then
                (* (step 67) a record holding booleans or data types: the one-level constructor *)
                let fa := combine (rftys ri) (skipn np args) in
                match opt_all (map (fun q => reify fuel ctx (snd q)) (filter (fun q => is_ty kn_int (fst q)) fa)),
                      opt_all (map (fun q => field_r (fst q) (snd q)) (filter (fun q => negb (is_ty kn_int (fst q))) fa)) with
                | Some ns, Some rs => Some (RMkR ri (to_sexps ns) (to_sexps_r rs))
                | _, _ => None
                end
              else
              if existsb (Nat.ltb 1) (rfw ri) then
                (* a record holding records (step 32): the outer numbers, then each inner record's fields, depth first *)
                let fix flat (fu : nat) (fw : list nat) (fs : list term) {struct fu} : option (list sexp) :=
                  match fu with
                  | O => None
                  | S fu =>
                      let wf := combine fw fs in
                      match opt_all (map (fun q => reify fuel ctx (snd q)) (filter (fun q => Nat.eqb (fst q) 1) wf)),
                            opt_all (map (fun q => match snd q with
                                                   | tApp (tConstruct ind' c' _) args' =>
                                                       match cindex ind' c' args' rt 0 with
                                                       | Some (ri', np', None) => flat fu (rfw ri') (skipn np' args')
                                                       | _ => None
                                                       end
                                                   | _ => None
                                                   end) (filter (fun q => Nat.ltb 1 (fst q)) wf)) with
                      | Some nums, Some recs => Some (nums ++ concat recs)
                      | _, _ => None
                      end
                  end in
                match flat 100 (rfw ri) (skipn np args) with
                | Some es => Some (RMk ri (to_sexps es))
                | None =>
                    (* a record value among the fields (step 43): the one-level constructor, its numbers and its records *)
                    let fa := combine (rftys ri) (skipn np args) in
                    match opt_all (map (fun q => reify fuel ctx (snd q)) (filter (fun q => is_ty kn_int (fst q)) fa)),
                          opt_all (map (fun q => reify_r fuel ctx (snd q)) (filter (fun q => negb (is_ty kn_int (fst q))) fa)) with
                    | Some ns, Some rs => Some (RMkR ri (to_sexps ns) (to_sexps_r rs))
                    | _, _ => None
                    end
                end
              else
              option_map (fun es => RMk ri (to_sexps (match tg with Some (k, pad) => SInt (ofn k) :: es ++ repeat (SInt (ofn 0)) pad | None => es end)))
                         (opt_all (map (reify fuel ctx) (skipn np args)))
          | None => None
          end
          end
      | tConstruct ind c _ =>
      (* (step 67) a field of a value holding booleans: a boolean as a value of bool's entry, else a record *)
      let field_r (q a : term) : option srec :=
        if is_bool q then match rbool rt 0 with Some rb => option_map (RBoolV rb) (reify_b fuel ctx a) | None => None end
        else reify_r fuel ctx a in
      (* (step 67) a constructor of a data type holding other than numbers: its tag, its number slots, its record slots *)
      let rmk_t (ri c : nat) (fields : list term) (ms : list (bool * nat)) (ft : list term) : option srec :=
        let nn := length (filter (is_ty kn_int) ft) in
        let fm0 := combine ms fields in
        let nums := map snd (filter (fun p : bool * nat * term => fst (fst p)) fm0) in
        match opt_all (map (reify fuel ctx) nums),
              opt_all (map (fun sq : nat * term =>
                 match List.find (fun p : bool * nat * term => if fst (fst p) then false else Nat.eqb (snd (fst p)) (fst sq)) fm0 with
                 | Some p => field_r (snd sq) (snd p)
                 | None => option_map RDflt (rindex_f (snd sq) rt)
                 end) (combine (seq 0 (length ft - nn)) (skipn nn ft))) with
        | Some ns, Some rs => Some (RMkR ri (to_sexps (SInt (ofn c) :: ns ++ repeat (SInt (ofn 0)) (nn - length ns))) (to_sexps_r rs))
        | _, _ => None
        end in
          match tctor_go ind c [] rt 0 with
          | Some (ri, np, ms, ft) => rmk_t ri c [] ms ft
          | None =>
          match cindex ind c [] rt 0 with
          | Some (ri, _, Some (k, pad)) => Some (RMk ri (to_sexps (SInt (ofn k) :: repeat (SInt (ofn 0)) pad)))
          | Some (ri, _, None) => Some (RMk ri SNil)
          | _ => None
          end
          end
      | tConst kn _ => match hb kn with Some b => reify_r fuel ctx b | None => None end
      | tApp (tLambda _ _ _ as f) args => reify_r fuel ctx (wout f args)
      | tApp (tLetIn _ _ _ _ as f) args => reify_r fuel ctx (wout f args)
      | tApp (tRel i) args => match nth_error ctx i with Some (CFn _ t) => reify_r fuel ctx (wout (capsub ctx t) args) | _ => None end
      (* a record chosen by a test of one comparison (step 21): its type the match's *)
      | tCase ci p c0 [b0; b1] =>
          if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
            match rindex (preturn p) rt 0,
                  (match bnorm fuel c0 with
                   | tApp (tConst kn _) [a; b] => if eq_mp (fst kn) prim_mp then option_map (fun x => (x, a, b)) (cmp_v (snd kn)) else None
                   | _ => None
                   end) with
            | Some ri, Some (cmp, a, b) =>
                match reify fuel ctx a, reify fuel ctx b, reify_r fuel ctx (bbody b0), reify_r fuel ctx (bbody b1) with
                | Some x, Some y, Some t1, Some t2 => Some (RIf ri cmp x y t1 t2)
                | _, _, _, _ => None
                end
            | Some ri, None =>     (* a test on a boolean (step 36) *)
                match reify_b fuel ctx c0, reify_r fuel ctx (bbody b0), reify_r fuel ctx (bbody b1) with
                | Some x, Some t1, Some t2 => Some (RIfB ri x t1 t2)
                | _, _, _ => None
                end
            | _, _ => None
            end
          (* a record chosen by a match on a counter (step 36) *)
          else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
            match c0 with
            | tRel i =>
                match rindex (preturn p) rt 0, cnt_index ctx i, reify_r fuel ctx (bbody b0), reify_r fuel (CCnt :: ctx) (bbody b1) with
                | Some ri, Some x, Some t0, Some t1 => Some (RMatchCnt ri x t0 t1)
                | _, _, _, _ => None
                end
            | _ => match known_branch c0 b0 b1 with Some t => reify_r fuel ctx t | None => reify_r fuel ctx (let_scrut ci p c0 b0 b1) end
            end
          else None
      (* a record built from a record taken apart (step 21): its type the match's *)
      | tCase ci p c0 [br] =>
          let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
          match lets_first ci p c [br] with Some t' => reify_r fuel ctx t' | None =>
          match rindex (preturn p) rt 0, reify_r fuel ctx c, (match rbr ci p br with Some (es0, bd0) => reify_r fuel (es0 ++ ctx) bd0 | None => None end) with
          | Some ri, Some x, Some y => Some (RMatchR ri x y)
          | _, _, _ => match iota_pair ci p c br with Some t' => reify_r fuel ctx t' | None =>
                       match rindex (preturn p) rt 0, rbs ci p br, reify_r fuel ctx c with
                       | Some ri, Some (rj, es1, bd1), Some x => option_map (RSplitR ri rj x) (reify_r fuel (es1 ++ ctx) bd1)
                       | _, _, _ => None
                       end end
          end
          end
      (* a record under lets: a helper giving a record written out, its arguments bound (step 16) *)
      | tLetIn _ b ty body =>
          if is_ty kn_int ty then
            match reify fuel ctx b, reify_r fuel (CNum :: ctx) body with Some e, Some x => Some (RLet e x) | _, _ => None end
          else if is_bool ty then match reify_b fuel ctx b, reify_r fuel (CBool :: ctx) body with Some y, Some x => Some (RLetB y x) | _, _ => None end
          else if is_nat ty then match reify_c fuel ctx b, reify_r fuel (CCnt :: ctx) body with Some c, Some x => Some (RLetC c x) | _, _ => None end
          else if is_ty kn_mem ty then None
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
          let '(kn1, args1) := tcall ctx kn args in
          match find_callee kn1 callees 0 with
          | Some (f, gs) =>
              match sq gs with
              | Some (KRec ri) =>
                  if sr gs || sw gs || negb (Nat.leb (sn gs) (length args1)) then None else
                  match opt_all (map (reify_c fuel ctx) (firstn (sn gs) args1)), read_mem ctx (sm gs) (skipn (sn gs) args1) with
                  | Some cs, Some nums => option_map (RCall ri f (to_scnts cs)) (reify_args nums)
                  | _, _ => None
                  end
              | _ => None
              end
          | None => match hb kn with Some b => reify_r fuel ctx (wout b args) | None => None end
          end
      | _ => None
      end
      end
      end
  end
with reify_b (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sbool :=
  match fuel with
  | O => None
  | S fuel =>
  match head_r t with Some t' => reify_b fuel ctx t' | None =>
  (* a match on a value of a data type (step 28), in a boolean (step 36): taken apart, a test chain on its tag *)
  match tag_parts t with
  | Some (ri, ws, c, bs) =>
      match reify_r fuel ctx c, opt_all (map (reify_b fuel (tag_ents ri ws ++ ctx)) bs) with
      | Some x, Some es => option_map (if rgen ri then BxSplitR ri x else BxMatchR x) (tag_chain (fun k e r => BIfCmp Ceq (fst (tag_test ws k)) (snd (tag_test ws k)) e r) es 0)
      | _, _ => None
      end
  | None =>
  match t with
  | tRel i => match bool_index ctx i with
              | Some x => Some (BVar x)
              | None => match nth_error ctx i with
                        | Some CRecB => option_map (fun j => BOfRec (RVar j)) (rec_index ctx i)
                        | _ => None
                        end
              end
  | tConstruct i 0 _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then Some BTrue else None
  | tConstruct i 1 _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then Some BFalse else None
  | tConst kn _ => match hb kn with Some b => reify_b fuel ctx b | None => None end
  | tApp (tLambda _ _ _ as f) args => reify_b fuel ctx (wout f args)
  | tApp (tLetIn _ _ _ _ as f) args => reify_b fuel ctx (wout f args)
  | tApp (tRel i) args => match nth_error ctx i with Some (CFn _ t) => reify_b fuel ctx (wout (capsub ctx t) args) | _ => None end
  | tApp (tConst kn _) args0 =>
      let reify_args (l : list term) : option sexps :=
        to_args (map (fun a => match reify fuel ctx a with Some e => Some (inl e) | None =>
                                match reify_b fuel ctx a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel ctx a) end end) l) in
      (* a call of a function of the program giving back a boolean (step 24), else a helper written out *)
      let helper := fun _ : unit =>
        let '(kn1, args1) := tcall ctx kn args0 in
        match find_callee kn1 callees 0 with
        | Some (f, gs) =>
            match sq gs with
            | Some KBool =>
                if sr gs || sw gs || negb (Nat.leb (sn gs) (length args1)) then None else
                match opt_all (map (reify_c fuel ctx) (firstn (sn gs) args1)), read_mem ctx (sm gs) (skipn (sn gs) args1) with
                | Some cs, Some nums => option_map (BCall f (to_scnts cs)) (reify_args nums)
                | _, _ => None
                end
            | _ => None
            end
        | None => match hb kn with Some b => reify_b fuel ctx (wout b args0) | None => None end
        end in
      let args := args0 in
      match args with
      | [a] => if Kername.eqb kn kn_negb then option_map BNot (reify_b fuel ctx a)
               (* (step 70) *)
               else if Kername.eqb kn kn_c_even then option_map BEven (reify_c fuel ctx a)
               else if Kername.eqb kn kn_c_odd then option_map (fun c => BNot (BEven c)) (reify_c fuel ctx a)
               else helper tt
      | [a; b] =>
          if Kername.eqb kn kn_andb then
            match reify_b fuel ctx a, reify_b fuel ctx b with Some x, Some y => Some (BAnd x y) | _, _ => None end
          else if Kername.eqb kn kn_orb then
            match reify_b fuel ctx a, reify_b fuel ctx b with Some x, Some y => Some (BOr x y) | _, _ => None end
          else
            match ncmp_v kn with
            | Some c => match reify_c fuel ctx a, reify_c fuel ctx b with Some x, Some y => Some (BCmpC c x y) | _, _ => None end
            | None =>
            match (if eq_mp (fst kn) prim_mp then cmp_v (snd kn) else None) with
            | Some c => match reify fuel ctx a, reify fuel ctx b with Some x, Some y => Some (BCmp c x y) | _, _ => None end
            | None => helper tt
            end
            end
      | _ => helper tt
      end
  (* a boolean chosen by a test of one comparison, or by a match on a counter variable (step 22) *)
  | tCase ci p c0 [b0; b1] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        match (match bnorm fuel c0 with
               | tApp (tConst kn _) [a; b] => if eq_mp (fst kn) prim_mp then option_map (fun x => (x, a, b)) (cmp_v (snd kn)) else None
               | _ => None
               end) with
        | Some (cmp, a, b) =>
            match reify fuel ctx a, reify fuel ctx b, reify_b fuel ctx (bbody b0), reify_b fuel ctx (bbody b1) with
            | Some x, Some y, Some t1, Some t2 => Some (BIfCmp cmp x y t1 t2)
            | _, _, _, _ => None
            end
        | None =>     (* a test on a boolean (step 36) *)
            match reify_b fuel ctx c0, reify_b fuel ctx (bbody b0), reify_b fuel ctx (bbody b1) with
            | Some x, Some t1, Some t2 => Some (BxIfB x t1 t2)
            | _, _, _ => None
            end
        end
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c0 with
        | tRel i =>
            match cnt_index ctx i, reify_b fuel ctx (bbody b0), reify_b fuel (CCnt :: ctx) (bbody b1) with
            | Some x, Some t0, Some t1 => Some (BMatchCnt x t0 t1)
            | _, _, _ => None
            end
        | _ => match known_branch c0 b0 b1 with Some t => reify_b fuel ctx t | None => reify_b fuel ctx (let_scrut ci p c0 b0 b1) end
        end
      else None
  (* a record taken apart (step 36): a helper giving one back written out first, the lets it starts with first *)
  | tCase ci p c0 [br] =>
      let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
      match lets_first ci p c [br] with Some t' => reify_b fuel ctx t' | None =>
        match reify_r fuel ctx c, (match rbr ci p br with Some (es0, bd0) => reify_b fuel (es0 ++ ctx) bd0 | None => None end) with
        | Some x, Some e => Some (BxMatchR x e)
        | _, _ => match rbs ci p br, reify_r fuel ctx c with
                  | Some (rj, es1, bd1), Some x => option_map (BxSplitR rj x) (reify_b fuel (es1 ++ ctx) bd1)
                  | _, _ => match iota_pair ci p c br with Some t' => reify_b fuel ctx t' | None => None end end
        end
      end
  (* lets of every kind (step 36) *)
  | tLetIn _ b ty body =>
      if is_ty kn_int ty then match reify fuel ctx b, reify_b fuel (CNum :: ctx) body with Some e, Some x => Some (BxLet e x) | _, _ => None end
      else if is_bool ty then match reify_b fuel ctx b, reify_b fuel (CBool :: ctx) body with Some y, Some x => Some (BxLetB y x) | _, _ => None end
      else if is_nat ty then match reify_c fuel ctx b, reify_b fuel (CCnt :: ctx) body with Some c, Some x => Some (BxLetC c x) | _, _ => None end
      else if is_ty kn_mem ty then None
      else match reify_r fuel ctx b, reify_b fuel (CRec :: ctx) body with Some y, Some x => Some (BxLetR y x) | _, _ => None end
  | _ => None
  end
  end
  end
  end.

(** a memory: the newest one, a write, lets, a test, a match on a counter, the recursive call or a call giving back a
    memory, on the memory written as its last argument *)
Definition is_rel (t : term) : bool := match t with tRel _ => true | _ => false end.

(* the memory and the pair readers are one mutual fixpoint (step 44): a memory takes a pair apart *)
Fixpoint reify_m (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option smem :=
  match fuel with
  | O => None
  | S fuel =>
  let reify_args (l : list term) : option sexps :=
    to_args (map (fun a => match reify fuel ctx a with Some e => Some (inl e) | None =>
                            match reify_b fuel ctx a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel ctx a) end end) l) in
  let reify_cs (l : list term) : option scnts := option_map to_scnts (opt_all (map (reify_c fuel ctx) l)) in
  match (match head_r t with Some t' => reify_m fuel ctx t' | None =>
  match tag_parts t with
  | Some (ri, ws, c, bs) =>
      match reify_r fuel ctx c, opt_all (map (reify_m fuel (tag_ents ri ws ++ ctx)) bs) with
      | Some x, Some es => option_map (if rgen ri then MSplitR ri x else MMatchR x) (tag_chain (fun k e r => MIf Ceq (fst (tag_test ws k)) (snd (tag_test ws k)) e r) es 0)
      | _, _ => None
      end
  | None =>
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
        let '(kn1, args1) := tcall ctx kn args in
        match find_callee kn1 callees 0 with
        | Some (f, gs) =>
            let args := args1 in
            if sr gs && sm gs && Nat.leb (sn gs) (length args) then
              match rev (skipn (sn gs) args) with
              | m :: rnums =>
                  match reify_cs (firstn (sn gs) args), reify_args (rev rnums), reify_m fuel ctx m with
                  | Some cs, Some As, Some d => Some (MCall f cs As d)
                  | Some cs, Some As, None =>
                      (* a whole pair given for the last number and the memory (step 44) *)
                      if sp gs then option_map (MCallP f cs As) (reify_pv fuel ctx m) else None
                  | _, _, _ => None
                  end
              | [] => None
              end
            else None
        | None => match hb kn with Some b => reify_m fuel ctx (wout b args) | None => None end
        end
  | tApp (tRel fi) args00 =>
      let args0 := self_perm ctx fi args00 in
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
  | tApp (tLetIn _ _ _ _ as f) args => reify_m fuel ctx (wout f args)
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
        | _ => match known_branch c b0 b1 with Some t => reify_m fuel ctx t | None => reify_m fuel ctx (let_scrut ci p c b0 b1) end
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
      else if is_pm ty then
        (* a number and a memory bound by a let, read through fst and snd (step 44, as XLetP) *)
        match reify_pv fuel ctx b, reify_m fuel (CMem :: CNum :: kill_mem ctx) (pm_split ty body) with
        | Some p, Some m => Some (MLetP p m)
        | _, _ => None
        end
      else match reify_r fuel ctx b, reify_m fuel (CRec :: ctx) body with Some x, Some y => Some (MLetR x y) | _, _ => None end
  | tCase ci p c0 [br] =>
      (* a record taken apart; a number and a memory taken apart (step 44): the number below the memory, every older memory dead *)
      let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
      match lets_first ci p c [br] with Some t' => reify_m fuel ctx t' | None =>
      if is_pm_case ci p br then
        match iota_pair ci p c br with Some t' => reify_m fuel ctx t' | None =>
        match reify_pv fuel ctx c, reify_m fuel (CMem :: CNum :: kill_mem ctx) (bbody br) with
        | Some x, Some y => Some (MMatchP x y)
        | _, _ => None
        end end
      else
      match reify_r fuel ctx c, (match rbr ci p br with Some (es0, bd0) => reify_m fuel (es0 ++ ctx) bd0 | None => None end) with
      | Some x, Some m => Some (MMatchR x m)
      | _, _ => match rbs ci p br, reify_r fuel ctx c with
                | Some (rj, es1, bd1), Some x => option_map (MSplitR rj x) (reify_m fuel (es1 ++ ctx) bd1)
                | _, _ => match iota_pair ci p c br with Some t' => reify_m fuel ctx t' | None => None end end
      end
      end
  | _ => None
  end
  end
  end) with
  | Some x => Some x
  | None => match hoist_read ctx t with Some t' => reify_m fuel ctx t' | None => None end
  end
  end
(* a number and a memory (step 26): built, given back by a function of the program or by the function itself, chosen by a
    test or a counter's match, after lets, or made from another one taken apart *)
with reify_pv (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option spv :=
  match fuel with
  | O => None
  | S fuel =>
  let reify_args (c : list cent) (l : list term) : option sexps :=
    to_args (map (fun a => match reify fuel c a with Some e => Some (inl e) | None =>
                            match reify_b fuel c a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel c a) end end) l) in
  let reify_cs (c : list cent) (l : list term) : option scnts := option_map to_scnts (opt_all (map (reify_c fuel c) l)) in
  match (match head_r t with Some t' => reify_pv fuel ctx t' | None =>
  match tag_parts t with
  | Some (ri, ws, c, bs) =>
      match reify_r fuel ctx c, opt_all (map (reify_pv fuel (tag_ents ri ws ++ ctx)) bs) with
      | Some x, Some es => option_map (if rgen ri then PvSplitR ri x else PvMatchR x) (tag_chain (fun k e r => PvIf Ceq (fst (tag_test ws k)) (snd (tag_test ws k)) e r) es 0)
      | _, _ => None
      end
  | None =>
  match t with
  | tApp (tConstruct ind 0 _) [a; b; e; m] =>
      if Kername.eqb (inductive_mind ind) (inductive_mind ind_prod) && is_ty kn_int a && is_ty kn_mem b then
        match reify fuel ctx e, reify_m fuel ctx m with Some x, Some y => Some (PvMk x y) | _, _ => None end
      else None
  | tApp (tConst kn _) args =>
      let '(kn1, args1) := tcall ctx kn args in
      match find_callee kn1 callees 0, rev args1 with
      | Some (f, gs), m :: rnums =>
          if match sq gs with Some KNum => true | _ => false end && Nat.leb (sn gs) (length (rev rnums)) then
            let rest := rev rnums in
            match reify_m fuel ctx m, reify_cs ctx (firstn (sn gs) rest), reify_args ctx (skipn (sn gs) rest) with
            | Some mm, Some cs, Some As => Some (PvCall f cs As mm)
            | None, Some cs, Some As => if sp gs then option_map (PvCallP f cs As) (reify_pv fuel ctx m) else None
            | _, _, _ => None
            end
          else None
      | None, _ => match hb kn with Some b => reify_pv fuel ctx (wout b args) | None => None end
      | _, _ => None
      end
  | tConst kn _ => match hb kn with Some b => reify_pv fuel ctx b | None => None end
  | tApp (tLambda _ _ _ as f) args => reify_pv fuel ctx (wout f args)
  | tApp (tLetIn _ _ _ _ as f) args => reify_pv fuel ctx (wout f args)
  | tApp (tRel fi) args00 =>
      let args0 := self_perm ctx fi args00 in
      match nth_error ctx fi, args0 with
      | Some (CFn _ t), _ => reify_pv fuel ctx (wout (capsub ctx t) args0)
      | _, tRel mi :: rest0 =>
          if is_ent CSelf ctx fi then
            (* the function itself, given a memory made from the newest one *)
            match option_map (with_caps ctx) (drop_fns ctx fd rest0) with
            | Some rest =>
                if is_ent CPred ctx mi && Nat.leb fnx (length rest) then
                  match rev (skipn fnx rest) with
                  | m :: rnums =>
                      match reify_cs ctx (firstn fnx rest), reify_args ctx (rev rnums), reify_m fuel ctx m with
                      | Some cs, Some As, Some d => Some (PvRec cs As d)
                      | _, _, _ => None
                      end
                  | [] => None
                  end
                else None
            | None => None
            end
          else None
      | _, _ => None
      end
  | tCase ci p c0 [b0; b1] =>
      let c := if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then bnorm fuel c0 else c0 in
      match lets_first ci p c [b0; b1] with Some t' => reify_pv fuel ctx t' | None =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        match (match c with
               | tApp (tConst kn _) [a; b] => if eq_mp (fst kn) prim_mp then option_map (fun x => (x, a, b)) (cmp_v (snd kn)) else None
               | _ => None
               end) with
        | Some (cmp, a, b) =>
            match reify fuel ctx a, reify fuel ctx b, reify_pv fuel ctx (bbody b0), reify_pv fuel ctx (bbody b1) with
            | Some x, Some y, Some t1, Some t2 => Some (PvIf cmp x y t1 t2)
            | _, _, _, _ => None
            end
        | None =>
            match reify_b fuel ctx c, reify_pv fuel ctx (bbody b0), reify_pv fuel ctx (bbody b1) with
            | Some x, Some t1, Some t2 => Some (PvIfB x t1 t2)
            | _, _, _ => None
            end
        end
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel i =>
            match cnt_index ctx i, reify_pv fuel ctx (bbody b0), reify_pv fuel (CCnt :: ctx) (bbody b1) with
            | Some x, Some t0, Some t1 => Some (PvMatch x t0 t1)
            | _, _, _ => None
            end
        | _ => match known_branch c b0 b1 with Some t => reify_pv fuel ctx t | None => reify_pv fuel ctx (let_scrut ci p c b0 b1) end
        end
      else None
      end
  | tCase ci p c0 [br] =>
      let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
      match lets_first ci p c [br] with Some t' => reify_pv fuel ctx t' | None =>
      match iota_pair ci p c br with Some t' => reify_pv fuel ctx t' | None =>
      if is_pm_case ci p br then
        (* a number and a memory taken apart: the number below the memory, every older memory dead *)
        match reify_pv fuel ctx c, reify_pv fuel (CMem :: CNum :: kill_mem ctx) (bbody br) with
        | Some x, Some y => Some (PvMatchP x y)
        | _, _ => None
        end
      else
        match reify_r fuel ctx c, (match rbr ci p br with Some (es0, bd0) => reify_pv fuel (es0 ++ ctx) bd0 | None => None end) with
        | Some x, Some e => Some (PvMatchR x e)
        | _, _ => match rbs ci p br, reify_r fuel ctx c with
                  | Some (rj, es1, bd1), Some x => option_map (PvSplitR rj x) (reify_pv fuel (es1 ++ ctx) bd1)
                  | _, _ => None end
        end
      end
      end
  | tLetIn _ b ty body =>
      if is_ty kn_mem ty then
        match reify_m fuel ctx b, reify_pv fuel (CMem :: kill_mem ctx) body with Some m, Some x => Some (PvLetM m x) | _, _ => None end
      else if is_ty kn_int ty then
        match reify fuel ctx b, reify_pv fuel (CNum :: ctx) body with Some e, Some x => Some (PvLet e x) | _, _ => None end
      else if is_bool ty then
        match reify_b fuel ctx b, reify_pv fuel (CBool :: ctx) body with Some e, Some x => Some (PvLetB e x) | _, _ => None end
      else if is_nat ty then
        match reify_c fuel ctx b, reify_pv fuel (CCnt :: ctx) body with Some c, Some x => Some (PvLetC c x) | _, _ => None end
      else if is_pm ty then None
      else match reify_r fuel ctx b, reify_pv fuel (CRec :: ctx) body with Some r, Some x => Some (PvLetR r x) | _, _ => None end
  | _ => None
  end
  end
  end) with
  | Some x => Some x
  | None => match hoist_read ctx t with Some t' => reify_pv fuel ctx t' | None => None end
  end
  end.

(** a number made after memories: lets of memories, numbers and booleans, tests, and at the end a number from the newest
    memory.  A read or a call whose memory is made in place ([rd h i (f .. s)]) is read as [let s2 := f .. s in rd h i s2] --
    the same term up to [let]; its numbers are read with the older memories dead, so they may not name one *)
(** a let inside an argument: up to zeta the let first (step 55) *)
Fixpoint float_op (fuel : nat) (t : term) : option term :=
  match fuel with
  | O => None
  | S fuel =>
      match t with
      | tApp f args =>
          let fix go (l pre : list term) : option term :=
            match l with
            | [] => None
            | a :: r =>
                match (match a with tLetIn _ _ _ _ => Some a | _ => float_op fuel a end) with
                | Some (tLetIn na e ty b) => Some (tLetIn na e ty (tApp (lift0 1 f) (map (lift0 1) (rev pre) ++ b :: map (lift0 1) r)))
                | _ => go r (a :: pre)
                end
            end in
          go args []
      | _ => None
      end
  end.
(** whether a term calls the function being read *)
Fixpoint has_self (fuel : nat) (ctx : list cent) (d : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tApp (tRel i) args =>
          if (if Nat.leb d i then is_ent CSelf ctx (i - d) else false) then true
          else existsb (has_self fuel ctx d) args
      | tApp f args => if has_self fuel ctx d f then true else existsb (has_self fuel ctx d) args
      | tLetIn _ b _ body => if has_self fuel ctx d b then true else has_self fuel ctx (S d) body
      | tLambda _ _ b => has_self fuel ctx (S d) b
      | tCase _ _ c brs =>
          if has_self fuel ctx d c then true
          else existsb (fun br => has_self fuel ctx (d + length (bcontext br)) (bbody br)) brs
      | _ => false
      end
  end.
Fixpoint reify_x (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sx :=
  match fuel with
  | O => None
  | S fuel =>
  let fallback := if has_self 1000 ctx 0 t then None else
                  match reify fuel ctx t with Some e => Some (XRet e) | None =>
                  match reify_b fuel ctx t with Some b => Some (XRetB b) | None => option_map (XRetR 0) (reify_r fuel ctx t) end end in
  let reify_args (c : list cent) (l : list term) : option sexps :=
    to_args (map (fun a => match reify fuel c a with Some e => Some (inl e) | None =>
                            match reify_b fuel c a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel c a) end end) l) in
  let reify_cs (c : list cent) (l : list term) : option scnts := option_map to_scnts (opt_all (map (reify_c fuel c) l)) in
  (* (step 47) [let v := b in body], b a call of a function that writes, of one given a pair not built in place, of the function
     itself: what follows on the memory the call was given, or (after a call that writes) reading no memory *)
  let bindc (bq : bool) (b body : term) : option sx :=
    let cv := if bq then CBool else CNum in
    let after (w : bool) :=
      if w then match reify fuel (cv :: kill_mem ctx) body with
                | Some e => Some (XRet e)
                | None => match reify_b fuel (cv :: kill_mem ctx) body with   (* (step 48 continued) a boolean, a record *)
                          | Some b => Some (XRetB b)
                          | None => option_map (XRetR 0) (reify_r fuel (cv :: kill_mem ctx) body)
                          end
                end
      else reify_x fuel (cv :: ctx) body in
    match b with
    | tApp (tConst kn _) args =>
        let '(kn1, args1) := tcall ctx kn args in
        match find_callee kn1 callees 0, rev args1 with
        | Some (f, gs), m :: rnums =>
            let rest := rev rnums in
            if negb (sr gs) && Nat.leb (sn gs) (length rest) then
              if sp gs && negb (pair_lit m) then
                match reify_pv fuel ctx m, reify_cs ctx (firstn (sn gs) rest), reify_args ctx (skipn (sn gs) rest), after (sw gs) with
                | Some p, Some cs, Some As, Some x => Some (XBindP bq f cs As p x)
                | _, _, _, _ => None
                end
              else if sw gs && sm gs && negb (sp gs) then
                match reify_m fuel ctx m, reify_cs ctx (firstn (sn gs) rest), reify_args ctx (skipn (sn gs) rest), after true with
                | Some mm, Some cs, Some As, Some x => Some (XBind bq f cs As mm x)
                | _, _, _, _ => None
                end
              else None
            else None
        | _, _ => None
        end
    | tApp (tRel fi) args00 =>
        match self_perm ctx fi args00 with
        | tRel mi :: rest0 =>
            if is_ent CSelf ctx fi && is_ent CPred ctx mi then
              match option_map (with_caps ctx) (drop_fns ctx fd rest0) with
              | Some rest =>
                  if Nat.leb fnx (length rest) then
                    match rev (skipn fnx rest) with
                    | m :: rnums =>
                        match reify_cs ctx (firstn fnx rest), reify_args ctx (rev rnums), reify_m fuel ctx m, after true with
                        | Some cs, Some As, Some d, Some x => Some (if bq then XBindRB cs As d x else XBindR cs As d x)
                        | _, _, _, _ => None
                        end
                    | [] => None
                    end
                  else None
              | None => None
              end
            else None
        | _ => None
        end
    | _ => None
    end in
  match (match head_r t with Some t' => reify_x fuel ctx t' | None =>
  match tag_parts t with
  | Some (ri, ws, c, bs) =>
      match reify_r fuel ctx c, opt_all (map (reify_x fuel (tag_ents ri ws ++ ctx)) bs) with
      | Some x, Some es => option_map (if rgen ri then XSplitR ri x else XMatchR x) (tag_chain (fun k e r => XIf Ceq (fst (tag_test ws k)) (snd (tag_test ws k)) e r) es 0)
      | _, _ => None
      end
  | None =>
  match t with
  | tLetIn _ b ty body =>
      if is_ty kn_mem ty then
        match reify_m fuel ctx b, reify_x fuel (CMem :: kill_mem ctx) body with Some m, Some x => Some (XLetM m x) | _, _ => None end
      else if is_pm ty then
        (* a number and a memory bound by a let, read through fst and snd (step 26) *)
        match reify_pv fuel ctx b, reify_x fuel (CMem :: CNum :: kill_mem ctx) (pm_split ty body) with
        | Some p, Some x => Some (XLetP p x)
        | _, _ => None
        end
      else if is_ty kn_int ty then
        (* the function's own call: bound; inside a number: bound first, by the fallback (step 52) *)
        if has_self 1000 ctx 0 b then match b with tApp (tRel _) _ => bindc false b body | _ => None end else
        match reify fuel ctx b, reify_x fuel (CNum :: ctx) body with Some e, Some x => Some (XLet e x) | _, _ => bindc false b body end
      else if is_bool ty then
        if has_self 1000 ctx 0 b then match b with tApp (tRel _) _ => bindc true b body | _ => None end else
        match reify_b fuel ctx b, reify_x fuel (CBool :: ctx) body with Some e, Some x => Some (XLetB e x) | _, _ => bindc true b body end
      else if is_nat ty then
        match reify_c fuel ctx b, reify_x fuel (CCnt :: ctx) body with Some c, Some x => Some (XLetC c x) | _, _ => None end
      (* the function's own call inside the record: bound first, by the fallback (step 55) *)
      else if (if has_self 1000 ctx 0 b then match b with tApp (tRel _) _ => false | _ => true end else false) then None
      else match reify_r fuel ctx b, reify_x fuel (CRec :: ctx) body with
           | Some r, Some x => Some (XLetR r x)
           | _, _ =>
               (* (step 48) a call given a pair not built in place, giving back a record *)
               match b with
               | tApp (tConst kn _) args =>
                   let '(kn1, args1) := tcall ctx kn args in
                   match find_callee kn1 callees 0, rev args1 with
                   | Some (f, gs), m :: rnums =>
                       let rest := rev rnums in
                       (* (step 48 continued) after a call that writes, what follows reads no memory: a number, a boolean, a record *)
                       let afterR (w : bool) :=
                         if w then match reify fuel (CRec :: kill_mem ctx) body with
                                   | Some e => Some (XRet e)
                                   | None => match reify_b fuel (CRec :: kill_mem ctx) body with
                                             | Some b => Some (XRetB b)
                                             | None => option_map (XRetR 0) (reify_r fuel (CRec :: kill_mem ctx) body)
                                             end
                                   end
                         else reify_x fuel (CRec :: ctx) body in
                       match sq gs with
                       | Some (KRec ri) =>
                           if negb (sr gs) && Nat.leb (sn gs) (length rest) then
                             if sp gs && negb (pair_lit m) then
                               match reify_pv fuel ctx m, reify_cs ctx (firstn (sn gs) rest), reify_args ctx (skipn (sn gs) rest), afterR (sw gs) with
                               | Some p, Some cs, Some As, Some x => Some (XBindPR ri f cs As p x)
                               | _, _, _, _ => None
                               end
                             else if sw gs && sm gs && negb (sp gs) then
                               (* (step 48 continued) a call of a function giving back a record that writes, on a memory *)
                               match reify_m fuel ctx m, reify_cs ctx (firstn (sn gs) rest), reify_args ctx (skipn (sn gs) rest), afterR true with
                               | Some mm, Some cs, Some As, Some x => Some (XBindRM ri f cs As mm x)
                               | _, _, _, _ => None
                               end
                             else None
                           else None
                       | _ => None
                       end
                   | _, _ => None
                   end
               | tApp (tRel fi) args00 =>
                   (* (step 48 continued) the function's own call, giving back a record: what follows reads no memory *)
                   let aftR := match reify fuel (CRec :: kill_mem ctx) body with
                               | Some e => Some (XRet e)
                               | None => match reify_b fuel (CRec :: kill_mem ctx) body with
                                         | Some b => Some (XRetB b)
                                         | None => option_map (XRetR 0) (reify_r fuel (CRec :: kill_mem ctx) body)
                                         end
                               end in
                   match self_perm ctx fi args00 with
                   | tRel mi :: rest0 =>
                       if is_ent CSelf ctx fi && is_ent CPred ctx mi then
                         match option_map (with_caps ctx) (drop_fns ctx fd rest0) with
                         | Some rest =>
                             if Nat.leb fnx (length rest) then
                               match rev (skipn fnx rest) with
                               | m :: rnums =>
                                   match reify_cs ctx (firstn fnx rest), reify_args ctx (rev rnums), reify_m fuel ctx m, aftR with
                                   | Some cs, Some As, Some d, Some x => Some (XBindRR 0 cs As d x)
                                   | _, _, _, _ => None
                                   end
                               | [] => None
                               end
                             else None
                         | None => None
                         end
                       else None
                   | _ => None
                   end
               | _ => None
               end
           end
  | tCase ci p c0 [br] =>
      (* a record taken apart, the number after it made after memories; or a number *)
      let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
      match lets_first ci p c [br] with Some t' => reify_x fuel ctx t' | None =>
      match reify_r fuel ctx c, (match rbr ci p br with Some (es0, bd0) => reify_x fuel (es0 ++ ctx) bd0 | None => None end) with
      | Some r, Some x => Some (XMatchR r x)
      | _, _ =>
          match iota_pair ci p c br with
          | Some t' => reify_x fuel ctx t'
          | None =>
              (* a number and a memory taken apart (step 26): the number below the memory, every older memory dead *)
              if is_pm_case ci p br then
                match reify_pv fuel ctx c, reify_x fuel (CMem :: CNum :: kill_mem ctx) (bbody br) with
                | Some x, Some y => Some (XMatchP x y)
                | _, _ => fallback
                end
              else match rbs ci p br, reify_r fuel ctx c with
                   | Some (rj, es1, bd1), Some r => match reify_x fuel (es1 ++ ctx) bd1 with Some x => Some (XSplitR rj r x) | None => fallback end
                   | _, _ => fallback
                   end
          end
      end
      end
  | tApp (tLambda _ _ _ as f) args => reify_x fuel ctx (wout f args)
  | tApp (tLetIn _ _ _ _ as f) args => reify_x fuel ctx (wout f args)
  | tCase ci p c0 [b0; b1] =>
      if has_self 1000 ctx 0 c0 then None else
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
        | _ => match known_branch c b0 b1 with Some t => reify_x fuel ctx t | None => reify_x fuel ctx (let_scrut ci p c b0 b1) end
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
        let '(kn1, args1) := tcall ctx kn args in
        match find_callee kn1 callees 0, rev args1 with
        | Some (f, gs), m :: rnums =>
            match (if sp gs && negb (sr gs) && negb (isq gs) && Nat.leb (sn gs) (length (rev rnums)) then
                     match reify_pv fuel ctx m, reify_cs ctx (firstn (sn gs) (rev rnums)), reify_args ctx (skipn (sn gs) (rev rnums)) with
                     | Some p, Some cs, Some As => Some (XCallP f cs As p)    (* a whole pair given (step 44) *)
                     | _, _, _ => None
                     end
                   else None) with Some x => Some x | None =>
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
              | Some mm, Some cs, Some As =>
                  Some (match sq gs with
                        | Some KBool => XBind true f cs As mm (XRetB (BVar 0))
                        | Some (KRec ri) => XBindRM ri f cs As mm (XRetR ri (RVar 0))
                        | _ => XCall f cs As mm
                        end)
              | _, _, _ => None
              end
            else fallback
            end
        | None, _ => match hb kn with Some b => reify_x fuel ctx (wout b args) | None => fallback end
        | _, _ => fallback
        end
  | tConst kn _ => match hb kn with Some b => reify_x fuel ctx b | None => fallback end
  | tApp (tRel fi) args00 =>
      let args0 := self_perm ctx fi args00 in
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
  end
  end) with
  | Some x => Some x
  | None =>
      let tryb (ot : option term) := match bind_first false ot ctx t with Some t' => reify_x fuel ctx t' | None => None end in
      match tryb None with
      | Some x => Some x
      | None => match tryb (Some (tInd ind_bool [])) with
                | Some x => Some x
                | None =>
                    match tryb (Some (tVar "kq_rec"%bs)) with
                    | Some x => Some x
                    | None =>
                        match (match hoist_read ctx t with Some t' => reify_x fuel ctx t' | None => None end) with
                        | Some x => Some x
                        (* (step 52) a memory made in place and read inside an expression: bound by a let *)
                        | None =>
                            match bind_first true None ctx t with
                            | Some t' => reify_x fuel ctx t'
                            | None => match float_op 100 t with Some t' => reify_x fuel ctx t' | None => None end
                            end
                        end
                    end
                end
      end
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
  let self_call (u0 : term) : option (scnts * sexps) :=
    let u := match u0 with tApp (tRel fi) args => tApp (tRel fi) (self_perm ctx fi args) | _ => u0 end in
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
  match (match head_r t with Some t' => reify_br fuel ctx t' | None =>
  match tag_parts t with
  | Some (ri, ws, c, bs) =>
      match reify_r fuel ctx c, opt_all (map (reify_br fuel (tag_ents ri ws ++ ctx)) bs) with
      | Some x, Some es => option_map (if rgen ri then BSplitR ri x else BMatchR x) (tag_chain (fun k e r => BIf Ceq (fst (tag_test ws k)) (snd (tag_test ws k)) e r) es 0)
      | _, _ => None
      end
  | None =>
  match self_call t with
  | Some (cs, a) => Some (BRec cs a)
  | None =>
  match t with
  | tApp (tLambda _ _ _ as f) args => reify_br fuel ctx (wout f args)
  | tApp (tLetIn _ _ _ _ as f) args => reify_br fuel ctx (wout f args)
  | tApp (tConst kn _) args =>
      match find_callee (fst (tcall ctx kn args)) callees 0, hb kn with
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
        | _ => match known_branch c b0 b1 with Some t => reify_br fuel ctx t | None => reify_br fuel ctx (let_scrut ci p c b0 b1) end
        end
      else None
      end
  | tCase ci p c0 [br] =>
      (* a record taken apart: the function itself, or a record (a helper giving one back written out first) *)
      let inner := (match rbr ci p br with Some (es0, bd0) => reify_br fuel (es0 ++ ctx) bd0 | None => None end) in
      match self_call c0 with
      | Some (cs, a) =>
          match inner with
          | Some e => Some (BMatchRec cs a e)
          | None => match rbs ci p br with
                    | Some (rj, es1, bd1) => option_map (fun e => BLetRec cs a (BSplitR rj (RVar 0) e)) (reify_br fuel (es1 ++ CRec :: ctx) (lift 1 (length es1) bd1))
                    | None => None
                    end
          end
      | None =>
          let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
          match lets_first ci p c [br] with Some t' => reify_br fuel ctx t' | None =>
            match reify_r fuel ctx c, inner with
            | Some x, Some e => Some (BMatchR x e)
            | _, _ => match iota_pair ci p c br with Some t' => reify_br fuel ctx t' | None =>
                      match rbs ci p br, reify_r fuel ctx c with
                      | Some (rj, es1, bd1), Some x => option_map (BSplitR rj x) (reify_br fuel (es1 ++ ctx) bd1)
                      | _, _ => None
                      end end
            end
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
  end
  end) with
  | Some r => Some r
  | None =>
      if fm then None else
      if has_self 1000 ctx 0 t then
        match bind_first false (Some (tVar "kq_rec"%bs)) ctx t with
        | Some t' => reify_br fuel ctx t'
        | None => match float_op 100 t with Some t' => reify_br fuel ctx t' | None => None end
        end
      else None
  end
  end.

(** a boolean given back (step 24): at the end a boolean, the function itself at the end or its negation, and lets, tests and
    a match on a counter around them.  At the end [a && b] is read as [if a then b else false] and [a || b] as [if a then true
    else b] -- the same terms, by the definitions of [andb] and [orb] -- so the function itself in [b] stays a loop, as C's
    short-circuit makes it (the translator's rule, F39) *)
Fixpoint reify_bb (fuel : nat) (ctx : list cent) (t : term) {struct fuel} : option sbb :=
  match fuel with
  | O => None
  | S fuel =>
  let reify_args (l : list term) : option sexps :=
    to_args (map (fun a => match reify fuel ctx a with Some e => Some (inl e) | None =>
                            match reify_b fuel ctx a with Some b => Some (inr (inl b)) | None => option_map (fun x => inr (inr x)) (reify_r fuel ctx a) end end) l) in
  (* the function itself: its counter's predecessor, its counters after the first, its numbers, the memory *)
  let self_call (u0 : term) : option (scnts * sexps) :=
    let u := match u0 with tApp (tRel fi) args => tApp (tRel fi) (self_perm ctx fi args) | _ => u0 end in
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
  (* a test: of one comparison, or of a boolean *)
  let test (c : term) (x y : option sbb) : option sbb :=
    match x, y with
    | Some t1, Some t2 =>
        let c := bnorm fuel c in
        match (match c with
               | tApp (tConst kn _) [a; b] => if eq_mp (fst kn) prim_mp then option_map (fun z => (z, a, b)) (cmp_v (snd kn)) else None
               | _ => None
               end) with
        | Some (cmp, a, b) => match reify fuel ctx a, reify fuel ctx b with Some u, Some v => Some (BbIf cmp u v t1 t2) | _, _ => None end
        | None => option_map (fun u => BbIfB u t1 t2) (reify_b fuel ctx c)
        end
    | _, _ => None
    end in
  match (match head_r t with Some t' => reify_bb fuel ctx t' | None =>
  match tag_parts t with
  | Some (ri, ws, c, bs) =>
      match reify_r fuel ctx c, opt_all (map (reify_bb fuel (tag_ents ri ws ++ ctx)) bs) with
      | Some x, Some es => option_map (if rgen ri then BbSplitR ri x else BbMatchR x) (tag_chain (fun k e r => BbIf Ceq (fst (tag_test ws k)) (snd (tag_test ws k)) e r) es 0)
      | _, _ => None
      end
  | None =>
  match self_call t with
  | Some (cs, a) => Some (BbRec cs a)
  | None =>
  match t with
  | tApp (tLambda _ _ _ as f) args => reify_bb fuel ctx (wout f args)
  | tApp (tLetIn _ _ _ _ as f) args => reify_bb fuel ctx (wout f args)
  | tApp (tConst kn _) [a] =>
      if Kername.eqb kn kn_negb then
        match self_call a with Some (cs, x) => Some (BbNotRec cs x) | None => option_map BbRet (reify_b fuel ctx t) end
      else match find_callee (fst (tcall ctx kn [a])) callees 0, hb kn with
           | None, Some b => reify_bb fuel ctx (wout b [a])
           | _, _ => option_map BbRet (reify_b fuel ctx t)
           end
  | tApp (tConst kn _) [a; b] =>
      if Kername.eqb kn kn_andb then test a (reify_bb fuel ctx b) (Some (BbRet BFalse))
      else if Kername.eqb kn kn_orb then test a (Some (BbRet BTrue)) (reify_bb fuel ctx b)
      else match find_callee (fst (tcall ctx kn [a; b])) callees 0, hb kn with
           | None, Some bd => reify_bb fuel ctx (wout bd [a; b])
           | _, _ => option_map BbRet (reify_b fuel ctx t)
           end
  | tApp (tConst kn _) args =>
      match find_callee (fst (tcall ctx kn args)) callees 0, hb kn with
      | None, Some b => reify_bb fuel ctx (wout b args)
      | _, _ => option_map BbRet (reify_b fuel ctx t)
      end
  | tCase ci p c0 [b0; b1] =>
      let c := if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then bnorm fuel c0 else c0 in
      match lets_first ci p c [b0; b1] with Some t' => reify_bb fuel ctx t' | None =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        test c (reify_bb fuel ctx (bbody b0)) (reify_bb fuel ctx (bbody b1))
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel i =>
            match cnt_index ctx i, reify_bb fuel ctx (bbody b0), reify_bb fuel (CCnt :: ctx) (bbody b1) with
            | Some x, Some e0, Some e1 => Some (BbMatch x e0 e1)
            | _, _, _ => None
            end
        | _ => match known_branch c b0 b1 with Some t => reify_bb fuel ctx t | None => reify_bb fuel ctx (let_scrut ci p c b0 b1) end
        end
      else None
      end
  | tCase ci p c0 [br] =>
      (* a record taken apart (a helper giving one back written out first) *)
      let c := match c0 with tApp (tConst kn _) args => match hb kn with Some hbd => wout hbd args | None => c0 end | _ => c0 end in
      match lets_first ci p c [br] with Some t' => reify_bb fuel ctx t' | None =>
        match reify_r fuel ctx c, (match rbr ci p br with Some (es0, bd0) => reify_bb fuel (es0 ++ ctx) bd0 | None => None end) with
        | Some x, Some e => Some (BbMatchR x e)
        | _, _ => match rbs ci p br, reify_r fuel ctx c with
                  | Some (rj, es1, bd1), Some x => option_map (BbSplitR rj x) (reify_bb fuel (es1 ++ ctx) bd1)
                  | _, _ => match iota_pair ci p c br with Some t' => reify_bb fuel ctx t' | None => None end end
        end
      end
  | tLetIn _ b ty body =>
      if is_ty kn_int ty then
        match reify fuel ctx b, reify_bb fuel (CNum :: ctx) body with Some x, Some y => Some (BbLet x y) | _, _ => None end
      else if is_bool ty then
        match self_call b with
        | Some (cs, a) => option_map (BbLetRec cs a) (reify_bb fuel (CBool :: ctx) body)
        | None => match reify_b fuel ctx b, reify_bb fuel (CBool :: ctx) body with Some x, Some y => Some (BbLetB x y) | _, _ => None end
        end
      else if is_nat ty then
        match reify_c fuel ctx b, reify_bb fuel (CCnt :: ctx) body with Some x, Some y => Some (BbLetC x y) | _, _ => None end
      else
        match reify_r fuel ctx b, reify_bb fuel (CRec :: ctx) body with Some x, Some y => Some (BbLetR x y) | _, _ => None end
  | _ => option_map BbRet (reify_b fuel ctx t)
  end
  end
  end
  end) with
  | Some r => Some r
  | None =>
      if fm then None else
      if has_self 1000 ctx 0 t then
        match bind_first false (Some (tInd ind_bool [])) ctx t with
        | Some t' => reify_bb fuel ctx t'
        | None => match float_op 100 t with Some t' => reify_bb fuel ctx t' | None => None end
        end
      else None
  end
  end.
End R.

Fixpoint lams (t : term) : list term * term :=
  match t with tLambda _ ty b => let '(l, r) := lams b in (ty :: l, r) | _ => ([], t) end.


(** the result type of a function type *)
Fixpoint ret_ty (t : term) : term :=
  match t with
  | tProd _ _ b => ret_ty b
  | tApp (tLambda _ _ b) [a] => subst10 a b
  | _ => t
  end.

(** the counters a parameter list starts with, and the parameters after them *)
Fixpoint lead_nats (tys : list term) : nat * list term :=
  match tys with
  | t :: r => if is_nat t then let '(n, l) := lead_nats r in (S n, l) else (O, tys)
  | [] => (O, [])
  end.

(** a signature off the parameter types and the result type: counters first, numbers, a memory last or not, a memory, a
    number, a boolean or a record of the program's types as the result *)
Definition kind_ty (rt : list rentry) (t : term) : option kind :=
  if is_ty kn_int t then Some KNum else if is_bool t then Some KBool else option_map KRec (rindex t rt 0).
(** the last parameter a number-and-memory pair (step 44): read as the last number and the memory, the signature flagged *)
Definition last_pm (tys : list term) : bool := match rev tys with t :: _ => is_pm t | [] => false end.
Definition with_sp (p : bool) (g : sig) : sig := mksig9 (sn g) (sk g) (sm g) (sr g) (sw g) (sq g) (sb g) (sv g) p.
Definition read_sig (rt : list rentry) (tys : list term) (ret : term) : option sig :=
  let '(c, rest) := lead_nats tys in
  let pm := last_pm rest in
  let m := pm || match rev rest with t :: _ => is_ty kn_mem t | [] => false end in
  let nums := if m then removelast rest else rest in
  let r := is_ty kn_mem ret in
  match option_map (fun ks => if pm then ks ++ [KNum] else ks) (opt_all (map (kind_ty rt) nums)) with
  | Some ks => if r || is_ty kn_int ret then Some (mksig c ks m r false None)
               else if is_bool ret then Some (mksig c ks m false false (Some KBool))
               else if is_pm ret then Some (mksig c ks m false false (Some KNum))
               else option_map (fun ri => mksig c ks m false false (Some (KRec ri))) (rindex ret rt 0)
  | None => None
  end.

(** whether a function gives back a boolean (step 24) *)
Definition isbq (gs : sig) : bool := match sq gs with Some KBool => true | _ => false end.
(** whether a function gives back a number and a memory (step 26) *)
Definition ispq (gs : sig) : bool := match sq gs with Some KNum => true | _ => false end.

Definition cent_of (k : kind) : cent := match k with KNum => CNum | KBool => CBool | KRec _ => CRec end.
Definition fun_ctx (gs : sig) : list cent := (if sm gs then [CMem] else []) ++ rev (map cent_of (sk gs)) ++ repeat CCnt (sn gs).

(** a function's parameters in the order the syntax takes (step 41): the recursion's counter, the other counters, the numbers,
    booleans and records, the memory -- each its place in the user's order *)
Definition canon_perm (tys : list term) (r : option nat) : list nat :=
  let ty i := nth i tys (tRel 0) in
  let idx := seq 0 (length tys) in
  let isr i := match r with Some r0 => Nat.eqb i r0 | None => false end in
  (match r with Some r0 => [r0] | None => [] end) ++ filter (fun i => is_nat (ty i) && negb (isr i)) idx
  ++ filter (fun i => negb (is_nat (ty i)) && negb (is_ty kn_mem (ty i))) idx
  ++ (match rev (filter (fun i => is_ty kn_mem (ty i)) idx) with m :: _ => [m] | [] => [] end).
Fixpoint pos_in (u : nat) (l : list nat) : nat := match l with [] => O | x :: r => if Nat.eqb x u then O else S (pos_in u r) end.
(** the context of such a body: each binder as the syntax takes it, a counter its index among the counters *)
Definition perm_ctx_m (dm : bool) (rt : list rentry) (tys : list term) (perm : list nat) : list cent :=
  let k := length (filter (fun i => is_nat (nth i tys (tRel 0))) perm) in
  map (fun u => let ty := nth u tys (tRel 0) in
                if is_nat ty then CCntP (Nat.sub (Nat.sub k 1) (pos_in u perm))
                else if is_ty kn_mem ty then (if dm && negb (existsb (Nat.eqb u) perm) then CDeadM else CMem)
                else match kind_ty rt ty with Some kd => cent_of kd | None => CDead end)
      (rev (seq 0 (length tys))).
(** whether a function's parameters stand in another order, and the order: none when the syntax's *)
Definition fun_perm (Σ : global_env) (kn : kername) : option (list nat) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      let pm := match cst_body cb with
                | Some (tFix [d] 0) => canon_perm (fst (lams (dbody d))) (Some (rarg d))
                | Some b => canon_perm (fst (lams b)) None
                | None => []
                end in
      if list_eq_dec Nat.eq_dec pm (seq 0 (length pm)) then None else Some pm
  | _ => None
  end.
(** one function of the program, given the ones before it, as its text reads: a recursive function starts with a match
    on its first counter *)
(** a call of a function whose last parameter is a number-and-memory pair (the function's own recursive call too), given a
    pair built in place: read with the pair's number and memory as its last two arguments, the components (step 44) *)
Definition pair_parts (t : term) : option (term * term) :=
  match t with
  | tApp (tConstruct i 0 _) [a; b; e; m] =>
      if Kername.eqb (inductive_mind i) (inductive_mind ind_prod) && is_ty kn_int a && is_ty kn_mem b then Some (e, m) else None
  | _ => None
  end.
Definition kn_pfst := kn_of <% @fst %>.
Definition kn_psnd := kn_of <% @snd %>.
Fixpoint flatp (fuel : nat) (isp : nat -> term -> bool) (d : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := flatp fuel isp in
      match t with
      | tApp f args =>
          (* [fst] and [snd] of the pair built in place: its number and its memory (iota) *)
          match (match f, args with
                 | tConst kn _, [_; _; c] =>
                     if Kername.eqb kn kn_pfst || Kername.eqb kn kn_psnd
                     then option_map (fun em => if Kername.eqb kn kn_pfst then fst em else snd em) (pair_parts c) else None
                 | _, _ => None
                 end) with
          | Some t' => go d t'
          | None =>
          let args' := map (go d) args in
          let f' := go d f in
          if isp d f then
            match rev args' with
            | a :: r => match pair_parts a with Some (e, m) => tApp f' (rev r ++ [e; m]) | None => tApp f' args' end
            | [] => tApp f' args'
            end
          else tApp f' args'
          end
      | tLambda na ty b => tLambda na ty (go (S d) b)
      | tLetIn na b ty body => tLetIn na (go d b) ty (go (S d) body)
      | tCase ci p c brs => tCase ci p (go d c) (map (fun br => {| bcontext := bcontext br; bbody := go (d + length (bcontext br)) (bbody br) |}) brs)
      | tProj pr c => tProj pr (go d c)
      | _ => t
      end
  end.
Definition isp_of (callees : list (kername * sig)) (self : option nat) (d : nat) (f : term) : bool :=
  match f with
  | tRel i => match self with Some k => Nat.eqb i (k + d) | None => false end
  | tConst kn _ => existsb (fun e => Kername.eqb (fst e) kn && sp (snd e)) callees
  | _ => false
  end.
(* a body: its pair parameter replaced by the pair of two new variables (the number, the memory), its calls given pairs built
   in place spread; a body with neither a pair parameter nor a flagged callee as it is *)
Definition pm_body (callees : list (kername * sig)) (tys : list term) (fx : bool) (body : term) : term :=
  if last_pm tys then flatp 100000 (isp_of callees (if fx then Some (S (length tys)) else None)) 0 (pm_split (last tys (tRel 0)) body)
  else if existsb (fun e => sp (snd e)) callees then flatp 100000 (isp_of callees None) 0 body else body.

(** a signature whose body writes (step 48 continued: a boolean read as an X body) *)
Definition wsig (g : sig) : sig := mksig9 (sn g) (sk g) (sm g) (sr g) true (sq g) (sb g) (sv g) (sp g).
(** an X body's records given the function's record type (step 48 continued: the reader leaves it 0) *)
Fixpoint xset_ri (ri : nat) (x : sx) : sx :=
  match x with
  | XRetR _ r => XRetR ri r
  | XLetM m x => XLetM m (xset_ri ri x)
  | XLet e x => XLet e (xset_ri ri x)
  | XLetB b x => XLetB b (xset_ri ri x)
  | XIf c a b x1 x2 => XIf c a b (xset_ri ri x1) (xset_ri ri x2)
  | XIfB b x1 x2 => XIfB b (xset_ri ri x1) (xset_ri ri x2)
  | XMatch c x0 x1 => XMatch c (xset_ri ri x0) (xset_ri ri x1)
  | XLetC c x => XLetC c (xset_ri ri x)
  | XLetR r x => XLetR r (xset_ri ri x)
  | XMatchR r x => XMatchR r (xset_ri ri x)
  | XMatchP p x => XMatchP p (xset_ri ri x)
  | XLetP p x => XLetP p (xset_ri ri x)
  | XSplitR sj r x => XSplitR sj r (xset_ri ri x)
  | XBind bq f cs a m x => XBind bq f cs a m (xset_ri ri x)
  | XBindR cs a m x => XBindR cs a m (xset_ri ri x)
  | XBindRB cs a m x => XBindRB cs a m (xset_ri ri x)
  | XBindRR _ cs a m x => XBindRR ri cs a m (xset_ri ri x)
  | XBindP bq f cs a p x => XBindP bq f cs a p (xset_ri ri x)
  | XBindPR rj f cs a p x => XBindPR rj f cs a p (xset_ri ri x)
  | XBindRM rj f cs a m x => XBindRM rj f cs a m (xset_ri ri x)
  | _ => x
  end.
Definition read_fun_c (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (kn : kername) : option (sig * fbody) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some (tFix [d] 0) =>
          if Nat.eqb (rarg d) 0 then
            let '(tys, body0) := lams (dbody d) in
            let body := pm_body callees tys true body0 in
            option_map (fun gb => (with_sp (last_pm tys) (fst gb), snd gb))
            match read_sig rt tys (ret_ty (dtype d)), body with
            | Some gs, tCase ci _ (tRel cnt) [b0; b1] =>
                let nx := Nat.pred (sn gs) in
                if negb (Nat.eqb (sn gs) 0) && Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat)
                   && Nat.eqb cnt ((if sm gs then 1 else 0) + length (sk gs) + nx) then
                  let ctx := fun_ctx gs ++ [CSelf] in
                  if ispq gs then
                    match reify_pv callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_pv callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                    | Some p0, Some p1 => Some (gs, FRecP p0 p1)
                    | _, _ => None
                    end
                  else if isbq gs then
                    match reify_bb callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_bb callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                    | Some r0, Some r1 => Some (gs, FRecB r0 r1)
                    | _, _ =>
                        (* (step 48 continued) a boolean whose body writes: an X body of booleans *)
                        if sm gs then
                          match reify_x callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_x callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                          | Some x0, Some x1 => Some (wsig gs, FRecX x0 x1)
                          | _, _ => None
                          end
                        else None
                    end
                  else if isq gs then
                    match reify_br callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_br callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                    | Some r0, Some r1 => Some (gs, FRecR r0 r1)
                    | _, _ =>
                        (* (step 48 continued) a record whose body writes: an X body of records *)
                        if sm gs then
                          match reify_x callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_x callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                          | Some x0, Some x1 => Some (wsig gs, FRecX (xset_ri (sqi gs) x0) (xset_ri (sqi gs) x1))
                          | _, _ => None
                          end
                        else None
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
          let '(tys, body0) := lams b in
          let body := pm_body callees tys false body0 in
          option_map (fun gb => (with_sp (last_pm tys) (fst gb), snd gb))
          match read_sig rt tys (ret_ty (cst_type cb)) with
          | Some gs =>
              let nx := Nat.pred (sn gs) in
              if ispq gs then option_map (fun r => (gs, FPlainP r)) (reify_pv callees (sm gs) nx hb tc [] rt 100000 (fun_ctx gs) body)
              else if isbq gs then
                match reify_bb callees (sm gs) nx hb tc [] rt 100000 (fun_ctx gs) body with
                | Some r => Some (gs, FPlainB r)
                | None => if sm gs then option_map (fun x => (wsig gs, FPlainX x)) (reify_x callees (sm gs) nx hb tc [] rt 100000 (fun_ctx gs) body) else None
                end
              else if isq gs then
                match reify_br callees (sm gs) nx hb tc [] rt 100000 (fun_ctx gs) body with
                | Some r => Some (gs, FPlainR r)
                | None => if sm gs then option_map (fun x => (wsig gs, FPlainX (xset_ri (sqi gs) x))) (reify_x callees (sm gs) nx hb tc [] rt 100000 (fun_ctx gs) body) else None
                end
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

(** the same, the parameters in another order (step 41): the body read with each binder at its place in the order the syntax
    takes, a recursive call's arguments put in that order ([CSelfP]) *)
Definition read_fun_p (dm : bool) (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (kn : kername) : option (sig * fbody) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some (tFix [d] 0) =>
          if true then
            let '(tys, body) := lams (dbody d) in
            let perm := canon_perm tys (Some (rarg d)) in
            match read_sig rt (map (fun i => nth i tys (tRel 0)) perm) (ret_ty (dtype d)), body with
            | Some gs, tCase ci _ (tRel cnt) [b0; b1] =>
                let nx := Nat.pred (sn gs) in
                if negb (Nat.eqb (sn gs) 0) && Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat)
                   && Nat.eqb cnt (Nat.sub (Nat.sub (length tys) 1) (rarg d)) then
                  let ctx := perm_ctx_m dm rt tys perm ++ [CSelfP perm] in
                  if ispq gs then
                    match reify_pv callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_pv callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                    | Some p0, Some p1 => Some (gs, FRecP p0 p1)
                    | _, _ => None
                    end
                  else if isbq gs then
                    match reify_bb callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_bb callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                    | Some r0, Some r1 => Some (gs, FRecB r0 r1)
                    | _, _ =>
                        (* (step 48 continued) a boolean whose body writes: an X body of booleans *)
                        if sm gs then
                          match reify_x callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_x callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                          | Some x0, Some x1 => Some (wsig gs, FRecX x0 x1)
                          | _, _ => None
                          end
                        else None
                    end
                  else if isq gs then
                    match reify_br callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_br callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                    | Some r0, Some r1 => Some (gs, FRecR r0 r1)
                    | _, _ =>
                        (* (step 48 continued) a record whose body writes: an X body of records *)
                        if sm gs then
                          match reify_x callees (sm gs) nx hb tc [] rt 100000 ctx (bbody b0), reify_x callees (sm gs) nx hb tc [] rt 100000 (CPred :: ctx) (bbody b1) with
                          | Some x0, Some x1 => Some (wsig gs, FRecX (xset_ri (sqi gs) x0) (xset_ri (sqi gs) x1))
                          | _, _ => None
                          end
                        else None
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
          let perm := canon_perm tys None in
          match read_sig rt (map (fun i => nth i tys (tRel 0)) perm) (ret_ty (cst_type cb)) with
          | Some gs =>
              let nx := Nat.pred (sn gs) in
              if ispq gs then option_map (fun r => (gs, FPlainP r)) (reify_pv callees (sm gs) nx hb tc [] rt 100000 (perm_ctx_m dm rt tys perm) body)
              else if isbq gs then
                match reify_bb callees (sm gs) nx hb tc [] rt 100000 (perm_ctx_m dm rt tys perm) body with
                | Some r => Some (gs, FPlainB r)
                | None => if sm gs then option_map (fun x => (wsig gs, FPlainX x)) (reify_x callees (sm gs) nx hb tc [] rt 100000 (perm_ctx_m dm rt tys perm) body) else None
                end
              else if isq gs then
                match reify_br callees (sm gs) nx hb tc [] rt 100000 (perm_ctx_m dm rt tys perm) body with
                | Some r => Some (gs, FPlainR r)
                | None => if sm gs then option_map (fun x => (wsig gs, FPlainX (xset_ri (sqi gs) x))) (reify_x callees (sm gs) nx hb tc [] rt 100000 (perm_ctx_m dm rt tys perm) body) else None
                end
              else if sr gs then option_map (fun m => (gs, FPlainM m)) (reify_m callees (sm gs) nx hb tc [] rt 100000 (perm_ctx_m dm rt tys perm) body)
              else match reify callees (sm gs) nx hb tc [] rt 100000 (perm_ctx_m dm rt tys perm) body with
                   | Some e => Some (gs, FPlain e)
                   | None => if sm gs then
                               option_map (fun x => (mksig (sn gs) (sk gs) true false true None, FPlainX x))
                                          (reify_x callees (sm gs) nx hb tc [] rt 100000 (perm_ctx_m dm rt tys perm) body)
                             else None
                   end
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(** one function of the program: as its text reads, its parameters in the syntax's order or not (step 41) *)
Definition read_fun (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (kn : kername) : option (sig * fbody) :=
  match fun_perm Σ kn with None => read_fun_c Σ hb tc rt callees kn | Some _ => read_fun_p false Σ hb tc rt callees kn end.

(** record types with these numbers of fields and nothing else: well-formedness reads only a record type's number of fields *)
(** the types of a record's record fields (step 43), by their indices in the table *)
Definition rjs (rt : list rentry) (ri : nat) : list nat :=
  match nth_error rt ri with
  | Some ((_, ft), _, _, _, _, g, _) =>
      match g, fst (fst (fst (fst (fst (fst (match nth_error rt ri with Some e => e | None => bool_entry end)))))) with
      | Some _, ([], _) => []
      | _, _ => flat_map (fun q => if is_ty kn_int q then [] else match rindex_f q rt with Some j => [j] | None => [] end) ft
      end
  | _ => []
  end.
(** (step 67) as [kitc.py] writes them for a program: which type is bool, which value's numbers are not free, a constructor's own slots *)
Definition rbi_of (rt : list rentry) (i : nat) : bool :=
  match nth_error rt i with Some (_, _, j, _, _, _, _) => Kername.eqb (inductive_mind j) (inductive_mind ind_bool) | None => false end.
Definition rnc_of (rt : list rentry) (i : nat) : bool :=
  match nth_error rt i with Some (mf, _, _, _, _, _, _) => match fst mf with [] => false | _ => true end | None => false end.
Definition rm_of (rt : list rentry) (i c : nat) : list bool :=
  match nth_error rt i with
  | Some (mf, _, _, _, _, Some ws, _) =>
      let nn := fold_left Nat.max ws O in
      map (fun s => existsb (fun p : bool * nat => if fst p then false else Nat.eqb (snd p) s) (nth c (fst mf) [])) (seq 0 (length (snd mf) - nn))
  | _ => []
  end.
Definition arity_recs (ars : list (nat * option (list nat))) (rt : list rentry) : RecTypes :=
  {| RT := fun _ => unit; RO := fun i => mkrops (fst (nth i ars (O, None))) (snd (nth i ars (O, None))) (fun _ => tt) (fun P _ k => k []);
     Rd := fun _ => tt; RS := fun i P _ k => k [] []; RB := fun _ _ _ => tt; RJ := rjs rt;
     RBl := fun _ _ => tt; RTb := fun _ _ => false; RBI := rbi_of rt; RNC := rnc_of rt; RM := rm_of rt |}.

(** the smallest bound of a function's own: above [kq_nat]'s 2^60 (step 33) *)
Definition own_bound : Z := (1152921504606846976 + 1048576 + 1)%Z.
(** the calls of a function's tree and its recursive calls, each with the counters' bounds in scope as [wf] tracks them
    (step 34; step 35: each counter variable below its own bound, a let's [lbnd], a match's predecessor the matched variable's;
    step 37: and each its linear bound over the function's counters), [B] the function's bound: the shape of KQR's shared-block
    check, [sh_*].  A call is its callee ([Some f]), a recursive call [None] *)
Definition cctx (B : Z) (bs : list cbe) : wfctx := ([], ((Some B, []), bs)).
Definition clet (B : Z) (bs : list cbe) (c : scnt) : list cbe := cpush_let (cctx B bs) c :: bs.
Definition cmt (B : Z) (bs : list cbe) (c : nat) : list cbe := cpush_match (cctx B bs) c :: bs.
Definition site : Type := (option nat * (list cbe * scnts))%type.
Fixpoint cl_e (B : Z) (bs : list cbe) (e : sexp) {struct e} : list site :=
  match e with
  | SVar _ | SInt _ | SFld _ _ => []
  | SOp _ a b | SLet a b | SRd a b => cl_e B bs a ++ cl_e B bs b
  | SRd32 a b | SRd8 a b => cl_e B bs a ++ cl_e B bs b
  | SIf _ a b t f => cl_e B bs a ++ cl_e B bs b ++ cl_e B bs t ++ cl_e B bs f
  | SRec ccs args => (None, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args
  | SCall f ccs args => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args
  | SMatch c e0 e1 => cl_e B bs e0 ++ cl_e B (cmt B bs c) e1
  | SIfB b t f => cl_b B bs b ++ cl_e B bs t ++ cl_e B bs f
  | SLetB b e => cl_b B bs b ++ cl_e B bs e
  | SLetC c e => cl_c B bs c ++ cl_e B (clet B bs c) e
  | SLetR x e | SMatchR x e | SSplitR _ x e => cl_r B bs x ++ cl_e B bs e
  | SOfC c => cl_c B bs c
  | SHwf _ args => cl_es B bs args
  | SSize h => cl_e B bs h
  end
with cl_es (B : Z) (bs : list cbe) (es : sexps) {struct es} : list site :=
  match es with
  | SNil => []
  | SCons e r => cl_e B bs e ++ cl_es B bs r
  | SConsB b r => cl_b B bs b ++ cl_es B bs r
  | SConsR x r => cl_r B bs x ++ cl_es B bs r
  end
with cl_c (B : Z) (bs : list cbe) (c : scnt) {struct c} : list site :=
  match c with CVar _ | CO => [] | CS c | KQR.CPred c | CDiv2 c | CMulK _ _ c => cl_c B bs c | CAdd a b | CMin a b | CMax a b | CSub a b | CDivN a b | CModN a b => cl_c B bs a ++ cl_c B bs b | CNat e | CToNat e | CToNatU e => cl_e B bs e | CIf b x y => cl_b B bs b ++ cl_c B bs x ++ cl_c B bs y end
with cl_cs (B : Z) (bs : list cbe) (cs : scnts) {struct cs} : list site :=
  match cs with CNil => [] | CCons c r => cl_c B bs c ++ cl_cs B bs r end
with cl_b (B : Z) (bs : list cbe) (b : sbool) {struct b} : list site :=
  match b with
  | BCmp _ x y => cl_e B bs x ++ cl_e B bs y
  | BVar _ | BTrue | BFalse => []
  | BAnd x y | BOr x y => cl_b B bs x ++ cl_b B bs y
  | BNot x => cl_b B bs x
  | BIfCmp _ a b x y => cl_e B bs a ++ cl_e B bs b ++ cl_b B bs x ++ cl_b B bs y
  | BMatchCnt c x0 x1 => cl_b B bs x0 ++ cl_b B (cmt B bs c) x1
  | BCall f ccs args => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args
  | BCmpC _ x y => cl_c B bs x ++ cl_c B bs y
  | BxIfB b x y => cl_b B bs b ++ cl_b B bs x ++ cl_b B bs y
  | BxLet e x => cl_e B bs e ++ cl_b B bs x
  | BxLetB b x => cl_b B bs b ++ cl_b B bs x
  | BxLetC c x => cl_c B bs c ++ cl_b B (clet B bs c) x
  | BxLetR y x | BxMatchR y x | BxSplitR _ y x => cl_r B bs y ++ cl_b B bs x
  | BOfRec y => cl_r B bs y
  | BEven c => cl_c B bs c
  end
with cl_r (B : Z) (bs : list cbe) (x : srec) {struct x} : list site :=
  match x with
  | RVar _ => []
  | RMk _ es => cl_es B bs es
  | RCall _ f ccs args => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args
  | RW64 _ _ a b => cl_r B bs a ++ cl_r B bs b
  | RLet e x => cl_e B bs e ++ cl_r B bs x
  | RLetR y x => cl_r B bs y ++ cl_r B bs x
  | RIf _ _ a b x y => cl_e B bs a ++ cl_e B bs b ++ cl_r B bs x ++ cl_r B bs y
  | RMatchR _ x y | RSplitR _ _ x y => cl_r B bs x ++ cl_r B bs y
  | RMkR _ ns rs => cl_es B bs ns ++ cl_es B bs rs
  | RIfB _ b x y => cl_b B bs b ++ cl_r B bs x ++ cl_r B bs y
  | RLetB b x => cl_b B bs b ++ cl_r B bs x
  | RLetC c x => cl_c B bs c ++ cl_r B (clet B bs c) x
  | RMatchCnt _ c x y => cl_r B bs x ++ cl_r B (cmt B bs c) y
  | RDflt _ => []
  | RBoolV _ b => cl_b B bs b
  end.
Fixpoint cl_m (B : Z) (bs : list cbe) (m : smem) {struct m} : list site :=
  match m with
  | MCur => []
  | MUpd h i v m => cl_e B bs h ++ cl_e B bs i ++ cl_e B bs v ++ cl_m B bs m
  | MUpd32 h i v m | MUpd8 h i v m => cl_e B bs h ++ cl_e B bs i ++ cl_e B bs v ++ cl_m B bs m
  | MLet e m => cl_e B bs e ++ cl_m B bs m
  | MLetM m1 m2 => cl_m B bs m1 ++ cl_m B bs m2
  | MIf _ a b m1 m2 => cl_e B bs a ++ cl_e B bs b ++ cl_m B bs m1 ++ cl_m B bs m2
  | MRec ccs args m => (None, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_m B bs m
  | MCall f ccs args m => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_m B bs m
  | MMatch c m0 m1 => cl_m B bs m0 ++ cl_m B (cmt B bs c) m1
  | MIfB b m1 m2 => cl_b B bs b ++ cl_m B bs m1 ++ cl_m B bs m2
  | MLetB b m => cl_b B bs b ++ cl_m B bs m
  | MLetC c m => cl_c B bs c ++ cl_m B (clet B bs c) m
  | MHw _ args m => cl_es B bs args ++ cl_m B bs m
  | MLetR x m | MMatchR x m | MSplitR _ x m => cl_r B bs x ++ cl_m B bs m
  | MMatchP p m | MLetP p m => cl_pv B bs p ++ cl_m B bs m
  | MCallP f ccs args p => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_pv B bs p
  end
with cl_pv (B : Z) (bs : list cbe) (p : spv) {struct p} : list site :=
  match p with
  | PvMk e m => cl_e B bs e ++ cl_m B bs m
  | PvCall f ccs args m => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_m B bs m
  | PvCallP f ccs args p => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_pv B bs p
  | PvRec ccs args m => (None, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_m B bs m
  | PvLet e p => cl_e B bs e ++ cl_pv B bs p
  | PvLetB c p => cl_b B bs c ++ cl_pv B bs p
  | PvLetC c p => cl_c B bs c ++ cl_pv B (clet B bs c) p
  | PvLetR x p | PvMatchR x p | PvSplitR _ x p => cl_r B bs x ++ cl_pv B bs p
  | PvLetM m p => cl_m B bs m ++ cl_pv B bs p
  | PvIf _ x y t f => cl_e B bs x ++ cl_e B bs y ++ cl_pv B bs t ++ cl_pv B bs f
  | PvIfB c t f => cl_b B bs c ++ cl_pv B bs t ++ cl_pv B bs f
  | PvMatch c p0 p1 => cl_pv B bs p0 ++ cl_pv B (cmt B bs c) p1
  | PvMatchP p q => cl_pv B bs p ++ cl_pv B bs q
  end.
Fixpoint cl_x (B : Z) (bs : list cbe) (x : sx) {struct x} : list site :=
  match x with
  | XRet e => cl_e B bs e
  | XRetB b => cl_b B bs b
  | XRetR _ r => cl_r B bs r
  | XBindRM _ f ccs args m x => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_m B bs m ++ cl_x B bs x
  | XLetM m x => cl_m B bs m ++ cl_x B bs x
  | XLet e x => cl_e B bs e ++ cl_x B bs x
  | XLetB b x => cl_b B bs b ++ cl_x B bs x
  | XIf _ a b x1 x2 => cl_e B bs a ++ cl_e B bs b ++ cl_x B bs x1 ++ cl_x B bs x2
  | XIfB b x1 x2 => cl_b B bs b ++ cl_x B bs x1 ++ cl_x B bs x2
  | XMatch c x0 x1 => cl_x B bs x0 ++ cl_x B (cmt B bs c) x1
  | XLetC c x => cl_c B bs c ++ cl_x B (clet B bs c) x
  | XRec ccs args m => (None, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_m B bs m
  | XCall f ccs args m => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_m B bs m
  | XCallP f ccs args p => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_pv B bs p
  | XBind _ f ccs args m x => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_m B bs m ++ cl_x B bs x
  | XBindR ccs args m x | XBindRB ccs args m x | XBindRR _ ccs args m x => (None, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_m B bs m ++ cl_x B bs x
  | XBindP _ f ccs args p x | XBindPR _ f ccs args p x => (Some f, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_pv B bs p ++ cl_x B bs x
  | XLetR r x | XMatchR r x | XSplitR _ r x => cl_r B bs r ++ cl_x B bs x
  | XMatchP p x | XLetP p x => cl_pv B bs p ++ cl_x B bs x
  end.
Fixpoint cl_br (B : Z) (bs : list cbe) (b : sbr) {struct b} : list site :=
  match b with
  | BRet x => cl_r B bs x
  | BRec ccs args => (None, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args
  | BMatchRec ccs args b | BLetRec ccs args b => (None, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_br B bs b
  | BLet e b => cl_e B bs e ++ cl_br B bs b
  | BLetB c b => cl_b B bs c ++ cl_br B bs b
  | BLetC c b => cl_c B bs c ++ cl_br B (clet B bs c) b
  | BLetR x b | BMatchR x b | BSplitR _ x b => cl_r B bs x ++ cl_br B bs b
  | BIf _ x y t f => cl_e B bs x ++ cl_e B bs y ++ cl_br B bs t ++ cl_br B bs f
  | BIfB c t f => cl_b B bs c ++ cl_br B bs t ++ cl_br B bs f
  | BMatch c b0 b1 => cl_br B bs b0 ++ cl_br B (cmt B bs c) b1
  end.
Fixpoint cl_bb (B : Z) (bs : list cbe) (b : sbb) {struct b} : list site :=
  match b with
  | BbRet x => cl_b B bs x
  | BbRec ccs args | BbNotRec ccs args => (None, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args
  | BbLetRec ccs args b => (None, (bs, ccs)) :: cl_cs B bs ccs ++ cl_es B bs args ++ cl_bb B bs b
  | BbLet e b => cl_e B bs e ++ cl_bb B bs b
  | BbLetB c b => cl_b B bs c ++ cl_bb B bs b
  | BbLetC c b => cl_c B bs c ++ cl_bb B (clet B bs c) b
  | BbLetR x b | BbMatchR x b | BbSplitR _ x b => cl_r B bs x ++ cl_bb B bs b
  | BbIf _ x y t f => cl_e B bs x ++ cl_e B bs y ++ cl_bb B bs t ++ cl_bb B bs f
  | BbIfB c t f => cl_b B bs c ++ cl_bb B bs t ++ cl_bb B bs f
  | BbMatch c b0 b1 => cl_bb B bs b0 ++ cl_bb B (cmt B bs c) b1
  end.
Definition cl_f (B : Z) (n : nat) (b : fbody) : list site :=
  let r := [(None, lshift (-1) (lunit (Nat.pred n)))] in
  match b with
  | FRec e0 e1 => cl_e B [] e0 ++ cl_e B r e1
  | FPlain e => cl_e B [] e
  | FRecM m0 m1 => cl_m B [] m0 ++ cl_m B r m1
  | FPlainM m => cl_m B [] m
  | FPlainX x => cl_x B [] x
  | FRecX x0 x1 => cl_x B [] x0 ++ cl_x B r x1
  | FRecR b0 b1 => cl_br B [] b0 ++ cl_br B r b1
  | FPlainR b => cl_br B [] b
  | FRecB b0 b1 => cl_bb B [] b0 ++ cl_bb B r b1
  | FPlainB b => cl_bb B [] b
  | FRecP p0 p1 => cl_pv B [] p0 ++ cl_pv B r p1
  | FPlainP p => cl_pv B [] p
  end.
(** each call's callee and the largest values of the counters it is given *)
Definition cl_calls (B : Z) (n : nat) (b : fbody) : list (nat * list Z) :=
  flat_map (fun q : site => match fst q with Some f => [(f, map (cmaxv B (fst (snd q))) (lc (snd (snd q))))] | None => [] end) (cl_f B n b).
(** the weights of a function whose recursion grows counters (steps 37, 38): none when each recursive call gives counters that
    are flat variables at the function's bound (step 35) or at most one of the function's counters (each below its bound);
    else one vector per counter, each the smallest satisfying [pot_ok] at every recursive call above that counter's unit
    vector, by rounds -- each weight raised to what the calls' linear bounds ask of it (a counter after the first: the
    coefficient of its variable; the first: the constant) -- or none when the rounds of one do not settle: a counter grown by
    itself or by the first has no weights.  Each vector is at most the one step 37 took from all ones.  [wf_f] checks what
    this gives *)
Definition w_ask (n : nat) (ws : list Z) (q : list cbe * scnts) : list Z :=
  let tot := fold_right ladd lzero (map (fun x => lscale (fst x) (snd x)) (combine (tl ws) (map (clinf (fst q)) (lc (snd q))))) in
  map (fun j => if Nat.eqb j 0 then Z.max (nth 0 ws 1%Z) (snd tot) else Z.max (nth j ws 1%Z) (nth (n - 1 - j) (fst tot) 0%Z)) (seq 0 n).
Fixpoint w_rounds (k n : nat) (rs : list (list cbe * scnts)) (ws : list Z) : option (list Z) :=
  let ws' := fold_left (w_ask n) rs ws in
  if forallb (fun z => z <=? 65536)%Z ws' then
    (if list_eq_dec Z.eq_dec ws' ws then Some ws else match k with O => None | S k' => w_rounds k' n rs ws' end)
  else None.
(** a counter grown by other counters (step 39): its polynomial [c + n·G], [n] the first counter and [G] its growth per round
    -- the recursive calls' linear bounds, the largest coefficient of each, with the first counter for the predecessor and
    each other counter given its own polynomial (a vector when step 38's rounds give one the check takes) -- in the order the
    counters depend on each other: none for a counter grown by itself by more than one per round, or a cycle *)
Definition fl (n : nat) (l : linf) : list Z * Z :=
  (map (fun i => if Nat.eqb i O then nth (Nat.pred n) (fst l) 0%Z else nth (Nat.sub (Nat.pred n) i) (fst l) 0%Z) (seq 0 n), snd l).
Definition flmax (a b : list Z * Z) : list Z * Z := (map (fun xy => Z.max (fst xy) (snd xy)) (combine (fst a) (fst b)), Z.max (snd a) (snd b)).
Definition lmax_j (n : nat) (rs : list (list cbe * scnts)) (j : nat) : list Z * Z :=
  match map (fun q => match nth_error (lc (snd q)) (Nat.pred j) with Some c => fl n (clinf (fst q) c) | None => (repeat 0%Z n, 0%Z) end) rs with
  | [] => (repeat 0%Z n, 0%Z)
  | l0 :: ls => fold_left flmax ls l0
  end.
Fixpoint ppoly (fuel n : nat) (rs : list (list cbe * scnts)) (lin : nat -> option poly) (j : nat) : option poly :=
  match lin j with
  | Some P => Some P
  | None =>
      match fuel with
      | O => None
      | S f =>
          let L := lmax_j n rs j in
          if (2 <=? nth j (fst L) 0)%Z then None else
          let deps := filter (fun i => negb (Nat.eqb i j) && (0 <? nth i (fst L) 0)%Z) (seq 1 (Nat.pred n)) in
          match opt_all (map (fun i => option_map (fun P => (i, P)) (ppoly f n rs lin i)) deps) with
          | None => None
          | Some ps =>
              let G := (Z.to_nat (nth 0 (fst L) 0%Z), [O]) :: (Z.to_nat (Z.max 0 (snd L)), []) ::
                       flat_map (fun iP => map (fun m => (Nat.mul (Z.to_nat (nth (fst iP) (fst L) 0%Z)) (fst m), snd m)) (snd iP)) ps in
              Some ((1, [j]) :: map (fun m => (fst m, O :: snd m)) G)
          end
      end
  end.
Definition mono_eq_dec : forall x y : nat * list nat, {x = y} + {x <> y}.
Proof. decide equality; [apply (list_eq_dec Nat.eq_dec) | apply Nat.eq_dec]. Defined.
Definition wts_of (n : nat) (b : fbody) : list poly :=
  let rs := flat_map (fun q : site => match fst q with None => [snd q] | Some _ => [] end) (cl_f own_bound n b) in
  if forallb (fun q => all_c (fun c => flat c && pvars (fst q) c || lin1 (clinf (fst q) c)) (snd q)) rs then [] else
  let unit c := map (fun j => if Nat.eqb j c then 1%Z else 0%Z) (seq 0 n) in
  let lin c := match w_rounds (4 * n + 4) n rs (unit c) with
               | Some ws => let P := lpoly (map Z.to_nat ws) in if forallb (fun q => ppot_ok P (fst q) (snd q)) rs then Some P else None
               | None => None
               end in
  match opt_all (map (ppoly n n rs lin) (seq 0 n)) with
  | Some vs => nodup (list_eq_dec mono_eq_dec) vs
  | None => []
  end.
(** a function with weights is given its counters by its callers (each weighted sum below its bound, worked out from the
    call graph) or, the entry, by [kq_nat] (each at most 2^60): the entry's own bound covers each counter at the smallest
    bound's value *)
Definition wmax (vs : list poly) (l : list Z) : Z := fold_right Z.max 0%Z (map (fun P => pevalz P l) vs).
Definition own_w (n : nat) (vs : list poly) : Z := (wmax vs (repeat (own_bound - 1)%Z n) + 1)%Z.
(** a function's signature as [wf_f] takes it: as read; with the bound the call graph worked out for it (step 34); with the
    smallest bound of its own (step 33); with weights when its recursion grows a counter, at the call graph's bound or their
    own (steps 37 to 39).  Every way a function is read -- a function, a template's copy, a local fixpoint's copy, a mutual block and
    its members -- takes its signature from here *)
Definition wf_sig (wfok : sig -> bool) (gs : sig) (b : fbody) (bd : option Z) : option sig :=
  let gb bd := mksig7 (sn gs) (sk gs) (sm gs) (sr gs) (sw gs) (sq gs) (Some bd) in
  (* the weights worked out only when the signature without them is refused *)
  let wtry (obd : option Z) :=
    match wts_of (sn gs) b with
    | [] => None
    | ws => let g := mksig8 (sn gs) (sk gs) (sm gs) (sr gs) (sw gs) (sq gs) (Some (match obd with Some x => x | None => own_w (sn gs) ws end)) ws in
            if wfok g then Some g else None
    end in
  match bd with
  | Some bd => if wfok (gb bd) then Some (gb bd) else wtry (Some bd)
  | None => if wfok gs then Some gs else if wfok (gb own_bound) then Some (gb own_bound) else wtry None
  end.


(** ... kept when it is well formed, the condition of [compile_f_ok]: a program read is a program compiled *)
Definition reify_fun_d (dm : bool) (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (kn : kername) (bt : kername -> option Z) (chk : bool) : option (sig * fbody) :=
  match (if dm then read_fun_p true Σ hb tc rt callees kn else read_fun Σ hb tc rt callees kn) with
  | Some (gs, b) =>
      let wfok := fun gs => @wf_f (arity_recs (map (fun e => (snd (fst (fst (fst e))), snd (fst e))) rt) rt) (map snd callees) (with_sp false gs) b in
      if negb chk then Some (gs, b) else
      (* the signature [wf_f] takes (steps 33, 34, 37); a function with the pair checked on the components (step 44) *)
      option_map (fun g => (with_sp (sp gs) g, b)) (wf_sig wfok gs b (bt kn))
  | None => None
  end.
Definition reify_fun := reify_fun_d false.
(** whether a function has two memory parameters *)
Definition two_mems (tys : list term) : bool :=
  match filter (is_ty kn_mem) tys with _ :: _ :: _ => true | _ => false end.

Definition ind_kind := ind_of <% KQR.kind %>.
Definition ind_list := ind_of <% list %>.
Definition kn_no_recs := kn_of <% @KQR.no_recs %>.
Fixpoint qnat (n : nat) : term := match n with O => tConstruct ind_nat 0 [] | S n => tApp (tConstruct ind_nat 1 []) [qnat n] end.
Definition qkind (k : kind) : term :=
  match k with KNum => tConstruct ind_kind 0 [] | KBool => tConstruct ind_kind 1 [] | KRec ri => tApp (tConstruct ind_kind 2 []) [qnat ri] end.
Definition qlist (A : term) (l : list term) : term :=
  fold_right (fun x acc => tApp (tConstruct ind_list 1 []) [A; x; acc]) (tApp (tConstruct ind_list 0 []) [A]) l.
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
      | tProj _ c => consts fuel c acc
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
Definition kn_fst := kn_of <% @fst %>.
Definition kn_snd := kn_of <% @snd %>.
(** (step 48 continued) whether a term uses the variable [d], a number and a memory, bare: other than through [fst], [snd] or taken
    apart by a match.  [k n p] is not convertible with [k n (fst p, snd p)], so such a let is lifted to a function of the pair *)
Fixpoint pm_bare (fuel d : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tRel i => Nat.eqb i d
      | tApp (tConst kn _) [a; b; tRel i] =>
          if Kername.eqb kn kn_fst || Kername.eqb kn kn_snd then false else pm_bare fuel d a || pm_bare fuel d b || Nat.eqb i d
      | tApp f args => pm_bare fuel d f || existsb (pm_bare fuel d) args
      | tLambda _ _ b => pm_bare fuel (S d) b
      | tLetIn _ b _ body => pm_bare fuel d b || pm_bare fuel (S d) body
      | tCase _ _ c brs =>
          match c with tRel _ => false | _ => pm_bare fuel d c end
          || existsb (fun br => pm_bare fuel (d + length (bcontext br)) (bbody br)) brs
      | tFix mfix _ => existsb (fun df => pm_bare fuel (d + length mfix) (dbody df)) mfix
      | _ => false
      end
  end.
Fixpoint has_pm_let (fuel : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tApp f args => if has_pm_let fuel f then true else existsb (has_pm_let fuel) args
      | tLambda _ _ b => has_pm_let fuel b
      | tLetIn _ b ty body =>
          (* tests in this order, with [if]: [&&] and [||] evaluate both sides under the machine, and a body is long *)
          if is_pm ty then
            if pm_bare 100000 0 body then true else if has_pm_let fuel b then true else has_pm_let fuel body
          else if has_pm_let fuel b then true else has_pm_let fuel body
      | tCase _ _ c brs => if has_pm_let fuel c then true else existsb (fun br => has_pm_let fuel (bbody br)) brs
      | tFix mfix _ => existsb (fun df => has_pm_let fuel (dbody df)) mfix
      | _ => false
      end
  end.
(** whether a text is one call of a budget function ([G], step 56) *)
Fixpoint ends_wg (s : string) : bool :=
  match s with
  | String.String a (String.String b (String.String c (String.String d String.EmptyString))) =>
      if Byte.eqb a "_"%byte then if Byte.eqb b "_"%byte then if Byte.eqb c "w"%byte then Byte.eqb d "g"%byte else false else false else false
  | String.String _ r => ends_wg r
  | String.EmptyString => false
  end.
Fixpoint is_w (t : term) : bool :=
  match t with
  | tLambda _ _ b => is_w b
  | tApp (tConst k _) _ => if eq_mp (fst k) copy_mp then ends_wg (snd k) else false
  | _ => false
  end.
(** (step 73) the kit's division of two digits by one: a recursive function like the program's *)
Definition kn_kq_d21g : kername := kn_of <% KQ.KQRun.kq_d21g %>.
Definition is_fn (Σ : global_env) (mp : modpath) (root kn : kername) : bool :=
  Kername.eqb kn root || eq_mp (fst kn) copy_mp || Kername.eqb kn kn_kq_d21g
  || (match body_of Σ kn with Some b => is_w b | None => false end)
  || (in_prog mp (fst kn) && (match lookup_env Σ (copy_mp, snd kn ^ "__wy"%bs) with Some _ => true | None => false end
                            || match body_of Σ kn with Some (tFix _ _) => true | _ => false end || big_def Σ kn
                            || (if in_prog mp (fst kn) then match body_of Σ kn with Some b => has_pm_let 1000 b | None => false end else false))).

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
               let cs := filter (fun k => (in_prog mp (fst k) || eq_mp (fst k) kit_mp) && negb (Kername.eqb k kn)) (consts 10000 b []) in
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
  if Kername.eqb kn kn_fst || Kername.eqb kn kn_snd then body_of Σ kn else
  if Kername.eqb kn kn_rd8 || Kername.eqb kn kn_upd8 || Kername.eqb kn kn_w64_op || Kername.eqb kn kn_kq_nat
     || existsb (Kername.eqb kn) fns then None
  else if in_prog mp (fst kn) then
    (* its fixpoints local ones (step 31): each read as a copy where it is applied *)
    match body_of Σ kn with
    | Some (tFix _ _) => None
    (* the full scan for a local fixpoint only where the bounded one finds a fixpoint: a helper is looked up at every call *)
    | Some b => if negb (has_fix 1000 b) then Some b else if lfix_body b then Some b else None
    | None => None
    end
  else if eq_mp (fst kn) kit_mp || eq_mp (fst kn) uint63_mp then
    match body_of Σ kn with Some b => if has_fix 1000 b then None else Some b | None => None end
  (* (step 63) what Rocq's libraries define over machine numbers, booleans and counters: a definition, written out as the program's are; a fixpoint inside it, a local one *)
  else if lib_open kn then
    match body_of Σ kn with
    | Some (tFix _ _) => None
    | Some b => if negb (has_fix 1000 b) then Some b else if lfix_body b then Some b else None
    | None => None
    end
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
      (* (step 59) the function one call of a budget function, a function among its parameters *)
      | Some b => if is_w b then (let tys := fst (lams b) in if existsb is_prod tys then Some tys else None) else None
      | None => None
      end
  | _ => None
  end.
Definition is_tmpl (Σ : global_env) (mp : modpath) (kn : kername) : bool :=
  in_prog mp (fst kn) && match tmpl_tys Σ kn with Some _ => true | None => false end.
Definition fn_args (tys args : list term) : list term := map snd (filter (fun p => is_prod (fst p)) (combine tys args)).
Definition nonfn_args (tys args : list term) : list term := map snd (filter (fun p => negb (is_prod (fst p))) (combine tys args)).

(** two functions given are the same copy when they are the same term (a structural comparison: MetaRocq's generic one is
    slow under [vm_compute], F2) *)
(** the copies made: the template, the functions given, the copy's name, its meaning (the template applied to them) *)
Definition copytab := list (kername * (list term * list cent) * kername * term).
(** the wrapper of a function whose parameters stand in another order (step 41): its parameters in the syntax's order, the
    function given them in its own -- a caller's text converts with it by one beta step *)
Definition perm_meaning (kn : kername) (tys : list term) (perm : list nat) : term :=
  let N := length perm in
  fold_right (fun ty b => tLambda {| binder_name := nAnon; binder_relevance := Relevant |} ty b)
             (tApp (tConst kn []) (map (fun u => if existsb (Nat.eqb u) perm then tRel (Nat.sub (Nat.sub N 1) (pos_in u perm)) else tRel 0) (seq 0 (length tys))))
             (map (fun i => nth i tys (tRel 0)) perm).
(** a memory parameter never read, for the theorem of each of its values (step 53): those parameters [u], the others as above *)
Definition dead_meaning (kn : kername) (tys : list term) (perm : list nat) : term :=
  let N := length perm in
  tLambda {| binder_name := nAnon; binder_relevance := Relevant |} (tConst kn_mem [])
    (fold_right (fun ty b => tLambda {| binder_name := nAnon; binder_relevance := Relevant |} (lift0 1 ty) b)
                (tApp (tConst kn []) (map (fun u => if existsb (Nat.eqb u) perm then tRel (Nat.sub (Nat.sub N 1) (pos_in u perm)) else tRel N) (seq 0 (length tys))))
                (map (fun i => nth i tys (tRel 0)) perm)).
Definition fun_tys (Σ : global_env) (kn : kername) : list term * bool :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) => match cst_body cb with Some (tFix [d] 0) => (fst (lams (dbody d)), true) | Some b => (fst (lams b), false) | None => ([], false) end
  | _ => ([], false)
  end.
(** a function read: under its own name, or (step 41) as its wrapper -- [kn__o] when it recurses, [kn__on] when not *)
(** the entry's parameter order when it is not the syntax's: [main]'s arguments put in that order *)
Definition entry_perm (p : program) : option (list nat) := match p with (Σ, tConst root _) => fun_perm Σ root | _ => None end.
Definition add_fun_d (dm : bool) (Σ : global_env) (kn : kername) (gs : sig) (b : fbody) (es : list (kername * sig * fbody)) (tbl : copytab) :
  list (kername * sig * fbody) * copytab :=
  match fun_perm Σ kn with
  | None => (es ++ [(kn, gs, b)], tbl)
  | Some pm => let '(tys, isfix) := fun_tys Σ kn in
               let ckn := (copy_mp, mangle kn ^ (if isfix then "__o" else "__on")) in
               let gkn := (copy_mp, snd ckn ^ "__g") in
               (es ++ [(ckn, gs, b)], tbl ++ [(kn, ([], [CSelfP pm]), ckn, perm_meaning kn tys pm)]
                                          ++ (if dm then [(gkn, ([], []), gkn, dead_meaning kn tys pm)] else []))
  end.
Definition add_fun := add_fun_d false.
Definition find_copy (T : kername) (fargs : list term) (capk : list cent) (tbl : copytab) : option kername :=
  option_map (fun e => snd (fst e)) (List.find (fun e => Kername.eqb T (fst (fst (fst e))) && teqs fargs (fst (snd (fst (fst e))))
                                                         && capk_eqb capk (snd (snd (fst (fst e))))) tbl).
(** a call of a template: the copy for its functions given, and its arguments -- the template's counters, the captured
    numbers and booleans, its other arguments, the captured memory (step 13) *)
(** a local fixpoint's key: the fixpoint with its captured variables numbered the last first, so that read with them after
    the copy's own parameters ([rev capk], as a template's copy is read) each is the parameter of its kind (step 31) *)
Definition lfix_key (fx : term) : list nat * term := let fv := fvs 1000 0 fx [] in (fv, abs_caps (rev fv) fx).
(** the template's parameters that are not functions, in the order the syntax takes (step 41): each its place among them *)
Fixpoint cnt_before (tys : list term) (u : nat) : nat :=
  match tys, u with _, O => O | t :: r, S u' => Nat.add (if is_prod t then O else 1) (cnt_before r u') | [], _ => O end.
Definition nonfn_perm (tys : list term) (r : nat) : list nat :=
  map (cnt_before tys) (filter (fun u => negb (is_prod (nth u tys (tRel 0)))) (canon_perm tys (Some r))).
Definition tmpl_rarg (Σ : global_env) (kn : kername) : nat :=
  match lookup_env Σ kn with Some (ConstantDecl cb) => match cst_body cb with Some (tFix [d] 0) => rarg d | _ => O end | _ => O end.
Definition tc_of_t (Σ : global_env) (mp : modpath) (tbl : copytab) (kn : kername) (args : list term) : option (kername * list term) :=
  if existsb (fun e => Kername.eqb kn (fst (fst (fst e)))) tbl then   (* a template with a copy: no look-up otherwise *)
    if Kername.eqb kn kn_lfix then
      match args with
      | (tFix [d] 0 as fx) :: rest =>
          let '(fv, key) := lfix_key fx in
          match List.find (fun e => Kername.eqb kn_lfix (fst (fst (fst e))) && teqs [key] (fst (snd (fst (fst e))))) tbl with
          | Some (_, (_, capk), ckn, _) =>
              let ltys := fst (lams (dbody d)) in
              let nc := fst (lead_nats ltys) in
              let rest := map (fun i => nth i rest (tRel 0)) (nonfn_perm ltys (rarg d)) in
              let cs := combine capk (map tRel fv) in
              Some (ckn, firstn nc rest ++ map snd (filter (fun p => is_capc (fst p)) cs) ++ map snd (filter (fun p => negb (is_memc (fst p)) && negb (is_capc (fst p))) cs) ++ skipn nc rest
                         ++ map snd (filter (fun p => is_memc (fst p)) cs))
          | None => None
          end
      | _ => None
      end
    else
    match tmpl_tys Σ kn with
    | Some tys => if Nat.eqb (length args) (length tys) then
                    let fa := fn_args tys args in
                    let fv := fold_left (fun a f => fvs 1000 0 f a) fa [] in
                    let fa' := map (abs_caps fv) fa in
                    match List.find (fun e => Kername.eqb kn (fst (fst (fst e))) && teqs fa' (fst (snd (fst (fst e))))) tbl with
                    | Some (_, (_, capk), ckn, _) =>
                        let nonfn := map (fun i => nth i (nonfn_args tys args) (tRel 0)) (nonfn_perm tys (tmpl_rarg Σ kn)) in
                        let nc := fst (lead_nats (filter (fun t => negb (is_prod t)) tys)) in
                        let cs := combine capk (map tRel fv) in
                        Some (ckn, firstn nc nonfn ++ map snd (filter (fun p => is_capc (fst p)) cs) ++ map snd (filter (fun p => negb (is_memc (fst p)) && negb (is_capc (fst p))) cs) ++ skipn nc nonfn
                                   ++ map snd (filter (fun p => is_memc (fst p)) cs))
                    | None => None
                    end
                  else None
    | None => None
    end
  else None.

(** a call of a function whose parameters stand in another order (step 41): a call of its wrapper, the arguments in the
    syntax's order *)
(** how many arguments the function has that a wrapper stands for *)
Fixpoint wrap_arity (t : term) : nat :=
  match t with tLambda _ _ b => wrap_arity b | tApp _ l => length l | _ => O end.
Definition tc_of (Σ : global_env) (mp : modpath) (tbl : copytab) (kn : kername) (args : list term) : option (kername * list term) :=
  match List.find (fun e => Kername.eqb kn (fst (fst (fst e))) && match snd (snd (fst (fst e))) with [CSelfP _] => true | _ => false end) tbl with
  | Some (_, (_, [CSelfP pm]), ckn, mn) =>
      if Nat.eqb (length args) (length pm) then Some (ckn, map (fun i => nth i args (tRel 0)) pm)
      else if Nat.eqb (length args) (wrap_arity mn) then
        let l := map (fun i => nth i args (tRel 0)) pm in
        let m := last l (tRel 0) in
        if forallb (fun p => if existsb (Nat.eqb p) pm then true else teq 1000 (nth p args (tRel 0)) m) (seq 0 (length args))
        then Some (ckn, l) else None
      else None
  | _ => tc_of_t Σ mp tbl kn args
  end.

(** the meaning of a copy: [fun x1 .. xn => T .. f .. xi ..], the functions given in their places; with captured variables
    (step 13) [fun c1 .. b1 .. x1 .. s => T .. f ..]: the template's counters, the captured numbers and booleans, the
    template's other parameters, the captured memory *)
Definition cap_ty (c : cent) : term :=
  match c with CBool => tInd ind_bool [] | CMem | CDead => tConst kn_mem [] | CCnt => tInd ind_nat [] | CRecT t => t | _ => tConst kn_int [] end.
Definition copy_meaning_h (hd : list term -> term) (tys fargs : list term) (capk : list cent) (pn : list nat) : term :=
  let nonfn0 := filter (fun t => negb (is_prod t)) tys in
  let nonfn := map (fun i => nth i nonfn0 (tRel 0)) pn in
  let nc := fst (lead_nats nonfn) in
  let cn := filter is_capc capk ++ filter (fun c => negb (is_memc c) && negb (is_capc c)) capk in
  let ncc := length (filter is_capc capk) in
  let mc := length cn in
  let cm := if existsb is_memc capk then 1 else 0 in
  let n := length nonfn + mc + cm in
  let pos i := if Nat.ltb i nc then i else i + mc in
  let capidx k := if is_memc (nth k capk CNum) then 0
                   else if is_capc (nth k capk CNum) then n - 1 - (nc + length (filter is_capc (firstn k capk)))
                   else n - 1 - (nc + ncc + length (filter (fun c => negb (is_memc c) && negb (is_capc c)) (firstn k capk))) in
  let sb := map (fun k => tRel (capidx k)) (seq 0 (length capk)) in
  let fix args (l fa : list term) (i : nat) : list term :=
    match l with
    | [] => []
    | t :: r => if is_prod t then match fa with f :: fa' => subst sb 0 f :: args r fa' i | [] => [] end
                else tRel (n - 1 - pos (pos_in i pn)) :: args r fa (S i)
    end in
  fold_right (fun ty b => tLambda {| binder_name := nAnon; binder_relevance := Relevant |} ty b)
             (tApp (hd sb) (args tys fargs 0))
             (firstn nc nonfn ++ map cap_ty cn ++ skipn nc nonfn ++ (if Nat.eqb cm 1 then [tConst kn_mem []] else [])).
Definition copy_meaning (T : kername) (tys fargs : list term) (capk : list cent) (pn : list nat) : term :=
  copy_meaning_h (fun _ => tConst T []) tys fargs capk pn.
(** a local fixpoint's copy (step 31): [fun c1 .. b1 .. x1 .. s => (fix g .. := ..) c1 .. x1 .. s], the fixpoint's captured
    variables (numbered the last first, [lfix_key]) the copy's parameters *)
Definition lfix_meaning (fx : term) (tys : list term) (capk : list cent) (pn : list nat) : term :=
  copy_meaning_h (fun sb => subst (rev sb) 0 fx) tys [] capk pn.

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
                         | Some b => has_lfix 100000 b || existsb (fun k => existsb (Kername.eqb k) tms || existsb (Kername.eqb k) th) (consts 10000 b [])
                         | None => false
                         end) hs in
      Nat.iter (length hs) step []
  end.

(** the calls of templates in a text, the helpers that reach a template written out: each the template, its functions
    given with their captured variables numbered in the order they first appear, and those variables' kinds (step 13: a
    number, a boolean, the memory -- read off the binders' types, [kctx], the nearest first) *)
Definition ty_cent (ty : term) : option cent :=
  if is_ty kn_int ty then Some CNum else if is_bool ty then Some CBool else if is_ty kn_mem ty then Some CMem
  else if is_nat ty then Some CCnt
  else if is_pm ty then None
  else match ty with tInd _ _ | tApp (tInd _ _) _ => Some (CRecT ty) | _ => None end.   (* step 42: a counter, a record of the program; step 67: one with parameters *)
(** the kinds of the variables a branch of a [match] binds, nearest first (step 42): a counter's predecessor a counter, a
    constructor's fields their types' *)
Definition br_kinds (Σ : global_env) (ind : inductive) (j n : nat) : list (option cent) :=
  if Kername.eqb (inductive_mind ind) (inductive_mind ind_nat) then repeat (Some CCnt) n
  else match lookup_env Σ (inductive_mind ind) with
       | Some (InductiveDecl mib) =>
           match nth_error (ind_bodies mib) (inductive_ind ind) with
           | Some oib => match nth_error (ind_ctors oib) j with
                         | Some c => if Nat.eqb (length (cstr_args c)) n then map (fun d => ty_cent (decl_type d)) (cstr_args c) else repeat None n
                         | None => repeat None n
                         end
           | None => repeat None n
           end
       | _ => repeat None n
       end.
Fixpoint sites (fuel : nat) (Σ : global_env) (tms : list kername) (hb : kername -> option term) (th : list kername)
  (kctx : list (option cent)) (t : term) (acc : list (kername * list term * list cent)) : list (kername * list term * list cent) :=
  match fuel with
  | O => acc
  | S fuel =>
      let wr (kn : kername) (args : list term) (acc : list (kername * list term * list cent)) :=
        if existsb (Kername.eqb kn) th then match hb kn with Some b => sites fuel Σ tms hb th kctx (wout b args) acc | None => acc end
        else acc in
      match t with
      | tApp (tConst kn _) args0 =>
          let acc := fold_left (fun a x => sites fuel Σ tms hb th kctx x a) args0 acc in
          let args := map (fsub (map (fun o => match o with Some c => c | None => CNum end) kctx)) args0 in
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
      | tApp (tFix [d] 0 as fx) args =>
          (* a local fixpoint applied (step 31): a copy whose parameters are its captured variables, if it takes no function *)
          let acc := fold_left (fun a x => sites fuel Σ tms hb th kctx x a) args acc in
          let '(fv, key) := lfix_key fx in
          let tys := fst (lams (dbody d)) in
          match opt_all (map (fun r => nth r kctx None) fv) with
          | Some capk =>
              if Nat.eqb (length args) (length tys) && negb (existsb is_prod tys)
                 && forallb cap_ok capk && Nat.leb (length (filter is_memc capk)) 1
                 && negb (existsb (is_ty kn_mem) tys && existsb is_memc capk)
              then (kn_lfix, [key], capk) :: acc else acc
          | None => acc
          end
      | tApp f args => fold_left (fun a x => sites fuel Σ tms hb th kctx x a) args (sites fuel Σ tms hb th kctx f acc)
      | tConst kn _ => wr kn [] acc
      | tLambda _ ty b => sites fuel Σ tms hb th (ty_cent ty :: kctx) b acc
      | tProd _ _ b => sites fuel Σ tms hb th (None :: kctx) b acc
      | tLetIn _ b ty body =>
          if fun_or_type ty then sites fuel Σ tms hb th kctx (subst [b] 0 body) acc
          else sites fuel Σ tms hb th (ty_cent ty :: kctx) body (sites fuel Σ tms hb th kctx b acc)
      | tCase ci _ c brs => snd (fold_left (fun ja br => (S (fst ja), sites fuel Σ tms hb th (br_kinds Σ (ci_ind ci) (fst ja) (length (bcontext br)) ++ kctx)
                                                                     (bbody br) (snd ja))) brs (O, sites fuel Σ tms hb th kctx c acc))
      | tFix mfix _ => fold_left (fun a d => sites fuel Σ tms hb th (repeat None (length mfix) ++ kctx) (dbody d) a) mfix acc
      | _ => acc
      end
  end.

(** a copy's parameters, nearest first: a function parameter bound to the function given *)
Fixpoint tkinds (rt : list rentry) (tys fargs : list term) (p : nat) : list cent :=
  match tys with
  | [] => []
  | t :: r => if is_prod t then match fargs with f :: fa => CFn p f :: tkinds rt r fa (S p) | [] => [] end
              else (if is_nat t then CCnt else if is_ty kn_mem t then CMem else if is_bool t then CBool
                    else match kind_ty rt t with Some (KRec _) => CRec | _ => CNum end) :: tkinds rt r fargs p
  end.
Fixpoint tdrop (tys : list term) (p : nat) : list (option nat) :=
  match tys with [] => [] | t :: r => if is_prod t then Some p :: tdrop r (S p) else None :: tdrop r p end.

(** a template's copy, read as a recursive function: its signature without the function parameters; the recursive call
    passes them on, and they are dropped *)
Definition read_def (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (d : def term) (fargs : list term) (capk : list cent) : option (sig * fbody) :=
          let '(tys0, body0) := lams (dbody d) in
          (* (step 46) the last parameter a number-and-memory pair: read on its components, the signature flagged *)
          let pmx := last_pm tys0 in
          let body := pm_body callees tys0 true body0 in
          let tys := if pmx then removelast tys0 ++ [tConst kn_int []; tConst kn_mem []] else tys0 in
          let pa := canon_perm tys (Some (rarg d)) in
          let tysc := map (fun i => nth i tys (tRel 0)) pa in
          option_map (fun gb => (with_sp pmx (fst gb), snd gb))
          match read_sig rt (filter (fun t => negb (is_prod t)) tysc) (ret_ty (dtype d)), body with
          | Some gs0, tCase ci _ (tRel cnt) [b0; b1] =>
              (* the captured numbers and booleans before the template's other parameters, the captured memory last *)
              let ncc := length (filter is_capc capk) in
              let gs := mksig (sn gs0 + ncc)
                              (map (fun c => match c with CBool => KBool | CRecT t => match rindex t rt 0 with Some ri => KRec ri | None => KNum end | _ => KNum end)
                                   (filter (fun c => negb (is_memc c) && negb (is_capc c)) capk) ++ sk gs0)
                              (sm gs0 || existsb is_memc capk) (sr gs0) (sw gs0) (sq gs0) in
              let nx := Nat.pred (sn gs) in
              let fd := tdrop (tl tysc) 0 in
              if negb (Nat.eqb (sn gs) 0) && negb (sm gs0 && existsb is_memc capk)
                 && Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat)
                 && Nat.eqb cnt (Nat.sub (Nat.pred (length tys)) (rarg d)) && is_nat (nth (rarg d) tys (tRel 0)) then
                let k := length (filter is_nat tys) in
                let tk := tkinds rt tys fargs 0 in
                let kt := k in
                let k := Nat.add kt ncc in
                (* the captured variables (step 42): a counter at its place after the template's, a record as a record *)
                let capc := map (fun i => match nth i capk CNum with
                                          | CCnt => CCntP (Nat.sub (Nat.sub k 1) (Nat.add kt (length (filter is_capc (firstn i capk)))))
                                          | CRecT _ => CRec | c => c end) (seq 0 (length capk)) in
                let ctx := if (if list_eq_dec Nat.eq_dec pa (seq 0 (length pa)) then Nat.eqb ncc 0 else false) then rev tk ++ [CSelf] ++ rev capc
                           else rev (map (fun u => if is_nat (nth u tys (tRel 0)) then CCntP (Nat.sub (Nat.sub k 1) (pos_in u pa)) else nth u tk CNum)
                                         (seq 0 (length tys))) ++ [if list_eq_dec Nat.eq_dec pa (seq 0 (length pa)) then CSelf else CSelfP pa] ++ rev capc in
                if sr gs then
                  match reify_m callees (sm gs) nx hb tc fd rt 100000 ctx (bbody b0),
                        reify_m callees (sm gs) nx hb tc fd rt 100000 (CPred :: ctx) (bbody b1) with
                  | Some m0, Some m1 => Some (gs, FRecM m0 m1)
                  | _, _ => None
                  end
                (* (step 46) a copy giving back a number and a memory, a boolean, a record *)
                else if ispq gs then
                  match reify_pv callees (sm gs) nx hb tc fd rt 100000 ctx (bbody b0),
                        reify_pv callees (sm gs) nx hb tc fd rt 100000 (CPred :: ctx) (bbody b1) with
                  | Some p0, Some p1 => Some (gs, FRecP p0 p1)
                  | _, _ => None
                  end
                else if isbq gs then
                  match reify_bb callees (sm gs) nx hb tc fd rt 100000 ctx (bbody b0),
                        reify_bb callees (sm gs) nx hb tc fd rt 100000 (CPred :: ctx) (bbody b1) with
                  | Some r0, Some r1 => Some (gs, FRecB r0 r1)
                  | _, _ =>
                      (* (step 48 continued) a copy giving back a boolean whose body writes: an X body of booleans *)
                      if sm gs then
                        match reify_x callees (sm gs) nx hb tc fd rt 100000 ctx (bbody b0),
                              reify_x callees (sm gs) nx hb tc fd rt 100000 (CPred :: ctx) (bbody b1) with
                        | Some x0, Some x1 => Some (wsig gs, FRecX x0 x1)
                        | _, _ => None
                        end
                      else None
                  end
                else if isq gs then
                  match reify_br callees (sm gs) nx hb tc fd rt 100000 ctx (bbody b0),
                        reify_br callees (sm gs) nx hb tc fd rt 100000 (CPred :: ctx) (bbody b1) with
                  | Some r0, Some r1 => Some (gs, FRecR r0 r1)
                  | _, _ =>
                      (* (step 48 continued) a copy giving back a record whose body writes: an X body of records *)
                      if sm gs then
                        match reify_x callees (sm gs) nx hb tc fd rt 100000 ctx (bbody b0),
                              reify_x callees (sm gs) nx hb tc fd rt 100000 (CPred :: ctx) (bbody b1) with
                        | Some x0, Some x1 => Some (wsig gs, FRecX (xset_ri (sqi gs) x0) (xset_ri (sqi gs) x1))
                        | _, _ => None
                        end
                      else None
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
          end.
Definition read_tmpl (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (callees : list (kername * sig)) (kn : kername) (fargs : list term) (capk : list cent) : option (sig * fbody) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) => match cst_body cb with Some (tFix [d] 0) => read_def hb tc rt callees d fargs capk | _ => None end
  | _ => None
  end.

Definition callees_of (es : list (kername * sig * fbody)) : list (kername * sig) := map (fun x => (fst (fst x), snd (fst x))) es.
(** a function read and added: with every other memory parameter the same memory; failing that, with those it never reads as such (step 53) *)
Definition read_add (Σ : global_env) (hb : kername -> option term) (tc : kername -> list term -> option (kername * list term)) (rt : list rentry)
  (kn : kername) (bt : kername -> option Z) (chk : bool) (es : list (kername * sig * fbody)) (tbl : copytab) : option (list (kername * sig * fbody) * copytab) :=
  match reify_fun Σ hb tc rt (callees_of es) kn bt chk with
  | Some (gs, b) => Some (add_fun Σ kn gs b es tbl)
  | None =>
      if two_mems (fst (fun_tys Σ kn)) then
        match reify_fun_d true Σ hb tc rt (callees_of es) kn bt chk with
        | Some (gs, b) => Some (add_fun_d true Σ kn gs b es tbl)
        | None => None
        end
      else None
  end.

(** (step 59) a copy of the function one call of a budget function: its text there, the leaf of [copy_meaning_h] the wrapper applied, written out *)
Fixpoint wrap_beta (b : term) (args : list term) : term :=
  match b, args with
  | tLambda _ _ c, a :: r => wrap_beta (subst10 a c) r
  | _, [] => b
  | _, _ => tApp b args
  end.
Fixpoint wrap_read (t : term) : term :=
  match t with
  | tLambda na ty c => tLambda na ty (wrap_read c)
  | tApp (tLambda _ _ _ as f) args => wrap_beta f args
  | _ => t
  end.
Fixpoint wrap_head (t : term) : option kername :=
  match t with
  | tLambda _ _ c => wrap_head c
  | tApp (tConst k _) _ => Some k
  | _ => None
  end.
Definition add_decl0 (Σ : global_env) (kn : kername) (ty b : term) : global_env :=
  {| universes := universes Σ;
     declarations := (kn, ConstantDecl {| cst_type := ty; cst_body := Some b; cst_universes := Monomorphic_ctx; cst_relevance := Relevant |})
                     :: declarations Σ;
     retroknowledge := retroknowledge Σ |}.
Definition anon_b0 := {| binder_name := nAnon; binder_relevance := Relevant |}.
(** the copy for a call site, made (with the copies its functions need) if it is not yet, before the functions that call it *)
Fixpoint ensure (fuel : nat) (Σ : global_env) (mp : modpath) (hb : kername -> option term) (rt : list rentry) (th tms : list kername)
  (bt : kername -> option Z) (chk : bool) (site : kername * list term * list cent)
  (st : option (list (kername * sig * fbody) * copytab)) {struct fuel} : option (list (kername * sig * fbody) * copytab) :=
  match fuel, st with
  | O, _ => None
  | _, None => None
  | S fuel, Some (es, tbl) =>
      let '(T, fargs, capk) := site in
      match find_copy T fargs capk tbl with
      | Some _ => st
      | None =>
          if Kername.eqb T kn_lfix then
            match fargs with
            | [tFix [d] 0 as fx] =>
                let '(tys, body) := lams (dbody d) in
                let nested := sites 1000 Σ tms hb th (map Some (rev (tkinds rt tys [] 0) ++ [CSelf] ++ rev capk)) body [] in
                match fold_left (fun st s => ensure fuel Σ mp hb rt th tms bt chk s st) (rev nested) st with
                | Some (es, tbl) =>
                    let ckn := (MPfile ["kqcopy"%bs], snd T ^ "__c" ^ string_of_nat (length tbl)) in
                    match read_def hb (tc_of Σ mp tbl) rt (callees_of es) d [] capk with
                    | Some (gs, b) => match option_map (with_sp (sp gs)) (if chk then wf_sig (fun g => @wf_f (arity_recs (map (fun e => (snd (fst (fst (fst e))), snd (fst e))) rt) rt) (map snd (callees_of es)) (with_sp false g) b) gs b (bt ckn) else Some gs) with
                                      | Some g => Some (es ++ [(ckn, g, b)], tbl ++ [(T, (fargs, capk), ckn, lfix_meaning fx tys capk (match fx with tFix [d] 0 => nonfn_perm tys (rarg d) | _ => seq 0 (length tys) end))])
                                      | None => None
                                      end
                    | None => None
                    end
                | None => None
                end
            | _ => None
            end
          else
          match tmpl_tys Σ T with
          | None => None
          | Some tys =>
              let nested := fold_left (fun a f => sites 1000 Σ tms hb th (map Some capk) f a) fargs [] in
              (* the copies the template's own body needs, its function parameters bound to the functions given (step 27) *)
              let nested := match lookup_env Σ T with
                            | Some (ConstantDecl cb) =>
                                match cst_body cb with
                                | Some (tFix [d] 0) =>
                                    let body := snd (lams (dbody d)) in
                                    sites 1000 Σ tms hb th (map Some (rev (tkinds rt tys fargs 0) ++ [CSelf] ++ rev capk)) body nested
                                (* (step 59) the budget function's copy for the same functions *)
                                | Some b => match wrap_head b with Some g => (g, fargs, capk) :: nested | None => nested end
                                | None => nested
                                end
                            | _ => nested
                            end in
              match fold_left (fun st s => ensure fuel Σ mp hb rt th tms bt chk s st) (rev nested) st with
              | Some (es, tbl) =>
                  let ckn := (MPfile ["kqcopy"%bs], snd T ^ "__c" ^ string_of_nat (length tbl)) in
                  match body_of Σ T with
                  | Some ((tLambda _ _ _) as wb) =>
                      (* (step 59) read as the wrapper written out at the functions given; its theorem from the wrapper's, equal to the user's at every argument (kitc.py) *)
                      let pn := nonfn_perm tys (tmpl_rarg Σ T) in
                      let trm := wrap_read (copy_meaning_h (fun _ => wb) tys fargs capk pn) in
                      let wkn := (MPfile ["kqcopy"%bs], snd ckn ^ "__w"%bs) in
                      let ty := fold_right (fun t b => tProd anon_b0 t b) (ret_ty (match lookup_env Σ T with Some (ConstantDecl cb) => cst_type cb | _ => tRel 0 end)) (fst (lams trm)) in
                      match reify_fun (add_decl0 Σ ckn ty trm) hb (tc_of Σ mp tbl) rt (callees_of es) ckn bt chk with
                      | Some (g, b) =>
                          Some (es ++ [(ckn, g, b)],
                                tbl ++ [(T, (fargs, capk), ckn, copy_meaning T tys fargs capk pn);
                                        (wkn, ([], []), wkn, copy_meaning_h (fun _ => tConst (MPfile ["kqcopy"%bs], mangle T ^ "__w"%bs) []) tys fargs capk pn)])
                      | None => None
                      end
                  | _ =>
                  match read_tmpl Σ hb (tc_of Σ mp tbl) rt (callees_of es) T fargs capk with
                  | Some (gs, b) => match option_map (with_sp (sp gs)) (if chk then wf_sig (fun g => @wf_f (arity_recs (map (fun e => (snd (fst (fst (fst e))), snd (fst e))) rt) rt) (map snd (callees_of es)) (with_sp false g) b) gs b (bt ckn) else Some gs) with
                                    | Some g => Some (es ++ [(ckn, g, b)], tbl ++ [(T, (fargs, capk), ckn, copy_meaning T tys fargs capk (nonfn_perm tys (tmpl_rarg Σ T)))])
                                    | None => None
                                    end
                  | None => None
                  end
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
      | tApp (tConstruct i _ u) args => fold_left (fun s x => body_rtys fuel Σ hb x s) args (add (ctor_ty Σ i u args) st)
      | tApp f args => fold_left (fun s x => body_rtys fuel Σ hb x s) args (body_rtys fuel Σ hb f st)
      | tLambda _ _ b => body_rtys fuel Σ hb b st
      | tLetIn _ b ty body => body_rtys fuel Σ hb body (body_rtys fuel Σ hb b (add ty st))
      | tCast c _ _ => body_rtys fuel Σ hb c st
      | tCase ci p c brs => fold_left (fun s br => body_rtys fuel Σ hb (bbody br) s) brs
                              (body_rtys fuel Σ hb c (add (ind_app (ci_ind ci) (puinst p) (pparams p)) st))
      | tProj pr c => body_rtys fuel Σ hb c (add (tInd (proj_ind pr) []) st)
      | tFix mfix _ => fold_left (fun s d => body_rtys fuel Σ hb (dbody d) s) mfix st
      | tConst kn _ => if existsb (Kername.eqb kn) (snd st) then st else
                       match hb kn with Some b => body_rtys fuel Σ hb b (fst st, kn :: snd st) | None => st end
      | _ => st
      end
  end.
(** (step 71) a type made from types *)
Fixpoint ty_fun (fuel : nat) (t : term) {struct fuel} : bool :=
  match fuel with O => false | S fuel => match t with tProd _ _ b => ty_fun fuel b | tSort _ => true | _ => false end end.
Fixpoint al_beta (args : list term) (t : term) {struct args} : term :=
  match args, t with
  | [], _ => t
  | a :: r, tLambda _ _ b => al_beta r (subst10 a b)
  | _, _ => mkApps t args
  end.
(** (step 68) a name of the program's for a type, [Definition cell := int]: its definition in its place, in every type and argument *)
Fixpoint al_t (fuel : nat) (Σ : global_env) (mp : modpath) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := al_t fuel Σ mp in
      match t with
      | tConst kn _ =>
          if in_prog mp (fst kn) then
            match lookup_env Σ kn with
            | Some (ConstantDecl cb) =>
                match cst_type cb, cst_body cb with
                | tSort _, Some b => go b
                | _, _ => t
                end
            | _ => t
            end
          else t
      | tProd na a b => tProd na (go a) (go b)
      | tLambda na a b => tLambda na (go a) (go b)
      | tLetIn na v a b => tLetIn na (go v) (go a) (go b)
      | tApp (tConst kn u) args =>
          (* (step 71) a name for a type function, applied: [M A] *)
          if in_prog mp (fst kn) then
            match lookup_env Σ kn with
            | Some (ConstantDecl cb) =>
                match cst_body cb with
                | Some b => if ty_fun 100 (cst_type cb) then go (al_beta args b) else tApp (tConst kn u) (map go args)
                | None => tApp (tConst kn u) (map go args)
                end
            | _ => tApp (tConst kn u) (map go args)
            end
          else tApp (tConst kn u) (map go args)
      | tApp f args => tApp (go f) (map go args)
      | tCase ci p c brs =>
          tCase ci {| pparams := map go (pparams p); puinst := puinst p; pcontext := pcontext p; preturn := go (preturn p) |} (go c)
                (map (fun br => {| bcontext := bcontext br; bbody := go (bbody br) |}) brs)
      | tFix mfix k => tFix (map (fun d => {| dname := dname d; dtype := go (dtype d); rarg := rarg d; dbody := go (dbody d) |}) mfix) k
      | _ => t
      end
  end.
Definition rtab_of (Σ : global_env) (hb : kername -> option term) (kns : list kername) : list rentry :=
  let nrm := al_t 100 Σ (match kns with k :: _ => fst k | [] => MPfile [] end) in
  (* (step 67) the records holding records the bodies use, a value holding booleans or data types wherever it is used: each after what it holds *)
  let fix add_deep (fu : nat) (rt : list rentry) (t : term) {struct fu} : list rentry :=
    match fu with
    | O => rt
    | S fu => match rec_shape Σ t with
              | Some e => match rindex t rt 0 with
                          | Some _ => rt
                          | None => let rt' := fold_left (fun rt q => if is_ty kn_int q then rt
                                                                      else if is_bool q then match rbool rt 0 with Some _ => rt | None => rt ++ [bool_entry] end
                                                                      else add_deep fu rt q) (snd (fst (fst (fst (fst (fst (fst e))))))) rt in
                                    match rindex t rt' 0 with Some _ => rt' | None => rt' ++ [e] end
                          end
              | None => rt
              end
    end in
  let isgen (e : rentry) : bool := match fst (fst (fst (fst (fst (fst (fst e)))))) with [] => false | _ => true end in
  let add_ty := fun rt t => match rec_shape Σ t with
                            | Some e => if isgen e then add_deep 10 rt t else
                                        match rindex t rt 0 with Some _ => rt | None => rt ++ [e] end
                            | None => rt end in
  let sig_rt := fold_left (fun rt kn =>
    match lookup_env Σ kn with
    | Some (ConstantDecl cb) => fold_left add_ty (map nrm (prod_tys (cst_type cb))) rt
    | _ => rt
    end) kns [] in
  (* the bodies' record types after the signatures': a program's record indices are those of before.  A record holding
     records only from a signature (step 32): built and taken apart in a body it needs nothing (step 25) *)
  let btys := map nrm (fst (fold_left (fun s kn => match body_of Σ kn with Some b => body_rtys 2000 Σ hb b s | None => s end) kns ([], []))) in
  let rt1 := fold_left (fun rt t => match rec_shape Σ t with
                         | Some e => if (if isgen e then true else existsb (Nat.ltb 1) (snd e)) then rt
                                     else match rindex t rt 0 with Some _ => rt | None => rt ++ [e] end
                         | None => rt end) btys sig_rt in
  fold_left (fun rt t => match rec_shape Σ t with
                         | Some e => if (if isgen e then true else existsb (Nat.ltb 1) (snd e)) then add_deep 10 rt t else rt
                         | None => rt end) btys rt1.
(** for kitc.py: each record type's text, its constructor's name (a data type's: its constructors' names), its number of fields,
    and a data type's constructors' widths (step 28) *)
Fixpoint ty_text (fuel : nat) (t : term) : string :=
  match fuel with
  | O => ""%bs
  | S fuel => if is_ty kn_int t then "PrimInt63.int"%bs else
              match t with
              | tInd i _ => string_of_kername (inductive_mind i)
              | tApp (tInd i _) ps => "(" ^ string_of_kername (inductive_mind i) ^ fold_left (fun a q => a ^ " " ^ ty_text fuel q) ps "" ^ ")"
              | _ => ""%bs
              end
  end.
(** a constructor's full name: its type's module and its own name *)
Definition ctor_text (t : term) (cn : ident) : string :=
  match t with
  | tInd i _ | tApp (tInd i _) _ => string_of_modpath (fst (inductive_mind i)) ^ "." ^ cn
  | _ => cn
  end.
(** a record holding records, for kitc.py (step 32): its constructor and, field by field, "i" for a number or the inner
    record's own shape -- [pair(pair(i,i),i)] *)
Fixpoint shape_text (fuel : nat) (Σ : global_env) (t : term) : string :=
  match fuel with
  | O => ""%bs
  | S fuel => match rfields Σ t with
              | Some (cn, ftys) =>
                  ctor_text t cn ^ "(" ^ fold_left (fun a q => (if a == "" then ""%bs else a ^ ",") ^ (if is_ty kn_int q then "i"%bs else shape_text fuel Σ q)) ftys ""
                  ^ ")"
              | None => ""%bs
              end
  end.
Definition rec_text (Σ : global_env) (rt : list rentry) (e : rentry) : string * string * nat * string :=
  let '(mf, t, i, n, ps, g, fw) := e in
  let sjoin := fun (sp : string) (l : list string) => fold_left (fun a x => if a == ""%bs then x else a ^ sp ^ x) l ""%bs in
  let idx := fun q => match rindex_f q rt with Some j => string_of_nat j | None => "?"%bs end in
  let cbs0 := match lookup_env Σ (inductive_mind i) with
              | Some (InductiveDecl mib) => match ind_bodies mib with oib :: _ => ind_ctors oib | [] => [] end
              | _ => [] end in
  let cnm := fun cb => string_of_modpath (fst (inductive_mind i)) ^ "." ^ cstr_name cb in
  match fst mf with
  | _ :: _ =>
      if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then ("Corelib.Init.Datatypes.bool"%bs, "true"%bs, 1, "B:"%bs) else
      match g with
      | None => (ty_text 10 t, match cbs0 with cb :: _ => cnm cb | [] => ""%bs end, n,
                 "G:" ^ sjoin "," (map (fun q => if is_ty kn_int q then "i"%bs else idx q) (snd mf)))
      | Some ws =>
          let nn := fold_left Nat.max ws O in
          (ty_text 10 t, sjoin " " (map cnm cbs0), n,
           "T:" ^ string_of_nat nn ^ ";" ^ sjoin "," (map idx (skipn nn (snd mf))) ^ ";"
           ^ sjoin "|" (map (fun m => "x" ^ sjoin "," (map (fun p : bool * nat => (if fst p then "n"%bs else "r"%bs) ^ string_of_nat (snd p)) m)) (fst mf)))
      end
  | [] =>
  if existsb (Nat.ltb 1) fw then (ty_text 10 t, match rfields Σ t with Some (cn, _) => ctor_text t cn | None => ""%bs end, n,
    "N:" ^ shape_text 10 Σ t ^ "@" ^ fold_left (fun a j => (if a == "" then ""%bs else a ^ ",") ^ string_of_nat j)
                                               (match rindex t rt 0 with Some ri => rjs rt ri | None => [] end) "") else
  let nm := string_of_kername (inductive_mind i) in
  let cn_of := fun c => string_of_modpath (fst (inductive_mind i)) ^ "." ^ c in
  let ty := match ps with [] => nm | _ => "(" ^ nm ^ fold_left (fun a _ => a ^ " PrimInt63.int") ps "" ^ ")" end in
  let cbs := match lookup_env Σ (inductive_mind i) with
             | Some (InductiveDecl mib) => match ind_bodies mib with oib :: _ => ind_ctors oib | [] => [] end
             | _ => [] end in
  match g with
  | None => (ty, match cbs with cb :: _ => cn_of (cstr_name cb) | [] => ""%bs end, n, ""%bs)
  | Some ws => (ty, fold_left (fun a cb => a ^ " " ^ cn_of (cstr_name cb)) cbs ""%bs, n, fold_left (fun a w => a ^ " " ^ string_of_nat w) ws ""%bs)
  end
  end.
Definition rec_info (p : program) : list (string * string * nat * string) :=
  match p with
  | (Σ, tConst root _) => let mp := fst root in let kns := reach 1000 Σ mp root root [] in
                          let rt := rtab_of Σ (helper_of Σ mp kns) kns in map (rec_text Σ rt) rt
  | _ => []
  end.

(* ---------------------------------------------------------------- mutual blocks of any signature (step 45) *)
(** a mutual block is read per strongly connected part of its members' call graph, the parts a part calls first.  The part is
    one function: its members' parameters in shared slots (the recursion's counter, one slot for the [i]-th other counter of
    any member, the selector, one slot of a kind for the [i]-th parameter of that kind of any member, the memory), its body the
    members' bodies moved into the slots under a match on the selector, a call of a member of the part its own recursive call
    (the callee's arguments in its slots, every other slot its current value), a call of another part's member a call of that
    member.  Each member is one call of it, the slots not its own given zeros.  Both are written as terms and read by the
    readers of every function; the part's meaning is [blkT] of the members' views, each the fixpoint's member given its own
    parameters from the slots *)
Definition kn_blkT := kn_of <% @KQR.blkT %>.
Definition unread_t : term := tVar "kq_unread"%bs.
Definition anon_b : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition pair_t (a b : term) : term := tApp (tConstruct ind_prod 0 []) [tConst kn_int []; tConst kn_mem []; a; b].
Definition pfst_t (p : term) : term := tApp (tConst kn_pfst []) [tConst kn_int []; tConst kn_mem []; p].
Definition psnd_t (p : term) : term := tApp (tConst kn_psnd []) [tConst kn_int []; tConst kn_mem []; p].
Definition lams_of (tys : list term) (b : term) : term := fold_right (fun ty b => tLambda anon_b ty b) b tys.
Definition pis_of (tys : list term) (b : term) : term := fold_right (fun ty b => tProd anon_b ty b) b tys.
Definition dflt_def : def term := {| dname := anon_b; dtype := unread_t; dbody := unread_t; rarg := 0 |}.
Fixpoint find_idx (x : nat) (l : list nat) : option nat :=
  match l with [] => None | y :: r => if Nat.eqb x y then Some O else option_map S (find_idx x r) end.
(** the members a member's body names *)
Definition mcalls (L : nat) (d : def term) : list nat :=
  map (fun q => Nat.sub (Nat.sub L 1) q) (filter (fun q => Nat.ltb q L) (fvs 1000 0 (dbody d) [])).
Fixpoint mreach (fuel : nat) (g : list (list nat)) (seen todo : list nat) : list nat :=
  match fuel with
  | O => seen
  | S fuel => match todo with
              | [] => seen
              | j :: r => if existsb (Nat.eqb j) seen then mreach fuel g seen r else mreach fuel g (j :: seen) (nth j g [] ++ r)
              end
  end.
Definition reaches (g : list (list nat)) (i j : nat) : bool := existsb (Nat.eqb j) (mreach 1000 g [] (nth i g [])).
Definition part_of (g : list (list nat)) (L j : nat) : list nat :=
  filter (fun i => Nat.eqb i j || (reaches g j i && reaches g i j)) (seq 0 L).
Definition mem_kn (mp : modpath) (mfix : mfixpoint term) (i : nat) : kername :=
  (mp, match nth_error mfix i with
       | Some d => match binder_name (dname d) with nNamed s => s | nAnon => "kq_member"%bs end
       | None => "kq_member"%bs end).
Definition part_name (mp : modpath) (mfix : mfixpoint term) (P : list nat) : kername :=
  (copy_mp, mangle (mem_kn mp mfix (hd O P)) ^ "__cblk").
Definition known (kn : kername) (es : list (kername * sig * fbody)) (tbl : copytab) : bool :=
  existsb (fun e => Kername.eqb (fst (fst e)) kn) es || existsb (fun e => Kername.eqb (fst (fst (fst e))) kn) tbl.
(** a member's parameter: the recursion's counter, its [q]-th other counter, its [o]-th parameter of a kind, the memory, a
    number-and-memory pair (its number its [o]-th number) *)
Inductive pcl := PRec | POc (q : nat) | PVal (k : kind) (o : nat) | PMemC | PPair (o : nat).
Definition classify_params (rt : list rentry) (tys : list term) (r : nat) : option (list pcl) :=
  opt_all (map (fun u =>
    let ty := nth u tys (tRel 0) in
    let pre := combine (seq 0 u) (firstn u tys) in
    let nkind (k : kind) := length (filter (fun p => match kind_ty rt (snd p) with
                                                     | Some k' => kind_eqb k k'
                                                     | None => is_pm (snd p) && kind_eqb k KNum end) pre) in
    if Nat.eqb u r then (if is_nat ty then Some PRec else None)
    else if is_nat ty then Some (POc (length (filter (fun p => is_nat (snd p) && negb (Nat.eqb (fst p) r)) pre)))
    else if is_ty kn_mem ty then Some PMemC
    else if is_pm ty then Some (PPair (nkind KNum))
    else option_map (fun k => PVal k (nkind k)) (kind_ty rt ty)) (seq 0 (length tys))).
(** the slots of a kind: a member's [o]-th parameter of kind [k] the [o]-th slot of that kind *)
Fixpoint kslot (K : list (kind * term)) (k : kind) (o : nat) : nat :=
  match K with
  | [] => O
  | (k', _) :: K' => if kind_eqb k k' then match o with O => O | S o' => S (kslot K' k o') end else S (kslot K' k o)
  end.
Definition add_slots (K : list (kind * term)) (cls : list pcl) (tys : list term) : list (kind * term) :=
  let nof k K := length (filter (fun e => kind_eqb (fst e) k) K) in
  fold_left (fun K ct => match ct with
                         | (PVal k o, ty) => if Nat.eqb (nof k K) o then K ++ [(k, ty)] else K
                         | (PPair o, _) => if Nat.eqb (nof KNum K) o then K ++ [(KNum, tConst kn_int [])] else K
                         | _ => K
                         end) (combine cls tys) K.
(** a member's body in the block: each parameter the block's binder of its slot (a pair the pair of its two) *)
Definition rel_arg (NB : nat) (ps : list nat) : term :=
  match ps with [p] => tRel (NB - 1 - p) | [p1; p2] => pair_t (tRel (NB - 1 - p1)) (tRel (NB - 1 - p2)) | _ => unread_t end.
Definition relocate (NB : nat) (pss : list (list nat)) (body : term) : term :=
  let N := length pss in subst (map (fun k => rel_arg NB (nth (N - 1 - k) pss [])) (seq 0 N)) 0 (lift NB N body).
Definition sel_lit (j : nat) : term := tApp (tConst kn_kq_nat []) [tInt (Uint63.of_Z (Z.of_nat j))].
(** which parameter of a member stands in slot [p]: the parameter, and 0 (its slot), 1 (a pair's number), 2 (a pair's memory) *)
Fixpoint find_pos (p : nat) (pss : list (list nat)) (u : nat) : option (nat * nat) :=
  match pss with
  | [] => None
  | ps :: r => match ps with
               | [a] => if Nat.eqb a p then Some (u, 0) else find_pos p r (S u)
               | [a; b] => if Nat.eqb a p then Some (u, 1) else if Nat.eqb b p then Some (u, 2) else find_pos p r (S u)
               | _ => find_pos p r (S u)
               end
  end.
Definition slot_arg (pss : list (list nat)) (p : nat) (args : list term) (dflt : term) : term :=
  match find_pos p pss 0 with
  | Some (u, 0) => nth u args unread_t
  | Some (u, 1) => pfst_t (nth u args unread_t)
  | Some (u, _) => psnd_t (nth u args unread_t)
  | None => dflt
  end.
(** two parameters of a member in one slot (step 53, two memory parameters): a call gives them the same *)
Definition slots_agree (pss : list (list nat)) (args : list term) : bool :=
  forallb (fun u => match nth u pss [] with
                    | [p] => match find_pos p pss 0 with
                             | Some (u0, 0) => if Nat.eqb u0 u then true else teq 1000 (nth u args unread_t) (nth u0 args unread_t)
                             | _ => true
                             end
                    | _ => true
                    end) (seq 0 (length pss)).
(** the calls of the members: of the part, its own recursive call; of another part, a call of that member *)
Fixpoint sibr (fuel : nat) (L NB X : nat) (pin : nat -> option (nat * list (list nat))) (nargs : nat -> nat) (outk : nat -> kername)
  (d : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => unread_t
  | S fuel =>
      let go := sibr fuel L NB X pin nargs outk in
      match t with
      | tRel i => if Nat.leb (d + NB) i then (if Nat.ltb i (d + NB + L) then unread_t else tRel (i - L + 1)) else t
      | tApp (tRel i) args =>
          let args' := map (go d) args in
          if Nat.leb (d + NB) i && Nat.ltb i (d + NB + L) then
            let jj := Nat.sub (Nat.sub L 1) (i - d - NB) in
            if Nat.eqb (length args') (nargs jj) then
              match pin jj with
              | Some (sel, pss) =>
                  if slots_agree pss args' then
                  tApp (tRel (d + NB)) (map (fun p => if Nat.eqb p (S X) then sel_lit sel else slot_arg pss p args' (tRel (d + NB - 1 - p)))
                                            (seq 0 NB))
                  else unread_t
              | None => tApp (tConst (outk jj) []) args'
              end
            else unread_t
          else tApp (go d (tRel i)) args'
      | tApp f args => tApp (go d f) (map (go d) args)
      | tLambda na ty b => tLambda na (go d ty) (go (S d) b)
      | tProd na ty b => tProd na (go d ty) (go (S d) b)
      | tLetIn na b ty body => tLetIn na (go d b) (go d ty) (go (S d) body)
      | tCase ci p c brs =>
          tCase ci {| puinst := puinst p; pparams := map (go d) (pparams p); pcontext := pcontext p;
                      preturn := go (d + length (pcontext p)) (preturn p) |}
                (go d c) (map (fun br => {| bcontext := bcontext br; bbody := go (d + length (bcontext br)) (bbody br) |}) brs)
      | tFix mfix k => tFix (map (fun df => {| dname := dname df; dtype := go d (dtype df); dbody := go (d + length mfix) (dbody df);
                                               rarg := rarg df |}) mfix) k
      | tProj pr c => tProj pr (go d c)
      | tCast c k ty => tCast (go d c) k (go d ty)
      | _ => t
      end
  end.
(** a value for a slot that is not the member's: a counter or a number 0, [false], a record of zeros *)
Fixpoint zero_of (rt : list rentry) (fuel : nat) (ty : term) : term :=
  match fuel with
  | O => unread_t
  | S fuel =>
      if is_ty kn_int ty then tInt (Uint63.of_Z 0) else if is_bool ty then tConstruct ind_bool 1 [] else if is_nat ty then tConstruct ind_nat 0 []
      else match option_map (fun i => nth_error rt i) (rindex ty rt 0) with
           | Some (Some ((_, fts), _, ind, _, pars, None, _)) =>
               match fts with [] => unread_t | _ => tApp (tConstruct ind 0 []) (pars ++ map (zero_of rt fuel) fts) end
           | _ => unread_t
           end
  end.
(** the members' bodies under a match on the selector: member [j] under [j] binders more ([k] those above) *)
Fixpoint nest_t (ci : case_info) (pr : predicate term) (bc1 : list aname) (sv : term) (k : nat) (es : list term) : term :=
  match es with
  | [] => unread_t
  | [e] => lift0 k e
  | e :: es' => tCase ci pr sv [{| bcontext := []; bbody := lift0 k e |}; {| bcontext := bc1; bbody := nest_t ci pr bc1 (tRel 0) (S k) es' |}]
  end.
Definition add_decl (Σ : global_env) (kn : kername) (ty b : term) : global_env :=
  {| universes := universes Σ;
     declarations := (kn, ConstantDecl {| cst_type := ty; cst_body := Some b; cst_universes := Monomorphic_ctx; cst_relevance := Relevant |})
                     :: declarations Σ;
     retroknowledge := retroknowledge Σ |}.
(** a part's slots: the other counters, the slots of the kinds, the memory, the number of binders, each member's parameters'
    binders, the binders' types *)
Definition part_layout (rt : list rentry) (mfix : mfixpoint term) (P : list nat)
  : option (nat * list (kind * term) * bool * nat * list (list (list nat)) * list term) :=
  let ds := map (fun i => nth i mfix dflt_def) P in
  let tyss := map (fun d => fst (lams (dbody d))) ds in
  match opt_all (map (fun dt => classify_params rt (fst dt) (rarg (snd dt))) (combine tyss ds)) with
  | None => None
  | Some clss =>
      let X := fold_left Nat.max (map (fun cls => length (filter (fun c => match c with POc _ => true | _ => false end) cls)) clss) O in
      let K := fold_left (fun K ct => add_slots K (fst ct) (snd ct)) (combine clss tyss) [] in
      let M := existsb (fun cls => existsb (fun c => match c with PMemC | PPair _ => true | _ => false end) cls) clss in
      let posc (c : pcl) : list nat :=
        match c with
        | PRec => [O] | POc q => [S q] | PVal k o => [S (S X) + kslot K k o] | PMemC => [S (S X) + length K]
        | PPair o => [S (S X) + kslot K KNum o; S (S X) + length K]
        end in
      Some (X, K, M, S (S X) + length K + (if M then 1 else 0), map (map posc) clss,
            [tInd ind_nat []] ++ repeat (tInd ind_nat []) X ++ [tInd ind_nat []] ++ map snd K ++ (if M then [tConst kn_mem []] else []))
  end.
(** a part's block function: the members' bodies in the slots under a match on the selector *)
Definition read_part (Σ : global_env) (mp : modpath) (hb : kername -> option term) (rt : list rentry) (bt : kername -> option Z) (chk : bool)
  (mfix : mfixpoint term) (P : list nat) (st : list (kername * sig * fbody) * copytab) : option (list (kername * sig * fbody) * copytab) :=
  let '(es, tbl) := st in
  let L := length mfix in
  let bn := part_name mp mfix P in
  let ds := map (fun i => nth i mfix dflt_def) P in
  let T := ret_ty (dtype (hd dflt_def ds)) in
  match part_layout rt mfix P with
  | None => None
  | Some (X, K, M, NB, psss, btys) =>
  if negb (forallb (fun d => teq 1000 (ret_ty (dtype d)) T) ds) then None else
  let pin := fun jj => option_map (fun s => (s, nth s psss [])) (find_idx jj P) in
  let nargs := fun jj => match nth_error mfix jj with Some d => length (fst (lams (dbody d))) | None => O end in
  let rd (dps : def term * list (list nat)) :=
    let body := sibr 100000 L NB X pin nargs (mem_kn mp mfix) 0 (relocate NB (snd dps) (snd (lams (dbody (fst dps))))) in
    let body := if M then flatp 100000 (fun _ _ => false) 0 body else body in
    match body with
    | tCase ci pr (tRel c) [b0; b1] => if Nat.eqb c (NB - 1) then Some (ci, pr, b0, b1) else None
    | _ => None
    end in
  match opt_all (map rd (combine ds psss)) with
  | Some (((ci, pr, b0, b1) :: _) as cs) =>
      let bc1 := bcontext b1 in
      let sv d := tRel (d + NB - 1 - S X) in
      let body := tCase ci pr (tRel (NB - 1))
                    [{| bcontext := []; bbody := nest_t ci pr bc1 (sv 0) 0 (map (fun c => bbody (snd (fst c))) cs) |};
                     {| bcontext := bc1; bbody := nest_t ci pr bc1 (sv 1) 0 (map (fun c => bbody (snd c)) cs) |}] in
      let bty := pis_of btys T in
      let bfix := tFix [{| dname := {| binder_name := nNamed (snd bn); binder_relevance := Relevant |}; dtype := bty;
                           dbody := lams_of btys body; rarg := 0 |}] 0 in
      let Σ1 := add_decl Σ bn bty bfix in
      match reify_fun Σ1 hb (tc_of Σ1 mp tbl) rt (callees_of es) bn bt chk with
      | Some (gs, b) =>
          (* the views: the block's binders but the selector, the member given its own *)
          let vtys := firstn (S X) btys ++ skipn (S (S X)) btys in
          let NV := length vtys in
          let vpos p := if Nat.leb p X then p else Nat.pred p in
          let varg (ps : list nat) := match ps with
                                      | [p] => tRel (NV - 1 - vpos p)
                                      | [p1; p2] => pair_t (tRel (NV - 1 - vpos p1)) (tRel (NV - 1 - vpos p2))
                                      | _ => unread_t end in
          let views := map (fun ip => lams_of vtys (tApp (tFix mfix (fst ip)) (map varg (snd ip)))) (combine P psss) in
          let mn := tApp (tConst kn_blkT []) [tConst kn_no_recs []; qnat X; qlist (tInd ind_kind []) (map (fun e => qkind (fst e)) K);
                                              tConstruct ind_bool (if M then 0 else 1) []; T; hd unread_t views; qlist (pis_of vtys T) (tl views)] in
          Some (es ++ [(bn, gs, b)], tbl ++ [(bn, ([], []), bn, mn)])
      | None => None
      end
  | _ => None
  end
  end.
(** a member: one call of its part's block function, the slots not its own given zeros *)
Definition add_member (Σ : global_env) (mp : modpath) (hb : kername -> option term) (rt : list rentry) (bt : kername -> option Z) (chk : bool)
  (mfix : mfixpoint term) (P : list nat) (i : nat) (st : option (list (kername * sig * fbody) * copytab))
  : option (list (kername * sig * fbody) * copytab) :=
  match st, part_layout rt mfix P, find_idx i P with
  | Some (es, tbl), Some (X, K, M, NB, psss, btys), Some sel =>
      let kn := mem_kn mp mfix i in
      if known kn es tbl then st else
      let pss := nth sel psss [] in
      let d := nth i mfix dflt_def in
      let tys := fst (lams (dbody d)) in
      let N := length tys in
      let marg p := if Nat.eqb p (S X) then sel_lit sel
                    else match find_pos p pss 0 with
                         | Some (u, 0) => tRel (N - 1 - u)
                         | Some (u, 1) => pfst_t (tRel (N - 1 - u))
                         | Some (u, _) => psnd_t (tRel (N - 1 - u))
                         | None => zero_of rt 100 (nth p btys unread_t)
                         end in
      let Σ2 := add_decl Σ kn (dtype d) (lams_of tys (tApp (tConst (part_name mp mfix P) []) (map marg (seq 0 NB)))) in
      match reify_fun Σ2 hb (tc_of Σ2 mp tbl) rt (callees_of es) kn bt chk with
      | Some (gs, b) => Some (add_fun Σ2 kn gs b es tbl)
      | None => None
      end
  | _, _, _ => None
  end.
(** a part whose members give back different types (not read yet) *)
Definition mixed_part (mfix : mfixpoint term) (k : nat) : bool :=
  let T := ret_ty (dtype (nth k mfix dflt_def)) in
  existsb (fun i => negb (teq 1000 (ret_ty (dtype (nth i mfix dflt_def))) T)) (part_of (map (mcalls (length mfix)) mfix) (length mfix) k).
(** a member's part, after the parts it calls (and the members of theirs it calls) *)
Fixpoint ensure_part (fuel : nat) (Σ : global_env) (mp : modpath) (hb : kername -> option term) (rt : list rentry) (bt : kername -> option Z)
  (chk : bool) (mfix : mfixpoint term) (g : list (list nat)) (j : nat) (st : option (list (kername * sig * fbody) * copytab)) {struct fuel}
  : option (list (kername * sig * fbody) * copytab) :=
  match fuel with
  | O => None
  | S fuel =>
      match st with
      | None => None
      | Some (es, tbl) =>
          let P := part_of g (length mfix) j in
          if known (part_name mp mfix P) es tbl then st else
          let deps := filter (fun i => negb (existsb (Nat.eqb i) P)) (flat_map (fun i => nth i g []) P) in
          match fold_left (fun st i => add_member Σ mp hb rt bt chk mfix (part_of g (length mfix) i) i (ensure_part fuel Σ mp hb rt bt chk mfix g i st))
                          deps st with
          | Some st' => read_part Σ mp hb rt bt chk mfix P st'
          | None => None
          end
      end
  end.

(** (step 48 continued) [let p := e in body], p a number and a memory that [body] uses bare, in tail position or as an operand: a function
    of its own, the free variables of the body its parameters (the counters first) and the pair the last, and the let a call of it
    given [e]: up to beta and zeta the same term, and a call given a pair and a function with a pair parameter are read since step
    44.  A variable that is not a number, a boolean, a counter or a record (the function itself, another memory: two versions), or of
    a type not known here, leaves the let as it is *)
Definition lift_param (y : term) : bool :=
  match y with
  | tInd _ _ => true
  | tConst kn _ => Kername.eqb kn kn_int
  | _ => false
  end.
Fixpoint ins_desc (x : nat) (l : list nat) : list nat :=
  match l with [] => [x] | y :: r => if Nat.ltb y x then x :: l else y :: ins_desc x r end.
Definition lift_tys (ci : case_info) (p : predicate term) (br : branch term) : list (option term) :=
  if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then map (fun _ => Some (tInd ind_nat [])) (bcontext br)
  else if is_pm_case ci p br then [Some (tConst kn_mem []); Some (tConst kn_int [])]
  else map (fun _ => None) (bcontext br).
Fixpoint lift_pm (fuel : nat) (mp : modpath) (base : string) (rq : option term) (ctx : list (option term)) (acc : list (string * term * term))
  (t : term) {struct fuel} : term * list (string * term * term) :=
  match fuel with
  | O => (t, acc)
  | S fuel =>
      match t with
      | tLambda na ty b => let '(b', acc') := lift_pm fuel mp base rq (Some ty :: ctx) acc b in (tLambda na ty b', acc')
      | tFix [d] k =>
          let '(b', acc') := lift_pm fuel mp base (Some (ret_ty (dtype d))) (None :: ctx) acc (dbody d) in
          (tFix [{| dname := dname d; dtype := dtype d; dbody := b'; rarg := rarg d |}] k, acc')
      | tCase ci p c brs =>
          let '(c', acc1) := lift_pm fuel mp base None ctx acc c in
          let '(brs', acc2) := fold_left (fun st br =>
                let '(l, a) := st in
                let '(bb, a') := lift_pm fuel mp base rq (lift_tys ci p br ++ ctx) a (bbody br) in
                (l ++ [{| bcontext := bcontext br; bbody := bb |}], a')) brs ([], acc1) in
          (tCase ci p c' brs', acc2)
      | tApp f args =>
          let rq' := match f with tConst kn _ => if eq_mp (fst kn) prim_mp then Some (tConst kn_int []) else None | _ => None end in
          let '(args', acc') := fold_left (fun st a =>
                let '(l, ac) := st in
                let '(a', ac') := lift_pm fuel mp base rq' ctx ac a in (l ++ [a'], ac')) args ([], acc) in
          (tApp f args', acc')
      | tLetIn na b ty body =>
          let '(b', acc1) := lift_pm fuel mp base None ctx acc b in
          let '(body', acc2) := lift_pm fuel mp base rq (Some ty :: ctx) acc1 body in
          let t' := tLetIn na b' ty body' in
          match rq with
          | Some T =>
              if is_pm ty && pm_bare 100000 0 body' then
                match hoist_core (fun j => match nth_error ctx j with Some (Some y) => is_ty kn_mem y | _ => false end) (fun _ => None) t' with
                | Some t2 => lift_pm fuel mp base rq ctx acc2 t2
                | None =>
                let fv := fvs 1000 1 body' [] in
                let tyof j := match nth_error ctx j with Some (Some y) => if lift_param y then Some y else None | _ => None end in
                match opt_all (map tyof fv) with
                | Some _ =>
                    let dflt := tRel 0 in
                    let isn j := match tyof j with Some y => is_nat y | None => false end in
                    let P := fold_right ins_desc [] (filter isn fv) ++ fold_right ins_desc [] (filter (fun j => negb (isn j)) fv) in
                    let m := length P in
                    let tys := map (fun j => match tyof j with Some y => y | None => dflt end) P ++ [ty] in
                    let sg := map (fun j => match find_idx j P with Some q => tRel (m - 1 - q) | None => dflt end) (seq 0 (length ctx)) in
                    let nm := base ^ "__l"%bs ^ string_of_nat (length acc2) in
                    (tApp (tConst (mp, nm) []) (map tRel P ++ [b']), acc2 ++ [(nm, pis_of tys T, lams_of tys (subst sg 1 body'))])
                | None => (t', acc2)
                end
                end
              else (t', acc2)
          | None => (t', acc2)
          end
      | _ => (t, acc)
      end
  end.
(** the program with its lets lifted: the environment with the new functions and each function's new text, the functions, the new
    functions' terms *)
(** a function whose next parameter stands after a let, as a section's [Let] leaves it (step 51): [fun k => let y := e in fun x => b]
    is [fun k x => let y := e in b] up to zeta, the same for its type, and a function is read from its parameters *)
Fixpoint let_then_lam (fuel : nat) (seen : bool) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel => match t with
              | tLambda _ _ b => if seen then true else let_then_lam fuel false b
              | tLetIn _ _ _ b => let_then_lam fuel true b
              | _ => false
              end
  end.
Fixpoint float_lets (fuel : nat) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tLambda na ty b => tLambda na ty (float_lets fuel b)
      | tLetIn na e ty b =>
          match float_lets fuel b with
          | tLambda nz tz bz =>
              tLambda nz (subst10 e tz)
                (float_lets fuel (tLetIn na (lift0 1 e) (lift0 1 ty) (subst [tRel 1; tRel 0] 0 (lift 2 2 bz))))
          | b' => tLetIn na e ty b'
          end
      | _ => t
      end
  end.
Fixpoint zeta_prods (fuel : nat) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tProd na a b => tProd na a (zeta_prods fuel b)
      | tLetIn _ e _ b => zeta_prods fuel (subst10 e b)
      | _ => t
      end
  end.
(** the functions read: each with its lets floated, before its pairs are lifted *)
Definition float_all (Σ : global_env) (kns : list kername) : global_env :=
  fold_left (fun S1 kn =>
    match lookup_env S1 kn with
    | Some (ConstantDecl cb) =>
        match cst_body cb with
        | Some b => if let_then_lam 1000 false b then add_decl S1 kn (zeta_prods 1000 (cst_type cb)) (float_lets 1000 b) else S1
        | None => S1
        end
    | _ => S1
    end) kns Σ.
Definition add_decl_cb (Σ : global_env) (kn : kername) (cb : constant_body) : global_env :=
  {| universes := universes Σ; declarations := (kn, ConstantDecl cb) :: declarations Σ; retroknowledge := retroknowledge Σ |}.
Definition lift_all (Σ : global_env) (mp : modpath) (kns : list kername) : global_env * list kername * copytab :=
  fold_left (fun st kn =>
    let '(S1, ks, tb) := st in
    match lookup_env S1 kn with
    | Some (ConstantDecl cb) =>
        match cst_body cb with
        | Some b =>
            if has_pm_let 1000 b then
              let '(b', ls) := lift_pm 100000 copy_mp (mangle kn) (Some (ret_ty (cst_type cb))) [] [] b in
              let S2 := fold_left (fun s l => add_decl s (copy_mp, fst (fst l)) (snd (fst l)) (snd l)) ls S1 in
              (add_decl S2 kn (cst_type cb) b', ks ++ map (fun l => (copy_mp, fst (fst l))) ls ++ [kn],
               tb ++ map (fun l => ((copy_mp, fst (fst l)), ([], []), (copy_mp, fst (fst l)), snd l)) ls)
            else (S1, ks ++ [kn], tb)
        | None => (S1, ks ++ [kn], tb)
        end
    | _ => (S1, ks ++ [kn], tb)
    end) kns (Σ, [], []).
(** (step 54) a number, a boolean, a record that writes under a let or a match, where something else is still to be worked out: as an operand, a
    call's argument, a let's value, a test.  It cannot be bound by a let (a match on a stuck term does not commute with what is around it), so it is
    a function of its variables, and a call of that function stands there, bound as any call that writes: the same term up to delta and beta *)
Fixpoint writes_t (fuel : nat) (Σ : global_env) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      existsb (fun k => if eq_mp (fst k) copy_mp then true else   (* a function just made: it writes *)
                        match lookup_env Σ k with
                        | Some (ConstantDecl cb) =>
                            let r := ret_ty (cst_type cb) in
                            if is_ty kn_mem r then true else if is_pm r then true
                            else if lib_file (mp_file (fst k)) then false
                            else match cst_body cb with Some b => writes_t fuel Σ b | None => false end
                        | _ => false
                        end) (consts 1000 t [])
  end.
Definition op_param (y : term) : bool :=
  match y with
  | tInd _ _ | tApp (tInd _ _) _ => true
  | tConst kn _ => if Kername.eqb kn kn_int then true else Kername.eqb kn kn_mem
  | _ => false
  end.
Definition op_res (y : term) : bool :=
  match y with
  | tInd i _ => negb (Kername.eqb (inductive_mind i) (inductive_mind ind_nat))
  | tApp (tInd _ _) _ => is_pm y
  | tConst kn _ => Kername.eqb kn kn_int
  | _ => false
  end.
Definition opnd (Σ : global_env) (base : string) (ctx : list (option term)) (acc : list (string * term * term)) (oty : option term) (a : term)
  : term * list (string * term * term) :=
  match oty, a with
  | Some T, (tLetIn _ _ _ _ | tCase _ _ _ _) =>
      if op_res T then
        if writes_t 6 Σ a then
          let fv := fvs 1000 0 a [] in
          let tyof j := match nth_error ctx j with Some (Some y) => if op_param y then Some y else None | _ => None end in
          match opt_all (map tyof fv) with
          | Some _ =>
              let dflt := tRel 0 in
              let cl j := match tyof j with Some y => if is_nat y then 0 else if is_ty kn_mem y then 2 else 1 | None => 1 end in
              let part c := fold_right ins_desc [] (filter (fun j => Nat.eqb (cl j) c) fv) in
              let P := part 0 ++ part 1 ++ part 2 in
              let m := length P in
              let tys := map (fun j => match tyof j with Some y => y | None => dflt end) P in
              let sg := map (fun j => match find_idx j P with Some q => tRel (m - 1 - q) | None => dflt end) (seq 0 (length ctx)) in
              let nm := base ^ "__kq"%bs ^ string_of_nat (length acc) in
              (tApp (tConst (copy_mp, nm) []) (map tRel P), acc ++ [(nm, pis_of tys T, lams_of tys (subst sg 0 a))])
          | None => (a, acc)
          end
        else (a, acc)
      else (a, acc)
  | _, _ => (a, acc)
  end.
Definition head_ty (Σ : global_env) (f : term) : term :=
  match f with
  | tConst kn _ => match lookup_env Σ kn with Some (ConstantDecl cb) => cst_type cb | _ => tRel 0 end
  | tConstruct i n _ =>
      match lookup_env Σ (inductive_mind i) with
      | Some (InductiveDecl mib) =>
          match nth_error (ind_bodies mib) (inductive_ind i) with
          | Some oib => match nth_error (ind_ctors oib) n with Some cb => cstr_type cb | None => tRel 0 end
          | None => tRel 0
          end
      | _ => tRel 0
      end
  | _ => tRel 0
  end.
Fixpoint arg_tys (args : list term) (ft : term) : list (option term) :=
  match args with
  | [] => []
  | x :: r => match ft with
              | tProd _ a b => Some a :: arg_tys r (subst10 x b)
              | _ => None :: arg_tys r ft
              end
  end.
Fixpoint lift_op (fuel : nat) (Σ : global_env) (base : string) (ctx : list (option term)) (acc : list (string * term * term)) (t : term)
  {struct fuel} : term * list (string * term * term) :=
  match fuel with
  | O => (t, acc)
  | S fuel =>
      match t with
      | tLambda na ty b => let '(b', a') := lift_op fuel Σ base (Some ty :: ctx) acc b in (tLambda na ty b', a')
      | tFix mfix k =>
          let cx := repeat None (length mfix) ++ ctx in
          let '(ds, a') := fold_left (fun st d =>
                let '(l, ac) := st in
                let '(b', ac') := lift_op fuel Σ base cx ac (dbody d) in
                (l ++ [{| dname := dname d; dtype := dtype d; dbody := b'; rarg := rarg d |}], ac')) mfix ([], acc) in
          (tFix ds k, a')
      | tCase ci p c brs =>
          let '(c1, a1) := lift_op fuel Σ base ctx acc c in
          let T := if Nat.eqb (ci_npar ci) 0 then Some (tInd (ci_ind ci) []) else None in
          let '(c2, a2) := opnd Σ base ctx a1 T c1 in
          let '(brs', a3) := fold_left (fun st br =>
                let '(l, a) := st in
                let '(bb, a') := lift_op fuel Σ base (lift_tys ci p br ++ ctx) a (bbody br) in
                (l ++ [{| bcontext := bcontext br; bbody := bb |}], a')) brs ([], a2) in
          (tCase ci p c2 brs', a3)
      | tApp f args =>
          let '(args1, a1) := fold_left (fun st a =>
                let '(l, ac) := st in
                let '(a', ac') := lift_op fuel Σ base ctx ac a in (l ++ [a'], ac')) args ([], acc) in
          let '(args2, a2) := fold_left (fun st ap =>
                let '(l, ac) := st in
                let '(a', ac') := opnd Σ base ctx ac (snd ap) (fst ap) in (l ++ [a'], ac')) (combine args1 (arg_tys args1 (head_ty Σ f))) ([], a1) in
          (tApp f args2, a2)
      | tLetIn na b ty body =>
          let '(b1, a1) := lift_op fuel Σ base ctx acc b in
          let '(b2, a2) := opnd Σ base ctx a1 (Some ty) b1 in
          let '(body', a3) := lift_op fuel Σ base (Some ty :: ctx) a2 body in
          (tLetIn na b2 ty body', a3)
      | _ => (t, acc)
      end
  end.
Definition lift_ops (Σ : global_env) (mp : modpath) (root : kername) : global_env * copytab :=
  fold_left (fun st kn =>
    let '(S1, tb) := st in
    if in_prog mp (fst kn) then
      match lookup_env S1 kn with
      | Some (ConstantDecl cb) =>
          match cst_body cb with
          | Some b =>
              match lift_op 100000 Σ (mangle kn) [] [] b with
              | (_, []) => st
              | (b', ls) =>
                  (add_decl (fold_left (fun s l => add_decl s (copy_mp, fst (fst l)) (snd (fst l)) (snd l)) ls S1) kn (cst_type cb) b',
                   tb ++ map (fun l => ((copy_mp, fst (fst l)), ([], []), (copy_mp, fst (fst l)), snd l)) ls)
              end
          | None => st
          end
      | _ => st
      end
    else st) (snd (reach_go 1000 Σ mp root root ([], []))) (Σ, []).
Fixpoint real_copies (fuel : nat) (dp : modpath) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tConst kn u => if eq_mp (fst kn) copy_mp then tConst (dp, snd kn) u else t
      | tApp f args => tApp (real_copies fuel dp f) (map (real_copies fuel dp) args)
      | tLambda na ty b => tLambda na ty (real_copies fuel dp b)
      | tProd na ty b => tProd na ty (real_copies fuel dp b)
      | tLetIn na b ty body => tLetIn na (real_copies fuel dp b) ty (real_copies fuel dp body)
      | tCase ci p c brs => tCase ci p (real_copies fuel dp c) (map (fun br => {| bcontext := bcontext br; bbody := real_copies fuel dp (bbody br) |}) brs)
      | tFix mfix k => tFix (map (fun d => {| dname := dname d; dtype := dtype d; dbody := real_copies fuel dp (dbody d); rarg := rarg d |}) mfix) k
      | _ => t
      end
  end.
(* ---------------------------------------------------------------- Rocq's own measure recursion (step 56) *)
Definition kn_fix_sub := kn_of <% @Corelib.Program.Wf.Fix_sub %>.
Definition kn_mr := kn_of <% @Corelib.Program.Wf.MR %>.
Definition kn_z_to_nat := kn_of <% Z.to_nat %>.
Definition kn_s_to_z := kn_of <% Sint63.to_Z %>.
Definition ind_sigT := ind_of <% @sigT %>.
Definition fix_sub_app (t : term) : option (term * term) :=
  match t with
  | tApp (tConst kn _) [_; tApp (tConst mr _) [_; _; _; m]; _; _; fs] =>
      if Kername.eqb kn kn_fix_sub then if Kername.eqb mr kn_mr then Some (m, fs) else None else None
  | _ => None
  end.
(** the parameters' types, the measure, the elaborated functional, the constant holding the [Fix_sub] when it is not the function *)
Definition pf_parts (Σ : global_env) (kn : kername) : option (list term * term * term * term * option kername) :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some b =>
          let T := ret_ty (cst_type cb) in
          match fix_sub_app b with
          | Some (m, fs) =>
              (* one parameter: several are packed in a sigma, and that constant is the one the function calls *)
              match prod_tys (cst_type cb) with
              | tApp (tInd i _) _ :: _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_sigT) then None else None
              | t :: _ => Some ([t], T, m, fs, None)
              | [] => None
              end
          | None =>
              let '(tys, r) := lams b in
              match r with
              | tApp (tConst fk _) [_] =>
                  match body_of Σ fk with
                  | Some fb => match fix_sub_app fb with Some (m, fs) => Some (tys, T, m, fs, Some fk) | None => None end
                  | None => None
                  end
              | _ => None
              end
          end
      | None => None
      end
  | _ => None
  end.
Definition kn_dec := kn_of <% @Corelib.Init.Sumbool.sumbool_of_bool %>.
Definition pf_case_bool := <% fun b : bool => if b then O else O %>.
Definition pf_prog_let (na : aname) : bool :=
  match binder_name na with
  | nNamed s => if String.prefix "filtered_var"%bs s then true else String.prefix "program_branch"%bs s
  | nAnon => false
  end.
(** a branch as [Program] writes it: its pattern's variables given, the proof of the test dropped *)
Fixpoint pf_strip (fuel : nat) (u : term) : term :=
  match fuel with
  | O => u
  | S fuel =>
      match u with
      | tApp (tLambda _ _ b) (a :: r) => pf_strip fuel (match r with [] => subst10 a b | _ => tApp (subst10 a b) r end)
      | tLambda _ _ a => subst10 (tVar "kqproof"%bs) a
      | _ => u
      end
  end.
(** the functional's body with its proofs dropped: [d] the place of the local function that gives the proof *)
Fixpoint pf_plain (fuel d : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tApp (tRel i) args =>
          if Nat.eqb i d then tApp (tVar "kqself"%bs) (map (pf_plain fuel d) (removelast args))
          else tApp (tRel i) (map (pf_plain fuel d) args)
      | tApp (tCase ci p c brs) [_] =>
          match preturn p with
          | tProd _ _ R =>
              tCase ci {| pparams := pparams p; puinst := puinst p; pcontext := pcontext p; preturn := subst10 (tVar "kqproof"%bs) R |}
                    (pf_plain fuel d c)
                    (map (fun br => {| bcontext := bcontext br; bbody := pf_plain fuel (d + length (bcontext br)) (pf_strip 100 (bbody br)) |}) brs)
          | _ => t
          end
      | tApp f args => tApp (pf_plain fuel d f) (map (pf_plain fuel d) args)
      (* [if dec c then a else b]: the test itself, the proof each branch binds never used but in a proof dropped *)
      | tCase ci p (tApp (tConst k _) [c]) [b0; b1] =>
          if Kername.eqb k kn_dec then
            match pf_case_bool with
            | tLambda _ _ (tCase ci' p' _ [br0; br1]) =>
                tCase ci' {| pparams := pparams p'; puinst := puinst p'; pcontext := pcontext p'; preturn := lift0 1 (subst10 (tVar "kqproof"%bs) (preturn p)) |} (pf_plain fuel d c)
                      [{| bcontext := bcontext br0; bbody := pf_plain fuel d (subst10 (tVar "kqproof"%bs) (bbody b0)) |};
                       {| bcontext := bcontext br1; bbody := pf_plain fuel d (subst10 (tVar "kqproof"%bs) (bbody b1)) |}]
            | _ => t
            end
          else tCase ci p (tApp (tConst k []) [pf_plain fuel d c]) [{| bcontext := bcontext b0; bbody := pf_plain fuel (d + length (bcontext b0)) (bbody b0) |};
                                                                     {| bcontext := bcontext b1; bbody := pf_plain fuel (d + length (bcontext b1)) (bbody b1) |}]
      | tLetIn na b ty body =>
          if pf_prog_let na then pf_plain fuel d (subst10 b body)
          else tLetIn na (pf_plain fuel d b) ty (pf_plain fuel (S d) body)
      | tLambda na ty b => tLambda na ty (pf_plain fuel (S d) b)
      | tCase ci p c brs =>
          tCase ci p (pf_plain fuel d c) (map (fun br => {| bcontext := bcontext br; bbody := pf_plain fuel (d + length (bcontext br)) (bbody br) |}) brs)
      | _ => t
      end
  end.
(** the recursive calls, by what [mk] makes of them at the depth they stand at *)
Fixpoint pf_calls (fuel : nat) (mk : nat -> list term -> term) (d : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tApp (tVar v) args =>
          if String.eqb v "kqself"%bs then mk d (map (pf_calls fuel mk d) args) else t
      | tApp f args => tApp (pf_calls fuel mk d f) (map (pf_calls fuel mk d) args)
      | tLetIn na b ty body => tLetIn na (pf_calls fuel mk d b) ty (pf_calls fuel mk (S d) body)
      | tLambda na ty b => tLambda na ty (pf_calls fuel mk (S d) b)
      | tCase ci p c brs =>
          tCase ci p (pf_calls fuel mk d c) (map (fun br => {| bcontext := bcontext br; bbody := pf_calls fuel mk (d + length (bcontext br)) (bbody br) |}) brs)
      | _ => t
      end
  end.
(** a value of a type: what a recursive call at budget 0 stands for; it never runs, a call there being below no measure *)
Fixpoint pf_zero (fuel : nat) (Σ : global_env) (T lastm : term) : term :=
  match fuel with
  | O => unread_t
  | S fuel =>
      if is_ty kn_int T then tInt (Uint63.of_Z 0) else if is_bool T then tConstruct ind_bool 1 [] else if is_nat T then tConstruct ind_nat 0 []
      else if is_ty kn_mem T then lastm
      else
        let ind_ps := match T with tInd i _ => Some (i, []) | tApp (tInd i _) ps => Some (i, ps) | _ => None end in
        match ind_ps with
        | Some (i, ps) =>
            let c := tConstruct i 0 [] in
            let ft := fold_left (fun t p => match t with tProd _ _ b => subst10 p b | _ => t end) ps (head_ty Σ c) in
            let l := ps ++ map (fun ty => pf_zero fuel Σ ty lastm) (removelast (prod_tys ft)) in
            match l with [] => c | _ => tApp c l end
        | None => unread_t
        end
  end.
(** a measure the budget stands above whatever the arguments: [Z.to_nat (Sint63.to_Z e)], through definitions of the program *)
Fixpoint pf_machine (fuel : nat) (Σ : global_env) (m : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match m with
      | tApp (tConst k _) [tApp (tConst z _) [_]] =>
          if Kername.eqb k kn_z_to_nat then Kername.eqb z kn_s_to_z
          else match body_of Σ k with Some b => pf_machine fuel Σ (snd (lams b)) | None => false end
      | tApp (tConst k _) _ => match body_of Σ k with Some b => pf_machine fuel Σ (snd (lams b)) | None => false end
      | _ => false
      end
  end.
(** a measure that is a counter expression: a counter parameter, [S], a sum, [kq_nat] *)
Fixpoint pf_counter (fuel : nat) (m : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match m with
      | tRel _ => true
      | tApp (tConst k _) [a; b] => if Kername.eqb k kn_nat_add then (if pf_counter fuel a then pf_counter fuel b else false) else false
      | tApp (tConst k _) _ => Kername.eqb k kn_kq_nat
      | tConstruct _ 0 _ => true
      | tApp (tConstruct _ 1 _) [c] => pf_counter fuel c
      | _ => false
      end
  end.
Definition pf_budget : term :=
  let b60 := tApp (tConst kn_kq_nat []) [tInt (Uint63.of_Z 1152921504606846976)] in
  let b61 := tApp (tConst kn_kq_nat []) [tInt (Uint63.of_Z 1152921504606846975)] in
  tApp (tConst kn_nat_add []) [b60; tApp (tConst kn_nat_add []) [b60; tApp (tConst kn_nat_add []) [b60; b61]]].
Definition pf_case_nat := <% fun n : nat => match n with O => O | S m => m end %>.
(** a bound of a measure (step 58): the measure with the program's definitions written out; a bound of a number of [Z] from the machine numbers in it; of a [nat], a number or a counter expression.  Nothing here is trusted: [KQRWf.bound_le] proves it *)
Definition kn_u_to_z := kn_of <% Uint63.to_Z %>.
Definition kn_z_add := kn_of <% Z.add %>.
Definition kn_z_sub := kn_of <% Z.sub %>.
Definition kn_z_mul := kn_of <% Z.mul %>.
Definition kn_z_div := kn_of <% Z.div %>.
Definition kn_z_mod := kn_of <% Z.modulo %>.
Definition kn_z_min := kn_of <% Z.min %>.
Definition kn_z_max := kn_of <% Z.max %>.
Definition kn_n_sub := kn_of <% Nat.sub %>.
Definition kn_n_mul := kn_of <% Nat.mul %>.
Definition kn_n_div := kn_of <% Nat.div %>.
Definition kn_n_mod := kn_of <% Nat.modulo %>.
Definition kn_n_min := kn_of <% Nat.min %>.
Definition kn_n_max := kn_of <% Nat.max %>.
Definition kn_n_log2 := kn_of <% Nat.log2 %>.
Definition kn_n_sqrt := kn_of <% Nat.sqrt %>.
Definition kn_n_div2 := kn_of <% Nat.div2 %>.
Fixpoint pf_beta (b : term) (args : list term) : term :=
  match b, args with
  | tLambda _ _ c, a :: r => pf_beta (subst10 a c) r
  | _, [] => b
  | _, _ => mkApps b args
  end.
Fixpoint pf_unf (fuel : nat) (Σ : global_env) (mp : modpath) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tApp (tConst k u) args =>
          let args' := map (pf_unf fuel Σ mp) args in
          if in_prog mp (fst k) then
            match body_of Σ k with
            | Some b => pf_unf fuel Σ mp (pf_beta b args')
            | None => tApp (tConst k u) args'
            end
          else tApp (tConst k u) args'
      | tApp (tLambda _ _ _ as f) args => pf_unf fuel Σ mp (pf_beta f args)
      | tApp f args => tApp f (map (pf_unf fuel Σ mp) args)
      | tConst k _ =>
          if in_prog mp (fst k) then
            match body_of Σ k with Some b => pf_unf fuel Σ mp b | None => t end
          else t
      | _ => t
      end
  end.
Fixpoint pos_val (fuel : nat) (t : term) {struct fuel} : option Z :=
  match fuel with
  | O => None
  | S fuel =>
      match t with
      | tConstruct _ 2 _ => Some 1%Z
      | tApp (tConstruct _ 0 _) [p] => option_map (fun v => (2 * v + 1)%Z) (pos_val fuel p)
      | tApp (tConstruct _ 1 _) [p] => option_map (fun v => (2 * v)%Z) (pos_val fuel p)
      | _ => None
      end
  end.
Definition z_val (t : term) : option Z :=
  match t with
  | tConstruct _ 0 _ => Some 0%Z
  | tApp (tConstruct _ 1 _) [p] => pos_val 100 p
  | tApp (tConstruct _ 2 _) [p] => option_map Z.opp (pos_val 100 p)
  | _ => None
  end.
Fixpoint zb (fuel : nat) (t : term) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel =>
      match z_val t with
      | Some v => Some (v, v)
      | None =>
          match t with
          | tApp (tConst k _) [_] =>
              if Kername.eqb k kn_s_to_z then Some ((-4611686018427387904)%Z, 4611686018427387903%Z)
              else if Kername.eqb k kn_u_to_z then Some (0%Z, 9223372036854775807%Z)
              else None
          | tApp (tConst k _) [a; b] =>
              match zb fuel a, zb fuel b with
              | Some (al, ah), Some (bl, bh) =>
                  if Kername.eqb k kn_z_add then Some ((al + bl)%Z, (ah + bh)%Z)
                  else if Kername.eqb k kn_z_sub then Some ((al - bh)%Z, (ah - bl)%Z)
                  else if Kername.eqb k kn_z_min then Some (Z.min al bl, Z.min ah bh)
                  else if Kername.eqb k kn_z_max then Some (Z.max al bl, Z.max ah bh)
                  else if Kername.eqb k kn_z_mul then
                    if Z.eqb bl bh then
                      if Z.leb 0 bl then Some ((al * bl)%Z, (ah * bl)%Z) else Some ((ah * bl)%Z, (al * bl)%Z)
                    else if Z.eqb al ah then
                      if Z.leb 0 al then Some ((al * bl)%Z, (al * bh)%Z) else Some ((al * bh)%Z, (al * bl)%Z)
                    else None
                  else if Kername.eqb k kn_z_div then
                    if Z.eqb bl bh then if Z.ltb 0 bl then Some ((al / bl)%Z, (ah / bl)%Z) else None else None
                  else if Kername.eqb k kn_z_mod then
                    if Z.eqb bl bh then if Z.ltb 0 bl then Some (0%Z, (bl - 1)%Z) else None else None
                  else None
              | _, _ => None
              end
          | _ => None
          end
      end
  end.
Inductive mbound := MNum (z : Z) | MCnt (t : term).
Fixpoint s_times (n : nat) (t : term) : term :=
  match n with O => t | S n' => tApp (tConstruct ind_nat 1 []) [s_times n' t] end.
Definition mb_add (a b : mbound) : option mbound :=
  match a, b with
  | MNum x, MNum y => Some (MNum (x + y))
  | MCnt t, MCnt u => Some (MCnt (tApp (tConst kn_nat_add []) [t; u]))
  | MCnt t, MNum z | MNum z, MCnt t => if Z.leb z 8 then Some (MCnt (s_times (Z.to_nat z) t)) else None
  end.
Fixpoint nb (fuel : nat) (t : term) {struct fuel} : option mbound :=
  match fuel with
  | O => None
  | S fuel =>
      match t with
      | tRel _ => Some (MCnt t)
      | tConstruct _ 0 _ => Some (MNum 0%Z)
      | tApp (tConstruct _ 1 _) [c] => match nb fuel c with Some u => mb_add u (MNum 1%Z) | None => None end
      | tApp (tConst k _) [a] =>
          if Kername.eqb k kn_z_to_nat then
            match zb 100 a with Some (_, h) => Some (MNum (Z.max 0 h)) | None => None end
          else if Kername.eqb k kn_kq_nat then Some (MCnt t)
          else if Kername.eqb k kn_nat_pred then nb fuel a
          else if Kername.eqb k kn_n_log2 then nb fuel a
          else if Kername.eqb k kn_n_sqrt then nb fuel a
          else if Kername.eqb k kn_n_div2 then nb fuel a
          else None
      | tApp (tConst k _) [a; b] =>
          if Kername.eqb k kn_nat_add then
            match nb fuel a, nb fuel b with
            | Some x, Some y => mb_add x y
            | _, _ => None
            end
          else if Kername.eqb k kn_n_sub then nb fuel a
          else if Kername.eqb k kn_n_div then nb fuel a
          else if Kername.eqb k kn_n_mod then nb fuel a
          else if Kername.eqb k kn_n_min then
            match nb fuel a, nb fuel b with
            | Some (MNum x), Some (MNum y) => Some (MNum (Z.min x y))
            | Some (MNum x), _ => Some (MNum x)
            | _, Some (MNum y) => Some (MNum y)
            | Some x, _ => Some x
            | _, Some y => Some y
            | _, _ => None
            end
          else if Kername.eqb k kn_n_max then
            match nb fuel a, nb fuel b with
            | Some (MNum x), Some (MNum y) => Some (MNum (Z.max x y))
            | Some x, Some y => mb_add x y
            | _, _ => None
            end
          else if Kername.eqb k kn_n_mul then
            match nb fuel a, nb fuel b with
            | Some (MNum x), Some (MNum y) => Some (MNum (x * y))
            | _, _ => None
            end
          else None
      | _ => None
      end
  end.
(** what the proof of the bound takes: "m" a machine number, "c" the measure itself, "l" arithmetic; how many phases; the budget of the last; the measure written out *)
Definition pf_bound (Σ : global_env) (mp : modpath) (M : term) : option (string * nat * term * term) :=
  if pf_machine 10 Σ M then Some ("m"%bs, 1, pf_budget, M)
  else if pf_counter 10 M then Some ("c"%bs, 1, M, M)
  else
    let M' := pf_unf 100 Σ mp M in
    match nb 200 M' with
    | Some (MNum z) =>
        let ph := Z.to_nat ((z + 4611686018427387904) / 4611686018427387904) in
        if Nat.leb ph 8 then Some ("l"%bs, Nat.max 1 ph, pf_budget, M') else None
    | Some (MCnt u) => Some ("l"%bs, 1, u, M')
    | None => None
    end.
(** what is made of a measure recursion: the budget functions, a phase each, and their type; the function one call of the last; the default of a call at budget 0; the result's type; the measure as a function and written out; the bound's proof and the phases *)
Record pfg := { pg_gs : list (kername * term); pg_gty : term; pg_w : term; pg_d : term; pg_t : term; pg_m : term; pg_n : term; pg_tag : string; pg_ph : nat; pg_sp : string; pg_cs : string }.
Definition pg_name (kn : kername) (i : nat) : kername :=
  (copy_mp, mangle kn ^ match i with O => ""%bs | S _ => "_"%bs ^ string_of_nat i end ^ "__wg"%bs).
(** the budget function, the function one call of it, the default of a call at budget 0, the measure as a function: [plain] with [sg base] for its free variables *)
Definition pf_gen (Σ : global_env) (kn : kername) (tys : list term) (T M plain : term) (sg : nat -> list term) (sp cs : string) : option pfg :=
  match pf_case_nat with
  | tLambda _ _ (tCase ci pr _ [br0; br1]) =>
      let n := length tys in
      let lastm (d : nat) (args : list term) := last args (tRel 0) in
      let b1 := pf_calls 100000 (fun d args => tApp (tRel (d + n + 2)) (tRel d :: args)) 0 (subst (sg 1) 0 plain) in
      let gty := tProd anon_b (tInd ind_nat []) (pis_of tys T) in
      let mkg (i : nat) : kername * term :=
        let b_0 := pf_calls 100000 (fun d args => match i with
                                                  | O => pf_zero 100 Σ T (lastm d args)
                                                  | S i' => tApp (tConst (pg_name kn i') []) (pf_budget :: args)
                                                  end) 0 (subst (sg 0) 0 plain) in
        let gk := pg_name kn i in
        let cs := tCase ci {| pparams := pparams pr; puinst := puinst pr; pcontext := pcontext pr; preturn := lift0 1 T |} (tRel n)
                    [{| bcontext := bcontext br0; bbody := b_0 |}; {| bcontext := bcontext br1; bbody := b1 |}] in
        (gk, tFix [{| dname := {| binder_name := nNamed (snd gk); binder_relevance := Relevant |}; dtype := gty;
                      dbody := tLambda anon_b (tInd ind_nat []) (lams_of tys cs); rarg := 0 |}] 0) in
      let rels := map (fun i => tRel (n - 1 - i)) (seq 0 n) in
      match pf_bound Σ (fst kn) M with
      | Some (tag, ph, bud, Mn) =>
          Some {| pg_gs := map mkg (seq 0 ph); pg_gty := gty;
                  pg_w := lams_of tys (tApp (tConst (pg_name kn (Nat.pred ph)) []) (bud :: rels));
                  pg_d := lams_of tys (pf_zero 100 Σ T (tRel 0)); pg_t := T; pg_m := lams_of tys M; pg_n := lams_of tys Mn;
                  pg_tag := tag; pg_ph := ph; pg_sp := sp; pg_cs := cs |}
      | None => None
      end
  | _ => None
  end.
(** for a [Program Fixpoint] of [n] parameters *)
Definition pf_make_p (Σ : global_env) (kn : kername) : option pfg :=
  match pf_parts Σ kn with
  | Some (tys, T, tLambda _ _ m0, tLambda _ _ (tLambda _ _ b0), _) =>
      let n := length tys in
      let fix peel (k : nat) (t : term) {struct k} : option term :=
        match k, t with
        | O, _ => Some t
        | S k', tLetIn _ _ _ body => peel k' body
        | _, _ => None
        end in
      match peel n m0, peel (S n) b0 with
      | Some M, Some body =>
          pf_gen Σ kn tys T M (pf_plain 100000 0 body)
                 (fun base => tVar "kqf"%bs :: map (fun i => tRel (base + i)) (seq 0 n) ++ [tVar "kqr"%bs; tVar "kqr"%bs])
                 "p"%bs ""%bs
      | _, _ => None
      end
  | _ => None
  end.
(** [Function] (step 57): the function is [fun ps => let (a, _) := f_terminate ps in a], [f_F] its functional, plain, and [f_tcc] states the measure's fall *)
Fixpoint fn_self (fuel self d : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tApp (tRel i) args =>
          if Nat.eqb i (d + self) then tApp (tVar "kqself"%bs) (map (fn_self fuel self d) args)
          else tApp (tRel i) (map (fn_self fuel self d) args)
      | tApp f args => tApp (fn_self fuel self d f) (map (fn_self fuel self d) args)
      | tLetIn na b ty body => tLetIn na (fn_self fuel self d b) ty (fn_self fuel self (S d) body)
      | tLambda na ty b => tLambda na ty (fn_self fuel self (S d) b)
      | tCase ci p c brs =>
          tCase ci p (fn_self fuel self d c) (map (fun br => {| bcontext := bcontext br; bbody := fn_self fuel self (d + length (bcontext br)) (bbody br) |}) brs)
      | _ => t
      end
  end.
(** the measure, in the function's parameters: the right of the first [<] [f_tcc] states; where a pattern's equation [x = C ..] has put the pattern in place of the parameter, the parameter again *)
Fixpoint tm_replace (fuel d : nat) (a b t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      if teq 100 (lift0 d a) t then lift0 d b else
      match t with
      | tApp f args => tApp (tm_replace fuel d a b f) (map (tm_replace fuel d a b) args)
      | tLambda na ty c => tLambda na ty (tm_replace fuel (S d) a b c)
      | tLetIn na v ty c => tLetIn na (tm_replace fuel d a b v) ty (tm_replace fuel (S d) a b c)
      | tCase ci p c brs =>
          tCase ci p (tm_replace fuel d a b c) (map (fun br => {| bcontext := bcontext br; bbody := tm_replace fuel (d + length (bcontext br)) a b (bbody br) |}) brs)
      | tProj p c => tProj p (tm_replace fuel d a b c)
      | _ => t
      end
  end.
Fixpoint tm_has_var (fuel : nat) (x : string) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => true
  | S fuel =>
      match t with
      | tVar y => String.eqb x y
      | tApp f args => if tm_has_var fuel x f then true else existsb (tm_has_var fuel x) args
      | tLambda _ _ c => tm_has_var fuel x c
      | tLetIn _ v _ c => if tm_has_var fuel x v then true else tm_has_var fuel x c
      | tCase _ _ c brs => if tm_has_var fuel x c then true else existsb (fun br => tm_has_var fuel x (bbody br)) brs
      | tProj _ c => tm_has_var fuel x c
      | _ => false
      end
  end.
Definition fn_pattern (A : term) : option (term * term) :=
  match A with
  | tApp (tInd i _) [_; tRel p; r] =>
      if String.eqb (snd (inductive_mind i)) "eq"%bs then
        match r with
        | tConstruct _ _ _ | tApp (tConstruct _ _ _) _ => Some (tRel p, r)
        | _ => None
        end
      else None
  | _ => None
  end.
Fixpoint fn_measure (fuel n depth : nat) (eqs : list (term * term)) (t : term) {struct fuel} : option term :=
  match fuel with
  | O => None
  | S fuel =>
      match t with
      | tProd _ A b =>
          let eqs' := match fn_pattern A with Some e => e :: eqs | None => eqs end in
          fn_measure fuel n (S depth) (map (fun e => (lift0 1 (fst e), lift0 1 (snd e))) eqs') b
      | tLetIn _ _ _ b => fn_measure fuel n (S depth) (map (fun e => (lift0 1 (fst e), lift0 1 (snd e))) eqs) b
      | tApp (tInd _ _) [a; _] => fn_measure fuel n depth eqs a
      | tApp (tConst _ _) [_; m] =>
          let m1 := fold_left (fun m e => tm_replace 200 0 (snd e) (fst e) m) eqs m in
          let m' := subst (repeat (tVar "kqc"%bs) (depth - n)) 0 m1 in
          if tm_has_var 200 "kqc"%bs m' then None
          else Some (match m' with tApp (tLambda _ _ b) [a] => subst10 a b | _ => m' end)
      | _ => None
      end
  end.
Fixpoint fn_lams (k : nat) (t : term) : option term :=
  match k, t with
  | O, _ => Some t
  | S k', tLambda _ _ b => fn_lams k' b
  | _, _ => None
  end.
Definition fn_make (Σ : global_env) (kn : kername) : option pfg :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some b =>
          let '(tys, r) := lams b in
          match r with
          | tCase _ _ (tApp (tConst tk _) _) [_] =>
              if String.eqb (snd tk) (snd kn ^ "_terminate"%bs) then
                match body_of Σ (fst kn, snd kn ^ "_F"%bs), lookup_env Σ (fst kn, snd kn ^ "_tcc"%bs) with
                | Some f0, Some (ConstantDecl tc) =>
                    let n := length tys in
                    match fn_lams (S n) f0, fn_measure 1000 n 0 [] (cst_type tc) with
                    | Some body, Some M =>
                        pf_gen Σ kn tys (ret_ty (cst_type cb)) M (fn_self 100000 n 0 body)
                               (fun base => map (fun i => tRel (base + i)) (seq 0 n) ++ [tVar "kqf"%bs])
                               "f"%bs ""%bs
                    | _, _ => None
                    end
                | _, _ => None
                end
              else None
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.
(** [Equations] (step 60): [f := fun ps => FixWf P (fun x H => f_functional .. (fun .. => H ..)) ..], [f_functional] with the function last among its parameters and the proof last among a call's arguments, its tests in clause constants: written out into a body with no proof, as [Program]'s and [Function]'s *)
Definition kn_fixwf : kername := (MPfile ["Subterm"%bs; "Prop"%bs; "Equations"%bs], "FixWf"%bs).
Definition kn_nat_lt := kn_of <% lt %>.
Fixpoint tm_has_rel (fuel d : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => true
  | S fuel =>
      match t with
      | tRel i => Nat.eqb i d
      | tApp f args => if tm_has_rel fuel d f then true else existsb (tm_has_rel fuel d) args
      | tLambda _ _ c => tm_has_rel fuel (S d) c
      | tLetIn _ v _ c => if tm_has_rel fuel d v then true else tm_has_rel fuel (S d) c
      | tCase _ _ c brs => if tm_has_rel fuel d c then true else existsb (fun br => tm_has_rel fuel (d + length (bcontext br)) (bbody br)) brs
      | _ => false
      end
  end.
Fixpoint eq_strip (n : nat) (pr : term) : term :=
  match n, pr with
  | S n', tProd _ _ r => eq_strip n' (subst10 (tVar "kqproof"%bs) r)
  | _, _ => pr
  end.
(** the scrutinee: a program's definition giving a constructor at once, [inspect] *)
Definition eq_scrut (Σ : global_env) (mp : modpath) (c : term) : term :=
  match c with
  | tApp (tConst k _) args =>
      if in_prog mp (fst k) then
        match body_of Σ k with
        | Some b => match pf_beta b args with (tApp (tConstruct _ _ _) _) as v => v | _ => c end
        | None => c
        end
      else c
  | _ => c
  end.
Fixpoint eq_norm (fuel : nat) (Σ : global_env) (mp : modpath) (d : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tApp (tApp f a) b => eq_norm fuel Σ mp d (tApp f (a ++ b))
      | tApp (tLambda _ _ _ as f) args => eq_norm fuel Σ mp d (pf_beta f args)
      | tApp (tRel i) args =>
          if Nat.eqb i d then tApp (tVar "kqself"%bs) (map (eq_norm fuel Σ mp d) (removelast args))
          else tApp (tRel i) (map (eq_norm fuel Σ mp d) args)
      | tApp (tCase ci p c brs) args =>
          eq_norm fuel Σ mp d
            (tCase ci {| pparams := pparams p; puinst := puinst p; pcontext := pcontext p; preturn := eq_strip (length args) (preturn p) |} c
                   (map (fun br => {| bcontext := bcontext br;
                                      bbody := pf_beta (bbody br) (map (lift0 (length (bcontext br))) args) |}) brs))
      | tApp (tConst k u) args =>
          if in_prog mp (fst k) && existsb (tm_has_rel 1000 d) args then
            match body_of Σ k with
            | Some b => eq_norm fuel Σ mp d (pf_beta b args)
            | None => t
            end
          else tApp (tConst k u) (map (eq_norm fuel Σ mp d) args)
      | tApp f args => tApp f (map (eq_norm fuel Σ mp d) args)
      | tCase ci p c brs =>
          match eq_scrut Σ mp c with
          | tApp (tConstruct _ i _) cargs =>
              match nth_error brs i with
              | Some br => eq_norm fuel Σ mp d (subst (rev (skipn (ci_npar ci) cargs)) 0 (bbody br))
              | None => t
              end
          | c' =>
              tCase ci p (eq_norm fuel Σ mp d c')
                    (map (fun br => {| bcontext := bcontext br; bbody := eq_norm fuel Σ mp (d + length (bcontext br)) (bbody br) |}) brs)
          end
      | tLambda na ty b => tLambda na ty (eq_norm fuel Σ mp (S d) b)
      | tLetIn na b ty body => tLetIn na (eq_norm fuel Σ mp d b) ty (eq_norm fuel Σ mp (S d) body)
      | _ => t
      end
  end.
(** the clause constants, each once, for [kitc.py] to unfold: the program's definitions in the body with a function among their parameters *)
Fixpoint eq_clauses (fuel : nat) (Σ : global_env) (mp : modpath) (t : term) (acc : list kername) {struct fuel} : list kername :=
  match fuel with
  | O => acc
  | S fuel =>
      match t with
      | tConst k _ =>
          if in_prog mp (fst k) then
            if existsb (Kername.eqb k) acc then acc else
            match body_of Σ k with
            | Some b =>
                let '(tys, bd) := lams b in
                if existsb is_prod tys then eq_clauses fuel Σ mp bd (k :: acc) else acc
            | None => acc
            end
          else acc
      | tApp f args => fold_left (fun a x => eq_clauses fuel Σ mp x a) args (eq_clauses fuel Σ mp f acc)
      | tLambda _ _ b => eq_clauses fuel Σ mp b acc
      | tLetIn _ v _ c => eq_clauses fuel Σ mp c (eq_clauses fuel Σ mp v acc)
      | tCase _ _ c brs => fold_left (fun a br => eq_clauses fuel Σ mp (bbody br) a) brs (eq_clauses fuel Σ mp c acc)
      | _ => acc
      end
  end.
Definition eq_make (Σ : global_env) (kn : kername) : option pfg :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some b =>
          match snd (lams b) with
          | tApp (tConst fw _) (_ :: _ :: tApp (tConst _ _) [_; _; mf; tConst rl _; _] :: _ :: tLambda _ _ (tLambda _ _ (tApp (tConst fk _) _)) :: _) =>
              if Kername.eqb fw kn_fixwf && Kername.eqb rl kn_nat_lt then
                let tys := removelast (prod_tys (cst_type cb)) in
                let n := length tys in
                match body_of Σ fk, fn_lams n mf with
                | Some fb, Some M =>
                    match fn_lams (S n) fb with
                    | Some body =>
                        let mp := fst kn in
                        let plain := pf_plain 100000 1000000 (eq_norm 100000 Σ mp 0 body) in
                        let cs := fk :: eq_clauses 100000 Σ mp body [] in
                        pf_gen Σ kn tys (ret_ty (cst_type cb)) M plain
                               (fun base => tVar "kqf"%bs :: map (fun i => tRel (base + i)) (seq 0 n))
                               "e"%bs (fold_right (fun k a => string_of_kername k ^ " "%bs ^ a) ""%bs cs)
                    | None => None
                    end
                | _, _ => None
                end
              else None
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.
(** (step 61) a fixpoint with its own call on a counter deeper than the predecessor (the two-step [match n with S (S q) => f q ..]): [FRec] has the function at the predecessor only.  A budget function above it: the counter its own parameter, the budget the counter's value *)
Fixpoint deep_call (fuel self m : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tApp (tRel i) args =>
          if Nat.eqb i self then
            match args with
            | tRel j :: _ => if Nat.eqb j m then existsb (deep_call fuel self m) args else true
            | _ => true
            end
          else existsb (deep_call fuel self m) args
      | tApp f args => if deep_call fuel self m f then true else existsb (deep_call fuel self m) args
      | tLambda _ _ c => deep_call fuel (S self) (S m) c
      | tLetIn _ v _ c => if deep_call fuel self m v then true else deep_call fuel (S self) (S m) c
      | tCase _ _ c brs =>
          if deep_call fuel self m c then true
          else existsb (fun br => let k := length (bcontext br) in deep_call fuel (self + k) (m + k) (bbody br)) brs
      | _ => false
      end
  end.
Definition deep_body (b : term) : option (def term) :=
  match b with
  | tFix [d] 0 =>
      if Nat.eqb (rarg d) 0 then
        let '(tys, body) := lams (dbody d) in
        match tys, body with
        | _ :: _, tCase cid _ (tRel c) [_; b1] =>
            let n := length tys in
            if Nat.eqb c (n - 1) && Kername.eqb (inductive_mind (ci_ind cid)) (inductive_mind ind_nat) then
              if deep_call 3000 (n + length (bcontext b1)) 0 (bbody b1) then Some d else None
            else None
        | _, _ => None
        end
      else None
  | _ => None
  end.
Definition deep_make (Σ : global_env) (kn : kername) : option pfg :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_body cb with
      | Some b =>
          match deep_body b with
          | Some d =>
              let '(tys, body) := lams (dbody d) in
              let n := length tys in
              pf_gen Σ kn tys (ret_ty (dtype d)) (tRel (n - 1)) (fn_self 100000 n 0 body)
                     (fun base => map (fun i => tRel (base + i)) (seq 0 n) ++ [tVar "kqf"%bs])
                     "d"%bs ""%bs
          | None => None
          end
      | None => None
      end
  | _ => None
  end.
Definition conv_def (Σ : global_env) (mp : modpath) (d : def term) : option (def term) :=
  let '(tys, body0) := lams (dbody d) in
  let body := body0 in
  let dT := al_t 1000 Σ mp (dtype d) in
  let extra := skipn (length tys) (removelast (prod_tys dT)) in
  let k := length extra in
  let n := length tys in
  let rels := map (fun i => tRel (k - 1 - i)) (seq 0 k) in
  let mk (ci : case_info) (p : predicate term) (c : nat) (brs : list (branch term)) (args : list term) :=
      if Nat.eqb c (n + k - 1 - rarg d) then
        Some {| dname := dname d; dtype := dT; rarg := rarg d;
                dbody := lams_of (tys ++ extra)
                  (tCase ci {| pparams := pparams p; puinst := puinst p; pcontext := pcontext p; preturn := al_t 1000 Σ mp (eq_strip (length args) (preturn p)) |} (tRel c)
                         (map (fun br => {| bcontext := bcontext br; bbody := pf_beta (bbody br) (map (lift0 (length (bcontext br))) args) |}) brs)) |}
      else None in
  match lift0 k body with
  | tApp (tCase ci p (tRel c) brs) args => mk ci p c brs (args ++ rels)
  | tCase ci p (tRel c) brs => match k with O => None | S _ => mk ci p c brs rels end
  | _ => None
  end.
(** (step 62) a mutual block whose members give back different types, one member [h] the only one the others call and none of them calling itself: [FRec] and a block's one result cannot hold them, and they do not need to.  The others written out in [h] (its own call then on deeper counters, a budget function as for those, a test on the call floated out), the others then ordinary functions calling [h] *)
Definition mix_unf (Σ : global_env) (mp : modpath) (d : def term) : def term :=
  let '(tys, body) := lams (dbody d) in
  let d1 := match body with
            | tApp (tConst fk _) args =>
                if in_prog mp (fst fk) then
                  match body_of Σ fk with
                  | Some fb => {| dname := dname d; dtype := dtype d; rarg := rarg d; dbody := lams_of tys (pf_beta fb args) |}
                  | None => d
                  end
                else d
            | _ => d
            end in
  match conv_def Σ mp d1 with Some e => e | None => d1 end.
Definition mix_direct (Σ : global_env) (mp : modpath) (d : def term) : bool :=
  match conv_def Σ mp d, snd (lams (dbody d)) with
  | None, tCase _ _ (tRel _) [_; _] => true
  | _, _ => false
  end.
Definition mix_hub (Σ : global_env) (mp : modpath) (mfix0 : mfixpoint term) (k : nat) : option nat :=
  let mfix := map (mix_unf Σ mp) mfix0 in
  let L := length mfix in
  let g := map (mcalls L) mfix in
  if (if Nat.ltb L 2 then false else if mixed_part mfix k then true else negb (forallb (mix_direct Σ mp) mfix0)) then
    if Nat.eqb (length (part_of g L k)) L then
      if forallb (fun d => Nat.eqb (rarg d) 0) mfix then
        List.find (fun h => forallb (fun j => if Nat.eqb j h then true else forallb (Nat.eqb h) (nth j g [])) (seq 0 L)) (seq 0 L)
      else None
    else None
  else None.
Definition mix_make (Σ : global_env) (kn : kername) : option pfg :=
  match body_of Σ kn with
  | Some (tFix mfix0 k) =>
      match mix_hub Σ (fst kn) mfix0 k with
      | Some h =>
          let mp := fst kn in
          let mfix := map (mix_unf Σ mp) mfix0 in
          let L := length mfix in
          let d := nth k mfix dflt_def in
          let rels (f : nat -> term) := map f (rev (seq 0 L)) in
          let self := tVar "kqself"%bs in
          let t :=
            if Nat.eqb k h then
              subst (rels (fun q => if Nat.eqb q h then self
                                    else subst (rels (fun q2 => if Nat.eqb q2 h then self else tVar "kqnone"%bs)) 0 (dbody (nth q mfix dflt_def))))
                    0 (dbody (nth h mfix dflt_def))
            else subst (rels (fun q => if Nat.eqb q h then tConst (mem_kn mp mfix h) [] else tVar "kqnone"%bs)) 0 (dbody d) in
          let '(tys, body) := lams t in
          let n := length tys in
          let cs := fold_right (fun q a => string_of_kername (mem_kn mp mfix q) ^ " "%bs ^ a) ""%bs (seq 0 L) in
          (* the functional of each, Equations' spelling *)
          let cs := fold_right (fun d0 a =>
                      match snd (lams (dbody d0)) with
                      | tApp (tConst fk _) _ => if in_prog mp (fst fk) then string_of_kername fk ^ " "%bs ^ a else a
                      | _ => a
                      end) cs mfix0 in
          pf_gen Σ kn tys (ret_ty (dtype d)) (tRel (n - 1)) (eq_norm 100000 Σ mp 1000000 body)
                 (fun base => map (fun i => tRel (base + i)) (seq 0 n)) "d"%bs cs
      | None => None
      end
  | _ => None
  end.
Definition mix_kns (Σ : global_env) (mp : modpath) : list kername :=
  flat_map (fun e => if in_prog mp (fst (fst e)) then
                       match snd e with
                       | ConstantDecl cb => match cst_body cb with
                                            | Some (tFix mfix k) => match mix_hub Σ mp mfix k with Some _ => [fst e] | None => [] end
                                            | _ => []
                                            end
                       | _ => []
                       end
                     else []) (declarations Σ).
Definition deep_kns (Σ : global_env) (mp : modpath) : list kername :=
  flat_map (fun e => if in_prog mp (fst (fst e)) then
                       match snd e with
                       | ConstantDecl cb => match cst_body cb with
                                            | Some b => match deep_body b with Some _ => [fst e] | None => [] end
                                            | None => []
                                            end
                       | _ => []
                       end
                     else []) (declarations Σ).
Definition pf_make (Σ : global_env) (kn : kername) : option pfg :=
  match pf_make_p Σ kn with
  | Some r => Some r
  | None =>
      match fn_make Σ kn with
      | Some r => Some r
      | None => match eq_make Σ kn with
                | Some r => Some r
                | None => match deep_make Σ kn with Some r => Some r | None => mix_make Σ kn end
                end
      end
  end.
(** whether the program holds a [Function]: Recdef's [iter] is in what it names *)
Definition kn_iter : kername := (MPfile ["Recdef"%bs; "funind"%bs; "Stdlib"%bs], "iter"%bs).
Definition pf_has_iter (Σ : global_env) : bool :=
  match lookup_env Σ kn_iter with Some _ => true | None => match lookup_env Σ kn_fixwf with Some _ => true | None => false end end.
(** the program with each [Program Fixpoint] or [Function] its budget function, and the function one call of it *)
(** (step 61) the function's own call under a choice in an operand: [(if c then f m x else a) + b].  It cannot be bound (it would run when the test is false), nor lifted (it names the fixpoint), and a match on a stuck test does not commute by conversion.  So the choice is floated out, [if c then f m x + b else a + b]: the fixpoint read is that one, equal to the user's at each counter by [KQRWf.own_step], and [callee_ok_eq] as for a measure.  Only for a program not read as it stands, whose C is then not changed *)
Fixpoint y_conb (fuel : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tConstruct _ _ _ | tApp (tConstruct _ _ _) _ => true
      | tCase _ _ _ brs => forallb (fun br => y_conb fuel (bbody br)) brs
      | _ => false
      end
  end.
(** (step 68) a branch that is a function given its arguments, at once: a proof a match's convoy gives it is typed in the branch only if not named *)
Fixpoint y_beta (args : list term) (t : term) {struct args} : term :=
  match args, t with
  | [], _ => t
  | a :: r, tLambda _ _ b => y_beta r (subst10 a b)
  | _, _ => mkApps t args
  end.
Fixpoint y_pull (fuel self : nat) (t : term) {struct fuel} : option (case_info * predicate term * term * list (branch term)) :=
  match fuel with
  | O => None
  | S fuel =>
      match t with
      | tCase ci p c brs =>
          if existsb (fun br => tm_has_rel 1000 (self + length (bcontext br)) (bbody br)) brs then Some (ci, p, c, brs)
          else
            match match c with
                  | tCase ci1 p1 c1 brs1 => if y_conb 100 c then Some (ci1, p1, c1, brs1) else y_pull fuel self c
                  | _ => y_pull fuel self c
                  end with
            | Some (ci', p', c', brs') =>
                Some (ci', p', c', map (fun br' =>
                  let k := length (bcontext br') in
                  {| bcontext := bcontext br';
                     bbody := match lift0 k t with
                              | tCase ci2 p2 _ brs2 => tCase ci2 p2 (bbody br') brs2
                              | u => u
                              end |}) brs')
            | None => None
            end
      | tApp (tCase ci p c brs) args =>
          Some (ci, p, c, map (fun br =>
            let k := length (bcontext br) in
            {| bcontext := bcontext br; bbody := y_beta (map (lift0 k) args) (bbody br) |}) brs)
      | tApp f args =>
          let fix go (pre post : list term) {struct post} :=
            match post with
            | [] => None
            | a :: r =>
                match y_pull fuel self a with
                | Some (ci, p, c, brs) =>
                    Some (ci, p, c, map (fun br =>
                      let k := length (bcontext br) in
                      {| bcontext := bcontext br;
                         bbody := tApp (lift0 k f) (map (lift0 k) (rev pre) ++ bbody br :: map (lift0 k) r) |}) brs)
                | None => go (a :: pre) r
                end
            end in
          go [] args
      | tLetIn na b ty body =>
          match y_pull fuel self b with
          | Some (ci, p, c, brs) =>
              Some (ci, p, c, map (fun br =>
                let k := length (bcontext br) in
                {| bcontext := bcontext br; bbody := tLetIn na (bbody br) (lift0 k ty) (lift k 1 body) |}) brs)
          | None => None
          end
      | _ => None
      end
  end.
Definition y_case_pair := <% fun p : PrimInt63.int * KQ.KQRun.mem => let (a, b) := p in O %>.
Definition y_anon : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
(** (step 72) a part that may be written twice: a variable, a number, a test of a variable against a number *)
Definition y_small (t : term) : bool :=
  match t with
  | tRel _ | tInt _ | tConstruct _ _ _ => true
  | tApp (tConst k _) [tRel _; tInt _] => eq_mp (fst k) prim_mp
  | _ => false
  end.
Fixpoint y_red (fuel : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tApp (tConst k u) [A; B; p] =>
          let p' := y_red fuel p in
          if Kername.eqb k kn_fst then
            match p' with
            | tApp (tConstruct _ 0 _) [_; _; a; _] => a
            | tLetIn na v ty b => tLetIn na v ty (y_red fuel (tApp (tConst k u) [lift0 1 A; lift0 1 B; b]))
            | _ => tApp (tConst k u) [A; B; p']
            end
          else if Kername.eqb k kn_snd then
            match p' with
            | tApp (tConstruct _ 0 _) [_; _; _; b] => b
            | tLetIn na v ty b => tLetIn na v ty (y_red fuel (tApp (tConst k u) [lift0 1 A; lift0 1 B; b]))
            | _ => tApp (tConst k u) [A; B; p']
            end
          else tApp (tConst k u) [A; B; p']
      | tApp f args => tApp (y_red fuel f) (map (y_red fuel) args)
      | tLambda na ty b => tLambda na ty (y_red fuel b)
      | tLetIn na v ty b => tLetIn na (y_red fuel v) ty (y_red fuel b)
      | tCase ci p c brs =>
          let c' := y_red fuel c in
          let dflt := tCase ci p c' (map (fun br => {| bcontext := bcontext br; bbody := y_red fuel (bbody br) |}) brs) in
          match c' with
          | tApp (tConstruct _ k _) cargs =>
              if forallb y_small (skipn (ci_npar ci) cargs) then
                match nth_error brs k with
                | Some br => y_red fuel (subst (rev (skipn (ci_npar ci) cargs)) 0 (bbody br))
                | None => dflt
                end
              else
                (* a pair: what is not small by a let, the number first, as the readers bind them *)
                match cargs, brs with
                | [A; B; x; y], [br] =>
                    if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_prod) then
                      if y_small x then tLetIn y_anon y B (y_red fuel (subst [x] 1 (bbody br)))
                      else if y_small y then tLetIn y_anon x A (y_red fuel (subst [lift0 1 y] 0 (bbody br)))
                      else tLetIn y_anon x A (tLetIn y_anon (lift0 1 y) (lift0 1 B) (y_red fuel (bbody br)))
                    else dflt
                | _, _ => dflt
                end
          | _ => dflt
          end
      | _ => t
      end
  end.
Definition y_ret (p : predicate term) (T : term) : predicate term :=
  {| pparams := pparams p; puinst := puinst p; pcontext := pcontext p; preturn := lift0 (length (pcontext p)) T |}.
Fixpoint y_tail (fuel self : nat) (T t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tCase ci p c brs =>
          match match c with
                | tCase ci1 p1 c1 brs1 => if y_conb 100 c then Some (ci1, p1, c1, brs1) else y_pull fuel self c
                | _ => y_pull fuel self c
                end with
          | Some (ci', p', c', brs') =>
              y_tail fuel self T (tCase ci' (y_ret p' T) c'
                (map (fun br' =>
                   let k := length (bcontext br') in
                   {| bcontext := bcontext br';
                      bbody := match lift0 k t with
                               | tCase ci2 p2 _ brs2 => tCase ci2 p2 (bbody br') brs2
                               | u => u
                               end |}) brs'))
          | None =>
              tCase ci p c (map (fun br =>
                let k := length (bcontext br) in
                {| bcontext := bcontext br; bbody := y_tail fuel (self + k) (lift0 k T) (bbody br) |}) brs)
          end
      | tLetIn na b ty body =>
          match y_pull fuel self b with
          | Some (ci, p, c, brs) =>
              y_tail fuel self T (tCase ci (y_ret p T) c (map (fun br =>
                let k := length (bcontext br) in
                {| bcontext := bcontext br; bbody := tLetIn na (bbody br) (lift0 k ty) (lift k 1 body) |}) brs))
          | None =>
              (* (step 62) a let of a number and a memory, the own call in what follows: taken apart, the pair made where it is used bare *)
              if is_pm ty && tm_has_rel 1000 (S self) body then
                match y_case_pair with
                | tLambda _ _ (tCase ci p _ [br]) =>
                    let pr := tApp (tConstruct {| inductive_mind := inductive_mind (ci_ind ci); inductive_ind := 0 |} 0 [])
                                   [tConst kn_int []; tConst kn_mem []; tRel 1; tRel 0] in
                    y_tail fuel self T (tCase ci (y_ret p T) b
                      [{| bcontext := bcontext br;
                          bbody := y_red 100000 (subst10 pr (lift 2 1 body)) |}])
                | _ => t
                end
              else tLetIn na b ty (y_tail fuel (S self) (lift0 1 T) body)
          end
      | tApp _ _ =>
          match y_pull fuel self t with
          | Some (ci, p, c, brs) => y_tail fuel self T (tCase ci (y_ret p T) c brs)
          | None =>
              let t' := y_red 1000 t in
              if teq 100000 t' t then t else y_tail fuel self T t'
          end
      | _ => t
      end
  end.
Definition y_case_nat := <% fun n : nat => match n with O => O | S m => O end %>.
(** a match on a counter whose constructor is written: its branch, Rocq's own iota: the guard of a fixpoint does not see through it *)
Fixpoint y_rep (fuel c d : nat) (v t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := y_rep fuel c d v in
      match t with
      | tRel i => if Nat.eqb i (c + d) then lift0 d v else t
      | tApp f args => tApp (go f) (map go args)
      | tLambda na a b => tLambda na a (y_rep fuel c (S d) v b)
      | tProd na a b => tProd na a (y_rep fuel c (S d) v b)
      | tLetIn na w a b => tLetIn na (go w) a (y_rep fuel c (S d) v b)
      | tCase ci p x brs =>
          tCase ci p (go x) (map (fun br => {| bcontext := bcontext br; bbody := y_rep fuel c (d + length (bcontext br)) v (bbody br) |}) brs)
      | tFix mfix k =>
          let n := length mfix in
          tFix (map (fun df => {| dname := dname df; dtype := dtype df; rarg := rarg df; dbody := y_rep fuel c (d + n) v (dbody df) |}) mfix) k
      | _ => t
      end
  end.
Fixpoint y_kn (fuel : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tCase ci p (tConstruct i 0 _) [b0; b1] =>
          if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then y_kn fuel (bbody b0)
          else tCase ci p (tConstruct i 0 []) (map (fun br => {| bcontext := bcontext br; bbody := y_kn fuel (bbody br) |}) [b0; b1])
      | tCase ci p (tApp (tConstruct i 1 u) [a] as c) [b0; b1] =>
          if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then y_kn fuel (subst10 a (bbody b1))
          else tCase ci p c (map (fun br => {| bcontext := bcontext br; bbody := y_kn fuel (bbody br) |}) [b0; b1])
      | tCase ci p c brs => tCase ci p (y_kn fuel c) (map (fun br => {| bcontext := bcontext br; bbody := y_kn fuel (bbody br) |}) brs)
      | tApp f args => tApp (y_kn fuel f) (map (y_kn fuel) args)
      | tLambda na a b => tLambda na a (y_kn fuel b)
      | tLetIn na v a b => tLetIn na (y_kn fuel v) a (y_kn fuel b)
      | _ => t
      end
  end.
Definition y_on_nat (d : def term) : bool :=
  match nth_error (fst (lams (dbody d))) (rarg d) with
  | Some (tInd i _) => Kername.eqb (inductive_mind i) (inductive_mind ind_nat)
  | _ => false
  end.
Definition y_fix (d : def term) : option term :=
  let '(tys, body) := lams (dbody d) in
  match body with
  | tCase ci p (tRel c) [b0; b1] =>
      let n := length tys in
      let T := ret_ty (dtype d) in
      if Nat.eqb (rarg d) 0 then
        let b1' := y_tail 1000 (n + length (bcontext b1)) T (bbody b1) in
        if teq 100000 b1' (bbody b1) then None
        else Some (tFix [{| dname := dname d; dtype := dtype d; rarg := rarg d;
                            dbody := lams_of tys (tCase ci p (tRel c) [b0; {| bcontext := bcontext b1; bbody := b1' |}]) |}] 0)
      else None
  | _ =>
      (* (step 68) lets or a test before the counter's match: the whole body in each branch of it, the same at each counter *)
      let n := length tys in
      let c := n - 1 - rarg d in
      match y_case_nat with
      | tLambda _ _ (tCase ci p _ [b0; b1]) =>
          if Nat.eqb (rarg d) 0 then
            Some (tFix [{| dname := dname d; dtype := dtype d; rarg := rarg d;
                           dbody := lams_of tys (tCase ci (y_ret p (ret_ty (dtype d))) (tRel c)
                                      [{| bcontext := bcontext b0; bbody := y_kn 100000 (subst [tConstruct ind_nat 0 []] c (lift 1 (S c) body)) |};
                                       {| bcontext := bcontext b1;
                                          bbody := y_kn 100000 (y_rep 100000 (S c) 0 (tApp (tConstruct ind_nat 1 []) [tRel 0]) (lift0 1 body)) |}]) |}] 0)
          else None
      | _ => None
      end
  end.
(** (step 60) a fixpoint whose match on its counter gives a function (Equations writes its clauses so, and a user may): the application pushed into the branches, read as any fixpoint.  No conversion opens a match on a variable, so it is not [denote s = f]; its two equations, at [O] and [S _], hold by conversion: the theorem a copy takes (kitc.py) *)
Definition conv_fix (Σ : global_env) (mp : modpath) (b : term) : option term :=
  match b with
  (* a block's members are one call of the block: a member so written is a gap, with its cells *)
  | tFix [d] i => match conv_def Σ mp d with Some e => Some (tFix [e] i) | None => None end
  | _ => None
  end.
Definition conv_kns (Σ : global_env) (mp : modpath) : list kername :=
  flat_map (fun e => if in_prog mp (fst (fst e)) then
                       match snd e with
                       | ConstantDecl cb => match cst_body cb with
                                            | Some b => match conv_fix Σ mp b with Some _ => [fst e] | None => [] end
                                            | None => []
                                            end
                       | _ => []
                       end
                     else []) (declarations Σ).
Definition conv_all (Σ : global_env) (mp : modpath) : global_env :=
  match conv_kns Σ mp with
  | [] => Σ
  | ks =>
      fold_left (fun S kn =>
        match lookup_env S kn with
        | Some (ConstantDecl cb) =>
            match cst_body cb with
            | Some b => match conv_fix Σ mp b with Some b' => add_decl S kn (al_t 1000 Σ mp (cst_type cb)) b' | None => S end
            | None => S
            end
        | _ => S
        end) ks Σ
  end.
(** (step 62) the budget function read: the own call under a choice in an operand floated out, as in [y_fix]; the budget function is the reader's own, so no equation for it *)
Definition y_post (g : kername * term) : kername * term :=
  match snd g with
  | tFix [d] 0 => match y_fix d with Some f' => (fst g, f') | None => g end
  | _ => g
  end.
Definition mix_decls (Σ : global_env) (mp : modpath) : global_env :=
  fold_left (fun S e =>
    if in_prog mp (fst (fst e)) then
      match snd e with
      | ConstantDecl cb =>
          match cst_body cb with
          | Some (tFix mfix k) =>
              match mix_hub Σ mp mfix k with
              | Some _ =>
                  fold_left (fun S2 q =>
                    let kq := mem_kn (fst (fst e)) mfix q in
                    match lookup_env S2 kq with
                    | Some _ => S2
                    | None => add_decl S2 kq (dtype (nth q mfix dflt_def)) (tFix mfix q)
                    end) (seq 0 (length mfix)) S
              | None => S
              end
          | _ => S
          end
      | _ => S
      end
    else S) (declarations Σ) Σ.
Definition pf_all (Σ00 : global_env) (mp : modpath) (root : kername) : global_env * copytab :=
  let Σ0 := mix_decls Σ00 mp in
  let Σ := conv_all Σ0 mp in
  match (match lookup_env Σ kn_fix_sub with Some _ => true | None => if pf_has_iter Σ then true else match deep_kns Σ mp with [] => match mix_kns Σ mp with [] => false | _ => true end | _ => true end end) with
  | false => (Σ, [])
  | true =>
      fold_left (fun st kn =>
        let '(S1, tb) := st in
        if in_prog mp (fst kn) then
          match pf_make S1 kn, lookup_env S1 kn with
          | Some r, Some (ConstantDecl cb) =>
              let m := mangle kn in
              let wk := (copy_mp, m ^ "__w"%bs) in
              let dk := (copy_mp, m ^ "__wd"%bs) in
              let mk := (copy_mp, m ^ "__wm"%bs) in
              let nk := (copy_mp, m ^ "__wn"%bs) in
              (add_decl (fold_left (fun S g => add_decl S (fst g) (pg_gty r) (snd g)) (map y_post (pg_gs r)) S1) kn (cst_type cb) (pg_w r),
               tb ++ map (fun g => (fst g, ([], []), fst g, snd g)) (map y_post (pg_gs r))
                  ++ [(wk, ([], []), wk, pg_w r); (dk, ([], []), dk, pg_d r); (mk, ([], []), mk, pg_m r); (nk, ([], []), nk, pg_n r)])
          | _, _ => st
          end
        else st) (mix_kns Σ mp ++ snd (reach_go 1000 Σ mp root root ([], []))) (Σ, [])
  end.
(** for kitc.py: each such function: its name, the constant holding its [Fix_sub], its number of parameters, its three made functions, and whether its measure is on a machine number *)
Definition pf_info (p : program) : list (string * string * nat * string * string * string * nat) :=
  match p with
  | (Σ, tConst root _) =>
      map (fun kn => (string_of_kername kn, ""%bs, O, ""%bs, ""%bs, "c"%bs, O)) (conv_kns Σ (fst root)) ++
      match (match lookup_env Σ kn_fix_sub with Some _ => true | None => if pf_has_iter Σ then true else match deep_kns Σ (fst root) with [] => match mix_kns (mix_decls Σ (fst root)) (fst root) with [] => false | _ => true end | _ => true end end) with false => [] | true =>
      flat_map (fun kn =>
        match pf_make Σ kn with
        | Some r =>
            match pf_parts Σ kn with
            | Some (tys, _, _, _, fk) =>
                [(string_of_kername kn, match fk with Some f => string_of_kername f | None => ""%bs end, length tys, mangle kn, pg_tag r, pg_sp r, pg_ph r)]
            | None => [(string_of_kername kn, pg_cs r, length (fst (lams (pg_m r))), mangle kn, pg_tag r, pg_sp r, pg_ph r)]
            end
        | None => []
        end) (mix_kns (mix_decls Σ (fst root)) (fst root) ++ filter (fun kn => in_prog (fst root) (fst kn)) (snd (reach_go 1000 Σ (fst root) root root ([], []))))
      end
  | _ => []
  end.
Definition ty_nf (t : term) : term := match t with tApp (tLambda _ _ b) [a] => subst10 a b | _ => t end.
Definition ty_red (t : term) : bool := match t with tApp (tLambda _ _ _) [_] => true | _ => false end.
Fixpoint ty_has (fuel : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tCast _ _ _ => true
      | tLambda _ ty b => if ty_red ty then true else ty_has fuel b
      | tLetIn _ v ty b => if ty_red ty then true else if ty_has fuel v then true else ty_has fuel b
      | tApp f args => if ty_has fuel f then true else existsb (ty_has fuel) args
      | tCase _ _ c brs => if ty_has fuel c then true else existsb (fun br => ty_has fuel (bbody br)) brs
      | tFix mfix _ => existsb (fun d => ty_has fuel (dbody d)) mfix
      | _ => false
      end
  end.
Fixpoint ty_beta (fuel : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tCast c _ _ => ty_beta fuel c
      | tLambda na ty b => tLambda na (ty_nf ty) (ty_beta fuel b)
      | tLetIn na v ty b => tLetIn na (ty_beta fuel v) (ty_nf ty) (ty_beta fuel b)
      | tApp f args => tApp (ty_beta fuel f) (map (ty_beta fuel) args)
      | tCase ci p c brs => tCase ci p (ty_beta fuel c) (map (fun br => {| bcontext := bcontext br; bbody := ty_beta fuel (bbody br) |}) brs)
      | tFix mfix k => tFix (map (fun d => {| dname := dname d; dtype := dtype d; rarg := rarg d; dbody := ty_beta fuel (dbody d) |}) mfix) k
      | _ => t
      end
  end.
(** (step 68) a function of Rocq's lists on a list written in the text: worked out, the same up to Rocq's reduction; if it stays stuck on a variable, left as it is *)
Definition lib_list (kn : kername) : bool :=
  let f := lib_file_of (fst kn) in
  if String.eqb f "ListDef"%bs then true else String.eqb f "List"%bs.
(** a constant that takes or gives a list: a helper over lists *)
Definition lu_is_list (t : term) : bool :=
  match t with
  | tInd i _ | tApp (tInd i _) _ => if String.eqb (snd (inductive_mind i)) "list"%bs then true else false
  | _ => false
  end.
Fixpoint lu_prod (fuel : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel => match t with
              | tProd _ a b => if lu_is_list a then true else lu_prod fuel b
              | _ => lu_is_list t
              end
  end.
Definition lu_list_ty (kn : kername) (Σ : global_env) : bool :=
  match lookup_env Σ kn with Some (ConstantDecl cb) => lu_prod 100 (cst_type cb) | _ => false end.
Definition lu_data (i : inductive) : bool := negb (Kername.eqb (inductive_mind i) (inductive_mind ind_nat)).
(** a constant that is a value of a type of data, written in the text *)
Definition lu_cdata (kn : kername) (Σ : global_env) : bool :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) =>
      match cst_type cb with
      | tInd i _ | tApp (tInd i _) _ =>
          if lu_data i then
            if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then false else
            true
          else false
      | _ => false
      end
  | _ => false
  end.
Fixpoint lu_red (fuel : nat) (Σ : global_env) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tApp (tLambda _ _ b) (a :: r) => lu_red fuel Σ (match r with [] => subst10 a b | _ => mkApps (subst10 a b) r end)
      | tApp (tApp f a1) a2 => lu_red fuel Σ (tApp f (a1 ++ a2))
      | tApp (tConst kn _) args =>
          (* a function of the lists, or a helper of the program with no fixpoint of its own *)
          if lib_list kn then
            match body_of Σ kn with
            | Some b => lu_red fuel Σ (mkApps b args)
            | None => t
            end
          else
            match body_of Σ kn with
            | Some (tFix [d] 0 as fx) =>
                match nth_error args (rarg d) with
                | Some a =>
                    match lu_red fuel Σ a with
                    | tConstruct i _ _ | tApp (tConstruct i _ _) _ =>
                        if lu_data i then lu_red fuel Σ (mkApps fx args) else t
                    | _ => t
                    end
                | None => t
                end
            | Some (tFix _ _) | None => t
            | Some b => if lu_list_ty kn Σ then lu_red fuel Σ (mkApps b args) else t
            end
      | tConst kn _ =>
          if lib_list kn then match body_of Σ kn with Some b => lu_red fuel Σ b | None => t end
          else if lu_cdata kn Σ then match body_of Σ kn with Some b => lu_red fuel Σ b | None => t end
          else t
      | tApp (tFix [d] 0 as fx) args =>
          match nth_error args (rarg d) with
          | Some a =>
              let a' := lu_red fuel Σ a in
              match a' with
              | tConstruct _ _ _ | tApp (tConstruct _ _ _) _ =>
                  lu_red fuel Σ (mkApps (subst10 fx (dbody d)) (firstn (rarg d) args ++ a' :: skipn (S (rarg d)) args))
              | _ => t
              end
          | None => t
          end
      | tCase ci p c brs =>
          match lu_red fuel Σ c with
          | tConstruct _ k _ =>
              match nth_error brs k with
              | Some br => lu_red fuel Σ (bbody br)
              | None => t
              end
          | tApp (tConstruct _ k _) cargs =>
              match nth_error brs k with
              | Some br => lu_red fuel Σ (subst (rev (skipn (ci_npar ci) cargs)) 0 (bbody br))
              | None => t
              end
          | _ => t
          end
      | _ => t
      end
  end.
(** every head worked out, under what is left *)
Fixpoint lu_full (fuel : nat) (Σ : global_env) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := lu_full fuel Σ in
      match lu_red 100000 Σ t with
      | tApp f args => tApp f (map go args)
      | tLambda na a b => tLambda na a (go b)
      | tLetIn na v a b => tLetIn na (go v) a (go b)
      | tCase ci p c brs => tCase ci p (go c) (map (fun br => {| bcontext := bcontext br; bbody := go (bbody br) |}) brs)
      | r => r
      end
  end.
Fixpoint lu_stuck (fuel : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => true
  | S fuel =>
      match t with
      | tConst kn _ => lib_list kn
      | tFix _ _ => true
      | tApp f args => if lu_stuck fuel f then true else existsb (lu_stuck fuel) args
      | tLambda _ _ b => lu_stuck fuel b
      | tLetIn _ v _ b => if lu_stuck fuel v then true else lu_stuck fuel b
      | tCase _ _ c brs => if lu_stuck fuel c then true else existsb (fun br => lu_stuck fuel (bbody br)) brs
      | _ => false
      end
  end.
(** a fixpoint given a value of data, written or named *)
Definition lu_fix_lit (kn : kername) (args : list term) (Σ : global_env) : bool :=
  match body_of Σ kn with
  | Some (tFix [d] 0) =>
      match nth_error args (rarg d) with
      | Some (tConstruct i _ _) | Some (tApp (tConstruct i _ _) _) => lu_data i
      | Some (tConst c _) => lu_cdata c Σ
      | _ => false
      end
  | _ => false
  end.
Fixpoint lu_t (fuel : nat) (Σ : global_env) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := lu_t fuel Σ in
      match t with
      | tApp (tConst kn u) args =>
          if if lib_list kn then true else if lu_list_ty kn Σ then true else lu_fix_lit kn args Σ then
            let r := lu_full 1000 Σ (tApp (tConst kn u) (map go args)) in
            if lu_stuck 100000 r then tApp (tConst kn u) (map go args) else r
          else tApp (tConst kn u) (map go args)
      | tApp f args => tApp (go f) (map go args)
      | tLambda na a b => tLambda na a (go b)
      | tLetIn na v a b => if lu_is_list a then go (subst10 v b) else tLetIn na (go v) a (go b)
      | tCase ci p c brs => tCase ci p (go c) (map (fun br => {| bcontext := bcontext br; bbody := go (bbody br) |}) brs)
      | tFix mfix k => tFix (map (fun d => {| dname := dname d; dtype := dtype d; rarg := rarg d; dbody := go (dbody d) |}) mfix) k
      | _ => t
      end
  end.
Definition mo_beta (args : list term) (t : term) : term := al_beta args t.
(** (step 71) a helper of the program that takes a function: written out, the same up to delta and beta; what it applies may then be a choice *)
Fixpoint mo_fun (fuel : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel => match t with tProd _ (tProd _ _ _) _ => true | tProd _ _ b => mo_fun fuel b | _ => false end
  end.
Fixpoint mo_t (fuel : nat) (Σ : global_env) (mp : modpath) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := mo_t fuel Σ mp in
      match t with
      | tApp (tConst kn u) args =>
          if in_prog mp (fst kn) then
            match lookup_env Σ kn with
            | Some (ConstantDecl cb) =>
                match cst_body cb with
                | Some b =>
                    if (match b with tFix _ _ => false | _ => if mo_fun 100 (al_t 1000 Σ mp (cst_type cb)) then true else match snd (lams b) with tCase _ _ _ _ => Nat.ltb (length (fst (lams b))) (length args) | _ => false end end)
                    then go (mo_beta args (al_t 100000 Σ mp b))
                    else tApp (tConst kn u) (map go args)
                | None => tApp (tConst kn u) (map go args)
                end
            | _ => tApp (tConst kn u) (map go args)
            end
          else tApp (tConst kn u) (map go args)
      | tApp (tLambda _ _ _ as f) args => go (mo_beta args f)
      | tApp f args => tApp (go f) (map go args)
      | tLambda na a b => tLambda na a (go b)
      | tLetIn na v a b => tLetIn na (go v) a (go b)
      | tCase ci p c brs =>
          let c1 := match c with
                    | tApp (tConst kn _) args =>
                        if in_prog mp (fst kn) then
                          match body_of Σ kn with
                          | Some b => match snd (lams b) with
                                      | tCase _ _ _ _ =>
                                          let w := mo_beta args b in
                                          if y_conb 100 w then w else c
                                      | _ => c
                                      end
                          | None => c
                          end
                        else c
                    | _ => c
                    end in
          tCase ci p (go c1) (map (fun br => {| bcontext := bcontext br; bbody := go (bbody br) |}) brs)
      | tFix mfix k => tFix (map (fun d => {| dname := dname d; dtype := dtype d; rarg := rarg d; dbody := go (dbody d) |}) mfix) k
      | _ => t
      end
  end.
(** (step 68) a function chosen by a match, applied *)
Fixpoint fc_has (fuel : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tApp (tCase _ _ _ _) _ => true
      | tCase _ _ (tCase _ _ _ _ as c) _ => if y_conb 100 c then true else fc_has fuel c
      | tApp f args => if fc_has fuel f then true else existsb (fc_has fuel) args
      | tLambda _ _ b => fc_has fuel b
      | tLetIn _ v _ b => if fc_has fuel v then true else fc_has fuel b
      | tCase _ _ c brs => if fc_has fuel c then true else existsb (fun br => fc_has fuel (bbody br)) brs
      | tFix mfix _ => existsb (fun d => fc_has fuel (dbody d)) mfix
      | _ => false
      end
  end.
(** (step 64) an operation of Rocq's machine numbers that its axioms define by others ([compare_def_spec] ..): that definition in its place.  Not by conversion, a primitive being stuck on a variable; the equation of [y_all] carries it, by those axioms *)
Definition pm_table : list (kername * term) :=
  [(kn_of <% PrimInt63.compare %>, <% fun x y : PrimInt63.int => if PrimInt63.ltb x y then Lt else if PrimInt63.eqb x y then Eq else Gt %>);
   (kn_of <% PrimInt63.compares %>, <% fun x y : PrimInt63.int => if PrimInt63.ltsb x y then Lt else if PrimInt63.eqb x y then Eq else Gt %>);
   (kn_of <% PrimInt63.addc %>, <% fun x y : PrimInt63.int => if PrimInt63.ltb (PrimInt63.add x y) x then CarryType.C1 (PrimInt63.add x y) else CarryType.C0 (PrimInt63.add x y) %>);
   (kn_of <% PrimInt63.addcarryc %>, <% fun x y : PrimInt63.int => if PrimInt63.leb (PrimInt63.add (PrimInt63.add x y) 1) x then CarryType.C1 (PrimInt63.add (PrimInt63.add x y) 1) else CarryType.C0 (PrimInt63.add (PrimInt63.add x y) 1) %>);
   (kn_of <% PrimInt63.subc %>, <% fun x y : PrimInt63.int => if PrimInt63.leb y x then CarryType.C0 (PrimInt63.sub x y) else CarryType.C1 (PrimInt63.sub x y) %>);
   (kn_of <% PrimInt63.subcarryc %>, <% fun x y : PrimInt63.int => if PrimInt63.ltb y x then CarryType.C0 (PrimInt63.sub (PrimInt63.sub x y) 1) else CarryType.C1 (PrimInt63.sub (PrimInt63.sub x y) 1) %>);
   (kn_of <% PrimInt63.diveucl %>, <% fun x y : PrimInt63.int => (PrimInt63.div x y, PrimInt63.mod x y) %>);
   (kn_of <% PrimInt63.addmuldiv %>, <% fun p x y : PrimInt63.int => PrimInt63.lor (PrimInt63.lsl x p) (PrimInt63.lsr y (PrimInt63.sub 63 p)) %>);
   (kn_of <% PrimInt63.mulc %>, <% fun x y : PrimInt63.int => (KQ.KQRun.kq_mh x y, PrimInt63.mul x y) %>);
   (kn_of <% PrimInt63.head0 %>, <% fun x : PrimInt63.int => KQ.KQRun.kq_h0 x %>);
   (kn_of <% PrimInt63.tail0 %>, <% fun x : PrimInt63.int => KQ.KQRun.kq_t0 x %>);
   (kn_of <% Nat.compare %>, <% fun a b : nat => if Nat.eqb a b then Eq else if Nat.ltb a b then Lt else Gt %>)].
Definition pm_of (k : kername) : option term :=
  option_map snd (List.find (fun e => Kername.eqb k (fst e)) pm_table).
(** (step 68) a test that gives a proof with its answer: the boolean test it is, by its arguments; by name, a library the reader need not load *)
Definition dec_of (k : kername) : option (term -> term -> term) :=
  let f := lib_file_of (fst k) in
  let nb := fun (g : kername) (swap : bool) => Some (fun a b : term => if swap then tApp (tConst g []) [b; a] else tApp (tConst g []) [a; b]) in
  if String.eqb f "PeanoNat"%bs then
    (if String.eqb (snd k) "eq_dec"%bs then nb kn_nat_eqb false else None)
  else if String.eqb f "Peano_dec"%bs then
    (if String.eqb (snd k) "eq_nat_dec"%bs then nb kn_nat_eqb false else None)
  else if String.eqb f "Compare_dec"%bs then
    (if String.eqb (snd k) "lt_dec"%bs then nb kn_nat_ltb false
     else if String.eqb (snd k) "le_dec"%bs then nb kn_nat_leb false
     else if String.eqb (snd k) "gt_dec"%bs then nb kn_nat_ltb true
     else if String.eqb (snd k) "ge_dec"%bs then nb kn_nat_leb true
     else if String.eqb (snd k) "le_lt_dec"%bs then nb kn_nat_leb false
     else if String.eqb (snd k) "le_gt_dec"%bs then nb kn_nat_leb false
     else None)
  else if String.eqb f "Uint63"%bs then
    (if String.eqb (snd k) "eqs"%bs then nb (kn_of <% PrimInt63.eqb %>) false else None)
  else None.
Definition y_case_bool := <% fun b : bool => if b then O else O %>.
(** (step 73) [diveucl_21 a b c]: Rocq's axioms say what it is when [a < c], and nothing else (§0.5, the fourth reason).  What the text shows at a place: the
    pairs [(a, c)] a test around it has shown [a < c] of, each with the [let]s it stands under written out, since the equation's tactic sees them so *)
Definition kn_d21 := kn_of <% PrimInt63.diveucl_21 %>.
Definition kn_ltb := kn_of <% PrimInt63.ltb %>.
Definition kn_leb := kn_of <% PrimInt63.leb %>.
Fixpoint test_shows (fuel : nat) (pol : bool) (t : term) {struct fuel} : list (term * term) :=
  match fuel with
  | O => []
  | S fuel =>
      match t with
      | tApp (tConst k _) [x; y] =>
          if Kername.eqb k kn_ltb then (if pol then [(x, y)] else [])
          else if Kername.eqb k kn_leb then (if pol then [] else [(y, x)])
          else if Kername.eqb k kn_andb then (if pol then test_shows fuel true x ++ test_shows fuel true y else [])
          else if Kername.eqb k kn_orb then (if pol then [] else test_shows fuel false x ++ test_shows fuel false y)
          else []
      | tApp (tConst k _) [x] => if Kername.eqb k kn_negb then test_shows fuel (negb pol) x else []
      | _ => []
      end
  end.
Fixpoint pm_norm (fuel : nat) (e : list (option term)) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tRel i =>
          match nth_error e i with
          | Some (Some v) => lift (S i) 0 (pm_norm fuel (skipn (S i) e) v)
          | _ => t
          end
      | tApp f args => tApp (pm_norm fuel e f) (map (pm_norm fuel e) args)
      | _ => t
      end
  end.
Definition shows_lift (n : nat) (g : list (term * term)) : list (term * term) := map (fun p => (lift n 0 (fst p), lift n 0 (snd p))) g.
Definition d21_pair := <% fun q r : PrimInt63.int => (q, r) %>.
Definition d21_kit := <% fun a b c : PrimInt63.int => KQ.KQRun.kq_d21 a b c %>.
(** what the program's text has at [diveucl_21 a b c]: three numbers written: its value, which the kernel computes; [a < c] shown or written: the kit's function; else itself, and the program is refused with that reason *)
Definition d21_at (e : list (option term)) (g : list (term * term)) (a b c : term) : term :=
  let a' := pm_norm 100 e a in
  let b' := pm_norm 100 e b in
  let c' := pm_norm 100 e c in
  let same := existsb (fun p => teq 1000 (fst p) a' && teq 1000 (snd p) c') g in
  match a', b', c' with
  | tInt x, tInt y, tInt z =>
      pf_beta d21_pair [tInt (fst (PrimInt63.diveucl_21 x y z)); tInt (snd (PrimInt63.diveucl_21 x y z))]
  | tInt x, _, tInt z =>
      if PrimInt63.ltb x z then pf_beta d21_kit [a; b; c] else tApp (tConst kn_d21 []) [a; b; c]
  | _, _, _ => if same then pf_beta d21_kit [a; b; c] else tApp (tConst kn_d21 []) [a; b; c]
  end.
Definition pm_ctx (n : nat) (e : list (option term)) : list (option term) := List.repeat None n ++ e.
Fixpoint pm_sub (fuel : nat) (e : list (option term)) (g : list (term * term)) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      (* a function given as an argument stays as it is: what it holds is under its binder, where no equation reaches *)
      let arg := fun a => match a with tLambda _ _ _ => a | _ => pm_sub fuel e g a end in
      let brch := fun (g' : list (term * term)) (br : branch term) =>
        {| bcontext := bcontext br;
           bbody := pm_sub fuel (pm_ctx (length (bcontext br)) e) (shows_lift (length (bcontext br)) g') (bbody br) |} in
      match t with
      | tApp (tConst k u) args =>
          let args' := map arg args in
          if Kername.eqb k kn_d21 then
            match args' with
            | [a; b; c] => d21_at e g a b c
            | _ => tApp (tConst k u) args'
            end
          else
          match pm_of k with
          | Some tm => pf_beta tm args'
          | None => tApp (tConst k u) args'
          end
      | tApp f args => tApp (pm_sub fuel e g f) (map arg args)
      | tLambda na ty b => tLambda na ty (pm_sub fuel (None :: e) (shows_lift 1 g) b)
      | tLetIn na v ty b => tLetIn na (pm_sub fuel e g v) ty (pm_sub fuel (Some v :: e) (shows_lift 1 g) b)
      | tCase ci p (tApp (tConst k _) dargs) [b0; b1] =>
          (* (step 68) the proofs not named by what follows *)
          match dec_of k, y_case_bool with
          | Some mk, tLambda _ _ (tCase cib pb _ _) =>
              match rev dargs with
              | y :: x :: _ =>
                  if (if tm_has_rel 1000 0 (bbody b0) then true else tm_has_rel 1000 0 (bbody b1))
                  then tCase ci p (tApp (tConst k []) (map arg dargs)) (map (brch g) [b0; b1])
                  else
                    tCase cib {| pparams := pparams pb; puinst := puinst pb; pcontext := pcontext pb; preturn := preturn p |} (mk (arg x) (arg y))
                      [{| bcontext := []; bbody := pm_sub fuel e g (subst10 (tRel 0) (bbody b0)) |};
                       {| bcontext := []; bbody := pm_sub fuel e g (subst10 (tRel 0) (bbody b1)) |}]
              | _ => t
              end
          | _, _ =>
              let c0 := pm_norm 100 e (tApp (tConst k []) dargs) in
              tCase ci p (pm_sub fuel e g (tApp (tConst k []) dargs))
                [brch (test_shows 100 true c0 ++ g) b0; brch (test_shows 100 false c0 ++ g) b1]
          end
      | tCase ci p c [b0; b1] =>
          (* a test held by a [let] *)
          let c0 := pm_norm 100 e c in
          tCase ci p (pm_sub fuel e g c)
            [brch (test_shows 100 true c0 ++ g) b0; brch (test_shows 100 false c0 ++ g) b1]
      | tCase ci p c brs => tCase ci p (pm_sub fuel e g c) (map (brch g) brs)
      | tFix mfix k =>
          tFix (map (fun d => {| dname := dname d; dtype := dtype d; rarg := rarg d;
                                 dbody := pm_sub fuel (pm_ctx (length mfix) e) (shows_lift (length mfix) g) (dbody d) |}) mfix) k
      | _ => t
      end
  end.
Definition pm_has (t : term) : bool :=
  existsb (fun k => if Kername.eqb k kn_d21 then true else match pm_of k with Some _ => true | None => match dec_of k with Some _ => true | None => false end end) (consts 10000 t []).
(** a body's choices over known constructors floated out: for a function with no fixpoint *)
Definition y_nf (T b : term) : term :=
  let '(tys, body) := lams b in lams_of tys (y_tail 1000 1000000 T body).
(* ---------------------------------------------------------------- a function read in another form (step 69) *)
(** A function whose form the compiler's theorem does not take and no conversion reaches: a memory parameter never read, moved by the
    recursion or given another memory by the call; a type parameter.  A function of its own in its place, at every argument equal to it, by
    induction (a row holds the statement; [kitc.py] proves it); its callers' text calls that one, each by an equation, step 61's, with that
    lemma among its rewrites *)
Definition drop_at (slots : list nat) (args : list term) : list term :=
  map snd (filter (fun ja : nat * term => negb (existsb (Nat.eqb (fst ja)) slots)) (combine (seq 0 (length args)) args)).
(** does the variable [v] occur outside the slots [slots] of the function's own calls ([fv] the function's variable) *)
Fixpoint rp_occ (fuel fv : nat) (slots : list nat) (v d : nat) (t : term) {struct fuel} : bool :=
  match fuel with
  | O => true
  | S fuel =>
      let go := rp_occ fuel fv slots v d in
      match t with
      | tRel i => Nat.eqb i (v + d)
      | tApp (tRel f) args =>
          if Nat.eqb f (fv + d) then existsb go (drop_at slots args)
          else if Nat.eqb f (v + d) then true else existsb go args
      | tApp f args => if go f then true else existsb go args
      | tLambda _ _ b => rp_occ fuel fv slots v (S d) b
      | tLetIn _ x _ b => if go x then true else rp_occ fuel fv slots v (S d) b
      | tCase _ _ c brs => if go c then true else existsb (fun br => rp_occ fuel fv slots v (d + length (bcontext br)) (bbody br)) brs
      | tFix mfix _ => existsb (fun df => rp_occ fuel fv slots v (d + length mfix) (dbody df)) mfix
      | tProj _ c => go c
      | _ => false
      end
  end.
(** the function's own calls given other arguments *)
Fixpoint rp_own (fuel fv d : nat) (f : list term -> list term) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := rp_own fuel fv d f in
      match t with
      | tApp (tRel i) args => if Nat.eqb i (fv + d) then tApp (tRel i) (map go (f args)) else tApp (tRel i) (map go args)
      | tApp g args => tApp (go g) (map go args)
      | tLambda na a b => tLambda na a (rp_own fuel fv (S d) f b)
      | tLetIn na x a b => tLetIn na (go x) a (rp_own fuel fv (S d) f b)
      | tCase ci p c brs => tCase ci p (go c) (map (fun br => {| bcontext := bcontext br; bbody := rp_own fuel fv (d + length (bcontext br)) f (bbody br) |}) brs)
      | tFix mfix k => tFix (map (fun df => {| dname := dname df; dtype := dtype df; rarg := rarg df; dbody := rp_own fuel fv (d + length mfix) f (dbody df) |}) mfix) k
      | tProj p c => tProj p (go c)
      | _ => t
      end
  end.
(** the memory parameters never read; one stays *)
Definition dead_slots (d : def term) : list nat :=
  let '(tys, body) := lams (dbody d) in
  let n := length tys in
  let pms := existsb is_pm tys in
  match filter (fun p => is_ty kn_mem (nth p tys (tRel 0))) (seq 0 n) with
  | [] => []
  | ms =>
      if if pms then false else Nat.eqb (length ms) 1 then [] else
      let dead := filter (fun p => negb (rp_occ 100000 n [p] (n - 1 - p) 0 body)) ms in
      (* a memory stays: the last one if none else holds one *)
      if if pms then false else Nat.eqb (length dead) (length ms) then removelast dead else dead
  end.
(** the type parameters a fixpoint starts with *)
Fixpoint lead_sorts (t : term) : nat := match t with tLambda _ (tSort _) b => S (lead_sorts b) | _ => O end.
Fixpoint skip_lam (k : nat) (t : term) : term :=
  match k, t with S k, tLambda _ _ b => skip_lam k b | _, _ => t end.
Fixpoint skip_pi (k : nat) (t : term) : term :=
  match k, t with S k, tProd _ _ b => skip_pi k b | _, _ => t end.
(** a definition with no fixpoint of its own: its body, marked by a [rarg] no fixpoint has *)
Definition rp_nofix : nat := 999.
(** a row: the function as the text names it, the types it is given, the slots dropped, the stem of what is made, its fixpoint *)
Definition rprow : Type := term * list term * list nat * string * def term.
(** (step 72) a row whose function gives back [unit] and a memory, what is in its place the memory: a mark among the slots, no slot *)
Definition rp_um : nat := 998.
Definition rp_real (slots : list nat) : list nat := filter (fun p => Nat.ltb p 900) slots.
Definition rp_is_um (slots : list nat) : bool := existsb (Nat.eqb rp_um) slots.
(** (step 72) a row whose function gives back a boolean and a memory, what is in its place a number and a memory *)
Definition rp_bm : nat := 997.
Definition rp_is_bm (slots : list nat) : bool := existsb (Nat.eqb rp_bm) slots.
Definition bm_ty := <% (bool * KQ.KQRun.mem)%type %>.
Definition bm_num := <% (PrimInt63.int * KQ.KQRun.mem)%type %>.
Definition bm_wrap := <% fun p : PrimInt63.int * KQ.KQRun.mem => let (x, t) := p in (PrimInt63.eqb x 1%uint63, t) %>.
Definition bm_b2i := <% fun b : bool => if b then 1%uint63 else 0%uint63 %>.
Definition bm_eq1 := <% fun x : PrimInt63.int => PrimInt63.eqb x 1%uint63 %>.
Definition bm_fst := <% fun p : PrimInt63.int * KQ.KQRun.mem => PrimInt63.eqb (fst p) 1%uint63 %>.
Definition bm_snd := <% fun p : PrimInt63.int * KQ.KQRun.mem => snd p %>.
Definition um_ty := <% (unit * KQ.KQRun.mem)%type %>.
Definition um_pair := <% fun t : KQ.KQRun.mem => (tt, t) %>.
Definition um_tt := <% tt %>.
(** the fixpoint in its place *)
Definition rp_def (r : rprow) : def term :=
  let '(_, inst, slots0, _, d) := r in
  let slots := rp_real slots0 in
  match inst with
  | [] =>
      let '(tys, body) := lams (dbody d) in
      let n := length tys in
      let b1 := rp_own 100000 n 0 (drop_at slots) body in
      let b2 := fold_left (fun b p => subst [tVar "dead"%bs] (n - 1 - p) b) slots b1 in
      let tys' := drop_at slots tys in
      {| dname := dname d; dtype := pis_of tys' (ret_ty (dtype d));
         rarg := if Nat.eqb (rarg d) rp_nofix then rp_nofix else rarg d - length (filter (fun p => Nat.ltb p (rarg d)) slots);
         dbody := lams_of tys' b2 |}
  | _ =>
      let t := length inst in
      let u := subst (rev inst) 0 (skip_lam t (dbody d)) in
      if Nat.eqb (rarg d) rp_nofix then
        {| dname := dname d; dtype := subst (rev inst) 0 (skip_pi t (dtype d)); rarg := rp_nofix; dbody := u |}
      else
      {| dname := dname d; dtype := subst (rev inst) 0 (skip_pi t (dtype d)); rarg := rarg d - t;
         dbody := rp_own 100000 0 0 (skipn t) u |}
  end.
Definition y_eq := <% @eq %>.
Definition rp_name (r : rprow) : kername := let '(_, _, _, st, _) := r in (copy_mp, st ^ "__rp__wy"%bs).
Definition rq_name (r : rprow) : kername := let '(_, _, _, st, _) := r in (copy_mp, st ^ "__rq__wy"%bs).
(** at every argument the function and the fixpoint in its place are equal *)
Definition rp_stmt (r : rprow) : term :=
  let '(h, inst, slots0, _, _) := r in
  let slots := rp_real slots0 in
  let d' := rp_def r in
  let tys := fst (lams (dbody d')) in
  (* a dropped slot's type is a memory: the statement takes every parameter of the function as the text names it *)
  let tys0 := match inst with [] => (let '(_, _, _, _, d0) := r in fst (lams (dbody d0))) | _ => tys end in
  let m := length tys0 in
  let rels := map (fun j => tRel (m - 1 - j)) (seq 0 m) in
  if rp_is_um slots0 then
    pis_of tys0 (tApp y_eq [um_ty; mkApps h rels; pf_beta um_pair [tApp (tConst (rp_name r) []) rels]])
  else if rp_is_bm slots0 then
    pis_of tys0 (tApp y_eq [bm_ty; mkApps h rels; pf_beta bm_wrap [tApp (tConst (rp_name r) []) rels]])
  else
  pis_of tys0 (tApp y_eq [ret_ty (dtype d'); tApp h (inst ++ rels); tApp (tConst (rp_name r) []) (match inst with [] => drop_at slots rels | _ => rels end)]).
(** a text with each such call written as a call of what is in its place *)
Definition rp_match (rows : list rprow) (h : term) (args : list term) : option term :=
  match List.find (fun r : rprow =>
          let '(h0, inst, _, _, _) := r in
          match h0, h with
          | tConst k0 _, tConst k _ => if Kername.eqb k0 k then teqs (firstn (length inst) args) inst else false
          | tFix _ _, tFix _ _ => teq 100000 h0 h
          | _, _ => false
          end) rows with
  | Some r =>
      let '(_, inst, slots0, _, d0) := r in
      let slots := rp_real slots0 in
      if rp_is_um slots0 then
        if Nat.eqb (length args) (length (fst (lams (dbody d0)))) then Some (pf_beta um_pair [tApp (tConst (rp_name r) []) args]) else None else
      if rp_is_bm slots0 then
        if Nat.eqb (length args) (length (fst (lams (dbody d0)))) then Some (pf_beta bm_wrap [tApp (tConst (rp_name r) []) args]) else None else
      Some (tApp (tConst (rp_name r) []) (match inst with [] => drop_at slots args | _ => skipn (length inst) args end))
  | None => None
  end.
Definition bm_part (rows : list rprow) (h : term) (args : list term) (pj : term) : option term :=
  match List.find (fun r : rprow =>
          let '(h0, _, sl, _, d0) := r in
          if rp_is_bm sl then
            match h0, h with
            | tConst k0 _, tConst k _ => Kername.eqb k0 k && Nat.eqb (length args) (length (fst (lams (dbody d0))))
            | _, _ => false
            end
          else false) rows with
  | Some r => Some (pf_beta pj [tApp (tConst (rp_name r) []) args])
  | None => None
  end.
Fixpoint rp_sub (fuel : nat) (rows : list rprow) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := rp_sub fuel rows in
      match t with
      | tApp h args =>
          match (match h, args with
                 | tConst k _, [_; _; tApp h2 a2] =>
                     if Kername.eqb k kn_fst then bm_part rows h2 (map go a2) bm_fst
                     else if Kername.eqb k kn_snd then bm_part rows h2 (map go a2) bm_snd else None
                 | _, _ => None
                 end) with
          | Some u => u
          | None =>
          let args' := map go args in
          match rp_match rows h args' with
          | Some u => u
          | None => tApp (go h) args'
          end
          end
      | tLambda na a b => tLambda na a (go b)
      | tLetIn na x a b => tLetIn na (go x) a (go b)
      | tCase ci p c brs => tCase ci p (go c) (map (fun br => {| bcontext := bcontext br; bbody := go (bbody br) |}) brs)
      | tFix mfix k => tFix (map (fun df => {| dname := dname df; dtype := dtype df; rarg := rarg df; dbody := go (dbody df) |}) mfix) k
      | tProj p c => tProj p (go c)
      | _ => t
      end
  end.
(** the heads applied in a text, a constant or a closed local fixpoint *)
Fixpoint rp_apps (fuel : nat) (t : term) (acc : list (term * list term)) {struct fuel} : list (term * list term) :=
  match fuel with
  | O => acc
  | S fuel =>
      let go := fun a x => rp_apps fuel x a in
      match t with
      | tApp h args =>
          let acc' := fold_left go args acc in
          match h with
          | tConst _ _ => (h, args) :: acc'
          | tFix [_] 0 => (h, args) :: acc'
          | _ => go acc' h
          end
      | tLambda _ _ b => go acc b
      | tLetIn _ x _ b => go (go acc x) b
      | tCase _ _ c brs => fold_left (fun a br => go a (bbody br)) brs (go acc c)
      | tFix mfix _ => fold_left (fun a df => go a (dbody df)) mfix acc
      | tProj _ c => go acc c
      | _ => acc
      end
  end.
Definition rp_known (rows : list rprow) (h : term) (inst : list term) : bool :=
  existsb (fun r : rprow =>
    let '(h0, i0, _, _, _) := r in
    match h0, h with
    | tConst k0 _, tConst k _ => if Kername.eqb k0 k then teqs i0 inst else false
    | tFix _ _, tFix _ _ => teq 100000 h0 h
    | _, _ => false
    end) rows.
(** the rows of a text *)
Definition rp_rows_of (Σ : global_env) (mp : modpath) (stem : string) (t : term) (rows : list rprow) : list rprow :=
  fold_left (fun (rs : list rprow) (ha : term * list term) =>
    let '(h, args) := ha in
    match h with
    | tFix [d] 0 =>
        match dead_slots d with
        | [] => rs
        | sl => if negb (closedn 0 h) then rs else
                if rp_known rs h [] then rs
                else rs ++ [(h, [], sl, stem ^ "__l"%bs ^ string_of_nat (length rs), d)]
        end
    | tConst k _ =>
        if in_prog mp (fst k) then
          match body_of Σ k with
          | Some (tFix [d] 0) =>
              match lead_sorts (dbody d) with
              | O => rs
              | t0 =>
                  let inst := firstn t0 args in
                  if Nat.eqb (length inst) t0 && forallb (closedn 0) inst then
                    if rp_known rs h inst then rs
                    else rs ++ [(h, inst, [], mangle k ^ "__i"%bs ^ string_of_nat (length rs), d)]
                  else rs
              end
          | Some b =>
              (* a definition polymorphic in a type, its body naming a fixpoint that is *)
              match lead_sorts b with
              | O => rs
              | t0 =>
                  let inst := firstn t0 args in
                  if Nat.eqb (length inst) t0 && forallb (closedn 0) inst
                     && existsb (fun ha2 : term * list term =>
                          match fst ha2 with
                          | tConst k2 _ => match body_of Σ k2 with Some (tFix [d2] 0) => Nat.ltb 0 (lead_sorts (dbody d2)) | _ => false end
                          | _ => false
                          end) (rp_apps 100000 b []) then
                    if rp_known rs h inst then rs
                    else match lookup_env Σ k with
                         | Some (ConstantDecl cb) =>
                             rs ++ [(h, inst, [], mangle k ^ "__i"%bs ^ string_of_nat (length rs) ^ "__n"%bs,
                                     {| dname := anon_b; dtype := cst_type cb; rarg := rp_nofix; dbody := b |})]
                         | _ => rs
                         end
                  else rs
              end
          | _ => rs
          end
        else rs
    | _ => rs
    end) (rp_apps 100000 t []) rows.
(** all the rows of a program: a memory never read in its functions, then the types its calls give, again in what those make *)
Definition rp_all (Σ : global_env) (mp : modpath) (root : kername) : list rprow :=
  let kns := snd (reach_go 1000 Σ mp root root ([], [])) in
  let r0 := fold_left (fun rs kn =>
              if if in_prog mp (fst kn) then negb (Kername.eqb kn root) else false then
                match body_of Σ kn with
                | Some (tFix [d] 0) =>
                    match dead_slots d with
                    | [] => rs
                    | sl => rs ++ [(tConst kn [], [], sl, mangle kn ^ "__i"%bs, d)]
                    end
                | _ => rs
                end
              else rs) kns [] in
  let r1 := fold_left (fun rs kn => match body_of Σ kn with Some b => if in_prog mp (fst kn) then rp_rows_of Σ mp (mangle kn) b rs else rs | None => rs end) kns r0 in
  let r2 := fold_left (fun (rs : list rprow) (_ : nat) => fold_left (fun a r => rp_rows_of Σ mp "p"%bs (dbody (rp_def r)) a) rs rs) (seq 0 3) r1 in
  (* a definition holding a call read in another form, a memory it hands only to that call now never read: one of its own, or it is read with two memories *)
  fold_left (fun rs kn =>
    if if in_prog mp (fst kn) then negb (Kername.eqb kn root) else false then
      match body_of Σ kn, lookup_env Σ kn with
      | Some (tFix _ _), _ => rs
      | Some b, Some (ConstantDecl cb) =>
          let b' := rp_sub 100000 r2 b in
          if teq 100000 b' b then rs else
          let dn := {| dname := anon_b; dtype := cst_type cb; rarg := rp_nofix; dbody := b' |} in
          match dead_slots dn with
          | [] => rs
          | sl => rs ++ [(tConst kn [], [], sl, mangle kn ^ "__n"%bs, dn)]
          end
      | _, _ => rs
      end
    else rs) kns r2.
(** (step 72) a procedure, a function giving back [unit] and a memory: the memory alone, in its place.  [f args] is [(tt, f' args)] at every argument, by induction *)
Fixpoint um_red (fuel : nat) (Σ : global_env) (mp : modpath) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := um_red fuel Σ mp in
      match t with
      | tApp (tLambda _ _ _ as f) args => go (al_beta args f)
      | tApp (tApp f a1) a2 => go (tApp f (a1 ++ a2))
      | tApp (tLetIn na v ty b) args => tLetIn na v ty (go (mkApps b (map (lift0 1) args)))
      | tApp (tCase ci p c brs) args =>
          tCase ci p c (map (fun br => let k := length (bcontext br) in
                                       {| bcontext := bcontext br; bbody := go (mkApps (bbody br) (map (lift0 k) args)) |}) brs)
      | tApp (tConst kn u) args =>
          if in_prog mp (fst kn) then
            match body_of Σ kn with
            | Some (tFix _ _) | None => t
            | Some b => if Nat.leb (length (fst (lams b))) (length args) then go (al_beta args (al_t 100000 Σ mp b)) else t
            end
          else t
      | tCase ci p c brs =>
          match go c with
          | tConstruct _ k _ =>
              match nth_error brs k with Some br => go (bbody br) | None => t end
          | tApp (tConstruct _ k _) cargs =>
              match nth_error brs k with
              | Some br => go (subst (rev (skipn (ci_npar ci) cargs)) 0 (bbody br))
              | None => t
              end
          | c' => tCase ci p c' brs
          end
      | _ => t
      end
  end.
(** the second part of the function's own call: the call *)
Fixpoint um_snd (fuel self d : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := um_snd fuel self d in
      match t with
      | tApp (tConst k u) [A; B; tApp (tRel i) a] =>
          if Kername.eqb k kn_snd && Nat.eqb i (self + d) then tApp (tRel i) (map go a)
          else tApp (tConst k u) [A; B; tApp (tRel i) (map go a)]
      | tApp f args => tApp (go f) (map go args)
      | tLambda na a b => tLambda na a (um_snd fuel self (S d) b)
      | tLetIn na v a b => tLetIn na (go v) a (um_snd fuel self (S d) b)
      | tCase ci p c brs => tCase ci p (go c) (map (fun br => {| bcontext := bcontext br; bbody := um_snd fuel self (d + length (bcontext br)) (bbody br) |}) brs)
      | _ => t
      end
  end.
Fixpoint um_tr (fuel : nat) (Σ : global_env) (mp : modpath) (self d : nat) (t : term) {struct fuel} : option term :=
  match fuel with
  | O => None
  | S fuel =>
      let go := um_tr fuel Σ mp self in
      match um_red 1000 Σ mp t with
      | tApp (tConstruct _ 0 _) [_; _; _; m] => Some (um_snd 100000 self d m)
      | tApp (tRel i) args as c => if Nat.eqb i (self + d) then Some c else None
      | tCase ci p (tApp (tRel i) args as c) [br] =>
          (* the function's own call taken apart: its memory by a let *)
          if Nat.eqb i (self + d) && Nat.eqb (length (bcontext br)) 2 then
            option_map (fun b => tLetIn anon_b c (tConst kn_mem []) b) (go (S d) (subst [um_tt] 1 (bbody br)))
          else None
      | tCase ci p c brs =>
          match opt_all (map (fun br => go (d + length (bcontext br)) (bbody br)) brs) with
          | Some bs => Some (tCase ci (y_ret p (tConst kn_mem [])) c (map (fun pb : branch term * term => {| bcontext := bcontext (fst pb); bbody := snd pb |}) (combine brs bs)))
          | None => None
          end
      | tLetIn na v ty b => option_map (fun b' => tLetIn na v ty b') (go (S d) b)
      | _ => None
      end
  end.
(** a procedure that is one write or a few, no test: written out where it is called, as any helper *)
Definition um_plain (Σ : global_env) (mp : modpath) (tys : list term) (t : term) : bool :=
  match um_red 1000 Σ mp t with tApp (tConstruct _ 0 _) _ => true | _ => false end.
Fixpoint um_inl (fuel : nat) (Σ : global_env) (mp : modpath) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := um_inl fuel Σ mp in
      match t with
      | tApp (tConst kn u) args =>
          let args' := map go args in
          let dflt := tApp (tConst kn u) args' in
          if in_prog mp (fst kn) then
            match lookup_env Σ kn with
            | Some (ConstantDecl cb) =>
                match cst_body cb with
                | Some (tFix _ _) | None => dflt
                | Some _ =>
                    let ty := al_t 1000 Σ mp (cst_type cb) in
                    if (if teq 1000 (ret_ty ty) um_ty then true else teq 1000 (ret_ty ty) bm_ty) && Nat.eqb (length (removelast (prod_tys ty))) (length args') then
                      match um_red 1000 Σ mp dflt with
                      | tApp (tConstruct _ 0 _) _ as r => r
                      | _ => dflt
                      end
                    else dflt
                end
            | _ => dflt
            end
          else dflt
      | tApp f args => tApp (go f) (map go args)
      | tLambda na a b => tLambda na a (go b)
      | tLetIn na v a b => tLetIn na (go v) a (go b)
      | tCase ci p c brs => tCase ci p (go c) (map (fun br => {| bcontext := bcontext br; bbody := go (bbody br) |}) brs)
      | tFix mfix k => tFix (map (fun d => {| dname := dname d; dtype := dtype d; rarg := rarg d; dbody := go (dbody d) |}) mfix) k
      | _ => t
      end
  end.
(** a function giving back a boolean and a memory *)
Fixpoint bm_snd_fst (fuel self d : nat) (t : term) {struct fuel} : term :=
  match fuel with
  | O => t
  | S fuel =>
      let go := bm_snd_fst fuel self d in
      match t with
      | tApp (tConst k u) [A; B; tApp (tRel i) a] =>
          if Nat.eqb i (self + d) then
            if Kername.eqb k kn_snd then lift0 0 (pf_beta bm_snd [tApp (tRel i) (map go a)])
            else if Kername.eqb k kn_fst then pf_beta bm_fst [tApp (tRel i) (map go a)]
            else tApp (tConst k u) [A; B; tApp (tRel i) (map go a)]
          else tApp (tConst k u) [A; B; tApp (tRel i) (map go a)]
      | tApp f args => tApp (go f) (map go args)
      | tLambda na a b => tLambda na a (bm_snd_fst fuel self (S d) b)
      | tLetIn na v a b => tLetIn na (go v) a (bm_snd_fst fuel self (S d) b)
      | tCase ci p c brs => tCase ci p (go c) (map (fun br => {| bcontext := bcontext br; bbody := bm_snd_fst fuel self (d + length (bcontext br)) (bbody br) |}) brs)
      | _ => t
      end
  end.
Definition bm_pair (v m : term) : term :=
  match y_case_pair with
  | tLambda _ _ (tCase ci _ _ _) =>
      tApp (tConstruct {| inductive_mind := inductive_mind (ci_ind ci); inductive_ind := 0 |} 0 []) [tConst kn_int []; tConst kn_mem []; v; m]
  | _ => v
  end.
Fixpoint bm_tr (fuel : nat) (Σ : global_env) (mp : modpath) (self d : nat) (t : term) {struct fuel} : option term :=
  match fuel with
  | O => None
  | S fuel =>
      let go := bm_tr fuel Σ mp self in
      match um_red 1000 Σ mp t with
      | tApp (tConstruct _ 0 _) [_; _; v; m] =>
          let v' := bm_snd_fst 100000 self d v in
          Some (bm_pair (match v' with
                         | tConstruct _ 0 _ => tInt 1%uint63
                         | tConstruct _ 1 _ => tInt 0%uint63
                         | _ => pf_beta bm_b2i [v']
                         end) (bm_snd_fst 100000 self d m))
      | tApp (tRel i) args as c => if Nat.eqb i (self + d) then Some c else None
      | tCase ci p (tApp (tRel i) args as c) [br] =>
          (* the function's own call taken apart: its boolean the number's test *)
          if Nat.eqb i (self + d) && Nat.eqb (length (bcontext br)) 2 then
            match y_case_pair with
            | tLambda _ _ (tCase cip pp _ _) =>
                option_map (fun b => tCase cip (y_ret pp bm_num) c [{| bcontext := bcontext br; bbody := b |}])
                  (go (d + 2) (subst [pf_beta bm_eq1 [tRel 0]] 1 (lift 1 2 (bbody br))))
            | _ => None
            end
          else None
      | tCase ci p c brs =>
          match opt_all (map (fun br => go (d + length (bcontext br)) (bbody br)) brs) with
          | Some bs => Some (tCase ci (y_ret p bm_num) c (map (fun pb : branch term * term => {| bcontext := bcontext (fst pb); bbody := snd pb |}) (combine brs bs)))
          | None => None
          end
      | tLetIn na v ty b => option_map (fun b' => tLetIn na v ty b') (go (S d) b)
      | _ => None
      end
  end.
Definition um_rows (Σ : global_env) (mp : modpath) (root : kername) (kns : list kername) : list rprow :=
  flat_map (fun kn =>
    if if in_prog mp (fst kn) then negb (Kername.eqb kn root) else false then
      match lookup_env Σ kn with
      | Some (ConstantDecl cb) =>
          let ty := al_t 1000 Σ mp (cst_type cb) in
          if teq 1000 (ret_ty ty) bm_ty then
            let ptys := removelast (prod_tys ty) in
            match cst_body cb with
            | Some (tFix [d] 0) =>
                let '(tys, body) := lams (dbody d) in
                let n := length tys in
                if Nat.eqb n (length ptys) then
                  match bm_tr 1000 Σ mp n 0 body with
                  | Some b' =>
                      [(tConst kn [], [], [rp_bm], mangle kn ^ "__b"%bs,
                        {| dname := dname d; dtype := pis_of tys bm_num; rarg := rarg d; dbody := lams_of tys b' |})]
                  | None => []
                  end
                else []
            | Some (tFix _ _) | None => []
            | Some b =>
                let '(tys, body) := lams b in
                let n := length tys in
                let extra := skipn n ptys in
                let k := length extra in
                let rels := map (fun i => tRel (k - 1 - i)) (seq 0 k) in
                if um_plain Σ mp (tys ++ extra) (mkApps (lift0 k body) rels) then [] else
                match bm_tr 1000 Σ mp 999 0 (mkApps (lift0 k body) rels) with
                | Some b' =>
                    [(tConst kn [], [], [rp_bm], mangle kn ^ "__b__n"%bs,
                      {| dname := anon_b; dtype := pis_of (tys ++ extra) bm_num; rarg := rp_nofix; dbody := lams_of (tys ++ extra) b' |})]
                | None => []
                end
            end
          else
          if teq 1000 (ret_ty ty) um_ty then
            let ptys := removelast (prod_tys ty) in
            match cst_body cb with
            | Some (tFix [d] 0) =>
                let '(tys, body) := lams (dbody d) in
                let n := length tys in
                if Nat.eqb n (length ptys) then
                  match um_tr 1000 Σ mp n 0 body with
                  | Some b' =>
                      [(tConst kn [], [], [rp_um], mangle kn ^ "__u"%bs,
                        {| dname := dname d; dtype := pis_of tys (tConst kn_mem []); rarg := rarg d; dbody := lams_of tys b' |})]
                  | None => []
                  end
                else []
            | Some (tFix _ _) | None => []
            | Some b =>
                let '(tys, body) := lams b in
                let n := length tys in
                let extra := skipn n ptys in
                let k := length extra in
                let rels := map (fun i => tRel (k - 1 - i)) (seq 0 k) in
                if um_plain Σ mp (tys ++ extra) (mkApps (lift0 k body) rels) then [] else
                match um_tr 1000 Σ mp 999 0 (mkApps (lift0 k body) rels) with
                | Some b' =>
                    [(tConst kn [], [], [rp_um], mangle kn ^ "__u__n"%bs,
                      {| dname := anon_b; dtype := pis_of (tys ++ extra) (tConst kn_mem []); rarg := rp_nofix; dbody := lams_of (tys ++ extra) b' |})]
                | None => []
                end
            end
          else []
      | _ => []
      end
    else []) kns.
(** each after what it names *)
Definition rp_topo (Σ : global_env) (rows : list rprow) : list rprow :=
  let names := fun r => consts 10000 (rp_sub 100000 rows (dbody (rp_def r))) [] in
  let is_row := fun k => existsb (fun q => Kername.eqb k (rp_name q)) rows in
  let rd := map (fun r => (r, filter is_row (names r))) rows in
  let fix go (fu : nat) (todo : list (rprow * list kername)) (doneL : list rprow) {struct fu} : list rprow :=
    match fu with
    | O => doneL ++ map fst todo
    | S fu =>
        match todo with
        | [] => doneL
        | _ =>
            let ready := filter (fun e : rprow * list kername =>
                           forallb (fun k => if Kername.eqb k (rp_name (fst e)) then true else existsb (fun q => Kername.eqb k (rp_name q)) doneL) (snd e)) todo in
            match ready with
            | [] => doneL ++ map fst todo
            | _ => go fu (filter (fun e : rprow * list kername => negb (existsb (fun q => Kername.eqb (rp_name (fst q)) (rp_name (fst e))) ready)) todo)
                         (doneL ++ map fst ready)
            end
        end
    end in
  go 100 rd [].
(** (step 73) the kit's functions [pm_table] names: a program that uses a primitive does not name them, so they are not in what Rocq quotes of it *)
Definition pm_kit : global_env :=
  ltac:(run_template_program (tmQuoteRecTransp (fun x y : PrimInt63.int => (KQ.KQRun.kq_h0 x, KQ.KQRun.kq_t0 x, KQ.KQRun.kq_mh x y, KQ.KQRun.kq_d21 x y x)) false)
          (fun q => let r := eval vm_compute in (fst q) in exact r)).
Definition pm_add (Σ : global_env) : global_env :=
  fold_left (fun S e => match lookup_env S (fst e) with
                        | Some _ => S
                        | None => {| universes := universes S; declarations := e :: declarations S; retroknowledge := retroknowledge S |}
                        end) (declarations pm_kit) Σ.
Definition y_all (Σ : global_env) (mp : modpath) (root : kername) : global_env * bool :=
  let rows := rp_topo Σ (rp_all Σ mp root ++ um_rows (conv_all Σ mp) mp root (snd (reach_go 1000 Σ mp root root ([], [])))) in
  (* (step 69) what is made, its own calls of what is in their place written too; the statements *)
  let S0 := fold_left (fun S2 r =>
              let d' := rp_def r in
              add_decl (add_decl S2 (rp_name r) (dtype d')
                         (if Nat.eqb (rarg d') rp_nofix then y_red 100000 (rp_sub 100000 rows (dbody d'))
                          else tFix [{| dname := dname d'; dtype := dtype d'; rarg := rarg d'; dbody := y_red 100000 (rp_sub 100000 rows (dbody d')) |}] 0))
                       (rq_name r) (tSort sProp) (rp_stmt r)) rows Σ in
  fold_left (fun st kn =>
    let '(S1, ch) := st in
    if existsb (fun r : rprow => match r with (tConst k _, _, sl, _, _) => if if rp_is_um sl then true else rp_is_bm sl then Kername.eqb k kn else false | _ => false end) rows then st else
    if in_prog mp (fst kn) then
      match lookup_env S1 kn with
      | Some (ConstantDecl cb) =>
          match cst_body cb with
          | Some b00 =>
              (* (step 68) a program's name for a type, read as its definition, the same up to delta *)
              let ty0 := al_t 1000 Σ mp (cst_type cb) in
              let b0x := mo_t 100000 Σ mp (lu_t 100000 Σ (al_t 100000 Σ mp b00)) in
              (* (step 69) its calls of what is read in another form *)
              let b0 := y_red 100000 (rp_sub 100000 rows (um_inl 100000 Σ mp b0x)) in
              let r0 := match rows with [] => false | _ => negb (teq 100000 b0 b0x) end in
              let c1 := if teq 100000 ty0 (cst_type cb) then negb (teq 100000 b0 b00) else true in
              (* (step 63) a binder's type a redex, from a motive, a cast: the same up to beta *)
              let c0 := if c1 then true else ty_has 1000 b0 in
              let b1 := if ty_has 1000 b0 then ty_beta 1000 b0 else b0 in
              let p00 := pm_has b1 in
              let b := if p00 then pm_sub 100000 [] [] b1 else b1 in
              let p0 := if p00 then true else r0 in
              (* (step 68) a function chosen by a match, applied *)
              let f0 := if p0 then false else fc_has 100000 b in
              let S1 := if p00 then pm_add S1 else S1 in
              let wy (f' : term) := (add_decl (add_decl S1 (copy_mp, snd kn ^ "__wy"%bs) ty0 f') kn ty0 f', true) in
              match b with
              | tFix [d] 0 =>
                  if negb (y_on_nat d) then st else
                  match y_fix d with
                  | Some f' => wy f'
                  | None => if p0 then wy b else if c0 then (add_decl S1 kn ty0 b, true) else st
                  end
              | _ =>
                  if p0 then wy (y_nf (ret_ty ty0) b)
                  else if f0 then wy (y_nf (ret_ty ty0) b)
                  else if c0 then (add_decl S1 kn ty0 b, true) else st
              end
          | None => st
          end
      | _ => st
      end
    else st) (snd (reach_go 1000 Σ mp root root ([], []))) (S0, match rows with [] => false | _ => true end).
(** the rows of those: the head of the environment, where [y_all] put them *)
Fixpoint ends_wy (s : string) : bool :=
  if String.eqb s "__wy"%bs then true else
  match s with String.EmptyString => false | String.String _ r => ends_wy r end.
Definition y_rows (Σ : global_env) : copytab :=
  flat_map (fun e =>
    if eq_mp (fst (fst e)) copy_mp then
      if ends_wy (snd (fst e)) then
        match snd e with
        | ConstantDecl cb => match cst_body cb with Some b => [(fst e, ([], []), fst e, b)] | None => [] end
        | _ => []
        end
      else []
    else []) (rev (firstn 200 (declarations Σ))).
Definition reify_prog2c (lo : bool) (bt : kername -> option Z) (chk : bool) (p : program) : option (list (kername * sig * fbody) * list (string * term)) :=
  match p with
  | (Σ000, tConst root _) =>
      let mp := fst root in
      let '(Σ00, ltp0) := pf_all Σ000 mp root in
      let ltp := y_rows Σ000 ++ ltp0 in
      let '(Σ0, lt0) := if lo then lift_ops Σ00 mp root else (Σ00, []) in
      let kns0 := reach 1000 Σ0 mp root root [] in
      let '(Σ, kns, lts1) := lift_all (float_all Σ0 kns0) mp kns0 in
      let lts := ltp ++ lt0 ++ lts1 in
      let hb := helper_of Σ mp kns in
      let rt := rtab_of Σ hb kns in
      (* a local fixpoint in a definition of the program's file: its copies are looked for as a template's are (step 31) *)
      let lf := existsb (fun e => if (if in_prog mp (fst (fst e)) then true else lib_open (fst e)) then
                                    match snd e with
                                    | ConstantDecl cb => match cst_body cb with Some b => lfix_body b | None => false end
                                    | _ => false end else false) (declarations Σ) in
      let tms := (if lf then [kn_lfix] else []) ++ filter (is_tmpl Σ mp) kns in
      let th := tmpl_helpers Σ hb tms kns in
      let st := fold_left (fun st kn =>
                  match st with
                  | None => None
                  | Some _ =>
                      if existsb (Kername.eqb kn) tms then st else
                      let st := match tms, body_of Σ kn with
                                | _ :: _, Some b => fold_left (fun st s => ensure 50 Σ mp hb rt th tms bt chk s st) (rev (sites 1000 Σ tms hb th [] b [])) st
                                | _, _ => st
                                end in
                      match st with
                      | Some (es, tbl) =>
                          match body_of Σ kn with
                          | Some (tFix mfix k) =>
                              if Nat.ltb 1 (length mfix) then
                                (* a member of a mutual block (step 45): its part, after the parts it calls, each read once *)
                                let g := map (mcalls (length mfix)) mfix in
                                add_member Σ (fst kn) hb rt bt chk mfix (part_of g (length mfix) k) k (ensure_part 100 Σ (fst kn) hb rt bt chk mfix g k (Some (es, tbl)))
                              else read_add Σ hb (tc_of Σ mp tbl) rt kn bt chk es tbl
                          | _ => read_add Σ hb (tc_of Σ mp tbl) rt kn bt chk es tbl
                          end
                      | None => None
                      end
                  end) kns (Some ([], lts)) in
      option_map (fun et => (fst et, map (fun e => (snd (snd (fst e)), real_copies 1000 (MPfile (mp_file mp)) (snd e))) (snd et))) st
  | _ => None
  end.
(** counter bounds worked out from the call graph (step 34): from the entry down -- the functions come callees first -- each
    function's bound above the largest counter any caller gives it, at least the smallest ([own_bound]) or, [small] (step 40),
    at least 1 for a function that is not the entry; a bound above 2^62 is refused by [wf_f] *)
Fixpoint upd_max (l : list Z) (f : nat) (v : Z) : list Z :=
  match l, f with [], _ => [] | x :: r, O => Z.max x v :: r | x :: r, S f => x :: upd_max r f v end.
Fixpoint find_kn (kn : kername) (l : list (kername * sig * fbody)) (i : nat) : option nat :=
  match l with [] => None | e :: r => if Kername.eqb kn (fst (fst e)) then Some i else find_kn kn r (S i) end.
Definition bounds_tab (small : bool) (es : list (kername * sig * fbody)) : kername -> option Z :=
  let n := length es in
  let sns := map (fun e : kername * sig * fbody => sn (snd (fst e))) es in
  let wss := map (fun e : kername * sig * fbody => wts_of (sn (snd (fst e))) (snd e)) es in
  let need f l := match nth f wss [] with [] => (fold_right Z.max 0 l + 1)%Z | vs => (wmax vs l + 1)%Z end in
  let bs := fold_left (fun bs i =>
              let Bi := nth i bs own_bound in
              match nth_error es i with
              | Some e => fold_left (fun bs' fc => upd_max bs' (fst fc) (need (fst fc) (snd fc))) (cl_calls Bi (sn (snd (fst e))) (snd e)) bs
              | None => bs
              end) (rev (seq 0 n)) (map (fun i => if Nat.eqb (S i) n then match nth i wss [] with [] => own_bound | ws => own_w (nth i sns O) ws end
                                             else if small then 1%Z else own_bound) (seq 0 n)) in
  fun kn => match find_kn kn es 0 with Some i => Some (nth i bs own_bound) | None => None end.
(** the program: read with the bounds of the index and the smallest own bound; failing that, read without the check, the bounds
    worked out from its calls, and read again with them (step 34); failing that, with the bounds worked out from 1 (step 40) *)
Definition reify_prog2b := reify_prog2c false.
Definition reify_prog2m (lo : bool) (p : program) : option (list (kername * sig * fbody) * list (string * term)) :=
  match reify_prog2c lo (fun _ => None) true p with
  | Some r => Some r
  | None => match reify_prog2c lo (fun _ => None) false p with
            | Some (es, _) => match reify_prog2c lo (bounds_tab false es) true p with
                              | Some r => Some r
                              | None => reify_prog2c lo (bounds_tab true es) true p
                              end
            | None => None
            end
  end.
(** (step 54) a program read as it stands, its C what it was; failing that, with its operands that write made functions *)
Definition reify_prog2 (p : program) : option (list (kername * sig * fbody) * list (string * term)) :=
  match reify_prog2m false p with
  | Some r => Some r
  | None =>
      match p with
      | (Σ, tConst root _) =>
          match match snd (lift_ops (fst (pf_all Σ (fst root) root)) (fst root) root) with
                | [] => None
                | _ => reify_prog2m true p
                end with
          | Some r => Some r
          | None =>
              (* (step 61) *)
              match y_all Σ (fst root) root with
              | (Σy, true) =>
                  match reify_prog2m false (Σy, tConst root []) with
                  | Some r => Some r
                  | None => reify_prog2m true (Σy, tConst root [])
                  end
              | _ => None
              end
          end
      | _ => None
      end
  end.
Definition is_kq4 (s : string) : bool :=
  match s with
  | String.String a (String.String b (String.String c (String.String d _))) =>
      if Byte.eqb a "_"%byte then if Byte.eqb b "_"%byte then if Byte.eqb c "k"%byte then Byte.eqb d "q"%byte else false else false else false
  | _ => false
  end.
Fixpoint has_kq (s : string) : bool :=
  match s with
  | String.EmptyString => false
  | String.String _ r => if is_kq4 s then true else has_kq r
  end.
(** the record types of the program as it was read *)
Definition rec_info2 (p0 : program) (r : option (list (kername * sig * fbody) * list (string * term))) : list (string * string * nat * string) :=
  let lo := match r with Some (_, mts) => existsb (fun q => has_kq (fst q)) mts | None => false end in
  let p := match r, p0 with
           | Some (_, mts), (Σ, tConst root u) =>
               if existsb (fun q => ends_wy (fst q)) mts then (fst (y_all Σ (fst root) root), tConst root u) else p0
           | _, _ => p0
           end in
  let wf := match p with (Σ, _) => match lookup_env Σ kn_fix_sub with Some _ => true | None => pf_has_iter Σ end end in
  if (if lo then true else wf) then
    match p with
    | (Σ000, tConst root _) =>
        let mp := fst root in
        let Σ00 := fst (pf_all Σ000 mp root) in
        let Σ0 := if lo then fst (lift_ops Σ00 mp root) else Σ00 in
        let kns0 := reach 1000 Σ0 mp root root [] in
        let '(Σ, kns, _) := lift_all (float_all Σ0 kns0) mp kns0 in
        let rt := rtab_of Σ (helper_of Σ mp kns) kns in map (rec_text Σ rt) rt
    | _ => []
    end
  else rec_info p.
Definition reify_prog (p : program) : option (list (kername * sig * fbody)) := option_map fst (reify_prog2 p).
Fixpoint strip_terminate (s : string) : option string :=
  if String.eqb s "_terminate"%bs then Some ""%bs else
  match s with
  | String.EmptyString => None
  | String.String c r => option_map (String.String c) (strip_terminate r)
  end.
(** whether the program holds a [Function] of the program's, whose [f_terminate] is what names it *)
Definition fn_bases (p : program) : list (modpath * string) :=
  flat_map (fun e => match strip_terminate (snd (fst e)) with
                     | Some b => if lib_file (mp_file (fst (fst e))) then [] else [(fst (fst e), b)]
                     | None => []
                     end) (declarations (fst p)).
Definition has_function (p : program) : bool := match fn_bases p with [] => false | _ => true end.
(** what a [Qed] hides of a [Function]: its plain functional and the statement of its calls' measures, and what those name.  Asked for only by a program with one: a bind on the whole quote costs a tenth of a second (measured on a kernel's program) *)
Definition quote_function (p : program) : TemplateMonad program :=
  match fn_bases p with
  | [] => ret p
  | bases =>
      Σ' <- monad_fold_left (fun S k =>
              cb <- tmQuoteConstant (fst k, snd k ^ "_tcc"%bs) false ;;
              F <- tmUnquote (tConst (fst k, snd k ^ "_F"%bs) []) ;;
              p2 <- tmQuoteRecTransp (my_projT2 F) false ;;
              T <- tmUnquote (tConst (fst k, snd k ^ "_tcc"%bs) []) ;;
              p3 <- tmQuoteRecTransp (my_projT2 T) false ;;
              ret {| universes := universes S;
                     declarations := ((fst k, snd k ^ "_tcc"%bs), ConstantDecl cb) :: declarations S ++ declarations (fst p2) ++ declarations (fst p3);
                     retroknowledge := retroknowledge S |}) bases (fst p) ;;
      (* the mark [pf_all] looks for, which the proof that held it would otherwise hide *)
      cb <- tmQuoteConstant kn_iter false ;;
      ret ({| universes := universes Σ'; declarations := (kn_iter, ConstantDecl cb) :: declarations Σ'; retroknowledge := retroknowledge Σ' |}, snd p)
  end.
(** the block functions' meanings (step 45) are made where the program's record types are known: [blkT] at their instance;
    the other meanings where the program is *)
Definition is_blk_m (t : term) : bool := match t with tApp (tConst kn _) _ => Kername.eqb kn kn_blkT | _ => false end.
Definition plain_mts (l : list (string * term)) : list (string * term) := filter (fun p => negb (is_blk_m (snd p))) l.
Definition blk_mts (inst : term) (l : list (string * term)) : list (string * term) :=
  map (fun p => (fst p, match snd p with tApp f (_ :: rest) => tApp f (inst :: rest) | t => t end)) (filter (fun p => is_blk_m (snd p)) l).
Definition meaning_of (l : list (string * term)) (nm : string) : term :=
  match List.find (fun q => fst q == nm) l with Some q => snd q | None => tVar "none"%bs end.

(** for kitc.py: each function the reifier made, and the constant it is a copy or a wrapper of (step 51) *)
Fixpoint head_const (t : term) : option kername :=
  match t with
  | tLambda _ _ b | tProd _ _ b => head_const b
  | tApp (tInd _ _) [_; a; _] => head_const a
  | tApp f _ => head_const f
  | tConst kn _ => Some kn
  | _ => None
  end.
Definition mts_info (l : list (string * term)) : list (string * string) :=
  map (fun p => (fst p, match head_const (snd p) with Some kn => string_of_kername kn | None => ""%bs end)) l.
(** for kitc.py: the program's functions that are one fixpoint, not a member of a block (step 51) *)
Definition fix1_info (p : program) : list string :=
  match p with
  | (Σ, tConst root _) =>
      map fn_text (filter (fun kn => match body_of Σ kn with Some (tFix [_] _) => true | _ => false end)
                          (reach 1000 Σ (fst root) root root []))
  | _ => []
  end.

(* ---------------------------------------------------------------- why a program is not read *)

Definition add_s (x : string) (l : list string) : list string := if existsb (fun y => y == x) l then l else l ++ [x].

(** the constants the syntax reads: the integer operations and comparisons, [rd], [upd], the program's functions *)
Definition known_const (fns : list kername) (kn : kername) : bool :=
  (eq_mp (fst kn) prim_mp && (match binop_v (snd kn), cmp_v (snd kn) with None, None => false | _, _ => true end))
  || Kername.eqb kn kn_rd || Kername.eqb kn kn_upd || Kername.eqb kn kn_rd32 || Kername.eqb kn kn_upd32 || Kername.eqb kn kn_rd8 || Kername.eqb kn kn_upd8
  || Kername.eqb kn kn_kq_nat || existsb (Kername.eqb kn) fns || Kername.eqb kn kn_ksize || Kername.eqb kn kn_w64_op
  || existsb (fun e => Kername.eqb (fst (fst e)) kn) hw_table || existsb (fun e => Kername.eqb (fst (fst e)) kn) hwf_table
  || Kername.eqb kn kn_andb || Kername.eqb kn kn_orb || Kername.eqb kn kn_negb
  || match ncmp_v kn with Some _ => true | None => false end || Kername.eqb kn kn_nat_pred || Kername.eqb kn kn_nat_add
  || Kername.eqb kn kn_c_min || Kername.eqb kn kn_c_max || Kername.eqb kn kn_c_sub || Kername.eqb kn kn_c_div2
  || Kername.eqb kn kn_c_mul || Kername.eqb kn kn_c_div || Kername.eqb kn kn_c_mod || Kername.eqb kn kn_c_even || Kername.eqb kn kn_c_odd
  || Kername.eqb kn kn_zton || Kername.eqb kn kn_zofn || Kername.eqb kn kn_s2z || Kername.eqb kn kn_u2z || Kername.eqb kn kn_ofz
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
                            || match ncmp_v kn with Some _ => true | None => false end
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
    ["read, but not well formed: a recursive call given counters that no weights keep from growing (a counter grown by"
     ^ " itself or by the first counter: it would have no bound, or whose weighted sums can pass 2^63 at the counters given), a call given fewer"
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
            | tFix [d] _ => (""%bs, dbody d, dtype d)
            | tFix mfix k => (if mixed_part mfix k then "a mutual block whose members that call each other give back different types"
                              else "mutual recursion", b, cst_type cb)
            | _ => (""%bs, b, cst_type cb)
            end in
          let '(tys, inner) := lams body in
          let hs := helpers_in 50 hb inner [] in      (* the helpers written out in it: each looked at once *)
          let texts := inner :: flat_map (fun k => match hb k with Some b => [b] | None => [] end) hs in
          let nohb := fun _ : kername => @None term in
          let odd := fold_left (fun a t => if is_ty kn_int t || is_ty kn_mem t || is_nat t then a else add_s (head_name t) a)
                               (filter (fun t => negb (is_bool t) && match rindex t rt 0 with Some _ => false | None => true end) tys ++ [ret_ty ty]) [] in
          let sigr := match read_sig rt (map (fun i => nth i tys (tRel 0)) (canon_perm tys (match b with tFix [d] _ => Some (rarg d) | _ => None end)))
                                     (ret_ty ty), odd with
                      | Some _, _ => []
                      | None, [] => ["two memories as parameters"]
                      | None, x :: r => ["a parameter or result of type " ^ fold_left (fun a y => a ^ ", " ^ y) r x]
                      end in
          let r0 := if rec == "" then sigr else rec :: sigr in
          let r0 := if two_mems tys then add_s "two memories as parameters, not handed the same memory and one not left unread (two versions of the memory both used)" r0 else r0 in
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
          (* step 51: nothing to compile and nothing to compare with: it has no text in the kernel *)
          let r4 := fold_left (fun a k => if lib_file (mp_file (fst k)) then a else
                                          match lookup_env Σ k with
                                          | Some (ConstantDecl c) =>
                                              match cst_body c with
                                              | None => add_s (snd k ^ " has no body in Rocq's kernel (an Axiom, a Parameter, a Variable, a function behind a module's : -- <: keeps its body)") a
                                              | Some _ => a
                                              end
                                          | _ => a
                                          end)
                              (fold_left (fun a t => consts 10000 t a) texts []) r4 in
          let r4 := if existsb (Kername.eqb kn_d21) (fold_left (fun a t => consts 10000 t a) texts [])
                    then add_s "diveucl_21 a b c with nothing showing a < c: Rocq's axioms say nothing there, so nothing says what it computes (Rocq-C-solution.md 0.5, fourth reason); test a <? c around it" r4 else r4 in
          let r4 := if existsb (Kername.eqb kn_c_pow) (fold_left (fun a t => consts 10000 t a) texts [])
                    then add_s "a power of a counter: a number that may need more than a word (Rocq-C-solution.md 0.5, second reason)" r4 else r4 in
          let r4 := if existsb (Kername.eqb kn_c_mul) (fold_left (fun a t => consts 10000 t a) texts [])
                    then add_s "a product of two counters, neither written in the program: a number that may need more than a word (Rocq-C-solution.md 0.5, second reason)" r4 else r4 in
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
      (* a local fixpoint in a definition of the program's file: its copies are looked for as a template's are (step 31) *)
      let lf := existsb (fun e => if (if in_prog mp (fst (fst e)) then true else lib_open (fst e)) then
                                    match snd e with
                                    | ConstantDecl cb => match cst_body cb with Some b => lfix_body b | None => false end
                                    | _ => false end else false) (declarations Σ) in
      let tms := (if lf then [kn_lfix] else []) ++ filter (is_tmpl Σ mp) kns in
      let th := tmpl_helpers Σ hb tms kns in
      let '(_, _, _, out) :=
        fold_left (fun '(es, tbl, bad, out) kn =>
          if existsb (Kername.eqb kn) tms then (es, tbl, bad, out) else
          let ss := match tms, body_of Σ kn with _ :: _, Some b => rev (sites 1000 Σ tms hb th [] b []) | _, _ => [] end in
          match fold_left (fun st s => ensure 50 Σ mp hb rt th tms (fun _ => None) true s st) ss (Some (es, tbl)) with
          | None =>
              let tr := flat_map (fun s => filter (fun r => negb (r == "a parameter or result of type a function"))
                                               (why_fun Σ hb (tc_of Σ mp tbl) rt kns bad (callees_of es) (fst (fst s)))) ss in
              (es, tbl, bad ++ [kn], out ++ [(snd kn, "gives functions to a recursive function whose copy for them is not read" :: tr)])
          | Some (es', tbl') =>
              match read_add Σ hb (tc_of Σ mp tbl') rt kn (fun _ => None) true es' tbl' with
              | Some (es2, tbl2) => (es2, tbl2, bad, out)
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
         (fn_text kn, sn g, kletters (sk g) ^ (if sp g then "p" else ""), sm g, sr g, sw g, match sq g with Some (KRec i) => rletter i | Some KBool => "B"%bs | Some KNum => "P"%bs | None => ""%bs end,
          sb g, sv g)) l.

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

(* a counter grown at every round of a recursion: no bound of each counter holds it; read with weights (step 37), the weighted
   sum of its counters below its bound -- the entry's own, each counter at the smallest bound's value *)
Definition grow_src := ltac:(run_template_program (tmQuoteRec grow)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd (fst x)) grow_src = [mksig8 2 (nk 1) false false false None (Some (own_w 2 (map lpoly [[1; 0]; [1; 1]]%nat))) (map lpoly [[1; 0]; [1; 1]]%nat)]).
Definition grow_Pr := mkprog (funs_of 0 grow_src) [].
Time Lemma grow_ok_r : callee_ok grow_Pr (gid1 0) (own_w 2 (map lpoly [[1; 0]; [1; 1]]%nat)) (sig_at grow_src 0) grow.
Proof. Time exact_no_check (compile_f_ok grow_Pr [] gid1 0 (sig_at grow_src 0) (body_at grow_src 0) eq_refl eq_refl (no_callees grow_Pr gid1) eq_refl eq_refl). Time Qed.

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
(* a let of [S n] over a variable: refused at step 9, read since step 35 (the let's counter carries its own bound) *)
Definition lcbad (n : nat) (a : i63) : i63 := let w := S n in c_inner w a.
Definition lcbad_src := ltac:(run_template_program (tmQuoteRec lcbad)
  (fun q => let r := eval vm_compute in (reify_prog q) in exact r)).
Check (eq_refl : option_map (fun l => map (fun x => snd x) l) lcbad_src =
  option_map (fun l => map (fun x => snd x) l) lcbad_src).
Check (eq_refl : match lcbad_src with Some l => body_at l (Nat.pred (length l)) | None => FPlain (SInt 0) end =
  FPlain (SLetC (CS (CVar 0)) (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil)))).

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
  Time exact_no_check (compile_f_okr ruse_Pr [] gid1 0 0 (nk 1) false (fr0 (body_at ruse_src 0)) (fr1 (body_at ruse_src 0)) None [] ruse_c0
    eq_refl eq_refl (no_callees ruse_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma ruse_ok1 : callee_ok ruse_Pr (gid1 1) (cbz 1) (sig_at ruse_src 1) ruse_c1.
Proof.
  Time exact_no_check (compile_f_okr ruse_Pr [existT ftype (sig_at ruse_src 0) ruse_c0] gid1 1 0 (nk 1) false
    (fr0 (body_at ruse_src 1)) (fr1 (body_at ruse_src 1)) None [] ruse_c1 eq_refl eq_refl
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
  Time exact_no_check (compile_f_okr rw_Pr [] gid1 0 0 (nk 1) false (fr0 (body_at rw_src 0)) (fr1 (body_at rw_src 0)) None [] rw_c0
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
  Time exact_no_check (compile_f_okrx rtuse_Pr [] gid1 0 0 (nk 2) (fx0 (body_at rtuse_src 0)) (fx1 (body_at rtuse_src 0)) None [] rtuse_c0
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
  mkrecs (fun _ => (i63 * i63)%type) (fun _ => mkrops 2 None (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end)) (fun _ => (0%uint63, 0%uint63)).
#[local] Instance rpair_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
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
  mkrecs (fun _ => rst) (fun _ => mkrops 2 None (fun l => mkrst (nth 0 l 0%uint63) (nth 1 l 0%uint63)) (fun P v k => match v with mkrst a b => k [a; b] end)) (fun _ => mkrst 0%uint63 0%uint63).
#[local] Instance rst_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
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
  Time exact_no_check (compile_f_okr rcap_Pr [] gid1 0 0 [KNum; KNum; KNum] true (fr0 (body_at rcap_src 0)) (fr1 (body_at rcap_src 0)) None [] rcap_c0
    eq_refl eq_refl (no_callees rcap_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma rcap_ok1 : callee_ok rcap_Pr (gid1 1) (cbz 1) (sig_at rcap_src 1) rcap_c1.
Proof.
  Time exact_no_check (compile_f_okr rcap_Pr [existT ftype (sig_at rcap_src 0) rcap_c0] gid1 1 0 [KNum; KNum; KNum] true
    (fr0 (body_at rcap_src 1)) (fr1 (body_at rcap_src 1)) None [] rcap_c1 eq_refl eq_refl
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
  [(mksig 1 [KNum; KNum; KNum] true false false (Some (KRec 0)),
    FRecR (BRet (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))))
      (BLet (SRd (SInt 0) (SVar 2)) (BRec CNil (SCons (SOp Badd (SVar 3) (SInt 1))
         (SCons (SIf Clt (SVar 0) (SVar 2) (SVar 0) (SVar 2)) (SCons (SIf Clt (SVar 1) (SVar 0) (SVar 0) (SVar 1)) SNil))))));
   (mksig 1 [] false false false (Some (KRec 0)),
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
  mkrecs (fun _ => (i63 * i63)%type) (fun _ => mkrops 2 None (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end)) (fun _ => (0%uint63, 0%uint63)).
#[local] Instance rpret_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
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
  mkrecs (fun _ => rspan) (fun _ => mkrops 2 None (fun l => mkrspan (nth 0 l 0%uint63) (nth 1 l 0%uint63)) (fun P v k => match v with mkrspan a b => k [a; b] end)) (fun _ => mkrspan 0%uint63 0%uint63).
#[local] Instance rrret_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
Definition rrret_Pr := mkprog (funs_of 0 rrret_src) [].
Time Lemma rscan_ok : callee_ok rrret_Pr (gid1 0) (cbz 0) (sig_at rrret_src 0) rscan.
Proof. Time exact_no_check (@compile_f_ok rrret_recs rrret_laws rrret_Pr [] gid1 0 (sig_at rrret_src 0) (body_at rrret_src 0) eq_refl eq_refl (no_callees rrret_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rrounds_ok : callee_ok rrret_Pr (gid1 1) (cbz 1) (sig_at rrret_src 1) rrounds.
Proof.
  Time exact_no_check (@compile_f_ok rrret_recs rrret_laws rrret_Pr [existT ftype (sig_at rrret_src 0) rscan] gid1 1 (sig_at rrret_src 1) (body_at rrret_src 1)
    eq_refl eq_refl (all_ok_callees rrret_Pr gid1 [existT ftype (sig_at rrret_src 0) rscan] (conj rscan_ok Logic.I)) eq_refl eq_refl).
Time Qed.
End RRret.

(* linearity: a memory written after a newer one was made and read has no tree (a read of it goes first, step 50) *)
Definition dup (s : mem) : mem := let s2 := KQ.KQRun.upd 0 0 1 s in KQ.KQRun.upd 0 1 (KQ.KQRun.rd 0 0 s2) s.
Definition dup_src := ltac:(run_template_program (tmQuoteRec dup)
  (fun q => let r := eval vm_compute in (reify_top q) in exact r)).
Check (eq_refl : dup_src = None).
Definition dup2 (s : mem) : mem := let s2 := KQ.KQRun.upd 0 0 1 s in KQ.KQRun.upd 0 1 (KQ.KQRun.rd 0 0 s) s2.
Definition dup2_src := ltac:(run_template_program (tmQuoteRec dup2)
  (fun q => let r := eval vm_compute in (reify_top q) in exact r)).
Check (eq_refl : match dup2_src with Some _ => true | None => false end = true).

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
  mkrecs (fun _ => KQ.KQRun.u64) (fun _ => mkrops 2 None (fun l => KQ.KQRun.mk_u64 (nth 0 l 0%uint63) (nth 1 l 0%uint63))
                     (fun P v k => match v with KQ.KQRun.mk_u64 a b => k [a; b] end)) (fun _ => KQ.KQRun.mk_u64 0%uint63 0%uint63).
#[local] Instance ru64_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
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
MetaRocq Run (tmMkDefinition "qblk"%bs (meaning_of (snd qmut_res) "KQC'_KQRReify'_qping__cblk"%bs)).
Definition qmut_Pr := mkprog (funs_of 0 qmut_src) [].
Time Lemma qblk_ok : callee_ok qmut_Pr (gid1 0) (cbz 0) (sig_at qmut_src 0) qblk.
Proof.
  Time exact_no_check (compile_f_okr qmut_Pr [] gid1 0 1 (nk 2) true (fr0 (body_at qmut_src 0)) (fr1 (body_at qmut_src 0)) None [] qblk
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
  mkrecs (fun _ => (i63 * i63)%type) (fun _ => mkrops 2 None (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end)) (fun _ => (0%uint63, 0%uint63)).
#[local] Instance rbp_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
Definition rbp_Pr := mkprog (funs_of 0 rbp_src) [].
Time Lemma rbp_ok : callee_ok rbp_Pr (gid1 0) (cbz 0) (sig_at rbp_src 0) rbp.
Proof.
  Time exact_no_check (@compile_f_ok rbp_recs rbp_laws rbp_Pr [] gid1 0 (sig_at rbp_src 0) (body_at rbp_src 0) eq_refl eq_refl
    (no_callees rbp_Pr gid1) eq_refl eq_refl).
Time Qed.
End RBP.

(* ---------------------------------------------------------------- lets read by zeta (step 20) *)
(* a let binding a function (the function written out at its calls) and a dead memory let (dropped) *)
Definition rzl (a b : i63) : i63 := let g := fun x => PrimInt63.add x b in PrimInt63.mul (g a) (g b).
Definition rzd (a b : i63) (s : mem) : mem := let t := KQ.KQRun.upd 0 a b s in KQ.KQRun.upd 0 b a s.
Definition rzl_src := ltac:(run_template_program (tmQuoteRec rzl)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition rzd_src := ltac:(run_template_program (tmQuoteRec rzd)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) rzl_src = [FPlain (SOp Bmul (SOp Badd (SVar 1) (SVar 0)) (SOp Badd (SVar 0) (SVar 0)))]).
Check (eq_refl : map (fun x => snd x) rzd_src = [FPlainM (MUpd (SInt 0) (SVar 0) (SVar 1) MCur)]).
Definition rz_Pr := mkprog (funs_of 0 rzl_src ++ funs_of 1 rzd_src) [].
Time Lemma rzl_ok : callee_ok rz_Pr (gid1 0) (cbz 0) (sig_at rzl_src 0) rzl.
Proof. Time exact_no_check (compile_f_ok rz_Pr [] gid1 0 (sig_at rzl_src 0) (body_at rzl_src 0) eq_refl eq_refl (no_callees rz_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma rzd_ok : callee_ok rz_Pr (gid1 1) (cbz 1) (sig_at rzd_src 0) rzd.
Proof.
  Time exact_no_check (compile_f_ok rz_Pr [existT ftype (sig_at rzl_src 0) rzl] gid1 1 (sig_at rzd_src 0) (body_at rzd_src 0) eq_refl eq_refl
    (all_ok_callees rz_Pr gid1 [existT ftype (sig_at rzl_src 0) rzl] (conj rzl_ok Logic.I)) eq_refl eq_refl).
Time Qed.

(* ---------------------------------------------------------------- records chosen by a test or built from a record taken apart (step 21) *)
(* the construct table's shapes: a helper giving a pair chosen by a test, and one swapping a pair it takes apart, each
   written out where it is used and the pair taken apart there *)
Definition rq_pick (a b : i63) : i63 * i63 := if PrimInt63.ltb a b then (a, b) else (b, a).
Definition rq_swap (a b : i63) : i63 * i63 := match (PrimInt63.add a b, a) with (x, y) => (y, x) end.
Definition rq (a b : i63) : i63 :=
  PrimInt63.add (let '(p, q) := rq_pick a b in PrimInt63.sub q p) (let '(x, y) := rq_swap a b in PrimInt63.sub x y).
Definition rq_src := ltac:(run_template_program (tmQuoteRec rq)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Eval vm_compute in map (fun x => snd x) rq_src.
Section RQ.
#[local] Instance rq_recs : RecTypes | 0 :=
  mkrecs (fun _ => (i63 * i63)%type) (fun _ => mkrops 2 None (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end)) (fun _ => (0%uint63, 0%uint63)).
#[local] Instance rq_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
Definition rq_Pr := mkprog (funs_of 0 rq_src) [].
Time Lemma rq_ok : callee_ok rq_Pr (gid1 0) (cbz 0) (sig_at rq_src 0) rq.
Proof.
  Time exact_no_check (@compile_f_ok rq_recs rq_laws rq_Pr [] gid1 0 (sig_at rq_src 0) (body_at rq_src 0) eq_refl eq_refl
    (no_callees rq_Pr gid1) eq_refl eq_refl).
Time Qed.
End RQ.

(* ---------------------------------------------------------------- booleans chosen by a test or a counter's match (step 22) *)
(* the construct table's shapes: a helper giving a boolean chosen by a test (of comparisons, or of calls of another helper),
   or by a match on its counter, written out where it is tested *)
Definition rbh (a b : i63) : bool := PrimInt63.ltb a b.
Definition rbt (n : nat) (a b : i63) : bool := if PrimInt63.ltb a b then true else false.
Definition rbc (n : nat) (a b : i63) : bool := if PrimInt63.ltb a b then rbh a b else rbh b a.
Definition rbm (n : nat) (a b : i63) : bool := match n with O => true | S _ => false end.
Definition rbu (n : nat) (a b : i63) : i63 :=
  PrimInt63.add (PrimInt63.add (if rbt n a b then 1 else 0) (if rbc n a b then 2 else 0)) (if rbm n a b then 4 else 0).
Definition rbu_src := ltac:(run_template_program (tmQuoteRec rbu)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Eval vm_compute in map (fun x => snd x) rbu_src.
Definition rbu_Pr := mkprog (funs_of 0 rbu_src) [].
Time Lemma rbu_ok : callee_ok rbu_Pr (gid1 0) (cbz 0) (sig_at rbu_src 0) rbu.
Proof. Time exact_no_check (compile_f_ok rbu_Pr [] gid1 0 (sig_at rbu_src 0) (body_at rbu_src 0) eq_refl eq_refl (no_callees rbu_Pr gid1) eq_refl eq_refl). Time Qed.

(* ---------------------------------------------------------------- a pair built in place, taken apart (step 23) *)
(* the construct table's number-and-memory shapes whose pair is built where it is taken apart: a helper giving a number and a
   memory, written out (its pair after a let), and the pair taken apart *)
Definition ip_f (a b : i63) (s : mem) : i63 * mem := let p := KQ.KQRun.rd 0 a s in (p, KQ.KQRun.upd 0 a (PrimInt63.add p b) s).
Definition ip (a b : i63) (s : mem) : i63 := let '(x, s2) := ip_f a b s in PrimInt63.add x (KQ.KQRun.rd 0 0 s2).
Definition ip_src := ltac:(run_template_program (tmQuoteRec ip)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Eval vm_compute in map (fun x => snd x) ip_src.
Definition ip_Pr := mkprog (funs_of 0 ip_src) [].
Time Lemma ip_ok : callee_ok ip_Pr (gid1 0) (cbz 0) (sig_at ip_src 0) ip.
Proof. Time exact_no_check (compile_f_ok ip_Pr [] gid1 0 (sig_at ip_src 0) (body_at ip_src 0) eq_refl eq_refl (no_callees ip_Pr gid1) eq_refl eq_refl). Time Qed.


(* ---------------------------------------------------------------- functions giving back a boolean (step 24) *)
(* the construct table's shapes: a loop, a search, [&&] and [||] around the recursive call, its negation; a caller testing
   them by jumps, and choosing a number on the last *)
Fixpoint vbtail (n : nat) (a b : i63) (s : mem) : bool :=
  match n with O => PrimInt63.ltb a b | S m => vbtail m (PrimInt63.add a 1) b s end.
Fixpoint vbsearch (n : nat) (a b : i63) (s : mem) : bool :=
  match n with O => false | S m => if PrimInt63.eqb (KQ.KQRun.rd 0 a s) b then true else vbsearch m (PrimInt63.add a 1) b s end.
Fixpoint vband (n : nat) (a b : i63) (s : mem) : bool :=
  match n with O => true | S m => (PrimInt63.ltb a b) && vband m (PrimInt63.add a 1) b s end.
Fixpoint vbor (n : nat) (a b : i63) (s : mem) : bool :=
  match n with O => false | S m => (PrimInt63.eqb a b) || vbor m (PrimInt63.add a 1) b s end.
Fixpoint vbneg (n : nat) (x : i63) : bool := match n with O => PrimInt63.ltb x 3 | S m => negb (vbneg m (PrimInt63.add x 1)) end.
Definition vbgo (n : nat) (a b : i63) (s : mem) : i63 :=
  PrimInt63.add (PrimInt63.add (if vbtail n a b s then 1 else 0) (if vbsearch n a b s then 2 else 0))
    (PrimInt63.add (if vband n a b s then (let x := PrimInt63.add a 1 in PrimInt63.mul x x) else 0)
       (PrimInt63.add (if vbor n a b s then 8 else 0) (if vbneg n a then a else b))).
Definition vbgo_src := ltac:(run_template_program (tmQuoteRec vbgo)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
(* the five read exactly as the hand-written trees of KQR.v's step 24 tests; the caller's tests are calls ([BCall]) *)
Check (eq_refl : firstn 5 (map snd vbgo_src) = [qtail_b; qsearch_b; qand_b; qor_b; qneg_b]).
Definition vbgo_Pr := mkprog (funs_of 0 vbgo_src) [].
Time Lemma vbtail_ok : callee_ok vbgo_Pr (gid1 0) (cbz 0) (sig_at vbgo_src 0) vbtail.
Proof. Time exact_no_check (compile_f_ok vbgo_Pr [] gid1 0 (sig_at vbgo_src 0) (body_at vbgo_src 0) eq_refl eq_refl (no_callees vbgo_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma vbsearch_ok : callee_ok vbgo_Pr (gid1 1) (cbz 1) (sig_at vbgo_src 1) vbsearch.
Proof. Time exact_no_check (compile_f_ok vbgo_Pr [] gid1 1 (sig_at vbgo_src 1) (body_at vbgo_src 1) eq_refl eq_refl (no_callees vbgo_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma vband_ok : callee_ok vbgo_Pr (gid1 2) (cbz 2) (sig_at vbgo_src 2) vband.
Proof. Time exact_no_check (compile_f_ok vbgo_Pr [] gid1 2 (sig_at vbgo_src 2) (body_at vbgo_src 2) eq_refl eq_refl (no_callees vbgo_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma vbor_ok : callee_ok vbgo_Pr (gid1 3) (cbz 3) (sig_at vbgo_src 3) vbor.
Proof. Time exact_no_check (compile_f_ok vbgo_Pr [] gid1 3 (sig_at vbgo_src 3) (body_at vbgo_src 3) eq_refl eq_refl (no_callees vbgo_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma vbneg_ok : callee_ok vbgo_Pr (gid1 4) (cbz 4) (sig_at vbgo_src 4) vbneg.
Proof. Time exact_no_check (compile_f_ok vbgo_Pr [] gid1 4 (sig_at vbgo_src 4) (body_at vbgo_src 4) eq_refl eq_refl (no_callees vbgo_Pr gid1) eq_refl eq_refl). Time Qed.
Definition vb_cs := [existT ftype (sig_at vbgo_src 0) vbtail; existT ftype (sig_at vbgo_src 1) vbsearch;
                     existT ftype (sig_at vbgo_src 2) vband; existT ftype (sig_at vbgo_src 3) vbor; existT ftype (sig_at vbgo_src 4) vbneg].
Time Lemma vbgo_ok : callee_ok vbgo_Pr (gid1 5) (cbz 5) (sig_at vbgo_src 5) vbgo.
Proof.
  Time exact_no_check (compile_f_ok vbgo_Pr vb_cs gid1 5 (sig_at vbgo_src 5) (body_at vbgo_src 5) eq_refl eq_refl
    (all_ok_callees vbgo_Pr gid1 vb_cs (conj vbtail_ok (conj vbsearch_ok (conj vband_ok (conj vbor_ok (conj vbneg_ok Logic.I))))))
    eq_refl eq_refl).
Time Qed.
Print Assumptions vbgo_ok.

(* ---------------------------------------------------------------- a value built in place, taken apart (step 25) *)
(* the construct table's shapes: a record with a proof field and one with a memory field, a list cell, a pair of pairs and a
   pair holding a function given to helpers (written out, each argument a constructor of plain values); a pair holding the
   memory, taken apart after a helper *)
Record w5bnd := w5mkb { w5bv : i63; w5bok : True }.
Record w5ms := w5mkms { w5mv : i63; w5mm : KQ.KQRun.mem }.
Definition w5k1 (x : i63) : i63 := w5bv (w5mkb x I).
Definition w5k2 (x : i63) : list i63 := cons x nil.
Definition w5k3 (t : KQ.KQRun.mem) (x : i63) : i63 := w5mv (w5mkms x t).
Definition w5k4 (p : (i63 * i63) * i63) : i63 := PrimInt63.add (PrimInt63.add (fst (fst p)) (snd (fst p))) (snd p).
Definition w5k5 (p : i63 * (i63 -> i63)) : i63 := (snd p) (fst p).
Definition w5k6 (p : i63 * KQ.KQRun.mem) : i63 * KQ.KQRun.mem := (PrimInt63.add (fst p) 1, snd p).
Definition w5go (n : nat) (a b : i63) (s : KQ.KQRun.mem) : i63 :=
  PrimInt63.add (PrimInt63.add (w5k1 a) (match w5k2 a with nil => 0 | cons x _ => x end))
    (PrimInt63.add (w5k3 s a) (PrimInt63.add (w5k4 ((a, b), a)) (w5k5 (a, fun x => PrimInt63.add x 1)))).
Definition w5gm (n : nat) (a b : i63) (s : KQ.KQRun.mem) : i63 :=
  let '(x, t) := w5k6 (a, s) in PrimInt63.add x (KQ.KQRun.rd 0 0 t).
Definition w5go_src := ltac:(run_template_program (tmQuoteRec w5go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition w5gm_src := ltac:(run_template_program (tmQuoteRec w5gm)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
(* each value read away by zeta and iota: the record fields, the list cell's head, the pairs' parts and the function applied *)
Check (eq_refl : map (fun x => snd x) w5go_src =
  [FPlain (SOp Badd (SOp Badd (SVar 1) (SVar 1)) (SOp Badd (SVar 1) (SOp Badd
     (SOp Badd (SOp Badd (SLetR (RLetR (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RVar 0)) (SMatchR (RVar 0) (SVar 1)))
                         (SLetR (RLetR (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RVar 0)) (SMatchR (RVar 0) (SVar 0))))
               (SLet (SVar 1) (SVar 0)))
     (SLet (SLet (SVar 1) (SVar 0)) (SOp Badd (SVar 0) (SInt 1))))))]).
Check (eq_refl : map (fun x => snd x) w5gm_src =
  [FPlainX (XLet (SOp Badd (SLet (SVar 1) (SVar 0)) (SInt 1)) (XLetM (MLetM MCur MCur) (XRet (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 0))))))]).
Section W5.
#[local] Instance w5_recs : RecTypes | 0 :=
  mkrecs (fun _ => (i63 * i63)%type) (fun _ => mkrops 2 None (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end)) (fun _ => (0%uint63, 0%uint63)).
#[local] Instance w5_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
Definition w5go_Pr := mkprog (funs_of 0 w5go_src) [].
Time Lemma w5go_ok : callee_ok w5go_Pr (gid1 0) (cbz 0) (sig_at w5go_src 0) w5go.
Proof.
  Time exact_no_check (@compile_f_ok w5_recs w5_laws w5go_Pr [] gid1 0 (sig_at w5go_src 0) (body_at w5go_src 0) eq_refl eq_refl
    (no_callees w5go_Pr gid1) eq_refl eq_refl).
Time Qed.
End W5.
Definition w5gm_Pr := mkprog (funs_of 0 w5gm_src) [].
Time Lemma w5gm_ok : callee_ok w5gm_Pr (gid1 0) (cbz 0) (sig_at w5gm_src 0) w5gm.
Proof. Time exact_no_check (compile_f_ok w5gm_Pr [] gid1 0 (sig_at w5gm_src 0) (body_at w5gm_src 0) eq_refl eq_refl (no_callees w5gm_Pr gid1) eq_refl eq_refl). Time Qed.
Print Assumptions w5go_ok.

(* ---------------------------------------------------------------- a number and a memory given back (step 26) *)
(* KQR.v's step 26 tests read from their text: a caller taking apart the pair of a recursion that takes its own pair apart
   ([jgo] over [jnon]), a caller binding the pair of a loop by a let read through fst and snd ([jlet] over [jtail]), a pair
   chosen by a test taken apart where it is made ([jif]) *)
Definition vjgo_src := ltac:(run_template_program (tmQuoteRec jgo)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition vjlet_src := ltac:(run_template_program (tmQuoteRec jlet)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition vjif_src := ltac:(run_template_program (tmQuoteRec jif)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) vjgo_src = [jnon_b;
  FPlainX (XMatchP (PvCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil)) MCur) jread)]).
Check (eq_refl : map (fun x => snd x) vjlet_src = [jtail_b;
  FPlainX (XLetP (PvCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil)) MCur)
                 (XRet (SOp Badd (SLet (SVar 0) (SVar 0)) (SRd (SInt 0) (SInt 0)))))]).
Check (eq_refl : map (fun x => snd x) vjif_src = [jif_b]).
Definition vjgo_Pr := mkprog (funs_of 0 vjgo_src) [].
Time Lemma vjnon_ok : callee_ok vjgo_Pr (gid1 0) (cbz 0) (sig_at vjgo_src 0) jnon.
Proof. Time exact_no_check (compile_f_ok vjgo_Pr [] gid1 0 (sig_at vjgo_src 0) (body_at vjgo_src 0) eq_refl eq_refl (no_callees vjgo_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma vjgo_ok : callee_ok vjgo_Pr (gid1 1) (cbz 1) (sig_at vjgo_src 1) jgo.
Proof.
  Time exact_no_check (compile_f_ok vjgo_Pr [existT ftype (sig_at vjgo_src 0) jnon] gid1 1 (sig_at vjgo_src 1) (body_at vjgo_src 1)
    eq_refl eq_refl (all_ok_callees vjgo_Pr gid1 [existT ftype (sig_at vjgo_src 0) jnon] (conj vjnon_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Definition vjlet_Pr := mkprog (funs_of 0 vjlet_src) [].
Time Lemma vjtail_ok : callee_ok vjlet_Pr (gid1 0) (cbz 0) (sig_at vjlet_src 0) jtail.
Proof. Time exact_no_check (compile_f_ok vjlet_Pr [] gid1 0 (sig_at vjlet_src 0) (body_at vjlet_src 0) eq_refl eq_refl (no_callees vjlet_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma vjlet_ok : callee_ok vjlet_Pr (gid1 1) (cbz 1) (sig_at vjlet_src 1) jlet.
Proof.
  Time exact_no_check (compile_f_ok vjlet_Pr [existT ftype (sig_at vjlet_src 0) jtail] gid1 1 (sig_at vjlet_src 1) (body_at vjlet_src 1)
    eq_refl eq_refl (all_ok_callees vjlet_Pr gid1 [existT ftype (sig_at vjlet_src 0) jtail] (conj vjtail_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Definition vjif_Pr := mkprog (funs_of 0 vjif_src) [].
Time Lemma vjif_ok : callee_ok vjif_Pr (gid1 0) (cbz 0) (sig_at vjif_src 0) jif.
Proof. Time exact_no_check (compile_f_ok vjif_Pr [] gid1 0 (sig_at vjif_src 0) (body_at vjif_src 0) eq_refl eq_refl (no_callees vjif_Pr gid1) eq_refl eq_refl). Time Qed.
Print Assumptions vjlet_ok.

(* ---------------------------------------------------------------- a template giving its function on (step 27) *)
(* the construct table's P_int_outer_capt: a template whose body gives its own function parameter to another template; the
   function given names the caller's number ([zof1]) or nothing ([zof2]) *)
Fixpoint zfold (n : nat) (i acc : i63) (f : i63 -> i63 -> i63) : i63 :=
  match n with O => acc | S m => zfold m (PrimInt63.add i 1) (f i acc) f end.
Fixpoint zouter (r : nat) (acc : i63) (f : i63 -> i63 -> i63) : i63 :=
  match r with O => acc | S r' => zouter r' (zfold 3 0 acc f) f end.
Definition zof1 (n : nat) (a b : i63) (s : KQ.KQRun.mem) : i63 := zouter n a (fun i acc => PrimInt63.add acc (PrimInt63.mul i b)).
Definition zof2 (n : nat) (a b : i63) (s : KQ.KQRun.mem) : i63 := zouter n a (fun i acc => PrimInt63.add acc (PrimInt63.mul i 7)).
Definition zof1_res := ltac:(run_template_program (tmQuoteRec zof1)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition zof1_src := ltac:(run_template_program (tmQuoteRec zof1)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
(* the copy of zfold for zouter's function, taking the captured number before its own; zouter's copy calls it, passing it on *)
Check (eq_refl : map (fun x => snd x) zof1_src =
  [FRec (SVar 0) (SRec CNil (SCons (SVar 2) (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SOp Badd (SVar 0) (SOp Bmul (SVar 1) (SVar 2))) SNil))));
   FRec (SVar 0) (SRec CNil (SCons (SVar 1) (SCons (SCall 0 (CCons (CS (CS (CS CO))) CNil) (SCons (SVar 1) (SCons (SInt 0) (SCons (SVar 0) SNil)))) SNil)));
   FPlain (SCall 1 (CCons (CVar 0) CNil) (SCons (SVar 0) (SCons (SVar 1) SNil)))]).
MetaRocq Run (tmMkDefinition "zof1_c0"%bs (meaning_of (snd zof1_res) "zfold__c0"%bs)).
MetaRocq Run (tmMkDefinition "zof1_c1"%bs (meaning_of (snd zof1_res) "zouter__c1"%bs)).
Definition zof1_Pr := mkprog (funs_of 0 zof1_src) [].
Time Lemma zof1_ok0 : callee_ok zof1_Pr (gid1 0) (cbz 0) (sig_at zof1_src 0) zof1_c0.
Proof.
  Time exact_no_check (compile_f_okr zof1_Pr [] gid1 0 0 [KNum; KNum; KNum] false (fr0 (body_at zof1_src 0)) (fr1 (body_at zof1_src 0)) None [] zof1_c0
    eq_refl eq_refl (no_callees zof1_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma zof1_ok1 : callee_ok zof1_Pr (gid1 1) (cbz 1) (sig_at zof1_src 1) zof1_c1.
Proof.
  Time exact_no_check (compile_f_okr zof1_Pr [existT ftype (sig_at zof1_src 0) zof1_c0] gid1 1 0 [KNum; KNum] false
    (fr0 (body_at zof1_src 1)) (fr1 (body_at zof1_src 1)) None [] zof1_c1 eq_refl eq_refl
    (all_ok_callees zof1_Pr gid1 [existT ftype (sig_at zof1_src 0) zof1_c0] (conj zof1_ok0 Logic.I)) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma zof1_ok2 : callee_ok zof1_Pr (gid1 2) (cbz 2) (sig_at zof1_src 2) zof1.
Proof.
  Time exact_no_check (compile_f_ok zof1_Pr [existT ftype (sig_at zof1_src 0) zof1_c0; existT ftype (sig_at zof1_src 1) zof1_c1]
    gid1 2 (sig_at zof1_src 2) (body_at zof1_src 2) eq_refl eq_refl
    (all_ok_callees zof1_Pr gid1 [existT ftype (sig_at zof1_src 0) zof1_c0; existT ftype (sig_at zof1_src 1) zof1_c1]
       (conj zof1_ok0 (conj zof1_ok1 Logic.I))) eq_refl eq_refl).
Time Qed.
Print Assumptions zof1_ok2.
(* without a capture: the same copies, the function given naming nothing *)
Check (eq_refl : option_map (fun l => length l) (reify_prog ltac:(run_template_program (tmQuoteRec zof2) (fun q => exact q))) = Some 3%nat).

(* ---------------------------------------------------------------- data types held as their tag and fields (step 28) *)
(* the construct table's shapes: an option chosen by a helper's test and taken apart by the caller (A_par_option), the same
   with a sum (A_par_sum), an option given back by a recursion (A_par_option_rec), an option as a loop's state
   (A_par_option_state) *)
Definition t8k (x : i63) : option i63 := if PrimInt63.ltb x 7 then None else Some x.
Definition t8go (a : i63) : i63 := match t8k a with Some x => x | None => 0 end.
Definition t8s (x : i63) : (i63 + i63)%type := if PrimInt63.ltb x 5 then inl x else inr x.
Definition t8sum (a : i63) : i63 := match t8s a with inl x => x | inr y => PrimInt63.add y 1 end.
Fixpoint t8res (n : nat) (x : i63) : option i63 :=
  match n with O => None | S m => if PrimInt63.eqb x 5 then Some x else t8res m (PrimInt63.add x 1) end.
Definition t8rgo (n : nat) (a : i63) : i63 := match t8res n a with Some y => y | None => 0 end.
Fixpoint t8st (n : nat) (x : i63) (o : option i63) : i63 :=
  match n with O => match o with Some y => y | None => x end | S m => t8st m (PrimInt63.add x 1) (if PrimInt63.eqb x 3 then Some x else o) end.
Definition t8sgo (n : nat) (a : i63) : i63 := t8st n a None.
Definition t8go_src := ltac:(run_template_program (tmQuoteRec t8go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition t8sum_src := ltac:(run_template_program (tmQuoteRec t8sum)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition t8rgo_src := ltac:(run_template_program (tmQuoteRec t8rgo)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition t8sgo_src := ltac:(run_template_program (tmQuoteRec t8sgo)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
(* Rocq's option: Some constructor 0, None constructor 1; each value its tag then its field, None's padded with 0 *)
Definition t8some (e : sexp) := RMk 0 (SCons (SInt 0) (SCons e SNil)).
Definition t8none := RMk 0 (SCons (SInt 1) (SCons (SInt 0) SNil)).
Check (eq_refl : map (fun x => snd x) t8go_src =
  [FPlain (SMatchR (RIf 0 Clt (SVar 0) (SInt 7) t8none (t8some (SVar 0))) (SIf Ceq (SVar 1) (SInt 0) (SVar 0) (SInt 0)))]).
Check (eq_refl : map (fun x => snd x) t8sum_src =
  [FPlain (SMatchR (RIf 0 Clt (SVar 0) (SInt 5) (RMk 0 (SCons (SInt 0) (SCons (SVar 0) SNil))) (RMk 0 (SCons (SInt 1) (SCons (SVar 0) SNil))))
                   (SIf Ceq (SVar 1) (SInt 0) (SVar 0) (SOp Badd (SVar 0) (SInt 1))))]).
Check (eq_refl : map (fun x => snd x) t8rgo_src =
  [FRecR (BRet t8none) (BIf Ceq (SVar 0) (SInt 5) (BRet (t8some (SVar 0))) (BRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)));
   FPlain (SMatchR (RCall 0 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil)) (SIf Ceq (SVar 1) (SInt 0) (SVar 0) (SInt 0)))]).
Check (eq_refl : map (fun x => snd x) t8sgo_src =
  [FRec (SMatchR (RVar 0) (SIf Ceq (SVar 1) (SInt 0) (SVar 0) (SVar 2)))
        (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) (SConsR (RIf 0 Ceq (SVar 0) (SInt 3) (t8some (SVar 0)) (RVar 0)) SNil)));
   FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) (SConsR t8none SNil)))]).
Section T8O.
#[local] Instance t8o_recs : RecTypes | 0 :=
  mkrecs (fun _ => option i63) (fun _ => mkrops 2 (Some [1; 0]%nat) (fun l => if PrimInt63.eqb (nth 0 l 0%uint63) 0%uint63 then Some (nth 1 l 0%uint63) else None)
                      (fun P v k => match v with Some y => k [0%uint63; y] | None => k [1%uint63; 0%uint63] end)) (fun _ => Some 0%uint63).
#[local] Instance t8o_laws : RecLaws.
Proof. apply laws_of; [intros i [y|] P k; reflexivity | intros i [y|]; reflexivity | intros i l E; discriminate E
              | intros i ws c rest E Lc Lr Hz; cbn in E; injection E as <-; kq_tag_case]. Qed.
Definition t8go_Pr := mkprog (funs_of 0 t8go_src) [].
Time Lemma t8go_ok : callee_ok t8go_Pr (gid1 0) (cbz 0) (sig_at t8go_src 0) t8go.
Proof. Time exact_no_check (@compile_f_ok t8o_recs t8o_laws t8go_Pr [] gid1 0 (sig_at t8go_src 0) (body_at t8go_src 0) eq_refl eq_refl (no_callees t8go_Pr gid1) eq_refl eq_refl). Time Qed.
Definition t8rgo_Pr := mkprog (funs_of 0 t8rgo_src) [].
Time Lemma t8res_ok : callee_ok t8rgo_Pr (gid1 0) (cbz 0) (sig_at t8rgo_src 0) t8res.
Proof. Time exact_no_check (@compile_f_ok t8o_recs t8o_laws t8rgo_Pr [] gid1 0 (sig_at t8rgo_src 0) (body_at t8rgo_src 0) eq_refl eq_refl (no_callees t8rgo_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma t8rgo_ok : callee_ok t8rgo_Pr (gid1 1) (cbz 1) (sig_at t8rgo_src 1) t8rgo.
Proof.
  Time exact_no_check (@compile_f_ok t8o_recs t8o_laws t8rgo_Pr [existT ftype (sig_at t8rgo_src 0) t8res] gid1 1 (sig_at t8rgo_src 1) (body_at t8rgo_src 1)
    eq_refl eq_refl (all_ok_callees t8rgo_Pr gid1 [existT ftype (sig_at t8rgo_src 0) t8res] (conj t8res_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Definition t8sgo_Pr := mkprog (funs_of 0 t8sgo_src) [].
Time Lemma t8st_ok : callee_ok t8sgo_Pr (gid1 0) (cbz 0) (sig_at t8sgo_src 0) t8st.
Proof. Time exact_no_check (@compile_f_ok t8o_recs t8o_laws t8sgo_Pr [] gid1 0 (sig_at t8sgo_src 0) (body_at t8sgo_src 0) eq_refl eq_refl (no_callees t8sgo_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma t8sgo_ok : callee_ok t8sgo_Pr (gid1 1) (cbz 1) (sig_at t8sgo_src 1) t8sgo.
Proof.
  Time exact_no_check (@compile_f_ok t8o_recs t8o_laws t8sgo_Pr [existT ftype (sig_at t8sgo_src 0) t8st] gid1 1 (sig_at t8sgo_src 1) (body_at t8sgo_src 1)
    eq_refl eq_refl (all_ok_callees t8sgo_Pr gid1 [existT ftype (sig_at t8sgo_src 0) t8st] (conj t8st_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions t8rgo_ok.
End T8O.
Section T8S.
#[local] Instance t8s_recs : RecTypes | 0 :=
  mkrecs (fun _ => (i63 + i63)%type) (fun _ => mkrops 2 (Some [1; 1]%nat) (fun l => if PrimInt63.eqb (nth 0 l 0%uint63) 0%uint63 then inl (nth 1 l 0%uint63) else inr (nth 1 l 0%uint63))
                      (fun P v k => match v with inl y => k [0%uint63; y] | inr y => k [1%uint63; y] end)) (fun _ => inl 0%uint63).
#[local] Instance t8s_laws : RecLaws.
Proof. apply laws_of; [intros i [y|y] P k; reflexivity | intros i [y|y]; reflexivity | intros i l E; discriminate E
              | intros i ws c rest E Lc Lr Hz; cbn in E; injection E as <-; kq_tag_case]. Qed.
Definition t8sum_Pr := mkprog (funs_of 0 t8sum_src) [].
Time Lemma t8sum_ok : callee_ok t8sum_Pr (gid1 0) (cbz 0) (sig_at t8sum_src 0) t8sum.
Proof. Time exact_no_check (@compile_f_ok t8s_recs t8s_laws t8sum_Pr [] gid1 0 (sig_at t8sum_src 0) (body_at t8sum_src 0) eq_refl eq_refl (no_callees t8sum_Pr gid1) eq_refl eq_refl). Time Qed.
End T8S.

(* ---- comparisons of counters and the predecessor (step 30), read from the text: KQR.v's [nceq], [nclt], [npk] and [npgo]
   (the trees exactly the hand-written ones), and the construct table's shapes in one caller with a memory it does not use *)
Definition w30eq (n : nat) (a b : i63) : i63 := if Nat.eqb n 3 then a else b.
Definition w30lt (n : nat) (a b : i63) : i63 := if Nat.ltb n 10 then a else b.
Fixpoint w30k (n : nat) (x : i63) : i63 := match n with O => x | S m => w30k m (PrimInt63.add x 1) end.
Definition w30pred (n : nat) (a b : i63) : i63 := w30k (Nat.pred n) a.
Definition w30go (n : nat) (a b : i63) (s : mem) : i63 :=
  PrimInt63.add (PrimInt63.add (if Nat.eqb n 3 then a else b) (if Nat.leb n 10 then a else b)) (w30k (Nat.pred n) a).
Definition w30eq_src := ltac:(run_template_program (tmQuoteRec w30eq)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition w30lt_src := ltac:(run_template_program (tmQuoteRec w30lt)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition w30pred_src := ltac:(run_template_program (tmQuoteRec w30pred)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition w30go_src := ltac:(run_template_program (tmQuoteRec w30go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map snd w30eq_src = [nceq_b]).
Check (eq_refl : map snd w30lt_src = [nclt_b]).
Check (eq_refl : map snd w30pred_src = [npk_b; FPlain (SCall 0 (CCons (KQR.CPred (CVar 0)) CNil) (SCons (SVar 1) SNil))]).
Definition w30pred_Pr := mkprog (funs_of 0 w30pred_src) [].
Time Lemma w30k_ok : callee_ok w30pred_Pr (gid1 0) (cbz 0) (sig_at w30pred_src 0) w30k.
Proof. Time exact_no_check (compile_f_ok w30pred_Pr [] gid1 0 (sig_at w30pred_src 0) (body_at w30pred_src 0) eq_refl eq_refl (no_callees w30pred_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w30pred_ok : callee_ok w30pred_Pr (gid1 1) (cbz 1) (sig_at w30pred_src 1) w30pred.
Proof.
  Time exact_no_check (compile_f_ok w30pred_Pr [existT ftype (sig_at w30pred_src 0) w30k] gid1 1 (sig_at w30pred_src 1) (body_at w30pred_src 1)
    eq_refl eq_refl (all_ok_callees w30pred_Pr gid1 [existT ftype (sig_at w30pred_src 0) w30k] (conj w30k_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Definition w30go_Pr := mkprog (funs_of 0 w30go_src) [].
Time Lemma w30k_ok' : callee_ok w30go_Pr (gid1 0) (cbz 0) (sig_at w30go_src 0) w30k.
Proof. Time exact_no_check (compile_f_ok w30go_Pr [] gid1 0 (sig_at w30go_src 0) (body_at w30go_src 0) eq_refl eq_refl (no_callees w30go_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w30go_ok : callee_ok w30go_Pr (gid1 1) (cbz 1) (sig_at w30go_src 1) w30go.
Proof.
  Time exact_no_check (compile_f_ok w30go_Pr [existT ftype (sig_at w30go_src 0) w30k] gid1 1 (sig_at w30go_src 1) (body_at w30go_src 1)
    eq_refl eq_refl (all_ok_callees w30go_Pr gid1 [existT ftype (sig_at w30go_src 0) w30k] (conj w30k_ok' Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions w30go_ok.

(* ---- a local fixpoint naming the caller's variables (step 31): [lf_f]'s [let fix g] names [b] -- the construct table's
   P_int_local_fix, through a helper written out, called twice with different variables captured (one copy); [lf_m]'s names
   a number and the memory.  Each is read as a copy whose parameters are its captured variables (the numbers before its own,
   the memory last), its meaning the fixpoint itself; the caller passes them *)
Definition lf_f (n : nat) (a b : i63) (s : mem) : i63 :=
  let fix g (m : nat) (x : i63) : i63 := match m with O => x | S k => g k (PrimInt63.add x b) end in g n a.
Definition lf_go (n : nat) (a b : i63) (s : mem) : i63 := PrimInt63.add (lf_f n a b s) (lf_f n b a s).
Definition lf_m (n : nat) (a b : i63) (s : mem) : i63 :=
  let fix g (m : nat) (i acc : i63) : i63 :=
    match m with O => acc | S k => g k (PrimInt63.add i 1) (PrimInt63.add acc (PrimInt63.mul (KQ.KQRun.rd 0 i s) b)) end in
  g n 0%uint63 a.
Definition lf_go_res := ltac:(run_template_program (tmQuoteRec lf_go)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition lf_go_src := fst lf_go_res.
Definition lf_m_res := ltac:(run_template_program (tmQuoteRec lf_m)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition lf_m_src := fst lf_m_res.
(* the copy: the captured [b] before its own [x], passed on by its recursive call; [lf_go]'s two calls, one copy *)
Check (eq_refl : map snd lf_go_src =
  [FRec (SVar 0) (SRec CNil (SCons (SVar 1) (SCons (SOp Badd (SVar 0) (SVar 1)) SNil)));
   FPlain (SOp Badd (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) (SCons (SVar 1) SNil)))
                    (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil))))]).
Check (eq_refl : map (fun x => snd (fst x)) lf_m_src = [mksig 1 [KNum; KNum; KNum] true false false None; mksig 1 [KNum; KNum] true false false None]).
Check (eq_refl : map snd lf_m_src =
  [FRec (SVar 0) (SRec CNil (SCons (SVar 2) (SCons (SOp Badd (SVar 1) (SInt 1))
                                            (SCons (SOp Badd (SVar 0) (SOp Bmul (SRd (SInt 0) (SVar 1)) (SVar 2))) SNil))));
   FPlain (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) (SCons (SInt 0) (SCons (SVar 1) SNil))))]).
MetaRocq Run (tmMkDefinition "lf_c0"%bs (meaning_of (snd lf_go_res) "kqlfix__c0"%bs)).
MetaRocq Run (tmMkDefinition "lf_m_c0"%bs (meaning_of (snd lf_m_res) "kqlfix__c0"%bs)).
Print lf_c0.
Print lf_m_c0.
Definition lf_go_Pr := mkprog (funs_of 0 lf_go_src) [].
Time Lemma lf_ok0 : callee_ok lf_go_Pr (gid1 0) (cbz 0) (sig_at lf_go_src 0) lf_c0.
Proof.
  Time exact_no_check (compile_f_okr lf_go_Pr [] gid1 0 0 [KNum; KNum] false (fr0 (body_at lf_go_src 0)) (fr1 (body_at lf_go_src 0)) None [] lf_c0
    eq_refl eq_refl (no_callees lf_go_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma lf_ok1 : callee_ok lf_go_Pr (gid1 1) (cbz 1) (sig_at lf_go_src 1) lf_go.
Proof.
  Time exact_no_check (compile_f_ok lf_go_Pr [existT ftype (sig_at lf_go_src 0) lf_c0] gid1 1 (sig_at lf_go_src 1) (body_at lf_go_src 1)
    eq_refl eq_refl (all_ok_callees lf_go_Pr gid1 [existT ftype (sig_at lf_go_src 0) lf_c0] (conj lf_ok0 Logic.I)) eq_refl eq_refl).
Time Qed.
Definition lf_m_Pr := mkprog (funs_of 0 lf_m_src) [].
Time Lemma lf_m_ok0 : callee_ok lf_m_Pr (gid1 0) (cbz 0) (sig_at lf_m_src 0) lf_m_c0.
Proof.
  Time exact_no_check (compile_f_okr lf_m_Pr [] gid1 0 0 [KNum; KNum; KNum] true (fr0 (body_at lf_m_src 0)) (fr1 (body_at lf_m_src 0)) None [] lf_m_c0
    eq_refl eq_refl (no_callees lf_m_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma lf_m_ok1 : callee_ok lf_m_Pr (gid1 1) (cbz 1) (sig_at lf_m_src 1) lf_m.
Proof.
  Time exact_no_check (compile_f_ok lf_m_Pr [existT ftype (sig_at lf_m_src 0) lf_m_c0] gid1 1 (sig_at lf_m_src 1) (body_at lf_m_src 1)
    eq_refl eq_refl (all_ok_callees lf_m_Pr gid1 [existT ftype (sig_at lf_m_src 0) lf_m_c0] (conj lf_m_ok0 Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions lf_m_ok1.

(* ---- a record holding records (step 32): [pp_f] gives back [(int * int) * int] by recursion, taking its own result apart
   with its inner pair at once ([let '(p, z) := .. in let '(x, y) := p in ..]: the construct table's P_pairp_rec), [pp_go]
   takes it apart the same way.  Held as one flat record of numbers: the outer number first, then the inner pair's two; the
   instance as kitc.py writes it *)
Fixpoint pp_f (n : nat) (a b : i63) (s : mem) : (i63 * i63) * i63 :=
  match n with O => ((a, b), 0%uint63) | S m => let '(p, z) := pp_f m a b s in let '(x, y) := p in ((y, x), PrimInt63.add z 1) end.
Definition pp_go (n : nat) (a b : i63) (s : mem) : i63 :=
  let '(p, z) := pp_f n a b s in let '(x, y) := p in PrimInt63.add (PrimInt63.add x y) z.
Definition pp_src := ltac:(run_template_program (tmQuoteRec pp_go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Definition pp_rec := ltac:(run_template_program (tmQuoteRec pp_go) (fun q => let r := eval vm_compute in (rec_info q) in exact r)).
Check (eq_refl : pp_rec = [("(Corelib.Init.Datatypes.prod (Corelib.Init.Datatypes.prod PrimInt63.int PrimInt63.int) PrimInt63.int)"%bs, "Corelib.Init.Datatypes.pair"%bs, 3, "N:Corelib.Init.Datatypes.pair(Corelib.Init.Datatypes.pair(i,i),i)@1"%bs);
                           ("(Corelib.Init.Datatypes.prod PrimInt63.int PrimInt63.int)"%bs, "Corelib.Init.Datatypes.pair"%bs, 2, ""%bs)]).
(* the fields bound where the text binds them: [z] the nearest of the outer numbers, then [x], [y]; the inner pair's own
   variable unusable *)
Check (eq_refl : map snd pp_src =
  [FRecR (BRet (RMk 0 (SCons (SInt 0) (SCons (SVar 1) (SCons (SVar 0) SNil)))))
         (BMatchRec CNil (SCons (SVar 1) (SCons (SVar 0) SNil))
            (BRet (RMk 0 (SCons (SOp Badd (SVar 2) (SInt 1)) (SCons (SVar 0) (SCons (SVar 1) SNil))))));
   FPlain (SMatchR (RCall 0 0 (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil)))
                   (SOp Badd (SOp Badd (SVar 1) (SVar 0)) (SVar 2)))]).
Section PP.
Definition pp_rt (i : nat) : Type := match i with O => (prod (prod PrimInt63.int PrimInt63.int) PrimInt63.int) | S O => (prod PrimInt63.int PrimInt63.int) | _ => unit end.
Definition pp_ro (i : nat) : rops (pp_rt i) :=
  match i as i0 return rops (pp_rt i0) with
  | O => mkrops 3%nat None (fun l => (pair (pair (nth 1%nat l 0%uint63) (nth 2%nat l 0%uint63)) (nth 0%nat l 0%uint63)))
                (fun P v k => match v with pair v1 v2 => match v1 with pair v3 v4 => k (cons v2 (cons v3 (cons v4 nil))) end end)
  | S O => mkrops 2%nat None (fun l => pair (nth 0%nat l 0%uint63) (nth 1%nat l 0%uint63)) (fun P v k => match v with pair x0 x1 => k (cons x0 (cons x1 nil)) end)
  | _ => mkrops 0%nat None (fun _ => tt) (fun P _ k => k nil) end.
Definition pp_rd (i : nat) : pp_rt i := match i as i0 return pp_rt i0 with O => (pair (pair 0%uint63 0%uint63) 0%uint63) | S O => pair 0%uint63 0%uint63 | _ => tt end.
#[local] Instance pp_recs : RecTypes | 0 := mkrecs (pp_rt) (pp_ro) (pp_rd).
#[local] Instance pp_laws : @RecLaws pp_recs.
Proof. apply laws_of.
- intros i x P k. destruct i as [|[|i]]; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].
- intros i x. destruct i as [|[|i]]; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].
- intros i l E L. destruct i as [|[|i]]; cbn in E, L; try discriminate E; repeat (destruct l as [|? l]; try discriminate L); reflexivity.
- intros i ws c rest E Lc Lr Hz. destruct i as [|[|i]]; cbn in E; try discriminate E; injection E as <-; kq_tag_case.
Qed.
Definition pp_Pr := mkprog (@funs_of pp_recs 0 pp_src) [].
Time Lemma pp_f_ok : @callee_ok pp_recs pp_Pr (gid1 0) (cbz 0) (sig_at pp_src 0) pp_f.
Proof. Time exact_no_check (@compile_f_ok pp_recs pp_laws pp_Pr [] gid1 0 (sig_at pp_src 0) (body_at pp_src 0) eq_refl eq_refl (no_callees pp_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma pp_go_ok : @callee_ok pp_recs pp_Pr (gid1 1) (cbz 1) (sig_at pp_src 1) pp_go.
Proof.
  Time exact_no_check (@compile_f_ok pp_recs pp_laws pp_Pr [existT (@ftype pp_recs) (sig_at pp_src 0) pp_f] gid1 1 (sig_at pp_src 1) (body_at pp_src 1)
    eq_refl eq_refl (@all_ok_callees pp_recs pp_Pr gid1 [existT (@ftype pp_recs) (sig_at pp_src 0) pp_f] (conj pp_f_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions pp_go_ok.
End PP.

(* ---- a sum of counters given to a callee (step 33): [w33go] gives [w33k] [n + n] -- A_par_nat_mul's shape.  Well formed only
   with a bound of its own, [w33go] -- the entry -- gets the smallest ([own_bound]); [w33k] keeps its index's *)
Fixpoint w33k (n : nat) (x : i63) : i63 := match n with O => x | S m => w33k m (PrimInt63.add x 1) end.
Definition w33go (n : nat) (a b : i63) (s : mem) : i63 := w33k (n + n) a.
Definition w33_src := ltac:(run_template_program (tmQuoteRec w33go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map snd w33_src = [npk_b; FPlain (SCall 0 (CCons (CAdd (CVar 0) (CVar 0)) CNil) (SCons (SVar 1) SNil))]).
Check (eq_refl : map (fun x => sb (snd (fst x))) w33_src = [None; Some own_bound]).
Definition w33_Pr := mkprog (funs_of 0 w33_src) [].
Time Lemma w33k_ok : callee_ok w33_Pr (gid1 0) (cbz 0) (sig_at w33_src 0) w33k.
Proof. Time exact_no_check (compile_f_ok w33_Pr [] gid1 0 (sig_at w33_src 0) (body_at w33_src 0) eq_refl eq_refl (no_callees w33_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w33go_ok : callee_ok w33_Pr (gid1 1) own_bound (sig_at w33_src 1) w33go.
Proof.
  Time exact_no_check (compile_f_ok w33_Pr [existT ftype (sig_at w33_src 0) w33k] gid1 1 (sig_at w33_src 1) (body_at w33_src 1)
    eq_refl eq_refl (all_ok_callees w33_Pr gid1 [existT ftype (sig_at w33_src 0) w33k] (conj w33k_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions w33go_ok.

(* ---- counter bounds worked out from the call graph (step 34): [w34k2] gives [w34k] a sum and is given a successor by the entry
   (A_par_nat_add_called_succ's shape): the entry the smallest bound, [w34k2] one more, [w34k] twice that and one *)
Fixpoint w34k (n : nat) (x : i63) : i63 := match n with O => x | S m => w34k m (PrimInt63.add x 1) end.
Fixpoint w34k2 (r n : nat) (x : i63) : i63 := match r with O => w34k (n + n) x | S q => w34k2 q n (PrimInt63.add x 1) end.
Definition w34go (n : nat) (a b : i63) (s : mem) : i63 := w34k2 n (S n) a.
Definition w34_src := ltac:(run_template_program (tmQuoteRec w34go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => sb (snd (fst x))) w34_src = [Some (2 * own_bound + 1)%Z; Some (own_bound + 1)%Z; Some own_bound]).
Definition w34_Pr := mkprog (funs_of 0 w34_src) [].
Time Lemma w34k_ok : callee_ok w34_Pr (gid1 0) (fbound (sig_at w34_src 0) 0) (sig_at w34_src 0) w34k.
Proof. Time exact_no_check (compile_f_ok w34_Pr [] gid1 0 (sig_at w34_src 0) (body_at w34_src 0) eq_refl eq_refl (no_callees w34_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w34k2_ok : callee_ok w34_Pr (gid1 1) (fbound (sig_at w34_src 1) 1) (sig_at w34_src 1) w34k2.
Proof.
  Time exact_no_check (compile_f_ok w34_Pr [existT ftype (sig_at w34_src 0) w34k] gid1 1 (sig_at w34_src 1) (body_at w34_src 1)
    eq_refl eq_refl (all_ok_callees w34_Pr gid1 [existT ftype (sig_at w34_src 0) w34k] (conj w34k_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma w34go_ok : callee_ok w34_Pr (gid1 2) (fbound (sig_at w34_src 2) 2) (sig_at w34_src 2) w34go.
Proof.
  Time exact_no_check (compile_f_ok w34_Pr [existT ftype (sig_at w34_src 0) w34k; existT ftype (sig_at w34_src 1) w34k2] gid1 2
    (sig_at w34_src 2) (body_at w34_src 2) eq_refl eq_refl
    (all_ok_callees w34_Pr gid1 [existT ftype (sig_at w34_src 0) w34k; existT ftype (sig_at w34_src 1) w34k2] (conj w34k_ok (conj w34k2_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions w34go_ok.

(* ---- a bound for each counter variable (step 35): a sum bound by a let and given to a callee (its own bound from the call graph),
   a let of a successor, a sum compared, a match on a sum read as a let of it and a match on the variable -- the cells
   A_par_nat_let_add, _let_succ, _eqb_add, _match_add *)
Fixpoint w35k (n : nat) (x : i63) : i63 := match n with O => x | S m => w35k m (PrimInt63.add x 1) end.
Definition w35a (n : nat) (a b : i63) (s : mem) : i63 := let w := (n + n)%nat in w35k w a.
Definition w35s (n : nat) (a b : i63) (s : mem) : i63 := let w := S n in w35k w a.
Definition w35e (n : nat) (a b : i63) (s : mem) : i63 := if Nat.eqb (n + n) 4 then a else b.
Definition w35m (n : nat) (a b : i63) (s : mem) : i63 := match (n + n)%nat with O => a | S p => w35k p a end.
Definition w35go (n : nat) (a b : i63) (s : mem) : i63 :=
  PrimInt63.add (PrimInt63.add (w35a n a b s) (w35s n a b s)) (PrimInt63.add (w35e n a b s) (w35m n a b s)).
Definition w35_src := ltac:(run_template_program (tmQuoteRec w35go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
(* the four are small helpers: written out in [w35go], which the reading gives the smallest bound of its own *)
Check (eq_refl : map (fun x => sb (snd (fst x))) w35_src = [None; Some own_bound]).
Check (eq_refl : body_at w35_src 1 =
  FPlain (SOp Badd
    (SOp Badd (SLetC (CAdd (CVar 0) (CVar 0)) (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil)))
              (SLetC (CS (CVar 0)) (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil))))
    (SOp Badd (SIfB (BCmpC Ceq (CAdd (CVar 0) (CVar 0)) (CS (CS (CS (CS CO))))) (SVar 1) (SVar 0))
              (SLetC (CAdd (CVar 0) (CVar 0)) (SMatch 0 (SVar 1) (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil))))))).
Definition w35_Pr := mkprog (funs_of 0 w35_src) [].
Time Lemma w35k_ok : callee_ok w35_Pr (gid1 0) (fbound (sig_at w35_src 0) 0) (sig_at w35_src 0) w35k.
Proof. Time exact_no_check (compile_f_ok w35_Pr [] gid1 0 (sig_at w35_src 0) (body_at w35_src 0) eq_refl eq_refl (no_callees w35_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w35go_ok : callee_ok w35_Pr (gid1 1) (fbound (sig_at w35_src 1) 1) (sig_at w35_src 1) w35go.
Proof. Time exact_no_check (compile_f_ok w35_Pr [existT ftype (sig_at w35_src 0) w35k] gid1 1 (sig_at w35_src 1) (body_at w35_src 1) eq_refl eq_refl
  (all_ok_callees w35_Pr gid1 [existT ftype (sig_at w35_src 0) w35k] (conj w35k_ok Logic.I)) eq_refl eq_refl). Time Qed.
Print Assumptions w35go_ok.
(* the bounds from the call graph see a let's bound: [w35r] binds [n + n] and gives it to [w35k], and is given [S n] by the entry --
   its bound one more than the entry's, [w35k]'s twice that less one (the let's bound) *)
Fixpoint w35r (r n : nat) (x : i63) : i63 := match r with O => let w := (n + n)%nat in w35k w x | S q => w35r q n (PrimInt63.add x 1) end.
Definition w35go2 (n : nat) (a b : i63) (s : mem) : i63 := w35r n (S n) a.
Definition w35b_src := ltac:(run_template_program (tmQuoteRec w35go2)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => sb (snd (fst x))) w35b_src = [Some (2 * own_bound + 1)%Z; Some (own_bound + 1)%Z; Some own_bound]).
Definition w35b_Pr := mkprog (funs_of 0 w35b_src) [].
Time Lemma w35bk_ok : callee_ok w35b_Pr (gid1 0) (fbound (sig_at w35b_src 0) 0) (sig_at w35b_src 0) w35k.
Proof. Time exact_no_check (compile_f_ok w35b_Pr [] gid1 0 (sig_at w35b_src 0) (body_at w35b_src 0) eq_refl eq_refl (no_callees w35b_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w35r_ok : callee_ok w35b_Pr (gid1 1) (fbound (sig_at w35b_src 1) 1) (sig_at w35b_src 1) w35r.
Proof.
  Time exact_no_check (compile_f_ok w35b_Pr [existT ftype (sig_at w35b_src 0) w35k] gid1 1 (sig_at w35b_src 1) (body_at w35b_src 1)
    eq_refl eq_refl (all_ok_callees w35b_Pr gid1 [existT ftype (sig_at w35b_src 0) w35k] (conj w35bk_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma w35go2_ok : callee_ok w35b_Pr (gid1 2) (fbound (sig_at w35b_src 2) 2) (sig_at w35b_src 2) w35go2.
Proof.
  Time exact_no_check (compile_f_ok w35b_Pr [existT ftype (sig_at w35b_src 0) w35k; existT ftype (sig_at w35b_src 1) w35r] gid1 2
    (sig_at w35b_src 2) (body_at w35b_src 2) eq_refl eq_refl
    (all_ok_callees w35b_Pr gid1 [existT ftype (sig_at w35b_src 0) w35k; existT ftype (sig_at w35b_src 1) w35r] (conj w35bk_ok (conj w35r_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions w35go2_ok.

(* ---- the constructs of the number sort in the boolean and record sorts (step 36): the construct table's shapes -- a boolean chosen
   by a test on a boolean, a number let in a later operand of [&&], a record taken apart in a test, a boolean-valued match on a sum;
   a pair chosen by a counter match, by a test on a boolean, by a match on a sum -- helpers written out where they are used *)
Definition x36_bif (n : nat) (a b : i63) : bool := if andb (PrimInt63.ltb a b) (PrimInt63.ltb b 10) then PrimInt63.eqb a b else false.
Definition x36_blet (n : nat) (a b : i63) : bool := andb (PrimInt63.ltb a b) (let c := PrimInt63.add a 1 in PrimInt63.ltb c 10).
Definition x36_bmr (n : nat) (a b : i63) : bool := let '(x, y) := (PrimInt63.add a 1, b) in PrimInt63.ltb x y.
Definition x36_badd (n : nat) (a b : i63) : bool := match (n + n)%nat with O => true | S _ => PrimInt63.ltb a b end.
Definition x36_pmc (n : nat) (a b : i63) : i63 * i63 := match n with O => (a, b) | S _ => (b, a) end.
Definition x36_pif (n : nat) (a b : i63) : i63 * i63 := if andb (PrimInt63.ltb a b) (PrimInt63.ltb b 10) then (a, b) else (b, a).
Definition x36_padd (n : nat) (a b : i63) : i63 * i63 := match (n + n)%nat with O => (a, b) | S _ => (b, a) end.
Definition x36go (n : nat) (a b : i63) (s : mem) : i63 :=
  PrimInt63.add (PrimInt63.add (if x36_bif n a b then 1 else 0) (if x36_blet n a b then 2 else 0))
   (PrimInt63.add (PrimInt63.add (if x36_bmr n a b then 4 else 0) (if x36_badd n a b then 8 else 0))
     (PrimInt63.add (let '(p, q) := x36_pmc n a b in PrimInt63.sub q p)
        (PrimInt63.add (let '(p, q) := x36_pif n a b in PrimInt63.sub q p) (let '(p, q) := x36_padd n a b in PrimInt63.sub q p)))).
Definition x36_src := ltac:(run_template_program (tmQuoteRec x36go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) x36_src = [FPlain
  (SOp Badd
     (SOp Badd
        (SIfB (BxIfB (BAnd (BCmp Clt (SVar 1) (SVar 0)) (BCmp Clt (SVar 0) (SInt 10))) (BCmp Ceq (SVar 1) (SVar 0)) BFalse) (SInt 1) (SInt 0))
        (SIfB (BAnd (BCmp Clt (SVar 1) (SVar 0)) (BxLet (SOp Badd (SVar 1) (SInt 1)) (BCmp Clt (SVar 0) (SInt 10)))) (SInt 2) (SInt 0)))
     (SOp Badd
        (SOp Badd
           (SIfB (BxMatchR (RMk 0 (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SVar 0) SNil))) (BCmp Clt (SVar 1) (SVar 0))) (SInt 4) (SInt 0))
           (SIfB (BxLetC (CAdd (CVar 0) (CVar 0)) (BMatchCnt 0 BTrue (BCmp Clt (SVar 1) (SVar 0)))) (SInt 8) (SInt 0)))
        (SOp Badd
           (SMatchR (RMatchCnt 0 0 (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil))))
              (SOp Bsub (SVar 0) (SVar 1)))
           (SOp Badd
              (SMatchR (RIfB 0 (BAnd (BCmp Clt (SVar 1) (SVar 0)) (BCmp Clt (SVar 0) (SInt 10)))
                          (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil))))
                 (SOp Bsub (SVar 0) (SVar 1)))
              (SMatchR (RLetC (CAdd (CVar 0) (CVar 0))
                          (RMatchCnt 0 0 (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) (RMk 0 (SCons (SVar 0) (SCons (SVar 1) SNil)))))
                 (SOp Bsub (SVar 0) (SVar 1)))))))]).
Check (eq_refl : map (fun x => sb (snd (fst x))) x36_src = [None]).
Section X36.
#[local] Instance x36_recs : RecTypes | 0 :=
  mkrecs (fun _ => (i63 * i63)%type) (fun _ => mkrops 2 None (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end)) (fun _ => (0%uint63, 0%uint63)).
#[local] Instance x36_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
Definition x36_Pr := mkprog (funs_of 0 x36_src) [].
Time Lemma x36go_ok : callee_ok x36_Pr (gid1 0) (fbound (sig_at x36_src 0) 0) (sig_at x36_src 0) x36go.
Proof.
  Time exact_no_check (@compile_f_ok x36_recs x36_laws x36_Pr [] gid1 0 (sig_at x36_src 0) (body_at x36_src 0) eq_refl eq_refl
    (no_callees x36_Pr gid1) eq_refl eq_refl).
Time Qed.
Print Assumptions x36go_ok.
End X36.

(* ---------------------------------------------------------------- counters grown by the recursion (step 37) *)
(* each function's weights found by the reifier, the smallest the check takes: k p (S m), k p (m + 2), a swap with a growth, a
   let-bound successor; the entry gives each its counters, their weighted sum below the callee's bound (worked out from the
   call graph); a counter grown by the first counter (quadratic) refused, with its reason *)
Fixpoint w37s (n m : nat) (x : i63) : i63 := match n with O => x | S p => w37s p (S m) (PrimInt63.add x 1) end.
Fixpoint w37t (n m : nat) (x : i63) : i63 := match n with O => x | S p => w37t p (m + 2) (PrimInt63.add x 1) end.
Fixpoint w37w (n a b : nat) (x : i63) : i63 := match n with O => x | S p => w37w p (S b) a (PrimInt63.add x 1) end.
Fixpoint w37l (n m : nat) (x : i63) : i63 := match n with O => x | S p => let q := S m in w37l p q (PrimInt63.add x 1) end.
Definition w37go (n : nat) (a b : i63) (s : mem) : i63 :=
  PrimInt63.add (PrimInt63.add (w37s n n a) (w37t n 0 b)) (PrimInt63.add (w37w n 1 n a) (w37l n n b)).
Definition w37_src := ltac:(run_template_program (tmQuoteRec w37go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (sv (snd (fst x)), sb (snd (fst x)))) w37_src =
  [(map lpoly [[1; 0]; [1; 1]]%nat, Some (own_w 2 (map lpoly [[1; 0]; [1; 1]]%nat)));
   (map lpoly [[1; 0]; [2; 1]]%nat, Some (own_w 2 (map lpoly [[1; 0]; [2; 1]]%nat)));
   (map lpoly [[1; 0; 0]; [1; 1; 1]]%nat, Some (own_w 3 (map lpoly [[1; 0; 0]; [1; 1; 1]]%nat)));
   (map lpoly [[1; 0]; [1; 1]]%nat, Some (own_w 2 (map lpoly [[1; 0]; [1; 1]]%nat)));
   ([], Some own_bound)]).
Check (eq_refl : map (fun x => snd x) w37_src =
  [FRec (SVar 0) (SRec (CCons (CS (CVar 1)) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil));
   FRec (SVar 0) (SRec (CCons (CAdd (CVar 1) (CS (CS CO))) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil));
   FRec (SVar 0) (SRec (CCons (CS (CVar 1)) (CCons (CVar 2) CNil)) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil));
   FRec (SVar 0) (SLetC (CS (CVar 1)) (SRec (CCons (CVar 0) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)));
   FPlain (SOp Badd (SOp Badd (SCall 0 (CCons (CVar 0) (CCons (CVar 0) CNil)) (SCons (SVar 1) SNil))
                              (SCall 1 (CCons (CVar 0) (CCons CO CNil)) (SCons (SVar 0) SNil)))
                    (SOp Badd (SCall 2 (CCons (CVar 0) (CCons (CS CO) (CCons (CVar 0) CNil))) (SCons (SVar 1) SNil))
                              (SCall 3 (CCons (CVar 0) (CCons (CVar 0) CNil)) (SCons (SVar 0) SNil))))]).
Definition w37_Pr := mkprog (funs_of 0 w37_src) [].
Time Lemma w37s_ok_r : callee_ok w37_Pr (gid1 0) (fbound (sig_at w37_src 0) 0) (sig_at w37_src 0) w37s.
Proof.
  Time exact_no_check (compile_f_ok w37_Pr [] gid1 0 (sig_at w37_src 0) (body_at w37_src 0)
    eq_refl eq_refl (no_callees w37_Pr gid1) eq_refl eq_refl).
Time Qed.
Time Lemma w37t_ok_r : callee_ok w37_Pr (gid1 1) (fbound (sig_at w37_src 1) 1) (sig_at w37_src 1) w37t.
Proof.
  Time exact_no_check (compile_f_ok w37_Pr [existT ftype (sig_at w37_src 0) w37s] gid1 1 (sig_at w37_src 1) (body_at w37_src 1)
    eq_refl eq_refl (all_ok_callees w37_Pr gid1 [existT ftype (sig_at w37_src 0) w37s] (conj w37s_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma w37w_ok_r : callee_ok w37_Pr (gid1 2) (fbound (sig_at w37_src 2) 2) (sig_at w37_src 2) w37w.
Proof.
  Time exact_no_check (compile_f_ok w37_Pr [existT ftype (sig_at w37_src 0) w37s; existT ftype (sig_at w37_src 1) w37t] gid1 2 (sig_at w37_src 2) (body_at w37_src 2)
    eq_refl eq_refl (all_ok_callees w37_Pr gid1 [existT ftype (sig_at w37_src 0) w37s; existT ftype (sig_at w37_src 1) w37t] (conj w37s_ok_r (conj w37t_ok_r Logic.I))) eq_refl eq_refl).
Time Qed.
Time Lemma w37l_ok_r : callee_ok w37_Pr (gid1 3) (fbound (sig_at w37_src 3) 3) (sig_at w37_src 3) w37l.
Proof.
  Time exact_no_check (compile_f_ok w37_Pr [existT ftype (sig_at w37_src 0) w37s; existT ftype (sig_at w37_src 1) w37t; existT ftype (sig_at w37_src 2) w37w] gid1 3 (sig_at w37_src 3) (body_at w37_src 3)
    eq_refl eq_refl (all_ok_callees w37_Pr gid1 [existT ftype (sig_at w37_src 0) w37s; existT ftype (sig_at w37_src 1) w37t; existT ftype (sig_at w37_src 2) w37w] (conj w37s_ok_r (conj w37t_ok_r (conj w37w_ok_r Logic.I)))) eq_refl eq_refl).
Time Qed.
Time Lemma w37go_ok_r : callee_ok w37_Pr (gid1 4) (fbound (sig_at w37_src 4) 4) (sig_at w37_src 4) w37go.
Proof.
  Time exact_no_check (compile_f_ok w37_Pr [existT ftype (sig_at w37_src 0) w37s; existT ftype (sig_at w37_src 1) w37t; existT ftype (sig_at w37_src 2) w37w; existT ftype (sig_at w37_src 3) w37l] gid1 4 (sig_at w37_src 4) (body_at w37_src 4)
    eq_refl eq_refl (all_ok_callees w37_Pr gid1 [existT ftype (sig_at w37_src 0) w37s; existT ftype (sig_at w37_src 1) w37t; existT ftype (sig_at w37_src 2) w37w; existT ftype (sig_at w37_src 3) w37l] (conj w37s_ok_r (conj w37t_ok_r (conj w37w_ok_r (conj w37l_ok_r Logic.I))))) eq_refl eq_refl).
Time Qed.
Print Assumptions w37go_ok_r.
Fixpoint w37q (n m : nat) (x : i63) : i63 := match n with O => x | S p => w37q p (m + p) (PrimInt63.add x 1) end.
Definition w37q_src := ltac:(run_template_program (tmQuoteRec w37q)
  (fun q => let r := eval vm_compute in (reify_prog q) in exact r)).
Check (eq_refl : w37q_src = None).
Eval vm_compute in ltac:(run_template_program (tmQuoteRec w37q) (fun q => let r := eval vm_compute in (reify_why q) in exact r)).
(* without weights: the recursion given the predecessor's successor, at most the first counter *)
Fixpoint w37p (n m : nat) (x : i63) : i63 := match n with O => x | S p => w37p p (S p) (PrimInt63.add x 1) end.
Definition w37p_src := ltac:(run_template_program (tmQuoteRec w37p)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (sv (snd (fst x)), snd x)) w37p_src =
  [([], FRec (SVar 0) (SRec (CCons (CS (CVar 0)) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)))]).
Definition w37p_Pr := mkprog (funs_of 0 w37p_src) [].
Time Lemma w37p_ok_r : callee_ok w37p_Pr (gid1 0) (fbound (sig_at w37p_src 0) 0) (sig_at w37p_src 0) w37p.
Proof. Time exact_no_check (compile_f_ok w37p_Pr [] gid1 0 (sig_at w37p_src 0) (body_at w37p_src 0) eq_refl eq_refl (no_callees w37p_Pr gid1) eq_refl eq_refl). Time Qed.

(* ---------------------------------------------------------------- counters grown apart (step 38) *)
(* two counters grown by one each round, given n n n by the entry: one vector per counter ([1; 0; 0], [1; 1; 0], [1; 0; 1]),
   each weighted sum at the entry's counters twice the smallest bound's value, where one sum of the three would pass 2^62 *)
Fixpoint w38d (n c d : nat) (x : i63) : i63 := match n with O => x | S p => w38d p (S c) (S d) (PrimInt63.add x 1) end.
Definition w38go (n : nat) (a b : i63) (s : mem) : i63 := w38d n n n a.
Definition w38_src := ltac:(run_template_program (tmQuoteRec w38go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (sv (snd (fst x)), sb (snd (fst x)))) w38_src =
  [(map lpoly [[1; 0; 0]; [1; 1; 0]; [1; 0; 1]]%nat, Some (2 * own_bound - 1)%Z); ([], Some own_bound)]).
Definition w38_Pr := mkprog (funs_of 0 w38_src) [].
Time Lemma w38d_ok_r : callee_ok w38_Pr (gid1 0) (fbound (sig_at w38_src 0) 0) (sig_at w38_src 0) w38d.
Proof. Time exact_no_check (compile_f_ok w38_Pr [] gid1 0 (sig_at w38_src 0) (body_at w38_src 0) eq_refl eq_refl (no_callees w38_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w38go_ok_r : callee_ok w38_Pr (gid1 1) (fbound (sig_at w38_src 1) 1) (sig_at w38_src 1) w38go.
Proof.
  Time exact_no_check (compile_f_ok w38_Pr [existT ftype (sig_at w38_src 0) w38d] gid1 1 (sig_at w38_src 1) (body_at w38_src 1)
    eq_refl eq_refl (all_ok_callees w38_Pr gid1 [existT ftype (sig_at w38_src 0) w38d] (conj w38d_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions w38go_ok_r.

(* ---------------------------------------------------------------- counters grown by other counters (step 39) *)
(* from written budgets: a counter grown by the predecessor (m + n^2), a counter grown by it (q + n m + n^3); their polynomials
   worked out by the reifier, each function's bound from what its caller gives it *)
Fixpoint w39q (n m : nat) (x : i63) : i63 := match n with O => x | S p => w39q p (m + p) (PrimInt63.add x 1) end.
Fixpoint w39c (n m q : nat) (x : i63) : i63 := match n with O => x | S p => w39c p (m + p) (q + m) (PrimInt63.add x 1) end.
Definition w39go (n : nat) (a b : i63) (s : mem) : i63 := PrimInt63.add (w39q 100 0 a) (w39c 50 0 0 b).
Definition w39_src := ltac:(run_template_program (tmQuoteRec w39go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => (sv (snd (fst x)), sb (snd (fst x)))) w39_src =
  [([lpoly [1; 0]; [(1, [1]); (1, [0; 0]); (0, [0])]]%nat, Some own_bound);
   ([lpoly [1; 0; 0]; [(1, [1]); (1, [0; 0]); (0, [0])]; [(1, [2]); (0, [0; 0]); (0, [0]); (1, [0; 1]); (1, [0; 0; 0]); (0, [0; 0])]]%nat,
    Some own_bound);
   ([], Some own_bound)]).
Definition w39_Pr := mkprog (funs_of 0 w39_src) [].
Time Lemma w39q_ok_r : callee_ok w39_Pr (gid1 0) (fbound (sig_at w39_src 0) 0) (sig_at w39_src 0) w39q.
Proof. Time exact_no_check (compile_f_ok w39_Pr [] gid1 0 (sig_at w39_src 0) (body_at w39_src 0) eq_refl eq_refl (no_callees w39_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w39c_ok_r : callee_ok w39_Pr (gid1 1) (fbound (sig_at w39_src 1) 1) (sig_at w39_src 1) w39c.
Proof.
  Time exact_no_check (compile_f_ok w39_Pr [existT ftype (sig_at w39_src 0) w39q] gid1 1 (sig_at w39_src 1) (body_at w39_src 1)
    eq_refl eq_refl (all_ok_callees w39_Pr gid1 [existT ftype (sig_at w39_src 0) w39q] (conj w39q_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma w39go_ok_r : callee_ok w39_Pr (gid1 2) (fbound (sig_at w39_src 2) 2) (sig_at w39_src 2) w39go.
Proof.
  Time exact_no_check (compile_f_ok w39_Pr [existT ftype (sig_at w39_src 0) w39q; existT ftype (sig_at w39_src 1) w39c] gid1 2
    (sig_at w39_src 2) (body_at w39_src 2) eq_refl eq_refl
    (all_ok_callees w39_Pr gid1 [existT ftype (sig_at w39_src 0) w39q; existT ftype (sig_at w39_src 1) w39c] (conj w39q_ok_r (conj w39c_ok_r Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions w39go_ok_r.
(* the same growth given n n from the data: the polynomial passes 2^62 at the entry's counters (the counter outgrows a machine
   number), refused *)
Definition w39d (n : nat) (a b : i63) (s : mem) : i63 := w39q n n a.
Definition w39d_src := ltac:(run_template_program (tmQuoteRec w39d) (fun q => let r := eval vm_compute in (reify_prog q) in exact r)).
Check (eq_refl : w39d_src = None).

(* ---------------------------------------------------------------- a function's bound from its callers, however small (step 40) *)
(* a recursive function passing small written counters on to one whose polynomial grows: its bound 101, its callee's above the
   polynomial at 100 *)
Fixpoint w40p (r n m : nat) (x : i63) : i63 := match r with O => w39q n m x | S q => w40p q n m (PrimInt63.add x 1) end.
Definition w40go (n : nat) (a b : i63) (s : mem) : i63 := w40p 3 100 0 a.
Definition w40_src := ltac:(run_template_program (tmQuoteRec w40go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => sb (snd (fst x))) w40_src = [Some 10101%Z; Some 101%Z; Some own_bound]).
Definition w40_Pr := mkprog (funs_of 0 w40_src) [].
Time Lemma w40q_ok_r : callee_ok w40_Pr (gid1 0) (fbound (sig_at w40_src 0) 0) (sig_at w40_src 0) w39q.
Proof. Time exact_no_check (compile_f_ok w40_Pr [] gid1 0 (sig_at w40_src 0) (body_at w40_src 0) eq_refl eq_refl (no_callees w40_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w40p_ok_r : callee_ok w40_Pr (gid1 1) (fbound (sig_at w40_src 1) 1) (sig_at w40_src 1) w40p.
Proof.
  Time exact_no_check (compile_f_ok w40_Pr [existT ftype (sig_at w40_src 0) w39q] gid1 1 (sig_at w40_src 1) (body_at w40_src 1)
    eq_refl eq_refl (all_ok_callees w40_Pr gid1 [existT ftype (sig_at w40_src 0) w39q] (conj w40q_ok_r Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma w40go_ok_r : callee_ok w40_Pr (gid1 2) (fbound (sig_at w40_src 2) 2) (sig_at w40_src 2) w40go.
Proof.
  Time exact_no_check (compile_f_ok w40_Pr [existT ftype (sig_at w40_src 0) w39q; existT ftype (sig_at w40_src 1) w40p] gid1 2
    (sig_at w40_src 2) (body_at w40_src 2) eq_refl eq_refl
    (all_ok_callees w40_Pr gid1 [existT ftype (sig_at w40_src 0) w39q; existT ftype (sig_at w40_src 1) w40p] (conj w40q_ok_r (conj w40p_ok_r Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions w40go_ok_r.

(* ---------------------------------------------------------------- parameters in any order (step 41) *)
(* the counter after a number, the memory before a number, the recursion on the second of two counters: each read in the order
   the syntax takes, as its wrapper (k__o), a call of it as a call of the wrapper; the theorems from the two equations *)
Fixpoint w41a (x : i63) (n : nat) : i63 := match n with O => x | S m => w41a (PrimInt63.add x 1) m end.
Fixpoint w41b (n : nat) (t : mem) (x : i63) : i63 := match n with O => PrimInt63.add x (KQ.KQRun.rd 0 0 t) | S m => w41b m t (PrimInt63.add x 1) end.
Fixpoint w41c (m n : nat) (x : i63) : i63 := match n with O => x | S p => w41c m p (PrimInt63.add x 1) end.
Definition w41go (n : nat) (a b : i63) (s : mem) : i63 := PrimInt63.add (PrimInt63.add (w41a a n) (w41b n s a)) (w41c n n b).
Definition w41_res := ltac:(run_template_program (tmQuoteRec w41go)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition w41_src := fst w41_res.
Check (eq_refl : map (fun x => (snd (fst (fst x)), snd x)) w41_src =
  [("KQC'_KQRReify'_w41a__o"%bs, FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)));
   ("KQC'_KQRReify'_w41b__o"%bs, FRec (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 0))) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)));
   ("KQC'_KQRReify'_w41c__o"%bs, FRec (SVar 0) (SRec (CCons (CVar 1) CNil) (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)));
   ("w41go"%bs, FPlain (SOp Badd (SOp Badd (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil)) (SCall 1 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil)))
                             (SCall 2 (CCons (CVar 0) (CCons (CVar 0) CNil)) (SCons (SVar 0) SNil))))]).
MetaRocq Run (tmMkDefinition "w41a_o"%bs (meaning_of (snd w41_res) "KQC'_KQRReify'_w41a__o"%bs)).
MetaRocq Run (tmMkDefinition "w41b_o"%bs (meaning_of (snd w41_res) "KQC'_KQRReify'_w41b__o"%bs)).
MetaRocq Run (tmMkDefinition "w41c_o"%bs (meaning_of (snd w41_res) "KQC'_KQRReify'_w41c__o"%bs)).
Definition w41_Pr := mkprog (funs_of 0 w41_src) [].
Time Lemma w41a_ok : callee_ok w41_Pr (gid1 0) (cbz 0) (sig_at w41_src 0) w41a_o.
Proof.
  Time exact_no_check (compile_f_okr w41_Pr [] gid1 0 0 (nk 1) false (fr0 (body_at w41_src 0)) (fr1 (body_at w41_src 0)) None [] w41a_o
    eq_refl eq_refl (no_callees w41_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Definition w41_cs1 := [existT ftype (sig_at w41_src 0) w41a_o].
Time Lemma w41b_ok : callee_ok w41_Pr (gid1 1) (cbz 1) (sig_at w41_src 1) w41b_o.
Proof.
  Time exact_no_check (compile_f_okr w41_Pr w41_cs1 gid1 1 0 (nk 1) true (fr0 (body_at w41_src 1)) (fr1 (body_at w41_src 1)) None [] w41b_o
    eq_refl eq_refl (all_ok_callees w41_Pr gid1 w41_cs1 (conj w41a_ok Logic.I)) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Definition w41_cs2 := [existT ftype (sig_at w41_src 0) w41a_o; existT ftype (sig_at w41_src 1) w41b_o].
Time Lemma w41c_ok : callee_ok w41_Pr (gid1 2) (cbz 2) (sig_at w41_src 2) w41c_o.
Proof.
  Time exact_no_check (compile_f_okr w41_Pr w41_cs2 gid1 2 1 (nk 1) false (fr0 (body_at w41_src 2)) (fr1 (body_at w41_src 2)) None [] w41c_o
    eq_refl eq_refl (all_ok_callees w41_Pr gid1 w41_cs2 (conj w41a_ok (conj w41b_ok Logic.I))) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Definition w41_cs3 := [existT ftype (sig_at w41_src 0) w41a_o; existT ftype (sig_at w41_src 1) w41b_o; existT ftype (sig_at w41_src 2) w41c_o].
Time Lemma w41go_ok : callee_ok w41_Pr (gid1 3) (cbz 3) (sig_at w41_src 3) w41go.
Proof.
  Time exact_no_check (compile_f_ok w41_Pr w41_cs3 gid1 3 (sig_at w41_src 3) (body_at w41_src 3) eq_refl eq_refl
    (all_ok_callees w41_Pr gid1 w41_cs3 (conj w41a_ok (conj w41b_ok (conj w41c_ok Logic.I)))) eq_refl eq_refl).
Time Qed.
Print Assumptions w41go_ok.
(* a function giving back a boolean, its counter after a number: its wrapper's theorem from the boolean copies' theorem *)
Fixpoint w41d (x : i63) (n : nat) : bool := match n with O => PrimInt63.ltb x 5 | S m => w41d (PrimInt63.add x 1) m end.
Definition w41dgo (n : nat) (a b : i63) (s : mem) : i63 := if w41d a n then 1 else 0.
Definition w41d_res := ltac:(run_template_program (tmQuoteRec w41dgo)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition w41d_src := fst w41d_res.
Check (eq_refl : map (fun x => snd (fst (fst x))) w41d_src = ["KQC'_KQRReify'_w41d__o"; "w41dgo"]%bs).
MetaRocq Run (tmMkDefinition "w41d_o"%bs (meaning_of (snd w41d_res) "KQC'_KQRReify'_w41d__o"%bs)).
Definition w41d_Pr := mkprog (funs_of 0 w41d_src) [].
Time Lemma w41d_ok : callee_ok w41d_Pr (gid1 0) (cbz 0) (sig_at w41d_src 0) w41d_o.
Proof.
  Time exact_no_check (compile_f_okrb w41d_Pr [] gid1 0 0 (nk 1) false (fbb0 (body_at w41d_src 0)) (fbb1 (body_at w41d_src 0)) None [] w41d_o
    eq_refl eq_refl (no_callees w41d_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma w41dgo_ok : callee_ok w41d_Pr (gid1 1) (cbz 1) (sig_at w41d_src 1) w41dgo.
Proof.
  Time exact_no_check (compile_f_ok w41d_Pr [existT ftype (sig_at w41d_src 0) w41d_o] gid1 1 (sig_at w41d_src 1) (body_at w41d_src 1) eq_refl eq_refl
    (all_ok_callees w41d_Pr gid1 [existT ftype (sig_at w41d_src 0) w41d_o] (conj w41d_ok Logic.I)) eq_refl eq_refl).
Time Qed.
(* a local fixpoint recursing on its second parameter, a template whose function comes first: their copies in the syntax's order *)
Definition w41l (n : nat) (a b : i63) (s : mem) : i63 :=
  let fix g (x : i63) (m : nat) : i63 := match m with O => x | S p => g (PrimInt63.add x 1) p end in g a n.
Fixpoint w41f (f : i63 -> i63) (n : nat) (x : i63) : i63 := match n with O => x | S m => w41f f m (f x) end.
Definition w41fgo (n : nat) (a b : i63) (s : mem) : i63 := PrimInt63.add (w41f (fun y => PrimInt63.add y 1) n a) (w41l n b a s).
Definition w41f_res := ltac:(run_template_program (tmQuoteRec w41fgo)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition w41f_src := fst w41f_res.
Check (eq_refl : map (fun x => (snd (fst (fst x)), snd x)) w41f_src =
  [("w41f__c0"%bs, FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)));
   ("kqlfix__c1"%bs, FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil)));
   ("w41fgo"%bs, FPlain (SOp Badd (SCall 0 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil)) (SCall 1 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil))))]).
MetaRocq Run (tmMkDefinition "w41f_c0"%bs (meaning_of (snd w41f_res) "w41f__c0"%bs)).
MetaRocq Run (tmMkDefinition "w41l_c1"%bs (meaning_of (snd w41f_res) "kqlfix__c1"%bs)).
Definition w41f_Pr := mkprog (funs_of 0 w41f_src) [].
Time Lemma w41f_ok : callee_ok w41f_Pr (gid1 0) (cbz 0) (sig_at w41f_src 0) w41f_c0.
Proof.
  Time exact_no_check (compile_f_okr w41f_Pr [] gid1 0 0 (nk 1) false (fr0 (body_at w41f_src 0)) (fr1 (body_at w41f_src 0)) None [] w41f_c0
    eq_refl eq_refl (no_callees w41f_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Definition w41f_cs1 := [existT ftype (sig_at w41f_src 0) w41f_c0].
Time Lemma w41l_ok : callee_ok w41f_Pr (gid1 1) (cbz 1) (sig_at w41f_src 1) w41l_c1.
Proof.
  Time exact_no_check (compile_f_okr w41f_Pr w41f_cs1 gid1 1 0 (nk 1) false (fr0 (body_at w41f_src 1)) (fr1 (body_at w41f_src 1)) None [] w41l_c1
    eq_refl eq_refl (all_ok_callees w41f_Pr gid1 w41f_cs1 (conj w41f_ok Logic.I)) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Definition w41f_cs2 := [existT ftype (sig_at w41f_src 0) w41f_c0; existT ftype (sig_at w41f_src 1) w41l_c1].
Time Lemma w41fgo_ok : callee_ok w41f_Pr (gid1 2) (cbz 2) (sig_at w41f_src 2) w41fgo.
Proof.
  Time exact_no_check (compile_f_ok w41f_Pr w41f_cs2 gid1 2 (sig_at w41f_src 2) (body_at w41f_src 2) eq_refl eq_refl
    (all_ok_callees w41f_Pr gid1 w41f_cs2 (conj w41f_ok (conj w41l_ok Logic.I))) eq_refl eq_refl).
Time Qed.

(* ---------------------------------------------------------------- captures of every kind (step 42) *)
(* a function given to a template naming a counter of the caller: the copy's counters the template's and the captured one *)
Fixpoint w42fold (n : nat) (i acc : i63) (f : i63 -> i63 -> i63) : i63 := match n with O => acc | S m => w42fold m (PrimInt63.add i 1) (f i acc) f end.
Definition w42go (n : nat) (a b : i63) (s : mem) : i63 := w42fold n 0 a (fun i acc => match n with O => acc | S _ => PrimInt63.add acc i end).
Definition w42_res := ltac:(run_template_program (tmQuoteRec w42go)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition w42_src := fst w42_res.
Check (eq_refl : map (fun x => (snd (fst (fst x)), sn (snd (fst x)), snd x)) w42_src =
  [("w42fold__c0"%bs, 2, FRec (SVar 0) (SRec (CCons (CVar 1) CNil) (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SMatch 1 (SVar 0) (SOp Badd (SVar 0) (SVar 1))) SNil))));
   ("w42go"%bs, 1, FPlain (SCall 0 (CCons (CVar 0) (CCons (CVar 0) CNil)) (SCons (SInt 0) (SCons (SVar 1) SNil))))]).
MetaRocq Run (tmMkDefinition "w42_c0"%bs (meaning_of (snd w42_res) "w42fold__c0"%bs)).
Definition w42_Pr := mkprog (funs_of 0 w42_src) [].
Time Lemma w42c_ok : callee_ok w42_Pr (gid1 0) (cbz 0) (sig_at w42_src 0) w42_c0.
Proof.
  Time exact_no_check (compile_f_okr w42_Pr [] gid1 0 1 (nk 2) false (fr0 (body_at w42_src 0)) (fr1 (body_at w42_src 0)) None [] w42_c0
    eq_refl eq_refl (no_callees w42_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma w42go_ok : callee_ok w42_Pr (gid1 1) (cbz 1) (sig_at w42_src 1) w42go.
Proof.
  Time exact_no_check (compile_f_ok w42_Pr [existT ftype (sig_at w42_src 0) w42_c0] gid1 1 (sig_at w42_src 1) (body_at w42_src 1) eq_refl eq_refl
    (all_ok_callees w42_Pr gid1 [existT ftype (sig_at w42_src 0) w42_c0] (conj w42c_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Print Assumptions w42go_ok.

(* ---- records holding records as values (step 43): [w43k] gives back a record holding a record, its own result bound by a let,
   taken apart one level and rebuilt from the inner record (RMkR); [w43go] takes one apart one level, gives the inner record to
   [w43pf] and takes it apart after a let.  The record table as kitc.py makes it: the one-level match and constructor of the
   record holding records, the others from their match and constructor *)
Fixpoint w43k (n : nat) (x y : i63) : (i63 * i63) * i63 :=
  match n with O => ((x, y), 0%uint63) | S m => let '(p, z) := w43k m y x in (p, PrimInt63.add z 1) end.
Fixpoint w43pf (n : nat) (p : i63 * i63) : i63 := match n with O => fst p | S m => w43pf m (snd p, fst p) end.
Definition w43go (n : nat) (a b : i63) (s : KQ.KQRun.mem) : i63 :=
  let '(p, z) := w43k n a b in let w := PrimInt63.add z 1 in
  PrimInt63.add (w43pf n p) (let '(u, v) := p in PrimInt63.add (PrimInt63.add w u) v).
Definition w43_rec := ltac:(run_template_program (tmQuoteRec w43go) (fun q => let r := eval vm_compute in (rec_info q) in exact r)).
Check (eq_refl : w43_rec = [("(Corelib.Init.Datatypes.prod (Corelib.Init.Datatypes.prod PrimInt63.int PrimInt63.int) PrimInt63.int)"%bs, "Corelib.Init.Datatypes.pair"%bs, 3, "N:Corelib.Init.Datatypes.pair(Corelib.Init.Datatypes.pair(i,i),i)@1"%bs);
                            ("(Corelib.Init.Datatypes.prod PrimInt63.int PrimInt63.int)"%bs, "Corelib.Init.Datatypes.pair"%bs, 2, ""%bs)]).
Definition w43_src := ltac:(run_template_program (tmQuoteRec w43go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) w43_src =
  [FRecR (BRet (RMk 0 (SCons (SInt 0) (SCons (SVar 1) (SCons (SVar 0) SNil)))))
         (BLetRec CNil (SCons (SVar 0) (SCons (SVar 1) SNil))
            (BSplitR 0 (RVar 0) (BRet (RMkR 0 (SCons (SOp Badd (SVar 0) (SInt 1)) SNil) (SConsR (RVar 0) SNil)))));
   FRec (SMatchR (RVar 0) (SVar 1))
        (SRec CNil (SConsR (RMk 1 (SCons (SMatchR (RVar 0) (SVar 0)) (SCons (SMatchR (RVar 0) (SVar 1)) SNil))) SNil));
   FPlain (SSplitR 0 (RCall 0 0 (CCons (CVar 0) CNil) (SCons (SVar 1) (SCons (SVar 0) SNil)))
             (SLet (SOp Badd (SVar 0) (SInt 1))
                (SOp Badd (SCall 1 (CCons (CVar 0) CNil) (SConsR (RVar 0) SNil))
                          (SMatchR (RVar 0) (SOp Badd (SOp Badd (SVar 2) (SVar 1)) (SVar 0))))))]).
Section W43.
Definition w43_rt (i : nat) : Type :=
  match i with O => (prod (prod PrimInt63.int PrimInt63.int) PrimInt63.int) | S O => (prod PrimInt63.int PrimInt63.int) | _ => unit end.
Definition w43_ro (i : nat) : rops (w43_rt i) :=
  match i as i0 return rops (w43_rt i0) with
  | O => mkrops 3%nat None (fun l => (pair (pair (nth 1%nat l 0%uint63) (nth 2%nat l 0%uint63)) (nth 0%nat l 0%uint63)))
                (fun P v k => match v with pair v1 v2 => match v1 with pair v3 v4 => k (cons v2 (cons v3 (cons v4 nil))) end end)
  | S O => mkrops 2%nat None (fun l => pair (nth 0%nat l 0%uint63) (nth 1%nat l 0%uint63)) (fun P v k => match v with pair x0 x1 => k (cons x0 (cons x1 nil)) end)
  | _ => mkrops 0%nat None (fun _ => tt) (fun P _ k => k nil) end.
Definition w43_rd (i : nat) : w43_rt i := match i as i0 return w43_rt i0 with O => (pair (pair 0%uint63 0%uint63) 0%uint63) | S O => pair 0%uint63 0%uint63 | _ => tt end.
Definition w43_rs (i : nat) : forall P : Type, w43_rt i -> (list PrimInt63.int -> list (sigT w43_rt) -> P) -> P :=
  match i as i0 return forall P : Type, w43_rt i0 -> (list PrimInt63.int -> list (sigT w43_rt) -> P) -> P with
  | O => fun P v k => match v with pair v0 v1 => k (cons v1 nil) (cons (existT w43_rt 1%nat v0) nil) end
  | S O => fun P v k => relim (w43_ro (S O)) v (fun l => k l nil)
  | _ => fun P _ k => k nil nil end.
Definition w43_rb (i : nat) : list PrimInt63.int -> list (sigT w43_rt) -> w43_rt i :=
  match i as i0 return list PrimInt63.int -> list (sigT w43_rt) -> w43_rt i0 with
  | O => fun l rs => (pair (tk w43_rd 1%nat (nth 0%nat rs (existT w43_rt 1%nat (w43_rd 1%nat)))) (nth 0%nat l 0%uint63))
  | S O => fun l _ => rmk (w43_ro (S O)) l
  | _ => fun _ _ => tt end.
Definition w43_rj (i : nat) : list nat := match i with O => (cons 1%nat nil) | _ => nil end.
#[local] Instance w43_recs : RecTypes | 0 :=
  {| RT := w43_rt; RO := w43_ro; Rd := w43_rd; RS := w43_rs; RB := w43_rb; RJ := w43_rj;
     RBl := fun i _ => w43_rd i; RTb := fun _ _ => false; RBI := fun _ => false; RNC := fun _ => false; RM := fun _ _ => nil |}.
#[local] Instance w43_laws : @RecLaws w43_recs.
Proof. split.
- intros i x P k. destruct i as [|[|i]]; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].
- intros i x. destruct i as [|[|i]]; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].
- intros i l E L _. destruct i as [|[|i]]; cbn in E, L; try discriminate E; repeat (destruct l as [|? l]; try discriminate L); reflexivity.
- intros i ws c rest E Lc Lr Hz _. destruct i as [|[|i]]; cbn in E; try discriminate E; injection E as <-; kq_tag_case.
- intros i x P k. destruct i as [|[|i]]; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].
- intros i x. destruct i as [|[|i]]; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].
- intros i x. destruct i as [|[|i]]; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].
- intros i l rs G Hk Hl. destruct i as [|[|i]]; cbn in G, Hk; try discriminate G; kq_rb_case.
- intros i ws c rest rs E. destruct i as [|[|i]]; cbn in E; discriminate E.
- intros i b E; discriminate E.
- intros i x E; discriminate E.
Qed.
Definition w43_Pr := mkprog (funs_of 0 w43_src) [].
Time Lemma w43k_ok : callee_ok w43_Pr (gid1 0) (cbz 0) (sig_at w43_src 0) w43k.
Proof. Time exact_no_check (compile_f_ok w43_Pr [] gid1 0 (sig_at w43_src 0) (body_at w43_src 0) eq_refl eq_refl (no_callees w43_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w43pf_ok : callee_ok w43_Pr (gid1 1) (cbz 1) (sig_at w43_src 1) w43pf.
Proof.
  Time exact_no_check (compile_f_ok w43_Pr [existT ftype (sig_at w43_src 0) w43k] gid1 1 (sig_at w43_src 1) (body_at w43_src 1)
    eq_refl eq_refl (all_ok_callees w43_Pr gid1 [existT ftype (sig_at w43_src 0) w43k] (conj w43k_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma w43go_ok : callee_ok w43_Pr (gid1 2) (cbz 2) (sig_at w43_src 2) w43go.
Proof.
  Time exact_no_check (compile_f_ok w43_Pr [existT ftype (sig_at w43_src 0) w43k; existT ftype (sig_at w43_src 1) w43pf] gid1 2
    (sig_at w43_src 2) (body_at w43_src 2) eq_refl eq_refl
    (all_ok_callees w43_Pr gid1 [existT ftype (sig_at w43_src 0) w43k; existT ftype (sig_at w43_src 1) w43pf] (conj w43k_ok (conj w43pf_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions w43go_ok.
End W43.

(* ---- a memory taking a number-and-memory pair apart (step 44): [w44wm] takes apart the pair [w44g] gives it, the number below
   the memory; the helper [w44lm], written out in [w44go], binds the pair by a let and reads it through fst and snd *)
Fixpoint w44g (n : nat) (x : i63) (t : KQ.KQRun.mem) : i63 * KQ.KQRun.mem :=
  match n with O => (x, t) | S m => w44g m (PrimInt63.add x 1) (KQ.KQRun.upd 0 x x t) end.
Fixpoint w44wm (n : nat) (x : i63) (t : KQ.KQRun.mem) : KQ.KQRun.mem :=
  match n with O => t | S m => let '(y, t2) := w44g n x t in w44wm m y (KQ.KQRun.upd 1 y y t2) end.
Definition w44lm (n : nat) (x : i63) (t : KQ.KQRun.mem) : KQ.KQRun.mem := let w := w44g n x t in KQ.KQRun.upd 2 (fst w) 0 (snd w).
Definition w44go (n : nat) (a b : i63) (s : KQ.KQRun.mem) : i63 := KQ.KQRun.rd 0 0 (w44lm n b (w44wm n a s)).
Definition w44_src := ltac:(run_template_program (tmQuoteRec w44go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) w44_src =
  [FRecP (PvMk (SVar 0) MCur) (PvRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil) (MUpd (SInt 0) (SVar 0) (SVar 0) MCur));
   FRecM MCur (MMatchP (PvCall 0 (CCons (CVar 1) CNil) (SCons (SVar 0) SNil) MCur)
                       (MRec CNil (SCons (SVar 0) SNil) (MUpd (SInt 1) (SVar 0) (SVar 0) MCur)));
   FPlainX (XLetM (MLetM (MCall 1 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil) MCur)
                         (MLetP (PvCall 0 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil) MCur)
                                (MUpd (SInt 2) (SLet (SVar 0) (SVar 0)) (SInt 0) (MLetM MCur MCur))))
                  (XRet (SRd (SInt 0) (SInt 0))))]).
Definition w44_Pr := mkprog (funs_of 0 w44_src) [].
Time Lemma w44g_ok : callee_ok w44_Pr (gid1 0) (cbz 0) (sig_at w44_src 0) w44g.
Proof. Time exact_no_check (compile_f_ok w44_Pr [] gid1 0 (sig_at w44_src 0) (body_at w44_src 0) eq_refl eq_refl (no_callees w44_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w44wm_ok : callee_ok w44_Pr (gid1 1) (cbz 1) (sig_at w44_src 1) w44wm.
Proof.
  Time exact_no_check (compile_f_ok w44_Pr [existT ftype (sig_at w44_src 0) w44g] gid1 1 (sig_at w44_src 1) (body_at w44_src 1)
    eq_refl eq_refl (all_ok_callees w44_Pr gid1 [existT ftype (sig_at w44_src 0) w44g] (conj w44g_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma w44go_ok : callee_ok w44_Pr (gid1 2) (cbz 2) (sig_at w44_src 2) w44go.
Proof.
  Time exact_no_check (compile_f_ok w44_Pr [existT ftype (sig_at w44_src 0) w44g; existT ftype (sig_at w44_src 1) w44wm] gid1 2
    (sig_at w44_src 2) (body_at w44_src 2) eq_refl eq_refl
    (all_ok_callees w44_Pr gid1 [existT ftype (sig_at w44_src 0) w44g; existT ftype (sig_at w44_src 1) w44wm] (conj w44g_ok (conj w44wm_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions w44go_ok.

(* ---- a number-and-memory pair as a parameter (step 44 continued): [w44bk] takes the pair last -- read on its components, its
   signature flagged; [w44bgo] calls it given the pair [w44bg] gives (XCallP).  [w44bk]'s theorem from the theorem of
   its components' function ([callee_ok_unpair]), that one from its two equations *)
Fixpoint w44bk (n : nat) (p : i63 * KQ.KQRun.mem) : i63 :=
  match n with O => fst p | S m => w44bk m (PrimInt63.add (fst p) (KQ.KQRun.rd 0 0 (snd p)), snd p) end.
Fixpoint w44bg (n : nat) (x : i63) (t : KQ.KQRun.mem) : i63 * KQ.KQRun.mem :=
  match n with O => (x, t) | S m => w44bg m (PrimInt63.add x 1) (KQ.KQRun.upd 0 x x t) end.
Definition w44bgo (n : nat) (a b : i63) (s : KQ.KQRun.mem) : i63 := w44bk n (w44bg n a s).
Definition w44b_src := ltac:(run_template_program (tmQuoteRec w44bgo)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) w44b_src =
  [FRec (SVar 0) (SRec CNil (SCons (SOp Badd (SVar 0) (SRd (SInt 0) (SInt 0))) SNil));
   FRecP (PvMk (SVar 0) MCur) (PvRec CNil (SCons (SOp Badd (SVar 0) (SInt 1)) SNil) (MUpd (SInt 0) (SVar 0) (SVar 0) MCur));
   FPlainX (XCallP 0 (CCons (CVar 0) CNil) SNil (PvCall 1 (CCons (CVar 0) CNil) (SCons (SVar 1) SNil) MCur))]).
Check (eq_refl : map (fun x => snd (fst x)) w44b_src =
  [mksig9 1 [KNum] true false false None None [] true; mksig8 1 [KNum] true false false (Some KNum) None [];
   mksig8 1 [KNum; KNum] true false true None None []]).
Definition w44b_Pr := mkprog (funs_of 0 w44b_src) [].
Time Lemma w44bk_ok : callee_ok w44b_Pr (gid1 0) (cbz 0) (sig_at w44b_src 0) w44bk.
Proof.
  Time exact_no_check (callee_ok_unpair w44b_Pr (gid1 0) (cbz 0) 1 [KNum] false false None None nil w44bk
    (compile_f_okr w44b_Pr [] gid1 0 0 [KNum] true (fr0 (body_at w44b_src 0)) (fr1 (body_at w44b_src 0)) None []%nat
       (cmapT 1 (ntypeTP [KNum] (rtq false None)) (ntypeT [KNum] true (rtq false None)) (unpairT [KNum] (rtq false None)) w44bk)
       eq_refl eq_refl (no_callees w44b_Pr gid1) eq_refl eq_refl eq_refl (fun n => ltac:(reflexivity)))).
Time Qed.
Time Lemma w44bg_ok : callee_ok w44b_Pr (gid1 1) (cbz 1) (sig_at w44b_src 1) w44bg.
Proof.
  Time exact_no_check (compile_f_ok w44b_Pr [existT ftype (sig_at w44b_src 0) w44bk] gid1 1 (sig_at w44b_src 1) (body_at w44b_src 1)
    eq_refl eq_refl (all_ok_callees w44b_Pr gid1 [existT ftype (sig_at w44b_src 0) w44bk] (conj w44bk_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma w44bgo_ok : callee_ok w44b_Pr (gid1 2) (cbz 2) (sig_at w44b_src 2) w44bgo.
Proof.
  Time exact_no_check (compile_f_ok w44b_Pr [existT ftype (sig_at w44b_src 0) w44bk; existT ftype (sig_at w44b_src 1) w44bg] gid1 2
    (sig_at w44b_src 2) (body_at w44b_src 2) eq_refl eq_refl
    (all_ok_callees w44b_Pr gid1 [existT ftype (sig_at w44b_src 0) w44bk; existT ftype (sig_at w44b_src 1) w44bg] (conj w44bk_ok (conj w44bg_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
Print Assumptions w44bgo_ok.
(* ---- a mutual block of any signature (step 45): [w45a] and [w45b] give back a memory, [w45b] has a parameter more and its
   counter second.  The block is one function, their parameters in shared slots, a call between them its own recursive call;
   its meaning [blkT] of their views, its theorem from its two equations ([compile_f_okrm]); [w45a] one call of it ([w45b],
   which the program does not name, nothing) *)
Fixpoint w45a (n : nat) (x : i63) (t : KQ.KQRun.mem) : KQ.KQRun.mem :=
  match n with O => t | S m => w45b (PrimInt63.add x 1) m x (KQ.KQRun.upd 0 x x t) end
with w45b (x : i63) (n : nat) (y : i63) (t : KQ.KQRun.mem) : KQ.KQRun.mem :=
  match n with O => KQ.KQRun.upd 1 y x t | S m => w45a m (PrimInt63.add x y) t end.
Definition w45go (n : nat) (a : i63) (s : KQ.KQRun.mem) : i63 := KQ.KQRun.rd 0 0 (w45a n a s).
Definition w45_res := ltac:(run_template_program (tmQuoteRec w45go)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition w45_src := fst w45_res.
Check (eq_refl : map (fun x => snd x) w45_src =
  [FRecM (MMatch 0 MCur (MUpd (SInt 1) (SVar 0) (SVar 1) MCur))
     (MMatch 1 (MRec (CCons (CNat (SInt 1)) CNil) (SCons (SOp Badd (SVar 1) (SInt 1)) (SCons (SVar 1) SNil)) (MUpd (SInt 0) (SVar 1) (SVar 1) MCur))
        (MRec (CCons (CNat (SInt 0)) CNil) (SCons (SOp Badd (SVar 1) (SVar 0)) (SCons (SVar 0) SNil)) MCur));
   FPlainM (MCall 0 (CCons (CVar 0) (CCons (CNat (SInt 0)) CNil)) (SCons (SVar 0) (SCons (SInt 0) SNil)) MCur);
   FPlainX (XLetM (MCall 1 (CCons (CVar 0) CNil) (SCons (SVar 0) SNil) MCur) (XRet (SRd (SInt 0) (SInt 0))))]).
Check (eq_refl : map (fun x => snd (fst x)) w45_src =
  [mksig8 2 [KNum; KNum] true true false None None []; mksig8 1 [KNum] true true false None None [];
   mksig8 1 [KNum] true false true None None []]).
MetaRocq Run (tmMkDefinition "w45blk"%bs (meaning_of (snd w45_res) "KQC'_KQRReify'_w45a__cblk"%bs)).
Definition w45_Pr := mkprog (funs_of 0 w45_src) [].
Time Lemma w45blk_ok : callee_ok w45_Pr (gid1 0) (cbz 0) (sig_at w45_src 0) w45blk.
Proof.
  Time exact_no_check (compile_f_okrm w45_Pr [] gid1 0 1 [KNum; KNum] true (fm0 (body_at w45_src 0)) (fm1 (body_at w45_src 0)) None [] w45blk
    eq_refl eq_refl (no_callees w45_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma w45a_ok : callee_ok w45_Pr (gid1 1) (cbz 1) (sig_at w45_src 1) w45a.
Proof.
  Time exact_no_check (compile_f_ok w45_Pr [existT ftype (sig_at w45_src 0) w45blk] gid1 1 (sig_at w45_src 1) (body_at w45_src 1)
    eq_refl eq_refl (all_ok_callees w45_Pr gid1 [existT ftype (sig_at w45_src 0) w45blk] (conj w45blk_ok Logic.I)) eq_refl eq_refl).
Time Qed.
Time Lemma w45go_ok : callee_ok w45_Pr (gid1 2) (cbz 2) (sig_at w45_src 2) w45go.
Proof.
  Time exact_no_check (compile_f_ok w45_Pr [existT ftype (sig_at w45_src 0) w45blk; existT ftype (sig_at w45_src 1) w45a] gid1 2
    (sig_at w45_src 2) (body_at w45_src 2) eq_refl eq_refl
    (all_ok_callees w45_Pr gid1 [existT ftype (sig_at w45_src 0) w45blk; existT ftype (sig_at w45_src 1) w45a] (conj w45blk_ok (conj w45a_ok Logic.I)))
    eq_refl eq_refl).
Time Qed.
(* ---- a template of any signature (step 46): [w46foldp] takes a record (a pair of numbers) and gives one back, and is given a
   function; its copy for [fun z => z + 1] read as a function giving back a record, its theorem from its two equations
   ([compile_f_okrr]) *)
Fixpoint w46foldp (n : nat) (p : i63 * i63) (g : i63 -> i63) : i63 * i63 :=
  match n with O => p | S m => w46foldp m (g (fst p), PrimInt63.add (snd p) 1) g end.
Definition w46go (n : nat) (a b : i63) (s : KQ.KQRun.mem) : i63 :=
  let '(x, y) := w46foldp n (a, b) (fun z => PrimInt63.add z 1) in PrimInt63.add x y.
Definition w46_res := ltac:(run_template_program (tmQuoteRec w46go)
  (fun q => let r := eval vm_compute in (reify_prog2 q) in match r with Some ?x => exact x end)).
Definition w46_src := fst w46_res.
Check (eq_refl : map (fun x => snd x) w46_src =
  [FRecR (BRet (RVar 0))
     (BRec CNil (SConsR (RMk 0 (SCons (SLet (SMatchR (RVar 0) (SVar 1)) (SOp Badd (SVar 0) (SInt 1)))
                                      (SCons (SOp Badd (SMatchR (RVar 0) (SVar 0)) (SInt 1)) SNil))) SNil));
   FPlain (SMatchR (RCall 0 0 (CCons (CVar 0) CNil) (SConsR (RMk 0 (SCons (SVar 1) (SCons (SVar 0) SNil))) SNil)) (SOp Badd (SVar 1) (SVar 0)))]).
Check (eq_refl : map (fun x => snd (fst x)) w46_src =
  [mksig8 1 [KRec 0] false false false (Some (KRec 0)) None []; mksig8 1 [KNum; KNum] true false false None None []]).
MetaRocq Run (tmMkDefinition "w46cp"%bs (meaning_of (snd w46_res) "w46foldp__c0"%bs)).
Section W46.
#[local] Instance w46_recs : RecTypes | 0 :=
  mkrecs (fun _ => (i63 * i63)%type) (fun _ => mkrops 2 None (fun l => (nth 0 l 0%uint63, nth 1 l 0%uint63)) (fun P v k => match v with (a, b) => k [a; b] end)) (fun _ => (0%uint63, 0%uint63)).
#[local] Instance w46_laws : RecLaws.
Proof. apply laws_of; [intros i [a b] P k; reflexivity | intros i [a b]; reflexivity | intros i [|a [|b [|c l]]] E L; try discriminate; reflexivity | intros i ws c rest E; discriminate E]. Qed.
Definition w46_Pr := mkprog (funs_of 0 w46_src) [].
Time Lemma w46cp_ok : callee_ok w46_Pr (gid1 0) (cbz 0) (sig_at w46_src 0) w46cp.
Proof.
  Time exact_no_check (@compile_f_okrr w46_recs w46_laws w46_Pr [] gid1 0 0 [KRec 0] false (fbr0 (body_at w46_src 0)) (fbr1 (body_at w46_src 0)) None [] 0 w46cp
    eq_refl eq_refl (no_callees w46_Pr gid1) eq_refl eq_refl eq_refl (fun n => eq_refl)).
Time Qed.
Time Lemma w46go_ok : callee_ok w46_Pr (gid1 1) (cbz 1) (sig_at w46_src 1) w46go.
Proof.
  Time exact_no_check (@compile_f_ok w46_recs w46_laws w46_Pr [existT ftype (sig_at w46_src 0) w46cp] gid1 1 (sig_at w46_src 1) (body_at w46_src 1)
    eq_refl eq_refl (all_ok_callees w46_Pr gid1 [existT ftype (sig_at w46_src 0) w46cp] (conj w46cp_ok Logic.I)) eq_refl eq_refl).
Time Qed.
End W46.
(* ---- a call inside an expression that writes the memory (step 47): [w47go] reads the memory and adds what [w47wr] gives,
   which writes it -- the read bound first, then the call (XBind), the sum after it reading no memory *)
Fixpoint w47wr (n : nat) (t : KQ.KQRun.mem) : i63 :=
  match n with O => KQ.KQRun.rd 0 0 t | S m => w47wr m (KQ.KQRun.upd 0 0 (PrimInt63.add (KQ.KQRun.rd 0 0 t) 1) t) end.
Definition w47go (n : nat) (a : i63) (s : KQ.KQRun.mem) : i63 := PrimInt63.add (KQ.KQRun.rd 1 0 s) (w47wr n s).
Definition w47_src := ltac:(run_template_program (tmQuoteRec w47go)
  (fun q => let r := eval vm_compute in (reify_prog q) in match r with Some ?x => exact x end)).
Check (eq_refl : map (fun x => snd x) w47_src =
  [FRecX (XRet (SRd (SInt 0) (SInt 0))) (XRec CNil SNil (MUpd (SInt 0) (SInt 0) (SOp Badd (SRd (SInt 0) (SInt 0)) (SInt 1)) MCur));
   FPlainX (XLet (SRd (SInt 1) (SInt 0)) (XBind false 0 (CCons (CVar 0) CNil) SNil MCur (XRet (SOp Badd (SVar 1) (SVar 0)))))]).
Definition w47_Pr := mkprog (funs_of 0 w47_src) [].
Time Lemma w47wr_ok : callee_ok w47_Pr (gid1 0) (cbz 0) (sig_at w47_src 0) w47wr.
Proof. Time exact_no_check (compile_f_ok w47_Pr [] gid1 0 (sig_at w47_src 0) (body_at w47_src 0) eq_refl eq_refl (no_callees w47_Pr gid1) eq_refl eq_refl). Time Qed.
Time Lemma w47go_ok : callee_ok w47_Pr (gid1 1) (cbz 1) (sig_at w47_src 1) w47go.
Proof.
  Time exact_no_check (compile_f_ok w47_Pr [existT ftype (sig_at w47_src 0) w47wr] gid1 1 (sig_at w47_src 1) (body_at w47_src 1)
    eq_refl eq_refl (all_ok_callees w47_Pr gid1 [existT ftype (sig_at w47_src 0) w47wr] (conj w47wr_ok Logic.I)) eq_refl eq_refl).
Time Qed.
