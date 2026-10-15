(* KQShape.v -- A FIRST CHECKER FOR "C-SHAPED" ROCQ (spike, 2026-10-13; nothing here is proved yet).

   `MetaRocq Run (kq_shape main).` reads the program `main` and everything of the same file it uses, and checks:

     the MEMORY rule, everywhere:   a memory that has been handed on (written, or given to a function that may
                                    write it) is never touched again.  A READER -- a function of the file that
                                    gives back a plain number (an int, a boolean, a nat) and in which nothing,
                                    however far down its calls, writes -- only looks: the memory given to it stays
                                    usable;
     and in every LOOP (a recursive function, and whatever such a function calls):
       VALUES    nothing is built (no constructor with arguments; a `nat` is a machine number here, KQNat.v, so `S n`
                 builds nothing) and nothing is taken apart except a boolean and a nat;
       CONTROL   a function that calls itself ONCE on a path does so as its last step (a loop); a function that calls
                 itself two or more times on a path (a tree: a segment tree, a divide and conquer) may do so anywhere --
                 each such call is a real call, as in C.  No function is made or passed as a value; only
                 machine-integer operations, the memory operations and the file's own functions are called.

   It answers with one line per refusal, naming the function.  A walk of the program's text: it always ends.

   It also gives ADVICE (it never refuses for these): two of the rules of WRITING-FAST-ROCQ.md that a walk of the text
   can see --
       rule 1   a loop reads AND writes the same fixed cell (`rd rST 2 ..` and `upd rST 2 ..`): that number is loop
                state kept in memory; carry it as a parameter;
       rule 4   both arms of an `if` go round the loop and differ only in numbers: put the `if` inside one call. *)
From MetaRocq.Utils Require Import utils bytestring Show.
From MetaRocq.Template Require Import All.
Import MonadNotation ListNotations.
Open Scope bs.
Open Scope list_scope.

Inductive bk := BMem | BSelf | BOther.

Definition eq_mp (a b : modpath) : bool := match ModPathComp.compare a b with Eq => true | _ => false end.

Definition mp_head (mp : modpath) : string :=
  match mp with MPfile (x :: _) => x | _ => "" end.
Definition is_prim (kn : kername) : bool := String.eqb (mp_head (fst kn)) "PrimInt63".
Definition is_kq (kn : kername) (id : string) : bool :=
  (String.eqb (mp_head (fst kn)) "KQRun" || String.eqb (mp_head (fst kn)) "KQBound") && String.eqb (snd kn) id.
Definition is_boolfn (kn : kername) : bool :=
  String.eqb (mp_head (fst kn)) "Datatypes" && existsb (String.eqb (snd kn)) ["andb"; "orb"; "negb"; "xorb"].
Definition is_mem_ty (t : term) : bool :=
  match t with tConst kn _ => is_kq kn "mem" | _ => false end.
Definition ind_name (i : inductive) : string := snd (inductive_mind i).

(* A ROUTINE DECLARED WITHOUT A BODY (an Axiom: the memory's operations, the machine's, a library's, a program's own,
   linked to C or assembly by name) is a machine operation: it may be called in a loop.  Nothing here knows any of their
   names; what such a routine does to the memory is read off its type (below: a writer, unless its result is a plain
   number). *)
Definition is_decl (Σ : global_env) (kn : kername) : bool :=
  match lookup_env Σ kn with Some (ConstantDecl cb) => match cst_body cb with None => true | Some _ => false end | _ => false end.
Definition ctor_info (Σ : global_env) (ind : inductive) (i : nat) : string * nat :=
  match lookup_env Σ (inductive_mind ind) with
  | Some (InductiveDecl mib) =>
      match nth_error (ind_bodies mib) (inductive_ind ind) with
      | Some oib => match nth_error (ind_ctors oib) i with
                    | Some c => (cstr_name c, cstr_arity c)
                    | None => ("?", 0)
                    end
      | None => ("?", 0)
      end
  | _ => ("?", 0)
  end.

Definition bname (na : aname) : string :=
  match binder_name na with nNamed id => id | nAnon => "_" end.

Definition memk (kn : kername) (l : list kername) : bool := existsb (Kername.eqb kn) l.
(* the integer functions of the library that are one machine operation each (`- x` is `0 - x`) *)
Definition is_intfn (kn : kername) : bool :=
  (String.eqb (mp_head (fst kn)) "Uint63" || String.eqb (mp_head (fst kn)) "Sint63")
  && existsb (String.eqb (snd kn)) ["opp"; "succ"; "pred"].

(* how many times a function calls itself on one path through this text, at most *)
Fixpoint ncalls (fuel : nat) (ctx : list (bk * string)) (t : term) : nat :=
  match fuel with
  | O => 0
  | S fuel =>
    match t with
    | tApp f args =>
        (match f with
         | tRel n => match nth_error ctx n with Some (BSelf, _) => 1 | _ => 0 end
         | _ => ncalls fuel ctx f
         end) + fold_left (fun a x => a + ncalls fuel ctx x) args 0
    | tLetIn na d _ b => ncalls fuel ctx d + ncalls fuel ((BOther, bname na) :: ctx) b
    | tLambda na _ b => ncalls fuel ((BOther, bname na) :: ctx) b
    | tCase _ _ d brs =>
        ncalls fuel ctx d
        + fold_left (fun a (b : branch term) =>
                       Nat.max a (ncalls fuel (map (fun na => (BOther, bname na)) (bcontext b) ++ ctx) (bbody b))) brs 0
    | tCast t _ _ => ncalls fuel ctx t
    | tProj _ t => ncalls fuel ctx t
    | _ => 0
    end
  end.

Section Walk.
  (* readers: the file's functions that only look at a memory;  self_rd: the function being read is one of them;
     tree: it calls itself two or more times on some path *)
  Context (Σ : global_env) (mp : modpath) (hot : bool) (readers : list kername) (self_rd tree : bool).

  Definition user (kn : kername) : bool := eq_mp (fst kn) mp.

  (* the state: the memories already handed on, by their position in the context counted from the outside *)
  Definition lvl (ctx : list (bk * string)) (n : nat) : nat := #|ctx| - 1 - n.
  Definition isdead (dead : list nat) (l : nat) : bool := existsb (Nat.eqb l) dead.
  Definition vname (ctx : list (bk * string)) (n : nat) : string :=
    match nth_error ctx n with Some (_, s) => s | None => "?" end.

  (* ---- for the advice of rule 4: is this argument a plain number (variables, constants, machine operations, reads)? *)
  Fixpoint strip (t : term) : term :=
    match t with
    | tLetIn _ d _ (tRel 0) => strip d
    | tCast t _ _ => strip t
    | _ => t
    end.
  Fixpoint pure_int (fuel : nat) (ctx : list (bk * string)) (t : term) : bool :=
    match fuel with
    | O => false
    | S fuel =>
      match t with
      | tInt _ => true
      | tRel n => match nth_error ctx n with Some (BOther, _) => true | _ => false end
      | tConst kn _ => user kn || is_prim kn
      | tCast t _ _ => pure_int fuel ctx t
      | tApp (tConst kn _) args =>
          if is_kq kn "rd" || is_kq kn "rd32" || is_kq kn "rd_u" || is_kq kn "rd32_u" then
            match args with
            | [h; i; tRel _] => pure_int fuel ctx h && pure_int fuel ctx i
            | _ => false
            end
          else (is_prim kn || (String.eqb (mp_head (fst kn)) "KQRun" && negb (is_kq kn "upd") && negb (is_kq kn "upd32") && negb (is_kq kn "upd_u") && negb (is_kq kn "upd32_u")
                && negb (is_kq kn "kq_input")))
               && forallb (pure_int fuel ctx) args
      | _ => false
      end
    end.
  (* two argument lists of the same call: the memories are the same variables, everything else is a plain number *)
  Fixpoint same_shape (ctx : list (bk * string)) (a1 a2 : list term) : bool :=
    match a1, a2 with
    | [], [] => true
    | x :: a1, y :: a2 =>
        (match x, y with
         | tRel n, tRel m =>
             match nth_error ctx n, nth_error ctx m with
             | Some (BMem, _), _ => Nat.eqb n m
             | _, Some (BMem, _) => Nat.eqb n m
             | _, _ => pure_int 60 ctx x && pure_int 60 ctx y
             end
         | _, _ => pure_int 60 ctx x && pure_int 60 ctx y
         end) && same_shape ctx a1 a2
    | _, _ => false
    end.

  Definition R := (list string * list nat)%type.
  (* the memories handed on after an `if`: those of either arm.  A SET: joined without repeating an element.  (Joined by
     appending, as first written, the list grew by about three times at every `if` on a path -- each arm starts from
     the list before it -- and nine `if`s after a dozen writes took the checker minutes, found 2026-10-15 by hw/.) *)
  Definition union_nat (a b : list nat) : list nat :=
    fold_left (fun acc l => if existsb (Nat.eqb l) acc then acc else l :: acc) a b.
  Definition seqR (r : R) (f : list nat -> R) : R := let '(e, d) := r in let '(e', d') := f d in (e ++ e', d').

  Fixpoint walk (fuel : nat) (ctx : list (bk * string)) (tail : bool) (dead : list nat) (t : term) : R :=
    match fuel with
    | O => (["the program is too large for this checker"], dead)
    | S fuel =>
      let use_mem (n : nat) (dead : list nat) : R :=       (* a memory handed on: it must still be alive *)
        if isdead dead (lvl ctx n)
        then (["the memory `" ^ vname ctx n ^ "` is used after it was handed on"], dead)
        else ([], lvl ctx n :: dead) in
      let read_mem (n : nat) (dead : list nat) : R :=      (* a memory read: alive, and it stays alive *)
        if isdead dead (lvl ctx n)
        then (["the memory `" ^ vname ctx n ^ "` is read after it was handed on"], dead)
        else ([], dead) in
      (* the arguments of a call, left to right; a memory given as it stands is handed on when the call happens *)
      let args_of (is_rd : bool) (args : list term) (dead : list nat) : R :=
        let '(e, d, pend) :=
          fold_left (fun (acc : list string * list nat * list nat) (a : term) =>
            let '(e, d, pend) := acc in
            match a with
            | tRel n =>
                match nth_error ctx n with
                | Some (BMem, _) =>
                    if is_rd then let '(e1, d1) := read_mem n d in (e ++ e1, d1, pend)
                    else if isdead d (lvl ctx n) || isdead pend (lvl ctx n)
                         then (e ++ ["the memory `" ^ vname ctx n ^ "` is used after it was handed on"], d, pend)
                         else (e, d, lvl ctx n :: pend)
                | Some (BSelf, _) => (e ++ ["the function is passed along as a value"], d, pend)
                | _ => (e, d, pend)
                end
            | _ => let '(e1, d1) := walk fuel ctx false d a in (e ++ e1, d1, pend)
            end) args ([], dead, []) in
        (e, pend ++ d) in
      match t with
      | tRel n =>
          match nth_error ctx n with
          | Some (BMem, _) => use_mem n dead
          | Some (BSelf, _) => (["the function is used as a value"], dead)
          | _ => ([], dead)
          end
      | tCast t _ _ => walk fuel ctx tail dead t
      | tLetIn _ def _ (tRel 0) => walk fuel ctx tail dead def
      | tLetIn na def ty body =>
          (* what is named inside `def` (a memory named inside an arm of an `if`) is gone when `def` ends: its place
             in the context is taken by the name bound here, which starts alive *)
          let '(e1, d1) := walk fuel ctx false dead def in
          let d1 := filter (fun l => Nat.ltb l #|ctx|) d1 in
          let '(e2, d2) := walk fuel ((if is_mem_ty ty then BMem else BOther, bname na) :: ctx) tail d1 body in
          (e1 ++ e2, filter (fun l => Nat.ltb l #|ctx|) d2)
      | tLambda na _ body =>
          let '(e, d) := walk fuel ((BOther, bname na) :: ctx) false dead body in
          ((if hot then ["a function is made inside the loop (fun " ^ bname na ^ " => ..)"] else []) ++ e, d)
      | tFix _ _ => ((if hot then ["a recursive function is defined inside this one"] else []), dead)
      | tApp f args =>
          match f with
          | tRel n =>
              match nth_error ctx n with
              | Some (BSelf, _) =>
                  let '(e, d) := args_of self_rd args dead in
                  ((if tail || tree then [] else ["the call to itself is not the last step"]) ++ e, d)
              | _ => let '(e, d) := args_of false args dead in
                     ((if hot then ["a function received as a value is called (`" ^ vname ctx n ^ "`)"] else []) ++ e, d)
              end
          | tConst kn _ =>
              let ok := is_prim kn || String.eqb (mp_head (fst kn)) "KQRun" || String.eqb (mp_head (fst kn)) "KQBound" || is_boolfn kn || is_intfn kn || user kn || is_decl Σ kn in
              let '(e, d) := args_of (is_kq kn "kq_rd" || is_kq kn "rd" || is_kq kn "rd32" || is_kq kn "rd_u" || is_kq kn "rd32_u"
                                      || is_kq kn "kq_sum" || memk kn readers) args dead in
              ((if hot && negb ok then ["calls `" ^ string_of_kername kn ^ "`, which is not a machine operation"] else []) ++ e, d)
          | tConstruct ind i _ =>
              let '(cn, ar) := ctor_info Σ ind i in
              let '(e, d) := args_of false args dead in
              ((if hot && negb (Nat.eqb ar 0) && negb (String.eqb cn "S")      (* S n is n + 1 on a machine number *)
                then ["builds a value (`" ^ cn ^ "`)"] else []) ++ e, d)
          | _ =>
              let '(e0, d0) := walk fuel ctx false dead f in
              let '(e, d) := args_of false args d0 in
              ((if hot then ["something other than a named function is called"] else []) ++ e0 ++ e, d)
          end
      | tConst kn _ =>
          let ok := is_prim kn || is_boolfn kn || is_intfn kn || user kn || String.eqb (mp_head (fst kn)) "KQRun" || is_decl Σ kn in
          ((if hot && negb ok then ["uses `" ^ string_of_kername kn ^ "`, which is not a machine operation"] else []), dead)
      | tCase ci _ discr brs =>
          let nm := ind_name (ci_ind ci) in
          let e0 := if hot && negb (String.eqb nm "bool" || String.eqb nm "nat")
                    then ["takes apart a `" ^ nm ^ "`: not a machine value"] else [] in
          let e4 := if tail && String.eqb nm "bool" then
                      match map (fun b : branch term => strip (bbody b)) brs with
                      | [tApp (tRel n1) a1; tApp (tRel n2) a2] =>
                          match nth_error ctx n1 with
                          | Some (BSelf, _) =>
                              if Nat.eqb n1 n2 && same_shape ctx a1 a2
                              then ["~both arms of an `if` go round the loop and differ only in numbers: put the `if` inside ONE call, "
                                    ^ "`loop f (if c then a else b) ..` (rule 4; the build merges this simple case by itself)"]
                              else []
                          | _ => []
                          end
                      | _ => []
                      end else [] in
          let '(e1, d1) := walk fuel ctx false dead discr in
          let rs := map (fun b : branch term =>
                           walk fuel (map (fun na => (BOther, bname na)) (bcontext b) ++ ctx) tail
                                (* the branch's variables come first: positions counted from the outside are unchanged *)
                                d1 (bbody b)) brs in
          (e0 ++ e4 ++ e1 ++ concat (map fst rs),
           fold_left (fun acc r => union_nat (filter (fun l => Nat.ltb l #|ctx|) (snd r)) acc) rs d1)
      | tProj _ t => let '(e, d) := walk fuel ctx false dead t in
                     ((if hot then ["reads a field of a record: not a machine value"] else []) ++ e, d)
      | _ => ([], dead)
      end
    end.

End Walk.

(* a definition: its parameters, then (for a recursive one) the function itself and its own parameters *)
Fixpoint params (ctx : list (bk * string)) (t : term) : list (bk * string) * term :=
  match t with
  | tLambda na ty body => params ((if is_mem_ty ty then BMem else BOther, bname na) :: ctx) body
  | _ => (ctx, t)
  end.

(* what the walk says of one definition, and whether it is a tree (calls itself twice or more on some path) *)
Definition check_body (Σ : global_env) (mp : modpath) (hot : bool) (readers : list kername) (self_rd : bool)
           (body : term) : list string * bool :=
  let '(ctx, t) := params [] body in
  match t with
  | tFix mfix _ =>
      let ctx' := rev (map (fun d => (BSelf, bname (dname d))) mfix) ++ ctx in
      let rs := map (fun d => let '(c, b) := params ctx' (dbody d) in
                              let tree := Nat.leb 2 (ncalls 4000 c b) in
                              (fst (walk Σ mp hot readers self_rd tree 4000 c true [] b), tree)) mfix in
      (concat (map fst rs), existsb snd rs)
  | _ => (fst (walk Σ mp hot readers false false 4000 ctx false [] t), false)
  end.

(* which constants of the file a term mentions *)
Fixpoint refs (fuel : nat) (mp : modpath) (t : term) : list kername :=
  match fuel with
  | O => []
  | S fuel =>
    match t with
    | tConst kn _ => if eq_mp (fst kn) mp then [kn] else []
    | tApp f args => refs fuel mp f ++ concat (map (refs fuel mp) args)
    | tLambda _ ty b => refs fuel mp b
    | tLetIn _ d _ b => refs fuel mp d ++ refs fuel mp b
    | tCase _ _ d brs => refs fuel mp d ++ concat (map (fun b : branch term => refs fuel mp (bbody b)) brs)
    | tFix mfix _ => concat (map (fun d => refs fuel mp (dbody d)) mfix)
    | tCast t _ _ => refs fuel mp t
    | tProj _ t => refs fuel mp t
    | _ => []
    end
  end.

Fixpoint has_fix (t : term) : bool :=
  match t with tLambda _ _ b => has_fix b | tFix _ _ => true | _ => false end.

(* does this text itself write a memory (`upd`)? *)
Fixpoint writes (decls : list kername) (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => true
  | S fuel =>
    match t with
    | tConst kn _ => is_kq kn "upd" || is_kq kn "upd32" || is_kq kn "upd_u" || is_kq kn "upd32_u" || is_kq kn "kq_in" || is_kq kn "kq_out"
                     || memk kn decls      (* a routine declared without a body whose result is not a plain number *)
    | tApp f args => writes decls fuel f || existsb (writes decls fuel) args
    | tLambda _ _ b => writes decls fuel b
    | tLetIn _ d _ b => writes decls fuel d || writes decls fuel b
    | tCase _ _ d brs => writes decls fuel d || existsb (fun b : branch term => writes decls fuel (bbody b)) brs
    | tFix mfix _ => existsb (fun d => writes decls fuel (dbody d)) mfix
    | tCast t _ _ => writes decls fuel t
    | tProj _ t => writes decls fuel t
    | _ => false
    end
  end.
(* is the result of a function of this type a plain number (an int, a boolean, a nat)?  Only such a function can be a
   reader: a result of any other type (a memory, a pair with a memory in it) could BE the memory it was given *)
Fixpoint plain_result (fuel : nat) (ty : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
    match ty with
    | tProd _ _ b => plain_result fuel b
    | tCast t _ _ => plain_result fuel t
    | tConst kn _ => is_prim kn && String.eqb (snd kn) "int"
    | tInd ind _ => String.eqb (ind_name ind) "bool" || String.eqb (ind_name ind) "nat"
    | _ => false
    end
  end.

(* ---- for the advice of rule 1: the FIXED cells (block and cell number both written in the program) that a piece of
   text reads and writes -- its own, and those of the non-recursive definitions it calls *)
Definition fixed_int (defs : list (kername * term)) (t : term) : option PrimInt63.int :=
  match strip t with
  | tInt i => Some i
  | tConst kn _ => match find (fun d : kername * term => Kername.eqb (fst d) kn) defs with
                   | Some (_, b) => match strip b with tInt i => Some i | _ => None end
                   | None => None
                   end
  | _ => None
  end.
Definition cell := (PrimInt63.int * PrimInt63.int)%type.
Definition cell_eq (a b : cell) : bool := PrimInt63.eqb (fst a) (fst b) && PrimInt63.eqb (snd a) (snd b).
Fixpoint cells (fuel : nat) (mp : modpath) (defs : list (kername * term)) (t : term) : list (bool * cell) :=
  match fuel with
  | O => []
  | S fuel =>
    match t with
    | tApp (tConst kn _) args =>
        let sub := flat_map (cells fuel mp defs) args in
        let at_ (w : bool) := match args with
                              | h :: i :: _ => match fixed_int defs h, fixed_int defs i with
                                               | Some a, Some b => [(w, (a, b))]
                                               | _, _ => []
                                               end
                              | _ => []
                              end in
        if is_kq kn "rd" then at_ false ++ sub
        else if is_kq kn "upd" then at_ true ++ sub
        else if eq_mp (fst kn) mp
             then match find (fun d : kername * term => Kername.eqb (fst d) kn) defs with
                  | Some (_, b) => if has_fix b then sub else cells fuel mp defs b ++ sub
                  | None => sub
                  end
             else sub
    | tApp f args => cells fuel mp defs f ++ flat_map (cells fuel mp defs) args
    | tLambda _ _ b => cells fuel mp defs b
    | tLetIn _ d _ b => cells fuel mp defs d ++ cells fuel mp defs b
    | tCase _ _ d brs => cells fuel mp defs d ++ flat_map (fun b : branch term => cells fuel mp defs (bbody b)) brs
    | tFix mfix _ => flat_map (fun d => cells fuel mp defs (dbody d)) mfix
    | tCast t _ _ => cells fuel mp defs t
    | _ => []
    end
  end.
Definition state_cells (mp : modpath) (defs : list (kername * term)) (body : term) : list cell :=
  let cs := cells 4000 mp defs body in
  let rd_ := map snd (filter (fun c : bool * cell => negb (fst c)) cs) in
  let wr := map snd (filter (fun c : bool * cell => fst c) cs) in
  fold_left (fun acc c => if existsb (cell_eq c) acc then acc else if existsb (cell_eq c) wr then c :: acc else acc) rd_ [].

Definition uniq (l : list string) : list string :=
  rev (fold_left (fun acc x => if existsb (String.eqb x) acc then acc else x :: acc) l []).

Definition report (Σ : global_env) (root : kername) : list string :=
  let mp := fst root in
  let cdecls := flat_map (fun d : kername * global_decl =>
                match snd d with
                | ConstantDecl cb => if eq_mp (fst (fst d)) mp
                                     then match cst_body cb with Some b => [(fst d, b, cst_type cb)] | None => [] end else []
                | _ => []
                end) (declarations Σ) in
  let defs := map (fun x : kername * term * term => (fst (fst x), snd (fst x))) cdecls in
  (* the writers: what writes a memory itself, or calls something of the file that does *)
  let wstep (w : list kername) : list kername :=
    fold_left (fun acc d => if memk (fst d) acc then acc
                            else if existsb (fun k => memk k acc) (refs 4000 mp (snd d)) then fst d :: acc else acc) defs w in
  (* a routine declared WITHOUT a body -- anywhere: the memory's, the machine's, a library's, a program's own -- whose
     result is not a plain number takes the memory and gives one back: it writes *)
  let axms := flat_map (fun d : kername * global_decl =>
                match snd d with
                | ConstantDecl cb => match cst_body cb with
                                     | None => if plain_result 64 (cst_type cb) then [] else [fst d]
                                     | Some _ => []
                                     end
                | _ => []
                end) (declarations Σ) in
  let writers := fold_left (fun w _ => wstep w) defs (axms ++ map fst (filter (fun d => writes axms 4000 (snd d)) defs)) in
  let readers := map (fun x : kername * term * term => fst (fst x))
                     (filter (fun x : kername * term * term => negb (memk (fst (fst x)) writers) && plain_result 64 (snd x)) cdecls) in
  let step (hot : list kername) : list kername :=
    fold_left (fun acc d => if memk (fst d) acc
                            then fold_left (fun a k => if memk k a then a else k :: a) (refs 4000 mp (snd d)) acc
                            else acc) defs hot in
  let hot0 := map fst (filter (fun d => has_fix (snd d)) defs) in
  let hot := fold_left (fun h _ => step h) defs hot0 in
  let is_note (m : string) : bool := String.prefix "~" m in
  let per := map (fun d =>
                 let '(ms0, tree) := check_body Σ mp (memk (fst d) hot) readers (memk (fst d) readers) (snd d) in
                 let ms := uniq ms0 in
                 (* rule 1, for a real loop only (a function whose calls to itself are all its last step): tree
                    recursion that leaves its results in cells is the recommended way, not a fault *)
                 let loop := has_fix (snd d) && negb tree
                             && negb (existsb (String.eqb "the call to itself is not the last step") ms) in
                 let r1 := if loop then map (fun c : cell =>
                               "~cell " ^ string_of_prim_int (snd c) ^ " of block " ^ string_of_prim_int (fst c)
                               ^ " is read AND written by this loop: it is loop state kept in memory -- carry it as a parameter and "
                               ^ "write it once, when the loop ends (rule 1)") (rev (state_cells mp defs (snd d))) else [] in
                 (snd (fst d), ms ++ r1)) (rev defs) in
  let errs := flat_map (fun x : string * list string =>
                 map (fun e => "  in `" ^ fst x ^ "`: " ^ e) (filter (fun m => negb (is_note m)) (snd x))) per in
  let notes := flat_map (fun x : string * list string =>
                 map (fun e => "  in `" ^ fst x ^ "`: " ^ String.substring 1 (String.length e - 1) e) (filter is_note (snd x))) per in
  let advice := match notes with [] => [] | _ => ("KQ-SHAPE ADVICE (" ^ string_of_nat #|notes| ^ "), for speed only:") :: notes end in
  (match errs with
   | [] => ["KQ-SHAPE OK: " ^ string_of_nat #|hot| ^ " function(s) on the hot path, "
            ^ string_of_nat (#|defs| - #|hot|) ^ " outside it -- "
            ^ String.concat ", " (map (fun k => snd k) (rev hot))]
   | _ => ("KQ-SHAPE REFUSE (" ^ string_of_nat #|errs| ^ "):") :: errs
   end) ++ advice.

Definition kq_shape {A} (a : A) : TemplateMonad unit :=
  p <- tmQuoteRec a ;;
  match snd p with
  | tConst kn _ => r <- tmEval all (String.concat nl (report (fst p) kn)) ;; tmMsg r
  | _ => tmFail "kq_shape: give it the name of a definition"
  end.

(* THE GATE: as kq_shape, but a refusal is an error -- the file does not compile, and the compile command after it is
   never reached: no C is made of a program outside the fragment. *)
Definition kq_gate {A} (a : A) : TemplateMonad unit :=
  p <- tmQuoteRec a ;;
  match snd p with
  | tConst kn _ =>
      ok <- tmEval all (match report (fst p) kn with first :: _ => String.prefix "KQ-SHAPE OK" first | [] => false end) ;;
      r <- tmEval all (String.concat nl (report (fst p) kn)) ;;
      if ok : bool then tmMsg r else tmFail r
  | _ => tmFail "kq_gate: give it the name of a definition"
  end.
