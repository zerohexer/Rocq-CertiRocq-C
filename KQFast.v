(* KQFast.v -- THE TRANSLATOR: ONE STANDARD FORM FOR A PROGRAM, EQUAL TO THE PROGRAM BY COMPUTATION ALONE.

   `MetaRocq Run (kq_fast main).` reads `main` and every function of the same file it uses, and defines next to each
   function `f` a twin `f_kq`: the same function in ONE STANDARD FORM, whatever way `f` was written.  Then it states

       f_kq = f                     (one statement per function, proved by `eq_refl`)

   and Rocq's kernel checks each of them.  Every step the translator makes is a step of plain computation (a name
   unfolded, a `let` put in or taken out, a constant test decided), so "the two are equal" is something the kernel
   SEES by computing; there is no proof script that could go wrong, and nothing about the translator has to be
   believed: a mistake in it stops the build at that line.  The compiler is then given `main_kq`.

   (How the kernel is asked, so that it answers at once.  `f_kq` calls the twins `g_kq` of the functions `f` calls.
   Asked whether `f_kq` and `f` are the same as they stand, the kernel would have to open `g_kq` and `g` at every call
   and compare them again -- and a call with a written budget, `find 40 ..`, it would start to RUN.  So the twins in
   `f_kq` are first replaced by the functions they are equal to, one after the other, each by the equality already
   proved (`eq_ind_r`); what is left to compare then calls the SAME functions on both sides, and the kernel only has
   to look at the arguments.)

   THE STANDARD FORM of a function body:
     1  HELPERS ARE WRITTEN OUT.  A call of a non-recursive definition of the file is replaced by its body; a named
        constant (`Definition M := 1000000007`) by its value.
     2  EVERY STEP HAS A NAME (`let k3 := x + y in ..`), and the same step is named ONCE: the same arithmetic on the
        same numbers, or the same cell read twice from the same memory, is computed one time.
     3  THE ORDER IS FIXED BY A RULE, not by how the text was nested:
          - whatever touches the memory (a read, a write, a call given the memory) stays in the order it was written;
          - plain arithmetic is placed AS EARLY as the numbers it is made of exist -- what only counts (`i + 1`) at the
            start, what waits for a read right after the read -- but inside an arm of an `if` when only that arm needs
            it, and before the `if` when both arms do;
          - of several pieces that can be placed at the same point, the one that ends the longest chain goes first.
        (The rule was CHOSEN BY MEASUREMENT, results/order.txt: of the rules tried on the 28 programs of hand/ -- as
        late as possible, as written, as early as possible -- this one is the only one that makes the text's own order
        irrelevant AND is on average as fast as the programs as written (1.00, the worst 1.10).  "As late as possible"
        is 2% slower on average and 64% slower on one program: on that machine code the processor stops guessing a
        jump on the data that it guesses perfectly otherwise.  No rule is the fastest for every loop.)
     4  A CHOICE BETWEEN TWO NUMBERS is one of two things, and the text says which:
          - `kq_select c a b` (KQRun.v): both numbers are worked out, one is taken; on the machine a conditional
            move, NEVER a jump.  When c is a comparison the comparison goes inside it (`kq_sel_lts x y a b`): two
            machine instructions in all;
          - `if c then a else b`: a jump, as an `if` of C.
        Which is faster depends on the data and on nothing else: a test that goes either way wants the first (a wrong
        guess costs the machine about fifteen cycles), a test that is nearly always the same way wants the second.
        So it is MEASURED: built with `kq_fast_with PInstr`, every `if` between two plain numbers counts, on a run of
        the program, how often a machine would have guessed it wrong; built with `kq_fast_with (PUse [..])` the ones
        in the list are made `kq_select`.  (An `if` whose arms do different work -- a read in one only, a division,
        another loop -- is always a jump: the arm not taken is work not done.  The author can settle one by hand:
        `kq_select` is used as written, and `if kq_jump c ..` is never changed.)
     5  STEPS OF THE SECOND KIND: two rewrites are equal to the text CASE BY CASE, not by computation.
          - An `if` whose two arms do THE SAME STEPS ON NUMBERS THAT MAY DIFFER (`if c then f a s else f b s`,
            `if c then upd h i x s else upd h i y s`, the same reads, the same call at the end) becomes one sequence
            of steps, each number that differs chosen by the test without a jump: `f (kq_select c a b) s`.
          - A choice made without a jump on a COMBINATION of tests (`c1 && c2`, `c1 || c2`) becomes one choice per
            test, nested: `kq_select c1 (kq_select c2 a b) b` (no test is first worked out as a number).
        Both are made only where the measurement of 4 says the test is guessed wrong often.  A function with such a
        step gets two twins: `f_kq1`, the standard form without them (equal to `f` by computation, as above), and
        `f_kq`, with them.  "f_kq = f_kq1, argument by argument" is then PROVED, by induction on the function's
        budget, by one tactic that is the same for every program (`kq_fast_qed`, at the end of this file: a case
        split on every test until both sides are the same text) -- for that function and for every function that
        calls it; `main_kq = main` follows.  The kernel checks the whole proof, so again nothing about the
        translator is trusted.  (Should a program have such a step in a function the translator keeps as written,
        or in two functions that call each other, it gets none: the steps of the first kind only.)

     6  STEP 3, READS AND WRITES WITHOUT THE TEST -- a SETTING, and off unless it is asked for (`kq_bounds`, below):
        a loop that counts reads and writes with no test per cell, after one test at its start; proved by a copy of
        the loop that carries the proofs (the section STEP 3 below, KQBound.v).  Off (`KQTests`, the default), every
        read and write tests its cell, as the model defines `rd` and `upd`.

   What is NOT made equal: the order of a function's parameters, `a + b` against `b + a` (equal, but not by
   computation alone).  A function the translator cannot read (it builds a pair, it is one of two functions that
   call each other in a way not known here) is kept as written; only the names of the functions it calls are
   changed.

   Nothing is proved about the translator and nothing needs to be.  2026-10-14. *)
From MetaRocq.Utils Require Import utils bytestring Show.
From MetaRocq.Template Require Import All.
From Stdlib Require Import ZArith Uint63.
Require Import KQ.KQRun KQ.KQShape KQ.KQBound.
Import MonadNotation ListNotations.
Close Scope sint63_scope.          (* KQRun.v opens it for programs; here a written number is a nat *)
Open Scope bs.
Open Scope list_scope.

(* ------------------------------------------------------------------ the names this file must know *)
Definition kn_of (t : term) : kername := match t with tConst kn _ => kn | _ => (MPfile [], "") end.
Definition kn_select  : kername := kn_of <% kq_select %>.
Definition kn_sel_lts : kername := kn_of <% kq_sel_lts %>.
Definition kn_sel_les : kername := kn_of <% kq_sel_les %>.
Definition kn_sel_eq  : kername := kn_of <% kq_sel_eq %>.
Definition kn_sel_ltu : kername := kn_of <% kq_sel_ltu %>.
Definition kn_sel_leu : kername := kn_of <% kq_sel_leu %>.
Definition kn_selectn : kername := kn_of <% kq_selectn %>.
Definition kn_sel_ges : kername := kn_of <% kq_sel_ges %>.
Definition kn_sel_gts : kername := kn_of <% kq_sel_gts %>.
Definition kn_sel_ne  : kername := kn_of <% kq_sel_ne %>.
Definition kn_sel_geu : kername := kn_of <% kq_sel_geu %>.
Definition kn_sel_gtu : kername := kn_of <% kq_sel_gtu %>.
Definition kn_prof    : kername := kn_of <% kq_prof %>.
Definition t_int     : term := <% PrimInt63.int %>.
Definition t_bool    : term := <% bool %>.
Definition t_eq      : term := <% @eq %>.
Definition t_eq_refl : term := <% @eq_refl %>.
Definition t_eq_ind_r : term := <% @eq_ind_r %>.
Definition kq2_ind (P : Prop) : Prop := P.     (* a statement proved by induction on its first argument *)
Definition kq2_def (P : Prop) : Prop := P.     (* a statement about a function that does not call itself *)
Definition kq2_wrap (P : Prop) : Prop := P.    (* a statement about a loop's start test (step 3) *)
Definition t_kq2_wrap : term := <% kq2_wrap %>.
Definition t_kq2_ind : term := <% kq2_ind %>.
Definition t_kq2_def : term := <% kq2_def %>.
Definition t_and     : term := <% and %>.
Definition t_True    : term := <% True %>.
Definition t_Prop    : term := <% Prop %>.

(* how the choices between two numbers are settled *)
Inductive pmode :=
| PPlain                      (* every `if` stays an `if` *)
| PInstr                      (* every `if` between two plain numbers counts its wrong guesses (a build to measure with) *)
| PUse (sel : list PrimInt63.int).   (* the `if`s with these numbers become `kq_select` *)

(* ------------------------------------------------------------------ the program, between reading and writing *)
Inductive atom := AV (v : nat) | AT (t : term).                    (* a variable; a constant (a number, true, O) *)
Inductive head :=
| HC (kn : kername) (u : Instance.t)                               (* a named function or operation *)
| HK (ind : inductive) (i : nat) (u : Instance.t)                  (* a constructor (S) *)
| HF (k : nat).                                                     (* member k of the recursive function being read *)

(* a FLOATING step: plain arithmetic, given no memory and giving none back; it may be put anywhere its numbers exist *)
Record fdef := mkF { f_ty : term; f_h : head; f_args : list atom }.

(* what stays where it was written *)
Inductive item :=
| IBind (v : nat) (ty : term) (h : head) (args : list atom)
| IIf (v lo : nat) (ty : term) (ci : case_info) (p : predicate term) (c : atom) (t e : blk)
| INat (v lo : nat) (ty : term) (ci : case_info) (p : predicate term) (n : atom) (z : blk) (x : nat) (xna : aname) (s : blk)
with blk := Blk (items : list item) (res : tl)
with tl :=
| TA (a : atom)
| TCall (h : head) (args : list atom)
| TIf (lo : nat) (ci : case_info) (p : predicate term) (c : atom) (t e : blk)
| TNat (lo : nat) (ci : case_info) (p : predicate term) (n : atom) (z : blk) (x : nat) (xna : aname) (s : blk).
(* (`lo`: the number of the first variable made inside the `if`; what has a smaller number was written before it) *)

Inductive ent := EA (a : atom) | EF (k : nat).                      (* what a position of the text's context stands for *)
Inductive scv := SV (v : nat) | SF (k : nat).

Record st := mkSt {
  s_nx : nat;                                   (* the next variable *)
  s_fl : list (nat * fdef);                     (* the floating steps *)
  s_av : list (head * list atom * nat);         (* which variable already holds which floating step *)
  s_rd : list (head * list atom * nat);         (* which variable already holds which read (forgotten when an arm ends) *)
  s_vt : list (nat * (term * nat));             (* every variable: its type, and how long a chain it ends *)
  s_np : nat * list (nat * nat) }.              (* the next number for a test; the tests met: number, kind *)
(* the kinds of test: 0  between two plain numbers (may be made without a jump);
                      1  two arms that do the same steps on numbers that may differ (may be made one sequence of steps);
                      2  between different work (a jump);
                      100 + kind: made with a step of the second kind (nested choices; one sequence of steps) *)

Definition M (A : Type) : Type := st -> option (A * st).
Definition mret {A} (a : A) : M A := fun s => Some (a, s).
Definition mbind {A B} (m : M A) (f : A -> M B) : M B := fun s => match m s with Some (a, s') => f a s' | None => None end.
Definition mfail {A} : M A := fun _ => None.
Notation "x <-- m ;; k" := (mbind m (fun x => k)) (at level 61, m at next level, right associativity).
Notation "' pat <-- m ;; k" := (mbind m (fun x => match x with pat => k end))
  (at level 61, pat pattern, m at next level, right associativity).

(* a number written out as a budget (`S (S (.. O))`) is ONE constant, however long *)
Fixpoint is_lit (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel => match t with
              | tConstruct _ _ _ => true
              | tInt _ => true
              | tApp (tConstruct _ _ _) args => forallb (is_lit fuel) args
              | _ => false
              end
  end.
Fixpoint lit_size (fuel : nat) (t : term) : nat :=
  match fuel with
  | O => 0
  | S fuel => match t with tApp _ args => S (fold_left (fun a x => a + lit_size fuel x) args 0) | _ => 1 end
  end.
Definition catom_eqb (a b : term) : bool :=
  match a, b with
  | tApp (tConstruct i1 n1 _) _, tApp (tConstruct i2 n2 _) _ =>
      Kername.eqb (inductive_mind i1) (inductive_mind i2) && Nat.eqb n1 n2
      && String.eqb (ind_name i1) "nat" && Nat.eqb (lit_size 100000 a) (lit_size 100000 b)
  | tInt i, tInt j => PrimInt63.eqb i j
  | tConst k1 _, tConst k2 _ => Kername.eqb k1 k2
  | tConstruct i1 n1 _, tConstruct i2 n2 _ =>
      Kername.eqb (inductive_mind i1) (inductive_mind i2) && Nat.eqb (inductive_ind i1) (inductive_ind i2) && Nat.eqb n1 n2
  | _, _ => false
  end.
Definition atom_eqb (a b : atom) : bool :=
  match a, b with AV n, AV m => Nat.eqb n m | AT t, AT u => catom_eqb t u | _, _ => false end.
Fixpoint atoms_eqb (a b : list atom) : bool :=
  match a, b with [], [] => true | x :: a, y :: b => atom_eqb x y && atoms_eqb a b | _, _ => false end.
Definition head_eqb (a b : head) : bool :=
  match a, b with
  | HC k1 _, HC k2 _ => Kername.eqb k1 k2
  | HK i1 n1 _, HK i2 n2 _ =>
      Kername.eqb (inductive_mind i1) (inductive_mind i2) && Nat.eqb (inductive_ind i1) (inductive_ind i2) && Nat.eqb n1 n2
  | HF k1, HF k2 => Nat.eqb k1 k2
  | _, _ => false
  end.
Fixpoint assoc {A} (v : nat) (l : list (nat * A)) : option A :=
  match l with [] => None | (k, a) :: l => if Nat.eqb k v then Some a else assoc v l end.
Definition mem_nat (v : nat) (l : list nat) : bool := existsb (Nat.eqb v) l.

Definition ty_simple (t : term) : bool := match t with tConst _ _ | tInd _ _ => true | _ => false end.
Definition is_int_ty (t : term) : bool := match t with tConst kn _ => is_prim kn && String.eqb (snd kn) "int" | _ => false end.
Fixpoint strip_prods (n : nat) (t : term) : option term :=
  match n with O => Some t | S n => match t with tProd _ _ b => strip_prods n b | _ => None end end.
Fixpoint lam_count (t : term) : nat := match t with tLambda _ _ b => S (lam_count b) | _ => 0 end.
Fixpoint lam_body (t : term) : term := match t with tLambda _ _ b => lam_body b | _ => t end.
Fixpoint lam_params (t : term) : list (aname * term) := match t with tLambda na ty b => (na, ty) :: lam_params b | _ => [] end.

Definition twin (kn : kername) : kername := (fst kn, snd kn ^ "_kq").

(* arithmetic that costs a cycle or two: what may be worked out without being needed *)
Definition cheap_kn (kn : kername) : bool :=
  (is_prim kn && negb (existsb (String.eqb (snd kn)) ["div"; "mod"; "divs"; "mods"; "diveucl"; "diveucl_21"; "addmuldiv"]))
  || is_boolfn kn || is_intfn kn
  || (String.eqb (mp_head (fst kn)) "KQRun"
      && existsb (String.eqb (snd kn)) ["zmin"; "zmax"; "zabs"; "zopp"; "zeven"; "kq_select"; "kq_sel_lts"; "kq_sel_les";
                                        "kq_sel_eq"; "kq_sel_ltu"; "kq_sel_leu"; "kq_selectn"; "kq_sel_ges"; "kq_sel_gts";
                                        "kq_sel_ne"; "kq_sel_geu"; "kq_sel_gtu"]).

Definition cheap_head (h : head) : bool :=
  match h with HC kn _ => cheap_kn kn | HK _ _ _ => true | HF _ => false end.

(* a read of the memory: the same read of the same memory is made once *)
Definition is_read_head (h : head) : bool := match h with HC kn _ => is_kq kn "rd" || is_kq kn "rd32" | _ => false end.

Section Read.
  Context (Σ : global_env) (mp : modpath) (root : kername) (mode : pmode) (ord : nat) (mrg : bool) (ftys : list term).
  (* `mrg`: steps of the second kind are made (the twin `f_kq`) or not (the twin `f_kq1`) *)

  (* the body of a definition of the file *)
  Definition ubody (kn : kername) : option term :=
    if eq_mp (fst kn) mp then match lookup_env Σ kn with Some (ConstantDecl cb) => cst_body cb | _ => None end else None.
  (* the definitions that get a twin: the functions of the file, and the program itself *)
  Definition has_fix_kn (kn : kername) : bool := match ubody kn with Some b => has_fix b | None => false end.
  Definition has_twin (kn : kername) : bool :=
    match ubody kn with Some b => has_fix b || Nat.ltb 0 (lam_count b) || Kername.eqb kn root | None => false end.

  (* ---- the type of what a call gives back *)
  Definition res_ty (h : head) (n : nat) : option term :=
    match h with
    | HC kn _ =>
        (* the choices and the counter of KQRun.v: a program that does not name them does not bring their types *)
        if Kername.eqb kn kn_prof then Some t_bool
        else if String.eqb (mp_head (fst kn)) "KQRun" && (String.prefix "kq_sel_" (snd kn) || String.prefix "kq_select" (snd kn))
             then Some t_int
        else
                 match lookup_env Σ kn with
                 | Some (ConstantDecl cb) => match strip_prods n (cst_type cb) with Some t => if ty_simple t then Some t else None | None => None end
                 | _ => None
                 end
    | HK ind _ u => let nm := ind_name ind in if String.eqb nm "nat" || String.eqb nm "bool" then Some (tInd ind u) else None
    | HF k => match nth_error ftys k with
              | Some t => match strip_prods n t with Some t => if ty_simple t then Some t else None | None => None end
              | None => None
              end
    end.
  Definition var_info (s : st) (v : nat) : term * nat := match assoc v (s_vt s) with Some x => x | None => (tRel 0, 0) end.
  Definition atom_mem (s : st) (a : atom) : bool := match a with AV v => is_mem_ty (fst (var_info s v)) | AT _ => false end.
  Definition atom_depth (s : st) (a : atom) : nat := match a with AV v => snd (var_info s v) | AT _ => 0 end.
  Definition args_depth (s : st) (args : list atom) : nat := fold_left (fun m a => Nat.max m (atom_depth s a)) args 0.

  Definition fresh (ty : term) (depth : nat) : M nat :=
    fun s => Some (s_nx s, mkSt (S (s_nx s)) (s_fl s) (s_av s) (s_rd s) ((s_nx s, (ty, depth)) :: s_vt s) (s_np s)).
  Definition next_test : M nat :=
    fun s => Some (fst (s_np s), mkSt (s_nx s) (s_fl s) (s_av s) (s_rd s) (s_vt s) (S (fst (s_np s)), snd (s_np s))).
  Definition note_test (k kind : nat) : M unit :=
    fun s => Some (tt, mkSt (s_nx s) (s_fl s) (s_av s) (s_rd s) (s_vt s) (fst (s_np s), (k, kind) :: snd (s_np s))).

  (* a comparison inside a choice: `kq_select (x <? y) a b` is `kq_sel_lts x y a b`; and with the test turned round,
     `kq_select (negb (x <? y)) a b` is `kq_sel_ges x y a b` *)
  Definition cmp_of (s : st) (c : nat) : option (string * atom * atom) :=
    match assoc c (s_fl s) with
    | Some (mkF _ (HC ck _) [x; y]) => if is_prim ck then Some (snd ck, x, y) else None
    | _ => None
    end.
  Definition fuse (s : st) (h : head) (args : list atom) : head * list atom :=
    match h, args with
    | HC kn u, [AV c; a; b] =>
        if Kername.eqb kn kn_select then
          let pick (k : kername) (x y : atom) := (HC k u, [x; y; a; b]) in
          match cmp_of s c with
          | Some (nm, x, y) =>
              if String.eqb nm "ltsb" then pick kn_sel_lts x y
              else if String.eqb nm "lesb" then pick kn_sel_les x y
              else if String.eqb nm "eqb" then pick kn_sel_eq x y
              else if String.eqb nm "ltb" then pick kn_sel_ltu x y
              else if String.eqb nm "leb" then pick kn_sel_leu x y
              else (h, args)
          | None =>
              match assoc c (s_fl s) with
              | Some (mkF _ (HC nk _) [AV c']) =>
                  if is_boolfn nk && String.eqb (snd nk) "negb" then
                    match cmp_of s c' with
                    | Some (nm, x, y) =>
                        if String.eqb nm "ltsb" then pick kn_sel_ges x y
                        else if String.eqb nm "lesb" then pick kn_sel_gts x y
                        else if String.eqb nm "eqb" then pick kn_sel_ne x y
                        else if String.eqb nm "ltb" then pick kn_sel_geu x y
                        else if String.eqb nm "leb" then pick kn_sel_gtu x y
                        else (HC kn_selectn u, [AV c'; a; b])
                    | None => (HC kn_selectn u, [AV c'; a; b])
                    end
                  else (h, args)
              | _ => (h, args)
              end
          end
        else (h, args)
    | _, _ => (h, args)
    end.

  (* a call whose result is needed as a variable: a floating step (found again if it was made before), or a step that
     stays in its place *)
  Definition mk_node (h0 : head) (args0 : list atom) (acc : list item) : M (atom * list item) :=
    fun s =>
      let '(h, args) := fuse s h0 args0 in
      match res_ty h #|args| with
      | None => None
      | Some ty =>
          let depth := S (args_depth s args) in
          if negb (existsb (atom_mem s) args) && negb (is_mem_ty ty) then
            match find (fun e : head * list atom * nat => head_eqb (fst (fst e)) h && atoms_eqb (snd (fst e)) args) (s_av s) with
            | Some (_, v) => Some ((AV v, acc), s)
            | None =>
                let v := s_nx s in
                Some ((AV v, acc), mkSt (S v) ((v, mkF ty h args) :: s_fl s) ((h, args, v) :: s_av s) (s_rd s)
                                        ((v, (ty, depth)) :: s_vt s) (s_np s))
            end
          else
            let is_read := is_read_head h in
            match (if is_read then find (fun e : head * list atom * nat => head_eqb (fst (fst e)) h && atoms_eqb (snd (fst e)) args) (s_rd s)
                   else None) with
            | Some (_, v) => Some ((AV v, acc), s)
            | None =>
                let v := s_nx s in
                Some ((AV v, IBind v ty h args :: acc),
                      mkSt (S v) (s_fl s) (s_av s) (if is_read then (h, args, v) :: s_rd s else s_rd s)
                           ((v, (ty, depth)) :: s_vt s) (s_np s))
            end
      end.

  (* a call that was made before (the same arithmetic, the same read of the same memory): the variable that holds it *)
  Definition known (s : st) (t : tl) : tl :=
    match t with
    | TCall h0 args0 =>
        let '(h, args) := fuse s h0 args0 in
        match res_ty h #|args| with
        | Some ty =>
            if negb (existsb (atom_mem s) args) && negb (is_mem_ty ty) then
              match find (fun e : head * list atom * nat => head_eqb (fst (fst e)) h && atoms_eqb (snd (fst e)) args) (s_av s) with
              | Some (_, v) => TA (AV v)
              | None => TCall h args
              end
            else if is_read_head h then
              match find (fun e : head * list atom * nat => head_eqb (fst (fst e)) h && atoms_eqb (snd (fst e)) args) (s_rd s) with
              | Some (_, v) => TA (AV v)
              | None => TCall h args
              end
            else TCall h args
        | None => t
        end
    | _ => t
    end.

  Definition bind_tl (t : tl) (acc : list item) : M (atom * list item) :=
    match t with
    | TA a => mret (a, acc)
    | TCall h args => mk_node h args acc
    | TIf lo ci p c t e =>
        fun s => (v <-- fresh (preturn p) (S (atom_depth s c)) ;; mret (AV v, IIf v lo (preturn p) ci p c t e :: acc)) s
    | TNat lo ci p n z x xna sb =>
        fun s => (v <-- fresh (preturn p) (S (atom_depth s n)) ;; mret (AV v, INat v lo (preturn p) ci p n z x xna sb :: acc)) s
    end.

  (* ---- STEPS OF THE SECOND KIND *)
  Definition with_rd (r : list (head * list atom * nat)) (s : st) : st := mkSt (s_nx s) (s_fl s) (s_av s) r (s_vt s) (s_np s).
  Definition is_int_atom (s : st) (a : atom) : bool :=
    match a with AV v => is_int_ty (fst (var_info s v)) | AT (tInt _) => true | AT _ => false end.
  (* the test is a combination of tests (`c1 && c2`, `c1 || c2`) *)
  Definition is_comb (s : st) (c : atom) : bool :=
    match c with
    | AV v => match assoc v (s_fl s) with
              | Some (mkF _ (HC kn _) [_; _]) => is_boolfn kn && (String.eqb (snd kn) "andb" || String.eqb (snd kn) "orb")
              | _ => false
              end
    | AT _ => false
    end.
  (* a choice without a jump between `a` and `b` by the test `c`; with `mrg`, one choice per test of a combination *)
  Fixpoint mk_sel (fuel : nat) (c a b : atom) {struct fuel} : M atom :=
    match fuel with
    | O => mfail
    | S fuel =>
        fun s =>
          let plain := match mk_node (HC kn_select []) [c; a; b] [] s with Some ((r, _), s') => Some (r, s') | None => None end in
          match (if mrg then match c with AV v => assoc v (s_fl s) | AT _ => None end else None) with
          | Some (mkF _ (HC kn _) [c1; c2]) =>
              if is_boolfn kn && String.eqb (snd kn) "andb" then (x <-- mk_sel fuel c2 a b ;; mk_sel fuel c1 x b) s
              else if is_boolfn kn && String.eqb (snd kn) "orb" then (x <-- mk_sel fuel c2 a b ;; mk_sel fuel c1 a x) s
              else plain
          | _ => plain
          end
    end.
  (* one number in place of two: the same, or chosen by the test *)
  Definition pick (c x y : atom) : M atom :=
    fun s => if atom_eqb x y then Some (x, s)
             else if is_int_atom s x && is_int_atom s y then mk_sel 100 c x y s else None.
  Fixpoint picks (c : atom) (xs ys : list atom) : M (list atom) :=
    match xs, ys with
    | [], [] => mret []
    | x :: xs, y :: ys => a <-- pick c x y ;; l <-- picks c xs ys ;; mret (a :: l)
    | _, _ => mfail
    end.
  (* a number of the second arm in terms of what the first arm made: a step of the second arm that answers a step of
     the first is that step; a piece of arithmetic made of such steps is made again of the answers *)
  Fixpoint resub (fuel : nat) (sg : list (nat * nat)) (a : atom) {struct fuel} : M atom :=
    match fuel with
    | O => mfail
    | S fuel =>
        match a with
        | AT _ => mret a
        | AV v =>
            match assoc v sg with
            | Some w => mret (AV w)
            | None =>
                fun s => match assoc v (s_fl s) with
                         | Some d =>
                             (args <-- (fix go (l : list atom) : M (list atom) :=
                                          match l with
                                          | [] => mret []
                                          | x :: l => y <-- resub fuel sg x ;; r <-- go l ;; mret (y :: r)
                                          end) (f_args d) ;;
                              if atoms_eqb args (f_args d) then mret a
                              else r <-- mk_node (f_h d) args [] ;; mret (fst r)) s
                         | None => Some (a, s)
                         end
            end
        end
    end.
  Definition resubs (fuel : nat) (sg : list (nat * nat)) (l : list atom) : M (list atom) :=
    (fix go (l : list atom) : M (list atom) :=
       match l with [] => mret [] | x :: l => y <-- resub fuel sg x ;; r <-- go l ;; mret (y :: r) end) l.
  (* the steps of the two arms, side by side: the same step (the same function, the same memory), its numbers picked *)
  Fixpoint mrg_items (fuel : nat) (c : atom) (sg : list (nat * nat)) (x y acc : list item) {struct x}
    : M (list (nat * nat) * list item) :=
    match x, y with
    | [], [] => mret (sg, acc)
    | IBind v1 ty g1 a1 :: x', IBind v2 _ g2 a2 :: y' =>
        if head_eqb g1 g2 then
          a2' <-- resubs fuel sg a2 ;;
          a <-- picks c a1 a2' ;;
          mrg_items fuel c ((v2, v1) :: sg) x' y' (IBind v1 ty g1 a :: acc)
        else mfail
    | _, _ => mfail
    end.
  Definition mrg_tl (fuel : nat) (c : atom) (sg : list (nat * nat)) (t1 t2 : tl) : M tl :=
    match t1, t2 with
    | TCall h1 a1, TCall h2 a2 =>
        if head_eqb h1 h2 then a2' <-- resubs fuel sg a2 ;; a <-- picks c a1 a2' ;; mret (TCall h1 a) else mfail
    | TA x, TA y => y' <-- resub fuel sg y ;; a <-- pick c x y' ;; mret (TA a)
    | _, _ => mfail
    end.

  (* is this text plain arithmetic on numbers that are there -- something that may be worked out and not used? *)
  Fixpoint cheap (fuel : nat) (env : list ent) (t : term) : bool :=
    match fuel with
    | O => false
    | S fuel =>
      let dummy := EA (AT (tRel 0)) in
      match t with
      | tRel n => match nth_error env n with Some (EA _) => true | _ => false end
      | tInt _ => true
      | tConstruct _ _ _ => true
      | tCast t _ _ => cheap fuel env t
      | tConst kn _ => match ubody kn with
                       | Some b => negb (has_fix b) && Nat.eqb (lam_count b) 0 && cheap fuel [] b
                       | None => true
                       end
      | tLetIn _ d _ b => cheap fuel env d && cheap fuel (dummy :: env) b
      | tApp (tConst kn _) args =>
          match ubody kn with
          | Some b => negb (has_fix b) && Nat.eqb (lam_count b) #|args| && forallb (cheap fuel env) args
                      && cheap fuel (repeat dummy #|args|) (lam_body b)
          | None => cheap_kn kn && forallb (cheap fuel env) args
          end
      | tApp (tConstruct _ _ _) args => is_lit 100000 t || forallb (cheap fuel env) args
      | tCase ci p c brs =>
          String.eqb (ind_name (ci_ind ci)) "bool" && is_int_ty (preturn p) && cheap fuel env c
          && forallb (fun b : branch term => cheap fuel env (bbody b)) brs
      | _ => false
      end
    end.

  (* THE READING: a piece of text, in a context, becomes steps (those that stay in place are added to acc, newest
     first) and what the piece is worth.  `force`: we are inside a choice that is being made without a jump, so every
     test met is made that way too. *)
  Fixpoint rexp (fuel : nat) (force : bool) (env : list ent) (t : term) (acc : list item) {struct fuel} : M (tl * list item) :=
    match fuel with
    | O => mfail
    | S fuel =>
      let ratoms :=
        fix go (ts : list term) (acc : list item) : M (list atom * list item) :=
          match ts with
          | [] => mret ([], acc)
          | t :: ts => '(tl, acc) <-- rexp fuel force env t acc ;;
                       '(a, acc) <-- bind_tl tl acc ;;
                       '(l, acc) <-- go ts acc ;;
                       mret (a :: l, acc)
          end in
      let rblk (frc : bool) (env : list ent) (t : term) : M blk :=
        fun s => match rexp fuel frc env t [] s with
                 | Some ((tl, acc), s') => Some (Blk (rev acc) (known s' tl), mkSt (s_nx s') (s_fl s') (s_av s') (s_rd s) (s_vt s') (s_np s'))
                 | None => None
                 end in
      match t with
      | tRel n => match nth_error env n with Some (EA a) => mret (TA a, acc) | _ => mfail end
      | tInt _ => mret (TA (AT t), acc)
      | tConstruct _ _ _ => mret (TA (AT t), acc)
      | tCast t _ _ => rexp fuel force env t acc
      | tLetIn _ d _ b => '(tl, acc) <-- rexp fuel force env d acc ;;
                          '(a, acc) <-- bind_tl tl acc ;;
                          rexp fuel force (EA a :: env) b acc
      | tConst kn u =>
          match ubody kn with
          | Some b => if has_fix b || Nat.ltb 0 (lam_count b) then mfail else rexp fuel force [] b acc
          | None => mret (TA (AT t), acc)
          end
      | tApp f args =>
          match f with
          | tConst kn u =>
              match ubody kn with
              | Some b =>
                  if has_fix b then '(ats, acc) <-- ratoms args acc ;; mret (TCall (HC kn u) ats, acc)
                  else if Nat.eqb (lam_count b) #|args|
                       then '(ats, acc) <-- ratoms args acc ;; rexp fuel force (rev (map EA ats)) (lam_body b) acc
                       else mfail
              | None => '(ats, acc) <-- ratoms args acc ;; mret (TCall (HC kn u) ats, acc)
              end
          | tRel n => match nth_error env n with
                      | Some (EF k) => '(ats, acc) <-- ratoms args acc ;; mret (TCall (HF k) ats, acc)
                      | _ => mfail
                      end
          | tConstruct ind i u =>
              if is_lit 100000 t then mret (TA (AT t), acc)
              else '(ats, acc) <-- ratoms args acc ;; mret (TCall (HK ind i u) ats, acc)
          | _ => mfail
          end
      | tCase ci p c brs =>
          let nm := ind_name (ci_ind ci) in
          if negb (ty_simple (preturn p)) then mfail
          else if String.eqb nm "bool" then
            match brs with
            | [bt; bf] =>
                let '(jump, c) := match c with
                                  | tApp (tConst kn _) [c'] => if is_kq kn "kq_jump" then (true, c') else (false, c)
                                  | _ => (false, c)
                                  end in
                '(tlc, acc) <-- rexp fuel force env c acc ;;
                '(ca, acc) <-- bind_tl tlc acc ;;
                match ca with
                | AT (tConstruct _ i _) => rexp fuel force env (bbody (if Nat.eqb i 0 then bt else bf)) acc
                | _ =>
                    k <-- next_test ;;
                    (* BOTH ARMS READ AS PLAIN ARITHMETIC, on trial: if each comes out as a number made of cheap steps
                       only -- nothing that stays in place (a read not made before, a write, a call given the memory),
                       no division, no loop -- this test is a CHOICE BETWEEN TWO PLAIN NUMBERS.  The trial is kept
                       when the choice is to be made without a jump, and undone otherwise. *)
                    trial <-- (fun s =>
                      if jump || negb (is_int_ty (preturn p)) then Some (None, s)
                      else match (('(t1, a1) <-- rexp fuel true env (bbody bt) [] ;;
                                   '(t2, a2) <-- rexp fuel true env (bbody bf) [] ;;
                                   mret (t1, a1, t2, a2)) s) with
                           | Some ((t1, a1, t2, a2), s') =>
                               let plain (t : tl) := match known s' t with
                                                     | TA _ => true
                                                     | TCall h args => cheap_head h && negb (existsb (atom_mem s') args)
                                                     | _ => false
                                                     end in
                               if match a1, a2 with [], [] => true | _, _ => false end && plain t1 && plain t2
                                  && forallb (fun e : nat * fdef => Nat.ltb (fst e) (s_nx s) || cheap_head (f_h (snd e))) (s_fl s')
                               then Some (Some (known s' t1, known s' t2, s'), s) else Some (None, s)
                           | None => Some (None, s)
                           end) ;;
                    let wanted := force || match mode with
                                           | PUse l => existsb (PrimInt63.eqb (Uint63.of_Z (Z.of_nat k))) l
                                           | _ => false
                                           end in
                    (* the test as a jump: an `if` of C *)
                    let as_jump (kind : nat) : M (tl * list item) :=
                      '(ca, acc) <-- (match mode with
                                      | PInstr => mk_node (HC kn_prof []) [AT (tInt (Uint63.of_Z (Z.of_nat k))); ca] acc
                                      | _ => mret (ca, acc)
                                      end) ;;
                      lo <-- (fun s => Some (s_nx s, s)) ;;
                      b1 <-- rblk false env (bbody bt) ;;
                      b2 <-- rblk false env (bbody bf) ;;
                      _ <-- note_test k kind ;;
                      mret (TIf lo ci p ca b1 b2, acc) in
                    match trial with
                    | Some (t1, t2, s') =>
                        if wanted then
                          _ <-- (fun _ => Some (tt, s')) ;;          (* the trial is kept *)
                          '(a, acc) <-- bind_tl t1 acc ;;
                          '(b, acc) <-- bind_tl t2 acc ;;
                          cmb <-- (fun s => Some (mrg && is_comb s ca, s)) ;;
                          if cmb then
                            (* a choice on a combination of tests: one choice per test, nested (second kind) *)
                            _ <-- note_test k 100 ;;
                            r <-- mk_sel 100 ca a b ;;
                            mret (TA r, acc)
                          else
                            _ <-- note_test k 0 ;;
                            mret (TCall (HC kn_select []) [ca; a; b], acc)
                        else as_jump 0
                    | None =>
                        (* BOTH ARMS DO THE SAME STEPS ON NUMBERS THAT MAY DIFFER (the same reads and writes, the same
                           call at the end), on trial: the second arm is read without what the first one read, and
                           the steps of the two are paired.  Kept -- one sequence of steps, each number that differs
                           chosen by the test without a jump -- when the measurement says so (second kind). *)
                        trial2 <-- (fun s =>
                          if jump then Some (None, s)
                          else match (('(t1, a1) <-- rexp fuel true env (bbody bt) [] ;;
                                       t1 <-- (fun s1 => Some (known s1 t1, s1)) ;;
                                       '(t2, a2) <-- (fun s1 => rexp fuel true env (bbody bf) [] (with_rd (s_rd s) s1)) ;;
                                       t2 <-- (fun s2 => Some (known s2 t2, s2)) ;;
                                       '(sg, acc') <-- mrg_items 4000 ca [] (rev a1) (rev a2) acc ;;
                                       t <-- mrg_tl 4000 ca sg t1 t2 ;;
                                       mret (t, acc')) s) with
                               | Some ((t, acc'), s') => Some (Some (t, acc', with_rd (s_rd s) s'), s)
                               | None => Some (None, s)
                               end) ;;
                        match trial2 with
                        | Some (t, acc', s') =>
                            if force || (wanted && mrg) then
                              _ <-- (fun _ => Some (tt, s')) ;;
                              _ <-- note_test k 101 ;;
                              mret (t, acc')
                            else as_jump 1
                        | None => if force then mfail else as_jump 2
                        end
                    end
                end
            | _ => mfail
            end
          else if String.eqb nm "nat" then
            match brs with
            | [bz; bs] =>
                match bcontext bz, bcontext bs with
                | [], [xna] =>
                    if force then mfail else
                    '(tln, acc) <-- rexp fuel force env c acc ;;
                    '(na, acc) <-- bind_tl tln acc ;;
                    lo <-- (fun s => Some (s_nx s, s)) ;;
                    x <-- fresh (tInd (ci_ind ci) []) 0 ;;
                    z <-- rblk false env (bbody bz) ;;
                    sb <-- rblk false (EA (AV x) :: env) (bbody bs) ;;
                    mret (TNat lo ci p na z x xna sb, acc)
                | _, _ => mfail
                end
            | _ => mfail
            end
          else mfail
      | _ => mfail
      end
    end.

  (* ------------------------------------------------------------------ THE WRITING *)
  Section Write.
    Context (s : st).
    Definition is_float (v : nat) : bool := match assoc v (s_fl s) with Some _ => true | None => false end.
    Definition floats_of (args : list atom) : list nat :=
      flat_map (fun a => match a with AV v => if is_float v then [v] else [] | AT _ => [] end) args.
    Definition add_new (l acc : list nat) : list nat := fold_left (fun acc v => if mem_nat v acc then acc else v :: acc) l acc.

    (* the floating steps a block names, in itself and in the blocks inside it *)
    Fixpoint need_blk (fuel : nat) (b : blk) : list nat :=
      match fuel with
      | O => []
      | S fuel =>
        let need_tl (t : tl) : list nat :=
          match t with
          | TA a => floats_of [a]
          | TCall _ args => floats_of args
          | TIf _ _ _ c t e => floats_of [c] ++ need_blk fuel t ++ need_blk fuel e
          | TNat _ _ _ n z _ _ sb => floats_of [n] ++ need_blk fuel z ++ need_blk fuel sb
          end in
        match b with
        | Blk items t =>
            flat_map (fun it => match it with
                                | IBind _ _ _ args => floats_of args
                                | IIf _ _ _ _ _ c t e => floats_of [c] ++ need_blk fuel t ++ need_blk fuel e
                                | INat _ _ _ _ _ n z _ _ sb => floats_of [n] ++ need_blk fuel z ++ need_blk fuel sb
                                end) items ++ need_tl t
        end
      end.
    (* and everything those need in turn *)
    Fixpoint closure (fuel : nat) (vs acc : list nat) : list nat :=
      match fuel with
      | O => acc
      | S fuel =>
          fold_left (fun acc v => if mem_nat v acc then acc
                                  else match assoc v (s_fl s) with
                                       | Some d => closure fuel (floats_of (f_args d)) (v :: acc)
                                       | None => acc
                                       end) vs acc
      end.
    Definition need_all (b : blk) : list nat := closure 4000 (need_blk 4000 b) [].
    Definition inter (a b : list nat) : list nat := filter (fun v => mem_nat v b) a.

    (* the longest chain first; of two equally long, the one met first *)
    Fixpoint insert_by (v : nat) (l : list nat) : list nat :=
      match l with
      | [] => [v]
      | w :: l' => if Nat.ltb (snd (var_info s w)) (snd (var_info s v)) then v :: l else w :: insert_by v l'
      end.
    Definition by_long (vs : list nat) : list nat := fold_left (fun acc v => if mem_nat v acc then acc else insert_by v acc) vs [].
    Fixpoint insert_short (v : nat) (l : list nat) : list nat :=
      match l with
      | [] => [v]
      | w :: l' => if Nat.ltb (snd (var_info s v)) (snd (var_info s w)) then v :: l else w :: insert_short v l'
      end.
    Fixpoint insert_id (v : nat) (l : list nat) : list nat :=
      match l with [] => [v] | w :: l' => if Nat.ltb v w then v :: l else w :: insert_id v l' end.
    (* THE RULE FOR THE ORDER of the pieces of arithmetic (each is placed just before the first thing that needs it,
       except under rules 2 and 3); of several needed at one place:
         0  the one that ends the longest chain first (what waits for a read before what only counts);
         1  the one that ends the shortest chain first (what only counts before what waits for a read);
         2  in the order they were written, and each is placed where it was written;
         3  as rule 0, but each is placed AS EARLY as the numbers it needs exist (what only counts comes first of
            all; what waits for a read comes right after the read). *)
    Definition by_depth (vs : list nat) : list nat :=
      match ord with
      | 0 | 3 => by_long vs
      | 1 => fold_left (fun acc v => if mem_nat v acc then acc else insert_short v acc) vs []
      | _ => fold_left (fun acc v => if mem_nat v acc then acc else insert_id v acc) vs []
      end.
    (* rule 2 only: everything written before variable number `lim` that the rest still needs *)
    Definition written_before (lim : nat) (b : blk) : list nat :=
      match ord with
      | 2 => fold_left (fun acc v => if mem_nat v acc then acc else insert_id v acc) (filter (fun v => Nat.ltb v lim) (need_all b)) []
      | _ => []
      end.
    (* rule 3 only: the pieces THIS block needs (not those only an arm inside it needs), in the order of their first
       use, that can be worked out now: every number they are made of is there *)
    Definition need_here (b : blk) : list nat :=
      match b with
      | Blk items t =>
          let of_if (c : atom) (bt be : blk) := floats_of [c] ++ inter (need_all bt) (need_all be) in
          flat_map (fun it => match it with
                              | IBind _ _ _ args => floats_of args
                              | IIf _ _ _ _ _ c bt be => of_if c bt be
                              | INat _ _ _ _ _ n _ _ _ _ => floats_of [n]
                              end) items
          ++ match t with
             | TA a => match a with AV v => match assoc v (s_fl s) with Some d => floats_of (f_args d) | None => [] end | AT _ => [] end
             | TCall _ args => by_long (floats_of args)
             | TIf _ _ _ c bt be => of_if c bt be
             | TNat _ _ _ n _ _ _ _ => floats_of [n]
             end
      end.
    Fixpoint can_now (fuel : nat) (sc : list scv) (v : nat) : bool :=
      match fuel with
      | O => false
      | S fuel =>
          match assoc v (s_fl s) with
          | Some d => forallb (fun a => match a with AT _ => true | AV w => can_now fuel sc w end) (f_args d)
          | None => existsb (fun x => match x with SV w => Nat.eqb w v | SF _ => false end) sc
          end
      end.
    Definition early (sc : list scv) (b : blk) : list nat :=
      match ord with
      | 3 => filter (can_now 4000 sc) (rev (closure 4000 (need_here b) []))
      | _ => []
      end.

    Fixpoint idx_v (v : nat) (sc : list scv) (i : nat) : option nat :=
      match sc with [] => None | SV w :: sc => if Nat.eqb v w then Some i else idx_v v sc (S i) | SF _ :: sc => idx_v v sc (S i) end.
    Fixpoint idx_f (k : nat) (sc : list scv) (i : nat) : option nat :=
      match sc with [] => None | SF j :: sc => if Nat.eqb j k then Some i else idx_f k sc (S i) | SV _ :: sc => idx_f k sc (S i) end.
    Definition atom_tm (sc : list scv) (a : atom) : option term :=
      match a with AT t => Some t | AV v => option_map tRel (idx_v v sc 0) end.
    Fixpoint atoms_tm (sc : list scv) (l : list atom) : option (list term) :=
      match l with
      | [] => Some []
      | a :: l => match atom_tm sc a, atoms_tm sc l with Some t, Some ts => Some (t :: ts) | _, _ => None end
      end.
    Definition head_tm (sc : list scv) (h : head) : option term :=
      match h with
      | HC kn u => Some (tConst (if has_twin kn then twin kn else kn) u)
      | HK ind i u => Some (tConstruct ind i u)
      | HF k => option_map tRel (idx_f k sc 0)
      end.
    Definition app_tm (sc : list scv) (h : head) (args : list atom) : option term :=
      match head_tm sc h, atoms_tm sc args with
      | Some f, Some [] => Some f
      | Some f, Some ts => Some (tApp f ts)
      | _, _ => None
      end.
    Definition kname (n : nat) : aname := mkBindAnn (nNamed ("k" ^ string_of_nat n)) Relevant.

    (* write the floating steps `vs` that are not written yet (each after what it needs), then go on *)
    Fixpoint wfloats (fuel : nat) (vs : list nat) (sc : list scv) (em : list nat) (n : nat)
             (k : list scv -> list nat -> nat -> option term) {struct fuel} : option term :=
      match fuel with
      | O => None
      | S fuel =>
        match vs with
        | [] => k sc em n
        | v :: vs =>
            if mem_nat v em then wfloats fuel vs sc em n k
            else match assoc v (s_fl s) with
                 | None => wfloats fuel vs sc em n k
                 | Some d =>
                     wfloats fuel (floats_of (f_args d)) sc em n (fun sc em n =>
                       if mem_nat v em then wfloats fuel vs sc em n k
                       else match app_tm sc (f_h d) (f_args d), wfloats fuel vs (SV v :: sc) (v :: em) (S n) k with
                            | Some rhs, Some body => Some (tLetIn (kname n) rhs (f_ty d) body)
                            | _, _ => None
                            end)
                 end
        end
      end.

    Fixpoint wblk (fuel : nat) (sc : list scv) (em : list nat) (n : nat) (b : blk) {struct fuel} : option term :=
      match fuel with
      | O => None
      | S fuel =>
        let wtl (sc : list scv) (em : list nat) (n : nat) (t : tl) : option term :=
          match t with
          | TA a =>
              wfloats 4000 (match a with AV v => written_before v (Blk [] (TA a)) | AT _ => [] end) sc em n (fun sc em n =>
              match a with
              | AV v => if mem_nat v em then atom_tm sc a
                        else match assoc v (s_fl s) with
                             | Some d => wfloats 4000 (by_depth (floats_of (f_args d))) sc em n (fun sc _ _ => app_tm sc (f_h d) (f_args d))
                             | None => atom_tm sc a
                             end
              | AT _ => atom_tm sc a
              end)
          | TCall h args =>
              wfloats 4000 (written_before 1000000 (Blk [] (TCall h args)) ++ by_depth (floats_of args)) sc em n (fun sc _ _ => app_tm sc h args)
          | TIf lo ci p c t e =>
              let both := match ord with 0 | 1 => inter (need_all t) (need_all e) | _ => [] end in
              wfloats 4000 (written_before lo (Blk [] (TIf lo ci p c t e)) ++ floats_of [c] ++ by_depth both) sc em n (fun sc em n =>
                match atom_tm sc c, wblk fuel sc em n t, wblk fuel sc em n e with
                | Some c', Some t', Some e' =>
                    Some (tCase ci p c' [{| bcontext := []; bbody := t' |}; {| bcontext := []; bbody := e' |}])
                | _, _, _ => None
                end)
          | TNat lo ci p nn z x xna sb =>
              wfloats 4000 (written_before lo (Blk [] (TNat lo ci p nn z x xna sb)) ++ floats_of [nn]) sc em n (fun sc em n =>
                match atom_tm sc nn, wblk fuel sc em n z, wblk fuel (SV x :: sc) em n sb with
                | Some n', Some z', Some s' =>
                    Some (tCase ci p n' [{| bcontext := []; bbody := z' |}; {| bcontext := [xna]; bbody := s' |}])
                | _, _, _ => None
                end)
          end in
        wfloats 4000 (early sc b) sc em n (fun sc em n =>
        match b with
        | Blk [] t => wtl sc em n t
        | Blk (it :: rest) t =>
            let after := need_all (Blk rest t) in
            match it with
            | IBind v ty h args =>
                wfloats 4000 (written_before v (Blk (it :: rest) t) ++ by_depth (floats_of args)) sc em n (fun sc em n =>
                  match app_tm sc h args, wblk fuel (SV v :: sc) em (S n) (Blk rest t) with
                  | Some rhs, Some body => Some (tLetIn (kname n) rhs ty body)
                  | _, _ => None
                  end)
            | IIf v lo ty ci p c bt be =>
                let nt := need_all bt in let ne := need_all be in
                let hoist := match ord with 0 | 1 => add_new (inter (add_new ne nt) after) (inter nt ne) | _ => [] end in
                wfloats 4000 (written_before lo (Blk (it :: rest) t) ++ floats_of [c] ++ by_depth hoist) sc em n (fun sc em n =>
                  match atom_tm sc c, wblk fuel sc em (S n) bt, wblk fuel sc em (S n) be, wblk fuel (SV v :: sc) em (S n) (Blk rest t) with
                  | Some c', Some t', Some e', Some body =>
                      Some (tLetIn (kname n) (tCase ci p c' [{| bcontext := []; bbody := t' |}; {| bcontext := []; bbody := e' |}]) ty body)
                  | _, _, _, _ => None
                  end)
            | INat v lo ty ci p nn z x xna sb =>
                wfloats 4000 (written_before lo (Blk (it :: rest) t) ++ floats_of [nn]) sc em n (fun sc em n =>
                  match atom_tm sc nn, wblk fuel sc em (S n) z, wblk fuel (SV x :: sc) em (S n) sb, wblk fuel (SV v :: sc) em (S n) (Blk rest t) with
                  | Some n', Some z', Some s', Some body =>
                      Some (tLetIn (kname n) (tCase ci p n' [{| bcontext := []; bbody := z' |}; {| bcontext := [xna]; bbody := s' |}]) ty body)
                  | _, _, _, _ => None
                  end)
            end
        end)
      end.
  End Write.

  (* a function's own text: its parameters, then its body in the standard form.  None: this text is not read *)
  Definition std_fun (nfix : nat) (t0 : nat) (body : term) : option (term * (nat * list (nat * nat))) :=
    let ps := lam_params body in
    let np := #|ps| in
    let s0 := mkSt np [] [] [] (rev (combine (seq 0 np) (map (fun p : aname * term => (snd p, 0)) ps))) (t0, []) in
    let env := map (fun i => EA (AV i)) (rev (seq 0 np)) ++ map EF (rev (seq 0 nfix)) in
    let sc := map SV (rev (seq 0 np)) ++ map SF (rev (seq 0 nfix)) in
    if forallb (fun p : aname * term => ty_simple (snd p)) ps then
      match rexp 4000 false env (lam_body body) [] s0 with
      | Some ((tl, acc), s) =>
          match wblk s 4000 sc [] 1 (Blk (rev acc) (known s tl)) with
          | Some b => Some (fold_right (fun (p : aname * term) b => tLambda (fst p) (snd p) b) b ps, (fst (s_np s), rev (snd (s_np s))))
          | None => None
          end
      | None => None
      end
    else None.
End Read.

(* replace named functions in a text; what replaces one may depend on how many names are bound around it *)
Fixpoint repl (fuel : nat) (f : kername -> nat -> option term) (d : nat) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel =>
    let r := repl fuel f in
    match t with
    | tConst kn u => match f kn d with Some x => x | None => t end
    | tApp g args => tApp (r d g) (map (r d) args)
    | tLambda na ty b => tLambda na ty (r (S d) b)
    | tLetIn na df ty b => tLetIn na (r d df) ty (r (S d) b)
    | tCase ci p c brs =>
        tCase ci p (r d c) (map (fun b : branch term => {| bcontext := bcontext b; bbody := r (#|bcontext b| + d) (bbody b) |}) brs)
    | tFix mfix i =>
        tFix (map (fun df : def term => {| dname := dname df; dtype := dtype df; dbody := r (#|mfix| + d) (dbody df); rarg := rarg df |}) mfix) i
    | tCast t k ty => tCast (r d t) k ty
    | tProj pr t => tProj pr (r d t)
    | _ => t
    end
  end.
(* a text kept as written: only the names of the functions it calls are changed *)
Definition rename (fuel : nat) (tw : kername -> bool) (t : term) : term :=
  repl fuel (fun kn _ => if tw kn then Some (tConst (twin kn) []) else None) 0 t.

(* the twin of one definition: its text, how many of its functions were put in the standard form, how many kept as
   written, the next number for a test and the tests it has (number, kind).  `t0`: the number its first test gets --
   the tests of a whole program are numbered through, so that a measurement can name each of them *)
Definition twin_of (Σ : global_env) (mp : modpath) (root : kername) (mode : pmode) (ord : nat) (mrg : bool) (t0 : nat) (kn : kername) (body : term)
  : term * nat * nat * (nat * list (nat * nat)) :=
  let tw := has_twin Σ mp root in
  if Kername.eqb kn root then (rename 4000 tw body, 0, 0, (t0, []))
  else match body with
       | tFix mfix i =>
           let ftys := map (fun d : def term => dtype d) mfix in
           let '(ds, ok, kept, tn, tl) :=
             fold_left (fun (acc : list (def term) * nat * nat * nat * list (nat * nat)) (d : def term) =>
                          let '(ds, ok, kept, tn, tl) := acc in
                          match std_fun Σ mp root mode ord mrg ftys #|mfix| tn (dbody d) with
                          | Some (b, (tn', tl')) => (ds ++ [{| dname := dname d; dtype := dtype d; dbody := b; rarg := rarg d |}], S ok, kept, tn', tl ++ tl')
                          | None => (ds ++ [{| dname := dname d; dtype := dtype d; dbody := rename 4000 tw (dbody d); rarg := rarg d |}], ok, S kept, tn, tl)
                          end) mfix ([], 0, 0, t0, []) in
           (tFix ds i, ok, kept, (tn, tl))
       | _ =>
           match std_fun Σ mp root mode ord mrg [] 0 t0 body with
           | Some (b, ts) => (b, 1, 0, ts)
           | None => (rename 4000 tw body, 0, 1, (t0, []))
           end
       end.

(* ------------------------------------------------------------------ STEP 3: READS AND WRITES WITHOUT THE TEST
   (KQBound.v).  A loop that COUNTS -- its budget is the number of rounds left and a parameter p goes up by one every
   round (every call to itself passes `p + 1`) -- reads or writes cell p (or p + d, d a number) of a block named by a
   number in every round; all those cells are inside the block when the last one is: p + d + budget <= the block's
   length, a test made ONCE, when the loop starts.  For such a loop f the translator writes
     f_kqc   the loop as before (every read and write tested);
     f_kqp   the loop with the fact "p + d + budget <= length" as an argument that each round passes on, and at each
             such read and write its proof (rd_p ..): Rocq's type checker checks it, and it is never compiled;
     f_kqu   the same text with the proofs left out (rd_u ..: no test on the machine) -- equal to f_kqc by
             computation (`f_kqu_eq`, checked);
     f_kq    what callers call: the test at the start (kq_fits), then f_kqu if it says yes, else f_kqc; with a copy
             (f_kqwp) in which "the test said yes" is turned into the fact f_kqp takes, checked too.
   Both texts of a round come out of ONE pass (b_tr, with and without the proofs), so f_kqu tests nothing that f_kqp
   does not prove inside its block. *)
Definition kn_rd      : kername := kn_of <% rd %>.
Definition kn_upd     : kername := kn_of <% upd %>.
Definition kn_rd32    : kername := kn_of <% rd32 %>.
Definition kn_upd32   : kername := kn_of <% upd32 %>.
Definition kn_rd_u    : kername := kn_of <% rd_u %>.
Definition kn_upd_u   : kername := kn_of <% upd_u %>.
Definition kn_rd32_u  : kername := kn_of <% rd32_u %>.
Definition kn_upd32_u : kername := kn_of <% upd32_u %>.
Definition kn_rd_p    : kername := kn_of <% rd_p %>.
Definition kn_upd_p   : kername := kn_of <% upd_p %>.
Definition kn_rd32_p  : kername := kn_of <% rd32_p %>.
Definition kn_upd32_p : kername := kn_of <% upd32_p %>.
Definition kn_add     : kername := kn_of <% PrimInt63.add %>.
Definition t_kq_len     : term := <% kq_len %>.
Definition t_kq_len32   : term := <% kq_len32 %>.
Definition t_fits       : term := <% fits %>.
Definition t_fits_now   : term := <% fits_now %>.
Definition t_fits_next  : term := <% fits_next %>.
Definition t_fits_next0 : term := <% fits_next0 %>.
Definition t_fits_next0l : term := <% fits_next0l %>.
Definition t_fits_nextl : term := <% fits_nextl %>.
Definition t_fits_nextr : term := <% fits_nextr %>.
Definition t_fits_nextrl : term := <% fits_nextrl %>.
Definition t_kq_fits    : term := <% kq_fits %>.
Definition t_kq_fits_ok : term := <% kq_fits_ok %>.
Definition t_andb_l     : term := <% andb_l %>.
Definition t_andb_r     : term := <% andb_r %>.
Definition t_add        : term := <% PrimInt63.add %>.
Definition t_conj       : term := <% @conj %>.
Definition t_proj1      : term := <% @proj1 %>.
Definition t_proj2      : term := <% @proj2 %>.
Definition t_I          : term := <% I %>.
Definition t_andb       : term := <% andb %>.
Definition t_bool_ty    : term := <% bool %>.
Definition t_btrue      : term := <% true %>.
Definition t_bfalse     : term := <% false %>.
Definition t_S          : term := <% S %>.
Definition ind_of (t : term) : inductive := match t with tInd i _ => i | _ => mkInd (MPfile [], "") 0 end.
Definition one63 : PrimInt63.int := Uint63.of_Z 1.

(* what a variable of a round stands for: a parameter; a parameter plus a number, written `p + c` or `c + p`; the loop
   itself; the budget's predecessor *)
Inductive bv := BParam (j : nat) | BAdd (j : nat) (c : PrimInt63.int) | BAddL (j : nat) (c : PrimInt63.int) | BSelf | BPred | BOther.
Definition bv_at (env : list bv) (k : nat) : bv := nth k env BOther.
Definition b_def (env : list bv) (d : term) : bv :=
  match d with
  | tApp (tConst kn _) [tRel k; tInt c] =>
      if Kername.eqb kn kn_add then match bv_at env k with BParam j => BAdd j c | _ => BOther end else BOther
  | tApp (tConst kn _) [tInt c; tRel k] =>
      if Kername.eqb kn kn_add then match bv_at env k with BParam j => BAddL j c | _ => BOther end else BOther
  | _ => BOther
  end.
(* a cell the loop reaches: in a narrow block?, which block (a number, or a parameter that every round passes on), at
   parameter j, plus a number (written after or before it) *)
Inductive bhk := BHLit (h : PrimInt63.int) | BHPar (j : nat).
Record bcj := mkCj { c_nar : bool; c_h : bhk; c_j : nat; c_d : option (bool * PrimInt63.int) }.
Definition bcj_eqb (a b : bcj) : bool :=
  Bool.eqb (c_nar a) (c_nar b)
  && match c_h a, c_h b with BHLit x, BHLit y => PrimInt63.eqb x y | BHPar x, BHPar y => Nat.eqb x y | _, _ => false end
  && Nat.eqb (c_j a) (c_j b)
  && match c_d a, c_d b with
     | None, None => true
     | Some (l1, x), Some (l2, y) => Bool.eqb l1 l2 && PrimInt63.eqb x y
     | _, _ => false
     end.
(* a read or a write of a block named by a number or by a parameter, at a parameter or a parameter plus a number *)
Definition b_access (env : list bv) (kn : kername) (args : list term) : option (bcj * bool) :=
  let fam := if Kername.eqb kn kn_rd then Some (false, false) else if Kername.eqb kn kn_upd then Some (false, true)
             else if Kername.eqb kn kn_rd32 then Some (true, false) else if Kername.eqb kn kn_upd32 then Some (true, true)
             else None in
  match fam, args with
  | Some (nar, wr), hb :: tRel k :: rest =>
      if Nat.eqb #|rest| (if wr then 2 else 1) then
        let hk := match hb with
                  | tInt h => Some (BHLit h)
                  | tRel kh => match bv_at env kh with BParam jh => Some (BHPar jh) | _ => None end
                  | _ => None
                  end in
        match hk, bv_at env k with
        | Some hk, BParam j => Some (mkCj nar hk j None, wr)
        | Some hk, BAdd j c => Some (mkCj nar hk j (Some (false, c)), wr)
        | Some hk, BAddL j c => Some (mkCj nar hk j (Some (true, c)), wr)
        | _, _ => None
        end
      else None
  | _, _ => None
  end.
(* the cells a round reaches, and what each call of the loop to itself passes *)
Fixpoint b_scan (fuel : nat) (env : list bv) (t : term) : list bcj * list (list bv) :=
  match fuel with
  | O => ([], [])
  | S fuel =>
      let join (l : list (list bcj * list (list bv))) := (concat (map fst l), concat (map snd l)) in
      match t with
      | tLetIn _ d _ b => join [b_scan fuel env d; b_scan fuel (b_def env d :: env) b]
      | tCase _ _ c brs => join (b_scan fuel env c :: map (fun br => b_scan fuel (repeat BOther #|bcontext br| ++ env) (bbody br)) brs)
      | tApp (tRel k) args =>
          let r := join (map (b_scan fuel env) args) in
          match bv_at env k with
          | BSelf => (fst r, map (fun a => match a with tRel k' => bv_at env k' | _ => BOther end) args :: snd r)
          | _ => r
          end
      | tApp (tConst kn _) args =>
          let r := join (map (b_scan fuel env) args) in
          match b_access env kn args with Some (c, _) => (c :: fst r, snd r) | None => r end
      | tApp f args => join (map (b_scan fuel env) (f :: args))
      | tLambda _ _ b => b_scan fuel (BOther :: env) b
      | _ => ([], [])
      end
  end.
(* a cell of the kind: every call of the loop to itself passes the budget's predecessor, j + 1 (or 1 + j), and the
   block's parameter unchanged *)
Definition b_ok (calls : list (list bv)) (r : nat) (c : bcj) : bool :=
  match calls with
  | [] => false
  | _ => forallb (fun call => match nth r call BOther with BPred => true | _ => false end
                              && match nth (c_j c) call BOther with
                                 | BAdd j' x | BAddL j' x => Nat.eqb j' (c_j c) && PrimInt63.eqb x one63
                                 | _ => false
                                 end
                              && match c_h c with
                                 | BHLit _ => true
                                 | BHPar jh => match nth jh call BOther with BParam j' => Nat.eqb j' jh | _ => false end
                                 end) calls
  end.
Fixpoint b_dedup (l acc : list bcj) : list bcj :=
  match l with [] => rev acc | c :: l => if existsb (bcj_eqb c) acc then b_dedup l acc else b_dedup l (c :: acc) end.
Fixpoint b_index (c : bcj) (l : list bcj) (k : nat) : option nat :=
  match l with [] => None | x :: l => if bcj_eqb c x then Some k else b_index c l (S k) end.

(* the terms of the fact: "cells e .. e + n - 1 of the block fit", for every cell of the plan *)
Definition cj_L (pj : nat -> term) (c : bcj) : term :=
  tApp (if c_nar c then t_kq_len32 else t_kq_len) [match c_h c with BHLit h => tInt h | BHPar jh => pj jh end].
Definition cj_E (pj : nat -> term) (c : bcj) : term :=
  match c_d c with
  | None => pj (c_j c)
  | Some (false, x) => tApp t_add [pj (c_j c); tInt x]
  | Some (true, x) => tApp t_add [tInt x; pj (c_j c)]
  end.
Definition cj_fits (pj : nat -> term) (fu : term) (c : bcj) : term := tApp t_fits [cj_L pj c; cj_E pj c; fu].
Fixpoint inv_ty (pj : nat -> term) (fu : term) (cs : list bcj) : term :=
  match cs with [] => t_True | c :: cs => tApp t_and [cj_fits pj fu c; inv_ty pj fu cs] end.
Fixpoint inv_proj (pj : nat -> term) (fu : term) (cs : list bcj) (k : nat) (H : term) : term :=
  match cs, k with
  | c :: cs', O => tApp t_proj1 [cj_fits pj fu c; inv_ty pj fu cs'; H]
  | c :: cs', S k' => inv_proj pj fu cs' k' (tApp t_proj2 [cj_fits pj fu c; inv_ty pj fu cs'; H])
  | [], _ => t_I
  end.
(* the next round's fact, for a call that passes j + 1 (`stepL`: 1 + j) *)
Definition cj_step_l (call : list bv) (c : bcj) : bool := match nth (c_j c) call BOther with BAddL _ _ => true | _ => false end.
Definition cj_next_ty (pj : nat -> term) (n : term) (stepL : bool) (c : bcj) : term :=
  let e1 := if stepL then tApp t_add [tInt one63; pj (c_j c)] else tApp t_add [pj (c_j c); tInt one63] in
  tApp t_fits [cj_L pj c; match c_d c with
                          | None => e1
                          | Some (false, x) => tApp t_add [e1; tInt x]
                          | Some (true, x) => tApp t_add [tInt x; e1]
                          end; n].
Fixpoint step_ty (pj : nat -> term) (n : term) (call : list bv) (cs : list bcj) : term :=
  match cs with [] => t_True | c :: cs => tApp t_and [cj_next_ty pj n (cj_step_l call c) c; step_ty pj n call cs] end.
Fixpoint step_pf (pj : nat -> term) (n H : term) (call : list bv) (all cs : list bcj) (k : nat) : term :=
  match cs with
  | [] => t_I
  | c :: cs' =>
      let hk := inv_proj pj (tApp t_S [n]) all k H in
      let L := cj_L pj c in
      let e := pj (c_j c) in
      let sl := cj_step_l call c in
      let pf := match c_d c, sl with
                | None, false => tApp t_fits_next0 [L; e; n; hk]
                | None, true => tApp t_fits_next0l [L; e; n; hk]
                | Some (false, x), false => tApp t_fits_next [L; e; tInt x; n; hk]
                | Some (false, x), true => tApp t_fits_nextl [L; e; tInt x; n; hk]
                | Some (true, x), false => tApp t_fits_nextr [L; e; tInt x; n; hk]
                | Some (true, x), true => tApp t_fits_nextrl [L; e; tInt x; n; hk]
                end in
      tApp t_conj [cj_next_ty pj n sl c; step_ty pj n call cs'; pf; step_pf pj n H call all cs' (S k)]
  end.

(* ONE PASS over a round, with the proofs (`prf`: the copy that is checked) or without them (the loop that is
   compiled).  `dl`: the binders below the round's start (the budget's predecessor n, and the fact H with `prf`). *)
Fixpoint b_tr (fuel : nat) (prf : bool) (m : nat) (cs : list bcj) (env : list bv) (dl : nat) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel =>
      let tr := b_tr fuel prf m cs in
      let base := if prf then 2 else 1 in
      let pj (j : nat) := tRel (dl + base + (m - 1 - j)) in
      let nT := tRel (dl + base - 1) in
      let HT := tRel dl in
      match t with
      | tLetIn na d ty b => tLetIn na (tr env dl d) ty (tr (b_def env d :: env) (S dl) b)
      | tCase ci p c brs =>
          tCase ci p (tr env dl c)
                (map (fun br => {| bcontext := bcontext br;
                                   bbody := tr (repeat BOther #|bcontext br| ++ env) (#|bcontext br| + dl) (bbody br) |}) brs)
      | tApp (tRel k) args =>
          let args' := map (tr env dl) args in
          match bv_at env k with
          | BSelf =>
              let call := map (fun a => match a with tRel k' => bv_at env k' | _ => BOther end) args in
              if prf then tApp (tRel k) (args' ++ [step_pf pj nT HT call cs cs 0]) else tApp (tRel k) args'
          | _ => tApp (tRel k) args'
          end
      | tApp (tConst kn u) args =>
          let args' := map (tr env dl) args in
          match b_access env kn args with
          | Some (c, wr) =>
              match b_index c cs 0 with
              | Some k =>
                  let nar := c_nar c in
                  let kn' := if prf then (if nar then (if wr then kn_upd32_p else kn_rd32_p) else (if wr then kn_upd_p else kn_rd_p))
                             else (if nar then (if wr then kn_upd32_u else kn_rd32_u) else (if wr then kn_upd_u else kn_rd_u)) in
                  let pf := tApp t_fits_now [cj_L pj c; nth 1 args (tRel 0); nT; inv_proj pj (tApp t_S [nT]) cs k HT] in
                  tApp (tConst kn' u) (if prf then args' ++ [pf] else args')
              | None => tApp (tConst kn u) args'
              end
          | None => tApp (tConst kn u) args'
          end
      | tApp f args => tApp (tr env dl f) (map (tr env dl) args)
      | tLambda na ty b => tLambda na ty (tr (BOther :: env) (S dl) b)
      | _ => t
      end
  end.

(* the parameters of a function's type, and what it gives back *)
Fixpoint prods (t : term) : list (aname * term) * term :=
  match t with tProd na ty b => let '(l, r) := prods b in ((na, ty) :: l, r) | _ => ([], t) end.
Definition lams (ps : list (aname * term)) (b : term) : term := fold_right (fun (pa : aname * term) acc => tLambda (fst pa) (snd pa) acc) b ps.
Definition pis (ps : list (aname * term)) (b : term) : term := fold_right (fun (pa : aname * term) acc => tProd (fst pa) (snd pa) acc) b ps.
Definition aH : aname := mkBindAnn (nNamed "H") Relevant.

(* the loop with its proofs (checked), the loop without them (compiled), and the plan; None: no loop of the kind *)
Definition b_fun (b2 : term) : option (term * term * list bcj * nat * nat * list (aname * term)) :=
  match b2 with
  | tFix [d] 0 =>
      let m := lam_count (dbody d) in
      let r := rarg d in
      let ps := lam_params (dbody d) in
      match lam_body (dbody d) with
      | tCase ci p (tRel k) [bo; bs] =>
          if Nat.eqb k (m - 1 - r) && String.eqb (ind_name (ci_ind ci)) "nat"
             && Nat.eqb #|bcontext bs| 1 && Nat.eqb #|bcontext bo| 0 then
            let envS := BPred :: rev (map BParam (seq 0 m)) ++ [BSelf] in
            let '(acc, calls) := b_scan 100000 envS (bbody bs) in
            let cs := b_dedup (filter (b_ok calls r) acc) [] in
            let ocalls := snd (b_scan 100000 (rev (map BParam (seq 0 m)) ++ [BSelf]) (bbody bo)) in
            match cs, ocalls with
            | [], _ => None
            | _, _ :: _ => None
            | _, [] =>
                let R := snd (prods (dtype d)) in
                let pj_top (j : nat) := tRel (m - 1 - j) in
                let pj_in (j : nat) := tRel (m - j) in
                let p' := {| puinst := puinst p; pparams := pparams p; pcontext := pcontext p;
                             preturn := tProd aH (inv_ty pj_in (tRel 0) cs) (lift 1 0 (preturn p)) |} in
                let bo' := {| bcontext := []; bbody := tLambda aH (inv_ty pj_top (tConstruct (ci_ind ci) 0 []) cs) (lift 1 0 (bbody bo)) |} in
                let bs' := {| bcontext := bcontext bs;
                              bbody := tLambda aH (inv_ty pj_in (tApp t_S [tRel 0]) cs)
                                               (b_tr 100000 true m cs (BOther :: envS) 0 (lift 1 0 (bbody bs))) |} in
                let fp := tFix [{| dname := dname d; dtype := pis ps (tProd aH (inv_ty pj_top (pj_top r) cs) R);
                                   dbody := lams ps (tCase ci p' (tRel k) [bo'; bs']); rarg := r |}] 0 in
                let bsu := {| bcontext := bcontext bs; bbody := b_tr 100000 false m cs envS 0 (bbody bs) |} in
                let fu := tFix [{| dname := dname d; dtype := dtype d; dbody := lams ps (tCase ci p (tRel k) [bo; bsu]); rarg := r |}] 0 in
                Some (fp, fu, cs, m, r, ps)
            end
          else None
      | _ => None
      end
  | _ => None
  end.

(* what callers call (compiled): the start test, then the loop without tests or the loop with them; and its copy
   (checked) in which "the test said yes" becomes the fact the loop with the proofs takes *)
Definition b_wrap (T : term) (cs : list bcj) (m r : nat) (ps : list (aname * term)) (kp ku kc : kername) : term * term :=
  let R := snd (prods T) in
  let pj (j : nat) := tRel (m - 1 - j) in
  let gs := map (fun c : bcj => tApp t_kq_fits [cj_L pj c; cj_E pj c; pj r]) cs in
  let G := fold_right (fun g acc => tApp t_andb [g; acc]) t_btrue gs in
  let cib := {| ci_ind := ind_of t_bool_ty; ci_npar := 0; ci_relevance := Relevant |} in
  let aB := mkBindAnn (nNamed "b") Relevant in
  let aE := mkBindAnn (nNamed "E") Relevant in
  let w := lams ps (tCase cib {| puinst := []; pparams := []; pcontext := [aB]; preturn := lift 1 0 R |} G
                          [{| bcontext := []; bbody := tApp (tConst ku []) (map pj (seq 0 m)) |};
                           {| bcontext := []; bbody := tApp (tConst kc []) (map pj (seq 0 m)) |}]) in
  (* under the binder E : G = true *)
  let pj1 (j : nat) := tRel (m - j) in
  let gs1 := map (lift 1 0) gs in
  let rest (l : list term) := fold_right (fun g acc => tApp t_andb [g; acc]) t_btrue l in
  let fix ext (l : list term) (k : nat) (E : term) : term :=
    match l, k with
    | g :: l', O => tApp t_andb_l [g; rest l'; E]
    | g :: l', S k' => ext l' k' (tApp t_andb_r [g; rest l'; E])
    | [], _ => E
    end in
  let fix pfs (l : list bcj) (k : nat) : term :=
    match l with
    | [] => t_I
    | c :: l' =>
        tApp t_conj [cj_fits pj1 (pj1 r) c; inv_ty pj1 (pj1 r) l';
                     tApp t_kq_fits_ok [cj_L pj1 c; cj_E pj1 c; pj1 r; ext gs1 k (tRel 0)]; pfs l' (S k)]
    end in
  let wp := lams ps (tApp (tCase cib {| puinst := []; pparams := []; pcontext := [aB];
                                        preturn := tProd aE (tApp t_eq [t_bool_ty; lift 1 0 G; tRel 0]) (lift 2 0 R) |} G
                                 [{| bcontext := []; bbody := tLambda aE (tApp t_eq [t_bool_ty; G; t_btrue])
                                                                (tApp (tConst kp []) (map pj1 (seq 0 m) ++ [pfs cs 0])) |};
                                  {| bcontext := []; bbody := tLambda aE (tApp t_eq [t_bool_ty; G; t_bfalse])
                                                                (tApp (tConst kc []) (map pj1 (seq 0 m))) |}])
                          [tApp t_eq_refl [t_bool_ty; G]]) in
  (w, wp).

(* what the translator defines, in this order *)
Inductive kdef := KDef (id : ident) (ty body : term) | KPrf (id : ident) (pty prf : term).

(* the name of a twin: `f_kq`; and `f_kq1` for the twin WITHOUT steps of the second kind, which a function that has
   such a step (or calls one that has) gets as well *)
Definition tname (kn : kername) (one : bool) : kername := (fst kn, snd kn ^ (if one then "_kq1" else "_kq")).

(* THE PROOF that a twin of the first kind is its function.  `todo`: the functions of the file whose twins the text
   names: the function, its type, the twin named.  With all of them put back in place of their twins the text is
   equal to the function by computation (`eq_refl`); each is then exchanged for its twin again by the equality proved
   for it before (named after the twin, `_eq`). *)
Fixpoint eq_chain (fuel : nat) (f : kername) (Tf body : term) (done todo : list (kername * term * kername)) : term :=
  match fuel with
  | O => tRel 0
  | S fuel =>
    let back (kn : kername) : option term :=
      match find (fun x : kername * term * kername => Kername.eqb kn (snd x)) done with
      | Some (o, _, _) => Some (tConst o [])
      | None => None
      end in
    match todo with
    | [] => (* the text with every function back in place, equal to ITSELF; that this text is `f` is then what the
               kernel computes -- `f` on the side it opens first *)
            tApp t_eq_refl [Tf; repl 4000 (fun kn _ => back kn) 0 body]
    | (o, T, tw) :: rest =>
        let hole := repl 4000 (fun kn d => if Kername.eqb kn tw then Some (tRel d) else back kn) 0 body in
        tApp t_eq_ind_r [T; tConst o [];
                         tLambda (mkBindAnn (nNamed "g") Relevant) T (tApp t_eq [Tf; hole; tConst f []]);
                         eq_chain fuel f Tf body (done ++ [(o, T, tw)]) rest;
                         tConst tw []; tConst (fst tw, snd tw ^ "_eq") []]
    end
  end.

(* "f_kq = f_kq1, argument by argument" -- the argument the function recurses on first: the proof is an induction
   on it *)
Definition pw_gen (lhs rhs : kername) (T : term) (r : option nat) (mark : term) : term :=
  let '(ps, R) := prods T in
  let n := #|ps| in
  let order := match r with Some r => r :: filter (fun j => negb (Nat.eqb j r)) (seq 0 n) | None => seq 0 n end in
  let pos (j : nat) : nat := match find (fun x : nat * nat => Nat.eqb (snd x) j) (combine (seq 0 n) order) with
                             | Some (q, _) => q
                             | None => 0
                             end in
  let args := map (fun j => tRel (n - 1 - pos j)) (seq 0 n) in
  let eqn := tApp t_eq [R; tApp (tConst lhs []) args; tApp (tConst rhs []) args] in
  let st := fold_right (fun j acc => match nth_error ps j with Some (na, ty) => tProd na ty acc | None => acc end) eqn order in
  tApp mark [st].
Definition pw_stmt (f : kername) (T : term) (r : option nat) : term :=
  pw_gen (tname f false) (tname f true) T r (match r with Some _ => t_kq2_ind | None => t_kq2_def end).
(* the argument a function recurses on; and whether it is one of several functions that call each other *)
Definition rec_arg (body : term) : option nat * bool :=
  match body with
  | tFix mfix i => (option_map (fun d : def term => rarg d) (nth_error mfix i), Nat.ltb 1 #|mfix|)
  | _ => (None, false)
  end.

(* WHAT A READ OR A WRITE DOES ABOUT THE BOUNDS OF ITS BLOCK -- the one setting that changes the machine code of a
   read or a write (never what a program computes):
     KQTests    (the default) every read and write tests its cell, as the model defines `rd` and `upd`.  The same for
                every program and every way of writing it; nothing to prove, and no program refused for its shape.
     KQProofs   step 3: a loop that COUNTS reads and writes with no test, after one test at its start, and the
                translator proves (by a copy of the loop that carries the proofs) that no read or write leaves its
                block.  Faster on most such loops and slower on a few (results/step3.txt); it applies to loops of
                one shape only. *)
Inductive kq_bounds := KQTests | KQProofs.

(* everything the translator makes for one program *)
Record tacc := mkAcc { a_tn : nat; a_aff : list kername; a_defs : list kdef; a_steps : list term;
                       a_ok : nat; a_kept : nat; a_tests : list (nat * nat * ident); a_two : nat; a_bad : bool;
                       a_three : nat }.

Definition twins (Σ : global_env) (root : kername) (mode : pmode) (ord : nat) (bnd : kq_bounds) (mrg : bool) : tacc :=
  let mp := fst root in
  let tw := has_twin Σ mp root in
  let funs := flat_map (fun d : kername * global_decl =>
                match snd d with
                | ConstantDecl cb => if eq_mp (fst (fst d)) mp && tw (fst d) then [(fst d, cst_type cb)] else []
                | _ => []
                end) (declarations Σ) in
  fold_left (fun (acc : tacc) (d : kername * global_decl) =>
    match snd d with
    | ConstantDecl cb =>
        match cst_body cb with
        | Some b =>
            let kn := fst d in
            let T := cst_type cb in
            if eq_mp (fst kn) mp && tw kn then
              let aff := a_aff acc in
              let isroot := Kername.eqb kn root in
              (* the functions a text names, each with its twin: the twin of the first kind (`g_kq1`) for those
                 that have one, in a text of the first kind *)
              let entries (one : bool) (named : list kername) :=
                map (fun x : kername * term => (fst x, snd x, tname (fst x) (one && memk (fst x) aff)))
                    (filter (fun x : kername * term => memk (twin (fst x)) named) funs) in
              let '(b2, ok, kept, (tn', tl2)) := twin_of Σ mp root mode ord mrg (a_tn acc) kn b in
              let named := refs 4000 mp b2 in
              let callee_aff := existsb (fun g => memk (twin g) named) aff in
              let two := filter (fun x : nat * nat => Nat.leb 100 (snd x)) tl2 in
              let tests := a_tests acc ++ map (fun x : nat * nat => (fst x, snd x, snd kn)) tl2 in
              let eqname (one : bool) := if isroot then "kq_fast_base" else snd (tname kn one) ^ "_eq" in
              (* step 3: only with the setting `KQProofs` *)
              let three := match bnd with KQProofs => if isroot then None else b_fun b2 | KQTests => None end in
              if negb callee_aff && match two with [] => true | _ => false end && match three with None => true | _ => false end then
                mkAcc tn' aff
                      (a_defs acc ++ [KDef (snd kn ^ "_kq") T b2;
                                      KPrf (eqname false) (tApp t_eq [T; if isroot then b2 else tConst (twin kn) []; tConst kn []])
                                           (eq_chain 4000 kn T b2 [] (entries false named))])
                      (a_steps acc) (a_ok acc + ok) (a_kept acc + kept) tests (a_two acc) (a_bad acc) (a_three acc)
              else
                let b1 := match two with
                          | [] => b2
                          | _ => let '(x, _, _, _) := twin_of Σ mp root mode ord false (a_tn acc) kn b in x
                          end in
                let b1 := repl 4000 (fun k _ => match find (fun g : kername => Kername.eqb k (twin g)) aff with
                                                | Some g => Some (tConst (tname g true) [])
                                                | None => None
                                                end) 0 b1 in
                let '(r, mutual) := rec_arg b in
                let first := [KDef (snd kn ^ "_kq1") T b1;
                              KPrf (eqname true) (tApp t_eq [T; if isroot then b1 else tConst (tname kn true) []; tConst kn []])
                                   (eq_chain 4000 kn T b1 [] (entries true named))] in
                match three with
                | None =>
                    mkAcc tn' (aff ++ [kn]) (a_defs acc ++ first ++ [KDef (snd kn ^ "_kq") T b2])
                          (if isroot then a_steps acc else a_steps acc ++ [pw_stmt kn T r])
                          (a_ok acc + ok) (a_kept acc + kept) tests (a_two acc + #|two|)
                          (a_bad acc || mutual || Nat.ltb 0 kept) (a_three acc)
                | Some (fp, fu, cs, m, rr, ps) =>
                    let kc := (fst kn, snd kn ^ "_kqc") in
                    let kp := (fst kn, snd kn ^ "_kqp") in
                    let ku := (fst kn, snd kn ^ "_kqu") in
                    let '(w, wp) := b_wrap T cs m rr ps kp ku kc in
                    let Tp := match fp with tFix (d :: _) _ => dtype d | _ => T end in
                    mkAcc tn' (aff ++ [kn])
                          (a_defs acc ++ first ++
                             [KDef (snd kc) T b2; KDef (snd kp) Tp fp; KDef (snd ku) T fu;
                              KPrf (snd ku ^ "_eq") (tApp t_eq [T; tConst ku []; tConst kc []]) (tApp t_eq_refl [T; tConst ku []]);
                              KDef (snd kn ^ "_kqwp") T wp; KDef (snd kn ^ "_kq") T w])
                          (a_steps acc ++ [pw_gen kc (tname kn true) T r (match r with Some _ => t_kq2_ind | None => t_kq2_def end);
                                           pw_gen (twin kn) kc T None t_kq2_wrap])
                          (a_ok acc + ok) (a_kept acc + kept) tests (a_two acc + #|two|)
                          (a_bad acc || mutual || Nat.ltb 0 kept) (S (a_three acc))
                end
            else acc
        | None => acc
        end
    | _ => acc
    end) (rev (declarations Σ)) (mkAcc 0 [] [] [] 0 0 [] 0 false 0).

(* everything the translator works out, as one value: `vm_compute` makes it in a few milliseconds *)
Record twin_res := mkRes { tr_defs : list kdef; tr_msg : string; tr_tests : string }.
Definition kq_twins (q : program) (mode : pmode) (ord : nat) (bnd : kq_bounds) : twin_res :=
  match snd q with
  | tConst root _ =>
      let a1 := twins (fst q) root mode ord bnd true in
      let a := if a_bad a1 then twins (fst q) root mode ord bnd false else a1 in
      let steps := fold_right (fun st acc => tApp t_and [st; acc]) t_True (a_steps a) in
      mkRes (a_defs a ++ [KDef "kq_fast_steps" t_Prop steps])
            ("KQ-FAST: " ^ string_of_nat (a_ok a) ^ " function(s) in the standard form, " ^ string_of_nat (a_kept a)
             ^ " kept as written, " ^ string_of_nat #|a_tests a| ^ " test(s) numbered, " ^ string_of_nat (a_two a)
             ^ " step(s) of the second kind, " ^ string_of_nat (a_three a)
             ^ " loop(s) without tests (step 3; bounds: " ^ (match bnd with KQTests => "tests" | KQProofs => "proofs" end)
             ^ "); every twin is equal to its function (checked)"
             ^ (if a_bad a1 then " -- steps of the second kind left out: one was in a function kept as written or in functions that call each other" else ""))
            (* every test: its number, its kind (c: between two plain numbers; t: two arms doing the same steps on
               numbers that may differ; j: between different work), the function it is in *)
            ("KQ-TESTS:" ^ String.concat "" (map (fun x : nat * nat * ident =>
                              let '(k, kind, f) := x in
                              " " ^ string_of_nat k ^ ":" ^ (match Nat.modulo kind 100 with 0 => "c" | 1 => "t" | _ => "j" end) ^ ":" ^ f)
                              (a_tests a)))
  | _ => mkRes [] "kq_fast: give it the name of a definition" ""
  end.

(* A twin is defined from its text AS IT IS (no step of computation is applied: the names of the steps and their order
   are what the compiler is to see), and then `twin = function` is proved by `eq_refl`: the kernel computes both sides
   and compares.  (The two helpers are written with their universes named: the library's own `tmMkDefinition` computes
   on the text it defines, which would take every `let` out again.) *)
Polymorphic Definition unq_def@{x t u | x < t +} (id : ident) (ty body : term) : TemplateMonad@{t u} unit :=
  @tmBind@{t u} Type@{x} unit (@tmUnquoteTyped@{t u} Type@{x} ty) (fun A : Type@{x} =>
  @tmBind@{t u} A unit (@tmUnquoteTyped@{t u} A body) (fun v : A =>
  @tmBind@{t u} A unit (@tmDefinitionRed_@{t u} false id None A v) (fun _ => @tmReturn@{t u} unit tt))).
Polymorphic Definition unq_prf@{t u | Set < t +} (id : ident) (pty prf : term) : TemplateMonad@{t u} unit :=
  @tmBind@{t u} Prop unit (@tmUnquoteTyped@{t u} Prop pty) (fun P : Prop =>
  @tmBind@{t u} P unit (@tmUnquoteTyped@{t u} P prf) (fun v : P =>
  @tmBind@{t u} P unit (@tmDefinitionRed_@{t u} true id None P v) (fun _ => @tmReturn@{t u} unit tt))).
Fixpoint define_all (l : list kdef) : TemplateMonad unit :=
  match l with
  | [] => tmReturn tt
  | KDef id ty b :: l => unq_def id ty b ;; define_all l
  | KPrf id pty prf :: l => unq_prf id pty prf ;; define_all l
  end.
Definition kq_define (r : twin_res) : TemplateMonad unit :=
  match tr_defs r with
  | [] => tmFail (tr_msg r)
  | l => define_all l ;; tmMsg (tr_msg r) ;; tmMsg (tr_tests r)
  end.

(* `MetaRocq Run (kq_fast main).`   or, with the choices settled by a measurement,   `MetaRocq Run (kq_fast_with (PUse [2; 5]) main).`
   Every setting at once: `kq_fast_full ORDER BOUNDS CHOICES main`, e.g. `kq_fast_full 3 KQProofs (PUse [2; 5]) main`
   (ORDER: the order rule, 3 unless an experiment says otherwise; BOUNDS: `KQTests` or `KQProofs`, above). *)
(* (the program is handed over as its TEXT, and only that text is computed on: computing on the program itself would
   set Rocq to working out what it does on every input) *)
Notation kq_fast_full o b m x :=
  (kq_define ltac:(run_template_program (tmQuoteRec x) (fun q => let t := eval vm_compute in (kq_twins q m o b) in exact t)))
  (only parsing).
Notation kq_fast_ord o m x := (kq_fast_full o KQTests m x) (only parsing).
Notation kq_fast_with m x := (kq_fast_ord 3 m x) (only parsing).
Notation kq_fast x := (kq_fast_with PPlain x) (only parsing).

(* ------------------------------------------------------------------ THE PROOF OF THE STEPS OF THE SECOND KIND
   Every program ends with  `Lemma main_kq_eq : main_kq = main.  Proof. kq_fast_qed kq_fast_steps kq_fast_base. Qed.`
   `kq_fast_steps` lists "f_kq = f_kq1, argument by argument" for each function with a step of the second kind and
   each function that calls one, callees first (`True` when there is none); `kq_fast_base` is `main_kq1 = main` (or
   `main_kq = main`), proved by computation as above.  Each statement is proved the same way: induction on the
   function's budget; the two twins written out one step; every function proved before replaced by its twin of the
   first kind, and the call to itself by the induction; then a case split on every test until the two sides are the
   same text.  No step looks at what the program does, and the kernel checks the proof. *)
Ltac kq_head t := lazymatch t with ?f _ => kq_head f | _ => t end.
Ltac kq_inner c := lazymatch c with context [if ?d then _ else _] => kq_inner d | _ => c end.
Ltac kq_refl := lazymatch goal with |- ?a = ?a => reflexivity end.
Ltac kq_unfold := progress (cbv delta [kq_select kq_selectn kq_sel_lts kq_sel_les kq_sel_eq kq_sel_ltu kq_sel_leu
                                      kq_sel_ges kq_sel_gts kq_sel_ne kq_sel_geu kq_sel_gtu kq_jump andb orb negb] beta iota).
Ltac kq_split := match goal with |- context [if ?c then _ else _] =>
                   let d := kq_inner c in (match type of d with bool => idtac end); destruct d; cbv beta iota end.
Ltac kq_close := repeat (first [kq_refl | kq_unfold | kq_split]);
                 first [kq_refl | fail 1 "KQ-FAST: a step of the second kind is not proved"].
Ltac kq_rw := repeat match goal with H : _ |- _ => progress (try rewrite !H) end.
Ltac kq_fn := lazymatch goal with
              | |- ?L = ?R => let f := kq_head L in let g := kq_head R in cbv delta [f g]; cbv beta iota zeta
              end; kq_rw; kq_close.
Ltac kq_fn_with H := lazymatch goal with
              | |- ?L = ?R => let f := kq_head L in let g := kq_head R in
                              cbv delta [f g] in H; cbv beta iota zeta in H; cbv delta [f g]; cbv beta iota zeta
              end; kq_rw; kq_close.
Ltac kq_wrap := lazymatch goal with
                | |- ?L = _ => let f := kq_head L in cbv delta [f]; cbv beta;
                               match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity
                end.
Ltac kq_one := lazymatch goal with
               | |- kq2_ind _ => cbv beta delta [kq2_ind]; let n := fresh "n" in let IH := fresh "IH" in
                                 intro n; induction n as [|n IH]; intros; [kq_fn | kq_fn_with IH]
               | |- kq2_def _ => cbv beta delta [kq2_def]; intros; kq_fn
               | |- kq2_wrap _ => cbv beta delta [kq2_wrap]; intros; kq_wrap
               end.
Ltac kq_steps := lazymatch goal with
                 | |- True => exact I
                 | |- ?A /\ ?B => let h := fresh "KQ" in assert (h : A) by kq_one;
                                  split; [exact h | cbv beta delta [kq2_ind kq2_def kq2_wrap] in h; kq_steps]
                 end.
Ltac kq_fast_qed S B :=
  let KQS := fresh "KQS" in
  assert (KQS : S) by (cbv delta [S]; kq_steps);
  cbv delta [S] in KQS;
  repeat (lazymatch type of KQS with _ /\ _ => let A := fresh "KQ" in destruct KQS as [A KQS] end);
  cbv beta delta [kq2_ind kq2_def kq2_wrap] in *;
  lazymatch type of B with
  | ?L = _ => lazymatch goal with
              | |- ?G = _ =>
                  (* the program written out, every function proved before replaced by its twin of the first kind:
                     then the fact (stated on the text of the first kind) is the same text *)
                  cbv delta [G]; cbv beta zeta; kq_rw;
                  let B' := fresh "B" in pose proof B as B'; cbv beta zeta in B'; exact B'
              end
  end.
