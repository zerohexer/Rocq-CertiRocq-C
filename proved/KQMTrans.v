(** The translator for kit programs: Rocq functions over the kit's memory (KQRun.v) to KQL, plus the statement
    that each KQL function computes its Rocq function.

    `kqm_translate f "name"` reads [f] and every function of the same file it uses and defines, for each function
    [g], the KQL function [g_kqm], the program [name], and the statement [g_kstmt].  Each statement is then proved by
    [kqm_auto] (KQMAuto.v) and checked by Rocq's kernel.  Nothing about the translator is trusted: a wrong translation
    is a statement that does not prove.

    What it reads (anything else is refused, with a message):
    - parameters: [nat] (a counter; the one the function recurses on comes first), [int], and at most one memory
      [mem], last; a result [int] or [mem];
    - in a body: [match] on a counter, [if] on a comparison of two numbers (also under [&&], [||], [negb]), [let],
      the arithmetic of [PrimInt63] (also the signed order and [asr]), [rd], [upd], calls of the file's functions,
      numbers written in the program, and helpers (non-recursive definitions of the file or of KQRun.v);
    - the memory is used only while it is the current one: after a write or a call that writes, the memory it was
      made from is gone. *)

From Stdlib Require Import ZArith Uint63 List.
From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Template Require Import All.
From compcert Require Import Maps.
From KQC Require Import KQL KQLAuto KQMSem KQMAuto.
Require KQ.KQRun KQ.hw.Runtime.
Import MonadNotation ListNotations.
Open Scope bs.

(* ------------------------------------------------------------------ names *)
Definition eq_mp (a b : modpath) : bool := match ModPathComp.compare a b with Eq => true | _ => false end.
Definition kn_of (t : term) : kername := match t with tConst kn _ => kn | _ => (MPfile [], "") end.
Definition ind_of (t : term) : inductive :=
  match t with tInd i _ => i | _ => {| inductive_mind := (MPfile [], ""); inductive_ind := 0 |} end.

Definition kn_rd := kn_of <% KQ.KQRun.rd %>.
Definition kn_upd := kn_of <% KQ.KQRun.upd %>.
Definition kn_rd32 := kn_of <% KQ.KQRun.rd32 %>.
Definition kn_upd32 := kn_of <% KQ.KQRun.upd32 %>.
Definition kn_kmem := kn_of <% KQ.KQRun.mem %>.
Definition kn_kq_nat := kn_of <% KQ.KQRun.kq_nat %>.
Definition kn_int := kn_of <% PrimInt63.int %>.
Definition kn_andb := kn_of <% andb %>.
Definition kn_orb := kn_of <% orb %>.
Definition kn_negb := kn_of <% negb %>.
Definition ind_nat := ind_of <% nat %>.
Definition ind_bool := ind_of <% bool %>.
Definition kn_fst := kn_of <% @fst %>.
Definition kn_snd := kn_of <% @snd %>.
Definition ind_prod := ind_of <% @prod %>.
Definition kit_mp : modpath := fst kn_rd.
(* the machine's operations (KQRun.v): the Rocq constant, the KQL operation, how many numbers it takes before the memory *)
Definition hw_table : list (kername * term * nat) :=
  [ (kn_of <% KQ.KQRun.hw_load %>, <% HLoad %>, 4)
  ; (kn_of <% KQ.KQRun.hw_store %>, <% HStore %>, 3)
  ; (kn_of <% KQ.KQRun.hw_store64 %>, <% HStore64 %>, 3)
  ; (kn_of <% KQ.KQRun.hw_atomic %>, <% HAtomic %>, 6)
  ; (kn_of <% KQ.KQRun.hw_atomic64 %>, <% HAtomic64 %>, 6)
  ; (kn_of <% KQ.KQRun.hw_cas %>, <% HCas %>, 6)
  ; (kn_of <% KQ.KQRun.hw_cas64 %>, <% HCas64 %>, 7)
  ; (kn_of <% KQ.KQRun.hw_aload %>, <% HALoad %>, 4)
  ; (kn_of <% KQ.KQRun.hw_astore %>, <% HAStore %>, 3)
  ; (kn_of <% KQ.KQRun.hw_astore64 %>, <% HAStore64 %>, 3)
  ; (kn_of <% KQ.KQRun.hw_fence %>, <% HFence %>, 1)
  ; (kn_of <% KQ.KQRun.hw_copy %>, <% HCopy %>, 3)
  ; (kn_of <% KQ.KQRun.hw_fill %>, <% HFill %>, 3)
  ; (kn_of <% KQ.KQRun.hw_cmp %>, <% HCmp %>, 5)
  ; (kn_of <% KQ.KQRun.hw_call %>, <% HCall %>, 4)
  ; (kn_of <% KQ.KQRun.hw_run %>, <% HRun %>, 10)
  ; (kn_of <% KQ.KQRun.hw_code_sync %>, <% HCodeSync %>, 2)
  ; (kn_of <% KQ.hw.Runtime.hw_irq_take %>, <% HIrqTake %>, 2) ].
Definition hw_lookup (kn : kername) : option (term * nat) :=
  match List.find (fun e => Kername.eqb (fst (fst e)) kn) hw_table with
  | Some e => Some (snd (fst e), snd e)
  | None => None
  end.
Definition q_Ehw := <% Ehw %>.
Definition q_Ehwf := <% Ehwf %>.
(* the machine's numbers: the Rocq constant and the KQL operation *)
Definition hwf_table : list (kername * term) :=
  [ (kn_of <% KQ.KQRun.hw_addr %>, <% FAddr %>)
  ; (kn_of <% KQ.hw.Runtime.hw_irq_info %>, <% FIrqInfo %>)
  ; (kn_of <% KQ.hw.Runtime.hw_irq_entry %>, <% FIrqEntry %>)
  ; (kn_of <% KQ.hw.Runtime.hw_cpu_code %>, <% FCpuCode %>)
  ; (kn_of <% KQ.hw.Runtime.hw_sym %>, <% FSym %>) ].
Definition hwf_lookup (kn : kername) : option term :=
  match List.find (fun e => Kername.eqb (fst e) kn) hwf_table with Some e => Some (snd e) | None => None end.

Definition prim_mp : modpath := fst (kn_of <% PrimInt63.add %>).
Definition uint63_mp : modpath := fst (kn_of <% Uint63.opp %>).

(* KQL syntax, as terms *)
Definition q_Avar := <% Avar %>.
Definition q_Aint := <% Aint %>.
Definition q_Eret := <% Eret %>.
Definition q_Eop := <% Eop %>.
Definition q_Eif := <% Eif %>.
Definition q_Esel := <% Esel %>.
Definition q_Ecall := <% Ecall %>.
Definition q_Ekld := <% Ekld %>.
Definition q_Ekst := <% Ekst %>.
Definition q_Ekld32 := <% Ekld32 %>.
Definition q_Ekst32 := <% Ekst32 %>.
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
Definition q_runk := <% runk %>.
Definition q_runx := <% runx %>.
Definition q_Zlt := <% Z.lt %>.
Definition q_Zofnat := <% Z.of_nat %>.
Definition q_natadd := <% Nat.add %>.
Definition q_wB := <% wB %>.
Definition q_cb := <% cb %>.
Definition q_cbk := <% cbk %>.
Fixpoint natq (n : nat) : term := match n with O => <% 0 %> | S n => tApp <% S %> [natq n] end.
Definition q_and := <% and %>.
Definition q_kmem := <% KQ.KQRun.mem %>.
Definition q_ex := <% @ex %>.
Definition q_zero : term := tInt 0%uint63.
Definition q_one : term := tInt 1%uint63.

Definition binop_of (s : ident) : option term :=
  if s == "add" then Some <% Badd %> else if s == "sub" then Some <% Bsub %>
  else if s == "mul" then Some <% Bmul %> else if s == "land" then Some <% Bland %>
  else if s == "lor" then Some <% Blor %> else if s == "lxor" then Some <% Blxor %>
  else if s == "lsl" then Some <% Blsl %> else if s == "lsr" then Some <% Blsr %>
  else if s == "asr" then Some <% Basr %> else if s == "div" then Some <% Bdiv %>
  else if s == "mod" then Some <% Bmod %> else if s == "mods" then Some <% Bmods %>
  else if s == "divs" then Some <% Bdivs %> else None.

Definition cmp_of (s : ident) : option term :=
  if s == "eqb" then Some <% Ceq %> else if s == "ltb" then Some <% Clt %>
  else if s == "leb" then Some <% Cle %> else if s == "ltsb" then Some <% Cslt %>
  else if s == "lesb" then Some <% Csle %> else None.

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
Inductive kind := KNat | KInt | KMem
| KRec (mk : term) (ks : list kind).   (* a record or pair of numbers and counters: [mk] is its constructor with the
                                           parameters put in; held in KQL as the flat list of its fields *)

Record finfo := mkFI {
  fi_kn : kername;            (* the Rocq function *)
  fi_id : positive;           (* its KQL name *)
  fi_kinds : list kind;       (* its parameters *)
  fi_rmem : bool;             (* it gives back a memory *)
  fi_rec : bool;              (* it calls itself *)
  fi_wr : bool }.             (* it writes the memory (or calls a function that does) *)

(* what a variable of the text stands for *)
Inductive ent :=
| ENat (a : term)       (* a counter, held in KQL as the atom [a] = ofn of it *)
| EInt (a : term)       (* a number, the atom [a] *)
| EBool (a : term)      (* a boolean, held as the atom [a]: 1 for true, 0 for false *)
| ECmp (c a b : term)   (* a boolean that is one comparison [a c b] of two atoms: kept as it is *)
| EMem (ver : nat)      (* a memory: the one the program has now when [ver] is the current version *)
| ERec (es : list ent)  (* a record or pair: its fields *)
| ESelf.                (* the function being read, calling itself *)

Record st := mkSt { s_next : positive; s_ver : nat }.

Definition K := st -> tres (term * st).
Definition KA := term -> st -> tres (term * st).

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

(* beta-reduce a helper's body against its arguments, as [let]s *)
Fixpoint beta_lets (b : term) (args : list term) : term :=
  match b, args with
  | tLambda na ty body, a :: args => tLetIn na a ty (beta_lets body (map (lift0 1) args))
  | _, [] => b
  | _, _ => mkApps b args
  end.

(* arithmetic on variables and numbers only: worked out whether or not it is wanted, without a jump *)
Fixpoint simple_term (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tRel _ | tInt _ => true
      | tApp (tConst kn _) args =>
          eq_mp (fst kn) prim_mp && (match binop_of (snd kn) with Some _ => true | None => false end)
          && forallb (simple_term fuel) args
      | tCase ci _ c [b0; b1] =>
          (* a choice between two such numbers on a test of such numbers *)
          Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool)
          && simple_test fuel c
          && simple_term fuel (bbody b0) && simple_term fuel (bbody b1)
      | _ => false
      end
  end
with simple_test (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tRel _ => true
      | tApp (tConst kn _) args =>
          (eq_mp (fst kn) prim_mp && (match cmp_of (snd kn) with Some _ => true | None => false end)
           && forallb (simple_term fuel) args)
          || ((Kername.eqb kn kn_andb || Kername.eqb kn kn_orb || Kername.eqb kn kn_negb)
              && forallb (simple_test fuel) args)
      | _ => false
      end
  end.

(* if-conversion with early reads: the same as [simple_term], and a read of the current memory is allowed too.  A read is
   total (outside a block it gives 0), so it can be run whether or not its arm is taken; both arms are then worked out
   and one is taken, without a jump.  [n_rd] counts the reads, to keep the work of the arm not taken small. *)
Fixpoint spec_term (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tRel _ | tInt _ => true
      | tApp (tConst kn _) args =>
          if Kername.eqb kn kn_rd || Kername.eqb kn kn_rd32 then
            match args with
            | [h; i; tRel _] => spec_term fuel h && spec_term fuel i
            | _ => false
            end
          else
            eq_mp (fst kn) prim_mp && (match binop_of (snd kn) with Some _ => true | None => false end)
            && forallb (spec_term fuel) args
      | tCase ci _ c [b0; b1] =>
          Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool)
          && spec_test fuel c
          && spec_term fuel (bbody b0) && spec_term fuel (bbody b1)
      | _ => false
      end
  end
with spec_test (fuel : nat) (t : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match t with
      | tRel _ => true
      | tApp (tConst kn _) args =>
          (eq_mp (fst kn) prim_mp && (match cmp_of (snd kn) with Some _ => true | None => false end)
           && forallb (spec_term fuel) args)
          || ((Kername.eqb kn kn_andb || Kername.eqb kn kn_orb || Kername.eqb kn kn_negb)
              && forallb (spec_test fuel) args)
      | _ => false
      end
  end.

Fixpoint n_rd (fuel : nat) (t : term) : nat :=
  match fuel with
  | O => 0
  | S fuel =>
      match t with
      | tApp (tConst kn _) args =>
          (if Kername.eqb kn kn_rd || Kername.eqb kn kn_rd32 then 1 else 0)
          + fold_left (fun a x => a + n_rd fuel x) args 0
      | tCase _ _ c brs => n_rd fuel c + fold_left (fun a b => a + n_rd fuel (bbody b)) brs 0
      | _ => 0
      end
  end.

(* two numbers that are worked out both, one taken: no jump.  Plain arithmetic always; with reads, a few of them.
   Used for a choice between two values only.  Merging a chain of calls into one call keeps to plain arithmetic: a
   chain of tests on a state that cycles (a state machine) is predicted well, and a conditional move in place of the
   jump makes each round wait for the one before and read on every path. *)
Definition choice_ok (a0 a1 : term) : bool :=
  (simple_term 100 a0 && simple_term 100 a1)
  || (spec_term 100 a0 && spec_term 100 a1 && Nat.leb (n_rd 100 a0 + n_rd 100 a1) 3).

Fixpoint opt_all_t {A} (l : list (option A)) : option (list A) :=
  match l with [] => Some [] | Some a :: l => option_map (cons a) (opt_all_t l) | None :: _ => None end.

(* ---- if c then F a.. else F b..  becomes  F (if c then a else b)..  with the tests worked out once, like the kit's
   [if]-merging: a chain of tests whose every end is a call of the function itself, the arguments of the calls differing
   only in numbers that are simple and in the values written by [upd]. *)
(* ---- records and pairs of numbers: read as the list of their fields, never built *)
Definition mk_npar (mk : term) : nat := match mk with tApp _ ps => length ps | _ => 0 end.

(* the type of the j-th field (from the first) of a record whose parameters are [params] *)
Fixpoint inst_ty (fuel : nat) (params : list term) (j : nat) (ty : term) : option term :=
  match fuel with
  | O => None
  | S fuel =>
      match ty with
      | tRel m => if Nat.ltb m j then None
                  else let q := m - j in
                       if Nat.ltb q (length params) then nth_error params (length params - 1 - q) else None
      | tConst _ _ | tInd _ _ => Some ty
      | tApp f args =>
          match inst_ty fuel params j f, opt_all_t (map (inst_ty fuel params j) args) with
          | Some f', Some args' => Some (tApp f' args')
          | _, _ => None
          end
      | _ => None
      end
  end.

Definition is_mem_kind (k : kind) : bool := match k with KMem => true | _ => false end.

Fixpoint kind_of (fuel : nat) (Σ : global_env) (ty : term) : option kind :=
  match fuel with
  | O => None
  | S fuel =>
      let rec_kind (i : inductive) (u : Instance.t) (params : list term) : option kind :=
        if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then Some KNat
        else if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then None
        else match lookup_env Σ (inductive_mind i) with
             | Some (InductiveDecl mib) =>
                 match nth_error (ind_bodies mib) (inductive_ind i) with
                 | Some oib =>
                     match ind_ctors oib with
                     | [cb] =>
                         if Nat.eqb (length params) (ind_npars mib) then
                           let flds := rev (map decl_type (cstr_args cb)) in
                           let fk := fun j t => match inst_ty 50 params j t with
                                                | Some t' => kind_of fuel Σ t'
                                                | None => None end in
                           match opt_all_t (mapi fk flds) with
                           | Some ks =>
                               if existsb is_mem_kind ks then None
                               else Some (KRec (match params with [] => tConstruct i 0 u
                                                | _ => tApp (tConstruct i 0 u) params end) ks)
                           | None => None
                           end
                         else None
                     | _ => None
                     end
                 | None => None
                 end
             | _ => None
             end in
      match ty with
      | tInd i u => rec_kind i u []
      | tConst kn _ => if Kername.eqb kn kn_int then Some KInt else if Kername.eqb kn kn_kmem then Some KMem else None
      | tApp (tInd i u) params => rec_kind i u params
      | _ => None
      end
  end.

(* the KQL atoms of an entry, in order *)
Fixpoint atoms_of (fuel : nat) (e : ent) : list term :=
  match fuel with
  | O => []
  | S fuel =>
      match e with
      | EInt a | ENat a => [a]
      | ERec es => flat_map (atoms_of fuel) es
      | _ => []
      end
  end.

(* the leaves of a kind: the numbers and counters a record is held as *)
Fixpoint leaves (fuel : nat) (k : kind) : list kind :=
  match fuel with
  | O => []
  | S fuel =>
      match k with
      | KRec _ ks => flat_map (leaves fuel) ks
      | KMem => []
      | k => [k]
      end
  end.

Fixpoint term_same (fuel : nat) (a b : term) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match a, b with
      | tRel i, tRel j => Nat.eqb i j
      | tInt x, tInt y => PrimInt63.eqb x y
      | tConst k _, tConst k' _ => Kername.eqb k k'
      | tApp f xs, tApp g ys =>
          term_same fuel f g && Nat.eqb (length xs) (length ys)
          && forallb (fun p => term_same fuel (fst p) (snd p)) (combine xs ys)
      | _, _ => false
      end
  end.

Definition mk_br (a : term) : branch term := {| bcontext := []; bbody := a |}.

Inductive mtree := MCall (n : nat) (args : list term) | MIf (j : nat) (t0 t1 : mtree).

Fixpoint mt_build (fuel : nat) (Γ : list ent) (t : term) (conds : list term) {struct fuel}
  : option (mtree * list term * option (case_info * predicate term)) :=
  match fuel with
  | O => None
  | S fuel =>
      match t with
      | tCase ci p c [b0; b1] =>
          if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
            let j := length conds in
            match mt_build fuel Γ (bbody b0) (conds ++ [c]) with
            | Some (m0, conds1, _) =>
                match mt_build fuel Γ (bbody b1) conds1 with
                | Some (m1, conds2, _) => Some (MIf j m0 m1, conds2, Some (ci, p))
                | None => None
                end
            | None => None
            end
          else None
      | tApp (tRel n) args =>
          match nth_error Γ n with
          | Some ESelf => Some (MCall n args, conds, None)
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint mt_callee (m : mtree) : nat :=
  match m with MCall n _ => n | MIf _ t0 _ => mt_callee t0 end.

Fixpoint mt_ok (n len : nat) (m : mtree) : bool :=
  match m with
  | MCall n' args => Nat.eqb n n' && Nat.eqb (length args) len
  | MIf _ t0 t1 => mt_ok n len t0 && mt_ok n len t1
  end.

(* the choice between two arguments on the test number [j] of [k] *)
Fixpoint merge_arg (fuel : nat) (ci : case_info) (p : predicate term) (cnd : term) (a0 a1 : term) : option term :=
  match fuel with
  | O => None
  | S fuel =>
      if term_same 100 a0 a1 then Some a0
      else if simple_term 100 a0 && simple_term 100 a1 then Some (tCase ci p cnd [mk_br a0; mk_br a1])
      else match a0, a1 with
           | tApp (tConst k u) [h0; i0; v0; m0], tApp (tConst k' _) [h1; i1; v1; m1] =>
               if Kername.eqb k kn_upd && Kername.eqb k' kn_upd then
                 match merge_arg fuel ci p cnd h0 h1, merge_arg fuel ci p cnd i0 i1,
                       merge_arg fuel ci p cnd v0 v1, merge_arg fuel ci p cnd m0 m1 with
                 | Some h, Some i, Some v, Some m => Some (tApp (tConst k u) [h; i; v; m])
                 | _, _, _, _ => None
                 end
               else None
           | _, _ => None
           end
  end.

(* argument number [i] of the whole tree, the tests being the variables [k-1-j] of the [k] lets *)
Fixpoint mt_arg (k : nat) (ci : case_info) (p : predicate term) (i : nat) (m : mtree) : option term :=
  match m with
  | MCall _ args => option_map (lift0 k) (nth_error args i)
  | MIf j t0 t1 =>
      match mt_arg k ci p i t0, mt_arg k ci p i t1 with
      | Some a0, Some a1 => merge_arg 50 ci p (tRel (k - 1 - j)) a0 a1
      | _, _ => None
      end
  end.

Fixpoint lets_of (conds : list term) (j : nat) (body : term) : term :=
  match conds with
  | [] => body
  | c :: conds =>
      tLetIn {| binder_name := nAnon; binder_relevance := Relevant |} (lift0 j c) (tInd ind_bool []) (lets_of conds (S j) body)
  end.

Definition merge_ifs (Γ : list ent) (t : term) : option term :=
  match mt_build 200 Γ t [] with
  | Some (m, conds, Some (ci, p)) =>
      let n := mt_callee m in
      match m with
      | MCall _ _ => None
      | MIf _ _ _ =>
          let k := length conds in
          let len := match m with MCall _ a => length a | MIf _ _ _ =>
                       (fix first (m : mtree) := match m with MCall _ a => length a | MIf _ t0 _ => first t0 end) m end in
          if mt_ok n len m then
            match opt_all_t (map (fun i => mt_arg k ci p i m) (seq 0 len)) with
            | Some args => Some (lets_of conds 0 (tApp (tRel (n + k)) args))
            | None => None
            end
          else None
      end
  | _ => None
  end.

Section TR.
Variable Σ : global_env.
Variable mp : modpath.                   (* the file of the program *)
Variable fns : list finfo.
Variable self : finfo.

Definition find_fn (kn : kername) : option finfo :=
  List.find (fun f => Kername.eqb (fi_kn f) kn) fns.

(* a helper: a definition of the file or of KQRun.v that does not call itself, written out where it is used *)
Definition helper_body (kn : kername) : option term :=
  if eq_mp (fst kn) mp || eq_mp (fst kn) kit_mp || eq_mp (fst kn) uint63_mp then
    match find_fn kn with
    | Some _ => None
    | None => match lookup_env Σ kn with
              | Some (ConstantDecl cb) =>
                  match cst_body cb with Some b => if has_fix 1000 b then None else Some b | None => None end
              | _ => None
              end
    end
  else None.

Definition fresh (s : st) : positive * st := (s_next s, mkSt (Pos.succ (s_next s)) (s_ver s)).
Definition bump (s : st) : st := mkSt (s_next s) (S (s_ver s)).
Definition with_ver (v : nat) (s : st) : st := mkSt (s_next s) v.

Definition wrap1 (c : term) (pre : list term) (r : tres (term * st)) : tres (term * st) :=
  match r with TOk (e, s) => TOk (tApp c (pre ++ [e]), s) | TErr m => TErr m end.

Fixpoint tr_int (fuel : nat) (Γ : list ent) (t : term) (s : st) (k : KA) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tRel n => match nth_error Γ n with
              | Some (EInt a) => k a s
              | _ => TErr "a variable used as a number is not one"
              end
  | tInt _ => k (aint t) s
  | tLetIn na b ty body => tr_let fuel Γ b ty s (fun Γ' s => tr_int fuel Γ' body s k)
  | tApp (tConst kn u) args =>
      if Kername.eqb kn kn_fst || Kername.eqb kn kn_snd then
        match args with
        | [ta; tb; c] =>
            tr_field fuel Γ (tApp (tInd ind_prod []) [ta; tb]) (if Kername.eqb kn kn_fst then 0 else 1) c s (fun e s =>
              match e with EInt a => k a s | ENat a => k a s | _ => TErr "a field that is not a number" end)
        | _ => TErr "fst or snd"
        end
      else if eq_mp (fst kn) prim_mp then
        match binop_of (snd kn), args with
        | Some o, [a; b] =>
            tr_int fuel Γ a s (fun A s => tr_int fuel Γ b s (fun B s =>
              let '(x, s) := fresh s in
              wrap1 q_Eop [qpos x; o; A; B] (k (avar x) s)))
        | _, _ => TErr ("not a supported operation: " ^ snd kn)
        end
      else if (match hwf_lookup kn with Some _ => true | None => false end) then
        match hwf_lookup kn, args with
        | Some op, [a] =>
            tr_int fuel Γ a s (fun A s =>
              let '(x, s) := fresh s in
              wrap1 q_Ehwf [op; qpos x; A] (k (avar x) s))
        | _, _ => TErr ("a machine number with the wrong number of arguments: " ^ snd kn)
        end
      else if Kername.eqb kn kn_rd then
        match args with
        | [h; i; m] =>
            tr_int fuel Γ h s (fun H s => tr_int fuel Γ i s (fun I s => tr_mem fuel Γ m s (fun s =>
              let '(x, s) := fresh s in
              wrap1 q_Ekld [qpos x; H; I] (k (avar x) s))))
        | _ => TErr "rd"
        end
      else if Kername.eqb kn kn_rd32 then
        match args with
        | [h; i; m] =>
            tr_int fuel Γ h s (fun H s => tr_int fuel Γ i s (fun I s => tr_mem fuel Γ m s (fun s =>
              let '(x, s) := fresh s in
              wrap1 q_Ekld32 [qpos x; H; I] (k (avar x) s))))
        | _ => TErr "rd32"
        end
      else match find_fn kn with
      | Some f =>
          if fi_rmem f then TErr "a function giving back a memory, used as a number"
          else tr_call fuel Γ f args s (fun As s =>
                 let s1 := if fi_wr f then bump s else s in
                 let '(x, s1) := fresh s1 in
                 wrap1 q_Ecall [qpos x; qpos (fi_id f); As] (k (avar x) s1))
      | None =>
          match helper_body kn with
          | Some b => tr_int fuel Γ (beta_lets b args) s k
          | None => TErr ("not readable: " ^ snd kn)
          end
      end
  | tApp (tRel n) args =>
      match nth_error Γ n with
      | Some ESelf =>
          if fi_rmem self then TErr "a call of itself giving back a memory, used as a number"
          else tr_call fuel Γ self args s (fun As s =>
                 let s1 := if fi_wr self then bump s else s in
                 let '(x, s1) := fresh s1 in
                 wrap1 q_Ecall [qpos x; qpos (fi_id self); As] (k (avar x) s1))
      | _ => TErr "a call of a variable"
      end
  | tConst kn _ =>
      match helper_body kn with
      | Some b => tr_int fuel Γ b s k
      | None => TErr ("not readable: " ^ snd kn)
      end
  | tCase ci p c [b0; b1] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        if choice_ok (bbody b0) (bbody b1) then
          (* both numbers are worked out, one is taken: a conditional move, no jump.  A choice on [a && b], [a || b],
             [negb a] is written as choices on the parts (KQMAuto.v's kqm_ifs rewrites the Rocq text the same way) *)
          match c with
          | tApp (tConst kn _) [ca] =>
              if Kername.eqb kn kn_negb then tr_int fuel Γ (tCase ci p ca [b1; b0]) s k
              else tr_boolval fuel Γ c s (fun C s =>
                tr_int fuel Γ (bbody b0) s (fun A0 s => tr_int fuel Γ (bbody b1) s (fun A1 s =>
                  let '(x, s) := fresh s in
                  wrap1 q_Esel [qpos x; <% Ceq %>; C; aint q_zero; A1; A0] (k (avar x) s))))
          | tApp (tConst kn _) [ca; cb] =>
              if Kername.eqb kn kn_andb then tr_int fuel Γ (tCase ci p ca [mk_br (tCase ci p cb [b0; b1]); b1]) s k
              else if Kername.eqb kn kn_orb then tr_int fuel Γ (tCase ci p ca [b0; mk_br (tCase ci p cb [b0; b1])]) s k
              else
              match (if eq_mp (fst kn) prim_mp then cmp_of (snd kn) else None) with
              | Some cmp =>
                  tr_int fuel Γ ca s (fun CA s => tr_int fuel Γ cb s (fun CB s =>
                    tr_int fuel Γ (bbody b0) s (fun A0 s => tr_int fuel Γ (bbody b1) s (fun A1 s =>
                      let '(x, s) := fresh s in
                      wrap1 q_Esel [qpos x; cmp; CA; CB; A0; A1] (k (avar x) s)))))
              | None =>
                  tr_boolval fuel Γ c s (fun C s =>
                    tr_int fuel Γ (bbody b0) s (fun A0 s => tr_int fuel Γ (bbody b1) s (fun A1 s =>
                      let '(x, s) := fresh s in
                      wrap1 q_Esel [qpos x; <% Ceq %>; C; aint q_zero; A1; A0] (k (avar x) s))))
              end
          | tRel n =>
              match nth_error Γ n with
              | Some (ECmp cmp CA CB) =>
                  tr_int fuel Γ (bbody b0) s (fun A0 s => tr_int fuel Γ (bbody b1) s (fun A1 s =>
                    let '(x, s) := fresh s in
                    wrap1 q_Esel [qpos x; cmp; CA; CB; A0; A1] (k (avar x) s)))
              | _ =>
                  tr_boolval fuel Γ c s (fun C s =>
                    tr_int fuel Γ (bbody b0) s (fun A0 s => tr_int fuel Γ (bbody b1) s (fun A1 s =>
                      let '(x, s) := fresh s in
                      wrap1 q_Esel [qpos x; <% Ceq %>; C; aint q_zero; A1; A0] (k (avar x) s))))
              end
          | _ =>
              tr_boolval fuel Γ c s (fun C s =>
                tr_int fuel Γ (bbody b0) s (fun A0 s => tr_int fuel Γ (bbody b1) s (fun A1 s =>
                  let '(x, s) := fresh s in
                  wrap1 q_Esel [qpos x; <% Ceq %>; C; aint q_zero; A1; A0] (k (avar x) s))))
          end
        else
          tr_cond fuel Γ c s (fun s => tr_int fuel Γ (bbody b0) s k) (fun s => tr_int fuel Γ (bbody b1) s k)
      else TErr "a match used as a number that this translator does not read"
  | tCase ci p c [b] => tr_rec_case fuel Γ ci p c s (fun Γ' s => tr_int fuel Γ' (bbody b) s k)
  | tProj pr c =>
      tr_field fuel Γ (tInd (proj_ind pr) []) (proj_arg pr) c s (fun e s =>
        match e with EInt a => k a s | ENat a => k a s | _ => TErr "a field that is not a number" end)
  | _ => TErr "not a number this translator reads"
  end
  end

(* a counter, as the atom holding [ofn] of it *)
with tr_nat (fuel : nat) (Γ : list ent) (t : term) (s : st) (k : KA) {struct fuel} : tres (term * st) :=
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
          wrap1 q_Eop [qpos x; <% Badd %>; A; aint q_one] (k (avar x) s))
      else TErr "a constructor"
  | tApp (tConst kn _) [tInt _] =>
      (* a budget written as a number: [kq_nat 30] *)
      if Kername.eqb kn kn_kq_nat then k (aint (tApp q_ofn [t])) s else TErr "not a counter this translator reads"
  | _ => if nat_lit 10000000 t then k (aint (tApp q_ofn [t])) s else TErr "not a counter this translator reads"
  end
  end

(* the arguments of a call: the numbers and counters first; a memory last, whose work is done after them *)
with tr_call (fuel : nat) (Γ : list ent) (f : finfo) (args : list term) (s : st) (k : KA) {struct fuel}
  : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  let fix go (ks : list kind) (args : list term) (acc : list term) (s : st) : tres (term * st) :=
    match ks, args with
    | [], [] => k (qlist q_atom (rev acc)) s
    | KNat :: ks, a :: args => tr_nat fuel Γ a s (fun A s => go ks args (A :: acc) s)
    | KInt :: ks, a :: args => tr_int fuel Γ a s (fun A s => go ks args (A :: acc) s)
    | KRec mk ks' :: ks, a :: args =>
        tr_recv fuel Γ mk ks' a s (fun e s => go ks args (List.app (rev (atoms_of 20 e)) acc) s)
    | [KMem], [m] => tr_mem fuel Γ m s (fun s => k (qlist q_atom (rev acc)) s)
    | _, _ => TErr "a call with the wrong arguments"
    end in
  go (fi_kinds f) args [] s
  end

(* the work of a memory expression, then [k] *)
with tr_mem (fuel : nat) (Γ : list ent) (t : term) (s : st) (k : K) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tRel n => match nth_error Γ n with
              | Some (EMem v) => if Nat.eqb v (s_ver s) then k s else TErr "a memory used after it was handed on"
              | _ => TErr "not a memory"
              end
  | tLetIn na b ty body => tr_let fuel Γ b ty s (fun Γ' s => tr_mem fuel Γ' body s k)
  | tCase ci p c [b0; b1] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        tr_cond fuel Γ c s (fun s => tr_mem fuel Γ (bbody b0) s k) (fun s => tr_mem fuel Γ (bbody b1) s k)
      else TErr "a match used as a memory that this translator does not read"
  | tCase ci p c [b] => tr_rec_case fuel Γ ci p c s (fun Γ' s => tr_mem fuel Γ' (bbody b) s k)
  | tApp (tConst kn _) args =>
      if Kername.eqb kn kn_upd then
        match args with
        | [h; i; v; m] =>
            tr_int fuel Γ h s (fun H s => tr_int fuel Γ i s (fun I s => tr_int fuel Γ v s (fun V s =>
              tr_mem fuel Γ m s (fun s => wrap1 q_Ekst [H; I; V] (k (bump s))))))
        | _ => TErr "upd"
        end
      else if Kername.eqb kn kn_upd32 then
        match args with
        | [h; i; v; m] =>
            tr_int fuel Γ h s (fun H s => tr_int fuel Γ i s (fun I s => tr_int fuel Γ v s (fun V s =>
              tr_mem fuel Γ m s (fun s => wrap1 q_Ekst32 [H; I; V] (k (bump s))))))
        | _ => TErr "upd32"
        end
      else match hw_lookup kn with
      | Some (op, n) =>
          if Nat.eqb (length args) (S n) then
            tr_ints fuel Γ (firstn n args) s (fun As s =>
              tr_mem fuel Γ (nth n args (tRel 0)) s (fun s =>
                wrap1 q_Ehw [op; qlist q_atom As] (k (bump s))))
          else TErr "a machine operation with the wrong number of arguments"
      | None =>
      match find_fn kn with
      | Some f =>
          if fi_rmem f then
            tr_call fuel Γ f args s (fun As s =>
              let '(x, s) := fresh (bump s) in
              wrap1 q_Ecall [qpos x; qpos (fi_id f); As] (k s))
          else TErr "a number used as a memory"
      | None => match helper_body kn with
                | Some b => tr_mem fuel Γ (beta_lets b args) s k
                | None => TErr ("not readable: " ^ snd kn)
                end
      end
      end
  | tApp (tRel n) args =>
      match nth_error Γ n with
      | Some ESelf =>
          if fi_rmem self then
            tr_call fuel Γ self args s (fun As s =>
              let '(x, s) := fresh (bump s) in
              wrap1 q_Ecall [qpos x; qpos (fi_id self); As] (k s))
          else TErr "a number used as a memory"
      | _ => TErr "a call of a variable"
      end
  | _ => TErr "not a memory this translator reads"
  end
  end

(* a test: the comparison, or && || negb of tests; [kT] and [kF] are the rest of the body after each outcome *)
with tr_cond (fuel : nat) (Γ : list ent) (t : term) (s : st) (kT kF : K) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tConstruct i 0 _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then kT s else TErr "a constructor"
  | tConstruct i 1 _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then kF s else TErr "a constructor"
  | tApp (tConst kn _) args =>
      if eq_mp (fst kn) prim_mp then
        match cmp_of (snd kn), args with
        | Some c, [a; b] =>
            tr_int fuel Γ a s (fun A s => tr_int fuel Γ b s (fun B s =>
              let v0 := s_ver s in
              match kT s with
              | TOk (et, s1) =>
                  match kF (with_ver v0 s1) with
                  | TOk (ef, s2) => TOk (tApp q_Eif [c; A; B; et; ef], s2)
                  | TErr m => TErr m
                  end
              | TErr m => TErr m
              end))
        | _, _ => TErr ("a test this translator does not read: " ^ snd kn)
        end
      else if Kername.eqb kn kn_andb then
        match args with
        | [c1; c2] => tr_cond fuel Γ c1 s (fun s => tr_cond fuel Γ c2 s kT kF) kF
        | _ => TErr "andb"
        end
      else if Kername.eqb kn kn_orb then
        match args with
        | [c1; c2] => tr_cond fuel Γ c1 s kT (fun s => tr_cond fuel Γ c2 s kT kF)
        | _ => TErr "orb"
        end
      else if Kername.eqb kn kn_negb then
        match args with
        | [c1] => tr_cond fuel Γ c1 s kF kT
        | _ => TErr "negb"
        end
      else match helper_body kn with
           | Some b => tr_cond fuel Γ (beta_lets b args) s kT kF
           | None => TErr ("not a test: " ^ snd kn)
           end
  | tConst kn _ =>
      match helper_body kn with
      | Some b => tr_cond fuel Γ b s kT kF
      | None => TErr ("not a test: " ^ snd kn)
      end
  | tLetIn na b ty body => tr_let fuel Γ b ty s (fun Γ' s => tr_cond fuel Γ' body s kT kF)
  | tCase ci p c [b] => tr_rec_case fuel Γ ci p c s (fun Γ' s => tr_cond fuel Γ' (bbody b) s kT kF)
  | tRel n =>
      match nth_error Γ n with
      | Some (EBool a) =>
          let v0 := s_ver s in
          match kT s with
          | TOk (et, s1) =>
              match kF (with_ver v0 s1) with
              | TOk (ef, s2) => TOk (tApp q_Eif [<% Ceq %>; a; aint q_zero; ef; et], s2)
              | TErr m => TErr m
              end
          | TErr m => TErr m
          end
      | Some (ECmp c A B) =>
          let v0 := s_ver s in
          match kT s with
          | TOk (et, s1) =>
              match kF (with_ver v0 s1) with
              | TOk (ef, s2) => TOk (tApp q_Eif [c; A; B; et; ef], s2)
              | TErr m => TErr m
              end
          | TErr m => TErr m
          end
      | _ => TErr "a variable used as a test is not a boolean"
      end
  | _ => TErr "not a test this translator reads"
  end
  end

(* a [let]: the bound term is a number, a memory or a boolean *)
with tr_let (fuel : nat) (Γ : list ent) (b ty : term) (s : st) (kk : list ent -> st -> tres (term * st)) {struct fuel}
  : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match kind_of 20 Σ ty with
  | Some (KRec mk ks) => tr_recv fuel Γ mk ks b s (fun e s => kk (e :: Γ) s)
  | _ =>
  match ty with
  | tConst kn _ =>
      if Kername.eqb kn kn_kmem then tr_mem fuel Γ b s (fun s => kk (EMem (s_ver s) :: Γ) s)
      else tr_int fuel Γ b s (fun a s => kk (EInt a :: Γ) s)
  | tInd i _ =>
      if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then
        match b with
        | tRel n =>
            (* a name for a boolean that is already known keeps what it stands for *)
            match nth_error Γ n with
            | Some (ECmp c CA CB) => kk (ECmp c CA CB :: Γ) s
            | Some (EBool a) => kk (EBool a :: Γ) s
            | _ => TErr "a variable used as a boolean is not one"
            end
        | tApp (tConst kn _) [ca; cb] =>
            match (if eq_mp (fst kn) prim_mp then cmp_of (snd kn) else None) with
            | Some c =>
                tr_int fuel Γ ca s (fun CA s => tr_int fuel Γ cb s (fun CB s => kk (ECmp c CA CB :: Γ) s))
            | None => tr_boolval fuel Γ b s (fun a s => kk (EBool a :: Γ) s)
            end
        | _ => tr_boolval fuel Γ b s (fun a s => kk (EBool a :: Γ) s)
        end
      else if Kername.eqb (inductive_mind i) (inductive_mind ind_nat) then
        tr_nat fuel Γ b s (fun a s => kk (ENat a :: Γ) s)
      else TErr "a let of a type this translator does not read"
  | _ => TErr "a let of a type this translator does not read"
  end
  end
  end

(* a list of numbers, worked out in order *)
with tr_ints (fuel : nat) (Γ : list ent) (ts : list term) (s : st)
             (kk : list term -> st -> tres (term * st)) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match ts with
  | [] => kk [] s
  | t :: ts => tr_int fuel Γ t s (fun A s => tr_ints fuel Γ ts s (fun As s => kk (A :: As) s))
  end
  end

(* a record or pair as the list of its fields: a variable that is one, a constructor with its fields worked out, a
   helper that gives one, a [match] or [let] that ends in one *)
with tr_recv (fuel : nat) (Γ : list ent) (mk : term) (ks : list kind) (t : term) (s : st)
             (kk : ent -> st -> tres (term * st)) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tRel n => match nth_error Γ n with
              | Some (ERec es) => kk (ERec es) s
              | _ => TErr "a variable used as a record is not one"
              end
  | tLetIn na b ty body => tr_let fuel Γ b ty s (fun Γ' s => tr_recv fuel Γ' mk ks body s kk)
  | tConstruct _ 0 _ => if Nat.eqb (length ks) 0 then kk (ERec []) s else TErr "a record constructor without its fields"
  | tApp (tConstruct _ 0 _) args =>
      let fields := skipn (mk_npar mk) args in
      if Nat.eqb (length fields) (length ks) then
        tr_vals fuel Γ ks fields s (fun es s => kk (ERec es) s)
      else TErr "a record constructor with the wrong number of fields"
  | tCase ci p c [b] => tr_rec_case fuel Γ ci p c s (fun Γ' s => tr_recv fuel Γ' mk ks (bbody b) s kk)
  | tApp (tConst kn _) args =>
      if (Kername.eqb kn kn_fst || Kername.eqb kn kn_snd) then
        match args with
        | [ta; tb; c] => tr_field fuel Γ (tApp (tInd ind_prod []) [ta; tb]) (if Kername.eqb kn kn_fst then 0 else 1) c s kk
        | _ => TErr "fst or snd"
        end
      else match find_fn kn with
      | Some _ => TErr "a function giving back a record: not read yet"
      | None => match helper_body kn with
                | Some b => tr_recv fuel Γ mk ks (beta_lets b args) s kk
                | None => TErr ("not readable: " ^ snd kn)
                end
      end
  | tConst kn _ =>
      match helper_body kn with
      | Some b => tr_recv fuel Γ mk ks b s kk
      | None => TErr ("not readable: " ^ snd kn)
      end
  | tProj pr c => tr_field fuel Γ (tInd (proj_ind pr) []) (proj_arg pr) c s kk
  | _ => TErr "not a record this translator reads"
  end
  end

with tr_vals (fuel : nat) (Γ : list ent) (ks : list kind) (ts : list term) (s : st)
             (kk : list ent -> st -> tres (term * st)) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match ks, ts with
  | [], [] => kk [] s
  | k :: ks, t :: ts =>
      tr_val fuel Γ k t s (fun e s => tr_vals fuel Γ ks ts s (fun es s => kk (e :: es) s))
  | _, _ => TErr "the fields of a record"
  end
  end

with tr_val (fuel : nat) (Γ : list ent) (k : kind) (t : term) (s : st)
            (kk : ent -> st -> tres (term * st)) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match k with
  | KInt => tr_int fuel Γ t s (fun a s => kk (EInt a) s)
  | KNat => tr_nat fuel Γ t s (fun a s => kk (ENat a) s)
  | KRec mk ks => tr_recv fuel Γ mk ks t s kk
  | KMem => TErr "a memory inside a record"
  end
  end

(* field [idx] of a record of type [ty] *)
with tr_field (fuel : nat) (Γ : list ent) (ty : term) (idx : nat) (c : term) (s : st)
              (kk : ent -> st -> tres (term * st)) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match kind_of 20 Σ ty with
  | Some (KRec mk ks) =>
      tr_recv fuel Γ mk ks c s (fun e s =>
        match e with
        | ERec es => match nth_error es idx with Some e1 => kk e1 s | None => TErr "no such field" end
        | _ => TErr "not a record"
        end)
  | _ => TErr "a projection of what is not a record of numbers"
  end
  end

(* [match c with mk x y => body end] on a record: the body is read with its fields as variables.  [kk] gets the
   context of the body. *)
with tr_rec_case (fuel : nat) (Γ : list ent) (ci : case_info) (p : predicate term) (c : term) (s : st)
                 (kk : list ent -> st -> tres (term * st)) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match kind_of 20 Σ (mkApps (tInd (ci_ind ci) (puinst p)) (pparams p)) with
  | Some (KRec mk ks) =>
      tr_recv fuel Γ mk ks c s (fun e s =>
        match e with
        | ERec es => kk (List.app (rev es) Γ) s
        | _ => TErr "not a record"
        end)
  | _ => TErr "a match this translator does not read"
  end
  end

(* a boolean as a number: 1 for true, 0 for false, worked out without a jump *)
with tr_boolval (fuel : nat) (Γ : list ent) (t : term) (s : st) (k : KA) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tConstruct i 0 _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then k (aint q_one) s else TErr "a constructor"
  | tConstruct i 1 _ => if Kername.eqb (inductive_mind i) (inductive_mind ind_bool) then k (aint q_zero) s else TErr "a constructor"
  | tRel n =>
      match nth_error Γ n with
      | Some (EBool a) => k a s
      | Some (ECmp c A B) =>
          let '(x, s) := fresh s in
          wrap1 q_Esel [qpos x; c; A; B; aint q_one; aint q_zero] (k (avar x) s)
      | _ => TErr "a variable used as a boolean is not one"
      end
  | tApp (tConst kn _) args =>
      if eq_mp (fst kn) prim_mp then
        match cmp_of (snd kn), args with
        | Some c, [a; b] =>
            tr_int fuel Γ a s (fun A s => tr_int fuel Γ b s (fun B s =>
              let '(x, s) := fresh s in
              wrap1 q_Esel [qpos x; c; A; B; aint q_one; aint q_zero] (k (avar x) s)))
        | _, _ => TErr ("a test this translator does not read: " ^ snd kn)
        end
      else if Kername.eqb kn kn_andb then
        match args with
        | [c1; c2] =>
            tr_boolval fuel Γ c1 s (fun A s => tr_boolval fuel Γ c2 s (fun B s =>
              let '(x, s) := fresh s in
              wrap1 q_Eop [qpos x; <% Bland %>; A; B] (k (avar x) s)))
        | _ => TErr "andb"
        end
      else if Kername.eqb kn kn_orb then
        match args with
        | [c1; c2] =>
            tr_boolval fuel Γ c1 s (fun A s => tr_boolval fuel Γ c2 s (fun B s =>
              let '(x, s) := fresh s in
              wrap1 q_Eop [qpos x; <% Blor %>; A; B] (k (avar x) s)))
        | _ => TErr "orb"
        end
      else if Kername.eqb kn kn_negb then
        match args with
        | [c1] =>
            tr_boolval fuel Γ c1 s (fun A s =>
              let '(x, s) := fresh s in
              wrap1 q_Eop [qpos x; <% Blxor %>; A; aint q_one] (k (avar x) s))
        | _ => TErr "negb"
        end
      else match helper_body kn with
           | Some b => tr_boolval fuel Γ (beta_lets b args) s k
           | None => TErr ("not a boolean: " ^ snd kn)
           end
  | tConst kn _ =>
      match helper_body kn with
      | Some b => tr_boolval fuel Γ b s k
      | None => TErr ("not a boolean: " ^ snd kn)
      end
  | tLetIn na b ty body => tr_let fuel Γ b ty s (fun Γ' s => tr_boolval fuel Γ' body s k)
  | tCase ci p c [b] => tr_rec_case fuel Γ ci p c s (fun Γ' s => tr_boolval fuel Γ' (bbody b) s k)
  | _ => TErr "not a boolean this translator reads"
  end
  end.

(* the body in tail position *)
Fixpoint tr_tail (fuel : nat) (Γ : list ent) (t : term) (s : st) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match t with
  | tCase ci p c [b0; b1] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel n =>
            match nth_error Γ n with
            | Some (ENat a) =>
                let v0 := s_ver s in
                match tr_tail fuel Γ (bbody b0) s with
                | TOk (e0, s1) =>
                    let '(x, s1) := fresh (with_ver v0 s1) in
                    match tr_tail fuel (ENat (avar x) :: Γ) (bbody b1) s1 with
                    | TOk (e1, s2) =>
                        TOk (tApp q_Eif [<% Ceq %>; a; aint q_zero; e0;
                                         tApp q_Eop [qpos x; <% Bsub %>; a; aint q_one; e1]], s2)
                    | TErr m => TErr m
                    end
                | TErr m => TErr m
                end
            | _ => TErr "a match on what is not a counter parameter"
            end
        | _ => TErr "a match on what is not a counter parameter"
        end
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        let plain := tr_cond fuel Γ c s (fun s => tr_tail fuel Γ (bbody b0) s) (fun s => tr_tail fuel Γ (bbody b1) s) in
        match merge_ifs Γ t with
        | Some t' => match tr_tail fuel Γ t' s with TOk r => TOk r | TErr _ => plain end
        | None => plain
        end
      else TErr "a match this translator does not read"
  | tLetIn na b ty body => tr_let fuel Γ b ty s (fun Γ' s => tr_tail fuel Γ' body s)
  | tCase ci p c [b] => tr_rec_case fuel Γ ci p c s (fun Γ' s => tr_tail fuel Γ' (bbody b) s)
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
Fixpoint lams (t : term) : list term * term :=
  match t with tLambda _ ty b => let '(l, r) := lams b in (ty :: l, r) | _ => ([], t) end.

Fixpoint prods_res (t : term) : term := match t with tProd _ _ b => prods_res b | _ => t end.

Definition result_mem (Σ : global_env) (ty : term) : option bool :=
  match kind_of 20 Σ (prods_res ty) with Some KInt => Some false | Some KMem => Some true | _ => None end.

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

(* a constant of the file is a function to translate when it calls itself or is the root *)
(* the size of a term, to tell a large helper from a small one *)
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

(* A definition that does not call itself is written out where it is used -- unless it is large, and its parameters and
   result are of kinds a function can have: then it is a function of its own (as a compiler does not inline a large
   function), proved once and called.  Writing out every helper into one body makes the proof of the caller as large
   as the whole program. *)
Definition inline_limit : nat := 40.
Definition big_fun (Σ : global_env) (kn : kername) : bool :=
  match body_of Σ kn with
  | Some (ty, b) =>
      match fparts b, result_mem Σ ty with
      | Some (false, tys, _), Some _ =>
          match opt_all (map (kind_of 20 Σ) tys) with
          | Some _ => Nat.ltb inline_limit (term_size 100000 b)
          | None => false
          end
      | _, _ => false
      end
  | None => false
  end.

Definition is_fun (Σ : global_env) (mp : modpath) (root kn : kername) : bool :=
  Kername.eqb kn root ||
  (eq_mp (fst kn) mp &&
   (match body_of Σ kn with Some (_, tFix _ _) => true | _ => false end || big_fun Σ kn)).

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
                             else if eq_mp (fst c) mp || eq_mp (fst c) kit_mp then reach fuel Σ mp root c d else d) cs done in
               if is_fun Σ mp root kn then List.app done [kn] else done
           | None => done
           end
  end.

(* does the body write the memory, directly or through a function that does *)
Fixpoint writes (fuel : nat) (fns : list finfo) (t : term) : bool :=
  match fuel with
  | O => true
  | S fuel =>
      match t with
      | tConst kn _ => Kername.eqb kn kn_upd || Kername.eqb kn kn_upd32 || (match hw_lookup kn with Some _ => true | None => false end) ||
                       match List.find (fun f => Kername.eqb (fi_kn f) kn) fns with Some f => fi_wr f | None => false end
      | tApp f args => writes fuel fns f || existsb (writes fuel fns) args
      | tLambda _ _ b => writes fuel fns b
      | tLetIn _ b _ body => writes fuel fns b || writes fuel fns body
      | tCase _ _ c brs => writes fuel fns c || existsb (fun br => writes fuel fns (bbody br)) brs
      | tFix mfix _ => existsb (fun d => writes fuel fns (dbody d)) mfix
      | _ => false
      end
  end.

Definition mk_info (Σ : global_env) (fns : list finfo) (i : nat) (kn : kername) : option finfo :=
  match body_of Σ kn with
  | Some (ty, b) =>
      match fparts b, result_mem Σ ty with
      | Some (isrec, tys, body), Some rm =>
          option_map (fun ks => mkFI kn (Pos.of_nat (1000 + i)) ks rm isrec (writes 10000 fns body))
                     (opt_all (map (kind_of 20 Σ) tys))
      | _, _ => None
      end
  | None => None
  end.

Fixpoint build_infos (Σ : global_env) (kns : list kername) (i : nat) (acc : list finfo) : option (list finfo) :=
  match kns with
  | [] => Some acc
  | kn :: kns =>
      match mk_info Σ acc i kn with
      | Some f => build_infos Σ kns (S i) (List.app acc [f])
      | None => None
      end
  end.

(* translate one function; its parameters are KQL variables 1 .. n *)
Definition tr_fun (Σ : global_env) (mp : modpath) (fns : list finfo) (f : finfo) : tres term :=
  match body_of Σ (fi_kn f) with
  | Some (_, b) =>
      match fparts b with
      | Some (_, _, body) =>
          let ks := fi_kinds f in
          let n := length (flat_map (leaves 20) ks) + (if existsb is_mem_kind ks then 1 else 0) in
          let pids := map (fun i => Pos.of_nat (S i)) (seq 0 n) in
          (* the entries of the parameters in order, taking their KQL variables from [ids] *)
          let fix ents_of (ks : list kind) (ids : list positive) : list ent * list positive :=
            match ks with
            | [] => ([], ids)
            | k :: ks =>
                let '(e, ids1) :=
                  (fix one (fuel : nat) (k : kind) (ids : list positive) : ent * list positive :=
                     match fuel with
                     | O => (EMem 0, ids)
                     | S fuel =>
                         match k, ids with
                         | KNat, i :: r => (ENat (avar i), r)
                         | KInt, i :: r => (EInt (avar i), r)
                         | KMem, i :: r => (EMem 0, r)
                         | KRec _ ks', _ =>
                             let '(es, r) := (fix many (l : list kind) (ids : list positive) : list ent * list positive :=
                                                match l with
                                                | [] => ([], ids)
                                                | k' :: l' => let '(e', r1) := one fuel k' ids in
                                                              let '(es', r2) := many l' r1 in (e' :: es', r2)
                                                end) ks' ids in
                             (ERec es, r)
                         | _, [] => (EMem 0, [])
                         end
                     end) 20 k ids in
                let '(es, ids2) := ents_of ks ids1 in
                (e :: es, ids2)
            end in
          let ents := fst (ents_of ks pids) in
          let Γ := List.app (rev ents) (if fi_rec f then [ESelf] else []) in
          let kpids := firstn (length (flat_map (leaves 20) ks)) pids in
          match tr_tail Σ mp fns f 2000 Γ body (mkSt (Pos.of_nat (S n)) 0) with
          | TOk (e, _) => TOk (tApp q_mkfn [qlist q_ident (map qpos kpids); e])
          | TErr m => TErr (snd (fi_kn f) ^ ": " ^ m)
          end
      | None => TErr (snd (fi_kn f) ^ ": not a function this translator reads")
      end
  | None => TErr "no body"
  end.

(* ------------------------------------------------------------------ the statement of a function *)
(* forall x1 .. xn M, Z.of_nat (sum of the counters) < wB -> run ..; the result and the memory it ends with:
     gives a memory:        runk P f args M 0 (g xs M)
     gives a number, reads: runk P f args M (g xs M) M
     gives a number, writes: exists M', runk P f args M (g xs M) M'  *)
(* the argument for a parameter of kind [k] in the statement: a record is its constructor applied to its leaves *)
Fixpoint stmt_arg (fuel : nat) (var : nat -> term) (k : kind) (j : nat) : term * nat :=
  match fuel with
  | O => (q_zero, j)
  | S fuel =>
      match k with
      | KRec mk ks =>
          let '(ts, j') := (fix many (l : list kind) (j : nat) : list term * nat :=
                              match l with
                              | [] => ([], j)
                              | k' :: l' => let '(t, j1) := stmt_arg fuel var k' j in
                                            let '(ts, j2) := many l' j1 in (t :: ts, j2)
                              end) ks j in
          (mkApps mk ts, j')
      | KMem => (q_zero, j)
      | _ => (var j, S j)
      end
  end.

Definition stmt (prog : term) (f : finfo) : term :=
  let ks := fi_kinds f in
  let hasM := existsb (fun k => match k with KMem => true | _ => false end) ks in
  let vks := flat_map (leaves 20) ks in
  let n := length vks in
  let nb := S n in
  let var i d := tRel (d + nb - 1 - i) in           (* parameter i, under d more binders *)
  let mvar d := tRel d in
  let nats := map fst (filter (fun ik => match snd ik with KNat => true | _ => false end)
                               (combine (seq 0 n) vks)) in
  (* the bound of a counter is lower for a function later in the file, so that a caller's counter plus a few is still
     inside the bound of the callee *)
  let cbf := tApp q_cbk [natq (Nat.sub (Pos.to_nat (fi_id f)) 1000)] in
  let bnd d := match nats with
               | [] => tApp q_Zlt [tApp q_Zofnat [<% 0 %>]; cbf]
               | i :: l => fold_left (fun acc j => tApp q_and [acc; tApp q_Zlt [tApp q_Zofnat [var j d]; cbf]])
                                     l (tApp q_Zlt [tApp q_Zofnat [var i d]; cbf])
               end in
  let arg i k d := match k with KNat => tApp q_ofn [var i d] | _ => var i d end in
  let args d := qlist q_i63 (map (fun ik => arg (fst ik) (snd ik) d) (combine (seq 0 n) vks)) in
  let fargs d := fst (fold_left (fun acc k => if is_mem_kind k then acc
                                            else let '(ts, j) := acc in
                                                 let '(t, j') := stmt_arg 20 (fun i => var i d) k j in (List.app ts [t], j'))
                               ks ([], 0)) in
  let fapp d := mkApps (tConst (fi_kn f) []) (List.app (fargs d) (if hasM then [mvar d] else [])) in
  let body d :=
    if fi_rmem f then tApp q_runk [prog; qpos (fi_id f); args d; mvar d; q_zero; fapp d]
    else if andb hasM (fi_wr f) then tApp q_runx [prog; qpos (fi_id f); args d; mvar d; fapp d]
    else tApp q_runk [prog; qpos (fi_id f); args d; mvar d; fapp d; mvar d] in
  let core := tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                (bnd 0) (body 1) in
  let withM := tProd {| binder_name := nNamed "M"; binder_relevance := Relevant |} q_kmem core in
  fold_right (fun ik acc =>
                tProd {| binder_name := nNamed ("x" ^ string_of_nat (fst ik)); binder_relevance := Relevant |}
                      (match snd ik with KNat => <% nat %> | _ => q_i63 end) acc)
             withM (combine (seq 0 n) vks).

(* ------------------------------------------------------------------ the whole program *)
Inductive kdef := KDef (id : ident) (ty body : term).
Record tout := mkOut { o_defs : list kdef; o_msg : string }.

(* the helpers (non-recursive definitions of the file or of the kit) that the bodies use, and that are written out *)
Fixpoint helpers_of (fuel : nat) (Σ : global_env) (mp : modpath) (fns : list finfo) (todo acc : list kername) : list kername :=
  match fuel with
  | O => acc
  | S fuel =>
      match todo with
      | [] => acc
      | kn :: todo =>
          if existsb (Kername.eqb kn) acc then helpers_of fuel Σ mp fns todo acc
          else match helper_body Σ mp fns kn with
               | Some b => helpers_of fuel Σ mp fns (List.app (consts 10000 b []) todo) (kn :: acc)
               | None => helpers_of fuel Σ mp fns todo acc
               end
      end
  end.

Definition help_name (kn : kername) : string :=
  if eq_mp (fst kn) uint63_mp then "Uint63." ^ snd kn else snd kn.

Definition last_error {A} (l : list A) : option A := match rev l with [] => None | x :: _ => Some x end.

Definition kqm_gen (p : program) (prog_name : ident) : tout :=
  let '(Σ, t) := p in
  match t with
  | tConst root _ =>
      let mp := fst root in
      let kns := reach 1000 Σ mp root root [] in
      match build_infos Σ kns 0 [] with
      | Some fns =>
          let fix go (fs : list finfo) (acc : list (finfo * term)) :=
            match fs with
            | [] => TOk (rev acc)
            | f :: fs => match tr_fun Σ mp fns f with
                         | TOk e => go fs ((f, e) :: acc)
                         | TErr m => TErr m
                         end
            end in
          match go fns [] with
          | TOk tfs =>
              let pkn : kername := (mp, prog_name) in
              let fdefs := map (fun fe => KDef (snd (fi_kn (fst fe)) ^ "_kqm") q_fn (snd fe)) tfs in
              let pfuns := qlist (tApp q_prod [q_ident; q_fn])
                             (map (fun fe => tApp q_pair [q_ident; q_fn; qpos (fi_id (fst fe));
                                                          tConst (mp, snd (fi_kn (fst fe)) ^ "_kqm") []]) tfs) in
              let parrs := tApp q_nil [tApp q_prod [q_ident; q_Z]] in
              let pdef := KDef prog_name <% prog %> (tApp q_mkprog [pfuns; parrs]) in
              let sdefs := map (fun fe => KDef (snd (fi_kn (fst fe)) ^ "_kstmt") <% Prop %> (stmt (tConst pkn []) (fst fe))) tfs in
              let used := fold_left (fun acc fe => match body_of Σ (fi_kn (fst fe)) with
                                                   | Some (_, b) => List.app (consts 10000 b []) acc
                                                   | None => acc end) tfs [] in
              let hs := filter (fun kn => negb (Kername.eqb kn kn_kq_nat)) (helpers_of 10000 Σ mp fns used []) in
              mkOut (List.app fdefs (pdef :: sdefs))
                    ("KQM: " ^ string_of_nat (length tfs) ^ " functions: " ^
                     String.concat " " (map (fun fe => snd (fi_kn (fst fe))) tfs) ^
                     "
KQM helpers: " ^ String.concat " " (map help_name hs) ^
                     "
KQM entry: " ^ (match last_error tfs with
                      | Some fe => let f := fst fe in
                                   snd (fi_kn f) ^ " " ^ string_of_nat (Pos.to_nat (fi_id f)) ^ " " ^
                                   String.concat "" (map (fun k => match k with KNat => "N" | KInt => "I" | KMem => "M" | KRec _ _ => "R" end) (fi_kinds f)) ^
                                   " " ^ (if fi_rmem f then "M" else "I")
                      | None => ""
                      end))
          | TErr m => mkOut [] ("KQM: refused: " ^ m)
          end
      | None => mkOut [] "KQM: refused: a function's parameters or result are not of a kind this translator reads"
      end
  | _ => mkOut [] "KQM: give it the name of a definition"
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

Definition kqm_define (o : tout) : TemplateMonad unit :=
  match o_defs o with
  | [] => tmFail (o_msg o)
  | l => define_all l ;; tmMsg (o_msg o)
  end.

Notation kqm_translate x name :=
  (kqm_define ltac:(run_template_program (tmQuoteRec x) (fun q => let t := eval vm_compute in (kqm_gen q name) in exact t)))
  (only parsing).

(* ------------------------------------------------------------------ the proof of a statement *)
Ltac kqm_auto :=
  hnf;
  (* a function that writes the memory and gives a number is stated with [runx]; the other proofs do not apply to
     it and, tried first, can run a long time before they fail *)
  lazymatch goal with
  | |- context [runx _ _ _ _ _] => first [ solve [ kqx_prove ] | solve [ kqx_prove0 ] ]
  | _ => first [ solve [ kqm_prove ] | solve [ kqm_prove0 ] ]
  end.
