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
Require KQ.KQRun KQ.hw.Runtime KQ.hw.User.
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
Definition kn_rd8 := kn_of <% KQ.KQRun.rd8 %>.
Definition kn_upd8 := kn_of <% KQ.KQRun.upd8 %>.
Definition kn_ksize := kn_of <% KQ.KQRun.kq_size %>.
Definition kn_w64_op := kn_of <% KQ.KQRun.w64_op %>.
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
  ; (kn_of <% KQ.hw.Runtime.hw_irq_take %>, <% HIrqTake %>, 2)
  ; (kn_of <% KQ.hw.User.hw_user %>, <% HUser %>, 5)
  ; (kn_of <% KQ.KQRun.kq_grow %>, <% HGrow %>, 2) ].
Definition hw_lookup (kn : kername) : option (term * nat) :=
  match List.find (fun e => Kername.eqb (fst (fst e)) kn) hw_table with
  | Some e => Some (snd (fst e), snd e)
  | None => None
  end.
Definition q_Ehw := <% Ehw %>.
Definition q_Ehwf := <% Ehwf %>.
(* the machine's numbers: the Rocq constant and the KQL operation *)
Definition hwf_table : list (kername * term * nat) :=
  [ (kn_of <% KQ.KQRun.hw_addr %>, <% FAddr %>, 1)
  ; (kn_of <% KQ.hw.Runtime.hw_irq_info %>, <% FIrqInfo %>, 1)
  ; (kn_of <% KQ.hw.Runtime.hw_irq_entry %>, <% FIrqEntry %>, 1)
  ; (kn_of <% KQ.hw.Runtime.hw_cpu_code %>, <% FCpuCode %>, 1)
  ; (kn_of <% KQ.hw.Runtime.hw_sym %>, <% FSym %>, 1)
  ; (kn_of <% KQ.hw.User.hw_userf %>, <% FUser %>, 5) ].
Definition hwf_lookup (kn : kername) : option (term * nat) :=
  match List.find (fun e => Kername.eqb (fst (fst e)) kn) hwf_table with Some e => Some (snd (fst e), snd e) | None => None end.

Definition prim_mp : modpath := fst (kn_of <% PrimInt63.add %>).
Definition uint63_mp : modpath := fst (kn_of <% Uint63.opp %>).

(* KQL syntax, as terms *)
Definition q_Avar := <% Avar %>.
Definition q_Aint := <% Aint %>.
Definition q_Abud := <% Abud %>.
Definition q_Eret := <% Eret %>.
Definition q_Eop := <% Eop %>.
Definition q_Eif := <% Eif %>.
Definition q_Esel := <% Esel %>.
Definition q_Ecall := <% Ecall %>.
Definition q_Ekld := <% Ekld %>.
Definition q_Ekst := <% Ekst %>.
Definition q_Ekld32 := <% Ekld32 %>.
Definition q_Ekst32 := <% Ekst32 %>.
Definition q_Ekld8 := <% Ekld8 %>.
Definition q_Eksize := <% Eksize %>.
Definition q_Ekst8 := <% Ekst8 %>.
Definition q_Ew64 := <% Ew64 %>.
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
Definition q_ksize := <% KQ.KQRun.kq_size %>.
Definition q_klen := <% KQ.KQBound.kq_len %>.
Definition q_stoz := <% Sint63.to_Z %>.
Definition q_upd := <% KQ.KQRun.upd %>.
Definition q_Ekst_ := <% Ekst %>.
Definition qint (n : nat) : term := tInt (Uint63.of_Z (Z.of_nat n)).
(* the block that carries a function's second result (cell 0) back to its caller: the caller puts the cell back as it was *)
Definition slot_blk : nat := 63.
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
Definition q_cap60 : term := tInt (Uint63.of_Z 1152921504606846976%Z).

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
  fi_wr : bool;               (* it writes the memory (or calls a function that does) *)
  fi_rrec : option (term * list kind); (* it gives back a record of two numbers: the record's constructor and kinds *)
  fi_bi : nat;                (* the place whose counter bound it has: its own, or for a mutual group the first one's *)
  fi_name : string;           (* its name: that of the Rocq function, and for a copy made for the functions it was given, one more *)
  fi_fixed : list (nat * term); (* the parameters (by place) that are functions given when it is called, and those functions *)
  fi_capk : list kind;        (* the variables of the caller those functions name, as parameters of the copy, by kind: numbers and counters
                                 after the others, a memory last *)
  fi_nrest : nat;             (* the parameters that are not captured and not a memory *)
  fi_restmem : bool }.        (* the function's own parameter list ends in a memory *)

(* what a variable of the text stands for *)
Inductive ent :=
| ENat (a : term)       (* a counter, held in KQL as the atom [a] = ofn of it *)
| EInt (a : term)       (* a number, the atom [a] *)
| EBool (a : term)      (* a boolean, held as the atom [a]: 1 for true, 0 for false *)
| ECmp (c a b : term)   (* a boolean that is one comparison [a c b] of two atoms: kept as it is *)
| EMem (ver : nat)      (* a memory: the one the program has now when [ver] is the current version *)
| ERec (es : list ent)  (* a record or pair: its fields *)
| ESelf                 (* the function being read, calling itself *)
| ESib (kn : kername)    (* another function of the same mutual fixpoint *)
| EFun (f : term) (m : nat).   (* a parameter that is a function known where the function is called: that function, whose free
                                    variables are the [m] captured ones, 0 .. m-1 (the function's own variable k stands for the
                                    captured parameter k, which the copy holds at the bottom of its environment) *)

Record st := mkSt { s_next : positive; s_ver : nat }.

Definition K := st -> tres (term * st).
Definition KA := term -> st -> tres (term * st).

(* a local function (let g := fun x => .. in ..) is a macro: the body of the let has the function put in at each use, as a
   helper written out where it is used.  Its variables are those of the text around it, so a function that names a
   variable of the caller needs nothing more. *)
Definition is_fun_ty (ty : term) : bool := match ty with tProd _ _ _ => true | _ => false end.

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

(* beta-reduce a helper's body against its arguments, as [let]s; an argument that is a function (the parameter has an
   arrow type) is put in where the parameter stands, as a macro's argument is: a function known where it is used *)
Fixpoint beta_lets_go (fuel : nat) (b : term) (args : list term) : term :=
  match fuel with
  | O => mkApps b args
  | S fuel =>
      match b, args with
      | tLambda na ty body, a :: args =>
          match ty with
          | tProd _ _ _ => beta_lets_go fuel (subst [a] 0 body) args
          | _ => tLetIn na a ty (beta_lets_go fuel body (map (lift0 1) args))
          end
      | _, [] => b
      | _, _ => mkApps b args
      end
  end.
Definition beta_lets (b : term) (args : list term) : term := beta_lets_go (S (length args)) b args.

(* ---- a function given to a template that names variables of the caller (a closure): the variables are found, in order of
   first appearance, and the function is written with them as 0, 1, .. (the template's copy takes them as parameters) *)
Fixpoint idx_of (j : nat) (l : list nat) (k : nat) : option nat :=
  match l with [] => None | x :: r => if Nat.eqb x j then Some k else idx_of j r (S k) end.

(* [d] binders are crossed; [cl] lists the free variables found so far, as numbered outside the function *)
Fixpoint abs_free (fuel : nat) (d : nat) (t : term) (cl : list nat) {struct fuel} : term * list nat :=
  match fuel with
  | O => (t, cl)
  | S fuel =>
      let fix lst (ts : list term) (d : nat) (cl : list nat) {struct ts} : list term * list nat :=
          match ts with
          | [] => ([], cl)
          | t :: r => let '(t', cl) := abs_free fuel d t cl in
                      let '(r', cl) := lst r d cl in (t' :: r', cl)
          end in
      match t with
      | tRel i =>
          if Nat.ltb i d then (t, cl)
          else let j := Nat.sub i d in
               match idx_of j cl 0 with
               | Some k => (tRel (k + d), cl)
               | None => (tRel (length cl + d), List.app cl [j])
               end
      | tLambda na ty b =>
          let '(ty', cl) := abs_free fuel d ty cl in
          let '(b', cl) := abs_free fuel (S d) b cl in (tLambda na ty' b', cl)
      | tProd na ty b =>
          let '(ty', cl) := abs_free fuel d ty cl in
          let '(b', cl) := abs_free fuel (S d) b cl in (tProd na ty' b', cl)
      | tLetIn na b ty body =>
          let '(b', cl) := abs_free fuel d b cl in
          let '(ty', cl) := abs_free fuel d ty cl in
          let '(body', cl) := abs_free fuel (S d) body cl in (tLetIn na b' ty' body', cl)
      | tApp f args =>
          let '(f', cl) := abs_free fuel d f cl in
          let '(args', cl) := lst args d cl in (tApp f' args', cl)
      | tCase ci p c brs =>
          let '(ps, cl) := lst (pparams p) d cl in
          let '(pr, cl) := abs_free fuel (d + length (pcontext p)) (preturn p) cl in
          let '(c', cl) := abs_free fuel d c cl in
          let fix lb (bs : list (branch term)) (cl : list nat) {struct bs} : list (branch term) * list nat :=
              match bs with
              | [] => ([], cl)
              | br :: r =>
                  let '(b', cl) := abs_free fuel (d + length (bcontext br)) (bbody br) cl in
                  let '(r', cl) := lb r cl in ({| bcontext := bcontext br; bbody := b' |} :: r', cl)
              end in
          let '(brs', cl) := lb brs cl in
          (tCase ci {| pparams := ps; puinst := puinst p; pcontext := pcontext p; preturn := pr |} c' brs', cl)
      | tFix mfix k =>
          let n := length mfix in
          let fix lm (ms : list (def term)) (cl : list nat) {struct ms} : list (def term) * list nat :=
              match ms with
              | [] => ([], cl)
              | m :: r =>
                  let '(ty', cl) := abs_free fuel d (dtype m) cl in
                  let '(b', cl) := abs_free fuel (d + n) (dbody m) cl in
                  let '(r', cl) := lm r cl in
                  ({| dname := dname m; dtype := ty'; dbody := b'; rarg := rarg m |} :: r', cl)
              end in
          let '(ms', cl) := lm mfix cl in (tFix ms' k, cl)
      | tProj pr c => let '(c', cl) := abs_free fuel d c cl in (tProj pr c', cl)
      | _ => (t, cl)
      end
  end.

(* a function given by an entry: its terms stands in the environment it is used in, its captured variables being the entries
   at the bottom of it *)
Definition efun_term (Γ : list ent) (f : term) (m : nat) : term :=
  subst (map (fun k => tRel (Nat.sub (length Γ) (S k))) (seq 0 m)) 0 f.

(* an application whose head is an application or a lambda, as the head of a plain application: what putting a function
   in (above) leaves, [f (f x)] with [f] a function written in place *)
Fixpoint app_norm_go (fuel : nat) (Γ : list ent) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel =>
      match t with
      | tApp (tApp f a) b => app_norm_go fuel Γ (tApp f (List.app a b))
      | tApp (tLambda na ty body) (a :: rest) => app_norm_go fuel Γ (beta_lets (tLambda na ty body) (a :: rest))
      | tApp (tRel n) args =>
          match nth_error Γ n with
          | Some (EFun f m) => app_norm_go fuel Γ (mkApps (efun_term Γ f m) args)
          | _ => t
          end
      | _ => t
      end
  end.
Definition app_norm (Γ : list ent) (t : term) : term := app_norm_go 100 Γ t.

(* the same through the arguments of applications (not under binders): a number written with the functions given put in,
   [(fun k lo hi => hi - lo) key 0 12 + 1], is worked down to [12 - 0 + 1] *)
Definition ind_atom := ind_of <% atom %>.
Fixpoint deep_norm (fuel : nat) (Γ : list ent) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel =>
      match app_norm Γ t with
      | tRel n =>
          (* a variable that stands for a number written in the program *)
          match nth_error Γ n with
          | Some (EInt (tApp (tConstruct i 1 _) [v])) =>
              if Kername.eqb (inductive_mind i) (inductive_mind ind_atom) then v else tRel n
          | _ => tRel n
          end
      | tLetIn _ b _ body => deep_norm fuel Γ (subst [b] 0 body)
      | tApp f args => tApp (deep_norm fuel Γ f) (map (deep_norm fuel Γ) args)
      | t' => t'
      end
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
      | tLambda _ ty b, tLambda _ ty' b' => term_same fuel ty ty' && term_same fuel b b'
      | tProd _ ty b, tProd _ ty' b' => term_same fuel ty ty' && term_same fuel b b'
      | tInd i _, tInd i' _ => Kername.eqb (inductive_mind i) (inductive_mind i') && Nat.eqb (inductive_ind i) (inductive_ind i')
      | tConstruct i n _, tConstruct i' n' _ =>
          Kername.eqb (inductive_mind i) (inductive_mind i') && Nat.eqb (inductive_ind i) (inductive_ind i') && Nat.eqb n n'
      | tApp f xs, tApp g ys =>
          term_same fuel f g && Nat.eqb (length xs) (length ys)
          && forallb (fun p => term_same fuel (fst p) (snd p)) (combine xs ys)
      | tLetIn _ b ty body, tLetIn _ b' ty' body' =>
          term_same fuel b b' && term_same fuel ty ty' && term_same fuel body body'
      | tCase ci p c brs, tCase ci' p' c' brs' =>
          Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind (ci_ind ci')) && Nat.eqb (inductive_ind (ci_ind ci)) (inductive_ind (ci_ind ci'))
          && Nat.eqb (length (pparams p)) (length (pparams p'))
          && forallb (fun q => term_same fuel (fst q) (snd q)) (combine (pparams p) (pparams p'))
          && Nat.eqb (length (pcontext p)) (length (pcontext p'))
          && term_same fuel (preturn p) (preturn p') && term_same fuel c c'
          && Nat.eqb (length brs) (length brs')
          && forallb (fun q => Nat.eqb (length (bcontext (fst q))) (length (bcontext (snd q)))
                               && term_same fuel (bbody (fst q)) (bbody (snd q))) (combine brs brs')
      | tProj pr c, tProj pr' c' =>
          Kername.eqb (inductive_mind (proj_ind pr)) (inductive_mind (proj_ind pr')) && Nat.eqb (proj_arg pr) (proj_arg pr')
          && term_same fuel c c'
      | tFix m k, tFix m' k' =>
          Nat.eqb k k' && Nat.eqb (length m) (length m')
          && forallb (fun q => term_same fuel (dtype (fst q)) (dtype (snd q)) && term_same fuel (dbody (fst q)) (dbody (snd q))
                               && Nat.eqb (rarg (fst q)) (rarg (snd q))) (combine m m')
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
Variable shared : list PrimInt63.int.              (* the narrow blocks that another processor may change: only atomics reach them *)

(* a block number written in the program, and whether a plain access may use it *)
Definition plain_block_ok (h : term) : bool :=
  match shared with
  | [] => true
  | _ => match h with
         | tInt n => negb (existsb (fun b => Z.eqb (Uint63.to_Z b) (Uint63.to_Z n)) shared)
         | _ => false
         end
  end.
Definition shared_msg : string := "a block that another processor can change is read and written only through atomics (hw_aload, hw_astore, hw_atomic, hw_cas on its address), and its number must be written in the program where it is used".

Definition find_fn (kn : kername) : option finfo :=
  List.find (fun f => Kername.eqb (fi_kn f) kn) fns.

(* a call's argument that is a function parameter of the function being read stands for the function it was given *)
Definition res_arg (Γ : list ent) (a : term) : term :=
  match a with
  | tRel n => match nth_error Γ n with Some (EFun f m) => efun_term Γ f m | _ => a end
  | _ => a
  end.

(* the function a call is of: the one of that name, or for a function that takes functions, the copy made for the
   functions this call gives it *)
Definition find_fn_args (Γ : list ent) (kn : kername) (args : list term) : option (finfo * list term) :=
  let try (f : finfo) : option (finfo * list term) :=
    if Kername.eqb (fi_kn f) kn then
      let fix chk (fx : list (nat * term)) (cl : list nat) : option (list nat) :=
          match fx with
          | [] => Some cl
          | jt :: r =>
              match nth_error args (fst jt) with
              | Some a => let '(a', cl') := abs_free 1000 0 (res_arg Γ a) cl in
                          if term_same 10000 a' (snd jt) then chk r cl' else None
              | None => None
              end
          end in
      match chk (fi_fixed f) [] with
      | Some cl => if Nat.eqb (length cl) (length (fi_capk f)) then Some (f, map tRel cl) else None
      | None => None
      end
    else None in
  let fix find (l : list finfo) : option (finfo * list term) :=
      match l with [] => None | f :: r => match try f with Some x => Some x | None => find r end end in
  find fns.

(* the captured variables of a copy, as its own function reads them: the entries at the bottom of its environment *)
Definition cap_terms (Γ : list ent) (f : finfo) : list term :=
  map (fun k => tRel (Nat.sub (length Γ) (S k))) (seq 0 (length (fi_capk f))).

(* the arguments of a call of a copy, in the order of its kinds: the others that are numbers, the captured numbers, a memory *)
Definition call_args (f : finfo) (caps rest : list term) : list term :=
  let nm := filter (fun kt => negb (is_mem_kind (fst kt))) (combine (fi_capk f) caps) in
  let cm := filter (fun kt => is_mem_kind (fst kt)) (combine (fi_capk f) caps) in
  let restnm := if fi_restmem f then removelast rest else rest in
  let restm := if fi_restmem f then match rev rest with m :: _ => [m] | [] => [] end else [] in
  List.app restnm (List.app (map snd nm) (match restm with m :: _ => [m] | [] => map snd cm end)).

(* a helper: a definition of the file or of KQRun.v that does not call itself, written out where it is used *)
Definition helper_body (kn : kername) : option term :=
  if Kername.eqb kn kn_w64_op then None   (* a 64-bit operation is one instruction: its definition is its meaning, not a helper *)
  else if eq_mp (fst kn) mp || eq_mp (fst kn) kit_mp || eq_mp (fst kn) uint63_mp then
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

Fixpoint fresh_list (n : nat) (s : st) : list positive * st :=
  match n with
  | O => ([], s)
  | S n => let '(x, s) := fresh s in let '(xs, s) := fresh_list n s in (x :: xs, s)
  end.

(* the entry of a record of numbers from the atoms of its fields, in order *)
Definition rec_ent (ks : list kind) (atoms : list term) : ent :=
  ERec (map (fun a => EInt a) atoms).

(* the arguments of a call without those that are the functions the copy was made for *)
Fixpoint dropfix (j : nat) (fixed : list (nat * term)) (args : list term) : list term :=
  match args with
  | [] => []
  | a :: r => if existsb (fun jt => Nat.eqb (fst jt) j) fixed then dropfix (S j) fixed r else a :: dropfix (S j) fixed r
  end.

Fixpoint tr_int (fuel : nat) (Γ : list ent) (t : term) (s : st) (k : KA) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match app_norm Γ t with
  | tRel n => match nth_error Γ n with
              | Some (EInt a) => k a s
              | _ => TErr "a variable used as a number is not one"
              end
  | tInt _ => k (aint t) s
  | tLetIn na b ty body => if is_fun_ty ty then tr_int fuel Γ (subst [b] 0 body) s k else tr_let fuel Γ b ty s (fun Γ' s => tr_int fuel Γ' body s k)
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
        match hwf_lookup kn with
        | Some (op, n) =>
            if Nat.eqb (length args) n then
              tr_ints fuel Γ args s (fun As s =>
                let '(x, s) := fresh s in
                wrap1 q_Ehwf [op; qpos x; qlist q_atom As] (k (avar x) s))
            else TErr ("a machine number with the wrong number of arguments: " ^ snd kn)
        | None => TErr "machine number"
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
            if negb (plain_block_ok h) then TErr shared_msg else
            tr_int fuel Γ h s (fun H s => tr_int fuel Γ i s (fun I s => tr_mem fuel Γ m s (fun s =>
              let '(x, s) := fresh s in
              wrap1 q_Ekld32 [qpos x; H; I] (k (avar x) s))))
        | _ => TErr "rd32"
        end
      else if Kername.eqb kn kn_rd8 then
        match args with
        | [h; i; m] =>
            if negb (plain_block_ok h) then TErr shared_msg else
            tr_int fuel Γ h s (fun H s => tr_int fuel Γ i s (fun I s => tr_mem fuel Γ m s (fun s =>
              let '(x, s) := fresh s in
              wrap1 q_Ekld8 [qpos x; H; I] (k (avar x) s))))
        | _ => TErr "rd8"
        end
      else if Kername.eqb kn kn_ksize then
        match args with
        | [h; m] =>
            tr_int fuel Γ h s (fun H s => tr_mem fuel Γ m s (fun s =>
              let '(x, s) := fresh s in
              wrap1 q_Eksize [qpos x; H] (k (avar x) s)))
        | _ => TErr "kq_size"
        end
      else match find_fn_args Γ kn args with
      | Some (f, caps) =>
          if fi_rmem f then TErr "a function giving back a memory, used as a number"
          else tr_call fuel Γ f caps args s (fun As s =>
                 let s1 := if fi_wr f then bump s else s in
                 let '(x, s1) := fresh s1 in
                 wrap1 q_Ecall [qpos x; qpos (fi_id f); As] (k (avar x) s1))
      | None =>
          match helper_body kn with
          | Some b => tr_int fuel Γ (beta_lets b args) s k
          | None => TErr ("not readable: " ^ snd kn ^ " (if it takes a function, the function given must name no variable of the caller: pass the variable as an argument)")
          end
      end
  | tApp (tRel n) args =>
      match nth_error Γ n with
      | Some ESelf =>
          if fi_rmem self then TErr "a call of itself giving back a memory, used as a number"
          else tr_call fuel Γ self (cap_terms Γ self) args s (fun As s =>
                 let s1 := if fi_wr self then bump s else s in
                 let '(x, s1) := fresh s1 in
                 wrap1 q_Ecall [qpos x; qpos (fi_id self); As] (k (avar x) s1))
      | Some (ESib kn) =>
          match find_fn kn with
          | Some f =>
              if fi_rmem f then TErr "a call of a function giving back a memory, used as a number"
              else tr_call fuel Γ f (cap_terms Γ f) args s (fun As s =>
                     let s1 := if fi_wr f then bump s else s in
                     let '(x, s1) := fresh s1 in
                     wrap1 q_Ecall [qpos x; qpos (fi_id f); As] (k (avar x) s1))
          | None => TErr "a call of a function of the same fixpoint that is not translated"
          end
      | _ => TErr "a call of a variable"
      end
  | tConst kn _ =>
      match helper_body kn with
      | Some b => tr_int fuel Γ b s k
      | None => TErr ("not readable: " ^ snd kn ^ " (if it takes a function, the function given must name no variable of the caller: pass the variable as an argument)")
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
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        (* a match on a counter anywhere in the text: a test of it against 0, the second branch with the counter less one *)
        match c with
        | tRel n =>
            match nth_error Γ n with
            | Some (ENat a) =>
                let v0 := s_ver s in
                match tr_int fuel Γ (bbody b0) s k with
                | TOk (e0, s1) =>
                    let '(x, s1) := fresh (with_ver v0 s1) in
                    match tr_int fuel (ENat (avar x) :: Γ) (bbody b1) s1 (fun A s => k A s) with
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
  match app_norm Γ t with
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
      if Kername.eqb kn kn_kq_nat then k (tApp q_Abud [match t with tApp _ [n] => n | _ => t end]) s else TErr "not a counter this translator reads"
  | tApp (tConst kn _) [e] =>
      (* a budget worked out while the program runs: [kq_nat n] for a number n: n if positive, else 0.  A budget made of numbers
         written in the program only (a measure applied to its arguments) is a budget written as a number *)
      if andb (Kername.eqb kn kn_kq_nat) (closedn 0 (deep_norm 100 Γ e)) then
        k (tApp q_Abud [deep_norm 100 Γ e]) s
      else
      if Kername.eqb kn kn_kq_nat then
        tr_int fuel Γ e s (fun A s =>
          let '(x, s) := fresh s in
          wrap1 q_Esel [qpos x; <% Csle %>; A; aint q_zero; aint q_zero; A]
            (let '(y, s) := fresh s in
             wrap1 q_Esel [qpos y; <% Cslt %>; aint q_cap60; avar x; aint q_cap60; avar x] (k (avar y) s)))
      else TErr "not a counter this translator reads"
  | _ => if nat_lit 10000000 t then k (aint (tApp q_ofn [t])) s else TErr "not a counter this translator reads"
  end
  end

(* the arguments of a call: the numbers and counters first; a memory last, whose work is done after them *)
with tr_call (fuel : nat) (Γ : list ent) (f : finfo) (caps : list term) (args : list term) (s : st) (k : KA) {struct fuel}
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
  go (fi_kinds f) (call_args f caps (dropfix 0 (fi_fixed f) args)) [] s
  end

(* the work of a memory expression, then [k] *)
with tr_mem (fuel : nat) (Γ : list ent) (t : term) (s : st) (k : K) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match app_norm Γ t with
  | tRel n => match nth_error Γ n with
              | Some (EMem v) => if Nat.eqb v (s_ver s) then k s else TErr "a memory used after it was handed on"
              | _ => TErr "not a memory"
              end
  | tLetIn na b ty body => if is_fun_ty ty then tr_mem fuel Γ (subst [b] 0 body) s k else tr_let fuel Γ b ty s (fun Γ' s => tr_mem fuel Γ' body s k)
  | tCase ci p c [b0; b1] =>
      if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_bool) then
        tr_cond fuel Γ c s (fun s => tr_mem fuel Γ (bbody b0) s k) (fun s => tr_mem fuel Γ (bbody b1) s k)
      else if Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) then
        match c with
        | tRel n =>
            match nth_error Γ n with
            | Some (ENat a) =>
                let v0 := s_ver s in
                match tr_mem fuel Γ (bbody b0) s k with
                | TOk (e0, s1) =>
                    let '(x, s1) := fresh (with_ver v0 s1) in
                    match tr_mem fuel (ENat (avar x) :: Γ) (bbody b1) s1 k with
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
            if negb (plain_block_ok h) then TErr shared_msg else
            tr_int fuel Γ h s (fun H s => tr_int fuel Γ i s (fun I s => tr_int fuel Γ v s (fun V s =>
              tr_mem fuel Γ m s (fun s => wrap1 q_Ekst32 [H; I; V] (k (bump s))))))
        | _ => TErr "upd32"
        end
      else if Kername.eqb kn kn_upd8 then
        match args with
        | [h; i; v; m] =>
            if negb (plain_block_ok h) then TErr shared_msg else
            tr_int fuel Γ h s (fun H s => tr_int fuel Γ i s (fun I s => tr_int fuel Γ v s (fun V s =>
              tr_mem fuel Γ m s (fun s => wrap1 q_Ekst8 [H; I; V] (k (bump s))))))
        | _ => TErr "upd8"
        end
      else match hw_lookup kn with
      | Some (op, n) =>
          if Nat.eqb (length args) (S n) then
            tr_ints fuel Γ (firstn n args) s (fun As s =>
              tr_mem fuel Γ (nth n args (tRel 0)) s (fun s =>
                wrap1 q_Ehw [op; qlist q_atom As] (k (bump s))))
          else TErr "a machine operation with the wrong number of arguments"
      | None =>
      match find_fn_args Γ kn args with
      | Some (f, caps) =>
          if fi_rmem f then
            tr_call fuel Γ f caps args s (fun As s =>
              let '(x, s) := fresh (bump s) in
              wrap1 q_Ecall [qpos x; qpos (fi_id f); As] (k s))
          else TErr "a number used as a memory"
      | None => match helper_body kn with
                | Some b => tr_mem fuel Γ (beta_lets b args) s k
                | None => TErr ("not readable: " ^ snd kn ^ " (if it takes a function, the function given must name no variable of the caller: pass the variable as an argument)")
                end
      end
      end
  | tApp (tRel n) args =>
      match nth_error Γ n with
      | Some ESelf =>
          if fi_rmem self then
            tr_call fuel Γ self (cap_terms Γ self) args s (fun As s =>
              let '(x, s) := fresh (bump s) in
              wrap1 q_Ecall [qpos x; qpos (fi_id self); As] (k s))
          else TErr "a number used as a memory"
      | Some (ESib kn) =>
          match find_fn kn with
          | Some f =>
              if fi_rmem f then
                tr_call fuel Γ f (cap_terms Γ f) args s (fun As s =>
                  let '(x, s) := fresh (bump s) in
                  wrap1 q_Ecall [qpos x; qpos (fi_id f); As] (k s))
              else TErr "a number used as a memory"
          | None => TErr "a call of a function of the same fixpoint that is not translated"
          end
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
  match app_norm Γ t with
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
  | tLetIn na b ty body => if is_fun_ty ty then tr_cond fuel Γ (subst [b] 0 body) s kT kF else tr_let fuel Γ b ty s (fun Γ' s => tr_cond fuel Γ' body s kT kF)
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
  match app_norm Γ t with
  | tRel n => match nth_error Γ n with
              | Some (ERec es) => kk (ERec es) s
              | _ => TErr "a variable used as a record is not one"
              end
  | tLetIn na b ty body => if is_fun_ty ty then tr_recv fuel Γ mk ks (subst [b] 0 body) s kk else tr_let fuel Γ b ty s (fun Γ' s => tr_recv fuel Γ' mk ks body s kk)
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
      else if Kername.eqb kn kn_w64_op then
        (* a 64-bit operation on two u64 (KQRun.v): one machine operation on the two words *)
        match args with
        | [o; a; b] =>
            tr_recv fuel Γ mk ks a s (fun ea s => tr_recv fuel Γ mk ks b s (fun eb s =>
              match atoms_of 20 ea, atoms_of 20 eb with
              | [al; ah], [bl; bh] =>
                  let '(xl, s) := fresh s in
                  let '(xh, s) := fresh s in
                  match kk (ERec [EInt (avar xl); EInt (avar xh)]) s with
                  | TOk (rest, s') => TOk (tApp q_Ew64 [o; qpos xl; qpos xh; al; ah; bl; bh; rest], s')
                  | TErr m => TErr m
                  end
              | _, _ => TErr "a 64-bit operation on what is not a pair of numbers"
              end))
        | _ => TErr "w64_op"
        end
      else match find_fn_args Γ kn args with
      | Some (f, caps) =>
          match fi_rrec f with
          | Some (mk', ks') =>
              (* the function gives back the first number and puts the second in cell 0 of the slot block; the caller
                 keeps the cell's old number, reads the new one and puts the old one back *)
              tr_call fuel Γ f caps args s (fun As s =>
                let '(o, s) := fresh s in
                let '(x, s) := fresh s in
                let '(y, s) := fresh s in
                match kk (ERec [EInt (avar x); EInt (avar y)]) s with
                | TOk (rest, s') =>
                    TOk (tApp q_Ekld [qpos o; aint (qint slot_blk); aint q_zero;
                           tApp q_Ecall [qpos x; qpos (fi_id f); As;
                             tApp q_Ekld [qpos y; aint (qint slot_blk); aint q_zero;
                               tApp q_Ekst [aint (qint slot_blk); aint q_zero; avar o; rest]]]], s')
                | TErr m => TErr m
                end)
          | None => TErr "a function giving back a record: it must be recursive, and give back two numbers"
          end
      | None => match helper_body kn with
                | Some b => tr_recv fuel Γ mk ks (beta_lets b args) s kk
                | None => TErr ("not readable: " ^ snd kn ^ " (if it takes a function, the function given must name no variable of the caller: pass the variable as an argument)")
                end
      end
  | tApp (tRel n) args =>
      match nth_error Γ n with
      | Some ESelf =>
          match fi_rrec self with
          | Some _ =>
              tr_call fuel Γ self (cap_terms Γ self) args s (fun As s =>
                let '(o, s) := fresh s in
                let '(x, s) := fresh s in
                let '(y, s) := fresh s in
                match kk (ERec [EInt (avar x); EInt (avar y)]) s with
                | TOk (rest, s') =>
                    TOk (tApp q_Ekld [qpos o; aint (qint slot_blk); aint q_zero;
                           tApp q_Ecall [qpos x; qpos (fi_id self); As;
                             tApp q_Ekld [qpos y; aint (qint slot_blk); aint q_zero;
                               tApp q_Ekst [aint (qint slot_blk); aint q_zero; avar o; rest]]]], s')
                | TErr m => TErr m
                end)
          | None => TErr "a call of itself giving back a record: it must give back two numbers"
          end
      | _ => TErr "a call of a variable"
      end
  | tConst kn _ =>
      match helper_body kn with
      | Some b => tr_recv fuel Γ mk ks b s kk
      | None => TErr ("not readable: " ^ snd kn ^ " (if it takes a function, the function given must name no variable of the caller: pass the variable as an argument)")
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
  match app_norm Γ t with
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
  | tLetIn na b ty body => if is_fun_ty ty then tr_boolval fuel Γ (subst [b] 0 body) s k else tr_let fuel Γ b ty s (fun Γ' s => tr_boolval fuel Γ' body s k)
  | tCase ci p c [b] => tr_rec_case fuel Γ ci p c s (fun Γ' s => tr_boolval fuel Γ' (bbody b) s k)
  | _ => TErr "not a boolean this translator reads"
  end
  end.

(* the body in tail position *)
Fixpoint tr_tail (fuel : nat) (Γ : list ent) (t : term) (s : st) {struct fuel} : tres (term * st) :=
  match fuel with
  | O => TErr "out of fuel"
  | S fuel =>
  match app_norm Γ t with
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
  | tLetIn na b ty body => if is_fun_ty ty then tr_tail fuel Γ (subst [b] 0 body) s else tr_let fuel Γ b ty s (fun Γ' s => tr_tail fuel Γ' body s)
  | tCase ci p c [b] => tr_rec_case fuel Γ ci p c s (fun Γ' s => tr_tail fuel Γ' (bbody b) s)
  | tApp (tRel n) args =>
      match nth_error Γ n with
      | Some ESelf => tr_call fuel Γ self (cap_terms Γ self) args s (fun As s => TOk (tApp q_Eloop [As], s))
      | Some (ESib _) =>
          if fi_rmem self then tr_mem fuel Γ t s (fun s => TOk (tApp q_Eret [aint q_zero], s))
          else tr_int fuel Γ t s (fun A s => TOk (tApp q_Eret [A], s))
      | _ => TErr "a call of a variable"
      end
  | _ =>
      match fi_rrec self with
      | Some (mk, ks) =>
          (* the first number is returned, the second goes into cell 0 of the slot block *)
          tr_recv fuel Γ mk ks t s (fun e s =>
            match atoms_of 20 e with
            | [a0; a1] => TOk (tApp q_Ekst [aint (qint slot_blk); aint q_zero; a1; tApp q_Eret [a0]], s)
            | _ => TErr "a record of two numbers"
            end)
      | None =>
          if fi_rmem self then tr_mem fuel Γ t s (fun s => TOk (tApp q_Eret [aint q_zero], s))
          else tr_int fuel Γ t s (fun A s => TOk (tApp q_Eret [A], s))
      end
  end
  end.
End TR.

(* ------------------------------------------------------------------ a function's head *)
Fixpoint lams (t : term) : list term * term :=
  match t with tLambda _ ty b => let '(l, r) := lams b in (ty :: l, r) | _ => ([], t) end.

Fixpoint prods_res (t : term) : term := match t with tProd _ _ b => prods_res b | _ => t end.

Definition result_mem (Σ : global_env) (ty : term) : option bool :=
  match kind_of 20 Σ (prods_res ty) with Some KInt => Some false | Some KMem => Some true | _ => None end.

(* the result of a function: a number, a memory, or a record or pair of two numbers *)
Definition result_kind (Σ : global_env) (ty : term) : option (bool * option (term * list kind)) :=
  match kind_of 20 Σ (prods_res ty) with
  | Some KInt => Some (false, None)
  | Some KMem => Some (true, None)
  | Some (KRec mk ks) =>
      match ks with
      | [KInt; KInt] => Some (false, Some (mk, ks))
      | _ => None
      end
  | _ => None
  end.

(* the parts of a function: whether it calls itself, its parameter types, its body *)
Definition fparts (b : term) : option (bool * list term * term) :=
  match b with
  | tFix mfix k => match nth_error mfix k with
                   | Some d => if Nat.eqb (rarg d) 0 then let '(l, r) := lams (dbody d) in Some (true, l, r) else None
                   | None => None
                   end
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
      match fparts b, result_kind Σ ty with
      | Some (false, tys, _), Some (_, rr) =>
          match opt_all (map (kind_of 20 Σ) tys) with
          | Some _ => (* a function that gives back a record (a u64) does more work per node *)
                      Nat.ltb (match rr with Some _ => Nat.div inline_limit 2 | None => inline_limit end) (term_size 100000 b)
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

(* A recursive function of the file that takes functions (a comparison, a step) is not translated by itself: each call that
   gives it known functions (closed terms: constants, applications of constants to numbers, lambdas that name no variable
   of the caller) makes a copy for those functions, as a template does.  A function that would need a variable of the
   caller (a closure) is refused: its variables are passed as arguments. *)
Definition is_prod (t : term) : bool := match t with tProd _ _ _ => true | _ => false end.

Definition template_places (Σ : global_env) (mp : modpath) (kn : kername) : list nat :=
  if eq_mp (fst kn) mp then
    match body_of Σ kn with
    | Some (_, tFix [d] 0) =>
        let tys := fst (lams (dbody d)) in
        filter (fun j => match nth_error tys j with Some ty => is_prod ty | None => false end) (seq 0 (length tys))
    | _ => []
    end
  else [].

(* the key of a copy: the function, the functions it is given (with the variables of the caller they name as 0, 1, ..), and
   the types of those variables *)
Definition fkey := (kername * list (nat * term) * list term)%type.
Definition fk_kn (k : fkey) : kername := fst (fst k).
Definition fk_fixed (k : fkey) : list (nat * term) := snd (fst k).
Definition fk_caps (k : fkey) : list term := snd k.

Definition key_eqb (a b : fkey) : bool :=
  Kername.eqb (fk_kn a) (fk_kn b) && Nat.eqb (length (fk_fixed a)) (length (fk_fixed b)) &&
  forallb (fun jt => jt) (map (fun p => Nat.eqb (fst (fst p)) (fst (snd p)) && term_same 10000 (snd (fst p)) (snd (snd p)))
                               (combine (fk_fixed a) (fk_fixed b))) &&
  Nat.eqb (length (fk_caps a)) (length (fk_caps b)) &&
  forallb (fun p => term_same 10000 (fst p) (snd p)) (combine (fk_caps a) (fk_caps b)).

(* a variable a function given to a template may name: a number, a counter or a memory (its type is closed) *)
Definition cap_ok (Σ : global_env) (ty : term) : bool :=
  closedn 0 ty && match kind_of 20 Σ ty with Some KInt => true | Some KNat => true | Some KMem => true | _ => false end.

(* the copy a call asks for: every function it is given is a term, whose free variables (the types of the variables of the text
   around, [env], newest first) are numbers, counters or a memory *)
Definition site_key (Σ : global_env) (mp : modpath) (env : list term) (kn : kername) (args : list term) : option fkey :=
  match template_places Σ mp kn with
  | [] => None
  | js =>
      let fix go (js : list nat) (cl : list nat) (acc : list (nat * term)) : option (list (nat * term) * list nat) :=
          match js with
          | [] => Some (rev acc, cl)
          | j :: r => match nth_error args j with
                      | Some a => let '(a', cl') := abs_free 1000 0 a cl in go r cl' ((j, a') :: acc)
                      | None => None
                      end
          end in
      match go js [] [] with
      | Some (fx, cl) =>
          match opt_all (map (fun j => match nth_error env j with
                                       | Some ty => if cap_ok Σ ty then Some ty else None
                                       | None => None end) cl) with
          | Some tys => Some (kn, fx, tys)
          | None => None
          end
      | None => None
      end
  end.

(* a helper of the file (not recursive) that takes functions: it is written out where it is used, with them put in, so its
   body is read that way *)
Definition helper_hof (Σ : global_env) (mp : modpath) (kn : kername) : option term :=
  if eq_mp (fst kn) mp then
    match body_of Σ kn with
    | Some (_, b) => if has_fix 1000 b then None else if existsb is_prod (fst (lams b)) then Some b else None
    | None => None
    end
  else None.

(* the functions a term calls: its constants, and for a template the copy the call asks for; [env] the types of the variables in
   scope, newest first ([unk] where not known) *)
Definition unk : term := tVar "?".

Fixpoint site_keys (fuel : nat) (Σ : global_env) (mp : modpath) (env : list term) (t : term) (acc : list fkey) : list fkey :=
  match fuel with
  | O => acc
  | S fuel =>
      let add (k : fkey) (acc : list fkey) := if existsb (key_eqb k) acc then acc else k :: acc in
      match t with
      | tConst kn _ => match template_places Σ mp kn with [] => add (kn, [], []) acc | _ => acc end
      | tApp (tConst kn _) args =>
          let acc := fold_left (fun acc a => site_keys fuel Σ mp env a acc) args acc in
          match template_places Σ mp kn with
          | [] => let acc := add (kn, [], []) acc in
                  match helper_hof Σ mp kn with Some b => site_keys fuel Σ mp env (beta_lets b args) acc | None => acc end
          | _ => match site_key Σ mp env kn args with Some k => add k acc | None => acc end
          end
      | tApp f args => fold_left (fun acc a => site_keys fuel Σ mp env a acc) args (site_keys fuel Σ mp env f acc)
      | tLambda _ ty b | tProd _ ty b => site_keys fuel Σ mp (ty :: env) b (site_keys fuel Σ mp env ty acc)
      | tLetIn _ b ty body => site_keys fuel Σ mp (ty :: env) body (site_keys fuel Σ mp env ty (site_keys fuel Σ mp env b acc))
      | tCase ci p c brs =>
          let isnat := Kername.eqb (inductive_mind (ci_ind ci)) (inductive_mind ind_nat) in
          fold_left (fun acc ib =>
                       let br := snd ib in
                       let env' := List.app (map (fun _ => if andb isnat (Nat.eqb (fst ib) 1) then tInd ind_nat [] else unk)
                                                 (bcontext br)) env in
                       site_keys fuel Σ mp env' (bbody br) acc)
                    (combine (seq 0 (length brs)) brs)
                    (site_keys fuel Σ mp env c (site_keys fuel Σ mp env (preturn p) acc))
      | tFix mfix _ =>
          let env' := List.app (rev (map dtype mfix)) env in
          fold_left (fun acc d => site_keys fuel Σ mp env' (dbody d) (site_keys fuel Σ mp env (dtype d) acc)) mfix acc
      | _ => acc
      end
  end.

(* the body of a copy: the template's body with the given functions put in for their parameters, as a function of the parameters
   that stay and of the variables those functions name *)
Definition inst_body (Σ : global_env) (key : fkey) : option term :=
  match body_of Σ (fk_kn key) with
  | Some (_, b) =>
      match fparts b with
      | Some (isrec, tys, inner) =>
          let n := length tys in
          let fixed := fk_fixed key in
          let caps := fk_caps key in
          let m := length caps in
          let surv := map snd (filter (fun jt => negb (existsb (fun f => Nat.eqb (fst f) (fst jt)) fixed))
                                      (combine (seq 0 n) tys)) in
          let s := length surv in
          (* surviving parameter p (0 = first) is at the place [count of survivors after it] above the captured ones *)
          let after p := length (filter (fun q => negb (existsb (fun jt => Nat.eqb (fst jt) q) fixed)) (seq (S p) (Nat.sub n (S p)))) in
          let capsub := map (fun k => tRel (Nat.sub (Nat.sub m 1) k)) (seq 0 m) in
          let sub := map (fun i => let p := Nat.sub (Nat.sub n 1) i in
                                   match List.find (fun jt => Nat.eqb (fst jt) p) fixed with
                                   | Some jt => subst capsub 0 (snd jt)
                                   | None => tRel (m + after p)
                                   end) (seq 0 n) in
          let body' := subst (List.app sub (if isrec then [tRel (m + s)] else [])) 0 inner in
          let anon := {| binder_name := nAnon; binder_relevance := Relevant |} in
          Some (fold_right (fun ty acc => tLambda anon ty acc) body' (List.app surv caps))
      | None => None
      end
  | None => None
  end.

(* the functions defined together with a fixpoint's (its own included), in the order of the definition *)
Definition group_keys (Σ : global_env) (key : fkey) : list fkey :=
  match fk_fixed key with
  | [] => match body_of Σ (fk_kn key) with
          | Some (_, tFix mfix _) =>
              if Nat.ltb 1 (length mfix)
              then map (fun d => (((fst (fk_kn key), match binder_name (dname d) with nNamed s => s | nAnon => "" end), @nil (nat * term)), @nil term)) mfix
              else [key]
          | _ => [key]
          end
  | _ => [key]
  end.

Definition is_fun_key (Σ : global_env) (mp : modpath) (root : kername) (key : fkey) : bool :=
  match fk_fixed key with
  | [] => is_fun Σ mp root (fk_kn key)
  | _ => true
  end.

(* every function reachable from the root, callees first: a function of the file, or a copy of a template *)
Fixpoint reach (fuel : nat) (Σ : global_env) (mp : modpath) (root : kername) (key : fkey)
               (done : list fkey) : list fkey :=
  match fuel with
  | O => done
  | S fuel =>
      if existsb (key_eqb key) done then done
      else match (match fk_fixed key with [] => option_map snd (body_of Σ (fk_kn key)) | _ => inst_body Σ key end) with
           | Some b =>
               let cs := rev (site_keys 10000 Σ mp [] b []) in
               let done := fold_left (fun d c =>
                             if key_eqb c key then d
                             else if eq_mp (fst (fk_kn c)) mp || eq_mp (fst (fk_kn c)) kit_mp then reach fuel Σ mp root c d else d) cs done in
               if is_fun_key Σ mp root key then List.app done (group_keys Σ key) else done
           | None => done
           end
  end.

(* does the body write the memory, directly or through a function that does *)
Fixpoint writes (fuel : nat) (fns : list finfo) (look : kername -> option term) (t : term) : bool :=
  match fuel with
  | O => true
  | S fuel =>
      match t with
      | tConst kn _ => Kername.eqb kn kn_upd || Kername.eqb kn kn_upd32 || Kername.eqb kn kn_upd8 || (match hw_lookup kn with Some _ => true | None => false end) ||
                       match List.find (fun f => Kername.eqb (fi_kn f) kn) fns with
                       | Some f => fi_wr f
                       | None => match look kn with Some b => writes fuel fns look b | None => false end
                       end
      | tApp f args => writes fuel fns look f || existsb (writes fuel fns look) args
      | tLambda _ _ b => writes fuel fns look b
      | tLetIn _ b _ body => writes fuel fns look b || writes fuel fns look body
      | tCase _ _ c brs => writes fuel fns look c || existsb (fun br => writes fuel fns look (bbody br)) brs
      | tFix mfix _ => existsb (fun d => writes fuel fns look (dbody d)) mfix
      | _ => false
      end
  end.

Definition mk_info (Σ : global_env) (mp : modpath) (fns : list finfo) (i : nat) (key : fkey) : option finfo :=
  let kn := fk_kn key in
  let fixed := fk_fixed key in
  match body_of Σ kn with
  | Some (ty, b) =>
      match fparts b, result_kind Σ ty with
      | Some (isrec, tys, body), Some (rm, rr) =>
          let tys := map snd (filter (fun jt => negb (existsb (fun f => Nat.eqb (fst f) (fst jt)) fixed)) (combine (seq 0 (length tys)) tys)) in
          let grp := match b with tFix mfix _ => if Nat.ltb 1 (length mfix) then Some mfix else None | _ => None end in
          (* a helper of the file written out where it is used writes the memory if its body does *)
          let look := fun k => if eq_mp (fst k) mp then
                                 match lookup_env Σ k with
                                 | Some (ConstantDecl cb) =>
                                     match cst_body cb with Some b0 => if has_fix 1000 b0 then None else Some b0 | None => None end
                                 | _ => None
                                 end
                               else None in
          let wr := match grp with
                    | Some mfix => existsb (fun d => writes 10000 fns look (dbody d)) mfix
                    | None => writes 10000 fns look body
                    end in
          (* a function of the same fixpoint just before this one: its bound index *)
          let bi := match grp, rev fns with
                    | Some mfix, p :: _ =>
                        if existsb (fun d => match binder_name (dname d) with nNamed s => String.eqb s (snd (fi_kn p)) | nAnon => false end) mfix
                        then fi_bi p else i
                    | _, _ => i
                    end in
          match opt_all (map (kind_of 20 Σ) tys), opt_all (map (kind_of 20 Σ) (fk_caps key)) with
          | Some rks, Some cks =>
              let restmem := existsb is_mem_kind rks in
              let capmem := existsb is_mem_kind cks in
              if andb restmem capmem then None
              else
                let restnm := filter (fun k => negb (is_mem_kind k)) rks in
                let capnm := filter (fun k => negb (is_mem_kind k)) cks in
                let ks := List.app restnm (List.app capnm (if orb restmem capmem then [KMem] else [])) in
                Some (mkFI kn (Pos.of_nat (1000 + i)) ks rm isrec wr rr bi
                           (match fixed with [] => snd kn | _ => snd kn ^ "_" ^ string_of_nat i end) fixed
                           cks (length restnm) restmem)
          | _, _ => None
          end
      | _, _ => None
      end
  | None => None
  end.

Fixpoint build_infos (Σ : global_env) (mp : modpath) (kns : list fkey) (i : nat) (acc : list finfo) : option (list finfo) :=
  match kns with
  | [] => Some acc
  | kn :: kns =>
      match mk_info Σ mp acc i kn with
      | Some f => build_infos Σ mp kns (S i) (List.app acc [f])
      | None => None
      end
  end.

(* translate one function; its parameters are KQL variables 1 .. n *)
Definition tr_fun (Σ : global_env) (mp : modpath) (fns : list finfo) (shared : list PrimInt63.int) (f : finfo) : tres term :=
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
          let ents00 := fst (ents_of ks pids) in
          (* the entries are: the parameters of the function that are not a memory, the captured numbers, a memory *)
          let nr := fi_nrest f in
          let ncap := length (filter (fun k => negb (is_mem_kind k)) (fi_capk f)) in
          let restnm_e := firstn nr ents00 in
          let capnm_e := firstn ncap (skipn nr ents00) in
          let mem_e := skipn (Nat.add nr ncap) ents00 in
          let ents0 := List.app restnm_e (if fi_restmem f then mem_e else []) in
          let m := length (fi_capk f) in
          let cap_by_k := (fix mkc (ks : list kind) (nm me : list ent) : list ent :=
                             match ks with
                             | [] => []
                             | k :: r => if is_mem_kind k
                                         then (match me with e :: _ => e | [] => EMem 0 end) :: mkc r nm me
                                         else match nm with e :: nm' => e :: mkc r nm' me | [] => EMem 0 :: mkc r [] me end
                             end) (fi_capk f) capnm_e (if fi_restmem f then [] else mem_e) in
          (* the parameters that are functions given by the caller stand where they were, as known functions *)
          let ents := (fix ins (j : nat) (fuel : nat) (es : list ent) : list ent :=
                         match fuel with
                         | O => es
                         | S fuel =>
                             match List.find (fun jt => Nat.eqb (fst jt) j) (fi_fixed f) with
                             | Some jt => EFun (snd jt) m :: ins (S j) fuel es
                             | None => match es with e :: r => e :: ins (S j) fuel r | [] => [] end
                             end
                         end) 0 (length ents0 + length (fi_fixed f)) ents0 in
          (* the fixpoint's functions, the last first (de Bruijn): this one, the others by name *)
          let fixents :=
            match body_of Σ (fi_kn f) with
            | Some (_, tFix mfix k) =>
                rev (mapi (fun j d => if Nat.eqb j k then ESelf
                                      else ESib (fst (fi_kn f), match binder_name (dname d) with nNamed s => s | nAnon => "" end)) mfix)
            | _ => if fi_rec f then [ESelf] else []
            end in
          let Γ := List.app (rev ents) (List.app fixents (rev cap_by_k)) in
          let kpids := firstn (length (flat_map (leaves 20) ks)) pids in
          match tr_tail Σ mp fns f shared 2000 Γ body (mkSt (Pos.of_nat (S n)) 0) with
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

(* field [j] of a record or pair [p] whose constructor (with its parameters) is [mk]: the projection of a primitive record,
   the field function of another *)
Definition field_proj_ind (Σ : global_env) (i : inductive) (params : list term) (j : nat) (p : term) : term :=
  match lookup_env Σ (inductive_mind i) with
  | Some (InductiveDecl mib) =>
      match nth_error (ind_bodies mib) (inductive_ind i) with
      | Some oib =>
          match ind_projs oib with
          | _ :: _ => tProj {| proj_ind := i; proj_npars := length params; proj_arg := j |} p
          | [] =>
              match ind_ctors oib with
              | [cb] =>
                  match nth_error (rev (map (fun d => binder_name (decl_name d)) (cstr_args cb))) j with
                  | Some (nNamed s) => tApp (tConst (fst (inductive_mind i), s) []) (List.app params [p])
                  | _ => p
                  end
              | _ => p
              end
          end
      | None => p
      end
  | _ => p
  end.

Definition field_proj (Σ : global_env) (mk : term) (j : nat) (p : term) : term :=
  match mk with
  | tApp (tConstruct i _ u) params =>
      if Kername.eqb (inductive_mind i) (inductive_mind ind_prod)
      then tApp (tConst (if Nat.eqb j 0 then kn_fst else kn_snd) []) (List.app params [p])
      else field_proj_ind Σ i params j p
  | tConstruct i _ u => field_proj_ind Σ i [] j p
  | _ => p
  end.

(* [kat]: the statement for one value of the first parameter (a counter): a function of it, for the lemma of a mutual group *)
Definition stmt (Σ : global_env) (prog : term) (f : finfo) (kat : bool) (slots : bool) : term :=
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
  let cbf := tApp q_cbk [natq (fi_bi f)] in
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
  (* the variables the functions given name: the captured numbers come after the others in the arguments, a captured memory is the memory *)
  let capterms d := (fix mkc (cks : list kind) (nm : list term) : list term :=
                       match cks with
                       | [] => []
                       | k :: r => if is_mem_kind k then mvar d :: mkc r nm
                                   else match nm with t :: nm' => t :: mkc r nm' | [] => mvar d :: mkc r [] end
                       end) (fi_capk f) (skipn (fi_nrest f) (fargs d)) in
  let full d := (fix ins (j : nat) (fuel : nat) (es : list term) : list term :=
                   match fuel with
                   | O => es
                   | S fuel =>
                       match List.find (fun jt => Nat.eqb (fst jt) j) (fi_fixed f) with
                       | Some jt => subst (capterms d) 0 (snd jt) :: ins (S j) fuel es
                       | None => match es with e :: r => e :: ins (S j) fuel r | [] => [] end
                       end
                   end) 0 (length (firstn (fi_nrest f) (fargs d)) + length (fi_fixed f)) (firstn (fi_nrest f) (fargs d)) in
  let fapp d := mkApps (tConst (fi_kn f) []) (List.app (full d) (if fi_restmem f then [mvar d] else [])) in
  (* the block of the slot has room for the second number *)
  (* the slot block has room when the program starts; its size never falls below that (KQSpec.v len_size) *)
  let szp d := tApp q_Zlt [<% 1%Z %>; tApp q_stoz [tApp q_klen [qint slot_blk]]] in
  let body d :=
    match fi_rrec f with
    | Some (mk, _) =>
        let p := fapp d in
        tApp q_runk [prog; qpos (fi_id f); args d; mvar d; field_proj Σ mk 0 p;
                     tApp q_upd [qint slot_blk; qint 0; field_proj Σ mk 1 p; mvar d]]
    | None =>
        if fi_rmem f then tApp q_runk [prog; qpos (fi_id f); args d; mvar d; q_zero; fapp d]
        else if andb hasM (fi_wr f) then tApp q_runx [prog; qpos (fi_id f); args d; mvar d; fapp d]
        else tApp q_runk [prog; qpos (fi_id f); args d; mvar d; fapp d; mvar d]
    end in
  let anon := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let core := if slots then tProd anon (bnd 0) (tProd anon (szp 1) (body 2))
              else tProd anon (bnd 0) (body 1) in
  let withM := tProd {| binder_name := nNamed "M"; binder_relevance := Relevant |} q_kmem core in
  fold_right (fun ik acc =>
                (if andb kat (Nat.eqb (fst ik) 0) then tLambda else tProd)
                      {| binder_name := nNamed ("x" ^ string_of_nat (fst ik)); binder_relevance := Relevant |}
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

(* the functions of one mutual fixpoint: consecutive, with the same bound index *)
Fixpoint group_runs (l : list finfo) (cur : list finfo) : list (list finfo) :=
  match l with
  | [] => match cur with _ :: _ :: _ => [rev cur] | _ => [] end
  | f :: l => match cur with
              | p :: _ => if Nat.eqb (fi_bi p) (fi_bi f) then group_runs l (f :: cur)
                          else (match cur with _ :: _ :: _ => [rev cur] | _ => [] end) ++ group_runs l [f]
              | [] => group_runs l [f]
              end
  end.

(* A function of a mutual fixpoint that the program does not name is not among the quoted constants (the others reach it
   by the fixpoint's own binder): add it, as the constant it is, with the fixpoint for its body. *)
Definition extend_siblings (Σ : global_env) : global_env :=
  let news := flat_map (fun kd =>
                match snd kd with
                | ConstantDecl cb =>
                    match cst_body cb with
                    | Some (tFix mfix k) =>
                        if Nat.ltb 1 (length mfix) then
                          flat_map (fun jd =>
                            let kn : kername := (fst (fst kd), match binder_name (dname (snd jd)) with nNamed s => s | nAnon => "" end) in
                            match lookup_env Σ kn with
                            | Some _ => []
                            | None => [(kn, ConstantDecl {| cst_type := dtype (snd jd); cst_body := Some (tFix mfix (fst jd));
                                                            cst_universes := cst_universes cb;
                                                            cst_relevance := cst_relevance cb |})]
                            end) (combine (seq 0 (length mfix)) mfix)
                        else []
                    | _ => []
                    end
                | _ => []
                end) (declarations Σ) in
  {| universes := universes Σ; declarations := List.app news (declarations Σ); retroknowledge := retroknowledge Σ |}.

Definition kqm_gen (shared : list PrimInt63.int) (p : program) (prog_name : ident) : tout :=
  let '(Σ0, t) := p in
  let Σ := extend_siblings Σ0 in
  match t with
  | tConst root _ =>
      let mp := fst root in
      let kns := reach 1000 Σ mp root (root, [], []) [] in
      match build_infos Σ mp kns 0 [] with
      | Some fns =>
          let fix go (fs : list finfo) (acc : list (finfo * term)) :=
            match fs with
            | [] => TOk (rev acc)
            | f :: fs => match tr_fun Σ mp fns shared f with
                         | TOk e => go fs ((f, e) :: acc)
                         | TErr m => TErr m
                         end
            end in
          match go fns [] with
          | TOk tfs =>
              let pkn : kername := (mp, prog_name) in
              let fdefs := map (fun fe => KDef (fi_name (fst fe) ^ "_kqm") q_fn (snd fe)) tfs in
              let pfuns := qlist (tApp q_prod [q_ident; q_fn])
                             (map (fun fe => tApp q_pair [q_ident; q_fn; qpos (fi_id (fst fe));
                                                          tConst (mp, fi_name (fst fe) ^ "_kqm") []]) tfs) in
              let parrs := tApp q_nil [tApp q_prod [q_ident; q_Z]] in
              let pdef := KDef prog_name <% prog %> (tApp q_mkprog [pfuns; parrs]) in
              let slots := existsb (fun fe => match fi_rrec (fst fe) with Some _ => true | None => false end) tfs in
              let sdefs := map (fun fe => KDef (fi_name (fst fe) ^ "_kstmt") <% Prop %> (stmt Σ (tConst pkn []) (fst fe) false slots)) tfs in
              let used := fold_left (fun acc fe => match body_of Σ (fi_kn (fst fe)) with
                                                   | Some (_, b) => List.app (consts 10000 b []) (List.app (flat_map (fun jt => consts 10000 (snd jt) []) (fi_fixed (fst fe))) acc)
                                                   | None => acc end) tfs [] in
              let grps := group_runs (map fst tfs) [] in
              let katdefs := flat_map (fun g => map (fun f => KDef (fi_name f ^ "_kat") <% nat -> Prop %> (stmt Σ (tConst pkn []) f true slots)) g) grps in
              let hs := filter (fun kn => negb (Kername.eqb kn kn_kq_nat)) (helpers_of 10000 Σ mp fns used []) in
              mkOut (List.app fdefs (pdef :: List.app sdefs katdefs))
                    ("KQM: " ^ string_of_nat (length tfs) ^ " functions: " ^
                     String.concat " " (map (fun fe => fi_name (fst fe)) tfs) ^
                     String.concat "" (map (fun g => "
KQM group: " ^ String.concat " " (map fi_name g)) grps) ^
                     (if slots then "
KQM pairfns: " ^ String.concat " " (map fi_name (filter (fun f => match fi_rrec f with Some _ => true | None => false end) (map fst tfs))) else "") ^
                     "
KQM helpers: " ^ String.concat " " (map help_name hs) ^
                     "
KQM entry: " ^ (match last_error tfs with
                      | Some fe => let f := fst fe in
                                   fi_name f ^ " " ^ string_of_nat (Pos.to_nat (fi_id f)) ^ " " ^
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
  (kqm_define ltac:(run_template_program (tmQuoteRec x) (fun q => let t := eval vm_compute in (kqm_gen nil q name) in exact t)))
  (only parsing).
(* the same for a program that shares narrow blocks with another processor: [sh] lists them (a Rocq list of numbers, written in the program) *)
Notation kqm_translate_s x name sh :=
  (kqm_define ltac:(run_template_program (tmQuoteRec x) (fun q => let t := eval vm_compute in (kqm_gen sh q name) in exact t)))
  (only parsing).

(* ------------------------------------------------------------------ the proof of a statement *)
Ltac kqm_auto :=
  hnf;
  (* a function that writes the memory and gives a number is stated with [runx]; the other proofs do not apply to
     it and, tried first, can run a long time before they fail *)
  lazymatch goal with
  | |- context [runx _ _ _ _ _] =>
      lazymatch goal with
      | |- forall (_ : nat), _ => first [ solve [ kqx_prove ] | solve [ kqx_prove0 ] ]
      | _ => solve [ kqx_prove0 ]
      end
  | _ =>
      lazymatch goal with
      | |- forall (_ : nat), _ => first [ solve [ kqm_prove ] | solve [ kqm_prove0 ] ]
      | _ => solve [ kqm_prove0 ]
      end
  end.
