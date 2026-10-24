(** KQMNames: naming the memories of a function's text.  A function that changes the memory in steps
    ([let s := f1 s in let s := f2 s in ..]) mentions each earlier memory in every later one, and a step that reads
    the memory it writes mentions it twice: written out, the text doubles per step.  The proof gives each memory of
    such a [let] a name (a local definition) in the goal, one [let] at a time (each a single step the kernel checks at
    once), and the walk (KQMAuto.v) gives its own memory the same name when it is the same, so both sides say
    "memory 7" and stay short.  Other [let]s are written out as before. *)
From Ltac2 Require Import Ltac2.
Require KQ.KQRun.

(* the goal is [evalk P f rho M e v M'] (7 arguments) or [evalx P f rho M e v] (6): the text of v, and of M' *)
Ltac2 kqm_is_let (c : constr) : bool :=
  match Constr.Unsafe.kind c with Constr.Unsafe.LetIn _ _ _ => true | _ => false end.

Ltac2 rec kqm_name_lets_goal () : unit :=
  let g := Control.goal () in
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.App f args =>
      let n := Array.length args in
      let idx :=
        if kqm_is_let (Array.get args 5) then 5
        else if Int.equal n 7 then (if kqm_is_let (Array.get args 6) then 6 else 0)
        else 0 in
      if Int.equal idx 0 then ()
      else
        match Constr.Unsafe.kind (Array.get args idx) with
        | Constr.Unsafe.LetIn bnd rhs body =>
            let args' := Array.copy args in
            if Constr.equal (Constr.type rhs) constr:(KQ.KQRun.mem) then
              (* the memory of this [let]: a local definition *)
              (Array.set args' idx body;
               let g' := Constr.Unsafe.make (Constr.Unsafe.LetIn bnd rhs (Constr.Unsafe.make (Constr.Unsafe.App f args'))) in
               Control.refine (fun () => open_constr:(_ : $g'));
               ltac1:(intro);
               kqm_name_lets_goal ())
            else
              (* any other [let] is written out *)
              (Array.set args' idx (Constr.Unsafe.substnl [rhs] 0 body);
               let g' := Constr.Unsafe.make (Constr.Unsafe.App f args') in
               Control.refine (fun () => open_constr:(_ : $g'));
               kqm_name_lets_goal ())
        | _ => ()
        end
  | _ => ()
  end.

Ltac kqm_name_lets := ltac2:(kqm_name_lets_goal ()).
