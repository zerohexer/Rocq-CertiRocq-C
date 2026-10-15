(* KQNat.v -- THE LOOP BUDGET AS A MACHINE NUMBER.
   A Rocq loop counts down a `nat`.  Compiled as it stands a nat is a chain of cells, one per unit: a loop of five
   million rounds walks 80 MB of them.  Here the compiler is told to keep a nat as ONE machine integer: O is 0, S n is
   n + 1, and looking at a nat (`match n with O => .. | S m => ..`) is a test against 0.

   Two commands of the compiler do it (`--allow-unsafe-erasure` is needed: these passes of MetaRocq carry no proof):
     Extract Inductive To Constants   every O, S and `match` on a nat becomes a call of the three definitions below;
     Extract Inline                   and those calls are replaced by the definitions' own text.
   Right for budgets below 2^62.  The program's text does not change: it still says `nat`. *)
From CertiRocq.Plugin Require Import CertiRocq.
From Stdlib Require Import Uint63.
Open Scope uint63_scope.

Definition kq_O : int := 0.
Definition kq_S (n : int) : int := n + 1.
(* The compiler hands a `match` three things: the number, what to do for O, what to do for S.  Types are gone by
   then, so this is written at ONE type (unit) and used at all of them; a version with a type parameter would be
   handed its arguments one place off. *)
Definition kq_case (n : int) (z : unit -> unit) (s : int -> unit) : unit :=
  if n =? 0 then z tt else s (n - 1).

CertiRocq Extract Inductive To Constants [ nat => [ [ kq_O kq_S | kq_case ] ] ].
CertiRocq Extract Inline [ kq_O, kq_S, kq_case ].
