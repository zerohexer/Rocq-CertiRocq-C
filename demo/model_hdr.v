(* model_hdr.v -- THE SAME TEXT RUN BY ROCQ ITSELF.
   demo/coop.body is compiled to C against KQRun.v, where the memory, the input and the output are things only
   declared.  Here they are DEFINED, as plain Rocq data: a memory is the blocks of cells, what is left of the input and
   what has been written; `rd`, `upd`, `kq_in`, `kq_out` are four small functions on it.  With this file in front, the
   body is an ordinary Rocq function that Rocq can run (the last lines do, on a small input) and that can be reasoned
   about with nothing but Rocq.  Integers are Z here; the native run uses 63-bit machine integers, which are the same
   as long as no number leaves that range. *)
From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Definition int := Z.
Record mem := mkW { cells : list (list Z); inp : list Z; out : list Z }.
Fixpoint set_nth {A} (n : nat) (v : A) (l : list A) : list A :=
  match l, n with [], _ => [] | _ :: r, O => v :: r | x :: r, S n => x :: set_nth n v r end.
Definition nat_of (z : Z) : nat := Z.to_nat (Z.max 0 z).               (* a negative number means 0 *)
Definition rd (h i : Z) (w : mem) : Z := nth (nat_of i) (nth (nat_of h) (cells w) []) 0.
Definition updc (h i v : Z) (c : list (list Z)) : list (list Z) :=
  set_nth (nat_of h) (set_nth (nat_of i) v (nth (nat_of h) c [])) c.
Definition upd (h i v : Z) (w : mem) : mem := mkW (updc h i v (cells w)) (inp w) (out w).
Definition kq_in (h i : Z) (w : mem) : mem :=
  match inp w with
  | x :: r => mkW (updc h i x (cells w)) r (out w)
  | [] => mkW (updc h i (-1) (cells w)) [] (out w)
  end.
Definition kq_out (v : Z) (w : mem) : mem := mkW (cells w) (inp w) (v :: out w).
Infix "land" := Z.land (at level 40, left associativity).
Infix ">>" := Z.shiftr (at level 30, no associativity).
Definition kq_nat (z : Z) : nat := Z.to_nat z.
Definition kq_O : Z := 0.
Definition kq_S (n : Z) : Z := n + 1.
Definition kq_case (n : Z) (z : unit -> unit) (s : Z -> unit) : unit := tt.
Definition kq_sum (w : mem) : Z := 0.
