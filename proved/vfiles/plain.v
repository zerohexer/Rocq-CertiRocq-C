(* An ordinary Rocq file.  `rocq c -R . KQ proved/vfiles/plain.v` compiles it as any other; `python3 proved/kitc.py proved/vfiles/plain.v`
   compiles it to C and proves the C computes it.  There is no main: the last function of the file is where the program starts (or
   --main=NAME), and its signature says what it takes: a number or a boolean from the command line, a counter from the command line,
   the memory from the memory file.  A library of lib/ is required as any other library. *)
From Stdlib Require Import Sint63.
From KQ Require Import KQRun.
From KQ.lib Require Import CInt.
Open Scope sint63_scope.

Record pt := mkpt { x : int; y : int }.

Definition step (p : pt) (v : int) : pt := mkpt (u32_add (x p) v) (rotl32 (y p) 5 + i8_of v).

Fixpoint fold (k : nat) (i n : int) (p : pt) (s : mem) : pt :=
  match k with
  | O => p
  | S m => if n <=? i then p else fold m (i + 1) n (step p (rd 0 i s)) s
  end.

Definition total (rounds : nat) (n seed : int) (s : mem) : int :=
  let p := fold rounds 0 n (mkpt seed 1) s in
  u32_xor (x p) (y p) + popcount32 (x p).
