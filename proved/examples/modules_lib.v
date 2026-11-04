(* a file the program modules.body requires: a record, a function giving it back, a function in a module that writes the memory *)
From KQ Require Import KQRun.
Record pt := mkp { px : int; py : int }.
Fixpoint walk (n : nat) (p : pt) : pt := match n with O => p | S m => walk m (mkp (py p) (px p + 1)) end.
Module Cells.
  Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.
End Cells.
