(* TestDiv.v -- KQRun's division and remainder against Z's, on numbers that include the negative ones and the edges
   of 63 bits (a result that does not fit 63 bits is compared after wrapping, as the machine does). *)
From Stdlib Require Import ZArith List Sint63.
Require Import KQ.KQRun.
Import ListNotations.
Open Scope Z_scope.
Definition xs : list Z :=
  [0; 1; -1; 2; -2; 3; -3; 7; -7; 8; -8; 10; -10; 26; 1000; -1000; 131071; 1000000006; 1000000007; 1000000008;
   -1000000007; -1000000008; 998244353; 123456789012; -98765432101; 2305843009213693952; -2305843009213693952;
   4611686018427387902; 4611686018427387903; -4611686018427387903; -4611686018427387904].
Definition wrap (z : Z) : Z := Sint63.to_Z (Uint63.of_Z z).
Definition ok (x y : Z) : bool :=
  (Sint63.to_Z (zdiv (Uint63.of_Z x) (Uint63.of_Z y)) =? wrap (x / y))
  && (Sint63.to_Z (zmod (Uint63.of_Z x) (Uint63.of_Z y)) =? wrap (x mod y)).
Definition bad : list (Z * Z) := filter (fun p => negb (ok (fst p) (snd p))) (list_prod xs xs).
Eval vm_compute in (length (list_prod xs xs), bad).
Goal bad = []. Proof. vm_compute. reflexivity. Qed.
