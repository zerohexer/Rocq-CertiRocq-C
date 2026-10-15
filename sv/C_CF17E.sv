Definition rS := 0.

Definition rD1 := 1.

Definition rD2 := 2.

Definition rSD := 3.

Definition rED := 4.

Definition MOD := 51123987.

Fixpoint expand (fuel : nat) (lo : Z) (hi : Z) (nz : Z) (k : Z) (kqm : mem) : Z :=
  (match fuel with | O => k | S f => (if (orb (Z.ltb lo 0) (Z.leb nz hi)) then k else (let a := (rd rS lo kqm) in (let b := (rd rS hi kqm) in (if (Z.eqb a b) then (let r := (expand f (lo - 1) (hi + 1) nz (k + 1) kqm) in r) else k)))) end).

Definition start_odd (i : Z) (l : Z) (r : Z) (kqm : mem) : Z :=
  (if (Z.ltb r i) then 1 else (let d := (rd rD1 ((l + r) - i) kqm) in (Z.min d ((r - i) + 1)))).

Fixpoint odd (fuel : nat) (n : nat) (i : Z) (l : Z) (r : Z) (nz : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let k0 := (start_odd i l r kqm) in (let k := (expand n (i - k0) (i + k0) nz k0 kqm) in (let kqs1 := (upd rD1 i k kqm) in (if (Z.ltb r ((i + k) - 1)) then (let kqs2 := (odd f n (i + 1) ((i - k) + 1) ((i + k) - 1) nz kqs1) in kqs2) else (let kqs3 := (odd f n (i + 1) l r nz kqs1) in kqs3))))) end).

Definition start_even (i : Z) (l : Z) (r : Z) (kqm : mem) : Z :=
  (if (Z.ltb r i) then 0 else (let d := (rd rD2 (((l + r) - i) + 1) kqm) in (Z.min d ((r - i) + 1)))).

Fixpoint even (fuel : nat) (n : nat) (i : Z) (l : Z) (r : Z) (nz : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let k0 := (start_even i l r kqm) in (let k := (expand n ((i - k0) - 1) (i + k0) nz k0 kqm) in (let kqs1 := (upd rD2 i k kqm) in (if (Z.ltb r ((i + k) - 1)) then (let kqs2 := (even f n (i + 1) (i - k) ((i + k) - 1) nz kqs1) in kqs2) else (let kqs3 := (even f n (i + 1) l r nz kqs1) in kqs3))))) end).

Definition range_add (h : Z) (lo : Z) (hi : Z) (kqm : mem) : mem :=
  (let x := (rd h lo kqm) in (let kqs1 := (upd h lo (x + 1) kqm) in (let y := (rd h (hi + 1) kqs1) in (let kqs2 := (upd h (hi + 1) (y - 1) kqs1) in kqs2)))).

Fixpoint mark (fuel : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let k1 := (rd rD1 i kqm) in (let k2 := (rd rD2 i kqm) in (let kqs1 := (range_add rSD ((i - k1) + 1) i kqm) in (let kqs2 := (range_add rED i ((i + k1) - 1) kqs1) in (let kqs3 := (range_add rSD (i - k2) (i - 1) kqs2) in (let kqs4 := (range_add rED i ((i + k2) - 1) kqs3) in (let kqs5 := (mark f (i + 1) kqs4) in kqs5))))))) end).

Fixpoint tally (fuel : nat) (i : Z) (se : Z) (ee : Z) (pe : Z) (tot : Z) (non : Z) (kqm : mem) : Z * Z :=
  (match fuel with | O => (tot, non) | S f => (let ds := (rd rSD i kqm) in (let de := (rd rED i kqm) in (let r := (tally f (i + 1) (se + ds) (ee + de) (((pe + ee) + de) mod MOD) ((tot + se) + ds) ((non + (((se + ds) mod MOD) * pe)) mod MOD) kqm) in r))) end).

Definition pairs_mod (t : Z) : Z :=
  if Z.even t then (t / 2 mod MOD) * ((t - 1) mod MOD) mod MOD
  else (t mod MOD) * ((t - 1) / 2 mod MOD) mod MOD.

Definition solve (n : nat) (nz : Z) (kqm : mem) : (Z) * mem :=
  (let kqs1 := (odd n n 0 0 (-1) nz kqm) in (let kqs2 := (even n n 0 0 (-1) nz kqs1) in (let kqs3 := (mark n 0 kqs2) in (let tn := (tally n 0 0 0 0 0 0 kqs3) in ((((pairs_mod (fst tn)) - (snd tn)) mod MOD), kqs3))))).
