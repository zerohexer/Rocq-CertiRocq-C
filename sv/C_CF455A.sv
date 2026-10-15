Definition rA := 0.

Definition rCNT := 1.

Definition rDP := 2.

Fixpoint count (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let x := (rd rA i s) in (let c := (rd rCNT x s) in (let s1 := (upd rCNT x (c + 1) s) in (let s2 := (count f (i + 1) s1) in s2)))) end).

Fixpoint fill (fuel : nat) (x : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let c := (rd rCNT x s) in (let a := (rd rDP (x - 1) s) in (let b := (rd rDP (x - 2) s) in (let s1 := (upd rDP x (Z.max a (b + (c * x))) s) in (let s2 := (fill f (x + 1) s1) in s2))))) end).

Definition solve (n : nat) (m : nat) (mz : Z) (s : mem) : Z * mem :=
  (let s1 := (count n 0 s) in (let c1 := (rd rCNT 1 s1) in (let s2 := (upd rDP 0 0 s1) in (let s3 := (upd rDP 1 c1 s2) in (let s4 := (fill (Nat.pred m) 2 s3) in (let r := (rd rDP mz s4) in (r, s4))))))).
