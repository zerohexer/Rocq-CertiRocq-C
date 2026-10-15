Definition rA := 0.

Definition rS := 1.

Definition rH := 2.

Definition rST := 3.

Fixpoint prefix (fuel : nat) (i : Z) (acc : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let x := (rd rA i kqm) in (let kqs1 := (upd rS i (acc + x) kqm) in (let kqs2 := (prefix f (i + 1) (acc + x) kqs1) in kqs2))) end).

Fixpoint base (fuel : nat) (i : Z) (acc : Z) (kqm : mem) : Z :=
  (match fuel with | O => acc | S f => (let x := (rd rA i kqm) in (let r := (base f (i + 1) (acc + (x * i)) kqm) in r)) end).

Definition bad (i1 : Z) (i2 : Z) (i3 : Z) (kqm : mem) : bool :=
  (let s1 := (rd rS (i1 - 1) kqm) in (let s2 := (rd rS (i2 - 1) kqm) in (let s3 := (rd rS (i3 - 1) kqm) in (Z.leb ((s3 - s1) * (i2 - i1)) ((s2 - s1) * (i3 - i1)))))).

Fixpoint pop_bad (fuel : nat) (j : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let sz := (rd rST 0 kqm) in (if (Z.ltb sz 2) then kqm else (let h1 := (rd rH (sz - 2) kqm) in (let h2 := (rd rH (sz - 1) kqm) in (let b := (bad h1 h2 j kqm) in (if b then (let kqs1 := (upd rST 0 (sz - 1) kqm) in (let kqs2 := (pop_bad f j kqs1) in kqs2)) else kqm)))))) end).

Definition push (fuel : nat) (j : Z) (kqm : mem) : mem :=
  (let kqs1 := (pop_bad fuel j kqm) in (let sz := (rd rST 0 kqs1) in (let kqs2 := (upd rH sz j kqs1) in (let kqs3 := (upd rST 0 (sz + 1) kqs2) in kqs3)))).

Fixpoint build (fuel : nat) (n : nat) (j : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let kqs1 := (push n j kqm) in (let kqs2 := (build f n (j + 1) kqs1) in kqs2)) end).

Definition value (k : Z) (x : Z) (kqm : mem) : Z :=
  (let j := (rd rH k kqm) in (let s := (rd rS (j - 1) kqm) in ((j * x) - s))).

Fixpoint bsearch (fuel : nat) (lo : Z) (hi : Z) (x : Z) (kqm : mem) : Z :=
  (match fuel with | O => (let v := (value lo x kqm) in v) | S f => (if (Z.ltb lo hi) then (let v1 := (value ((lo + hi) / 2) x kqm) in (let v2 := (value (((lo + hi) / 2) + 1) x kqm) in (if (Z.leb v1 v2) then (let r := (bsearch f (((lo + hi) / 2) + 1) hi x kqm) in r) else (let r := (bsearch f lo ((lo + hi) / 2) x kqm) in r)))) else (let v := (value lo x kqm) in v)) end).

Fixpoint best (fuel : nat) (i : Z) (acc : Z) (kqm : mem) : Z :=
  (match fuel with | O => acc | S f => (let x := (rd rA i kqm) in (let sz := (rd rST 0 kqm) in (let q := (bsearch 40 0 (sz - 1) x kqm) in (let s := (rd rS (i - 1) kqm) in (let r := (best f (i + 1) (Z.max acc (q - ((x * i) - s))) kqm) in r))))) end).

Definition solve (n : nat) (kqm : mem) : Z * mem :=
  (let kqs1 := (upd rS 0 0 kqm) in (let kqs2 := (prefix n 1 0 kqs1) in (let kqs3 := (upd rST 0 0 kqs2) in (let kqs4 := (build (S n) n 1 kqs3) in (let bs := (base n 1 0 kqs4) in (let bt := (best n 1 0 kqs4) in ((bs + bt), kqs4))))))).
