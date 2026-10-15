Definition rS := 0.

Definition rT := 1.

Definition rO := 2.

Definition rC := 3.

Definition rQL := 4.

Definition rQR := 5.

Definition rANS := 6.

Definition merge (a b : Z * Z * Z) : Z * Z * Z :=
  match a, b with
  | (t1, o1, c1), (t2, o2, c2) =>
      let m := Z.min o1 c2 in (t1 + t2 + 2 * m, o1 + o2 - m, c1 + c2 - m)
  end.

Definition leaf (ch : Z) : Z * Z * Z := if Z.eqb ch 1 then (0, 1, 0) else (0, 0, 1).

Definition node (o : Z) (kqm : mem) : Z * Z * Z :=
  (let t := (rd rT o kqm) in (let a := (rd rO o kqm) in (let c := (rd rC o kqm) in ((t, a), c)))).

Definition put (o : Z) (x : Z * Z * Z) (kqm : mem) : mem :=
  (match x with | (kqt1, c) => (match kqt1 with | (t, a) => (let kqs1 := (upd rT o t kqm) in (let kqs2 := (upd rO o a kqs1) in (let kqs3 := (upd rC o c kqs2) in kqs3))) end) end).

Fixpoint build (h : nat) (o : Z) (l : Z) (r : Z) (kqm : mem) : mem :=
  (match h with | O => kqm | S h' => (if (Z.eqb l r) then (let ch := (rd rS l kqm) in (let kqs1 := (put o (leaf ch) kqm) in kqs1)) else (let kqs2 := (build h' (2 * o) l ((l + r) / 2) kqm) in (let kqs3 := (build h' ((2 * o) + 1) (((l + r) / 2) + 1) r kqs2) in (let x := (node (2 * o) kqs3) in (let y := (node ((2 * o) + 1) kqs3) in (let kqs4 := (put o (merge x y) kqs3) in kqs4)))))) end).

Fixpoint query (h : nat) (o : Z) (l : Z) (r : Z) (ql : Z) (qr : Z) (kqm : mem) : Z * Z * Z :=
  (match h with | O => ((0, 0), 0) | S h' => (if (orb (Z.ltb qr l) (Z.ltb r ql)) then ((0, 0), 0) else (if (andb (Z.leb ql l) (Z.leb r qr)) then (let x := (node o kqm) in x) else (let x := (query h' (2 * o) l ((l + r) / 2) ql qr kqm) in (let y := (query h' ((2 * o) + 1) (((l + r) / 2) + 1) r ql qr kqm) in (merge x y))))) end).

Fixpoint answer_all (fuel : nat) (h : nat) (i : Z) (nz : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let l := (rd rQL i kqm) in (let r := (rd rQR i kqm) in (let x := (query h 1 1 nz l r kqm) in (match x with | (kqt2, _) => (match kqt2 with | (t, _) => (let kqs1 := (upd rANS i t kqm) in (let kqs2 := (answer_all f h (i + 1) nz kqs1) in kqs2)) end) end)))) end).

Definition solve (q : nat) (h : nat) (nz : Z) (kqm : mem) : mem :=
  (let kqs1 := (build h 1 1 nz kqm) in (let kqs2 := (answer_all q h 0 nz kqs1) in kqs2)).
