Definition rA := 0.

Definition rSUM := 1.

Definition rOFF := 2.

Definition rC := 3.

Definition rST := 4.

Definition rQL := 5.

Definition rQR := 6.

Definition rANS := 7.

Definition INF := 1000000000000000000.

Definition alloc (k : Z) (kqm : mem) : (Z) * mem :=
  (let t := (rd rST 0 kqm) in (let kqs1 := (upd rST 0 (t + k) kqm) in (t, kqs1))).

Fixpoint fill_inf (fuel : nat) (i : Z) (hi : Z) (off : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.ltb hi i) then kqm else (let kqs1 := (upd rC (off + i) INF kqm) in (let kqs2 := (fill_inf f (i + 1) hi off kqs1) in kqs2))) end).

Fixpoint inner (fuel : nat) (x : Z) (y : Z) (lenR : Z) (bound : Z) (add : Z) (cx : Z) (offR : Z) (offO : Z) (kqm : mem) : (Z) * mem :=
  (match fuel with | O => (y, kqm) | S f => (if (Z.ltb lenR y) then (y, kqm) else (let cy := (rd rC (offR + y) kqm) in (if (Z.ltb bound cy) then (y, kqm) else (let old := (rd rC ((offO + x) + y) kqm) in (let kqs1 := (upd rC ((offO + x) + y) (Z.min old (Z.max cx (cy + add))) kqm) in (let kqp2 := (inner f x (y + 1) lenR bound add cx offR offO kqs1) in ((fst kqp2), (snd kqp2)))))))) end).

Fixpoint outer (fuel : nat) (m : nat) (x : Z) (y : Z) (lenL : Z) (lenR : Z) (sumL : Z) (p : Z) (offL : Z) (offR : Z) (offO : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.ltb lenL x) then kqm else (let cx := (rd rC (offL + x) kqm) in (let cx1 := (rd rC ((offL + x) + 1) kqm) in (let kqp1 := (inner m x y lenR (((cx1 - 1) + sumL) - (x * p)) ((x * p) - sumL) cx offR offO kqm) in (let kqs2 := (outer f m (x + 1) ((fst kqp1) - 1) lenL lenR sumL p offL offR offO (snd kqp1)) in kqs2))))) end).

Fixpoint build (h : nat) (n : nat) (o : Z) (l : Z) (r : Z) (p : Z) (kqm : mem) : mem :=
  (match h with | O => kqm | S h' => (if (Z.eqb l r) then (let x := (rd rA l kqm) in (let kqp1 := (alloc 3 kqm) in (let kqs2 := (upd rOFF o (fst kqp1) (snd kqp1)) in (let kqs3 := (upd rSUM o x kqs2) in (let kqs4 := (upd rC (fst kqp1) (Z.opp INF) kqs3) in (let kqs5 := (upd rC ((fst kqp1) + 1) (p - x) kqs4) in (let kqs6 := (upd rC ((fst kqp1) + 2) INF kqs5) in kqs6))))))) else (let kqs7 := (build h' n (2 * o) l ((l + r) / 2) p kqm) in (let kqs8 := (build h' n ((2 * o) + 1) (((l + r) / 2) + 1) r p kqs7) in (let kqp9 := (alloc ((r - l) + 3) kqs8) in (let kqs10 := (upd rOFF o (fst kqp9) (snd kqp9)) in (let kqs11 := (upd rC (fst kqp9) (Z.opp INF) kqs10) in (let kqs12 := (fill_inf n 1 ((r - l) + 2) (fst kqp9) kqs11) in (let sl := (rd rSUM (2 * o) kqs12) in (let sr := (rd rSUM ((2 * o) + 1) kqs12) in (let kqs13 := (upd rSUM o (sl + sr) kqs12) in (let ol := (rd rOFF (2 * o) kqs13) in (let orr := (rd rOFF ((2 * o) + 1) kqs13) in (let kqs14 := (outer n n 0 0 ((((l + r) / 2) - l) + 1) (r - ((l + r) / 2)) sl p ol orr (fst kqp9) kqs13) in kqs14))))))))))))) end).

Fixpoint count_le (fuel : nat) (off : Z) (lo : Z) (hi : Z) (v : Z) (kqm : mem) : Z :=
  (match fuel with | O => lo | S f => (if (Z.ltb lo hi) then (let c := (rd rC (off + (((lo + hi) + 1) / 2)) kqm) in (if (Z.leb c v) then (let r := (count_le f off (((lo + hi) + 1) / 2) hi v kqm) in r) else (let r := (count_le f off lo ((((lo + hi) + 1) / 2) - 1) v kqm) in r))) else lo) end).

Fixpoint query (h : nat) (o : Z) (l : Z) (r : Z) (ql : Z) (qr : Z) (v : Z) (p : Z) (kqm : mem) : Z :=
  (match h with | O => v | S h' => (if (orb (Z.ltb qr l) (Z.ltb r ql)) then v else (if (andb (Z.leb ql l) (Z.leb r qr)) then (let off := (rd rOFF o kqm) in (let s := (rd rSUM o kqm) in (let k := (count_le 40 off 0 ((r - l) + 1) v kqm) in ((v + s) - (k * p))))) else (let v1 := (query h' (2 * o) l ((l + r) / 2) ql qr v p kqm) in (let v2 := (query h' ((2 * o) + 1) (((l + r) / 2) + 1) r ql qr v1 p kqm) in v2)))) end).

Fixpoint answer_all (fuel : nat) (h : nat) (i : Z) (nz : Z) (p : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let l := (rd rQL i kqm) in (let r := (rd rQR i kqm) in (let a := (query h 1 1 nz l r 0 p kqm) in (let kqs1 := (upd rANS i a kqm) in (let kqs2 := (answer_all f h (i + 1) nz p kqs1) in kqs2))))) end).

Definition solve (n : nat) (q : nat) (h : nat) (nz : Z) (p : Z) (kqm : mem) : mem :=
  (let kqs1 := (build h (S n) 1 1 nz p kqm) in (let kqs2 := (answer_all q h 0 nz p kqs1) in kqs2)).
