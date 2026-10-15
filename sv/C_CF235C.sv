Definition rS := 0.

Definition rNEXT := 1.

Definition rLINK := 2.

Definition rLEN := 3.

Definition rCNT := 4.

Definition rST := 5.

Definition rBKT := 6.

Definition rORD := 7.

Definition rQ := 8.

Definition rQOFF := 9.

Definition rQLEN := 10.

Definition rVIS := 11.

Definition rANS := 12.

Definition K := 26.

Definition new_state (len : Z) (kqm : mem) : (Z) * mem :=
  (let sz := (rd rST 0 kqm) in (let kqs1 := (upd rST 0 (sz + 1) kqm) in (let kqs2 := (upd rLEN (sz + 1) len kqs1) in ((sz + 1), kqs2)))).

Fixpoint walk_set (fuel : nat) (p : Z) (c : Z) (cur : Z) (kqm : mem) : (Z) * mem :=
  (match fuel with | O => (p, kqm) | S f => (if (Z.eqb p 0) then (p, kqm) else (let q := (rd rNEXT ((p * K) + c) kqm) in (if (Z.eqb q 0) then (let kqs1 := (upd rNEXT ((p * K) + c) cur kqm) in (let l := (rd rLINK p kqs1) in (let kqp2 := (walk_set f l c cur kqs1) in ((fst kqp2), (snd kqp2))))) else (p, kqm)))) end).

Fixpoint walk_redirect (fuel : nat) (p : Z) (c : Z) (q : Z) (clone : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.eqb p 0) then kqm else (let t := (rd rNEXT ((p * K) + c) kqm) in (if (Z.eqb t q) then (let kqs1 := (upd rNEXT ((p * K) + c) clone kqm) in (let l := (rd rLINK p kqs1) in (let kqs2 := (walk_redirect f l c q clone kqs1) in kqs2))) else kqm))) end).

Fixpoint copy_next (fuel : nat) (k : Z) (src : Z) (dst : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let x := (rd rNEXT ((src * K) + k) kqm) in (let kqs1 := (upd rNEXT ((dst * K) + k) x kqm) in (let kqs2 := (copy_next f (k + 1) src dst kqs1) in kqs2))) end).

Definition extend (n2 : nat) (c : Z) (kqm : mem) : mem :=
  (let last := (rd rST 1 kqm) in (let ll := (rd rLEN last kqm) in (let kqp1 := (new_state (ll + 1) kqm) in (let kqs2 := (upd rCNT (fst kqp1) 1 (snd kqp1)) in (let kqp3 := (walk_set n2 last c (fst kqp1) kqs2) in (if (Z.eqb (fst kqp3) 0) then (let kqs4 := (upd rLINK (fst kqp1) 1 (snd kqp3)) in (let kqs5 := (upd rST 1 (fst kqp1) kqs4) in kqs5)) else (let q := (rd rNEXT (((fst kqp3) * K) + c) (snd kqp3)) in (let lp := (rd rLEN (fst kqp3) (snd kqp3)) in (let lq := (rd rLEN q (snd kqp3)) in (if (Z.eqb (lp + 1) lq) then (let kqs6 := (upd rLINK (fst kqp1) q (snd kqp3)) in (let kqs7 := (upd rST 1 (fst kqp1) kqs6) in kqs7)) else (let kqp8 := (new_state (lp + 1) (snd kqp3)) in (let kqs9 := (copy_next 26 0 q (fst kqp8) (snd kqp8)) in (let lk := (rd rLINK q kqs9) in (let kqs10 := (upd rLINK (fst kqp8) lk kqs9) in (let kqs11 := (walk_redirect n2 (fst kqp3) c q (fst kqp8) kqs10) in (let kqs12 := (upd rLINK q (fst kqp8) kqs11) in (let kqs13 := (upd rLINK (fst kqp1) (fst kqp8) kqs12) in (let kqs14 := (upd rST 1 (fst kqp1) kqs13) in kqs14)))))))))))))))))).

Fixpoint build (fuel : nat) (n2 : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let c := (rd rS i kqm) in (let kqs1 := (extend n2 c kqm) in (let kqs2 := (build f n2 (i + 1) kqs1) in kqs2))) end).

Fixpoint bucket (fuel : nat) (v : Z) (sz : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.ltb sz v) then kqm else (let l := (rd rLEN v kqm) in (let b := (rd rBKT l kqm) in (let kqs1 := (upd rBKT l (b + 1) kqm) in (let kqs2 := (bucket f (v + 1) sz kqs1) in kqs2))))) end).

Fixpoint prefix (fuel : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let a := (rd rBKT (i - 1) kqm) in (let b := (rd rBKT i kqm) in (let kqs1 := (upd rBKT i (a + b) kqm) in (let kqs2 := (prefix f (i + 1) kqs1) in kqs2)))) end).

Fixpoint place (fuel : nat) (v : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.ltb v 1) then kqm else (let l := (rd rLEN v kqm) in (let b := (rd rBKT l kqm) in (let kqs1 := (upd rBKT l (b - 1) kqm) in (let kqs2 := (upd rORD (b - 1) v kqs1) in (let kqs3 := (place f (v - 1) kqs2) in kqs3)))))) end).

Fixpoint propagate (fuel : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.ltb i 0) then kqm else (let v := (rd rORD i kqm) in (let l := (rd rLINK v kqm) in (let cv := (rd rCNT v kqm) in (let cl := (rd rCNT l kqm) in (let kqs1 := (upd rCNT l (cl + cv) kqm) in (let kqs2 := (propagate f (i - 1) kqs1) in kqs2))))))) end).

Fixpoint fall (fuel : nat) (v : Z) (c : Z) (kqm : mem) : Z :=
  (match fuel with | O => v | S f => (if (Z.eqb v 1) then v else (let q := (rd rNEXT ((v * K) + c) kqm) in (if (Z.eqb q 0) then (let l := (rd rLINK v kqm) in (let r := (fall f l c kqm) in r)) else v))) end).

Fixpoint shrink (fuel : nat) (v : Z) (m : Z) (kqm : mem) : Z :=
  (match fuel with | O => v | S f => (let lk := (rd rLINK v kqm) in (let ll := (rd rLEN lk kqm) in (if (Z.leb m ll) then (let r := (shrink f lk m kqm) in r) else v))) end).

Definition step (n2 : nat) (v : Z) (l : Z) (c : Z) (m : Z) (kqm : mem) : Z * Z :=
  (let v1 := (fall n2 v c kqm) in (let l1 := (rd rLEN v1 kqm) in (let q := (rd rNEXT ((v1 * K) + c) kqm) in (if (Z.eqb q 0) then (1, 0) else (let v2 := (shrink n2 q m kqm) in (let l2 := (rd rLEN v2 kqm) in (v2, (Z.min ((Z.min l l1) + 1) l2)))))))).

Fixpoint scan (fuel : nat) (n2 : nat) (i : Z) (v : Z) (l : Z) (off : Z) (m : Z) (qid : Z) (acc : Z) (kqm : mem) : (Z) * mem :=
  (match fuel with | O => (acc, kqm) | S f => (if (Z.leb ((2 * m) - 1) i) then (acc, kqm) else (let c := (rd rQ (off + (i mod m)) kqm) in (let vl := (step n2 v l c m kqm) in (match vl with | (v', l') => (if (Z.leb m l') then (let vs := (rd rVIS v' kqm) in (if (Z.eqb vs qid) then (let kqp1 := (scan f n2 (i + 1) v' l' off m qid acc kqm) in ((fst kqp1), (snd kqp1))) else (let kqs2 := (upd rVIS v' qid kqm) in (let k := (rd rCNT v' kqs2) in (let kqp3 := (scan f n2 (i + 1) v' l' off m qid (acc + k) kqs2) in ((fst kqp3), (snd kqp3))))))) else (let kqp4 := (scan f n2 (i + 1) v' l' off m qid acc kqm) in ((fst kqp4), (snd kqp4)))) end)))) end).

Fixpoint answer_all (fuel : nat) (n2 : nat) (mx : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let off := (rd rQOFF i kqm) in (let m := (rd rQLEN i kqm) in (let kqp1 := (scan mx n2 0 1 0 off m (i + 1) 0 kqm) in (let kqs2 := (upd rANS i (fst kqp1) (snd kqp1)) in (let kqs3 := (answer_all f n2 mx (i + 1) kqs2) in kqs3))))) end).

Definition solve (n : nat) (n2 : nat) (q : nat) (mx : nat) (kqm : mem) : mem :=
  (let kqs1 := (upd rST 0 1 kqm) in (let kqs2 := (upd rST 1 1 kqs1) in (let kqs3 := (build n n2 0 kqs2) in (let sz := (rd rST 0 kqs3) in (let kqs4 := (bucket n2 1 sz kqs3) in (let kqs5 := (prefix n 1 kqs4) in (let kqs6 := (place n2 sz kqs5) in (let kqs7 := (propagate n2 (sz - 1) kqs6) in (let kqs8 := (answer_all q n2 mx 0 kqs7) in kqs8))))))))).
