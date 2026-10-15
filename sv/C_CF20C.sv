Definition rEU := 0.

Definition rEV := 1.

Definition rEW := 2.

Definition rHEAD := 3.

Definition rNXT := 4.

Definition rTO := 5.

Definition rWT := 6.

Definition rDIST := 7.

Definition rPAR := 8.

Definition rHK := 9.

Definition rHV := 10.

Definition rST := 11.

Definition rOUT := 12.

Definition INF := 1000000000000000000.

Definition add_edge (e : Z) (u : Z) (v : Z) (w : Z) (kqm : mem) : mem :=
  (let kqs1 := (upd rTO e v kqm) in (let kqs2 := (upd rWT e w kqs1) in (let h := (rd rHEAD u kqs2) in (let kqs3 := (upd rNXT e h kqs2) in (let kqs4 := (upd rHEAD u e kqs3) in kqs4))))).

Fixpoint build_adj (fuel : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let u := (rd rEU i kqm) in (let v := (rd rEV i kqm) in (let w := (rd rEW i kqm) in (let kqs1 := (add_edge ((2 * i) + 1) u v w kqm) in (let kqs2 := (add_edge ((2 * i) + 2) v u w kqs1) in (let kqs3 := (build_adj f (i + 1) kqs2) in kqs3)))))) end).

Fixpoint init_dist (fuel : nat) (v : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let kqs1 := (upd rDIST v INF kqm) in (let kqs2 := (init_dist f (v + 1) kqs1) in kqs2)) end).

Definition hswap (i : Z) (j : Z) (kqm : mem) : mem :=
  (let ki := (rd rHK i kqm) in (let vi := (rd rHV i kqm) in (let kj := (rd rHK j kqm) in (let vj := (rd rHV j kqm) in (let kqs1 := (upd rHK i kj kqm) in (let kqs2 := (upd rHV i vj kqs1) in (let kqs3 := (upd rHK j ki kqs2) in (let kqs4 := (upd rHV j vi kqs3) in kqs4)))))))).

Fixpoint sift_up (fuel : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.leb i 1) then kqm else (let ki := (rd rHK i kqm) in (let kp := (rd rHK (i / 2) kqm) in (if (Z.ltb ki kp) then (let kqs1 := (hswap i (i / 2) kqm) in (let kqs2 := (sift_up f (i / 2) kqs1) in kqs2)) else kqm)))) end).

Definition min_child (i : Z) (sz : Z) (kqm : mem) : Z :=
  (if (Z.ltb sz ((2 * i) + 1)) then (2 * i) else (let kl := (rd rHK (2 * i) kqm) in (let kr := (rd rHK ((2 * i) + 1) kqm) in (if (Z.ltb kr kl) then ((2 * i) + 1) else (2 * i))))).

Fixpoint sift_down (fuel : nat) (i : Z) (sz : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.ltb sz (2 * i)) then kqm else (let c := (min_child i sz kqm) in (let ki := (rd rHK i kqm) in (let kc := (rd rHK c kqm) in (if (Z.ltb kc ki) then (let kqs1 := (hswap i c kqm) in (let kqs2 := (sift_down f c sz kqs1) in kqs2)) else kqm))))) end).

Definition push (h : nat) (k : Z) (v : Z) (kqm : mem) : mem :=
  (let sz := (rd rST 0 kqm) in (let kqs1 := (upd rHK (sz + 1) k kqm) in (let kqs2 := (upd rHV (sz + 1) v kqs1) in (let kqs3 := (upd rST 0 (sz + 1) kqs2) in (let kqs4 := (sift_up h (sz + 1) kqs3) in kqs4))))).

Definition pop (h : nat) (kqm : mem) : (Z * Z) * mem :=
  (let sz := (rd rST 0 kqm) in (let k := (rd rHK 1 kqm) in (let v := (rd rHV 1 kqm) in (let lk := (rd rHK sz kqm) in (let lv := (rd rHV sz kqm) in (let kqs1 := (upd rHK 1 lk kqm) in (let kqs2 := (upd rHV 1 lv kqs1) in (let kqs3 := (upd rST 0 (sz - 1) kqs2) in (let kqs4 := (sift_down h 1 (sz - 1) kqs3) in ((k, v), kqs4)))))))))).

Fixpoint relax_edges (fuel : nat) (h : nat) (e : Z) (v : Z) (dv : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.eqb e 0) then kqm else (let w := (rd rTO e kqm) in (let c := (rd rWT e kqm) in (let nx := (rd rNXT e kqm) in (let dw := (rd rDIST w kqm) in (if (Z.ltb (dv + c) dw) then (let kqs1 := (upd rDIST w (dv + c) kqm) in (let kqs2 := (upd rPAR w v kqs1) in (let kqs3 := (push h (dv + c) w kqs2) in (let kqs4 := (relax_edges f h nx v dv kqs3) in kqs4)))) else (let kqs5 := (relax_edges f h nx v dv kqm) in kqs5))))))) end).

Fixpoint dijkstra (fuel : nat) (m : nat) (h : nat) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let sz := (rd rST 0 kqm) in (if (Z.eqb sz 0) then kqm else (let kqp1 := (pop h kqm) in (let kqv1 := (fst kqp1) in (match kqv1 with | (k, v) => (let dv := (rd rDIST v (snd kqp1)) in (if (Z.ltb dv k) then (let kqs2 := (dijkstra f m h (snd kqp1)) in kqs2) else (let e := (rd rHEAD v (snd kqp1)) in (let kqs3 := (relax_edges m h e v dv (snd kqp1)) in (let kqs4 := (dijkstra f m h kqs3) in kqs4))))) end))))) end).

Fixpoint trace (fuel : nat) (v : Z) (k : Z) (kqm : mem) : (Z) * mem :=
  (match fuel with | O => (k, kqm) | S f => (let kqs1 := (upd rOUT k v kqm) in (if (Z.eqb v 1) then ((k + 1), kqs1) else (let p := (rd rPAR v kqs1) in (let kqp2 := (trace f p (k + 1) kqs1) in ((fst kqp2), (snd kqp2)))))) end).

Fixpoint reverse (fuel : nat) (i : Z) (j : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.leb j i) then kqm else (let x := (rd rOUT i kqm) in (let y := (rd rOUT j kqm) in (let kqs1 := (upd rOUT i y kqm) in (let kqs2 := (upd rOUT j x kqs1) in (let kqs3 := (reverse f (i + 1) (j - 1) kqs2) in kqs3)))))) end).

Definition solve (n : nat) (m : nat) (m2 : nat) (h : nat) (nz : Z) (kqm : mem) : (Z) * mem :=
  (let kqs1 := (build_adj m 0 kqm) in (let kqs2 := (init_dist n 1 kqs1) in (let kqs3 := (upd rDIST 1 0 kqs2) in (let kqs4 := (push h 0 1 kqs3) in (let kqs5 := (dijkstra (S m2) m2 h kqs4) in (let dn := (rd rDIST nz kqs5) in (if (Z.eqb dn INF) then ((-1), kqs5) else (let kqp6 := (trace n nz 0 kqs5) in (let kqs7 := (reverse n 0 ((fst kqp6) - 1) (snd kqp6)) in ((fst kqp6), kqs7)))))))))).
