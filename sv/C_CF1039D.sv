Definition rEU := 0.

Definition rEV := 1.

Definition rHEAD := 2.

Definition rNXT := 3.

Definition rTO := 4.

Definition rORD := 5.

Definition rPAR := 6.

Definition rT1 := 7.

Definition rT2 := 8.

Definition rANS := 9.

Definition rST := 10.

Definition add_edge (e : Z) (u : Z) (v : Z) (kqm : mem) : mem :=
  (let kqs1 := (upd rTO e v kqm) in (let h := (rd rHEAD u kqs1) in (let kqs2 := (upd rNXT e h kqs1) in (let kqs3 := (upd rHEAD u e kqs2) in kqs3)))).

Fixpoint build_adj (fuel : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let u := (rd rEU i kqm) in (let v := (rd rEV i kqm) in (let kqs1 := (add_edge ((2 * i) + 1) u v kqm) in (let kqs2 := (add_edge ((2 * i) + 2) v u kqs1) in (let kqs3 := (build_adj f (i + 1) kqs2) in kqs3))))) end).

Fixpoint visit (fuel : nat) (e : Z) (v : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.eqb e 0) then kqm else (let w := (rd rTO e kqm) in (let pv := (rd rPAR v kqm) in (let nx := (rd rNXT e kqm) in (if (Z.eqb w pv) then (let kqs1 := (visit f nx v kqm) in kqs1) else (let kqs2 := (upd rPAR w v kqm) in (let t := (rd rST 0 kqs2) in (let kqs3 := (upd rORD t w kqs2) in (let kqs4 := (upd rST 0 (t + 1) kqs3) in (let kqs5 := (visit f nx v kqs4) in kqs5)))))))))) end).

Fixpoint bfs (fuel : nat) (m : nat) (qi : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let v := (rd rORD qi kqm) in (let e := (rd rHEAD v kqm) in (let kqs1 := (visit m e v kqm) in (let kqs2 := (bfs f m (qi + 1) kqs1) in kqs2)))) end).

Fixpoint reset (fuel : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let kqs1 := (upd rT1 i 0 kqm) in (let kqs2 := (upd rT2 i 0 kqs1) in (let kqs3 := (reset f (i + 1) kqs2) in kqs3))) end).

Definition relax (p : Z) (len : Z) (kqm : mem) : mem :=
  (let a := (rd rT1 p kqm) in (if (Z.ltb a len) then (let kqs1 := (upd rT2 p a kqm) in (let kqs2 := (upd rT1 p len kqs1) in kqs2)) else (let b := (rd rT2 p kqm) in (if (Z.ltb b len) then (let kqs3 := (upd rT2 p len kqm) in kqs3) else kqm)))).

Fixpoint sweep (fuel : nat) (i : Z) (k : Z) (cnt : Z) (kqm : mem) : Z * mem :=
  (match fuel with | O => (cnt, kqm) | S f => (let v := (rd rORD i kqm) in (let a := (rd rT1 v kqm) in (let b := (rd rT2 v kqm) in (let p := (rd rPAR v kqm) in (if (Z.leb k ((a + b) + 1)) then (let kqp1 := (sweep f (i - 1) k (cnt + 1) kqm) in ((fst kqp1), (snd kqp1))) else (let kqs2 := (relax p (a + 1) kqm) in (let kqp3 := (sweep f (i - 1) k cnt kqs2) in ((fst kqp3), (snd kqp3))))))))) end).

Definition greedy (n : nat) (nz : Z) (k : Z) (kqm : mem) : Z * mem :=
  (let kqs1 := (reset (S n) 0 kqm) in (let kqp2 := (sweep n (nz - 1) k 0 kqs1) in ((fst kqp2), (snd kqp2)))).

Fixpoint fill (fuel : nat) (i : Z) (r : Z) (a : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.ltb r i) then kqm else (let kqs1 := (upd rANS i a kqm) in (let kqs2 := (fill f (i + 1) r a kqs1) in kqs2))) end).

Fixpoint dc (h : nat) (n : nat) (nz : Z) (l : Z) (r : Z) (al : Z) (ar : Z) (kqm : mem) : mem :=
  (match h with | O => kqm | S h' => (if (Z.ltb r l) then kqm else (if (Z.eqb al ar) then (let kqs1 := (fill n l r al kqm) in kqs1) else (let kqp2 := (greedy n nz ((l + r) / 2) kqm) in (let kqs3 := (upd rANS ((l + r) / 2) (fst kqp2) (snd kqp2)) in (let kqs4 := (dc h' n nz l (((l + r) / 2) - 1) al (fst kqp2) kqs3) in (let kqs5 := (dc h' n nz (((l + r) / 2) + 1) r (fst kqp2) ar kqs4) in kqs5)))))) end).

Definition solve (n : nat) (m : nat) (nz : Z) (kqm : mem) : mem :=
  (let kqs1 := (build_adj (Nat.pred n) 0 kqm) in (let kqs2 := (upd rORD 0 1 kqs1) in (let kqs3 := (upd rPAR 1 0 kqs2) in (let kqs4 := (upd rST 0 1 kqs3) in (let kqs5 := (bfs n m 0 kqs4) in (let kqs6 := (dc 20 n nz 1 nz nz 0 kqs5) in kqs6)))))).
