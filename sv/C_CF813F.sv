Definition rQX := 0.

Definition rQY := 1.

Definition rKEY := 2.

Definition rIDX := 3.

Definition rTMP := 4.

Definition rNH := 5.

Definition rRU := 6.

Definition rRV := 7.

Definition rRN := 8.

Definition rST := 9.

Definition rP := 10.

Definition rRK := 11.

Definition rPX := 12.

Definition rSTA := 13.

Definition rSTB := 14.

Definition rANS := 15.

Fixpoint keys (fuel : nat) (i : Z) (nz : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let x := (rd rQX i kqm) in (let y := (rd rQY i kqm) in (let kqs1 := (upd rKEY i ((x * (nz + 1)) + y) kqm) in (let kqs2 := (upd rIDX (i - 1) i kqs1) in (let kqs3 := (keys f (i + 1) nz kqs2) in kqs3))))) end).

Fixpoint merge (fuel : nat) (i : Z) (j : Z) (k : Z) (mid : Z) (r : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.ltb mid i) then (if (Z.ltb r j) then kqm else (let x := (rd rIDX j kqm) in (let kqs1 := (upd rTMP k x kqm) in (let kqs2 := (merge f i (j + 1) (k + 1) mid r kqs1) in kqs2)))) else (if (Z.ltb r j) then (let x := (rd rIDX i kqm) in (let kqs3 := (upd rTMP k x kqm) in (let kqs4 := (merge f (i + 1) j (k + 1) mid r kqs3) in kqs4))) else (let a := (rd rIDX i kqm) in (let b := (rd rIDX j kqm) in (let ka := (rd rKEY a kqm) in (let kb := (rd rKEY b kqm) in (if (Z.leb ka kb) then (let kqs5 := (upd rTMP k a kqm) in (let kqs6 := (merge f (i + 1) j (k + 1) mid r kqs5) in kqs6)) else (let kqs7 := (upd rTMP k b kqm) in (let kqs8 := (merge f i (j + 1) (k + 1) mid r kqs7) in kqs8))))))))) end).

Fixpoint copy_back (fuel : nat) (k : Z) (r : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.ltb r k) then kqm else (let x := (rd rTMP k kqm) in (let kqs1 := (upd rIDX k x kqm) in (let kqs2 := (copy_back f (k + 1) r kqs1) in kqs2)))) end).

Fixpoint msort (h : nat) (q : nat) (l : Z) (r : Z) (kqm : mem) : mem :=
  (match h with | O => kqm | S h' => (if (Z.leb r l) then kqm else (let kqs1 := (msort h' q l ((l + r) / 2) kqm) in (let kqs2 := (msort h' q (((l + r) / 2) + 1) r kqs1) in (let kqs3 := (merge q l (((l + r) / 2) + 1) l ((l + r) / 2) r kqs2) in (let kqs4 := (copy_back q l r kqs3) in kqs4))))) end).

Definition push_rec (node : Z) (u : Z) (v : Z) (kqm : mem) : mem :=
  (let c := (rd rST 0 kqm) in (let hd := (rd rNH node kqm) in (let kqs1 := (upd rRU (c + 1) u kqm) in (let kqs2 := (upd rRV (c + 1) v kqs1) in (let kqs3 := (upd rRN (c + 1) hd kqs2) in (let kqs4 := (upd rNH node (c + 1) kqs3) in (let kqs5 := (upd rST 0 (c + 1) kqs4) in kqs5))))))).

Fixpoint add_iv (h : nat) (node : Z) (l : Z) (r : Z) (a : Z) (b : Z) (u : Z) (v : Z) (kqm : mem) : mem :=
  (match h with | O => kqm | S h' => (if (orb (Z.ltb b l) (Z.ltb r a)) then kqm else (if (andb (Z.leb a l) (Z.leb r b)) then (let kqs1 := (push_rec node u v kqm) in kqs1) else (let kqs2 := (add_iv h' (2 * node) l ((l + r) / 2) a b u v kqm) in (let kqs3 := (add_iv h' ((2 * node) + 1) (((l + r) / 2) + 1) r a b u v kqs2) in kqs3)))) end).

Fixpoint pairs (fuel : nat) (h : nat) (p : Z) (qz : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (if (Z.leb qz p) then kqm else (let t1 := (rd rIDX p kqm) in (let k1 := (rd rKEY t1 kqm) in (let x := (rd rQX t1 kqm) in (let y := (rd rQY t1 kqm) in (if (Z.ltb (p + 1) qz) then (let t2 := (rd rIDX (p + 1) kqm) in (let k2 := (rd rKEY t2 kqm) in (if (Z.eqb k1 k2) then (let kqs1 := (add_iv h 1 1 qz t1 (t2 - 1) x y kqm) in (let kqs2 := (pairs f h (p + 2) qz kqs1) in kqs2)) else (let kqs3 := (add_iv h 1 1 qz t1 qz x y kqm) in (let kqs4 := (pairs f h (p + 1) qz kqs3) in kqs4))))) else (let kqs5 := (add_iv h 1 1 qz t1 qz x y kqm) in (let kqs6 := (pairs f h (p + 1) qz kqs5) in kqs6)))))))) end).

Fixpoint init_dsu (fuel : nat) (v : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let kqs1 := (upd rP v v kqm) in (let kqs2 := (upd rRK v 0 kqs1) in (let kqs3 := (upd rPX v 0 kqs2) in (let kqs4 := (init_dsu f (v + 1) kqs3) in kqs4)))) end).

Fixpoint find (fuel : nat) (v : Z) (par : Z) (kqm : mem) : Z * Z :=
  (match fuel with | O => (v, par) | S f => (let p := (rd rP v kqm) in (if (Z.eqb p v) then (v, par) else (let x := (rd rPX v kqm) in (let r := (find f p (Z.lxor par x) kqm) in r)))) end).

Definition link (rs : Z) (rb : Z) (px : Z) (kqm : mem) : mem :=
  (let kqs1 := (upd rP rs rb kqm) in (let kqs2 := (upd rPX rs px kqs1) in (let ks := (rd rRK rs kqs2) in (let kb := (rd rRK rb kqs2) in (let t := (rd rST 1 kqs2) in (let kqs3 := (upd rSTA t rs kqs2) in (if (Z.eqb ks kb) then (let kqs4 := (upd rRK rb (kb + 1) kqs3) in (let kqs5 := (upd rSTB t 1 kqs4) in (let kqs6 := (upd rST 1 (t + 1) kqs5) in kqs6))) else (let kqs7 := (upd rSTB t 0 kqs3) in (let kqs8 := (upd rST 1 (t + 1) kqs7) in kqs8))))))))).

Definition union (fuel : nat) (u : Z) (v : Z) (kqm : mem) : (bool) * mem :=
  (let fu := (find fuel u 0 kqm) in (let fv := (find fuel v 0 kqm) in (match fu with | (ru, pu) => (match fv with | (rv, pv) => (if (Z.eqb ru rv) then ((negb (Z.eqb pu pv)), kqm) else (let ku := (rd rRK ru kqm) in (let kv := (rd rRK rv kqm) in (if (Z.ltb ku kv) then (let kqs1 := (link ru rv (Z.lxor (Z.lxor pu pv) 1) kqm) in (true, kqs1)) else (let kqs2 := (link rv ru (Z.lxor (Z.lxor pu pv) 1) kqm) in (true, kqs2)))))) end) end))).

Fixpoint rollback (fuel : nat) (mark : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let t := (rd rST 1 kqm) in (if (Z.leb t mark) then kqm else (let rs := (rd rSTA (t - 1) kqm) in (let rb := (rd rP rs kqm) in (let fl := (rd rSTB (t - 1) kqm) in (let kb := (rd rRK rb kqm) in (let kqs1 := (upd rRK rb (kb - fl) kqm) in (let kqs2 := (upd rP rs rs kqs1) in (let kqs3 := (upd rPX rs 0 kqs2) in (let kqs4 := (upd rST 1 (t - 1) kqs3) in (let kqs5 := (rollback f mark kqs4) in kqs5))))))))))) end).

Fixpoint apply (fuel : nat) (e : Z) (kqm : mem) : (bool) * mem :=
  (match fuel with | O => (true, kqm) | S f => (if (Z.eqb e 0) then (true, kqm) else (let u := (rd rRU e kqm) in (let v := (rd rRV e kqm) in (let nx := (rd rRN e kqm) in (let kqp1 := (union 40 u v kqm) in (if (fst kqp1) then (let kqp2 := (apply f nx (snd kqp1)) in ((fst kqp2), (snd kqp2))) else (false, (snd kqp1)))))))) end).

Fixpoint dfs (h : nat) (q : nat) (node : Z) (l : Z) (r : Z) (kqm : mem) : mem :=
  (match h with | O => kqm | S h' => (let mark := (rd rST 1 kqm) in (let e := (rd rNH node kqm) in (let kqp1 := (apply q e kqm) in (if (fst kqp1) then (if (Z.eqb l r) then (let kqs2 := (upd rANS l 1 (snd kqp1)) in (let kqs3 := (rollback q mark kqs2) in kqs3)) else (let kqs4 := (dfs h' q (2 * node) l ((l + r) / 2) (snd kqp1)) in (let kqs5 := (dfs h' q ((2 * node) + 1) (((l + r) / 2) + 1) r kqs4) in (let kqs6 := (rollback q mark kqs5) in kqs6)))) else (let kqs7 := (rollback q mark (snd kqp1)) in kqs7))))) end).

Definition solve (q : nat) (n : nat) (qz : Z) (nz : Z) (kqm : mem) : mem :=
  (let kqs1 := (keys q 1 nz kqm) in (let kqs2 := (msort 20 q 0 (qz - 1) kqs1) in (let kqs3 := (pairs q 20 0 qz kqs2) in (let kqs4 := (init_dsu n 1 kqs3) in (let kqs5 := (dfs 20 q 1 1 qz kqs4) in kqs5))))).
