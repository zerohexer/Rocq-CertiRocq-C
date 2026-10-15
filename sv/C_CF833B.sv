Definition rA := 0.

Definition rLAST := 1.

Definition rPREV := 2.

Definition rMX := 3.

Definition rLZ := 4.

Definition rD0 := 5.

Definition rD1 := 6.

Definition NEG := -1000000000000000000.

Fixpoint prevs (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let x := (rd rA i s) in (let l := (rd rLAST x s) in (let s1 := (upd rPREV i l s) in (let s2 := (upd rLAST x i s1) in (let s3 := (prevs f (i + 1) s2) in s3))))) end).

Definition pull (o : Z) (s : mem) : mem :=
  (let x := (rd rMX (2 * o) s) in (let y := (rd rMX ((2 * o) + 1) s) in (let s1 := (upd rMX o (Z.max x y) s) in s1))).

Definition apply (o : Z) (v : Z) (s : mem) : mem :=
  (let m := (rd rMX o s) in (let z := (rd rLZ o s) in (let s1 := (upd rMX o (m + v) s) in (let s2 := (upd rLZ o (z + v) s1) in s2)))).

Definition push (o : Z) (s : mem) : mem :=
  (let z := (rd rLZ o s) in (let s1 := (apply (2 * o) z s) in (let s2 := (apply ((2 * o) + 1) z s1) in (let s3 := (upd rLZ o 0 s2) in s3)))).

Fixpoint build (h : nat) (o : Z) (l : Z) (r : Z) (src : Z) (s : mem) : mem :=
  (match h with | O => s | S h' => (if (Z.eqb l r) then (let v := (rd src l s) in (let s1 := (upd rMX o v s) in (let s2 := (upd rLZ o 0 s1) in s2))) else (let s3 := (build h' (2 * o) l ((l + r) / 2) src s) in (let s4 := (build h' ((2 * o) + 1) (((l + r) / 2) + 1) r src s3) in (let s5 := (pull o s4) in (let s6 := (upd rLZ o 0 s5) in s6))))) end).

Fixpoint update (h : nat) (o : Z) (l : Z) (r : Z) (ql : Z) (qr : Z) (v : Z) (s : mem) : mem :=
  (match h with | O => s | S h' => (if (orb (Z.ltb qr l) (Z.ltb r ql)) then s else (if (andb (Z.leb ql l) (Z.leb r qr)) then (let s1 := (apply o v s) in s1) else (let s2 := (push o s) in (let s3 := (update h' (2 * o) l ((l + r) / 2) ql qr v s2) in (let s4 := (update h' ((2 * o) + 1) (((l + r) / 2) + 1) r ql qr v s3) in (let s5 := (pull o s4) in s5)))))) end).

Fixpoint qmax (h : nat) (o : Z) (l : Z) (r : Z) (ql : Z) (qr : Z) (s : mem) : Z * mem :=
  (match h with | O => (NEG, s) | S h' => (if (orb (Z.ltb qr l) (Z.ltb r ql)) then (NEG, s) else (if (andb (Z.leb ql l) (Z.leb r qr)) then (let m := (rd rMX o s) in (m, s)) else (let s1 := (push o s) in (let r2 := (qmax h' (2 * o) l ((l + r) / 2) ql qr s1) in (let r3 := (qmax h' ((2 * o) + 1) (((l + r) / 2) + 1) r ql qr (snd r2)) in ((Z.max (fst r2) (fst r3)), (snd r3))))))) end).

Fixpoint sweep (fuel : nat) (h : nat) (i : Z) (nz : Z) (hcur : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let p := (rd rPREV i s) in (let s1 := (update h 1 0 (nz - 1) p (i - 1) 1 s) in (let r2 := (qmax h 1 0 (nz - 1) 0 (i - 1) s1) in (let s3 := (upd hcur i (fst r2) (snd r2)) in (let s4 := (sweep f h (i + 1) nz hcur s3) in s4))))) end).

Fixpoint layers (k : nat) (n : nat) (h : nat) (nz : Z) (hprev : Z) (hcur : Z) (s : mem) : Z * mem :=
  (match k with | O => (let v := (rd hprev nz s) in (v, s)) | S k' => (let s1 := (build h 1 0 (nz - 1) hprev s) in (let s2 := (upd hcur 0 NEG s1) in (let s3 := (sweep n h 1 nz hcur s2) in (let r4 := (layers k' n h nz hcur hprev s3) in ((fst r4), (snd r4)))))) end).

Fixpoint fill_neg (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let s1 := (upd rD0 i NEG s) in (let s2 := (fill_neg f (i + 1) s1) in s2)) end).

Definition solve (k : nat) (n : nat) (h : nat) (nz : Z) (s : mem) : Z * mem :=
  (let s1 := (prevs n 1 s) in (let s2 := (upd rD0 0 0 s1) in (let s3 := (fill_neg n 1 s2) in (let r4 := (layers k n h nz rD0 rD1 s3) in ((fst r4), (snd r4)))))).
