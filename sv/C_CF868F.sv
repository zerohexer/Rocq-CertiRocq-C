Definition rA := 0.

Definition rCNT := 1.

Definition rD0 := 2.

Definition rD1 := 3.

Definition rST := 4.

Definition INF := 1000000000000000000.

Definition add (i : Z) (kqm : mem) : mem :=
  (let x := (rd rA i kqm) in (let c := (rd rCNT x kqm) in (let s := (rd rST 2 kqm) in (let kqs1 := (upd rST 2 (s + c) kqm) in (let kqs2 := (upd rCNT x (c + 1) kqs1) in kqs2))))).

Definition del (i : Z) (kqm : mem) : mem :=
  (let x := (rd rA i kqm) in (let c := (rd rCNT x kqm) in (let s := (rd rST 2 kqm) in (let kqs1 := (upd rCNT x (c - 1) kqm) in (let kqs2 := (upd rST 2 (s - (c - 1)) kqs1) in kqs2))))).

Fixpoint ext_l (fuel : nat) (l : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let cl := (rd rST 0 kqm) in (if (Z.ltb l cl) then (let kqs1 := (upd rST 0 (cl - 1) kqm) in (let kqs2 := (add (cl - 1) kqs1) in (let kqs3 := (ext_l f l kqs2) in kqs3))) else kqm)) end).

Fixpoint ext_r (fuel : nat) (r : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let cr := (rd rST 1 kqm) in (if (Z.ltb cr r) then (let kqs1 := (upd rST 1 (cr + 1) kqm) in (let kqs2 := (add (cr + 1) kqs1) in (let kqs3 := (ext_r f r kqs2) in kqs3))) else kqm)) end).

Fixpoint shr_l (fuel : nat) (l : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let cl := (rd rST 0 kqm) in (if (Z.ltb cl l) then (let kqs1 := (del cl kqm) in (let kqs2 := (upd rST 0 (cl + 1) kqs1) in (let kqs3 := (shr_l f l kqs2) in kqs3))) else kqm)) end).

Fixpoint shr_r (fuel : nat) (r : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let cr := (rd rST 1 kqm) in (if (Z.ltb r cr) then (let kqs1 := (del cr kqm) in (let kqs2 := (upd rST 1 (cr - 1) kqs1) in (let kqs3 := (shr_r f r kqs2) in kqs3))) else kqm)) end).

Definition move (fuel : nat) (l : Z) (r : Z) (kqm : mem) : mem :=
  (let kqs1 := (ext_l fuel l kqm) in (let kqs2 := (ext_r fuel r kqs1) in (let kqs3 := (shr_l fuel l kqs2) in (let kqs4 := (shr_r fuel r kqs3) in kqs4)))).

Fixpoint scan (fuel : nat) (n : nat) (p : Z) (hi : Z) (mid : Z) (hprev : Z) (best : Z) (opt : Z) (kqm : mem) : (Z * Z) * mem :=
  (match fuel with | O => ((best, opt), kqm) | S f => (if (Z.ltb hi p) then ((best, opt), kqm) else (let kqs1 := (move n p mid kqm) in (let dv := (rd hprev (p - 1) kqs1) in (let cs := (rd rST 2 kqs1) in (if (Z.ltb (dv + cs) best) then (let kqp2 := (scan f n (p + 1) hi mid hprev (dv + cs) p kqs1) in ((fst kqp2), (snd kqp2))) else (let kqp3 := (scan f n (p + 1) hi mid hprev best opt kqs1) in ((fst kqp3), (snd kqp3)))))))) end).

Fixpoint compute (h : nat) (n : nat) (l : Z) (r : Z) (optl : Z) (optr : Z) (hprev : Z) (hcur : Z) (kqm : mem) : mem :=
  (match h with | O => kqm | S h' => (if (Z.ltb r l) then kqm else (let kqp1 := (scan n n optl (Z.min ((l + r) / 2) optr) ((l + r) / 2) hprev INF (-1) kqm) in (let kqv1 := (fst kqp1) in (match kqv1 with | (best, opt) => (let kqs2 := (upd hcur ((l + r) / 2) best (snd kqp1)) in (let kqs3 := (compute h' n l (((l + r) / 2) - 1) optl opt hprev hcur kqs2) in (let kqs4 := (compute h' n (((l + r) / 2) + 1) r opt optr hprev hcur kqs3) in kqs4))) end)))) end).

Fixpoint layers (k : nat) (h : nat) (n : nat) (nz : Z) (hprev : Z) (hcur : Z) (kqm : mem) : (Z) * mem :=
  (match k with | O => (let v := (rd hprev nz kqm) in (v, kqm)) | S k' => (let kqs1 := (compute h n 1 nz 1 nz hprev hcur kqm) in (let kqs2 := (upd hcur 0 INF kqs1) in (let kqp3 := (layers k' h n nz hcur hprev kqs2) in ((fst kqp3), (snd kqp3))))) end).

Fixpoint fill_inf (fuel : nat) (i : Z) (kqm : mem) : mem :=
  (match fuel with | O => kqm | S f => (let kqs1 := (upd rD0 i INF kqm) in (let kqs2 := (fill_inf f (i + 1) kqs1) in kqs2)) end).

Definition solve (k : nat) (h : nat) (n : nat) (nz : Z) (kqm : mem) : (Z) * mem :=
  (let kqs1 := (upd rST 0 1 kqm) in (let kqs2 := (upd rST 1 0 kqs1) in (let kqs3 := (upd rST 2 0 kqs2) in (let kqs4 := (upd rD0 0 0 kqs3) in (let kqs5 := (fill_inf n 1 kqs4) in (let kqp6 := (layers k h n nz rD0 rD1 kqs5) in ((fst kqp6), (snd kqp6)))))))).
