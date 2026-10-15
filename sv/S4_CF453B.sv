Definition INFTY := 1000000000.
Definition h0 := 0.
Definition h1 := 1.
Definition h2 := 2.
Definition h3 := 3.

Definition set_primes (s : mem) : mem :=
  (let p0 := (upd h2 0 2 s) in (let p1 := (upd h2 1 3 p0) in (let p2 := (upd h2 2 5 p1) in (let p3 := (upd h2 3 7 p2) in
  (let p4 := (upd h2 4 11 p3) in (let p5 := (upd h2 5 13 p4) in (let p6 := (upd h2 6 17 p5) in (let p7 := (upd h2 7 19 p6) in
  (let p8 := (upd h2 8 23 p7) in (let p9 := (upd h2 9 29 p8) in (let p10 := (upd h2 10 31 p9) in (let p11 := (upd h2 11 37 p10) in
  (let p12 := (upd h2 12 41 p11) in (let p13 := (upd h2 13 43 p12) in (let p14 := (upd h2 14 47 p13) in (let p15 := (upd h2 15 53 p14) in
  (let p16 := (upd h2 16 59 p15) in p16))))))))))))))))).

(* the bit j of the prime mask is carried as the number bj = 2^j: no shift is needed *)
Fixpoint pmask (fuel : nat) (b : Z) (j : Z) (bj : Z) (acc : Z) (s : mem) : Z :=
  (match fuel with
   | O => acc
   | S f => (let pj := (rd h2 j s) in
            (if ((b mod pj) =? 0) then (let r := (pmask f b (j + 1) (bj * 2) (Z.lor acc bj) s) in r)
             else (let r := (pmask f b (j + 1) (bj * 2) acc s) in r)))
   end).

Fixpoint fill_masks (fuel : nat) (b : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let m := (pmask 17 b 0 1 0 s) in (let s1 := (upd h1 b m s) in (let s2 := (fill_masks f (b + 1) s1) in s2)))
   end).

Fixpoint init_dp (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let s1 := (upd h3 i INFTY s) in (let s2 := (init_dp f (i + 1) s1) in s2))
   end).

Fixpoint trans_b (fuel : nat) (b : Z) (i : Z) (m : Z) (cur : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let mb := (rd h1 b s) in
            (if ((Z.land m mb) =? 0)
             then (let idx := (((i + 1) * 131072) + (Z.lor m mb)) in (let ai := (rd h0 i s) in
                  (let cost := (cur + (Z.abs (ai - b))) in (let old := (rd h3 idx s) in
                  (if (cost <? old) then (let s1 := (upd h3 idx cost s) in (let s2 := (trans_b f (b + 1) i m cur s1) in s2))
                   else (let s2 := (trans_b f (b + 1) i m cur s) in s2))))))
             else (let s2 := (trans_b f (b + 1) i m cur s) in s2)))
   end).

Fixpoint trans_m (fuel : nat) (m : Z) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let cur := (rd h3 ((i * 131072) + m) s) in
            (if (cur <? INFTY) then (let s1 := (trans_b 58 1 i m cur s) in (let s2 := (trans_m f (m + 1) i s1) in s2))
             else (let s2 := (trans_m f (m + 1) i s) in s2)))
   end).

Fixpoint trans_i (fuel : nat) (w : nat) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let s1 := (trans_m w 0 i s) in (let s2 := (trans_i f w (i + 1) s1) in s2))
   end).

Fixpoint best (fuel : nat) (m : Z) (n : Z) (acc : Z) (s : mem) : Z :=
  (match fuel with
   | O => acc
   | S f => (let v := (rd h3 ((n * 131072) + m) s) in (let r := (best f (m + 1) n (Z.min acc v) s) in r))
   end).

Definition solve (w : nat) (wn : nat) (nn : nat) (n : Z) (s : mem) : Z :=
  (let s0 := (set_primes s) in (let s1 := (fill_masks 58 1 s0) in (let s2 := (init_dp wn 0 s1) in
  (let s3 := (upd h3 0 0 s2) in (let s4 := (trans_i nn w 0 s3) in (let r := (best w 0 n INFTY s4) in r)))))).
