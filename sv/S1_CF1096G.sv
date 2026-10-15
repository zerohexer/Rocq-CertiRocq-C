Definition P := 998244353.
Definition NN := 1048576.
Definition h0 := 0.
Definition h1 := 1.

Fixpoint mpow (fuel : nat) (b : Z) (e : Z) (acc : Z) : Z :=
  (match fuel with
   | O => acc
   | S f => (if (e =? 0) then acc
             else (let b2 := ((b * b) mod P) in (let a2 := (if ((e mod 2) =? 1) then ((acc * b) mod P) else acc) in
                  (let r := (mpow f b2 (e / 2) a2) in r))))
   end).

Fixpoint rev20 (fuel : nat) (x : Z) (r : Z) : Z :=
  (match fuel with
   | O => r
   | S f => (let q := (rev20 f (x / 2) ((r * 2) + (x mod 2))) in q)
   end).

Fixpoint bitrev (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let j := (rev20 20 i 0) in
            (if (i <? j) then (let x := (rd h0 i s) in (let y := (rd h0 j s) in (let s1 := (upd h0 i y s) in
                  (let s2 := (upd h0 j x s1) in (let s3 := (bitrev f (i + 1) s2) in s3)))))
             else (let s3 := (bitrev f (i + 1) s) in s3)))
   end).

Fixpoint bfly (fuel : nat) (base : Z) (half : Z) (w : Z) (wlen : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let u := (rd h0 base s) in (let v := (((rd h0 (base + half) s) * w) mod P) in
            (let s1 := (upd h0 base ((u + v) mod P) s) in (let s2 := (upd h0 (base + half) (((u - v) + P) mod P) s1) in
            (let s3 := (bfly f (base + 1) half ((w * wlen) mod P) wlen s2) in s3)))))
   end).

Fixpoint blocks (fuel : nat) (w : nat) (st : Z) (len : Z) (wlen : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let s1 := (bfly w st (len / 2) 1 wlen s) in (let s2 := (blocks f w (st + len) len wlen s1) in s2))
   end).

Fixpoint stages (fuel : nat) (w : nat) (len : Z) (iv : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let g := (if (iv =? 1) then (mpow 60 3 (P - 2) 1) else 3) in
            (let wlen := (mpow 60 g ((P - 1) / len) 1) in
            (let s1 := (blocks w w 0 len wlen s) in (let s2 := (stages f w (len * 2) iv s1) in s2))))
   end).

Fixpoint scale (fuel : nat) (i : Z) (c : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let v := (((rd h0 i s) * c) mod P) in (let s1 := (upd h0 i v s) in (let s2 := (scale f (i + 1) c s1) in s2)))
   end).

Definition ntt (w : nat) (iv : Z) (s : mem) : mem :=
  (let s1 := (bitrev w 0 s) in (let s2 := (stages 20 w 2 iv s1) in s2)).

Fixpoint pow_all (fuel : nat) (i : Z) (e : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let v := (mpow 31 (rd h0 i s) e 1) in (let s1 := (upd h0 i v s) in (let s2 := (pow_all f (i + 1) e s1) in s2)))
   end).

Fixpoint set_digits (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let d := (rd h1 i s) in (let s1 := (upd h0 d 1 s) in (let s2 := (set_digits f (i + 1) s1) in s2)))
   end).

Fixpoint sum_sq (fuel : nat) (i : Z) (acc : Z) (s : mem) : Z :=
  (match fuel with
   | O => acc
   | S f => (let a := (rd h0 i s) in (let r := (sum_sq f (i + 1) ((acc + (a * a)) mod P) s) in r))
   end).

Definition solve (w : nat) (k : nat) (n : Z) (s : mem) : Z :=
  (let s1 := (set_digits k 0 s) in (let s2 := (ntt w 0 s1) in (let s3 := (pow_all w 0 (n / 2) s2) in
  (let s4 := (ntt w 1 s3) in (let inv := (mpow 60 NN (P - 2) 1) in (let s5 := (scale w 0 inv s4) in
  (let r := (sum_sq w 0 0 s5) in r))))))).
