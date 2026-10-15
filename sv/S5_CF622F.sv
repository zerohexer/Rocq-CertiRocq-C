Definition MOD := 1000000007.

Definition h0 := 0.

Definition h1 := 1.

Definition h2 := 2.

Definition h3 := 3.

Definition h4 := 4.


Fixpoint mpow (fuel : nat) (b : Z) (e : Z) (acc : Z) : Z :=
  (match fuel with
   | O => acc
   | S f => (if (e =? 0) then acc
             else (let b2 := ((b * b) mod MOD) in (let a2 := (if ((e mod 2) =? 1) then ((acc * b) mod MOD) else acc) in
                  (let r := (mpow f b2 (e / 2) a2) in r))))
   end).


Fixpoint fill_y (fuel : nat) (i : Z) (k : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let y0 := (rd h0 (i - 1) s) in (let pw := (mpow 31 i k 1) in
            (let y := ((y0 + pw) mod MOD) in (let s1 := (upd h0 i y s) in (let s2 := (fill_y f (i + 1) k s1) in s2)))))
   end).


Fixpoint fill_fact (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let a := (rd h1 (i - 1) s) in (let s1 := (upd h1 i ((a * i) mod MOD) s) in (let s2 := (fill_fact f (i + 1) s1) in s2)))
   end).


Fixpoint fill_inv (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let a := (rd h2 i s) in (let s1 := (upd h2 (i - 1) ((a * i) mod MOD) s) in (let s2 := (fill_inv f (i - 1) s1) in s2)))
   end).


Fixpoint fill_pre (fuel : nat) (i : Z) (n : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let a := (rd h3 (i - 1) s) in (let s1 := (upd h3 i ((a * ((n - (i - 1)) mod MOD)) mod MOD) s) in (let s2 := (fill_pre f (i + 1) n s1) in s2)))
   end).


Fixpoint fill_suf (fuel : nat) (i : Z) (n : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let a := (rd h4 i s) in (let s1 := (upd h4 (i - 1) ((a * ((n - i) mod MOD)) mod MOD) s) in (let s2 := (fill_suf f (i - 1) n s1) in s2)))
   end).


Fixpoint lagrange (fuel : nat) (i : Z) (m : Z) (acc : Z) (s : mem) : Z :=
  (match fuel with
   | O => acc
   | S f => (let y := (rd h0 i s) in (let pr := (rd h3 i s) in (let sf := (rd h4 i s) in (let iv := (rd h2 i s) in (let jv := (rd h2 (m - i) s) in
            (let t := (((((y * pr) mod MOD) * sf) mod MOD) * ((iv * jv) mod MOD)) in (let tm := (t mod MOD) in
            (let t1 := (if (((m - i) mod 2) =? 1) then ((MOD - tm) mod MOD) else tm) in
            (let r := (lagrange f (i + 1) m ((acc + t1) mod MOD) s) in r)))))))))
   end).


Definition solve (w : nat) (w1 : nat) (n : Z) (k : Z) (s : mem) : Z :=
  (let m := (k + 1) in (let s0 := (upd h0 0 0 s) in (let s1 := (fill_y w 1 k s0) in (let s1b := (upd h1 0 1 s1) in
  (let s2 := (fill_fact w 1 s1b) in (let fm := (rd h1 m s2) in (let iv := (mpow 31 fm (MOD - 2) 1) in (let s3 := (upd h2 m iv s2) in
  (let s4 := (fill_inv w m s3) in (let s4b := (upd h3 0 1 s4) in (let s5 := (fill_pre w 1 n s4b) in (let s5b := (upd h4 m 1 s5) in
  (let s6 := (fill_suf w m n s5b) in
  (if (n <=? m) then (rd h0 n s6) else (let r := (lagrange w1 0 m 0 s6) in r))))))))))))))).
