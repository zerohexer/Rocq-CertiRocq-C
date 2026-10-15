Definition h0 := 0.
Definition h1 := 1.
Definition h2 := 2.
Definition h3 := 3.
Definition h4 := 4.

Fixpoint fall (fuel : nat) (i : Z) (k : Z) (s : mem) : Z :=
  (match fuel with
   | O => k
   | S f => (let a := (rd h0 i s) in (let b := (rd h0 k s) in
            (if (andb (0 <? k) (negb (a =? b))) then (let k2 := (rd h1 (k - 1) s) in (let r := (fall f i k2 s) in r)) else k)))
   end).

Fixpoint pi_loop (fuel : nat) (w : nat) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let k0 := (rd h1 (i - 1) s) in (let k := (fall w i k0 s) in
            (let a := (rd h0 i s) in (let b := (rd h0 k s) in
            (let k1 := (if (a =? b) then (k + 1) else k) in
            (let s1 := (upd h1 i k1 s) in (let s2 := (pi_loop f w (i + 1) s1) in s2)))))))
   end).

Fixpoint cnt_init (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let s1 := (upd h2 i 1 s) in (let s2 := (cnt_init f (i + 1) s1) in s2))
   end).

Fixpoint cnt_push (fuel : nat) (i : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (let p := (rd h1 (i - 1) s) in
            (if (0 <? p) then (let a := (rd h2 p s) in (let b := (rd h2 i s) in (let s1 := (upd h2 p (a + b) s) in
                  (let s2 := (cnt_push f (i - 1) s1) in s2))))
             else (let s2 := (cnt_push f (i - 1) s) in s2)))
   end).

Fixpoint borders (fuel : nat) (len : Z) (k : Z) (s : mem) : Z :=
  (match fuel with
   | O => k
   | S f => (if (len =? 0) then k
             else (let c := (rd h2 len s) in (let s0 := (upd h4 k c s) in (let s1 := (upd h3 k len s0) in
                  (let nl := (rd h1 (len - 1) s1) in (let r := (borders f nl (k + 1) s1) in r))))))
   end).

Definition solve (w : nat) (w1 : nat) (n : Z) (s : mem) : Z :=
  (let s0 := (upd h1 0 0 s) in (let s1 := (pi_loop w w 1 s0) in (let s2 := (cnt_init w1 0 s1) in
  (let s3 := (cnt_push w n s2) in (let r := (borders w n 0 s3) in r))))).
