Definition MOD := 1000000007.

Definition PHI := 1000000006.

Definition h0 := 0.


Fixpoint mpow (fuel : nat) (b : Z) (e : Z) (acc : Z) : Z :=
  (match fuel with
   | O => acc
   | S f => (if (e =? 0) then acc
             else (let b2 := ((b * b) mod MOD) in (let a2 := (if ((e mod 2) =? 1) then ((acc * b) mod MOD) else acc) in
                  (let r := (mpow f b2 (e / 2) a2) in r))))
   end).


Definition mc (a : Z) (b : Z) (i : Z) (j : Z) (s : mem) : Z :=
  (((((rd h0 (a + (i * 3)) s) * (rd h0 (b + j) s)) + ((rd h0 ((a + (i * 3)) + 1) s) * (rd h0 ((b + 3) + j) s)))
    + ((rd h0 ((a + (i * 3)) + 2) s) * (rd h0 ((b + 6) + j) s))) mod PHI).


Definition mmul (a : Z) (b : Z) (d : Z) (s : mem) : mem :=
  (let s0 := (upd h0 d (mc a b 0 0 s) s) in (let s1 := (upd h0 (d + 1) (mc a b 0 1 s) s0) in
  (let s2 := (upd h0 (d + 2) (mc a b 0 2 s) s1) in (let s3 := (upd h0 (d + 3) (mc a b 1 0 s) s2) in
  (let s4 := (upd h0 (d + 4) (mc a b 1 1 s) s3) in (let s5 := (upd h0 (d + 5) (mc a b 1 2 s) s4) in
  (let s6 := (upd h0 (d + 6) (mc a b 2 0 s) s5) in (let s7 := (upd h0 (d + 7) (mc a b 2 1 s) s6) in
  (let s8 := (upd h0 (d + 8) (mc a b 2 2 s) s7) in s8))))))))).


Definition mcopy (src : Z) (dst : Z) (s : mem) : mem :=
  (let s0 := (upd h0 dst (rd h0 src s) s) in (let s1 := (upd h0 (dst + 1) (rd h0 (src + 1) s) s0) in
  (let s2 := (upd h0 (dst + 2) (rd h0 (src + 2) s) s1) in (let s3 := (upd h0 (dst + 3) (rd h0 (src + 3) s) s2) in
  (let s4 := (upd h0 (dst + 4) (rd h0 (src + 4) s) s3) in (let s5 := (upd h0 (dst + 5) (rd h0 (src + 5) s) s4) in
  (let s6 := (upd h0 (dst + 6) (rd h0 (src + 6) s) s5) in (let s7 := (upd h0 (dst + 7) (rd h0 (src + 7) s) s6) in
  (let s8 := (upd h0 (dst + 8) (rd h0 (src + 8) s) s7) in s8))))))))).


Fixpoint mpowm (fuel : nat) (e : Z) (s : mem) : mem :=
  (match fuel with
   | O => s
   | S f => (if (e =? 0) then s
             else (let s1 := (if ((e mod 2) =? 1) then (let t := (mmul 9 0 18 s) in (let u := (mcopy 18 9 t) in u)) else s) in
                  (let t2 := (mmul 0 0 18 s1) in (let s2 := (mcopy 18 0 t2) in (let s3 := (mpowm f (e / 2) s2) in s3)))))
   end).


Definition init_m (s : mem) : mem :=
  (let a0 := (upd h0 0 1 s) in (let a1 := (upd h0 1 1 a0) in (let a2 := (upd h0 2 1 a1) in (let a3 := (upd h0 3 1 a2) in
  (let a4 := (upd h0 4 0 a3) in (let a5 := (upd h0 5 0 a4) in (let a6 := (upd h0 6 0 a5) in (let a7 := (upd h0 7 1 a6) in
  (let a8 := (upd h0 8 0 a7) in (let r0 := (upd h0 9 1 a8) in (let r1 := (upd h0 10 0 r0) in (let r2 := (upd h0 11 0 r1) in
  (let r3 := (upd h0 12 0 r2) in (let r4 := (upd h0 13 1 r3) in (let r5 := (upd h0 14 0 r4) in (let r6 := (upd h0 15 0 r5) in
  (let r7 := (upd h0 16 0 r6) in (let r8 := (upd h0 17 1 r7) in r8)))))))))))))))))).


Definition solve (n : Z) (f1 : Z) (f2 : Z) (f3 : Z) (c : Z) (s : mem) : Z :=
  (let s0 := (init_m s) in (let s1 := (mpowm 63 (n - 3) s0) in
  (let a := (rd h0 9 s1) in (let b := (rd h0 10 s1) in (let cc := (rd h0 11 s1) in
  (let g1 := ((c * f1) mod MOD) in (let g2 := ((((c * c) mod MOD) * f2) mod MOD) in
  (let g3 := (((((c * c) mod MOD) * c) mod MOD) * f3) in (let g3m := (g3 mod MOD) in
  (let p3 := (mpow 31 g3m a 1) in (let p2 := (mpow 31 g2 b 1) in (let p1 := (mpow 31 g1 cc 1) in
  (let gn := ((((p3 * p2) mod MOD) * p1) mod MOD) in
  (let cinv := (mpow 31 c (MOD - 2) 1) in (let pn := (mpow 63 cinv n 1) in ((gn * pn) mod MOD)))))))))))))))).
