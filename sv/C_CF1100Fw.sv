Definition rC := 0.

Definition rPW := 1.

Definition rBAS := 2.

Definition rPOS := 3.

Definition rQL := 4.

Definition rQR := 5.

Definition rANS := 6.

Fixpoint init_pw (fuel : nat) (b : Z) (p : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let s1 := (upd rPW b p s) in (let s2 := (init_pw f (b + 1) (p * 2) s1) in s2)) end).

Fixpoint copy_row (fuel : nat) (b : Z) (src : Z) (dst : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let x := (rd rBAS (src + b) s) in (let p := (rd rPOS (src + b) s) in (let s1 := (upd rBAS (dst + b) x s) in (let s2 := (upd rPOS (dst + b) p s1) in (let s3 := (copy_row f (b + 1) src dst s2) in s3))))) end).

Fixpoint ins (fuel : nat) (b : Z) (x : Z) (p : Z) (base : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let pw := (rd rPW b s) in (if (Z.eqb (Z.land x pw) 0) then (let s1 := (ins f (b - 1) x p base s) in s1) else (let cur := (rd rBAS (base + b) s) in (if (Z.eqb cur 0) then (let s2 := (upd rBAS (base + b) x s) in (let s3 := (upd rPOS (base + b) p s2) in s3)) else (let q := (rd rPOS (base + b) s) in (if (Z.ltb q p) then (let s4 := (upd rBAS (base + b) x s) in (let s5 := (upd rPOS (base + b) p s4) in (let s6 := (ins f (b - 1) (Z.lxor x cur) q base s5) in s6))) else (let s7 := (ins f (b - 1) (Z.lxor x cur) p base s) in s7))))))) end).

Fixpoint build (fuel : nat) (w : nat) (r : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let s1 := (copy_row w 0 ((r - 1) * 20) (r * 20) s) in (let x := (rd rC r s1) in (let s2 := (ins w 19 x r (r * 20) s1) in (let s3 := (build f w (r + 1) s2) in s3)))) end).

Fixpoint qry (fuel : nat) (b : Z) (l : Z) (base : Z) (res : Z) (s : mem) : Z :=
  (match fuel with | O => res | S f => (let p := (rd rPOS (base + b) s) in (let cur := (rd rBAS (base + b) s) in (if (andb (Z.leb l p) (Z.ltb res (Z.lxor res cur))) then (let r := (qry f (b - 1) l base (Z.lxor res cur) s) in r) else (let r := (qry f (b - 1) l base res s) in r)))) end).

Fixpoint answer_all (fuel : nat) (w : nat) (i : Z) (s : mem) : mem :=
  (match fuel with | O => s | S f => (let l := (rd rQL i s) in (let r := (rd rQR i s) in (let a := (qry w 19 l (r * 20) 0 s) in (let s1 := (upd rANS i a s) in (let s2 := (answer_all f w (i + 1) s1) in s2))))) end).

Definition solve (n : nat) (q : nat) (w : nat) (s : mem) : mem :=
  (let s1 := (init_pw w 0 1 s) in (let s2 := (build n w 1 s1) in (let s3 := (answer_all q w 0 s2) in s3))).
