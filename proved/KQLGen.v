(** The code generator: KQL to CompCert Clight.

    A 63-bit number [n] is held in an unsigned 64-bit C variable as the word [2n + 1], the way the kit holds it:
    addition and subtraction need no mask ([a + b - 1], [a - b + 1]), the orders are C's own orders on the words,
    a shift amount or a divisor is [w >> 1].  Division by zero and over-wide shifts are guarded so the C has no
    undefined behaviour.  Variables become C temporaries (registers): source variable [x] is temporary [xO x];
    [Eloop]'s scratch temporaries are [xI _], so the two never meet.  Each function body is wrapped in [Sloop];
    [Eloop] assigns the parameters and [continue]s. *)

From Stdlib Require Import ZArith List Uint63.
From compcert Require Import Coqlib Maps Integers AST Ctypes Cop Clight.
From KQC Require Import KQL KQTArith.
Import ListNotations.

Definition tyl : type := Tlong Unsigned noattr.
Definition tyb : type := Tint I32 Signed noattr.
Definition tls : type := Tlong Signed noattr.

Definition tv (x : ident) : ident := xO x.
Definition sc (i : nat) : ident := xI (Pos.of_succ_nat i).

Definition c64 (n : Z) : expr := Econst_long (Int64.repr n) tyl.
Definition c1 : expr := c64 1.

Definition tr_atom (a : atom) : expr :=
  match a with
  | Avar x => Etempvar (tv x) tyl
  | Aint n => Econst_long (tg n) tyl
  end.

Definition bin (op : Cop.binary_operation) (a b : expr) : expr := Ebinop op a b tyl.
Definition cmpe (op : Cop.binary_operation) (a b : expr) : expr := Ebinop op a b tyb.

(** [w >> 1] (logical), the same on the signed reading, and the signed view of a word *)
Definition sh1 (e : expr) : expr := Ebinop Oshr e c1 tyl.
Definition sg (e : expr) : expr := Ecast e tls.
Definition ssh1 (e : expr) : expr := Ebinop Oshr (sg e) c1 tls.
(** [(q << 1) | 1]: the word of the number [q] *)
Definition tagup (e : expr) : expr := Ebinop Oor (Ebinop Oshl e c1 tyl) c1 tyl.

Definition tr_cmpe (c : cmpop) (A B : expr) : expr :=
  match c with
  | Ceq => cmpe Oeq A B
  | Clt => cmpe Olt A B
  | Cle => cmpe Ole A B
  | Cslt => cmpe Olt (sg A) (sg B)
  | Csle => cmpe Ole (sg A) (sg B)
  end.

(** [asr A B]: below 63 two signed shifts; from 63 on the sign; from 2^62 on (a negative shift) zero *)
Definition tr_asr (t : ident) (A B : expr) : statement :=
  Sifthenelse (cmpe Olt B (c64 127))
    (Sset t (tagup (Ebinop Oshr (ssh1 A) (sh1 B) tls)))
    (Sifthenelse (cmpe Olt B (c64 (2 ^ 63)))
       (Sset t (Ebinop Oor (Ebinop Oshr (sg A) (c64 63) tls) c1 tyl))
       (Sset t c1)).

(** the signed remainder, taken on the signed readings; a zero divisor leaves the dividend *)
Definition tr_mods (t : ident) (A B : expr) : statement :=
  Sifthenelse (cmpe Oeq B c1) (Sset t A)
    (Sset t (tagup (Ebinop Omod (ssh1 A) (ssh1 B) tls))).

Definition tr_op (x : ident) (o : binop) (A B : expr) : statement :=
  let t := tv x in
  match o with
  | Badd => Sset t (bin Osub (bin Oadd A B) c1)
  | Bsub => Sset t (bin Oadd (bin Osub A B) c1)
  | Bmul => Sset t (bin Oadd (bin Omul (bin Osub A c1) (sh1 B)) c1)
  | Bland => Sset t (bin Oand A B)
  | Blor => Sset t (bin Oor A B)
  | Blxor => Sset t (bin Oor (bin Oxor A B) c1)
  | Bdiv => Sifthenelse (cmpe Oeq B c1) (Sset t c1) (Sset t (tagup (bin Odiv (sh1 A) (sh1 B))))
  | Bmod => Sifthenelse (cmpe Oeq B c1) (Sset t A) (Sset t (tagup (bin Omod (sh1 A) (sh1 B))))
  | Blsl => Sifthenelse (cmpe Olt B (c64 127)) (Sset t (bin Oadd (bin Oshl (bin Osub A c1) (sh1 B)) c1)) (Sset t c1)
  | Blsr => Sifthenelse (cmpe Olt B (c64 127)) (Sset t (tagup (bin Oshr (sh1 A) (sh1 B)))) (Sset t c1)
  | Basr => tr_asr t A B
  | Bmods => tr_mods t A B
  end.

Fixpoint tylist (n : nat) : list type :=
  match n with O => [] | S n => tyl :: tylist n end.

Definition funty (n : nat) : type := Tfunction (tylist n) tyl cc_default.

Fixpoint set_scratch (i : nat) (args : list atom) : statement :=
  match args with
  | [] => Sskip
  | a :: l => Ssequence (Sset (sc i) (tr_atom a)) (set_scratch (S i) l)
  end.

Fixpoint set_params (i : nat) (ps : list ident) : statement :=
  match ps with
  | [] => Sskip
  | p :: l => Ssequence (Sset (tv p) (Etempvar (sc i) tyl)) (set_params (S i) l)
  end.

Definition tarr (n : Z) : type := Tarray tyl n noattr.

(** Cell [I] (a plain index) of memory block [h] (an array of [n] cells); a cell holds the word of its number. *)
Definition cell (h : ident) (n : Z) (I : expr) : expr :=
  Ederef (Ebinop Oadd (Evar h (tarr n)) I (Tpointer tyl noattr)) tyl.

(** The kit's memory: two global tables, the address of each of 64 blocks and the limit [2 * size] of each
    (both set by the loader). *)
Definition kq_tab : ident := 90000%positive.
Definition kq_lens : ident := 90001%positive.
Definition tptr : type := Tpointer tyl noattr.
Definition kq_nblocks : Z := 64.

Definition t32 : type := Tint I32 Unsigned noattr.
(** the limit of block [H] (a plain index), held as an [unsigned int] so that a store into a (long) cell cannot change it *)
Definition kld_len (H : expr) : expr :=
  Ecast (Ederef (Ebinop Oadd (Evar kq_lens (Tarray t32 kq_nblocks noattr)) H (Tpointer t32 noattr)) t32) tyl.
(** the cell of block [H] (a plain index) at the tagged number [I]: its address is the block's plus [4 * I - 4] bytes
    ([= 8 * (I >> 1)] for the word of a number), so no shift is needed *)
Definition tchar : type := Tint I8 Unsigned noattr.
Definition tcp : type := Tpointer tchar noattr.
Definition cell_off (I : expr) : expr := Ebinop Osub (Ebinop Omul I (c64 4) tyl) (c64 4) tyl.
Definition kld_base (H : expr) : expr :=
  Ederef (Ebinop Oadd (Evar kq_tab (Tarray tptr kq_nblocks noattr)) H (Tpointer tptr noattr)) tptr.
Definition kld_addr (H I : expr) : expr :=
  Ecast (Ebinop Oadd (Ecast (kld_base H) tcp) (cell_off I) tcp) tptr.
Definition kld_cell (H I : expr) : expr := Ederef (kld_addr H I) tyl.

(** [if (h < 64) { if (i < size h) then <inner> else <outer> } else <outer>] on the words [H = 2h + 1], [I = 2i + 1]:
    [H < 128], and [I < 2 * size]; [inner] indexes with [H >> 1] and [I >> 1]. *)
Definition kit_guard (H I : expr) (inner outer : statement) : statement :=
  Sifthenelse (cmpe Olt H (c64 128))
    (Sifthenelse (cmpe Olt I (kld_len (sh1 H))) inner outer)
    outer.

(** The narrow blocks (cells of 4 bytes) have two tables of their own: the address of each block, and twice its size. *)
Definition kq_tab32 : ident := 90002%positive.
Definition kq_lens32 : ident := 90003%positive.
Definition tint32 : type := Tint I32 Signed noattr.
Definition tptr32 : type := Tpointer tint32 noattr.

Definition kld_len32 (H : expr) : expr :=
  Ecast (Ederef (Ebinop Oadd (Evar kq_lens32 (Tarray t32 kq_nblocks noattr)) H (Tpointer t32 noattr)) t32) tyl.
Definition cell_off32 (I : expr) : expr := Ebinop Osub (Ebinop Omul I (c64 2) tyl) (c64 2) tyl.
Definition kld_base32 (H : expr) : expr :=
  Ederef (Ebinop Oadd (Evar kq_tab32 (Tarray tptr32 kq_nblocks noattr)) H (Tpointer tptr32 noattr)) tptr32.
Definition kld_addr32 (H I : expr) : expr :=
  Ecast (Ebinop Oadd (Ecast (kld_base32 H) tcp) (cell_off32 I) tcp) tptr32.
Definition kld_cell32 (H I : expr) : expr := Ederef (kld_addr32 H I) tint32.

Definition kit_guard32 (H I : expr) (inner outer : statement) : statement :=
  Sifthenelse (cmpe Olt H (c64 128))
    (Sifthenelse (cmpe Olt I (kld_len32 (sh1 H))) inner outer)
    outer.

Section TR.
Variable P : prog.

Fixpoint tr_exp (ps : list ident) (e : exp) : statement :=
  match e with
  | Eret a => Sreturn (Some (tr_atom a))
  | Eop x o a b k => Ssequence (tr_op x o (tr_atom a) (tr_atom b)) (tr_exp ps k)
  | Eif c a b t f =>
      Sifthenelse (tr_cmpe c (tr_atom a) (tr_atom b)) (tr_exp ps t) (tr_exp ps f)
  | Esel x c a b t f k =>
      Ssequence
        (Sifthenelse (tr_cmpe c (tr_atom a) (tr_atom b))
           (Sset (tv x) (tr_atom t)) (Sset (tv x) (tr_atom f)))
        (tr_exp ps k)
  | Ecall x g args k =>
      Ssequence (Scall (Some (tv x)) (Evar g (funty (length args))) (map tr_atom args))
                (tr_exp ps k)
  | Eload x h i k =>
      match asize P h with
      | Some n =>
          Ssequence
            (Sifthenelse (cmpe Olt (sh1 (tr_atom i)) (c64 n))
               (Sset (tv x) (cell h n (sh1 (tr_atom i)))) (Sset (tv x) c1))
            (tr_exp ps k)
      | None => Sskip
      end
  | Estore h i a k =>
      match asize P h with
      | Some n =>
          Ssequence
            (Sifthenelse (cmpe Olt (sh1 (tr_atom i)) (c64 n))
               (Sassign (cell h n (sh1 (tr_atom i))) (tr_atom a)) Sskip)
            (tr_exp ps k)
      | None => Sskip
      end
  | Ekld x h i k =>
      Ssequence
        (kit_guard (tr_atom h) (tr_atom i)
           (Sset (tv x) (kld_cell (sh1 (tr_atom h)) (tr_atom i))) (Sset (tv x) c1))
        (tr_exp ps k)
  | Ekst h i a k =>
      Ssequence
        (kit_guard (tr_atom h) (tr_atom i)
           (Sassign (kld_cell (sh1 (tr_atom h)) (tr_atom i)) (tr_atom a)) Sskip)
        (tr_exp ps k)
  | Ekld32 x h i k =>
      Ssequence
        (kit_guard32 (tr_atom h) (tr_atom i)
           (Sset (tv x) (tagup (Ecast (kld_cell32 (sh1 (tr_atom h)) (tr_atom i)) tls))) (Sset (tv x) c1))
        (tr_exp ps k)
  | Ekst32 h i a k =>
      Ssequence
        (kit_guard32 (tr_atom h) (tr_atom i)
           (Sassign (kld_cell32 (sh1 (tr_atom h)) (tr_atom i)) (Ecast (sh1 (tr_atom a)) tint32)) Sskip)
        (tr_exp ps k)
  | Eloop args => Ssequence (set_scratch 0 args) (Ssequence (set_params 0 ps) Scontinue)
  end.

Fixpoint binders (e : exp) : list ident :=
  match e with
  | Eret _ | Eloop _ => []
  | Eop x _ _ _ k | Ecall x _ _ k | Eload x _ _ k | Esel x _ _ _ _ _ k => tv x :: binders k
  | Estore _ _ _ k => binders k
  | Ekst _ _ _ k => binders k
  | Ekld x _ _ k => tv x :: binders k
  | Ekld32 x _ _ k => tv x :: binders k
  | Ekst32 _ _ _ k => binders k
  | Eif _ _ _ t f => binders t ++ binders f
  end.

Definition notin (ps : list ident) (t : ident) : bool :=
  negb (existsb (Pos.eqb t) ps).

Definition tr_fn (f : fn) : function :=
  let ps := map tv (kparams f) in
  {| fn_return := tyl;
     fn_callconv := cc_default;
     fn_params := map (fun p => (p, tyl)) ps;
     fn_vars := [];
     fn_temps := map (fun t => (t, tyl))
                   (filter (notin ps) (nodup Pos.eq_dec (binders (kbody f)))
                    ++ map sc (seq 0 (length (kparams f))));
     fn_body := Sloop (tr_exp (kparams f) (kbody f)) Sskip |}.

End TR.

Definition tr_defs (P : prog) : list (ident * globdef fundef type) :=
  map (fun gf => (fst gf, Gfun (Internal (tr_fn P (snd gf))))) (pfuns P).
