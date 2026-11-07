(* lib/CInt.v -- THE INTEGER TYPES OF C, written in Rocq.  Nothing here is an operation of the machine: each is an ordinary
   function over the numbers of the system (63 bits, signed) and the u64 of KQRun.v, and the C it becomes is proved like any
   other function.

   A value of a narrow type is a number of the system in the type's range: u8 0 .. 255, i8 -128 .. 127, and so on.  Each operation
   gives back a value in the range, with C's wrap-around: u32_add a b is (a + b) mod 2^32, i32_add wraps as a C compiler's
   -fwrapv does (C itself leaves signed overflow undefined; a definition must say something, and this is what the hardware does).
   Division by zero gives what Z's does (0, and the remainder the number), the smallest number over -1 the wrap-around.
   Applied to values of the type, every operation gives a value of the type; on any other number the theorems of lib/CIntSpec.v
   say what it gives.

       u8_of u16_of u32_of i8_of i16_of i32_of   a number of the system cut to the type, as a C cast does
       <t>_add _sub _mul _div _mod _and _or _xor _not _shl _shr _ltb _leb   (the shifts take the amount modulo the width)
       rotl32 rotr32 rotl64 rotr64  bswap16 bswap32 bswap64
       popcount32 popcount64 clz32 clz64 ctz32 ctz64
       u64_mulhi                       the high half of a product (uint64_t's / and % are u64_divu, u64_modu of KQRun.v)
       i64_* over u64: two's complement in 64 bits: _add _sub _mul _div _mod _ltb _leb _shr (arithmetic)

   A program that names one of these gets this text in front of it (proved/kitc.py), as for lib/Slab.v.  `lib/CIntSpec.v` proves
   what they compute, each against Z. *)
From Stdlib Require Import Sint63.
Require Import KQ.KQRun.
Open Scope sint63_scope.

(* CINT-BEGIN *)
Definition u8_of (x : int) : int := PrimInt63.land x 255.
Definition i8_of (x : int) : int := let y := PrimInt63.land x 255 in if y <? 128 then y else y - 256.
Definition u8_add (a b : int) : int := u8_of (a + b).
Definition u8_sub (a b : int) : int := u8_of (a - b).
Definition u8_mul (a b : int) : int := u8_of (a * b).
Definition u8_and (a b : int) : int := u8_of (PrimInt63.land a b).
Definition u8_or (a b : int) : int := u8_of (PrimInt63.lor a b).
Definition u8_xor (a b : int) : int := u8_of (PrimInt63.lxor a b).
Definition u8_not (a : int) : int := u8_of (255 - a).
Definition u8_shl (a n : int) : int := u8_of (PrimInt63.lsl (u8_of a) (PrimInt63.land n 7)).
Definition i8_add (a b : int) : int := i8_of (a + b).
Definition i8_sub (a b : int) : int := i8_of (a - b).
Definition i8_mul (a b : int) : int := i8_of (a * b).
Definition i8_and (a b : int) : int := i8_of (PrimInt63.land a b).
Definition i8_or (a b : int) : int := i8_of (PrimInt63.lor a b).
Definition i8_xor (a b : int) : int := i8_of (PrimInt63.lxor a b).
Definition i8_not (a : int) : int := i8_of (255 - a).
Definition i8_shl (a n : int) : int := i8_of (PrimInt63.lsl (u8_of a) (PrimInt63.land n 7)).
Definition u8_div (a b : int) : int := PrimInt63.div a b.
Definition u8_mod (a b : int) : int := PrimInt63.mod a b.
Definition u8_ltb (a b : int) : bool := PrimInt63.ltb a b.
Definition u8_leb (a b : int) : bool := PrimInt63.leb a b.
Definition i8_ltb (a b : int) : bool := a <? b.
Definition i8_leb (a b : int) : bool := a <=? b.
Definition u8_shr (a n : int) : int := PrimInt63.lsr a (PrimInt63.land n 7).
Definition i8_div (a b : int) : int := if PrimInt63.eqb b (-1) then i8_of (0 - a) else i8_of (PrimInt63.divs a b).
Definition i8_mod (a b : int) : int := if PrimInt63.eqb b (-1) then 0 else i8_of (PrimInt63.mods a b).
Definition i8_shr (a n : int) : int := PrimInt63.asr a (PrimInt63.land n 7).
Definition u16_of (x : int) : int := PrimInt63.land x 65535.
Definition i16_of (x : int) : int := let y := PrimInt63.land x 65535 in if y <? 32768 then y else y - 65536.
Definition u16_add (a b : int) : int := u16_of (a + b).
Definition u16_sub (a b : int) : int := u16_of (a - b).
Definition u16_mul (a b : int) : int := u16_of (a * b).
Definition u16_and (a b : int) : int := u16_of (PrimInt63.land a b).
Definition u16_or (a b : int) : int := u16_of (PrimInt63.lor a b).
Definition u16_xor (a b : int) : int := u16_of (PrimInt63.lxor a b).
Definition u16_not (a : int) : int := u16_of (65535 - a).
Definition u16_shl (a n : int) : int := u16_of (PrimInt63.lsl (u16_of a) (PrimInt63.land n 15)).
Definition i16_add (a b : int) : int := i16_of (a + b).
Definition i16_sub (a b : int) : int := i16_of (a - b).
Definition i16_mul (a b : int) : int := i16_of (a * b).
Definition i16_and (a b : int) : int := i16_of (PrimInt63.land a b).
Definition i16_or (a b : int) : int := i16_of (PrimInt63.lor a b).
Definition i16_xor (a b : int) : int := i16_of (PrimInt63.lxor a b).
Definition i16_not (a : int) : int := i16_of (65535 - a).
Definition i16_shl (a n : int) : int := i16_of (PrimInt63.lsl (u16_of a) (PrimInt63.land n 15)).
Definition u16_div (a b : int) : int := PrimInt63.div a b.
Definition u16_mod (a b : int) : int := PrimInt63.mod a b.
Definition u16_ltb (a b : int) : bool := PrimInt63.ltb a b.
Definition u16_leb (a b : int) : bool := PrimInt63.leb a b.
Definition i16_ltb (a b : int) : bool := a <? b.
Definition i16_leb (a b : int) : bool := a <=? b.
Definition u16_shr (a n : int) : int := PrimInt63.lsr a (PrimInt63.land n 15).
Definition i16_div (a b : int) : int := if PrimInt63.eqb b (-1) then i16_of (0 - a) else i16_of (PrimInt63.divs a b).
Definition i16_mod (a b : int) : int := if PrimInt63.eqb b (-1) then 0 else i16_of (PrimInt63.mods a b).
Definition i16_shr (a n : int) : int := PrimInt63.asr a (PrimInt63.land n 15).
Definition u32_of (x : int) : int := PrimInt63.land x 4294967295.
Definition i32_of (x : int) : int := let y := PrimInt63.land x 4294967295 in if y <? 2147483648 then y else y - 4294967296.
Definition u32_add (a b : int) : int := u32_of (a + b).
Definition u32_sub (a b : int) : int := u32_of (a - b).
Definition u32_mul (a b : int) : int := u32_of (a * b).
Definition u32_and (a b : int) : int := u32_of (PrimInt63.land a b).
Definition u32_or (a b : int) : int := u32_of (PrimInt63.lor a b).
Definition u32_xor (a b : int) : int := u32_of (PrimInt63.lxor a b).
Definition u32_not (a : int) : int := u32_of (4294967295 - a).
Definition u32_shl (a n : int) : int := u32_of (PrimInt63.lsl (u32_of a) (PrimInt63.land n 31)).
Definition i32_add (a b : int) : int := i32_of (a + b).
Definition i32_sub (a b : int) : int := i32_of (a - b).
Definition i32_mul (a b : int) : int := i32_of (a * b).
Definition i32_and (a b : int) : int := i32_of (PrimInt63.land a b).
Definition i32_or (a b : int) : int := i32_of (PrimInt63.lor a b).
Definition i32_xor (a b : int) : int := i32_of (PrimInt63.lxor a b).
Definition i32_not (a : int) : int := i32_of (4294967295 - a).
Definition i32_shl (a n : int) : int := i32_of (PrimInt63.lsl (u32_of a) (PrimInt63.land n 31)).
Definition u32_div (a b : int) : int := PrimInt63.div a b.
Definition u32_mod (a b : int) : int := PrimInt63.mod a b.
Definition u32_ltb (a b : int) : bool := PrimInt63.ltb a b.
Definition u32_leb (a b : int) : bool := PrimInt63.leb a b.
Definition i32_ltb (a b : int) : bool := a <? b.
Definition i32_leb (a b : int) : bool := a <=? b.
Definition u32_shr (a n : int) : int := PrimInt63.lsr a (PrimInt63.land n 31).
Definition i32_div (a b : int) : int := if PrimInt63.eqb b (-1) then i32_of (0 - a) else i32_of (PrimInt63.divs a b).
Definition i32_mod (a b : int) : int := if PrimInt63.eqb b (-1) then 0 else i32_of (PrimInt63.mods a b).
Definition i32_shr (a n : int) : int := PrimInt63.asr a (PrimInt63.land n 31).
Definition rotl32 (x n : int) : int :=
  let k := PrimInt63.land n 31 in
  u32_of (PrimInt63.lor (PrimInt63.lsl (u32_of x) k) (PrimInt63.lsr (u32_of x) (PrimInt63.land (32 - k) 31))).
Definition rotr32 (x n : int) : int := rotl32 x (32 - PrimInt63.land n 31).
Definition rotl64 (x : u64) (n : int) : u64 :=
  let k := PrimInt63.land n 63 in u64_or (u64_shl x k) (u64_shr x (PrimInt63.land (64 - k) 63)).
Definition rotr64 (x : u64) (n : int) : u64 := rotl64 x (64 - PrimInt63.land n 63).
Definition bswap16 (x : int) : int :=
  PrimInt63.lor (PrimInt63.lsl (PrimInt63.land x 255) 8) (PrimInt63.land (PrimInt63.lsr x 8) 255).
Definition bswap32 (x : int) : int :=
  PrimInt63.lor (PrimInt63.lsl (bswap16 (PrimInt63.land x 65535)) 16) (bswap16 (PrimInt63.land (PrimInt63.lsr x 16) 65535)).
Definition bswap64 (x : u64) : u64 := u64_of_halves (bswap32 (u64_lo32 x)) (bswap32 (u64_hi32 x)).
(* the bits set, by the additions in parallel *)
Definition popcount32 (x0 : int) : int :=
  let x := u32_of x0 in
  let a := x - PrimInt63.land (PrimInt63.lsr x 1) 1431655765 in
  let b := PrimInt63.land a 858993459 + PrimInt63.land (PrimInt63.lsr a 2) 858993459 in
  let c := PrimInt63.land (b + PrimInt63.lsr b 4) 252645135 in
  PrimInt63.land (PrimInt63.lsr (u32_of (c * 16843009)) 24) 255.
Definition popcount64 (x : u64) : int := popcount32 (u64_lo32 x) + popcount32 (u64_hi32 x).
(* the zeros above the highest bit, below the lowest *)
Definition clz32 (x0 : int) : int := let x := u32_of x0 in if PrimInt63.eqb x 0 then 32 else PrimInt63.head0 x - 31.
Definition ctz32 (x0 : int) : int := let x := u32_of x0 in if PrimInt63.eqb x 0 then 32 else PrimInt63.tail0 x.
Definition clz64 (x : u64) : int := if PrimInt63.eqb (u64_hi32 x) 0 then 32 + clz32 (u64_lo32 x) else clz32 (u64_hi32 x).
Definition ctz64 (x : u64) : int := if PrimInt63.eqb (u64_lo32 x) 0 then 32 + ctz32 (u64_hi32 x) else ctz32 (u64_lo32 x).
Definition u64_top (r : u64) : bool := PrimInt63.eqb (PrimInt63.land (w_hi r) 1) 1.
(* the high half of a 64 by 64 product, by halves of 32 bits *)
Definition u64_mulhi (a b : u64) : u64 :=
  let al := mk_u64 (u64_lo32 a) 0 in let ah := mk_u64 (u64_hi32 a) 0 in
  let bl := mk_u64 (u64_lo32 b) 0 in let bh := mk_u64 (u64_hi32 b) 0 in
  let t := u64_mul al bl in
  let m1 := u64_add (u64_mul ah bl) (u64_shr t 32) in
  let m2 := u64_add (u64_mul al bh) (u64_and m1 (mk_u64 4294967295 0)) in
  u64_add (u64_add (u64_mul ah bh) (u64_shr m1 32)) (u64_shr m2 32).
(* int64_t: the bits of a u64, in two's complement *)
Definition i64_neg (a : u64) : bool := u64_top a.
Definition i64_add := u64_add.
Definition i64_sub := u64_sub.
Definition i64_mul := u64_mul.
Definition i64_ltb (a b : u64) : bool :=
  if i64_neg a then (if i64_neg b then u64_ltb a b else true) else (if i64_neg b then false else u64_ltb a b).
Definition i64_leb (a b : u64) : bool := negb (i64_ltb b a).
Definition i64_abs (a : u64) : u64 := if i64_neg a then u64_sub (mk_u64 0 0) a else a.
Definition i64_div (a b : u64) : u64 :=
  let q := u64_divu (i64_abs a) (i64_abs b) in
  if xorb (i64_neg a) (i64_neg b) then u64_sub (mk_u64 0 0) q else q.
Definition i64_mod (a b : u64) : u64 :=
  let r := u64_modu (i64_abs a) (i64_abs b) in
  if i64_neg a then u64_sub (mk_u64 0 0) r else r.
Definition i64_shr (a : u64) (n : int) : u64 :=
  let k := PrimInt63.land n 63 in
  if i64_neg a then u64_sub (mk_u64 (-1) 1) (u64_shr (u64_sub (mk_u64 (-1) 1) a) k) else u64_shr a k.
(* CINT-END *)
