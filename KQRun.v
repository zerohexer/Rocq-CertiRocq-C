(* KQRun.v (the Codeforces harness) -- what a natively-run program gets from outside, under the names the plain-function
   surface already uses:  a memory of numbered blocks (`rd h i s`, `upd h i v s`), the numbers on the command line, and
   Z's arithmetic on machine integers (signed, 63 bits).  The memory is ONE set of C arrays written in place. *)
From Stdlib Require Export Sint63.
Open Scope sint63_scope.

Axiom mem : Type.
Axiom rd  : int -> int -> mem -> int.          (* the number in cell i of block h; 0 outside the memory *)
Axiom upd : int -> int -> int -> mem -> mem.   (* cell i of block h now holds v; nothing outside the memory *)
Axiom kq_arg : int -> int.                     (* the i-th number on the command line *)
Axiom kq_input : int -> mem.                   (* the memory the program starts with (read from a file by C) *)
Axiom kq_sum : mem -> int.                     (* a checksum of the whole memory *)
(* INPUT AND OUTPUT.  The outside world is part of what a `mem` stands for: the cells, what is left of the input, what
   has been written so far.  So the two operations are writers like `upd` -- they take a memory and give the next one,
   and the checker's rule (a memory handed on is never touched again) keeps them in the order the program says. *)
Axiom kq_in  : int -> int -> mem -> mem.       (* the next number of the input goes into cell i of block h (-1: no more) *)
Axiom kq_out : int -> mem -> mem.              (* the number v is added to the output *)
(* NARROW BLOCKS: cells of 4 bytes, as a C `int`.  A second family of blocks, numbered from 0 like the first and apart
   from it: `rd32 h i s` is the number in cell i of narrow block h (0 outside it); `upd32 h i v s` puts v there, kept
   modulo 2^32 and read back as a signed 32-bit number (-2^31 .. 2^31 - 1; nothing outside the block).  A write to a
   block of one family never changes a block of the other.  What it is for: half the bytes per number where the numbers
   fit, so twice as many in the machine's fast memory. *)
Axiom rd32  : int -> int -> mem -> int.
Axiom upd32 : int -> int -> int -> mem -> mem.
(* GROWING A BLOCK while the program runs: `kq_grow h n s` makes wide block h hold at least n cells.  The cells it had
   keep their numbers and the new ones hold 0 -- what a read outside the block gave before -- so no read changes; a
   block only grows.  For a block 0 .. 63 and n below 2^31; otherwise nothing happens.  `kq_size h s` is block h's size
   in the memory s (`kq_len h`, KQBound.v, stays the size it had when the program started).  What it is for: memory
   whose size is not known when the program starts, a heap (lib/Slab.v). *)
Axiom kq_grow : int -> int -> mem -> mem.
Axiom kq_size : int -> mem -> int.

(* BYTES AND HALFWORDS of a narrow block, laid out as the machine does (little-endian): byte i of narrow block h is byte
   (i mod 4) of cell i / 4.  A read outside the block gives 0 and a write outside it does nothing, as for the cells.  They
   are written with the cells' operations; the proved route reads them as a byte access (one load, one store). *)
Definition rd8 (h i : int) (s : mem) : int :=
  PrimInt63.land (PrimInt63.asr (rd32 h (PrimInt63.asr i 2%uint63) s) (PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63)) 255%uint63.
Definition upd8 (h i v : int) (s : mem) : mem :=
  let c := PrimInt63.asr i 2%uint63 in
  let sh := PrimInt63.mul (PrimInt63.land i 3%uint63) 8%uint63 in
  let old := rd32 h c s in
  upd32 h c (PrimInt63.add (PrimInt63.sub old (PrimInt63.lsl (PrimInt63.land (PrimInt63.asr old sh) 255%uint63) sh))
                           (PrimInt63.lsl (PrimInt63.land v 255%uint63) sh)) s.
Definition rd16 (h i : int) (s : mem) : int :=
  PrimInt63.lor (rd8 h (PrimInt63.mul i 2%uint63) s) (PrimInt63.lsl (rd8 h (PrimInt63.add (PrimInt63.mul i 2%uint63) 1%uint63) s) 8%uint63).
Definition upd16 (h i v : int) (s : mem) : mem :=
  upd8 h (PrimInt63.add (PrimInt63.mul i 2%uint63) 1%uint63) (PrimInt63.asr v 8%uint63) (upd8 h (PrimInt63.mul i 2%uint63) v s).

Definition zmin (a b : int) : int := if a <=? b then a else b.
Definition zmax (a b : int) : int := if a <=? b then b else a.
Definition zabs (a : int) : int := if a <? 0 then - a else a.
Definition zopp (a : int) : int := - a.
Definition zeven (a : int) : bool := (a land 1) =? 0.
(* Z rounds a quotient DOWN and gives the remainder the divisor's sign; the machine rounds toward 0.
   Both are COMPILED FROM THIS TEXT (the build writes them out at their uses, where the divisor is usually a number
   written in the program).  A number that is not negative, divided by one that is positive -- nearly every division
   of a program -- goes the machine's unsigned way, which needs no correction.  The two parameters are named once
   more by a `let`, so that writing the definition out computes each argument once, in the order of a call. *)
Definition zdiv (a0 b0 : int) : int :=
  let a := a0 in
  let b := b0 in
  if andb (0 <=? a) (0 <? b) then PrimInt63.div a b
  else
    let q := a / b in
    let r := a mod b in
    if r =? 0 then q
    else if r <? 0 then (if 0 <? b then q - 1 else q) else (if b <? 0 then q - 1 else q).
Definition zmod (a0 b0 : int) : int :=
  let a := a0 in
  let b := b0 in
  if andb (0 <=? a) (0 <? b) then PrimInt63.mod a b
  else
    let r := a mod b in
    if r =? 0 then r
    else if r <? 0 then (if 0 <? b then r + b else r) else (if b <? 0 then r + b else r).

(* A CHOICE BETWEEN TWO NUMBERS THAT IS NEVER A JUMP.
   In Rocq `kq_select c a b` IS `if c then a else b`.  What it says is for the machine: both numbers are worked out,
   then one is taken (a conditional move) -- there is no guess to get wrong.  For a test that goes either way (a bit of
   the data, a comparison of two unsorted numbers) this is several times faster than a jump; for a test that is nearly
   always the same way a plain `if` is faster (the machine guesses it, and the number not taken is never worked out).
   The kq_sel_* forms are the same choice with the comparison inside it (KQFast.v writes them; one comparison and one
   conditional move on the machine).
   `kq_jump c` is c: it marks a test the author wants kept as an `if` whatever a measurement says (KQFast.v).
   `kq_prof k c` is c: in a build made to measure, test number k counts how often a machine would guess it wrong. *)
Definition kq_select (c : bool) (a b : int) : int := if c then a else b.
Definition kq_sel_lts (x y a b : int) : int := if PrimInt63.ltsb x y then a else b.
Definition kq_sel_les (x y a b : int) : int := if PrimInt63.lesb x y then a else b.
Definition kq_sel_eq  (x y a b : int) : int := if PrimInt63.eqb x y then a else b.
Definition kq_sel_ltu (x y a b : int) : int := if PrimInt63.ltb x y then a else b.
Definition kq_sel_leu (x y a b : int) : int := if PrimInt63.leb x y then a else b.
(* and with the test turned round (`negb`): still one comparison and one conditional move *)
Definition kq_selectn (c : bool) (a b : int) : int := if negb c then a else b.
Definition kq_sel_ges (x y a b : int) : int := if negb (PrimInt63.ltsb x y) then a else b.
Definition kq_sel_gts (x y a b : int) : int := if negb (PrimInt63.lesb x y) then a else b.
Definition kq_sel_ne  (x y a b : int) : int := if negb (PrimInt63.eqb x y) then a else b.
Definition kq_sel_geu (x y a b : int) : int := if negb (PrimInt63.ltb x y) then a else b.
Definition kq_sel_gtu (x y a b : int) : int := if negb (PrimInt63.leb x y) then a else b.
Definition kq_jump (c : bool) : bool := c.
Definition kq_prof (k : int) (c : bool) : bool := c.

(* a loop budget from a number known only when the program runs: built once, by doubling *)
Fixpoint kq_nat_go (k : nat) (x : int) : nat :=
  match k with
  | O => O
  | S k' => if x <=? 0 then O
            else let h := kq_nat_go k' (x >> 1) in
                 if (x land 1) =? 1 then S (h + h) else (h + h)%nat
  end.
Definition kq_nat (x : int) : nat := kq_nat_go 63 x.
(* Rocq is told NOT to open `kq_nat` when it compares two programs (KQFast.v proves `main_kq = main` by having the
   kernel compare them).  A program's budget is `kq_nat (kq_arg 0)`: a number nobody knows before the run.  Opened,
   it is 63 nested tests each naming the next one twice, and comparing two of those never ends.  Computing with it
   (`vm_compute`, the tests) is not affected. *)
#[global] Strategy opaque [kq_nat].

(* `/` and `mod` MEAN Z's division and remainder, EVERYWHERE.
   Rocq reads an argument whose type is `int` in the scope bound to `int` (sint63's), whatever scope is open; there `/`
   and `mod` are the machine's (rounding toward 0).  A notation in a scope of our own is therefore not enough -- it was
   tried, and `f ((l + r) / 2)` silently used the machine's division while `let m := (l + r) / 2` used Z's.  So the two
   notations are replaced IN sint63's scope.  The machine's operations keep their names (PrimInt63.divs, .mods). *)
#[warnings="-notation-overridden"] Infix "/" := zdiv : sint63_scope.
#[warnings="-notation-overridden"] Infix "mod" := zmod : sint63_scope.
Declare Scope kq_scope.
Infix "/" := zdiv : kq_scope.
Infix "mod" := zmod : kq_scope.

(* THE MACHINE, the generic part (hw/): what C can do to hardware WITHOUT assembly, for a program with no operating
   system under it -- a kernel, a driver.  Declared only, like the memory; hw/kq_hw.h gives each a body in plain C (a
   `volatile` access, a C11 atomic, memmove ..), the same text for every processor GCC or Clang build for.  What needs
   the processor's own instructions (ports, interrupts on and off, control registers ..) is not here, and not in C
   either: a program writes those instructions itself, in Rocq, from the processor's manual, into memory, and runs
   them with hw_run (hw/X86.v: x86's, written that way).  Nothing here knows an instruction set.
   Every operation that does something takes the memory and gives it back -- devices are part of what a `mem` stands for,
   so the checker keeps them in the program's order -- and what one READS goes into a cell of a wide block (h, i).  A
   width w is a number of bytes, 1, 2, 4 or 8; a value of 8 bytes is two 32-bit halves, the low one first.  What each
   operation guarantees, a program's proofs find in KQSpec.v. *)
Axiom hw_load  : int -> int -> int -> int -> mem -> mem.        (* hw_load w a h i: the w bytes at address a (a device
                                                                   access: never merged, moved or left out), zero-
                                                                   extended, into cell i of block h; w = 8: the low half
                                                                   into cell i, the high half into cell i + 1 *)
Axiom hw_store : int -> int -> int -> mem -> mem.               (* hw_store w a v: the low 8w bits of v to address a
                                                                   (w = 1, 2, 4) *)
Axiom hw_store64 : int -> int -> int -> mem -> mem.             (* hw_store64 a lo hi: the 64 bits hi * 2^32 + lo *)
(* ATOMIC operations (C11), on memory shared with interrupt code, other processors, a device.  op: 0 add, 1 subtract,
   2 and, 3 or, 4 xor, 5 exchange.  Sequentially consistent, but for hw_aload (acquire) and hw_astore (release). *)
Axiom hw_atomic   : int -> int -> int -> int -> int -> int -> mem -> mem.       (* hw_atomic op w a v h i: [a] := [a] op v
                                                                                   (w = 1, 2, 4); the old value into cell i *)
Axiom hw_atomic64 : int -> int -> int -> int -> int -> int -> mem -> mem.       (* hw_atomic64 op a lo hi h i: the old
                                                                                   value into cells i, i + 1 *)
Axiom hw_cas      : int -> int -> int -> int -> int -> int -> mem -> mem.       (* hw_cas w a old new h i: if [a] = old
                                                                                   then [a] := new; what was found into
                                                                                   cell i, 1 (swapped) or 0 into cell i + 1 *)
Axiom hw_cas64    : int -> int -> int -> int -> int -> int -> int -> mem -> mem. (* hw_cas64 a olo ohi nlo nhi h i: found
                                                                                   into cells i, i + 1; 1 or 0 into i + 2 *)
Axiom hw_aload    : int -> int -> int -> int -> mem -> mem.     (* hw_aload w a h i: an atomic load (acquire), as hw_load *)
Axiom hw_astore   : int -> int -> int -> mem -> mem.            (* hw_astore w a v: an atomic store (release), w = 1, 2, 4 *)
Axiom hw_astore64 : int -> int -> int -> mem -> mem.            (* hw_astore64 a lo hi *)
Axiom hw_fence    : int -> mem -> mem.                          (* 0: a full fence; 1: acquire; 2: release *)
(* BYTES in bulk (C's memmove, memset, memcmp) *)
Axiom hw_copy : int -> int -> int -> mem -> mem.                (* hw_copy d src n: n bytes from src to d (they may overlap) *)
Axiom hw_fill : int -> int -> int -> mem -> mem.                (* hw_fill d b n: n bytes b at d *)
Axiom hw_cmp  : int -> int -> int -> int -> int -> mem -> mem.  (* hw_cmp x y n h i: -1, 0 or 1 into cell i, as memcmp *)
(* CODE at an address (a function pointer): a routine of the firmware, of a loader, of another program *)
Axiom hw_call : int -> int -> int -> int -> mem -> mem.         (* hw_call a x h i: the function at address a called with
                                                                   x; its result (the low 63 bits) into cell i *)
(* MACHINE CODE THE PROGRAM WRITES ITSELF: bytes computed in Rocq (an instruction's encoding, from the processor's
   manual) and put in memory -- a narrow block: its cells are 4 bytes each, at a real address (hw_addr) -- then run. *)
Axiom hw_run : int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> mem -> mem.
                                                                (* hw_run n a x0 x1 x2 x3 x4 x5 h i: the code at address a
                                                                   called as a C function of six machine words, in the
                                                                   processor family's own C calling convention (x86-64:
                                                                   x0 .. x5 in rdi rsi rdx rcx r8 r9, results rax rdx;
                                                                   RISC-V: a0 .. a5, results a0 a1; AArch64: x0 .. x5, x0
                                                                   x1); the first n (0, 1 or 2) of its two results, each
                                                                   the low 63 bits, into cells i, i + 1 *)
Axiom hw_code_sync : int -> int -> mem -> mem.                  (* hw_code_sync a n: the n bytes at a, just written, are
                                                                   what the processor runs from now on (its instruction
                                                                   cache told: nothing to do on x86; fence.i on RISC-V)
                                                                   -- before hw_run of code written or changed *)
(* a plain number, fixed for the whole run *)
Axiom hw_addr : int -> int.     (* the address of the first cell of narrow block h, on a page boundary: for what the
                                   processor or a device reads by itself -- page tables, an interrupt table, a ring of
                                   descriptors -- built in narrow blocks, whose cells are plain 32-bit numbers *)

(* 64-BIT UNSIGNED NUMBERS.  A number is 63 bits wide, so an unsigned 64-bit number is two of them: `w_lo` the low 63 bits
   and `w_hi` the bit above (read modulo 2).  The meaning is `u64_val`, a number of Z in 0 .. 2^64 - 1; every operation
   is defined by it, with the wrap-around of C's `unsigned long long`: u64_add a b is (a + b) mod 2^64.  The shifts
   take the amount modulo 64.  The comparisons give 0 or 1 in `w_lo` (u64_ltb, u64_leb, u64_eqb give booleans).  The
   proved route holds a u64 as two variables and does each operation as one 64-bit machine operation. *)
Require Import ZArith.
Set Primitive Projections.
Record u64 := mk_u64 { w_lo : int; w_hi : int }.
Unset Primitive Projections.
Definition u64_val (a : u64) : Z := Z.add (Uint63.to_Z (w_lo a)) (Z.mul (Z.pow 2%Z 63%Z) (Z.modulo (Uint63.to_Z (w_hi a)) 2%Z)).
Definition u64_of_Z (z : Z) : u64 :=
  mk_u64 (Uint63.of_Z (Z.modulo z (Z.pow 2%Z 63%Z))) (Uint63.of_Z (Z.div (Z.modulo z (Z.pow 2%Z 64%Z)) (Z.pow 2%Z 63%Z))).
Inductive w64op := W_add | W_sub | W_mul | W_and | W_or | W_xor | W_shl | W_shr | W_ltu | W_leu | W_eq.
Definition w64_z (o : w64op) (x y : Z) : Z :=
  match o with
  | W_add => Z.add x y
  | W_sub => Z.sub x y
  | W_mul => Z.mul x y
  | W_and => Z.land x y
  | W_or => Z.lor x y
  | W_xor => Z.lxor x y
  | W_shl => Z.shiftl x (Z.modulo y 64%Z)
  | W_shr => Z.shiftr x (Z.modulo y 64%Z)
  | W_ltu => if Z.ltb x y then 1%Z else 0%Z
  | W_leu => if Z.leb x y then 1%Z else 0%Z
  | W_eq => if Z.eqb x y then 1%Z else 0%Z
  end.
(* sealed: the definition sits behind a Qed, so no conversion (the kernel's included) ever works an operation out; the
   meaning is the equation w64_op_unfold *)
Lemma w64_op_ex : { f : w64op -> u64 -> u64 -> u64 | forall o a b, f o a b = u64_of_Z (w64_z o (u64_val a) (u64_val b)) }.
Proof. exists (fun o a b => u64_of_Z (w64_z o (u64_val a) (u64_val b))). intros. reflexivity. Qed.
Definition w64_op : w64op -> u64 -> u64 -> u64 := proj1_sig w64_op_ex.
Lemma w64_op_unfold : forall o a b, w64_op o a b = u64_of_Z (w64_z o (u64_val a) (u64_val b)).
Proof. exact (proj2_sig w64_op_ex). Qed.
Lemma u64_eta : forall r : u64, mk_u64 (w_lo r) (w_hi r) = r.
Proof. intros r. destruct r. reflexivity. Qed.
(* the proofs compare programs that use these operations: two uses are the same when written the same, never by working them out *)
Strategy opaque [w64_op].
Definition u64_add (a b : u64) : u64 := w64_op W_add a b.
Definition u64_sub (a b : u64) : u64 := w64_op W_sub a b.
Definition u64_mul (a b : u64) : u64 := w64_op W_mul a b.
Definition u64_and (a b : u64) : u64 := w64_op W_and a b.
Definition u64_or (a b : u64) : u64 := w64_op W_or a b.
Definition u64_xor (a b : u64) : u64 := w64_op W_xor a b.
(* shift by n bits, n taken modulo 64 *)
Definition u64_shl (a : u64) (n : int) : u64 := w64_op W_shl a (mk_u64 n 0%uint63).
Definition u64_shr (a : u64) (n : int) : u64 := w64_op W_shr a (mk_u64 n 0%uint63).
Definition u64_ltb (a b : u64) : bool := PrimInt63.eqb (w_lo (w64_op W_ltu a b)) 1%uint63.
Definition u64_leb (a b : u64) : bool := PrimInt63.eqb (w_lo (w64_op W_leu a b)) 1%uint63.
Definition u64_eqb (a b : u64) : bool := PrimInt63.eqb (w_lo (w64_op W_eq a b)) 1%uint63.
(* a number of this system (63 bits, signed) as a u64 (modulo 2^64), and the low 63 bits of a u64 back as a number *)
Definition u64_of_int (n : int) : u64 := mk_u64 n (if n <? 0 then 1 else 0).
Definition u64_to_int (a : u64) : int := w_lo a.
(* a u64 from its two 32-bit halves, and the halves back *)
Definition u64_of_halves (hi lo : int) : u64 :=
  mk_u64 (PrimInt63.lor (PrimInt63.lsl (PrimInt63.land hi 2147483647%uint63) 32%uint63) (PrimInt63.land lo 4294967295%uint63))
         (PrimInt63.lsr (PrimInt63.land hi 4294967295%uint63) 31%uint63).
Definition u64_lo32 (a : u64) : int := PrimInt63.land (w_lo a) 4294967295%uint63.
Definition u64_hi32 (a : u64) : int :=
  PrimInt63.lor (PrimInt63.lsr (w_lo a) 32%uint63) (PrimInt63.lsl (PrimInt63.land (w_hi a) 1%uint63) 31%uint63).
