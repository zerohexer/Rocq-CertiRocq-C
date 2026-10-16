(* lib/Slab.v -- A HEAP OF OBJECTS THAT GROWS: ZER's Slab, written in Rocq like any program, on one memory block that
   grows (KQRun.v kq_grow).  A program that names a `slab_` function gets this text in front of it (compile.sh), so the
   checker and the translator read it as the program's own; proofs Require this file.

   An object has f fields of one number each.  `slab_init b f cap grow` makes block b an empty slab with room for cap
   objects; when it is full it doubles, unless grow is 0 (then it is a fixed POOL, for code that may not allocate).
   A HANDLE names an object: the block, the slot and the slot's GENERATION in one number,
       b * 2^56 + slot * 2^28 + generation          (b below 64, slot and generation below 2^28)
   A slot's generation is 0 before its first use, odd while it holds an object, even while it is free; freeing moves
   it on, so every copy of the old handle is dead from then on -- `slab_live` says so, whoever holds it -- and so is a
   handle of another slab (its block differs).  `slab_get` / `slab_set` on a handle that is not live read 0 and write
   nothing: a proof that the handles a program uses are live makes those tests always pass (lib/SlabSpec.v).

   To allocate, read the handle first, then take the slot:   let h := slab_next b s in let s := slab_take b s in ..
   (slab_next is 0 when a fixed pool is full; slab_take then does nothing).

   The block:  cell 0 room (slots), 1 slots used so far, 2 free list (1 + its first slot; 0: empty), 3 f, 4 grow;
   slot i from cell 8 + i * (f + 1): its generation, then its fields (a free slot keeps the free list's next in field 0) *)
From Stdlib Require Import Sint63.
Require Import KQ.KQRun.
Open Scope sint63_scope.
Open Scope bool_scope.

(* SLAB-BEGIN *)
Definition slab_base (f i : int) : int := 8 + i * (f + 1).
Definition slab_slot (h : int) : int := (h >> 28) land 268435455.
Definition slab_gen (h : int) : int := h land 268435455.
(* b * 2^56 + i * 2^28 + g, written as arithmetic (the C compiler makes the same shifts of it): what proofs reason about *)
Definition slab_handle (b i g : int) : int := b * 72057594037927936 + i * 268435456 + g.
Definition slab_next_gen (g : int) : int := if g + 1 =? 268435456 then 2 else g + 1.

Definition slab_init (b f cap grow : int) (s : mem) : mem :=
  let s := kq_grow b (8 + cap * (f + 1)) s in
  let s := upd b 0 cap s in
  let s := upd b 1 0 s in
  let s := upd b 2 0 s in
  let s := upd b 3 f s in
  upd b 4 grow s.

(* is h an object of the slab in block b, not freed since it was taken *)
Definition slab_live (b h : int) (s : mem) : bool :=
  let i := slab_slot h in
  let g := slab_gen h in
  (0 <=? h) && ((h >> 56) =? b) && (i <? rd b 1 s) && ((g land 1) =? 1) && (rd b (slab_base (rd b 3 s) i) s =? g).

(* the handle the next slab_take gives; 0 when a fixed pool is full *)
Definition slab_next (b : int) (s : mem) : int :=
  let fr := rd b 2 s in
  if 0 <? fr then slab_handle b (fr - 1) (slab_next_gen (rd b (slab_base (rd b 3 s) (fr - 1)) s))
  else let i := rd b 1 s in
       if (i <? rd b 0 s) || (rd b 4 s =? 1) then slab_handle b i 1 else 0.

Fixpoint slab_zero (fuel : nat) (b c k n : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S fuel => if n <=? k then s else slab_zero fuel b c (k + 1) n (upd b (c + 1 + k) 0 s)
  end.

(* takes the slot slab_next named: the first free one (its fields zeroed), else a new one -- the block doubles first
   when the slab is full and may grow *)
Definition slab_take (b : int) (s : mem) : mem :=
  let f := rd b 3 s in
  let fr := rd b 2 s in
  if 0 <? fr then
    let c := slab_base f (fr - 1) in
    let nx := rd b (c + 1) s in
    let g := slab_next_gen (rd b c s) in
    let s := upd b 2 nx s in
    let s := upd b c g s in
    slab_zero (kq_nat f) b c 0 f s
  else
    let i := rd b 1 s in
    let cap := rd b 0 s in
    if i <? cap then upd b (slab_base f i) 1 (upd b 1 (i + 1) s)
    else if rd b 4 s =? 1 then
      let ncap := 2 * cap + 1 in
      let s := kq_grow b (8 + ncap * (f + 1)) s in
      let s := upd b 0 ncap s in
      upd b (slab_base f i) 1 (upd b 1 (i + 1) s)
    else s.

(* field k of object h; 0 if h is not live or k is not one of its fields *)
Definition slab_get (b h k : int) (s : mem) : int :=
  let f := rd b 3 s in
  if slab_live b h s && (0 <=? k) && (k <? f) then rd b (slab_base f (slab_slot h) + 1 + k) s else 0.

Definition slab_set (b h k v : int) (s : mem) : mem :=
  let f := rd b 3 s in
  if slab_live b h s && (0 <=? k) && (k <? f) then upd b (slab_base f (slab_slot h) + 1 + k) v s else s.

(* object h is freed: its generation moves on and its slot goes to the front of the free list *)
Definition slab_free (b h : int) (s : mem) : mem :=
  if slab_live b h s then
    let i := slab_slot h in
    let c := slab_base (rd b 3 s) i in
    let g := slab_next_gen (rd b c s) in
    let fr := rd b 2 s in
    let s := upd b c g s in
    let s := upd b (c + 1) fr s in
    upd b 2 (i + 1) s
  else s.
(* SLAB-END *)
