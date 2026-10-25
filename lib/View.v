(* lib/View.v -- ONE MEMORY SEEN AS BYTES, HALFWORDS, WORDS AND 64-BIT CELLS: what C does with a cast, written as functions.

   A narrow block (rd32, upd32: cells of 4 bytes) is raw memory laid out as the machine does (little-endian).  KQRun.v has
   the views of 8 bits (rd8, upd8), 16 bits (rd16, upd16) and 32 bits (rd32, upd32).  This adds the view of 64 bits, as
   the u64 of KQRun.v (cell 2 i is the low half, 2 i + 1 the high half), and a number of the system (63 bits, signed)
   stored in 8 bytes -- a handle or an address kept in a record of the raw memory:

       view_rd64 h i s     the u64 held by the 8 bytes at byte 8 i of narrow block h
       view_upd64 h i v s  the memory with v written there
       view_rdn h i s      the number held by the 8 bytes (what view_updn wrote: a number below 2^62 in size comes back as it
       view_updn h i v s   went in)

   A program that names a view_ function gets this text in front of it (compile.sh, proved/kitc.py), as for lib/Slab.v.
   A read or write outside the block does what rd32 / upd32 do there: 0, nothing.  `lib/ViewSpec.v` proves that a write of
   64 bits changes no other 32-bit or wide cell (view_upd64_frame, view_upd64_rd) and that the u64 read back from a cell
   just written stands for the number written (view_rd64_upd64). *)
From Stdlib Require Import Sint63.
Require Import KQ.KQRun.
Open Scope sint63_scope.

(* VIEW-BEGIN *)
Definition view_rd64 (h i : int) (s : mem) : u64 :=
  u64_of_halves (rd32 h (2 * i + 1) s) (rd32 h (2 * i) s).
Definition view_upd64 (h i : int) (v : u64) (s : mem) : mem :=
  upd32 h (2 * i + 1) (u64_hi32 v) (upd32 h (2 * i) (u64_lo32 v) s).
Definition view_rdn (h i : int) (s : mem) : int := u64_to_int (view_rd64 h i s).
Definition view_updn (h i v : int) (s : mem) : mem := view_upd64 h i (u64_of_int v) s.
(* VIEW-END *)
