(* hw/User.v -- A PROGRAM'S OWN ROUTINES, for the proved route (proved/): hand-written C or assembly the program calls by
   number.  A program names them with ordinary definitions,
     Definition asm_store32 (a v : int) (s : mem) : mem := hw_user 0 a v 0 0 s.
     Definition asm_bswap32 (x : int) : int := hw_userf 0 x 0 0 0.
   and lists them in hw/NAME.ext, one per line: `NUMBER CNAME ARGUMENTS KIND` (KIND is `mem` for a routine that takes and
   gives back the memory, `pure` for one that gives a number).  The C routine is called the way the kit's operations are
   (System V convention; every number arrives as 2n + 1, the memory as its token; it gives back the token, or a number
   marked the same way).  What a routine does to the memory is what the theorem assumes of it (`hw_law`, `hwf_law`). *)
Require Import KQ.KQRun.
Axiom hw_user  : int -> int -> int -> int -> int -> mem -> mem.   (* hw_user k a b c d: the program's routine k on a b c d *)
Axiom hw_userf : int -> int -> int -> int -> int -> int.          (* hw_userf k a b c d: a routine that gives a number *)
