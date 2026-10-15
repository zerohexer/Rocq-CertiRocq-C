(* hw/Runtime.v -- WHAT THE RUNTIME GIVES a program that is the machine's only one (hw/kq_bare.c, hw/boot.S): no
   instruction set here either -- those are written by programs (KQRun.v: hw_run; hw/X86.v).  Linked as every declared
   routine: NAME -> kq_hw_<NAME minus hw_>, bodies in hw/kq_hw.h. *)
Require Import KQ.KQRun.
Axiom hw_irq_take  : int -> int -> mem -> mem.  (* the oldest interrupt noted (not run at once) and not taken yet: its
                                                   vector into cell i; -1 if none *)
Axiom hw_irq_info  : int -> int.                (* in a program run at an interrupt: 0 -> the vector, 1 -> the error
                                                   code, 2 -> the interrupted address; else -1 *)
Axiom hw_irq_entry : int -> int.                (* the address of the runtime's entry code for interrupt vector v *)
Axiom hw_cpu_code  : int -> int.                (* 0 -> where the code another processor starts in is, 1 -> its length *)
Axiom hw_sym       : int -> int.                (* the runtime's own addresses, for machine code a program writes
                                                   itself: 0 -> its C handler of interrupts, kq_hw_isr(vector, error
                                                   code, interrupted address); 1 -> where a second processor's C code
                                                   starts (kq_ap_main, on a stack of its own); else -1 *)
