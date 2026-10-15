(* hw/Riscv.v -- RISC-V's instructions for a kernel in supervisor mode, written in Rocq from the RISC-V manuals (Volume
   I: the base instructions and Zicsr; Volume II: the privileged architecture).  The same pattern as hw/X86.v: machine
   code put in narrow block CODE by riscv_setup, run through hw_run as a C function of the RISC-V convention
   (arguments in a0 .. a5, results in a0, a1; ret = jalr zero, 0(ra)). *)
Require Import KQ.KQRun.
Open Scope sint63_scope.
Local Notation CODE := 7.
Definition at_slot (k : int) : int := hw_addr CODE + 32 * k.
(* every RISC-V instruction is one 32-bit word, so one cell of a narrow block: word j of slot k is cell 8k + j *)
Definition put (k j w : int) (s : mem) : mem := upd32 CODE (8 * k + j) w s.
(* the formats (Volume I, chapter 2): R and I *)
Definition r_type (f7 rs2 rs1 f3 rd op : int) : int :=
  (f7 << 25) lor (rs2 << 20) lor (rs1 << 15) lor (f3 << 12) lor (rd << 7) lor op.
Definition i_type (imm rs1 f3 rd op : int) : int :=
  ((imm land 4095) << 20) lor (rs1 << 15) lor (f3 << 12) lor (rd << 7) lor op.
(* registers by number: x0 zero, x1 ra, x5 t0, x10 .. x17 a0 .. a7 *)
Local Notation ZERO := 0.
Local Notation RA := 1.
Local Notation T0 := 5.
Local Notation A0 := 10.
Local Notation A1 := 11.
Local Notation A3 := 13.
Local Notation A4 := 14.
Local Notation A6 := 16.
Local Notation A7 := 17.
(* the instructions used *)
Definition addi (rd rs1 imm : int) : int := i_type imm rs1 0 rd 0x13.
Definition slli (rd rs1 sh : int) : int := i_type sh rs1 1 rd 0x13.
Definition srli (rd rs1 sh : int) : int := i_type sh rs1 5 rd 0x13.
Definition or_r (rd rs1 rs2 : int) : int := r_type 0 rs2 rs1 6 rd 0x33.
Definition csrrw (rd csr rs1 : int) : int := i_type csr rs1 1 rd 0x73.
Definition csrrs (rd csr rs1 : int) : int := i_type csr rs1 2 rd 0x73.
Definition csrrsi (rd csr u : int) : int := i_type csr u 6 rd 0x73.
Definition csrrci (rd csr u : int) : int := i_type csr u 7 rd 0x73.
Definition RET : int := i_type 0 RA 0 ZERO 0x67.               (* jalr zero, 0(ra) *)
Definition WFI : int := r_type 8 5 0 0 0 0x73.
Definition SFENCE_VMA (rs1 rs2 : int) : int := r_type 9 rs2 rs1 0 0 0x73.
Definition ECALL : int := 0x73.
(* CSR numbers (Volume II) *)
Local Notation SSTATUS := 0x100.
Local Notation STVEC := 0x105.
Local Notation STVAL := 0x143.
Local Notation SATP := 0x180.
Local Notation TIME := 0xC01.
(* encodings checked, when this file compiles, against what the assembler (LLVM, riscv64) makes of the same text *)
Example e_csrr  : csrrs A0 SSTATUS ZERO = 0x10002573 := eq_refl.    (* csrr a0, sstatus *)
Example e_csrci : csrrci ZERO SSTATUS 2 = 0x10017073 := eq_refl.    (* csrci sstatus, 2 *)
Example e_wfi   : WFI = 0x10500073 := eq_refl.
Example e_ret   : RET = 0x00008067 := eq_refl.
Example e_sfvma : SFENCE_VMA A0 ZERO = 0x12050073 := eq_refl.       (* sfence.vma a0, zero *)
Example e_csrw  : csrrw ZERO SATP A0 = 0x18051073 := eq_refl.       (* csrw satp, a0 *)

Definition riscv_setup (s : mem) : mem :=
  let s := put 0 1 RET (put 0 0 (csrrci ZERO SSTATUS 2) s) in                   (* 0  interrupts off: SIE cleared *)
  let s := put 1 1 RET (put 1 0 (csrrsi ZERO SSTATUS 2) s) in                   (* 1  interrupts on *)
  let s := put 2 2 RET (put 2 1 (csrrsi ZERO SSTATUS 2) (put 2 0 WFI s)) in     (* 2  wait (wfi wakes even with SIE
                                                                                     off), then on: none is lost *)
  let s := put 3 0 (csrrs A0 TIME ZERO) s in                                    (* 3  rdtime a0 *)
  let s := put 3 1 (srli A1 A0 32) s in                                         (*    a1: the high half *)
  let s := put 3 2 (slli A0 A0 32) s in
  let s := put 3 3 (srli A0 A0 32) s in                                         (*    a0: the low half *)
  let s := put 3 4 RET s in
  let s := put 4 1 RET (put 4 0 (csrrs A0 STVAL ZERO) s) in                    (* 4  the address that faulted *)
  let s := put 5 1 RET (put 5 0 (SFENCE_VMA A0 ZERO) s) in                     (* 5  forget what is known of a0's page *)
  let s := put 6 1 RET (put 6 0 (csrrw ZERO STVEC A0) s) in                    (* 6  traps go to a0 *)
  let s := put 7 0 (slli T0 A1 60) s in                                         (* 7  satp := mode a1 (8: Sv39), the *)
  let s := put 7 1 (srli A0 A0 12) s in                                         (*    root's page number *)
  let s := put 7 2 (or_r A0 A0 T0) s in
  let s := put 7 3 (csrrw ZERO SATP A0) s in
  let s := put 7 4 (SFENCE_VMA ZERO ZERO) s in
  let s := put 7 5 RET s in
  let s := put 8 0 (addi A6 A3 0) s in                                          (* 8  a call to the firmware (SBI): *)
  let s := put 8 1 (addi A7 A4 0) s in                                          (*    a6 := function, a7 := extension *)
  let s := put 8 2 ECALL s in
  let s := put 8 3 RET s in
  hw_code_sync (at_slot 0) 288 s.

(* the operations, with the names hw/X86.v gives them: a program that uses only these and KQRun.v's builds for either *)
Definition hw_irq_off (s : mem) : mem := hw_run 0 (at_slot 0) 0 0 0 0 0 0 0 0 s.
Definition hw_irq_on (s : mem) : mem := hw_run 0 (at_slot 1) 0 0 0 0 0 0 0 0 s.
Definition hw_irq_wait (s : mem) : mem := hw_run 0 (at_slot 2) 0 0 0 0 0 0 0 0 s.
Definition hw_cycles (h i : int) (s : mem) : mem := hw_run 2 (at_slot 3) 0 0 0 0 0 0 h i s.
Definition hw_fault_addr (h i : int) (s : mem) : mem := hw_run 1 (at_slot 4) 0 0 0 0 0 0 h i s.
Definition hw_tlb_page (a : int) (s : mem) : mem := hw_run 0 (at_slot 5) a 0 0 0 0 0 0 0 s.
Definition hw_vectors (a lim : int) (s : mem) : mem := hw_run 0 (at_slot 6) a 0 0 0 0 0 0 0 s.
Definition hw_pt_set (a : int) (s : mem) : mem := hw_run 0 (at_slot 7) a (if a =? 0 then 0 else 8) 0 0 0 0 0 0 s.
(* RISC-V's own: the firmware's services (timer, other harts, shutdown) -- error into cell i, value into i + 1 *)
Definition hw_sbi (ext fid a0 a1 a2 h i : int) (s : mem) : mem := hw_run 2 (at_slot 8) a0 a1 a2 fid ext 0 h i s.
(* a CSR by its number, any one: the number is part of the instruction, so the routine is written for the number
   asked, then run (slot 31: a program that also does this at an interrupt keeps a slot of its own for it there) *)
Definition hw_csr_read (csr h i : int) (s : mem) : mem :=
  let s := put 31 1 RET (put 31 0 (csrrs A0 csr ZERO) s) in
  hw_run 1 (at_slot 31) 0 0 0 0 0 0 h i (hw_code_sync (at_slot 31) 8 s).
