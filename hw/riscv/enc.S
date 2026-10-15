/* the 20 instructions of hw/riscv/Riscv.v, as assembly text: what LLVM makes of it is compared with what Rocq computes */
  .text
  csrr a0, sstatus
  csrci sstatus, 2
  csrsi sstatus, 2
  wfi
  ret
  rdtime a0
  srli a1, a0, 32
  slli a0, a0, 32
  srli a0, a0, 32
  csrr a0, stval
  sfence.vma a0, zero
  csrw stvec, a0
  slli t0, a1, 60
  srli a0, a0, 12
  or a0, a0, t0
  csrw satp, a0
  sfence.vma zero, zero
  mv a6, a3
  mv a7, a4
  ecall
