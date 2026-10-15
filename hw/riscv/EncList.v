Require Import KQ.KQRun KQ.hw.riscv.Riscv.
From Stdlib Require Import List. Import ListNotations.
Open Scope sint63_scope.
Compute [csrrs 10 0x100 0; csrrci 0 0x100 2; csrrsi 0 0x100 2; WFI; RET; csrrs 10 0xC01 0; srli 11 10 32; slli 10 10 32;
         srli 10 10 32; csrrs 10 0x143 0; SFENCE_VMA 10 0; csrrw 0 0x105 10; slli 5 11 60; srli 10 10 12; or_r 10 10 5;
         csrrw 0 0x180 10; SFENCE_VMA 0 0; addi 16 13 0; addi 17 14 0; ECALL].
