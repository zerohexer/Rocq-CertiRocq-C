/* hw/kernel.S -- the kernel's OWN machine routines: declared in hw/kernel.body (Axiom asm_..), listed in hw/kernel.ext.
   Each is called as a C function (System V): a number arrives marked, as the word 2n + 1; the memory as its token.
   Give back the token, or a marked number. */
.text
.global kq_hw_asm_bswap32
kq_hw_asm_bswap32:                 /* asm_bswap32 n: the 4 low bytes of n in the other order (a pure number) */
  mov %rdi, %rax
  sar $1, %rax
  bswap %eax                       /* also clears the high half of rax */
  lea 1(%rax,%rax), %rax
  ret
.global kq_hw_asm_store32
kq_hw_asm_store32:                 /* asm_store32 a v s: the low 32 bits of v at address a; the memory goes on */
  sar $1, %rdi
  sar $1, %rsi
  movl %esi, (%rdi)
  mov %rdx, %rax
  ret
.section .note.GNU-stack,"",@progbits
