/* boot.S -- from the boot loader to the Rocq program, and the entry code of every interrupt.  Written once.
   QEMU (-kernel) or GRUB load this file as a Multiboot kernel and start it in 32-bit mode.  It maps the first 4 GB of
   memory to itself (2 MB pages; the last GB holds devices: the local interrupt controller at 0xFEE00000), turns on 64-bit mode and the vector registers, and calls kq_bare_main (kq_bare.c).
   The 256 interrupt entries (kq_hw_stubs: their addresses, for the Rocq program's own interrupt table) each save the
   registers C may change, hand the vector, the error code and the interrupted address to kq_hw_isr, and return. */
.set MB_MAGIC, 0x1BADB002
.set MB_FLAGS, 0x00000003
.section .multiboot, "a"
.align 4
.long MB_MAGIC, MB_FLAGS, -(MB_MAGIC + MB_FLAGS)

.section .bss
.align 4096
boot_pml4: .skip 4096
boot_pdpt: .skip 4096
boot_pd:   .skip 16384
.align 16
boot_stack: .skip 262144
boot_stack_top:
ap_stack: .skip 262144
ap_stack_top:

.section .data
.align 16
gdt64:
  .quad 0
  .quad 0x00AF9A000000FFFF          /* 0x08: code, 64-bit */
  .quad 0x00CF92000000FFFF          /* 0x10: data */
gdt64_ptr:
  .word gdt64_ptr - gdt64 - 1
  .quad gdt64

.section .text
.code32
.global _start
_start:
  cli
  mov $boot_stack_top, %esp
  mov $boot_pdpt, %eax
  or $3, %eax
  mov %eax, boot_pml4
  xor %ecx, %ecx
3:
  mov %ecx, %eax
  shl $12, %eax
  add $boot_pd, %eax
  or $3, %eax
  mov %eax, boot_pdpt(,%ecx,8)
  inc %ecx
  cmp $4, %ecx
  jne 3b
  xor %ecx, %ecx
1:
  mov %ecx, %eax
  shl $21, %eax
  or $0x83, %eax
  mov %eax, boot_pd(,%ecx,8)
  movl $0, boot_pd+4(,%ecx,8)
  inc %ecx
  cmp $2048, %ecx
  jne 1b
  mov $boot_pml4, %eax
  mov %eax, %cr3
  mov %cr4, %eax
  or $0x20, %eax                    /* PAE */
  mov %eax, %cr4
  mov $0xC0000080, %ecx             /* EFER */
  rdmsr
  or $0x100, %eax                   /* long mode */
  wrmsr
  mov %cr0, %eax
  or $0x80000001, %eax              /* paging, protection */
  mov %eax, %cr0
  lgdt gdt64_ptr
  ljmp $0x08, $long_mode

.code64
long_mode:
  mov $0x10, %ax
  mov %ax, %ds
  mov %ax, %es
  mov %ax, %ss
  mov %ax, %fs
  mov %ax, %gs
  mov $boot_stack_top, %rsp
  mov %cr0, %rax                    /* the vector registers on: no emulation, monitor */
  and $~0x4, %rax
  or $0x2, %rax
  mov %rax, %cr0
  mov %cr4, %rax                    /* OSFXSR, OSXMMEXCPT */
  or $0x600, %rax
  mov %rax, %cr4
  call kq_bare_main
2:
  cli
  hlt
  jmp 2b

/* ---- ANOTHER PROCESSOR starts here, in real mode, once this code is copied to 0x8000 (32768: hw_sym 0 and 1 say where
   it is and how long) and the processor is sent INIT and STARTUP 8 through the local interrupt controller -- which the
   Rocq program does.  To protected mode with its own small table of segments, to 64-bit mode on the same page tables
   as the first processor, then kq_ap_main (kq_bare.c) on a stack of its own. */
.global kq_ap_tramp, kq_ap_tramp_end
.code16
kq_ap_tramp:
  cli
  xor %ax, %ax
  mov %ax, %ds
  lgdtl (ap_gdt_ptr - kq_ap_tramp + 0x8000)
  mov %cr0, %eax
  or $1, %eax
  mov %eax, %cr0
  ljmpl $0x08, $(ap_pm - kq_ap_tramp + 0x8000)
.code32
ap_pm:
  mov $0x10, %ax
  mov %ax, %ds
  mov %ax, %es
  mov %ax, %ss
  mov %cr4, %eax
  or $0x20, %eax
  mov %eax, %cr4
  mov $boot_pml4, %eax
  mov %eax, %cr3
  mov $0xC0000080, %ecx
  rdmsr
  or $0x100, %eax
  wrmsr
  mov %cr0, %eax
  or $0x80000000, %eax
  mov %eax, %cr0
  ljmp $0x18, $ap_lm
.align 8
ap_gdt:
  .quad 0
  .quad 0x00CF9A000000FFFF          /* 0x08: code, 32-bit */
  .quad 0x00CF92000000FFFF          /* 0x10: data */
  .quad 0x00AF9A000000FFFF          /* 0x18: code, 64-bit */
ap_gdt_ptr:
  .word ap_gdt_ptr - ap_gdt - 1
  .long ap_gdt - kq_ap_tramp + 0x8000
kq_ap_tramp_end:
.code64
ap_lm:
  mov $0x10, %ax
  mov %ax, %ds
  mov %ax, %es
  mov %ax, %ss
  mov $ap_stack_top, %rsp
  mov %cr0, %rax
  and $~0x4, %rax
  or $0x2, %rax
  mov %rax, %cr0
  mov %cr4, %rax
  or $0x600, %rax
  mov %rax, %cr4
  call kq_ap_main
4:
  cli
  hlt
  jmp 4b

/* ---- the interrupt entries.  The processor pushes an error code for vectors 8, 10-14, 17, 21, 29, 30; for the others
   a 0 is pushed here, so that every entry leaves the same frame. */
.altmacro
.macro ISR v
isr\v:
  .if (\v == 8) || ((\v >= 10) && (\v <= 14)) || (\v == 17) || (\v == 21) || (\v == 29) || (\v == 30)
  push $\v
  .else
  push $0
  push $\v
  .endif
  jmp isr_common
.endm
.set i, 0
.rept 256
  ISR %i
  .set i, i + 1
.endr

isr_common:
  push %rax
  push %rcx
  push %rdx
  push %rsi
  push %rdi
  push %r8
  push %r9
  push %r10
  push %r11
  mov 72(%rsp), %rdi                /* the vector */
  mov 80(%rsp), %rsi                /* the error code */
  mov 88(%rsp), %rdx                /* where the processor was */
  cld
  call kq_hw_isr
  pop %r11
  pop %r10
  pop %r9
  pop %r8
  pop %rdi
  pop %rsi
  pop %rdx
  pop %rcx
  pop %rax
  add $16, %rsp
  iretq

.section .data
.align 8
.global kq_hw_stubs
.macro STUBADDR v
  .quad isr\v
.endm
kq_hw_stubs:
.set i, 0
.rept 256
  STUBADDR %i
  .set i, i + 1
.endr

.section .note.GNU-stack,"",@progbits
