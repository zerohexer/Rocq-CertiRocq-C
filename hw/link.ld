/* link.ld -- the kernel at 1 MB, the Multiboot header first */
ENTRY(_start)
SECTIONS {
  . = 1M;
  .text : { *(.multiboot) *(.text*) }
  .rodata : { *(.rodata*) }
  .data : { *(.data*) }
  .bss : { *(COMMON) *(.bss*) }
  /DISCARD/ : { *(.note*) *(.comment) *(.eh_frame*) }
}
