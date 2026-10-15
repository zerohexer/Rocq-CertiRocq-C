# Writing a processor's instructions in Rocq

The kit's core knows no instruction set.  A program that needs an instruction C cannot express -- interrupts on and
off, the page tables, a system register, port I/O -- writes that instruction's machine code itself: the bytes are
computed in Rocq from the processor's manual, put in memory, and called as a small function.  `hw/X86.v` does this for
every x86-64 instruction the test kernels use.  It is an ordinary file a user could have written; another processor is
another file like it, from that processor's manual.

## The primitives

| Primitive | What it does |
|---|---|
| `hw_store 1 a b`, `upd32 blk k w` | write the code's bytes (or 32-bit words) into a narrow block: 4-byte cells at a real, page-aligned address |
| `hw_addr blk` | where that block is |
| `hw_code_sync a n` | the n bytes at `a`, just written, are code from now on (x86: nothing to do; elsewhere the instruction cache is told) |
| `hw_run n a x0 .. x5 h i` | call the code at `a` with up to six arguments; the first `n` (0, 1 or 2) of its two results into cells `i`, `i + 1` of block `h` |
| `hw_sym k` | addresses inside the runtime, for code that must call back into it: 0 the C handler of interrupts, 1 a second processor's C code |

What needs no instruction stays in the generic core and costs no call: device registers (`hw_load`, `hw_store`),
atomics and fences, bulk copies.

## The rules a routine follows

It is called as a C function of the processor's own convention:

| | x86-64 (System V) | RISC-V | AArch64 |
|---|---|---|---|
| arguments `x0` .. `x5` | rdi rsi rdx rcx r8 r9 | a0 .. a5 | x0 .. x5 |
| results | rax, rdx | a0, a1 | x0, x1 |
| must be left as found | rbx rbp r12 .. r15, rsp | s0 .. s11, sp | x19 .. x28, sp |
| return | `ret` (C3) | `ret` (0x00008067) | `ret` (0xD65F03C0) |

- A result is a 63-bit number; a value that needs all 64 bits comes back as two 32-bit halves, low first (that is how
  `rdtsc` and `rdmsr` give it anyway).
- Code called from a program run at an interrupt leaves the vector and floating-point registers alone: the runtime
  does not save them.
- If the program's own page tables can forbid execution, the code's block must be mapped executable.
- After writing or changing code: `hw_code_sync`, then `hw_run`.
- `hw/X86.v` keeps slots 0 .. 31 of narrow block 7 (32 bytes each); a program's own code goes from slot 32 on.

## Reading `hw/X86.v`

One line per instruction, its bytes as the manual's opcode tables give them; the ModRM byte is computed from its
three fields, so the line reads like the manual:

```coq
Definition modrm (md reg rm : int) : int := (md << 6) lor (reg << 3) lor rm.
...
  let s := i4 4 0 0x0F 0x22 (modrm 3 3 RDI) RET s in           (* 4  mov cr3, rdi              0F 22 /r *)
  let s := i4 9 13 0x0F 0x01 (modrm 0 3 4) 0x24 s in           (*    lidt [rsp]                0F 01 /3 *)
...
Definition hw_pt_set (a : int) (s : mem) : mem := run0 4 a 0 0 s.
```

`x86_setup` writes every routine once, then `hw_code_sync`; a program calls it first.  From then on `hw_pt_set`,
`hw_port_in`, `hw_irq_wait` .. are ordinary Rocq functions.  `hw/build.sh` puts the file's text in front of every
program (`ISA=X86`, the default), so the translator and the checker see inside it; it also compiles on its own
(`rocq c -R . KQ hw/X86.v`), to try an encoding with `Compute`.

`hw/own.body` goes further: it writes a whole interrupt entry routine (53 bytes: save the registers C may change, call
the runtime's C handler found with `hw_sym 0`, `iretq`), puts it in its interrupt table, and the timer's interrupts
come in through it.

## Code written when it is needed

Because the encoding is computed, an instruction whose operand is part of the instruction can be written at the moment
it is asked for.  A RISC-V CSR's number is such an operand -- so instead of a list of every CSR, one function:

```coq
Definition hw_csr_read (csr h i : int) (s : mem) : mem :=
  let s := put 31 1 RET (put 31 0 (csrrs A0 csr ZERO) s) in
  hw_run 1 (at_slot 31) 0 0 0 0 0 0 h i (hw_code_sync (at_slot 31) 8 s).
```

(A program that does this both in its main program and at an interrupt gives each a slot of its own.)

## A RISC-V file

The same pattern from the RISC-V manuals (Volume I: the base and Zicsr; Volume II: the privileged architecture), for a
kernel in supervisor mode.  Every RISC-V instruction is one 32-bit word, so a routine is a few cells of the block:

```coq
Definition put (k j w : int) (s : mem) : mem := upd32 CODE (8 * k + j) w s.
Definition i_type (imm rs1 f3 rd op : int) : int :=
  ((imm land 4095) << 20) lor (rs1 << 15) lor (f3 << 12) lor (rd << 7) lor op.
Definition csrrs  (rd csr rs1 : int) : int := i_type csr rs1 2 rd 0x73.
Definition csrrci (rd csr u : int) : int := i_type csr u 7 rd 0x73.
Definition RET : int := i_type 0 RA 0 ZERO 0x67.               (* jalr zero, 0(ra) *)
Example e_csrr : csrrs A0 SSTATUS ZERO = 0x10002573 := eq_refl.    (* csrr a0, sstatus *)
...
  let s := put 0 1 RET (put 0 0 (csrrci ZERO SSTATUS 2) s) in      (* interrupts off: SIE cleared *)
...
Definition hw_irq_off (s : mem) : mem := hw_run 0 (at_slot 0) 0 0 0 0 0 0 0 0 s.
Definition hw_sbi (ext fid a0 a1 a2 h i : int) (s : mem) : mem := hw_run 2 (at_slot 8) a0 a1 a2 fid ext 0 h i s.
```

The whole file, `riscv/Riscv.v` beside this guide (interrupts off / on / wait, the time counter, the faulting address,
`sfence.vma`, `stvec`, `satp`, calls to the SBI firmware, any CSR by number), was CHECKED: it compiles, its `Example`
pins are checked by Rocq's kernel, and its 20 instruction words are the very words LLVM's assembler makes of the same
assembly text (`riscv/check.sh`, in the image: 20 of 20 the same).  Copied to `hw/Riscv.v`, it is what `ISA=Riscv`
would take.  It has not RUN: under the programs, RISC-V needs what x86 has, written once --

- boot code: OpenSBI starts the kernel at 0x80200000 in supervisor mode (a0: the hart's number); a stack, the zeroed
  memory, then `kq_bare_main`;
- the runtime's few processor lines (`hw/kq_bare.c`): its serial line (a 16550 at 0x10000000, by MMIO), stopping QEMU
  (its test device at 0x100000), interrupts off around the interrupt queue, halting; and a trap entry, or one written
  in Rocq as `hw/own.body` does for x86;
- `__clear_cache` (one `fence.i`), which `hw_code_sync` becomes when there is no C library;
- a link script, and `clang --target=riscv64-unknown-elf -mcmodel=medany`; QEMU: `qemu-system-riscv64 -machine virt
  -bios default`.

## The same names on every processor

If two instruction files give the same names (`hw_irq_off`, `hw_irq_wait`, `hw_cycles`, `hw_pt_set` ..), a program
that uses only those and the generic core builds for either (`ISA=X86`, `ISA=Riscv`).  The names are a convention
between files, not part of the core.

## Proving an encoding

The `Example ... := eq_refl` pins are checked by Rocq's kernel every time the file compiles.  Further, an encoding can
be proved against a Rocq model of the instruction set: riscv-coq (MIT) has a RISC-V decoder, and the official Sail
specifications of RISC-V and ARM can be turned into Rocq; for x86 only partial ones exist (RockSalt's decoder, for
one).  What an instruction DOES stays
trusted; a user who wants to prove code that uses one states its law as an axiom, as `KQSpec.v` does for the memory.

## What it costs

Measured by `hw/own.body` under KVM on the i9-12900H (time-stamp counter 2918.5 MHz): 100 000 calls of a routine
that only returns, then 100 000 memory reads, 20 times over, the fastest of each kept (the laptop changes its speed as
it runs: single runs vary two to four times).  A call: 2.3 ticks, 0.8 ns, in 5 runs of 6; a read: 0.9 - 1.7 ticks,
0.3 - 0.6 ns.  So a call costs a few tenths of a nanosecond more than a plain read -- little next to what the
instruction itself does to a device.  Hot paths keep the generic operations, which are inlined C.

## What stays in the kit for each processor family

The part that runs before any Rocq code or IS the runtime: `hw/boot.S` (x86: the Multiboot entry, the switch to 64-bit
mode, 256 interrupt entries, the second processor's start), a handful of x86 lines in `hw/kq_bare.c` (the serial port
for its own messages, stopping QEMU, interrupts off around the queue, halting, `cr2` in a fault's message), and
`hw/link.ld`.  Everything above it is Rocq.
