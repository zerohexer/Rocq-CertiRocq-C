# The goal of the proved route

Programs are written in Rocq and run as C at C speed.  Everything that is logic is proved.  Only the hardware is
assumed.

## The line between proved and assumed

**Proved (software level): logic over integers and memory.**  Arithmetic, bit fields, indices, loops, calls, state
machines, ring buffers, descriptor building, allocators, drivers' decisions and the order in which they touch a device.
All of it is ordinary Rocq over 63-bit integers and memory blocks.  The proof says the generated C does exactly what the
Rocq text does, including the sequence of operations on memory and devices.  Properties of the Rocq text (a protocol,
an invariant) carry over to the C.

**Assumed (hardware level): what an instruction does.**  A store to a device register, a barrier, an atomic, a control
register write, a halt.  Each is a primitive with a stated law and an entry in the trace.  The real behaviour of the
hardware is checked by running on the device or an emulator (QEMU, KVM), not proved.  There is no model of the CPU.

**Hand-written, once per architecture, trusted:** boot and entry stubs, interrupt entry, context switch, the linker
script, in the style of Linux (`head.S`, `entry.S`).  Small `.S` files or inline asm.  Not per program.

**Trusted tools:** the Clight-to-C printer, clang, the loader that fills the memory tables.  Covered by tests: the
answers against the C++ run, the clang build against CompCert's `ccomp`, UBSan.

## What the language is

Ordinary Rocq, no new syntax and no operators made to look like C: `Fixpoint`, `match`, `if`, `let`, the `PrimInt63`
operations, and the memory functions `rd`, `upd`, `rd32`, `upd32` with their laws.  Written in the flat style
(`WRITING-FAST-ROCQ.md`): integers and counters, a function calling itself last, no allocation in a loop.  The checker
refuses what does not follow it.  There is no runtime and no collector.  Data that lives in memory has a layout the
program chooses, as in C, and an allocator written in Rocq on the memory primitives (`lib/Slab.v`).

Widening means reading more of ordinary Rocq that still compiles without a runtime: pairs and records split into
integers, closures with a known function inlined or specialized, polymorphism erased.  What would need a runtime
(a value of run-time size that outlives a call) is refused with the reason, not compiled slowly.

## Where it stands

Proved and in the corpus (36 programs, all proved, answers equal to the C++ run, median 1.02 of the kit's time):
63-bit integer operations except signed division, comparisons, loops, calls, wide and narrow memory blocks.

## What is left, in order

1. Signed division; mutual recursion; pairs and records split into integers.
2. Growing blocks and the heap library on them.
3. The hardware primitives, as assumed operations with laws and a trace: raw-address load and store of 1, 2, 4 and
   8 bytes, atomics and compare-and-swap, fences, copy and fill.  Driver and OS logic around them is then proved.
4. Checks of the trusted tools: the printed C against `ccomp`, UBSan.
5. Shared memory between programs for concurrency: marked shared operations whose proof allows the environment to change
   the cell, and a launcher that runs the programs.  Each program stays a sequential proof.

## Not goals

A model of the CPU or the instruction set.  Proving data-structure invariants away (bounds guards cost little and
stay).  A garbage collector or any run-time system.  Floating point and I/O until a program needs them.
