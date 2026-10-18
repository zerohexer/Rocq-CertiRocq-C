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

## What an optimization may be

The program as written decides the speed.  The translation reflects the structure of the Rocq text in the C it
makes, as a C programmer's text would: a loop that keeps its running total in a memory cell is as slow as the same
loop in C, and it stays that way.  A pass that rescues a badly structured program is not wanted; it hides the cost
from the person who wrote it, and the checker's advice is how they find out.

So the yardstick is C written the same way, not the best C for the task.  Where our output is slower than that C, the
difference is ours to remove, and only by a change that is **general**:

- it applies to every program, because it removes a cost our translation adds to each operation or each choice
  (the test on every memory access, the mark on every integer, the counter on every loop, a choice kept as a jump);
- or it is a standard compiler pass that C compilers apply to any C program (forwarding a value to a later read of
  the same address, hoisting loop-invariant work, if-conversion, dropping a test that cannot fail);
- it is stated and proved once, from the laws of integers and memory, for all programs; the per-program statement
  does not change;
- it is not keyed to the shape of one benchmark.

Where our memory model knows more than a C compiler does, a pass may do more than clang can.  Block numbers are
constants and a read outside a block gives 0, so two accesses to different blocks never alias, and a read can be
run early without a fault.

A cost that comes from the structure of the program stays.  Writing a loop as one pass with a phase number
(a state machine) costs about twice what it costs in C; that is the fixed overhead above, not a reason for a
pass that merges the phases.

### How a pass is chosen

1. Write the program in several ways (`tests/mkworst.py`, `tests/mksame.py`) and the same ways in C
   (`tests/worst_c.c`, `tests/worst_ref.c`).
2. Time each way on one pinned core and compare it with the C of the same shape, not with the first way.
3. Where the gap is large, count instructions, branches and wrong guesses per element (`KQ_PERF=1`; on the host, not
   in a container) for our output and for the C, to see which operation adds the work.
4. Fix the operation for every program, then run the same ways again.

A guess about the cause is tested before it becomes a pass.  One guess was wrong: reloading the block's address
and size from the tables at every access costs nothing, because clang already hoists those loads.

### What is measured so far

Plain loops by the guideline run at 1.0 to 1.7 times the time of C.  They execute 1.7 to 2 times the instructions
of C (the test on every access, the mark on integers) at a higher instruction rate, and make no wrong guesses.
Written badly on purpose (state in cells, phases), the same loops are 2 to 12 times slower than their guideline
way, against 1.1 to 3.8 times for C written that way.  The one gap with a separate cause is the search with its
state in cells on the proved route: 5.9 wrong guesses per query, because a choice whose arms contain reads stays a
jump.  The kit route moves such reads in front of the choice and measures whether a jump or a conditional move is
faster; the proved route's translator does not yet.

The general passes, in order: if-conversion with early reads (a read is total, so it can be moved in front of a
choice), proved removal of the test on an access whose index is in range, forwarding a stored or loaded value to
a later read of the same address, hoisting loop-invariant reads.

## Where it stands

Proved and in the corpus (36 programs, all proved, answers equal to the C++ run, median 1.02 of the kit's time):
63-bit integer operations except signed division, comparisons, loops, calls, wide and narrow memory blocks.

## What is left, in order

1. Signed division; mutual recursion; pairs and records split into integers.
2. Growing blocks and the heap library on them.
3. The hardware primitives, as assumed operations with laws and a trace: raw-address load and store of 1, 2, 4 and
   8 bytes, atomics and compare-and-swap, fences, copy and fill.  Driver and OS logic around them is then proved.
4. The general passes above, each proved once and measured against C written the same way.
5. Checks of the trusted tools: the printed C against `ccomp`, UBSan.
6. Shared memory between programs for concurrency: marked shared operations whose proof allows the environment to change
   the cell, and a launcher that runs the programs.  Each program stays a sequential proof.

## Not goals

A model of the CPU or the instruction set.  Proving data-structure invariants away (bounds guards cost little and
stay).  A garbage collector or any run-time system.  Floating point and I/O until a program needs them.
