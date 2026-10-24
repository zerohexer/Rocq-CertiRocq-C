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

## What C can do, and its counterpart in Rocq

The aim is that anything a C program does can be written in Rocq: operating systems and general programs.  C has no
collector either; a C program lays out its data and manages its memory, and so does a Rocq program here.  What C
offers, and what takes its place:

| C | In Rocq | State |
|---|---|---|
| integers, bit operations, loops, calls | `PrimInt63` operations, `Fixpoint`s whose last step is the call; `u64` (two halves, one instruction per operation) for full 64-bit unsigned arithmetic | proved, signed division included; 64-bit unsigned proved (`proved/examples/w64.body`) |
| arrays, buffers | memory blocks read and written with `rd`, `upd` | wide and 32-bit cells proved; 8-bit cells are one byte access in the C (proved against CompCert's memory), 16-bit cells are two |
| structs, unions, bit fields | records split into integers, or a layout in a block; bit fields are bit operations | records and pairs of numbers as parameters, `let`s, `match`es and fields are proved; a recursive function giving back a record or pair of two numbers is proved (the second goes through a slot block); more than two, and unions, missing |
| pointers, raw addresses | an integer address into a region; for an OS, RAM is one block at its base address | missing |
| `malloc`, `free` | an allocator written in Rocq on a growing block (`kq_grow`, `kq_size`) | `lib/Slab.v` goes through the proved route (`proved/examples/heap.body`); `kq_grow`'s C body is assumed, like the other machine operations |
| function pointers, callbacks | a table of function ids, a proved dispatch on the id, the environment passed as arguments; a known function given to a helper is put in, a recursive function that takes functions gets a copy per function given | proved (`proved/examples/dispatch.body`, `hof_*.body`); closures refused |
| hardware access, atomics, inline assembly | primitives with a stated law and a trace; hand-written `.S` once per architecture | loads, stores, atomics, fences, bulk bytes, `hw_run`, `hw_addr`, interrupt-take proved against the kit's laws, the C bodies assumed (`hw_law`, `hwf_law`); five test kernels (`hw/`: the kernel, interrupt handler, fault handler, second processor, interrupt entry written in Rocq) are proved and boot in QEMU; a program's own assembly/C routines are declared and assumed (`hw_user`) |
| floating point | `PrimFloat` as C `double` | not started |
| files, sockets, system calls | primitives with a trace, as for hardware | not started |
| threads, SMP | one program per thread; shared memory reached only through marked atomics (`kq_shared` makes the translator refuse plain access); the launcher is written in Rocq (INIT/STARTUP through the local interrupt controller); a spinlock library | built (`hw/lock.body` on two processors); the model is the atomics' laws, no interleaving semantics |
| calling existing C libraries | declared as assumed primitives with stated laws | not started |
| strings, `printf` | byte blocks and a formatting library written in Rocq | missing |

Higher-order functions are not on the list because C has none.  A function known where it is used is inlined
(what a macro or a template does) and costs nothing.  A function chosen at run time is a function-pointer table
with an explicit environment, as `qsort` takes a comparison and a context pointer.  A closure that captures
variables and outlives the call is what a C programmer builds by hand as a struct; written implicitly it allocates
behind the programmer's back, and it is refused.

Data that needs a collector is not translated: lists and trees that outlive a call are laid out in blocks with an
allocator, as in C.

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
faster.  The proved route now does the first half: a choice between two values whose arms read the current memory
(up to three reads) is taken with a conditional move, since a read is total.  Measured with that change (ms, one core):
state in cells in the mixed loop 115 to 18, in the search 1076 to 351 (kit route 296), cells and phases in the search
1367 to 496; all 36 programs of the corpus still proved and equal to the C++ answers, and the C of 6 of 7 timed
programs is unchanged.  Merging a chain of calls keeps to plain arithmetic: with reads in the arguments the
phase-cycling search got twice as slow (411 to 785), because a conditional move in place of a well-predicted jump
makes each round wait for the one before.

The general passes still to do, in order: proved removal of the test on an access whose index is in range,
forwarding a stored or loaded value to a later read of the same address, hoisting loop-invariant reads.

## Where it stands

Proved and in the corpus (36 programs, all proved, answers equal to the C++ run, median 1.02 of the kit's time):
63-bit integer operations, comparisons, loops, calls, wide and narrow memory blocks.

## What is left, in order

1. Records of more than two numbers as results of functions, and a choice between two records.  (Done: 8- and 16-bit
   cells; records and pairs as parameters, `let`s and `match`es; results of two numbers;
   mutual recursion; function-id tables and known functions as arguments.)
2. The hardware primitives are in (the C bodies assumed, `hw_law`, `hwf_law`), and the kernels of `hw/` go through the
   proved route and boot (`hw/build_proved.sh`): several programs per kernel (interrupt, fault, second processor) and
   the program's own assembly/C routines are done.  Left: a freestanding build of the generated C checked on its own,
   and the proof time of very long straight-line code (the 100-store instruction table takes 16 s; 14 read-modify-write steps 23 s, 24 of them about 3 minutes).
3. The heap library's own lemmas (invariants of the slab that a user theorem about their program can use), and a freestanding `kq_grow`.
4. The general passes of the section above, each proved once and measured against C written the same way:
   if-conversion with early reads is done; next the removal of the test on an access whose index is in range.
   These run alongside the other items and block none of them.
5. Floating point, system calls and declarations of C libraries, for hosted programs.
6. Concurrency beyond the marked atomics: an interleaving semantics of two programs, to state and prove protocol
   properties (mutual exclusion of a lock, a queue) once for all programs; a lock with fairness (ticket lock).
7. Checks of the trusted tools: the printed C against `ccomp`, UBSan.

## Not goals

A model of the CPU or the instruction set.  Proving data-structure invariants away (bounds guards cost little and
stay).  A garbage collector or any run-time system.  Floating point and I/O until a program needs them.
