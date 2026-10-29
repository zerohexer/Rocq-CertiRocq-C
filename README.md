# Rocq -> CertiRocq -> C

Plain Rocq programs compiled to C by CertiRocq and run natively at about the speed of C++.  Programs use machine
integers and a memory of numbered blocks.  A translator puts each program in one standard form that Rocq's kernel
checks equal to the original, a checker accepts the programs whose memory can be written in place, and a patched
CertiRocq, a clean-up of its C and a small support library do the rest.  `hw/` extends this to programs with no
operating system under them: device registers, atomics, interrupts, and processor instructions written in Rocq.

## Getting started

You need git and Docker (Linux, macOS, or Windows with WSL 2), about 8 GB of disk, and 6 GB of memory for Docker
while the images build.

```
git clone https://github.com/zerohexer/Rocq-CertiRocq-C.git
cd Rocq-CertiRocq-C
bash images.sh          # once: the two Docker images, about 25 minutes
```

A first program, `examples/hello.body`:

```coq
Axiom c_putchar : int -> mem -> mem.   (* C's putchar *)

Definition main : int :=
  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in
  let s := kq_input 0 in
  let s := c_putchar 72 s in    (* H *)
  let s := c_putchar 101 s in   (* e *)
  ...
  let s := c_putchar 10 s in    (* new line *)
  rd 0 0 s.
```

Build it and run it:

```
docker run --rm -v "$PWD":/w kernelq-certirocq:1b45a1aa-kq2 bash /w/compile.sh examples/hello.body
```

```
KQ-SHAPE OK: 0 function(s) on the hot path, 1 outside it --
left in the C: 0 values built, 0 of them inside a loop, 0 closures built, 0 calls through a closure
built bin/U_hello
Hello, world!
main = 0
```

`compile.sh` runs the whole pipeline -- the translator, the checker, CertiRocq, the clean-up of the C, clang -- and
then the program; numbers after the file name are its command line.  The generated C is `U_hello_prog.c`, the cleaned
C `bld/user/U_hello.c`, the program `bin/U_hello`.  `examples/count.body` is a loop over a number from the command
line (`compile.sh examples/count.body 5` prints 1 to 5).  What a program can use is declared in `KQRun.v`; how to
write one that stays fast is `WRITING-FAST-ROCQ.md`.

**C functions.**  A program calls any C function by declaring it, with a prefix that says how the call works:

```coq
Axiom c_putchar : int -> mem -> mem.        (* putchar(c), for its effect *)
Axiom cr_rand : int -> int -> mem -> mem.   (* rand(): its result into cell i of block h *)
Axiom c_sqrt : int -> int.                  (* sqrt(x), no effects: its result is the answer *)
```

Arguments are numbers; an address is a number too (`hw_addr h` is narrow block h's, for a buffer).  `compile.sh`
writes the C that connects each declaration (`cffi.py`); `-e CINCLUDE="a.h"` adds headers and `-e CLIBS=-lm`
libraries.  A C file next to the program is compiled and linked with it, and a `.mem` file next to it is its starting
memory.  `examples/`: `libs` (the C and maths libraries), `write` (a buffer handed to `write`), `own` (a C function of
the program's own).

## Results

26 Codeforces problems.  Time of the computation in ms, and in brackets how many times the C++ time; Intel Core Ultra 9
285H, one pinned core, best of 7 (stock: best of 3).  Every answer equals the C++ answer.

| Problem | What the work is | C++, written by hand | Rocq, stock CertiRocq | Rocq, this pipeline |
|---|---|---|---|---|
| CF455A | two loops over 5 million cells | 4.3 | 357 (82×) | **5.8 (1.35×)** |
| CF380C | segment tree, 100 000 queries | 54.8 | 204 (3.7×) | **51.6 (0.94×)** |
| CF1100F | table of bases, 500 000 queries | 87.1 | 357 (4.1×) | **98.2 (1.13×)** |
| CF868F | divide and conquer with a moving window | 69.6 | 1459 (21×) | **63.5 (0.91×)** |
| CF631E | hull of lines, binary search | 3.6 | 49.7 (14×) | **4.9 (1.37×)** |
| CF833B | segment tree, add and maximum on ranges | 305 | 1710 (5.6×) | **320 (1.05×)** |
| CF17E | palindromes of 2 million letters | 31.3 | 664 (21×) | **38.4 (1.23×)** |
| CF20C | shortest paths with a heap | 9.2 | 48.9 (5.3×) | **7.5 (0.82×)** |
| CF1039D | greedy on a tree, divide and conquer | 472 | 6015 (13×) | **588 (1.25×)** |
| CF813F | offline: sort, segment tree, union-find with undo | 30.3 | 220 (7.3×) | **45.9 (1.52×)** |
| CF235C | suffix automaton | 38.0 | 221 (5.8×) | **47.2 (1.24×)** |
| CF1172F | segment tree of sorted arrays | 217 | 1375 (6.3×) | **195 (0.90×)** |
| CF432D | prefix function of 2 million letters | 6.7 | 405 (61×) | **8.1 (1.22×)** |
| CF453B | table over sets of primes | 598 | 3557 (5.9×) | **384 (0.64×)** |
| CF622F | modular arithmetic, 1 million terms | 60.7 | 408 (6.7×) | **86.3 (1.42×)** |
| CF61E | tree of sums (binary indexed), used twice | 46.9 | 275 (5.9×) | **59.9 (1.28×)** |
| CF385C | sieve up to 10 million | 160 | 2760 (17×) | **151 (0.94×)** |
| CF1167C | union-find | 5.1 | 181 (35×) | **8.9 (1.74×)** |
| CF163A | table of 25 million cells, two rows kept | 8.8 | 321 (36×) | **23.3 (2.65×)** |
| CF460C | binary search on the answer | 29.3 | 1422 (49×) | **35.8 (1.22×)** |
| CF35C | walk over a 2000 x 2000 grid with a queue | 20.5 | 815 (40×) | **22.2 (1.08×)** |
| CF295B | all shortest ways, 500 vertices | 30.9 | 493 (16×) | **81.8 (2.65×)** |
| CF339D | tree updated from the bottom, 2 million changes | 73.8 | 715 (9.7×) | **124 (1.68×)** |
| CF547B | nearest smaller with a stack | 27.7 | 508 (18×) | **35.8 (1.29×)** |
| CF165E | table over sets of 22 bits | 57.3 | 622 (11×) | **62.2 (1.09×)** |
| CF7D | two running hashes over 5 million letters | 18.8 | 876 (47×) | **20.5 (1.09×)** |

All three are native programs, timed the same way:

- **C++, written by hand**: an independent solution in C++, compiled by `clang++ -O2`.
- **Rocq**: the solution written in Rocq.  CertiRocq compiles it to C, `clang -O2 -flto` compiles the C, and the
  machine code runs.
  - **stock CertiRocq**: unmodified, with its own defaults, runtime and integer operations (`nat` as a chain of cells);
  - **this pipeline**: the translator, the patched CertiRocq, the clean-up of the C and the support code below; the
    fastest program for that problem.
- The two Rocq columns are the same Rocq source, so they compare one to one.  The C++ uses the same algorithm and
  data structure but is written as a contestant would, not translated line by line: its arrays hold 4-byte `int`s where
  a Rocq cell is 8 bytes (unless the program uses narrow blocks), and in four problems (CF1100F, CF833B, CF20C, CF453B)
  the fastest Rocq program uses a formulation the C++ does not.  `results/table_285H.md` also times the C++ with 8-byte
  cells and the C++ written the way the Rocq is (against the latter: CF453B 1.29×, CF20C 1.32×, CF1100F 0.96×, CF833B
  1.10×).
- This pipeline against C++: median 1.23 times the C++ time; 16 of 26 problems at or below 1.25, 21 at or below 1.5.
  On an Intel Core i9-12900H: median 1.09 (`results/table.md`).
- This pipeline against stock CertiRocq, program by program: 8.8 times faster (geometric mean over 51 programs, from
  2.7 to 61 times; `results/stock_vs_ours.txt`).

## How it works

No C is written for any program, and nothing in the pipeline depends on which program it compiles.

| Step | What it does |
|---|---|
| Translator (`KQFast.v`) | Puts every function in one standard form (every step named, a cell read once, a fixed order) and proves it equal to the original; the kernel checks each proof.  Step 2 merges two arms that do the same work into one, proved by induction.  Step 3, off by default, drops the bounds test from counting loops; a copy of each such loop carrying the proofs is type-checked. |
| Measured choices (`prof.sh`, `kqsel.py`) | A test the processor guesses wrong one time in ten or more becomes a conditional move (`hand/NAME.sel`). |
| Checker (`KQShape.v`) | Refuses four things: a memory used after it was handed on, a value built in a loop, a recursive call that is not the last step, a function used as a value.  A refused program does not compile. |
| `nat` as a machine integer (`KQNat.v`) | A loop budget is one number. |
| Patched CertiRocq (`patch/`) | A larger inlining budget and a larger small-function threshold, so that calls with many parameters build no closures; `Extract Inline` backported.  Every pass keeps its proof. |
| Compiler settings | `--anf-variant 9 --c-args 1000 --allow-unsafe-erasure`: every parameter a C argument; lambda lifting; MetaRocq's optional erasure passes. |
| Clean-up of the C (`kq_post3.py`) | Removes the collector's saves of values that are not pointers (the largest single cost); merges the calls that end both arms of an `if`; writes the pieces of a loop into one function; reports values and closures left in loops. |
| Support code (`sup/v4/`) | The memory, the integer operations (inline), the conditional move.  CertiRocq's own signed remainder, arithmetic shift and unsigned comparisons are wrong on part of their range and are not used. |
| Build | `clang -O2 -flto`. |

`WRITING-FAST-ROCQ.md` gives the nine rules a program follows to stay fast, each with its measured case.  The same loop
written in different ways gives the same C: of 50 ways in `tests/same.sh`, 36 compile to identical C and the others
run within 6% (`results/same.txt`).

## Hardware (`hw/`)

Programs that are the machine's only program, built by the same pipeline and run in QEMU.

| Part | What it is |
|---|---|
| `KQRun.v`, `hw/kq_hw.h` | generic operations in plain C: device registers (`hw_load`, `hw_store`), atomics and fences, bulk copies, and `hw_run`, which calls machine code the program wrote |
| `hw/X86.v` | the x86-64 instructions the kernels use, written in Rocq from Intel's manual and run through `hw_run`.  How to write such a file for another processor: `hw/WRITING-INSTRUCTIONS.md`; `hw/riscv/` is a RISC-V one whose encodings equal LLVM's assembler's |
| `hw/Runtime.v`, `hw/boot.S`, `hw/kq_bare.c` | the runtime: boot, interrupt entry, the interrupt queue, a memory area per program |
| `KQSpec.v`, `KQModel.v`, `KQSpecDemo.v` | the laws of the generic operations (one axiom), a model in which every law is proved, and proofs about kernel code that rest on the laws alone |

| Kernel | What it does | Control (must fail) |
|---|---|---|
| `kernel` | serial driver, page tables, interrupt table and timer, MSRs, `cpuid`, PCI, atomics, bulk memory, its own assembly | a page-table entry points at the wrong 2 MB |
| `irqnow` | Rocq code run at the moment each timer interrupt arrives | the handler does not acknowledge |
| `fault` | a page fault handled by Rocq code: the page mapped, the write retried | the wrong page mapped |
| `smp` | a second processor started by the Rocq program; a shared atomic counter | the processor is never started |
| `own` | an interrupt entry routine written in Rocq; the cost of `hw_run`: 0.8 ns a call under KVM | the routine reports the wrong vector |

## Dynamic memory (`lib/Slab.v`)

A block can grow while the program runs: `kq_grow h n s` gives block h at least n cells, `kq_size h s` is its size.
The cells it had keep their numbers and the new ones read 0, so no read changes.  The laws (`KQSpec.v`) say so, and
the model (`KQModel.v`) proves them consistent.

`lib/Slab.v` is a heap of objects on one growing block, after ZER's `Slab`, written in plain Rocq.  A program that
names a `slab_` function gets its text in front of the program's own.

| Function | What it does |
|---|---|
| `slab_init b f cap grow` | block b becomes an empty slab of objects with f fields; it doubles when full, or stays a fixed pool (`grow` = 0) |
| `slab_next b s`, then `slab_take b s` | the handle of the next object, then the allocation |
| `slab_get b h k s`, `slab_set b h k v s` | field k of object h |
| `slab_free b h s` | frees object h |
| `slab_live b h s` | is h a live object of this slab |

A handle is the block, the slot and the slot's generation in one number.  Freeing moves the generation on, so every
copy of a freed handle is dead, also once its slot holds a new object, and a handle of another slab is never live.
`slab_get` and `slab_set` on a handle that is not live read 0 and write nothing.

`lib/SlabSpec.v` proves, against the memory's laws alone:

| Theorem | Statement |
|---|---|
| `slab_take_live` | the handle `slab_next` gave is live after `slab_take`, also when the slab must double |
| `slab_free_kills` | after `slab_free b h`, h is not live |
| `slab_reuse_keeps_dead` | after `slab_free b h` and a `slab_take` that reuses h's slot, h is still not live |
| `slab_get_set` | through a live handle, a field reads what was last written to it |
| `slab_init_inv`, `slab_set_inv`, `slab_free_inv`, `slab_take_inv` | the slab's invariant (`slab_inv`: the header and the generations well formed, and the free list a list of distinct free slots, each holding the next) holds after `slab_init`, and again after each of `slab_set`, `slab_free`, `slab_take`, so a proof about a program that calls them one after the other can use it at every step.  `slab_take_inv` needs room for a doubled capacity (below 2^27 slots, and the block under 2^31 cells), as `slab_take_live` does |

`examples/slab_set.body` is a hash set on a slab, both of its blocks starting empty; `examples/slab_set_malloc.c` is the
same set in C with `malloc` and `free`.  Both give the same set; the Rocq version takes 5-7x the C's time, most of it the
handle test on every field access.

## A proved route (`proved/`)

A second route from Rocq to C, with proofs: a program of `hand/` is translated to KQL, a small first-order language,
with a kernel-checked statement per function that the KQL computes the Rocq function; KQL goes to CompCert's Clight
by a generator proved once, over the kit's memory (`KQRun.v`, with its laws).  The C printed from that Clight runs as
fast as the kit's own build.  `proved/README.md` has the steps, what is proved and what is not, the corpus and the
speed.  `Rocq-C-solution.md` is the complete record of the goal, the decisions, the measurements and the work left.

## Checked

- Every program in `hand/` (36): what is compiled is proved equal to it by the kernel, with the bounds tests and with
  the bounds proofs.
- Every program's answers on the large inputs equal the C++ answers; each corpus program equals the original Z
  program on a random input, computed in Rocq.
- The removal of the collector's saves: everything rerun with a collector that runs every few allocations; removing
  every save is detected.
- The integer operations against a reference (`tests/test_arith.c`); Rocq's division against Z's (`tests/TestDiv.v`).
- The checker on 18 programs with known verdicts (`tests/shape/`).
- `hw/check.sh`: the laws, the 5 kernels under QEMU's processor and under KVM, the 5 controls.  Its first part,
  `hw/spec.sh`, also checks that the heap's four theorems rest on the laws alone.
- The proved route (`proved/corpus.sh`): every proof accepted by the kernel; every program of `hand/` that it reads
  proved, built, and giving the C++ answer.
- `all.sh` rebuilds and remeasures everything from an empty directory.

## Trusted

CertiRocq's unverified parts (the erasure options, the C code generator), clang, the support code (`sup/v4/`; `hw/`
for programs on the bare machine), the convention that a `nat` is one machine integer (`KQNat.v`), the clean-up pass,
the checker, which is tested, not proved, and the C functions a program declares, with the code `cffi.py` writes to
connect them.  The translator is not trusted: the kernel checks its output every time.

## Limits

- Every memory access tests its cell by default; step 3 removes the test in counting loops.
- A cell is 8 bytes where C++ often uses 4, unless the program uses narrow blocks (`rd32`, `upd32`).
- The C compiler vectorizes some C++ loops that it does not vectorize in the generated C (CF295B).
- Integers are 63 bits; a 64-bit value travels as two halves.
- A loop is a chain of C tail calls; with more than six parameters the C compiler may make them real calls, so a long
  loop needs a large stack.  The scripts run programs with `ulimit -s unlimited`.

## Running it

```
bash images.sh       # once: the two Docker images (network, about 25 minutes, 6 GB of memory)
docker run --rm --memory=3g --memory-swap=3g --network=none -v $PWD:/w kernelq-certirocq:1b45a1aa-kq2 bash /w/all.sh
```

`all.sh` makes the inputs, builds everything, runs every check and prints the table (about 25 minutes;
`results/all.txt`).  `bash one.sh NAME` builds and measures one program of `hand/`.

A program's settings, next to it in `hand/`: `NAME.sel`, the tests made without a jump (written by `prof.sh`), and
`NAME.bounds`, `tests` (the default) or `proofs`.  `KQBOUNDS=proofs` sets it for a whole run.

Hardware: `hw/build.sh NAME` in the image, `hw/run.sh NAME` on the host (QEMU), `hw/check.sh` for all of it.

`pstat.sh` and `tests/same.sh` read the processor's counters and run on the host.

## Licence

MIT (`LICENSE`), the same as CertiRocq.  `patch/` modifies CertiRocq (MIT, its authors).
