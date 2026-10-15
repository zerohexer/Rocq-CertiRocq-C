# Rocq -> CertiRocq -> C

Plain Rocq programs compiled to C by CertiRocq and run natively at about the speed of C++.  Programs use machine
integers and a memory of numbered blocks.  A translator puts each program in one standard form that Rocq's kernel
checks equal to the original, a checker accepts the programs whose memory can be written in place, and a patched
CertiRocq, a clean-up of its C and a small support library do the rest.  `hw/` extends this to programs with no
operating system under them: device registers, atomics, interrupts, and processor instructions written in Rocq.

## Results

26 Codeforces problems, each against an independent C++ solution.  Time of the computation in ms; Intel Core Ultra 9
285H, one pinned core, best of 7 (stock: best of 3).  Every answer equals the C++ answer.

| Problem | What the work is | C++ | CertiRocq, stock | CertiRocq, optimized | stock / C++ | optimized / C++ |
|---|---|---|---|---|---|---|
| CF455A | two loops over 5 million cells | 4.3 | 357 | 5.8 | 82.4 | **1.35** |
| CF380C | segment tree, 100 000 queries | 54.8 | 204 | 51.6 | 3.7 | **0.94** |
| CF1100F | table of bases, 500 000 queries | 87.1 | 357 | 98.2 | 4.1 | **1.13** |
| CF868F | divide and conquer with a moving window | 69.6 | 1459 | 63.5 | 21.0 | **0.91** |
| CF631E | hull of lines, binary search | 3.6 | 49.7 | 4.9 | 13.9 | **1.37** |
| CF833B | segment tree, add and maximum on ranges | 305 | 1710 | 320 | 5.6 | **1.05** |
| CF17E | palindromes of 2 million letters | 31.3 | 664 | 38.4 | 21.2 | **1.23** |
| CF20C | shortest paths with a heap | 9.2 | 48.9 | 7.5 | 5.3 | **0.82** |
| CF1039D | greedy on a tree, divide and conquer | 472 | 6015 | 588 | 12.7 | **1.25** |
| CF813F | offline: sort, segment tree, union-find with undo | 30.3 | 220 | 45.9 | 7.3 | **1.52** |
| CF235C | suffix automaton | 38.0 | 221 | 47.2 | 5.8 | **1.24** |
| CF1172F | segment tree of sorted arrays | 217 | 1375 | 195 | 6.3 | **0.90** |
| CF432D | prefix function of 2 million letters | 6.7 | 405 | 8.1 | 60.7 | **1.22** |
| CF453B | table over sets of primes | 598 | 3557 | 384 | 5.9 | **0.64** |
| CF622F | modular arithmetic, 1 million terms | 60.7 | 408 | 86.3 | 6.7 | **1.42** |
| CF61E | tree of sums (binary indexed), used twice | 46.9 | 275 | 59.9 | 5.9 | **1.28** |
| CF385C | sieve up to 10 million | 160 | 2760 | 151 | 17.3 | **0.94** |
| CF1167C | union-find | 5.1 | 181 | 8.9 | 35.4 | **1.74** |
| CF163A | table of 25 million cells, two rows kept | 8.8 | 321 | 23.3 | 36.5 | **2.65** |
| CF460C | binary search on the answer | 29.3 | 1422 | 35.8 | 48.6 | **1.22** |
| CF35C | walk over a 2000 x 2000 grid with a queue | 20.5 | 815 | 22.2 | 39.8 | **1.08** |
| CF295B | all shortest ways, 500 vertices | 30.9 | 493 | 81.8 | 16.0 | **2.65** |
| CF339D | tree updated from the bottom, 2 million changes | 73.8 | 715 | 124 | 9.7 | **1.68** |
| CF547B | nearest smaller with a stack | 27.7 | 508 | 35.8 | 18.3 | **1.29** |
| CF165E | table over sets of 22 bits | 57.3 | 622 | 62.2 | 10.9 | **1.09** |
| CF7D | two running hashes over 5 million letters | 18.8 | 876 | 20.5 | 46.7 | **1.09** |

- **CertiRocq, stock**: the same Rocq text through unmodified CertiRocq: its defaults, its runtime, its integer
  operations, `nat` as a chain of cells.
- **CertiRocq, optimized**: this repository's pipeline; the fastest program for that problem.
- Optimized / C++: median 1.23; 16 of 26 at or below 1.25, 21 at or below 1.5.  On an Intel Core i9-12900H: median
  1.09 (`results/table.md`).
- Optimized against stock, program by program: 8.8 times faster (geometric mean over 51 programs, from 2.7 to 61
  times; `results/stock_vs_ours.txt`).

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

## Checked

- Every program in `hand/` (36): what is compiled is proved equal to it by the kernel, with the bounds tests and with
  the bounds proofs.
- Every program's answers on the large inputs equal the C++ answers; each corpus program equals the original Z
  program on a random input, computed in Rocq.
- The removal of the collector's saves: everything rerun with a collector that runs every few allocations; removing
  every save is detected.
- The integer operations against a reference (`tests/test_arith.c`); Rocq's division against Z's (`tests/TestDiv.v`).
- The checker on 18 programs with known verdicts (`tests/shape/`).
- `hw/check.sh`: the laws, the 5 kernels under QEMU's processor and under KVM, the 5 controls.
- `all.sh` rebuilds and remeasures everything from an empty directory.

## Trusted

CertiRocq's unverified parts (the erasure options, the C code generator), clang, the support code (`sup/v4/`; `hw/`
for programs on the bare machine), the convention that a `nat` is one machine integer (`KQNat.v`), the clean-up pass,
and the checker, which is tested, not proved.  The translator is not trusted: the kernel checks its output every time.

## Limits

- Every memory access tests its cell by default; step 3 removes the test in counting loops.
- A cell is 8 bytes where C++ often uses 4, unless the program uses narrow blocks (`rd32`, `upd32`).
- The C compiler vectorizes some C++ loops that it does not vectorize in the generated C (CF295B).
- Integers are 63 bits; a 64-bit value travels as two halves.

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

## Files

| File | What it is |
|---|---|
| `KQRun.v`, `KQNat.v` | what a program imports: the memory, arithmetic, the conditional move, input and output, the generic hardware operations; `nat` as a machine integer |
| `KQFast.v` | the translator (steps 1 to 3) and the tactic `kq_fast_qed` |
| `KQBound.v` | the reads and writes without the test, block lengths, and the lemmas step 3's proofs use |
| `KQShape.v` | the checker |
| `KQSpec.v`, `KQModel.v`, `KQSpecDemo.v` | the laws, their model, proofs about kernel code |
| `kq_post3.py` | the clean-up of the generated C |
| `sup/v4/` | the C support code |
| `patch/`, `images.sh`, `docker/build.sh` | the CertiRocq patch; the two Docker images |
| `hw/` | the hardware layer, its kernels and checks |
| `hand/`, `hand.tsv` | the 36 programs written by the guideline, with their measured choices |
| `sv/`, `sv2fast.py` | the corpus programs and their conversion |
| `problems.tsv`, `big/`, `cpp64/`, `cppw/` | the timed problems and their C++ solutions |
| `demo/` | two tasks and a scheduler with input and output, and a model under which Rocq runs the same text |
| `prof.sh`, `kqsel.py` | the measured choices |
| `bounds.sh` | a program's bounds setting |
| `mknarrowbody.py`, `mknarrow.py`, `narrow.tsv` | programs and memories with narrow blocks |
| `mkbig.py`, `mkcase.py`, `mkrefs.sh` | the large inputs; a random input per corpus program and the original's answer |
| `setup.sh`, `regen.sh`, `mk.sh`, `check.sh`, `shape.sh`, `bench.sh`, `table.sh`, `all.sh`, `one.sh` | inputs; Rocq to C; build; compare with the originals; checker verdicts; timing; the table; everything; one program |
| `floor.sh`, `pstat.sh`, `mktable.py` | the cost of the bounds test; the processor's counters; the table as Markdown |
| `tests/` | the same loop written many ways; the bounds settings compared; stock CertiRocq; the integer operations; Rocq's division; the checker's verdicts |
| `results/` | every measurement: tables for both machines, stock against optimized, each step on and off, two C compilers |

## Licence

MIT (`LICENSE`), the same as CertiRocq.  `patch/` modifies CertiRocq (MIT, its authors).
