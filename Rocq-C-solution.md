# ROCQ-C SOLUTION — ordinary Rocq to freestanding, portable C: proved, natural, at C speed

**What this file is.**  The complete record of the Rocq-to-C work: the goal in full, the architecture as built, every
decision that is settled and why, every measurement, every trap that cost a session, the method for finding what is
missing, and the ordered list of what is left.  It is the counterpart of the cost-shape record of the KernelQ project
(`docs/rocq-cost-shape-solution.md` there): a fresh session reads this file and does not re-derive anything that is here.

`proved/GOAL.md` is the short statement of the goal and stays the place the README points to; this file contains all of it
(§0) and everything around it.  When the two disagree, this file is the newer one; fix `GOAL.md`.

---

## ★ READ THIS FIRST — the state in one screen (2026-10-30)

**The goal (owner, verbatim in spirit, §0.2):** write ordinary Rocq — the way one writes ordinary Lean and gets C from
`lean --c` — and get freestanding, portable C at C speed, with **no runtime and no collector**, where **everything that is
logic is proved** and **only the hardware is assumed** through generic primitives with laws, so that an operating system,
its interrupt handling and its drivers can be written in Rocq by the user, for any architecture, from the manual.
**No over-rejection, no style rules to learn, no patching holes one by one, general optimizations only, fast proofs.**

**What exists and works (all verified on the final tree, 2026-10-29/30):**

```
pipeline     Rocq text --(MetaRocq translator, untrusted)--> KQL --(generator, PROVED ONCE)--> Clight --(printer)--> C --> clang
per program  for EVERY function: "the KQL function computes the Rocq function", checked by Rocq's kernel
corpus       36 Codeforces-style programs: all proved, built, answers equal to the C++ run; median 1.02x the kit's own build
examples     22 programs (records, pairs, mutual recursion, functions as values, closures, loops, measure recursion, u64, bytes,
             views, a growing heap, machine operations): all proved, built, answers equal to hand-computed values
kernels      5 test kernels (interrupts, a page fault handled in Rocq, a second processor, an interrupt entry written in Rocq
             byte by byte, a kernel with page tables/IDT/PCI/atomics) proved and booting in QEMU (TCG and KVM)
naturalness  construct table: 780 cells, 759 translated and proved, 20 gaps, none by design yet (first full run 533 / 231
             of 770; 733 / 41 of 775 on the morning of 2026-10-30)
proof time   cold 35-54 s per test kernel (was 2m29-4m18); a rerun of an unchanged program ~15 s (per-function proof cache);
             corpus: 243 function proofs, 1.9 s on average
theorems     the slab heap keeps its invariant through init/set/free/take; views of one memory are consistent; loops whose budget
             is a measure end with their test false; measure recursion satisfies its equation and an induction principle
```

**Where the work is, in the order to take it (§12 has each item with its acceptance):**
1. The 20 gaps of the construct table (§3.5): proof search of pair-valued choices (6); polymorphic and class-based helpers
   (4); arithmetic on counters (4); records of three numbers given back by recursion (3: with the memory law the owner approved, D27,
   §3.5); an `option` given back by a recursive function or kept as a loop's state (2: its tag and its field); a
   local `fix` naming the caller's variables (1).  Then the by-design boundaries pinned by cells that show their cause, each
   with a control (§3.5, §3.6).
2. **A verified compiler by reflection** (§1.12, D26, §12.V): a syntax `S` of the fragment, its meaning `denote`, a compiler
   `compile : S -> KQL` proved once; the user's function is reified into `S` (untrusted) and per program only `denote s = f` is
   checked by conversion — zero proof search, nothing added to the trust, for other people's programs.  Built so far
   (`proved/KQR.v`, `KQRReify.v`): numbers, tests, lets, reads, calls, recursion on a counter, memory writes — each
   per-program step in milliseconds, long read-then-write bodies included on our fork of Rocq's kernel (D28, `rocq-fork/`);
   next `kitc.py --reflect`.  Emit-then-prove is the interim.
3. **The translator's own side conditions** (§3.7): the counter must be the first parameter, the memory the last, at most one
   memory, functions only from the program's own file — conventions a user has to learn, which the construct table does not yet
   vary because its generator writes programs that way.  They are over-rejections until a theorem needs them.
4. **Rocq's own measure recursion** (`Program Fixpoint {measure ..}`, `Function`, `Equations`): what the owner asked for as
   loops "level 2".  `wfix` is the step built so far; the owner's form is owed (§4.5, §12.P).
5. **The operations of freestanding C not yet in KQL** (§2.1): `uint64_t` division and remainder, signed 64-bit arithmetic, the
   high half of a product, 8/16/32-bit arithmetic with C's wrap-around.
6. Compiling from an ordinary `.v` file with one command (`Kq Compile`), entry arguments read from the signature, C printed at
   once and the proofs checked behind it (§12.B).
7. Freestanding: the generated C built and checked on its own; a freestanding `kq_grow` (§9.5).
8. The general passes, each proved once: removal of the bounds test on an access whose index is in range, forwarding a stored
   value to a later read, hoisting loop-invariant reads (§6.4).
9. An interleaving semantics for two programs (protocol properties proved once), a fair lock; checks of the trusted tools
   (`ccomp`, UBSan); hosted features (floating point, system calls, C libraries) when a program needs them.
10. **Naturalness as a theorem** (§3.8): a grammar of the accepted fragment, defined without reference to the translator, and a
   proof that the translator and the proof succeed on every term of it — the table is the measurement, the theorem is the claim.

§0.10 says when the goal is reached.

**Do not (§10 has the reasons):** add a runtime or a collector; translate `nat`/`Z` arithmetic as if it were fixed-width; add
an optimization keyed to one benchmark; fix a refusal by looking at one sample program instead of the construct table; port a
processor family in C or assembly; put a scheduler, a memory manager, drivers or a filesystem into the toolchain; trust the
translator; use the proof cache as release evidence (use `KQ_MONO=1`); run two heavy jobs on one machine at once; call a
refusal "by design" because of a value's type; build an easier substitute for what the owner asked and record it as the
decision (§13.8).

---

## CONTENTS

- §0  THE GOAL — the owner's words, the line between proved and assumed, what natural means, what is refused, the yardstick
      — §0.9 HOW TO DECIDE when this file does not say (read it before any change) — §0.10 WHEN THE GOAL IS REACHED
- §1  THE ARCHITECTURE AS BUILT — pipeline, KQL, numbers, memory, translator, statements, generator, printer, hardware, libraries
      — §1.11 the CakeML comparison — §1.12 THE DECISION IN FORCE: a verified compiler by reflection (zero proof search)
- §2  WHAT C CAN DO, AND ITS COUNTERPART IN ROCQ — the capability table with today's state
- §3  NATURALNESS — THE CONSTRUCT TABLE: method, generator, classification, numbers, the 20 gaps, how to close one, the
      translator's own side conditions, naturalness as a theorem
- §4  LOOPS AND RECURSION — fuel, counted loops, measure loops, measure recursion (`wfix`) and its theory, Rocq's own forms
      (owed: the owner's "level 2")
- §5  FUNCTIONS AS VALUES, CLOSURES, LOCAL FUNCTIONS — templates, captures, comparison of terms, budgets of constants
- §6  SPEED OF THE GENERATED C — measurements, where the overhead is, passes done, passes left, how a pass is chosen
- §7  PROOF SPEED — why proofs cost, what was done, numbers, profiles, what is deliberately not done
- §8  THEOREMS ABOUT PROGRAMS — what a user proves about their Rocq text, the libraries' theorems, how to write one, traps
- §9  HARDWARE AND THE OPERATING-SYSTEM GOAL — generic primitives, the per-architecture floor, concurrency, freestanding
- §10 DECISIONS — SETTLED, DO NOT RE-ARGUE
- §11 FINDINGS AND TRAPS LEDGER
- §12 THE WORK LEFT — the live, ordered plan
- §13 HOW TO WORK ON IT — commands, gates, rules, procedures, debugging recipes
- §14 COMMIT LEDGER
- §15 GLOSSARY
- §16 RELATED DOCUMENTS

---

## §0. THE GOAL

### 0.1 In one line

**Programs are written in ordinary Rocq and run as C at C speed.  Everything that is logic is proved.  Only the hardware is
assumed.**  Writing them is as easy as writing ordinary Rocq: nothing is refused except what would need a runtime.

### 0.2 The owner's words (the requirements, as stated across the sessions)

These are the requirements the design answers to.  They are paraphrased closely; where a phrase is quoted it is the owner's.

- **Native, full, natural.**  "Native full completeness of portable C in Rocq, proven, and able to do hardware interaction,
  interrupt primitives basically; arch-wise able to do it ourselves since we provided primitives."  "No over-reject, natural
  FULL, max high speed optimization, general, no need breaking head, fast proof, natural."  "No patching holes whatsoever,
  full natural."
- **As simple as Lean's C output.**  "All of Lean code, no brain, just follow original syntax, emit C, done — we should be
  simple as that when writing to C."  "Flexible, portable as hell like Lean, not struggle to convert."  Memory and layout are
  manual and static — that is accepted; "other than that it should be flexible".
- **General optimization only.**  "General optimization is best."  Speed comes from how the Rocq is written plus one general
  pipeline; no per-program C, nothing tuned to one benchmark, the C compiler is "just a compiler".  Faster than C is fine;
  faster and unstable is not.
- **Find gaps by construct, not by sample.**  Logging refusals of sample programs and fixing them one by one was rejected as
  "patching": "this is patching whole, which isn't good; there should be a better direct way to identify all sorts of correct
  patterns, combinations whatsoever" (the A×B×C orderings).  Hence the construct table (§3), "similar to cost shape".
- **Loops must not be a workaround.**  The fuel parameter was called a workaround; the owner asked for the native way and
  then: "make it level 2, stable, perfect and good" — level 2 being, as it was offered, Rocq's own `Program Fixpoint
  {measure ..}` / `Function` (§4.5).
- **The toolchain is freestanding C, nothing above it.**  A scheduler, process tables, a memory manager, drivers and a
  filesystem are not part of it: "not part of freestanding but above primitives; we should do freestanding / portable C;
  put it as not included".  Interrupt handling and the scheduler are written by the user on the primitives, per architecture,
  "just like C".
- **Hardware is generic primitives, never a port.**  "Give the user primitives, so it is generic; we manually build RISC-V
  instructions / intrinsics in Rocq based on the specs using primitives."  The core knows no instruction set (§9.1).
- **Numbers.**  Fixed-width integers like C.  Making `Z` "auto-switch" to `int` was discussed and kept separate: it would
  change the meaning (wrap-around) unless a proof of the range is given (§10, D3).
- **Proof time is development time, not run time**, and it must stay small: cached, parallel, general tactic improvements
  only (§7).
- **Process.**  Commits are authored by the owner only, with no co-author trailer and no narration; push only when the owner
  says; the repository is public, so no host details, addresses, user names or local paths go into it.

### 0.3 The line between proved and assumed

**Proved (software level): logic over integers and memory.**  Arithmetic, bit fields, indices, loops, calls, state machines,
ring buffers, descriptor building, allocators, drivers' decisions and the order in which they touch a device.  All of it is
ordinary Rocq over 63-bit integers and memory blocks.  The proof says the generated C does exactly what the Rocq text does,
including the sequence of operations on memory and devices.  Properties of the Rocq text (a protocol, an invariant) carry over
to the C.

**Assumed (hardware level): what an instruction does.**  A store to a device register, a barrier, an atomic, a control
register write, a halt.  Each is a primitive with a stated law and an entry in the trace.  The real behaviour of the hardware is
checked by running on the device or an emulator (QEMU, KVM), not proved.  There is no model of the CPU.

**Hand-written, once per architecture, trusted:** boot and entry stubs, interrupt entry, context switch, the linker script, in
the style of Linux (`head.S`, `entry.S`).  Small `.S` files or inline asm.  Not per program.

**Trusted tools:** the Clight-to-C printer, clang, the loader that fills the memory tables.  Covered by tests: the answers
against the C++ run; planned: the clang build against CompCert's `ccomp`, UBSan (§12.H).

### 0.4 What the language is, and what "natural" means

Ordinary Rocq, no new syntax and no operators made to look like C: `Definition`, `Fixpoint`, `match`, `if`, `let`, records,
pairs, the `PrimInt63` operations, and the memory functions (`rd`, `upd`, `rd32`, `upd32`, `rd8`, `upd8`, `rd16`, `upd16`,
`kq_size`, `kq_grow`) with their laws.  There is no runtime and no collector.  Data that lives in memory has a layout the
program chooses, as in C, and an allocator written in Rocq on the memory primitives (`lib/Slab.v`).

**Natural means:** the user writes `Definition`, `Fixpoint`, `match`, `let`, tuples, records, helpers, local functions,
recursion that is not a last step, functions as arguments, closures over local variables, loops over ranges, recursion with a
measure — and does not arrange the text for the translator.  Numbers are the fixed-width `int` and `u64` of C, not `nat` and
`Z` (those are unbounded and need a bignum, which is a runtime; `nat` stays the loop counter).  Memory is laid out by the user:
blocks, the slab, views.

The comparison point is Lean's compiler (§5.7): ordinary Lean compiles because Lean carries a runtime (every value a heap
object, reference counted, `Nat` a scalar that falls back to a bignum).  The part of Lean's compiler that needs no runtime —
inlining, join points, lambda lifting, specialization, tail calls as jumps — is the model, and is what this route does.

### 0.5 What is refused, and only this

1. **A value that would be allocated behind the programmer's back and outlive the call**: a list or tree whose size comes from
   the data (built by recursion); a function value that is not known from the text where it is called (returned by a
   recursive function, built anew at each round of a recursion).  In C such data is laid out by the programmer; here it is
   laid out in blocks with an allocator (`lib/Slab.v`), the same way.
2. **An unbounded number** used as a value (`Z`, `nat` arithmetic beyond counting down).  C has none; a bignum is a runtime.
3. **Two versions of the memory both used** (`let t := upd .. s in .. t .. s ..`): the memory is linear, which is what lets a
   pure function be compiled to in-place updates; keeping both would be a copy made behind the programmer's back.

**Whether a value needs a runtime is decided by its size and its lifetime, never by its type.**  A value of a non-recursive
inductive type of numbers (`option int`, `int + int`, an enumeration whose constructors carry numbers) has a fixed size: it is
its tag and its fields, the way a record is its fields (D15), and C writes it as a tagged struct passed by value — wherever it
goes, a call's result and a loop's state included.  A constructor or a function built and taken apart in the same text (`match
k a with Some x => ..` where `k` is put in, `cons x nil` matched at once, `(snd p) (fst p)` on a pair holding a function, a
function returned by a helper that is put in) needs nothing at run time at all.  A memory made by a `let` and never used is not
a second version.  None of these is refused; each is a gap until it is translated (§3.5).

Each refusal names the reason and the library to use instead.  **Every other refusal is a gap in the translator, not a rule of
the language** — and the construct table (§3) is the list of them.

### 0.6 The target: freestanding, portable C — and what is not included

The target is what a freestanding, portable C compiler offers: the language and the primitives, nothing above them.
**Not included, because C does not include them either:** a scheduler, process and thread tables, a memory manager, a driver
set, a filesystem.  These are programs a user writes in Rocq on the primitives (`hw/kernel.body` is a small one), with the
hardware layouts taken from the manual.  The only per-architecture parts are the hand-written stubs and the bodies of the
primitives.

**Not goals:** a model of the CPU or the instruction set; proving data-structure invariants away (bounds guards cost little and
stay unless a proof removes them); a garbage collector or any run-time system; floating point and I/O until a program needs
them.

### 0.7 The yardstick of speed: C written the same way

The program as written decides the speed.  The translation reflects the structure of the Rocq text in the C it makes, as a C
programmer's text would: a loop that keeps its running total in a memory cell is as slow as the same loop in C, and it stays
that way.  A pass that rescues a badly structured program is not wanted; it hides the cost from the person who wrote it.

So the yardstick is **C written the same way**, not the best C for the task.  Where our output is slower than that C, the
difference is ours to remove, and only by a change that is **general** (§6.4): it removes a cost our translation adds to every
operation, or it is a standard pass C compilers apply to any program; it is stated and proved once; it is not keyed to a
benchmark.  Where our memory model knows more than a C compiler does (block numbers are constants, a read outside a block gives
0, so different blocks never alias and a read can run early without a fault), a pass may do more than clang can.

### 0.8 The yardstick of proof time

Proof time is development time.  The C is a function of the program alone (the generator is proved once), so it can be printed
at once; the per-function statements are checked behind it, each in its own file, in parallel, and remembered by content
(§7).  An unchanged program rebuilds in about 15 s; a cold test kernel proves in under a minute.  Improvements to proof time
are general (tactics, the walk, the cache), never per program.

### 0.9 HOW TO DECIDE — when this file does not say

This section exists because the goal is easy to drift from: each local step can look reasonable and still lead away from it (a
convention that makes the translator simpler, a check that makes a proof go through, an optimization that wins one benchmark, a
limit written down instead of removed).  Before any change, answer these in order; a change that fails one is not made, however
convenient.

1. **Does the trusted base stay the same?**  Nothing new is trusted: the translator stays unchecked-but-verified-per-program, the
   generator's theorem covers the change (a new operation is a new case of it), and a machine operation comes with a law proved
   for the model.  If the change needs a new assumption, it is a decision for the owner, not a step.
2. **Is it natural and native?**  Would ordinary Rocq or Lean code look like this?  Then it must be accepted.  Does the change
   make the user write something they would not otherwise write (an order of parameters, a wrapper, a special name, a budget to
   guess)?  Then it is the wrong change, unless Rocq itself imposes it or a theorem needs it (D22).  The only refusals are the three
   of §0.5.
3. **Is it general?**  It applies to every program with that construct, not to the program in front of you.  It is found and
   tested by construct (§3), never by fixing the sample that failed.  An optimization removes a cost the translation adds to every
   operation or is a standard C pass, proved once (§0.7).
4. **Does it keep the C of existing programs?**  Byte-identical C for programs that do not use the change, or a measured reason
   why not, with the corpus timed.
5. **Is it closed by a construction?**  A gap is closed when the cell is translated and proved; a boundary when it has a pinned
   cell and a control (§3.6).  Writing the limit into a README closes nothing.
6. **Is the proof time still small?**  General tactic changes only; no per-program proof scripts; the cold kernels stay under a
   minute and a rerun stays at the cache's floor.

**When two of these conflict:** soundness (1) over everything; then natural acceptance (2); then generality (3); then speed of the
C; then proof time; then the size of the change.  "Proper over fast" (D20): the straightforward, correct construction wins over
a quick one even when the quick one passes the gate.

**When the right move is unclear:** measure before deciding (a cell of the table, a timing on one pinned core, a profile of the
proof); record the measurement here (§11); then decide by the order above.  A guess becomes a rule only after it is tested.

### 0.10 When the goal is reached

All of these, on one tree, each by its own check — not before, and never by a description:

| # | Condition | Check |
|---|---|---|
| 1 | **No over-rejection by construct**: every cell of the construct table translated and proved, or pinned by design with a control — the family that varies the translator's own conventions included (§3.7) | `MD=1 bash proved/matrix/run.sh`: 0 gaps |
| 2 | **Rocq's own spelling**: measure recursion read in Rocq's forms (§4.5); type and instance arguments specialized | the `wfix` examples written as `Program Fixpoint` compile, prove, give the same answers |
| 3 | **The operations of freestanding C** (§2.1) | every row of §2.1 proved, each with an example |
| 4 | **Written and compiled like `lean --c`**: one command in an ordinary `.v` file, the C at once, the proofs behind it, refusals that read like type errors (§12.B, D23) | every example and corpus program compiled that way, with the same C as before |
| 5 | **Freestanding** (§9.5) | the generated C of the examples builds with no hosted headers and runs |
| 6 | **C speed**: no cost the translation adds to every operation is left once the general passes are in (§6.4) | the same-shape benchmarks (`tests/mkworst.py`) against C written the same way; `proved/corpus.sh times` |
| 7 | **Trust unchanged** | `ASSUME=1 bash proved/make.sh` lists what §1.10 lists and nothing more |
| 8 | **Proof time small**: cold test kernels under a minute, an unchanged rerun at the cache's floor | `KQ_TIMES=1`; the kernels' times |
| 8b | **No proof search per program**: every program is compiled through the verified `compile`, with only the conversion check `denote s = f` (§1.12) | the gate with the walk switched off |
| 9 | **Hardware by the user**: the test kernels prove and boot; an architecture is added from its manual over the generic primitives with no change to the core (§9.1) | `bash hw/check.sh` |

Then the end state: **naturalness as a theorem** (§3.8, §12.M), which turns condition 1 from a measurement into a claim — the
order the cost-shape work followed by the owner's decision there (close every decidable over-rejection row, then prove the
completeness theorem).  Concurrency semantics (§12.G) and one text carrying its cost and its C (§12.N) go beyond the goal: they
make it stronger and are taken when their condition arises.

---

## §1. THE ARCHITECTURE AS BUILT

### 1.1 The pipeline

| Step | File | How it is justified |
|---|---|---|
| Rocq function → KQL | `proved/KQMTrans.v` (a MetaRocq program) | per program: for each function the statement `runk P f args M (g xs M) M'`, proved by `kqm_auto` (`proved/KQMAuto.v`) and checked by the kernel.  **The translator is not trusted** |
| KQL → Clight | `proved/KQLGen.v` | proved once, for every program: `sim` (`KQLProof.v`) for the arithmetic, `simk` (`KQM.v`) with the kit's memory; top theorem `kit_function_correct` (`KQMTop.v`) |
| Clight → assembly | CompCert 3.17 | CompCert's pass theorems, composed in `KQLBack.v` (the measured builds use clang instead) |
| Clight → C text | `proved/KQLPrint.v` | not proved: prints each Clight construct as the C that means the same; a choice between two atoms as the kit's `kq_sel_*` |
| tables, driver | `proved/kitc.py`, `sup/v4/kq_io3.c` | trusted C: fills the memory tables from the loader's blocks and calls the entry function |
| machine operations | `hw/kq_hw.h` | trusted C bodies of the external functions the generated code calls, assumed through `hw_law` / `hwf_law` |

`kit_function_correct`: if the KQL program runs function `g` on `vs` from the kit's memory `M` to `v` and `M'`, then the
Clight function the generator made from it, called on the numbers of `vs`, from any Clight memory that holds `M` in the
tables, returns the number `v` and leaves a Clight memory that holds `M'`.  Composed with the per-function statement, the C
computes the Rocq function.

**Why not CertiRocq's own front end.**  CertiRocq's proof of its translation to λANF (`convert_top_anf_correct`) assumes the
program has no primitive operations (`no_prims`), and λANF's semantics for its optimisation passes (`bstep`) has no rule for
them.  Every program here uses `PrimInt63`, so those theorems say nothing about it.  This route does not go through them.
(The repository's first route, "the kit route", does use CertiRocq for speed with an unproved but tested checker; the proved
route reaches the same speed with proofs — §6.1.)

### 1.2 KQL: the target language of the translator

A small first-order language in A-normal form over 63-bit machine numbers (`proved/KQL.v`, memory semantics in `KQMSem.v`):

```
atoms        Avar x | Aint n | Abud n          (Abud: a budget written as a number, read as kq_nat n, never built as unary nat)
expressions  Eret a                            return
             Eop x op a b k                    x := a op b (add sub mul divs mods and or xor shifts comparisons)
             Eif c a b t e                     branch on a comparison of atoms
             Esel x c a b t e k                x := if (a c b) then t else e   -- a conditional move, no jump
             Ecall x g args k                  call (a call in tail position of g itself is a loop: Eloop args)
             Ekld x h i k  / Ekst h i v k      wide cell read / write (8-byte cells)
             Ekld32 / Ekst32                   32-bit cells of a narrow block
             Ekld8 / Ekst8                     one byte of a narrow block (one C byte access)
             Eksize x h k                      the size of a block now
             Ew64 ...                          one 64-bit unsigned operation on two halves (u64)
             Ehw op args k                     a machine operation on the memory (loads, stores, atomics, fences, copies, kq_grow ..)
             Ehwf x op args k                  a number the machine gives without a memory (addresses, interrupt info ..)
             Eloop args                        the function itself again (a tail call)
```

Functions take atoms and give one number; a function that gives back two numbers returns the first and puts the second into
cell 0 of block 63 (the slot block), which the caller saves and restores (§1.4).  The evaluation relations are `evalk` /
`runk` (a function that reads or gives a memory) and `evalx` / `runx` (a function that writes the memory and gives a number).

### 1.3 Numbers

A 63-bit number `n` is the 64-bit word `2n + 1`, the way the kit holds it.  Addition is `a + b - 1`, subtraction
`a - b + 1`, the orders are C's orders on the words (signed ones through a cast), `land` and `lor` are the same on the words,
`lxor` is `(a ^ b) | 1`, a shift amount or a divisor is `w >> 1`.  No mask is needed.  Division by zero, a shift of 63 or more
and the signed remainder are tested first, so the C has no undefined behaviour.  Lemmas: `KQTArith.v`, `KQLSigned.v`.  One fact
Rocq's integer axioms leave open — the smallest number divided by -1 is the smallest number — is stated as `divs_min_neg1`
(Rocq's own computation agrees).

`u64`: a record of two numbers (`w_lo`, the low 63 bits, and `w_hi`, the bit above) with primitive projections; meaning
`u64_val`; every operation is `w64_op o a b`, one KQL instruction (`Ew64`) whose C packs the halves into one
`unsigned long long`.  `w64_op` is **sealed** (defined behind a `Qed`, its meaning is the equation `w64_op_unfold`) so no
conversion — the kernel's included — works a chain of operations out (§11, F7).

### 1.4 The memory

The memory is the kit's abstract `mem` (`KQRun.v`) with `rd`, `upd`, `kq_size`, `kq_grow` and the narrow-block operations;
what is assumed of it is one record of laws, `KQSpec.real_laws` (one axiom), and `KQModel.v` proves every law for a model, so
the laws cannot contradict each other.  A block number and a cell number are run-time numbers; a read outside gives 0 and a
write outside changes nothing (negative numbers included).

In C the memory is two global tables set by the loader: `kq_tab` (the address of each of 64 blocks) and `kq_lens` (twice the
size of each); narrow blocks have `kq_tab32` / `kq_lens32`.  `kmrel M m` says a Clight memory `m` holds `M` in that layout; a
cell holds the word of its number, so a read or a write moves the word as it is.

- **Narrow blocks**: cells of 4 bytes (`rd32`, `upd32`, a signed 32-bit number); bytes and halfwords (`rd8`/`upd8`,
  `rd16`/`upd16`) are views of the same raw memory, little-endian (`KQBytes.v`, `KQByteArith.v` prove the C byte access
  against CompCert's memory).
- **Views** (`lib/View.v`, laws in `lib/ViewSpec.v`): the same narrow block seen as 64-bit cells (`view_rd64`/`view_upd64`)
  and as a system number in 8 bytes (`view_rdn`/`view_updn`).
- **The slot block** (63): carries the second result of a function that gives back two numbers; its room is its starting
  length (`1 < kq_len 63`), which the driver provides.
- **Growing blocks**: `kq_grow h n s` (a machine operation, `HGrow`, assumed like the others; hosted, it is a `realloc` that
  refills the tables; exit code 3 when memory runs out) and `kq_size h s` (one instruction, `Eksize`).  Laws `size_grow`,
  `rd_grow`, ..., `size_neg`, all proved for the model.
- **Several processors**: blocks shared with another processor are listed (`kq_shared`) and reached only through marked
  atomics (§9.4).

### 1.5 The translator (`proved/KQMTrans.v`)

A MetaRocq program run inside Rocq (`MetaRocq Run (kqm_translate main "name")`): it quotes the program, computes the set of
functions to translate, translates each to KQL, and defines for each function `f_kqm` (its KQL), the program, and `f_kstmt`
(its statement).  It prints `KQM: N functions: ...`, the helpers, the groups of mutual functions, the functions with two
results and the entry; `kitc.py` reads those lines.

**What a variable of the text stands for** (`ent`): `ENat a` (a counter, the atom holds `ofn` of it), `EInt a`, `EBool a`,
`ECmp c a b` (a boolean that is one comparison, kept as it is), `EMem v` (the memory, at version `v`), `ERec es` (a record or
pair: its fields), `ESelf`, `ESib kn` (another function of the same mutual fixpoint), `EFun f m` (a parameter that is a
function known where the function is called: that function, with `m` captured variables — §5.2).

**Kinds of parameters** (`kind`): `KNat`, `KInt`, `KMem`, `KRec mk ks` (a record of numbers and counters, held as the flat list
of its fields).  A function's information (`finfo`): its name and KQL id, the kinds of its parameters, whether it gives a
memory, recurses, writes, gives two results, its counter-bound index, its name, the functions it was given (`fi_fixed`), the
captured variables of those (`fi_capk`), and the shape of its own parameter list (`fi_nrest`, `fi_restmem`).

**Which functions are translated** (`reach`): every function of the file reachable from the entry, callees first.  A function
of the file that recurses, or the root, is a KQL function.  A helper that does not recurse is written out where it is used,
unless it is large (more than 40 nodes of its text: then it is a function of its own, proved once).  A recursive function that
takes functions is a **template**: every call that gives it known functions makes a copy for them (`site_key`, `inst_body`;
§5.1).

**The translation proper**: a family of mutual functions over the quoted term in continuation style — `tr_int` (a number),
`tr_nat` (a counter), `tr_mem` (a memory), `tr_cond` (a test, two continuations), `tr_let`, `tr_recv` / `tr_vals` / `tr_field`
/ `tr_rec_case` (records), `tr_boolval` (a boolean as 0/1), `tr_call` (arguments of a call), and `tr_tail` (the body in tail
position, where self calls are loops).  `app_norm` normalizes the head of an application (beta through `beta_lets`, partial
applications merged, a known function parameter put in); `deep_norm` does the same through the arguments (§5.5).

**Two rewrites keep the C free of jumps on data**, as the kit's own translator does:
- a choice between numbers (`if c then a else b`, nested ones included) is worked out both ways and taken with a conditional
  move (`Esel`); the two numbers may read the current memory, up to three reads in all, because a read is total;
- `if c then f a1 .. an else f b1 .. bn` in tail position (a chain of tests, every end a call of the function itself, the
  arguments differing only in numbers and in the values `upd` writes) becomes one call whose arguments are such choices.  These
  stay plain arithmetic: a chain of tests on a state that cycles is predicted well, and a conditional move in its place makes
  each round wait for the one before (measured, §6.3).

A choice on `a && b`, `a || b`, `negb a` is translated as choices on the parts, and the proof rewrites the goal the same way
(`kqm_ifs`), so the kernel's check needs no case split per test.

**Booleans (2026-10-30).**  A boolean is the number 1 or 0 (`EBool`, and the kind `KBool` for parameters and record fields).  A
recursive function may give one back (`fi_rbool`): its value is returned as 1 or 0.  At the end of such a function `a || b` is
read as `if a then true else b` and `a && b` as `if a then b else false`, so a call of the function itself in `b` stays a loop
(what C's short-circuit makes of it).  A call of a function giving back a boolean is a call followed by a test against 0 where it
is a test (`tr_cond`), and the number itself where it is a value (`tr_boolval`).  A test made by an `if` is the first test, then
the test of the branch taken (nothing is computed twice); a test made by a `match` on a counter is the counter's test against 0.
A boolean value made by an `if` of cheap branches is a conditional move, otherwise a branch.

**Values built and taken apart in place (`knorm`, 2026-10-30).**  Every reader starts from `knorm Γ t`, which adds to `app_norm`:
a `match` on a constructor takes its branch with the fields bound as `let`s (case of a known constructor; a memory field bound
last, so a number read before the write is read first); a `match` on a `let` or on an `if` is put inside it; a helper's call as a
scrutinee or a `let`'s value is written out first (`unfold_h`); `fst`/`snd` (and a primitive projection) of a constructor is the
field; a `let` of a constructor value is its fields bound as `let`s; a `let` never used is dropped; a `let` of a number-and-memory
pair made by a call becomes a `match` taking it apart.  **These rules fire only for values the readers do not hold as they are**
(`held_ty`: not a number, counter, boolean, memory or record of numbers) and for a dead memory `let`, so a program read before is
read the same way — measured: the C of every example, corpus program and kernel (142 files) is byte-identical with and without
these changes.  The readers rebind `t` to the normalized term, because a case that builds from `t` itself (a literal's atom) must
see what the `match` saw (§11, F41).

**A number and a memory as a result (`fi_rim`, 2026-10-30).**  A function giving back `int * mem` (or a record of one number and
one memory, `mem_pair`) returns the number and ends with the memory: the pair at its end is the number worked out first, then the
memory's work; a call is one call, the version of the memory bumped, its pair taken apart where it is made (`tr_rec_case`).  A
record chosen by a test is the test, then the record of the branch taken (`tr_recv`).

### 1.6 The per-function statement and its proof

For a function `g` with KQL id `f`, the statement says that running `f` on the arguments from memory `M` gives the Rocq
result:

```
gives a memory:          forall xs M, bounds -> runk P f args M 0 (g xs M)
gives a number, reads:   forall xs M, bounds -> runk P f args M (g xs M) M
gives a number, writes:  forall xs M, bounds -> runx P f args M (g xs M)          (the end memory exists)
gives two numbers:       ... runk P f args M (fst (g ..)) (upd 63 0 (snd (g ..)) M), with 1 < kq_len 63
gives a boolean:         as for a number, with the value kq_b2i (g xs M), the number 1 or 0 (KQMAuto.v)
gives a number and a memory:  forall xs M, bounds -> runk P f args M (fst (g xs M)) (snd (g xs M))
```

A boolean parameter is quantified as a `bool` and passed to the KQL function as `kq_b2i x`.

`bounds` says each counter is below `cbk i` (a bound a little under 2^62, lower for functions later in the file, so a caller's
counter plus a few is still inside the callee's).  A record parameter is the record's constructor applied to its fields.

**The proof** (`kqm_auto`, `KQMAuto.v` + `KQMNames.v`): `hnf`; if the first parameter is a counter, induction on it
(`kqm_prove`), else no induction (`kqm_prove0`); then `kqm_enter` (open the KQL body on the left and the Rocq definition one
step on the right) and `kqm_walk`, which repeats one step per KQL instruction: an `Eop` is `K_op` with the arithmetic
normalized (`kqm_norm`), a read or write uses the memory laws, an `Eif` splits on the test (`kqm_test`), a call uses the
callee's statement (put in the context with `pose proof`) or the induction hypothesis (`kqm_call`, chosen by the callee's id),
a budget is bounded by `kqm_bound`.  Three devices keep long bodies tractable (§7.2): the variable bindings are compacted into a
tree every 24 bindings (`kqm_compact`), the memories of the function's `let`s get names (`kqm_name_lets`, `kqm_share`), and
counter rewrites are tried only where a counter is added to and only inside an induction.

Booleans in the walk: `kq_b2i` is unfolded with the other definitions (`kqm_red0`); a test of a boolean held as 1 or 0
(`eqb (if c then 1 else 0) 0`) is rewritten to the test of `c` itself (`b2i_eqb0`) before it is split on — the shape is looked at
first, so this costs nothing where it does not apply — so splitting on it splits the Rocq text's `if c` too; the function a
statement is about is found inside `kq_b2i` (`kqm_vhead`).  A function giving back a number and a memory is listed with the
functions giving back two numbers (`KQM pairfns`), whose pairs the walk already takes apart (`kqm_pairs_on`).

**Budgets.**  `kq_nat x` is the counter of a number: `x` if positive, 0 otherwise, at most 2^60 (`kq_nat_le`), computed by
`kq_nat_go 63` without building a unary number.  A budget written as a number is the atom `Abud`; a budget made only of numbers
written in the program (a measure applied to constants) is also `Abud` (§5.5); a budget worked out at run time is clamped by two
conditional moves.  `kq_nat` is opaque to conversion (`Strategy opaque`), so no proof ever unfolds `kq_nat 100000000`.

### 1.7 The C, the build, and the driver (`proved/kitc.py`)

`kitc.py NAME...` (in the image, in the repository): reads `hand/NAME.body` or a path; puts the libraries the program names in
front of it (`slab_` → `lib/Slab.v`, `view_` → `lib/View.v`, `loop_`/`wfix` → `lib/Loop.v`, the text between the
`-BEGIN`/`-END` markers); translates (`proved/gen/NAME_t.v`, compiled to a `.vo` other files import); computes a key per
function and checks each function's statement in its own file (`proved/gen/NAME_u_F.v`), in parallel (`KQ_JOBS`), unless the
key is in the cache (`proved/gen/cache/`); prints the C (`Redirect .. Eval vm_compute in (KQLPrint.pstr .. (tr_kit_program
NAME_prog))`); writes the driver (fills the tables from the loader, calls the entry with the numbers `main` gives); builds
`bin/P_NAME` with the kit's support code.  Options: `--no-build`, `--bare`, `--secondary --prefix= --entry=` (a second program
of a kernel), `--ext=` (the program's own routines), `--emit-first` (the C printed and built right after the translation, the
proofs after it — the C is a function of the KQL program alone), `--no-proof` (the C without the proofs; with `--no-build`, a
check of what the translator reads).  Measured on `CF622F` (8 functions, the corpus's slowest proof): the binary at 15.3 s and
the proofs at 76.2 s with `--emit-first`, against nothing before 76.7 s in the default order; the check alone 14.9 s, nearly all
of it the translation.  The default order is unchanged, so the gate means what it meant.  Environment: `KQ_STRICT=1` (a proof that fails is an error, not
`Admitted`), `KQ_TIMEOUT` (seconds per proof, default 300), `KQ_JOBS` (default 3), `KQ_MONO=1` (the whole program in one file,
no cache), `KQ_TIMES=1` (each proof's time).

`main` today is written in the `.body` convention (`Definition main : int := let kq_keep := .. in solve (kq_nat (kq_arg 0))
.. (kq_input 0)`).  Replacing it by a command that reads the entry's signature is §12.B.

### 1.8 Machine operations

The operations of `KQRun.v` that reach the machine (`hw_load`, `hw_store`, `hw_store64`, the atomics and compare-and-swap,
`hw_fence`, `hw_copy`, `hw_fill`, `hw_cmp`, `hw_call`, `hw_run`, `hw_code_sync`, `kq_grow`, interrupt-take) are read like
`upd`: each takes the memory and gives it back, and what one reads goes into the cell it is told to fill.  In KQL they are one
instruction, `Ehw`, whose meaning is the kit's own operation on the abstract memory (`hw_sem`).  The generator emits it as a
call of an external function (`f91000` ..), and the C bodies are the kit's (`hw/kq_hw.h`: `volatile` accesses, C11 atomics,
`memmove`), so a device access is never merged, moved or left out.  Numbers the machine gives without a memory (`hw_addr`,
`hw_irq_info`, `hw_irq_entry`, `hw_cpu_code`, `hw_sym`) are `Ehwf`.

`kit_function_correct` takes the hypotheses `hw_law` / `hwf_law`: called from a Clight memory that holds `M`, each external
function finishes with no event and leaves a memory that holds `hw_sem o vs M` (or gives the number the abstract one names).
They are not axioms of Rocq; they are what the theorem assumes of the C bodies and of the machine — the same kind of statement
as the loader's.  `KQSpec.real_laws` says what each operation does to the memory (a load fills its cell and no other, a store
changes no wide cell, the trace records it); a proof about a program holds for every number a device could give back.

### 1.9 Libraries and their theorems

| Library | What it is | Theorems (file) |
|---|---|---|
| `lib/Slab.v` | objects with generation-checked handles on one block that doubles when full (a fixed pool when `grow = 0`) | `lib/SlabSpec.v`: `slab_take_live`, `slab_free_kills`, `slab_reuse_keeps_dead`, `slab_get_set`, and the invariant `slab_inv` kept by `slab_init_inv`, `slab_set_inv`, `slab_free_inv`, `slab_take_inv` |
| `lib/View.v` | one narrow block as bytes, halfwords, words, 64-bit cells, numbers in 8 bytes | `lib/ViewSpec.v`: `view_upd64_frame`, `view_upd64_rd`, `view_rd64_upd64` |
| `lib/Loop.v` | `loop_up`, `loop_up_m`, `loop_find`, `loop_two`, and recursion with a measure `wfix1..3`, `wfix1m..3m`, `wfixm1..2` | `lib/LoopSpec.v` (`loop_two_ends`, generic `wf_indep`, `wf_eq`, `wf_wrapper_eq`, `wf_ind`), `proved/KQLoopSpec.v` (per form `_eq`, `_ind`, `_dec_tac`), `proved/KQLoopExamples.v` (`tri_closed`, `gcd_correct`) |
| `hw/lib.body` | a spinlock (compare-and-swap with a pause, a release store) and kernel helpers | (properties of the lock rest on the hardware's atomics; §9.4) |

`hw/spec.sh` compiles the laws, the model, the demos and the library specs, and checks that the library theorems rest on
`KQSpec.real_laws` alone (and the model on nothing of ours).

### 1.10 What is trusted, exactly

`Print Assumptions kit_function_correct` (`ASSUME=1 proved/make.sh`): Rocq's 63-bit integer axioms; `divs_min_neg1`; the kit's
memory primitives `KQRun.rd` / `upd` / `kq_size` / `mem` and `KQSpec.real_laws`; classical axioms CompCert uses.  No admits.
Outside the proofs: the loader that fills the tables, the driver in `kitc.py`, the printer, clang, and the C bodies of the
machine operations with the laws the theorem assumes of them.  The per-program statements add nothing: the translator's output
is checked by the kernel every time.

### 1.11 Where the architecture goes: proofs built by construction, the CakeML way (decided by the owner, 2026-10-30; its plan superseded the same day by §1.12)

*The analysis in this section stands; its plan (converting the walk to proofs built by construction) was superseded the same
day by the owner's requirement of zero proof time for other people's programs — the decision in force is §1.12 (D26).*

**What kind of compiler this is.**  Three ways to get from a program to machine code exist, and the words for them are easy
to confuse:

| Style | What is proved | Example |
|---|---|---|
| **unverified compiler** | nothing; the compiler is trusted code | Lean's `lean --c` (LCNF → IR → `EmitC`) |
| **verified compiler** | one theorem about the compiler: for every program, its output is correct | CompCert; CertiRocq's passes; the CakeML compiler; **our generator** (KQL → Clight, `kit_function_correct`) |
| **proof-producing (certifying) translation** | nothing about the translator; each run produces a theorem about that program, checked by the prover's kernel | CakeML's HOL → CakeML translator; Pancake's decompiler; **our translator** (Rocq → KQL, `f_kstmt` per function) |

Our route is the third on top of the second: every compiled program has an end-to-end, kernel-checked theorem (the C computes
the Rocq function), and the top half adds nothing to what is trusted.  Say "proved end to end for every compiled program", not
"a verified compiler": a verified compiler has one theorem quantified over all programs, and our top half does not.

**The precedent: CakeML and Pancake** (github.com/CakeML/cakeml, its `README.md`, `translator/README.md`,
`pancake/README.md`, read 2026-10-30).  `translator/` is *"a proof-producing translator from HOL functions to CakeML"*
(`ml_translatorLib.sml`; its relation `Eval` is defined in `ml_translatorScript.sml`); the CakeML compiler below it is verified
down to machine code and compiled by itself inside the logic.  Pancake is *"a C-like compiler built from the lower parts of the
CakeML compiler"*, and its programs are verified through *"the proof-producing Pancake decompiler"*.  So the strongest project
of this kind uses exactly our split: per-program proofs at the top (where the source is functions in the logic), one proved
compiler at the bottom.  The source being functions in the logic is what makes theorems about the program carry over to the
machine code — the same as here, where the program is the Rocq function.

**The one difference that matters.**  CakeML's translator *builds* the theorem as it translates: one lemma per construct of the
source, of the form "if the parts compute their values, the whole computes its value" (for example: if `c`, `a`, `b` compute
`cv`, `av`, `bv`, then `If c a b` computes `if cv then av else bv`), stacked along the function's text.  A function it accepts
always gets its theorem; nothing is searched.  Ours translates first and then a tactic (`kqm_auto`, the walk of §1.6)
*searches* for the proof.  That search is where the "proof the tactics do not find" gaps (§3.5) and most of the proof time
(§7) come from.

**The decision.**  The top half moves to proofs built by construction: the translator emits, with each piece of KQL, the lemma
that justifies it, applied to the Rocq subterm it came from.

| Property | Today | After |
|---|---|---|
| sound (the C equals the Rocq) | yes, every program, kernel-checked | the same — this adds no strength |
| proof completeness: every program the translator accepts gets its proof | no — the walk can fail to find one | yes, by construction |
| language completeness: nothing natural refused | measured by the construct table | still a separate job (which constructs the translator reads); provable as a theorem about the translator, which is a Rocq function (§3.8, §12.M) |
| one theorem "for every program, correct" | no | still no: that needs the translator itself proved against MetaRocq's semantics of Rocq (months; CertiRocq's front-end theorem leaves out primitive integers, which every program here uses). CakeML lives with the same limit at its top |
| proof time | 35–54 s per test kernel, mostly search | expected much lower (an estimate until the spike measures it) |
| cost of a new construct | a translator rule plus tactic tuning, then hope the walk finds it | a translator rule plus one lemma |

**Why not a verified translator instead.**  It would give the single theorem, but every construct must then be proved inside
the translator's theorem, over MetaRocq's formal evaluation extended with primitive integers — the cost-shape kind of work, for
months.  Completeness does not get cheaper that way: the same constructs must be handled.  The proof-producing route gives every
property except the single theorem, at a fraction of the cost.

**The cost-shape work did build a theorem of exactly that kind**, which is the main reason it took one to two months while this
route moves fast.  Its theorems are quantified over every program the checker accepts and proved against MetaRocq's formal
evaluation of Rocq: `graded_run_bounded` (from the one boolean the grader computes, every run of an accepted program keeps the
bound), `graded_sim` (the simulation across all 13 rules of MetaRocq's `eval`), `erased_ops_bounded_by_checker` (the same
carried across MetaRocq's erasure) — with a ledger of what they still assume (the typing layer's axioms, the well-formedness of
the global environment).  KernelQ's `docs/rocq-cost-shape-solution.md` and its research files hold them.  A verified Rocq → KQL
translator would be the same kind of proof — harder in that it is full equality of results and memory with KQL as the target,
easier in that there is no cost measure and no adversary — and the cost-shape machinery (run lemmas over MetaRocq's `eval`, the
induction over its rules, the bridge through erasure) is what it would reuse.  So the single theorem is not ruled out forever;
it is not on the plan, and if it is ever wanted it does not start from zero.

**What does not change.**  The trusted base (§1.10); the generator and its theorem; the per-function statement `f_kstmt` (so
the meaning of the theorem and the C are unchanged); the proof cache; the construct table and the gate.

**What it replaces.**  The searching parts of `KQMAuto.v`: `kqm_test` (splitting on a test in the goal), the splitting loop of
`kqm_fin`, `kqm_known` / `kqm_hyps_known` / `kqm_known_conv` (re-finding tests already split on), `kqm_splitall`, the choice of
rewrites in `kqm_norm`, and the named-memory fallback of `KQMNames.v` (the lemmas build the memory terms themselves).  `kqm_call`
picks the callee's statement by its id and stays.

**The design, in outline.**  The relation is the existing `evalk` / `runk`; the lemmas are stated over the Rocq constructs the
translator reads, so the Rocq side never needs searching.  For a test, instead of `K_if` followed by a destruct:

```
evalk P f rho M et v1 M1 -> evalk P f rho M ef v2 M2 -> aval rho a = Some va -> aval rho b = Some vb ->
evalk P f rho M (Eif c a b et ef) (if cmp_sem c va vb then v1 else v2) (if cmp_sem c va vb then M1 else M2)
```

— the Rocq `if` is the conclusion, so the translator, which knows the Rocq `if` it is translating, applies it directly.  The same
for a conditional move, a counter match (with `ofn`), a `let`, a read and a write (with the memory laws), a call (with the
callee's statement), a loop (with the induction hypothesis), a boolean held as 0/1 (`kq_b2i`), a record taken apart.  Side
conditions — a counter below `cbk`, a budget under 2^60, room in the slot block — are designed to follow from the statement's
own hypotheses and are closed by a decision procedure (`lia`, `vm_compute`), never by search.  Where the Rocq side and the
lemma's conclusion are equal only by computation (unfolding the function one step, `kq_b2i`, `fst`/`snd` of a pair), the kernel
checks that by conversion, which is a check, not a search.

**The plan** (§12.Q):
1. Land the current batch of construct-table work (its gate and full table).
2. **A spike**: lemmas for `Eop`, `Eif`, `Esel`, `Eret`, `Ecall`, `Eloop` and the counter match, emitted by the translator for
   `proved/examples/wfix.body`, one corpus program and the longest kernel function (`x86_setup`, ~2,400 steps).  Measure proof
   time and acceptance against today's walk on the same programs.  Measure first (§0.9): the plan continues only if the spike is
   at least as reliable and faster.
3. Convert construct by construct.  The walk stays as the fallback until every construct has its lemma; the table and the gate
   stay green at every step.
4. Then the completeness theorem over the grammar of the accepted fragment (§3.8, §12.M).

**The bottom half.**  Release builds go through CompCert's `ccomp` (§12.H), so that the bottom is verified down to assembly as
CakeML's is, rather than ending at our printer and clang.

### 1.12 THE DECISION IN FORCE: a verified compiler by reflection — zero proof search per program, nothing added to the trust (owner, 2026-10-30)

**The requirement (owner):** compile other people's programs with no proof time: "need to compile others' programs with zero
proof time, I need this, it takes too long".  The owner chose "a verified translator now", accepting added trust if needed.  It
turned out that no trust has to be added (below).

**The four routes, and the verdict on each:**

| Route | Proof work per program | Added to the trust | Verdict |
|---|---|---|---|
| emit then prove (§12.B) | the C in seconds; the walk's proof runs behind and arrives later | nothing | **the interim**, until the compiler below covers a program |
| proofs built by construction (§1.11, D25) | much less than the walk, not zero | nothing | **skipped** (owner): the walk is not converted |
| verified translator against MetaRocq's semantics of Rocq | none | MetaRocq's quote of the program, MetaRocq's typing and erasure assumptions, well-formedness of the environment (the cost-shape ledger) | **rejected**: MetaRocq's formal evaluation cannot run our programs (next paragraph); fixing that is an upstream extension of MetaRocq for months, and it adds trust |
| **verified compiler by reflection** | one conversion check (`denote s = f`), no search | **nothing** | **chosen** |

**Why MetaRocq's semantics cannot be the source (measured 2026-10-30, in the image's MetaRocq sources).**  The erased
evaluation `EWcbvEval.eval` has 21 rules (`eval_box`, `eval_beta`, `eval_zeta`, `eval_iota`.., `eval_delta`, `eval_construct`..,
`eval_prim`, `eval_atom`); `eval_prim` / `eval_primitive` only says a primitive *value* (`prim_int i`) evaluates to itself, and
PCUIC's `PCUICWcbvEval` is the same.  There is no rule for a primitive *operation*: `PrimInt63.add` is a constant without a body,
so `eval_delta` cannot fire, and every program here — all arithmetic is `PrimInt63` — is stuck in that semantics.  This is the
same gap as CertiRocq's front end (`convert_top_anf_correct` assumes `no_prims`, §1.1, F1).  The cost-shape work met the same
wall and went around it, without adding a rule: its record (`docs/rocq-cost-shape-solution.md` in KernelQ, "ROUTE 1, MACHINE
INTEGERS — REFUTED BY MEASUREMENT") says a rung written with `Int63` arithmetic "would have no derivation at all, so every
theorem about it would be VACUOUS", and its programs compute on `Z`, an inductive type, instead.  So there is no extension of
MetaRocq of ours to reuse.

**The chosen design: proof by reflection.**  The standard Rocq technique for compiling functions of the logic with a compiler
proved once, used for example by Fiat Cryptography (functions reified to a syntax, compiler passes proved once, the per-program
check being the syntax's meaning by conversion):

1. **`S`, a syntax of the accepted fragment, defined by us** (a deep embedding): numbers, booleans, counters, records and pairs,
   `let`, tests and choices, calls, recursion on a counter and with a measure, functions given to functions, memory reads and
   writes, growing blocks, views, machine operations.
2. **`denote : S -> (the Rocq function it stands for)`**, a Rocq function.  It uses `PrimInt63`'s operations and `KQRun`'s
   memory operations directly, so primitives are no problem: the meaning of `add` in `S` *is* `PrimInt63.add`.
3. **`compile : S -> option KQL`, proved once**: `compile s = Some k -> k computes denote s` (the per-function statement's
   shape, for every `s`), composed with the generator's `kit_function_correct` down to Clight.  This is a verified compiler
   in the full sense — one theorem for every program of `S`.
4. **`reify`: the user's ordinary Rocq function to an `s : S`** — the current MetaRocq translator's front end, rewritten to
   produce `S` instead of KQL.  It is **not** trusted and needs no proof: its output is checked.
5. **The per-program check: `denote s = f`, by conversion** — the kernel unfolds the denotation (and only it) and compares the
   result with the user's function.  No tactic, no search; its cost is to be measured by the spike (the risk: a conversion that
   unfolds large terms; the denotation is unfolded, `kq_nat` and the user's helpers stay folded where the syntax names them).

**MetaRocq's role, after the change.**  MetaRocq only *reads* the user's function (its quote is how `reify` sees the text);
its semantics of Rocq is not used at all, for primitive operations or for anything else, and nothing about it is trusted —
`denote s = f` is checked by the kernel.  The two routes compared: the rejected one has one theorem over MetaRocq's model of all of
Rocq and trusts the quote; this one has one theorem over `S` and checks the reification.  If one day even the conversion check is
too slow, it can be skipped — then `reify` is trusted, exactly as the rejected route trusts the quote — so this route is never
worse on time and, by default, adds no trust.

**If the MetaRocq route is ever reopened.**  It has two problems, and only the first is about integers.  (1) Primitive
operations cannot be evaluated in MetaRocq's semantics (F38).  The ways to fix that, none done here: (A) extend MetaRocq itself —
a rule "a primitive operation applied to literals evaluates to its result" in its typing, reduction, evaluation and erasure proofs
(the erasure proof alone was measured at ~1,200 lines by the cost-shape work) — months, in another project, best as a
contribution upstream; (B) replace each primitive operation in the quoted program by an ordinary Rocq definition (over `Z` or
bits) that MetaRocq can evaluate, with a proof that it equals the primitive — messy, literals must be converted too, and each
program then needs a proof that the replacement keeps its meaning, which brings per-program proofs back; (C) let MetaRocq's
evaluation take an interpretation for constants without a body — the same scale as (A), the erasure proof changes too.
(2) The theorem is about the quoted program: concluding anything about the user's function means trusting MetaRocq's quote
(an OCaml plugin) and its typing/erasure assumptions — that stays after any of (A)-(C).  For the user the two routes are the
same (ordinary Rocq in, C out; what is accepted is decided by the same front end); the difference is internal.  So: reflection
now; if MetaRocq gains primitive operations upstream, the all-of-Rocq route becomes possible, with its added trust.

**What changes, what stays.**
- **Moves into the proved `compile`:** everything the translator does today beyond reading syntax — putting helpers in,
  copies of templates for the functions given (with captures), records as their fields, the slot block for a second result,
  if-conversion (`choice_ok`), merging a chain of tail calls, values built and taken apart in place (`knorm`), the memory's
  linearity (a check inside `compile`, proved sound), budgets (`kq_nat`, `Abud`), booleans as 0/1, number-and-memory results.
- **Stays as it is:** KQL, the generator and its theorem, the printer, the trusted base (§1.10) — the per-program equation is
  checked by the kernel, so the reifier adds nothing; the construct table (it now measures `reify` and `compile`); the gate.
- **Stays as the fallback:** the current translator with the walk, for programs `S` does not yet cover — the gate keeps both
  paths green — until the table's cells all go through `compile`; then the walk is retired.
- **The claim becomes:** `compile` is a verified compiler for `S` ("for every program of `S`, the KQL computes its meaning");
  each user program is compiled by reifying it into `S` and checking `denote s = f` once.

**Completeness, after the change.**  "Nothing natural is refused" splits in two: `compile` succeeds on every `s` of a grammar —
a theorem about a Rocq function (§3.8, §12.M); `reify` produces `s` for every Rocq text of that grammar — a property of the
untrusted reifier, measured by the construct table (as the cost-shape work measured that Rocq's elaborator lands in its grammar).

**The plan** (§12.V):
1. Land the current batch of construct-table work (gate, full table, commit).
2. Emit then prove (the part of §12.B that prints the C before the proof): the interim for other people's programs.
3. **The spike**: `S` with numbers, tests, `let`, calls and recursion on a counter; `denote`; `compile` to KQL proved for that
   subset; `reify` for it; on the counted loops of `proved/examples/` and a few corpus programs, measure the per-program check
   (`denote s = f`) against the walk's time.  Continue only if the check is fast and reliable (measure first, §0.9).
4. Grow `S` construct by construct, driven by the construct table: each construct is an `S` node, a `denote` case, a `compile`
   case and its proof case; the walk's fallback shrinks as `S` grows.
5. The completeness theorem for `compile` over the grammar.

**THE WEIGHING, IN FULL (the owner's questions of 2026-10-30 and the answers, so none of it is re-derived).**

*How the decision was reached.*  The owner first asked whether a verified compiler would be better than translation, citing
CakeML and Pancake; the repository was read (§1.11) and the CakeML way (proofs built by construction) was decided.  The owner then
asked for "zero proof time for other people's programs" and, offered the choice, picked "a verified translator now", accepting
added trust.  That offer had a wrong premise — that zero proof time needs added trust — and MetaRocq's semantics turned out not to
run primitive operations at all (F38).  Reflection was then proposed, compared from every side below, and the owner decided:
**"we are going with reflection"**.

*"MetaRocq is verified, so it can be trusted" — what that covers.*  MetaRocq proves its checker and its erasure correct against
**its own model** of Rocq.  Connecting the user's actual function to that model still rests on (1) the quote — the unverified
OCaml plugin that turns the function into MetaRocq syntax — and (2) assumptions inside its proofs (the cost-shape ledger shows
`guard_checking`, and on the erasure path `fake_normalization` and `fake_guard_impl_properties`).  Reflection adds none of these:
the kernel checks `denote s = f`, and the reifier is checked, not trusted.

*"But reflection still needs proof computation."*  Per program it needs one computation by the kernel: unfold `denote`, compare
with the user's function.  No tactic, no search, nothing that can fail to be found.  Expected milliseconds to a few seconds per
program (an estimate; the spike measures it, including on `x86_setup`, ~2,400 steps), against 35–54 s of search per test kernel
today.  Literal zero is possible by skipping the check, at the price of trusting the reifier — the same kind of trust the MetaRocq
route puts in its quote.  So reflection is never worse on time and, by default, adds no trust.

*Would the MetaRocq extension be the bigger win?*  What it would win: a theorem about Rocq itself rather than about `S`; a
contribution others use (CertiRocq, the MetaRocq community); and **the cost-shape work could then compute on `Int63`**, with honest
machine-word costs instead of `Z`.  What it costs: months on MetaRocq's metatheory (a new reduction rule touches confluence,
subject reduction and erasure correctness — work MetaRocq's own team has not done), then months for the verified translator on
top, then keeping a fork of MetaRocq working across releases unless it is accepted upstream.

| | reflection (chosen) | MetaRocq extension + verified translator |
|---|---|---|
| one theorem for every program | yes, over `S` | yes, over (quoted) Rocq |
| proof work per program | one kernel computation (or none, trusting the reifier) | none |
| added to the trust | nothing | the quote; `guard_checking`; the normalization assumptions of erasure |
| native for the user | the same | the same |
| maintenance | stock Rocq; MetaRocq only reads the text | a fork of MetaRocq's metatheory, broken by every release |
| risk | known technique, done before | an open research problem; can stall |
| time to working | weeks to a couple of months, our own code | many months, mostly in MetaRocq |

*The harsh version: a PhD, professors as users, production.*  **Reflection, and it is not close.**  (1) Production rules out a
private fork of someone else's metatheory.  (2) The reviewer's first question — "what connects the C to *my* function?" — has
the strongest possible answer: the kernel checks `denote s = f` for every program.  The MetaRocq route answers "an unverified
quote plus assumptions".  (3) Reflection has worked before (Fiat Cryptography; and, as recalled — check before citing — Œuf, a
verified compiler for a Gallina subset that reifies programs into a syntax and compiles through CompCert); the MetaRocq extension
is an open problem.  (4) The contribution of this project is not the front end: it is Rocq to **freestanding C with no runtime
and no collector**, memory with linearity and in-place updates, hardware primitives, operating-system kernels that prove and
boot, at C speed.  The questions a reviewer will ask, and the answers: *why not CertiRocq?* — its front-end theorem assumes no
primitive operations and its output needs a collector; *why not Œuf or Fiat?* — no memory, no runtime-free systems code, no
kernels.  Reflection gets to a complete, verified, fast system that makes that case; the MetaRocq extension would use up the
time before the systems story exists.

*Where reflection is honestly weak (and what answers it).*  It covers a fragment `S` — so the construct table and the
completeness theorem must be strong (§3, §3.8).  The per-program check grows with the program — measured by the spike on the
longest kernel function.  Measured since (F46): linear for numbers and for memories used once per step, exponential on Rocq's
stock kernel for a straight-line body that reads and then writes the same memory step after step (about 1 s at 20 steps) — a
property of Rocq's conversion that the walk shares; closed by our fork's conversion memo (D28, §12.R): 300 such steps in
milliseconds.  `S` must be designed well up front — from the construct table, so it is not redone.

*"A fragment `S` versus all of Rocq" — is that patching, or less native?*  Neither; it is a technical detail.  Both routes
cover a fragment: "over Rocq" in the MetaRocq route only means the theorem's statement mentions all Rocq terms — its translator
still refuses most of them (values that need a runtime, everything not yet built), so its real domain is "where the translator
succeeds".  `S` is the explicit name of that same set.  It is defined by construct (term formers × places × types, the construct
table), designed once and grown construct by construct, as every compiler's internal language is (Lean's LCNF, CompCert's
Clight, CertiRocq's λANF) — patching would be special cases for particular programs, which `S` is not.  The user never sees
`S`: they write ordinary Rocq, `reify` maps it, and an uncovered construct is a refusal with its reason, as today.  The only
internal differences: a new construct is an `S` node, a `denote` case, a `compile` case and a reifier case (in the MetaRocq route:
a translator case and its proof case — the same effort); and completeness is a theorem for `compile` plus a measurement for
`reify` (in the MetaRocq route one theorem over quoted terms) — minor, since the table measures the reifier anyway.  **What
decides "native" is coverage** — the table at 0 gaps, the translator's own conventions removed (§3.7), Rocq's own
`Program Fixpoint` read (§4.5) — the same work in either route.

*When the MetaRocq extension makes sense.*  As a separate, thesis-sized contribution: machine integers in MetaRocq itself, which
would also give the cost-shape work `Int63`.  Valuable; not on the critical path of Rocq to C.  Reflection now; the extension
later, if that need comes — the two do not exclude each other.

---

## §2. WHAT C CAN DO, AND ITS COUNTERPART IN ROCQ

The aim is that anything a C program does can be written in Rocq: operating systems and general programs.  C has no collector
either; a C program lays out its data and manages its memory, and so does a Rocq program here.

| C | In Rocq | State (2026-10-30) |
|---|---|---|
| integers, bit operations | `PrimInt63` operations; `u64` for full 64-bit unsigned arithmetic | proved, signed division included; `u64` proved (`proved/examples/w64.body`) |
| loops | a `Fixpoint` on a counter; `loop_up`/`loop_find` over a range; `loop_two` and `wfixN` for loops that end because a measure falls | proved; no budget to guess in the library forms (§4) |
| recursion, not only tail | any position; `wfixN` with `rec` in any position | proved (`int_nontail*` cells, `wfix.body`) |
| calls, mutual recursion | `Fixpoint .. with ..` | proved (`mutual.body`) |
| arrays, buffers | memory blocks with `rd`, `upd`; narrow blocks with `rd32`, `upd32`, bytes, halfwords | proved; a byte is one C byte access |
| structs, bit fields | records split into integers, or a layout in a block; bit fields are bit operations | records and pairs as parameters, `let`s, `match`es, fields; a recursive function giving back two numbers (slot block); **more than two numbers as a result, a choice between records, a number paired with a memory: gaps (§3.5)** |
| unions, tagged unions | a non-recursive inductive (`option`, a sum, an enumeration whose constructors carry numbers) held as its tag and fields; a raw layout in a narrow block with views | views proved; **inductive values held as tag and fields: gap (§3.5)** |
| pointers, raw addresses | an integer address into a region; RAM as one block at its base; views of one block | views proved; **an address type with proved arithmetic, pointers that outlive a call: not yet (§12.C)** |
| `malloc`, `free` | an allocator written in Rocq on a growing block (`kq_grow`, `kq_size`) | `lib/Slab.v` proved through the route (`heap.body`), invariants proved (`SlabSpec.v`); `kq_grow`'s C body assumed |
| function pointers, callbacks | a known function is put in; a recursive function that takes functions gets a copy per function given; a function chosen at run time is a dispatch on an id with the environment as an argument | proved (`dispatch.body`, `hof_*.body`) |
| closures over local variables | a function given to a template may name variables of the caller: they become parameters of the copy | proved (capture cells, `loops.body`); a closure that **escapes** is refused by design |
| local helper functions | `let g := fun x => .. in ..` | proved (put in at each use) |
| hardware access, atomics, inline assembly | primitives with a stated law and a trace; hand-written `.S` once per architecture; a program's own routines declared as primitives | proved against the laws, C bodies assumed; 5 test kernels boot (§9) |
| interrupts, faults | a second program run at the interrupt; the entry routine itself can be written in Rocq | proved and booting (`irqnow`, `fault`, `own`) |
| threads, SMP | one program per processor; shared memory only through marked atomics (`kq_shared`); a spinlock library; the launcher written in Rocq | built (`hw/lock.body` on two processors); **no interleaving semantics yet (§12.G)** |
| strings, `printf` | byte blocks and a formatting library written in Rocq | **missing (§12.C)** |
| floating point | `PrimFloat` as C `double` | **not started (hosted, §12.I)** |
| files, sockets, system calls | primitives with a trace, as for hardware | **not started (hosted)** |
| calling existing C libraries | declared as assumed primitives with stated laws | **not started**; a program's own routines already work this way |

Higher-order functions are not on the list because C has none.  A function known where it is used is inlined (what a macro or a
template does) and costs nothing.  A function chosen at run time is a function-pointer table with an explicit environment, as
`qsort` takes a comparison and a context pointer.  A closure that captures variables and outlives the call is what a C
programmer builds by hand as a struct; written implicitly it allocates behind the programmer's back, and it is refused.

### 2.1 The operation set is finite, closed and extensible — and it is checked against C's

The generator's theorem (`kit_function_correct`) is proved once, by induction over KQL, **one case per constructor of a finite
operation set** — the shape of the "mother theorem" of the KernelQ records (pedagogy doc LS.19.9: *for all programs, by induction,
one case per constructor of the finite op set*).  Adding an operation is adding a constructor, its meaning, one case of the
proof, its C, and (for a machine operation) its law with the law proved for the model.  So "the primitives are complete" is a
finite checklist against what freestanding C offers, not an open question:

| C | KQL | State |
|---|---|---|
| `+ - *` on signed integers | `Badd`, `Bsub`, `Bmul` on 63-bit numbers | proved |
| `/ %` signed, unsigned | `Bdivs`, `Bmods`; `Bdiv`, `Bmod` (division by zero, the smallest by -1 defined, no UB) | proved |
| `& | ^ ~ << >>` (logical, arithmetic) | `Bland`, `Blor`, `Blxor` (`~x` is `x ^ -1`), `Blsl`, `Blsr`, `Basr` (amounts ≥ 63 defined) | proved |
| `== < <=` signed and unsigned | `Ceq`, `Cslt`, `Csle`, `Clt`, `Cle` | proved |
| `?:` | `Esel` (conditional move) | proved |
| `if`, `while`, `for`, `goto` within a function | `Eif`, self tail calls (`Eloop`), calls | proved |
| function call, return, recursion | `Ecall`, `Eret` | proved |
| function pointers | a dispatch on an id (clang makes a jump table) | proved |
| `uint64_t` `+ - * & | ^ << >> < <= ==` | `Ew64` (`W_add` .. `W_eq`) | proved |
| **`uint64_t` `/ %`**, signed 64-bit (`int64_t`) arithmetic beyond 63 bits, the high half of a 64×64 product | — | **missing** (add `W_divu`, `W_modu`, signed variants, `W_mulhi` to `w64op`) |
| `int8/16/32_t`, `uint8/16/32_t` arithmetic with C's wrap-around | a library over `int` with masks and sign extension (`sx32` exists) | **library to write** |
| loads and stores of 8, 16, 32, 64 bits | `Ekld8`/`Ekst8`, `rd16`/`upd16` (two bytes), `Ekld32`/`Ekst32`, `Ekld`/`Ekst`, views | proved |
| `volatile`, atomics, fences, `memcpy`, `memset`, `memcmp` | `Ehw` machine operations | laws, C bodies assumed |
| `__builtin_popcount`, `clz`, `ctz`, `bswap`, rotate | expressible as loops or bit tricks today | **optional single instructions** (speed) |
| `malloc`, `free` | a library on growing blocks | proved library |
| `float`, `double` | — | hosted, not started |
| `setjmp`/`longjmp`, variadic functions, `alloca` | — | not planned (not needed by freestanding programs written this way) |

**Higher-order functions beyond this are not needed for parity with C**, and the cost-shape work found why they are the one hard
place: every decidability problem there was a single phenomenon — **a callee not syntactically determined**.  C has no closures;
its function pointers are determined at run time from a table, which is exactly the id dispatch above.  So the route translates
every function that is known where it is used (put in, or a copy per function given, captures included) and every function
chosen at run time from an explicit table; a function value that is not known from the text where it is called (returned by
a recursive function, built anew at each round) is refused by design, because in C it would be a struct the programmer builds.
A function returned by a helper that is put in is known where it is called, and is accepted (`A_par_fun_result`).  Full higher-order — function values flowing anywhere — is the
cost-shape record's "#10, the big one", and it is not on this route's path.

---

## §3. NATURALNESS — THE CONSTRUCT TABLE

### 3.1 Why by construct, never by sample

Logging what sample programs get refused, and fixing those, finds only what someone happened to write; it is "patching" and was
rejected (§0.2).  Rocq's term formers are a small closed set (variable, lambda, let, application, constant, constructor, match,
projection, fixpoint, literals); the places a former can stand are few (tail or not, scrutinee, branch, let-bound, function,
argument, result); the runtime-free types are a small grammar (`int`, `bool`, `unit`, products and records of these, a known
function, a function chosen at run time, a memory).  The audit is the table of all of these.  Every cell is one of:

- **translated and proved** (with its rule);
- **refused by design**, with the named reason (it needs a runtime: allocation that outlives the call, an unbounded number, a
  memory used after it was handed on);
- **a gap**: runtime-free, not yet translated or not yet proved.

The claim "the checker does not over-reject" is exactly: **no cell is a gap**.  This is the method of the cost-shape work in
KernelQ, whose audit goes by term former because a walk with a catch-all cannot be shown complete.

### 3.2 The generator (`proved/matrix/gen.py`)

`python3 proved/matrix/gen.py OUTDIR` writes one program per cell and `OUTDIR/cells.tsv`.  Each program defines
`go : nat -> int -> int -> mem -> int` and a `main` that applies it, on top of a small shared prelude (a record of three
numbers, helpers giving a number, a pair, a boolean, a memory, a record; `twice`; a recursive `fold` that takes a function).

- **Family P — producers.**  Every way of producing a value of each result kind — `int`, `bool`, `int * int`, a record of
  three, `int * mem`, `mem`, `(int * int) * int` — by a function `f`, consumed by `go`.  Literals, arithmetic, `let` chains,
  `if` (with `&&`, `||`, `negb`, a `let`-bound test, nested, chained), `match` on a boolean, a counter, a pair, a record,
  beta-redexes, local functions, helpers, functions given to `twice`/`fold` (closed, capturing, named, passed through),
  memory reads and writes, pairs and records built, destructured, projected, recursion in tail and non-tail positions,
  mutual recursion, a local `fix`, `u64`, shifts, comparisons, division.
- **Family A — parameters.**  Every kind of parameter a function can take, passed to a helper and used: `int`, `bool` (used
  once, twice, negated, passed on, combined), pairs (projected, destructured, matched, passed, returned, nested), records,
  functions (closed, capturing, named, passed on, two-argument, stored in a `let`, returned, inside a pair), counters
  (several, arithmetic, `pred`, comparisons, conversion), memories (one, two, in a pair, in a record), `option`, `list`, a
  sum, `unit`, polymorphic and class-based helpers, a record with a proof field.
- **Family N — nestings.**  Every ordered nesting, one to three deep, of eight contexts (`let`, `if`, arithmetic, a pair
  destructured, a call, a beta-redex, a `match` on a counter, a read) around a core of arithmetic: 8 + 64 + 512 = 584
  programs, so every construct is met inside every other in every order (the "A×B×C" of the owner's request).

New cells are added to `gen.py` when a feature is built (the capture cells, for instance), so the table only grows.

### 3.3 The classification (`proved/matrix/classify.py`)

`bash proved/matrix/run.sh [OUT]` runs the table (in the image, in the repository, after `proved/make.sh`): it writes the cells
(`gen.py`), runs `kitc.py --no-build` on each — the real translator and the real prover, `KQ_STRICT=1`, `KQ_TIMEOUT=120`, `PJ`
cells at a time — keeps one line of output per cell in `OUT/results.txt` (default `proved/matrix/out`) and classifies them.
`PATT=a+b` runs only the cells whose names contain `a` or `b`; `MD=1` writes `proved/matrix/MATRIX.md` (for a full run).
`classify.py RESULTS... [--md FILE]` gives each cell a verdict: `ok`, `design` (the list `DESIGN_CELLS` — empty since 2026-10-30:
a cell goes there only when its program shows the cause, next to its control, §3.6), `invalid` (the generated program is not
Rocq: no verdict), or `gap` with its category (regular expressions on the refusal reason; `BY_NAME` where two categories share
one message).  The full table is a long run: the cells of one category while working, the full table once per landing that
changed the translator or the walk.

### 3.4 The numbers

| Run | Cells | Translated and proved | By design | Gaps | Not Rocq |
|---|---|---|---|---|---|
| first full run (2026-10-27) | 770 | 533 | 5 | 231 | 1 |
| after counter matches anywhere, local functions, captures, comparison of terms with tests, budgets of constants (2026-10-30) | 775 | **733** | 5 | **36** | 1 |
| the same results classified again: the five "by design" cells build and take apart their value in place (2026-10-30, F35) | 775 | **733** | **0** | **41** | 1 |
| after booleans (results, parameters, made by `if`/`match`), values built and taken apart in place, a number and a memory as a result, records chosen by a test; 5 new cells (2026-10-30, evening) | 780 | **759** | 0 | **20** | 1 |

What closed the 195 cells: a `match` on a counter read anywhere, not only at the top of a recursion (≈190 cells of family N and
P — the single largest gap, found only because the nestings put a `match` inside every other construct); a `let`-bound local
function put in at each use (5); a function given to a template that names variables of the caller (the closure cells); two
functions compared as terms when they contain a test, a `let`, a projection or a local `fix`; a budget made only of numbers
written in the program read as a written budget.

### 3.5 The 20 gaps (the live list, from `MATRIX.md`)

| Cells | Category | Cells by name | What it takes |
|---|---|---|---|
| 6 | the translation is accepted, **the proof is not found** | `P_pair_if`, `P_pair_if_inside`, `P_pair_call_arith`, `P_pair_nontail_if`, `P_pair_proj_pair`, `P_int_match_nat2` | proof search only: a pair built by an `if` (each field a conditional move) needs the walk to take the record apart on the Rocq side the same way; `match n with O | S O | S (S _)` needs the nested counter test in `kqm_test`.  Under §12.V these become cases of `compile`, where nothing is searched |
| 4 | **polymorphic / class-based helpers** | `A_par_poly_id`, `A_par_poly_pair`, `A_par_poly_hof`, `A_par_typeclass` | specialization at the use (Lean's `fixedInst`): a type argument and an instance argument are put in like a known function; types are erased in KQL already |
| 4 | **arithmetic and comparisons on counters** | `A_par_nat_eqb`, `A_par_nat_ltb`, `A_par_nat_mul` (`n + n`), `A_par_nat_pred` | a counter is one machine number (`ofn`); `Nat.eqb`/`Nat.ltb` are comparisons of those, `pred` is a conditional move, `n + n` is an addition with the bound kept under `cbk` |
| 3 | **a record of three numbers given back by recursion** | `P_rec3_tail_rec`, `P_rec3_nontail`, `P_pairp_rec` | the slot block from one cell to k-1 cells.  A caller puts k-1 cells back after the call, which needs the law that writes to two different cells can be swapped (`Upd h i v (Upd h j w s) = Upd h j w (Upd h i v s)` for different cells).  It does not follow from `upd_upd` and `upd_rd_id`; the model proves it the way it proves those (functional extensionality).  **Approved by the owner (2026-10-30, D27)**; it goes into `KQSpec.laws` (proved in `KQModel.v`) together with the construct that uses it, as a construct of `S` (§12.V) — F43 |
| 2 | **an `option` given back by a recursive function, or kept as a loop's state** | `A_par_option_rec`, `A_par_option_state` | a non-recursive inductive of numbers held as its tag and its fields: a kind for it (parameters, results through the slot block, a `match` as a test of the tag) |
| 1 | a local `fix` that names a variable of the caller | `P_int_local_fix` | a local `fix` is a template whose copy takes its free variables as parameters (lambda lifting, as captures do) |

**By design: none yet.**  The cells once counted by design (`A_par_option`, `A_par_list`, `A_par_sum`, `A_par_fun_in_pair`,
`P_mem_dup`) build and take apart their value in place, or never use the second memory (F35); they are now translated and proved
(`knorm`), and `A_par_fun_result` was all along.  They are the **controls** for the boundaries of §0.5, whose **pins** are still
to be written: a list built by recursion with its length from the data (control `A_par_list`); a function returned by a
recursive function and called later (control `A_par_fun_result`); both versions of the memory used (control `P_mem_dup`); a `Z`
result (control: the same program on `int`).  **Not Rocq (1):** `A_par_nat_arith` (`k (m + 0)` is not a structurally smaller
argument; the generated program itself is rejected by Rocq, so there is no verdict).

### 3.6 How a gap is closed

1. Find the cell's refusal (`proved/gen/CELL_t.v` for a translation, `CELL_u_F.v` for a proof) and the place in
   `KQMTrans.v` / `KQMAuto.v` it comes from.
2. Write the translator rule **for the construct**, not for the cell: the rule must hold for every place and type the construct
   can appear in.
3. The per-program statement is proved the same way as the rest (no new trust).  If the proof needs a new memory law, it goes
   into `KQSpec.v` and is proved for the model in `KQModel.v`.
4. Run the cells of that category, then **the full table**, then the gate (examples, corpus, kernels if the walk changed).
5. Record the new numbers in `MATRIX.md` and §3.4.

A refusal that is genuinely by design gets added to `DESIGN_CELLS` with its reason, and the refusal message names the library
to use instead.

**Rules for closing, carried over from the cost-shape work** (they were learned there at a cost and hold here unchanged):
- **A gap is not closed by writing down its limit.**  Either the construct is translated and proved, or the cell stays a gap.  A
  sentence in a README saying "X is not read" is a record of a gap, never its closure.
- **A boundary is closed only with a machine-checked pin and a control.**  A by-design refusal is a cell of the table that is
  refused (the pin) next to the nearest cell that is accepted and differs only in the cause (the control) — for instance a
  closure that escapes (refused) next to the same closure used in place (accepted).  A measurement written in prose is not
  closed.  **The pin must show the cause in its own text** — a size that comes from the data, a value that must outlive the place
  where it can be put in, two versions of the memory both used.  A refusal message is not a cause, and neither is a type: five
  cells were counted by design because they mention `option`, a list or a function, while their programs needed no runtime
  (F35).
- **Never add a check to the translator without a theorem that needs it** (the cost-shape record's rule 2'): a condition with no
  theorem behind it is either an over-rejection or load-bearing but unjustified, and which one cannot be told by reasoning.  Every
  side condition is audited for the theorem that requires it (§3.7).
- **The method, not the patches, is the result.**  When a family of refusals closes, the record says which rule closed it and
  why the rule covers the whole family.

### 3.7 What the table does not yet cover: the translator's own side conditions

The generator writes programs in the shape the translator expects, so the table does not see the translator's conventions.  Each
is a rule a user must learn today, and each is an over-rejection unless a theorem needs it:

| Condition | Where | Theorem that needs it? | What to do |
|---|---|---|---|
| the counter a function recurses on is its **first** parameter | `fparts`: `rarg d = 0` | no: the statement's induction can be on any `nat` parameter | read `rarg d = k` for any `k`; induct on parameter `k` |
| the memory is the **last** parameter | `tr_call` (`[KMem], [m]` last), `mk_info` | no: the memory is one KQL argument wherever it stands | accept the memory at any position |
| at most **one memory** per function | `mk_info` (`restmem && capmem` refused), the walk | partly: one memory is the linearity that makes in-place update correct; two *different* memory parameters both live would alias the one global memory | refuse only two memories used at once (by design, with pin and control); accept two parameters of which one is dead or one is the other (`A_par_mem_two`, two memory parameters of which one is unused, is already accepted) |
| a function to translate is in the **program's own file** (or the kit) | `is_fun`, `reach`: `eq_mp (fst kn) mp` | no: a function of another file is quoted the same way | translate functions of any file the program imports (a multi-file program, a user library) — the cost-shape work measured the same need (a course library in a separate file) |
| a captured variable is a number, a counter or a memory | `cap_ok` | no: a captured boolean, pair or record is a parameter like any other | accept every kind `kind_of` accepts |
| a helper larger than 40 nodes becomes a function of its own | `big_fun` | none (a proof-size choice, not a refusal) | keep; it is not visible to the user |
| a choice between values reads at most three times to be a conditional move | `choice_ok` | none (a speed choice, measured) | keep; above three it is a branch, not a refusal |
| budgets below 2^60 | `kq_nat` | yes: the bound of every counter (`cbk`) | keep; state it in the measure's domain |

**Action:** add a family to `gen.py` that varies these — the counter in each position, the memory in each position, two memory
parameters (one dead, one an alias, both live), a function from another file, a captured boolean / pair / record — and close each
cell or pin it as by design with its control.

### 3.8 The end state: naturalness as a theorem

The table is a measurement: it says that 733 programs are accepted, not that every program of a described kind is.  The cost-shape
work closed the same question by theorem: a grammar `G` of the accepted fragment defined **without any reference to the checker**,
a decision procedure for it, and a proof that inside `G` the checker accepts everything (there: `G_is_pterm`).  Here that means:
a grammar of runtime-free Rocq terms (the constructs × places × types of §3.1, minus the by-design cells), and a theorem that on
every term of it the translator succeeds and the statement it produces is provable by the walk — or, more practically, that the
walk is complete for every KQL term the translator produces.  The second part is the hard one (the walk is a tactic); a
reflective checker (§7.5) would make it a theorem about a Rocq function.  Until then, the claim is the table, with every side
condition audited (§3.7).

---

## §4. LOOPS AND RECURSION

### 4.1 Rocq's rule, and why fuel exists at all

Rocq accepts a `Fixpoint` only if one argument visibly becomes structurally smaller at each recursive call (a `nat` counting
down, a list getting shorter).  A counted loop fits that rule exactly: `Fixpoint sum (k : nat) (i acc : int) := match k with O
=> acc | S k' => sum k' (i + 1) (acc + rd 0 i s) end`, called with `k` the number of rounds, is native Rocq and exact.

A `while (i < n)` loop does end — `n - i` falls every round — but Rocq does not see a calculation falling, only structure.
The usual workaround is **fuel**: a spare `nat` that counts down beside the real test, `match fuel with O => acc | S f => if i
<? n then loop f (i + 1) .. else acc end`.  Fuel is not this project's invention, and its one danger is real: **a fuel that is
too small silently ends the loop early with a wrong answer**, which C's `while` never does.  The two `O => acc` lines of the
counted loop and the fuel loop are the same text; only in the second can reaching it be wrong.

Making termination fully automatic is impossible in general (it is the halting problem): a loop whose end depends on the data
(Collatz) has no argument a tactic can invent.  The common shapes — counting up to a bound, counting down, halving — have
obvious measures.  The design below therefore takes **the measure itself as the budget**, which removes the guess, and proves
once that a falling measure makes the budget enough.

### 4.2 Counted loops (`lib/Loop.v`)

```coq
loop_up   lo hi acc (fun i acc => ..)     (* for (i = lo; i < hi; i++) acc = ..; gives acc *)
loop_up_m lo hi s   (fun i s => ..)       (* the same with the memory as the state; gives the memory *)
loop_find lo hi (fun i => test)           (* the first i in lo .. hi-1 that passes the test, hi if none; stops there *)
```

The number of rounds is `kq_nat (hi - lo)`: exact, nothing to choose.  The function given may name any variable of the text
around it (§5.2).  `proved/examples/loops.body`.

### 4.3 A loop on two numbers with a measure (`loop_two`)

`loop_two meas c fa fb a b` is `while (c a b) { (a, b) = (fa a b, fb a b) }` with budget `kq_nat (meas a b)`.
`lib/LoopSpec.v`: `loop_two_ends` — if the measure falls at every round that runs and stays at least 0, the loop ends with
its test false (and `loop_two_go_ends` for the budgeted function itself).  `proved/examples/loop_while.body` (Euclid's gcd).

### 4.4 Recursion with a measure: the `wfix` family (built on the way to "level 2", §4.5)

Write the function as its body, with `rec` for the recursive call, and a measure that falls at every call:

```coq
Definition gcd (a b : int) : int :=
  wfix2 (fun x y => y) (fun rec x y => if 0 <? y then rec y (x mod y) else x) a b.
Definition tri (n : int) : int :=
  wfix1 (fun x => x) (fun rec x => if 0 <? x then x + rec (x - 1) else 0) n.
Definition lower_bound (key : int) (s : mem) : int :=      (* binary search: the measure is the width of the range *)
  wfix3m (fun k lo hi => hi - lo)
         (fun rec k lo hi t => if lo <? hi
                               then (if rd 0 ((lo + hi) / 2) t <? k then rec k ((lo + hi) / 2 + 1) hi t
                                     else rec k lo ((lo + hi) / 2) t)
                               else lo) key 0 12 s.
```

**Forms.**  `wfix1`, `wfix2`, `wfix3` (numbers to a number); `wfix1m`, `wfix2m`, `wfix3m` (numbers and a memory that is read,
to a number); `wfixm1`, `wfixm2` (numbers and a memory, to the memory it ends with — the loop's state is the memory).  Each is
`wfixN meas F args := wfixN_go (kq_nat (meas args + 1)) F args` with `wfixN_go k F args := match k with O => default | S k' =>
F (wfixN_go k' F) args end`.

**Translation.**  `wfixN_go` is a template (a recursive function that takes a function); the body `F` is put in, `rec`
becomes the copy calling itself, so a tail `rec` is a loop and any other `rec` is a call.  Nothing in the translator is
specific to `wfix`.  Examples: `proved/examples/wfix.body` (gcd and the non-tail sum, answer 76), `wfix_mem.body` (the binary
search, a memory fill with `wfixm1`, a three-number non-tail recursion, answer 544).

**The theory, written once** (`lib/LoopSpec.v`, Section `WF`, for any argument type `A` and result type `B`).  Given `go :
nat -> A -> B` with `go (S k) x = F (go k) x`, a measure `m : A -> Z` and a domain `P : A -> Prop`:

```
dec            := forall r1 r2 x, P x -> (forall y, P y -> 0 <= m y < m x -> r1 y = r2 y) -> F r1 x = F r2 x
                   (F consults rec only at arguments in the domain whose measure is smaller and not below 0 —
                    the termination argument; it is the extensionality premise of Rocq's own Fix_eq)
wf_indep       dec -> once the budget is above the measure, the budget does not matter
wf_eq          dec -> go k x = F (go k) x                      (for 0 <= m x < k)
wf_wrapper_eq  dec -> W x = F W x   where W x := go (fuel x) x and fuel x >= m x + 1 (below 2^60)
wf_ind         dec -> a property Q x (W x) follows by induction on the measure from
                      "Q holds of F's answer whenever it holds of rec's answers at smaller arguments"
```

`go 0` is never mentioned: with the budget above the measure the zero-budget case is never reached, which is the point.

**Per form** (`proved/KQLoopSpec.v`, generated by `tools/mkloopspec.py` from one template; the `kq_nat` budget facts come from
`kq_nat_val` in `KQMAuto.v`): `<form>_dec` (the termination argument in curried form), `<form>_eq` (`wfix2 meas F x y = F
(wfix2 meas F) x y`), `<form>_ind`, and the tactic `<form>_dec_tac side`, which opens `F`, splits on its tests, turns the
comparisons into integer facts and closes every recursive call with `side`.  `wf_side` handles the usual measures: it knows `x
- 1`, `x mod y` and `x / 2` (`sub1_Z`, `rem_range`, `div2_range`).

**Worked examples** (`proved/KQLoopExamples.v`), the three steps a user does:

```coq
Lemma tri_dec : wfix1_dec tri_meas tri_F tri_P.
Proof. wfix1_dec_tac ltac:(unfold tri_meas, tri_P in *; wf_side). Qed.            (* termination: one line *)
Corollary tri_eq : ... wfix1 tri_meas tri_F x = tri_F (wfix1 tri_meas tri_F) x.   (* the equation *)
Theorem tri_closed : forall x, tri_P x -> (2 * Z_ (wfix1 tri_meas tri_F x) = Z_ x * (Z_ x + 1))%Z.
Theorem gcd_correct : forall x y, gcd_P x y -> Z_ (wfix2 gcd_meas gcd_F x y) = Z.gcd (Z_ x) (Z_ y).
```

`Print Assumptions` of these: Rocq's integer primitives and the declared memory type only — nothing of ours.

**Limits, stated.**  The measure and the budget are below `2^60` (the cap of `kq_nat`); `gcd`'s domain therefore says the
second number is below `2^60`.  The user supplies the measure and the domain.  A loop with no measure (Collatz) still needs a
budget (Rocq itself asks for a measure or fuel there, so that is Rocq's rule, not ours).  **Rocq's own `Program Fixpoint
{measure ..}` (the `Acc`/`Fix_F` form) is not read yet — it is owed (§4.5).**

### 4.5 Reading Rocq's own measure recursion — owed (the owner's "level 2")

**What the owner asked for.**  Asked for loops "natively, without workaround", two levels were offered (2026-10-29): level 1, a
loop whose budget is a measure; level 2, Rocq's own `Program Fixpoint {measure ..}` / `Function`.  The owner answered "make it
level 2, stable, perfect and good".  What was built is `wfix` (§4.4): the same equation as Rocq's `Fix_eq` and an induction
principle, with no budget to guess — but a library form the user must learn, not Rocq's own spelling, and it was then recorded
as if the owner's form were optional (F36).  Under D22 the spelling is the point: a Rocq user writes `Program Fixpoint`,
`Function` or `Equations`, and that text must compile.  `wfix` stays (it is ordinary Rocq, it is proved, and it is the engine
below); reading Rocq's own forms is open work (§12.P), not an option.

**How (a plan, not yet tested).**  `Program Fixpoint f (x : A) {measure (m x)} : B := body` is elaborated to `Fix_sub` over the
relation `MR lt m`; each recursive call receives a `sig` value `exist _ y proof` (the argument and a proof that the measure
falls).  The route:
- **translator:** recognize the elaborated `Fix_sub` / `Fix_F_sub` head in the quoted term (MetaRocq reads it as it reads
  everything else); a recursive call is `wfix`'s `rec` applied to `y` — the `sig`'s value — and the proof is dropped (it is in
  `Prop`); the budget is the measure plus one, as for `wfix`, so the KQL is that of the `wfix` form of the same function;
- **statement and proof:** the walk unfolds the definition one step with `Corelib.Program.Wf.fix_sub_eq`, whose
  extensionality premise is a hypothesis — the same condition as `wfix`'s `dec`, discharged by the same tactic — and inducts on
  the measure (`wf_ind`'s shape).  **Never `fix_sub_eq_ext` from `Stdlib.Program.WfExtensionality`**: it rests on functional
  extensionality, an axiom (§0.9, question 1).  Both lemmas were read in the image's standard library (2026-10-30);
- **the measure** Rocq's form takes is a `nat` (or a well-founded relation); a measure on `int` is written through a
  conversion (`Z.to_nat (to_Z ..)`), which the translator reads as `kq_nat`, with the 2^60 cap in the domain as for `wfix`;
- **the other spellings:** `Function` (`Recdef`: it generates `f_equation` and a functional induction principle) and
  `Equations` (installed in the image: it generates its own equations and elimination principle), each read the same way once
  the first works.

Accepted when the `wfix` examples written as `Program Fixpoint` compile, prove with no new assumption, and give the same answers,
and the construct table has cells for each spelling.

---

## §5. FUNCTIONS AS VALUES, CLOSURES, LOCAL FUNCTIONS

### 5.1 Templates: specialization per function given

A helper that does not recurse and takes a function is written out where it is used, with the function put in.  A recursive
function that takes functions (`template_places`: the parameters whose type is a product) is a template: every call that gives
it known functions makes a copy (`site_key` computes the key, `inst_body` the copy's body), cached by the key so two calls with
the same functions share one copy; the copy is a KQL function of its own, proved against the original applied to those
functions.  This is Lean's specialization of `fixedHO` parameters (§5.7).

### 5.2 Captures: closures over the caller's variables

A function given to a template may name variables of the text around it (`fold n 0 a (fun i acc => acc + i * b + rd 0 i s)`).
`abs_free` finds the free variables of the function given, in order of first appearance, and writes the function with them as
`tRel 0 .. m-1`; the key of the copy (`fkey`) is the function, the functions given (abstracted), and the **types** of the
captured variables (`cap_ok`: a number, a counter or a memory).  The copy takes the captured variables as extra parameters
(`fi_capk`): numbers and counters after the copy's own numbers, a memory merged with the copy's memory (one memory per
function — linearity).  At the call, `find_fn_args` abstracts the call's function the same way and passes the captured
variables (`call_args`); inside the copy its own recursive calls pass them on (`cap_terms`: they sit at the bottom of its
environment).  The statement of the copy substitutes the captured parameters into the function given (`capterms`).

### 5.3 Local functions

`let g := fun x => .. in ..` (a `let` whose type is a product) is put in at each use (`is_fun_ty` in every `tLetIn` arm).  Its
variables are those of the text around it, so a local function that names a variable of the caller needs nothing more.

### 5.4 Comparing two functions as terms

Two functions given to a template are the same copy when they are the same term after abstraction (`term_same`).  Until
2026-10-29 `term_same` had no case for `match`/`if`, `let`, projections or local fixpoints, so **any function given to a template
that contained a test was never matched with its copy** and was refused ("not readable") — on the old translator as well, so it
was a hole from the start, found only because the measure-recursion bodies all contain a test.  Fixed for those four formers.

### 5.5 Budgets made of numbers written in the program

`kq_nat (meas a b + 1)` where the measure is a lambda applied to numbers written in the program (`lower_bound key s := wfix3m ..
key 0 12 s`) was translated as a budget worked out at run time (two clamping conditional moves); the proof reduced those to the
plain number 13, and the copy's statement — about `ofn x0` for any counter `x0` — could not match a bare 13.  `deep_norm`
normalizes the budget term through arguments, substitutes `let`s and reads back variables whose entries are literal numbers;
when the result is closed it is a written budget (`Abud`), which the proof rewrites to `ofn (kq_nat n)` (`bud_ofn`).

### 5.6 What is left in this area

`P_int_local_fix` (a local `fix` naming the caller's variables: lift it as captures are), polymorphic and class-based helpers
(specialize type and instance arguments as known functions), and — by design — functions returned or stored in data.

### 5.7 What Lean's compiler shows (read 2026-10, `src/Lean/Compiler/LCNF`)

The pass list (`LCNF/Passes.lean`), base phase: `init`, `pullInstances`, `cse`, `simp`, `floatLetIn`, `findJoinPoints`,
`pullFunDecls`, `reduceJpArity`, `simp` with `implementedBy`, `eagerLambdaLifting`, `specialize`, `findJoinPoints`, `simp`, `cse`;
mono phase: `simp`, `reduceJpArity`, `structProjCases`, `extendJoinPointContext`, `floatLetIn`, `reduceArity`,
`commonJoinPointArgs`, `simp`, `floatLetIn`, `lambdaLifting`, `elimDeadBranches`, `cse`, `extractClosed`; impure phase:
`pushProj`, `insertResetReuse`, `elimDeadVars`, `simpCase`, `inferBorrow`, `explicitBoxing`, `explicitRc`, `expandResetReuse`,
`coalesceRC`, `toposort`.  The impure phase (boxing, reference counting, reset/reuse) exists only because Lean has a runtime.

| Lean | Here |
|---|---|
| specialization of `fixedHO` / `fixedInst` parameters, cached by key, the lambda's free variables as extra parameters of the copy (`Specialize.lean`, `Closure.lean`) | templates + captures (§5.1, §5.2); `fixedInst` (instances, types) is the polymorphism gap |
| lambda lifting (`LambdaLifting.lean`) | local functions are put in (§5.3); a local `fix` with captures is the gap |
| join points (a local function used only in tail position is a jump) | not needed so far: helpers are put in; a candidate if a body with many tails gets large |
| `floatLetIn`, `cse`, `reduceArity`, `elimDeadBranches` | not done; standard general passes, allowed by §0.7 if proved once |
| a self tail call: parallel assignment of the parameters, then `goto _start` (`EmitC.lean`, `emitTailCall`) | `Eloop`; the C is a self tail call that clang turns into a jump |
| `partial def` (no termination proof, trusted) | impossible in Rocq without making the logic inconsistent; the measure is the honest replacement (§4) |
| `Nat` falls back to a bignum | no runtime: fixed-width numbers (§0.4) |

Lean's own kernel has a re-implementation in Lean with metatheory in progress (Lean4Lean, github.com/digama0/lean4lean, read
2026-10-29): a typing relation and a proof that the implementation meets it, with open `sorry`s outside its experimental part,
no verified compilation (`reduceBool` unsupported), sharing bugs with the C++ kernel since it is derived from it.  It formalizes
the kernel, not the evaluation and erasure that MetaRocq provides for Rocq.

---

## §6. SPEED OF THE GENERATED C

### 6.1 What is measured

| Comparison | Result | Where |
|---|---|---|
| proved route over the kit route's own build, 36 corpus programs, best of 5, one pinned core | **median 1.02**, range 0.89 – 1.55 (the same program timed twice varies ~15%) | `proved/README.md` table, `proved/corpus.sh times` |
| kit route over C++, 26 Codeforces problems | median 1.09 (17/26 ≤ 1.25, 23/26 ≤ 1.5; worst CF295B 3.24, a loop the C++ compiler vectorizes) on one machine; median 1.23 on another — ratios depend on the CPU | `README.md` results, `all.sh` |
| kit route over **unmodified** CertiRocq on the same Rocq text | 8.8x faster (geometric mean over 51 programs; median 6.7; 2.7x to 61x); per problem stock CertiRocq is ~13x the C++, this route ~1.2x | `tests/stock.sh` |
| plain loops written by the guideline, over C of the same shape | 1.0 – 1.7x; 1.7 – 2x the instructions at a higher instruction rate, no wrong guesses | `tests/mkworst.py`, `tests/worst_c.c` |
| the same loops written badly on purpose (state in cells, phases) | 2 – 12x their guideline way, against 1.1 – 3.8x for C written that way | same |
| bytes: a sum over 10^6 bytes, 100 times | 136 ms as shifts and masks of 32-bit cells, 74 ms as byte loads | `tests/bytebench.body`, `tests/bytebench_c.c` |
| a hash set on the slab against the same set with `malloc`/`free` in C | 5 – 7x the C (most of it the handle test on every field access) | `examples/slab_set.body`, `examples/slab_set_malloc.c` |

The bad-style penalty is larger than C's because of three costs this route adds to every memory access and every loop: the
bounds test on each `rd`/`upd`, the tag bit of each number, and the counter of each loop.  That is exactly what the general passes
(§6.4) remove.

### 6.2 Where the overhead comes from (known limits)

- Every memory access tests its cell by default; the kit route removes the test in counting loops where a proof exists
  (`+2.0%` cycles on average between the default and the bounds-proved build; worst CF295Bv2 98 → 122 ms).
- A cell is 8 bytes where C++ often uses 4, unless the program uses narrow blocks.
- The C compiler vectorizes some C++ loops that it does not vectorize in the generated C (CF295B).
- Integers are 63 bits; a 64-bit value travels as two halves (one instruction per operation, §1.3).
- A loop is a chain of C tail calls; with more than six parameters the C compiler may make them real calls, so a long loop needs
  a large stack (the scripts run programs with `ulimit -s unlimited`).
- A function with two results saves and restores one cell of the slot block per call.

### 6.3 Passes done, and what they measured

- **If-conversion with early reads.**  A choice between two values whose arms read the current memory (up to three reads) is
  a conditional move, since a read is total (`choice_ok` in `KQMTrans.v`).  State in cells in the mixed loop 115 → 18 ms; in
  the search 1076 → 351 ms (kit route 296); cells and phases in the search 1367 → 496 ms.  All 36 corpus programs still proved
  and equal; the C of 6 of 7 timed programs unchanged.
- **Merging a chain of tail calls into one call with conditional moves**, with plain arithmetic only.  Allowing reads in the
  merged arguments made the phase-cycling search twice as slow (411 → 785 ms): a conditional move in place of a well-predicted
  jump makes each round wait for the one before.  So the merge keeps to plain arithmetic and the value choice may read.
- A guess that turned out wrong and is recorded so it is not re-made: reloading a block's address and size from the tables at
  every access costs nothing, because clang already hoists those loads.

### 6.4 Passes left, in order, and the rule for any pass

1. **Removal of the test on an access whose index is in range**, proved: the access's index is shown in range by the same
   kind of reasoning the bounds proofs of the kit route use, and the KQL instruction without the test is used.  The general
   instance of "dropping a test that cannot fail".
2. **Forwarding** a stored or loaded value to a later read of the same address (different blocks never alias — a fact our
   memory model has and C's does not).
3. **Hoisting** loop-invariant reads.

The rule (§0.7): a pass removes a cost the translation adds to every operation, or is a standard pass C compilers apply to any
program; it is stated and proved once from the laws of integers and memory; the per-program statement does not change; it is
not keyed to the shape of one benchmark.  A cost that comes from the structure of the program stays (a loop written as one pass
with a phase number costs about twice what it costs in C; that is not a reason for a pass that merges the phases).

**How a pass is chosen:** write the program several ways (`tests/mkworst.py`, `tests/mksame.py`) and the same ways in C
(`tests/worst_c.c`, `tests/worst_ref.c`); time each on one pinned core against the C of the same shape; where the gap is large,
count instructions, branches and wrong guesses per element (`KQ_PERF=1`, on the host, not in a container) to see which operation
adds the work; fix the operation for every program; run the same ways again.  A guess about the cause is tested before it
becomes a pass.

---

## §7. PROOF SPEED

### 7.1 Why the proofs cost what they cost

The proof of a function walks its KQL body one instruction at a time, against the Rocq definition opened on the other side.
Three costs grew with the length of a function, and each was found by profiling:

1. **The variable bindings** are a chain of `PTree.set` that each lookup worked out from the top.  Fixed: the chain is turned
   into a tree every 24 bindings (`kqm_compact`).  The 100-store table of the interrupt kernel went from 119 s to 16 s.
2. **A rewrite for counters** scanned the whole goal at every addition.  Fixed: tried only where a counter is added to (by
   syntactic pattern), and only inside an induction (a function that does not recurse has no counter to rewrite).
3. **A run of read-modify-write steps** (`upd b i (rd b j s + 1) s`, repeated) mentions the previous memory twice per step, so
   the memory term doubles per step when written out (sixteen steps took over five minutes).  Fixed for practical lengths:
   a function that does not recurse is first proved with the plain walk (up to 150 s), then, if that runs out, with each memory of
   its `let`s named in the goal (`KQMNames.v`, peeling one `let` at a time) and the walk's own memory given the same name
   (`kqm_share`).  Fourteen steps prove in 23 s with the plain walk; twenty-four need the named walk, 45 s after the plain one
   ran out.  What remains is the kernel comparing the chain of `let`s with itself, which still grows steeply, so beyond a few
   dozen steps the steps go into functions or loops.  A call has no such problem: the memory after it is `f args M`.

Other one-time findings: `w64_op` sealed (a chain of 64-bit operations made the kernel check run 40+ minutes before); a budget
`kq_nat x` bounded without working the number out (`kq_nat_cbk` before any `vm_compute`, otherwise memory blew up); a first
parameter of type `int` is never tried as an induction (only a `nat`).

### 7.2 What was done in the proof-speed sessions (2026-10-25/26)

- **Each function's statement is checked alone, in its own file**, against the statements of the functions before it (taken as
  given there — admitted stubs in that file), **in parallel** (`KQ_JOBS`), and **remembered** (`proved/gen/cache/`) under a key
  made of the tactic libraries (`proved/*.v`, `KQRun.v`, the header), the tactic setup of the program, and what Rocq prints
  (with `Set Printing All`) for the function, its statement and every function of the program it mentions.  Changing a function
  re-proves it and everything that mentions it; changing a tactic library re-proves everything.
- **`kqm_known`** (replace a test already split on by its outcome) checks syntactically that the test occurs in the goal
  before rewriting with it; a failed rewrite was a full goal traversal with unification per hypothesis.  The `report` function
  of one kernel went from 45 s to 25 s.
- **The budget-bound check** uses `vm_compute` on the small arithmetic side condition instead of conversion.
- **Counter rewrites only inside an induction**, and **one reduction after a known test** instead of after every attempt.

### 7.3 The numbers

| Test kernel | before the walk fixes | before per-function proofs | after per-function proofs | now |
|---|---|---|---|---|
| irqnow | 2m29 – 4m18 (all five) | 41 s | 40 s | **35 s** |
| fault | | 46 s | 41 s | **36 s** |
| smp | | 50 s | 42 s | **37 s** |
| own | | 1m38 | 1m01 | **54 s** |
| kernel | | 1m12 | 44 s | **40 s** |

- A rerun of an unchanged kernel: **~15 s** (translation, printing, building; every proof from the cache).
- 2026-10-30, one machine, one day (whole build, translation included; this machine varies ~15% from run to run): the pushed
  translator 35.6 / 42.9 / 41.7 / 56.9 / 44.6 s (irqnow, fault, smp, own, kernel); after the boolean, `knorm` and
  number-and-memory work 37.9 / 41.8 / 42.1 / 58.0 / 45.6 s.
- The 36-program corpus: 243 function proofs, 462 s in sum, **1.9 s on average**, the slowest 59 s (`lagrange` of CF622F).
- The critical path of every test kernel is one function, `x86_setup`: about 2,400 straight-line steps, ~18 s now (24 s
  before).  Parallel files cannot split a single function.

### 7.4 What the profiles say is left

- `eapply K_op` is ~45% of `x86_setup`: about 5 ms per step on every step, because the goal holds the whole remaining body
  and every step instantiates a term that size.  The cost is flat per step; whether total time is quadratic in the length was
  not measured directly.
- A function with many tests (`lagrange`: ~15 tests) spends about a third of its time in `kqm_known`: every test split on adds
  a hypothesis that is re-scanned after every later step (steps × hypotheses × goal size).  Scanning only recent tests is unsafe
  (a test can reappear after unfolding); dropping a hypothesis once its test is gone breaks `kqm_hyps_known`/`kqm_known_conv`,
  which read those hypotheses later.

### 7.5 Deliberately not done, and when to revisit

- **Proving long straight-line functions in segments** (each segment its own lemma, so no step sees the whole remaining
  body; segments can run in parallel): would take `x86_setup` from ~18 s to perhaps under 10 s (an estimate), at the cost of a new
  proof structure and new translator output.  Revisit when functions of thousands of steps become common.
- **Proof by reflection** (a checker written as a Rocq function, proved once, run by `vm_compute` on each instance — the
  approach of large verified compilers and cryptographic code generators when tactic proofs get too slow): could be orders of
  magnitude faster; a large project.  Revisit when proof time is the bottleneck.
- **A rework of the walk** to remember settled tests and rewrite only what each step changes: helps a handful of functions,
  risks the core of every proof.

### 7.6 Is the cache safe?

The tactics are untrusted; the kernel checks every proof that runs, so a bad tactic change can only make a proof fail.  The
cache records "this function's proof passed" under its key; a key that missed something that matters could skip a real check.
The key includes all tactic libraries, the printed text of everything the function mentions and — since 2026-10-31 (F48) —
the content of the Rocq executables that check the proofs and the setting of the kernel's conversion memo, so the risk is small, but
**release evidence is `KQ_MONO=1`** (one file, no cache, the whole program checked together).  `Print Assumptions` on a
per-function file shows the stubs of the functions before it; an audit for "no admitted lemmas" also uses `KQ_MONO=1`.

---

## §8. THEOREMS ABOUT PROGRAMS

### 8.1 What carries over

The per-function statements say the C computes the Rocq function.  So a theorem the user proves about the Rocq text — an
invariant of a data structure, a protocol order, a closed form, a bound on an index — holds of the C, with the trust of §1.10.
The theorems are the user's, about the user's own text, in ordinary Rocq; the route adds nothing to prove.

### 8.2 The libraries' theorems

- **The heap** (`lib/SlabSpec.v`, each resting on `KQSpec.real_laws` alone): a handle `slab_next` promised is live after
  `slab_take` (also when the slab doubles); after `slab_free b h`, `h` is not live, whoever holds a copy; a freed handle stays dead
  when its slot is taken again; through a live handle a field reads what was last written.  And the invariant `slab_inv` — the
  header and the generations well formed (`slab_ok`) **and** the free list a list of distinct free (even-generation) slots in use,
  each holding the next (`fl_body`, `fl_chain`) — holds after `slab_init` and again after each of `slab_set`, `slab_free`,
  `slab_take` (`slab_take_inv` needs room for a doubled capacity: below 2^27 slots and the block under 2^31 cells).  A proof
  about a program that calls them one after the other can use it at every step.
- **Views** (`lib/ViewSpec.v`): a write of 64 bits changes no other 32-bit or wide cell; the 64-bit value read back from a cell
  just written stands for the number written.
- **Loops** (`lib/LoopSpec.v`, `proved/KQLoopSpec.v`): §4.3, §4.4.
- **Kernel code** (`KQSpecDemo.v`): a device-given index stays in bounds; a store keeps the other cells; the page-directory fill
  writes the entries it should (by induction).

### 8.3 How a user theorem is written

Integers: the facts `lt_Z`, `le_Z`, `lt_Z_false`, `le_Z_false`, `eq_Z`, `eq_Z_false` (a comparison as a fact about integers),
`add_Z`, `sub_Z`, `mul_Z` (the operation is the integer operation when it does not overflow), `to_Z_bounds`; `Sint63.mod_spec`
(the remainder is `Z.rem`), `Sint63.div_spec` (`Z.quot`); `lia` and `nia` for the integer goals.  Memory: the laws of
`KQSpec.v` (`rd_upd_eq`, `rd_upd_ne`, `size_upd`, `rd_grow`, `size_grow`, ...).  Recursion: induction on the counter for a
`Fixpoint`, `<form>_ind` for measure recursion.  Pattern: state the property on the Rocq function, prove it by the recursion's
induction with the step done by unfolding one round, the comparison facts, the arithmetic facts, and `lia`.

### 8.4 Traps met while writing these proofs (each cost a run)

- Inside `(...)%Z` the notations of an argument are read in `Z_scope`: `Z_ (r (y - 1))` inside `%Z` makes `y - 1` the integer
  subtraction and fails to type.  Write `(y - 1)%sint63`.
- In a file that imports the kit, `x mod y` resolved to the unsigned remainder; name the signed operations: `Sint63.rem`,
  `Sint63.div`.
- With `sint63_scope` open, `int * int` is a multiplication: write `(int * int)%type`.
- `Ltac` definitions inside a `Section` disappear at `End`: define tactics outside sections.
- `Add` is a keyword: do not name a hypothesis `Add`.
- `Z.gcd_mod` gives `Z.gcd b a`, not `Z.gcd a b`: finish with `Z.gcd_comm`.
- A theorem of a section takes only the section variables its statement mentions (and the hypotheses its statement needs): a
  hypothesis used only in the proof is not an argument.  Read the signature with `About` after closing the section.
- `f_equal` on `F r1 x = F r2 x` with `F` folded produces `r1 = r2`, and `apply H` on that sends the unifier into a
  higher-order problem that took 8 GB.  Open the head first (`wf_dec_finish` does), and put a timeout on the `apply`.
- A compiled library that changed must be recompiled before a file that imports it is tested, or the test runs the old
  library (a stale `.vo` hid a fix for one run).
- `reflexivity` on a goal containing a large computable term can make it evaluate the term; `exact eq_refl` (kernel
  conversion) does not go through the same path.

---

## §9. HARDWARE AND THE OPERATING-SYSTEM GOAL

### 9.1 Generic primitives, never a port (owner, 2026-10-15)

The core knows no instruction set.  An architecture is written by the user in Rocq, from the manual, over generic primitives:
the program writes instruction words (encoded in Rocq from the specification) into a narrow block and runs them (`hw_run`: a
call with several arguments and two results; `hw_code_sync`: the one per-family instruction-cache step — none on x86, `fence.i`
on RISC-V; `hw_sym`: run-time addresses).  `hw/X86.v` holds the x86 instructions the test kernels use, written that way.  A
request for "a guide for architecture X" means the generic mechanism plus how a user writes X with it — never porting X in C
or assembly.  Per-family C bodies would be hardcoding moved to another file.

### 9.2 The per-architecture floor

Hand-written, once per architecture, trusted: the boot code (`hw/boot.S`), the interrupt and fault entry, a context switch, the
linker script (`hw/link.ld`), the instruction-cache step.  Everything else — page tables, interrupt tables, device drivers,
timers, the second processor's start-up (INIT/STARTUP through the local interrupt controller), even the interrupt entry routine
(`own`: written in Rocq byte by byte) — is Rocq.

### 9.3 What an operating-system writer writes in Rocq

The scheduler, the process and thread tables, the memory manager, the drivers and the filesystem are programs on the
primitives, like any other program (§0.6).  The toolchain's part is that they compile, are proved to compute their Rocq
definitions, and can carry the writer's own theorems (no page mapped twice, a lock held by one processor at a time — §12.G).

**The five test kernels** (`hw/build_proved.sh NAME`, `hw/run.sh NAME_p`; all prove and boot under QEMU's processor and KVM):

| Kernel | What it shows |
|---|---|
| `kernel` | serial line, screen, page tables, interrupt table, ten timer interrupts, the processor's registers, PCI, atomics, bulk bytes, assembly routines of its own |
| `irqnow` | interrupts handled at once by a Rocq program run at the interrupt |
| `fault` | a page fault handled by a Rocq program that maps the page; the access is retried |
| `smp` | a second processor running a Rocq program |
| `own` | the interrupt entry routine written in Rocq, byte by byte |

**Several programs in one kernel:** `hw/NAME_irq.body` runs at an interrupt or a fault, `hw/NAME_ap.body` on a second processor;
each is its own Rocq text, translated and proved (`kitc.py --secondary --prefix=irq_ --entry=kq_irq_body`); they share the tables
and the machine operations with the main program.  An interrupt program is compiled with `-mgeneral-regs-only`.

**A program's own routines:** an assembly or C routine declared in the Rocq text as an `Axiom` and listed in `hw/NAME.ext` is
called through `hw_user` / `hw_userf` (`hw/User.v`), assumed by `hw_law` / `hwf_law` like the other operations.

### 9.4 Concurrency, now and next

Now: one program per processor, each proved as a sequential function of the memory; shared memory only through marked
operations (`hw_aload` acquire, `hw_astore` release, `hw_atomic`, `hw_cas`, `hw_fence`: external calls with C11 atomics, so the C
compiler neither merges nor moves a plain access across them); a program lists the narrow blocks it shares (`kq_shared`) and the
translator refuses a plain access to them, or to any block whose number is not written where it is used.  The proof of each
program holds for every number a marked operation can give back.  `hw/lock.body` and `hw/lock_ap.body` on two processors each
add 1 to a counter 100,000 times under the spinlock: 200,000; without the lock (`hw/smp.body`) updates are lost.

Next (§12.G): an interleaving semantics of two programs, so that protocol properties (mutual exclusion of a lock, a queue) are
stated and proved once for all programs; a lock with fairness (ticket lock).

### 9.5 Freestanding

The generated C is built today with the kit's support code, hosted (tests) or bare (`hw/kq_bare.c` with the kernels).  Left: a
freestanding build of the generated C checked on its own (no hosted headers, no libc beyond what the support code provides), and
a freestanding `kq_grow` (today its hosted body is a `realloc`; on the machine, the program's own allocator does the same, and the
law is the same).

---

## §10. DECISIONS — SETTLED, DO NOT RE-ARGUE

Each with its reason.  Re-opening one needs a new fact, not a new preference.

| # | Decision | Why |
|---|---|---|
| D1 | **No runtime, no collector.**  Data that outlives a call is laid out by the program in blocks, with an allocator written in Rocq | the target is freestanding C, which has none; a runtime would make the C a different language (owner, 2026-10-19) |
| D2 | **The translator is untrusted; the generator is proved once; each function's statement is checked by the kernel** | the trusted base stays small and does not grow with the translator, however clever it gets |
| D3 | **Numbers are fixed-width (`int`, `u64`); `nat` is the loop counter; `Z`/`nat` arithmetic is not translated as fixed-width.**  Accepting `Z` where a proof shows its range is a possible later option, kept separate | treating `Z` as `int` changes the meaning (wrap-around); a bignum fallback is a runtime (owner, 2026-10-27: "keep it separate") |
| D4 | **General optimizations only; the yardstick is C written the same way** | the program as written decides the speed; a pass keyed to a benchmark hides costs and is unstable (owner) |
| D5 | **Gaps are found by construct (the table), never by sample programs** | sample programs find only what someone wrote; the table is finite and closed (owner, 2026-10-27) |
| D6 | **The toolchain is freestanding C plus primitives; a scheduler, process tables, a memory manager, drivers and a filesystem are user programs, not included** | C does not include them; including them would be hardcoding above the primitives (owner, 2026-10-27) |
| D7 | **Hardware is generic primitives; architectures are written by users in Rocq from the manual; nothing is ported in C or assembly** | per-family C bodies are hardcoding moved to another file (owner, 2026-10-15) |
| D8 | **CertiRocq's front end is not used by the proved route** | its translation theorem assumes no primitive operations (`no_prims`); every program here uses `PrimInt63` |
| D9 | **Rocq, not Lean, for this project** | MetaRocq gives Rocq's evaluation and erasure as formal objects, which the cost-shape work and this route's statements rely on; Lean's kernel formalization (Lean4Lean) is in progress and covers the kernel, not evaluation and erasure (§5.7) |
| D10 | **Proof speed: per-function files, a content cache, parallel runs and general tactic changes; segmenting long functions and reflection only when proof time becomes the bottleneck** | the cheap general wins are taken; the rest is a project with risk for a few functions (2026-10-26) |
| D11 | **The cache is not release evidence: `KQ_MONO=1` is** | a missing key ingredient could skip a check; the single-file run cannot |
| D12 | **Loops: the measure is the exact budget, never a guessed fuel; the equation and the induction principle are proved.**  `wfix` is the library form (built); Rocq's own `Program Fixpoint` / `Function` / `Equations` are read as well (owed: §4.5, §12.P) | a guessed fuel gives silent wrong answers; the owner asked for Rocq's own form ("level 2", 2026-10-29), and D22 makes its spelling the point.  Corrected 2026-10-30: this row first called reading `Program Fixpoint` optional, which recorded the substitute as the decision (F36) |
| D13 | **The only acceptance rules are §0.5.  The flat style of `WRITING-FAST-ROCQ.md` is performance advice, like keeping a C loop variable in a register** | a rule nobody can discover is an over-rejection; costs are the user's to choose |
| D14 | **One memory per function, linear** | lets a pure function be compiled to in-place updates and is what C programs do anyway |
| D15 | **Records and pairs are never built; they are their fields** | no allocation, and the C is what a programmer writes for a struct passed by value |
| D16 | **A function with two results returns the first and puts the second into the slot block, saved and restored** | no allocation; the statement states it exactly |
| D17 | **If-conversion at value choices (reads allowed); call-chain merges with plain arithmetic only** | measured both ways (§6.3) |
| D18 | **Budgets are capped at 2^60** | a counter always has room to count a few more, and no proof works a budget out; consequence: a measure must be below 2^60 |
| D19 | **Commits: authored by the owner only, no co-author trailer, no narration; push only when the owner says; no host details, addresses, user names or local paths in the repository** | owner's standing rules; the repository is public |
| D20 | **Proper over fast**: the straightforward, correct construction is preferred to a quick one; decisions are judged by this file's criteria | owner's standing preference (also in the cost-shape work) |
| D21 | **A gap is closed by a construction, never by stating its limit; a boundary needs a pin and a control; no translator check without a theorem that needs it** | §3.6; learned in the cost-shape work, where each was the cause of a re-opened item |
| D22 | **Natural and native over conventions of our own.**  A convention stays only if Rocq itself imposes it (structural recursion, linear use of a value in a pure function's in-place translation) or a theorem needs it; anything Lean or Rocq would accept as ordinary code is accepted (a counter at any position, the memory at any position, functions from other files, any captured kind) | owner, 2026-10-30: "own convention is nice, but I prefer natural native" |
| D23 | **A refusal reads like a type error, not a syntax error**: it names the construct, the place in the user's text, the reason (one of §0.5, or "not yet translated" for a gap), and what to write instead | the user writes ordinary Rocq; a refusal is about meaning (it needs a runtime), never about spelling |
| D24 | **The operation set is finite and is completed against freestanding C's operations (§2.1); full higher-order function values are not needed** | the generator's theorem is one case per operation; C has no closures, and its function pointers are an explicit table |
| D25 | **The top half moves to proofs built by construction, the CakeML way: the translator emits each piece of KQL with the lemma that justifies it (one lemma per construct), so no proof is searched for.  The hybrid stays (per-program proofs on top, one proved generator below); the translator itself is not proved (no single "for every program" theorem).  Spike first, then convert construct by construct, then the completeness theorem; release builds through `ccomp`**  *(Its plan — converting the walk — was superseded the same day by D26.)* | CakeML, the strongest project of this kind, uses this split with a proof-producing translator on top (§1.11); it removes proof-search failures and most proof time and makes each new construct one rule plus one lemma, at a fraction of the cost of a verified translator, which would mean proving the translator against MetaRocq's semantics with primitive integers for months (owner, 2026-10-30: "go ahead, record this decision with every context") |
| D27 | **The memory law "writes to two different cells commute" may be added to `KQSpec.laws`** (proved for the model in `KQModel.v`, with functional extensionality as the other laws are), when the construct that needs it is built — results of more than two numbers through the slot block | it holds of every memory; it does not follow from the two existing equations (F43); one more statement assumed of the real memory, so the owner decided (2026-10-30: "go ahead") |
| D28 | **Our own fork of Rocq carries the conversion memo** (rocq-prover/rocq#22309, backported to 9.1.1 as `rocq-fork/conv-memo-v9.1.1.patch`), not contributed upstream and not waited for.  It is a change to Rocq's kernel, so to the trusted base; the owner asked for it to be made sound and proved correct (§12.R) | measured: it removes F46 (a read-then-write chain of 100 steps checked in 0.003 s, 30 steps were over 120 s) with nothing else changed.  It is a **general** change (§0.7, §0.9 question 3), not a rule for some programs: memoization of the kernel's comparison within one conversion check, so that two shared subterms are compared once rather than once per path to them — the standard way to compare graphs with sharing, and what Lean's kernel does (F46: 13 ms at 1000 steps); it is not a store of results across runs (the table lives for one check and is dropped), and it is keyed to no construct or program.  Owner, 2026-10-31: "no need to patch upstream to them, we do our own upstream fork".  **Weighed against the alternative and chosen over it:** `Kq Definition` (the compiled function *defined as* `denote s` by our command, as `Program Definition` / `Equations` define theirs) adds nothing to the trusted base and needs no per-program check at all, but users write the command instead of `Definition`, the kernel checks "the C computes what you typed" only where the check is cheap, and users' own proofs that unfold a long read-then-write chain stay exponential; the fork keeps plain `Definition`, checks fidelity always in linear time and makes those proofs fast too, at the price of a patch under every proof.  The owner: "I will choose fork regardless unverified OCaml since it follows same as MetaRocq" — Rocq's kernel is unverified OCaml, and the project already relies on MetaRocq's OCaml quote, so an argued, model-proved, tested patch is the same class of trust |
| D26 | **A verified compiler by reflection: a syntax `S` of the accepted fragment, its meaning `denote`, a compiler `compile : S -> KQL` proved once, the user's function reified into `S` by an untrusted reifier, and per program only the conversion check `denote s = f`.  The current translator with the walk stays as the fallback until `S` covers the table; emit-then-prove is the interim.  The walk is not converted to proofs built by construction (D25's plan dropped)** | the owner needs other people's programs compiled with zero proof time (2026-10-30); MetaRocq's formal evaluation has no rule for primitive operations, so a translator verified against it cannot even state our programs' runs and would add MetaRocq's quote and typing/erasure assumptions to the trust; reflection gives one theorem for every program of `S`, no search per program and nothing added to the trust (§1.12).  The owner, after the full comparison (§1.12, "the weighing"): "we are going with reflection" |

---

## §11. FINDINGS AND TRAPS LEDGER

Dated where known.  "Fixed" means fixed in the tree; the entry stays so the trap is recognized if it returns.

| # | Finding | Consequence / fix |
|---|---|---|
| F1 | CertiRocq's `convert_top_anf_correct` assumes `no_prims`; λANF's `bstep` has no rule for primitives (and one lemma there is admitted) | D8: the proved route goes around it (2026-10-17) |
| F2 | MetaRocq's generic term equality costs ~0.3 s per comparison under `vm_compute` and blew 4 GB | compare constant names, never whole terms by the generic equality |
| F3 | Under MetaRocq's imports `ident` is a byte string | use `positive` for KQL names |
| F4 | A `nat` literal in a program must be one constant (`nat_lit`), or the walk recurses its depth | budgets as `Abud` atoms; `kq_nat` opaque |
| F5 | `reflexivity` on a goal with a computable result made Rocq evaluate a whole sort | `exact eq_refl` (kernel conversion): 0.05 s |
| F6 | `;` after `eapply L; [a|b|c]` binds wrongly when a preceding tactic made several goals | parenthesize |
| F7 | A chain of 64-bit operations made the kernel check run over 40 minutes | `w64_op` sealed behind a `Qed`, its meaning an equation |
| F8 | `cbv` reduction lists must include `PrimInt63.land/lor/lxor/add/sub/mul`, or case-splitting destructs literal tests | the lists in `KQMAuto.v` |
| F9 | Bindings as a `PTree.set` chain worked out per lookup | compaction every 24 bindings (119 s → 16 s on one table) |
| F10 | Counter rewrites scanned the whole goal at every addition | guarded by syntactic patterns; only inside an induction |
| F11 | Read-modify-write runs double the memory term per step; one `change` of the whole `let` chain was exponential (kernel conversion of `let` chains) | named memories, peeled one `let` at a time; plain walk first with a 150 s timeout |
| F12 | A first parameter of type `int` was tried as an induction | induction only when the first binder is a `nat` |
| F13 | A helper that writes the memory was not seen as writing, so its caller was stated as reading | `writes` looks into helper bodies |
| F14 | A budget worked out at run time with a symbolic value blew memory in `vm_compute` | `kq_nat` clamped, bounded by `kq_nat_cbk` before any computation |
| F15 | A failed `rewrite` with a known test was a full goal traversal per hypothesis | syntactic occurrence check first (45 s → 25 s on one function) |
| F16 | Two functions given to a template were never equal if they contained a test, a `let`, a projection or a local `fix` (`term_same` had no case) — a hole from the start | cases added (2026-10-29) |
| F17 | A budget made of numbers written in the program was reduced by the proof to a numeral, which a copy's statement (about `ofn x0`) cannot match | `deep_norm`: such a budget is a written budget (`Abud`) (2026-10-29) |
| F18 | A `let`-bound local function was refused ("a let of a type this translator does not read") | put in at each use |
| F19 | A `match` on a counter was read only at the top of a recursion; inside any other construct it was refused | read anywhere: ~190 cells of the table (2026-10-27) |
| F20 | In files importing the kit, `x mod y` resolved to the unsigned remainder | name `Sint63.rem`, `Sint63.div` |
| F21 | A termination tactic with `F` folded produced `r1 = r2` and an 8 GB unification | open the head of `F` first; timeout on `apply` |
| F22 | A changed library not recompiled made a test run the old code | recompile in dependency order before testing a dependent file |
| F23 | Inside `%Z`, an argument's `y - 1` is integer subtraction | `(y - 1)%sint63` |
| F24 | An in-process `ulimit -v` makes an OCaml process abort out of memory with a core dump the size of the process; repeated probes filled a disk with dumps (2026-10-20) | memory caps on the container (a kill, no dump), `--ulimit core=0`, no `ulimit -v`, one probe at a time, a free-disk guard |
| F25 | A container backend went down once under load | stay within the memory cap; restart is the machine owner's call |
| F26 | The kit route's checker appended dead lists per `if` (three times per test): exponential | union instead; verdicts unchanged |
| F27 | `(hw_*)` inside a Rocq comment ends the comment (`*)`) | avoid that spelling in comments |
| F28 | `a && b && c` is left-nested | the `&&`-splitting rules expect it |
| F29 | Two processors racing: the race loop must come right after the barrier, or the loops never overlap | `hw/smp.body` |
| F30 | Merging call chains with reads in the arguments made a phase-cycling loop twice as slow | D17 |
| F31 | Reloading the block tables at every access costs nothing (clang hoists them) | no pass for it |
| F32 | The 2^60 budget cap makes a large measure fall outside the theorems | the domain of a measure function includes "below 2^60" |
| F33 | Proof time is dominated by the longest function; parallel files cannot split one function | §7.5 |
| F34 | Lean's freedom comes from its runtime; its front-end passes are the model | §5.7 |
| F35 | The five cells counted "by design" (`option`, a sum, a list cell, a function in a pair, a dead memory `let`) were classified by type; their programs build and take apart the value in place or never use the second memory, and `A_par_fun_result`, in the same list, was accepted all along | reclassified as gaps (41); §0.5 now says the cause is size and lifetime, never type; a design cell needs a pin that shows the cause, and a control (2026-10-30) |
| F36 | The owner asked for loops "level 2" — Rocq's own `Program Fixpoint`, as offered; `wfix` was built instead and recorded as the decision, the owner's form "optional" | the owner's request is the target again (D12, §4.5, §12.P); §13.8 has a row for this drift (2026-10-30) |
| F39 | `a || b` at the end of a function giving back a boolean, read as `orb` (both sides worked out, then combined), makes a call of the function itself in `b` a real call: the recursion grows the stack | read as `if a then true else b` there, so the call is a loop, as C's short-circuit makes it |
| F40 | The rules for values built and taken apart in place, applied everywhere, could change the C of programs that were already read | they apply only to values the readers do not hold and to dead memory lets; measured: 142 generated C files byte-identical with and without (2026-10-30) |
| F41 | After normalizing, a reader's literal case built its atom from the original term: `Aint (let s := .. in 7)`, a free variable at definition time ("The reference 4 is free"), seen on the simplest cell `P_int_lit` | every reader rebinds `t` to the normalized term |
| F42 | In the table's cells the value taken apart is usually a helper's call (`match k a with ..`), which the normalizer did not see through | `unfold_h` writes a helper's call out before the rules look at it |
| F43 | Giving back more than two numbers needs the caller to put back several cells of the slot block, which needs writes to different cells to commute; the laws have no such statement and it does not follow from `upd_upd` / `upd_rd_id` (memories are equal only through those) | waits on the owner (adding a law to `real_laws` is adding to the trust); the model would prove it with functional extensionality, as it proves the others |
| F44 | `kitc.py` prints only the last 300 characters of a failed translation, mostly warnings; the classifier then cannot see the reason | read the `.v`'s error, or the `KQM: refused:` line; `run.sh` keeps 400 characters of a cell's output |
| F45 | The dead-`let` check of the normalizer made the three kernels with the 2,400-step function 10–20% slower to build: `||` and `existsb` work out both sides under `vm_compute`, so every memory `let` scanned the whole rest of the function (quadratic in its length) | the type is looked at first, and the scan stops at the first occurrence; the kernels back within a few percent of the pushed translator, measured the same day (§7.3) |
| F46 | The per-program check `denote s = f` is exponential in the number of steps of a straight-line body that reads a memory and then writes it (`let s1 := upd 0 1 (rd 0 0 s + 1) s in ..`, each memory used twice): 10 steps 0.003 s, 20 steps 0.7–1.0 s, 30 steps over 120 s (`KQR.v`, `chain10`/`chain20`, 2026-10-31).  It is Rocq's conversion: after the `let`s are substituted the kernel compares the two sides path by path, with no memory of what it has already compared, and a memory used twice per step doubles the paths per step.  Measured apart from `S`: the same chain against a verbatim copy of its own text, 16/18/20 steps, 0.09/0.24/0.73 s by the elaborator's conversion and 0.015/0.065/0.25 s by the VM's (`vm_cast`), the same growth.  The walk met the same wall (F11).  Not affected: memories used once per step (`x86_setup`'s chain of `hw_store`s), lets of numbers (the 300-let body: 0.001 s), and the same steps in a helper or a loop, because a call or the recursive call is a constant on both sides and the comparison stops there | open.  **Not fixed in Rocq** (measured 2026-10-31, the kernel alone, `exact_no_check` then `Qed`, a standalone file with `mem`/`rd`/`upd` as axioms, 16/18/20/22 steps): Rocq 9.1.1 (ours) 0.17/0.46/1.53/5.35 s; `rocq/rocq-prover:dev` = 9.4+alpha of 2026-10-29 (commit `a533ceb`, newer than the latest release 9.3.0 of 2026-09-19, includes the merged #22299, a pointer-equality shortcut) 0.13/0.30/0.98/3.24 s — the same growth.  **The fix is proposed upstream, not merged**: rocq-prover/rocq #22309 "kernel: cache conversion results within a session" (open; a table of pairs of closure cells already found convertible, for one conversion — its description is this finding: "the cost of the check then scales with how many times a shared subterm occurs, not with how large it is"), with #22319 (the cache as flat arrays) and #22401 (draft, further experiments) on top.  **Lean has it**: Lean 4.32 (the `kernelq-lean` image), the same chain checked against the meaning of a syntax tree (`den`, by `M.rec`, the `MLetM` shape), kernel 0.38/0.44/0.51/2.4/12.9 ms at 20/30/40/200/1000 steps, the elaborator's `rfl` ~130 ms at 1000 — its definitional-equality check remembers pairs already found equal.  CakeML (HOL4) has no conversion in its kernel: its translator proves each construct with a lemma and never compares a function with a separately built term (by design, not measured here).  **The cache removes it (measured 2026-10-31, on the work laptop):** #22309 built on its own base: the chain against `den`, cache off 0.15/0.25/1.0/3.8 s at 16/18/20/22, cache on 0.000–0.003 s up to 1000 steps (the whole file with the 1000-step chains 0.53 s, 376 MB).  **Backported to our Rocq 9.1.1** (`rocq-fork/conv-memo-v9.1.1.patch`: the PR's three files, two of its call sites rewritten for 9.1.1, `fid = 0` in every cell literal — the compiler refuses a literal without it): standalone the same (cache off 3.3 s at 22, on 0.003 s at 1000); **our own `KQR.v` chains** (the 9.1.1 image, only `rocq-runtime` replaced so the compiled libraries stay valid — replacing `rocq-core` rebuilds Corelib and every library compiled against it is then refused as inconsistent): `chain20` `denote = f` 1.15 s → 0.003 s, `chain30` (over 120 s before) 0.000 s / 0.002 s, `chain100` 0.001 s / 0.003 s (the equation / `compile_f_ok`'s theorem), `Print Assumptions` unchanged.  The elaborator's own check (`exact`) does not use the cache (it is unification, where the PR keeps it off), so the per-program step is `exact_no_check` and the kernel checks at `Qed` — the trust is the same.  Adopted as our fork: D28.  The other ways out, not taken: skip the check for such a function (trusts the reifier); a style rule (D13, D22) |
| F47 | Rebuilding the image on the fork filled the heavy-run machine's disk to 0 bytes (2026-10-31): `opam reinstall --keep-build-dir` kept the build folder of every package (MetaRocq's alone is many GB, against 3.8 GB for the whole installed switch), and `docker commit` then wrote the container's changes a second time as a layer; the free-space guard ran only when a job started, and — found after the recovery — it read the free space wrongly (the directory count printed before the number was glued onto it, so it refused only near 0 bytes): how much was free when the build started is not known.  The container runtime went down, the data disk gave I/O errors, the machine's other containers stopped at the engine's restart.  Recovered by deleting the job's own objects through Docker after the engine came back, then `fstrim` (0 → 31 GB free) | an image build keeps only the build folder it needs (CertiRocq's, for the kq2 patch), deletes sources and caches before the commit, and checks free space during the build (stop under 20 GB), not only at the start; expect the commit to need the container's growth again.  The guard's reading is fixed and was checked both ways (it passes at the real 45.6 GB, refuses at a higher threshold).  The rebuild done that way: 69 minutes, the container grew 4.09 GB, free space never under 45 GB |
| F48 | The proof cache's key did not include Rocq itself: the tactic libraries, `KQRun.v`, the header and the printed functions only.  A tree that kept its cache across a change of kernel (an upgrade, our fork, D28) would have reused proofs the old kernel checked without checking them again (found 2026-10-31 when the kernel changed) | the key includes the content of the `coqc` / `rocq` executables (the kernel is linked into them) and `ROCQ_CONV_CACHE` (`rocq_id` in `kitc.py`); every cached proof is missed once after the change |
| F38 | MetaRocq's formal evaluation (`EWcbvEval.eval`, `PCUICWcbvEval`) has rules for primitive values only, none for primitive operations: `PrimInt63.add` has no body, `eval_delta` cannot fire, every program here is stuck in it | the verified compiler is built by reflection over our own syntax instead (D26, §1.12) (read in the image's MetaRocq sources, 2026-10-30) |
| F37 | CakeML's architecture is ours: a proof-producing translator from the logic's functions on top, one verified compiler below; Pancake is verified through a proof-producing decompiler.  The difference is that CakeML builds each proof by construction while ours searches | D25, §1.11 (read in the CakeML repository, 2026-10-30) |

---

## §12. THE WORK LEFT — the live, ordered plan

Each item: what, why, and how it is accepted.  The order is by how much of the goal it closes per unit of risk.

**The order to take them in** (the letters are names, not the order): the batch of **A** in progress lands (done,
`30d0199`) → **B**'s emit-then-prove part (done: `--emit-first`, `--no-proof`) → **V** (the verified compiler by reflection:
spike, then growth; D26) → the rest of **A**, **L**, **P** (the user's ordinary text refused), done as constructs of `S` →
**O** (operations C has) → the rest of **B** (compiling like `lean --c`) → **C** → **D** → **E** → **H** (with release builds
through `ccomp`) → **G** → **M** → **J**; **F**, **I** and **N** when their condition arises; **K** when the owner says.
**Q** is dropped (D26).

**A. The construct-table gaps (20 cells, §3.5), then the by-design pins.**  The categories of §3.5: proof search for
pair-valued choices and nested counter tests (6); polymorphic and class-based helpers by specialization (4); arithmetic and
comparisons on counters (4); records of three numbers by recursion (3, with the commuting law, D27); an
`option` across a call or as a loop's state (2); a local `fix` with captures (1).  Under §12.V the remaining ones are done as
constructs of `S`.  Then the pins of §0.5's boundaries, each with its control (§3.5): cells added to `gen.py` and to
`DESIGN_CELLS` together.  Accepted when: the category's cells are `ok`, the full table is re-run and `MATRIX.md` updated, and
the gate (examples, corpus, kernels if the walk changed) passes.

**B. Compiling from an ordinary `.v` file, as simply as `lean --c`.**
- A command (`Kq Compile solve.`) in an ordinary Rocq file: the entry's arguments are read from its signature (numbers from the
  command line, the memory from the memory file), replacing the `main` convention of `.body` files.
- ~~Emit first, prove behind~~ — **done 2026-10-30**: `kitc.py --emit-first` (the C and the binary right after the
  translation, the proofs behind; §1.7).
- ~~A check-only mode~~ — **done 2026-10-30**: `kitc.py --no-proof --no-build` (the translation alone, with its refusals).
- Refusal messages that say what to write instead (the library, the rewrite), with a pointer into this file.
Accepted when: every example and corpus program compiles from a `.v` file with the command, with the same C as today.

**C. Language beyond the table.**  Records of k numbers as results (the slot block with k-1 cells); strings and a formatting
library on byte blocks (`printf`-like, written in Rocq); an address type with proved arithmetic, and pointers beyond views;
specialization of type and instance arguments; optional: `Z` where a proof gives the range (D3).  A tactic that proposes the measure itself for the common loop shapes (counting up to a bound, counting
down, halving), so `wfixN` needs no measure written for them; loops whose end depends on the data still take one.

**D. Freestanding.**  The generated C built and checked on its own (no hosted headers, the support code only); a freestanding
`kq_grow`.

**E. The general speed passes (§6.4):** bounds-test removal where the index is proved in range; forwarding; hoisting.  Each
proved once, measured against C written the same way.

**F. Proof speed, only if it becomes the bottleneck (§7.5):** segmenting long straight-line functions; reflection.

**G. Concurrency:** an interleaving semantics of two programs over the marked operations; protocol properties proved once (a
lock's mutual exclusion, a queue); a ticket lock.

**H. Checks of the trusted tools:** the printed C compiled by CompCert's own front end (`ccomp`) and compared; UBSan builds of
the corpus and examples.

**I. Hosted features, when a program needs them:** `PrimFloat` as C `double`; system calls as primitives with a trace;
declarations of C library functions as primitives with laws.

**J. Documents:** split `WRITING-FAST-ROCQ.md` into "what is refused" (§0.5) and "what costs what" (performance advice), and
update its cost table (on the proved route pairs and records do not allocate; functions given to helpers cost nothing).  Do it
once the table's gaps are closed, so it is written once.

**K. Push** the local commits when the owner says (§14).

**L. The translator's side conditions (§3.7):** the generator family that varies parameter order, memory count, file, and capture
kinds; then counter at any position, memory at any position, functions from other files (multi-file programs and user
libraries), captures of every kind.  Accepted when those cells are `ok` or pinned by design with a control.

**M. Naturalness as a theorem (§3.8):** the grammar of the fragment, its decision procedure, and the completeness of the
translator on it; the walk's completeness through a reflective checker if that is built (§7.5).

**N. One text, its cost and its C (optional, later).**  The cost-shape work proves a word-RAM bound for programs written in a
cost monad (KernelQ, `docs/rocq-cost-shape-solution.md`); this route compiles plain programs to C.  Joining them means the same
Rocq text carries both: its complexity bound proved and its C proved.  Spikes on the cost-shape side measured pieces of it (a
cache as an ordinary layer over the same RAM with a locality bound; space read off the memory with an allocator as ordinary
functions; a C loop matched step for step to the Rocq loop).  Not started here; it needs the cost monad's charges to erase to
nothing in the C, which is a translator rule plus a theorem.

**O. The operation checklist (§2.1):** `uint64_t` division and remainder, signed 64-bit arithmetic, the high half of a product;
a library for 8/16/32-bit signed and unsigned arithmetic with C's wrap-around; optionally `popcount`, `clz`, `ctz`, `bswap`,
rotate as single instructions.  Each is a constructor, a case of the generator's proof, its C, and an example.

**R. The kernel's conversion memo, made sound and proved (D28, F46).**  What can be proved, and what not: (1) a Rocq proof of the
memoized comparison over a model of the closure machine — cells with identities, allocation (a fresh identity), the in-place
update (a cell's term replaced by a reduct of it), copies (a new identity), the table keyed by the two identities, the two lifts
and the problem — that every answer from the table is the answer the comparison would give, assuming what the kernel already
assumes (its comparison decides convertibility; a reduct is convertible to its redex); (2) the invariants the model needs, made
checkable in the OCaml: every cell literal carries `fid = 0`, the counter is the only place an identity is given, `update`
writes only `mark` and `term`, the table is created only for checked conversion; (3) differential testing: every proof of this
repository, the image's libraries and Rocq's own test suite with the memo on and off, the verdicts compared.  Not provable here:
that the OCaml code is the model — Rocq's kernel is unverified OCaml and there is no verified path from OCaml in this stack —
so (2) and (3) carry that step, as they do for the rest of the kernel.  Then the image is rebuilt on the fork (Rocq, Stdlib,
MetaRocq, CompCert, CertiRocq recompiled; plugins must be, since the kernel's interfaces change) and the gate run.
**(1) done (2026-10-31): `rocq-fork/ConvMemo.v`** — cells as a map from identities to their current terms (a cell without an
identity is not in it), `assign` (= `uid`: the counter's next value), `reduce` (= `update`: a reduct in place), `record` (an
outcome the comparison gave), the states reached from the empty table (`reach`); **`lookup_correct`: every outcome taken from
the table is true of the current terms of the two cells**, `table_functional`: no two outcomes for one key,
`lookup_correct_flift`: the key made by stripping `FLIFT`s is the problem's.  Hypotheses: the relation is invariant under a
reduction step on either side at any lift; the comparison run on a miss gives the true outcome given true sub-outcomes;
`lift l (FLIFT n t) = lift (shft n l) t`.  `Print Assumptions`: closed (no axiom).  **(2) done: `rocq-fork/check_patch.py`**
— on the patched tree all 13 checks hold (57 cell literals and copies set `fid = 0`, none a nonzero one; one write of an
identity, in `uid`, after the counter; `update` writes the mark and the term only, and the one other in-place term write is
the lock of a cell under reduction, `FLOCKED`, written back by `update`; the table created only under `use_cache`, on for
`gen_conv`, off for `generic_conv` and for the pre-check registered on CClosure; a hit returns the universe state as given);
on stock 9.1.1 it fails.  **(3), the image:** building on the work laptop (opam pins `rocq-runtime`/`rocq-core` to the patched
tree and recompiles every package of the image, then the kq2 CertiRocq patch as `patch/rebuild.sh` does).
**The image is built** (`kernelq-certirocq:1b45a1aa-kq2-fork`, on the heavy-run machine; the disk-safe recipe of F47: 69
minutes, the container grew 4.09 GB) **and the cold gate passes on it (2026-10-31)** — a fresh tree from the repository at HEAD,
every file compiled and every proof checked by the patched kernel (the cache key now names the kernel, F48): `make.sh`
`core-ok` (36 s); examples 22 / 22 give the expected answer (4 m 56 s); corpus 36 / 36 proved, built and equal to the C++ answers
(7 m 16 s for the proofs); the five kernels proved and built in 34 / 35 / 36 / 54 / 40 s (irqnow, fault, smp, own, kernel; the
stock kernel's the same day 36–57 s); **the generated C byte-identical to the stock kernel's for all 66 programs** (22 examples,
8 kernel programs, 36 corpus).  Trap: a fresh tree has no `big/` inputs (`*.mem`, `*.args`, `*.in`, the C++ answers are
git-ignored, made by the setup scripts), so `corpus.sh` reports every program as not agreeing with `result 0` — copy or make
them first.  **Rocq's own test suite on the fork, the memo on and off (2026-10-31):** the same patched binary, run as the
`rocq-test-suite` package runs it (`make -k`, against the installed `rocq`; the OCaml unit tests need `ounit2`, not installed,
so they do not run): **2,521 tests pass and 1 fails in each run, and no test changes its verdict when the memo is switched on**
— the suite's tests that two terms must *not* be convertible included.  The one failure, the same in both, is
`misc/bench-render` (`rocq timelog2html`, a tool rendering timing logs as HTML: not the kernel).  **(3) is done.**  **(4) done (2026-10-31):** the per-program steps of `KQR.v` and
`KQRReify.v` are `exact_no_check` (the elaborator does not run its own, unmemoized comparison; the kernel checks the term at
`Qed`, with the memo — nothing more is trusted), and `proved/KQRChain.v` (in `make.sh`) pins read-then-write chains of 30, 100
and 300 steps: on the fork, `make.sh` `core-ok`, each `denote = f` 0.000–0.002 s at `Qed` and each composed theorem 0.003–0.076
s to elaborate and 0.002–0.006 s at `Qed`; `Print Assumptions` the same base.  **§12.R is done: the fork is the route's kernel**
(images.sh's third image; `KQRChain.v` needs it — on the stock kernel it is exponential).

**P. Rocq's own measure recursion (§4.5) — the owner's "level 2".**  Read `Program Fixpoint {measure ..}` (then `Function`,
`Equations`) as `wfix` is read: the same KQL, the walk unfolding with `Corelib.Program.Wf.fix_sub_eq` and inducting on the
measure, no new assumption.  Accepted when the `wfix` examples written as `Program Fixpoint` compile, prove and give the same
answers, and the construct table has cells for each spelling.

**V, how `S` grows — the design (2026-10-30), so each step extends the proof instead of redoing it.**
1. **Signatures.**  A function is: a counter or not (first parameter, `nat`, recursion on it), `k` numbers, a memory parameter
   or not (last), a result (a number; then a memory, a boolean, a number and a memory, a record).  Its meaning has exactly the
   user's curried type, built by `abs`/`app` generalized over the signature, so the per-program check stays a conversion.
2. **Programs and calls.**  A program is its functions, callees first (as the translator orders them today).  A call is
   `SCall i args` (and the counter argument when the callee recurses on one).  The meanings of the callees are *parameters* of
   `denote`: at the per-program check they are the user's own constants, so the user's text `h a b s` is literally what the
   meaning reduces to (no unfolding of `h`).  The theorem of `compile` assumes the callees' KQL statements — the same modular
   structure as today's per-function statements: each function's theorem uses the ones before it, checked one by one.
3. **Memory.**  Numbers and memories are two sorts with two environments (the numbers, the memories), `let` of either sort,
   `SUpd` (a write) and the memory functions (growing, views, machine operations) as memory expressions.  `compile` checks
   linearity — only the newest memory is used, as `KQMTrans` refuses "a memory used after it was handed on" — and the proof's
   invariant is that the KQL memory is the newest memory.  Reads and writes need no memory law (KQL's semantics applies
   `KQRun.rd` / `upd` themselves); the laws enter only where the slot block is put back (results of several numbers, D27).
4. **Then, from the construct table:** booleans (a sort held as 1 or 0), records and pairs (their fields as separate
   variables; several numbers as a result through the slot block), a number and a memory as a result, values taken apart in
   place (the reifier does `knorm`'s rewrites before building the tree, so they are no construct of `S` at all), functions given
   to functions (the reifier makes the copy per function given, as the translator does; the copy is an ordinary `S` function),
   measure recursion (`wfix`, as a template).
5. **`kitc.py --reflect`** compiles a program through `compile` when its root and every callee are in `S` (the C at once, each
   function's theorem one `exact` and a conversion), and falls back to the translator with the walk otherwise; the gate runs
   both; each step of `S` moves programs from the fallback to the verified path, measured on the examples, the corpus, the
   kernels and the table.
Each step: the `sexp` node(s), the `denote` case, the `compile` case, the proof case; `sum` and `long` re-checked; an example
added; the per-program check timed on the longest function it now covers.

**Step 1 done (2026-10-30): signatures, plain functions, calls.**  A function has a signature `sig` (`sc`: a counter first;
`sk` numbers; `sm`: a memory last) and a body `FRec e0 e1` (recursive on the counter) or `FPlain e`; its meaning has the user's
curried type (`ntype`, `ftype`, `absn`, `appn`, `callf`; a function without a memory gets the kit's declared `kq_input 0` as a
memory it never reads).  A call is `SCall f c args` (`c`: no counter, this function's counter, its predecessor); the meanings of
the callees are parameters of `denote_f` (`callee := {g : sig & ftype g}`).  **`compile_f_ok`: if every callee's KQL computes
its meaning (`callees_ok`), the function's KQL computes its meaning (`callee_ok`)** — proved once, with the counter's induction
for `FRec`, over `cexp_all` (now with the call case) and `ctail_ok`; `denote_nomem` (a body that reads no memory means the same
for any memory) and `denote_rec_ext` (the meaning depends on the recursive call only through its values) carry the no-memory
case.  End to end with a call: `h` (a plain helper without memory) and `loop` (a loop calling `h acc (rd 0 i s)`) — the kernel
accepts `loop = denote_f [existT ftype h_g h] ..` with the user's own `h` as the callee's meaning, and `loop_ok` is
`compile_f_ok` with `h_ok` as the callee assumption: each per-program step 0.000–0.004 s; assumptions Rocq's integers and the
kit memory's declared operations only.  **The reifier reads programs (2026-10-31):** `reify_prog` takes the quoted root, finds the
program's functions with `reach` (the root's own file's constants that have a body, callees first, as the old translator orders
them), and reads each with `reify_fun` — a recursive function (`FRec`) or a plain one (`FPlain`), its signature off its
parameter types (`read_sig`), the user's calls as `SCall` (the callee's counter and memory read off the arguments).  From
`loop`'s text it finds `h`, orders it first, and gives exactly the hand-written trees; the KQL program is made from the reified
list (`funs_of`), and the per-program theorems follow — `h_ok_r`, then `loop_ok_r` with `h_ok_r` as the callee assumption —
0.000–0.002 s each, assumptions the same base.  Next: step 3 of the design, memory writes (numbers and memories as two sorts,
linearity checked by `compile`), then `kitc.py --reflect`.

**Step 3, memory writes — the design in detail (2026-10-31).**
- *Syntax.*  A third mutual sort `smem`: `MCur` (the newest memory), `MUpd h i v m` (`upd h i v m`), `MLet e m` (a number
  `let`), `MLetM m1 m2` (`let s2 := m1 in m2`), `MIf c a b m1 m2`, `MRec args` and `MCall f c args` (calls of functions that
  give back a memory).  Numbers gain `SLetM m e` (`let s2 := m in e`).  A read `SRd h i` and every call pass **the newest
  memory**; a call or read on a written memory written inline (`h a (upd .. s)`) is reified as `let s2 := upd .. s in h a s2`
  — the kernel's conversion includes `let` (zeta), so the per-program check is unchanged.
- *Signatures* gain the result kind (`sr`: a memory, which requires `sm`): `ntype k m r` ends in `mem` or `i63`; the recursive
  call's meaning is of that kind.
- *Meaning.*  `denote_e` / `denote_m` take the memories in scope `menv` (nearest first): `MCur` is the nearest, `MLetM` binds
  `let s2 := .. in ..` exactly as the user's text.
- *Linearity, checked by `compile`'s well-formedness.*  Only the newest memory is ever named, and an expression that writes
  consumes it: after a write the memory before it is dead.  The KQL memory is threaded; the proof's invariant is **"the KQL
  memory is the newest memory of `menv`"**.  Inside one construct the numbers are worked out first, reading the memory before
  the construct's own writes (`MUpd h i v m`: `h i v` read the memory `m` starts from — what the Rocq text means — then `m`
  writes, then the write), as `tr_mem` does today.
- *Refused for now* (a later step, the number-and-memory results): a function giving back a number that writes the memory —
  after such a call the caller's memory in Rocq is still the old one while the KQL memory has changed; today's translator
  handles it by invalidating the caller's memory (`runx`), and so will this, with its own statement.
- *Laws.*  Writes need none (KQL's semantics applies `KQRun.upd` itself, as for reads).

**Step 3 done (2026-10-31): memory writes.**  Built in `proved/KQR.v` and `proved/KQRReify.v`, with two changes to the design
above, both found by reading KQL's semantics against the user's text:
- *`smem` is its own inductive, not mutual with `sexp`*, and numbers gain no `SLetM`: in this step a number never writes (a
  function giving back a number that writes is the deferred `runx` case), so a number expression is evaluated on one memory and
  the number lemmas (`cexp_all`, `ctail_ok`) only gained the memory as an argument instead of a section variable.  When the
  `runx` case comes, a writing number body is a third sort over `smem` and `sexp` (`let s2 := .. in` then a number), which
  again leaves `sexp` as it is.
- *`MRec args m` and `MCall f c args m` carry their memory argument as a sub-expression* instead of always passing the newest
  memory: `fill m (i + 1) (upd 0 i v s)` is read as written, and the number arguments are worked out on the memory before the
  write — what the text means when an argument reads `s` and the memory argument writes it (with the `let` reading of the design,
  such an argument would read the written memory and the check would refuse the tree).  So `menv` is not needed: only the
  newest memory can be named at all.
The syntax: `MCur`, `MUpd h i v m`, `MLet e m`, `MLetM m1 m2` (`let s2 := m1 in m2`), `MIf c a b m1 m2`, `MRec args m`,
`MCall f c args m`; `sig` gained `sr` (a memory as the result; `ntype k m r`, `rty r`); a call's number and memory are `calln` /
`callm`; `fbody` gained `FRecM` / `FPlainM`; `callee_ok` says a function giving back a memory returns 0 and leaves
`callm ..`, one giving back a number keeps the memory.  `cmem` compiles a memory in continuation style (the numbers, then the
memory given, then `Ekst` or the call), `ctailm` in tail position (a test is a branch, the recursive call `Eloop`, the end
`Eret 0`).  **`cmem_ok`: KQL's memory after the code is the memory the Rocq text makes** — that is the whole invariant, since
the syntax names only the newest memory; `ctailm_ok` for the tail; `compile_f_ok` gained the two memory cases (the counter's
induction for `FRecM`), proved on the first compile.  `wfm` checks the memory side (the recursive call only where allowed, a
callee called for a memory takes and gives one, a callee called for a number gives a number).  **Linearity**: in the syntax, by
construction; in the reifier, a `let s2 := .. in` marks every older memory dead (`CDead`, `kill_mem`), so a text that uses an
older memory after a newer one (`dup`: `let s2 := upd .. s in upd 0 1 (rd 0 0 s) s2`) has no tree and is refused there, with
its reason (§0.5's third refusal).  **Measured** (`KQR.v`, `KQRReify.v`): `fill` (a loop writing the memory), `suffix` (a
recursion that is not a tail call, its result bound by a memory `let` and then read and written), `init` (a test, a write, a
call of `fill` on the written memory), each `denote = f` and each composed theorem 0.000–0.02 s; the reifier gives exactly the
hand-written trees, finds `fill` from `init`'s text and orders it first, and `init_ok_r` takes `fill_ok_r` as its callee
assumption; `Print Assumptions` of `init_ok`, `init_ok_r`, `chain20_ok`: Rocq's integers and the kit memory's declared
operations, no memory law, no admit; `make.sh` `core-ok`.  **A limit found, shared with the walk (F46):** a straight-line body
that reads a memory and then writes it, step after step, makes the check exponential in the number of such steps (10 steps
0.003 s, 20 steps 0.7–1.0 s, 30 steps over 120 s) — a property of Rocq's conversion, not of `S`: the same chain compared with a
verbatim copy of its own text grows the same way.  The same steps in a helper or a loop cost per step.  Next: `kitc.py
--reflect`, then the table's constructs (booleans, records and several results through the slot block with D27, number-and-
memory results and writing number functions, functions given to functions, `wfix`, `Program Fixpoint`).

**`kitc.py --reflect` (2026-10-31; `KQ_REFLECT=1` for the scripts that call it).**  Per program: `NAME_r.v` quotes the entry
`main` applies and runs `KQRReify.reify_prog` on it (printing each function's name and signature, `info_of`); if every reached
function is read, `NAME_rp.v` defines `NAME_prog` from `KQR.compile_f` and gives function `j` its theorem
`KQR.callee_ok NAME_prog (gid1 j) ..` by one `exact_no_check (KQR.compile_f_ok ..)`, the theorems of functions `0 .. j-1` as its
callee assumption (`KQR.all_ok_callees`, a lemma that packs them); the kernel checks each at `Qed`.  The C is printed from
`NAME_prog` by the same printer, the driver filled from the entry's signature (its id `1000 + j`, its parameter kinds, its
result).  A program the reifier does not read, or whose check fails, takes the translator and the walk as before (reported).
Names are qualified (`KQR.`, `KQRReify.`), so a user's function may be called like a test of `KQR.v` (`sum`, `loop`, ...).
Measured on `proved/examples/reflect_calls.body` (a loop over block 0 calling a helper without memory; answer 2515, worked out
by hand): proved by the verified compiler, 2 functions, built, 2515; the whole `kitc.py` run 2.31 s against 4.32 s for the
translator and the walk (the theorems take milliseconds; the rest is starting Rocq and loading).  The fallback: `loop_while`
(`loop_two`, not in `S`) is reported not read, then proved by the translator, answer 41.  Next: the gate with `KQ_REFLECT=1`
(how many programs take the verified path — the measure `S` grows against), then the table's constructs.

**Q. (Dropped by D26; kept for its reasoning.)  Proofs built by construction (§1.11, D25).**  (1) The spike: lemmas over the Rocq constructs for `Eop`, `Eif`, `Esel`,
`Eret`, `Ecall`, `Eloop` and the counter match, emitted by the translator, on `wfix.body`, one corpus program and `x86_setup`;
proof time and acceptance measured against the walk.  Continue only if at least as reliable and faster.  (2) Conversion,
construct by construct, the walk as fallback until the last construct has its lemma.  Accepted when every example, corpus program
and kernel proves with emitted proofs and no searching tactic on the main path, proof time is measured and not worse, and the
construct table is unchanged or better.

**V. The verified compiler by reflection (§1.12, D26).**  **The per-program check is measured (2026-10-30, `proved/KQR.v`):**
`sexp` (numbers, operations, tests, lets, reads of the memory, the recursive call on the counter's predecessor) and `denote_fun`
(the parameters bound first with `abs`, calls applied with `app`, so the meaning reduces to exactly the shape of the user's
`Fixpoint`); the kernel accepts `sum = denote_fun 2 ..` for a counted loop in 0.000 s, refuses a wrong syntax tree in 0.008 s,
and accepts a loop whose body is 300 `let`s with 300 memory reads in 0.001 s (proof) + 0.001 s (`Qed`) — the whole file in
0.67 s, 494 MB.  Against 35–54 s of search per test kernel today.  Still to measure as the syntax grows: records, writes of the
memory, calls of other functions, captures — each needs its meaning to reduce to the user's text exactly.
**The verified compiler for the first subset is proved (2026-10-30, `proved/KQR.v`):** `sexp` / `sexps` (mutual: numbers,
operations, tests, lets, reads of the memory, the recursive call on the counter's predecessor with its numbers), `denote_fun`,
`compile_fun` (A-normal form in continuation style; a test at the end is a branch, the recursive call at the end a loop
`Eloop`, elsewhere a call `Ecall`; the counter tested against 0 and its predecessor in a fresh variable, as the translator does
it today) and **`compile_fun_ok`: for every well-formed tree, every counter below `wB` and every arguments, the KQL function
computes `denote_fun`** — proved once by induction on the counter, over a mutual continuation lemma (`cexp_all`) and the tail
lemma (`ctail_ok`); its assumptions are Rocq's primitive integers and the kit memory's declared operations only (no memory law is
needed for reads; no admit).  End to end, a user's function gets its KQL statement with no tactic search: `sum_ok` (the counted
loop) by `change` + `exact (compile_fun_ok ..)` in 0.001 s, `long_ok` (300 lets and reads) in 0.003 s.  **`reify` is built (2026-10-30, `proved/KQRReify.v`):** it reads the
user's quoted `Fixpoint f (n : nat) (x1 .. xk : int) (s : mem) : int := match n with O => .. | S m => .. end` and gives
`(k, e0, e1)`, or `None` outside the subset; it is independent of the old translator.  End to end from the text: the trees it
gives for `sum` and the 300-step loop are the hand-written ones (checked by `eq_refl`), and the per-program theorems
(`sum_ok_r`, `long_ok_r`: `compile_fun_ok` at the reified tree, the kernel checking that the tree means the function) take
0.003 s; assumptions the same base.  **The code is the same as today's:** for `sum`, the KQL of `compile_fun` and the old
translator's `sum_kqm` are the same instructions in the same order (`Eif Ceq` on the counter, `Eop Bsub`, `Eop Badd`, `Ekld`,
`Eop Badd`, `Eloop`), only the temporaries numbered from 4 instead of 5 — so the C is the same code, and the existing printer
(`KQLPrint.pstr` of `KQMTop.tr_kit_program`) prints it from the reflect route's program unchanged.  Next: a `kitc.py` path
for programs in the subset (quote, reify, compile, the per-program lemma by `exact`, the C; no walk), then the constructs of
the table
(writes of the memory, records, calls of other functions, booleans, captures, ...), each an `sexp` node, a `denote` case, a
`compile` case and its proof case.  (1) The spike: `S` for numbers, tests, `let`, calls, recursion on a
counter; `denote`; `compile` proved for it (`compile s = Some k -> k computes denote s`); `reify` for it; the per-program check
`denote s = f` measured against the walk on the counted loops of the examples and a few corpus programs.  Continue only if the
check is fast and reliable.  (2) Growth, construct by construct from the construct table: `S` node, `denote` case, `compile` case,
proof case; programs outside `S` keep the fallback (translator + walk).  Accepted when every example, corpus program and kernel
compiles through `compile` with only the conversion check, the trusted base is unchanged (`Print Assumptions`), the check's time
is measured, and the construct table is unchanged or better; then the walk is retired.

---

## §13. HOW TO WORK ON IT

### 13.1 Environment and commands

Everything runs in the repository's CertiRocq image (Rocq 9 with MetaRocq, CompCert 3.17, clang), in the repository directory
(`setup.sh`, `images.sh` build it).

```
bash proved/make.sh                     # every proof of the route, "core-ok" at the end (ASSUME=1: print the assumptions)
python3 proved/kitc.py NAME ...         # translate, prove each function, print the C, build bin/P_NAME
python3 proved/kitc.py --emit-first NAME  # the same, with the C and the binary first and the proofs behind
python3 proved/kitc.py --no-proof --no-build NAME   # the translation alone: what is read, what is refused
bash proved/examples.sh                 # every proved/examples/*.body: proved, built, answer = NAME.expect
bash proved/corpus.sh [times]           # every program of hand.tsv; "times" also times each next to the kit's build
bash hw/spec.sh                         # the laws, the model, the demos, the library theorems rest on the laws alone
bash hw/check.sh                        # the kernels under QEMU's processor and under KVM, with their controls
bash hw/build_proved.sh NAME            # one kernel through the proved route; hw/run.sh NAME_p boots it
bash proved/matrix/run.sh [OUT]         # the construct table (PATT=a+b: some cells; PJ: cells at a time; MD=1: write MATRIX.md)
python3 proved/matrix/gen.py OUT        # only the table's programs (run.sh calls it)
python3 proved/matrix/classify.py RESULTS --md proved/matrix/MATRIX.md   # classify saved results again (run.sh calls it)
python3 tools/mkloopspec.py > proved/KQLoopSpec.v
bash all.sh                             # everything from an empty directory (the kit route's gates too)
```

Which machine the heavy runs go to, its container names and its free-disk guard are kept in the session's local notes, never in
this public file; the rules of §13.3 hold wherever the runs go.

### 13.2 What landing a change requires

- `proved/make.sh` ends with `core-ok`;
- `proved/examples.sh`: every example gives its expected answer;
- `proved/corpus.sh`: 36 of 36 proved, built and equal to the C++ answers;
- `hw/spec.sh` passes;
- when the translator or the walk changed: the kernels (`hw/build_proved.sh` for the five, or `hw/check.sh`) and the full
  construct table;
- for a release: the same with `KQ_MONO=1` (no cache).

### 13.3 Machine rules

- Every container gets a memory cap (8 GB is enough for everything here) and `--ulimit core=0`; never `ulimit -v` inside it
  (§11, F24).
- One heavy job per machine at a time: concurrent runs share the tree and its generated files and clash.
- Check free disk space before a long run; clean only the files this work created.
- Timings on one pinned core, counters on the host, never mixed across machines.

### 13.4 Procedures

**Close a construct-table gap:** §3.6.

**Add a library with theorems:** the text between `(* NAME-BEGIN *)` / `(* NAME-END *)` markers in `lib/Name.v`; its
trigger prefix in the tuple of `kitc.py` (and `compile.sh` for the kit route); its theorems in `lib/NameSpec.v` (or under
`proved/` if they need the translator's libraries, then in `proved/make.sh` after their dependencies); `hw/spec.sh` compiles
the files and, for theorems that must rest on the laws alone, checks their assumptions.

**Add a machine operation:** the primitive in `KQRun.v`; its law in `KQSpec.v` and the law proved for the model in
`KQModel.v`; its entry in the translator's operation table (`hw_table` / `hwf_table` in `KQMTrans.v`) and its meaning in
`KQMSem.v` (`hw_sem` / `hwf_sem`); its C body in `hw/kq_hw.h`.  Existing programs must give byte-identical C.

**Add an example:** `proved/examples/NAME.body`, `.expect` (the answer computed apart from Rocq), and `.mem` / `.args` when it
needs its own memory or arguments.

### 13.5 Debugging recipes

- **The refusal of a translation** is printed by `MetaRocq Run` in `proved/gen/NAME_t.v`'s output: `KQM: refused: FUNCTION: reason`.
- **Where a proof stops:** in `proved/gen/NAME_u_F.v`, replace `kqm_auto. Qed.` by `hnf; intros; kqm_enter; kqm_walk. Show. Abort.`
  and compile it: the goal the walk could not continue on is printed.
- **Where proof time goes:** `Set Ltac Profiling.` before the lemma, `Show Ltac Profile.` after; `KQ_TIMES=1` for each function's
  time; `Time` on single steps with `Set Default Timeout N`; `/usr/bin/time -f "%es %MKB"` for the memory of a `coqc` run.
- **What a theorem rests on:** `Print Assumptions NAME` (compile the file first; filter for names outside Rocq's integers).
- **A section theorem's arguments:** `About NAME` after the section is closed.

### 13.6 Starting a session

1. Read "READ THIS FIRST", §0 (all of it, §0.9 included), §10 and §12.  Do not re-derive anything in §10 or §11.
2. Check the tree: `git status`, `git log` against §14 (what is pushed, what is local), and that the image builds `proved/make.sh`
   to `core-ok`.
3. Pick the first open item in §12's order unless the owner names another; for a gap, start from its cells in `MATRIX.md`.
4. Before changing the translator or the walk, run the cells you expect to change, so the before/after is measured.

### 13.7 Definition of done (for any item)

- The construction exists (translator rule, proof, library, operation) — not a description of it.
- Its cells of the table are `ok`, or pinned by design with a control; the full table is re-run when the translator changed.
- The gate of §13.2 passed on the final tree, and its numbers are the ones reported.
- This file is updated: §3.4/§3.5 numbers, the item in §12, any finding in §11, any decision in §10, the commit in §14.
- Committed with the owner as author (D19).  Pushed only when the owner says.

### 13.8 What a fresh session gets wrong (and the correct move)

| Tempting move | Why it is wrong | Correct move |
|---|---|---|
| fix the one program that was refused | finds only what was written; leaves the rest of the family | find the construct, fix it for every place and type, re-run the table (§3) |
| add a condition to the translator so a proof goes through | an unjustified check is an over-rejection (rule 2') | prove the general case, or leave the cell a gap |
| write "X is not supported" in a README and call the item done | a limit written down is not closed | build it, or keep it open in §12 |
| ask the user to write the code differently (parameter order, a wrapper, a budget) | the goal is ordinary Rocq | make the translator accept the natural form (D22) |
| guess a fuel or a timeout to make a loop or proof pass | a guessed budget gives silent wrong answers | the measure as the budget (§4); a timeout only as a limit on proof search |
| an optimization that helps one benchmark | unstable, hides costs | a general pass, proved once, measured against C written the same way (§6.4) |
| port a processor family in C or assembly | hardcoding in another file | generic primitives; the architecture in Rocq (§9.1) |
| add a scheduler, allocator policy or driver to the toolchain | not part of freestanding C (D6) | write it as a user program or a library on the primitives |
| treat `Z` or `nat` arithmetic as `int` | changes the meaning | fixed-width numbers; `Z` only with a proved range, if ever (D3) |
| report "verified" from a cached run, or from part of the gate | the cache can skip; part of a gate is not the gate | the full gate on the final tree; `KQ_MONO=1` for a release |
| edit `proved/KQLoopSpec.v` by hand | it is generated | change `tools/mkloopspec.py` and regenerate |
| change a tactic library and test a file that imports it without recompiling | the old library runs | recompile in dependency order first (§11, F22) |
| run two heavy jobs on one machine, or a container without a memory cap | clashes, out-of-memory dumps that fill a disk | one heavy job, capped, `core=0` (§13.3) |
| lower a safety threshold (disk guard, timeout) quietly | the owner relies on it | say so, with the reason, in the report |
| put host names, addresses, user names or local paths in the repository | it is public | keep them in local notes only |
| call a refusal "by design" because of the value's type (`option`, a list, a function) | type is not the cause; size and lifetime are (§0.5, F35) | by design only with a pin that shows the cause and a control (§3.6) |
| build an easier substitute for what the owner asked, and record the substitute as the decision | the owner's request silently leaves the plan (F36) | build the substitute if it is a real step, say plainly that it is not what was asked, and keep the request open in §12 |
| call the route "a verified compiler" before §12.V is done, or say the reifier is verified | until `compile` covers a program, that program's theorem comes from the walk; the reifier is never verified, its output is checked (`denote s = f`) | "proved end to end for every compiled program"; after §12.V: "`compile` is a verified compiler for `S`; a program is reified and checked by conversion" |
| verify the translator against MetaRocq's semantics of Rocq | that semantics has no rule for primitive operations (F38) and adds trust | reflection over our own syntax (§1.12) |
| take a settled decision of §10 as covering a case its reason does not cover | the reason is the decision; the wording is only its record | apply the reason; if the wording and the reason disagree, fix the wording and say so in the report |

### 13.9 When to stop and ask the owner

Pushing; deleting anything that is not this work's own output; changing a settled decision of §10; adding an assumption to the
trusted base; anything touching the owner's other work or machines beyond this work's own containers and files; and any choice
between two designs that §0.9 does not order.  Everything else — design within §0.9, building, measuring, recording — goes ahead.

### 13.10 Reporting

State what ran and what it gave (the gate lines with their numbers), what did not run and why, and what is unverified.  A
number that was estimated is called an estimate.  A failure is reported with its output.  A change that turned out wrong is
recorded in §11 rather than silently reverted.

---

## §14. COMMIT LEDGER (newest first)

Pushed to the public repository up to `0beefec` (2026-10-30); `git log --oneline origin/main..HEAD` lists what is local.

| Commit | What |
|---|---|
| (this commit) | `proved/KQR.v` + `KQRReify.v` step 3: memory writes (`smem`, `cmem_ok`, `ctailm_ok`, the memory cases of `compile_f_ok`; the reifier reads memory bodies, linearity by dead memories); F46 |
| `a8206b2` | `proved/KQRReify.v`: programs (`reach`, plain functions, calls); per-program theorems from the text |
| `08304f4` | `proved/KQR.v` step 1: signatures, plain functions, calls; the modular theorem `compile_f_ok` |
| `52b0012` | `proved/KQRReify.v`: the reifier (the user's text to the syntax); the per-program theorem from the text in 0.003 s |
| `9cdbf38` | `proved/KQR.v`: the verified compiler by reflection for the first subset — `compile_fun_ok` proved once; per-program statements by computation in milliseconds |
| `0beefec` | `proved/KQR.v`: the per-program check measured (meaning = function in about a millisecond) |
| `741373f` | `kitc.py --emit-first`, `--no-proof` |
| `b8ad7c9` | D27, the commuting memory law approved |
| `30d0199` | booleans (results, parameters, made by `if`/`match`), values built and taken apart in place (`knorm`), a number and a memory as a result, records chosen by a test; 5 new table cells; the table at 759 / 20 of 780 |
| `685b6ff` … `2e2be49` | the architecture decisions: §1.11 (CakeML), §1.12 (the verified compiler by reflection, D26), the MetaRocq route and its two problems |
| `485465e` … `f0f9f26` | this file, its additions and corrections; `proved/matrix/run.sh`; the five design cells reclassified as gaps (41) |
| `7e41ee8` | the construct table re-run: 775 cells, 733 proved, 5 by design, 36 gaps |
| `b014f1d` | measure recursion (`wfix*`): the budget is the measure; equation and induction proved; termination tactic; `tri_closed`, `gcd_correct`; functions with tests compared as terms; budgets of constants |
| `39b81ee` | `loop_two` and `loop_two_ends` |
| `4fa10f4` | closures: a function given to a template may name the caller's variables; `loop_up`, `loop_up_m`, `loop_find` |
| `04ba834` | a `match` on a counter anywhere; local functions; `classify.py` |
| `95d2e8c` | GOAL: writing it is as easy as ordinary Rocq; the construct table's generator |
| `3fc5c62` | the slab's invariant kept by init, set, free, take |
| `3184a86` | GOAL: scheduler, process tables, memory manager, drivers, filesystem are user programs |
| `76e777a` | fewer whole-goal passes per proof step |
| `7463962` | per-function proofs, in parallel, cached; two slow tactic steps made cheaper |
| `dca14f2` | views of one memory |
| `a361f7d` | named memories for read-modify-write chains |
| `1417a2c` | faster proofs of long straight-line code; helpers that write seen as writing |
| `f53a213` | growing blocks and the slab through the route; run-time budgets |
| `435f220` | 64-bit unsigned numbers |
| `c6216f7` | two processors with a lock; shared blocks only through atomics |
| `b22b690`, `4aef909` | bytes as one access; 8- and 16-bit cells |
| `d0a07b4` | recursive functions giving back two numbers |
| `2cb35c3` | mutual recursion |
| `9490bfa` | functions as arguments; a copy per function given |
| `26094de`, `a18ac3f`, `17e24d5` | kernels through the proved route; several programs per kernel; machine operations as one instruction |
| `08635d9` | signed division |
| `f334668`, `8fb4de1` | records and pairs; if-conversion with reads |
| `156d70c`, `a23ee76`, `e12b6fc` | GOAL: what C can do; what an optimization may be; what is proved and assumed |

---

## §15. GLOSSARY

| Term | Meaning |
|---|---|
| kit route | the repository's first route: Rocq → CertiRocq (with the kit's checker and passes) → C; fast, tested, not proved |
| proved route | `proved/`: Rocq → KQL (translator, untrusted) → Clight (generator, proved once) → C; this file's subject |
| KQL | the first-order language the translator targets (§1.2) |
| the kit's memory | the abstract `mem` with `rd`, `upd`, sizes, narrow blocks, growth, machine operations, and its laws (`real_laws`) |
| narrow block | a block of 4-byte cells, raw memory seen as bytes, halfwords, words, 64-bit cells |
| slot block | block 63, which carries the second result of a function with two results |
| counter, budget | a `nat` loop counter; held in KQL as one machine number (`ofn`); a budget is a counter's starting value (`kq_nat x`, capped at 2^60) |
| `Abud` | a KQL atom for a budget written as a number |
| `Esel` | a choice between two values taken with a conditional move |
| statement | per function: "the KQL function computes the Rocq function" (`f_kstmt`) |
| the walk | the proof of a statement, one KQL instruction per step (`kqm_walk`) |
| unit | one function's proof in its own file, with stubs for the functions before it |
| cache key | libraries + tactic setup + printed function, statement and everything it mentions |
| template, copy | a recursive function that takes functions; the KQL function made for one call's functions |
| capture | a variable of the caller named by a function given to a template; a parameter of the copy |
| construct table | one program per construct × place × type; each cell `ok`, `design`, or a `gap` |
| measure, domain | a number that falls at every recursive call; the arguments the termination argument covers |
| `wfix` | recursion with a measure, the measure plus one as the budget (§4.4) |
| `hw_law`, `hwf_law` | the hypotheses of the top theorem about the C bodies of the machine operations |
| `real_laws` | the one axiom: the record of the memory's laws, proved for a model |
| verified compiler | a compiler with one theorem: for every program, the output is correct (our generator) |
| proof-producing (certifying) translation | a translator that is not proved; each run produces a theorem about that program, checked by the kernel (our translator; CakeML's) |
| proof by reflection | a Rocq function (here `compile`) proved once, run on a syntax (`S`) the program is turned into; per program only the syntax's meaning is checked against the program by conversion (§1.12) |
| `S`, `denote`, `reify` | the syntax of the accepted fragment; its meaning as a Rocq function; the untrusted step from the user's Rocq function to `S` (§1.12) |
| proof built by construction | a proof assembled from one lemma per construct along the program's text, as CakeML's translator does — nothing searched (§1.11) |

---

## §16. RELATED DOCUMENTS

- `proved/GOAL.md` — the short statement of the goal (§0 contains it).
- `proved/README.md` — the proved route: steps, numbers, memory, what the translator reads, machine operations, kernels,
  several processors, what is trusted, the corpus table.
- `README.md` — the repository: the kit route, results, hardware, dynamic memory, the proved route, what is checked and trusted,
  limits.
- `WRITING-FAST-ROCQ.md` — the costs of each way of writing (to be split, §12.J).
- `proved/matrix/MATRIX.md` — the latest construct-table summary.
- CakeML (github.com/CakeML/cakeml): `translator/README.md` (the proof-producing translator, `Eval`), `pancake/README.md` (the
  C-like language compiled by CakeML's lower passes, its proof-producing decompiler) — the precedent for §1.11.
- In the KernelQ project: `docs/rocq-cost-shape-solution.md` (the cost-shape record: the word-RAM cost model, settled; the
  method of auditing by term former that §3 follows) and `docs/kernelq-pedagogy-goal.md` (why Rocq is the learning track; LS.30
  on Rocq computing, LS.31 on the roles of Coq, Clight, VST, RefinedC and CompCert).
