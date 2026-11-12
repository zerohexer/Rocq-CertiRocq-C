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

**COMPLETENESS IS STRICT (owner, 2026-11-02).**  A construct is done only in its general form — every place and type it can
appear in.  A step built narrower than its design ("only at the entry", "only in this order", "not inside an expression") is
**not done**: it is not recorded as done, and the next item does not start as if it were.  Every place a step leaves unread gets
a construct-table cell in the same commit, so the table shows it as a gap; "0 gaps" is a claim about the table's cells, never
about completeness while known unread places have no cell.  (`CLAUDE.md` in the repository says the same, for every session.)

**WHAT MAY BE ASSUMED IS STRICT TOO (owner, 2026-11-06).**  Everything that has a definition other than the machine is proved.  A CPU having
an instruction for something does not make it hardware.  `proved/TRUSTED.txt` lists what is assumed; a chain and a push stop on any difference
from it (`proved/check_trust.py`), and a change to it goes to the owner (§0.3, §13.9, D29, F66).  **Today the proof ends at Clight**: the
printer, clang, the loader and the driver are not proved (§12.H).  Step 65's five operations, `divs_min_neg1` and the copy, the fill and the compare of bytes are gone (steps 73, 74, 75, §12.T); what is left assumed is the machine's own, the memory's laws, what the loader gives.

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
   (`proved/KQR.v`, `KQRReify.v`): numbers, tests, lets, reads, calls, recursion on a counter, memory writes, counters as
   values (several counters, `S`/`O`, budgets, a match on a counter inside a body), booleans (tests made of `&&`, `||`,
   `negb`, boolean lets), choices between numbers as conditional moves, number functions that write the memory, cells of 4
   bytes, helpers written out where they are used, a `let` of a counter, chains of tail calls merged into one call,
   functions given to recursive functions (a copy per function given), loops that write and give a number, booleans and
   records as parameters (a record a value in the meaning, its fields in KQL), records given back (the fields after the first
   through the slot block), functions given that name the caller's variables, machine operations, bytes, 64-bit numbers
   (`u64`: record variables with their types, one instruction per operation), mutual recursion (a block as one function with
   a selector), functions giving back a boolean, values of any inductive type built in place and taken apart, a number and a memory given back, `option` / `sum` and their kind held as their tag and fields — each per-program step in milliseconds, long read-then-write bodies included on our fork of Rocq's kernel
   (D28, `rocq-fork/`); **it is `kitc.py`'s route since 2026-11-02 and the walk is retired** (§12.V step 29): **all 71 of the
   gate's programs**, the five test kernels included, and `lock` on two processors, and **776 of the construct table's 780
   cells** before the places left unread got cells; with them and the cells added since **3988 of 4134, 69 gaps, 76 by design** (and 1 program Rocq itself refuses) — a program the reifier does not read is refused with its
   reasons, no proof is searched; the translator and the walk only behind `kitc.py --walk`, the yardstick a program is timed
   against.  Next: the 20 gaps of the places §12.V's steps left unread, each as a construct of `S` in its general form
   (completeness is strict: `CLAUDE.md`), in the order the record of 2026-11-02 gives.
3. **The translator's own side conditions** (§3.7): all closed or with their cells: the counter at any position and the memory at any position since
   step 41, functions of any module and file since step 51, a second memory parameter since step 53.
4. **Rocq's own measure recursion** (`Program Fixpoint {measure ..}`, `Function`, `Equations`): what the owner asked for as
   loops "level 2".  `Program Fixpoint` is read since step 56, `Function` since step 57, `Equations` since step 60; `{wf R x}` on a relation of the user's is the gap left (§4.5, §12.P).
5. **The operations of freestanding C** (§2.1): `lib/CInt.v` and `uint64_t`'s `/`, `%` since step 88.
6. Compiling from an ordinary `.v` file with one command: since step 89 (§12.B); refusals that say what to write instead are left.
7. Freestanding: since step 90 (§9.5).
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

**Assumed (hardware level): only what has no definition except the machine.**  A store to a device register, a barrier, an
atomic against another processor, a control register write, a halt.  Each is a primitive with a stated law and an entry in the
trace.  The real behaviour of the hardware is checked by running on the device or an emulator (QEMU, KVM), not proved.  There is
no model of the CPU.

**The test: does it have a definition other than the machine?**  If Rocq can state what it computes, it is logic: it is written in
Rocq and proved.  A CPU having an instruction for it does not make it hardware: `clz`, the high half of a product, a division, what
a copy does to a memory are logic.  "Trusted" and "hardware" are different words: C written here that nobody proved is trusted, and
it is this work's to prove, not the hardware's.  About Rocq's own primitives nothing is assumed beyond Rocq's axioms and its kernel;
"the axioms only relate them" is no reason to assume anything, since relating them is enough to prove a definition equal.  Where
the axioms are silent no fact is added: a closed term is computed, a test in the program rules the case out, otherwise the program
is refused with that reason (§0.5).  Speed is no reason either: a faster form is a Rocq function or a case of the generator's proof,
measured.  The list of what is assumed is `proved/TRUSTED.txt` (§1.10, §13.9).

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
3. **Two versions of the memory both used, differing in cells whose number comes from the data** (`wp n a s + wp n b s`, `wp`
   writing a cell at each round of a recursion, at a moving index): the memory is linear, which is what lets a pure function be
   compiled to in-place updates; keeping both would be a copy of the memory, or a log of the writes as long as the data, made
   behind the programmer's back.  Two versions differing in cells fixed by the text (`let t := upd 0 a b s in .. t .. s ..`, a call
   that writes one cell named in its text) need neither: the old values of those cells are kept in variables and put back, as a
   C programmer writes it (F63).
4. **A constant with no body in Rocq's kernel**: an `Axiom`, a `Parameter`, a function behind a module's `:`.  This one has nothing to do
   with a runtime: Rocq itself cannot run such a constant and nothing says what it computes, so no theorem can say the C computes it
   (F65).  `<:` keeps a module's bodies; what only the hardware defines is named by a machine operation with its law (§1.8).
   The same reason covers a primitive where Rocq's axioms say nothing and the arguments are not known (`diveucl_21 a b c` with nothing
   showing `a < c`): nothing says what it computes there.  A literal is computed, a test in the text rules the case out, otherwise it
   is refused with that reason (§12.T).

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

1. **Does the trusted base stay the same?**  Nothing new is trusted: the translator stays unchecked-but-verified-per-program and
   the generator's theorem covers the change.  A new machine operation, a new C body, a new axiom is a new assumption, whatever comes
   with it: a law proved for the model shows the laws do not contradict each other and says nothing about the C.  It passes only
   §0.3's test, and then it is a decision for the owner, not a step (§13.9); `proved/check_trust.py` stops the chain and the push on
   a difference.  If a construct costs no proof work, find what is carrying it (F66).
2. **Is it natural and native?**  Would ordinary Rocq or Lean code look like this?  Then it must be accepted.  Does the change
   make the user write something they would not otherwise write (an order of parameters, a wrapper, a special name, a budget to
   guess)?  Then it is the wrong change, unless Rocq itself imposes it or a theorem needs it (D22).  The only refusals are the four
   of §0.5.
3. **Is it general?**  It applies to every program with that construct, not to the program in front of you.  It is found and
   tested by construct (§3), never by fixing the sample that failed.  An optimization removes a cost the translation adds to every
   operation or is a standard C pass, proved once (§0.7).
4. **Does it keep the C of existing programs?**  Byte-identical C for programs that do not use the change, or a measured reason
   why not, with the corpus timed.
5. **Is it closed by a construction, in its general form?**  A gap is closed when the cell is translated and proved; a boundary
   when it has a pinned cell and a control (§3.6).  Writing the limit into a README closes nothing.  A construct accepted only in
   some of its places is not closed: the places left get cells, and the step goes on until they are accepted (owner, 2026-11-02:
   completeness is strict, no narrower substitute is done).
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
| 7 | **Trust: only what has no definition except the machine** | `proved/check_trust.py --gate LOG`: the tree and `ASSUME=1 bash proved/make.sh` list what `proved/TRUSTED.txt` lists, with no line of the classes `remove` and `audit` left |
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
| Clight → assembly | clang (any C compiler) | not proved here (D30): the proof ends at Clight; a CompCert licence holder compiles the C with `ccomp` (`KQLBack.v` composes CompCert's pass theorems, outside the default build) |
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
and the signed remainder are tested first, so the C has no undefined behaviour.  Lemmas: `KQTArith.v`, `KQLSigned.v`.  What
Rocq's integer axioms leave open, the smallest number divided by -1, is no fact here: the instruction means `kq_divs`, whose
definition says it (step 74).

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
`hw_fence`, `hw_call`, `hw_run`, `hw_code_sync`, `kq_grow`, interrupt-take) are read like
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

`Print Assumptions` of every lemma of `KQMTop.v` (the generator's `kit_function_correct` among them), `KQR.v` (the verified
compiler's `compile_f_ok`), `KQRWf.v` and `KQPrim.v`, from a file that imports nothing, so that each name is the one constant it
names (`ASSUME=1 proved/make.sh`, since step 92, F76): Rocq's 63-bit integer axioms; the kit's memory primitives `KQRun.rd` / `upd`
/ `kq_size` / `mem` and `KQSpec.real_laws`; the machine's operations; classical axioms CompCert uses.  No admits.
Outside the proofs: the loader that fills the tables, the driver in `kitc.py`, the printer, clang, and the C bodies of the
machine operations with the laws the theorem assumes of them.  Each program's own end theorem, `{name}_end` (step 96: the entry's
theorem said of the Clight the generator makes), is printed the same way by the gate's scripts and compared too: a program's proofs can
rest on more than the route's lemmas, Rocq's axioms of the primitives the reader writes as their definitions (F80).

**So the proof ends at Clight**: the theorem says the Clight the generator makes computes the Rocq function, under the list below.
Printing that Clight as C, compiling the C, filling the tables and starting it are not proved (§12.H).  Say "proved to Clight, under
`proved/TRUSTED.txt`"; "verified Rocq to C" is not true past that.

**`proved/TRUSTED.txt` is the list**: every axiom of the proofs, every operation of `hwop` and `hwfop`, every C body of `hw/kq_hw.h`,
every name the gate's `Print Assumptions` gives, each with a class: `hw` (only the machine defines it), `mem` (the abstract memory, its
laws proved for a model), `env` (what the program is given by the loader and the driver), `rocq` (a fact Rocq's own axioms leave open),
`audit` (not plainly hardware, to be checked), `remove` (logic, to be proved and taken off).  `proved/check_trust.py` compares it with
the tree and, with `--gate`, with the gate's log: a difference exits 1, and the chains and the repository's push hook stop.  A cell of
the construct table that rests on an operation marked `remove` or `audit` is not simply "proved" (§12.T).

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
  paths green — until the table's cells all go through `compile`; then the walk is retired.  *(Retired 2026-11-02, step 29:
  every proved cell goes through `compile`; the translator and the walk are kept behind `kitc.py --walk` as the yardstick.)*
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
proof, its C, and (for a machine operation, which only what passes §0.3's test may be) its law with the law proved for the model.  So "the primitives are complete" is a
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
| `uint64_t` `/ %`, signed 64-bit (`int64_t`) arithmetic, the high half of a 64×64 product | `W_divu`, `W_modu` of `Ew64`, one instruction, a test at 0 (`KQRun.v` `u64_divu`, `u64_modu`); `lib/CInt.v`: `u64_mulhi`, `i64_*`, over `Ew64` | proved, with what each computes (`lib/CIntSpec.v`, step 88) |
| `int8/16/32_t`, `uint8/16/32_t` arithmetic with C's wrap-around | `lib/CInt.v`: `u8_add` .. `i32_shr`, over `int`; a signed overflow wraps | proved, with what each computes (step 88) |
| loads and stores of 8, 16, 32, 64 bits | `Ekld8`/`Ekst8`, `rd16`/`upd16` (two bytes), `Ekld32`/`Ekst32`, `Ekld`/`Ekst`, views | proved |
| `volatile`, atomics, fences | `Ehw` machine operations | laws, C bodies assumed |
| `memcpy`, `memset`, `memcmp` | `hw_copy`, `hw_fill`, `hw_cmp`: loops over the byte loads and stores, ordinary functions of the kit (step 75) | proved |
| `__builtin_popcount`, `clz`, `ctz`, `bswap`, rotate | `lib/CInt.v`: `popcount32`, `clz32`, `ctz32`, `bswap32`, `rotl32` and the 64-bit ones, Rocq functions (`head0`, `tail0`: step 73) | proved, with what each computes (step 88); a single instruction only as a case of the generator's proof, measured; never as a machine operation (F66) |
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
| at most **one memory** per function | `mk_info` (`restmem && capmem` refused), the walk | partly: one memory is the linearity that makes in-place update correct; two *different* memory parameters both live would alias the one global memory | done (step 53): two parameters holding the same memory read as one by a wrapper, a parameter never read and handed on as it is by a theorem for each of its values, both live by design with pin and control; the forms left are gaps with cells (`A_par_mem2_*`) |
| a function to translate is in the **program's own file** (or the kit) | `is_fn`, `reach`: `in_prog` since step 51 | no: a function of another file is quoted the same way | done (step 51): a constant of any file that is not a library's, of a nested module, of a functor's instance; a file the program requires beside it is compiled first |
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
{measure ..}` (the `Acc`/`Fix_F` form) is read since step 56 (§4.5).**

### 4.5 Reading Rocq's own measure recursion (the owner's "level 2")

**State (2026-11-04).**  `Program Fixpoint {measure ..}` is read (§12.V, step 56), by a simpler way than the plan below: no
`fix_sub_eq`, no measure computed at run time, no cap in the domain of the theorem: one lemma, `fix_sub_budget`, from `Fix_sub` to a
fuel function, closed under `Print Assumptions`.  `Function` is read (step 57): its plain functional, one tactic over `f_ind`, the measure read back
from `f_tcc`.  Any measure with a bound is read (step 58), a budget in phases above a counter's range, so `wfix_mem`'s binary search is
written with its natural measure.  `Equations` is read (step 60): `FixWf` over its functional, its clauses written out.  `{wf R x}` on a
relation of the user's has its cells and is a gap: no measure to put a budget above.

**What the owner asked for.**  Asked for loops "natively, without workaround", two levels were offered (2026-10-29): level 1, a
loop whose budget is a measure; level 2, Rocq's own `Program Fixpoint {measure ..}` / `Function`.  The owner answered "make it
level 2, stable, perfect and good".  What was built is `wfix` (§4.4): the same equation as Rocq's `Fix_eq` and an induction
principle, with no budget to guess — but a library form the user must learn, not Rocq's own spelling, and it was then recorded
as if the owner's form were optional (F36).  Under D22 the spelling is the point: a Rocq user writes `Program Fixpoint`,
`Function` or `Equations`, and that text must compile.  `wfix` stays (it is ordinary Rocq, it is proved, and it is the engine
below); reading Rocq's own forms is open work (§12.P), not an option.

**How (the plan as it was written before step 56, kept for its reasoning; §12.V step 56 has what was built).**  `Program Fixpoint f (x : A) {measure (m x)} : B := body` is elaborated to `Fix_sub` over the
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

The generated C is built three ways: hosted with the kit's support code (tests), bare with `hw/kq_bare.c` (kernels), and since step 90 on its own: `sup/free/` holds all it needs, no hosted header and no libc, and `proved/examples.sh` builds every example that way, runs it and compares its answer.  `kq_grow` has a freestanding body in `sup/free/kq_mem.c` and in `hw/kq_bare.c`, over free memory the start hands it or a fixed room; it is C, on `proved/TRUSTED.txt` with the loader and the driver (§12.H).

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
| D12 | **Loops: the measure is the exact budget, never a guessed fuel; the equation and the induction principle are proved.**  `wfix` is the library form (built); Rocq's own `Program Fixpoint` (step 56), `Function` (step 57) and `Equations` (step 60) are read | a guessed fuel gives silent wrong answers; the owner asked for Rocq's own form ("level 2", 2026-10-29), and D22 makes its spelling the point.  Corrected 2026-10-30: this row first called reading `Program Fixpoint` optional, which recorded the substitute as the decision (F36) |
| D13 | **The only acceptance rules are §0.5.  The flat style of `WRITING-FAST-ROCQ.md` is performance advice, like keeping a C loop variable in a register** | a rule nobody can discover is an over-rejection; costs are the user's to choose |
| D14 | **One memory per function, linear** | lets a pure function be compiled to in-place updates and is what C programs do anyway |
| D15 | **Records and pairs are never built; they are their fields** | no allocation, and the C is what a programmer writes for a struct passed by value |
| D16 | **A function with two results returns the first and puts the second into the slot block, saved and restored** | no allocation; the statement states it exactly |
| D17 | **If-conversion at value choices (reads allowed); call-chain merges with plain arithmetic only** | measured both ways (§6.3) |
| D18 | **Budgets are capped at 2^60** | a counter always has room to count a few more, and no proof works a budget out; consequence: a measure must be below 2^60.  For `wfix`, the library form; Rocq's own spellings since step 58 take any measure with a bound, written budgets summed up to 2^62 and phases above |
| D19 | **Commits: authored by the owner only, no co-author trailer, no narration; push only when the owner says; no host details, addresses, user names or local paths in the repository** | owner's standing rules; the repository is public |
| D20 | **Proper over fast**: the straightforward, correct construction is preferred to a quick one; decisions are judged by this file's criteria | owner's standing preference (also in the cost-shape work) |
| D21 | **A gap is closed by a construction, never by stating its limit; a boundary needs a pin and a control; no translator check without a theorem that needs it** | §3.6; learned in the cost-shape work, where each was the cause of a re-opened item |
| D22 | **Natural and native over conventions of our own.**  A convention stays only if Rocq itself imposes it (structural recursion, linear use of a value in a pure function's in-place translation) or a theorem needs it; anything Lean or Rocq would accept as ordinary code is accepted (a counter at any position, the memory at any position, functions from other files, any captured kind) | owner, 2026-10-30: "own convention is nice, but I prefer natural native" |
| D23 | **A refusal reads like a type error, not a syntax error**: it names the construct, the place in the user's text, the reason (one of §0.5, or "not yet translated" for a gap), and what to write instead | the user writes ordinary Rocq; a refusal is about meaning (it needs a runtime), never about spelling |
| D24 | **The operation set is finite and is completed against freestanding C's operations (§2.1); full higher-order function values are not needed** | the generator's theorem is one case per operation; C has no closures, and its function pointers are an explicit table |
| D25 | **The top half moves to proofs built by construction, the CakeML way: the translator emits each piece of KQL with the lemma that justifies it (one lemma per construct), so no proof is searched for.  The hybrid stays (per-program proofs on top, one proved generator below); the translator itself is not proved (no single "for every program" theorem).  Spike first, then convert construct by construct, then the completeness theorem; release builds through `ccomp`**  *(Its plan — converting the walk — was superseded the same day by D26.)* | CakeML, the strongest project of this kind, uses this split with a proof-producing translator on top (§1.11); it removes proof-search failures and most proof time and makes each new construct one rule plus one lemma, at a fraction of the cost of a verified translator, which would mean proving the translator against MetaRocq's semantics with primitive integers for months (owner, 2026-10-30: "go ahead, record this decision with every context") |
| D27 | **The memory law "writes to two different cells commute" may be added to `KQSpec.laws`** (proved for the model in `KQModel.v`, with functional extensionality as the other laws are), when the construct that needs it is built — results of more than two numbers through the slot block | it holds of every memory; it does not follow from the two existing equations (F43); one more statement assumed of the real memory, so the owner decided (2026-10-30: "go ahead") |
| D28 | **Our own fork of Rocq carries the conversion memo** (rocq-prover/rocq#22309, backported to 9.1.1 as `rocq-fork/conv-memo-v9.1.1.patch`), not contributed upstream and not waited for.  It is a change to Rocq's kernel, so to the trusted base; the owner asked for it to be made sound and proved correct (§12.R) | measured: it removes F46 (a read-then-write chain of 100 steps checked in 0.003 s, 30 steps were over 120 s) with nothing else changed.  It is a **general** change (§0.7, §0.9 question 3), not a rule for some programs: memoization of the kernel's comparison within one conversion check, so that two shared subterms are compared once rather than once per path to them — the standard way to compare graphs with sharing, and what Lean's kernel does (F46: 13 ms at 1000 steps); it is not a store of results across runs (the table lives for one check and is dropped), and it is keyed to no construct or program.  Owner, 2026-10-31: "no need to patch upstream to them, we do our own upstream fork".  **Weighed against the alternative and chosen over it:** `Kq Definition` (the compiled function *defined as* `denote s` by our command, as `Program Definition` / `Equations` define theirs) adds nothing to the trusted base and needs no per-program check at all, but users write the command instead of `Definition`, the kernel checks "the C computes what you typed" only where the check is cheap, and users' own proofs that unfold a long read-then-write chain stay exponential; the fork keeps plain `Definition`, checks fidelity always in linear time and makes those proofs fast too, at the price of a patch under every proof.  The owner: "I will choose fork regardless unverified OCaml since it follows same as MetaRocq" — Rocq's kernel is unverified OCaml, and the project already relies on MetaRocq's OCaml quote, so an argued, model-proved, tested patch is the same class of trust |
| D29 | **Only what has no definition except the machine is assumed.  About Rocq's primitives: Rocq's axioms and kernel and nothing more; where they are silent a closed term is computed, a test in the text rules the case out, otherwise a refusal with that reason.  `proved/TRUSTED.txt` is the list; a change to it is the owner's; a chain and a push stop on a difference** | owner, 2026-11-06: "I want everything verified"; "write them as ordinary Rocq functions and prove each equal to the primitive".  The goal already said so; step 65 went around it (F66), so the check is a program now, not a sentence.  **The floor, the owner's (2026-11-07):** Rocq's kernel and axioms, our fork's memo among them; the hardware, that it follows its manuals, since being right on every model of every ISA is impossible; the memory's laws and each architecture's boot and entry stubs.  Above that floor the aim is correctness on any ISA.  Past Clight is not the floor: the printer, clang, the loader and the driver are software, open at §12.H |
| D30 | **The proof ends at Clight.  The C text is compiled by any C compiler; one who holds a CompCert licence compiles it with `ccomp`, and CompCert's theorem then carries it from its C to assembly.  CompCert's passes are not part of this work** | owner, 2026-11-08: "we are verified till Clight / C semantics, equivalence till assembly is CompCert, people who own CompCert can change our clang / GCC to CompCert".  What this work uses of CompCert is the definition of Clight (`Clight.v`, `Cop.v`, `Ctypes.v`, `common/`, `lib/`), dual-licensed under the LGPL; the passes are under a non-commercial licence.  A route through the passes, proved (`release_correct`) and run on all 59 examples on 2026-11-08, was set aside for that reason; the tree at Clight and the C text are still joined by the printer, which is checked, not proved |
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
| F49 | Moving a program from the translator to the verified compiler changes its C, and the gate checks answers, not speed: two corpus programs became 1.45x slower in step 4 (`CF295B`, `CF295Bv2`: a minimum written into a cell, a conditional move in the translator's C, a jump in `compile`'s), unseen by the gate (2026-10-31) | if-conversion in `compile` (§12.V), timed again: within the spread; a program moved to the verified path is timed against the translator's build before the move is reported |
| F50 | A call given a written counter (`dfs 20 ..`) made the per-program check run out of memory: comparing the function with its tree's meaning, the kernel unfolded the user's function first, and a function applied to a written counter is worked out round by round (`tw 20`, two calls a round: 4.7 s, 1.2 GB); the compiler's meaning functions set to unfold first did not help (2026-10-31, `CF813F`) | `kitc.py` sets the program's functions to be unfolded last (`Strategy opaque`) in each theorem file — the order only; `tw 20` 0.002 s, pinned in `KQR.v` |
| F51 | The verified compiler's C for `CF868F` was 1.48x slower than the translator's: two calls of the function itself at the end of a test were a jump (the translator merges them into one call with chosen arguments), and with that fixed still 1.22x: temporaries reused across the arms of a test (the same KQL with every variable bound once ran at the translator's speed; 85 register moves against 67 in the loop) (2026-10-31) | `compile` merges such calls (equal arguments once) and numbers every variable once (`after`); all 16 programs on the verified path timed within the spread |
| F52 | Moving `CF453B` to the verified compiler made it 1.34x slower: a choice on `a && b` between two numbers was compiled as the boolean's value (moves to 1 / 0 and a `land`) and one move, where the translator chooses on the parts (two moves); measured apart on variants of the C (2026-11-01) | `compile`'s `csel` (choices on the parts), its lemma in `cexp_all`; what is left (1.11x) is `zabs` as a conditional move against the translator's jump, which comes from its `choice_ok` not looking through `Uint63.opp` — kept, the general rule (D17) |
| F53 | Moving `CF1100F` to the verified compiler made it 1.52x slower: a chain of three tests whose four ends call the loop itself on the same cells written was jumps, where the translator merges it into one call (its differing arguments and the written values chosen by conditional moves); step 6's merge took only two ends on the newest memory (2026-11-01) | `compile` merges any such chain (`mrg_e`, `mrg_m`, proved once; tests on comparisons or booleans; writes of the same cells), the two-call case giving the same code as before; `CF1100F` 109.1 / 108.5 ms |
| F54 | A copy of a recursive function for the functions it is given (step 10) set to be unfolded last, like the program's functions: comparing a caller's text (`wfix2_go (kq_nat (..)) F a b`) with the copy's call, the kernel unfolded the template on `kq_nat (..)` rather than the copy, and the check did not end in 10 minutes (2026-11-01, `wfix`) | the templates are unfolded last, the copies first (a copy is a definition that unfolds to its caller's text in one step) |
| F55 | A bound written as a `nat` literal (`1048576` in `nat`, in the first version of step 12 part 3's `wfr`) is elaborated as a computation (`Nat.of_num_uint ..`), not a numeral: `lia` treats it as an unknown and fails ("Cannot find witness") (2026-11-01) | bounds in `Z` (`Z.of_nat x <= 1048576`), as the rest of `KQR.v` writes them |
| F56 | The reasons tally after step 12 counted `loops` under "calls of writing functions inside expressions": the reason scan (`writes`) flags a number function whose text mentions a function that writes, and `loops`' `solve` does make a memory with `loop_up_m`; read part by part, that part is read and the blocker is a function given to a template that names the caller's variables (a closure), which the scan does not name (2026-11-01) | step 13 is captures; a program's blocker is confirmed by reading its parts apart before a step is chosen for it |
| F57 | The reifier's structural comparison `teq` (the copies' keys) had no case for a fixpoint: a local fixpoint's key was never equal to itself, so its copy was made and its call never found (2026-11-02) | the case added (step 31) — the hole F16 found in the translator's `term_same`, met again in the reifier |
| F58 | Step 31's first version made the kernels' build 2–3 s slower (the reifier's step on `HWP_kernel` 5.5 s against 2.5 s), the C unchanged: a helper of the program's file was scanned in full for a local fixpoint at every call, before the bounded scan that decides most helpers | the same test in the other order; back to step 30's times.  A test the reifier runs at every call goes cheapest first (as F45) |
| F59 | A fix made by hand in a file that an edit script regenerates is lost at the next regeneration: step 37's rewrite of `pot_ok` (made in the file, its proofs written against it) vanished when the core was made again from its script, and a proof term fixed by hand the same way (2026-11-03) | every fix goes into the script; the work files are made again from the scripts alone and compared byte for byte before a build counts |
| F60 | Three of the reifier's ways of reading a function — a template's copy, a local fixpoint's copy, a mutual block and its members — checked `wf_f` with the signature as read only: the call graph's bounds (step 34) and the smallest own bound (step 33) never reached them, and the copies' theorems took no bound at all (found by step 37's cells of a template and of a mutual block, 2026-11-03) | one function gives every way of reading its signature (`wf_sig`); the copies' theorems take any bound and weights |
| F61 | A written budget's largest value was `kq_nat`'s bound, 2^60, whatever was written: a mutual block's selector (given as a written number) counted 2^60 in a weighted sum, and the block's bound passed 2^62 (2026-11-03) | `cnat_max`: a written number in `kq_nat`'s range is its own largest value, in `cmax`, `cmaxv` and `clinf` |
| F62 | The reifier's step was timed in two trees whose directories differ in size: `coqc` scans every directory `-R` and `-Q` give it, and the working tree holds every cell's generated files and the cells themselves (234 MB against 101 MB), so a file that loads only MetaRocq takes 0.80 s there against 0.73 s.  The 0.04–0.08 s the records of steps 44 continued to 48 put on the libraries' loading (and on the reifier's tests) was this.  Timed in copies of both trees without those directories, step 44 continued's files against step 48's: `HWP_kernel` 2.50 / 2.52 s, `HWP_own` 1.93 / 1.95, `HWP_irqnow` 1.63 / 1.64 — the same.  The timing now makes those copies. |
| F63 | §0.5's third refusal took its example from a fixed difference: `let t := upd .. s in .. t .. s ..` differs from `s` in one cell, whose old value a variable keeps and puts back, as a C programmer does; `A_par_write_two` (step 47, one cell named in the callee's text) is the same.  Only two versions differing in cells whose number comes from the data need a copy (found by step 49's design, 2026-11-03) | §0.5's third refusal worded by the size of the difference, as values are (F35); the fixed side gets cells (gaps), a pin and a control show the side from the data (step 49) |
| F64 | `&&` and `||` are functions: under `vm_compute` both sides are evaluated, and a scan written `is_pm ty && pm_bare 100000 0 body` walked the whole body at every let, a fuel literal of 100000 built each time, quadratic on a long chain of lets.  The first version of step 48 continued's `has_pm_let` cost 27% on the kernels' reifier step (`HWP_kernel` 2.36 to 3.00 s), found by the timing before its commit (2026-11-04) | the test written with `if`, the cheap one first: back to 2.38 s.  The same as F58: a test the reifier runs often goes cheapest first, and only `if` makes that an order |
| F72 | A chain went on past a refusal: the gate's `== refused (must be none): 1` line was printed and nothing read it, and `examples.sh` said 48 of 48 with `monad_fix` refused, because it ran the binary an earlier run had left (step 77's first version, found reading the log before the record) | a chain stops on that line; `examples.sh` removes the binary before it compiles |
| F71 | A rule added to the proof tactic for one class took a cell that was read: step 76's `kq_convoy` on a variable left `A_l_convoy_b` unproved, and the count of proved cells, which rose by 39 where 40 were expected, was the only sign: no line of the gate says a cell was lost | the rule fixed (step 78); each landing now compares the table's results with the last one's, cell by cell, and says what was lost |
| F70 | The record table was built in three places, `rec_info` with the made functions that name a value's type and the reader's two without them: a syntax tree numbering its records by one table, its meaning read by the other.  Nothing wrong was accepted: the kernel's check `denote s = f` refused it (`A_v_callee_other_value`, two types of the same width, found at step 78) | one list for all three |
| F73 | `compile` writes what follows an operand in each arm of a test that cannot be a conditional move, so `k` of them in one expression are `2^k` copies, and `x mod p` is three arms: a matrix power modulo `p` was read, its check passed, and printing its C ran out of memory; nothing had measured the size of the C (found by the fifth probe, step 85) | step 86: above 1024 copies by a count from the text, such operands are functions.  A join point in KQL would need no function: §6.4 |
| F74 | The first `u64_divu`, a loop of 64 rounds in `lib/CInt.v` before it became an instruction, shifted the remainder and lost its top bit: wrong for a divisor above `2^63`.  It was read and its C proved equal to it: the verified compiler says the C computes the function, and nothing about whether the function is what its name says.  Writing the theorem against `Z` found it, at the case the invariant needed.  So a library of ours carries its theorems (`lib/CIntSpec.v`), and "proved" about a library names which of the two is meant |
| F75 | The printed C left-shifted negative numbers: `tagup` of a signed number.  Clight defines that, C does not, so the text clang read said less than the Clight the theorem is about.  No answer was wrong: clang's IR has no `nsw` on a signed left shift.  Undefined behaviour trapped found it on its first run, 4 of 59 examples.  Fixed in the generator with a cast, the assembly the same.  So a difference between Clight and the printed C is a real class, and the printer is not the place to fix one |
| F76 | The trust check compared printed names as text.  Each file prints an axiom by the shortest name valid in its own scope, so one axiom was listed under two spellings (14 lines), and a short name printed elsewhere could have been another constant and still matched; every line `name :` after the first `Axioms:` of `make.sh`'s whole output was taken as an assumption, `Check`'s outputs included (`eq_refl`, `int`); and the set came from three end theorems plus what files happened to print, so `KQRWf.kq_compares_def` (step 64), which a program using `compares` rests on, was never printed: `PrimInt63.compares` and `Sint63Axioms.compare_spec`, Rocq's own, were not on the list.  Found at step 92, when `lxor_spec` was printed short | `make.sh` prints what every lemma of `KQMTop.v`, `KQR.v`, `KQRWf.v`, `KQPrim.v` rests on, from a file that imports nothing, between two markers, and the gate reads only that; `proved/TRUSTED.txt` lists that set, each axiom once by its full name (90): the short spellings, the artifacts and two primitive types only the untrusted reader's prints reached out, the two of `compares` in, with the owner's agreement that Rocq's own axioms are the floor (2026-11-09) |
| F77 | A written counter turned into a number, `Uint63.of_nat 100000`, took 97 s to check and `Uint63.of_nat 0xFFFFF` over 300 s, against 1.5 s for the rest of the program: the meaning says `ofn c`, the text `of_Z (Z.of_nat c)` (`Uint63.of_nat` is a notation for it), and the kernel opened the program's `of_Z` first, whose match worked `Z.of_nat` out on the number in unary.  It was there before step 94 for any written counter turned into a number, under a second at 4095 (found by step 94's cells) | the check files `kitc.py` writes unfold `ofn`, our abbreviation, first (`Strategy expand`): 3.4 s; the order only, as F50 |
| F78 | F77 was one case: a call of the library on written numbers in the program's text is opened by the kernel and worked out in unary whenever the meaning reaches the same call by another road.  `Nat.ltb n (Nat.pow 10 18)` did not end in 120 s with the meaning `cmpn Clt n (Nat.pow 10 18)`, nor with our meaning functions unfolded first; `Nat.land 1000000 65535` written out failed (found by step 95's cells) | the check files unfold our abbreviations first and every library function a node of `S` means last, so both sides meet at the call and its arguments are compared: 1.5 to 3.6 s, the gate's programs the same or faster, measured without the cache |
| F79 | A program's tree, `{name}_src`, was defined as a projection of the reader's whole result, whose type holds MetaRocq's `term`, so every program's theorem reached Rocq's primitive types of floats and strings, `PrimFloat.float` and `PrimString.string`, off the list, while nothing of the claim uses them: F76 met them only in the untrusted reader's prints (found by step 96, the first end theorem printed: 82 names, 2 off the list) | the tree is defined by its computed value, which is in `S` alone: 80 names, all on the list, the C the same |
| F80 | The list held what the route's lemmas rest on, and a program's own proofs rest on more: since step 64 the reader writes `PrimInt63.compare`, `addc`, `subc`, `addmuldiv`, `diveucl` as their definitions, and a program's proof of that rests on Rocq's axioms of them, `Uint63Axioms.*_def_spec`, never printed (found by step 96's gate, `prim_fix`) | the chain stopped and it went to the owner, who listed the ten, Rocq's own, the floor (2026-11-10); `check_trust.py --gate` asks every listed name to be used by the route or by a program, so the list stays exact both ways |
| F81 | A test of whether a rewrite changed a body, written `negb (teq 100000 new old)`, said changed for an unchanged long body: `teq` answers false once its fuel runs out, so `lib/CInt.v`'s `u64_top` got a rewritten row of its own and `cint_fix`'s C changed (found by step 98's C comparison) | decided by a scan for what the rewrite rewrites (`y_inner_has`); a comparison of terms with fuel is never the test of a change |
| F82 | A rewriting made general in its first version took cells read before: floating a match on any choice of constructors and opening any library definition that calls what the reader knows lost `A_l_dec_*` (step 68 reads `ge_dec` by its name), `A_m_b_find_bind` (a choice of pairs), `A_zc_r_chosen` (a choice of records of functions), seven cells, found by the cell-by-cell comparison of the table (F71) | the floating takes constructors without arguments of a type other than `bool`, the opening only what nothing knows by name; the seven read again before the step landed |
| F83 | A follow-up named by its first guess at the cause: step 101 recorded `A_zr_land_budget` as "step 83's reading of such a counter takes `S`, `+`, `*`", and step 102's first version built rules for the bit operations in that reading (`nc_has`, `nc_c`, `nc_tr`).  Probed on the cell, the cause was elsewhere: the function's bound was not kept, `nb_all` counting its constant 1023 against a cap of 1000 on its multiples and constant together; with the bound kept, the operation around the counter was read as any counter's, and the rules built gave the same C, byte for byte, on all 26 cells (2026-11-10) | before building for a refusal, probe the reading's records on the cell (the rows, the bounds' table, the site test) and name the cause from them; a rule that changes nothing in the C is compared with and without and dropped |
| F84 | A walk that runs a test at each node, the test a walk of its own, is quadratic on a written number: a `nat` the reader reads is unary, so 1023 is a chain of 1023 links, and step 83's walks (`nc_any`, `nc_sub`) ran their site test, `nc_has` comparing the kernel name of `nat` at each link, at every link: 2 s at 1023, three walks per function, `A_zr_land_budget` read in 18 s (2026-11-10) | a written number is a leaf of every such walk (`cnt_lit` at the top), which gives the same results where it holds no call; F77 is the same unary `nat` in the kernel's checks |
| F69 | `rewrite` compares up to unfolding, full, whatever `Strategy opaque` says: a lemma about a function whose body is one operation fires on that operation where the function is not written, and with a tactic turning the operation back the proof never ended | the lemma only where the function is in the goal (`match goal with |- context [F]`); a proof that looks for what to rewrite is stepped by hand when it times out |
| F68 | A program's own file (`Require`d by its text) was compiled again only when older than its source, not than the kit, so after `KQRun.v` changed the program failed once on Rocq's inconsistent assumptions and `kitc.py` wrote no C; the comparison showed `none`, at steps 65 and 73 | `build_user_files` counts the kit's `.vo` |
| F67 | A budget written as `S (S ..)` makes a conversion unroll the fixpoint: both sides reduce on the constructor, and with two branches in each round the comparison is exponential.  `reflexivity` on `(fix go ..) 63 c 0 a b = kq_d21_go 63 c 0 a b` did not end, nor `rewrite` of a term holding it, with the fixpoints' bodies identical | a written budget is `kq_nat 63`, opaque to a conversion (D18); a lemma about it is stated with the budget a variable, and the number put in with `exact` |
| F66 | **Step 65 was wrong, and is recorded, not reverted silently.**  It put `head0`, `tail0`, the high half of `mulc` and `diveucl_21` behind `hwf_law` as five machine operations whose C bodies were written here (`hw/kq_hw.h`), and landed it without the owner's decision, against §0.3, §0.9 and §13.9.  The reasoning was false: its design says Rocq's axioms "only relate these", "so no definition stands in for them", while relating them is enough to prove a definition equal.  Nothing stopped it: §0.3 worded what is assumed as "what an instruction does", and CPUs have `clz`; §0.9 read as if a machine operation with a law were no new assumption, though the law's model says nothing about the C; §2.1 and §12.O offered these as "single instructions" and §13.4 had a recipe with no proof of the body; the chain printed the difference in the trusted base and carried on, and the record wrote it up; the table counted those cells as proved.  It is F36's drift: an easier route written up as the design.  Also found while answering it: Rocq's kernel gives `head0 0 = tail0 0 = 63` and `diveucl_21 a b c = (0, 0)` when `c <= a` (`vm_compute`), which the axioms do not say.  The first follows from computing at 0, the second cannot be stated for variables | §0.3's test, D29, `proved/TRUSTED.txt`, `proved/check_trust.py` in the chains and in a push hook, §13.4, §13.8; the operations proved and removed by §12.T.  If a construct costs no proof work, find what is carrying it |
| F65 | §0.5 said three refusals, and a function behind a module's `:` is not one of them and not a gap: the kernel holds no body for it, Rocq cannot run it, and `denote s = f` has nothing to unfold.  The same for an `Axiom` and a `Parameter`.  Refused only with its short name until now, as if it were something not read.  And `kitc.py` looked for `kq_shared` in the body's own text alone, so a list of shared blocks in another file would have meant no check of them, silently (found by step 51's design, 2026-11-04) | a fourth refusal in §0.5 with its own reason, which names `<:`; `kq_shared` looked for wherever the program's text is, with the refusal of a plain access pinned from a module and from a file |
| F38 | MetaRocq's formal evaluation (`EWcbvEval.eval`, `PCUICWcbvEval`) has rules for primitive values only, none for primitive operations: `PrimInt63.add` has no body, `eval_delta` cannot fire, every program here is stuck in it | the verified compiler is built by reflection over our own syntax instead (D26, §1.12) (read in the image's MetaRocq sources, 2026-10-30) |
| F37 | CakeML's architecture is ours: a proof-producing translator from the logic's functions on top, one verified compiler below; Pancake is verified through a proof-producing decompiler.  The difference is that CakeML builds each proof by construction while ours searches | D25, §1.11 (read in the CakeML repository, 2026-10-30) |

---

## §12. THE WORK LEFT — the live, ordered plan

Each item: what, why, and how it is accepted.  The order is by how much of the goal it closes per unit of risk.

**The order to take them in** (the letters are names, not the order): **T** first, after the steps already built land (the assumptions step 65 added; owner, 2026-11-06).  Before that: the batch of **A** in progress lands (done,
`30d0199`) → **B**'s emit-then-prove part (done: `--emit-first`, `--no-proof`) → **V** (the verified compiler by reflection:
spike, then growth; D26 — done 2026-11-02, the walk retired, step 29) → the rest of **A**, **L**, **P** (the user's ordinary text refused), done as constructs of `S` →
**O** (operations C has) → the rest of **B** (compiling like `lean --c`) → **C** → **D** → **E** → **H** (with release builds
through `ccomp`) → **G** → **M** → **J**; **F**, **I** and **N** when their condition arises; **K** when the owner says.
**Q** is dropped (D26).

**T. What is assumed, down to what has no definition except the machine (owner, 2026-11-06; D29, F66).**
- ~~*`head0`, `tail0`, the high half of `mulc`, `diveucl_21`*~~ — **done, step 73**: ordinary Rocq functions in `KQRun.v`, proved equal to the primitive from Rocq's axioms alone (`proved/KQPrim.v`); for `diveucl_21` where `a < c`, and for `c <= a` Rocq's axioms say nothing: three written numbers are computed, a test in the text rules the case out, otherwise refused with that reason.
- ~~*`hw_copy`, `hw_fill`, `hw_cmp`*~~ — **done, step 75**: loops over the byte loads and stores in the kit, no operation of their own.  *`kq_grow`*: stays assumed, class `env`: the allocator under the memory's tables, with the loader and the driver (§12.H).
- ~~*`divs_min_neg1`*~~ — **done, step 74**: `Bdivs` means `kq_divs`, which says what the smallest number over -1 is by its definition; `/` needs no test, and a written-out `divs` where the text rules the case out.
- *The printer, clang, the loader, the driver*: §12.H, unless the owner wants them sooner.
- ~~*Each program's own end theorem in the gate*~~ (F76's follow-up, owner 2026-11-09) — **done, step 96**: `{name}_end`, the entry's
  theorem said of the Clight the generator makes (`KQREnd.callee_end`); what it rests on printed for every example, corpus program and
  kernel (`KQ_ENDAX=1`, set by the gate's scripts) and compared with the list by `check_trust.py --gate`.
Accepted when: no line of the classes `remove` and `audit` is left in `proved/TRUSTED.txt`, and §1.10 says so.  **Done on `4898663`**, the printer, clang, the loader and the driver left at §12.H.

**A. The construct-table gaps (20 cells, §3.5), then the by-design pins.**  The categories of §3.5: proof search for
pair-valued choices and nested counter tests (6); polymorphic and class-based helpers by specialization (4); arithmetic and
comparisons on counters (4); records of three numbers by recursion (3, with the commuting law, D27); an
`option` across a call or as a loop's state (2); a local `fix` with captures (1).  Under §12.V the remaining ones are done as
constructs of `S`.  Then the pins of §0.5's boundaries, each with its control (§3.5): cells added to `gen.py` and to
`DESIGN_CELLS` together.  Accepted when: the category's cells are `ok`, the full table is re-run and `MATRIX.md` updated, and
the gate (examples, corpus, kernels if the walk changed) passes.
- ~~*A local mutual fixpoint naming a variable of the function*~~ (found at step 108) — **done, step 110**: the block lifted under
  the variables it names alone, a match's with its constructor's argument types, each member the user's block under them; a Section's
  mutual `Fixpoint`, the same shape at the top level, read with it.  Step 108 lifts a closed one; a member naming a
  parameter or a let of the function wants it as a parameter of its own, given in each call of the block (lambda lifting), and a
  variable bound by a match has no type in the term to give that parameter.  Accepted when `A_zy_capture` and `A_zy_capture_let` are
  proved.
- *A local mutual fixpoint calling the fixpoint it stands in* (found at step 110): `match k with S j => (fix f .. lq j x .. with g ..
  for f) .. end` inside `Fixpoint lq`: the block names `lq`, a function, so its members would take a function as a parameter, a
  function given (step 10's copies) inside the very function given.  Accepted when `A_zz_in_fix_call` is proved.
- ~~*A mutual block giving back a counter*~~ (found at step 108, there before it) — **done at the top level and under parameters, step
  111**: the block's rows made together, one block of rows read as step 45 reads one, their statements proved by one mutual fixpoint;
  `A_zy_top_counter` proved; the local block is the follow-up below.  Step 82 reads a function giving back a counter as a row
  of one function; a block's members as one row with a selector, as step 45 makes them one function.  Accepted when `A_zy_counter`
  and `A_zy_top_counter` are proved.
- ~~*A local mutual block giving back a counter*~~ (found at step 111) — **done, step 112**: `y_all` lifts first, the rows made over the
  lifted members.  The reading lifts a local block (steps 108, 110), and the rows are
  made before it, on the program as written (`y_all`), so the block's members have none.  Lifting first, the members made, their rows
  over them.  Accepted when `A_zy_counter` is proved.
- *A mutual block's counter used as a counter* (found at step 111): `Nat.leb (ev n) 3`: step 83's bound is read and proved of single
  functions.  Accepted when `A_zx_as_counter` is proved.
- *A block of different types one of whose members gives back a counter* (found at step 111): step 62 reads such a block by writing
  the others into the one they call, and step 111's rows are of blocks whose members all give back counters.  Accepted when
  `A_zx_mixed` is proved.
- ~~*A counter a function gives back, used as a counter inside a bit operation*~~ (found at step 101) — **done, step 102**: the cause was
  the function's bound not kept (its constant counted with its multiples), not step 83's reading (F83); `A_zr_land_budget` proved.
- ~~*A bound's constant from 5000 on*~~ (found at step 102) — **done, step 105**: the constant in `Z`, counted with the multiples where
  the counter is used.  `nb_all` kept a function's bound only where its constant is below 5000, since
  the bound's statement carries it as a chain of successors (76500: 18 s and 2.4 GB to check); the constant in `Z`, in the statement
  and in the reader, and counted with the multiples against the counters' bounds where the counter is used (step 83's `nc_c` counts
  multiples only).  Accepted when such a bound is proved and used where the counter is used as itself, which needs it (`ff (cbm n n) a`
  with `cbm k m <= k + m + 76500`, and with `+ 1228500`), each pinned by a cell, and `A_zt_sum_setbit_big` (`setbit` by 20 in such a sum,
  a constant `2^20`) is proved.
- ~~*A counter a function gives back, used where its value modulo a word is enough*~~ (found at step 102) — **done, step 104**: the
  operand the row's number where a row in it has no bound.  `Nat.land x 255` is the same at
  `x` and at `x` modulo a word, and a row gives that (steps 82, 101), so no bound is needed; today such a use is read only where the
  function has a bound (`A_zs_const_mid`, `A_zs_big_const`, whose bounds' constants are 76500 and 1228500).  Inside `land` with a
  number below a word, `testbit` below 63, `mod` by a power of two, `even`, `odd`: accepted when these are proved for functions with no
  bound (a doubling, a quadratic, those two).
- ~~*A sum around such a counter with an operation the check knows nothing of*~~ (found at step 102, there since step 83) — **done, step
  103**: a call counted by the bound the check is given of it, another of Rocq's libraries past the limit.  In
  `cnt n a s + Nat.log2 n` step 83's reading takes the whole sum as one site, counting `log2 n` as one counter (`nc_c`'s 1 for any call),
  and the check, given no bound of `log2`, falls to a path that unfolds it: no answer in 120 s, the same with `sqrt` and `gcd`.  A sum is
  one site only where the check has a bound of each part; `log2`, `sqrt`, `gcd` given theirs.  Accepted when those three are proved and
  an operation with no bound is refused at once.

**B. Compiling from an ordinary `.v` file, as simply as `lean --c`.**
- ~~A command in an ordinary Rocq file~~ — **done at step 89**, without a command: `python3 proved/kitc.py prog.v [--main=NAME]`: the entry's arguments are read from its signature (numbers and counters from the
  command line, the memory from the memory file), and the file is one Rocq compiles on its own.  A `.body` still works.
- ~~Emit first, prove behind~~ — **done 2026-10-30**: `kitc.py --emit-first` (the C and the binary right after the
  translation, the proofs behind; §1.7).
- ~~A check-only mode~~ — **done 2026-10-30**: `kitc.py --no-proof --no-build` (the translation alone, with its refusals).
- Refusal messages that say what to write instead (the library, the rewrite), with a pointer into this file.
Accepted when: every example and corpus program compiles from a `.v` file with the command, with the same C as today (`tests/vroute.py`, step 89).  Left: the refusal messages.

**C. Language beyond the table.**  Records of k numbers as results (the slot block with k-1 cells); strings and a formatting
library on byte blocks (`printf`-like, written in Rocq); an address type with proved arithmetic, and pointers beyond views;
specialization of type and instance arguments; optional: `Z` where a proof gives the range (D3).  A tactic that proposes the measure itself for the common loop shapes (counting up to a bound, counting
down, halving), so `wfixN` needs no measure written for them; loops whose end depends on the data still take one.

**D. Freestanding.**  **Done at step 90** (§9.5): the generated C built and checked on its own, no hosted headers, the support code only (`sup/free/`); a freestanding `kq_grow`.

**E. The general speed passes (§6.4):** bounds-test removal where the index is proved in range; forwarding; hoisting.  Each
proved once, measured against C written the same way.
- ~~*A counter written as a number*~~ — **done, step 94**: a chain of successors on 0 is `CLit k`, the digits Rocq writes from 5000 on
  are `CNumU u`, a product by such a number `CMulU`; each is one constant in the C; the 33 changed programs' C
  and clang's assembly compared: the corpus programs' machine code is the same, so the timing is too.
- ~~*A power of two written numbers above 4096*~~ — **done, step 95**: `CPowL` over two written numbers, its code the value worked
  out in `Z` by squaring; past a word, a pin with its control.

**F. Proof speed, only if it becomes the bottleneck (§7.5):** segmenting long straight-line functions; reflection.
- ~~*The look for a local mutual block, once per program*~~ (found at step 108) — **done, step 109**: step 31's look made before the
  lifting, nothing lifted where it finds none.  Step 108 walks every function's body for one in each of
  the reading's tries (`lift_all` runs in each `reify_prog2c`), and `HWP_irqnow`'s reifier step measured about 0.1 s slower (1.69 to
  1.76 s on a quiet machine), the other kernels within 1%.  The lifting done once, before the tries.  Accepted when the kernels'
  reifier step measures as step 107's.
- ~~*The laws of a data type with many constructors*~~ (found at step 106) — **done, step 107**: each arm's tag computed once;
  `A_q_byte_lit` 8.7 s.  `A_q_byte_lit` (`match x with x41 => 1 | _ => 0 end` on a
  `byte`, 256 constructors) takes about 100 s, there before these steps.  Its proof file spends 88 s in one law, `KQR.kq_rbt_case`:
  each arm takes 1 ms at its tag, but the loop `destruct c as [|c]` leaves the goal's tag as `S (.. (S c))`, so arm k reduces k
  levels of a 256-branch match, cubic in the constructors; simplifying the whole goal at each step unfolds the representation and
  runs out of memory.  A byte match is ordinary in a parser or a driver.  Accepted when `A_q_byte_lit`'s proof file takes under 10 s,
  every law of every program of the gate and the table proved as before.

**G. Concurrency:** an interleaving semantics of two programs over the marked operations; protocol properties proved once (a
lock's mutual exclusion, a queue); a ticket lock.

**H. The tools the proof stops at.**  The theorem is about the Clight the generator makes.  "The driver" here is the C `main` `kitc.py` writes, which fills the tables and calls the entry: not a device driver and not tied to an ISA.  A device driver is an ordinary Rocq program on the machine operations.  The printer, clang, the loader that fills the
tables, `kq_grow` and the driver are not proved.  **The proof ends at Clight (D30, owner, 2026-11-08)**: the C text goes to any C compiler,
and a holder of a CompCert licence uses `ccomp`, whose theorem carries it from CompCert's C to assembly (its own front end and assembler
trusted).  Nothing of the default build uses CompCert's passes: `proved/KQLBack.v` is outside `make.sh` since step 88.  Left here: checks
of the printed C against the Clight, in `proved/examples.sh` since step 91 (undefined behaviour trapped, `-O0`, `ccomp` where it is
installed); the loader and `kq_grow` as a case of the generator's proof or as Rocq on the primitives.

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

**O. The operation checklist (§2.1):** **done at step 88**: `uint64_t` division and remainder as one instruction, a case of the generator's proof; `lib/CInt.v`: signed 64-bit arithmetic, the high half of a product, 8/16/32-bit signed and unsigned arithmetic with C's wrap-around, `popcount`, `clz`, `ctz`, `bswap`, rotate, with what each computes proved (`lib/CIntSpec.v`).  Left, when a program's speed asks for it: `popcount`, `clz`, `ctz` as a single instruction, a case of the generator's proof, measured; never a machine operation (F66).

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

**P. Rocq's own measure recursion (§4.5) — the owner's "level 2".**  `Program Fixpoint {measure ..}` is read (§12.V, step 56, by `fix_sub_budget`, the
plan through `fix_sub_eq` dropped), no new assumption; `{wf R x}` a gap with its cell.  `Function` is read (step 57), `Equations` (step 60).  Accepted when the `wfix` examples written as `Program Fixpoint` compile, prove and give the same
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
(`loop_two`, not in `S`) is reported not read, then proved by the translator, answer 41.  **The gate with `KQ_REFLECT=1`, on
the fork (2026-10-31): everything passes** — `make.sh` `core-ok`; examples 23 / 23; corpus 36 / 36 equal to the C++ answers;
the five kernels proved and built (36–54 s, as without it) — and **the baseline `S` grows against: 1 of 67 programs through the
verified compiler** (`reflect_calls`), **66 read by the translator** (fallback), **0 read but refused by the check**.
**Why a program is not read (2026-10-31, `KQRReify.reify_why`, printed by `kitc.py --reflect`):** for each function not read,
its constants outside the syntax, constructors, matches on other types, projections, local fixpoints, lets of other types, a
signature not read (with the types, or "parameters in an order not read" when every type is a number, counter or memory), and
known constructs in places not read yet (a number function that writes the memory, a match on a counter inside the body, a test
that is a boolean value), and "calls f, not read".  **The tally over the gate's 67 programs** (the reasons grouped by construct;
a program is done only when all of its are): counters as values — a second counter (`rounds (r n : nat) ..` recurses on `r` and
passes `n` on), `S`/`O`, budgets `kq_nat` — 56 programs; booleans 27; number functions that write the memory 25; `KQRun.v`'s
helpers `zdiv`/`zmod`/`zmin` (C's signed division, a minimum: defined outside the program's file, so not reached) 21; narrow
memory (32-bit cells, bytes, views) 15; machine operations 10; functions given to functions (the loop library, `wfix`) 8;
records and pairs 4; `u64` 2; negation (`opp`) 2; mutual recursion 1.  **The order that completes the most programs**: counters
as values (9 of 67 through the verified compiler), booleans (20), narrow memory (26), number functions that write (31),
`KQRun.v`'s helpers read as functions (41), machine operations (51 — the kernels), functions given to functions (58), then
records, `u64`, negation, mutual recursion (67).  The reasons are a scan of each function's text, so removing one may reveal a
reason of place behind it; the gate counts after each step.  **Next: counters as values.**

**Step 4, counters as values — the design (2026-10-31).**
- *Signatures*: `sc : bool` becomes `sn : nat`, the number of counter parameters, first (the first is the one a recursive body
  recurses on); `ftype g := ctype (sn g) (ntype ..)` with `ctype x T` = `x` arrows from `nat`; `absc` / `appc` bind and apply
  them as `absn` / `appn` do numbers; a call is `callf g h cvs vs s`.
- *Syntax*: a fourth mutual sort `scnt` — `CVar i` (the `i`-th counter variable, nearest first), `CO`, `CS c`, `CNat e`
  (`kq_nat e`, a budget from a number; `kq_nat` stays opaque, the proof uses `kq_nat_val` / `kq_nat_le`).  `SCall f cs args`,
  `MCall f cs args m` give the callee its counters; `SRec cs args`, `MRec cs args m` give the recursive call its counters after
  the first (the first is the predecessor, as now).  `SMatch c e0 e1` / `MMatch c m0 m1`: a match on a counter variable inside a
  body, the predecessor `CVar 0` in the second branch.  `ncnt` (`NNone | NCnt | NPred`) is gone: it was these three lists.
- *Meaning*: `denote_e` / `denote_m` take the counter environment `cenv : list nat` (nearest first); the recursive call's meaning
  takes the counters after the first, `rec : list nat -> list i63 -> mem -> ..`.
- *KQL*: the counters in variables `1 .. sn` (the first in 1, as now), the numbers after them, the predecessor after those;
  `CS` an addition, `CO` the atom 0, `CNat` the clamp the translator makes (two conditional moves), `SMatch` an `Eif` against 0
  and a subtraction.
- *Bounds* (a counter's machine number `ofn n` wraps at `wB`, so the zero test needs `n < wB`; `S` makes counters grow): function
  `j` of a program assumes its counters below `cbz j := 2^62 - j·2^20`, which falls as `j` grows; a caller comes after its callees,
  so a counter it holds plus up to `2^20` steps of `S` is still below a callee's bound.  `wf` checks: a callee's counter
  arguments nest `S` at most `2^20` deep; the recursive call's counters after the first and `SMatch`'s subject have no `S` (a
  counter grown at every round has no bound); `CNat` is at most `2^60`, below every `cbz j` of a program of fewer than `2^41`
  functions.  The proof's invariant gains: the atoms of the counter environment hold `ofn` of its values, all below `cbz j`.
- *Reifier*: counter entries in the context, read off `nat` parameters and the predecessor of a match on a counter; `S`, `O`,
  `kq_nat` as counter expressions.  `kitc.py`: the entry's kinds `N` × `sn`.
- *Not in this step*: a `let` of a counter, arithmetic and comparisons on counters (`Nat.eqb`, `n + n`), counters after a number
  parameter (§3.7).

**Step 4 done (2026-10-31): counters as values.**  Built as designed, in `proved/KQR.v` and `proved/KQRReify.v`:
- *Syntax and meaning*: `sig.sn` counters first; the counter sort `scnt` (`CVar`, `CO`, `CS`, `CNat`) mutual with `sexp`;
  `SRec cs args` / `MRec cs args m` (the recursive call's counters after the first, the first being the predecessor),
  `SCall f cs args` / `MCall f cs args m`, `SMatch c e0 e1` / `MMatch c m0 m1`; `denote_*` take the counter environment;
  `ctype` / `absc` / `appc` bind and apply counters as `ntype` / `absn` / `appn` do numbers.
- *KQL*: the counters in variables `1 .. sn`, then the numbers; `CS` an addition, `CO` the atom 0, `CNat` the translator's
  clamp (two conditional moves), `SMatch` an `Eif` against 0 and a subtraction into a fresh variable.
- *Bounds*: `callee_ok P id B gs h` takes the bound; function `j` is proved for counters below `cbz j = 2^62 - j·2^20`, and a
  callee's theorem is used at its own bound; `compile_f_ok` gained two decided conditions (`length cs <= j`, `j < 2^40`), closed
  by `eq_refl`; `wf` checks that a callee's counters nest `S` at most 2^20 deep (`shallow`) and that the recursive call's have
  none (`flat`); the invariant gained the counter environment (`cenv_ok`: each atom holds `ofn` of its counter; `cbound`: every
  counter below `cbz j`).  `kq_nat` stays opaque: the proof uses `KQMAuto`'s facts about it (`kq_nat_val`, the clamp).
- *Reifier*: counter entries in the context — a `nat` parameter, the predecessor a match on a counter binds, and the
  predecessor of the first counter, which the recursive call is given first; `O`, `S`, `kq_nat` as counter expressions,
  numerals included; a call's counters split off its arguments by the callee's `sn`; the signature's leading `nat`s.  A function
  is kept only when it is well formed (`wf_f`), so a program the reifier reads is a program `compile` takes; one read but not
  well formed — a counter grown at every round of a recursion (`grow`) — is refused with that reason.
- *Measured* (stock kernel, one machine): `inner`, `rounds` (two counters, the second given on to a callee and to the
  recursive call), `twice` (a match on a counter inside a body, `S (S p)` given to a callee), `bud` (`kq_nat` of a number), and
  from the text a program calling them with numerals as counters (`cnt_all`): the reifier gives exactly the hand-written trees;
  every theorem 0.001–0.023 s; `KQR.v` compiles in 3.7 s, `KQRReify.v` in 2.5 s.  `Print Assumptions`: Rocq's integer axioms —
  now with three of the signed ones (`Sint63Axioms.asr_spec`, `leb_spec`, `ltb_spec`, through `kq_nat`'s facts) — and the kit
  memory's declared operations; no memory law, no admit.
- *The gate with `KQ_REFLECT=1`, on the fork (2026-10-31): everything passes* — `make.sh` `core-ok` (32 s); examples 24 / 24
  (the new `reflect_counters` included: answer 652, worked out by hand); corpus 36 / 36 equal to the C++ answers; the five
  kernels proved and built (36 / 37 / 41 / 57 / 44 s); and **9 of the gate's 68 programs through the verified compiler** (was
  1 of 67): `reflect_calls`, `reflect_counters`, `sdiv`, and the corpus programs `CF1167C`, `CF165E`, `CF165Ev2`, `CF295B`,
  `CF295Bv2`, `CF339D`; **0 read but refused by the check**; the other 59 read by the translator, all passing.  The new example
  through the translator (the default gate's path): proved, 652.  (The gate script's count of programs not read misses the five
  main kernel programs, whose long reason lines the kernel build cuts at 700 characters; the tally below counts them.)
- *The tally after the step* (the reasons per program, as before, over the 68): booleans 27, number functions that write the
  memory 26, `KQRun.v`'s helpers 21, narrow memory 15, machine operations 10, functions given to functions 8, a `let` of a
  counter 4 (`CF1100F` and its two variants, `heap`), records and pairs 4, `u64` 2, negation 2, mutual recursion 1, records of
  other types 2.  One program the tally of step 3 counted as needing counters only, `CF163A`, needed more: its `solve` reads the
  memory a call gives back (`rd rST 0 (rows .. s)`) — a number function that writes the memory — which the reason scan did not
  see and reported as "not classified"; the scan now names it (`rd_in_place`).  So the step completed every program it could.
  **The order that completes the most now**: booleans (+8, 17 of 68), number functions that write the memory (+6, 23),
  `KQRun.v`'s helpers read as functions (+8, 31), narrow memory (+8, 39), machine operations (+9, 48: the kernels), functions
  given to functions (+7, 55), a `let` of a counter (+4, 59), then records, `u64`, negation, the rest (68).  **Next: booleans.**

**If-conversion in `compile` (2026-10-31; F49).**  Timing the six corpus programs that moved to the verified path in step 4
against the translator's build of the same text (same machine, same run, one pinned core, best of 7) found two of them 1.45x
slower: `CF295B` 94.8 → 139.2 ms, `CF295Bv2` 84.8 → 122.2 ms (the other four within the spread).  Their inner loop writes the
smaller of two numbers (`upd rD (bi + j) (if b <? a then b else a) s`); the translator makes that choice a conditional move
(`choice_ok`, D17) and `compile` made it a jump, with the rest of the loop written out on both sides.  Now `compile` does what
the translator does: a choice whose two numbers are arithmetic, variables, reads of the memory and such choices, with at most
three reads in the two, is worked out both ways and taken with `Esel` (`choice_ok` on the syntax, the case of `cexp`); a choice
with a call, a `let` or a match, and a test at the end of a function (a loop's tests), stays a jump.  The proof case needs no
condition: both numbers evaluate (the lemma for numbers says so for every well-formed one), so which choices are converted is
a speed decision only.  Test: `relax` (the loop of `CF295B`), its KQL has the conditional move, its theorem in milliseconds.
Measured again (same conditions): `CF295B` 98.5 / 94.9 ms, `CF295Bv2` 91.8 / 91.9, `CF339D` 167.8 / 176.1, `CF165E` 98.5 /
101.0, `CF165Ev2` 79.8 / 81.3, `CF1167C` 9.0 / 8.7 (the translator's build / the verified compiler's) — within the run-to-run
spread (§6.1: about 15%; `CF339D` was equal in the first run); the C of `CF295B` is now the translator's, line for line.
The gate with `KQ_REFLECT=1` on the fork, on this tree: `make.sh` `core-ok`; examples 24 / 24; corpus 36 / 36 equal to the C++
answers; the five kernels proved and built (36 / 36 / 38 / 54 / 41 s); the same 9 programs through the verified compiler, 0
refused by the check.
**Rule kept from it:** a program moved from the translator to the verified compiler is timed against the translator's build of
the same text before the move is reported (`rtime` in the session's tools: both builds, one run, one pinned core) — the gate
checks answers, not speed.

**Step 5, booleans — the design (2026-10-31).**
- *Syntax*: a fifth mutual sort `sbool` — `BCmp c a b` (a comparison of two numbers), `BVar i` (the `i`-th boolean variable,
  nearest first), `BTrue`, `BFalse`, `BAnd x y`, `BOr x y`, `BNot x`.  Numbers gain `SIfB b t e` (a test on a boolean that is
  not one comparison) and `SLetB b e` (`let x := b in e`); memories gain `MIfB b m1 m2` and `MLetB b m`.  A test on one
  comparison stays `SIf` / `MIf`, so the C of the programs already on the verified path does not change.
- *Meaning*: `denote_b` gives `cmp_sem`, `andb`, `orb`, `negb`, `true`, `false`, and `nth i benv false` — the user's `&&`, `||`
  and `negb` are those constants, so the per-program check stays a conversion; a boolean environment `benv` is threaded through
  the meanings as the counters' is.
- *KQL*: a test on a boolean is jumps (`ccond`, a continuation for each outcome): `a && b` tests `a`, then `b` where `a` held
  (C's short-circuit, the translator's choices on the parts); `negb` swaps the outcomes; a boolean variable is its atom tested
  against 0.  A boolean value (a `let`) is held as 1 or 0: a comparison by a conditional move (`Esel .. 1 0`), `&&` / `||` /
  `negb` by `land` / `lor` / `lxor 1` of the parts' values — no jump; both parts are worked out, which changes only the cost of
  the part not needed (every part is pure and total).  A choice between two cheap numbers on a boolean is a conditional move on
  its value, as for a comparison.
- *Proof*: the invariant gains `benv_ok` (each boolean atom holds 1 or 0 for its value) with its `lt_all`; two new cases of the
  mutual lemma — the test ("if the code for the outcome that holds evaluates to `v` from every extension of the environment,
  the test does") and the value (`land (b2i x) (b2i y) = b2i (andb x y)`, and the same for `lor` and `lxor`).
- *Reifier*: a boolean entry in the context; `andb`, `orb`, `negb`, `true`, `false`, comparisons and boolean variables as
  boolean expressions; a `let` of type `bool`; a test whose subject is not one comparison.
- *Not in this step*: boolean parameters and results of functions (`put (isnew : bool) ..`, a function giving back a boolean).
  They change the signature from "`k` numbers" to a list of kinds of value, which records and pairs need as well; that is done
  once, for both, as the step on values across calls.  So `CF35C` (its helper `put` takes a boolean) waits; the other seven
  programs the tally gives booleans are expected.

**Step 5 done (2026-10-31): booleans.**  Built as designed, in `proved/KQR.v` and `proved/KQRReify.v`:
- *The proof*: every meaning, compiler and lemma of `KQR.v` gained the boolean environment (`benv`, and `benvA`, its atoms);
  the invariant has nine parts (`benv_ok`, its `lt_all`); the mutual lemma's fifth part, for a boolean, is the conjunction of
  the test (`ccond`) and the value (`cbval`) — one sort, two lemmas; `b2i_land` / `b2i_lor` / `b2i_lxor` / `b2i_eq0` carry the
  values.  The memory and tail lemmas gained the four cases (`SIfB`, `SLetB`, `MIfB`, `MLetB`), `compile_f_ok` starts with no
  booleans.  Proved as designed, no new hypothesis.
- *Tests*: `chk` (three tests made of `&&`, `||`, `negb`, each choosing between two numbers: conditional moves on the
  booleans' values, its KQL has `Esel`), `cnt_in` (a boolean `let` tested at the end of a loop: jumps), `mark` (a memory chosen
  by `a && negb b`); a tree with `||` where the text has `&&` is refused by the check; every theorem 0.001–0.004 s; `KQR.v`
  compiles in 3.9 s; `Print Assumptions` the same base as step 4.  The reifier gives exactly the hand-written trees for the
  three; a test on one comparison stays `SIf`, so the C of the programs already on the verified path is unchanged.
- *Through the verified compiler: 17 of the gate's 69 programs* (was 9 of 68): `ifs_chain`, the new `reflect_bools` (answer
  4095, worked out by hand; the first expected value, 4084, was mine and wrong — the eighth cell is 7, read as 77 from the
  memory file — and both builds, the translator's and the verified compiler's, gave 4095), `CF380C`, `CF380Cp`, `CF235C`, `CF235Cv2`, `CF813F`, `CF813Fv2` added — the seven the tally
  expected.  **Timed against the translator's build** (F49's rule; best of 7 ms, the translator's / the verified compiler's):
  `CF380C` 62.1 / 62.4, `CF380Cp` 49.6 / 47.9, `CF235C` 55.5 / 52.7, `CF235Cv2` 66.7 / 67.8, `CF813F` 44.6 / 44.4, `CF813Fv2`
  38.9 / 40.2 — within the spread.  (A first run of `CF380C` and `CF235Cv2` gave the same wrong answer with both builds: the
  timing script had dropped `hand.tsv`'s memory column; with it, both right.)
- *A check that ran out of memory (F50).*  The first gate of this step had `CF813F` and `CF813Fv2` read and then refused by the
  check: the theorem of their `solve` exhausted the memory (over 2 GB in 6 s locally).  `solve` calls its callees with written
  counters (`dfs 20 q ..`, `msort 20 ..`).  Comparing the function with its tree's meaning, the kernel chose to unfold the user's
  `dfs` before the meaning side had reduced to the same call — and a function applied to a written counter is worked out round
  by round (pinned in `KQR.v` with `tw 20`, two calls a round: 4.7 s and 1.2 GB for one theorem).  With a counter variable, as
  in every earlier test, the user's function is stuck after one step, so this never showed.  Setting the compiler's meaning
  functions to be unfolded first (`Strategy expand`) did not change it; setting the program's own functions to be unfolded last
  (`Strategy opaque`, written by `kitc.py` into each program's theorem file) did: `tw 20` 0.002 s, `CF813F`'s whole theorem file
  2.7 s.  It changes the order of unfolding only — nothing that converts stops converting, as for `kq_nat` (§1.6).
- *The gate with `KQ_REFLECT=1`, on the fork, on the final tree (2026-10-31): everything passes* — `make.sh` `core-ok`; examples
  25 / 25; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (36 / 37 / 39 / 55 / 43 s); **17
  programs through the verified compiler** (the 9 before, `ifs_chain`, `reflect_bools`, `CF380C`, `CF380Cp`, `CF235C`,
  `CF235Cv2`, `CF813F`, `CF813Fv2`), **0 read but refused by the check**.
- *The tally after the step* (over the 69): number functions that write the memory 26, `KQRun.v`'s helpers 21, narrow memory
  15, machine operations 10, functions given to functions 8, a `let` of a counter 4, records and pairs 4, a test on a call
  giving back a boolean 4 (the loop library's function parameters, `u64` comparisons, the heap), boolean parameters and results
  3 (`CF35C`, `CF35Cn`, `heap`: the step on values across calls), `u64` 2, negation 2, mutual recursion 1, records of other types
  2.  **The order that completes the most now**: number functions that write the memory (+6, 23 of 69), `KQRun.v`'s helpers
  (+8, 31), narrow memory (+7, 38), machine operations (+9, 47: the kernels), functions given to functions (+5, 52), a `let` of
  a counter (+3, 55), then records, tests on calls, boolean parameters, `u64`, negation, the rest.  **Next: number functions
  that write the memory.**

**Step 6, number functions that write the memory — the design (2026-10-31).**  The six programs this step completes
(`helper_write`, `rmw_chain`, `CF20C`, `CF163A`, `CF868F`, `CF868Fv2`) have one shape: a root `solve` that makes memories —
`let`s, calls of functions giving back a memory, writes — and then gives a number read from the last memory, often written
inline (`rd rST 0 (rows .. s)`), possibly under a test.  Such a function is stated as the translator states it (§1.6), with
the end memory hidden: `runx` (`exists M', runk .. M'`).
- *Signature*: `sig` gains `sw` — a number function that writes; `callee_ok` says, for such a function, that its KQL gives the
  number with some end memory.  Calls of it (`SCall`, `MCall`) are refused by `wf` for now: after such a call the caller's KQL
  memory is not the Rocq text's (it would have to be dropped, the translator's `runx` caller rule) — the next step.
- *Syntax*: a sort `sx` over `smem` and `sexp`: `XRet e` (a number from the newest memory), `XLetM m x` (`let s2 := m in x`),
  `XLet`, `XLetB`, `XIf`, `XIfB`, `XMatch`; a body `FPlainX x`.
- *Meaning*: `denote_x` (the number) and `endx` (the memory KQL ends with: the last one made) — the proof states the end memory
  exactly, so the continuations of the existing lemmas, which fix the result and the end memory up front, need no change and no
  determinism lemma; `callee_ok`'s `exists` is given by `endx`.  (A writing function calling a writing function, and loops that
  write and give a number, need the callee's end memory, which its statement hides: done with the caller rule.)
- *KQL*: `ctailx` — the memories by `cmem`, the tests as branches, the end `Eret` of the number.
- *Reifier*: a number function the number reader does not read is tried as `sx`: `let` of a memory, of a number, of a boolean;
  tests; and a read or a call whose memory is made in place (`rd h i (f .. s)`) is read as `let s2 := f .. s in rd h i s2` —
  the same term up to `let` (zeta), so the check is unchanged; the numbers of that read must not name the older memory (dead).

**Step 6 done (2026-10-31): number functions that write the memory — and two more of the translator's code-shape rules.**
- *Built as designed*: `sig.sw`; the sort `sx` with `denote_x` and `endx`, `ctailx` and its lemma `ctailx_ok` (the KQL gives the
  number and ends with exactly `endx`'s memory — no determinism lemma needed); `callee_ok` gives a writing function's statement
  as `runx` (some end memory); `SCall` / `MCall` of a writing function refused by `wf`, and the old proof cases take the new
  conjunct.  The reifier reads such a function when the number reader does not, a read or call whose memory is made in place
  as a memory `let`.  Tests: `mafter` (memory lets, a call, a test, `rd 0 2 (bump 2 s3)`), its theorem in 0.003 s; a call of
  it from a number refused by `wf`.
- *Timing found two more rules the verified compiler lacked* (F51; the six moved programs timed against the translator's
  build, as F49 asks): `CF868F` was 1.48x slower.  (1) **Merging two calls of the function itself**: `if v <? best then scan ..
  v p s else scan .. best opt s` is one loop step in the translator's C, the differing arguments chosen by conditional moves
  (§1.5's second rewrite, D17); `compile` made it a jump.  Now `ctail` / `ctailm` merge a test whose two ends are calls of the
  function itself on the newest memory, with arguments of plain arithmetic: equal arguments (`same_e`, structural) worked out
  once, the others chosen (`cmerge_s` / `cmerge_c`, their lemmas `cmerge_s_ok` / `cmerge_c_ok`, the loop lemmas
  `loop_call_ok` / `loopm_call_ok`); as for if-conversion, which calls are merged is a speed decision, the proof needs only
  that both argument lists evaluate.  Test: `argmin` (the shape of `CF868F`'s loop).  This brought `CF868F` to 1.22x, and a
  first version that also moved equal arguments (`p + 1` on both sides) left the next round waiting on the test.  (2) **Each
  variable bound once per function**: with the C now the translator's construct for construct, `CF868F` was still 1.22x
  slower; the two C files differed only in the numbering of temporaries — `compile` reused numbers across the arms of a test
  (both arms start from the same next variable), the translator numbers every variable once.  Measured apart: the same KQL
  renamed to unique numbers (a throwaway script) ran at the translator's speed (112.7 ms against 114.0; reversing the
  declarations or reordering the functions changed nothing); the reused numbers give the C compiler worse register choices
  (85 register moves against 67 in the loop).  Now the second arm of every test starts after the first arm's variables
  (`after n e`, `maxv`) — twelve places in the compiler; the proof needs only that the second arm starts at some later
  variable, which the invariant already allows (`after_le`, `agree_mono`).
- *Timed (best of 7 ms, the translator's / the verified compiler's), all 16 corpus programs on the verified path*: `CF1167C`
  8.9 / 9.3, `CF165E` 101.7 / 101.5, `CF165Ev2` 83.6 / 79.6, `CF235C` 61.3 / 57.9, `CF235Cv2` 68.2 / 66.1, `CF295B` 96.1 / 98.0,
  `CF295Bv2` 91.1 / 98.1, `CF339D` 180.7 / 183.7, `CF380C` 62.1 / 66.0, `CF380Cp` 47.9 / 47.7, `CF813F` 45.2 / 46.5, `CF813Fv2`
  46.1 / 43.4, `CF20C` 7.4 / 6.9, `CF163A` 24.6 / 25.0, `CF868F` 107.3 / 107.3, `CF868Fv2` 64.3 / 63.9 — within the spread.
- *Through the verified compiler: 24 of the gate's 70 programs* (was 17 of 69): `helper_write`, `rmw_chain`, `CF20C`, `CF163A`,
  `CF868F`, `CF868Fv2` and the new example `reflect_writes` (a write, a call that fills, a number let, a branch reading a memory
  made in place; answer 64, worked out by hand; the translator gives 64 too).
- *The gate with `KQ_REFLECT=1`, on the fork, on the final tree (2026-10-31): everything passes* — `make.sh` `core-ok`; examples
  26 / 26; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (37 / 37 / 39 / 55 / 42 s); **24
  programs through the verified compiler, 0 read but refused by the check**.
- *Not yet read*: a call of a writing function (the caller's memory must then be dropped — the translator's `runx` caller
  rule), a loop that writes and gives back a number (its end memory, from the recursion, is hidden by its statement), and a
  memory made in place inside a larger expression (`rd .. (f s) + 1`: only at the head of the last number today).
- *The tally after the step* (over the 69 of the tally run): `KQRun.v`'s helpers 21, number functions that write in places not
  read yet 16, narrow memory 15, machine operations 10, functions given to functions 8, loops that write and give a number 5,
  a `let` of a counter 4, records 4, tests on calls giving back a boolean 4, boolean parameters 3, `u64` 2, negation 2, the
  rest 3.  **The order that completes the most now**: narrow memory (+5, 28 of 69), `KQRun.v`'s helpers (+4, 32), calls of
  writing functions and reads in place inside expressions (+3, 35), machine operations (+8, 43: the kernels), functions given
  to functions (+4, 47), loops that write and give a number (+5, 52), then the rest.  **Next: narrow memory.**

**Step 7 done (2026-10-31): narrow memory — cells of 4 bytes.**  The five programs it completes use `rd32` / `upd32` only
(bytes and halfwords, `rd8` / `upd8` / `rd16` / `upd16`, are definitions over them in `KQRun.v`, met in 3 programs; they come with
the helpers, next).  `SRd32 h i` among the numbers and `MUpd32 h i v m` among the memories, meaning `KQRun.rd32` / `upd32`
themselves, compiled to `Ekld32` / `Ekst32`, whose rules have exactly the shape of the wide cells' (`K_ld32`, `K_st32`), so the
proof cases are those of `SRd` / `MUpd`; a 32-bit read counts as a read for the conditional-move rule (as the translator's
`choice_ok` counts `rd32`).  Tests: `acc32` (a loop writing 4-byte cells from the cell before), `sum32`; the reifier gives the
hand-written trees.  **29 of the gate's 70 programs through the verified compiler** (was 24): `CF339Dn`, `CF295Bn`, `CF235Cn`,
`CF380Cn`, `CF165En`.  Timed against the translator's build (best of 7 ms): `CF339Dn` 111.4 / 110.8, `CF295Bn` 118.3 / 119.0,
`CF235Cn` 37.2 / 36.7, `CF380Cn` 55.9 / 56.7, `CF165En` 58.6 / 57.5 — the same.
The gate with `KQ_REFLECT=1`, on the fork, on the final tree (2026-10-31): everything passes — `make.sh` `core-ok`; examples
26 / 26; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (37 / 37 / 39 / 57 / 42 s); **29 programs
through the verified compiler, 0 read but refused by the check**.
**The order that completes the most now**: `KQRun.v`'s helpers (+4, 33 of 70 — and needed by 21), functions given to functions
(+3, 36), calls of writing functions and reads in place inside expressions (+3, 39), machine operations (+8, 47: the kernels),
loops that write and give a number (+5, 52), a `let` of a counter (+3, 55), then the rest.

**Step 8, helpers written out where they are used — the design (2026-10-31).**  `zdiv`, `zmod`, `zmin`, `zmax`, `zabs`
(`KQRun.v`: C's signed division and remainder corrected to `Z`'s rounding, a minimum) are not reached today because the reifier
follows only the root's own file — and they should not become functions of their own: the translator writes them out at
their uses (§1.5, `helper_body`), where the divisor is usually a number written in the program and the C compiler turns the
division into a multiplication.  So the reifier does the same, for the same set: a definition of the program's file, of
`KQRun.v` or of `Uint63` that has no fixpoint and is not one of the program's functions is read at a call as its body with the
arguments as `let`s (`beta_lets`, as the translator's); `reach` keeps as functions only the root, the recursive definitions and
the helpers larger than the translator's bound (`big_fun`, 40 nodes).  Nothing changes in the proved compiler: the kernel's
check unfolds the helper and the `let`s itself (`zdiv a b` is `let a0 := a in let b0 := b in ..` up to delta, beta and zeta),
and the program's functions set to be unfolded last (F50) are only the ones that stay functions.  A `let` of an argument
costs nothing in KQL (a `let` binds the argument's atom, a written number stays a number).  Helpers met in a boolean position
(a test on a helper giving back a boolean) are not read yet (a boolean `let` is not in the boolean sort).

**Step 8 done (2026-11-01): helpers written out where they are used — and one more of the translator's code-shape rules.**
- *Built as designed, in the reifier* (`KQRReify.v`; nothing in the proved compiler for the reading): `helper_of` — a
  definition of the program's file, of `KQRun.v` or of `Uint63` with no fixpoint that is not one of the program's functions;
  the functions are the root, the definitions of the file that are a fixpoint, and those larger than 40 nodes whose parameters
  are numbers, counters, booleans or a memory and whose result is a number or a memory (`is_fn`, `big_def`: the translator's
  `is_fun` / `big_fun`).  Left out on purpose: `rd8` / `upd8` (and so `rd16` / `upd16` over them), which must become one byte
  access each, as the translator makes them, not shifts of a 4-byte cell (§6.1: 74 against 136 ms); `w64_op`; `kq_nat`.  At a
  call the helper's body is read with its parameters given their arguments (`wout`, the translator's `beta_lets`): put in when
  the argument is a variable, a number, a constant, a constructor or a written counter, or when the parameter is a function or a
  type; bound by a `let` otherwise, so each argument is worked out once and in the order of the call.  `reach` walks helper
  bodies for the functions they call.  The kernel's check unfolds the helper itself (delta, beta, zeta, iota); only the
  functions that stay functions are unfolded last (F50).  `reach` and the reasons of a program not read look at each helper
  once: a first version re-read a helper's body at each call and made the reifier's step on the kernels' programs slower than
  step 7's (`HWP_kernel` 16.7 → 22.1 s, `HWP_own` 18.7 → 22.2 s, the first gate's kernels 3–6 s slower); now the same as step
  7's (17.0 / 16.5 s, 18.5 / 18.6 s).
- *Three rules writing out needs, each the translator's* (`knorm`, `app_norm`, §1.5): a match on a counter written as `O` /
  `S ..` takes its branch (`c_twice 2 x` is a call of `c_inner` with `S (S (S O))`); a function applied to its arguments is
  written out the same way (`twice (fun z => z - 1) i`); and the lets a test's subject starts with come first — a match on a let
  is put inside it, the same term up to zeta — for the first operand of `&&`, `||`, `negb` only, so the work is done where the
  translator does it (`slab_live b h s && ..` in the heap's `slab_get`).  The design above had left a test on a helper giving
  back a boolean unread; with this rule it is read (a let in a later operand of `&&` / `||` still is not).
- *Tests* (`KQRReify.v`): `hz` (the kit's `zdiv`, `zmod`, `zeven` in a test, `zmax`, `zabs`, `zopp`, `zmin`: one function),
  `hbig` (more than 40 nodes: stays a function, called twice), `hb8` (`rd8`: not read, its reason "rd8"), `hho` (a helper given a
  lambda and a partial application), `hlt` (a test on a helper whose boolean starts with two lets); `loop`, `cnt_all`,
  `mafter` read with their helpers written out — each tree checked against the hand-written one, each theorem in milliseconds,
  `Print Assumptions` the same base.  New example `reflect_helpers` (answer 19, worked out by hand: Z's rounding on negative
  cells, a helper given a function, a boolean helper with lets; the translator gives 19 too).
- *The C of the programs read before*: the helpers of the program's file were functions in the verified compiler's C and are
  written out now, as in the translator's: of the 29 programs read before, 23 have byte-identical C, 6 changed (`CF20C` and the
  examples `helper_write`, `reflect_bools`, `reflect_calls`, `reflect_counters`, `rmw_chain`).
- *Timing found one more rule* (F52, the F49 rule): `CF453B` was 1.34x slower (346 → 465 ms).  Its inner loop writes `if (m
  land mb =? 0) && (cost <? old) then cost else old`; `compile` made the boolean's value (two conditional moves to 1 / 0, a
  `land`) and then one move, the translator chooses on the parts (`if a then (if b then T else F) else F`, two moves — §1.5).
  Measured apart, the verified compiler's C with only that choice replaced by the translator's two moves: 457 → 376–381 ms
  (the translator's 343).  Now `compile` has `csel b T F` — on a comparison or a boolean variable one conditional move, on
  `&&`, `||`, `negb` choices on the parts — used by a choice on a boolean (`SIfB`); its lemma `csel_ok` is the third part of the
  boolean case of `cexp_all`; test: `chk`'s three choices are five moves on the comparisons and no bit operation (`shape`).
  **What is left on `CF453B` (1.11x) is kept, and why**: `cost := cur + zabs (ai - b)` is a conditional move in the verified
  compiler (the general rule, D17; C's `abs` compiles without a jump too) and a jump in the translator's C, because the
  translator's `choice_ok` does not look through `- a` (a call of `Uint63.opp`, a helper, is not a "simple term" to it) — an
  accident of the translator's rule, which this data favours: the sign of `ai - b` changes once per inner loop.  Measured: the
  translator's C with that jump made a conditional move runs at 376 ms, the verified compiler's speed.
- *Timed (best of 7 ms, the translator's / the verified compiler's), the 8 corpus programs whose C changed or that moved*:
  `CF20C` 8.84 / 8.78, `CF35C` 36.78 / 38.09, `CF35Cn` 27.21 / 27.42, `CF385C` 214.76 / 207.65, `CF385Cn` 148.27 / 147.95,
  `CF453B` 355.88 / 394.07 (above), `CF547B` 32.17 / 31.42, `CF622F` 84.53 / 85.85.
- *Through the verified compiler: 39 of the gate's 71 programs* (was 29 of 70): `CF35C`, `CF35Cn` (their helper `put`, which
  takes a boolean, is written out), `CF385C`, `CF385Cn`, `CF453B`, `CF547B`, `CF622F`, the examples `dispatch`, `hof_inline`
  and the new `reflect_helpers`.
- *The gate with `KQ_REFLECT=1`, on the fork, on the final tree (2026-11-01): everything passes* — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (37 / 37 / 39 / 55 / 43 s); **39
  programs through the verified compiler, 0 read but refused by the check**.
- *The tally after the step* (over the gate's 71 programs): calls of writing functions and reads in place inside expressions
  16, machine operations 10, functions given to functions (recursive functions that take functions: the loop library,
  `wfix`) 7, loops that write and give a number 7, records and pairs 6, a `let` of a counter 4, tests on a call giving back a
  boolean 4, bytes 2, `u64` 2, the rest 3.  **The order that completes the most now**: a `let` of a counter (+3, 42 of 71),
  loops that write and give a number (+2, 44), calls of writing functions and reads in place inside expressions (+3, 47),
  machine operations (+9, 56: the kernels), functions given to functions (+4, 60), tests on calls giving back a boolean (+3,
  63), records (+2, 65), then bytes, `u64`, the rest.  **Next: a `let` of a counter.**

**Step 9 done (2026-11-01): a `let` of a counter — and the translator's merge of tail calls in full (F53).**
- *Built*: `SLetC c e`, `MLetC c m`, `XLetC c x` — `let w := c in ..`, `w` a counter (`CVar 0`) — in the three sorts; `compile`
  works the counter out once (`ccnt`) and binds its atom; the proof cases in `cexp_all`, `cmem_ok`, `ctail_ok`, `ctailm_ok`,
  `ctailx_ok`, `denote_nomem` (with `inv_clet`).  Every counter of a function must stay below its bound (`cbz j`), so `wf`
  takes a counter `let` when it is a variable or a budget with no successor over it, or a counter built of `O`, `S` and
  budgets only, at most 2^20 successors deep (`letc_ok`; `letc_bound`: such a counter is at most 2^60 + 2^20, below every
  bound — `cfree_bound`, `cbz_big`).  The reifier reads a `let` of type `nat` in its three readers.  Refused, with its reason:
  a `let` of `S n` over a variable (it could reach the bound; taking it means weakening the bound of every counter of the
  function by 2^20) — met in no program of the gate.  Tests: `lc` (a counter written as a number and a budget bound by lets
  in a memory function), `lcn` (a counter variable bound in a number function), `lcx` (in a number made after memories),
  `lcbad` (refused).  A first version of `cfree_bound` used `simpl in *`, which unfolded `kq_nat`'s 63 rounds on a symbolic
  number and ran the compilation out of memory (2 GB in 50 s); a `cbn` limited to the three functions involved fixed it.
- *Moved*: `CF1100F`, `CF1100Fv2`, `CF1100Fv3` (`let w := 20%nat in answer_all q w 0 (build n w 1 s)`).
- *Timing found the rest of the translator's merge* (F53): `CF1100F` was 1.52x slower (110 → 167 ms).  Its inner loop `row`
  is a chain of three tests whose four ends are calls of `row` itself, each given the memory with the same two cells written
  (`upd rPOS (dst + b) .. (upd rBAS (dst + b) .. s)`); the translator makes it one call (§1.5, `merge_ifs`: the tests worked
  out once, the differing arguments chosen along them, the cells written once with the values chosen — 80 lines and 11
  conditional moves in its C), `compile` made it jumps (169 lines, 26 tests); step 6's merge (F51) took only one test between
  two calls on the newest memory.  `qry`'s two calls under a test on `&&` were jumps too.  Now general: `mt_e` / `mt_m` read a
  chain of tests — comparisons or booleans — whose every end is a call of the function itself (for a memory, given writes
  `upd h i v ..` down to the newest memory) into a tree; `ctests` works out every test once (a comparison's operands, a
  boolean's value), `cposs` the arguments place by place — an item the same at every end once, the others at each end and
  chosen by conditional moves along the tree (`cpick`) — and `cwrites` the writes, innermost first, then the loop; taken when
  every end has the same shape and each place is the same at every end or plain arithmetic at every end (`mt_ok`, the
  translator's condition).  Proved once: `mrg_e_ok`, `mrg_m_ok`, over `ctests_ok`, `cpick_ok`, `cposs_ok`, `cwrites_ok` and
  `mt_e_sel` / `mt_m_sel` (the chain means the call of the end its tests choose).  The two-call merge (`cmerge_s`,
  `cmerge_c`) is gone: for one test and two ends the new code is the same instructions in the same order — the C of every
  other program is byte-identical to step 8's (60 of 63 compared; the three that differ are the moved ones).  Tests:
  `mrow` (two tests, three ends writing the same cells: 6 conditional moves, the counter's test the only jump), `mqry` (a test
  on `&&`: 3 moves, one jump); each theorem in milliseconds.
- *Timed (best of 7 ms, the translator's / the verified compiler's)*: `CF1100F` 109.09 / 108.52, `CF1100Fv2` 103.45 / 102.66,
  `CF1100Fv3` 79.08 / 81.43 — the same.
- *Through the verified compiler: 42 of the gate's 71 programs* (was 39).
- *The gate with `KQ_REFLECT=1`, on the fork, on the final tree (2026-11-01): everything passes* — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (36 / 37 / 39 / 57 / 43 s); **42
  programs through the verified compiler, 0 read but refused by the check**.
- *The tally after the step* (over the gate's 71 programs): calls of writing functions and reads in place inside expressions
  16, machine operations 10, functions given to functions 7, loops that write and give a number 7, records and pairs 6, tests
  on a call giving back a boolean 4, bytes 2, `u64` 2, the rest 3.  **The order that completes the most now**: functions
  given to functions (+2, 44 of 71), loops that write and give a number (+3, 47), calls of writing functions and reads in place
  inside expressions (+4, 51), machine operations (+9, 60: the kernels), tests on calls giving back a boolean (+3, 63), records
  (+2, 65), then `u64`, bytes, the rest.  **Next: functions given to functions.**

**Step 10, functions given to functions — the design (2026-11-01).**  A recursive function that takes functions (`applyn n f
x`, the loop library's `loop_up_go`, `wfix1_go k F a`) is a *template*: as in the translator (§5.1), each call that gives it
known functions gets a copy of its own, and the template itself is no function of the program.
- *Reifier*: a template's function parameter is bound to the function given (a context entry `CFn p t`): where the body
  applies it, the function is written out (`wout`, as a helper); in the template's own recursive calls the same parameter is
  passed on and is dropped, so a copy's recursion is an ordinary recursive call — `wfix1_go`'s `F (wfix1_go k' F) a` becomes,
  once `F` is written out, `.. rec (a - 1) ..` with `rec := wfix1_go k' F`, a call of the copy itself.  The call sites are
  found in each function's text with its helpers written out (`wfix1 meas F a` is `wfix1_go (kq_nat (meas a + 1)) F a`), and
  the copies are read before the function that calls them, one per template and functions given (compared as terms); a call
  is then `SCall` / `MCall` of the copy with the arguments that are not functions.  Functions given that name the caller's
  variables (closures, §5.2) are not in this step.
- *The copy's statement*: its meaning is the template applied to the functions given — `fun n x => applyn n add3 x` — which
  is what the caller's text reduces to, so the caller's check is unchanged.  But it is not a `fix`, so the copy cannot be
  checked like a function, by comparing its text with the meaning of its tree: that meaning is a `fix` over the counter.  So
  `KQR.v` gains `compile_f_okr` (and `compile_f_okrm` for a memory): a function `h` given by its two equations — `h 0` is the
  tree's meaning at 0, `h (S n)` is the tree's recursive body with `h n` as its recursive call — has the statement.  Each
  equation is checked by conversion (`eq_refl`; the template unfolds one round on `0` or `S n`); the theorem is proved once
  from `compile_f_ok` (by induction on the counter: `h` and the tree's meaning agree at every counter, the meaning depending
  on its recursive call only through its values — `denote_rec_ext`).  Nothing is added to what is trusted.
- *`kitc.py`*: a copy's meaning is defined from the term the reifier gives (`tmMkDefinition`), and its theorem is
  `compile_f_okr` with the two equations; the templates are unfolded last, like the program's functions (F50).

**Step 10 done (2026-11-01): functions given to functions.**  Built as designed:
- *`KQR.v`*: `denote_rec_ext` (over the five sorts: the meaning depends on the recursive call only through its values on
  well-formed arguments) and `denote_m_recm_ext` (the same for a memory); `compile_f_okr` / `compile_f_okrm` — a function
  given by its two equations has the statement — proved once from `compile_f_ok` by induction on the counter; `fr0` / `fr1` /
  `fm0` / `fm1` (the parts of a recursive body, for the per-program call).  Test: `tcopy` (`tapply n tadd3`, a template given a
  function), its statement from its equations in 0.002 s, the comparison with its tree's meaning refused.
- *The reifier*: function parameters bound to the functions given (`CFn`), dropped from the recursive call (`drop_fns`);
  templates (`tmpl_tys`), the call sites in a text with its helpers written out (`sites`), the copies made before the functions
  that call them and the copies their functions need before them (`ensure`), compared as terms by a structural comparison
  (`teq`), named `T__cK`, read as recursive functions (`read_tmpl`), their meaning terms (`copy_meaning`) given with the
  program (`reify_prog2`); a copy that is not read gives its template's reasons.  Looking for the call sites writes out only
  the helpers that reach a template (`tmpl_helpers`: a template call inside a helper is seen with the helper's arguments put
  in), and a program with no template looks for none: a first version wrote every helper out at every call, and the
  reifier's step on the kernels' programs went from 15.9 to 24.3 s (`HWP_kernel`); now 16.7 against step 9's 15.9 s, the
  others within half a second.  Tests: `ruse` (two copies of `rapply`,
  given `radd3` and `rmix`), `rw` (the shape of `wfix1_go`: the function given is applied to the template's own partial
  application, and written out the recursion is a call of the copy) — the trees exactly the hand-written ones, each copy
  defined from its meaning term by `tmMkDefinition` and checked by `compile_f_okr`, the callers by `compile_f_ok`.
- *`kitc.py`*: the copies' meanings defined in `NAME_r.v`, each copy's theorem `compile_f_okr` (or `compile_f_okrm`) with
  `eq_refl` and `fun n => eq_refl`; the templates unfolded last, the copies first (F54: with the copies set to be unfolded
  last as well, the kernel unfolded the template applied to `kq_nat (..)` rather than the copy, and `wfix`'s check did not end
  in 10 minutes; a copy unfolds to its caller's text in one step).
- *Through the verified compiler: 46 of the gate's 71 programs* (was 42): `hof_rec` (3267906294), `wfix` (76), `loop_while`,
  `wfix_mem` — `loop_while` and `wfix_mem` as well because their other blocker lay inside the template (a test on a call of the
  function parameter), which is now written out.  All four are examples: no corpus program moved, so none to time.
- *Not in this step*: functions given that name the caller's variables (closures, §5.2) — no program of the gate needs them
  now (`loops` and `hof_cells` wait on functions that write).
- *The gate with `KQ_REFLECT=1`, on the fork, on the final tree (2026-11-01): everything passes* — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (38 / 38 / 40 / 57 / 42 s); **46
  programs through the verified compiler, 0 read but refused by the check**.
- *The tally after the step* (over the gate's 71 programs): calls of writing functions and reads in place inside expressions
  15, machine operations 10, loops that write and give a number 7, records and pairs 6, bytes 2, tests on a call giving back a
  boolean 2, `u64` 2, mutual recursion 1, the rest 2.  **The order that completes the most now**: loops that write and give a
  number (+3, 49 of 71), calls of writing functions and reads in place inside expressions (+4, 53), machine operations (+9, 62:
  the kernels), records (+2, 64), then bytes, `u64`, tests on calls giving back a boolean, the rest.  **Next: loops that write
  and give a number.**

**Step 11, loops that write and give a number — the design (2026-11-01).**  Seven programs of the gate have a recursive
function that writes the memory and gives back a number (`CF7D`'s `scan`, `CF460C`'s `search`, `CF61E`'s `rights`, `CF833B`'s
`layers`, `hof_cells`' `rounds`, `hw_mmio`'s `go`); in each the recursive call is the last step, given a memory made from the
newest one (`scan f (i + 1) .. (upd rDEG i d s)`, `let s1 := check .. s in .. search f .. s1`), and its caller calls it as its
last step too (`solve n nz s := scan n 1 nz 0 0 1 0 s`; `CF61E`: `rights n nz nz 0 (clear (S n) 0 (lefts n 1 nz s))`, the
memory it is given made by calls).  The tally counts three completed by this (`CF7D`, `CF460C`, `hof_cells`); `CF61E`, `CF61En`
and `CF833B` are expected as well, because the other reason it gives them ("a number function that writes the memory where it
is not read yet", on their `solve`) is this same last call; `hw_mmio` waits on machine operations.
- *Syntax*: two nodes of `sx`, both at the end only: `XRec cs args m` (the function itself, its counters after the first, its
  numbers, the memory `m`) and `XCall f cs args m` (a number function that writes, the same arguments); a body `FRecX x0 x1`
  (recursive on the first counter, a number, writing).  The numbers are worked out on the memory before `m`'s writes, as for
  `MRec` / `MCall` (what the text means when an argument reads `s` and the memory argument writes it).
- *Meaning*: `denote_x` gains the recursive call's meaning `recx` (`rec` and `recm` stay for the numbers and memories inside,
  which may not call it); `denote_f`'s `FRecX` is the `fix` over the counter, as for `FRec`, with `denote_x`.
- *KQL*: `XRec` the counters, numbers and memory, then `Eloop`; `XCall` the same, then `Ecall` and `Eret` of its result.
- *The statement*: a writing function's KQL gives the number with some end memory (`runx`, as now).  The end memory of a loop is
  its recursive call's, which that call's statement hides, so `endx` (the exact end memory) cannot be written any more.  But
  which end memory is reached depends only on the values the call is given — numbers, counters, the memory — never on the rest
  of KQL's variables: so `ctailx_ok` becomes **"there is an end memory such that, for every KQL environment the invariant
  holds of, the code gives the number and that memory"** — the existential outside the environment.  Then every case uses the
  lemmas as they are (`cexp_all`, `cmem_ok`, ... fix the result and the end memory before the continuation): a test's end
  memory is the one of the branch its test takes, a let's is its body's, `XRec`'s is the recursive call's (from the induction
  on the counter, `Hrecx`), `XCall`'s the callee's (from its statement).  No determinism lemma is needed.  `compile_f_ok`
  gains `FRecX` by the counter's induction, as `FRec`; `compile_f_okrx` (a copy of a writing template, from its two
  equations) as `compile_f_okr`, over `denote_x_recx_ext`.
- *Reifier*: a recursive function the number reader does not read is tried as `sx` in both branches (`FRecX`), the
  recursive call at the end read as `XRec`; a call of a writing function at the end as `XCall`; the number reader no longer
  reads a call of a writing function (it was refused by `wf` anyway), so the end of a body is tried by the `sx` reader.  The same
  in a template's copy.
- *`kitc.py`*: a writing copy's theorem is `compile_f_okrx`.
- *Not in this step*: a call of a writing function, or the recursive call, inside an expression (`rd .. (f s) + 1`,
  `acc + rec ..`): the caller's memory must then be dropped after the call — the next step.

**Step 11 done (2026-11-01): loops that write and give a number.**  Built as designed:
- *`KQR.v`*: `XRec`, `XCall`, `FRecX`; `denote_x` with `recx`; `ctailx` (`XRec`: the arguments, the memory, `Eloop`;
  `XCall`: the same, `Ecall`, `Eret`); `wfx` with the flag `rx`; **`ctailx_ok` restated: "there is an end memory such that,
  for every KQL environment the invariant holds of, the code gives the number and that memory"** — each case picks the end
  memory from the meaning alone (a test's branch, a let's body, the recursive call's from `Hrecx`, the callee's from its
  statement) and then uses `cexp_all`, `cmem_ok`, ... as they are; `endx` is gone.  `loopx_call_ok` (the loop step with the
  end memory its call reaches); `compile_f_ok`'s `FRecX` case by the counter's induction; `denote_x_recx_ext`;
  `compile_f_okrx` (a copy of a writing template from its two equations).  No determinism lemma, no new hypothesis; `KQR.v`
  compiles in 9 s.  Tests: `deg` (a loop reading a cell, writing the next, adding to a total) and `deg_top` (its caller, the
  last call `XCall`), the shape of their KQL (`Eloop`; `Ecall` then `Eret`), the recursive call inside an expression and in a
  plain body refused, `tdcopy` (`compile_f_okrx`); each theorem 0.002–0.003 s; `Print Assumptions` the same base.
- *The reifier*: a call of a writing function is no longer read as a number (it was refused by `wf`), so the end of a body
  goes to the `sx` reader: there a call of a writing function at the end is `XCall`, the recursive call at the end `XRec`; a
  recursive function whose branches the number reader does not read is read as `FRecX`, in a template's copy too.  The
  reason "a recursive function that writes the memory and gives back a number" is gone; a function that writes in a place not
  read yet gives "a number function that writes the memory where it is not read yet".  Tests (`KQRReify.v`): `rdeg` /
  `rdeg_top` (the trees of `deg` / `deg_top`), `rsearch` (a memory made by a call, a boolean let on it, the recursive call
  given that memory and a number chosen on the boolean: `CF460C`'s shape), `rtuse` (a copy of a writing template, read as a
  loop that writes, `compile_f_okrx`).
- *`kitc.py`*: a writing copy's theorem is `compile_f_okrx`.
- *The C*: of the 63 examples and corpus programs compared with step 10's, 57 have byte-identical C; the 6 that differ are the
  moved ones.  One difference from the translator's C, kept: a counter written as a number in a call (`search 64 ..` in
  `CF460C`'s `solve`, `query 21 ..` and `add 21 ..` inside `CF61E`'s loop) is a chain of additions (`CS` is one addition)
  where the translator writes the constant; clang folds them, as the timing shows.
- *Timed (best of 7 ms, the translator's / the verified compiler's)*: `CF7D` 21.80 / 21.55, `CF460C` 35.84 / 35.50, `CF61E`
  83.66 / 82.17, `CF61En` 52.24 / 52.39, `CF833B` 313.95 / 315.68 — the same.
- *Through the verified compiler: 52 of the gate's 71 programs* (was 46): `CF7D`, `CF460C`, `CF61E`, `CF61En`, `CF833B`,
  `hof_cells` — the six expected (the tally had counted three; the other reason it gave `CF61E`, `CF61En` and `CF833B` was the
  same last call).
- *The tally after the step* (over the gate's 71 programs): calls of writing functions and reads in place inside expressions
  13 (`loops`, `bytes`, `views`, `heap`, `hw_mmio` and the kernels' eight programs, most of them with machine operations as
  well), machine operations 10, records and pairs 6, bytes 2, tests on a call giving back a boolean 2, `u64` 2, records of
  other types 2, mutual recursion 1.  **The order that completes the most now**: records and pairs (+2, 54 of 71:
  `pair_ret`, `rec_pair`), calls of writing functions and reads in place inside expressions (+1, 55: `loops`), machine
  operations (+9, 64: the kernels and `hw_mmio`), then tests on calls giving back a boolean, `u64`, bytes, records of other
  types, mutual recursion.  **Next: records and pairs.**
- *The gate with `KQ_REFLECT=1`, on the fork, on the final tree (2026-11-01): everything passes* — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (37 / 38 / 39 / 56 / 43 s); **52
  programs through the verified compiler, 0 read but refused by the check**.


**Step 12, records and pairs — the design (2026-11-01).**  Six programs of the gate need them: `pair_ret` and `rec_pair`
(pairs only), `rec_ret` and `rec_state` (records of the program's own types, `Record span := mkspan {lo; hi}`), `views` and
`w64` (with other constructs).  The places: a record parameter (`inner .. (p : int * int) ..`, a loop's state), its fields
(`fst p`, `acc r`), taking it apart (`let '(h, l) := ..`), a record built and passed (`inner f (i + 1) (fst p + h, snd p + l)
s`), a function giving one back (`minmax` at the end of a loop, `fibp` after taking its own recursive call apart), a record
bound by a `let` and used through its fields (`let w := scan .. in .. hi w ..`).
- *Why the record must stay a value in the meaning.*  The translator states a record parameter as the constructor applied
  to its fields (§1.6) and its walk proves the rest by case analysis.  Here the check is conversion only, and Rocq has no eta
  for `prod` or for a non-primitive record: `g w` is not convertible to `g (fst w, snd w)`, nor `let w := c in .. hi w ..` to
  `match c with mkspan a b => .. b .. end`.  So the meaning holds the user's record value itself — `p`, `w` — and its fields
  are the user's own match on it; KQL holds the fields (D15), and the invariant says each field's atom holds that field.
- *Record types*: a program's record types are **descriptors** given to the meaning as parameters, as the callees are: a type
  `T`, its number of fields `rn`, its constructor on a list of numbers `rmk`, and its match `relim : forall P, T -> (list
  i63 -> P) -> P` — for `prod`, `fun P v k => match v with (a, b) => k [a; b] end`, so a field is `relim v (fun l => nth j l
  0)`, which reduces to the user's `fst p` / `hi w` (both are that match).  A descriptor's laws — building then taking
  apart gives the fields back, `relim v k = k (relim v id)`, `rn` fields — are what the proof needs of it; for each program
  they are proof terms by a dependent match (`match v with (a, b) => eq_refl end`), checked by the kernel like the copies'
  equations.  Records of numbers only (D15); a pair and a record of the program's own type are the same construct.
- *Signatures*: the parameters after the counters become a list of kinds, `KNum`, `KBool`, `KRec r` (record type `r`), in
  the user's order — booleans as parameters come with it (step 5 deferred them to this step); the result gains `RRec r`.
  The meaning's type is still the user's curried type, so the check stays a conversion.
- *Syntax*: a sort of records (mutual with the numbers): a record variable, the constructor on numbers, a call or the
  recursive call giving one back, tests and lets around one, taking one apart; among the numbers: a field of a record
  variable, a `let` of a record, taking a record apart (`let '(a, b) := r in e`); a call's arguments become a list of
  numbers, booleans and records.  A function's body may be a record (recursive on its counter or plain).
- *KQL*: a record is its field atoms; passed as arguments, its fields.  **A function giving back a record returns its first
  field and writes the others into cells `0 .. rn-2` of the slot block (63), the last one first (D16); the caller saves those
  cells before the call, reads the fields after it and writes the saved values back, cell 0 first.**  Its statement: the
  first field, with the end memory those writes make; the caller's memory is then the text's again by three of the memory
  laws (`upd_upd`, `upd_rd_id`, `rd_upd_ne`: cell 0 written back over its write gives the memory with cells 1 .. written,
  and so on down) — so a record of any number of fields needs no new law (F43 asked for the commuting law, D27; this order
  of writing back does not need it).  The laws are `KQSpec.real_laws`, already in the trusted base (§1.10); the verified
  compiler's theorem gains it as an assumption for programs that give back records.  Reading a slot cell back needs the
  block to have room: every statement of a program takes `rn - 1 < kq_len 63` for its largest record (the translator
  takes `1 < kq_len 63`, the driver provides it).
- *Proof*: the invariant gains the record variables (each field's atom holds that field); the mutual lemma gains the record
  sort and the argument lists; the callee assumption is stated over argument values of each kind (a record argument is a
  value, its KQL arguments its fields), so passing a record variable needs no eta.
- *Reifier*: kinds read off the parameter types (a record type: an inductive with one constructor whose fields are numbers;
  `prod int int`); the program's descriptors made from the types met, with their law terms, defined by `kitc.py` like the
  copies' meanings; `fst`, `snd` and a record's own projections as fields; a match on a record; a record built.
- *Built in three parts*, each with its tests and the gate green: (1) kinds in signatures and argument lists (numbers and
  booleans; the C of every program unchanged), (2) record parameters, fields, records built and passed, lets and matches,
  (3) records given back through the slot block.


**Step 12, parts 1 and 2 done (2026-11-01): kinds in signatures; records and pairs as values.**
- *Part 1* (`d84bfe0`): the parameters after the counters are a list of kinds in the user's order — numbers, booleans,
  records — and a call's arguments numbers, booleans and records (a boolean passed as 1 or 0, a record as its fields);
  `absn` / `appn` bind each kind into its own environment, the parameters' atoms are found by kind and width (`kpos`,
  `katoms`); a chain of tail calls is merged only when every argument is a number.  The C of every program unchanged (63 of
  63 compared).  Test: `bcount` (a boolean passed on negated to the recursive call, one chosen by the caller), read from text
  too (`rbcount`).
- *Part 2* (`a084907`): the program's record types are a class instance given to the meaning (`RecTypes`: each type, its
  constructor on the list of its fields, the user's own match; `RecLaws`: the match gives its continuation the fields, there
  are as many as the type says, the constructor's fields are what it was built of — per program by a fixed script); the
  meaning holds record values (`VRec`), KQL their fields (the invariant's last part).  Syntax: a record sort (`RVar`,
  `RMk`), a field (`SFld`), a let of a record (`SLetR`), a record taken apart (`SMatchR`), a record argument (`SConsR`).
  Every field and match goes through `rmatch v F`, equal to `F (vflat v)` by the laws, so no kind check is needed where a
  record is read.  A record passed as an argument is built in place; passing a record variable as it is needs a typing
  context in `wf` and is not read yet (refused by `wf`: a gap of this step).  The reifier: the record types read off the
  reached functions' types (an inductive with one constructor whose fields are numbers; `prod int int`), `fst` / `snd` and
  the program's own projections written out (a field is then the record taken apart), a match on a record, a let of one, a
  constructor; `kitc.py` writes the instance (`NAME_rt` / `_ro` / `_rd` and the laws) and passes it to the theorems
  explicitly.  Tests: `pinner` / `pouter`, `pmatch`, `plet` (`KQR.v`); `rpinner` / `rpouter` (a pair as a loop's state) and
  `rsinner` / `rsouter` (a record of the program's own type) read from text.  `KQR.v` compiles in 11.6 s; `Print
  Assumptions` the same base (the cast of a record value to its type uses `Eqdep_dec.UIP_refl_nat`, a theorem).
- *Through the verified compiler: 54 of the gate's 71 programs* (was 52): `rec_pair`, `rec_state` (examples, nothing to
  time); the C of every other program unchanged.
- *The gate with `KQ_REFLECT=1`, on the fork, on `a084907` (2026-11-01): everything passes* — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (37 / 39 / 39 / 57 / 43 s); **54
  programs through the verified compiler, 0 read but refused by the check**.
- *Left in step 12*: part 3, records given back through the slot block (`pair_ret`, `rec_ret`), as designed above.

**Step 12, part 3 in detail — the design (2026-11-01).**
- *Signature*: `sig` gains `sq : option nat`, a record of type `ri` as the result; the meaning's type ends in `RT ri` (the
  user's `int * int` or `span`), so `ntype` / `absn` / `appn` are generalized over the result type.
- *Syntax*: records gain `RCall ri f cs args`, a call of a function giving back a record, wherever a record is read (a `let`, a
  record taken apart, an argument).  A function giving back a record has a body of its own sort `sbr`: `BRet x` (a record built,
  or given by a call), `BRec cs args` (the function itself at the end: a loop), `BMatchRec cs args b` and `BLetRec cs args b`
  (the function itself not at the end, taken apart or bound: `fibp`'s `let '(a, b) := fibp m in ..`), and the lets, tests and
  counter match of the other tail sorts; bodies `FRecR` / `FPlainR`.
- *Meaning*: `denote_br` gives the record value itself (`RT ri`), the recursive call's meaning `recr` of that type, so the
  user's `match fibp m with (a, b) => .. end` is literally what the meaning reduces to; `BRet x` is `to_rt ri` of the record's
  value (the constructor on its fields reduces to the user's `(lo, hi)` or `mkspan a b`).
- *KQL*: at the end, the fields after the first written into cells `0 .. rn-2` of the slot block, the last one first, then the
  first field returned; a call giving back a record (another function, or the function itself not at the end): the cells
  saved into fresh variables, the call, the cells read into fresh variables (the fields), the saved values written back, cell
  0 first.
- *Statement*: a function giving back a record returns its first field and ends with the memory those writes make
  (`callm`: `wslot 0 (tl fields) M`); every theorem of a program takes `slot_room` (for each record type of more than one
  field, `rn - 1 <= kq_len 63`), which the driver provides, as it provides `1 < kq_len 63` for the translator's two results.
- *Proof*: after the save, the call, the reads and the write-back, the caller's memory is the one before, by `upd_upd`,
  `upd_rd_id` and `rd_upd_ne` (`wback`); the fields are read back by `rd_upd_eq` (the cell inside the block: `size_ge_len`
  and `slot_room`).
- *Not in this part*: a record variable given back or passed as it is (`BRet (RVar ..)`: the typing context part 2 left for
  later); the function itself giving back a record inside a number (`fst (fibp m) + 1`); a template giving back a record.
- *Reifier*: the result type read into `sq`; a function whose result is a record read as `FRecR` / `FPlainR`; `let '(a, b)
  := f ..`, `let w := f ..` and a record argument made by a call read as `RCall`; `kitc.py` prints the signature's sixth part.

**Step 12, part 3 done (2026-11-01): records given back.**  Built as designed:
- *`KQR.v`*: `sig.sq`; `RCall`; the sort `sbr` (`BRet`, `BRec`, `BMatchRec`, `BLetRec`, `BLet`, `BLetB`, `BLetC`, `BLetR`,
  `BMatchR`, `BIf`, `BIfB`, `BMatch`), `denote_br` (the record value itself, `RT ri`), `ctailr` (`cput`: the fields after the
  first into cells `0 .. rn-2`, the last first, then `Eret` of the first), a call giving back a record compiled by `ccallr`
  (the cells saved, the call, the cells read, `cback` writing the saved values back cell 0 first); `wfbr` (at the end a
  record built or given by a call, of the type the function gives back); `FRecR` / `FPlainR`.  Proved once:
  `ccallr_ok` (after the call the caller's memory is the one before and its continuation gets the fields) over `wback`,
  `rd_wslot_seq`, `rd_wslot_lt` (the laws `upd_upd`, `upd_rd_id`, `rd_upd_ne`, `rd_upd_eq`, the cells told apart by
  `ofn_inj`, the room by `size_ge_len` and `slot_room`), the `RCall` case of `cexp_all`, `ctailr_ok`, `compile_f_ok_rec`;
  `slot_room` is the first premise of `callee_ok`, so every theorem of a program takes it and passes it to its callees.  No
  new law: the order of writing back makes the commuting law (D27) unnecessary for records of any number of fields.
  **What every theorem now rests on**: `compile_f_ok` uses the memory laws in its `RCall` case, so `Print Assumptions` of every
  program's theorem lists `KQSpec.real_laws` — one theorem for all programs, so programs without records too.  It was already
  in the route's trusted base (§1.10: `kit_function_correct` rests on it), so the end-to-end trust is unchanged; the
  records of steps 1–11 that say "no memory law" describe the theorems before this step.  Tests: `minmax` (a pair at the end
  of a loop), `fibp` (the function itself taken apart before the end), `prounds` (a loop taking both apart, a counter written
  as a budget), `plast` (a pair bound by a let, read through its fields, the fields given to a second call), a record
  variable given back refused, a tree with its fields the other way round refused; each theorem 0.002–0.005 s; `KQR.v`
  compiles in 8.7 s.
- *The reifier*: `read_sig` reads a record of the program's types as the result; `reify_br` reads a body giving back a
  record (the function itself at the end `BRec`, taken apart or bound before the end `BMatchRec` / `BLetRec`); `reify_r`
  reads a call of a function giving back a record (`RCall`) and writes a helper giving one back out; the number reader no
  longer reads such a call as a number.  A template giving back a record is not read yet.  Tests: `pair_ret`'s text (the trees
  exactly the hand-written ones) and `rec_ret`'s (a record of the program's own type, its projections written out), every
  theorem in milliseconds.
- *`kitc.py`*: the signature's sixth part (`None`, or `Some i` for a record of type `i`, printed as a letter `a .. h`); an
  entry giving back a record falls back to the translator (`main` takes numbers); **the driver provides the slot block for
  every program with record types** (`max(8, rn - 1)` cells of its largest record), which the theorems' `slot_room` premise
  needs — `rec_pair` and `rec_state` therefore gain the slot block's two lines in their driver.
- *The C*: of the 63 examples and corpus programs compared with part 2's, 59 have byte-identical C; `pair_ret` and `rec_ret`
  are the moved ones; `rec_pair` and `rec_state` differ only by the two lines of the slot block in their driver.
- *Through the verified compiler: 56 of the gate's 71 programs* (was 54): `pair_ret`, `rec_ret` (examples: nothing to time).
- *The tally after the step* (over the gate's 71 programs): calls of writing functions and reads in place inside expressions
  13 (`loops`, `bytes`, `views`, `heap`, `hw_mmio` and the kernels' eight programs), machine operations 10, bytes 2, `u64` 2
  (`views`, `w64`: the `u64` record and its constructors are what is left of "records"), tests on a call giving back a boolean
  2, mutual recursion 1 (with a local `fix`).  **The order that completes the most now**: calls of writing functions and reads
  in place inside expressions (+1, 57 of 71: `loops`), machine operations (+9, 66: the kernels and `hw_mmio`), bytes (+1,
  67), tests on calls giving back a boolean (+1, 68: `heap`), then `u64` (+2, 70), mutual recursion with a local `fix` (+1,
  71).  **Next: calls of writing functions and reads in place inside expressions.**
- *The gate with `KQ_REFLECT=1`, on the fork, on `6fda012` (2026-11-01): everything passes* — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (37 / 38 / 40 / 56 / 44 s); **56
  programs through the verified compiler, 0 read but refused by the check**.

**Step 13, functions given that name the caller's variables — the design (2026-11-01).**  The tally after step 12 put `loops`
under "calls of writing functions and reads in place inside expressions".  Read part by part (each of its lines as a function
of its own), its memory part is read already (`let s2 := loop_up_m .. s .. in .. rd 1 (lo + 2) s2`); what is not read is a
function given to `loop_up` / `loop_find` that names variables of the caller (`fun i acc => acc + rd 0 i s * b`: the
memory `s` and the number `b`) — the captures of §5.2, which the translator has and step 10 left out (F56).  So this step
is captures.
- *The reifier, and nothing else*: a call of a template whose functions given name the caller's variables gets a copy whose
  meaning takes those variables as parameters — `fun k b i acc s => loop_up_go k i acc (fun i acc => acc + rd 0 i s * b)`:
  the template's counters, the captured numbers and booleans in the order they first appear, the template's other
  parameters, the captured memory last (only when the template takes no memory: one memory per function, linearity).  The
  call passes the caller's variables (`C (kq_nat (hi - lo)) b lo 0 s`), which is the caller's text up to delta and beta, so
  the caller's check is unchanged.  The copy is read as a copy is read now: the captured variables are entries of the
  context after the copy's own, the function given written out names them, the recursive call passes them on; its theorem
  is `compile_f_okr` with its two equations by conversion (step 10).  Two functions given are the same copy when they are
  the same term once their captured variables are numbered in the order they first appear, and of the same kinds.
- *Nothing in `KQR.v`*: a copy with captures is an ordinary function of `S`; nothing is added to what is proved or trusted.
- *Not in this step*: capturing a counter, a record, or a variable bound by a match; capturing the memory when the template
  takes a memory too (two memories at once — refused by design, §0.5's third refusal, when both are used).

**Step 13 done (2026-11-01): functions given that name the caller's variables.**  Built as designed, in the reifier only
(`KQR.v` and `kitc.py` unchanged):
- *Reading*: the variables a function given names (`fvs`, in the order they first appear) are numbered `0 ..` (`abs_caps`),
  so the same function at two calls is the same copy; the call sites carry their kinds, read off the binders' types
  (`sites`, a number, a boolean or the memory; any other kind: no copy, so the caller is not read); the copy table keeps
  the kinds with the functions given.  The copy's signature is the template's with the captured numbers and booleans before
  its other parameters and the captured memory last; its context has the captured variables after `CSelf`, where the
  template's own text cannot name them; a function given, written out, names them (`capsub`); the recursive call passes
  them on (`with_caps`); a call of the template passes the caller's variables (`tc_of`).  The copy's meaning
  (`copy_meaning`) takes them as parameters in that order; a copy without captures is the same term as before.
- *Tests* (`KQRReify.v`): `rcap` (the first two lines of `loops`: a sum whose function names the caller's number and memory,
  a search whose test names a number and the memory), both copies read with the captured variables as parameters, each
  checked by `compile_f_okr` with its two equations by conversion, the caller by `compile_f_ok`; each theorem 0.001–0.004 s.
- *The C*: of the 63 examples and corpus programs compared with step 12's, 62 have byte-identical C; `loops` is the moved one.
- *Through the verified compiler: 57 of the gate's 71 programs* (was 56): `loops` (185; an example: nothing to time).
- *The tally after the step* (over the gate's 71 programs; the 14 not read): "a number function that writes the memory where
  it is not read yet" 12 (the reason scan's flag, which F56 found wrong for `loops`: to be confirmed program by program),
  machine operations 10 (the kernels' eight programs, `hw_mmio`, `heap`), bytes 2, tests on a call giving back a boolean 2,
  `u64` 2 (with its record), mutual recursion 1 (with a local `fix`).  **The order that completes the most now**: machine
  operations (+9, 66 of 71: the kernels and `hw_mmio`, if their flag is the scan's), tests on calls giving back a boolean
  (+1, 67: `heap`), bytes (+1, 68), `u64` (+2, 70), mutual recursion (+1, 71).  **Next: machine operations** (their
  programs read part by part first, F56).
- *The gate with `KQ_REFLECT=1`, on the fork, on `b4899ef` (2026-11-01): everything passes* — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (37 / 38 / 40 / 56 / 43 s); **57
  programs through the verified compiler, 0 read but refused by the check**.

**Step 14, machine operations — the design (2026-11-01).**  Ten programs of the gate use the machine's operations (§1.8):
the five kernels' eight programs, `hw_mmio`, `heap` (`kq_grow`, `kq_size`).  KQL has them already, with their meaning:
`Ehw o args k` (an operation on the memory, `hw_sem o vs M` — `hw_store a b c M`, `kq_grow h n M`, ..., each the kit's own
function), `Ehwf o x args k` (a number the machine gives without a memory, `hwf_sem`: `hw_addr`, `hw_irq_info`, ...),
`Eksize x h k` (a block's size now); the generator emits the first two as calls of the external functions whose C bodies
are assumed by `hw_law` / `hwf_law` (§1.10).  So `S` takes them as KQL does:
- *Syntax and meaning*: `MHw o args m` among the memories, `hw_sem o (numbers of args) (memory of m)` — the numbers worked
  out on the memory before `m`'s writes, as for `MUpd`; `SHwf o args` among the numbers, `hwf_sem o (numbers)`; `SSize h`,
  `KQRun.kq_size h s` on the newest memory.  `hw_sem HStore [a; b; c] s` is `hw_store a b c s` by computation, so the
  user's text is what the meaning reduces to and the check stays a conversion.
- *Well formed*: as many numbers as the operation takes (`hw_arity`, `hwf_arity`); `SSize` only where there is a memory.
  A choice with a size or a machine number in it is a jump, as in the translator (its `choice_ok` has neither).
- *Proof*: one case each, by `K_hw`, `K_hwf`, `K_size`, which have the shape of `K_st` / `K_op` / `K_ld`; nothing is
  assumed of the operations in `KQR.v` — what they do is `hw_sem`, and what the machine does is `hw_law` / `hwf_law`, below,
  as for the translator.
- *Reifier*: the translator's two tables (the Rocq constant, the operation, its number of arguments before the memory);
  `kq_size` with the newest memory.  The reasons scan stops naming them.
- *`kitc.py`*: a program that shares blocks with another processor (`kq_shared`, §9.4: plain accesses to them refused)
  stays with the translator until the verified path has that rule — none of the gate's programs does (`lock` does).
- *Expected*: the kernels and `hw_mmio`, if their remaining reason ("a number function that writes the memory where it is
  not read yet") is the scan's (F56) — read part by part once the operations are read.

**Step 14 done (2026-11-01): machine operations.**  Built as designed:
- *`KQR.v`*: `MHw`, `SHwf`, `SSize`, their meanings (`hw_sem`, `hwf_sem`, `kq_size`), their KQL (`Ehw`, `Ehwf`, `Eksize`), well
  formed when the operation gets its number of arguments and a size has a memory; one proof case each, in `cexp_all` and
  `cmem_ok` (by `K_hwf`, `K_size`, `K_hw`), the others in the lemmas over the syntax.  No new hypothesis; `Print Assumptions`
  the same base (the machine's operations were in it already: KQL's meaning names them).  Tests: `mmio` (`hw_mmio`'s loop: a
  store to a device, a fence, a load into a cell, the cell read), `hsz` (a machine number and a block's size), `hgrow`
  (`kq_grow`); an operation given too few arguments and a size without a memory refused; each theorem 0.001–0.006 s; `KQR.v`
  compiles in 9.0 s.
- *The reifier*: the translator's two tables and `kq_size`; the reasons scan no longer names them.  Test `rhw` (`hw_mmio`'s
  loop, and a caller passing a machine number and a block size and a grown block, its helpers written out): the trees
  exactly the hand-written ones, the theorems in milliseconds.
- *`kitc.py`*: a program with `kq_shared` stays with the translator (`lock`, outside the gate).
- *The kernels*: their eight programs are read in full — the scan's "a number function that writes the memory where it is
  not read yet" was its own again, for them and for `heap` (and `heap`'s "a test on a boolean that is not read" too): F56's
  rule held.  Each kernel was built by the verified compiler and started in QEMU on this machine apart from the gate (which
  builds them): all five pass every check (the answer 0; `irqnow` 10 interrupts handled by Rocq at once, `fault` its page
  mapped by Rocq, `smp` two processors), under QEMU's processor and under KVM.  **The kernels' build, proofs included, is now
  10 / 10 / 10 / 12 / 11 s** (irqnow, fault, smp, own, kernel), against 37 / 38 / 40 / 56 / 43 s with the walk the step
  before — the verified compiler's per-program step in place of the search (§7.3's numbers were the walk's).
- *The C*: of the 63 examples and corpus programs compared with step 13's, 61 have byte-identical C (compared on this
  machine: the heavy-run machine was off the network for a while); `heap` and `hw_mmio` are the moved ones.
- *Through the verified compiler: 67 of the gate's 71 programs* (was 57): `heap`, `hw_mmio` and the kernels' eight (examples
  and kernels: nothing to time).
- *The tally after the step* (the four not read): bytes 2 (`bytes`, `views`: `rd8` / `upd8`), `u64` 2 (`views`, `w64` —
  `w64`'s "test on a call giving back a boolean" is `u64_ltb` / `u64_eqb`), mutual recursion 1 (`mutual`, with a local
  `fix`), and the scan's flag on `bytes` and `views`.  **The order that completes the most now**: bytes (+1, 68 of 71:
  `bytes`), `u64` (+2, 70: `w64`, `views`), mutual recursion (+1, 71).  **Next: bytes.**  (The tally script's greedy order
  loops when no category completes a program; read off by hand this time.)
- *The gate with `KQ_REFLECT=1`, on the fork, on `6241ac9` (2026-11-01): everything passes* — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (10 / 10 / 10 / 12 / 11 s); **67
  programs through the verified compiler, 0 read but refused by the check**.

**Step 15, bytes — the design (2026-11-01).**  `bytes` and `views` read and write single bytes (`rd8`, `upd8`; `rd16`, `upd16`
are definitions over them).  Step 8 left them out of the helpers written out on purpose, so that each stays one byte access
(§6.1: 74 against 136 ms) — and KQL has that access: `Ekld8` / `Ekst8`, whose meaning is `KQRun.rd8` / `upd8` themselves
(the generator's C is one byte load or store, `KQBytes.v`).  So, as step 7 did for 4-byte cells: `SRd8 h i` among the numbers
and `MUpd8 h i v m` among the memories, meaning `rd8` / `upd8` of the user's own text, compiled to `Ekld8` / `Ekst8`; one proof
case each by `K_ld8` / `K_st8`, the shape of `K_ld32` / `K_st32`; the reifier reads `rd8` / `upd8` (still not written out)
and writes `rd16` / `upd16` out over them, as the translator does.  A choice with a byte read in it is a jump, as in the
translator (its `choice_ok` counts `rd` and `rd32` only).  Expected: `bytes` (+1); `views` needs `u64` too.

**Step 15 done (2026-11-01): bytes.**  Built as designed: `SRd8`, `MUpd8` (`KQR.v`: meanings, KQL, well-formedness, one proof
case each, `Print Assumptions` the same base; tests `bsum`, `bfill`, their KQL one `Ekld8` / `Ekst8` each, each theorem in
milliseconds); the reifier reads `rd8` / `upd8` and writes `rd16` / `upd16` out over them (test `hb8`: a byte and a halfword
read, a byte and a halfword written).  The C: 62 of 63 byte-identical, `bytes` the moved one.  **68 of the gate's 71
programs through the verified compiler** (was 67): `bytes` (an example: nothing to time).  The three not read: `u64` 2
(`views`, `w64` — and `w64` passes and gives back `u64` variables as they are, the record variable that parts 2 and 3 of
step 12 left out: a record variable's type is not known to `wf`), mutual recursion 1 (`mutual`, with a local `fix`).
**Next: `u64`.**  The gate with `KQ_REFLECT=1`, on the fork, on `93b17a4` (2026-11-01): everything passes — `make.sh`
`core-ok`; examples 27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (10 / 10 / 10 / 12 /
11 s); **68 programs through the verified compiler, 0 read but refused by the check**.

**Step 16, `u64` — the design (2026-11-01).**  `w64` and `views` compute on `u64` (§1.3): a record of two numbers (`w_lo`,
`w_hi`) with primitive projections, whose operations are one sealed function, `w64_op o a b` (`u64_add a b := w64_op W_add a b`,
`u64_ltb a b := w_lo (w64_op W_ltu a b) =? 1`, ...), and KQL's one instruction `Ew64` (the two halves of each operand to the two
halves of the result).  Read part by part, they need three things, built in this order:
- *(a) Record variables with their types.*  `w64` passes `u64` variables as they are (`stream f st1 ..`) and gives one back
  (`| O => h`): the record variable that parts 2 and 3 of step 12 left out, because `wf` does not know a record variable's
  type.  `wf` gains the types of the record variables in scope (`rk`, one record type each, the nearest first: a parameter's
  from its kind, a `let`'s and a match's from what is bound); `RVar i` then has the type `nth i rk`, so it may be an argument
  of that kind and may be given back.  The proof gains the matching fact of the meaning: each record value in scope has the
  type `rk` says (`kind_of`), kept by every binder.
- *(b) Records bound in memories.*  Written out, `view_upd64 h i (u64_mul ..) s` binds the `u64` by a `let` and writes its two
  halves: `MLetR` / `MMatchR` among the memories and `XLetR` / `XMatchR` among the numbers made after memories, as `SLetR` /
  `SMatchR` are among the numbers.
- *(c) The operation and its fields.*  `RW64 o a b` among the records, meaning the record built from the fields of
  `w64_op o (mk_u64 a0 a1) (mk_u64 b0 b1)`, the `aᵢ` / `bᵢ` the operands' fields: no type equality is needed, and because `u64`
  has definitional eta (primitive projections), this is the user's `w64_op o a b` by conversion.  Compiled to `Ew64` on the
  operands' field atoms, its result the two fields; one proof case by `K_w64`; well formed when the operands and the result
  have two fields.  The reifier reads `w64_op` as `RW64` and a primitive projection (`w_lo r`) as the field of a record taken
  apart; `u64` is a record type of the program like any other (`rec_shape` takes it: one constructor, two numbers), and
  `kitc.py`'s instance for it is the one it writes for a record (its match is the projections, its laws by `reflexivity`).
- *Expected*: `w64` and `views` (+2, 70 of 71).  The gap of (a) also closes for the program's own records.

**Step 16 done (2026-11-01): `u64`.**  Built as designed, with one addition found by reading the two programs part by part:
- *(a) Record variables with their types.*  `wf` and its relatives take `rk`, the types of the record variables in scope, the
  nearest first (a parameter's from the signature, `rk0`; a `let`'s from what it binds, `rtype`); `RVar i` is well formed
  when `i` is in scope, of type `nth i rk`, so it may be an argument of that kind or be given back.  The proof carries the
  matching fact of the meaning, `rtyped renv rk` (`map kind_of renv = map KRec rk`), kept by every binder (`rtyped_cons`,
  `kind_denote_r`) and true at a body's start (`rtyped0`, from the arguments' kinds).  Tests: `ppass` (a pair variable given
  to another function as it is), `pswap` (given to the recursive call as it is or swapped, and given back as it is: `w64`'s
  shape).
- *(b) Records bound in memories.*  `MLetR` / `MMatchR` among the memories, `XLetR` / `XMatchR` among the numbers made after
  memories; their cases the shape of `SLetR` / `SMatchR`'s.
- *(c) The operation.*  `RW64 ri o a b` among the records, meaning `VRec ri` of the fields of
  `w64_op o (u64_of_l (fields of a)) (u64_of_l (fields of b))`, the user's `w64_op o a b` by the definitional eta of `u64`;
  compiled to one `Ew64`; one proof case by `K_w64` (`ra`, `rb` the operands' fields made a `u64`, the result's fields by
  `rl_mk`); well formed when the result and both operands are of types of two fields.
- *Found by reading part by part (F56)*: written out, a helper giving a record binds the arguments that are not plain by
  `let`s (`u64_of_int (rd 0 i s land 255)`, `u64_of_halves (rd32 ..) (rd32 ..)`), and `mix` is a chain of `u64` lets, so
  records under lets stand inside operands and arguments.  `RLet` (a number) and `RLetR` (a record) among the records read
  them wherever a record stands; `rtype` is now recursive (a record under lets has the type of the record they end with).
- No new hypothesis; `Print Assumptions` the same base.  `KQR.v` compiles in 17 s (13 s at step 15).  Tests (`U64Test`, `u64`
  a record type of the program): `uadd` (its KQL starts with one `Ew64`), `ultb` (a comparison as a test), `ufold` (`views`'
  `fold_words`), `uput` (`view_upd64`: a `u64` bound by a let in a memory, its halves written), `uwr` (a number after a memory,
  a `u64` let and a match), `ulets` (lets in both operands); refused: a record variable out of scope, an operation not the
  text's; each theorem 2–18 ms.
- *The reifier* reads `w64_op` as `RW64` (`u64` in the program's record table, as any record of two numbers), a primitive
  projection as a field (`SFld` of a variable, else the record taken apart), a `let` inside a record (`RLet` / `RLetR`),
  record lets and matches in memories and in numbers made after memories.  Tests: `w64`'s text (`urfnv`, `urstream`, `urw64`)
  and `views`' memory functions (`urvfill`, `urvfold`, `urviews`), each theorem by `compile_f_ok`, 3–38 ms.  `kitc.py`
  unchanged: the instance it writes for a record is `u64`'s.
- The C: 61 of 63 byte-identical, `w64` and `views` the moved ones.  **70 of the gate's 71 programs through the verified
  compiler** (was 68): `w64`, `views` (examples: nothing to time).  The one not read: `mutual` (two functions of one `Fixpoint
  .. with ..` calling each other on the counter's predecessor).  **Next: mutual recursion.**
- The gate with `KQ_REFLECT=1`, on the fork, on `6c6f038` (2026-11-01): everything passes — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (10 / 10 / 10 / 12 / 12 s); **70 programs
  through the verified compiler, 0 read but refused by the check**.

**Step 17, mutual recursion — the design (2026-11-01).**  `mutual`'s `ping` and `pong` are one `Fixpoint .. with ..`: each
calls the other (or itself) on the counter's predecessor; `rounds` is not read only because it calls `ping` (read part by part,
F56).  The meaning of a function is checked by conversion against the user's constant, and the user's `ping` is a fixpoint of
two bodies, which no single-body fixpoint converts to; so the block is not given a meaning of its own -- it is compiled as one
function and its meaning is made of the user's functions:
- *The block function.*  The members (number functions of one signature, for now) become one function with one counter more,
  the *selector*, last among its counters: its body is `FRec` of a match on the selector over the members' bodies, and a call of
  member `j` on the predecessor is the recursive call `SRec` given the selector `CNat (SInt j)` (a counter that does not grow:
  `flat`).  So a tail call between members is a loop, in KQL as in C.
- *Its meaning.*  `blk hs` (`KQR.v`, new definition): the function of one counter more that, at a counter `n`, takes the
  parameters and applies member `sel` of the list `hs` at `n` -- written with its parameter lambdas outside the choice, as the
  meaning of a body is, so the choice and the match on the selector stand in the same place.  With `hs` the user's `[ping;
  pong]`, its two equations (at `0`, and at `S n` with the recursive call `blk hs n`) hold by conversion: unfolded at `S n`,
  `ping` calls `pong n`, and `blk hs n` at selector `1` is `pong n`.  So the block function's theorem is `compile_f_okr` (step
  10's theorem for a function given by its equations): no new theorem.
- *The members.*  Each is one call of the block function with its selector (`FPlain (SCall ..)`), meaning `blk hs n j ..` --
  the user's member by conversion; its theorem is `compile_f_ok`.  A caller calls a member as any function.
- *The reifier* reads a constant whose body is a fixpoint of several bodies as the block function (a function of its own, as a
  template's copy is, with its meaning `blk [..]`) and its members; `kitc.py` proves the block function by `compile_f_okr`.
- *Expected*: `mutual` (+1, 71 of 71).  Not in this step: members of different signatures, or giving back a memory or a record.

**Step 17 done (2026-11-01): mutual recursion.**  Built as designed:
- *`KQR.v`*: `blk` (with `sel_app`, the choice of member applied in each branch, and `vals_rev`, the parameters' values from
  a body's numbers, booleans and records) — definitions only: no new theorem, no change to the syntax, the meanings or the
  proofs.  Test: `mping` / `mpong` (`mutual`'s two functions) as one function with a selector, `mblk = blk [mping; mpong]`
  proved by `compile_f_okr` from its two equations by conversion, each member one call of it proved by `compile_f_ok`; the
  block function's KQL is one loop (the test between a call of `mping` and one of `mpong` merged into one call, step 9); each
  theorem 3–5 ms; `Print Assumptions` the same base.
- *The reifier*: a constant whose body is a fixpoint of several bodies (number functions of one signature, numbers and
  booleans as parameters, recursive on the first counter) is read as the block function `<first member>__cblk`, a function
  of its own as a template's copy is: each member's body lifted to make room for the selector, the members' fix binders read
  as `CSib j`, a call of member `j` on the predecessor the recursive call given `CNat (SInt j)`, the branches nested under
  matches on the selector (`nest_sel`); its meaning `@blk no_recs .. [tFix mfix 0; ..]`, the fixpoint's own bodies (so a member
  the program does not name, as `pong`, needs nothing), the first member's type as the list's; each member reached is one call
  of it (`member_body`).  Test: `mutual`'s text (`qping`, `qpong`, `qrounds`), the block's tree the hand-written one, each
  theorem 3–6 ms.  `kitc.py` unchanged: the block function is proved as a copy is (`compile_f_okr`).
- The C: 62 of 63 byte-identical, `mutual` the moved one.  **All 71 of the gate's programs through the verified compiler**
  (was 70): `mutual` (an example: nothing to time).  §12.V's tally is done.  **Next: the acceptance of §12.V's plan (2)** —
  the trusted base (`Print Assumptions`), the check's time, the construct table through the verified compiler — and then the
  walk retired (the one program known to stay with the translator: `lock`, outside the gate, a block shared with another
  processor).
- The gate with `KQ_REFLECT=1`, on the fork, on `c6a1d3e` (2026-11-01): everything passes — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (10 / 10 / 10 / 12 / 11 s); **71 programs
  through the verified compiler, 0 read but refused by the check, 0 not read**.

**Step 18, blocks shared with another processor — the design (2026-11-01).**  `hw/lock.body` and `hw/lock_ap.body` (two
processors, one counter under a spinlock; outside the gate) declare `kq_shared` and are sent to the translator, the one
program family the verified compiler leaves to the walk.  The guarantee is the same on both routes: each program is proved as a
sequential function of the memory, for every value a marked operation gives back (§9.4) — the compiler stays sequential, as
every verified compiler does (CompCert, CakeML / Pancake, Bedrock2, Jasmin: none proves shared-memory concurrency; the
Pancake route's recommended pattern, components that share only declared regions through operations whose semantics lets
the memory change, is the one built here).  What the verified side lacks is the translator's rule that keeps the sequential
model honest: in a program that declares `kq_shared`, a plain access to a narrow block (`rd32`, `rd8`, `upd32`, `upd8`)
names its block by a number written where it is used and not shared.  So:
- *`KQR.v`*: `sh_ok sh b`, the rule as a function of the syntax tree (every `SRd32` / `SRd8` / `MUpd32` / `MUpd8` of the
  body: its block a literal `SInt n` with `n` not in `sh`; nothing asked when `sh` is empty).  A check beside the theorem, as
  `wf` is: `compile_f_ok` is unchanged, the per-program file adds one lemma per function, `sh_ok kq_shared body = true`,
  proved by `eq_refl` — the kernel checks the rule on the tree whose meaning it checked.
- *The reifier* reports a function that breaks it (its reason the translator's message); *`kitc.py`* no longer sends a
  `kq_shared` program to the translator: it reads it, and proves the rule beside each function.
- *Expected*: `lock` and `lock_ap` through the verified compiler, built and booted on two processors (200 000); no gate
  program changes.  The protocol itself (the lock's mutual exclusion, so 200 000) stays where it is (§12.G).

**Step 18 done (2026-11-01): blocks shared with another processor.**  Built as designed:
- *`KQR.v`*: `sh_ok sh b` (with `sh_blk` and one function per sort of the syntax), definitions only: `compile_f_ok` and every
  other theorem unchanged.  Tests: a plain narrow-block read and write of unshared blocks accepted, a write to the shared
  block and a read through a block number not written refused, a marked operation and a wide-block read not asked, a
  program sharing nothing not asked.
- *`kitc.py`*: a `kq_shared` program is read by the verified compiler; `sh_ok kq_shared` is worked out on every tree read
  (a function that breaks it: the reason, the translator's own refusal next), and proved beside each function's theorem by
  a lemma `<program>_rsh<j>` (`exact eq_refl`), so the kernel checks the rule on the tree whose meaning it checked.  The
  reifier is unchanged (the rule is a property of the tree, worked out in Rocq).
- *`lock`*: `hw/build_proved.sh lock` with `KQ_REFLECT=1` — `lock` 9 functions and `lock_ap` 4 through the verified
  compiler, a rule lemma for each, built in 12.6 s; booted on two processors, under QEMU's processor and under KVM: `cntr
  200000`, the program answered 0.  A plain `rd32` of the shared block is refused on both routes (the verified side's
  reason, then the translator's).  `lock` stays outside `hw/check.sh` (the machine's gate, whose every kernel has a control).
- The C: 63 of 63 byte-identical (no gate program shares blocks; compared on this machine, the work laptop busy with the
  construct table).  The construct table through the verified compiler (the acceptance, on `beff230`, 19 min): of 780 cells,
  **512 through the verified compiler**, 253 more proved only by the walk, 15 gaps on both routes (765 proved, against 759
  in the last table of the translator alone), 0 read but refused by the check.  So the walk is not retired yet (§12.V (2):
  the construct table unchanged or better): 224 of the 253 are one construct — a record built or taken apart inside a body,
  in no function's signature (`let '(p, q) := (a + b, b) in ..`), absent from the program's record table, which is read
  off the signatures; the other 29: functions giving back a boolean (8), a function bound by a `let` (5), writing
  functions with a number and a memory or a pair (9), `option` / `sum` / `list` / records of other fields (5), a capture
  (1), `u64` inside a body (1).  **Next: record types from the bodies, then these by the tally, then the walk retired.**
- The gate with `KQ_REFLECT=1`, on the fork, on `8642551` (2026-11-01): everything passes — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels proved and built (10 / 10 / 10 / 12 / 11 s); **71 programs
  through the verified compiler, 0 read but refused by the check, 0 not read**.

**Step 19, record types from the bodies — the design (2026-11-01).**  224 of the construct table's 253 cells proved only by the
walk build a record and take it apart inside a body (`let '(p, q) := (a + b, b) in p - q`; a helper giving a pair or an `r3`,
written out) with the record's type in no function's signature: the program's record table is read off the signatures of the
functions reached (`rtab_of`), so the type is not in it, and the constructor and the match are not read.  So `rtab_of` also
takes the record types the bodies name — of a constructor applied (its parameters the first arguments), of a match (its
parameters the predicate's), of a `let`, of a primitive projection — in the functions reached and the helpers they write out
(each helper once), after the signatures' (so a program's record indices are unchanged).  `KQR.v` is unchanged: a record
built and taken apart is `RMk` and `SMatchR`, its fields atoms of KQL (no memory, no call).  *Expected*: the 224 cells, and
`P_int_w64` (a `u64` built inside a body); the C of every gate program unchanged.

**Step 19 done (2026-11-02): record types from the bodies.**  Built as designed, in the reifier only (`KQR.v` and `kitc.py`
unchanged): `body_rtys` collects the types a body names — a constructor applied (`ctor_ty`, its parameters the first arguments),
a match (the predicate's parameters), a `let`, a primitive projection — through the helpers it writes out (each once), and
`rtab_of` adds them after the signatures'.  Test: `rbp` (a pair built and taken apart inside a body, the construct table's
`N_nest` shape): the record table finds `prod int int`, the tree is `SMatchR` over `RMk`, the theorem 0.002 s.  The C: 63 of
63 byte-identical.  **The construct table through the verified compiler (on `d61befd`, 14 min): of 780 cells 729 through the
verified compiler** (was 512), 39 more proved only by the walk (was 253), 12 gaps on both routes (was 15: three cells gaps
before are proved now) — 768 proved, 0 read but refused by the check.  The 39: a pair of a number and a memory (the
number-and-memory results, 11), functions giving back a boolean (8), pairs still not read (nested, holding a function,
chosen by a test: 7), a function bound by a `let` (5), a record chosen by a test or a match (2), `option` / `sum` / `list` /
records of other fields (5), a capture (1).  **Next: these, by the tally.**  The gate with `KQ_REFLECT=1`, on the fork, on
`d61befd`: everything passes — `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels proved and built
(10 / 10 / 10 / 13 / 12 s); **71 programs through the verified compiler, 0 refused, 0 not read**.

**Step 20, lets read by zeta — the design (2026-11-02).**  Of the construct table's 39 cells proved only by the walk, six
need no new syntax: a `let` binding a function (`let g := fun x => x + b in g a`: `P_int_lam_let`, `_noncapt`, `_twice`,
`P_int_local_fun_multi`, `P_int_hof_passed`) and a dead `let` (`let t := upd 0 a b s in upd 0 b a s`, `t` unused:
`P_mem_dup`, where the reader took `s` for dead once `t` was bound).  Both are the same term as their body with the binding
put in, up to zeta — as a helper written out is up to delta and beta — so the reifier reads them so, in every reader (numbers,
records, memories, numbers made after memories, records given back): a function's `let` becomes calls of the function
written out, a dead `let` is dropped (its meaning is not part of the result, and its KQL is not made).  `KQR.v` and
`kitc.py` unchanged.  *Expected*: the six cells; a gate program's C changes only if it has such a `let`.

**Step 20 done (2026-11-02): lets read by zeta.**  Built as designed: `zeta_head` (a `let` whose type is a function's, or
whose variable its body does not name — `noccur_between` — read as `subst [b] 0 body`), at the head of the readers of
numbers, records, memories, numbers made after memories and records given back.  Tests: `rzl` (a `let` of a function called
twice: the tree is the function written out at each call, `(a + b) * (b + b)`) and `rzd` (a dead memory `let`: one `MUpd`),
each theorem 0.002–0.004 s.  The C: 63 of 63 byte-identical (no gate program has such a `let`).  The construct table (on
`0993a8b`): **735 of 780 through the verified compiler** (was 729: the six), 33 more by the walk alone, 12 gaps.  The gate
with `KQ_REFLECT=1` on `0993a8b`: everything passes — `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels
(10 / 10 / 10 / 13 / 12 s); **71 programs through the verified compiler, 0 refused, 0 not read**.

**Step 21, records chosen by a test or built from a record taken apart — the design (2026-11-02).**  Four of the 33 cells
proved only by the walk (`P_rec3_if`, `P_rec3_match`, `P_pair_call_swap`, `P_pair_match_destr`) write out a helper giving a
record that its body chooses by a test (`if a <? b then mk3 a b 0 else mk3 b a 1`) or builds from a record it takes apart
(`match hp a b with (x, y) => (y, x) end`), and take the record apart where it is used.  So `RIf ri c a b x y` and `RMatchR
ri x y` among the records, of type `ri`.  Their meanings put the test and the match inside one record value — `VRec ri (if ..
then to_rt ri x else to_rt ri y)`, `VRec ri (rmatch x (fun l => to_rt ri y))` — so that taken apart they are the user's match
on the user's test (a test of two record values, `if .. then VRec .. else VRec ..`, does not convert to it: measured, the
kernel refused it).  Compiled as `SIf` and `SMatchR` are (the test a jump, the continuation in both branches); one proof case
each, through `to_rt_vflat`; well formed when both branches, or the record made, are of type `ri`.  The reifier reads the
type off the match's own return type.  *Expected*: the four cells.

**Step 21 done (2026-11-02): records chosen by a test or built from a record taken apart.**  Built as designed (`KQR.v`:
`RIf ri`, `RMatchR ri`, their meanings, KQL, types, well-formedness and shared-block rule; one case each in `cexp_all`, the
others trivial or rewrites).  Tests: `pchoose` (a pair chosen by a test, taken apart) and `pswap2` (a pair built from a pair
taken apart), each theorem in milliseconds; branches of two record types refused.  The reifier reads a record-valued test of
one comparison and a match on a record, the type off `preturn` (test `rq`: the construct table's shapes, a helper choosing a
pair by a test and one swapping a pair it takes apart).  The C: 63 of 63 byte-identical.  The construct table (on
`97b3ece`): **741 of 780 through the verified compiler** (was 735: the four, and two gaps on both routes before), 29 more by
the walk alone, 10 gaps (770 proved).  The gate with `KQ_REFLECT=1` on `97b3ece`: everything passes — `make.sh` `core-ok`;
examples 27 / 27; corpus 36 / 36; the five kernels (10 / 10 / 10 / 13 / 11 s); **71 programs through the verified compiler,
0 refused, 0 not read**.

**Step 22, booleans chosen by a test or by a counter's match — the design (2026-11-02).**  Three of the 29 cells proved only
by the walk (`P_bool_if`, `P_bool_if_call`, `P_bool_match_nat`) write out a helper giving a boolean that its body chooses by a
test (`if a <? b then hb a b else hb b a`) or by a match on its counter (`match n with O => true | S _ => false end`), and
test it.  So `BIfCmp c a b x y` and `BMatchCnt c x0 x1` among the booleans (the names `BIf` / `BMatch` are the records'),
meaning the user's test and match; compiled in each of the three forms a boolean is compiled to — a jump, a value, a choice of
two atoms — as `SIf`'s jump and `SMatch` are (the continuations in both branches); one proof case each in each of the three.
The reifier reads a boolean-valued test of one comparison and a boolean-valued match on a counter variable.  *Expected*: the
three cells.  Not in this step: a function giving back a boolean (5 of the 29), which needs the recursive call's meaning to
give one.

**Step 22 done (2026-11-02): booleans chosen by a test or by a counter's match.**  Built as designed (`KQR.v`: `BIfCmp`,
`BMatchCnt`, their meanings, their three compilations, well-formedness, the shared-block rule, `specb`; one case each in each of
the three parts of `cexp_all`'s boolean statement, `denote_nomem`, `denote_rec_ext`).  Tests: `bpick` (a choice of two
atoms), `bjump` (a jump: a branch with a `let`), `bval` (a value bound by a `let`), `bcnt` / `bcntv` (the counter's match as a
jump and as a value), each theorem in milliseconds.  The reifier reads a boolean-valued test of one comparison and a
boolean-valued match on a counter variable (test `rbu`: the construct table's three shapes).  The C: 63 of 63 byte-identical.
The construct table (on `825c046`): **744 of 780 through the verified compiler** (was 741: the three), 26 more by the walk
alone, 10 gaps.  The gate with `KQ_REFLECT=1` on `825c046`: everything passes — `make.sh` `core-ok`; examples 27 / 27; corpus
36 / 36; the five kernels (10 / 10 / 10 / 13 / 12 s); **71 programs through the verified compiler, 0 refused, 0 not read**.

**Step 23, a pair built in place, taken apart — the design (2026-11-02).**  Five of the 26 cells proved only by the walk
(`P_intmem_lit`, `_wr`, `_alloc_like`, `_call`, `_let`) write out a helper giving a number and a memory as a pair built in
place (`(rd 0 a s, upd 0 a b s)`, after its lets) and take the pair apart: a pair of a number and a memory is not a record of
numbers.  But a match on a pair built in place is the same term, up to iota and zeta, as its branch with the two parts bound by
lets, which the readers read (a number's let, a memory's).  So the reifier reads it so (`iota_pair`, the parts' types the pair's
parameters), in every reader, after the record reading (so a record of numbers is read as before).  `KQR.v` and `kitc.py`
unchanged.  *Expected*: the five cells.  Not in this step: a function giving back a number and a memory (4 of the 26).

**Step 23 done (2026-11-02): a pair built in place, taken apart.**  Built as designed (`iota_pair`, in the readers of numbers,
records, memories, numbers made after memories and records given back, after the record reading and the lets brought before
the match).  Test `ip` (a helper giving a number and a memory, its pair after a let, taken apart): read as a number's `let`
and a memory's, the theorem in milliseconds; the earlier tests' trees unchanged.  The C: 63 of 63 byte-identical.  The
construct table (on `e0c149e`): **752 of 780 through the verified compiler** (was 744: the five, and three pairs of pairs
built in place, `P_pairp_lit`, `_let`, `_call`, whose inner pair is a record), 18 more by the walk alone, 10 gaps.  The 18:
functions giving back a boolean (5), functions giving back a number and a memory or a pair of them chosen by a test (4), a
pair holding a memory as a parameter (1), `option` / `sum` / `list` and records holding a proof or a memory (5), a pair of
pairs as a parameter (1), a pair holding a function (1), a capture of an outer variable (1) — each a new construct, the next
steps.  The gate with `KQ_REFLECT=1` on `e0c149e`: everything passes — `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36;
the five kernels (10 / 10 / 10 / 12 / 12 s); **71 programs through the verified compiler, 0 refused, 0 not read**.

**Step 24, functions giving back a boolean — the design (2026-11-02).**  Five of the 18 cells proved only by the walk
(`P_bool_tail_rec`, `_rec_search`, `_nontail_and`, `_nontail_or`, `A_par_bool_rec_negb`) are recursive functions giving back a
boolean (`match n with O => true | S m => (a <? b) && f m (a + 1) b s end`, `negb (k m (x + 1))`), tested by their callers.
The meaning's recursive call (`rec`) gives a number, so a boolean function needs its own, as a record's (`recr` of
`denote_br`); built as step 12 part 3 built records given back, with no slot block:
- *The result kind*: `sq : option kind` (was `option nat`): `Some (KRec ri)` a record (as before), `Some KBool` a boolean;
  `rtq` gives `bool`, `calln` its number `b2i` (the KQL returns 1 or 0), `callm` the memory it was given; `callee_ok`
  unchanged in shape.
- *The body*: a new sort `sbb` (a boolean given back) — `BbRet b` (a boolean at the end), `BbRec cs args` (the function itself
  at the end: a loop), `BbNotRec cs args` (its negation at the end: a call, then `lxor 1`), `BbIf`, `BbIfB`, `BbMatch`, `BbLet` —
  with `denote_bb` and its own `recb` (giving a boolean); `x && f ..` is `if x then f .. else false` and `x || f ..` is `if x
  then true else f ..` by the definitions of `andb` / `orb`, so `BbIfB` reads them.  Bodies `FRecB`, `FPlainB`; `ctailb`
  compiles in tail position; `wfbb`; `ctailb_ok` and `compile_f_ok`'s boolean case (by the counter's induction, its
  hypothesis the recursive call's KQL giving `b2i (recb ..)`).
- *A call*: `BCall f cs args` among the booleans, a call of a function giving back a boolean, in its three compilations (the
  call, then a jump on its 1 or 0, or the value, or a choice); proved from `callee_ok`.
- *The reifier*: `read_sig` reads a boolean result; a body giving back a boolean read as `sbb`; a call of such a function in a
  test read as `BCall`; `kitc.py` prints the signature's sixth part `B` for it.
- *Expected*: the five cells.

**Step 24 done (2026-11-02): functions giving back a boolean.**  Built as designed, with the lets of the other tail sorts all
in the body sort (the design named `BbLet`; `BbLetB`, `BbLetC`, `BbLetR`, `BbMatchR` came with it, each a case copied from the
record body's):
- *`KQR.v`*: `sig.sq : option kind` (a record `Some (KRec ri)`, a boolean `Some KBool`; `Some KNum` is refused by `wf_f`);
  `rtq`, `calln` (`b2i`), `callm` (the memory given), `vrec_of`, `boolf` (the boolean a call gives back).  The sort `sbb`
  (`BbRet`, `BbRec`, `BbNotRec`, the lets, `BbIf`, `BbIfB`, `BbMatch`), `denote_bb` with its own `recb`, `FRecB` / `FPlainB`,
  `ctailb` (a boolean at the end by its value, `cbval`; the function itself at the end `Eloop`; its negation the call and
  `lxor 1`), `wfbb`, `sh_bb`.  `BCall f cs args` among the booleans, compiled in the three forms a boolean is compiled to (the
  call, then a jump on its 1 or 0, or the value, or a conditional move on it), `wfb` asking a callee that gives back a boolean
  and keeps the memory.  Proved once: `bcall_run` (the callee's statement read at a boolean) and the `BCall` case of each of the
  three parts of `cexp_all`'s boolean statement, `denote_nomem`, `denote_rec_ext`, `denote_bb_nomem`; `ctailb_ok` (every case
  of the body, the recursive call's hypothesis `Hrecb`: its KQL gives `b2i (recb ..)` and keeps the memory);
  `compile_f_ok_bool` (by the counter's induction, as `compile_f_ok_rec`), the `Some KBool` case of `compile_f_ok`.  No new
  hypothesis.  Tests: `qtail`, `qsearch`, `qand`, `qor`, `qneg` (the five cells' shapes; `qand`'s KQL a loop, `qneg`'s a call
  and `lxor`), callers testing them by a jump (`qgo`), as a value (`qval`), by a choice (`qpick`); the recursive call in a plain
  body, a call of a number function as a boolean and the tree of `||` for `&&` refused; each theorem 3–15 ms; `Print
  Assumptions` the same base.  Trap met: a `lia` in a section sees every section hypothesis in scope, so `ctailb_ok`, written
  after the record part, took that part's `ri` and `1 <= rn (RO ri)` as arguments — the boolean part now stands before it.
- *The reifier*: `read_sig` reads a boolean result; `reify_bb` reads a body giving back one (at the end `a && b` as `if a
  then b else false` and `a || b` as `if a then true else b`, the same terms by the definitions of `andb` / `orb`, so the
  function itself in `b` is a loop — the translator's rule, F39; `negb` of the function itself `BbNotRec`); `reify_b` reads a
  call of such a function as `BCall`.  Test `vbgo` (the five and a caller testing each): the five trees exactly KQR.v's
  hand-written ones, each theorem 3–11 ms.
- *`kitc.py`*: the signature's sixth part `B`; an entry giving back a boolean is compiled (its KQL returns 1 or 0).
- The C: 63 of 63 byte-identical (no gate program has a function giving back a boolean).  The construct table (on
  `8780f64`, the code of `8da3b4d`): **757 of 780 through the verified compiler** (was 752: the five), 13 more by the walk alone, 10 gaps.
  The gate with `KQ_REFLECT=1` on `8da3b4d`: everything passes — `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the
  five kernels (11 / 11 / 11 / 13 / 12 s); **71 programs through the verified compiler, 0 refused, 0 not read**.

**Step 25, a value of any inductive type built in place and taken apart — the design (2026-11-02).**  Six of the cells proved only
by the walk (`A_par_dep_record`, `A_par_list`, `A_par_mem_record`, `A_par_pair_nested`, `A_par_fun_in_pair`,
`A_par_mem_pair`) build a value in place and take it apart: a record with a proof or a memory field (`bv (mkb x I)`,
`mv (mkms x t)`), a list cell (`match k a with nil => 0 | cons x _ => x end`, `k a := cons a nil`), a pair of pairs or a pair
holding a function or a memory given to a helper (`k ((a, b), a)`, `k (a, fun x => x + 1)`, `k (a, s)`).  Read apart (a scratch
file, the reifier on the smaller terms): a match on such a value written directly is read already (`iota_pair`, step 23); what
stops is the helper written out — `wout` binds an argument that is a constructor applied by a `let`, of a type no reader
holds, so the match under it never meets the constructor.  All three rules below give the same term up to Rocq's own zeta,
iota and beta, so the check is unchanged, and they fire only where the readers held nothing before (F40's rule), so a program
read before is read the same way:
- *zeta*: a `let` of a constructor applied to arguments that are themselves plain (variables, numbers, constants,
  constructors, functions), at a type the readers do not hold (not a number, boolean, counter, memory or record of the
  program's types), is its body with the value put in;
- *iota*: a match, of any inductive type, on a constructor applied whose fields are plain is its branch with the fields put in
  (after the readings there are, as `iota_pair` is), with a two-branch match on a type other than `bool` / `nat` and a match of
  more branches included; the scrutinee a helper's call written out first;
- *iota at the head of an application*: such a match applied to arguments (`(snd (a, F)) x` written out) is its branch applied.
`KQR.v` and `kitc.py` unchanged.  *Expected*: the six cells.  Not in this step: `option` / `sum` chosen by a test and taken
apart (`A_par_option`, `A_par_sum`: a match on an `if` is not the `if` of two matches up to conversion, so it needs the type held
as its tag and fields, a construct of `S`), a number and a memory given back (4), a capture through two templates (1).

**Step 25 done (2026-11-02): a value of any inductive type built in place and taken apart.**  Built as designed, in the
reifier only (`KQR.v` and `kitc.py` unchanged): `plain_val` (a plain argument, a function, a type, or a constructor of plain
values), `zeta_con` (a `let` of a constructor of plain values at a type no reader holds — `held`: a number, a boolean, a
counter, a memory or a record of the program's types — is its body with the value put in), `iota_go` (a match on a
constructor whose fields are plain is its branch with the fields put in), `hnf_con` (the head of a scrutinee: a helper written
out, a `let` read, a match on a constructor reduced) and `head_r`, which replaces `zeta_head` at the head of the six readers:
the lets of step 20, then the constructor `let`, then iota on a constructor of a type no reader takes apart (`generic_ind`: not
`bool`, `nat`, `prod` or a record of the program's) or at the head of an application.  Test `w5go` / `w5gm` (the six shapes):
the record fields, the list cell's head, the pairs' parts and the function applied are read away, the pair holding the memory
is read as a number made after memories; trees pinned, each theorem 2–6 ms, `Print Assumptions` the same base.  The C: 63 of 63
byte-identical.  The construct table (on `9ab7709`, the code of `31bb4f4`): **764 of 780 through the verified compiler** (was
757: the six, and `A_par_typeclass`, a gap on both routes before — a class's method taken from its instance built in place),
7 more by the walk alone, 9 gaps.  The gate with `KQ_REFLECT=1` on `31bb4f4`: everything passes —
`make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (10 / 10 / 10 / 12 / 11 s); **71 programs through the verified compiler, 0
refused, 0 not read**.

**Step 26, a number and a memory given back — the design (2026-11-02).**  Four of the cells proved only by the walk give
back `int * mem`: a helper choosing the pair by a test, written out where its pair is taken apart (`P_intmem_if`: `let '(x,
s2) := (if a <? b then (a, upd 0 a b s) else (b, s)) in x + rd 0 0 s2`); a loop (`P_intmem_tail_rec`: `f m (a + 1) b (upd 0 a
b s)` at the end; `A_par_mem_pair_rec`); a recursion taking its own pair apart (`P_intmem_nontail`: `let '(x, s2) := f m a b s
in (x + 1, upd 0 x b s2)`); their callers take the pair apart, by a match or by a let read through `fst` / `snd` (`let r := k n
a s in fst r + rd 0 0 (snd r)`).  A match on a test is not the test of two matches up to conversion, so the pair chosen by a
test must be a construct of `S`, as a record chosen by a test is (step 21).  The translator states such a function as
`runk P f args M (fst (g ..)) (snd (g ..))` (§1.6): its KQL returns the number and ends with the memory.
- *The result kind*: `sq = Some KNum` (a number and a memory): `rtq` gives `i63 * mem`, `calln` its first part, `callm` its
  second, so `callee_ok` states it as the translator does, unchanged in shape.
- *Pair values*: a sort `spv` — `PvMk e m` (built: the number worked out on the memory before `m`'s writes, then `m`),
  `PvCall f cs args m` (a function giving back a pair), `PvRec cs args m` (the function itself), `PvIf`, `PvIfB`, `PvMatch c
  p0 p1` (a counter's match), `PvLet`-family lets, `PvMatchP p q` (`p` taken apart: its number the nearest number, its memory
  the newest, then `q`); its meaning `denote_pv` is the user's pair itself (with the recursive call's own meaning `recp`).
- *Compiled two ways*: in tail position (`ctailp`: the number returned after the writes, the function itself a loop, a call
  then its result), and where it is taken apart (`cpv`, continuation style: the number's atom given on, the KQL memory the
  pair's memory — `cpv_ok`, from `cmem_ok`, `ccallr`'s pattern without the slot block).
- *Taken apart*: `XMatchP p x` among the numbers made after memories, `MMatchP p m` among the memories, `PvMatchP` among the
  pairs; and the let form, `XLetP` / `MLetP` (`fst r` a number variable, `snd r` the newest memory while nothing writes after
  it — the memory's linearity, checked as for every memory).
- *Bodies*: `FRecP`, `FPlainP`; `ctailp_ok` and `compile_f_ok`'s case (the counter's induction, its hypothesis the recursive
  call's KQL giving the pair's number and ending with its memory).
- *The reifier*: `read_sig` reads `int * mem` as the result; a body read as a pair value; a pair taken apart read as
  `XMatchP` / `MMatchP` / `PvMatchP` (a helper's pair written out first), the let form through `fst` / `snd`.
- *Expected*: the four cells.  Not in this step: a pair of a number and a memory as a parameter (a memory is passed only as
  the function's memory), records of a number and a memory (`mem_pair`) beyond `prod`.

**Step 26 done (2026-11-02): a number and a memory given back.**  Built as designed, with one place left for later:
- *`KQR.v`*: `sq = Some KNum` gives back `i63 * mem` (`rtq`; `calln` its first part, `callm` its second; `pvf` the pair a call
  gives back).  The sort `spv` (`PvMk`, `PvCall`, `PvRec`, the lets and the memory let, `PvIf`, `PvIfB`, `PvMatch`, `PvMatchP`),
  `denote_pv` with its own `recp`; `cpv` (continuation style: the number's atom given on, the KQL memory the pair's) and `ctailp`
  (tail: the number returned after the writes, the function itself a loop); `XMatchP` and `XLetP` among the numbers made after
  memories (one compilation, `cpv` then the rest); `wfpv`, `sh_pv`; bodies `FRecP`, `FPlainP`.  Proved once: `pvcall_run` (a
  callee's statement read at a pair), `cpv_ok`, `ctailp_ok` — both stated for any recursive call (`recp`, `rp` quantified, not
  section variables: `ctailx_ok` uses them at `rp = false`) —, the two cases of `ctailx_ok` and `denote_x_recx_ext`,
  `compile_f_ok_pair` (by the counter's induction) and `compile_f_ok`'s case.  No new hypothesis.  Tests: `jtail`, `jnon`,
  `jif`, `jgo`, `jlet` (the four cells' shapes and the let form: `jtail`'s KQL a loop, `jnon`'s a call); a pair function without
  a memory, a pair taken from a number function and the parts the other way round refused; each theorem 2–8 ms; `Print
  Assumptions` the same base.
- *Not built*: `MMatchP` / `MLetP` (a memory function taking a pair apart): `smem` would become mutual with `spv` and every proof
  over memories one mutual induction; no cell of the table needs it yet, so it stays open.
- *The reifier*: `read_sig` reads `int * mem` as the result; `reify_pv`; `XMatchP` after the step-23 reading (a pair built in
  place is still read as two lets); the let form by putting the pair of two new variables in for `r` (`pm_split`), so that `fst
  r` and `snd r` reduce by step 25's rules; a read whose memory argument reduces to the newest memory (`rd 0 0 (snd r)`) read as
  a read.  Test: KQR.v's tests read from their text (`jgo` over `jnon`, `jlet` over `jtail`, `jif`), the trees pinned, each
  theorem 2–6 ms.
- *`kitc.py`*: the signature's sixth part `P`.
- The C: 63 of 63 byte-identical.  The construct table (on `4fff28f`, the code of `6b0d249`): **768 of 780 through the verified compiler** (was
  764), 3 more by the walk alone, 9 gaps.  The gate with `KQ_REFLECT=1` on `6b0d249`: everything passes — `make.sh`
  `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (10 / 10 / 10 / 12 / 12 s); **71 programs through the verified compiler, 0 refused,
  0 not read**.

**Step 27, a template giving its own function parameter to another template — the design (2026-11-02).**  One cell proved
only by the walk, `P_int_outer_capt`: `outer r acc f := match r with O => acc | S r' => outer r' (fold 3 0 acc f) f end`, called
with a function naming the caller's `b`.  Read apart (a scratch file, the reifier on smaller programs): the copy of `outer` is
not read even when the function given names nothing — inside the copy, `fold 3 0 acc f` gives `fold` the copy's own function
parameter, which neither the scan for the copies a program needs (`sites`, run over the functions given only) nor the look-up
of a call of a template (`tc_of`) resolves to the function it is bound to.  So, in the reifier only:
- a function parameter of a copy, given to another template, is the function it is bound to (its context entry's function,
  its captured variables placed as the copy's, `capsub`) — where a call is looked up in every reader, and in the scan for sites;
- `ensure` scans the template's own body too, its function parameters bound to the functions given, and makes the copies it
  needs before the copy itself (the copy of `fold` for `outer`'s function, taking the same captured variable).
`KQR.v` and `kitc.py` unchanged; the copy's theorem is `compile_f_okr` as for every copy.  *Expected*: the cell.

**Step 27 done (2026-11-02): a template giving its own function parameter to another template.**  Built as designed, in the
reifier only (`KQR.v` and `kitc.py` unchanged): `fsub` (a copy's function parameter is the function it is bound to, its
captured variables placed as the copy's), used by `tcall` at every look-up of a call and by `sites` in the scan; `ensure` scans
the template's own body, its function parameters bound to the functions given, and makes the copies it needs first.  Test
`zof1` / `zof2` (the cell's shape with and without a captured number): the copy of `zfold` for `zouter`'s function takes the
captured number before its own, `zouter`'s copy calls it passing it on; trees pinned; each copy by `compile_f_okr`, the caller
by `compile_f_ok`, 2–8 ms; `Print Assumptions` the same base (the test's tree list taken from `reify_prog`, not from the pair
`reify_prog2` gives with the copies' meaning terms, whose type carries MetaRocq's term syntax and with it the declarations of
Rocq's primitive float and string types).  The C: 63 of 63 byte-identical.  The construct table (on `e6b2aa4`, the code of `09d1b1d`): **769 of 780
through the verified compiler** (was 768), 2 more by the walk alone, 9 gaps.  The gate with `KQ_REFLECT=1` on
`09d1b1d`: everything passes — `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (10 / 10 / 11 / 12 / 12 s); **71 programs
through the verified compiler, 0 refused, 0 not read**.

**Step 28, `option`, `sum` and their kind held as their tag and fields — the design (2026-11-02).**  Two cells proved only by
the walk (`A_par_option`, `A_par_sum`: a helper choosing `None` / `Some x` or `inl x` / `inr x` by a test, its value taken apart
by the caller) and two gaps on both routes (`A_par_option_rec`: an `option` given back by a recursion; `A_par_option_state`: an
`option` as a loop's state).  A match on a test is not the test of two matches up to conversion, so the value must be held.
Rather than a new sort, a non-recursive inductive whose constructors carry numbers is held as a record whose first field is
its constructor's number and the others its fields, padded with 0 — the way C holds a tagged union — so every construct of
records already built (built, chosen by a test, taken apart, bound, passed, given back through the slot block) serves it:
- *`KQR.v`*: `rops` gains `rtg : option (list nat)` (`None` a record; `Some ws` a data type, constructor `c` carrying `nth c
  ws` numbers).  `RecLaws`' third law splits: `rl_mk` for a record (as now), `rl_mk_tag` for a data type (each constructor's
  number, its fields and written zeros, built then taken apart, gives them back) — per program by a fixed tactic
  (`kq_tag_case`); `rl_mk_c` derives the law for any list in a constructor's form (`canon`).  `RMk`'s well-formedness asks the
  form of the syntax (`canon_s`: the tag a written constructor number, the fields after the constructor's own written zeros),
  and `canon_s_ok` carries it to the meaning; `RW64` asks a plain record.  The only proof cases touched are `RMk`'s and
  `RW64`'s.  A match on such a value is a record taken apart and a test of its tag: `match v with None => e0 | Some x => e1
  end` is, by the record's own match and the kernel's computation of `PrimInt63.eqb` on written numbers, the same term as
  taking the record apart and choosing `e0` where the tag is 0, `e1` otherwise.
- *The reifier*: the record table takes such types (`rec_shape`: several constructors, their fields numbers), with their
  widths; a constructor reads as `RMk` with its number and the padding; a match reads, in each reader, as its record match and
  a chain of tests of the tag (the branches lifted to the record's fields); `kitc.py` writes the instance (`rmk` a chain of
  tests of the tag, `relim` the type's match, `kq_tag_case` for the law).
- *Expected*: the four cells.

**Step 28 done (2026-11-02): `option`, `sum` and their kind held as their tag and fields.**  Built as designed:
- *`KQR.v`*: `rops.rtg`; `canon` / `zeros_from` (a list in a constructor's form); `RecLaws` with `rl_mk` (a record) and
  `rl_mk_tag` (a data type, for each constructor); `rl_mk_c` derived once; `canon_s` / `zeros_s` on `RMk`'s syntax and
  `canon_s_ok`; `RW64` asks a plain record.  The proof cases touched: `RMk`'s and `RW64`'s in `cexp_all`, nothing else.  No new
  hypothesis.  `kq_tag_case` (with `kq_zeros`), the per-program tactic for `rl_mk_tag`, outside the sections.  Tests (`d_recs`:
  `option` and `sum`): `dopt`, `dsum` (built by a test, taken apart by a test of the tag), `dpar` (a parameter), `dres` / `dgo`
  (given back by a recursion through the slot block, and its caller), `dstate` (a loop's state); a tag not written, a field after
  the constructor's own not zero and a tag beyond the constructors refused; each theorem 3–24 ms; `Print Assumptions` the same
  base.
- *The reifier*: `rec_shape` takes a non-recursive inductive of several constructors whose fields are numbers or its number
  parameters (not `bool`, not `nat`: found by a first version, which took `nat`'s `S` field, the type itself, for a parameter,
  and read counter matches as data — every earlier test caught it), with its widths in the table's entry; `cindex` gives a
  constructor its number and padding; `tag_parts` / `tag_chain` read a match in each of the six readers as the reader's record
  match and a test chain on the tag (each branch lifted to the record's fields); `arity_recs` and `rec_text` carry the widths.
  Rocq's `option` is `Some` (0) then `None` (1): the reifier follows the declaration.  Test `t8go`, `t8sum`, `t8rgo`, `t8sgo` (the
  four cells' shapes): trees pinned, instances as `kitc.py` writes them, each theorem 2–8 ms.
- *`kitc.py`*: a data type's instance — `rmk` a chain of tests of the tag, `relim` the type's match padded with zeros, the
  laws by `destruct` and `KQR.kq_tag_case`.
- The C: 63 of 63 byte-identical.  The construct table (on `14e971d`): **773 of 780 through the verified compiler** (was
  769), 0 more by the walk alone, 7 gaps (was 9: `A_par_option_rec` and `A_par_option_state`, gaps on both
  routes before, are proved now).  The gate with `KQ_REFLECT=1` on `14e971d`: everything passes — `make.sh` `core-ok`; examples
  27 / 27; corpus 36 / 36; the five kernels (10 / 10 / 10 / 13 / 12 s); **71 programs through the verified compiler, 0 refused, 0 not read**.

**Step 29, the walk retired — the design (2026-11-02).**  Since step 28 every cell of the construct table that is proved at all
is proved by the verified compiler (773 of 780; the 7 left are gaps on both routes), every program of the gate goes through it
(71 of 71, `lock` too), and the trusted base is the one of §1.10 — the condition §12.V (2) set for retiring the walk ("the
construct table unchanged or better").  So:
- *`kitc.py`*: the verified compiler is the route (`KQ_REFLECT` is no longer needed); a program the reifier does not read, or
  whose check fails, is refused with the reifier's reasons — read like a type error (D23), not handed to a proof search.  The
  translator and the walk stay in the tree, reachable only by an explicit `--walk` (or `KQ_WALK=1`): the yardstick F49 asks for
  (a program moved to the verified compiler is timed against the translator's build) and the record of what the walk proved.
- *The construct table*: its classifier names the refusal ("not read by the verified compiler", with the reasons).
- *Accepted when*: the gate without `KQ_REFLECT` and without `--walk` (goal row 8b: "the gate with the walk switched off")
  passes — examples, corpus, the five kernels — every program through the verified compiler, none refused; the construct table
  run the same way proves the same 773 cells; `ASSUME=1 make.sh` lists §1.10's base.
- *Not in this step*: removing the translator's and the walk's files (`KQMTrans.v`, `KQMAuto.v`, `KQMNames.v`): the timing
  yardstick still uses them, and `lib/` and the kit route are untouched.

**Step 29 done (2026-11-02): the walk retired.**  Built as designed: `kitc.py`'s route is the verified compiler (`KQ_REFLECT`
and `--reflect` change nothing now); a program the reifier does not read, or whose check fails, is refused with the reifier's
reasons (`... ; refused`, then `NAME REFUSED: not compiled by the verified compiler`); `--walk` / `KQ_WALK=1` give the translator
and the walk alone.  `matrix/classify.py` names the refusal (its reasons as the category); `proved/README.md` says which route
is which.  Found by the acceptance run and fixed in `8b406b3`: when Rocq itself refuses the program (the construct table's
`A_par_nat_arith`, `k (m + 0)` not structurally smaller) the refusal said only "the reifier did not run", so the table counted
it as a gap — the translator's message used to carry Rocq's error; now the refusal carries it (`Rocq refused the file: Cannot
guess decreasing argument of fix.`) and the cell is "not Rocq" again (that cell, and a proved and a refused one, re-run alone;
no gate program reaches that branch).  **Acceptance (goal row 8b, "the gate with the walk switched off"), on `eadb665`, with no
`KQ_REFLECT` and no `--walk`**: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36 equal to the C++ answers; the five kernels
proved and built (10 / 10 / 10 / 13 / 12 s); **71 programs through the verified compiler, 0 refused**; the retired route still
builds its yardstick (`kitc.py --walk`, `reflect_counters` proved, 652); `ASSUME=1 make.sh` lists §1.10's base — Rocq's 63-bit
integer axioms, `divs_min_neg1`, the kit's memory primitives and `real_laws`, the machine operations' declarations, CompCert's
classical axioms — and nothing else.  The construct table run the same way: **773 of 780 through the verified compiler, none
by the walk** (the same 773 as with it, step 28), 7 refused: 6 gaps (`A_par_nat_eqb`, `_ltb`, `_mul`, `_pred`: arithmetic and
comparisons on counters; `P_int_local_fix`: a local `fix` naming the caller's variables; `P_pairp_rec`: a pair of pairs given
back by recursion) and `A_par_nat_arith`, not Rocq.  The C: 63 of 63 byte-identical.  **§12.V is done**: every program is compiled
through the verified `compile`, with only the conversion check per program.

**Step 30, comparisons of counters and the predecessor — the design (2026-11-02).**  Three of the six gaps compare counters or
take a predecessor: `if Nat.eqb n 3 then a else b` (`A_par_nat_eqb`), `if Nat.ltb n 10 ..` (`A_par_nat_ltb`), `k (Nat.pred n) a`
(`A_par_nat_pred`).  A counter is held as its machine number (`ofn`), so:
- *Syntax and meaning*: `BCmpC c a b` among the booleans, `c` one of `Ceq`, `Clt`, `Cle`, meaning `Nat.eqb` / `Nat.ltb` /
  `Nat.leb` of the two counters — the user's own functions, so the check stays a conversion; `CPred a` among the counters,
  meaning `Nat.pred`.
- *KQL*: `BCmpC` as `BCmp` is compiled, on the counters' atoms (a test, a value, a choice of two atoms); `CPred` a subtraction of
  1 and a conditional move keeping 0.
- *Proof*: one case each in the counter and boolean parts of `cexp_all` (and the lemmas over the syntax): the machine numbers
  compare as the counters do, and `ofn (Nat.pred n)` is the subtraction or 0, for counters below `2^62` — which every counter of
  a function is, by `denote_c_bound` and the depth `wf` already bounds; `CPred` adds no depth (it does not grow) and keeps a
  counter flat.
- *The reifier*: `Nat.eqb`, `Nat.ltb`, `Nat.leb` of two counters in `reify_b`; `Nat.pred` in `reify_c`.
- *Expected*: the three cells.  Not in this step: `n + n` given to a callee (`A_par_nat_mul`) — a callee's theorem asks its
  counters below its own bound, which the sum of two of the caller's can pass; it needs bounds per function computed and checked
  for the program instead of `cbz j`, a step of its own; a local `fix` naming the caller's variables; a pair of pairs given back.

**Step 30 done (2026-11-02): comparisons of counters and the predecessor.**  Built as designed:
- *`KQR.v`*: `BCmpC c a b` among the booleans, meaning `cmpn c` of the two counters (`Nat.eqb` / `Nat.ltb` / `Nat.leb`, the user's
  own functions), compiled in the three forms a boolean is compiled to (a jump, a value, a choice of two atoms) on the counters'
  atoms; `CPred c` among the counters (`Nat.pred`), a subtraction of 1 and a conditional move keeping 0, adding no depth.  `wf`
  takes a comparison of the unsigned kinds only (`Ceq`, `Clt`, `Cle`), of counters at most 2^20 successors deep (`shallow`).
  Proved once: `cmpn_ofn` (counters below `wB` compare as their machine numbers, through `ofn_phi`) and `ofn_pred_sel` (the
  predecessor's machine number), the two cases of `cexp_all` (the comparison's three parts, the predecessor),
  `denote_nomem`, `denote_rec_ext`, `denote_c_bound`, `cfree_bound`.  No new hypothesis; `Print Assumptions` the same base.
  Tests: `nceq`, `nclt` (the shapes of `A_par_nat_eqb` / `_ltb`), `ncle` (two counters, a jump), `ncv` (bound by a let), `nloop`
  (a comparison in a loop's tail: the two calls merged), `npk` / `npgo` (`A_par_nat_pred`: the predecessor given to a loop),
  `npv` (bound by a let of a counter), `nsel` (a choice inside an expression: one conditional move; a test at the end of a
  function stays a jump, as for numbers); a signed comparison of counters refused by `wf`, a wrong comparison and a missing
  predecessor refused by the check; each theorem in milliseconds.
- *The reifier*: `Nat.eqb`, `Nat.ltb`, `Nat.leb` of two counters read as `BCmpC` (`reify_b`; the reasons scan knows them),
  `Nat.pred` as `CPred` (`reify_c`).  Test `w30*`: the trees of `nceq`, `nclt`, `npk` / `npgo` exactly the hand-written ones, a
  caller with the three shapes and a memory it does not use, each theorem in milliseconds.
- The C: 63 of 63 byte-identical.  The construct table (on `d61d943`): **776 of 780 through the verified compiler** (was 773:
  the three), 3 gaps (`A_par_nat_mul`, `P_int_local_fix`, `P_pairp_rec`) and `A_par_nat_arith`, not Rocq.  The gate on
  `d61d943`, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (10 / 10 / 11 / 13 /
  12 s); **71 programs through the verified compiler, 0 refused**; `ASSUME=1 make.sh` the same base as step 29's.

**Step 31, a local `fix` naming the caller's variables — the design (2026-11-02).**  `P_int_local_fix`: `f n a b s := let fix g
m x := match m with O => x | S k => g k (x + b) end in g n a`, called by `go`.  Read apart: `f` is refused as a constant outside the
syntax — not a function of the program (no fixpoint at its head, small) and not a helper (its body has a fixpoint); and written
out, a fixpoint applied is no construct of `S`.  A local fixpoint is a template applied to nothing but its captured variables
(§5.6: lambda lifting, as captures are), so, in the reifier only, as step 13's copies are made:
- a local fixpoint of one body, recursive on its first parameter, a counter, taking no function, applied to all its arguments,
  is a call of a *copy*: a function of the program whose parameters are the fixpoint's counters, its captured numbers and
  booleans (in the order they first appear), its other parameters, the captured memory last (only when it takes none of its
  own); its meaning is the fixpoint itself with the captured variables as those parameters (`fun c b x => (fix g m x := ..
  b ..) c x`), so the caller's text is the call of the copy up to delta, beta and zeta, and the copy's theorem is
  `compile_f_okr` with its two equations by conversion (step 10);
- two local fixpoints are one copy when they are the same term once their captured variables are numbered;
- a definition of the program's file whose fixpoints are all local is a helper, written out where it is used;
- the call sites are looked for as a template's (`sites`), in the functions and in the helpers that have a local fixpoint,
  with a `let` of a function read as its body with the function put in, as the readers read it.
`KQR.v` unchanged.  *Expected*: the cell.

**Step 31 done (2026-11-02): a local `fix` naming the caller's variables.**  Built as designed, in the reifier (`KQR.v`
unchanged):
- *Reading*: a local fixpoint of one body applied is read, at the head of the six readers (`head_r`), as a call of a reserved
  name (`kn_lfix`) with the fixpoint first; the call look-up (`tc_of`) gives its copy and the arguments in the copy's order (the
  counters, the captured numbers and booleans, the others, the captured memory).  The copy is made as a template's
  (`ensure`, the sites in its own body first), read by the template's reader taken over the fixpoint's body (`read_def`),
  its meaning the fixpoint with the captured variables as parameters (`lfix_meaning`, over `copy_meaning_h`); its key is
  the fixpoint with its captured variables numbered the last first (`lfix_key`), so that, read with them after its own
  parameters (`rev capk`, as a template's copy is read), each is the parameter of its kind.  The call sites (`sites`) gain
  the fixpoint applied, and a `let` of a function read by zeta, as the readers read it; the helpers looked through for them
  include those with a local fixpoint (`has_lfix`, a scan that counts no fuel left as none).  A definition of the program's
  file whose fixpoints are local is a helper.
- *Found on the way* (F57): `teq`, the structural comparison of the copies' keys, had no case for a fixpoint — a key with one
  never equal to itself, so the copy was made and its call not found.  Fixed (the hole F16 found in the translator's
  `term_same`).
- *`kitc.py`*: the copies' templates are held back in the check (`Strategy opaque`) except `kqlfix`, which is no constant.
- *Tests* (`KQRReify.v`): `lf_go` (the cell's shape through a helper written out, called twice with different variables
  captured: one copy), `lf_m` (a captured number and the memory): trees pinned, the copies' meanings
  `fun n b x => (fix g m x := .. x + b ..) n x` and `fun n b i acc s => (fix g ..) n i acc`, each copy by `compile_f_okr` from its
  equations, each caller by `compile_f_ok`, in milliseconds; `Print Assumptions` the same base.
- *A slowdown found by the gate and removed* (F58): the first version's kernels built in 12 / 12 / 12 / 15 / 15 s (step 30: 10 /
  10 / 11 / 13 / 12 s), the C unchanged; the reifier's step on `HWP_kernel` 5.5 s against 2.5 s: a helper of the program's file
  was scanned in full for a local fixpoint at every call before the bounded scan.  The same test in the other order
  (`c48dc6c`): 2.6 / 2.1 / 1.8 s on `HWP_kernel` / `HWP_own` / `HWP_irqnow` (step 30's 2.5 / 1.9 / 1.7 s).
- The C: 63 of 63 byte-identical.  The construct table (on `446e1c2`): **777 of 780 through the verified compiler** (was 776),
  2 gaps (`A_par_nat_mul`, `P_pairp_rec`) and `A_par_nat_arith`, not Rocq; the follow-up computes the same test, so the table
  stands for it.  The gate on the follow-up, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the
  five kernels (10 / 10 / 10 / 13 / 12 s); **71 programs through the verified compiler, 0 refused**; the trusted base unchanged.

**Step 32, records holding records — the design (2026-11-02).**  `P_pairp_rec`: `f` gives back `(int * int) * int` by recursion
(`((a, b), 0)`; `let '(p, z) := f m a b s in let '(x, y) := p in ((y, x), z + 1)`), and `go` takes it apart the same way.  A record
type of the table has numbers as fields (D15); a record holding records is held as one flat record of numbers — C's struct
holding a struct, laid out in place — so every construct of records (built, chosen, taken apart, bound, passed, given back
through the slot block) serves it, and `KQR.v` is unchanged (a record type is any type with its descriptor and laws, step 12):
- *The order of the fields*: the outer record's numbers first, then each inner record's fields, recursively, in field order —
  the order in which Rocq's nested patterns bind them (`let '((x, y), z) := v` is `match v with (p, z) => match p with (x, y)
  => ..`: binders `p z x y`, of which `p` is no number).  So a record taken apart together with its inner records, at once and in
  that order, is `SMatchR` with its numbers where the text binds them, the inner records' own variables unusable after it, and
  the meaning's match is the user's, nest for nest.  Inner records taken apart in another order are not read (the descriptor is
  one per type).
- *A constructor* of such a type, each inner record built in place, is `RMk` on the flat numbers; an inner record given as a
  variable or a call is not read (no eta for `prod`: `(p, z)` is not `((fst p, snd p), z)`).
- *The reifier*: the record table's entries gain their fields' widths (a field whose type is a record of the table: its
  width), `rec_shape` takes such fields; one helper (`rbr`) reads a record taken apart and its inner records in the seven
  places a record match is read today; the constructor flattened as above.
- *`kitc.py`*: the instance of such a type — its constructor on the flat list, its match nest for nest, a value of it — from
  texts the reifier gives (`rec_text`); the laws' script also destructs the values a match in the goal takes apart.
*Expected*: the cell.

**Step 32 done (2026-11-02): records holding records.**  Built as designed, in the reifier and `kitc.py` (`KQR.v` unchanged):
- *The record table*: each entry carries its fields' widths (`rentry`'s sixth part; empty for a data type); `rec_shape` takes a
  field that is a number, a parameter that is a number or a record, or a record type of its own, each of at least one number
  (a `True` field is no record field: it made `w5bnd` — step 25's test — a record of the table, and its reading changed; the
  test caught it).  Records holding records come into the table **from the functions' signatures only**: built and taken
  apart in a body they need nothing (step 25), and taking them from the bodies changed how step 25's test was read (`fst (fst
  p)` on a pair of pairs built in place) — the test caught that too.
- *Reading*: `rbr` reads a record taken apart, with its inner records at once in its fields' order, depth first, as the
  readers' entries (a number an entry, an inner record's own variable unusable after it), in the seven places a record match is
  read; a constructor whose inner records are built in place is `RMk` on the flat numbers (the outer numbers, then the inner
  records' fields).  An inner record used as a value (`fst (fst r)` on such a record) is not read: no eta for `prod`.
- *`kitc.py`*: the instance of such a type from the shape the reifier gives (`rec_text`: `N:pair(pair(i,i),i)`) — the
  constructor on the flat list, the match nest for nest, a value of it; the laws' script also unfolds the descriptors and
  destructs what a match takes apart where `reflexivity` alone does not close a law (the existing programs' laws close as
  before).
- *Tests* (`KQRReify.v`): `pp_f` / `pp_go` (the cell's shape): the record table and its texts, the trees pinned (`z` the nearest
  number, then `x`, `y`), the instance as `kitc.py` writes it, both theorems in milliseconds; `Print Assumptions` the same base.
- *The reifier's step on the kernels' programs*: `HWP_own` 2.0–2.1 s with both step 31's reifier and this one, `HWP_kernel`
  2.6–2.7 s against 2.7–3.4 s (the same session, interleaved: within the spread or up to half a second); the body types'
  record shape is worked out once per type.
- The C: 63 of 63 byte-identical.  The construct table (on `1dcf4f8`): **778 of 780 through the verified compiler** (was 777), 1
  gap (`A_par_nat_mul`) and `A_par_nat_arith`, not Rocq.  The gate on `1dcf4f8`, the walk switched off: `make.sh` `core-ok`;
  examples 27 / 27; corpus 36 / 36; the five kernels (10 / 11 / 11 / 13 / 12 s); **71 programs through the verified compiler, 0
  refused**; the trusted base unchanged.

**Step 33, a sum of counters given to a callee — the design (2026-11-02).**  The last gap, `A_par_nat_mul`: `k (n + n) a`.  Two
parts.  (1) `CAdd a b` among the counters (`Nat.add` of two counters), an addition of their machine numbers — exact, since every
counter of a function is below `2^62`.  (2) The bound.  Function `j` is proved for counters below `cbz j = 2^62 - j·2^20`, and a
callee is used at its own bound; `wf` lets a caller give a callee counters at most `2^20` successors over its own (`shallow`),
which `cbz`'s fall of `2^20` per function covers.  A sum of two counters can reach twice the caller's bound, which no bound
falling with the function's index covers.  So the bound becomes **per function and per program**: a table of bounds, one per
function, given to `compile_f_ok` (as the callees are) and worked out by the reifier — the entry's at least `2^60 + 2^20` (its
counters come from `kq_nat`), each callee's above every counter its callers give it; a counter expression's largest value for
a bound `B` of its variables is `cmax B c` (a variable `B - 1`, a successor one more, a sum the sum, a budget `2^60`, a
predecessor its argument's).  `wf`'s call condition becomes `cmax (the caller's bound) c < the callee's bound` in place of
`shallow`; the table's range (each bound in `[2^60 + 2^20, 2^62]`) is checked by computation; a recursive call's counters stay
flat, as now.  Nothing is added to what is trusted: the bounds are checked, not assumed.  *Expected*: the cell, and the C of
every program unchanged (the bounds are in the statements, not in the code).

**Step 33 done (2026-11-02): a sum of counters given to a callee; counter bounds per function.**  Built as designed, with one
part narrower than the design (said below):
- *`KQR.v`*: `CAdd a b` among the counters (`Nat.add`), compiled to one addition of the machine numbers.  `sig` carries an
  optional bound (`sb`; the constructor `mksig7`, and `mksig` keeps the six arguments with no bound, so every signature written
  before is unchanged); `fbound gs j` is the own bound or the index's (`cbz j`).  `wf`'s first argument is the callees'
  signatures with the function's own bound (`ub`: the own bound, or `cbz` of the callees' number, which is at least the
  function's index); its call condition is the largest value of each counter given (`cmax`: a variable the bound less one,
  a successor one more, a sum the sum, a budget 2^60, a predecessor its argument's) below the callee's `fbound`, which is at
  most 2^62 — in place of `shallow`; for every program before this step it accepts what `shallow` did.  `wf_f` checks the
  range of an own bound (`bok`: above 2^60 + 2^20, at most 2^62).  `shallow` and `flat` ask for no sum (`noadd`).  The proof:
  the section's bound is the own one (`cbj`), `cbz_big` / `cbz_small` hold of it, `ub_ge` (it is at most `ub`) and
  `cs_fit_bound` (the counters given are below the callee's bound) replace `cbz_mono`; `cexp_all`'s counter part carries
  `cmax cbj c < wB` in place of the depth (`shallow_wb`, `letc_wb`, `all_flat_wb`, `all_fit_wb`), the sum's case by
  `ofn_add`; `cmax_bound`, `cmax_mono`, `cmax_depth`, `cmax_nonneg`; `compile_f_ok` and its per-kind parts stated at
  `fbound gs j` for a signature with any bound.  No new hypothesis; `Print Assumptions` the same base.  Tests: `ka` (proved for
  counters up to 2^62) and `kgo` (its own up to 2^61, giving `ka` `n + n`), the KQL one addition and the call; refused: the
  call at the index's bound, a sum given to the recursive call, a sum compared, a bound out of its range, the tree without the
  sum.  (Found on the way: `lia` does not prove `2^62 - j·2^20 <= 2^62 - l·2^20` from `l <= j` in that context; the
  monotonicity lemmas do.)
- *The reifier*: `Nat.add` of two counters read as `CAdd`; a function well formed only with a bound of its own is given the
  smallest (`own_bound`, 2^60 + 2^20 + 1), which suits a function no other calls — the entry, whose counters come from
  `kq_nat`.  **Narrower than the design**: the design works the bounds out top-down from the call graph (each callee above
  every counter its callers give it); what is built gives an own bound only to a function that needs one, at the smallest,
  so a function that passes a sum of counters and is itself called is not read yet — the general form stays open.  Nothing of
  soundness rests on this: each caller's `wf_f` checks what it gives against its callee's bound.  Test `w33go` (the cell's
  shape): its tree with the sum, its own bound, both theorems in milliseconds.
- *`kitc.py`*: a function's signature printed with its bound, its theorem stated at it.
- The C: 63 of 63 byte-identical.  The construct table (on `dfd4832`): **779 of 780 through the verified compiler** (was 778), **0 gaps**; the one left, `A_par_nat_arith`, is not Rocq (Rocq refuses it: `k (m + 0)` is not a smaller argument).  The gate on `dfd4832`, the walk switched off: `make.sh`
  `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 11 / 11 / 13 / 13; step 32's 10 / 11 / 11 / 13 / 12: at most a second more, within the spread these runs have shown s); **71 programs through the verified compiler, 0
  refused**; the trusted base unchanged.

**The places §12.V's steps left unread, as cells (2026-11-02).**  Completeness is strict (owner; `CLAUDE.md`): every place a step
left unread gets a cell, so the table shows it.  22 cells added to `gen.py` (802 in all): a sum of counters given by a function that
is itself called (`A_par_nat_add_called`; its caller giving it a successor, `_called_succ`), under a successor, bound by a let,
compared; a let of a successor of a counter variable (step 9); a record holding records used as a value, taken apart later, given
on (step 32); a number and a memory taken apart by a function giving back a memory, and as a parameter (step 26); a mutual block of
members of different signatures, and of members giving back a memory (step 17); a capture of a counter, of a record, of a variable
bound by a match on a record (step 13); a template giving back a record (step 12); a number function that writes, called inside an
expression, and its recursive call inside one (step 11); a let in a later operand of `&&` (step 8); the counter not first and the
memory not last (§3.7).  Run alone: 3 are read already (`A_par_nat_add_called`, `_add_succ`: the reifier's own bound cascades when
a caller gives counters on as they are), 19 are refused — gaps, to be closed as constructs of `S`, in this order: counter bounds per
counter (sums and successors anywhere, top-down), the parameters in any order, captures of every kind, records holding records as
values, memory functions taking a number-and-memory pair apart, mutual blocks of any signatures, templates giving back records,
writing functions inside expressions, lets inside later operands.  A function from another file (§3.7) needs a generator that
writes two files: not yet a cell.  **The full table on `7252fa8`: 802 cells, 781 through the verified compiler, 20 gaps, 1 not
Rocq** — the gaps are these cells (the sum given by a called function whose caller gives it a successor, a sum bound by a let or
compared, a let of a successor; a capture of a counter, of a record, of a match-bound variable; a writing function inside an
expression and its recursive call inside one; a let in a later operand of `&&`; a record holding records used as a value, taken
apart later, given on; a memory function taking a number-and-memory pair apart, and the pair as a parameter; mutual blocks of any
signature and giving back a memory; a template giving back a record; the counter not first, the memory not last).

**Step 34, counter bounds worked out from the call graph — the design (2026-11-02).**  Step 33's general form: a function's own
bound such that every caller's counters fit it, whatever the call graph (`A_par_nat_add_called_succ`: a function passing a sum, its
caller giving it a successor, which the smallest own bound cannot take).  In the reifier only (`KQR.v` takes any bounds already):
when a program is not read with the bounds of the index and the smallest own bound, it is read again without the well-formedness
check, the calls of each function collected from its tree (`cl_*`, a traversal of every sort of `S`, the shared-block check's
shape), and the bounds worked out from the entry down — the entry's the smallest (its counters come from `kq_nat`), each callee's
above the largest counter any caller gives it (`cmax` over the caller's bound) — and the program read a third time with those
bounds, every function checked by `wf_f`.  A bound above 2^62 is refused by `wf_f` (`bok`).  Programs read today are read as
today (their statements unchanged).  *Expected*: the cell.

**Step 34 done (2026-11-02): counter bounds worked out from the call graph.**  Built as designed, in the reifier (`KQR.v` and
`kitc.py` unchanged): `reify_fun` takes a bound table and can read without the check; `reify_prog2` reads as before and, when that
fails, reads without the check, collects each function's calls (`cl_*`, generated from KQR's shared-block traversal: each call its
callee and its counters), works the bounds out from the entry down (`bounds_tab`: the entry `own_bound`, each callee above the
largest counter any caller gives it, `cmax` over the caller's bound) and reads again with them.  Programs read before are read the
same way (the first reading succeeds; their statements unchanged).  Test `w34*` (the cell's shape): the bounds pinned (the entry
`own_bound`, the function given a successor one more, its callee given the sum twice that and one), the three theorems in
milliseconds.  The C: 63 of 63 byte-identical.  The construct table (on `ca1ff4f`): **782 of 802 through the verified compiler**
(was 781: `A_par_nat_add_called_succ`), 19 gaps, 1 not Rocq.  The gate on `ca1ff4f`, the walk switched off: `make.sh` `core-ok`;
examples 27 / 27; corpus 36 / 36; the five kernels (12 / 13 / 12 / 15 / 14 s on the work machine, against 11 / 11 / 11 / 13 / 13
at step 33 — so measured apart, on one machine, cold, interleaved: the whole build of `HWP_kernel` 9.46 / 9.31 s with step 32's
files and 9.20 / 9.26 s with step 34's, `HWP_own` 9.80 / 9.75 s and 9.64 / 9.53 s: the same; the work machine's runs vary by a
second or two); **71 programs through the verified compiler, 0 refused**; the trusted base unchanged.

**Step 35, a bound for each counter variable — the design (2026-11-02).**  The counter gaps left: a sum bound by a let, a let of a
successor of a variable, a sum compared, a match on a sum (`A_par_nat_let_add`, `_let_succ`, `_eqb_add`, `_match_add`, added with this
design).  Each binds or tests a counter that can be above the function's bound: one bound for all of a function's counters (`cbj`)
cannot hold both `n` and `n + n`.  So each counter variable carries its own bound:
- *KQR*: the bounds of the counters in scope (`cbs`, nearest first) travel in `wf`'s first argument with the callees and the own
  bound — a parameter's the function's bound, a let's `cmax cbs c + 1`, a match's predecessor the matched variable's — and `cmax`
  reads them (a variable its own bound less one).  `wf` asks every bound pushed to be at most 2^62 (a machine number with room), a
  callee's counters below its bound, the recursive call's below the function's bound, a comparison's below `wB`; `letc_ok`'s
  depth rule and `shallow` in comparisons go (the bounds cover them).  The invariant's `cbound` becomes one bound per variable;
  `cexp_all`'s counter part asks `cmax cbs c < wB` of the variables' own bounds; a let and a match push their bound.
- *The reifier*: unchanged but for a match whose subject is a counter expression (read as a let of it and a match on the variable,
  the same term up to zeta).
*Expected*: the four cells.  *Not in this step, a cell of its own*: the recursive call giving a counter its successor
(`A_par_nat_rec_succ`, `k p (S m)`): its value stays below the sum of the two counters' starting values, which no bound of one
variable says — it needs a bound relating two counters (step 36).

**Step 35 done (2026-11-03): a bound for each counter variable.**  Built as designed, in `proved/KQR.v` and the reifier:
- *`KQR.v`*: `wf`'s first argument carries the bounds of the counters in scope (`list sig * (option Z * list (option Z))`: the
  callees, the own bound, the counters' bounds, the nearest first; `None` a counter below the function's bound).  `cmaxv B bs c`
  is a counter's largest value, each variable below its own bound (`cbv`); a call checks `cmaxv` of its counters below the
  callee's bound; the recursive call's counters are flat with their variables at the function's bound (`pvars`); a let of a
  counter pushes `lbnd` (none when step 9's `letc_ok` holds of a counter whose variables are at the function's bound, else
  `cmaxv + 1`, at most 2^62: `letc_okv`); a match on a counter pushes the matched variable's bound for the predecessor; a
  comparison of counters asks `cmaxv < wB`.  For every program read before, every bound pushed is `None`, so `wf` accepts what
  it accepted.  The proof: the invariant's bound is one per variable (`cboundv cbj cbs cenv`: each counter below its own bound,
  each bound at most 2^62); the mutual lemma's motives, the memory, tail and pair lemmas quantify the bounds (`sigsv cbs`), a
  let and a match push theirs (`inv_clet`, `inv_cpush`, `lbnd_bound`); the merged calls' lemmas take one bound list (a nested
  section: a chain of tests binds no counter); `compile_f_ok` starts from none (`cboundv_nil`).  No new hypothesis; `Print
  Assumptions` the same base.  Tests: `klet` (a sum bound by a let, given to a callee), `kls` (a let of `S n` at the index's
  bound), `kcmp` (a sum compared, at the index's bound), `kmt` (a match on a sum), each theorem in milliseconds; refused: a let of
  a sum at the index's bound, the recursive call given a let-bound sum, a let-bound sum given to a callee whose bound it passes,
  a tree that is not the text.  Step 33's test of a sum compared, refused then, is accepted.
- *The reifier*: a match on a counter that is not a variable is read as a let of it and a match on the variable (`let_scrut`,
  the same term up to zeta) in the six readers that have a counter let; the call-graph bounds (step 34) track the counters'
  bounds as `wf` does (`cl_*` take the function's bound and the bounds in scope and give each call's largest counter,
  `cmaxsv`, a let's bound `lbndv` = `lbnd`).  Tests: `w35go` (the four cells' shapes, small helpers written out into one
  function, read with the smallest own bound), `w35b` (a function binding `n + n` and given `S n` by the entry: its callee's
  bound worked out through the let's), `lcbad` (step 9's let of `S n`, refused then, read now); every theorem in milliseconds.
- *Cells*: 11 more (815): a match on a counter in every result kind's place — on a sum for a boolean in a test, a boolean given
  back, a memory, a number made after memories, a pair, a record given back, a number and a memory given back; on a counter
  variable for a pair, a record of three, a pair of pairs, a number and a memory (the table had none).  Run alone: 6 proved, 5
  refused — a boolean-valued match on a sum inside a test (the boolean sort has no counter let), a pair or a record chosen by a
  counter match, on a variable or a sum (the record sort has no counter match): the next step.
- *The reifier's step on the kernels' programs* (one machine, interleaved, step 34's files / step 35's): `HWP_kernel` 2.84 / 3.07 s
  against 2.83 / 2.88 s, `HWP_own` 2.31 / 2.18 against 2.19 / 2.20, `HWP_irqnow` 1.86 / 2.57 against 1.97 / 1.87 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `e79f85f`): **792 of 815 through the verified compiler** (was 782 of
  802: the four step-35 cells and six of the eleven new), 22 gaps (the five new cells refused, `A_par_nat_rec_succ`, the sixteen
  left before), 1 not Rocq.  The gate on `e79f85f`, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36;
  the five kernels (11 / 11 / 11 / 18 / 13 s on the work machine — measured apart, one machine, cold, interleaved, on one core:
  `HWP_kernel` 11.62 / 10.76 s with step 34's files and 10.92 / 10.87 s with step 35's, `HWP_own` 11.50 / 11.34 and 11.26 / 11.15 s:
  the same; the work machine's runs vary); **71 programs through the verified compiler, 0 refused**; the trusted base unchanged.

**Step 36, the boolean and record sorts given the constructs of the number sort — the design (2026-11-03).**  The number sort has, for
each way a value can be made, a node: a test on a comparison or on a boolean, a let of each kind (number, boolean, counter, record), a
match on a counter, a record taken apart.  The boolean sort (`sbool`) has the test on a comparison (`BIfCmp`) and the counter match
(`BMatchCnt`) only; the record sort (`srec`) has the number let, the record let and the test on a comparison only.  So a boolean or a
record made any other way is refused wherever it stands: a boolean chosen by a test on a boolean (`if (a <? b) && c then x else y`
in a test), a let in a later operand of `&&` (`P_int_if_and_let`, step 8's place), a record taken apart inside a test (`let '(x, y) :=
hp a b in x <? y`), a boolean-valued match on a sum (`P_bool_match_add`, step 35's place), a record or pair chosen by a counter match
(`P_pair_match_nat`, `P_rec3_match_nat`, `P_pairp_match_nat`, `P_pair_match_add`, found with step 35's cells), a record chosen by a
test on a boolean, a boolean let inside a record.  The constructs, each the counterpart of a number node already proved:
- *`sbool`*: `BIfB b x y` (`SIfB`), `BLet e x` (`SLet`), `BLetB b x` (`SLetB`), `BLetC c x` (`SLetC`, its counter's bound pushed as
  step 35's), `BLetR r x` (`SLetR`), `BMatchR r x` (`SMatchR`).  Each compiled in the three forms a boolean is compiled to (a jump, a
  value, a choice of two atoms): the let's code, then the boolean's in the extended environment; a test on a boolean, the jumps of
  `ccond`, then the branch's form.  Proof: one case of each of the three parts of `cexp_all`'s boolean statement per node, the shape of
  the number node's case; `denote_nomem`, `denote_rec_ext` one case each.
- *`srec`*: `RIfB ri b x y` (`SIfB`), `RLetB b x` (`SLetB`), `RLetC c x` (`SLetC`), `RMatchCnt ri c x y` (`SMatch`, the predecessor
  pushed with the matched variable's bound).  Meanings that put the choice inside one record value, as `RIf` does (step 21: a test of
  two record values does not convert to the user's text taken apart).
- *The reifier*: these in `reify_b` / `reify_r`; a match on a counter expression read as a let and a match there too (step 35's
  `let_scrut`); the reasons scan, `cl_b` / `cl_r` (the bounds tracked).
- *Cells*: a boolean chosen by a test on a boolean, a number let and a record taken apart inside a later operand, a record or a pair
  chosen by a test on a boolean, a boolean let inside a record — beside the six step 35 left.
*Expected*: those cells and step 35's five gaps, `P_int_if_and_let`.  *Not in this step*: the relational bound (step 37,
`A_par_nat_rec_succ`).

**Step 36 done (2026-11-03): the boolean and record sorts given the constructs of the number sort.**  Built as designed:
- *`KQR.v`*: `BxIfB`, `BxLet`, `BxLetB`, `BxLetC`, `BxLetR`, `BxMatchR` among the booleans and `RIfB`, `RLetB`, `RLetC`, `RMatchCnt`
  among the records, each with the meaning of its number counterpart (the records' choices inside one record value, as `RIf`'s),
  its KQL in the boolean's three forms (a test on a boolean is the test's jumps, then the branch's form; a let is the value's code,
  then the boolean's) and in the record's, well-formedness (a counter let pushes its bound, step 35; a record match on a counter
  pushes the matched variable's), the shared-block rule.  Proof: one case each in each of the three parts of `cexp_all`'s boolean
  statement and in its record part, `denote_nomem`, `denote_rec_ext`, `kind_denote_r` (its induction now generalizes the
  environments and the bounds).  No new hypothesis; `Print Assumptions` the same base.  Tests (`x36_P`): `xbif` (a test on a
  boolean, as a choice), `xbifj` (as jumps), `xblet` (a number let in a later operand of `&&`), `xbletb` (a boolean let, as the
  boolean's value), `xbletc` (a counter let, its bound pushed), `xbmr` / `xbletr` (a record taken apart, a record let, in a
  boolean), `xrifb` / `xrletb` / `xrmc` / `xrletc` (a record chosen by a test on a boolean, a boolean let in a record, a record
  chosen by a counter match, a counter let in a record); refused: records of two types in a test on a boolean, a counter let at
  the index's bound, a test's branches the other way round; each theorem in milliseconds.
- *The reifier*: the boolean reader starts as the number reader does (`head_r`: lets read by zeta, constructor lets, iota) and reads
  a match on a value of a data type as a test chain on its tag (step 28), lets of every kind, a test on a boolean, a match on a
  counter expression (`let_scrut`), a record taken apart; the record reader reads the tag chain (its type off the match's
  return type), boolean and counter lets, a test on a boolean, a match on a counter; the call collection has the new nodes'
  bounds.  Test `x36go` (the seven shapes of the construct table, helpers written out): the tree pinned, the theorem in
  milliseconds.
- *Found on the way*: `Fail Check (eq_refl : f = denote_f ..)` on a tree whose test has its branches the other way round made
  Rocq raise `Anomaly ""` instead of failing; `Fail Definition .. := eq_refl` refuses the same tree normally (the form the other
  tests use).
- *Cells*: 10 more (825): a boolean chosen by a test on a boolean, a number let in a later operand of `&&`, a record taken apart
  and a match on an `option` in a boolean, a pair and a record of three chosen by a test on a boolean, a boolean let and a counter
  let in a pair, a match on an `option` giving a pair and a record of three.  Run alone: all 10 proved, and with them four of the
  five step 35 left (`P_bool_match_add`, `P_pair_match_nat`, `P_pair_match_add`, `P_rec3_match_nat`) and step 8's `P_int_if_and_let`.
  `P_pairp_match_nat` stays refused: a record holding records comes into the record table from the signatures only (step 32), so a
  pair of pairs chosen by a counter match inside a body is the records-as-values step's.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, settled rounds; step 35's files / step 36's):
  `HWP_kernel` 2.74 / 2.65 / 2.76 s against 2.81 / 2.90 / 2.89 s, `HWP_own` 2.10 / 2.02 / 2.04 against 2.14 / 2.17 / 2.14, `HWP_irqnow`
  1.80 / 1.68 / 1.70 against 1.77 / 1.77 / 1.72 — about 0.15 s (5 %) more on `HWP_kernel`, within the spread step 32 recorded.
- The C: 63 of 63 byte-identical.  The construct table (on `c764f08`): **807 of 825 through the verified compiler** (was 792 of
  815: the ten new cells, four of step 35's five and `P_int_if_and_let`), 17 gaps, 1 not Rocq.  The gate on `c764f08`, the walk
  switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 11 / 12 / 14 / 13 s); **71 programs
  through the verified compiler, 0 refused**; the trusted base unchanged.

**Step 37, counters grown by the recursion: a bound on a weighted sum — the design (2026-11-03).**  `A_par_nat_rec_succ`:
`k (n m : nat) x := match n with O => x | S p => k p (S m) (x + 1) end` — an index counting up while the budget counts down, the
ordinary way to walk positions with `nat`.  The recursive call's counters must stay below the function's bound at every round;
`S m` is not below `m`'s bound, but `p + S m = n + m`: the sum does not grow.  So a function whose recursion grows a counter is
proved for counters whose **weighted sum** is below its bound, and the recursion keeps the weighted sum from growing:
- *Signature*: `sig` gains the weights `sv : list nat` (none: each counter below the bound, as today; else one weight of at least 1
  per counter, the first the recursion's).  `callee_ok`'s premise on the counters given is `cfits gs B cvs`: each below `B`, or
  `Σ wᵢ·cᵢ < B` — which gives each below `B` (weights at least 1), so the body's invariant is as today plus the weighted sum.
- *The recursion*: its counters after the first may be any counter expressions whose weighted sum, with the predecessor first,
  is at most the current one: with each counter variable in scope carrying a linear upper bound over the function's counters
  (a parameter itself, a let its expression's, a match's predecessor its variable's less one), `wf` checks coefficient by
  coefficient that `Σᵢ≥₂ wᵢ·lin(c′ᵢ) ≤ w₁ + Σᵢ≥₂ wᵢ·mᵢ`.  `k p (S m)` takes weights `[1; 1]`, `k p (m + 2)` `[2; 1]`, two counters
  swapped equal weights.  A counter grown by the predecessor itself (`k p (m + p)`) grows quadratically: no weighted sum bounds
  it; with a budget from the data it outgrows a machine number (§0.5's second reason), with a written budget it does not — not in
  this step, a cell of its own.
- *A call of such a function*: `wf` asks `Σ wᵢ·cmaxv(cᵢ)` below the callee's bound (the call-graph bounds, step 34, the same).
- *Proof*: the invariant gains the parameters' values (the bottom of the counter environment) and, per counter variable, its
  value below its linear bound evaluated at them; the recursive call's premise from the coefficient check; `compile_f_ok`'s
  induction on the first counter with `cfits` in place of each-below.
- *The reifier*: a function not well formed only because its recursion grows a counter is read again with weights, the smallest
  satisfying the check (a small linear search: the constraints are `wⱼ ≥ Σᵢ wᵢ·coefᵢⱼ`, `w₁ ≥ Σ wᵢ·constᵢ`); `kitc.py` prints them.
*Expected*: `A_par_nat_rec_succ`, and cells for `k p (m + 2)`, a swap, a let-bound successor given to the recursion; the cell of a
growth by the predecessor refused (its own step).

**Step 37 done (2026-11-03): counters grown by the recursion, bound by a weighted sum.**  Built as designed, and in the general
form at the places its cells found narrow:
- *`KQR.v`*: `sig` gains the weights `sv` (`mksig8`; `mksig7` is a signature without them).  `callee_ok`'s premise on the counters
  given is `cfits` (each below the bound, or `Σ wᵢ·cᵢ` below it); `wf_f` asks one weight per counter, each at least 1 (`swok`).
  Each counter variable in scope carries, beside its bound, a linear bound over the function's counters (`cbe`, `linf`: a
  parameter its own unit, a let its expression's `clinf`, a match's predecessor its variable's less one; a recursive body starts
  with the first counter's predecessor, `wctx`).  The recursion's counters (`rec_ok`): with weights, `pot_ok` coefficient by
  coefficient (`Σᵢ≥₂ wᵢ·lin(c′ᵢ)` against the weights, none on the first counter, the constant at most `w₁`), each below 2^63;
  without weights, a flat variable at the function's bound (step 35) **or at most one of the function's counters** (`lin1`: no
  coefficient below 0, their sum at most 1, no constant above 0 — `k p (S p)`), each below 2^63.  A call of a function with
  weights asks `Σ wᵢ·cmaxv(cᵢ)` below the callee's bound (`cfits_b`).  A written budget's largest value is its own (`cnat_max`,
  in `cmax`, `cmaxv` and `clinf`; a mutual block's selector is one).  The proof: the invariant `cboundv cbj cbs pv cenv` holds
  the parameters' values `pv` (the bottom of the counter environment) and each variable's value below its linear bound at them;
  the recursion's premise (`rec_ok_fits`) from `pot_sound` (with weights: the weighted sum given at most the current one) or
  `lin1_lt` (without: below the largest of the function's counters); `compile_f_ok`'s induction on the first counter with `cfits`
  in place of each-below (`cfits_forall`: weights at least 1 put each counter below the bound).  The copies' theorems
  (`compile_f_okr`, `okrm`, `okrx`) take any bound and any weights; they took neither, so a copy with a bound had no theorem.
  No new hypothesis; `Print Assumptions` the same base.  Tests: `krs` (`k p (S m)`, weights `[1; 1]`), `krt` (`k p (m + 2)`,
  `[2; 1]`), `krw` (a swap with a growth, `[1; 1; 1]`), `krl` (a let-bound successor), `krg` (a call giving `n n`, its weighted
  sum below the callee's bound), `krp` (`k p (S p)`, no weights); refused: the growth without weights, weights too small, a zero
  weight, weights of the wrong number, `k p (m + p)` with any weights, a call whose weighted sum passes the callee's bound, the
  predecessor's second successor, a tree that is not the text; each theorem in milliseconds.
- *The reifier*: the call-graph walk (step 34) runs on the new bound lists and collects the recursive calls (`cl_f`, `site`);
  `wts_of` gives no weights when each recursive call's counters pass without them, else the smallest satisfying `pot_ok`, by
  rounds from all ones (each weight raised to what the calls' linear bounds ask of it; none when the rounds do not settle).  The
  entry's bound with weights covers each counter at the smallest bound's value (`own_w`); the call-graph bounds ask a callee
  with weights the weighted sum of what it is given and start only the entry at `own_w`.  Every way a function is read — a
  function, a template's copy, a local fixpoint's copy, a mutual block and its members — takes its signature from one function
  (`wf_sig`: as read, the call graph's bound, the smallest own bound, weights); before, the copies and the blocks were tried as
  read only (narrow since steps 33 and 34).  `info_of` gives the weights; `kitc.py` prints `mksig8` with them and gives a copy's
  theorem its bound and weights.  Tests: `grow` (refused since step 9; read with `[1; 1]`, its theorem), `w37go` (the four
  shapes called with their weighted sums: `[1; 1]`, `[2; 1]`, `[1; 1; 1]`, `[1; 1]`, bounds from the call graph), `w37p`
  (`k p (S p)`, no weights), `w37q` (`k p (m + p)`, refused with its reason); each theorem in milliseconds.
- *Found on the way*: F59, F60, F61.
- *Cells*: 18 more (843): a counter grown by the recursion in every result kind's place (a boolean, a memory, a pair, a record
  of three, a pair of pairs, a number and a memory, a number function that writes the memory); grown by a constant, swapped,
  through a let, two grown, under a match on another counter, the function called by a recursion, a template, a mutual block;
  the predecessor's successor; grown by the predecessor (`k p (m + p)`) from the data and from a written budget.  Run alone:
  15 proved, with them `A_par_nat_rec_succ`; 3 refused: `A_par_nat_rec_two_succ` (`k p (S c) (S d)` given `n n n` by the entry:
  its weights add to at least 4, and a weighted sum of three counters at 2^60 passes 2^62 while the counters stay below 2^61 —
  one weighted sum per grown counter bounds it: the next step), `A_par_nat_rec_add_pred_lit` (quadratic growth from a written
  budget: bounded, not read: a step of its own), `A_par_nat_rec_add_pred` (the same from the data: the counter outgrows a
  machine number, §0.5's second reason; by design once its control, the written-budget cell, is read, §3.6).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 36's files /
  step 37's): `HWP_kernel` 2.93 / 2.99 s, `HWP_own` 2.31 / 2.25, `HWP_irqnow` 1.90 / 1.93 — the same (the machine was loaded: the
  rounds spread from 2.9 to 4.6 s).
- The C: 63 of 63 byte-identical.  The construct table (on `6f87d43`): **823 of 843 through the verified compiler** (was 807 of
  825: fifteen of the eighteen new cells and `A_par_nat_rec_succ`), 19 gaps, 1 not Rocq.  The gate on `6f87d43`, the walk switched
  off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 11 / 12 / 14 / 12 s); **71 programs through
  the verified compiler, 0 refused**; the trusted base unchanged.

**Step 38, counters grown apart: several weighted sums — the design (2026-11-03).**  `A_par_nat_rec_two_succ`:
`k (n c d : nat) x := match n with O => x | S p => k p (S c) (S d) (x + 1) end`, given `n n n` by the entry.  One weighted sum
needs `w₁ ≥ w₂ + w₃`, so its weights add to at least 4, and three counters at `kq_nat`'s 2^60 give a sum past a machine number's
room (2^62), while each counter stays below 2^61: `n + c` and `n + d` never grow.  The single weighted sum is the narrow form;
the general one is a set of them:
- *Signature*: the weights become a list of weight vectors (`sv : list (list nat)`), each one weight per counter, at least 0,
  each counter with a weight of at least 1 in one vector at least.  `cfits`: every vector's weighted sum below the bound — which
  puts each counter below it, through a vector where its weight is at least 1.  Step 37's single vector is a list of one.
- *The recursion*: `pot_ok` for each vector (a weight of 0 asks its counter's coefficient to be at most 0).
- *A call*: each vector's `Σ wᵢ·cmaxv(cᵢ)` below the callee's bound.
- *Proof*: step 37's, for each vector: the invariant's premise per vector (the weighted sum at the parameters below the bound),
  `pot_sound` per vector, `cfits_forall` through the vector that covers each counter.
- *The reifier*: no weights when the recursion's counters pass without them; else one vector from step 37's rounds when its
  bound fits; else one vector per counter, each by the rounds from that counter's unit vector (each weight raised to what the
  calls' linear bounds ask: `e_c` grows to `e_1 + e_c` for a counter grown by one), the vectors kept that `pot_ok` takes and
  their union covering every counter; `kitc.py` prints them.
*Expected*: `A_par_nat_rec_two_succ`, and cells for three counters grown apart (`k p (S c) (S d) (S e)`), one grown by two
per round beside one grown by one (`k p (c + 2) (S d)`), two grown apart beside a swapped pair (`k p (S c) (S e) d` with `d`,
`e` swapped each round), each given its counters by the entry.  *Not in this step*: growth by the predecessor
from a written budget (`A_par_nat_rec_add_pred_lit`, quadratic: its bound is not linear in the counters).

**Step 38 done (2026-11-03): counters grown apart, several weighted sums.**  Built as designed:
- *`KQR.v`*: the weights are a list of vectors (`sv : list (list nat)`); `swok` asks each vector one weight per counter and
  every counter a weight of at least 1 in one vector; `cfits` asks every vector's weighted sum below the bound; the recursion
  asks `pot_ok` of each vector (`rec_ok`), a call each vector's `Σ wᵢ·cmaxv(cᵢ)` below the callee's bound and each counter given
  below 2^63 (`cfits_b`; the weights at least 1 that gave the latter in step 37 are now asked of the coverage only).  The
  proof: the invariant's premise per vector (`Hpv`), `pot_sound` per vector (`rec_ok_fits`), `cfits_forall` through the vector
  that covers each counter (`dotw_ge_nth`: a counter whose weight is at least 1 is at most the weighted sum).  No new
  hypothesis; `Print Assumptions` the same base.  Step 37's tests take their single vector as a list of one.  Tests: `krd`
  (`k p (S c) (S d)`, vectors `[1; 1; 0]`, `[1; 0; 1]`), `krdg` (a call giving `n n n` at 2^61: each sum fits where one of the
  three would not); refused: one weighted sum of the three for that call, a counter no vector covers, a vector whose sum grows;
  each theorem in milliseconds.
- *The reifier*: one vector per counter, each the smallest above that counter's unit vector by step 37's rounds (each at most
  the vector step 37 took from all ones), the same vectors once; the entry's bound and the call-graph bounds take the largest
  vector sum (`wmax`); the weights are worked out only when the signature without them is refused (`wf_sig`; `vm_compute`
  evaluates a `let` at once).  `kitc.py` reads and prints the vectors.  Tests: step 37's pinned weights as vectors (`grow`
  `[1; 0]`, `[1; 1]`; `w37go`'s four), `w38go` (`k p (S c) (S d)` given `n n n`: `[1; 0; 0]`, `[1; 1; 0]`, `[1; 0; 1]`, its
  bound twice the smallest bound's value); each theorem in milliseconds.
- *Cells*: 3 more (846): three counters grown apart, one grown by two beside one by one, two grown beside a swap.  Run alone:
  all three proved, and with them `A_par_nat_rec_two_succ`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 37's files /
  step 38's): `HWP_kernel` 2.88 / 2.84 s, `HWP_own` 2.27 / 2.11, `HWP_irqnow` 1.85 / 1.76 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `03f83e9`): **827 of 846 through the verified compiler** (was 823 of
  843: the three new cells and `A_par_nat_rec_two_succ`), 18 gaps, 1 not Rocq.  The gate on `03f83e9`, the walk switched off:
  `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 11 / 12 / 13 / 12 s); **71 programs through the
  verified compiler, 0 refused**; the trusted base unchanged.

**Step 39, counters grown by other counters: polynomial weighted sums — the design (2026-11-03).**  The last cells of the
counter family (the record of 2026-11-02's first item): `A_par_nat_rec_add_pred_lit`, `k (n m : nat) x := match n with O => x |
S p => k p (m + p) (x + 1) end` from a written budget (`k 100 0 a`): `m` grows by the predecessor, about `n²/2` in all.  No
weighted sum of the counters bounds it (a sum grown by `p` each round), but `2m + n² + n` never grows: with `n = p + 1`,
`2m + (p + 1)² + (p + 1) − (2(m + p) + p² + p) = 2`.  So the weights become polynomials:
- *Signature*: each weight vector becomes a polynomial in the counters — monomials, each a coefficient (a natural number) and
  the counters it multiplies (a list of indices); a degree-1 polynomial is step 38's vector.  `cfits`: each polynomial at the
  counters below the bound; every counter has a degree-1 monomial of coefficient at least 1 in one polynomial (so it is below
  the bound).
- *The recursion*: for each polynomial `Φ`, `Φ(old) − Φ(new) ≥ 0` coefficient by coefficient over the predecessor and the
  other counters, all at least 0: the old first counter `p + 1`, each new counter at most its linear bound (`Φ` has no
  coefficient below 0, so it grows with each argument); the products expanded (`pmul`, `padd`), equal monomials cancelled
  (`pnonneg`).  Step 38's `pot_ok` is the degree-1 case.
- *A call*: each polynomial at the largest values of the counters given (`cmaxv`) below the callee's bound.
- *Proof*: `peval` of a sum and a product; `Φ` monotone in each counter; the check's soundness (`pnonneg p = true -> 0 <= peval
  p pv` for counters at least 0); the invariant's premise per polynomial; `cfits_forall` through a degree-1 monomial.
- *The reifier*: for each counter its polynomial by rounds from its unit vector, as step 38, and when a round asks a weight on the
  first counter (a counter grown by the predecessor), the polynomial gains the first counter's square times that weight's need
  (and degree 3 for a counter grown by a counter grown by the predecessor, and so on, up to a small degree); the result checked
  by `wf_f`.
*Expected*: `A_par_nat_rec_add_pred_lit`; `A_par_nat_rec_add_pred` refused (from the data `2m + n² + n` passes 2^62: the counter
outgrows a machine number, §0.5's second reason) and, with its control read, moved to `DESIGN_CELLS`; cells for growth by the
predecessor in a mutual block and in a template, a counter grown by a counter grown by the predecessor (degree 3) from a written
budget, and a growth by the predecessor's successor.

**Step 39 done (2026-11-03): counters grown by other counters, polynomial weighted sums.**  Built as designed:
- *`KQR.v`*: the weights are polynomials in the counters (`poly`: monomials, each a coefficient and the counters it multiplies);
  `swok` asks every counter a monomial of its own with a coefficient of at least 1; `cfits` asks each polynomial at the counters
  below the bound (`pevalz`); the recursion's check `ppot_ok`: the polynomial at the body's start (the first counter the
  predecessor's successor) less the polynomial at the recursive call's counters' linear bounds (`zlin`), expanded over the
  predecessor and the other counters (`zsubst`, `zmul`), equal monomials summed once their counters are sorted (`zcoef`), no
  coefficient below 0 (`znonneg`); a call asks each polynomial at the counters' largest values below the callee's bound.  Step 37's
  check of the weights' number is gone: a monomial of a counter the function does not have multiplies 0 at both ends, so no
  theorem needs it (§3.6's rule), and that test is now accepted.  The proof: `ppot_sound` from `znonneg_sound` (the coefficients
  summed over sorted monomials, `prodz_isort`), `pevalz_zsubst`, `pevalz_mono` (a polynomial with no coefficient below 0 grows
  with each counter) and `zeval_zlin` (a linear bound over the body's start as a polynomial in the predecessor and the other
  counters); `rec_ok_fits` takes the recursive call's number of counters (checked where it is used); `cfits_forall` through the
  counter's own monomial (`pevalz_unit`).  No new hypothesis; `Print Assumptions` the same base.  Steps 37 and 38's tests take
  their vectors as polynomials of degree 1 (`lpoly`).  Tests: `krq` (`k p (m + p)`, the polynomial `2m + n² + n`) called from a
  written budget (`krqg`, 100); refused: the same given `n n` at 2^61, a polynomial of degree 1, a counter with no monomial of its
  own; each theorem in milliseconds.
- *The reifier*: each counter's polynomial is step 38's vector when the check takes it, else `c + n·G` with `G` the counter's
  growth per round — the recursive calls' linear bounds (the largest coefficient of each), the first counter's coefficient for
  the predecessor, a positive constant, each other counter replaced by its own polynomial — in the order the counters depend on
  each other (`ppoly`; none for a counter grown by itself by more than one per round, or a cycle); the entry's own bound and the
  call-graph bounds take the largest polynomial value (`wmax`, `own_w` with the number of counters).  `kitc.py` reads the weights
  to the end of each function's tuple (by bracket matching) and prints the polynomials.  Tests: step 38's pins as polynomials;
  `w39go` (`k p (m + p)` from 100: `m + n²`; a counter grown by it from 50: `q + n·m + n³`; each function the smallest own bound),
  `w39d` (the same from the data: refused); each theorem in milliseconds.
- *Cells*: 5 more (851): growth by the predecessor's successor, a counter grown by one grown by the predecessor (degree 3), growth
  by the predecessor in a mutual block and in a template, a recursive function passing small written counters on.  Run alone: 3
  proved, and with them `A_par_nat_rec_add_pred_lit`; 2 refused: `A_par_nat_rec_add_pred_mutual` and `_pass` — the function in
  between (a block's member, a recursive function) has a bound of at least 2^60 + 2^20 (`bok`: every bound holds a budget, up to
  2^60), so its callee's polynomial at its counters passes 2^62; a function's bound below that, from what its callers give it, is
  the next step.  `A_par_nat_rec_add_pred` (from the data) is by design: the counter reaches about n²/2, beyond a machine number
  (§0.5, second reason); its control is the written-budget cell (`DESIGN_CELLS` in `classify.py`).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 38's files /
  step 39's): `HWP_kernel` 2.73 / 2.71 s, `HWP_own` 2.07 / 2.05, `HWP_irqnow` 1.74 / 1.77 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `7fb6b50`): **831 of 851 through the verified compiler**, 1 by design
  (`A_par_nat_rec_add_pred`), 18 gaps, 1 not Rocq (was 827 of 846: three of the five new cells and `A_par_nat_rec_add_pred_lit`).
  The gate on `7fb6b50`, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels
  (11 / 11 / 11 / 13 / 13 s); **71 programs through the verified compiler, 0 refused**; the trusted base unchanged.

**Step 40, a function's bound from what its callers give it, however small — the design (2026-11-03).**
`A_par_nat_rec_add_pred_mutual`, `A_par_nat_rec_add_pred_pass`: a function between the entry's written counters and one whose
polynomial grows (a mutual block's member, a recursive function passing its counters on) gets a bound of at least 2^60 + 2^20,
because every bound must hold a budget (`bok`'s lower end; `cbz_big` in the proofs): its callee's polynomial at its counters then
passes 2^62.  The bound the call graph works out for it (step 34) is 101; nothing but that lower end refuses it.  So:
- *`KQR.v`*: `bok` asks a written bound to be at least 1 and at most 2^62.  The seven places the proofs use the lower end become
  checks of the counter's largest value against the bound, which for a written bound is the same number in `wf` (`ub`) and in
  the theorem (`cbj`): a let of a counter takes the function's bound (`lbnd`'s none) only when its largest value is below it as
  well as `letc_ok`; the recursion's flat counter (step 35's rule) likewise; a budget given to the recursion or bound by a let is
  below a small bound only when its written value is (`cnat_max`).  A bound left to the index (`None`, `cbz`) keeps today's room.
- *The reifier*: the call-graph bounds start a function that is not the entry at 1 and raise it to what its callers give it; the
  entry keeps the smallest own bound (`kq_nat`'s counters).
- *Proof*: `cbz_big` splits on the bound: written, the explicit checks; left to the index, as today.
*Expected*: the two cells; the bounds of programs read before unchanged (the first reading succeeds); cells for a function in
between that is a template, and for a let of a budget in a function with a small bound.

**Step 40 done (2026-11-03): a function's bound from what its callers give it, however small.**  Built as designed:
- *`KQR.v`*: `bok` asks a written bound to be at least 1 (it asked more than 2^60 + 2^20); a let of a counter takes the function's
  bound only when its largest value is below it as well (`lbnd`, `letc_okv`), and the recursion's flat counter likewise (`rec_ok`).
  The proof: `cbz_big` holds of a bound left to the index only; a written bound is the one `wf` checks against (`ub_cbj`), so the
  checks give the theorem's bound (`fits_cbj`, `flatv_cmax`); the counters at most one of the function's counters need only a bound
  above 0 (`cbj_pos`).  With the budgets' room the new checks always hold, so every program read before is read the same.  No new
  hypothesis; `Print Assumptions` the same base.  Tests: `kpas` (a recursive function passing 100 and 0 on, its bound 101) and
  `krq` (its bound 20000, above its polynomial at 100: 10300), `kpasg`; a bound of 1000 taken (refused before, a test of step 33);
  refused: a bound of 0, a written budget above a small bound given to the recursion or bound by a let, a caller giving more than
  the bound; each theorem in milliseconds.
- *The reifier*: when the call-graph bounds (step 34) fail, the program is read once more with them worked out from 1 for every
  function but the entry (`bounds_tab true`); programs read before keep their bounds.  Test `w40go` (`w40p`, a recursive function
  passing 100 and 0 on: its bound 101; `w39q`'s 10101; the entry the smallest own bound); each theorem in milliseconds.
- *Cells*: 2 more (853): a template in between, a let of a written budget in a function with a small bound.  Run alone: both
  proved, and with them `A_par_nat_rec_add_pred_mutual` and `_pass`.  The counter family has no gap left.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 39's files /
  step 40's): `HWP_kernel` 2.66 / 2.55 s, `HWP_own` 2.05 / 1.97, `HWP_irqnow` 1.72 / 1.66 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `3dcc757`): **835 of 853 through the verified compiler**, 1 by design,
  16 gaps, 1 not Rocq (was 831 of 851: the two new cells, `A_par_nat_rec_add_pred_mutual` and `_pass`).  The gate on `3dcc757`, the
  walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 12 / 12 / 14 / 12 s); **71 programs
  through the verified compiler, 0 refused**; the trusted base unchanged.

**Step 41, parameters in any order — the design (2026-11-03).**  The second item of the record of 2026-11-02's order (§3.7):
`A_par_conv_nat_second` (`k (x : int) (n : nat)`, the recursion on the second parameter) and `A_par_conv_mem_first` (the memory
before a number).  The reader asks the counters first, the recursion on the first parameter and the memory last — conventions no
theorem needs.  A function whose parameters stand in another order is read as the function in the order the syntax takes (the
recursion's counter first, the other counters, the numbers, booleans and records in their order, the memory last) through a
wrapper, as a template's copy is (step 10):
- *The reifier*: such a function gets a wrapper `k__o := fun (parameters in the syntax's order) => k (in the user's order)`,
  defined in the program as a copy's meaning is; its body read from the user's text with each parameter at its place in the
  syntax's order and each recursive call's arguments put in that order; a call of `k` read as a call of the wrapper, its
  arguments reordered.  The caller's text converts with its meaning: the wrapper applied is `k` applied (one beta step).
- *`KQR.v`*: the wrapper's theorem from its two equations by conversion (`k`'s fix unfolds one step at `S n` whatever parameter it
  recurses on), the copies' theorems (`compile_f_okr`, `okrm`, `okrx`) — and the same for every result kind they do not cover
  yet: a boolean, a record, a number and a memory (`compile_f_okrb`, `okrr`, `okrp`, over the extensionality of each sort's
  meaning in its recursive function: `denote_bb`, `denote_br`, `denote_pv`, as `denote_m_recm_ext` is for memories).  Those
  theorems are also what a template giving back a record needs (a later item of the order).
- *kitc.py*: a wrapper's theorem by its result kind; an entry whose parameters are in another order is called by the driver in
  the syntax's order (the reifier gives the order).
- *Cells*: a counter after a number, the recursion on the second of two counters, a boolean and a record before the counter, the
  memory between two numbers, a function giving back a boolean, a record and a number and a memory with its parameters in another
  order, an entry with its parameters in another order.
*Expected*: the two cells and those.

**Step 41 done (2026-11-03): parameters in any order.**  Built as designed:
- *`KQR.v`*: the copies' theorems for every result kind: `compile_f_okrb` (a boolean), `okrr` (a record), `okrp` (a number and a
  memory), each from the two equations by conversion, over the extensionality of its sort's meaning in its recursive function
  (`denote_bb_recb_ext`, `denote_br_recr_ext`, `denote_pv_recp_ext`, as `denote_m_recm_ext` is for memories) and one lemma that
  moves a function's theorem to any function giving the same at every counters and arguments (`callee_ok_ext`); the bodies'
  parts for them (`fbb0` .. `fpv1`).  No new hypothesis; `Print Assumptions` the same base.  These are also what a template giving
  back a record needs (a later item).
- *The reifier*: a function whose parameters stand in another order (`fun_perm`: the recursion on a counter that is not the
  first, a counter after a number, the memory not last) is read by `read_fun_p`, generated from `read_fun`'s text: the body's
  context in the user's binder order, each parameter counter with its place among the counters in the syntax's order (`CCntP`),
  the fix binder with the order (`CSelfP`), a recursive call's arguments put in that order at every self-call reader
  (`self_perm`); the indices of numbers, booleans and records are counted within their kind, so the user's order already gives
  the syntax's.  The function enters the program as its wrapper `k__o` (`k__on` when it does not recurse), whose meaning is
  `fun (parameters in the syntax's order) => k (in the user's)`; a call of `k` is a call of the wrapper, its arguments reordered
  (`tc_of`), and the caller's text converts with its meaning by one beta step.  The reasons no longer name the order; with the
  parameters in the syntax's order the one refusal left there is two memories.  Tests: `w41go` (`w41a`, the counter after a
  number; `w41b`, the memory before a number; `w41c`, the recursion on the second of two counters; their wrappers' theorems by
  `compile_f_okr`, the entry's by `compile_f_ok`), `w41dgo` (a boolean given back: `compile_f_okrb`); each theorem in milliseconds.
- *kitc.py*: a wrapper takes its copies' theorem by result kind (`okrm`, `okrx`, `okrb`, `okrr` with the record's index, `okrp`,
  `okr`); wrappers are unfolded first as copies are; an entry whose parameters stand in another order gets `main`'s arguments
  in the syntax's order (the reifier gives the order, `entry_perm`): `A_par_conv_entry` built and run gives 105 for 100 and 5.
- *Cells*: 11 more (864): a boolean and a record before the counter, the recursion on the second counter, the memory between two
  numbers, a boolean, a pair, a memory, a number and a memory, and a writing function giving back a number with their parameters
  in another order, an entry with its parameters in another order (`gen.py`: a cell may carry its own `main`); and the two places
  this commit leaves unread, found while building it: a local fixpoint recursing on its second parameter (`A_par_conv_lfix`) and
  a template whose function parameter comes first (`A_par_conv_tmpl`) -- a copy's reading still asks the recursion on the first
  parameter and the counters first.  Run alone: the first 9 proved, and with them `A_par_conv_nat_second` and
  `A_par_conv_mem_first`; the two copies' places refused.  The step goes on with them (below).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 40's files /
  step 41's; the machine loaded): `HWP_kernel` 2.94 / 2.95 s, `HWP_own` 2.24 / 2.35, `HWP_irqnow` 1.93 / 1.95 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `3270bf7`): **846 of 864 through the verified compiler**, 1 by design,
  16 gaps, 1 not Rocq (was 835 of 853: the nine new cells, `A_par_conv_nat_second` and `_mem_first`; the two copies' cells new
  gaps).  The gate on `3270bf7`, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels
  (12 / 12 / 12 / 14 / 15 s; the work machine's runs vary by a second or two, the reifier's step measured apart above); **71
  programs through the verified compiler, 0 refused**; the trusted base unchanged.

**Step 41 continued (2026-11-03): the copies with their parameters in any order.**  The two places the first commit left unread,
in the reifier only (`KQR.v`, `kitc.py` unchanged): a template's copy and a local fixpoint's copy take the template's non-function
parameters in the syntax's order (`nonfn_perm`) — the copy's signature and binders in that order, the template called in its
meaning with them back in the user's order (`copy_meaning_h` takes the order), its body read with the parameter counters' places
(`CCntP`) and its recursive call reordered over all the template's parameters, functions included, before those are dropped
(`CSelfP`, `tdrop` over the reordered types); a call of the template or of the local fixpoint gives its arguments in the copy's
order (`tc_of`); a local fixpoint no longer has to recurse on its first parameter (`sites`).  A copy whose template has its
parameters in the syntax's order is made as before.  Tests: `w41fgo` (a template whose function comes first, a local fixpoint
recursing on its second parameter written out in the entry; the copies' theorems from their two equations, the entry's); each
theorem in milliseconds.  Cells: `A_par_conv_lfix` and `A_par_conv_tmpl` proved; run as a check beside them, 220 of the 224
cells that involve templates, captures and local functions proved, the other 4 the known gaps (three captures, a template giving
back a pair).  The reifier's step on the kernels' programs (one core, interleaved, three rounds, the fastest; the machine loaded;
step 41's first files / these): `HWP_kernel` 4.07 / 4.05 s, `HWP_own` 3.08 / 3.15, `HWP_irqnow` 2.60 / 2.64 — the same.
The C: 63 of 63 byte-identical.  The construct table (on `c825e9a`): **848 of 864 through the verified compiler**, 1 by design,
14 gaps, 1 not Rocq (was 846: the two copies' cells).  The gate on `c825e9a`, the walk switched off: `make.sh` `core-ok`;
examples 27 / 27; corpus 36 / 36; the five kernels (14 / 13 / 14 / 20 / 15 s); **71 programs through the verified compiler, 0
refused**; the trusted base unchanged.

**Step 42, captures of every kind — the design (2026-11-03).**  The third item of the record of 2026-11-02's order:
`A_par_capture_nat` (a function given to a template naming a counter of the caller), `A_par_capture_rec` (naming a record),
`A_par_capture_match` (naming a field bound by taking a record apart, inside a recursion).  A captured variable becomes a
parameter of the copy (step 13), but `sites` reads each one's kind off its binder's type and knows numbers, booleans and the
memory only (`ty_cent`, `cap_ok`), and gives the variables a `match` binds no kind at all (`repeat None`), so the call site is
dropped before a copy is made:
- *Kinds*: a `nat` binder is a counter; a binder of a record type of the program is that record (its index in the record table);
  the variables a `match` binds take their constructor's field types (a counter's predecessor a counter, a record's fields their
  kinds).
- *The copy*: its counters are the template's, then the captured counters; its other parameters the captured numbers, booleans
  and records, then the template's, then a memory (the syntax's order, step 41).  The copy's body sees every parameter counter at
  its place (`CCntP`); its meaning binds the captured counters as `nat` and the captured records at their types; a call gives the
  captured variables in the same order.
- *Proof*: none new — a copy's theorem is about its signature, whatever its parameters stood for in the caller.
  The copy's recursive call passes the captured counters on after the template's counters (`with_caps`), and a copy in the
  syntax's order (step 41) finds its captured variables after its fix binder too (`after_self` reads `CSelfP`).
*Expected*: the three cells, and cells for a captured counter and record together, a counter captured inside a recursion, a
counter captured by a local fixpoint, a template in another order given a function that captures.

**Step 42 done (2026-11-03): captures of every kind.**  Built as designed, in the reifier only (`KQR.v`, `kitc.py` unchanged):
- *Kinds*: `sites` reads a `nat` binder as a counter and a binder of an inductive type as a record carrying its type (`ty_cent`,
  `CRecT`), and gives the variables a `match` binds their constructor's field types (`br_kinds`: a counter's predecessor a
  counter); `cap_ok` takes counters and records.
- *The copy*: its counters are the template's, then the captured counters (`is_capc`); its other parameters the captured
  numbers, booleans and records (a record's kind its index in the record table), then the template's, then a memory; its body
  sees each parameter counter at its place (`CCntP`) and each captured record as a record; its meaning binds a captured counter
  as `nat` and a captured record at its type (`cap_ty`); a call gives the captured counters after the template's counters and the
  other captured variables before its numbers (`tc_of`); the copy's recursive call passes them on the same way (`with_caps`).
  A copy in the syntax's order (step 41) found no captured variables after its fix binder: `after_self` reads `CSelfP` too.
- *Proof*: none new.  Test `w42go` (a function given to a template naming the caller's counter: the copy's two counters, its
  theorem from its two equations); each theorem in milliseconds.
- *Cells*: 4 more (868): a counter and a record captured together, a counter captured inside a recursion, a counter captured by a
  local fixpoint, a template in another order given a function that captures.  Run alone: all 4 proved, and with them
  `A_par_capture_nat`, `_rec` and `_match`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; the step 41
  continuation's files / step 42's): `HWP_kernel` 3.07 / 3.11 s, `HWP_own` 2.35 / 2.41, `HWP_irqnow` 1.97 / 2.03 — the same.
  Run as a check beside the cells: 227 of the 228 cells that involve templates, captures and local functions proved, the other
  the known gap (a template giving back a pair).
- The C: 63 of 63 byte-identical.  The construct table (on `8ab60a6`): **855 of 868 through the verified compiler**, 1 by design,
  11 gaps, 1 not Rocq (was 848 of 864: the four new cells and the three captures).  The gate on `8ab60a6`, the walk switched off:
  `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (12 / 12 / 12 / 14 / 14 s); **71 programs through the
  verified compiler, 0 refused**; the trusted base unchanged.

**Step 43, records holding records as values — the design (2026-11-03).**  The fourth item of the record of 2026-11-02's
order: `A_par_pairp_proj` (`fst (fst r)` and `snd r` of a record holding records), `A_par_pairp_late` (an inner record taken
apart after other text), `A_par_pairp_pass` (an inner record given to a function), `P_pairp_match_nat` (a record holding
records chosen by a match on a counter, in a helper written out).  The readers hold a record as its numbers, and a record
holding records as the numbers of all its records (step 32); the meaning of taking one apart is the record type's own match
(`relim`), which binds those numbers only.  So an inner record is read only when the text takes it apart at once, and a
projection or a match that binds the inner record as a value has no reading.  Rocq has no eta rule for pairs
(`match p with (x, y) => (x, y) end` is not `p`), so the meaning has to bind the inner record as itself.  And a record holding
records that only a body uses is not in the program's record table (step 32: built and taken apart in place it needs none),
so one chosen by a test or a match has no type:
- *`KQR.v`*: each record type gets a one-level match and constructor, given by the program as `relim` and `rmk` are (`RS`,
  `RB`, and the types of its record fields, `RJ`): the match gives the number fields and the record fields, each in their
  order.  The laws: the number fields and then the record fields' numbers are the record's numbers (`relim`'s, the order the
  C holds them in), the record fields are of the types `RJ`, and the constructor on such fields has them as its numbers.  A
  record type without record fields gets them from `relim` and `rmk` (`mkrecs`, and `laws_of` for the laws).  Each sort gets a
  one-level take-apart that binds the number fields as numbers and the record fields as record variables (`SSplitR`,
  `BxSplitR`, `RSplitR`, `MSplitR`, `PvSplitR`, `XSplitR`, `BSplitR`, `BbSplitR`); the record sort gets a constructor on
  numbers and records (`RMkR`).  The C: a record's words are split among the fields, nothing is copied.
- *The reifier*: the record table keeps each record's field types, and holds the records holding records the bodies use
  (after every other, each after the records it holds: a program's indices are those of before).  A match on a record holding
  records that the text does not take apart at once is read as the one-level take-apart; a projection (`fst r`) is such a
  match, its branch the field; the function's own result is bound by a let and then taken apart.  A constructor of a record
  holding records given a record value is `RMkR`.  A record holding records built of plain values is put in where it is
  bound (zeta), as one built in a body was.
- *kitc.py*: for each record type with record fields, the one-level match and constructor, and the laws by a fixed script.
*Expected*: the four cells, and cells for an inner record rebuilt into a new outer record (in a recursion, by a let), one bound
by a let, one given back by a function, three levels of records, and an inner record taken apart one level in a test and in
functions giving back a boolean, a memory, a number after memories, a number and a memory, and a record.

**Step 43 done (2026-11-03): records holding records as values.**  Built as designed:
- *`KQR.v`*: `RecTypes` gains each record type's one-level match and constructor and its record fields' types (`RS`, `RB`, `RJ`),
  `RecLaws` their four laws (`rs_nat`, `rs_flat`, `rs_kinds`, `rb_mk`); `mkrecs` and `laws_of` give them to a program without
  records holding records from its matches and constructors (every record table of the tests is now made that way).  The eight
  one-level take-aparts and `RMkR`: their meaning `rsplit` (the record's own one-level match, its record fields as record
  values) and `RB`; their C the record's words split among the fields (`rnn`, `rsl`); `wf` asks the record's type and gives the
  body its record fields' types.  The proofs: the fields' atoms from the laws (`split_atoms`, `slices_ok`), the record variables
  they make (`inv_rlets`, `rsplit_typed`), the constructor's records (`rec_vals`); a case in each lemma over the syntax.  No new
  hypothesis; `Print Assumptions` the same base.
- *The reifier*: the record table keeps each record's field types (`rftys`), and holds the bodies' records holding records
  after every other; a match not taken apart at once is read as the one-level take-apart (`rbs`), in each sort; the function's
  own result is bound by a let first (`BLetRec`, then `BSplitR`); a constructor given a record value is `RMkR`; a record holding
  records built of plain values is put in where it is bound (`held`).  `rec_info` names each record holding records' record
  fields' types after its shape (`N:pair(pair(i,i),i)@1`).  Test `w43go` (`w43k` rebuilding its own result from the inner
  record, `w43go` giving the inner record to `w43pf` and taking it apart after a let; the record table as kitc.py makes it, its
  laws by the fixed script; the three theorems); each theorem in milliseconds.
- *kitc.py*: each program's one-level match and constructor (`_rs`, `_rb`, `_rj`), their laws by the fixed script
  (`KQR.kq_rb_case`).
- *Cells*: 11 more (879): an inner record rebuilt in a recursion and by a let, bound by a let, given back by a function, three
  levels, taken apart one level in a test and in functions giving back a boolean, a memory, a number after memories, a number
  and a memory, a record.  Run alone: all 11 proved, and with them `A_par_pairp_proj`, `_late`, `_pass` and
  `P_pairp_match_nat`.  Run as a check beside them, the 309 cells that involve records: 305 proved, the other 4 the known gaps
  (a template giving back a pair, the two number-and-memory pairs) and the cell refused by design.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 42's files /
  step 43's): `HWP_kernel` 2.56 / 2.67 s, `HWP_own` 1.98 / 2.06, `HWP_irqnow` 1.66 / 1.74 -- each about 0.1 s more, every round.
- The C: 63 of 63 byte-identical.  The construct table (on `4840d28`): **870 of 879 through the verified compiler**, 1 by design,
  7 gaps, 1 not Rocq (was 855 of 868: the eleven new cells and the four records holding records).  The gate on `4840d28`, the
  walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (12 / 12 / 12 / 14 / 13 s); **71
  programs through the verified compiler, 0 refused**; the trusted base unchanged.

**Step 44, a memory function taking a number-and-memory pair apart — the design (2026-11-03).**  The fifth item of the record
of 2026-11-02's order: `A_par_intmem_mem_fn` (a function giving back a memory takes apart the pair a call gives it:
`let '(y, t2) := g n x t in wm m y (upd 1 y y t2)`); the pair as a parameter (`A_par_intmem_param`) is the step's continuation.
A number made after memories and a pair take a pair apart (`XMatchP`, `PvMatchP`, step 26) or bind one by a let (`XLetP`); a
memory does neither, because the pair's own memories are of the memory sort: the two sorts are defined one after the other, the
memory first.
- *`KQR.v`*: the memory sort and the pair sort one mutual type; their meanings, their C, their checks and the call-graph
  functions mutual.  The memory sort gets `MMatchP p m` (the pair's number the nearest number in `m`, its memory the newest) and
  `MLetP p m` (bound by a let, read through `fst` and `snd`): the meaning the user's match or let on the pair (its own recursive
  call none, as in `XMatchP`), the C the pair's code and then `m`'s.  The pair's check takes the flags it is given: a number made
  after memories and a pair function give it theirs as before, a memory function its own, so the pair's memories may hold that
  function's recursive call.  The lemmas over the two sorts by mutual induction (`cmem_cpv_ok`, `denote_mpv_recm_ext`); their
  earlier statements corollaries.
- *The reifier*: a match on a number-and-memory pair in a memory function's body is read as `MMatchP`, a let of one as `MLetP`
  (the number below the memory, every older memory dead, as in the other sorts); the memory and pair readers mutual, and the
  call-graph sites.
- *Cells*: a memory function taking apart a pair built in place after other text, one chosen by a test; at the end of a memory
  function; bound by a let and read through `fst` and `snd`; inside a memory given to a call; one a function gives that takes
  one apart itself.
*Expected*: `A_par_intmem_mem_fn` and those.  The continuation, the pair as a parameter, is designed when it starts: a function
whose last parameter is a number-and-memory pair has that pair in its signature, its theorem from the function on the two
components (a call built of a number and a memory is a call on the components), and a call given any pair expression a call
form that takes the whole pair (its proof through `surjective_pairing`).

**Step 44 done (2026-11-03): a memory function taking a number-and-memory pair apart.**  Built as designed:
- *`KQR.v`*: `smem` and `spv` one mutual type (`smem_comb`); `denote_m`/`denote_pv`, `cmem`/`cpv`, `wfm`/`wfpv`, `sh_m`/`sh_pv`
  mutual; `MMatchP` and `MLetP` with their meaning, C (`cpv` then `cmem`, in tail position `ctailm`) and check.  `wfpv` takes
  the flags its memories and numbers are checked with (`false false true` where it was before).  The proofs: `cmem_cpv_ok` (the
  old `cmem_ok` and `cpv_ok` one lemma by mutual induction, a pair's own recursive call given to the pair's induction hypotheses,
  a memory inside a pair by the memory's), `denote_mpv_recm_ext` (the memory's and the pair's extensionality in the memory's
  recursive call); `cmem_ok`, `cpv_ok`, `denote_m_recm_ext` their corollaries, unchanged; `ctailm_ok` gains the two cases.  No new
  hypothesis; `Print Assumptions` the same base.
- *The reifier*: `reify_m`/`reify_pv` mutual; a match on a number-and-memory pair in a memory read as `MMatchP`, a let of one as
  `MLetP` (`pm_split`, as for `XLetP`); `cl_m`/`cl_pv` mutual.  Test `w44go` (`w44wm` taking apart the pair `w44g` gives it, the
  helper `w44lm` written out in `w44go` binding its pair by a let; the three theorems); each theorem in milliseconds.
- *Cells*: 6 more (885): a memory function taking apart a pair built in place after other text, one chosen by a test; at the end
  of a memory function; bound by a let; inside a memory given to a call; one a function gives that takes one apart itself.  Run
  alone: all 6 proved, and with them `A_par_intmem_mem_fn`; `A_par_intmem_param` refused (the continuation).  Run as a check
  beside them, the 268 cells that involve memories: 264 proved, the other 4 the known gaps (the pair as a parameter, a mutual
  block giving back memories, a writing function inside an expression and its recursive call inside one).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 43's files /
  step 44's): `HWP_kernel` 2.57 / 2.59 s, `HWP_own` 1.97 / 2.01, `HWP_irqnow` 1.66 / 1.71 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `4d99efa`): **877 of 885 through the verified compiler**, 1 by design,
  6 gaps, 1 not Rocq (was 870 of 879: the six new cells and `A_par_intmem_mem_fn`).  The gate on `4d99efa`, the walk switched
  off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (12 / 12 / 12 / 14 / 13 s); **71 programs through
  the verified compiler, 0 refused**; the trusted base unchanged.  The step goes on with the pair as a parameter (below).

**Step 44 continued, a number-and-memory pair as a parameter — the design (2026-11-03).**  `A_par_intmem_param`
(`k (n : nat) (p : int * mem)`, called `k n (a, s)`, its recursive call `k m (fst p + rd 0 0 (snd p), snd p)`).  A signature
holds numbers, booleans, records and a memory, each its own parameter; a pair parameter is refused.  Taking it as a number and a
memory through a wrapper (`k__p n x s := k n (x, s)`, as step 41 does for order) reads the function, and a call given a pair built
in place; but a call given any other pair expression `P` (a call's result) is `k n P`, which is not `k n (fst P, snd P)` up to
conversion (no eta for pairs), so the wrapper alone leaves those calls unread:
- *`KQR.v`*: a signature gets a flag `sp`: its last number and its memory are one parameter, a pair (`mksig8` the signature
  without).  The function's type takes the pair there (`ntypeTP`); its KQL takes the number and the memory as before; a call on
  numbers and a memory is the function on the pair of the last number and the memory (`callf`, `appnTP`).  A signature with the
  pair takes a memory and ends with a number (`pairok`, in `swok`).  A function's own body is read and proved on the two
  components; its theorem with the pair from the components' theorem (`callee_ok_unpair`, through `appnTP_unpair`): kitc proves
  `fun .. x s => k .. (x, s)` by the theorems of before and gives `k`'s from it.  A call given a whole pair expression, where a
  call giving back a memory, a pair, or a number after memories at its end stands: `MCallP`, `PvCallP`, `XCallP`, its meaning
  the function applied to the pair (`callfp`), its C the arguments, the pair's code, then the call on the pair's number and
  memory; the proof from the callee's theorem at the pair's two parts and `surjective_pairing`.
- *The reifier*: a function whose last parameter is a number-and-memory pair is read on the components: its body with the pair
  replaced by the pair of two new variables (`pm_split`), the flag set in its signature; a call given a pair built in place is a
  call on its number and memory; a call given another pair expression the new call forms.
- *kitc.py*: the flag in a signature; the function's theorem from the components' one.
- *Cells*: a pair parameter after other parameters; the function giving back a memory, a pair, a boolean; a call given a pair a
  function gives (giving back a number, a memory, a pair); the pair taken apart in the body; the recursion given the pair as it
  is.  A call of such a function inside an expression given a pair that is not built in place is a writing function inside an
  expression (a later item of the order): a cell, a gap.
*Expected*: `A_par_intmem_param` and those.

**Step 44 continued (2026-11-03): a number-and-memory pair as a parameter.**  Built as designed:
- *`KQR.v`*: `sig` has the flag `sp` (`mksig9`; `mksig8` the signature without it, a notation, declared again after the section);
  `ftype`, `callf` and `denote_f` take the pair where the signature takes a memory and has the flag (`ntypeTP`, `appnTP`; the
  function on the components `unpairT`, made a function of the pair `pairT`, `cmapT` over the counters); `swok` refuses the flag
  on a function's own signature, so its body is read and proved on the components and `compile_f_ok`'s flagged case is void;
  `callee_ok_unpair` gives the flagged function's theorem from the components' one (`appnTP_unpair`).  `MCallP`, `PvCallP`,
  `XCallP`: meaning `callfp` (the function applied to the pair, `appnTPP`), C the arguments, the pair's code, the call on its
  number and memory, check as `MCall`, `PvCall`, `XCall` with the callee flagged, taking a memory, ending with a number (`last_num`);
  their runs from the callee's theorem at the pair's number and memory (`pcall_pre`, `mcallp_run`, `pvcallp_run`,
  `xcallp_run`, through `callf_snoc`, `appnTP_snoc`); a case in each lemma over the sorts.  No new hypothesis; `Print
  Assumptions` the same base.
- *The reifier*: a last parameter of type `int * mem` read as a number and the memory, the signature flagged (`read_sig`,
  `with_sp`); the body with the pair replaced by the pair of two new variables (`pm_split`), and every call of a flagged function
  (its own recursive call too) given a pair built in place read with the pair's number and memory, `fst` and `snd` of such a
  pair its parts (`flatp`, `pm_body`); a function's own check on the components; a call given another pair expression read as
  the new forms.  Test `w44bgo` (`w44bk` with the pair last, its theorem by `callee_ok_unpair` from its components' two
  equations; `w44bgo` giving it the pair `w44bg` gives, `XCallP`); each theorem in milliseconds.
- *kitc.py*: the flag (`p` after the kinds) in a signature, `KQR.mksig9 .. true`; a flagged function's theorem
  `callee_ok_unpair` over the components' (`compile_f_ok`, or for a recursive one the copies' theorems over
  `cmapT (unpairT ..) k`, its step equation by `reflexivity`: the bare `eq_refl` term meets an anomaly of Rocq's elaborator).
- *Cells*: 11 more (896): the pair after other parameters; the function giving back a memory, a pair, a boolean; a call given
  the pair a function gives, giving back a number, a memory, a pair; the pair taken apart in the body; the recursion given the
  pair as it is; and the two places this step leaves unread: a call inside an expression given a pair a function gives
  (`A_par_pm_call_expr`, `A_par_pm_call_bool_fn`, the writing functions inside expressions of a later item).  Run alone: 9
  proved, and with them `A_par_intmem_param`; the two places refused.  Run as a check beside them (on the first build), the
  469 cells that involve memories, pairs, calls or tail positions: 465 proved, the other 4 the known gaps (a template given a
  function and giving back records, a mutual block giving back memories, a writing function inside an expression and its
  recursive call inside one).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 44's files /
  the continuation's): `HWP_kernel` 2.70 / 2.74 s, `HWP_own` 2.07 / 2.11, `HWP_irqnow` 1.73 / 1.80 -- within 4%.  The first
  build ran the pair pass over every body (2.81 / 2.14 / 1.87 s against 2.63 / 2.03 / 1.72); it now runs only over a body with
  a pair parameter or a flagged callee.
- The C: 63 of 63 byte-identical.  The construct table (on `be57d75`): **887 of 896 through the verified compiler**, 1 by design,
  7 gaps, 1 not Rocq (was 877 of 885: the nine new cells read and `A_par_intmem_param`).  The gate on `be57d75`, the walk
  switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (13 / 16 / 14 / 21 / 14 s); **71
  programs through the verified compiler, 0 refused**; the trusted base unchanged.  Next: mutual blocks of any signature (the
  record of 2026-11-02's order).

**Step 45, mutual blocks of any signature — the design (2026-11-03).**  The sixth item of the record of 2026-11-02's order:
`A_par_mutual_sig` (`ev (n : nat) (x : int)` and `od (n : nat) (x y : int)`, one `Fixpoint .. with ..`) and `A_par_mutual_mem`
(`wa` and `wb`, each giving back a memory).  Step 17 reads a block whose members are number functions of one signature, numbers
and booleans as parameters, recursive on the first: the block one function with a selector, its meaning `blk` of the members,
read by a reader of its own.  The general form: members of any signatures and parameter orders, giving back any sort, calling
each other in any pattern:
- *`KQR.v`*: `blkT`, the block's meaning over the members' *views*: each member seen as a function of the block's counters (the
  selector apart) and parameters, giving the member its own in its own order; the result of any type `T`; `sel_appT` the
  choice (the first member apart, so no default value is needed).  A block giving back a number, a number that writes the
  memory, a memory, a boolean, a record or a pair is then proved by the theorem of a function given by its equations for that
  sort (`compile_f_okr`, `_okrx`, `_okrm`, `_okrb`, `_okrr`, `_okrp`), by conversion as in step 17.  Definitions only.
- *The block's signature*: the members' parameters in shared slots — the recursion's counter, one slot for the `i`-th other
  counter of any member, the selector, one slot of a kind for the `i`-th parameter of that kind of any member, the memory (a
  number-and-memory pair a number slot and the memory).  A call of one member by another passes its arguments in the callee's
  slots and every other slot its current value, so a tail call between members stays one loop with nothing more to move; a
  member is one call of the block, the slots not its own given zeros.
- *The members' call graph*: a block is read per strongly connected part of it, the parts a part calls first.  A call into
  another part is a call of that member (the user's constant, a member the program does not name included).  So members giving
  back different sorts are read whenever the members of one part agree (and those of one part agree on the memory: a member
  without one cannot call one with it).  A member gets a function of its own only where it is called: by the program, or from
  another part.
- *The reifier*: the part's function is written as a term — a fixpoint over the slots, the members' bodies moved into them
  (`relocate`), under a match on the selector (`nest_t`), a call of a member of the part its own recursive call with the slots
  filled (`sibr`) — and each member as a term, one call of it; both are then read by the readers of every function, so every
  sort, every parameter order and every construct a body may hold are read as in a function of its own.  The reader of step 17
  goes.
- *kitc.py*: a block's meaning is made in the proof file, where the program's record types are (`blkT` takes them); a member
  with the pair as a parameter is not a fix over its counter (its theorem the one of a function of the pair, not of a copy).
- *Cells*: a boolean and a record among one member's parameters, a second counter, the recursion's counter not first; giving
  back a boolean (`even` / `odd`), a record, a number and a memory, a number that writes the memory; a number that reads the
  memory and one that writes it in one part; three members; two parts of different sorts; a member taking the pair.  A part
  whose members give back different types (a number and a memory calling each other) is a cell, a gap (a later step), refused
  with that reason.
*Expected*: `A_par_mutual_sig`, `A_par_mutual_mem` and those; `mutual`'s C byte-identical.

**Step 45 done (2026-11-03): mutual blocks of any signature.**  Built as designed:
- *`KQR.v`*: `blkT` and `sel_appT` (the block's meaning over the members' views, the result of any type) — definitions only: no
  new theorem, no change to the syntax, the meanings or the proofs; `Print Assumptions` the same base.
- *The reifier*: a member of a mutual block is read through its part of the members' call graph (`mcalls`, `part_of`), the
  parts it calls first (`ensure_part`); the part's slots (`part_layout`: `classify_params`, `add_slots`, `kslot`); its function
  written as a fixpoint over the slots (`relocate`, `sibr`, `nest_t`) and each member called as one call of it (`add_member`,
  `zero_of`), both put in the environment (`add_decl`) and read by the readers of every function; the meaning `blkT` of the
  views; a member gets a function only where the program or another part calls it.  The reader of step 17 (`read_block`,
  `member_body`, `blk_meaning`) is gone.  A part whose members give back different types is refused with that reason
  (`mixed_part`).  Test `w45go` (`w45a` and `w45b` giving back a memory, `w45b` with a parameter more and its counter
  second, the block's theorem by `compile_f_okrm`, `w45a`'s and `w45go`'s by `compile_f_ok`; `w45b`, which the program does not
  name, nothing), each theorem in milliseconds; the step-17 test unchanged.
- *kitc.py*: a block's meaning made in the proof file at the program's record types (`KQRReify.blk_mts`, the other meanings
  where they were, `plain_mts`); a member of a mutual block taking the pair has the theorem of a function of the pair.
- *Cells*: 13 more (909): a boolean and a record among one member's parameters, a second counter, the recursion's counter not
  first; giving back a boolean, a record, a number and a memory, a number that writes the memory; a number that reads the memory
  and one that writes it in one part; three members; two parts of different sorts; a member taking the pair; and the place this
  step leaves unread, a part whose members give back different types (`A_par_mutual_mixed`, a gap).  Run alone: 12 proved, and
  with them `A_par_mutual_sig` and `A_par_mutual_mem` (step 17's `P_int_mutual` still); `A_par_mutual_mixed` refused.  Run as a
  check beside them, 170 cells (the mutual blocks, the pair, records, templates, a parameter of another order, and every eighth
  cell of the table): 166 proved, the other 4 the known gaps.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 44
  continued's files / step 45's): `HWP_kernel` 2.58 / 2.63 s, `HWP_own` 1.99 / 2.04, `HWP_irqnow` 1.68 / 1.76.  The difference
  is the loading of the libraries (`KQR` and the reifier alone: 0.90 / 0.96 s; the reifier's file holds the step's definitions
  and its test); the reading itself is the same (no mutual block in them).
- The C: 63 of 63 byte-identical (`mutual` too).  The construct table (on `dcb282b`): **901 of 909 through the verified
  compiler**, 1 by design, 6 gaps, 1 not Rocq (was 887 of 896: the twelve new cells read and `A_par_mutual_sig`,
  `A_par_mutual_mem`).  The gate on `dcb282b`, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the
  five kernels (12 / 11 / 12 / 14 / 12 s); **71 programs through the verified compiler, 0 refused**; the trusted base unchanged.
  Next: templates giving back records (the record of 2026-11-02's order).

**Step 46, templates of any signature — the design (2026-11-03).**  The seventh item of the record of 2026-11-02's order:
`A_par_fun_rec_pair` (`foldp (n : nat) (p : int * int) (g : int -> int) : int * int`, a template taking a record and giving one
back).  A template's copy for the functions it is given (step 10), and a local fixpoint's (step 31), is read by `read_def`: its
result a number, a memory or a number that writes the memory; every parameter that is not a counter, a memory or a boolean read
as a number; the copy checked without the program's record types.  The general form, a copy read as any function is:
- *The reifier*: a copy giving back a boolean, a record, or a number and a memory, read by the readers of those sorts (as
  `read_fun_c` reads a function); a record among its parameters a record (`tkinds`); its last parameter a number-and-memory pair
  read on its components, its signature flagged (as step 44 continued reads a function); the copy checked with the program's
  record types and, flagged, on its components; a record given back by a function given to it read with that function's body
  written out, as the other sorts read it.  `KQR.v` unchanged: the copies' theorems for every result sort are there (step 41).
- *kitc.py*: a flagged copy's theorem the one of a recursive function of the pair (its components' copy theorem, then
  `callee_ok_unpair`).
- *Cells*: a template giving back a boolean (and with a capture), a record (and with a capture), a number and a memory; a record
  and a boolean among its parameters; a local fixpoint giving back a record; functions given that give back a record, take a
  record, write the memory, take a boolean; the pair as a parameter.
*Expected*: `A_par_fun_rec_pair` and those.

**Step 46 done (2026-11-03): templates of any signature.**  Built as designed, in the reifier and `kitc.py` (`KQR.v`
unchanged):
- *The reifier*: `read_def` reads a copy giving back a number and a memory (`FRecP`), a boolean (`FRecB`) or a record
  (`FRecR`) as `read_fun_c` reads a function; `tkinds` reads a record among a template's parameters as a record; a copy whose
  last parameter is a number-and-memory pair is read on its components (`pm_body`), its signature flagged and checked on them;
  a copy is checked with the program's record types (`arity_recs`, as a function is — without them every template holding a
  record was refused); the record reader writes out the body of a function given to the template (`CFn`), as the other
  readers do.  Test `w46go` (`w46foldp`'s copy for `fun z => z + 1`, taking and giving back a pair of numbers, its theorem by
  `compile_f_okrr`, `w46go`'s by `compile_f_ok`), each theorem in milliseconds.
- *kitc.py*: a flagged copy's theorem from its components' copy theorem (`callee_ok_unpair`), as a recursive function's.
- *Cells*: 13 more (922): a template giving back a boolean (and with a capture), a record (and with a capture), a number and a
  memory; a record and a boolean among its parameters; a local fixpoint giving back a record; functions given that give back a
  record, take a record, write the memory, take a boolean; the pair as a parameter.  Run alone: all 13 proved, and with them
  `A_par_fun_rec_pair`.  Run as a check beside them, 194 cells (templates, local fixpoints, records, the pair, and every
  ninth cell of the table): 191 proved, the other 3 the known gaps (the writing functions inside expressions).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 45's
  files / step 46's): `HWP_kernel` 2.58 / 2.63 s, `HWP_own` 2.00 / 2.04, `HWP_irqnow` 1.68 / 1.73 — the loading of the
  libraries again (`KQR` and the reifier alone: 0.88 / 0.94 s; this step's change to the reader is small, its test with a
  record instance is not): every program loads the reifier's tests; they go to a file of their own next (below).
- The C: 63 of 63 byte-identical.  The construct table (on `4283f5d`): **915 of 922 through the verified compiler**, 1 by design,
  5 gaps, 1 not Rocq (was 901 of 909: the thirteen new cells read and `A_par_fun_rec_pair`).  The gate on `4283f5d`, the walk
  switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 12 / 12 / 14 / 13 s); **71 programs
  through the verified compiler, 0 refused**; the trusted base unchanged.  Next: calls inside expressions that write the memory or
  are given a pair (the record of 2026-11-02's order).

**Step 47, calls inside expressions that write the memory or are given a pair — the design (2026-11-03).**  The eighth item of
the record of 2026-11-02's order: `A_par_write_fn_expr` (`wr n s + 1`, `wr` a number function that writes the memory),
`P_int_write_nontail` (`f m a b (upd 0 a b s) + 1`, the function's own recursive call inside an expression), and the two places
step 44 continued left: `A_par_pm_call_expr` (`k n (g n a s) + 1`) and `A_par_pm_call_bool_fn` (`if k n (g n a s) then ..`).
A number function that writes (`XCall`, `XRec`, `XCallP`, steps 11 and 44) is read only at the end of a body: its theorem says
the memory after it is *some* memory, so nothing after it may read the memory, and the sort of numbers has no place for a call
that changes it.  A call of a function given a pair, whatever it gives back, is read only at the end of a body too.
- *`KQR.v`*: the sort of a number that writes gets `XBind f cs args m x` (function `f` on the memory `m`, its result — a number,
  a boolean, a record — the nearest value of its kind in `x`), `XBindR cs args m x` (the function itself) and `XBindP f cs args p
  x` (given the pair `p`): `x` runs after the call.  When the callee writes, `x` is a number that reads no memory (`XRet e`, `e`
  checked without one): its value the same whatever the memory (`denote_nomem`); when it does not, `x` is any number that writes,
  on the memory the call was given.  C: the call into a variable (`Ecall`; the function's own name for `XBindR`, a call that is
  not a loop), then `x`'s code.  The proofs: the callee's theorem (for `XBindR` the induction hypothesis on the counter), then
  `x`'s; a case in each lemma over the sort.
- *The reifier*: a number expression holding a call of a function that writes, or of a function given a pair that is not built
  in place: the parts that read the memory and stand outside the call bound before it by lets (the meaning is Rocq's, which no
  order of evaluation changes; the lets are a conversion away from the text), the call bound (`XBind`, `XBindR`, `XBindP`), the
  rest after it with the call's result (a read of the memory always goes before: in Rocq it reads the memory the call was given).
  Two calls that write the memory in one expression: refused (below).
- *Cells*: a writing call inside an expression after a read of the memory, before one, inside a test, under a let, its result
  used twice; the function's own writing call inside an expression; a call given a pair inside an expression, giving back a
  number, a boolean, a record; two writing calls in one expression (refused: each is given the memory before both, which needs
  a copy of the memory; whether that is by design is §0.5's question, answered with a pin and a control when it is built).
*Expected*: the four cells and those.

**Step 47 done (2026-11-03): calls inside expressions that write the memory or are given a pair.**  Built as designed:
- *`KQR.v`*: `XBind`, `XBindR`, `XBindP` in the sort of a number that writes, their meaning (`xres`: the call's result, a number
  or a boolean, given to what follows), C (the call into a variable, the function's own name for `XBindR`, then what follows)
  and check (`resq`; after a call that writes, `xfree`: a number checked as reading no memory and as a number of the body);
  the proofs: `ctailx_ok`'s three cases (the callee's theorem, or `Hrecx`, then the induction hypothesis; after a call that
  writes, what follows moved from the callee's end memory to the memory given, through `denote_rec_ext_r` — `denote_rec_ext`
  with its hypothesis asked only where the recursive call is allowed — and `denote_nomem`), `denote_x_recx_ext`'s
  (`xres_ext`), `inv_call_res`.  No new hypothesis; `Print Assumptions` the same base.
- *The reifier*: a number holding such a call in a place evaluated before the rest (`bind_first`: an operand, a call's
  argument, a test) is read with the call bound by a let, the operands of the numbers' operations that read the memory bound
  before it; a let of such a call read as `XBind`, `XBindR` or `XBindP` (`bindc`), what follows after a call that writes read
  with the memory dead.  Test `w47go` (a read of the memory plus a call that writes it), each theorem in milliseconds.
  `kitc.py` unchanged.
- *Cells*: 9 more (931): a call that writes after a read of the memory, before one, in a test, bound by a let, its result used
  twice, as a call's argument; the function's own inside an expression; and the two places this step leaves unread: a call
  given a pair giving back a record (`A_par_pm_call_rec`) and two calls that write in one expression (`A_par_write_two`, each
  given the memory before both: a copy of the memory, a question for later).  Run alone: 7 proved, and with them the four
  cells of the item (`A_par_write_fn_expr`, `P_int_write_nontail`, `A_par_pm_call_expr`, `A_par_pm_call_bool_fn`).
  Run as a check beside them, 549 cells (memories, pairs, calls, writes, mutual blocks, and every tenth cell of the table):
  546 proved, the other 3 the known gaps (a mutual part of two types, and this step's two).  The step reads such a call in the
  body of a number only; the places in the bodies of the other sorts (a call given a pair not built in place inside an
  expression of a function giving back a boolean, a record, a number and a memory, a memory) got their 4 cells a commit late
  (`1fab4bb`, all refused): the rule asks for the same commit, and that was missed.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 46's
  files / step 47's): `HWP_kernel` 2.52 / 2.62 s, `HWP_own` 1.95 / 2.01, `HWP_irqnow` 1.66 / 1.71 — most of it the loading of
  the libraries (`KQR` and the reifier alone: 0.88 / 0.94 s; both files grew by the step's definitions, proofs and test).
- The C: 63 of 63 byte-identical.  The construct table (on `706834b`): **926 of 931 through the verified compiler**, 1 by design,
  3 gaps, 1 not Rocq (was 915 of 922: the seven new cells read and the four of the item).  The gate on `706834b`, the walk
  switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (12 / 12 / 12 / 14 / 13 s); **71 programs
  through the verified compiler, 0 refused**; the trusted base unchanged.  With the 4 cells of `1fab4bb`: **926 of 935**, 7 gaps.
  The record of 2026-11-02's order is done (its last item, a let in a later operand, was read since step 36); next: the places the
  steps since left unread (a call given a pair giving back a record, two calls that write in one expression, a mutual part of two
  types).

**Step 48, calls given a pair inside expressions of every sort — the design (2026-11-03).**  The places step 47 left:
`A_par_pm_call_rec` (`f1 (kr n (g n a s))`, the call giving back a record) and the four cells of `1fab4bb` (a call given a pair
not built in place inside an expression of a function giving back a boolean, a record, a number and a memory, a memory).  Step 47
binds such a call in the body of a number that writes, its result a number or a boolean:
- *`KQR.v`*: the bound call's result may be a record too (its fields from the slot block, as `RCall` reads them: `ccallr`, the
  slot block given back as it was); and the bodies of the other sorts get the same binding — a boolean's (`sbb`), a record's
  (`sbr`), a memory's and a number-and-memory pair's (`smem`, `spv`, one mutual type since step 44): a call given a pair, its
  result the nearest value of its kind in what follows, on the pair's memory.  The proofs: a case in each lemma over those
  sorts, from the callee's theorem at the pair's two parts (`pcall_pre`) and the induction hypothesis.
- *The reifier*: `bind_first` and the let of such a call read in the readers of those sorts as in `reify_x`.
- *Cells*: a call given a pair inside an expression of each sort, giving back a number, a boolean, a record; bound by a let;
  inside a test.  A call that writes inside an expression of a memory's or a pair's body is given a memory the body uses again
  after it (the body's own result is a memory made from the one before): with two calls that write in one expression it is
  the place of a copy of the memory — cells beside `A_par_write_two`, decided together.
*Expected*: the five cells and those.

**Step 48 (2026-11-03): a call given a pair, bound, giving back a record; the bodies of the other sorts go on.**  Built:
- *`KQR.v`*: `XBindPR` in the sort of a number that writes (a call given a pair not built in place, its result a record of type
  `ri`, the nearest record in what follows): meaning `xrec`, C `ccallr` (the fields from the slot block, the slot block given
  back as it was, as `RCall` reads them), check as `XBindP`'s with the record's size; `ctailx_ok`'s case (`pcall_pre`,
  `ccallr_ok`, `inv_rlet`), `denote_x_recx_ext`'s (`xrec_ext`).  No new hypothesis; `Print Assumptions` the same base.
- *The reifier*: such a call bound with the record type it gives back (`bcall_rec`), a let of it read as `XBindPR`.  No test of
  its own in the reifier's file (every program loads those; the cells test it).
- *Cells*: 2 more (937): the record bound by a let, inside a test.  Run alone: both proved, and with them `A_par_pm_call_rec`.
  Run as a check beside them, 436 cells (pairs, records, writes, mutual blocks, templates, and every twelfth cell of the
  table): 429 proved, the other 7 the known gaps and the cell refused by design.
- *Not built, the step's continuation*: the four places of `1fab4bb`.  A call given a pair not built in place inside a function
  giving back a boolean or a record writes the memory in that function, and those sorts have no form of a function that writes
  (the number's has, step 11); inside a function giving back a pair or a memory it is given the pair a let holds, a call no
  sort reads yet.  Their cells stay gaps until then.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest; step 47's
  files / step 48's): `HWP_kernel` 2.54 / 2.62 s, `HWP_own` 1.96 / 2.03, `HWP_irqnow` 1.65 / 1.73 — the loading of `KQR` (alone:
  0.86 / 0.94 s; with the reifier 0.88 / 0.94), which grew by the step's proof; the reading the same.  Every program loads
  `KQR`'s proofs and tests and the reifier's tests: a file of them apart is the next general step for proof time.
- The C: 63 of 63 byte-identical.  The construct table (on `10a5276`): **929 of 937 through the verified compiler**, 1 by design,
  6 gaps, 1 not Rocq (was 926 of 935: the two new cells read and `A_par_pm_call_rec`).  The gate on `10a5276`, the walk switched
  off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 12 / 12 / 13 / 13 s); **71 programs through
  the verified compiler, 0 refused**; the trusted base unchanged.  The step goes on with the bodies of the other sorts (below).

**Correction (2026-11-03): the reifier's timing of steps 44 continued to 48.**  Their timing lines put a difference of 0.04–0.08 s on the
libraries' loading; it was the scan of the working tree's generated files and cells (F62).  Timed without them, step 44 continued's files
against step 48's: `HWP_kernel` 2.50 / 2.52 s, `HWP_own` 1.93 / 1.95, `HWP_irqnow` 1.63 / 1.64 — the same.  The pair pass of step 44
continued, run since its first timing only over a body with a pair parameter or a flagged callee, stays so (it reads nothing else);
the reifier's tests in a file of their own, proposed in steps 46 and 48, cost nothing measurable and are not made.

**Step 48 continued, functions giving back a boolean or a record that write the memory, and a call given the pair a let holds —
the design (2026-11-03).**  The four places of `1fab4bb`.
- *A boolean or a record that writes.*  `kb n x t := k n (g n x t) <? 5`: `g` writes the memory, so `kb` does, and its theorem
  must say the memory after it is *some* memory, as a number that writes says (step 11, `sw`).  `callee_ok` already states that
  for any result (`if sw gs then exists M', ..`); what is missing is the body: the sort of a number that writes gets results of
  the other two kinds — `XRetB b` and `XRetR r` (a boolean, a record, from the newest memory) — and its meaning a result of the
  signature's type (`rtq`), so a function giving back a boolean or a record whose body writes is read in that sort, its theorem
  `compile_f_ok`'s case for it, the caller's `XBind` / `XBindP` / `XBindPR` taking its result as for a number (the record from the
  slot block).
- *A call given the pair a let holds.*  `let p := g n x t in upd 0 (k n p) 0 (snd p)`: `k n p` is not `k n (fst p, snd p)` up to
  conversion, so the call takes the pair itself: in the memory's and the pair's sorts, a number made by a call given the pair
  the nearest pair variable holds — the form of `MCallP` / `PvCallP` for a number, its meaning `callfp` on that pair, its C the
  call on the pair's number and the newest memory (which is the pair's, a let of a pair making its memory the newest, step 26).
- *Cells*: the four of `1fab4bb`; a boolean and a record that write, called at the end and inside an expression; the pair a let
  holds given to a call inside a test and twice.
*Expected*: the four cells and those.

**Step 48 continued (2026-11-03): functions giving back a boolean whose body writes the memory; records and the pair a let holds
go on.**  Built, the first of the design's two parts for booleans:
- *`KQR.v`*: a boolean as a leaf of the sort of a number that writes (`XRetB`: its code 1 or 0, from the newest memory) and the
  boolean such a body gives (`denote_xb`, the function's own call `recb`; `xresb`, `xrecb`); a function giving back a boolean
  whose signature writes (`sw`) has an X body whose leaves are booleans or its own call (`xbool`), its meaning `denote_xb`
  (`denote_f0`); `denote_x_xb` (the body's number is its boolean as 1 or 0, `xres_xresb`, `xrec_xrecb`); `compile_f_ok_bool`
  gains the case, built on the X case's proof and that lemma.  A call that writes may give back a boolean (`XBind` /
  `XBindP` with `bq`); what follows it reads no memory and may be a boolean (`xfree` with `XRetB`), proved once for every such
  place by `after_free` (the code run on the memory the call left gives the meaning on the memory it was given; the five places
  of steps 47 and 48 end with it).  No new hypothesis; `Print Assumptions` the same base.
- *The reifier*: a boolean as the last resort of a number that writes (`XRetB`); a function giving back a boolean that its
  readers of booleans refuse read as an X body of booleans, its signature writing (`wsig`); what follows a call that writes may
  be a boolean; a binding call found through the helpers written out where they are used (`bind_first`).
- *Cells*: 2 more (939): a boolean through a call that writes, a boolean whose recursion is given a memory it writes.  Run
  alone: both proved, and with them `A_par_pm_call_in_bool`.  Run as a check beside them, 442 cells (booleans, pairs, writes,
  mutual blocks, memories, and every eleventh cell of the table): 437 proved, the other 5 the known gaps.  (The binding through
  helpers wrote out a record's projection on a first build and lost `A_par_pm_call_rec_test`; it now writes helpers out only
  when the text as written holds no call to bind.)
- *Not built yet, the step's continuation*: a record whose body writes (`A_par_pm_call_in_rec`: the same with a record leaf, its
  fields to the slot block at the end) and the pair a let holds given to a call (`A_par_pm_call_in_pv`, `A_par_pm_call_in_mem`).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the
  trees without their generated files, F62; step 48's files / this step's): `HWP_kernel` 2.56 / 2.55 s, `HWP_own` 1.94 / 1.93,
  `HWP_irqnow` 1.62 / 1.64 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `f70ad99`): **932 of 939 through the verified compiler**, 1 by design,
  5 gaps, 1 not Rocq (was 929 of 937: the two new cells read and `A_par_pm_call_in_bool`).  The gate on `f70ad99`, the walk
  switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (14 / 12 / 12 / 15 / 13 s); **71 programs
  through the verified compiler, 0 refused**; the trusted base unchanged.  The step goes on with a record whose body writes and
  the pair a let holds.

**Step 49, two versions of the memory both used — the boundary pinned: the design (2026-11-03).**  `A_par_write_two` (`wr n s +
wr2 n s`, step 47): each call is given the memory before both and each writes it, so the memory before the first must still be
there for the second — §0.5's third refusal as it was worded.  Read by its size (a runtime is decided by size and lifetime, never
by type: §0.5, F35), the two versions differ in the cells the first call writes, and `wr` writes one cell, named in its text
(`upd 0 0 ..`): its old value kept in a variable and put back after the call is what a C programmer writes (here not even that:
`wr2` reads and writes another cell), and nothing runs behind anyone's back.  A copy is forced only when the two versions differ
in cells whose number comes from the data — a recursion writing a cell at each round at a moving index, whose old values the
other version still reads.  So (F63):
- *§0.5's third refusal* is that: two versions of the memory both used, differing in cells whose number comes from the data.  Two
  versions differing in cells fixed by the text are runtime-free: a gap until read.
- *The pin*, `A_par_write_two_data`: `wp n a s + wp n b s`, each call a prefix sum in place over the `n` cells from its own index
  (each round reads the cell the round before wrote, so no call's reads can be split from its writes), both given the memory
  before both, their ranges overlapping as the data falls: keeping the old memory for the second call takes the old values of up
  to `n` cells, a copy or a log as large as the data.  By design (`DESIGN_CELLS`).
- *Its control*, `A_par_write_two_seq`: the same two calls with the memory handed on (`let '(v, t) := wpp n a s in v + wp n b t`,
  the first giving back its memory) — one version at a time; read and proved today.
- *The runtime-free side, a cell in each place*: `A_par_write_two` (two calls in an expression of a number), `A_par_write_in_mem`
  (a memory's body giving the result of a call that writes to a write on the memory it was given: `upd 0 1 (wr n t + x) t`),
  `P_mem_both` (§0.5's old example, a let: `let t := upd 0 a b s in upd 0 b (rd 0 0 t) s`).  Gaps of one category (classified by
  name); reading them — the cells the first version writes saved before it and put back after, or the old version's reads moved
  before — is a construct of `S` for a later step.
- No change to `KQR.v`, the reifier or `kitc.py`: the C and the gate are `f70ad99`'s; the construct table is run.
*Expected*: 943 cells (the four new); 933 proved (`A_par_write_two_seq`), 2 by design, 7 gaps, 1 not Rocq.

**Step 49 done (2026-11-03): two versions of the memory both used — the boundary pinned.**  Built as designed, in the table only:
- *§0.5's third refusal* is worded by the size of the difference (F63): two versions of the memory both used are refused when
  they differ in cells whose number comes from the data; when they differ in cells fixed by the text, the old values can be kept
  and put back, and the place is a gap.
- *Cells*: 4 more (943).  The pin `A_par_write_two_data` (`wp n a s + wp n b s`, each call a prefix sum in place over `n` cells
  from its own index, both given the memory before both): refused, by design (`DESIGN_CELLS`); its control
  `A_par_write_two_seq` (the same two calls, the first giving back its memory and the second given it): proved.  The fixed side
  in each place — two calls in an expression of a number (`A_par_write_two`, step 47), a call that writes inside a memory's body
  (`A_par_write_in_mem`), a let (`P_mem_both`, §0.5's old example): refused, gaps of one category (`BY_NAME`).  Run alone
  beside `P_mem_dup` (the second version never used: proved), each verdict as listed.
- No change to `KQR.v`, the reifier or `kitc.py`.
- *A slip of step 48 continued found*: its boolean half reads the function's own call at the end of a boolean that writes, not
  bound by a let or negated, and that place got no cell; it gets one with the record half (next), recorded there.
- The C: the same (`KQR.v`, `KQRReify.v` and `kitc.py` byte-identical to `f70ad99`'s).  The construct table (on `5057f75`): **933
  of 943 through the verified compiler**, 2 by design, 7 gaps, 1 not Rocq (was 932 of 939: the control read, the pin by design,
  two gaps added).  The gate on `5057f75`, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five
  kernels (11 / 12 / 12 / 13 / 13 s); **71 programs through the verified compiler, 0 refused**; the trusted base unchanged.  Step
  48 continued goes on with a record whose body writes and the pair a let holds.

**Step 48 continued, functions giving back a record whose body writes the memory — the design (2026-11-03).**  The record half of
the design of `dad6b6d` (`A_par_pm_call_in_rec`: `kq n x t := mk3 (k n (g n x t)) 0 1`, `g` writes, so `kq` does).  A record is given
back as its first field, the others in the slot block (step 12); a function that writes says the memory after it is *some*
memory (`callee_ok`, `sw`), which loses the slot block, so a caller could not read the fields.  So:
- *The contract*: for a function that writes, the memory after it is some memory whose slot block holds the record's fields
  after the first (`callmw`: `wslot O (tl fields) M'` for a record, `M'` for the other results); `callmw_norec` (a result that is
  not a record: `M'`) at every place the contract was used before.
- *The body*: the sort of a number that writes gets a record leaf `XRetR ri r` (the record from the newest memory: its fields after
  the first put in the slot block, the first returned, as `BRet`'s code does).  A function giving back a record whose signature
  writes has an X body whose leaves are records of its type or its own call (`xrecr ri`), its meaning `denote_xr` (the record;
  the own call `recxr`); its theorem `ctailxr_ok`: the code gives the first field and leaves the slot block with the others over
  some memory — by induction as `ctailx_ok`, the leaves `XRetR` (`crec_ok`, `cput_ok`), the own call (the induction hypothesis in
  the new form), and after a call that writes a record that reads no memory (`after_free`'s record case).  `compile_f_ok_rec`
  gains the case.
- *The callers*: a call of a function giving back a record on a memory, bound (`XBindRM ri f cs args m x`, the record the nearest in
  `x`: meaning `xrec`, code `ccallr`), and `XBindPR` given a function that writes: after a call that writes, `x` reads no memory
  (`xfree`), the fields read from the slot block the contract keeps (`ccallrw_ok`).
- *The reifier*: a function giving back a record that its readers of records refuse, read as an X body of records with `XRetR`
  leaves, its signature writing; a binding call of a function giving back a record read as `XBindRM` / `XBindPR`.
- *Cells*: `A_par_pm_call_in_rec`; a record that writes called at the end, inside an expression, its recursion given a memory it
  writes; and the places this step leaves unread: the function's own call not at the end in a function giving back a boolean or a
  record that writes (bound by a let, negated) — the boolean's cell missed by the boolean half (its slip, recorded).
*Expected*: `A_par_pm_call_in_rec` and the new cells but the own call not at the end.

**Step 48 continued (2026-11-04): functions giving back a record whose body writes the memory; the pair a let holds goes on.**
Built, the design's record half:
- *`KQR.v`*: the contract of a function that writes keeps a record's slot block: the memory after it is some memory whose slot
  block holds the fields after the first (`callmw`, `callmwp`; for the other results the end memory itself, `callmw_norec`).  A
  record as a leaf of the sort of a number that writes (`XRetR`: its fields after the first put in the slot block, the first
  returned) and a call giving back a record on a memory, bound (`XBindRM`); `XBindPR` takes a function that writes too (after it,
  what follows reads no memory).  A function giving back a record whose signature writes has an X body whose leaves are records of
  its type or its own call (`xrecbody`), its meaning `denote_xr`; its theorem `ctailxr_ok` (the code returns the first field and
  leaves the slot block holding the others over some memory), the same induction as `ctailx_ok` (its text made from that
  lemma's by a script, the leaves and the binding calls apart); after a call that writes, a record that reads no memory
  (`after_free_r`; `after_free`'s end memory `xfend`, the slot block written over the call's end memory); a call of a function
  that writes giving back a record (`ccallrw_ok`: the saved cells written back over its end memory).  `compile_f_ok_rec` gains
  the case.  No new hypothesis; `Print Assumptions` the same base.
- *The reifier*: a record as the last resort of an X body's leaf and of what follows a call that writes (`XRetR`, its type the
  function's, `xset_ri`); a function giving back a record that its readers of records refuse read as an X body of records, its
  signature writing; a call of a function giving back a record that writes bound (`XBindRM` on a memory, `XBindPR` given a
  pair).  And a general change to the binding of a call (`bind_first`): it looks into a let's bound term, unless that term is
  itself the call — a helper given a computed argument is written out as a let (`wout`), so a call that writes in such a helper's
  body was not found (`A_par_pm_call_in_rec`, whose helper builds the record); the exception keeps a bound call from being bound
  again (its first version did that until the fuel ran out, on the own call of `A_par_rec_write_own_let`).
- *Cells*: 9 more (952): a record that writes through a call inside an expression and in a test, its recursion given a memory it
  writes; a call that writes inside a record built in place, projected and bound by a let; and the places this step leaves: the
  function's own call not at the end in a record and in a boolean that writes (`A_par_rec_write_own_let`,
  `A_par_bool_write_own_neg` — the boolean's place missed by step 48 continued's first half, a slip recorded here), a template
  giving back a record and a boolean that writes (`A_par_tmpl_rec_write`, `A_par_tmpl_bool_write`: their copies' theorems).  Run
  alone: the five read cells proved, and with them `A_par_pm_call_in_rec`; the four places refused.  Run as a check beside them,
  506 cells (booleans, pairs, writes, records, templates, mutual blocks, memories, and every eleventh cell of the table): 494
  proved, the other 12 the known gaps and the two cells refused by design.
- *Not built yet, the step's continuation*: those four places, and the pair a let holds given to a call (`A_par_pm_call_in_pv`,
  `A_par_pm_call_in_mem`).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the
  trees without their generated files, F62; the boolean half's files / this half's): `HWP_kernel` 2.55 / 2.55 s, `HWP_own` 1.97 /
  1.97, `HWP_irqnow` 1.66 / 1.67 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `2d66918`): **939 of 952 through the verified compiler**, 2 by design,
  10 gaps, 1 not Rocq (was 933 of 943: the five new cells read and `A_par_pm_call_in_rec`; the four places of the new cells left
  unread added as gaps).  The gate on `2d66918`, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the
  five kernels (12 / 11 / 12 / 15 / 13 s); **71 programs through the verified compiler, 0 refused**; the trusted base unchanged.
  The step goes on with the own call not at the end, templates giving back a record or a boolean that writes, and the pair a let
  holds.

**Step 48 continued, templates giving back a boolean or a record that writes — the design (2026-11-04).**  Two of the places the
record half left: `A_par_tmpl_bool_write`, `A_par_tmpl_rec_write` — a template (a recursive function taking functions, §5.1)
whose body writes and gives back a boolean or a record.  Each call giving it known functions gets a copy, read with the
function parameters bound, and a copy's theorem comes from its two equations (`compile_f_okrx` for a number that writes, step
46); a copy whose body is an X body of booleans or of records has no such theorem, and the reader of copies has no X body for
those results.  So:
- *`KQR.v`*: the copies' theorems for an X body of booleans and of records (`compile_f_okrxb`, `compile_f_okrxr`), from
  `compile_f_ok` and the meanings' independence of the own call beyond its values (`denote_xb_recb_ext`, `denote_xr_recr_ext`,
  as `denote_x_recx_ext`).
- *The reifier*: a copy giving back a boolean or a record that the readers of booleans and records refuse, read as an X body (as
  `read_fun_c` reads a function since the record half).
- *`kitc.py`*: a copy whose signature writes and gives back a boolean or a record gets those theorems.
- *Cells*: the two pinned; a template giving back a boolean and a record that writes through a call (not only through its
  recursion).
*Expected*: those four cells.  The pair a let holds needs the pair as a value in the meanings (the call `k n p` is not
convertible with `k n (fst p, snd p)`: `prod` has no eta, and `k`'s recursion on a symbolic counter does not reduce), so it is a
design of its own; the function's own call not at the end comes after this one.

**Step 48 continued (2026-11-04): templates giving back a boolean or a record that writes.**  Built as designed:
- *`KQR.v`*: the copies' theorems for an X body of booleans and of records (`compile_f_okrxb`, `compile_f_okrxr`), from
  `compile_f_ok` and the meanings' independence of the own call beyond its values (`denote_xb_recb_ext`, `denote_xr_recr_ext`,
  made from `denote_x_recx_ext`'s text; `xresb_ext`, `xrecb_ext`, `xresR_ext`, `xrecR_ext`).  No new hypothesis;
  `Print Assumptions` the same base.
- *The reifier*: a copy giving back a boolean or a record that the readers of booleans and records refuse read as an X body, its
  signature writing (the records' type set, `xset_ri`); the binding of a call (`bind_first`) asks a template's call for its
  copy's signature (`tcall`), as the readers do — a boolean's call in a test was bound only when it was not a template's.
- *`kitc.py`*: a copy whose signature writes and gives back a boolean or a record gets those theorems.
- *Cells*: 2 more (954): a template giving back a boolean and a record that writes through a call.  Run alone, with every
  template cell (19): all proved, the two pinned by the record half among them.  Run as a check beside them, 507 cells (booleans,
  pairs, writes, records, templates, functions given, mutual blocks, memories, and every eleventh cell of the table): 497
  proved, the other 10 the known gaps and the two cells refused by design.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the
  trees without their generated files, F62; the record half's files / these): `HWP_kernel` 2.59 / 2.57 s, `HWP_own` 1.99 / 1.98,
  `HWP_irqnow` 1.68 / 1.68 — the same (a first run, on a machine loaded by other work, spread 0.15 s between rounds; the second
  is the one given).
- The C: 63 of 63 byte-identical.  The construct table (on `4804dc5`): **943 of 954 through the verified compiler**, 2 by design,
  8 gaps, 1 not Rocq (was 939 of 952: the two new cells read and the two the record half pinned).  The gate on `4804dc5`, the walk
  switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 11 / 11 / 14 / 13 s); **71 programs
  through the verified compiler, 0 refused**; the trusted base unchanged.  The step goes on with the function's own call not at
  the end and the pair a let holds.

**Step 48 continued, the function's own call not at the end of a boolean or a record that writes — the design (2026-11-04).**
`A_par_bool_write_own_neg` (`negb (kbo m (x + 1) (upd 0 x x t))`), `A_par_rec_write_own_let` (`let w := kro m .. in mk3 (f1 w + 1)
(f2 w) (f3 w)`).  A number's own call is bound by `XBindR` (step 47), its value a number.  A boolean's or a record's own call
gives a value of that kind, and the meaning of a number's body has no own call of those kinds.  So:
- *`KQR.v`*: `XBindRB cs args m x` and `XBindRR ri cs args m x`: the function's own call on the memory `m`, its boolean the nearest
  boolean or its record the nearest record in `x`, `x` run after it and reading no memory (`xfree`).  Their meanings are in
  `denote_xb` and `denote_xr`, through the own call there.  A number's body has neither (`xnum`, asked by its `wf_f`, a premise of
  `ctailx_ok`).  The boolean's body gets its own theorem `ctailxb_ok` as the record's has (the code returns the boolean as 1 or 0),
  made from `ctailx_ok`'s text in the same way; the route through the number's meaning (`denote_x_xb`) is removed, since that
  meaning has no own call of a boolean.  C: the call into a variable under the function's own name; the record's fields through
  `ccallr`.
- *The reifier*: such a call bound by a let (`bindc`, and the let of a record).  A call not bound by a let is bound first
  (`bind_first`), the let's type a number and, when what follows is not read, a boolean, then a record: the reader does not know
  the function's result there, and the let's type is not part of the meaning (the check goes through zeta).
- *Cells*: the two pinned; the boolean bound by a let; the record's inside an expression.
*Expected*: those four.

**Step 48 continued (2026-11-04): the function's own call not at the end of a boolean or a record that writes; a call at the end of
one, mutual blocks of them.**  Built as designed, and one place found on the way:
- *`KQR.v`*: `XBindRB`, `XBindRR`, the function's own call on a memory, its boolean or its record the nearest of its kind in what
  follows, which reads no memory (`xfree`); C: the call into a variable under the function's own name, the record's fields through
  `ccallr` (`ccallrw_ok`).  Their meanings are in `denote_xb` and `denote_xr`.  A number's body has neither (`xnum`, in its `wf_f`, a
  premise of `ctailx_ok`).  The boolean's body has its own theorem `ctailxb_ok` (`after_free_b`), made like the record's from the
  number's text, one script now making all three (`xresb_calln` and its fellows); the route through the number's meaning
  (`denote_x_xb`, `xres_xresb`, `xrec_xrecb`) is removed.  No new hypothesis; `Print Assumptions` the same base.
- *The reifier*: such a call bound by a let (`bindc`, the let of a record); `bind_first` binds an own call not bound by a let, its
  let's type a number, then a boolean, then a record, until what follows is read (the type is not part of the meaning).  Found on
  the way: a boolean or a record that writes, called at the end of a function giving back one, was read as `XCall`, not a leaf of
  those bodies, which also refused every mutual block of them (a member is one call of its block): it is now read as the call bound
  and its result the leaf (`XBind` with `XRetB`, `XBindRM` with `XRetR`; for a boolean the same code).
- *Cells*: 8 more (962): the boolean's own call bound by a let, the record's inside an expression; both with a template; a mutual
  block of booleans and of records that write; a boolean and a record that writes called at the end.  Run alone: all proved, and
  with them `A_par_bool_write_own_neg`, `A_par_rec_write_own_let`.  Run as a check beside them, 511 cells (booleans, pairs, writes,
  records, templates, functions given, mutual blocks, memories, and every eleventh cell of the table): 503 proved, the other 8 the
  known gaps and the two cells refused by design.
- *Not built yet, the step's continuation*: the pair a let holds given to a call (`A_par_pm_call_in_pv`, `A_par_pm_call_in_mem`).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the
  trees without their generated files, F62; the templates' files / these): `HWP_kernel` 2.44 / 2.42 s, `HWP_own` 1.82 / 1.85,
  `HWP_irqnow` 1.53 / 1.53 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `9d5ee76`): **953 of 962 through the verified compiler**, 2 by design,
  6 gaps, 1 not Rocq (was 943 of 954: the eight new cells read and the two own calls pinned).  The gate on `9d5ee76`, the walk
  switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 11 / 11 / 14 / 13 s); **71 programs
  through the verified compiler, 0 refused**; the trusted base unchanged.  The step goes on with the pair a let holds.

**Step 48 continued, a call given the pair a let holds — the design (2026-11-04).**  `A_par_pm_call_in_pv` (`let p := g n x t in (k n p + 1,
snd p)`), `A_par_pm_call_in_mem`.  The design of `dad6b6d` gave the call the pair's parts, the nearest number and the newest memory;
that is not the user's term: `k n p` is not convertible with `k n (fst p, snd p)` (`prod` has no eta, and `k`'s recursion on a symbolic
counter does not reduce), so the meaning needs the pair as a value, and a pair environment in every meaning and invariant would be
the price.  There is no need for one: `let p := e in BODY` is, up to zeta and beta, a function of the pair given `e`.  So:
- *The reader*: a let of a pair whose body uses the pair bare (not only through `fst` and `snd`) is lifted, before the function holding it
  is read: a function of the program's own, its parameters the free variables of the body in the reader's order, the pair the last
  parameter, its body the let's; the let becomes a call of it given `e`.  The call given a pair expression and the function with a
  pair parameter are constructs of `S` since step 44, proved; on the pair parameter `k n p` is `k n (x, s)`, read as such.  The
  meaning of the function holding the let then reduces to the user's text by beta and zeta: nothing is added to the trust and
  `KQR.v` does not change.  The C has one function more, called once, as a local function written by hand.
- *`kitc.py`*: the lifted function's definition made from its term, as a copy's and a block's are.
- *Places*: a let whose body holds the function's own call (it cannot be lifted out of the fixpoint), a memory other than the pair's
  in the body (two versions): cells of their own.
- *Cells*: the two pinned; the pair given to two calls; a number's and a boolean's body; the pair given inside a test; the own call in
  the body; the old memory in the body.
*Expected*: those, but the last two.

**Step 48 continued (2026-11-04): a call given the pair a let holds; the step is done but for the two places below.**  Built as designed,
in the reifier alone (`KQR.v` and `kitc.py` unchanged):
- *The reader*: a let of a number and a memory whose body uses the pair bare (`pm_bare`: other than through `fst`, `snd` or a match)
  is lifted before the function holding it is read (`lift_pm`, `lift_all`): a function of its own, `NAME__lK`, its parameters the
  free variables of the body (the counters first), the pair the last; the let a call of it given the pair's expression.  The function's
  definition goes out as a copy's does (the table of `mts`), its theorem as any function's with a pair parameter (step 44), and the
  function holding the let reduces to the user's text by beta and zeta.  A definition holding such a let counts as a function, not a
  helper written out (`is_fn`: written out, the let would come back).  The lift is for a let in tail position or an operand of the
  machine's operations.
- *Cells*: 10 more (972): the pair given to two calls; in the body of a number, a boolean, a record; given in a test; given back; in a
  recursive function; as an operand; and the two places left: the function's own call in the let's body (`A_par_pm_let_own`: it cannot
  leave the fixpoint) and the memory before the pair read in the body (`A_par_pm_let_old`).  Run alone: 8 proved, and with them
  `A_par_pm_call_in_pv`, `A_par_pm_call_in_mem`; the two places refused.  Run as a check beside them, 522 cells (booleans, pairs,
  writes, records, templates, functions given, mutual blocks, memories, and every eleventh cell of the table): 514 proved, the other
  8 the known gaps and the two cells refused by design (on the first version of the scan, F64, which gives the same answers).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the
  trees without their generated files, F62; the own call's files / these): `HWP_kernel` 2.35 / 2.38 s, `HWP_own` 1.78 / 1.80,
  `HWP_irqnow` 1.48 / 1.48 — the same.  The first version of the scan cost 27% (3.00 / 2.27 / 1.87 s), caught here before its commit:
  F64.
- The C: 63 of 63 byte-identical.  The construct table (on `ffd7312`): **963 of 972 through the verified compiler**, 2 by design,
  6 gaps, 1 not Rocq (was 953 of 962: the eight new cells read and the two pinned; the two places left added as gaps).  The gate
  on `ffd7312`, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 11 / 12 / 14
  / 13 s); **71 programs through the verified compiler, 0 refused**; the trusted base unchanged.  What is left of step 48: the two
  places of these cells.

**Step 50, a read of the memory before a write, standing after the write — the design (2026-11-04).**  `A_par_pm_let_old` and forms that
had no cell, measured refused: `let v := wr n s in v * 2 + rd 1 0 s`, `let t := upd 0 a b s in rd 0 b t + rd 1 0 s`, `let '(x, t) := g n a s
in x + rd 1 0 s + rd 0 0 t`, a pair let read through `fst`, a memory's body.  In Rocq the read sees the memory before the write, so
the read can go first: `let r := rd 1 0 s in let t := .. in .. r ..` is the same term up to zeta, and there is no second version of
the memory at run time.  Step 47 does this for the operands of one expression; a let holds the same.  So, in the reader alone:
- *`hoist_read`*: when a body with a let or a match of a pair or a record first is not read, the first read of the newest memory in what
  follows it (`rd`, `rd32`, `rd8`, or a call of a function that reads the memory and does not write it, giving a number or a boolean),
  whose arguments name nothing bound after that first binding, is bound before it, and the body read again; a read at a later place
  in turn.  A fallback: a program read today keeps its C.  In the readers of a number that writes, a memory, a number and a memory
  (`reify_x`, `reify_m`, `reify_pv`); the lift of a pair (step 48 continued) does the same for a memory it would otherwise have to take.
- *The place left*: a read whose index comes from what the write gives (`let v := wr n s in rd 1 v s`) must see the old memory after the
  write: it stays a gap of the fixed side of §0.5's third refusal, or by design when the write's cells come from the data.
- *Cells*: those forms; a read in a test after the write; a read-only call after the write; two reads; that place.
*Expected*: those, but the place left.

**Step 50 done (2026-11-04): a read of the memory before a write, standing after the write.**  Built as designed, in the reifier alone
(`KQR.v` and `kitc.py` unchanged):
- *The reader*: `hoist_read`: a body with a first binding that writes (a let of a memory or of a pair, a pair taken apart, a call of a
  function that writes) which is not read: the first read of the newest memory in what follows (`rd`, `rd32`, `rd8`, or a call of a
  function that reads and does not write it, giving a number or a boolean), its arguments naming nothing bound after that binding, is
  bound before it, and the body read again; in `reify_x`, `reify_m`, `reify_pv`, as a fallback.  The same term up to zeta.  The lift of a
  pair (step 48 continued) does it too for a memory it would have to take (`A_par_pm_let_old`).
- *A correction*: the reifier's own test pinned `let s2 := upd 0 0 1 s in upd 0 1 (rd 0 0 s) s2` as refused, for linearity.  It only reads
  the old memory, so there is no second version at run time: that refusal was an over-rejection.  It is now read (`dup2`); the pin
  is the program that writes the old memory after reading the new (`dup`).
- *Cells*: 14 more (986): the read after a call that writes, a let of a memory, a pair taken apart, a pair bound, in a test; in the body
  of a memory, a pair, a boolean; a call that reads; two reads; a pair a let holds read through `fst` and `snd` in the body of a pair
  and of a memory (both refused before); and the place left: a read whose index comes from what the write gives
  (`A_par_old_read_index`, a gap of the fixed side of §0.5's third refusal).  Run alone: 13 proved, and with them `A_par_pm_let_old`;
  that place refused.  Run as a check beside them, 543 cells (booleans, pairs, writes, records, templates, functions given, mutual
  blocks, memories, and every eleventh cell of the table): 535 proved, the other 8 the known gaps and the two cells refused by design.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the
  trees without their generated files, F62; step 48 continued's files / these): `HWP_kernel` 2.43 / 2.45 s, `HWP_own` 1.84 / 1.86,
  `HWP_irqnow` 1.54 / 1.53 — the same.
- The C: 63 of 63 byte-identical.  The construct table (on `ddfc85b`): **977 of 986 through the verified compiler**, 2 by design,
  6 gaps, 1 not Rocq (was 963 of 972: the thirteen new cells read and `A_par_pm_let_old`, the one place left added as a gap).  The
  gate on `ddfc85b`, the walk switched off: `make.sh` `core-ok`; examples 27 / 27; corpus 36 / 36; the five kernels (11 / 11 / 11
  / 13 / 13 s); **71 programs through the verified compiler, 0 refused**; the trusted base unchanged.  Next: programs across
  modules and files (§12.L), then a second memory parameter of a recursive function, the function's own call in a let of a pair
  used bare, a mutual part of two types.

**Step 51, programs across modules and files (§12.L, §3.7) — the design (2026-11-04).**  Measured refused: a function, a fixpoint, a
writing function, a record in a nested `Module Lib`.  The reifier asks of every constant whether it stands in the root's module
(`eq_mp (fst kn) mp`), and `kitc.py` writes the kernel's short name as a Rocq term, and takes facts about a function from its name and
from the text of the program.  No theorem needs any of this: a constant of another module or file is quoted the same way, and what is
read from it is compared with it by the kernel.  So, with `KQR.v` unchanged:
- *In the program*: a constant of the root's module, or of any file that is not a library's (Rocq's, MetaRocq's, this compiler's, the
  kit's).  Whatever that lets in is still checked by `denote s = f`.  In `reach`, `is_fn`, `helper_of`, `is_tmpl`, the scan for local
  fixpoints.  A mutual block's members stand in the block's module, not the root's.
- *Names*: what `kitc.py` writes is the kernel's full name, which no later name can shadow: functions, record types, constructors.  A
  function the reifier makes (a wrapper, a block, a lifted pair) carries its origin's full name in one identifier, so that two
  functions of one short name in two modules or files have two wrappers.
- *No guessing from names or text*: the reifier says which functions it made and of what constant (for the unfolding order), and which
  are one fixpoint; a user function named like a derived one (`f__c3`, `g__o`) is then an ordinary function.  The entry is the last
  function read.  `kq_shared` is looked for wherever the program's text is, a module or a file included: found nowhere it would mean
  no check of the shared blocks, silently.
- *Files*: a file the program's text requires (or loads) that stands in its directory is compiled first, those it requires first,
  with that directory as a library of no prefix: `Require Import Other.`, `From sub Require Import X.`, as `coqc -Q . ""` would have it.
- *Sections*: a closed section's `Variable` is a parameter; its `Let` leaves a let before the function's next parameter
  (`fun k => let y := e in fun x => b`).  Up to zeta that is `fun k x => let y := e in b`: a helper is written out through the let, a
  function read with the let floated.  A let applied (`(let y := e in fun x => b) a`), which nothing read before, is the same.
- *The refusal left, and a fourth in §0.5*: a constant with no body in Rocq's kernel (an `Axiom`, a `Parameter`, a function behind a
  module's `:`).  Rocq itself cannot run it and there is nothing to compare a meaning with, so no theorem can say the C computes it.
  The refusal says so and names `<:`, which keeps the body.  Pinned, with `<:` as the control.  Refusing a plain access to a block listed
  in `kq_shared` (§9.4) gets its first pins too, its list in a module and in a file, so a list in another place cannot go unnoticed.
- *Cells*: every sort of function and value in a nested module and in another file (number, writing, reading, boolean, a number and a
  memory, record, record given back, record holding a record, data type, constant, big, function given, captures, mutual, parameters in
  another order, local fixpoint, lifted pair); two levels of modules and of files; one short name in two modules or in a module and the
  file, for each sort; the entry in a module and in a file; `Import`, `Require Export`, `Load`; an alias, `Include`, `<:`, `:`, a functor's
  one and two instances; closed sections with `Variable` and `Let`; a primitive record, a type alias, a class in a module.
*Expected*: 1079 of 1093, 7 by design, 6 gaps.  Left for the next step of §12.L: a second memory parameter of a recursive function
(dead or an alias: to read; both live: to pin).

**Step 51 done (2026-11-04): programs across modules and files.**  Built as designed, with `KQR.v` unchanged:
- *In the program*: `in_prog`: a constant of the root's module, or of any file that is not a library's.  In `reach`, `is_fn`, `helper_of`,
  `is_tmpl`, the scan for local fixpoints (which now runs only over the program's constants: it was written with `&&`, F64).  A mutual
  block's members stand in the block's module.
- *Names*: what `kitc.py` writes is the kernel's full name: functions, record types, constructors.  A wrapper, a block, a lifted pair
  carry their origin's full name in one identifier (`mangle`), so two of one short name have two of them.  Copies were unique already.
- *Nothing guessed*: the reifier gives `kitc.py` the functions it made and what each is made from (`mts_info`) and the functions that are one
  fixpoint (`fix1_info`), in place of two patterns on names and one on the program's text; the entry is the last function read.
  `A_par_name_like_derived` is the case that was wrong before: a user function named `foo__c3` or `bar__o` was taken for a copy or a wrapper.
  The parser of a record's shape took a constructor whose name starts with `i` for a number field; fixed.
- *`kq_shared`*: looked for in the program's text and its files, in a module or not (`shared_term`).  Found only in the body's own text, a
  list in another file would have meant no check of the shared blocks, silently.  So the refusal of a plain access gets its first pins, a
  list in a module and in a file.
- *Files*: a file the text requires or loads that stands in its directory is compiled first, those it requires first, with that directory
  as a library of no prefix; a program with no such file keeps its flags.  An example runs across them: `proved/examples/modules`, two
  functions of one short name, an entry in a module, a section's `Let`, a record and a writing function of another file, built and giving
  the answer worked out apart from Rocq (89).
- *Sections*: a helper is written out through a let before its next parameter (`wout`), a function read with the let floated
  (`float_all`, its type by `zeta_prods`), a let applied as a lambda is, in the 11 readers that apply a lambda.
- *The fourth refusal (§0.5, F65)*: a constant with no body in the kernel, with its own reason, which names `<:`.
- *A gap found, no cell before*: `rd 0 2 (fill n 0 s) + a`, a read of a memory made in place as an operand, is refused, while the same with a
  let reads.  Nothing to do with modules: the next step, its cells with it.
- *Cells*: 107 more (1093), in `A_mod_*` and `A_file_*`.  Run alone: 102 proved, the five pins refused with their reasons.  Run as a check
  beside them, 647 cells (booleans, pairs, writes, records, templates, functions given, mutual blocks, memories, and every eleventh cell of the table): 634 proved, the other 13 the six known gaps and the seven cells refused by design.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees
  without their generated files, F62; step 50's files / these): `HWP_kernel` 2.54 / 2.54 s, `HWP_own` 1.94 / 1.91, `HWP_irqnow` 1.61 / 1.59 — the same.
- The C: the 63 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `0b929ef`): **1079 of 1093 through the verified compiler**, 7 by design, 6 gaps, 1 not Rocq (was 977 of 986: the 102 new cells
  read, the five pins refused with their reasons).  The gate on `0b929ef`, the walk switched off: `make.sh` `core-ok`; examples 28
  / 28; corpus 36 / 36; the five kernels (11 / 11 / 11 / 13 / 12 s); **72 programs through the verified compiler, 0 refused**; the
  trusted base unchanged.  Next: a memory made in place and read inside an expression; a second memory parameter of a recursive
  function; the function's own call in a let of a pair used bare; a mutual part of two types.

**Step 52, a memory made in place and read inside an expression — the design (2026-11-04).**  Found by step 51's example, no cell before:
`rd 0 2 (fill n 0 s) + a` refused, where `let t := fill n 0 s in rd 0 2 t + a` is read, and so is `rd 0 2 (fill n 0 s)` alone.  Step 47 binds a
call of a function that writes when it stands inside an expression; a memory made in place, given to a read or to a function that reads,
is the same case: up to zeta the term is `let t := .. in .. rd 0 2 t ..`, every occurrence of the same memory term one let.  So, in the reader alone:
- *`bind_first`*: the memory given to `rd`, `rd32`, `kq_size` or a function taking a memory, when it is not a variable, is what to bind, with
  the type of a memory.  What the operands read of the memory before it is bound before it, as step 47 has it.
- *The place left, by design*: `upd 1 (rd 0 2 (fill n 0 t)) x t` and `rd 0 2 (fill n 0 s) + rd 0 3 (fill n 1 s)`: two versions of the memory both
  used, differing in cells whose number comes from the data (§0.5, third reason); the controls hand the memory on.
- *Cells*: on the left and the right of an operation; `upd`, a let, a call in the place of the memory; `rd32`, `rd8`, `rd16`, `kq_size`; in a test, a
  let's value, a call's argument, a helper's; a read of the old memory before and after it; a function that reads, a function that writes, given it;
  a chain of two; the same term twice; in the body of a boolean, a record, a recursive function; the pins and their controls.
- *Found while narrowing it, no cell before*: `let u := upd 0 x x t in kq m x u + 1` in a function that writes, refused as not well formed, where
  `kq m x (upd 0 x x t) + 1` is read: at the end of a body that writes, the function's own call on the memory a let made was read as a number of the
  body, which `wfx` refuses (rightly: it writes).  It is bound instead, as step 48 continued has it, as an operand, a let's value, a test.
*Expected*: those, but the pins: 1116 of 1132, 9 by design, 6 gaps.

**Step 52 done (2026-11-04): a memory made in place and read inside an expression.**  Built as designed, in the reifier alone (`KQR.v` and
`kitc.py` unchanged):
- *The reader*: `bind_first`'s new mode: the memory given to `rd`, `rd32`, `rd8`, `kq_size`, a function taking a memory or a helper taking one (at its
  parameter's place), when it is not a variable, bound by a let, every occurrence of the same term one let, what the operands read of the
  memory before it bound before it.  The same term up to zeta.  A fallback, last in `reify_x`: a program read before keeps its C.
- *What narrowing it found*: at the end of a body that writes, the function's own call on the memory a let made was read as a number of the
  body and refused as not well formed.  `has_self`: it is bound instead, as an operand, a let's value, a test's operand, as step 48 continued has it.
- *By design*: `A_par_made_two` and `A_par_made_old_write`: two versions both used, differing in cells whose number comes from the data; control
  `A_par_made_seq`, the memory handed on.
- *Cells*: 39 more (1132): `A_par_made_*`, `A_par_own_let_mem_*`.  Run alone: 37 proved, the two pins refused.  Run as a check beside them, 615
  cells: 605 proved, the other 10 the six known gaps and the four of the cells refused by design among them.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees
  without their generated files, F62; step 51's files / these): `HWP_kernel` 2.51 / 2.52 s, `HWP_own` 1.91 / 1.91, `HWP_irqnow` 1.60 / 1.60 — the same.
- The C: 64 of 64 byte-identical.  The construct table (on `99d5a45`): **1116 of 1132 through the verified compiler**, 9 by
  design, 6 gaps, 1 not Rocq (was 1079 of 1093: the 37 new cells read, the two pins refused).  The gate on `99d5a45`, the walk
  switched off: `make.sh` `core-ok`; examples 28 / 28; corpus 36 / 36; the five kernels (11 / 11 / 11 / 13 / 12 s); **72 programs
  through the verified compiler, 0 refused**; the trusted base unchanged.  Next: a second memory parameter; the function's own
  call in a let of a pair used bare; a mutual part of two types.

**Step 53, a second memory parameter (§3.7) — the design (2026-11-04).**  Measured refused: `k4 n u x t` with `u` never read, `k5 n u t x` swapping its two;
non-recursive functions are written out, so they read already.  In the meaning there is one memory only if the two parameters hold the same one, so a
function of two is read as a function of one, by a wrapper, as parameter order is (step 41):
- *The same memory*: `fun n x t => k n t x t`.  Every memory variable that is the newest memory is that one memory.  A recursive call must hand them
  the same memory, up to which of those variables it names; a call of the function likewise.  With conversion alone: nothing in `KQR.v`.
- *A memory never read, handed on as it is*: `k m u (x + 1) (upd 0 x x t)`: the first form does not convert, `k m t ..` against `k m t' ..` at a stuck counter.
  But for any value `u` of it, `fun n x t => k n u x t` is an ordinary function of one memory, and its theorem holds for each `u`; at the memory the call gives
  it, that is the theorem of the wrapper.  One lemma, proved once: `callee_ok_dead` (and `deadN`, `deadC`, which take the function of `u` to the wrapper).
  No assumption, and the C is the C of the function of one memory.
- *By design*: both live, `cp m u (upd 0 x (rd 1 x u) t) (x + 1)`: at each round read from the one and written in the other, two versions differing in cells
  whose number comes from the data (§0.5, third reason).  Control: the same with one memory.  The call giving two versions likewise.
- *Left, gaps*: a memory never read but given another memory by the call or moved by the recursion (no conversion and no fixed value to quantify over); the
  never-read form inside a copy, a local fixpoint and a mutual block; beside a pair parameter.  Each with its cell, the next step's.
- *Cells*: 37: the forms above in every result sort, in any order of parameters, three memories, a mutual block, a copy, a local fixpoint, a big function, the
  entry, a caller of two memories itself.  An example runs it: `proved/examples/two_mems`.
*Expected*: 1144 of 1169, 11 by design, 13 gaps.

**Step 53 done (2026-11-04): a second memory parameter.**  Built as designed:
- *The reader*: the order the syntax takes has one memory, the last (`canon_perm`).  Every memory variable that is the newest memory is that memory: a recursive call
  and a call of the function must give the others the same one, up to which of those variables they name (`alias_norm`).  The wrapper's meaning gives every memory
  parameter the one memory.  A mutual block's members have one memory slot already; a call of a member giving two memories is refused where the block is written
  (`slots_agree`), not left to the kernel's check.
- *A memory never read, handed on as it is*: read with it marked (`CDeadM`), when the first reading fails.  `dead_meaning`: the function of it, `__g`.  `kitc.py` wraps the
  copy theorem in `callee_ok_dead`.
- *`KQR.v`*: `deadN`, `deadC`, `appc_deadC`, `appnT_deadN`, `callee_ok_dead`: added, nothing else touched; no new assumption.  At each value of the parameter the
  function of the others is an ordinary function of one memory, its theorem proved as any other's, and at the memory the call gives there the wrapper is that function.
- *`kitc.py`*: main giving an entry of two memory parameters two different memories is refused (it cannot today: main names one memory).
- *An example runs it*: `proved/examples/two_mems`, two memories handed crosswise and one never read while the other moves, built and giving the answer worked out apart from
  Rocq (18).
- *Left, gaps with cells*: a memory never read but given another memory by the call (`A_par_mem2_dead_other`) or moved by the recursion (`A_par_mem2_dead_moved`); never read inside
  a copy, a local fixpoint, a mutual block (`A_par_mem2_tmpl_dead`, `_lfix_dead`, `_mutual_moved`); beside a pair parameter (`A_par_mem2_hand_on_pair_param`, `_dead_pair_param`).
- *Cells*: 37 more (1169).  Run alone: 28 proved, the two pins and the seven gaps refused with their reasons.  Run as a check beside them, 653 cells: 634 proved, the others the
  known gaps and the cells refused by design among them.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files,
  F62; step 52's files / these): `HWP_kernel` 2.49 / 2.50 s, `HWP_own` 1.90 / 1.91, `HWP_irqnow` 1.59 / 1.60 — the same.
- The C: the 64 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `3fc8bcf`): **1144 of 1169 through the verified compiler**, 11 by design, 13 gaps, 1 not Rocq (was 1116 of 1132: the 28 new
  cells read, the two pins refused, the seven places left added as gaps).  The gate on `3fc8bcf`, the walk switched off: `make.sh`
  `core-ok`; examples 29 / 29; corpus 36 / 36; the five kernels (11 / 11 / 11 / 13 / 12 s); **73 programs through the verified
  compiler, 0 refused**; the trusted base unchanged.  Next: a family of the table crossing memories made in place, what reads
  them, where the expression stands and the sort of the function, which step 52's accident showed was missing; then the gaps,
  §12.P.

**Step 54, a family of the table crossing what writes with what is around it (§3.1) — the design (2026-11-04).**  Step 52's gap was found by accident, writing an example: the
table's nesting family nests one pure core in its contexts, and nothing crossed a memory made in place with the places it can stand in.  So a new family, `X_*`, by construct: ten ways of
making a memory (`upd`, `upd32`, two writes, a let, a recursive call, a helper, a choice, a match, a chain, `snd` of a pair) × twelve ways of reading it (`rd`, `rd32`, `kq_size`, a function that
reads, one that writes, a helper, `fst`, a record's field, a boolean, a pair bound and read, `snd`, a pair taken apart) × eighteen places (the whole, an operand on either side, a test, a let's
value, an argument of a helper, of a call, of a template, a field, a pair, under a let, under a choice, under a match) × four sorts of function, every two of the four crossed: 591 programs.  Measured
on step 53's reader: 465 read.  The refusals are three classes, each general:
- *A helper hiding the read*: `h ..` whose text reads the memory it is given, itself hidden in a helper: helpers written out a level at a time until the made memory shows.
- *The first part of a call that gives back a pair*: `fst (g n b s) + a`: bound by a let of the pair, read through `fst` and `snd` as since step 26.
- *An operand that writes under a let or a match*: `(if a <? b then rd 0 b (fill n a s) else a) + b`.  A let of it cannot be written: a match on a stuck term does not commute with what is around it,
  so `(if c then x else y) + b` and `if c then x + b else y + b` do not convert.  But `f a b n s + b`, with `f` a new function of its free variables and that operand its body, does: delta and beta.
  So it is lifted, as the pair a let holds is (step 48 continued); `KQR.v` unchanged.  As a fallback for the whole program: a program read today keeps its C.  The function's own call in such an operand
  cannot be lifted out of the fixpoint: a cell, a gap, with `A_par_pm_let_own`.
*Expected*: every `X_*` cell read; the C byte-identical.

**Step 54 done (2026-11-04): a family of the table crossing what writes with what is around it.**  Built as designed, in the reifier and the generator (`KQR.v` unchanged):
- *The family*: `X_*`, 591 programs: ten ways of making a memory × twelve ways of reading it × eighteen places × four sorts of function, every two of the four crossed.  On step 53's reader 465 were read.
- *The reader*: helpers written out a level at a time until a memory made in place shows (`unroll`); `fst` of a call giving back a pair: the call bound by a let of the pair; an operand, a call's argument, a let's value,
  a test that writes under a let or a match: a function of its free variables (`lift_ops`, `__kq`), the same term up to delta and beta, as a fallback for the whole program, so a program read before keeps its C.
- *Found by the family*: a function the reifier made, named in the text of another (a lift inside a lift), was named `kqcopy..`, which is no constant: Rocq's anomaly at the definition.  The same since step 51 for
  a pair let inside a pair let, which had no cell.  Now named by the name its definition has (`real_copies`); `A_par_pm_let_nested`.
- *Left, a gap with its cell*: the function's own call in an operand under a choice (`A_par_own_opnd_choice`): it names the fixpoint, so it cannot be lifted out, as `A_par_pm_let_own`.
- *Cells*: 593 more (1762).  All of `X_*` proved when run alone, with `A_par_pm_let_nested`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 53's files / these): `HWP_kernel`
  2.50 / 2.51 s, `HWP_own` 1.90 / 1.91, `HWP_irqnow` 1.60 / 1.61 — the same.
- The C: 65 of 65 byte-identical.  The construct table (on `e86d7c8`): **1736 of 1762 through the verified compiler**, 11 by
  design, 14 gaps, 1 not Rocq (was 1144 of 1169: the 591 new `X_*` cells and `A_par_pm_let_nested` read, the one place left added
  as a gap).  The gate on `e86d7c8`, the walk switched off: `make.sh` `core-ok`; examples 29 / 29; corpus 36 / 36; the five
  kernels (12 / 12 / 12 / 14 / 13 s); **73 programs through the verified compiler, 0 refused**; the trusted base unchanged.  Next:
  the same for the function's own call; then the gaps, §12.P.

**Step 55, the function's own call in every place (§3.1) — the design (2026-11-04).**  The family of step 54 for the function's own call: `Y_*`, 225 programs: six ways of giving it its memory (the same, a write, a let
of a write, a call, a let of a call, none) × fourteen places × three sorts.  Measured on step 54's reader: 163 read.  Three classes:
- *A boolean function that tests its own result, with no memory*: `if kf m (a + 1) b then a <? b else b <? a`, `let c := kf m .. in negb c`.  Refused: `sbb` has no let of the own call; a function with a memory goes through
  an X body since step 48 continued, one without has none.  Records have had the node since step 12 (`BLetRec`).  So `BbLetRec`, in `KQR.v`: a node, its meaning, its code, its well-formedness, three proof cases.  No new assumption.
- *The own call where it stands, in a body with no memory*: `mk3 (f1 (kf m ..) + a) b 0`: bound by a let (the same term up to zeta), read by `BLetRec` or `BbLetRec`.
- *Inside a record, a let around an operand, at the end of a body that writes*: bound first, the let floated: `(let y := e in x) + a` is `let y := e in x + a` up to zeta.
- *Left, gaps with their cells*: the own call under a choice in an operand, in a body that writes or a boolean's or a record's: `(if c then f m .. else a) + b`.  It cannot be bound (it would run when the test is false, and a
  budget of 2^60 would then be run in full), it cannot be lifted (it names the fixpoint), and a match on a stuck test does not commute.  A number function that only reads does it already, the expression's code taking a continuation; the
  X body's has none.  36 cells of one class.
*Expected*: 1933 of 1995, 11 by design, 50 gaps.

**Step 55 done (2026-11-04): the function's own call in every place.**  Built as designed:
- *The family*: `Y_*`, 225 programs: six ways of giving the own call its memory × fourteen places × three sorts.  On step 54's reader 163 were read.
- *`KQR.v`*: `BbLetRec`: let c := the function itself in a boolean's body; its meaning, code, well-formedness, three proof cases, as `BLetRec` for records.  No new assumption.
- *The reader*: in a body with no memory the own call is bound where it stands (`reify_bb`, `reify_br`, as a fallback); a let around an operand floated (`float_op`), the same up to zeta; a let of a record
  holding the own call, at the end of a body that writes, bound first instead of being read as a value of the body.  `A_par_own_nomem_*`: eight programs of a function with no memory using its own result.
- *Left, gaps with their cells*: the own call under a choice in an operand, in a body that writes or a boolean's or a record's: 36 cells of one class.
- *Cells*: 233 more (1995).  Run as a check beside them, 922 cells: 866 proved, the others the 36, the known gaps and the cells refused by design among them.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 54's files / these):
  `HWP_kernel` 2.53 / 2.55 s, `HWP_own` 1.93 / 1.94, `HWP_irqnow` 1.62 / 1.63 — the same.
- *The check itself, faster (owner, 2026-11-04)*: nothing dropped.  The table six cells at a time instead of three, inside the same memory cap; the C check's old side taken from the last check's new side when the code is byte for
  byte the one it ran on (the check compares them first).  From 65 minutes on 1762 cells to 47 on 1995: the C 7 minutes (18), the gate 12 (11), the table 28 (36).
- The C: 65 of 65 byte-identical.  The construct table (on `417fcc1`): **1933 of 1995 through the verified compiler**, 11 by
  design, 50 gaps, 1 not Rocq (was 1736 of 1762: the 189 `Y_*` cells and the eight `A_par_own_nomem_*` read, the 36 of one class
  added as gaps).  The gate on `417fcc1`, the walk switched off: `make.sh` `core-ok`; examples 29 / 29; corpus 36 / 36; the five
  kernels (12 / 12 / 12 / 13 / 13 s); **73 programs through the verified compiler, 0 refused**; the trusted base unchanged.  Next:
  §12.P, Rocq's own measure recursion; the own call under a choice wants the X body's code to take a continuation.

**Step 56, Rocq's own measure recursion: `Program Fixpoint` (§12.P, §4.5, the owner's "level 2") — the design (2026-11-04).**  `Program Fixpoint f (x ..) {measure (m x)} := body` elaborates to `Fix_sub` over `MR lt m` on an `Acc` proof, each
recursive call given a proof.  Conversion can never open it: the recursion is on the `Acc` proof, stuck at a variable.  Measured on gcd and a binary search on the memory, with their real elaborated terms:
- *The one lemma* (`fix_sub_budget`, written once): given `G : nat -> A -> B` and `Fs`, the elaborated functional, if `Fs x h = G k x` whenever `h` agrees with `G (k - 1)` (or a default at `k = 0`) on what `h` is given, then
  `Fix_sub .. x = G k x` for every `k >= m x`.  By induction on the `Acc` proof.  `fix_sub_eq`'s extensionality premise is not needed, so neither functional extensionality nor proof irrelevance is: `Print Assumptions` shows none.
- *The premise, per function*: a few tests walked by a small tactic, in 0 s on both: a test's convoy (`(if c as a return a = c -> R then t else f) eq_refl`) by one lemma of its own, since `destruct c` is ill-typed under the obligations' proofs.
- *`G`*: the body with its proofs dropped, as a fixpoint on a budget, read by the reader as any fixpoint: `Fs` is a term the reifier takes apart, untrusted, and the kernel checks everything.  The program's `f` is then `fun x => G K x`.
- *The budget, with no run-time measure and no cap in the theorem*: a measure `Z.to_nat (Sint63.to_Z e)` is below 2^62 whatever `e` is, so `K = kq_nat 2^60 + kq_nat 2^60 + kq_nat 2^60 + kq_nat (2^60 - 1)`, a constant, within the counters' bound of step 40; §4.5's plan (a measure computed at
  run time, 2^60 "in the domain") is dropped: the equation holds for every argument, so a caller's text, which names `f`, is compiled as it stands.  A measure that is a counter expression: that expression.  Any other measure: refused with its reason, a cell.
- *The theorem about `f`*: `callee_ok` of `fun x => G K x` by the compiler's theorem, then `callee_ok_eq`, proved once: a function's theorem holds of any function equal to it at every argument.  Nothing added to the trust.
- *Cells*: the sorts of function and of result, one parameter and several, a memory, a test, nested tests, a match on a counter, a non-tail call, a caller; a proof of a real obligation in an example, `proved/examples/program_fix`, answers worked out apart.  Left for what follows: `Function`, `Equations`, `{wf R x}`, `dec`.

**Step 56 done (2026-11-04): Rocq's own measure recursion, `Program Fixpoint`, the owner's "level 2".**  Built as designed, simpler than §4.5's plan:
- *`proved/KQRWf.v`, written once*: `fix_sub_budget`: a budget function equal to the `Fix_sub` at every budget above the measure, by induction on the `Acc` proof; `Print Assumptions`: closed.  `fix_sub_eq`'s extensionality premise is not used, so neither functional
  extensionality nor proof irrelevance is.  `convoy_b`, `convoy_n`, `convoy_p`, `convoy_d`: a test as `Program` writes it, its branches taking the test's proof (`destruct` is ill-typed there).  `wf_step`: the premise, per function, in no measurable time.  `to_nat_le_budget`: a measure on a machine number is below the budget whatever the number.
- *`KQR.v`*: `eqN`, `eqC`, `callee_ok_eq`: a function's theorem holds of any function equal to it at every argument.  Added, nothing else touched.
- *The reader*: `pf_all`, as a pass before everything: each `Program Fixpoint`'s functional taken apart, its proofs dropped (`pf_plain`), a fixpoint on a budget made of it, the function one call of that with a constant budget: `kq_nat 2^60 + kq_nat 2^60 + kq_nat 2^60 + kq_nat (2^60 - 1)`, or, a
  measure that is a counter expression, that expression.  Read as any function: no case for it past that.  No cost to a program without a `Fix_sub`.
- *`kitc.py`*: the equation for each such function before anything is made opaque, then `callee_ok_eq` over the compiler's theorem.  A caller's text names the user's function and is compiled as it stands.
- *The acceptance (§4.5)*: `proved/examples/program_fix` is `wfix.body` with `gcd` and `tri` as `Program Fixpoint`, every obligation proved, `gcd`'s through the kit's `mod`: proved, built, and the same answer, 76.  `Print Assumptions` of its top theorem: the kit's and Rocq's integers' only; no obligation, no extensionality.
- *Left*: `{wf R x}` on a relation of the user's (`A_pf_wf_rel`, a gap: no measure to put a budget above); `Function` and `Equations`, next.  A binary search over machine numbers cannot be written so: `lo + hi` can wrap, and its obligation is then false; `wfix_mem` stays in `wfix`'s spelling, whose budget is its own.
- *Cells*: 25 more (2020), `A_pf_*`: each sort of function and result, several parameters, a memory, nested tests, `if dec`, a let, a record, a pair, a caller, a function given, a module, two functions, a measure on a counter and on a sum.  Run alone: 24 proved, `A_pf_wf_rel` refused.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 55's files / these): `HWP_kernel` 2.57 / 2.57 s, `HWP_own` 1.95 / 1.95, `HWP_irqnow` 1.64 / 1.65 — the same.
- The C: the 65 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `cbae7b2`): **1957 of 2020 through the verified compiler**, 11 by design, 51 gaps, 1 not Rocq (was 1933 of 1995: the 24 `A_pf_*`
  cells read, `A_pf_wf_rel` added as a gap).  The gate on `cbae7b2`, the walk switched off: `make.sh` `core-ok`; examples 30 / 30;
  corpus 36 / 36; the five kernels (12 / 12 / 13 / 14 / 14 s); **74 programs through the verified compiler, 0 refused**; the
  trusted base unchanged.  Next: `Function`, then `Equations`.

**Step 57, `Function` (§12.P, §4.5) — the design (2026-11-04).**  `Function f (ps) {measure m x} : T := body` elaborates to `f_F`, a functional with no proof in it, `f_tcc`, stating for each recursive call that the measure falls, `f_terminate`, a `sig` (opaque under `Qed`), and `f := fun ps => let (a, _) := f_terminate ps in a`, with `f_ind`.  Measured on the real elaborated terms:
- *`G`*: `f_F`'s body with its parameter `f` as the budget function: no proof to drop, so simpler than step 56's `pf_plain`.  The same `G`, the same reading, the same `callee_ok_eq`.
- *The equation*: `f_ind` gives every branch, its tests known and each call's result by induction; `f_tcc` gives each call's measure below.  One tactic in `KQRWf.v`, `fn_branch`, over those branches; no `Fix_sub`, no axiom, and it holds under `Defined` and `Qed` alike, since neither opens `f_terminate`.
- *The measure*: `Function` keeps it nowhere but in `f_tcc`, and there a pattern has replaced the parameter: `m < S m` under `n = S m`, `mu (fst (x, y))` under `p = (x, y)`.  Read from the `<`, each pattern's equation turned back.  What is then not in the parameters: refused.
- *The quote*: `tmQuoteRec` quotes the bodies of opaque constants, which the kernel can never open: 32 s on a `Function`'s reifier file, 43 s on a `Program Fixpoint`'s, every proof's closure of `lia`.  `tmQuoteRecTransp .. false` leaves them out.  A program with a `Function` is then asked for what a `Qed` hides of it (`f_F`, `f_tcc`, by name, and what they name) in a second step, from `kitc.py`'s tactic: a bind in the monad on the whole quote costs a tenth of a second on a kernel's program (measured), so only such a program pays.  No program's C changes: what is left out could not have been read.
- *The spellings around it*: `{struct n}` and a mutual `Function` are plain fixpoints, a `Function` with no recursion a plain definition: cells, nothing to do.
- *Left, each with its cells*: a function as a parameter (`A_fn_fun_param`, `A_pf_fun_param`: `pq` is read as a function with a function parameter; it wants a copy per function given, equal to the user's at every argument); a sum of machine numbers as the measure (`A_fn_sum`, `A_pf_sum_machine`: up to 2^63, beyond a counter's 2^62); `{wf R x}` (`A_fn_wf_rel`, as `A_pf_wf_rel`: no measure); `Equations` (`A_eq_num`, `A_eq_mem`, next).
- *The acceptance*: `proved/examples/function_fix`, `wfix.body` with `gcd` and `tri` as `Function`, proofs closed by `Qed`, the answer worked out apart: 76.  26 cells of `Function`, 2 more of `Program Fixpoint`, 2 of `Equations`.

**Step 57 done (2026-11-04): `Function`.**  Built as designed:
- *`KQRWf.v`*: `fn_branch`, one tactic over a branch of `f_ind`: its tests known, each call by induction, each call's measure below by `f_tcc`.  No axiom: `Print Assumptions` of an example's theorem shows the kit's and Rocq's integers' only.
- *The reader*: `fn_make`: `f_F`'s body with its parameter the budget function, through step 56's `pf_gen`, read as any fixpoint; `fn_measure`: the measure from `f_tcc`'s first `<`, each pattern's equation turned back (`m < S m` under `n = S m` is `n`; `mu (fst (x, y))` under `p = (x, y)` is `mu (fst p)`), and what is then not in the parameters refused.
- *`kitc.py`*: the equation for each such function by `f_ind`, under `Defined` and `Qed` alike; the quote `tmQuoteRecTransp .. false`, with a second step only for a program with a `Function` (`has_function`, `quote_function`): a bind in the monad on the whole quote cost a tenth of a second on a kernel's program, measured apart (0.12 s: 2.84 to 2.96), so it is not paid by others.  A `Program Fixpoint`'s reifier file 43 s to 1.5 s, a `Function`'s 32 s to 2 s: the closures of `lia` no longer quoted.
- *The acceptance*: `proved/examples/function_fix` is `wfix.body` with `gcd` and `tri` as `Function`, proofs closed by `Qed`: proved, built, the same answer, 76.
- *Cells*: 30 more (2050).  `A_fn_*` 26: each sort of function and result, several parameters, a memory, nested tests, a let, a record, a caller, a function given, a module, two functions, a measure on a counter, on a pattern of a pair, of an option, on a parameter not first, written inline, `Qed`, `{struct n}`, mutual, no recursion.  `A_pf_fun_param`, `A_pf_sum_machine`, `A_eq_num`, `A_eq_mem`.  Run alone: 23 proved of the 30.
- *Left, each with its cells*: `A_fn_fun_param`, `A_pf_fun_param`: a function as a parameter; `A_fn_sum`, `A_pf_sum_machine`: a measure up to 2^63, beyond a counter's 2^62; `A_fn_wf_rel` with `A_pf_wf_rel`: `{wf R x}`; `A_eq_num`, `A_eq_mem`: `Equations`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 56's files / these, with the new quote): `HWP_kernel` 2.81 / 2.84 s, `HWP_own` 2.08 / 2.12, `HWP_irqnow` 1.83 / 1.79 — the same.
- The C: the 66 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `e2a5c2c`): **1980 of 2050 through the verified compiler**, 11 by design, 58 gaps, 1 not Rocq (was 1957 of 2020: 23 of the 30
  new cells read, 7 added as gaps).  The gate on `e2a5c2c`, the walk switched off: `make.sh` `core-ok`; examples 31 / 31; corpus
  36 / 36; the five kernels (12 / 12 / 12 / 13 / 13 s); **75 programs through the verified compiler, 0 refused**; the trusted base
  unchanged.  Next: any measure with a bound, then a function as a parameter, then `Equations`.

**Step 58, any measure with a bound (§12.P, §4.5) — the design (2026-11-04).**  Step 56 and 57 read two measures: a machine number through `Z.to_nat (Sint63.to_Z e)`, and a counter expression.  Left refused: `n - i`, `mu x / 2`, `Nat.max`, `Z.to_nat (Sint63.to_Z hi - Sint63.to_Z lo)`, the width of a range, the natural measure of a binary search; `mu x + mu y`.  The last two reach 2^63, above a counter's 2^62, so they are not a matter of reading only.
- *The bound*: what the budget needs is a number or a counter above the measure, not the measure's shape.  The reader writes the measure's definitions out (`pf_unf`), then bounds it: an interval for a term of `Z` (`zb`: `to_Z` of `Sint63` and `Uint63`, literals, `+`, `-`, `min`, `max`, by a literal `*`, `/`, `mod`), a number or a counter expression for a `nat` (`nb`: `+`, `S`, a `-` by what it subtracts from, `min`, `max`, `/`, `mod`, `pred`, `log2`, `sqrt`, `div2`, a product of numbers).  Nothing here is trusted: the one tactic `KQRWf.bound_le`, the bounds of the machine numbers in it and arithmetic, proves it, and a wrong bound is a failed proof.  The forms step 56 and 57 read keep their terms and their C.
- *A budget in phases*: a counter stops at 2^62 (its room for arithmetic: `cbz_small`), the width of a range reaches 2^63 - 1.  A budget function's budget run out does not have to end: it hands on to the phase before it, whose own budget is full.  `G1 0 x` is the body with its calls of `G0 K`, `G1 (S k) x` the body with its calls of `G1 k`: read as any fixpoint, the O branch's call a call of another function, so nothing is added to `S`.  One lemma, `KQRWf.fix_sub_phase_F`, from the phase before to the next, on `fix_sub_budget_F`'s form, so no proof irrelevance is needed: `m x <= k + S Kp`.  As many phases as the bound asks; a program whose measure fits has one, and the same C.
- *`Function`*: the same, each phase's lemma by its induction principle; by `functional induction`, since `f_ind` takes a parameter uniform in the recursion ahead of its motive (`A_fn_m_sub_counter`, found by its cell).
- *Cells*: 18: `A_pf_m_*` each operation on machine numbers and on counters, a measure of the program's own, `A_fn_m_*`; `A_fn_sum`, `A_pf_sum_machine` read, no longer gaps.
- *The acceptance (§4.5, again)*: `proved/examples/program_fix_mem` is `wfix_mem.body`, the binary search, the fill and the recursion that is not a tail call, as `Program Fixpoint`, with `lo + (hi - lo) / 2`, every obligation proved, the answer worked out apart: 544.

**Step 58 done (2026-11-04): any measure with a bound.**  Built as designed:
- *`KQRWf.v`*: `fix_sub_phase_F`; `fn_branch_ph`; `bound_le`, `bound_of`, with `sint_bounds`, `uint_bounds`, `nat_div_le`, `nat_mod_le`, `kq_budget_val`.  `Print Assumptions` of the lemma: closed.
- *The reader*: `pf_unf`, `zb`, `nb`, `pf_bound`; `pf_gen` makes a budget function per phase (`pg_gs`); `pf_counter` looks into a sum, where it took `mu x + 1` for a counter expression.  A program with no such measure sees none of it.
- *`kitc.py`*: the equation in phases, for both spellings; `functional induction` for a `Function`, which `f_ind`'s uniform parameter forced.
- *The acceptance*: `proved/examples/program_fix_mem`: proved, built, 544, as `wfix_mem`; its binary search on 2 phases.
- *Cells*: 18 more (2068): each proved, and `A_fn_sum`, `A_pf_sum_machine`, gaps before.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 57's files / these): `HWP_kernel` 2.61 / 2.61 s, `HWP_own` 1.98 / 1.97, `HWP_irqnow` 1.67 / 1.66 — the same.
- The C: the 67 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `6add419`): **2000 of 2068 through the verified compiler**, 11 by design, 56 gaps, 1 not Rocq (was 1980 of 2050: the 18 new
  cells read, `A_fn_sum` and `A_pf_sum_machine` read).  The gate on `6add419`, the walk switched off: `make.sh` `core-ok`;
  examples 32 / 32; corpus 36 / 36; the five kernels (12 / 12 / 12 / 13 / 13 s); **76 programs through the verified compiler, 0
  refused**; the trusted base unchanged.  Next: a function as a parameter, then `Equations`.

**Step 59, a function as a parameter of a measure recursion (§5.1, §12.P) — the design (2026-11-04).**  `A_fn_fun_param`, `A_pf_fun_param`: `pq (fun i => i + b) a` with `pq (f : int -> int) (x : int)`.  Both spellings make `pq` one call of a budget function `pq__wg k f x`, a fixpoint with a function among its parameters, which is a template (§5.1).  But a caller's text names `pq`, the user's, which no conversion opens, so `pq`'s copy cannot be `pq__wg`'s:
- *The copy*: `pq__cK := fun c x => pq (fun i => i + c) x`, the user's function at the function given, the form every copy has, so a caller's text converts with it in one step, as any template's.
- *Its reading*: the wrapper written out at the function given, `fun c x => pq__wg K (fun i => i + c) x`, read as any function, its call a call of `pq__wg`'s own copy, made first (`ensure`).
- *Its theorem*: by `callee_ok_eq` as `pq`'s own in step 56, from the theorem of that reading: `pq__w F x = pq F x` is `pq`'s equation at the function given, proved once for every `f`.  So the lemma is by the function's name, not by its place in the program's list, which a template is not in.
- *A function built anew at each round* (`pq (fun i => f i + 1) (x - 1)`): by design, §0.5's first refusal, as for a `Fixpoint`: its copies would have no last one.  `A_fn_f_grows`, `A_pf_f_grows`; the control is `A_fn_fun_param`.
- *Cells*: 26: for both spellings, two functions given, one named, one reading the memory, one giving a boolean, the function not the first parameter, two functions as parameters, a memory given back, a writing number function, a record, inside a function given to a template, a helper handing it on, a measure on a counter, and the two pins.
- *The acceptance*: `proved/examples/fun_fix`, both spellings, a function naming the caller's variable, one reading the memory, one giving a boolean; the answer worked out apart, 47.

**Step 59 done (2026-11-04): a function as a parameter of a measure recursion.**  Built as designed:
- *The reader*: `tmpl_tys` takes the function one call of a budget function; `ensure` makes the budget function's copy, then reads `pq__cK` as the wrapper written out (`wrap_read`), with its `__w` text.  `KQR.v` and `KQRWf.v` unchanged.
- *`kitc.py`*: each function's equation by its name (`reqs`), since a template is not in the program's list; a copy's: that equation at the functions given (`pfc`), then `callee_ok_eq`.
- *The acceptance*: `proved/examples/fun_fix`: proved, built, 47.
- *Cells*: 26 more (2094): 24 proved, the two pins refused, by design (13 now); `A_fn_fun_param`, `A_pf_fun_param`, gaps before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 58's files / these): `HWP_kernel` 2.57 / 2.60 s, `HWP_own` 1.94 / 1.95, `HWP_irqnow` 1.63 / 1.63 — the same.
- The C: the 68 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `2ba5d30`): **2026 of 2094 through the verified compiler**, 13 by design, 54 gaps, 1 not Rocq (was 2000 of 2068: 24 of the 26
  new cells read, the 2 pins by design, `A_fn_fun_param` and `A_pf_fun_param` read).  The gate on `2ba5d30`, the walk switched
  off: `make.sh` `core-ok`; examples 33 / 33; corpus 36 / 36; the five kernels (12 / 12 / 12 / 14 / 13 s); **77 programs through
  the verified compiler, 0 refused**; the trusted base unchanged.  Next: `Equations`.

**Step 60, `Equations` (§12.P, §4.5) — the design (2026-11-04).**  `Equations f ps : T by wf (m ps) lt := ..` elaborates to `f := fun ps => FixWf P (fun x H => f_functional .. (fun .. => H ..)) ..`: `FixWf` is `Fix` on the relation of the measure, `f_functional` has the function last among its parameters and a proof last among a call's arguments, and its tests sit in clause constants `f_clause_1`, `f_clause_1_clause_1`, each taking the rest of the parameters and the function again, through `inspect` (a definition of the user's, as `Equations`' manual writes it) or `dec`.  Measured on the elaborated terms.  `f_unfold_eq` rests on functional extensionality, so it is not used:
- *The one lemma*: `fix_wf_budget_F`, `fix_sub_budget_F`'s twin on `Fix_F`; `fix_wf_phase_F` the same for a phase.  `Print Assumptions`: closed.
- *`G`*: `eq_norm` writes the clauses out at the function (each constant given it), a match on `inspect c` taken apart at its constructor, an application pushed into a match's branches, the proof of each call dropped.  Then step 56's `pf_gen`: budget, phases, bound, all of it.  The measure comes from `FixWf`'s instance `wf_tele_measure .. m lt ..`.  Not by conversion, as for the other two spellings: the equation carries it.
- *The equation*: one tactic, `eq_step`: the clauses unfolded (the reader names them: `kitc.py` does not look at names), `inspect`'s pair taken apart with its equation, the equation written into `G`'s own test.
- *A function as a parameter*: step 59's copy, by the same equation, nothing more to do.
- *Structural `Equations`*: a plain `fix`, but `match n with O => fun x => .. | S m => fun x => .. end x`: the match on the counter gives a function.  No conversion opens that under a variable, so `denote s = f` cannot hold; its two equations at `O` and `S _` hold by conversion, the theorem a copy takes.  The reader pushes the application in (`conv_all`), for every fixpoint: a user may write it so as well, `Fixpoint f (n : nat) : int -> int := match n with ..`, which had no cell.  A member of a mutual block so written: left, `A_eq_mutual`, `A_par_match_fun_mutual`.
- *Cells*: 28: each sort of function and result, `dec`, nested tests, a let, a caller, a module, a function given and as a parameter, a measure on a counter, on a pattern, in phases, no recursion, structural, mutual, `where`; `A_par_match_fun*`; `A_eq_wf_rel` a gap with `A_pf_wf_rel`.
- *The acceptance*: `proved/examples/equations_fix`: `wfix_mem.body` once more, in `Equations`' spelling, the answer worked out apart: 544.

**Step 60 done (2026-11-04): `Equations`.**  Built as designed:
- *`KQRWf.v`*: `fix_wf_budget_F`, `fix_wf_phase_F`, `eq_step`.  Reflexivity comes last in the tactic: tried first, on a goal still holding a test, with `G`'s budget a written `2^62 - 1`, Rocq's unifier opened the budget and ran out of memory (2 GB in 7 s, found on the example's second phase).
- *The reader*: `lib_file` takes `Equations`; `eq_make`, `eq_norm`, `eq_clauses`; `pf_info`'s last but one field names the spelling; `conv_def`, `conv_all`: a match on the counter that gives a function, for any fixpoint of one member.  A program with no such fixpoint scans its declarations once and sees none of it.
- *`kitc.py`*: the equation by `FixWf`, with its clauses made `Transparent` (`Equations` makes them opaque); `cv`: such a fixpoint takes the theorem a copy takes.
- *The acceptance*: `proved/examples/equations_fix`: proved, built, 544.
- *Cells*: 28 more (2122): 25 proved; `A_eq_mutual`, `A_par_match_fun_mutual`, `A_eq_wf_rel` gaps; `A_eq_num`, `A_eq_mem`, gaps before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 59's files / these): `HWP_kernel` 2.54 / 2.54 s, `HWP_own` 1.94 / 1.94, `HWP_irqnow` 1.63 / 1.64 — the same.
- The C: the 69 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `0efd280`): **2053 of 2122 through the verified compiler**, 13 by design, 55 gaps, 1 not Rocq (was 2026 of 2094: 25 of the 28
  new cells read, 3 gaps; `A_eq_num`, `A_eq_mem` read).  The gate on `0efd280`, the walk switched off: `make.sh` `core-ok`;
  examples 34 / 34; corpus 36 / 36; the five kernels (12 / 12 / 13 / 14 / 13 s); **78 programs through the verified compiler, 0
  refused**; the trusted base unchanged.  Next: the own call under a choice and on a deeper counter.

**Step 61, the function's own call under a choice and on a deeper counter (§3.1, §12.A) — the design (2026-11-04).**  The class of 37 cells step 55 left, `(if c then f m .. else a) + b` in a body that writes, a boolean's, a record's; and a class with no cell until now, found by writing this step's cells: `match n with S (S q) => f q ..`, as ordinary as Fibonacci, refused in every sort.  Both are the same difficulty: the form Rocq's text has is not the form the compiler's theorem takes, and no conversion goes from one to the other, a match on a stuck test or counter not commuting.  Both are closed by what steps 56 to 60 built, a function read in a form of the reader's and equal to the user's at every argument (`callee_ok_eq`), with `KQR.v` unchanged:
- *Under a choice*: §12.V step 55 wanted the X body's code to take a continuation, a large change to `KQR.v`.  Not needed: the choice is floated out by the reader, `if c then f m .. + b else a + b`, which it reads already.  Into an operand of anything, a let, a test (`y_pull`, `y_tail`), the rest of the expression written in each branch, which is what the continuation would have done.  Only for a program not read as it stands, so no program's C changes.  The equation: at each counter, test by test, the call by induction (`own_step`); the fixpoint named `f__wy`.
- *On a deeper counter*: `FRec` has the function at the predecessor only.  A budget function above it, as for a measure: `G k n .. := match k with O => .. | S k' => (the body, each own call G k' ..)`, the counter `n` its ordinary parameter and also the budget, `G n n ..`.  Step 56's `pf_gen`, no phase, the measure the counter.  The equation by induction on the budget, the counters taken apart as the body takes them (`deep_step`).  It costs one more counter in the C.
- *By design*: two calls of a function that writes at each round from the same memory, under two choices: §0.5's third refusal, as without the choices.  `A_own_two_choices`; the control, `A_own_two_choices_read`.
- *Cells*: 19: two choices, one inside the own call's argument, a let of the choice, in a test, in a helper's argument, nested, a read after; the deeper counter at the end and in an operand, reading, writing, giving back a memory, a boolean, a record, Fibonacci.
- *The acceptance*: `proved/examples/own_fix`: Fibonacci, two steps at a time over a memory, the own call under a choice with a write; the answer worked out apart: 65.

**Step 61 done (2026-11-04): the function's own call under a choice and on a deeper counter.**  Built as designed:
- *`KQRWf.v`*: `own_step`, `deep_step`.  `KQR.v` unchanged.
- *The reader*: `y_pull`, `y_tail`, `y_fix`, `y_all`, `y_rows`, the last resort of `reify_prog2`; `deep_call`, `deep_body`, `deep_make`, `deep_kns`.  The first version of `deep_body` gave its scan a fuel of 100000 and made `HWP_irqnow` 1.62 to 1.71 s on the reifier's step, found by the timing: a `nat` literal is built each time it is evaluated (F64); 3000 is enough for a body's depth, back to the same.
- *`kitc.py`*: `yf`, `sp == "d"`, each the equation before `Strategy opaque` and then `callee_ok_eq`.
- *The acceptance*: `proved/examples/own_fix`: proved, built, 65.
- *Cells*: 19 more (2141): 18 proved, `A_own_two_choices` by design (14 now); the class of step 55, 36 cells and `A_par_own_opnd_choice`, read.
- *Left*: `A_par_pm_let_own` (a let of a pair holding the own call, used bare), the second memory parameter (7), fixed differences (4), `A_par_mutual_mixed`, `{wf R x}` (3), a mutual block whose match gives a function (2).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 60's files / these): `HWP_kernel` 2.56 / 2.56 s, `HWP_own` 1.94 / 1.96, `HWP_irqnow` 1.64 / 1.65 — the same.
- The C: the 70 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `d3999c8`): **2108 of 2141 through the verified compiler**, 14 by design, 18 gaps, 1 not Rocq (was 2053 of 2122: the class of
  step 55, 36 cells and `A_par_own_opnd_choice`, read; 18 of the 19 new cells read).  The gate on `d3999c8`, the walk switched
  off: `make.sh` `core-ok`; examples 35 / 35; corpus 36 / 36; the five kernels (12 / 13 / 13 / 13 / 13 s); **79 programs through
  the verified compiler, 0 refused**; the trusted base unchanged.  Next: a mutual block of different result types.

**Step 62, a mutual block of different result types; a member's match that gives a function (§3.5, §12.A) — the design (2026-11-04).**  `A_par_mutual_mixed` stood alone in the table, and it turns out to be by design: its member giving a memory writes on what the other's call, writing too, was given.  But a block that only reads, a number and a boolean, a number and a record, was refused as well, and had no cell.  A block's one function has one result.  The members of different types need not share one:
- *A hub*: when one member `h` is the only one the others call, and none of them calls itself (even and odd, of any types), the others are written out in `h`: its own calls are then on deeper counters and may stand in a test, which step 61 reads: a budget function, the test floated.  The others are ordinary functions calling `h`.  Each equal to the user's member at every argument, by step 61's `deep_step`, the members unfolded as the tests take the counters apart.
- *A member's match that gives a function*: `Equations`' mutual, `f_functional f g n x`, and a block written so by hand: step 60 left them; each is such a block after its functional is written out, so the same route, whatever its types.
- *Own calls under a choice in what a budget function was made from*: floated as it is made, no equation being owed for the reader's own function.  `y_post`.
- *`{wf lt n}`*: `Program Fixpoint` elaborates it to `MR lt`, `Function` to `lt` with `well_founded lt` beside its `tcc`: read by steps 56 and 57 already; cells, so the table says so.
- *Left*: both members calling themselves, with different types (`A_par_mutual_both_self`): no member to write the others into.  `{wf R x}` on the user's relation.
- *Cells*: `A_par_mutual_int_bool`, `_int_bool_mem`, `_int_record`, `_three`, `_both_self`, `A_pf_wf_lt`, `A_fn_wf_lt`.

**Step 62 done (2026-11-04): a mutual block of different result types; a member's match that gives a function.**  Built as designed:
- *The reader*: `mix_hub`, `mix_unf`, `mix_direct`, `mix_make`, `mix_kns`, `mix_decls` (a member the program's text does not name is not in what Rocq quotes: added); `y_post`.  `KQR.v` unchanged.
- *`KQRWf.v`*: `deep_step` takes a tactic that unfolds the members, and takes a counter apart before it takes a test apart, since a member's test on `n` opens only then.
- *`A_par_mutual_mixed`*: by design with its pin and a control (15 now).
- *Cells*: 6 more (2147): 5 proved, `A_par_mutual_both_self` a gap; `A_eq_mutual`, `A_par_match_fun_mutual`, gaps before, read.  The design's `A_par_mutual_three` was not written into the table; step 67's cells add it.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 61's files / these): `HWP_kernel` 2.56 / 2.57 s, `HWP_own` 1.96 / 1.95, `HWP_irqnow` 1.66 / 1.64 — the same.
- The C: 71 of 71 byte-identical.  The construct table (on `4ed9b94`): **2115 of 2147 through the verified compiler**, 15 by
  design, 16 gaps, 1 not Rocq (was 2108 of 2141: 5 of the 6 new cells read, `A_eq_mutual` and `A_par_match_fun_mutual` read,
  `A_par_mutual_mixed` by design).  The gate on `4ed9b94`, the walk switched off: `make.sh` `core-ok`; examples 35 / 35; corpus 36
  / 36; the five kernels (12 / 13 / 13 / 18 / 14 s); **79 programs through the verified compiler, 0 refused**; the trusted base
  unchanged.  Next: natural forms the table had no cell for.

**Step 63, natural forms the table had no cell for (§3.1, §12.A) — the design (2026-11-05).**  Step 61 found Fibonacci refused, in a table of two thousand cells: the families vary what the reader was built for.  So a probe, 74 programs written as one writes Rocq, without looking at the reader.  54 are read or are read after this step; the rest are classes, each with its cells:
- *What Rocq's libraries define*: `xorb`, `implb`, `Bool.eqb`, `Sint63.abs`, `Uint63.is_zero`, `is_even`, `oppcarry`, `Nat.iter`, `nat_rect`, `nat_rec`, `proj1_sig` were refused by name, as a library's.  They are helpers like the program's: written out, the same up to delta, so a conversion checks them.  `lib_open` says which, by file and for two files by name, since the readers know `Nat.ltb`, `Nat.add`, `andb` as operations.  A fixpoint inside one is a local fixpoint.
- *A motive*: `nat_rect (fun _ => int) ..` leaves `(fun _ => int) n` as a fixpoint's type and a binder's.  The same up to beta; as a last resort on a program not read, so nothing else changes.
- *A cast*: `(a + b : int)` was refused, a term the readers do not take apart.  The same up to conversion; the same last resort.
- *A value holding a proof*: `proj1_sig (exist _ v p)` read as `v` where it is built in place: the proof is no value, so it need not be plain.
- *`unit`*: a match on `tt`.
- *Left, each with its cells*: an operation of Rocq's machine numbers KQL has no instruction for: `compare`, `compares`, `head0`, `tail0`, `mulc`, `addc`, `subc`, `diveucl`, `diveucl_21`, `addmuldiv` (§12.O, which has them in part); a library function on a counter beyond `S`, `+`, `pred`: `min`, `max`, `sub`, `div2`, `even`, `mul`; a boolean as a field of a record or a data type; a `sig` given back by a function.
- *Cells*: 74, `A_n_*`.
- *The acceptance*: `proved/examples/lib_fix`: `Nat.iter`, `xorb`, `Sint63.abs`, a cast, `nat_rect`; the answer worked out apart: 34.

**Step 63 done (2026-11-05): natural forms the table had no cell for.**  Built as designed, in the reifier alone (`KQR.v`, `KQRWf.v`, `kitc.py` unchanged):
- *The reader*: `lib_open` in `helper_of` and where a local fixpoint is looked for; `ret_ty` through a redex; `ty_beta`, `ty_has`, last resort in `y_all`; a sig's proof no value in `iota_go`; `unit` and `sig` in `head_r`.
- *The acceptance*: `proved/examples/lib_fix`: proved, built, 34.
- *Cells*: 74 more (2221): 54 proved, 20 gaps, four classes.  A probe finds what the families do not: its programs are written with no thought of the reader, so it should be done again as the language grows.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 62's files / these): `HWP_kernel` 2.61 / 2.59 s, `HWP_own` 1.97 / 1.96, `HWP_irqnow` 1.65 / 1.65 — the same.
- The C: the 71 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `f1d978e`): **2169 of 2221 through the verified compiler**, 15 by design, 36 gaps, 1 not Rocq (was 2115 of 2147: 54 of the 74
  new cells read, 20 gaps, each with its category).  The gate on `f1d978e`, the walk switched off: `make.sh` `core-ok`; examples
  36 / 36; corpus 36 / 36; the five kernels (13 / 12 / 12 / 14 / 14 s); **80 programs through the verified compiler, 0 refused**;
  the trusted base unchanged.  Next: the operations of Rocq's machine numbers that its own axioms define by others.

**Step 64, the operations of Rocq's machine numbers that its own axioms define by others (§2.1, §12.O) — the design (2026-11-05).**  `compare`, `compares`, `addc`, `addcarryc`, `subc`, `subcarryc`, `diveucl`, `addmuldiv` have no instruction in KQL, and they need none: `Uint63Axioms` says what each is, `compare_def_spec : compare x y = compare_def x y`, `compare_def` written with `ltb` and `eqb`, and so on (`compares` from `compare_spec`, a lemma of ours).  These are Rocq's own axioms about its integers, which every theorem here rests on already; nothing is added.
- *The form read*: each such primitive replaced by its definition (`pm_table`, `pm_sub`), then step 61's floating: a match on `if c then C1 r else C0 r` is a choice over known constructors, floated out of the match, the match then gone (`y_conb`).  A primitive is stuck on a variable, so this is not a conversion: step 61's route, a function read in a form of the reader's and equal to the user's at every argument (`callee_ok_eq`).
- *The equation*: step 61's tactic, the axioms rewritten first (`prim_rw`); for a function with no fixpoint, `own_step0`.
- *A definition holding one*: a function of its own instead of written out, since a caller's conversion could not see through it (`is_fn`).
- *Left*: `head0`, `tail0`, `mulc`, `diveucl_21`: their axioms only relate them, they need instructions (machine operations, next).
- *Cells*: 12, `A_pm_*`, in a fixpoint, under an operand, writing, in a let, a helper giving `comparison` back.
- *The acceptance*: `proved/examples/prim_fix`: the answer worked out apart: 1062.

**Step 64 done (2026-11-05): the operations of Rocq's machine numbers that its own axioms define by others.**  Built as designed:
- *`KQRWf.v`*: `kq_compares_def`, `prim_rw`, `own_step0`; `own_step` rewrites the axioms first.  `KQR.v` unchanged.
- *The reader*: `pm_table`, `pm_sub`, `pm_has`, `y_nf`, `y_conb`, in `y_all`, the last resort; `is_fn`.
- *`kitc.py`*: the equation of a function with no fixpoint.
- *The acceptance*: `proved/examples/prim_fix`: proved, built, 1062.
- *Cells*: 12 more (2233), all proved; `A_n_compare`, `_compares`, `_addc`, `_subc`, `_diveucl`, `_addmuldiv`, gaps before, read.  `Print Assumptions` of the example's theorem: the kit's and Rocq's integers' only.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 63's files / these): `HWP_kernel` 2.63 / 2.63 s, `HWP_own` 1.98 / 1.99, `HWP_irqnow` 1.65 / 1.67 — the same.
- The C: the 72 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `2442197`): **2187 of 2233 through the verified compiler**, 15 by design, 30 gaps, 1 not Rocq (was 2169 of 2221: the 12 new
  cells read, 6 gaps before read).  The gate on `2442197`, the walk switched off: `make.sh` `core-ok`; examples 37 / 37; corpus 36
  / 36; the five kernels (12 / 12 / 12 / 13 / 13 s); **81 programs through the verified compiler, 0 refused**; the trusted base
  unchanged.  Next: `head0`, `tail0`, the high half of `mulc`, `diveucl_21`.

**Step 65, `head0`, `tail0`, the high half of `mulc`, `diveucl_21` (§2.1, §12.O) — the design (2026-11-05).**  Rocq's axioms only relate these to other operations (`head0_spec` for a positive number, `mulc_spec` as an equation in `Z`), so no definition stands in for them.  They are what a machine has instructions for, as `hw_addr` is what a machine knows: operations of the machine (`Ehwf`, §1.8), the number each gives named by Rocq's own primitive, `hwf_law` the statement that the C gives that number.
- *The operations*: `FHead0`, `FTail0`, `FMulHi`, `FDiv21Q`, `FDiv21R`.  `kq_mulhi a b := fst (mulc a b)` and two more, in the kit, so that one result has a name.  `snd (mulc a b)` needs no operation: it is `mul a b`, proved from `mulc_spec` and `mul_spec`.
- *The form read*: `pm_table`, step 64's: `mulc x y` as `(kq_mulhi x y, mul x y)`, by a lemma; the rest named directly.
- *The C*, trusted as the others in `hw/kq_hw.h` are: `__builtin_clzll` on the tagged word, whose top bit is the number's and whose lowest is set, so never 0; `ctz` on the number, 63 at 0, as Rocq's; the high half by 32-bit limbs and `diveucl_21` by shifting and subtracting, as Rocq's own, no `__int128`, which CompCert has not.  Its wrappers only in a program that uses one: no other C changes.
- *The acceptance*: `proved/examples/mach_fix`: its answer is what Rocq's `vm_compute` gives, `5302306`.

**Step 65 done (2026-11-05): `head0`, `tail0`, the high half of `mulc`, `diveucl_21`.**  Built as designed: `hwfop` five more, `hwf_sem`, the names in `KQLGen.v`, `kq_mulhi`, `kq_div21q`, `kq_div21r` in `KQRun.v`, the C in `hw/kq_hw.h`, `kq_mulc_def`, `kq_div21_def`.  The generator's proof took them with no change, being over any `hwfop`.  What is assumed grows by five statements of the same form as those there (`hwf_law`): the C gives the number Rocq's primitive gives.
- *The acceptance*: `proved/examples/mach_fix`: proved, built, its answer `vm_compute`'s, `5302306`.
- *Cells*: `A_n_head0`, `_tail0`, `_mulc`, `_diveucl_21`, gaps before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 64's files / these): `HWP_kernel` 2.59 / 2.62 s, `HWP_own` 1.97 / 1.99, `HWP_irqnow` 1.65 / 1.66 — the same within the noise.
- The C: the 73 programs before the same but for five new declarations of the external functions, which nothing calls (the first
  build also wrote the five wrappers into every program: the test for use matched the declarations, so it now looks at calls), the
  new example through the verified compiler.  The construct table (on `62cc800`): **2191 of 2233 through the verified compiler**,
  15 by design, 26 gaps, 1 not Rocq (was 2187 of 2233: 4 gaps before read).  The gate on `62cc800`, the walk switched off:
  `make.sh` `core-ok`; examples 38 / 38; corpus 36 / 36; the five kernels (12 / 12 / 13 / 13 / 14 s); **82 programs through the
  verified compiler, 0 refused**; the trusted base: `head0`, `tail0`, `mulc`, `diveucl_21` of Rocq's primitives, which the
  statements of `hwf_law` now name, and nothing else.  Next: counters: `Nat.min`, `Nat.max`, `Nat.sub`, `Nat.div2`.

**Step 66, counters: `Nat.min`, `Nat.max`, `Nat.sub`, `Nat.div2` (§3.5, §12.A) — the design (2026-11-05).**  A counter was `S`, `+`, `pred` and a written number.  These four stay within what they are given (`+` is the only one that grows), so they need no bound of their own: four constructs of `scnt`, `CMin`, `CMax`, `CSub`, `CDiv2`, their meanings, their code (a conditional move, `-` and a move, a shift), each a case of the theorem.  `Nat.mul` grows from the data, `Nat.even` is a test of its own: left, with their cells.
- *Cells*: 9, `A_c_*`, as an argument, in a let, a match on one, nested, compared; `A_n_nat_min`, `_max`, `_sub`, `_div2` read.
- *The acceptance*: `proved/examples/cnt_fix`, worked out apart: 5061203.

**Step 66 done (2026-11-05): counters: `Nat.min`, `Nat.max`, `Nat.sub`, `Nat.div2`.**  Built as designed, in `KQR.v` (`scnt` four constructors, `denote_c`, `ccnt`, `cmax`, `cmaxv`, `clinf`, `pvars`, `wfc`, `sh_c`, `noadd`, `ofn_min`, `ofn_max`, `ofn_sub_sel`, `ofn_div2`, the arms of three mutual inductions and of the simulation), no new assumption, and the reader.
- *The acceptance*: `proved/examples/cnt_fix`: proved, built, 5061203.
- *Cells*: 9 more (2242), all proved; `A_n_nat_min`, `_max`, `_sub`, `_div2`, gaps before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 65's files / these): `HWP_kernel` 2.59 / 2.58 s, `HWP_own` 2.00 / 1.98, `HWP_irqnow` 1.67 / 1.65 — the same.
- The C: the 73 programs before byte-identical, and `modules`, whose hash step 65's check had not recorded, the same as before
  with step 65's five declarations taken out; the new example through the verified compiler.  The construct table (on `f3878f9`):
  **2204 of 2242 through the verified compiler**, 15 by design, 22 gaps, 1 not Rocq (was 2191 of 2233: the 9 new cells read, 4
  gaps before read).  The gate on `f3878f9`, the walk switched off: `make.sh` `core-ok`; examples 39 / 39; corpus 36 / 36; the
  five kernels (14 / 13 / 14 / 15 / 16 s); **83 programs through the verified compiler, 0 refused**; the trusted base as step 65
  left it.  Next: values of a fixed size holding booleans, records and data types.

**Step 67, values of a fixed size holding booleans, records and data types (§0.5, §3.5, §12.A) — the design (2026-11-05).**  A second probe, 116 programs written as one writes Rocq (`int * bool` given back by a search, a record with a flag, `option (int * int)`, `option (option int)`, an enumeration as a field), found the largest class left: 57 refused, 24 of them this one.  §0.5 says whether a value needs a runtime is decided by its size and its lifetime, never by its type; these have a fixed size, and a C programmer writes them as a tagged struct passed by value.  The table's families had varied numbers in their fields only.
- *The difficulty*: a record is held as its numbers, `relim` gives them and `rmk` builds from them.  A boolean's number is 1 or 0, and `(if b then 1 else 0) =? 1` is not `b` up to conversion on a stuck `b`: no reading through numbers converts to the user's text.  And `rmk` on any number is not the inverse: 2 would come back as 1.
- *A boolean as a value*: the table gets an entry for `bool`, its one number `b2i b`, and two nodes: `RBoolV ri b`, a boolean as a value of that type, whose meaning is `b` itself; `BOfRec r`, the boolean of such a value, whose meaning is the value itself.  So the check stays a conversion and no equation is proved per program.  The entry is marked, so that everywhere else a boolean stays a boolean, 1 or 0, as it was.
- *Numbers not free*: `RNC i`: a value whose numbers are not free is not built from numbers alone: `RMk` is refused on it, by the check.  It is built one level, by `RMkR` (step 43), and taken apart one level, by the `*SplitR` nodes (step 43), in every sort.  Nothing else in the theorem changes: a value is still passed, returned through the slot block and held as its flat numbers.
- *A data type holding other than numbers*: its tag, its number slots, its record slots, the same for every constructor: a field goes to the next slot of its type its constructor has not used, so `int + bool` is 3 numbers, tag, number, boolean.  A match is `*SplitR` and a chain of tests on the tag; the branch's binders are moved to the slots.  A constructor is `RMkR` with its tag written, the number slots past its fields zeros, the record slots where it holds no field `RDflt`, the value every other constructor leaves there.  The law: `rb_tag`, per program by a fixed tactic.
- *Data types of numbers only keep their layout*, and a value built and taken apart in place is still read away by iota, so no program read before changes.
- *Captures*: a captured variable's type with parameters (`int * int` too, refused until now, with no cell): `ty_cent`.
- *Left, each with its cells*: a counter as a field (`A_fx_nat_pair`, `_field`, `_opt`): its number is `ofn c`, and a bound must come from somewhere; a memory as a field of a data type (`A_fx_opt_mem`, `_rec`).
- *Cells*: 224: `A_fx_*`: 15 values (`int * bool`, `bool * bool`, nested, records with a flag, an enumeration and a data type as a field, `option bool`, `option (int * int)`, `option r3`, `option (option int)`, sums, a pair holding an `option`, `unit`, a data type of the user's holding a pair and a boolean) crossed with 14 places (a let, a parameter, given back by a tail and a non-tail recursion, a loop's state, a choice, a function that writes, beside a memory, a copy's state, a mutual block's parameter and result, a local fixpoint, a closure, a function given); a boolean field given on, in `&&`, let-bound, copied, a literal; `A_par_mutual_three`, step 62's.
- *The acceptance*: `proved/examples/value_fix`: a flag in a loop's state, a search giving back `int * bool`, `option (int * int)`, a data type with a pair and a boolean; the answer worked out apart: 2663.

**Step 67 done (2026-11-05): values of a fixed size holding booleans, records and data types.**  Built as designed:
- *`KQR.v`*: three nodes, `RBoolV`, `BOfRec`, `RDflt`; `RMkR` on a data type (`canon_mk`, `rs_canon`); the class's `RBl`, `RTb`, `RBI`, `RNC`, `RM`; the laws `rb_tag`, `rb_b`, `rt_b`, and `RNC` in `rl_mk`, `rl_mk_tag`; `kq_rbt_case`, the per-program tactic for `rb_tag`.  The per-program step is a conversion, as before: no equation.
- *The reader*: `rentry` holds each constructor's slots; `ctor_slots`, `slot_ent`, `tag_ents`; `tag_parts` moves a branch's binders to the slots; `tctor_go`; `CRecB`, a record variable holding a boolean; `bool_entry`; `rtab_of` puts a value holding such fields after what it holds; `ty_cent` takes a type with parameters.  In a `let` or a match on a constructor the value is still read away, so no program read before changes: found by the test of step 25's, `w5go`, which failed until `held` and `generic_ind` said so.
- *`kitc.py`*: three kinds of a table entry, `B:`, `G:`, `T:`.
- *The acceptance*: `proved/examples/value_fix`: proved, built, 2663.
- *Cells*: 223 more: 218 proved; `A_fx_nat_pair`, `_field`, `_opt`, `A_fx_opt_mem`, `_rec` gaps; `A_n_sum_ty`, `A_n_option_bool`, `A_n_record_bool`, gaps before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 66's files / these): `HWP_kernel` 2.61 / 2.61 s, `HWP_own` 1.97 / 1.99, `HWP_irqnow` 1.65 / 1.72.  The first version was the same on the first two and 1.64 / 1.71 on the third; a data type's slots were worked out before the test that it is `bool` or `nat`, at every test in every body, and moving that test first left it as it was, so that was not the cause.  **`HWP_irqnow`'s 4% is not explained**: it has no record type at all, and the other two kernels do not show it.
- The C: the 74 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `c7ff7fc`): **2425 of 2465 through the verified compiler**, 15 by design, 24 gaps, 1 not Rocq (was 2204 of 2242: 218 of the 223
  new cells read, 5 gaps; `A_n_sum_ty`, `A_n_option_bool`, `A_n_record_bool` read).  The gate on `c7ff7fc`, the walk switched off:
  `make.sh` `core-ok`; examples 40 / 40; corpus 36 / 36; the five kernels (12 / 12 / 13 / 14 / 13 s); **84 programs through the
  verified compiler, 0 refused**; the trusted base as step 65 left it.  Next: type aliases, the library's recursors, Rocq's lists
  written in the text, tests with a proof.

**Step 68, what Rocq's libraries and ordinary text spell otherwise (§3.1, §12.A) — the design (2026-11-05).**  The rest of the second probe that needs no new construct of `S`: each is the same term up to conversion, or an equation of step 61's kind, with `KQR.v` unchanged.
- *A program's name for a type*: `Definition cell := int`, `Definition P := (int * int)%type`, in a fixpoint's signature, a binder, a match's return type, a record's parameters.  Read as its definition, the same up to delta.  The record table reads it the same way, or the reader's table and `kitc.py`'s differ (`al_t`, `rtab_of`).
- *Lets or a test before the counter's match*: `Fixpoint f m x := let y := x + 1 in match m with .. end`, `if x <? 0 then x else match m with ..`, refused until now with no cell.  The whole body in each branch of the counter's match, an equation at each counter (`y_fix`).  A match on a written constructor is read away first: a fixpoint's guard does not see through it (`y_kn`).
- *A function chosen by a match, applied*: `(if c then f else g) x`, `(match n with ..) x`, in any place.  The arguments in each branch (`y_pull`), an equation.  A convoy written by hand, `match m as k return m = k -> int with .. end eq_refl`, is the same when no branch names the proof: given at once (`y_beta`).
- *The libraries' recursors and small functions*: `bool_rect`, `prod_rect`, `option_rect`, `sum_rect`, `option_map`, `eq_rect` and their `_rec`: helpers, written out (`lib_open`).
- *A test that gives a proof with its answer*: `Nat.eq_dec`, `lt_dec`, `le_dec`, `gt_dec`, `ge_dec`, `le_lt_dec`, `le_gt_dec`, `Uint63.eqs`: read as the boolean test it is, one lemma each in `KQRWf.v`, when what follows does not name the proof (`dec_of`).  `Nat.compare` by its definition, as step 64's `compare`.
- *Rocq's lists on a list written in the text*: `List.fold_left f (cons a (cons b nil)) 0`, `map`, `nth`, `rev`, `app`, `hd`, `tl`, a helper giving one, a let of one: its size is in the text, so nothing runs behind anyone's back.  Worked out before it is read, the same up to Rocq's own reduction (`lu_t`); if it stays stuck on a variable, left as it is.
- *By design, each with a pin and a control*: a list whose length comes from the data, built by a recursion (`A_l_list_data`; control `A_l_list_fold_left`); arithmetic on `Z` (`A_l_z_arith`; control `A_l_z_arith_ctrl`); a counter the recursion grows and gives back (`A_l_nat_ret_grow`; control `A_l_nat_ret_ctrl`).
- *A slip found*: `bound_le`, step 58's: `Nat.div2_decr a a (le_n a)` did not type at the premise it has, and no cell had a measure with `Nat.div2`.  `A_l_pf_div2`.
- *Left, each with its cells*: a recursive function polymorphic in a type (`A_l_poly_rec`, `_nofun`; next step); a function of the program giving a proof with its answer (`A_l_dec_own`); a proof a test gives, named by what follows (`A_l_dec_proof_used`); a local mutual fixpoint (`A_l_fix_mut`); a counter given back that does not grow (`A_l_nat_ret_same`); a fixpoint inside a fixpoint giving back a function (`A_l_ack`).
- *Cells*: 87, `A_l_*`.
- *The acceptance*: `proved/examples/lib2_fix`: a name for a type, a let before the counter's match, a function chosen by a test, `Nat.eq_dec`, `Nat.compare`, a list written in the text, `option_rect`; the answer worked out apart: 4108235.

**Step 68 done (2026-11-05): what Rocq's libraries and ordinary text spell otherwise.**  Built as designed, with `KQR.v` unchanged:
- *The reader*: `al_t`, in `y_all` and in `rtab_of`; `y_fix` for a body that does not start with the counter's match, `y_kn`, `y_rep`; `y_pull` at a match applied, `y_beta`; `fc_has`; `lu_red`, `lu_full`, `lu_t`, `lu_stuck`; `dec_of`, in `pm_sub`; `Nat.compare` in `pm_table`; `lib_open` by name; `body_rtys` through a cast.
- *`KQRWf.v`*: `kq_d_eq`, `kq_d_lt`, `kq_d_le`, `kq_d_gt`, `kq_d_ge`, `kq_d_lel`, `kq_d_leg`, `kq_d_eqs`, `kq_compare_nat`, each with its proof from Rocq's own lemmas, in `prim_rw`.  `bound_le`, on a measure with `Nat.div2`, the first time a cell had one: the lemma's premise was wrong; the function has two names, `Init.Nat.div2` and `PeanoNat.Nat.div2`, by the program's imports; and the budget's facts were posed on every goal, and `lia`, comparing its atoms by conversion, ran `Nat.div2 k` against `kq_nat` of a written number and out of memory: posed only where a budget is.
- *A first version let a template take a type* (`is_prod` on a sort): it did not read a polymorphic recursive function, and every `Equations` cell stopped, `inspect` taken for a clause: found by a run of cells beside the family, and taken out.  A function polymorphic in a type wants a replacement of its own, next step.
- *The acceptance*: `proved/examples/lib2_fix`: proved, built, 4108235.
- *Cells*: 87 more: 77 proved, 3 by design (18 now), `A_l_ack`, `_dec_own`, `_dec_proof_used`, `_fix_mut`, `_nat_ret_same`, `_poly_rec`, `_poly_rec_nofun` gaps.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 67's files / these): `HWP_kernel` 2.62 / 2.63 s, `HWP_own` 1.98 / 2.00, `HWP_irqnow` 1.73 / 1.74 — the same.
- The C: the 75 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `304ee51`): **2502 of 2552 through the verified compiler**, 18 by design, 31 gaps, 1 not Rocq (was 2425 of 2465: the 77 of the
  87 new cells read, 3 by design, 7 gaps).  The gate on `304ee51`, the walk switched off: `make.sh` `core-ok`; examples 41 / 41;
  corpus 36 / 36; the five kernels (12 / 13 / 13 / 14 / 13 s); **85 programs through the verified compiler, 0 refused**; the
  trusted base as step 65 left it.  Next: a function read in another form, its callers told by a lemma: a memory never read, a
  type parameter.

**Step 69, a function read in another form, its callers told by a lemma: a memory never read, a type parameter (§3.7, §12.A) — the design (2026-11-05).**  Two classes with one difficulty.  `kw m t (x + 1) (upd 0 x x t)` with `u` never read but moved by the recursion, or a call giving it another memory: step 53's wrapper needs the same memory, its lemma a fixed one, and neither holds.  `pfold {T} m g x`, a recursive function polymorphic in a type: `pfold int m g x` is not, up to conversion, a fixpoint with `T` put in, since `T` comes before the counter and a fixpoint is stuck on it.  In both a function of its own stands in the first one's place, and it is equal to it at every argument: not a conversion, an induction.
- *What is in its place*: the parameter dropped, from its binder and from every own call; or the type put in.  A row of the reader's holds the function and the statement `forall .., f .. = f' ..` (`rp_def`, `rp_stmt`).  `kitc.py` proves each statement by induction on the counter, `own_step`.
- *Its callers*: their text calls `f'`, each an equation of step 61's kind (`rp_sub`), the lemmas among its rewrites through one hook, `kq_rw`, each program setting it.  So a caller may itself be a fixpoint, or a definition holding such a call.
- *A local fixpoint*, closed, the same: the statement is about the `fix` as the text writes it.  *A definition* that hands a memory only to such a call has then that memory never read: a row of its own (`__n`), its proof no induction.  *A polymorphic definition* holding a polymorphic fixpoint's call: a row at its types.
- *`rec_info2`*: where the program was read in another form, the record table is that form's: a type only `T` becomes has no entry otherwise.
- *No proof search beyond these lemmas, and only for a program not read as it stands*: `KQR.v` is unchanged, and so is the C of every program read before.
- *Left, each with its cells*: a memory never read in a mutual block (`A_par_mem2_mutual_moved`): the lemma is a mutual induction; a measure recursion polymorphic in a type (`A_rp_poly_measure`).
- *Cells*: 26, `A_rp_*`: the parameter at each position, three memories, every result sort, the caller a fixpoint, what is called also read so; `T` a pair, a boolean, a memory, a record, an `option`, two instances, two type parameters, a helper; the pin, both memories live.  `A_par_mem2_dead_moved`, `_dead_other`, `_dead_pair_param`, `_hand_on_pair_param`, `_lfix_dead`, `_tmpl_dead`, `A_l_poly_rec`, `_nofun`, gaps before, read.
- *The acceptance*: `proved/examples/poly_fix`: the answer worked out apart: 1072003.

**Step 69 done (2026-11-05): a function read in another form, its callers told by a lemma.**  Built as designed, with `KQR.v` unchanged:
- *The reader*: `dead_slots`, `rp_occ`, `rp_own`, `rp_def`, `rp_stmt`, `rp_match`, `rp_sub`, `rp_apps`, `rp_rows_of`, `rp_all`, `rp_topo` (each row after what it names), in `y_all`; `y_rows` in the order made; `real_copies` through a product; `rec_info2` of the form read.
- *`KQRWf.v`*: `kq_rw`, a hook in `own_step`, `own_step0`, `deep_step`.
- *`kitc.py`*: the lemmas, in order, the hook set after each.
- *The acceptance*: `proved/examples/poly_fix`: proved, built, 1072003.
- *Cells*: 26 more: 24 proved, `A_rp_dead_live_control` by design, `A_rp_poly_measure` a gap; `A_par_mem2_dead_moved`, `_dead_other`, `_dead_pair_param`, `_hand_on_pair_param`, `_lfix_dead`, `_tmpl_dead`, `A_l_poly_rec`, `_nofun`, gaps before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 68's files / these): `HWP_kernel` 2.60 / 2.59 s, `HWP_own` 1.98 / 1.97, `HWP_irqnow` 1.70 / 1.71 — the same.  The first version marked a definition with no fixpoint by a `rarg` of 1000000, a `nat`: a million cells in every load of the reifier, 17 MB and 2% on each kernel, found by the timing (F64 again); 999.
- The C: the 76 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `a89c37b`): **2534 of 2578 through the verified compiler**, 19 by design, 24 gaps, 1 not Rocq (was 2502 of 2552: the 24 of the
  26 new cells read, 1 by design, 1 gap; 8 gaps before read).  The gate on `a89c37b`, the walk switched off: `make.sh` `core-ok`;
  examples 42 / 42; corpus 36 / 36; the five kernels (13 / 13 / 13 / 14 / 14 s); **86 programs through the verified compiler, 0
  refused**; the trusted base as step 65 left it, four of its names to be taken away (F66, §12.T).  Next: counters and numbers.

**Step 70, counters and numbers (§0.5, §3.5, §12.A) — the design (2026-11-06).**  A counter was `S`, `+`, `pred`, `min`, `max`, `-`, `div2` and a budget.  What is left of the table's list and of the second probe, all the same matter, a counter's machine number: `Nat.even`, `Nat.mul`, `Uint63.of_nat`, `Uint63.to_nat`, `Z.to_nat (Sint63.to_Z e)`.
- *A counter as a number*: `SOfC c`, whose meaning is `ofn c`, `of_Z (Z.of_nat c)`, what `Uint63.of_nat` is a notation for; its code is the counter's atom, which holds that number already.  No instruction.
- *A number as a counter*: `CToNatU e`, `Z.to_nat (Uint63.to_Z e)`, what `Uint63.to_nat` is a notation for: the same word, no instruction.  `CToNat e`, `Z.to_nat (Sint63.to_Z e)`: a conditional move to 0 on the sign.
- *A counter's room*: a counter was below 2^62, its bound asked to leave room above it (`cbz_small`), which nothing used.  `Uint63.to_nat a` reaches 2^63 - 1.  A counter only has to be a machine number: the limit becomes 2^63, in `bok`, `cfits_b`, `cboundv`.  What can grow past it is refused as before, by the check that every counter given is below the callee's bound and below 2^63.  The default bound of a function is unchanged, and a bound is no part of the C.
- *A number written as a `Z`*: `Uint63.of_Z 5`: the reader works it out, `SInt`; the check is by conversion.
- *A counter times a number written in the program*: `CMulK`, either side, one `mul`; the bound of a product is the product of bounds, zero included (`Nat.mul n 0`).
- *`Nat.div`, `Nat.modulo`*: not on the list, the first thing one writes beside `even`: `CDivN`, `CModN`, one instruction each, Rocq's `x / 0 = 0` and `x mod 0 = x` being the machine's.
- *`Nat.even`, `Nat.odd`*: `BEven c`: `c mod 2`, then a test, a value or a conditional move, as a comparison is; `odd` its negation by its definition.
- *A counter chosen by a test*: `CIf b x y`: both counters worked out, a conditional move on the parts of the test (`csel`), as for numbers.
- *`Nat.double`, `succ`, `square`, `Nat.pow` of written numbers*: written out or worked out.
- *By design, §0.5's second reason, each with a control*: `Nat.mul n n`, `Nat.square n`, `Nat.pow 2 n`, and a product or a sum that can pass 2^63 (`Nat.mul 1000 n` for a budget, `Uint63.to_nat a + n`): a number that may need more than a word.  The refusal says so.
- *Left, each with its cell*: a match on a counter giving a counter (`A_c2_match_cnt`); a `min` that bounds its operand (`A_c2_min_clamp`: a bound of the smaller of the two would take `wfc` asking each operand below 2^63); the library's recursive functions on counters, which give back a counter (`gcd`, `log2`, `sqrt`, `land`, `shiftr`, `testbit`), with `A_l_nat_ret_same`; `Nat.b2n`.
- *Cells*: 119, `A_c2_*`: a counter as a number in every place of a number; a number as a counter in every place of a counter, signed and unsigned; a product, `/`, `mod`, `even`, `odd`, a test, in a let, a match, a loop, a recursion, a function giving back a boolean, writing; the same names under `Require Import Arith`, whose module `Nat` is another.
- *The acceptance*: `proved/examples/conv_fix`, answer worked out apart: 37172565.

**Step 70 done (2026-11-06): counters and numbers.**  Built as designed:
- *`KQR.v`*: `SOfC`, `BEven`, `CMulK`, `CToNat`, `CToNatU`, `CDivN`, `CModN`, `CIf`: seven cases of the theorem, each a few lines over the lemmas `ofn_mul` (no premise: the machine's product of the two words is the word of the product, modulo), `ofn_divn`, `ofn_modn`, `ofn_even`, `ofn_to_nat`, `ofn_to_natu`.  A counter's limit 2^63 everywhere it was 2^62, `cbz_small` removed, unused: the proofs took it as it stood, since what they ask of a counter is that it be below `wB`.  A test of the old limit (a let of `n + n` refused for want of room) now tests `n + n + n`.
- *The reader*: `cnt_val`, `pos_lit`, `z_lit`; `Nat.mul`, `Nat.div`, `Nat.modulo`, `Nat.pow`, `Z.to_nat`, a test in `reify_c`; `Uint63.of_Z` in `reify`; `Nat.even`, `Nat.odd` in `reify_b`; `double`, `succ`, `square` in `lib_open`.  `A_c2_ar_*`: under `Require Import Arith`, whose `Nat` names were one worry: all read.
- *A bound*: a function whose bound had to be smaller for `n + n` (`x36`) needs none now.  The bound is in the theorem, not in the C.
- *The acceptance*: `proved/examples/conv_fix`: proved, built, 37172565.
- *Cells*: 119 more: 105 proved; 5 by design; 9 gaps; `A_n_nat_even`, `A_n_nat_mul`, gaps before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 69's files / these): `HWP_kernel` 2.60 / 2.63 s, `HWP_own` 1.99 / 2.01, `HWP_irqnow` 1.74 / 1.73 — the same within the noise.
- The C: the 77 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `b682bd8`): **2641 of 2697 through the verified compiler**, 24 by design, 31 gaps, 1 not Rocq (was 2534 of 2578: 105 of the 119
  new cells read, 5 by design, 9 gaps; `A_n_nat_even`, `A_n_nat_mul` read).  The gate on `b682bd8`, the walk switched off:
  `make.sh` `core-ok`; examples 43 / 43; corpus 36 / 36; the five kernels (13 / 13 / 13 / 15 / 13 s); **87 programs through the
  verified compiler, 0 refused**; `check_trust.py` stopped the chain on `mul_spec`, `div_spec`, `mod_spec`, new in the gate's
  list: `About` shows they are `Uint63Axioms.mul_spec`, `div_spec`, `mod_spec`, Rocq's own and on the list already, printed short
  since `KQR.v` now names them through `Uint63`.  Nothing assumed changed; the three spellings added to `proved/TRUSTED.txt`.
  Next: what a third probe of natural programs found.

**Step 71, a third probe; the state monad (§3.1, §12.A) — the design (2026-11-06).**  106 programs written as one writes Rocq, without looking at the reader: a state monad over the memory, a state machine on a data type, records updated and nested, a record of functions, classes, sections, definitions by tactics, `sig`, `option` and a result type, lists and trees written in the text, the spellings of the operations.  72 read.  What was refused is few classes, the largest one the way a functional programmer writes an operating system's code: `Definition M A := mem -> A * mem`, `ret`, `bind`, `x <- m ;; k`.
- *The monad is no construct*: with `M` written out by hand the sequences, the writes and the tests in a plain function read already: a helper is written out by conversion, and `let (x, t') := (rd h i t, t) in ..` is iota.  So nothing new in `KQR.v`.  What was missing:
  - *A name for a type made from types*: `M A` (`al_t` took `Definition cell := int` only): its body at its arguments, the same up to delta and beta.
  - *A fixpoint whose result is such a name*: `Fixpoint loop k i : M int := match k with ..`: the match gives a function, step 60's `conv_def`, which looked at the type as it stands, and at a branch that is a lambda.  A branch that is a helper's call applied to more is one application (`pf_beta`).
  - *A test in a continuation*: `x <- rdm 0 i ;; if x <? j then ret x else ..` leaves `(if c then f else g) t'` inside the helpers.  `mo_t` writes out a helper that takes a function, then step 68's floating sees the choice.  The equation: step 61's tactic, tried with the helpers unfolded on the user's side too (`cbn`, then a `cbv` that leaves only `kq_nat`), after the tactic as it stood, so no program read before changes its proof.
- *Data written in the text*: a fixpoint on a list, a tree, a string given constructors: worked out as step 68 works out Rocq's own list functions, by the same rule and for the program's own fixpoints, a table behind a constant too.  The same up to conversion.  A fixpoint on data in any other place is what it was, §0.5's first refusal.  So it must not be taken for a counter's: `y_fix` and `deep_body` look at the type.
- *A helper that chooses a function*, `mk c a` with `mk c := if c then f else g`; a match on a helper that chooses between known constructors, `let (o, t) := tk a s in ..` with `tk` giving `(None, t)` or `(Some v, t')`: written out, then floated.
- *A constant under a primitive projection* was not looked for (`consts`): `pa (f n a)`, `f` recursive.  Cells for primitive projections with it.
- *By design*: `PArray`, Rocq's primitive arrays: persistent, every version kept, which is a runtime (§0.5's first reason).  Control: a memory.
- *Left, each with its cells*: a value and a memory given back together by a recursion, the value not one number (`M unit` for a procedure, `int * int * mem`, a record holding a memory); a record of functions or a class's instance given to a recursive function; a value holding a proof given back (`sig`, a `sumbool` by tactics, `Scheme Equality`'s `eq_dec`); a function giving back a counter; floating point (§12.I).
- *Cells*: 111, `A_q_*`.
- *The acceptance*: `proved/examples/monad_fix`: a procedure that fills, a recursion that sums, a test in the monad, a table and a tree written in the text; the answer worked out apart: 56043.

**Step 71 done (2026-11-06): a third probe; the state monad.**  Built as designed, in the reifier and one line of `kitc.py` (`KQR.v`, `KQRWf.v` unchanged):
- *The reader*: `ty_fun`, `al_beta` and a case in `al_t`; `conv_def` on the type with its names written out, `pf_beta` one application; `mo_fun`, `mo_t`; `lu_data`, `lu_cdata`, `lu_fix_lit`, a case in `lu_red`; `y_on_nat`, and `deep_body` asking for a counter; `consts` through a projection.  All of it in the last resort, on a program not read as it stands.
- *`kitc.py`*: an equation's tactic tried as it stood, then with `cbn`, then with a `cbv` that leaves `kq_nat`: the first two are the same proof on every program read before.
- *The acceptance*: `proved/examples/monad_fix`: proved, built, 56043.
- *Cells*: 111 more: 94 proved, 16 gaps, `A_q_parray_get` by design; `A_fx_nat_opt`, a gap before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 70's files / these): `HWP_kernel` 2.60 / 2.62 s, `HWP_own` 1.98 / 1.97, `HWP_irqnow` 1.74 / 1.73 — the same.
- The C: the 78 programs before byte-identical, the new example through the verified compiler.  The construct table (on
  `95e32a8`): **2736 of 2808 through the verified compiler**, 25 by design, 46 gaps, 1 not Rocq (was 2641 of 2697: 94 of the 111
  new cells read, 1 by design, 16 gaps; `A_fx_nat_opt` read).  The gate on `95e32a8`, the walk switched off: `make.sh` `core-ok`;
  examples 44 / 44; corpus 36 / 36; the five kernels (13 / 12 / 13 / 14 / 13 s); **88 programs through the verified compiler, 0
  refused**; `check_trust.py`: trust unchanged.  Next: a procedure in a monad, a test in a monad.

**Step 72, a procedure and a test in the monad (§0.5, §12.A) — the design (2026-11-06).**  What step 71 left of the monad: `M unit`, the procedure, and `M bool`, a function giving back a test and the memory, when they recurse or choose.  (Written out where it is used, a function with no test already is.)  A function giving back a number and a memory is a form `compile` takes (step 26), with no other value in it, and no conversion takes `unit * mem` or `bool * mem` to it.  Step 69's route does: a function of its own in its place, equal at every argument by induction.
- *`M unit`*: `f args = (tt, f' args)`, `f'` giving back the memory.  Its body: `f`'s with the helpers written out, a pair's memory at its ends, the own call taken apart by a let of its memory.
- *`M bool`*: `f args = let (x, t) := f' args in (x =? 1, t)`, `f'` giving back a number and the memory: 1 or 0 at its ends, a test of the number where its own call's boolean was used.
- *Its callers*: rewritten as a row's are; `fst`, `snd` of such a call directly, a match on it by the floating of step 68, a pair's parts bound by lets on the way, the number first (`y_red`).
- *A write and a test*: two tactics change, for all equations, both only after what they did before fails or where nothing was stuck: a pair taken apart before a test, since a test can name its parts on one side and the pair on the other; `fst`, `snd` reduced.
- *By design*: both parts of two calls of such a function that writes at a moving index, from one memory: §0.5's third reason.  Control: one call.
- *Left, each with its cell*: other values with a memory given back by a recursion: an enumeration (`A_m_e_enum_ret`), `option int`, a pair (`A_m_e_opt_ret`, `A_m_e_pair_ret`), which take more than the one number a function returns; a function named `p1` or `p2`, a token of the notations of MetaRocq, which every generated file imports: found by writing these cells (`A_m_e_name_p1`).
- *Found on the way*: a line of the reifier's output broken after a parenthesis hid a made function from `kitc.py`'s pattern, by the length of the names.
- *Cells*: 24, `A_m_*`.
- *The acceptance*: `proved/examples/proc_fix`: a procedure that fills, a search giving back whether it found, a procedure with a test; the answer worked out apart: 150.

**Step 72 done (2026-11-06): a procedure and a test in the monad.**  Built as designed, with `KQR.v` unchanged:
- *The reader*: a row's mark among its slots (`rp_um`, `rp_bm`, `rp_real`); `um_red`, `um_tr`, `um_snd`, `bm_tr`, `bm_snd_fst`, `um_rows`; `um_plain`, `um_inl`: what has no test written out in place; `bm_part`; in `y_red`, a match on known parts and the parts of a let; the floating goes on after a reduction.
- *`KQRWf.v`*: `own_step`, `own_step0`: `fst`, `snd` reduced, a pair taken apart before a test.
- *`kitc.py`*: a row's statement tried three ways, as an equation is since step 71, what is rewritten left folded (`keepf`); the pattern on the reifier's list allows a line broken after a parenthesis.
- *The acceptance*: `proved/examples/proc_fix`: proved, built, 150.
- *Cells*: 24 more: 19 proved; `A_m_b_two_calls` by design; `A_m_e_enum_ret`, `_opt_ret`, `_pair_ret`, `_name_p1` gaps; `A_q_mon_mem`, a gap before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, in copies of the trees without their generated files, F62; step 71's files / these): `HWP_kernel` 2.72 / 2.73 s, `HWP_own` 2.08 / 2.10, `HWP_irqnow` 1.81 / 1.83 — the same..
- The C: 79 of the 80 programs before byte-identical; `mach_fix` differs in its driver alone, which no longer sets up the slot
  block: the form read holds no pair, and its function's C is the same; the new example through the verified compiler.  The
  construct table (on `dcf40e2`): **2756 of 2832 through the verified compiler**, 26 by design, 49 gaps, 1 not Rocq (was 2736 of
  2808: 19 of the 24 new cells read, 1 by design, 4 gaps; `A_q_mon_mem` read).  The gate on `dcf40e2`, the walk switched off:
  `make.sh` `core-ok`; examples 45 / 45; corpus 36 / 36; the five kernels (13 / 13 / 13 / 14 / 14 s); **89 programs through the
  verified compiler, 0 refused**; `check_trust.py`: trust unchanged.  Next: what is assumed, §12.T: the five operations of step 65
  proved and removed.

**Step 73, `head0`, `tail0`, the high half of `mulc`, `diveucl_21` as ordinary functions, proved (§12.T, F66) — the design (2026-11-06).**  Step 65 made them operations of the machine with C bodies nobody proved, and that was wrong (F66): they are logic.  Rocq's axioms relate them to other operations, and that is enough to prove a definition equal.
- *The kit* (`KQRun.v`): `kq_mh`, the high half by digits of 21 bits; `kq_h0`, `kq_t0`, a binary search of six tests; `kq_d21`, shift and subtract, 63 rounds, its budget written `kq_nat 63` so that no conversion unrolls it.  Ordinary Rocq over `PrimInt63`.
- *`proved/KQPrim.v`*, from Rocq's own axioms and nothing else (`Print Assumptions` of each): `kq_mulc_def : mulc x y = (kq_mh x y, mul x y)`, `kq_h0_eq : head0 x = kq_h0 x`, `kq_t0_eq : tail0 x = kq_t0 x` at every argument (at 0 the axioms are silent and the kernel computes 63, by conversion); `kq_d21_eq : ltb a c = true -> diveucl_21 a b c = kq_d21 a b c`.
- *`diveucl_21` when `c <= a`*: Rocq's axioms say nothing there, and its kernel's answer on numbers cannot be stated for variables.  No fact is added (D29).  Three written numbers: the kernel's value.  `a` and `c` written with `a < c`: the kit's function.  A test around it that shows `a < c`: `ltb a c` true, `leb c a` false, through `negb`, `andb`, `orb`: the kit's function (`test_shows`, `d21_at`, a list of what is shown carried down `pm_sub`).  Otherwise the program is refused with that reason (§0.5's fourth): a pin and a control.
- *The form read*: step 64's route.  `pm_table` has the three; the equation is `own_step`'s, `prim_rw` with the three lemmas, `kq_guard` with `kq_d21_eq` where the test has been taken apart; a pair of `diveucl_21` is not taken apart before its test.
- *Removed*: `FHead0`, `FTail0`, `FMulHi`, `FDiv21Q`, `FDiv21R`, their five C bodies, `kq_mulhi`, `kq_div21q`, `kq_div21r`, `HW_PRIM`.  `proved/TRUSTED.txt` loses them, and the gate's `Print Assumptions` no longer names `head0`, `tail0`, `mulc`, `diveucl_21`.
- *The C*: the other programs lose the five declarations they never used; compared with them stripped, as step 65 did.  `mach_fix` is the one program that used them: its text now tests `1 <? b` around its `diveucl_21`.
- *Speed*: `head0` and `tail0` are six tests where they were one instruction; measured against the instruction.  A faster form may come later as a case of the generator's proof, never as a machine operation.
- *Cells*: 83, `A_t_*`: `head0`, `tail0` in every place of a number, `mulc` as a pair, `diveucl_21` under each test, recursion included; pins: nothing shown, the test the other way, another pair of numbers, a signed test.

**Step 73 done (2026-11-06): `head0`, `tail0`, the high half of `mulc`, `diveucl_21` as ordinary functions, proved.**  Built as designed:
- *`proved/KQPrim.v`*: `kq_mulc_def`, `kq_h0_eq`, `kq_t0_eq` at every argument, `kq_d21_eq`, `kq_d21_le` where `a < c`; `make.sh` with `ASSUME=1` prints what each rests on: Rocq's own integer axioms, nothing else.  A written budget of 63 made a conversion unroll 63 rounds with two branches each, and `reflexivity` never ended; `kq_nat 63` is opaque to a conversion, as every written budget is (F67).
- *The kit*: `kq_mh`, `kq_h0`, `kq_t0`, `kq_d21`, `kq_d21g`.  `kq_d21g` is a fixpoint, read as a function of the program's by its name.  What a program does not name is not in what Rocq quotes of it, so the reader carries the kit's bodies (`pm_kit`, `pm_add`).
- *The reader*: `test_shows`, `pm_norm`, `d21_at`; `pm_sub` carries the tests around a place and the `let`s it stands under.  A function given as an argument stays as it is: no equation reaches under its binder, and the first version read those cells and then failed the proof.
- *`KQRWf.v`*: `kq_guard`; a pair of `diveucl_21` is not taken apart before the test around it.
- *`kitc.py`*: a program's own files are compiled again when the kit is newer than they are.  `modules` gave no C after `KQRun.v` changed, at steps 65 and 73, both found by the comparison of the C: its file's `.vo` was older than the kit's (F68).
- *Removed*: `FHead0`, `FTail0`, `FMulHi`, `FDiv21Q`, `FDiv21R`, their five C bodies, `kq_mulhi`, `kq_div21q`, `kq_div21r`, `HW_PRIM`.  `proved/TRUSTED.txt` loses those ten lines and the short names `head0`, `tail0`, `mulc`, `diveucl_21`, and gains `Uint63Axioms.head0_spec`, `tail0_spec`, `mulc_spec`, `diveucl_21_spec`, Rocq's own, which `KQPrim.v` rests on: a change to the list, reported to the owner, what they asked for.
- *`mach_fix`*: its text tests `1 <? b` around its `diveucl_21`: proved, built, 5302306, as before.
- *Cells*: 83 more: 70 proved; `A_t_d_none`, `_lit_ge`, `_other`, `_signed`, `_else`, `_leb_then`, `_outside` by design, the reason and the control `A_t_d_ltb` in their own text; `A_t_d_helper_out`, `_trans`, `A_t_h0_given_lam`, `_given_bare`, `A_t_t0_given_lam`, `_given_bare` gaps.  `A_n_diveucl_21`, read since step 65, is by design now: it was read on an assumption.
- *What it costs*: a loop of 10^8 rounds on one pinned core, the fastest of three runs, the same answers (the control, a shift: 17.5 / 17.4 ms; step 72's files / these): `head0` 71.5 / 256.8 ms, `tail0` 36.7 / 259.5 ms, the high half of `mulc` 104.2 / 208.4 ms; `diveucl_21` over 10^6 rounds 89.9 / 87.6 ms.  So `head0` and `tail0` are six tests, about 2.4 ns each where the instruction was under 1 ns.  That is the price of no unproved C here; a faster form may come as a case of the generator's proof (§12.O), never as an operation of the machine.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 72's files / these): `HWP_kernel` 2.63 / 2.64 s, `HWP_own` 2.02 / 2.01, `HWP_irqnow` 1.75 / 1.75 — the same.
- The C: the 80 programs before the same but for the five declarations they never used, compared with those stripped; `mach_fix`
  tests first, its answer the same.  The construct table (on `9f620a8`): **2825 of 2915 through the verified compiler**, 34 by
  design, 55 gaps, 1 not Rocq (was 2756 of 2832: 70 of the 83 new cells read, 7 by design, 6 gaps; `A_n_diveucl_21` by design).
  The gate on `9f620a8`, the walk switched off: `make.sh` `core-ok`; examples 45 / 45; corpus 36 / 36; the five kernels (13 / 13 /
  13 / 14 / 13 s); **89 programs through the verified compiler, 0 refused**; `check_trust.py`: the tree and the gate's list as
  `proved/TRUSTED.txt` now says, which has lost ten lines of the machine and four short names and gained four of Rocq's own
  axioms.  Next: the signed quotient: `divs_min_neg1` taken away.

**Step 74, the signed quotient: `divs_min_neg1` taken away (§12.T) — the design (2026-11-06).**  `proved/KQTArith.v` had one axiom of ours about a primitive: the smallest number over -1 is the smallest number.  Rocq's `div_spec` excludes that case, and the generator's theorem needed its value.  It has the shape of `diveucl_21` when `c <= a`, and no fact is needed.
- *`kq_divs a b`* (`KQRun.v`): `if a` is the smallest number `and b` is -1 `then a else divs a b`.  It says what the case is by its definition.  `Bdivs` means it: the theorem for the instruction is proved from `div_spec` and that definition, and the C is what it was.
- *`/`*: `zdiv`'s text uses `kq_divs`, read as `Bdivs`.  A division by a variable needs no test and its C does not change.
- *`PrimInt63.divs`, `Sint63.div` written out*: equal to `kq_divs` where the text rules the case out: a written number, a test that shows the divisor is not -1 or the first number is not the smallest (`=?`, a sign test, through `negb`, `andb`, `orb`, `let`s): `test_shows`, `divs_at`, `kq_guard`, by the lemmas of `proved/KQPrim.v`, which rest on nothing but `eqb_correct` and the kernel's computation.  Otherwise refused, with that reason and what to write: a pin and a control.
- *Cells*: 45, `A_s_*`.

**Step 74 done (2026-11-06): the signed quotient: `divs_min_neg1` taken away.**  Built as designed:
- *`KQRun.v`*: `kq_divs`; `zdiv` uses it.
- *`proved/KQL.v`, `KQTArith.v`*: `Bdivs` means `kq_divs`; `divs_t` and `eqb_zero_divs` proved from `div_spec` and that definition.  `proved/TRUSTED.txt` loses the axiom: `proved/` holds no axiom of ours about Rocq's numbers any more.
- *`proved/KQPrim.v`*: `kq_divs_r`, `kq_divs_l` and their forms for `=?` the other way round and for the sign tests, each a test taken apart and the kernel's computation at the one number.
- *The reader*: `pm_eval`, `divs_at`; `test_shows` for `=?`, `<?`, `<=?` against 0.  `kq_divs` is read as `Bdivs`, and a written-out `divs` only through `pm_sub`.  `KQRWf.v`: `kq_guard`, `kq_part`.
- *The walk* (`KQMTrans.v`): `kq_divs` as `Bdivs`.  A written-out `PrimInt63.divs` is no longer translated by it: it is retired, behind `--walk`.
- *What is refused that was read*: nothing among the gate's programs.  `sdiv` is the only one that names `PrimInt63.divs`, each time with a written divisor (`7`, `0 - 3`).  `/` needs no test.
- *Cells*: 45 more: 36 proved; `A_s_none`, `_sint_none`, `_lit_min`, `_lit_m1`, `_else`, `_other`, `_test_unrelated` by design, the reason and the controls `A_s_test_pos`, `A_s_lit_b`, `A_s_slash_var` in their own text; `A_s_helper_out`, `A_s_given_lam` gaps.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 73's files / these): `HWP_kernel` 2.61 / 2.63 s, `HWP_own` 2.01 / 2.01, `HWP_irqnow` 1.74 / 1.75 — the same.
- The C: the 81 programs byte-identical.  The construct table (on `c79685b`): **2861 of 2960 through the verified compiler**, 41
  by design, 57 gaps, 1 not Rocq (was 2825 of 2915: 36 of the 45 new cells read, 7 by design, 2 gaps).  The gate on `c79685b`, the
  walk switched off: `make.sh` `core-ok`; examples 45 / 45; corpus 36 / 36; the five kernels (13 / 13 / 13 / 15 / 14 s); **89
  programs through the verified compiler, 0 refused**; `check_trust.py`: the tree and the gate's list as `proved/TRUSTED.txt` now
  says, which has lost `divs_min_neg1` twice.  Next: the bytes in bulk as ordinary functions.

**Step 75, the bytes in bulk as ordinary functions (§12.T) — the design (2026-11-06).**  `hw_copy`, `hw_fill`, `hw_cmp` are operations of the machine with C bodies (`memmove`, `memset`, `memcmp`), and their laws say what they leave alone, not what they do.  They have a definition other than the machine: loops of one byte at a time over `hw_load` and `hw_store`.
- *The kit* (`KQRun.v`): `hw_fill d b n s`; `hw_copy d src n h i s`, downwards when `d` is inside the source, each byte through cell `i` of block `h`, the way every load goes; `hw_cmp x y n h i s`, through cells `i` and `i + 1`, its answer in `i`.  `hw_copy` takes a cell it did not take before: a load puts what it reads in a cell, and no cell is the reader's to choose behind the program's back.
- *Read as the program's*: `hw_copy_up`, `hw_copy_down`, `hw_fill_go`, `hw_cmp_go`, fixpoints of the kit, by name (`kn_kit_fns`).
- *Removed*: `HCopy`, `HFill`, `HCmp`, their C bodies, their laws and the model's, three lines of `proved/TRUSTED.txt` each.  What a copy does now follows from the laws of a load and a store, and each byte is an event of the trace.
- *`kq_grow`*: stays assumed, with the loader and the driver.  It is the allocator under the memory's tables, which the proof does not reach (§12.H, §12.D); its class in the list says so.
- *The kernels*: `hw/kernel.body`, `kernel_p.body`, `smp.body`, `lock.body` name a free cell.  Booted under KVM: `bulk 0`, the second processor started from a trampoline copied by the new loop.
- *The C*: the other programs lose the three declarations they never used; compared with them stripped.
- *The acceptance*: `proved/examples/bulk_fix`: a fill, a copy each way, a compare each way, on the page that stands for a device; the answer worked out apart: 257985075201.
- *Cells*: 21, `A_h_*`.

**Step 75 done (2026-11-06): the bytes in bulk as ordinary functions.**  Built as designed:
- *`KQRun.v`*: `hw_copy_up`, `hw_copy_down`, `hw_copy`, `hw_fill_go`, `hw_fill`, `hw_cmp_go`, `hw_cmp`.  *`KQSpec.v`, `KQModel.v`*: three operations and their ten laws gone, each proved of the model before, none needed.  *`hw/kq_hw.h`*, *`KQL.v`*, *`KQLGen.v`*, *`KQMSem.v`*, *`KQMTrans.v`*, *`kitc.py`*: as designed.
- *The reader*: `kn_kit_fns`.  `KQR.v`, `KQRWf.v` unchanged.
- *`proved/TRUSTED.txt`*: loses the axioms, `hwop`s, C bodies and printed names of the three; `kq_grow`'s class is `env`, and §12.H names it.  No line of `remove` or `audit` is left: §12.T's condition.
- *The kernels*, built through the verified compiler and booted under KVM: `kernel` `bulk 0`, every check passed, answer 0; `smp` `cpus 2`, `atom 2000000`, answer 0; `lock` answer 0.  `lock` prints nothing: its two lines are in a `let` of a memory it does not use, dropped as a dead memory, the same on step 73's tree; a fault of its text, not of this step.  `hw/spec.sh`: the laws hold in a model, the proofs about kernel code rest on them alone.
- *The acceptance*: `proved/examples/bulk_fix`: proved, built, 257985075201.
- *Cells*: 21 more: 21 proved.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 74's files / these): `HWP_kernel` 2.88 / 3.14 s, it now reads the loops of its copy and its fill as functions of its own; `HWP_own` 2.20 / 2.12, `HWP_irqnow` 1.90 / 1.80, the machine slower in this run than in the last, both sides.
- The C: the 81 programs the same but for the three declarations and the three bodies they never used, compared with those lines
  put back (the chain's first comparison stripped the declarations only and stopped: all 81 then the same to the byte).  The
  construct table (on `4898663`): **2882 of 2981 through the verified compiler**, 41 by design, 57 gaps, 1 not Rocq (was 2861 of
  2960: the 21 new cells read).  The gate on `4898663`, the walk switched off: `make.sh` `core-ok`; examples 46 / 46; corpus 36 /
  36; the five kernels (13 / 13 / 16 / 14 / 15 s); **90 programs through the verified compiler, 0 refused**; `check_trust.py`: the
  tree and the gate's list as `proved/TRUSTED.txt` now says, which has lost the three operations, with no line of `remove` or
  `audit` left.  Next: a value and a proof given back: the rest of a function made by tactics.

**Step 76, a function giving back a value with a proof: `sig`, `sumbool` (§12.A) — the design (2026-11-07).**  `{y : int | P y}` and `{A} + {B}` are the value and its proof, and a proof is no value: what such a function computes is a number or a boolean.  Step 69's route takes it: a function of its own in its place, equal at every argument.
- *The row*: `f' args = proj1_sig (f args)`, `f' args = if f args then true else false` (`er_rows`, `er_tr`, `er_stmt`, marks `rp_sg`, `rp_sb`).  Its body is `f`'s with `exist v p` read as `v`, `left _` as `true`, `right _` as `false`, the recursive call as itself, by induction on the counter where there is one.
- *Its callers* (`er_sub`): `proj1_sig (f args)`, a match on it, a `let` of it, a test on it, when the proof is not named by what follows; what names the proof is not a value, so it is not computed: it stays a gap with its cell.
- *What tactics write*: `destruct t eqn:E` leaves `match t .. end eq_refl`, proofs of its branches naming `t`, so `t` cannot be taken apart in the goal (`kq_convoy`, `convoy_true`, `convoy_false`).  `decide equality` writes matches on the parameters: taken apart when a test is made of them.  `Scheme Equality` writes a test by a `let`, taken apart at once.  A library's test (`Uint63.eqs`) is its boolean test.
- *A proof as a field*: step 67's table read `{True} + {True}` as a data type holding two empty records, and the check failed: a proposition's proof is no value, whatever its shape (`Sort.is_prop`).
- *The acceptance*: `proved/examples/proof_fix`: a `sig` and a `sumbool` by recursion, one made by tactics, `decide equality`; the answer worked out apart: 1008112.
- *Cells*: 37, `A_e_*`.

**Step 76 done (2026-11-07): a function giving back a value with a proof.**  Built as designed:
- *The reader*: `rp_sg`, `rp_sb`, `er_row`, `er_sub`, `er_proj`, `er_tr`, `er_rows`, `er_stmt`, in `y_all`; `Sort.is_prop` in `rec_shape_go`.  `KQR.v` unchanged.
- *`KQRWf.v`*: `kq_unf`, `convoy_true`, `convoy_false`, `kq_convoy`; `own_step`, `own_step0`: `proj1_sig` reduced, a `sig` taken apart, a test taken apart where nothing is matched inside it, a variable taken apart where a test is made of a match on it, and last, after `reflexivity`, any variable a match is on.
- *`kitc.py`*: `kq_unf` set where a program has rows; the function itself unfolded in its row's proof; such a row's lemma rewrites only where its function is in the goal: `rewrite` compares up to unfolding even with the constant opaque, so a function that is one operation turned that operation back into itself, for ever (F69).
- *The acceptance*: `proved/examples/proof_fix`: proved, built, 1008112.
- *Cells*: 37 more: 34 proved; `A_e_sig_field`, `_sig_nat`, `_sig_param` gaps; `A_n_sig_result`, `A_q_enum_dec`, `A_q_sig_rec`, `A_q_sig_ret`, `A_q_sumbool_ret`, `A_l_dec_own`, gaps before, read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 75's files / these): `HWP_kernel` 3.00 / 2.96 s, `HWP_own` 2.00 / 2.02, `HWP_irqnow` 1.67 / 1.69 — the same.
- *Lost, found by comparing this table with the last one*: `A_l_convoy_b`, read since step 68, is refused: `kq_convoy` takes a convoy on a variable before the rule that took the variable apart, and leaves the variable's value in a hypothesis while the rest of the goal tests it again.  Not a wrong proof, a refused program.  Put right in step 78 (F71).
- The C: the 82 programs byte-identical.  The construct table (on `64ac544`): **2921 of 3018 through the verified compiler**, 41
  by design, 55 gaps, 1 not Rocq (was 2882 of 2981: 34 of the 37 new cells read, 3 gaps; 6 gaps read; 1 cell lost, above).  The
  gate on `64ac544`, the walk switched off: `make.sh` `core-ok`; examples 47 / 47; corpus 36 / 36; the five kernels (13 / 13 / 15
  / 14 / 14 s); **91 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust unchanged`.  Next: what a
  fourth probe of natural programs found.

**Step 77, what a fourth probe of natural programs found: a value and a memory written out (§3.1, §12.A) — the design (2026-11-07).**  A probe finds what the families do not, so another: 87 programs written as one writes them, drivers in an error monad over the memory, ring buffers, bitmaps, hash tables, schedulers, page-table walks, classes, sections, functors, proofs as arguments, with no thought of the reader.  60 are read as they stand.  The rest are classes, each with its cells:
- *A helper giving back a value that is not one number and a memory* (`R A := M (option A)`, `res * mem`), not recursive: written out (`vm_ty` in `um_inl`, `vm_unf` until none is left), then the choices floated: a `let` of a value chosen among constructors is that value where it is taken apart, `fst` and `snd` go into a choice, a match on a `let` has the `let` outside.
- *A program's own notation, a scope it opens*: what the reader found is read back as Rocq prints it, so `x |> f` printed an application otherwise and the reader's answer was lost: printed in a file with none of them in scope.
- *The same with recursion*: `A_p_err_rec`, `_err_rec_mem`, `_res_mem_rec`, `_rec_mem_loop`, step 78.  *Left*: a proof as a parameter, a counter given back, a class's instance given to a recursion, a dependent pair, a vector, a written number through a definition, the kit's input and output: gaps with their cells.  `A_p_cps_grow` and `A_p_list_built` are by design, each with its control.
- *The acceptance*: `proved/examples/drv_fix`: a driver in that monad; the answer worked out apart: 5024.
- *Cells*: 87, `A_p_*`.

**Step 77 done (2026-11-07): what a fourth probe found: a value and a memory written out.**  Built as designed:
- *The reader*: `vm_ty`, `vm_unf`, `y_dty`; `y_red`, `y_conb`, `y_tail` as designed.  `KQR.v`, `KQRWf.v` unchanged.  `y_nf`'s mark for no own call was the literal 1000000, added to at every test: this driver's read took 29 s and 2.4 GB, and 3 s and 885 MB with 9999 (F64 again).  Every program read in another form gains by it.
- *`kitc.py`*: the reader's results printed in `NAME_ro.v` when the program has a notation or opens a scope; otherwise as before.
- *The acceptance*: `proved/examples/drv_fix`: proved, built, 5024.
- *Cells*: 87 more: 67 proved; `A_p_cps_grow`, `_list_built` by design; 18 gaps, listed by their categories.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 76's files / these): `HWP_kernel` 2.95 / 2.96 s, `HWP_own` 2.02 / 2.03, `HWP_irqnow` 1.69 / 1.71 — the same.
- *Found by the gate*: the first version floated `fst` and `snd` into a choice and then asked the kernel for a conversion, which is none: `monad_fix`, read before, was refused.  `y_fl`, `y_hasp`: such a body takes the equation route, and `KQRWf.own_step0p` is its proof's last alternative.  The gate printed `refused: 1` and the chain went on (F72).
- The C: 83 of the 84 programs byte-identical; `proc_fix` differs in `solve`, not in a loop, by one conditional move more on a
  boolean of a chosen pair.  The construct table (on `3d8a0a5`): **2988 of 3105 through the verified compiler**, 43 by design, 73
  gaps, 1 not Rocq (was 2921 of 3018: 67 of the 87 new cells read, 2 by design, 18 gaps; no cell lost).  The gate on `3d8a0a5`,
  the walk switched off: `make.sh` `core-ok`; examples 48 / 48; corpus 36 / 36; the five kernels (16 / 16 / 19 / 16 / 17 s); **92
  programs through the verified compiler, 0 refused**; `check_trust.py`: `trust unchanged`.  Next: a value of several numbers and
  a memory given back by a recursion.

**Step 78, a value of several numbers and a memory given back by a recursion (§3.5, §12.A) — the design (2026-11-07).**  `lp : nat -> int -> mem -> option int * mem`, an error monad over the memory, a result record and the memory: the reader takes a number and a memory, the record of step 13 with no memory written, nothing else.
- *The form*: a function of its own in the function's place (step 69's route), giving back the value's first number and the memory with the value's other numbers in the cells of the slot block, `f' args = match f args with (v, t) => (x0 v, upd 63 0 (x1 v) (upd 63 1 (x2 v) t)) end`.  The numbers of a value: its tag if it has several constructors, then the fields of the one it is, each laid out the same way down to numbers.
- *A call*: the cells the value goes through are saved, the numbers read after it, the cells written back, cell 0 first, as a record's caller does (D16): `let o_j := rd 63 j t in match f' .. t with (x0, t') => let x_j := rd 63 (j - 1) t' in let t1 := (written back) in K`, the value built again from its numbers where it is used.
- *What that rests on*: writing the cells back gives the memory back only if the function leaves them alone.  A lemma per function: `rd 63 j (snd (f args)) = rd 63 j s`, by induction from the memory's laws, first of every recursive function of the program that gives a memory (`KQRWf.fr_*`, one for each operation).  `upd_upd` and `upd_rd_id` do the rest, cell 0 first: D27's commuting law is not needed.  No new axiom: the laws are `real_laws`.
- *Room*: a cell holds what was written only where the block has room, so the equations hold under `W <= kq_len 63 + 1`, `W` the program's largest value, which `KQR.slot_room` gives once the value's type is in the table: a made function names it.  `KQR.callee_ok_eqr`: the theorem takes `slot_room` as its premise, so an equation may too.
- *What it may write*: a block whose number is written, or a definition of one, and is not 63; what writes no wide cell; a helper's body read with its arguments in place.  A write to the slot block, a block number not written, what has no law (`kq_in`, `kq_out`, `hw_call`, `hw_run`, `hw_code_sync`) leave the function unread, its reasons said: gaps with their cells.
- *The places*: the call last, followed by more, twice, a tail call of another such function (taken apart and given back), a choice of pairs taken apart (in each branch), a `let` of the pair; the counter at any place, the memory at any place; each caller's form.
- *The C*: a program with no such function: byte-identical.
- *The acceptance*: `proved/examples/vals_fix`: a value of three numbers with several constructors, a record of three after a call that is not the last step, the slot block's cells written by the caller read back after both; the answer worked out apart: 1785.
- *Cells*: 78, `A_v_*`.

**Step 78, a value of several numbers and a memory given back by a recursion — the result (2026-11-07).**
- *`KQR.v`*: `callee_ok_eqr`.  *`KQRWf.v`*: `fr_upd`, `fr_upd32`, `fr_upd8`, `fr_upd16`, `fr_grow`, `fr_load`, `fr_aload`, `fr_store`, `fr_store64`, `fr_astore`, `fr_astore64`, `fr_fence`, `fr_atomic`, `fr_atomic64`, `fr_cas`, `fr_cas64`, `fr_copy`, `fr_fill`, `fr_cmp`; `slot_eq`, `slot_ne`, `upd_same`; the tactic `kq_vm0`, switched on by a program with such a function: a call's pair taken apart as `fst c` and `snd c` (`surjective_pairing`), so that the same call is the same two parts wherever it stands and what is known of `snd c` applies; `fr_step`, the frame lemma's induction.
- *The reader*: `vm_rows`, `vm_tr`, `vm_sub`, `vm_call`, `vm_leaf`, `vm_flat`, `vm_mk`, `vm_lets`, `vm_fr_ok`; a row's mark 994; a row and a frame lemma carry the counter's place in their names (`__v<n>`, `__f<n>`), read by `kitc.py` for `fix IH (n + 1)`.  A made function `__t` names the value's type and the types its fields hold, so that they are in the table.
- *`kitc.py`*: in a program with such a function, a room lemma from `slot_room` at the table's largest entry, the frame lemmas first, the rows' and the callers' equations under it; a program with none: the file as before.
- *Found by the cells*: the table was built in three places, the reader's two without the made functions: a tree numbering its records by one table was checked against another, and the kernel refused it (F70).
- *The acceptance*: `proved/examples/vals_fix`: proved, built, 1785.
- *Cells*: 78 more: 62 proved; `A_v_call_in_helper_two`, `A_v_o_two_mems` by design, the controls `A_v_call_in_helper`, `A_v_mem_first` in their own text; gaps by their categories: the same call named twice; a block number not written, the slot block; the kit's output; a local fix, a Section's fixpoint; a mutual block; a polymorphic recursion; a Program Fixpoint; the memory before the value; a memory as a field.  Eight gaps read: `A_p_err_rec`, `_err_rec_mem`, `_res_mem_rec`, `_rec_mem_loop`, `A_m_e_enum_ret`, `_opt_ret`, `_pair_ret`, `A_q_mem_rec_triple`.  `A_q_mem_record` and `A_q_st_mem_iter` hold a memory in a value given as a parameter: moved to that category.
- *`A_l_convoy_b`*, lost at step 76, read again: `kq_convoy` puts a variable's value in the goal too (F71).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 77's files / these): `HWP_kernel` 3.02 / 3.02 s, `HWP_own` 2.06 / 2.10, `HWP_irqnow` 1.73 / 1.70 — the same.
- The C: the 84 programs byte-identical.  The construct table (on `89fd65c`): **3059 of 3183 through the verified compiler**, 45
  by design, 78 gaps, 1 not Rocq (was 2988 of 3105: 62 of the 78 new cells read, 2 by design, 14 gaps; 9 gaps read, `A_l_convoy_b`
  among them; no cell lost).  The gate on `89fd65c`, the walk switched off: `make.sh` `core-ok`; examples 49 / 49; corpus 36 / 36;
  the five kernels (16 / 16 / 19 / 16 / 17 s); **93 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust
  unchanged`.  Next: what is left of a value and a memory given back: a local fix, a section, what a recursion holds.

**Step 79, a value and a memory from the other forms of recursion, a block's number given, the same call named twice (§3.5, §12.A) — the design (2026-11-07).**  Step 78's form for what its own cells left: completeness is strict.
- *A fixpoint under parameters* (a Section's variable, `fun f => fix go ..`): one fixpoint of them all, its own call given them (`vm_norm`), the row and the frame lemma as step 78's, its counter's place counted after them.  Such a function keeps its name where it is called: it is not written out as a helper is.
- *A local fix*: `let fix go .. in go ..`, `(fix go ..) ..`, in a function or a helper written out, naming what is around it: its row is of the fix itself, what it names abstracted (`lfix_key`, `vm_lfs`), one row per fix, its statements stated of the fix, so that what is known of it applies where the text has it.  A `let` of a fix is the fix where it is used; a match on a `let` has the `let` outside; a match on a choice of such pairs is in each branch (`vm_zfix`).
- *A block's number as a parameter*: the frame lemma and the row's equation take that it is not 63 (`eqb h 63 = false`, its place among the slots a mark, `vm_fr` collecting it), the function's own call must hand it on, and a call must give a written number, a definition of one, or, in a row, a parameter of its own that is one too.  A helper with such a parameter, not recursive, is written out where it is called (`vm_ginl`).  Where nothing shows it is not 63: a gap with its cell; the program is refused with its reason.
- *The same call named twice*: `fst (f x)` and `snd (f x)` from one memory are one call: taken apart once where the first is worked out, deeper if only a branch names it (`vm_cand`, `vm_occ`, `vm_repl`); in a function's own text and in a row's.  `fst (f x)` and `snd (f y)` from one memory are two versions: by design, a pin and its control.
- *The proof*: rewriting takes a side goal, closed by what is written or what the lemma takes (`KQRWf.vm_side`).  A call of a fix is taken apart as a call of a function is; a variable matched is told apart before a pair with a match in it.  A last alternative for the caller's equation unfolds the program's functions too, for a function given that is read as a local fix.
- *The C*: a program with no such function: byte-identical.
- *Left*: a mutual block, a polymorphic recursion, a Program Fixpoint, the memory before the value in the pair, a memory in a record: gaps with their cells, next.
- *The acceptance*: `proved/examples/sect_fix`: a Section's variable with a block given, a local fix, the same call named for its value and its memory; the answer worked out apart: 93.
- *Cells*: 41, `A_w_*`.

**Step 79, a value and a memory from the other forms of recursion — the result (2026-11-07).**
- *The reader*: `vm_norm`, `vm_row`, `vm_lfs`, `vm_lf_rows`, `vm_zfix`, `vm_fr` (what a function writes, the block numbers it takes), `vm_gs`, `vm_keep`, `vm_blk`, `vm_pres`, `rp_gds`, `vm_ginl`, `vm_isr`, `vm_cand`, `vm_occ`, `vm_repl`; `vm_lets` in a row's text too; `vm_sub` takes whether it reads a row; `um_inl` and `um_red` leave a fixpoint under parameters by its name; `rp_topo` sees through a call of a row.  *`KQRWf.v`*: `vm_side`, `vm_head`.  *`kitc.py`*: a local fix's lemmas name no constant; a last alternative for the callers' equations.  `KQR.v` unchanged.
- *The acceptance*: `proved/examples/sect_fix`: proved, built, 93.
- *Cells*: 41 more: 33 proved; `A_w_s_mem`, `A_w_l_cap_mem`, `A_w_t_other_args` by design, each with its controls in its own text; gaps `A_w_b_call_63`, `_b_call_tested`, `_b_call_var`, `_b_moved`, `A_w_l_writes_mem`.  Six gaps read: `A_v_call_both`, `A_v_o_given_top`, `_o_local_fix`, `_o_local_fix_cap`, `_o_section`, `A_v_w_block_param`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 78's files / these): `HWP_kernel` 3.11 / 3.08 s, `HWP_own` 2.12 / 2.10, `HWP_irqnow` 1.81 / 1.77 — the same.
- The C: the 85 programs byte-identical.  The construct table (on `4000208`): **3098 of 3224 through the verified compiler**, 48
  by design, 77 gaps, 1 not Rocq (was 3059 of 3183: 33 of the 41 new cells read, 3 by design, 5 gaps; 6 gaps read; no cell lost).
  The gate on `4000208`, the walk switched off: `make.sh` `core-ok`; examples 50 / 50; corpus 36 / 36; the five kernels (16 / 16 /
  19 / 16 / 16 s); **94 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust unchanged`.  Next: a memory
  in a record or a pair, at any place.

**Step 80, a memory in a record or a pair, at any place, as a result and as a parameter (§3.5, §12.A) — the design (2026-11-07).**  `Record st := { cnt : int; mm : mem }`, `step (x : st) : st`, `run (k : nat) (x : st) : st`, `mem * int`: a state written the way one writes it.
- *The form*: a function of its own in the function's place (step 69's route), its parameters the fields of what holds the memory, its result the pair of steps 13 and 78, the value's numbers nested, the memory second.  `f' k c t = match f k (mkst c t) with mkst c' t' => (c', t') end`, by induction.  Then that function is read as any function is: a number and a memory, or through the slot block (step 78), a boolean and nothing there too.
- *The text*: the parameter is its constructor on the fields, so a match, a field, a helper's text reduce (`vm_pj`, `vm_open`: the numbers first, the memory last); a helper holding such a value is written out; a let of such a value is its fields; a let of a call is taken apart; the same call named twice, through `fst`, `snd` or a field, in a function's own text or another's, is one call (`vm_cand`, `vm_occ`, `vm_repl`, now on the call itself).
- *The call*: a value holding a memory given as a parameter is written as its constructor where it is given.  A variable given to a call: the function it is in holds it too, or a helper written out.  A call giving one: a gap with its cell.
- *The proof*: the row's lemma on the pair goes last (`KQRWf.kq_rw2`), once what is known of the pair has been used, the function it is of taken apart then.
- *An environment with no pair*: a program that names none has no `prod` in what is quoted; the reader adds it, and `unit`.
- *The C*: a program with no such function: byte-identical.
- *Left*: a memory deeper in a value, a call as such a parameter, a local fix giving a record: gaps with their cells, with a mutual block, a polymorphic recursion, a Program Fixpoint.
- *The acceptance*: `proved/examples/stat_fix`: a state record through a step function and a recursion, the memory before the number in a pair; the answer worked out apart: 228.
- *Cells*: 48, `A_x_*`.

**Step 80, a memory in a record or a pair — the result (2026-11-07).**
- *The reader*: `vm_sh`, `vm_needs`, `vm_qs`, `vm_qdef`, `vm_qcalls`, `vm_qtail`, `vm_qrows`, `vm_qstmt`, `vm_qsub`, `vm_pj`, `vm_open`, `vm_fs`, `vm_yr`, a row's mark 993; `vm_lets` of any such type, the function's own call too; `um_inl` writes out a helper holding such a value, not a number and a memory, which is read as it was (the first version wrote that out too, and the chain stopped on `monad_fix`'s C); on a function read as a pair the value may be a boolean or nothing (`vm_ty_q`); `vm_with_prod`, `vm_with_unit`.  *`KQRWf.v`*: `kq_rw2`; a match on a value not told apart by a test is taken apart last.  *`kitc.py`*: such a row's lemma goes to `kq_rw2`; what it is of stays folded.  `KQR.v` unchanged.
- *The acceptance*: `proved/examples/stat_fix`: proved, built, 228.
- *Cells*: 48 more: 44 proved; `A_x_p_two_states` by design, its control in its own text; gaps `A_x_f_three`, `A_x_p_var_rec`, `A_x_r_local`.  Four gaps read: `A_q_mem_record`, `A_v_o_record_mem`, `_o_value_mem_param`, `_o_ret_in_pair_rev`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 79's files / these): `HWP_kernel` 3.16 / 3.12 s, `HWP_own` 2.12 / 2.14, `HWP_irqnow` 1.80 / 1.82 — the same.
- The C: the 86 programs byte-identical.  The construct table (on `d9b85b2`): **3146 of 3272 through the verified compiler**, 49
  by design, 76 gaps, 1 not Rocq (was 3098 of 3224: 44 of the 48 new cells read, 1 by design, 3 gaps; 4 gaps read; no cell lost).
  The gate on `d9b85b2`, the walk switched off: `make.sh` `core-ok`; examples 51 / 51; corpus 36 / 36; the five kernels (16 / 17 /
  19 / 16 / 16 s); **95 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust unchanged`.  Next: a proof
  as a parameter, a value with its proof as a parameter.

**Step 81, a proof as a parameter, a value with its proof as a parameter (§3.5, §12.A) — the design (2026-11-07).**  A read that takes a proof its index is in range, a recursion taking a proof of its counter's bound, `{y : int | P y}`, a record holding a proof: ordinary dependent Rocq.  A proof computes nothing.
- *A proof as a parameter*: a function of its own in the function's place without it (step 69's row, its slots), at every argument and every proof equal to it.  A parameter whose type has sort Prop, through definitions and arrows (`prf_ty`), that nothing reads but the function's own call at that place and what is in the place of a function it calls.  A convoy giving it (`match k as k0 return k0 <= 100 -> int with .. end H`): the proof in each branch first (`prf_push`).
- *A value with its proof as a parameter*: `sig`, a record holding proofs: the fields that are not proofs as parameters, each a projection of what is given, `g x = g' (proj1_sig x)` at every `x`, so that what is given need not be written as its constructor; a helper giving such a value is written out.  A field of what is made here reduces (`sp_red`, `sp_pj`); a proof left in the text leaves the function unread.
- *What stands in those places is read as any function*: a value and a memory through step 78, under step 79's and step 80's forms.
- *A proof taken apart in what is computed* (`match H with eq_refl => ..` where `H` is a variable): the kernel's reduction stops on it: a gap with its cell.
- *The C*: a program with no such function: byte-identical.
- *The acceptance*: `proved/examples/prfp_fix`: all of these together; the answer worked out apart: 42.
- *Cells*: 40, `A_y_*`.

**Step 81, a proof as a parameter — the result (2026-11-07).**
- *The reader*: `prf_ty`, `prf_push`, `prf_def`, marks 992 and 991 among a row's slots; `sp_sh`, `sp_get`, `sp_pj`, `sp_red`, `sp_args`, `sp_tys`, `sp_own`, `sp_def`, `sp_rows`, `sp_stmt`, `sp_sub`; `rp_all` reads a function's body on the rows before it; `y_all` makes those in such a place functions as it does step 80's.  `um_inl` writes out a helper giving such a value.  `KQR.v`, `KQRWf.v` unchanged.  *`kitc.py`*: a row `__g<n>` has its counter's place in its name.
- *The acceptance*: `proved/examples/prfp_fix`: proved, built, 42.
- *Cells*: 40 more: 39 proved; `A_y_p_section_unused` a gap.  Four gaps read: `A_p_proof_arg`, `A_p_proof_arg_rec`, `A_p_sig_arg`, `A_e_sig_param`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 80's files / these): `HWP_kernel` 2.97 / 2.99 s, `HWP_own` 2.04 / 2.02, `HWP_irqnow` 1.72 / 1.68 — the same.
- *Lost, found by comparing this table with the last one*: 12 cells read since step 76 (`A_e_sig_arg`, `_sig_bool`, `_sig_calls`, `_sig_def`, `_sig_match`, `_sig_let`, `_sig_mem`, `_sig_spec_if`, `_sig_tactic`, `_sig_two`, `A_p_program_def`, `A_q_sig_ret`) were refused by the first version: a helper giving back a `sig` was written out, away from its own route.  Not a wrong proof, refused programs; put right in the commit after it, the table run again.
- The C: the 87 programs byte-identical.  The construct table (on `6ce4511`): **3189 of 3312 through the verified compiler**, 49
  by design, 73 gaps, 1 not Rocq (was 3146 of 3272: 39 of the 40 new cells read, 1 gap; 4 gaps read; 12 cells lost by the first
  version, read again).  The gate on `6ce4511`, the walk switched off: `make.sh` `core-ok`; examples 52 / 52; corpus 36 / 36; the
  five kernels (16 / 17 / 20 / 16 / 17 s); **96 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust
  unchanged`.  Next: a function giving back a counter, made a number where it is used.

**Step 82, a function giving back a counter, made a number where it is used (§3.5, §12.A) — the design (2026-11-07).**  `cnt k i t : nat`, how many cells are not 0: natural, and `nat` is unary only in the logic.
- *The form*: a function of its own in the function's place giving back the number, `F args = of_Z (Z.of_nat (f args))` at every argument, whatever the size: the machine's numbers are modulo `wB`, and `S`, `+`, `*` are homomorphic (`KQRWf.nr_S`, `nr_add`, `nr_mul`, from Rocq's own lemmas on `of_Z`).  No bound is needed, and none is assumed.
- *Read*: `O`, `S`, a counter as a number (`SOfC`), its own call, a function of this kind, `Nat.add`, `Nat.mul`, a choice, a match, a let of a counter (a number then).  A parameter only handed on and given back (an accumulator) is a number too: `F k i (of_Z (Z.of_nat acc)) = of_Z (Z.of_nat (f k i acc))`.  A helper giving a counter is read in place.
- *Where it applies*: a counter made a number at once, `Uint63.of_nat (f args)`.  That is where the number is the same.  Used as a counter, `Nat.leb (f args) 3`, `match f args with`, given to a recursion: the comparison is of the counter, and its number is the counter only below `wB`: a bound is needed: gaps with their cells, next.
- *The proof*: the row's lemma from the text's side (`rewrite <-`): `of_Z (Z.of_nat (f ..))` to the row's call, whatever the accumulator's form; `kq_nr` only on `S`, `Nat.add`, `Nat.mul` as written, since a function of the shape of `Nat.add` is `Nat.add` up to conversion.
- *The C*: a program with no such function: byte-identical.
- *Left*: a counter in a pair, in an `option`, with a memory; a local fix; a recursion two steps down: gaps with their cells.
- *The acceptance*: `proved/examples/cret_fix`: a count by recursion after the call, a count as a parameter, a helper over both; the answer worked out apart: 5548.
- *Cells*: 44, `A_z_*`.

**Step 82, a function giving back a counter, made a number — the result (2026-11-07).**
- *The reader*: `nr_only`, `nr_tail_ok`, `nr_tr`, `nr_rows`, `nr_stmt`, `nr_sub`, a row's mark 990, the accumulators' places among its slots; `nr_sub` before the library is unfolded, since `Uint63.of_nat` is a notation for `of_Z (Z.of_nat ..)`.  The reason "two memories as parameters" no longer given for a counter given back.  *`KQRWf.v`*: `nr_O`, `nr_S`, `nr_add`, `nr_mul`, `kq_nr`, `nr_step`.  *`kitc.py`*: `__k<n>` rows; `Uint63.of_Z`, `Z.of_nat`, `Nat.add`, `Nat.mul` stay folded in such a program's proofs.  `KQR.v` unchanged.
- *The acceptance*: `proved/examples/cret_fix`: proved, built, 5548.
- *Cells*: 44 more: 34 proved; gaps by their categories: a counter in a value, a local fix, a recursion two steps down; a counter used as a counter (its bound).  Four gaps read: `A_q_nat_ret_acc`, `A_q_nat_ret_len`, `A_p_nat_len`, `A_p_nat_add`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 81's files / these): `HWP_kernel` 3.00 / 3.06 s, `HWP_own` 2.04 / 2.05, `HWP_irqnow` 1.72 / 1.71 — the same.
- *One cell read and refused by the check*: `A_q_nat_field`, `Uint63.of_nat` of a counter that is a field of a record: the reader gives a form the kernel does not find equal to the function, and the check refuses it, so nothing false is accepted, and the cell stays a gap in its category; a cell should be read or refused by the reader, not by the check, and this goes with the counters in values.
- The C: the 88 programs byte-identical.  The construct table (on `b017845`): **3227 of 3356 through the verified compiler**, 49
  by design, 79 gaps, 1 not Rocq (was 3189 of 3312: 34 of the 44 new cells read, 10 gaps; 4 gaps read; no cell lost).  The gate on
  `b017845`, the walk switched off: `make.sh` `core-ok`; examples 53 / 53; corpus 36 / 36; the five kernels (17 / 17 / 19 / 16 /
  17 s); **97 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust unchanged`.  Next: a counter
  expression as a counter.

**Step 83, a counter a function gives back, used as a counter (§3.5, §12.A) — the design (2026-11-07).**  Step 82 made `cnt k i t : nat` a number where it is made one.  `Nat.leb (cnt n a s) 3`, `match cnt n a s with`, `ff (cnt n a s) b`: the comparison is of the counter, and its number is the counter only below `wB`, so a bound is needed, proved, not assumed.
- *The bound*: of each function giving back a counter, `f args <= w0 * c0 + .. + d`, linear in its counters, read off its text, proved by induction from the text alone (`__b<n>_<rarg>__bq__wy`, `KQRWf.nb_step`).  `w` for its recursion's counter: the most a round adds to the result and to the counters it hands on; 1 for the others, `d` the most an end gives.  Another such function's bound is put in at its arguments.
- *Where no such bound exists*: a round adding a parameter (`c + tw m c`, `tw m + th m`) reaches `n^2`, an own call twice in a round or a doubling (`tw m + tw m`, `2 * tw m`, `tw m (acc + acc)`) reaches `2^n`: past a machine number from a written budget, so what the text means needs a bignum there (§0.5, second reason): by design, each with a control beside it, the same function with a linear bound.
- *The form*: the largest counter expression around such a call, `S`, `+`, `*` of a written number, as one number: `ff (S (cnt n a s)) b` is `ff (Z.to_nat (Uint63.to_Z (F n a s + 1))) b`, what a C programmer writes.  Equal where the bound keeps it below `wB`.  Nothing new in `S`: `CToNatU`, read since step 70.
- *The caller's equation*: under its own counters' bound, `KQR.callee_ok_eqb`, since `callee_ok` takes that bound as its premise anyway; `KQRWf.nc_E`, `nc_fold`, `nc_step`: back to the counter in one step, each side by `lia` from the bounds of the calls in the goal or kept by a test.  A counter at most twice its counters fits below the index's bound; up to seven times, below the smallest own bound (`__nco__wy`, 2^60 and a little); more does not fit below `wB` from `kq_nat`'s 2^60: a gap with its cell.
- *What is proved*: nothing assumed beyond the list: the bound and the equation are theorems of each program.  The C: a program with no such call: byte-identical.
- *Left, with cells*: a counter's `CToNatU` is at most `2^63 - 1` to `wf`, so a callee that grows its counter is not called with it (`A_zb_o_callee_grows`); a function giving back a counter that uses another's as a counter (`A_zb_o_counter_row_uses`); a function with weights (`A_zb_o_weights`); a local fix; a recursion two steps down, as at step 82; a test in `Z` on it (`A_z_u_zofnat`).
- *The acceptance*: `proved/examples/cuse_fix`: a budget, a test, a match, an operand, in a recursion; the answer worked out apart: 419061.
- *Cells*: 65, `A_zb_*`.

**Step 83, a counter a function gives back, used as a counter — the result (2026-11-07).**  Built as designed:
- *The reader*: `nb_go`, `nb_of`, `nb_all`, `nb_stmt` (the bound, read off the text); `nc_has`, `nc_c`, `nc_tr`, `nc_sub`, `nc_any`, `nc_s` (the counter as a number; a let of one held as the number, once); marks `__nc__wy`, `__nco__wy` (the smallest own bound), `__nch__wy` (a helper, unfolded).  *`KQR.v`*: `eqCb`, `callee_ok_eqb`, nothing else.  *`KQRWf.v`*: `nc_E`, `nc_fold`, `nc_step`, `nc_match`, `nb_step`; `kq_nc` before `kq_rw` in the two steps that read a text, `vm_side` with `lia` where the program has such a counter.  *`kitc.py`*: the bounds before the equations, each after what it calls; the equations of what uses them under the counters' bound.
- *The acceptance*: `proved/examples/cuse_fix`: proved, built, 419061.
- *Cells*: 70 more: 60 proved; by design, each with a control: `A_zb_s_power`, `_s_power_mul`, `_a_acc_doubles` (a doubling), `A_zb_s_add_var`, `_s_quadratic` (a round adding a parameter); gaps by their categories: `A_zb_o_callee_grows`, `_o_counter_row_uses`, `_o_weights`, `_o_local`, `_s_deep`.  Five gaps read: `A_z_u_counter_use`, `_eqb`, `_leb`, `_match`, `A_p_nat_len_cmp`.  `A_l_nat_ret_grow`, by design since step 68 ("an unbounded number"), is read: its counter grows by one a round, its bound is linear, and the classification was wrong: a design cell needs the cause shown, here a doubling.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62; step 82's files / these): `HWP_kernel` 3.27 / 3.27 s, `HWP_own` 2.24 / 2.25, `HWP_irqnow` 1.88 / 1.89 — the same.  The first version cost 6%: a look-up of a mark per function, the whole environment each time (F64 again); the marks are looked for once now.
- *Better than the design said*: `A_l_nat_ret_same` read too, a gap of step 82.
- *The table's image*: from this table on, the image the gate runs in is one flattened layer: every file's checksum the same as before, less the opam build and source folders, which nothing reads when it runs.
- The C: the 89 programs byte-identical.  The construct table (on `95d192b`): **3294 of 3426 through the verified compiler**, 53
  by design, 78 gaps, 1 not Rocq (was 3227 of 3356: 60 of the 70 new cells read, 5 by design, 5 gaps; 6 gaps read, and
  `A_l_nat_ret_grow`, wrongly by design; no cell lost).  The gate on `95d192b`, the walk switched off: `make.sh` `core-ok`;
  examples 54 / 54; corpus 36 / 36; the five kernels (17 / 17 / 19 / 16 / 17 s); **98 programs through the verified compiler, 0
  refused**; `check_trust.py`: `trust unchanged`.  Next: a class's instance read as a type, a record of functions given to a
  recursive function.

**Step 84, a class or a record of functions given to a recursive function (§3.5, §12.A, D22) — the design (2026-11-07).**  `Fixpoint rep {T} `{Monoid T} (k : nat) (x : T)`, `Fixpoint use (k : nat) (o : ops) (x : int)`: ordinary Rocq, and the instance or the record is known where it is called.  A function value not known from the text needs a runtime; these are known.  Step 69's route takes them: a function of its own in the function's place, equal at every argument.
- *A class after the types a fixpoint starts with* (`lead_inst`, `cl_ty`): what it is given, closed, is read as a type is: a row per type and instance, `rep'` for `rep int add_m`.  A class counts if its record holds a function or it is a record of the program's over a type.
- *A method at a closed instance* (`cl_red`, `cl_whnf`, `cl_proj`, `cl_beta`): what the instance says, written out where the row or the text has it: the instance's definition unfolded, an instance built from others (`d_pair d_int d_int`) included, the field taken, what it is given put in, a call by a `let`, so that a method using an argument twice is one call of it in the C.
- *A record of functions among a recursive function's parameters* (`sp_sh`, step 81's route for a value with its proof): its fields as parameters, functions given as functions are at step 10, so a field that names the caller's variables is a capture.  A helper given such a record is written out (`sp_uh`); a projection takes what follows the record (`sp_pj`).
- *A record over a type in the table*: its constructor takes the type (`kitc.py`): `@Build_Dflt int`.
- *What is proved*: each row equal to the function at every argument, by the kernel; `denote s = f'`.  Nothing assumed, nothing changed in `KQR.v`.  *The C*: a program with no such function: byte-identical.
- *By design*: a record of functions built anew at each round from the data (`A_zc_r_gives_record`): §0.5's first refusal; its control `A_zc_r_capture`.
- *Left, with cells*: a mutual block (`A_zc_c_mutual`, `A_zc_r_mutual`), a type after the counter (`A_zc_c_counter_late`), a record of functions inside a record (`A_zc_r_nested`).
- *The acceptance*: `proved/examples/cls_fix`: two instances of a class at a number and at a record, a class giving a boolean, a record of functions that reads and writes the memory, naming the caller's variable; the answer worked out apart: 4109666.
- *Cells*: 38, `A_zc_*`.

**Step 84, a class or a record of functions given to a recursive function — the result (2026-11-07).**  Built as designed:
- *The reader*: `cl_ty`, `lead_cl`, `lead_inst` (a closed instance read as a type is); `cl_whnf`, `cl_proj`, `cl_beta`, `cl_red`, `cl_all`, `cl_s` (a method at a closed instance written out, in the rows and the text); `sp_sh`, `sp_uh`, `sp_pj` (a record of functions among a recursive function's parameters as its fields).  `KQR.v`, `KQRWf.v` unchanged.  *`kitc.py`*: a record over a type: its constructor takes the type.
- *The acceptance*: `proved/examples/cls_fix`: proved, built, 4109666.
- *Cells*: 38 more: 33 proved; `A_zc_r_gives_record` by design, with its control; gaps `A_zc_c_mutual`, `_r_mutual`, `_c_counter_late`, `_r_nested`.  Four gaps read: `A_p_class_rec`, `A_p_class_two`, `A_q_cl_fold`, `A_q_rec_vtable_rec`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 83's files / these): `HWP_kernel` 2.98 / 2.96 s, `HWP_own` 2.04 / 2.05, `HWP_irqnow` 1.72 / 1.71 — the same.
- *Found by comparing the tables*: the first version bound a function given to a class's method by a `let` of a type that is not plainly a function, and `A_p_class_monad` stopped being read.  `cl_beta` puts a function in, as it does a variable; nothing but text is copied.  The gate and the table were run again.
- The C: the 90 programs byte-identical, and `cls_fix`, new.  The construct table (on `413a349`): **3331 of 3464 through the
  verified compiler**, 54 by design, 78 gaps, 1 not Rocq (was 3294 of 3426: 33 of the 38 new cells read, 1 by design, 4 gaps; 4
  gaps read; a cell lost by the first version, read again).  The gate on `413a349`, the walk switched off: `make.sh` `core-ok`;
  examples 55 / 55; corpus 36 / 36; the five kernels (15 / 15 / 18 / 14 / 15 s); **99 programs through the verified compiler, 0
  refused**; `check_trust.py`: `trust unchanged`.  Next: what a fifth probe found: a memory inside an option, a helper's choice of
  a value and a memory.

**Step 85, what a fifth probe found: a memory inside an option, a helper's choice of a value and a memory (§3.1, §12.A) — the design (2026-11-07).**  34 larger programs written as one writes them, several features at once: a hash table, an allocator, a tokenizer, a stack machine, a heap, a BFS, a big number, a CRC, a matrix power, a class of numbers, dates, a quicksort, a driver's ring, a scheduler, a tree in an array, UTF-8, base64, functors, closures, an error monad.  26 are read as they stand.  What was left are classes, each with its cells:
- *A match on a helper's choice of a value and a memory* (`match alloc s with (Some p, t) => ..`, `let (y, u) := step x t in ..`, `step` a chain of tests over a record and a memory): the helper written out (step 77), then the match in each arm where it reduces (`cf_on`, `cf_fl`, `cf_red`); not where that would repeat a long text over many ends: a gap with its cell.  The same in what stands in a recursive function's place.
- *A memory inside an option from a helper* (`push : .. -> option mem`, `pop : .. -> option (int * mem)`): written out, as a value and a memory are (`cf_opt`); `Some x` taken apart by a let of what it holds.
- *A memory inside an option from a recursion* (`mem -> option (A * mem)`, an error monad over the memory; `option mem`): a function of its own in its place gives back the value and the memory apart, `option A * mem` (`int * mem` for `option mem`, 1 for `Some`), and the function is the one in its place wrapped, at every argument, by induction (`om_wrap`, `om_wrap0`, `om_tr`, `om_rows`, `om_stmt`, `om_sub`, mark `rp_om`, `__m<rarg>`).  `None` hands back the newest memory in scope: where there is no value the memory is not looked at, so nothing depends on which, and no fact is added.  Its value goes through the slot block by step 78.
- *A method through a helper over a class* (`same {T} `{EqDec T} x y`): written out at a closed instance; what a class's program unfolds is named to the proof (`__clu__wy`).
- *The C*: a program with no such function: byte-identical.  Written out in each arm, where it was refused before.
- *Left, with cells*: a memory in a data type of the program's or in a `sum` (`A_zd_d_*`), the memory before a call that gave nothing (`A_zd_r_default`).  And the matrix power (`A_zp_mat_pow`): many tests that cannot be moves in one expression make the C a power of them: step 86.
- *The acceptance*: `proved/examples/optm_fix`: an allocator's helper, a ring's helper, a fill by recursion over it, a copy in an error monad; the answer worked out apart: 1674.
- *Cells*: 76: 42 `A_zd_*`, the probe's 34 `A_zp_*`.

**Step 85, what a fifth probe found — the result (2026-11-07).**  Built as designed:
- *The reader*: `cf_opt`, `cf_size`, `cf_ends`, `cf_on`, `cf_has`, `cf_fl`, `cf_lp`, `cf_red`; `om_wrap`, `om_wrap0`, `om_of`, `om_match`, `om_tr`, `om_rows`, `om_stmt`, `om_sub`, `om_s`, a row's mark 989; `cl_red` through a helper over a class; marks `__clu__wy`.  `KQR.v`, `KQRWf.v` unchanged.  *`kitc.py`*: `__m<n>` rows; what a class's program unfolds, `om_wrap` among it.
- *The acceptance*: `proved/examples/optm_fix`: proved, built, 1674.
- *Cells*: 76 more: 71 proved; gaps by their categories: `A_zd_d_res`, `_d_res_rec`, `_d_sum_rec`, `A_zd_r_default`, `A_zp_mat_pow`.  Two gaps read: `A_fx_opt_mem`, `A_fx_opt_mem_rec`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 84's files / these): `HWP_kernel` 2.98 / 2.97 s, `HWP_own` 2.06 / 2.04, `HWP_irqnow` 1.73 / 1.72 — the same.
- *`drv_fix`'s C differs*: a choice on written numbers, which the old form carried as a conditional move, is worked out when it is read: 11 temporaries fewer, the same answer.  It is the only one.
- The C: 90 of the 91 programs byte-identical, `drv_fix` as above.  The construct table (on `875c47b`): **3404 of 3540 through the
  verified compiler**, 54 by design, 81 gaps, 1 not Rocq (was 3331 of 3464: 71 of the 76 new cells read, 5 gaps; 2 gaps read; no
  cell lost).  The gate on `875c47b`, the walk switched off: `make.sh` `core-ok`; examples 56 / 56; corpus 36 / 36; the five
  kernels (15 / 15 / 18 / 15 / 15 s); **100 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust
  unchanged`.  Next: tests that cannot be moves, many in one expression.

**Step 86, tests that cannot be moves, many in one expression (§6, §12.A) — the design (2026-11-07).**  `compile` writes what follows an operand in each arm of a test that cannot be a conditional move (`KQR.choice_ok`: a call, a division).  So `k` such tests in one expression are `2^k` copies, and `x mod p`, which tests its signs and divides, is three arms: a matrix power modulo `p`, eight `mod` in one call's arguments, was read and proved and ran out of memory printing its C (F73).  A programmer writes that without thinking, so it is ordinary Rocq and must be read.
- *How many copies* (`jn_ds`, `jn_tail`, `jn_tab`, `jn_cnt`, `jn_pre`): read from the text, the compiler's way: an arm in each place a test puts it, a helper's own number from its body, a function read as a function a call, at the end of a function nothing after it.  One pass over the program's own declarations, in machine numbers: it runs for every program (F64).
- *More than 1024*: the program is read again with every such operand a function of its variables (step 54's `lift_ops`, `opnd`, the same term up to delta and beta), so it is a call and what follows is written once.  No proof to find: `denote s = f` by conversion, as before.  Clang inlines what is worth it.
- *Fewer*: read as it was, its C byte-identical.  The line keeps the programs read today as they are: none of them has more, and no measurement says a lower one would be better or worse.
- *An own call in such an operand* cannot leave its fixpoint: `A_ze_own_call_*`: written in each arm as before: eight are 256 copies, twelve a gap with its cell.
- *What it does not do*: a join point in KQL (an `Eif` whose arms go on to one continuation, the C `if (c) t = a; else t = b;`) would need no function, and is a change to KQL, `eval`, the generator and its proof: not this step, §6.4.
- *A function named `p1` or `p2`*: `.p1` is a token of MetaRocq's notations in the proof file, so `KQG.file.p1` did not parse: by its short name there, the program's file being imported (`A_m_e_name_p1`).
- *The acceptance*: `proved/examples/jn_fix`: a matrix power modulo a number, a sum of eight remainders; the answer worked out apart: 5525.
- *Cells*: 23, `A_ze_*`, with controls below the threshold.

**Step 86, tests that cannot be moves, many in one expression — the result (2026-11-07).**  Built as designed:
- *The reader*: `jn_div`, `jn_mul`, `jn_ds`, `jn_dup`, `jn_tail`, `jn_own`, `jn_tab`, `jn_big`, `jn_cnt`, `jn_pre`, `jn_add`, `jn_try`, `jn_mark`; `opnd`, `lift_op`, `lift_ops`, `rec_info2` take it.  `KQR.v`, `KQRWf.v` unchanged.  *`kitc.py`*: a function named `p1` or `p2` by its short name.
- *The acceptance*: `proved/examples/jn_fix`: proved, built, 5525.
- *Cells*: 23 more: 22 proved; `A_ze_own_call_12` a gap.  One gap read: `A_m_e_name_p1`; and `A_zp_mat_pow`, step 85's.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 85's files / these): `HWP_kernel` 2.98 / 3.01 s, `HWP_own` 2.04 / 2.07, `HWP_irqnow` 1.71 / 1.73: 0.03 s, the count.  Its first version made them 2.8 times slower, 8 s on `HWP_kernel`: `Nat.min 100000 ..` builds that literal at every node, and it took a look-up per function (F64 again); the timing is what found it.
- The C: the 92 programs byte-identical.  The construct table (on `3ed96d9`): **3428 of 3563 through the verified compiler**, 54
  by design, 80 gaps, 1 not Rocq (was 3404 of 3540: 22 of the 23 new cells read, 1 gap; 2 gaps read; no cell lost).  The gate on
  `3ed96d9`, the walk switched off: `make.sh` `core-ok`; examples 57 / 57; corpus 36 / 36; the five kernels (15 / 15 / 18 / 15 /
  15 s); **101 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust unchanged`.  Next: a memory in a
  value of any data type; a sixth probe.

**Step 87, a memory in a value of any data type; a sixth probe (§3.1, §12.A) — the design (2026-11-07).**  A sixth probe, 30 programs in other styles: state and reader monads over records, a state machine over an enumeration, nested records, structures in memory, a linked list and a tree by pointers, a knapsack, a matrix product, strings, a DFS by mutual recursion, a class over a memory, functors, sections, a local function over a memory, a closure given to a loop, tables in lists, FNV over `u64`.  29 read as they stand.  Its one failure is step 85's construct in another type: an error monad over a `sum`.
- *The form* (`gm_sh`, `gm_tr`, `gm_match`, `gm_fields`, `gm_arm`; `om_rows`, `om_stmt`, `om_sub` take it): a data type some constructors of which hold a memory, each at most one, a memory or a pair ending in one (`Ok (v : int) (t : mem) | Err (e : int)`, `int + (A * mem)`, a type of the program's, over a type or not).  A function of its own in the function's place gives back the value and the memory apart: the value is a sum of the constructors' other fields, each a tuple of them, the memory the one the constructor held or the newest in scope where it holds none.  The function is that one wrapped, at every argument, by induction, as in step 85: nothing depends on the memory where the value holds none, and no fact is added.
- *A helper giving back such a value*: written out, and the match in each arm (`cf_on`, keyed by the whole type, so that `int + int` stays as it was).
- *`vm_fq`*: a frame lemma only of a pair: `int + mem` looked like one.
- *The environment*: `sum` put in where a program's value needs it and its text never names it (`vm_with_sum`), as `prod` and `unit`.
- *The C*: a program with no such function: byte-identical.
- *Left, with cells*: three constructors or more held through a recursion (`A_zf_r_three`): the value is a sum in a sum, and a match on it after the call is not reduced yet.
- *The acceptance*: `proved/examples/resm_fix`: a fill by recursion over a helper in a type of the program's, a total in an error monad over a `sum`; the answer worked out apart: 75080.
- *Cells*: 51: 21 `A_zf_*`, the probe's 30 `A_zq_*`.

**Step 87, a memory in a value of any data type; a sixth probe — the result (2026-11-07).**  Built as designed:
- *The reader*: `gm_kf`, `gm_sh`, `gm_pty`, `gm_sty`, `gm_plain`, `gm_vs`, `gm_inj`, `gm_pack`, `gm_proj`, `gm_cases`, `gm_match`, `gm_fields`, `gm_arm`, `gm_tr`, `cf_holds`, `vm_with_sum`; `cf_on`, `cf_has`, `cf_fl`, `cf_lp`, `cf_red`, `vm_yr` given the program's such types; `om_rows`, `om_stmt`, `om_sub`, `vm_fq`, `um_inl` as designed.  `KQR.v`, `KQRWf.v`, `kitc.py` unchanged.
- *The acceptance*: `proved/examples/resm_fix`: proved, built, 75080.
- *Cells*: 51 more: 50 proved; `A_zf_r_three` a gap.  Three gaps read: `A_zd_d_res`, `A_zd_d_res_rec`, `A_zd_d_sum_rec`, step 85's.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 86's files / these): `HWP_kernel` 3.10 / 3.08 s, `HWP_own` 2.11 / 2.12, `HWP_irqnow` 1.79 / 1.77: no difference.
- The C: the 93 programs byte-identical.  The construct table (on `720c58c`): **3481 of 3614 through the verified compiler**, 54
  by design, 78 gaps, 1 not Rocq (was 3428 of 3563: 50 of the 51 new cells read, 1 gap; 3 gaps read; no cell lost).  The gate on
  `720c58c`, the walk switched off: `make.sh` `core-ok`; examples 58 / 58; corpus 36 / 36; the five kernels (15 / 15 / 18 / 15 /
  16 s); **102 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust unchanged`.  Next: the integer types
  of C as ordinary functions, what each computes proved.

**Step 88, the integer types of C as ordinary functions, what each computes proved (§2.1, §12.O) — the design (2026-11-07).**  `uint8_t` .. `int32_t` with C's wrap-around, `uint64_t`'s division and remainder, the high half of a product, `int64_t`, rotations, byte swaps, `popcount`, `clz`, `ctz`.  All of it has a definition other than the machine, so all of it is Rocq functions or cases of the generator's proof (§0.3, F66); nothing is added to what is assumed.
- *`uint64_t`'s `/` and `%`*: `W_divu`, `W_modu` of `w64op`, one instruction of `Ew64`, what `Z`'s `/` and `mod` give in `KQRun.v`.  A case of the generator's proof: C's are undefined at 0, so `tr_w64` writes a test around them (`w64_set`, `exec_w64set`), and clang removes it where it knows the divisor.  A division in the hardware is C's, which Clight's semantics states: this is proved against CompCert's `Int64.divu`, not assumed.  `KQ.KQRun.u64_divu`, `u64_modu`.
- *The library* (`lib/CInt.v`, generated text, 185 lines): over the numbers of the system and the `u64` of `KQRun.v`.  A value of a narrow type is a number in the type's range; each operation gives a value in the range.  A program that names one gets the text in front of it (`kitc.py`), in a module of its own, so a name of the program's own stands beside it and shadows it.
- *The theorems* (`lib/CIntSpec.v`): 120, against `Z`: each narrow operation on any number of the system, modulo `2^w` or wrapped into the signed range (`sw`); `u64_divu`, `u64_modu` against `/` and `mod`; `u64_mulhi` by its carries; `int64_t` read in two's complement (`sv`), including the smallest number over -1 and a divisor of 0; rotations; bytes; `clz`, `ctz` from Rocq's axioms on `head0`, `tail0`; `popcount32` by the two halves of 16 bits, each step checked on all 65536 values by computation.  `proved/make.sh` stops if they rest on anything but Rocq's axioms of its machine numbers.
- *C's undefined cases*: a signed overflow wraps, the way `-fwrapv` does; a division by 0 gives what `Z`'s does; the smallest number over -1 wraps.  A definition has to say something.  A test in the text is needed around `divs` by Rocq's axioms (§0.5, fourth reason): the library has it.
- *Many of them in one expression* (`jn_cnt`, `jn_own`, `jn_pre`): step 86's first test counted the written tests of the program's own text, so helpers of a library with tests inside them were never counted, and `i64_div` four times in one expression ran out of time.  A test written in a helper counts now, in a module of the file too, and one is enough to look further, since a helper used four times is four; the look at the environment's head goes to 500 declarations, since a library comes in front of the program.
- *The speed*: `u64_mulhi` is four multiplications, as portable C writes it: Clight has no high half.  `popcount`, `clz`, `ctz`: C has no operator; a form with one instruction would be a case of the generator's proof, measured, never a machine operation (F66).
- *`proved/make.sh`*: `KQLBack.v`, CompCert's pass theorems composed, leaves the default build: nothing depends on it, and the passes' licence is non-commercial (D30).
- *The acceptance*: `proved/examples/cint_fix`: every operation on every pair of 32 numbers, the edges of each type among them, folded into one number; the answer worked out apart in Python from the statements of the theorems: 258591630940955040.
- *Cells*: 128, `A_zg_*`: one per operation, and places: a name of the program's own beside the library's, many with tests in one expression, nested, a round of SHA-256, in loops, in a memory, as a record's field, given as a function.

**Step 88, the integer types of C as ordinary functions, what each computes proved — the result (2026-11-07).**  Built as designed:
- *The library*: `lib/CInt.v`; `kitc.py`'s trigger, in a module of its own.  *The theorems*: `lib/CIntSpec.v`, 120; `proved/make.sh` compiles them and stops if they rest on anything but Rocq's axioms of its machine numbers (`PrimInt63`, `Uint63Axioms`, `Sint63Axioms`).
- *`uint64_t`'s `/` and `%`*: `W_divu`, `W_modu`, `w64_int`, `w64_set`, `exec_w64set`.
- *Found by the theorem*: the first `u64_divu`, a loop of shift and subtract in the library before it became an instruction, shifted the remainder and lost its top bit, wrong for a divisor above `2^63`: the C was proved equal to a wrong function (F74).  The example found nothing more: its answer, worked out apart from the statements of the theorems, was right at the first run.
- *The reader*: `jn_in`; `jn_cnt`, `jn_own`, `jn_pre`.
- *A cell the check refused*: `A_q_nat_field`, read since step 82 and refused by the check, is refused by the reader now, with its reason (`nr_grows`): a counter a helper makes through a successor is not the same term as its number.
- *The acceptance*: `proved/examples/cint_fix`: proved, built, 258591630940955040.
- *Cells*: 128 more, all read.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 87's files / these): `HWP_kernel` 3.45 / 3.43 s, `HWP_own` 2.31 / 2.32, `HWP_irqnow` 1.96 / 1.95: no difference, with the first test now true for most programs.
- The C: the 94 programs byte-identical, and `cint_fix`, new.  The construct table (on `42c08a7`): **3609 of 3742 through the
  verified compiler**, 54 by design, 78 gaps, 1 not Rocq (was 3481 of 3614: the 128 new cells all read; no cell lost; the table's
  one cell read and refused by the check now refused by the reader).  The gate on `42c08a7`, the walk switched off: `make.sh`
  `core-ok`, `lib/CIntSpec.v` on Rocq's axioms of its machine numbers alone; examples 59 / 59; corpus 36 / 36; the five kernels
  (15 / 15 / 18 / 15 / 15 s); **103 programs through the verified compiler, 0 refused**; `check_trust.py`: `trust unchanged`.
  Next: an ordinary `.v` file, as simply as `lean --c`.

**Step 89, an ordinary `.v` file, as simply as `lean --c` (§12.B, §0.10's fourth) — the design (2026-11-07).**  `python3 proved/kitc.py prog.v`: no `.body`, no `main` to write, no special command in the file.  A command in the file (`Kq Compile solve.`) would need a plugin under every file and adds nothing: the tool reads the file as `lean --c` reads one, and the file stays one Rocq compiles on its own.
- *The start*: the last function of the file, or `--main=NAME`.
- *The arguments, from the signature* (`sig_args`, `last_def`): Rocq's `Check` says the type; a number or a boolean from the command line, a counter from the command line, the memory from the memory file; a number given back is printed, a memory summed.  Any other type at the entry is refused with the type and the reason.  The `main` of a `.body` was never proved: the driver writes the same call.
- *Libraries*: a program that requires `KQ.lib.CInt` gets no text in front of it; the reader reads a library's functions as any other file's (step 51).  One that only names them still gets the text, as a `.body` does, but then it does not compile on its own.
- *A `.body`*: unchanged, its C byte-identical.
- *The acceptance* (`tests/vroute.py`): every example and corpus program written as a `.v` with no `main`: the C of its functions the same as the `.body` route's, the answers the same.  `proved/vfiles/plain.v` is in the gate: compiled by Rocq on its own, then by `kitc.py`, the answer worked out apart: 1345105947.
- *Not here*: refusals that say what to write instead (§12.B's last item), the driver proved (§12.H).

**Step 89, an ordinary `.v` file — the result (2026-11-07).**  Built as designed:
- *`kitc.py`*: `.v` accepted, `--main=NAME`, `last_def`, `sig_args`; `proved/examples.sh` runs `proved/vfiles/*.v`, each compiled by Rocq on its own first.
- *The acceptance*: `tests/vroute.py`: 93 of 95 programs, the 59 examples and 34 of the corpus's 36: the same C and, for the examples, the expected answer.  The other two, `CF868F` and `CF868Fv2`, have a `main` that computes an argument, which a signature cannot say: in a `.v` that computation is a function of the program, and its C has one function more.  An entry that takes a list is refused with its type and the reason.  `proved/vfiles/plain`: proved, built, 1345105947.
- *No cell*: the reader is unchanged and the table's programs are `.body` files.
- The C: the 95 programs byte-identical.  The construct table (on `ec163ad`): **3609 of 3742 through the verified compiler**, 54
  by design, 78 gaps, 1 not Rocq (was 3609 of 3742: unchanged, the reader being unchanged; the table run again after the laptop it
  ran on stopped).  The gate on `ec163ad`, the walk switched off: `make.sh` `core-ok`; examples 60 / 60, `proved/vfiles/plain`
  among them; corpus 36 / 36; the five kernels (15 / 15 / 18 / 15 / 16 s); **104 programs through the verified compiler, 0
  refused**; `check_trust.py`: `trust unchanged`.  Next: the generated C on its own, no hosted header and no libc.

**Step 90, the generated C on its own: no hosted header, no libc (§12.D, §9.5, §0.10's fifth) — the design (2026-11-07).**  The kernels were built freestanding, but with CertiRocq's runtime headers on the include path and with no `kq_grow`.  What a program's C needs from anything else is now small and written down.
- *`sup/free/`*: `values.h`, `gc_stack.h`: a value is a word, and the entry's pointer is never read: no heap, no collector, no runtime in the generated C.  `kq_mem.c`: the memory's tables, the slow paths, `kq_grow` over free memory someone hands it, the checksum, `memcpy` and its kin: no operating system, no instruction set, no hosted header.  `kq_start_linux.c`: a start for the gate on x86-64 Linux, with raw system calls: the arguments, the memory file, the answer.  A kernel has `hw/boot.S` and `hw/kq_bare.c` in its place.
- *`kitc.py`*: a hosted program's `NAME_bare.c` is written beside its `NAME_proved.c`: the same functions, the driver without `sys/mman.h`.  `NAME_proved.c` is byte-identical.  A bare program that grows a block gets the wrapper `f91019`.
- *`hw/kq_bare.c`*: `kq_grow` from a fixed room in the kernel's own memory; no more room stops the program, as the hosted one does.  `hw/grow.body`: a kernel that grows a block and checks old and new cells; the gate builds it through the proved route; booted under QEMU's processor by hand: it answers 0.
- *The check* (`proved/examples.sh`): every example also built with `-ffreestanding -nostdinc -nostdlib -static` and only clang's own `stdint.h`, `stddef.h`, run, and compared with its expected answer.
- *What stays assumed*: `kq_grow` stays on `proved/TRUSTED.txt` as the allocator under the tables (§12.H): this writes its C, it does not prove it.  Nothing is added to the list; `sup/free/` is support code like `sup/v4/`, outside the theorem, as the driver and the loader are.
- *Not here*: the kit route's support (`sup/v4/`, `gc_stack.c`) stays for the hosted test, where it is linked and not used by the functions; the corpus has its own speed run and is not built this way.

**Step 90, the generated C on its own — the result (2026-11-07).**  Built as designed:
- *`sup/free/`*: `values.h`, `gc_stack.h`, `kq_mem.c`, `kq_start_linux.c`.  *`kitc.py`*: `NAME_bare.c` beside `NAME_proved.c`, the wrapper of `kq_grow` in a bare program that grows.  *`hw/kq_bare.c`*: `kq_grow` from a fixed room.  *`hw/grow.body`*: built through the proved route, booted under QEMU's processor: `QEMU exit status 1: the program answered 0`; `irqnow` still boots, 10 interrupts handled.
- *The check*: all 59 examples with no hosted header and no libc, statically linked, nothing left undefined, each its expected answer; `w64` is 14 KB.  Unused wrappers of the machine's operations go with `--gc-sections`, as `-flto` removes them in the hosted build.
- *No cell*: the reader is unchanged.
- *One cell refused in the table run, `A_ze_mod_5`, with no reason*: run alone on the same files it is read and proved (14 s, 2.2 GB); three cells at a time under the table's 8 GB, it was stopped for memory.  The reader did not change.  It stays counted as refused here, as the table says.
- The C: the 95 programs byte-identical.  The construct table (on `925e035`): **3608 of 3742 through the verified compiler**, 54
  by design, 79 gaps, 1 not Rocq (was 3609 of 3742: `A_ze_mod_5` refused in the run for memory, as above; nothing else changed).
  The gate on `925e035`, the walk switched off: `make.sh` `core-ok`; examples 60 / 60, and 59 / 59 freestanding; corpus 36 / 36;
  the five kernels and `grow` (16 / 16 / 18 / 15 / 16 / 6 s); **105 programs through the verified compiler, 0 refused**;
  `check_trust.py`: `trust unchanged`.  Next: the printed C says what the Clight says, and the tools are asked.

**Step 91, the printed C says what the Clight says, and the tools are asked (§12.H) — the design (2026-11-08).**  The theorem ends at Clight; the text clang reads is the printer's.  §12.H's interim is to check that text with other tools.  Doing so found a difference at once.
- *The difference* (F75): `tagup` shifts a number left by one, and for a signed one the printed C is `(((long long)x >> 1) / ..) << 1`.  Clight defines the left shift of a negative number; C leaves it undefined.  So the C text said less than the theorem's Clight.  clang gives it the meaning Clight does (its IR has no `nsw` on it), so no answer was wrong, and nothing in the theorem said so.
- *The fix*, in the generator, not the printer, since the generator is proved: `ucast`: a signed number goes to the unsigned type first (`KQLGen.tagup`, `KQLProof.eval_tagup`).  Unsigned operands print as before.
- *The C*: the text of the programs with a signed operation changes by that cast, and only those; clang's assembly for them is the same, line for line.
- *The checks* (`proved/examples.sh`), each the same printed functions, each to the expected answer: undefined behaviour trapped (`-fsanitize=undefined -fsanitize-trap`, no runtime); `-O0 -fno-strict-aliasing`; CompCert's `ccomp`, where it is installed (`KQ_NO_CCOMP=1` leaves it out): `sup/v4/kq_io.h` gives it the plain `?:` in place of the asm of a conditional move, so the printed C compiles with it as it is, for whoever holds its licence (D30).  A program that calls an operation of the machine is left out of `ccomp` only: their C bodies are GNU C.
- *What this is not*: a proof.  The printer, clang and the driver stay unproved, and the CompCert route of §12.H stays open.  Each of these checks a few runs, of the examples only.

**Step 91, the printed C says what the Clight says, and the tools are asked — the result (2026-11-08).**  Built as designed:
- *The generator*: `ucast`, `tagup`, `eval_tagup`.  *`kitc.py`*: the freestanding form leaves out the machine's wrappers when none is called.  *`proved/examples.sh`*: the three builds.
- *The C*: the text of 41 of the 95 programs differs, by the cast; clang's assembly is the same for all 41, compared at `-O2` before and after.
- *The checks*, on the 59 examples: undefined behaviour trapped 59 right; `-O0` 59 right; `ccomp` 56 right, 3 call an operation of the machine.  Before the fix the first stopped 4 programs: `cint_fix`, `reflect_helpers`, `sdiv`, `views`.
- *No cell*: the reader is unchanged.
- The C: 54 of the 95 programs byte-identical, the 41 others different by the cast and only by it, their assembly the same.  The
  construct table (on `95b1f77`): **3609 of 3742 through the verified compiler**, 54 by design, 78 gaps, 1 not Rocq (was 3608 of
  3742: `A_ze_mod_5` read again, the run having had the memory this time).  The gate on `95b1f77`, the walk switched off:
  `make.sh` `core-ok`; examples 60 / 60, 59 / 59 freestanding; the same C: undefined behaviour trapped 59 / 59, `-O0` 59 / 59,
  `ccomp` 56 / 56 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (15 / 15 / 17 / 15 / 16 / 5 s); **105
  programs through the verified compiler, 0 refused**; `check_trust.py`: `trust unchanged`.  Next: the construct table's gaps, and
  the general speed passes (§6.4).

**Step 92, the bit operations of Rocq's library on counters (§2.1, §3.5, §12.A) — the design (2026-11-08).**  `Nat.land n 6`, `Nat.shiftr n 1`, `Nat.testbit n k`, `Nat.b2n`: natural, and a counter is one machine number (step 70).  Each has a definition in Rocq and is one to three instructions of the machine, so each is a case of the generator's proof, proved from Rocq's lemmas and its axioms of the machine's numbers; nothing is added to what is assumed (§0.3, F66).
- *The family*, Stdlib's `Nat` (`Init.Nat`, `PeanoNat`): `land`, `lor`, `lxor`, `ldiff`, `shiftr`, `clearbit`, `testbit`, `shiftl`, and what is defined by them, `b2n`, `setbit`, `ones`, `lnot`.  `gcd`, `log2`, `sqrt`, `log2_up`, `sqrt_up`, `lcm` recurse, and a loop is a function of its own in KQL: step 93.
- *`S`* (`KQR.v`): `CBitN o a b`, `o` one of `NLand`, `NLor`, `NLxor`, `NLdiff`, `NShiftr`, `NClear`, its meaning the library's function by conversion (`nbop_nat`); `CShl k c`, `Nat.shiftl c k` with `k` written; `BTestN a k`, `Nat.testbit a k`.  The code: `land`, `lor`, `lxor`, `lsr` of the two machine numbers; `ldiff` the `land` of the first and the `lxor` of the second with the 63 ones; `clearbit` the same with `lsl 1 k` for the second; `testbit` the `land` of `lsr a k` with 1, then a test, a value or a conditional move, as `BEven` is; `shiftl` `lsl` by the written number.
- *What is proved*, each from Rocq's lemmas on `Nat`, `Z` and its axioms of `PrimInt63` alone: the machine's `land`, `lor`, `lxor` of two counters below `wB` are those of the counters (`Nat.land_spec`, `Z.land_spec`, bit by bit, `Z.bits_inj'`); `lsr` is `Nat.shiftr` for any count below `wB`, 63 and above included; `ldiff` and `clearbit` by the 63 ones, `clearbit` by a count of 63 and above too, which `lsl` makes 0; the bit is `(a / 2^k) mod 2` on both sides; `lsl` is `Nat.shiftl` modulo `wB` at every counter, as a product is (step 70).
- *Their bounds* (`cmax`, `cmaxv`, `clinf`): `land`, `ldiff`, `shiftr`, `clearbit` at most the first, written as the larger of the two so that the whole fitting shows each part fits, as `CDivN`; `lor`, `lxor` below the power of two above the larger (`Z.log2_lor`, `Z.log2_lxor`), so that two counters below `2^63` give one below it; in the linear bound the sum (`Z.add_lor_land`); `shiftl` the bound times `2^k`.  `wf` asks both operands below `2^63`, the bound of the whole below it where it is a counter, as for any.
- *The reader*: the six by name in `reify_c`, `testbit` in `reify_b`, `shiftl` when its count is a written number; `shiftr` is no longer opened to its `nat_rect`; `b2n`, `setbit`, `ones`, `lnot` opened to their definitions.  The same under `Require Import Arith`.
- *By design* (§0.5, second reason), each with a control: `Nat.shiftl` by a counter, `Nat.setbit`, `Nat.ones`, `Nat.lnot` at a counter, and `shiftl` by a written number past a word: a number that may need more than a word, as `Nat.pow 2 n` (step 70); the controls the same at a written number.  `clearbit` at a counter is read: its value is at most the first.
- *Left, with cells*: a function giving back a counter (step 82's rows) built with one of them: `land`, `lor`, `lxor`, `ldiff` agree modulo `wB` at every counter, `shiftr`, `testbit`, `clearbit` do not and want step 83's bounds.
- *The C*: a program with no such operation: byte-identical.
- *The acceptance*: `proved/examples/bitn_fix`: a count of the bits set by `testbit`, masks by `land`, `lor`, `lxor`, `ldiff`, `clearbit`, shifts, `b2n`, `setbit`, `ones`, `lnot` at written numbers, as budgets, tests and numbers, in a recursion; the answer worked out apart.
- *Cells*: `A_zh_*`: each operation as a budget, a number, a test, a match, a let, in a recursion, under `Require Import Arith`, nested, on a counter of a machine number; `testbit` in a test, a value, a conditional move, under `&&` and `negb`; the pins and controls above; the rows left.

**Step 92, the bit operations of Rocq's library on counters — the result (2026-11-09).**  Built as designed, the bounds made exact:
- *`S`* (`KQR.v`): `nbop`, `nbop_nat`, `CBitN`, `CShl`, `BTestN`; `cbitn` (the code), `cbitm` (the bound); `nbit_z`, `z_land` .. `z_shiftl`, `ofn_land` .. `ofn_testbit`, `cbitn_ok`, `cbitm_bound`, `cbitm_mono`, `nbop_le_add`: from Rocq's lemmas on `Nat` and `Z` and its axioms of the machine's numbers, nothing more.  The cases of `cexp_all` and of the bounds' lemmas.
- *The bounds, exact*: the design wrote them as the larger operand, so that the whole fitting would show each part fits, as `CDivN`.  Then `Nat.shiftl (Nat.land n 3) 2`, at most 12, would have been refused as a number past a word: an over-rejection.  `wf` asks each operand to fit, as `testbit`'s does, and the bound is the smaller for `land`, the first for `ldiff`, `shiftr`, `clearbit`, the power of two above the larger for `lor`, `lxor`.
- *The reader* (`KQRReify.v`): `nbop_of`, the six by name, `CShl` at a written count, `BTestN`; `shiftr` no longer opened; `setbit`, `ones`, `lnot` opened.
- *Found by `b2n`*: a counter that is a helper's call on a test, `Nat.b2n (a <? b)` or a function of the program's, was refused: writing a helper out binds what it is given by a `let` when it is not a variable, and a counter had no reading of a `let`.  A `let` in a counter named at most once is put in its place (`rel_occ`), what the kernel's check does (zeta), with nothing written twice.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 91's files / these): `HWP_kernel` 3.16 / 3.14 s, `HWP_own` 2.15 / 2.14, `HWP_irqnow` 1.81 / 1.79 — the same.  The first version cost 5% on `HWP_own` (2.13 / 2.25): the six names were tested at every call of a constant in a counter, before the program's helpers, and `testbit` before the comparisons of the machine's numbers, the common test (F64 again).  They are tested last now.
- *The trust check stopped the step* on `lxor_spec`: `Uint63Axioms.lxor_spec`, already listed, printed short since `KQR.v`'s theorem now reaches it.  Taken to the owner; looking at it found the check weak (F76): names compared as text, `Check`'s outputs taken as assumptions, and `PrimInt63.compares`, `Sint63Axioms.compare_spec`, which `KQRWf.kq_compares_def` (step 64) rests on, never printed.  The owner: Rocq's own axioms are the floor.  `make.sh` prints what every lemma of the route rests on, from a file that imports nothing; `proved/TRUSTED.txt` lists that, 90 names, each once by its full name; the gate reads only that.  Nothing assumed changed: the two of `compares` were assumed since step 64 and not listed.
- *The acceptance*: `proved/examples/bitn_fix`: proved, built, 734603704.
- *Cells*: 75 more: 67 proved; by design, each with a control: `A_zh_shiftl_var`, `_shiftl_big`, `_setbit_var`, `_ones_var`, `_lnot_var` (a power of two of a counter, a counter shifted past a word; controls `A_zh_shiftl_lit`, `_setbit_lit`, `_ones_lit`, `_lnot_lit`); gaps `A_zh_row_land`, `_row_shiftr`, `_row_testbit_own`: a function giving back a counter built by a bit operation, step 82's rows.  `A_zh_row_testbit`, a test on a parameter in such a function, is read.  Four gaps read: `A_c2_nat_land`, `_shiftr`, `_testbit`, `_b2n`.  The code commit says 73 cells: the control `A_zh_shiftl_masked` and the gap `A_zh_row_testbit_own` were added after its message was written.
- The C: the 95 programs byte-identical, and `bitn_fix`, new.  The construct table (on `af6b6ca`): **3680 of 3817 through the
  verified compiler**, 59 by design, 77 gaps, 1 not Rocq (was 3609 of 3742: 67 of the 75 new cells read, 5 by design, 3 gaps; 4
  gaps read; no cell lost).  The gate on `da6b1d1` (`af6b6ca` and the trust check of F76), the walk switched off: `make.sh` `core-ok`; examples 61 / 61, 60 / 60
  freestanding; the same C: undefined behaviour trapped 60 / 60, `-O0` 60 / 60, `ccomp` 57 / 57 and 3 not built with it; corpus 36
  / 36; the five kernels and `grow` (15 / 16 / 19 / 16 / 16 / 6 s); **106 programs through the verified compiler, 0 refused**;
  `check_trust.py`: `trust unchanged`, 90 assumptions each by its full name.  Next: the recursive functions of the library on
  counters, `gcd`, `log2`, `sqrt` (step 93).

**Step 93, the recursive functions of Rocq's library on counters: `gcd`, `sqrt`, `log2` (§2.1, §3.5, §12.A) — the design (2026-11-09).**  `Nat.gcd a b`, `Nat.sqrt n`, `Nat.log2 n`: natural, each has a definition in Rocq, and each needs a loop, which in KQL is a function of its own.  So each is a call of a function of the kit, an ordinary Rocq function over machine numbers proved equal to the library's, compiled with the program as any of its functions; nothing is added to what is assumed.
- *The kit* (`KQRun.v`): `kq_gcdg k a b`, Euclid's loop, its budget the first operand (it decreases at every round, so no bound has to be guessed or proved); `kq_sqrtg k lo hi a`, a search between 0 and 3037000500 in 32 rounds, the square of the middle below `2^63`; `kq_log2g k x r s`, a search of six rounds over the shifts 32, 16 .. 1.  Ordinary Rocq over `PrimInt63`.
- *What is proved* (`KQR.v`), from Rocq's lemmas on `Nat` and `Z` and its axioms of the machine's numbers alone: `kq_gcdg a (ofn a) (ofn b) = ofn (Nat.gcd a b)` for `a`, `b` below `wB` (by induction on the budget: what it is given is at most it); `kq_sqrtg 32 0 3037000500 (ofn a) = ofn (Nat.sqrt a)` (the search's invariant, `lo^2 <= a < hi^2`); `kq_log2g 6 (ofn a) 0 32 = ofn (Nat.log2 a)`.
- *`S`*: `CLib o f a b`, `o` one of `LGcd`, `LSqrt`, `LLog2`, its meaning the library's function by conversion; its code a call of the program's function `f` with the budget and the start of the search.  `wf` asks `f`'s signature to be `o`'s (`kit_sig o`) and the operands to fit.
- *Which function `f` is*: a kit function stands in the program's table of callees under a signature no other call reaches: the pair flag of step 44 without a memory, which every other call refuses, and its own bound (`2^63`, 33, 7), so the three are distinct.  The theorem takes one more premise, `KitsOk cs`: every callee under such a signature is the kit's function.  It is proved for each program by its constructors, the signatures compared by computation; its function is compiled under the same signature without the flag, which for a function that takes no memory is the same type and the same call, so the callee's theorem is the function's by conversion.
- *Bounds*: each at most the larger operand (`Nat.gcd_le`, `Nat.sqrt_le_lin`, `Nat.log2_le_lin`); in the linear bound the sum.
- *The reader*: the three by name, after the program's helpers (step 92's lesson); the kit functions put among the program's functions when its text names one; `log2_up`, `sqrt_up` opened to their definitions.
- *By design* (§0.5, second reason): `Nat.lcm`, a product of two counters, as `Nat.mul n n` (step 70), its control `A_c2_mul_r`.
- *The C*: a program with no such call: byte-identical.  One that has one gets the kit's function once.
- *The acceptance*: `proved/examples/libn_fix`: gcds, square roots and logarithms over a block's cells, as budgets, tests and numbers, in a recursion; the answer worked out apart.
- *Cells*: `A_zi_*`: each function as a budget, a number, a test, a match, a let, in a recursion, nested, on a counter of a machine number, under `Require Import Arith`, at 0 and at the largest numbers; `log2_up`, `sqrt_up`; `lcm` and its control.

**Step 93, the recursive functions of Rocq's library on counters: `gcd`, `sqrt`, `log2` — the result (2026-11-09).**  Built as designed:
- *The kit* (`KQRun.v`): `kq_gcdg`, `kq_sqrtg`, `kq_log2g`.  *What is proved* (`KQR.v`): `kq_gcdg_ok`, `kq_sqrtg_inv` and `kq_sqrt_ok`, `kq_log2g_inv` and `kq_log2_ok`, `nsqrt_z`, `nlog2_z`, `nlop_le`, from Rocq's lemmas and its axioms of the machine's numbers alone.
- *`S`*: `nlop`, `nlop_nat`, `CLib`; `kit_bound`, `kit_sig`, `kit_fun`, `kit_mark`, `kit_sigb`, `kits_ok`, `kit_entry`, `kit_entry_ok`, `kit_args`, `kit_call`; the cases of `cexp_all` and of the bounds' lemmas.
- *Where the premise went*: the design put it beside `callees_ok`, which would have added an argument to every theorem built on the compiler's and to every call of them.  It is `callees_ok`'s second half, `kits_ok`, and `all_ok` asks of a callee under a kit's signature that it be the kit's function as well (`if kit_mark gs then ..`): for any other callee its obligation is what it was, so no proof of a program or of the tests changed but a kit entry's, which gives `kit_entry_ok`.
- *A written budget unrolls a loop* (F67 again): in `kit_call` the budget 32 written in `sqrt`'s call made `cbn` unroll both branches of its 32 rounds and the proof never ended; the budget is a variable through the reduction, put in by an equation after.
- *The reader* (`KQRReify.v`): `kit_kn`, `nlop_of`, `kit_of_kn`, `lk_kit`, `lk_ops`, `lk_with`, `kit_fix`; the three after the program's helpers; the kit's functions quoted in, read first, under their kit signatures.  *`kitc.py`*: a kit entry's theorem by `compile_f_ok` under its signature without the flag, its entry of `all_ok` with `kit_entry_ok`.
- *Left, with cells*: `log2_up`, `sqrt_up` match on `Nat.compare`, which shows only once they are opened, after the step that rewrites it: a gap with its cells.  *Found*: a counter written as a number is read as a chain of successors: §12.E.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 92's files / these): `HWP_kernel` 3.05 / 3.05 s, `HWP_own` 2.13 / 2.10, `HWP_irqnow` 1.80 / 1.78 — the same.  The first version cost 4% on `HWP_kernel` (3.07 / 3.20): every program looked the three library names up in its whole environment, three times; one pass comparing short names first now (F64 again).
- *The acceptance*: `proved/examples/libn_fix`: proved, built, 2800517866.
- *Cells*: 36 more: 33 proved; `A_zi_lcm` by design, a product of two counters, its control `A_c2_mul_r`; gaps `A_zi_log2_up`, `_sqrt_up`.  Three gaps read: `A_c2_nat_gcd`, `_sqrt`, `_log2`.
- The C: the 96 programs byte-identical, and `libn_fix`, new.  The construct table (on `b8758c7`): **3716 of 3853 through the
  verified compiler**, 60 by design, 76 gaps, 1 not Rocq (was 3680 of 3817: 33 of the 36 new cells read, 1 by design, 2 gaps; 3
  gaps read; no cell lost).  The gate on `b8758c7`, the walk switched off: `make.sh` `core-ok`; examples 62 / 62, 61 / 61
  freestanding; the same C: undefined behaviour trapped 61 / 61, `-O0` 61 / 61, `ccomp` 58 / 58 and 3 not built with it; corpus 36
  / 36; the five kernels and `grow` (15 / 15 / 18 / 15 / 16 / 6 s); **107 programs through the verified compiler, 0 refused**;
  `check_trust.py`: `trust unchanged`.  Next: the follow-ups of §12 (a program's own theorem in the gate, §12.T; a written counter
  as one number, §12.E), and the table's gaps.

**Step 94, a counter written as a number, one number in the C (§12.E's follow-up, §3.5) — the design (2026-11-09).**  A counter written as a number was read as a chain of successors: its code as long as the number, `Nat.land n 4095` 4095 additions, and printing that C ran out of 3 GB (found at step 93).  And from 5000 on Rocq writes a `nat` as `Nat.of_num_uint` of its digits, which was not read at all: `go 100000 ..`, as one writes a budget.  Both are one number of the machine.
- *`S`* (`KQR.v`): `CLit k`, its meaning the number `k` itself, what Rocq writes below 5000; `CNumU u`, its meaning `Nat.of_num_uint u`, the digits Rocq writes from 5000 on, decimal or hexadecimal.  The code of each: the constant, `ofn k`, and `of_Z (nu_z u)`, `nu_z` the digits read into `Z` as `Nat.of_uint_acc` reads them into `nat`.
- *What is proved*: `nu_z_ok : Z.of_nat (Nat.of_num_uint u) = nu_z u`, by induction on the digits, closed under the global context (no axiom at all); the rest is the constant's value.
- *Bounds*: exact, `k` and `nu_z u`.  A number past a word as a counter is refused by the fitting every counter has (§0.5, second reason): a pin, its control the same below `2^63`.  `CLit` keeps what the chain had for a `let`'s bound (its depth `k`, no addition), so a `let` of a written counter is bounded as before; `CNumU` has its own bound.
- *The reader*: a written counter of 1 or more, a chain of successors on 0, is `CLit`; `Nat.of_num_uint` of written digits is `CNumU`.
- *The C*: a program with a counter written as a number changes: each chain of additions becomes its constant.  Each changed program's C compared, and clang's assembly before and after; the answers the same, the corpus timed if a corpus program changes.
- *The acceptance*: `proved/examples/lit_fix`: budgets of 12 and 4095, a test against 100000, a mask of 65535, a hexadecimal one, a budget of 1000000 in a loop that stops early; the answer worked out apart.
- *Cells*: `A_zj_*`: a written counter as a budget, a number, a test, a let, an operand, in a recursion, below and from 5000, decimal and hexadecimal, at the edges (1, 4999, 5000, `2^63 - 1`); the pin past a word and its control.

**Step 94, a counter written as a number, one number in the C — the result (2026-11-09).**  Built as designed, with one node more:
- *`S`* (`KQR.v`): `CLit`, `CNumU`; `du_z`, `hu_z`, `nu_z`; `du_z_ok`, `hu_z_ok`, `nu_z_ok`, closed under the global context; the cases of `cexp_all` and of the bounds' lemmas.
- *A product by a number written from 5000 on* (`Nat.mul n 100000`): the reader's tree is computed (`vm_compute`), so a `nat` in it is unary, and `CMulK`'s factor, a `nat`, would carry 100000 as 100000 successors.  `CMulU l u c`, the factor as its digits, its meaning `Nat.mul (Nat.of_num_uint u) c` (or the other order), its code the product by `of_Z (nu_z u)`, its bounds `CMulK`'s with `nu_z u` for the factor; each case of the proofs is `CMulK`'s after `nu_z_ok`.
- *The reader* (`KQRReify.v`): a chain of successors on 0 is `CLit`; `Nat.of_num_uint` of written digits is `CNumU` (`ddig_of`, `hdig_of`, `uint_of`, `num_lit`), looked for after the program's helpers; `Nat.mul` by such a number is `CMulU`; a power of two written numbers up to 4096 is the `CLit` of its value, where it was a chain; such a number given to a helper is put in its parameter's place, as one below 5000 is.  The reader's pinned trees say `CLit` now; `KQR.v`'s hand-written ones keep their chains, which test `CS`.
- *Found by the cells* (F77): `Uint63.of_nat 100000` took 97 s to check, `Uint63.of_nat 0xFFFFF` over 300 s.  The meaning says `ofn c`, the text `of_Z (Z.of_nat c)` (`Uint63.of_nat` is a notation for it), and the kernel opened the program's `of_Z` first, whose match worked `Z.of_nat` out on the number in unary.  It was there before this step for any written counter turned into a number, under a second at 4095.  The check files `kitc.py` writes unfold `ofn`, our abbreviation, first: 3.4 s, the C the same.
- *Left, with a cell*: a power of two written numbers above 4096 (`A_zj_pow_big`, `Nat.pow 2 13`): read only up to 4096; the refusal's hint said "may need more than a word" of 8192 and names both cases now; §12.E.
- *The C*: 33 of the 97 programs change, 19 of them corpus programs, and each gets shorter: every chain of additions on a written counter is its constant (`CF61E` 506 to 338 lines, `libn_fix` 1556 to 318, `bitn_fix` 904 to 310); the other 64 byte-identical; `lit_fix` new.  clang's assembly (`-O2`) before and after: the same for 32, the file's name aside; `conv_fix` has its 1355 instructions with two of them placed elsewhere and other registers.  The corpus programs' machine code is the same, so no timing changes.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 93's files / these): `HWP_kernel` 2.97 / 2.98 s, `HWP_own` 2.05 / 2.04, `HWP_irqnow` 1.73 / 1.72 — the same.
- *The acceptance*: `proved/examples/lit_fix`: budgets of 12, 4095, `2^10` and 6000 named twice, masks of 65535 and `0xFFFF0`, a test against 100000, products by 100000 and 7000, a budget of 1000000 in a loop that stops at 1000: proved, built, 134643534.  Its C holds each number once.
- *Cells*: 37 more: 34 proved, at 1, 4999, 5000 and `2^63 - 1`, decimal and hexadecimal, as budgets, numbers, tests, lets, operands, in a match, a recursion and a callee; by design, each with a control: `A_zj_land_past` (a written number past a word, control `A_zj_land_max`), `A_zj_mul_big` (a counter times 100000, past a word, control `A_zj_mul_r`); gap `A_zj_pow_big`.
- The C: 33 programs changed as above, 64 byte-identical, and `lit_fix`, new.  The construct table (on `da8f5f1`): **3750 of 3890
  through the verified compiler**, 62 by design, 77 gaps, 1 not Rocq (was 3716 of 3853: 34 of the 37 new cells read, 2 by design,
  1 gap; no cell lost).  The gate on `da8f5f1`, the walk switched off: `make.sh` `core-ok`; examples 63 / 63, 62 / 62
  freestanding; the same C: undefined behaviour trapped 62 / 62, `-O0` 62 / 62, `ccomp` 59 / 59 and 3 not built with it; corpus 36
  / 36; the five kernels and `grow` (15 / 16 / 18 / 15 / 16 / 6 s); **108 programs through the verified compiler, 0 refused**;
  `check_trust.py`: `trust unchanged`.  Next: §12.E's new follow-up (a power of two written numbers above 4096), §12.T's (each
  gate program's own theorem in the gate), and the table's gaps.

**Step 95, a power of two written numbers, its value one number in the C (§12.E's follow-up of step 94, §3.5) — the design (2026-11-09).**  `Nat.pow 2 13`, `2 ^ 20`, `Nat.pow 10 18`: natural, the value known from the text.  It was read only up to 4096, as a chain of successors (since step 94 the `CLit` of its value); above, refused with a hint that it "may need more than a word" (`A_zj_pow_big`).
- *`S`* (`KQR.v`): `CPowL a b`, `a` and `b` written numbers (`CLit`, `CNumU`, `CO`), its meaning `Nat.pow a b` by conversion, its code the constant `of_Z (zpw a b)`, `zpw` a power by squaring in `Z`, so that working it out costs the exponent's digits, not its value.  `wf` asks both to be written numbers: the code is a constant only then.
- *What is proved*: `zpw a b = Z.pow a b`; `Z.of_nat (Nat.pow x y) = Z.pow x y` (Rocq's `Nat2Z.inj_pow`); a written number's `Z` is its meaning's (`nu_z_ok`).
- *Bounds*: exact, the value.  A power past a word is refused by the fitting every counter has (§0.5, second reason): `Nat.pow 2 63`, a pin, control `Nat.pow 2 62`.  The reader refuses a base of 2 or more with an exponent of 63 or more before any computing (the same reason; the value would have more digits than the exponent says).
- *The check*: the meaning and the text meet at the same call of `Nat.pow` only if the kernel unfolds our side first; else it works the program's `Nat.pow 2 40` out in unary (measured: 2^12 at once, 2^40 not in 60 s), F77's trap again.  Which order the check files set (our meaning functions first, or the library's function last) is measured on the gate's programs before it is chosen.
- *The reader*: `Nat.pow` of two written numbers is `CPowL`, whatever the value; the 4096 limit goes.
- *The C*: a program with a power of written numbers up to 4096: the same constant, byte-identical; any other: byte-identical.
- *The acceptance*: `proved/examples/pow_fix`: `2 ^ 13`, `Nat.pow 10 18` as a test, `2 ^ 40` as a mask's bound, `Nat.pow 3 39`, `0 ^ 0`, `1 ^ 100000`, under `Require Import Arith`; the answer worked out apart.
- *Cells*: `A_zk_*`: as a budget, a number, a test, a let, an operand, in a recursion; at 0 ^ 0, 1 ^ 100000, 2 ^ 62, 10 ^ 18, a hexadecimal exponent; the pins `2 ^ 63`, `10 ^ 19` and their controls; `A_zj_pow_big` read.

**Step 95, a power of two written numbers, its value one number in the C — the result (2026-11-09).**  Built as designed, its operands a type of their own:
- *`S`* (`KQR.v`): `wnum` (`WLit k`, `WNum u`: a written number, below 5000 or as its digits), `wval`, `wz`; `ppw`, `zpw`, a power by squaring in `Z`; `CPowL a b` over two `wnum`s; `ppw_ok`, `wz_ok`, `cpw_ok`, closed under the global context; the cases of `cexp_all` and of the bounds' lemmas.  The design gave `CPowL` two counters with `wf` asking both to be written: but the bounds' lemmas hold for every tree, with no `wf` premise, and the linear bound has nothing to bound a power of two counters with.  Its operands are written numbers by their type, so it is a constant as `CNumU` is, its bound exact, and `wf` has nothing to ask.
- *The reader* (`KQRReify.v`): `Nat.pow` of two written numbers (`wnum_of`) is `CPowL`, whatever the value; a base of 2 or more with an exponent of 63 or more is refused before any computing.  The 4096 limit is gone; the hint for a refused power names a power of a counter and one past a word.
- *The check* (F78): with the meaning `Nat.pow a b` and the text `Nat.pow 10 18` the kernel still worked the number out in unary when it sat in a comparison: `Nat.ltb n (Nat.pow 10 18)` did not end in 120 s, unfolding our meaning functions first did not help, unfolding `Nat.pow` last did (1.5 s); `Nat.land 1000000 65535` written out failed the same way.  F77 was one case of it.  The check files `kitc.py` writes unfold our abbreviations first (`ofn`, `cmpn`, `nbop_nat`, `nlop_nat`) and every library function a node of `S` means last, so that the meaning and the text meet at the same call and its arguments are compared.  Measured against the order of step 94 and against `Nat.pow` alone last, without the cache, on the new cells and nine gate programs: the same or faster (`CF622F` 13.1 to 10.5 s, `vals_fix` 13.0 to 10.0 s), and the two cells the old order failed proved (3.6 s).
- *The C*: the 98 programs byte-identical: `lit_fix`'s `Nat.pow 2 10` is a `CPowL` now, the same constant.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 94's files / these): `HWP_kernel` 3.05 / 3.10 s, `HWP_own` 2.11 / 2.09, `HWP_irqnow` 1.78 / 1.80 — the same, these the faster in two rounds of three.
- *The acceptance*: `proved/examples/pow_fix`: `2 ^ 13` as a budget, `10 ^ 18` in a test, `2 ^ 40 - 1` as a mask, `3 ^ 39` modulo 1000003, `0 ^ 0` and `1 ^ 100000` as budgets, under `Require Import Arith`: proved, built, 123463739004.
- *Cells*: 25 more: 23 proved, at `0 ^ 0`, `0 ^ 100000`, `1 ^ 100000`, `2 ^ 62`, `10 ^ 18`, `3 ^ 39`, `100000 ^ 3`, a hexadecimal exponent, as budgets, numbers, tests, lets, operands, in a recursion and a callee, with the notation, under `Arith`, and five calls of the library on written numbers alone; by design, each with a control: `A_zk_past_63`, `A_zk_past_ten19` (past a word; controls `A_zk_num_62`, `A_zk_num_ten18`).  One gap read: `A_zj_pow_big`.
- The C: the 98 programs byte-identical, and `pow_fix`, new.  The construct table (on `c938ac6`): **3774 of 3915 through the
  verified compiler**, 64 by design, 76 gaps, 1 not Rocq (was 3750 of 3890: 23 of the 25 new cells read, 2 by design; 1 gap read;
  no cell lost).  The gate on `c938ac6`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the
  same C: undefined behaviour trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five
  kernels and `grow` (15 / 16 / 18 / 15 / 15 / 6 s); **109 programs through the verified compiler, 0 refused**; `check_trust.py`:
  `trust unchanged`.  Next: §12.T's follow-up (each gate program's own theorem in the gate), then the table's gaps.

**Step 96, each program's own end theorem, and what it rests on, in the gate (§12.T's follow-up, F76) — the design (2026-11-10).**  Since step 92 the gate checks what every lemma of the route rests on.  A program's claim is put together per program: the entry's theorem `{name}_rok{j}` (the KQL function computes the Rocq function), and the generator's `kit_function_correct` (the Clight function computes what the KQL run gives).  Nothing stated the two joined for the program, and nothing checked what that rests on.
- *`proved/KQREnd.v`*: `callee_end`, proved once: from a function's `callee_ok`, the two checks the generator's theorem takes (`names_ok`, `params_ok`, decided by computation), the machine operations as its laws say (`hw_ok`, `kit_function_correct`'s own premises) and the slot block's room, the Clight function the generator makes, called from any Clight memory holding the kit's memory, gives the Rocq function's answer and a memory holding the one the Rocq function gives back (`endk`): `callee_ok` with the KQL run replaced by the Clight run.  In `make.sh` and in the route's list of what it rests on, which it does not change (measured: 79 names, all on the list).
- *Each program* (`kitc.py`): `{name}_end`, `callee_end` applied to the entry's theorem, the two checks by `eq_refl`.  With `KQ_ENDAX=1` (the gate sets it) what `{name}_end` rests on is printed from a file that imports nothing, so each name is the one constant it names (F76), one line a program: `NAME END-ASSUM n: names`.
- *The gate*: the lines of every example, corpus program and kernel; `check_trust.py --gate` asks each name to be on the list and one line for each program through the verified compiler, and stops otherwise.
- *What it does not change*: the C, the per-function theorems, what is assumed.  A program whose end theorem rested on anything off the list would stop the gate: a finding, taken to the owner.
- *The acceptance*: the gate prints the end theorem's assumptions of all its programs, each within the list, and `check_trust.py --gate` compares them; a program made to rest on an `Axiom` of its own is refused before, by §0.5's fourth reason, and a line naming something off the list makes `check_trust.py` stop (tried on a copy of a log).

**Step 96, each program's own end theorem, and what it rests on, in the gate — the result (2026-11-10).**  Built as designed:
- *`proved/KQREnd.v`*: `hw_ok`, `endk`, `callee_end`; in `make.sh` and in the route's list of what it rests on, which it leaves as it was (79 names, all on the list).
- *Each program* (`kitc.py`): `{name}_end := callee_end .. {name}_rok{j} eq_refl eq_refl`, the entry `j` the last function read; with `KQ_ENDAX=1`, set by `examples.sh`, `corpus.sh` and `hw/build_proved.sh`, what it rests on, printed from a file that imports nothing, one line a program (`hw/build_proved.sh` keeps that line whole, `examples.sh` four lines a program).  1 to 2 s more a program, in the gate only.
- *Found by the first one printed* (F79): `lit_fix`'s end theorem rested on 82 names, `PrimFloat.float` and `PrimString.string` among them, off the list.  A program's tree was defined as a projection of the reader's whole result, whose type holds MetaRocq's `term`; the tree is its computed value now, in `S` alone: 80 names, all on the list.
- *`check_trust.py --gate`*: each name of each `END-ASSUM` line on the list, a line for each program through the verified compiler, the count of names as printed.  Tried on copies of a log: a clean one, `trust unchanged`; a program's line naming one more axiom, `NOT ON THE LIST: assumption KQ.Mine.my_axiom (the end theorem of lit_fix)` and a stop; a program's line missing, `NO END THEOREM PRINTED` and a stop.
- *Found by the gate* (F80): `prim_fix`'s end theorem rested on ten names off the list, `PrimInt63.compare`, `addc`, `subc`, `addmuldiv`, `diveucl` and Rocq's axioms of their definitions, `Uint63Axioms.*_def_spec`: since step 64 the reader writes those primitives as their definitions and each program's proof of that rests on them, while the list held what the route's lemmas rest on.  The chain stopped; taken to the owner, who listed them, Rocq's own, the floor, as at step 92 (2026-11-10).  `check_trust.py --gate` now asks every listed name to be used by the route or by a program's end theorem, and every name either prints to be listed: 100 names.  The other 108 programs' end theorems were within the list as it was.
- *The C*: the 99 programs byte-identical.
- *What it costs*: the gate's five kernels and `grow` 21 / 22 / 24 / 18 / 18 / 9 s, against 15 / 16 / 18 / 15 / 15 / 6: a kernel is several programs, and each prints its end theorem from a file of its own, which loads the route's libraries.  The gate only: a program compiled without `KQ_ENDAX` pays nothing.
- *The table*: every cell's check file states its end theorem now, and every cell read before is still proved: no cell lost, none read and refused by the check.
- The C: the 99 programs byte-identical.  The construct table (on `e73b49b`): **3774 of 3915 through the verified compiler**, 64
  by design, 76 gaps, 1 not Rocq (was 3774 of 3915: no cell new, lost or gained).  The gate on `e73b49b`, the walk switched off:
  `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour trapped 63 / 63, `-O0` 63 / 63,
  `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (21 / 22 / 24 / 18 / 18 / 9 s, the end
  theorems printed); **109 programs through the verified compiler, 0 refused**, and their 109 end theorems each within the list;
  `check_trust.py`: `trust unchanged` with the list of `e73b49b` (the gate ran on `ca0513c`, the list the owner's decision after
  it).  Next: step 97 (the bounds of a min and of a subtraction of counters exact), built and its cells read locally; then the
  comparisons in any place (`log2_up`, `sqrt_up`, step 98).

**Step 97, the bounds of a min and of a subtraction of counters exact (§3.5, §12.A; the gap `A_c2_min_clamp`) — the design (2026-11-10).**  `Nat.mul 3 (Nat.min (Uint63.to_nat a) 1000)`: at most 3000, refused as a number past a word, since the bound of a min was the larger of its operands' (`Z.max`) and its linear bound their sum.  The same for `Nat.sub 1000 x`, at most 1000, bounded by the larger of the two.
- *Bounds* (`KQR.v`): a min, the smaller of its operands' (`Z.min`); a subtraction, its first operand's; in the linear bound, a subtraction its first operand's, a min the second operand's where it is below the first at every place, else the first's (`lmin`): any of the two bounds a min, so the choice needs no proof.
- *`wf`*: with an exact bound the whole fitting no longer shows that each operand fits, and the code computes both: `wf` asks each operand of a min and of a subtraction to fit, as for the bit operations (step 92).  Every program read before still is: an operand fitted there since the larger bound did.
- *What is proved*: the bounds' lemmas' cases (`Nat.min`, `Nat.sub` under `Z.of_nat`), `cexp_all`'s two cases taking the operands' fits from `wf`.
- *The C*: unchanged, bounds are not code.
- *Cells*: `A_zl_*`: a min with the number first and second, of two counters, nested, in a let, a test, a number, a call's counter, a callee's; a subtraction the same; a subtraction of a min; the pins: an operand past a word in a min and in a subtraction, each with its control, the operand masked.  `A_c2_min_clamp` read.

**Step 97, the bounds of a min and of a subtraction of counters exact — the result (2026-11-10).**  Built as designed:
- *Bounds* (`KQR.v`): in `cmax` and `cmaxv` a min is `Z.min` of its operands', a subtraction its first operand's; in `clinf` a subtraction its first's, a min `lmin`, the second's linear bound where `lle_c` finds it below the first's at every place, else the first's.  `wfc` asks each operand of a min and of a subtraction to fit, as for `CBitN`.
- *The proofs*: the bounds' lemmas as they were, `lia` taking `Nat.min` and `Nat.sub` under `Z.of_nat`, but for `clinf_bound`'s two cases (a case on `lmin`'s choice; the first operand alone) and `cmaxv_cmax`'s cases of two operands, whose second rewrite a subtraction no longer has.  `cexp_all`'s two cases take the operands' fits from `wf`, and `auto` closes with them what `lia` closed: the two `lia`s left met the continuation and failed.
- *The C*: the 99 programs byte-identical: bounds are not code.
- *Cells*: 17 more: 15 proved, a min with the number first and second, of two counters, nested, in a let, a test, a number, a call's counter, a callee's; a subtraction the same; a subtraction of a min; by design, each with a control: `A_zl_min_past`, `A_zl_sub_past` (an operand past a word; controls `A_zl_min_past_ctl`, `A_zl_sub_past_ctl`, the operand masked).  One gap read: `A_c2_min_clamp`.
- The C: the 99 programs byte-identical.  The construct table (on `94e26b0`): **3790 of 3932 through the verified compiler**, 66
  by design, 75 gaps, 1 not Rocq (was 3774 of 3915: 15 of the 17 new cells read, 2 by design; 1 gap read; no cell lost).  The gate
  on `94e26b0`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined
  behaviour trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow`
  (21 / 21 / 24 / 18 / 18 / 9 s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within
  the list; `check_trust.py`: `trust unchanged`.  Next: a match on a comparison in any place, `log2_up`, `sqrt_up` (step 98),
  built and its cells read locally.

**Step 98, a match on a comparison in any place: `log2_up`, `sqrt_up`, `Nat.compare` in a counter (§3.5, §12.A; the gaps `A_zi_log2_up`, `A_zi_sqrt_up`) — the design (2026-11-10).**  `Nat.log2_up n` is `match Nat.compare 1 n with Lt => S (log2 (pred n)) | _ => 0 end`.  The reader writes `Nat.compare` as its definition, a choice of `Lt`, `Eq`, `Gt` by tests (step 64), and floats a match on such a choice into the tests at a function's end (`y_tail`, step 69), each by an equation `kitc.py` proves of the program.  Two places were not reached: a definition of Rocq's library that calls `Nat.compare` is written out where the program calls it after that rewriting, so its call never met it; and a match on a choice anywhere but the end, a counter given to a call, was not floated.
- *The reader* (`KQRReify.v`): a definition of Rocq's libraries, not a fixpoint, whose body calls what the rewriting writes as its definition, written out first (`pm_open`); a match on a choice of constructors floated in any place, inside a fixpoint too, the new match's type the outer one's where that does not depend on the value matched, a constant constructor's branch taken (`y_inner`).  Both inside `y_all`, which runs only where the first reading failed: a program read before is read as before.
- *What is proved*: nothing new in `KQR.v`; each such program's equation, as for the rewriting it extends, by `kitc.py`.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zm_*`: `log2_up`, `sqrt_up` as a number, a test, a let, under `Arith`, in a recursion, at 0 and at a written number, one of the other; `Nat.compare` matched in a counter, against a counter of a machine number, in a test, nested; a match on a choice written by hand in a counter; `PrimInt63.compare` matched in a counter.  `A_zi_log2_up`, `A_zi_sqrt_up` read.

**Step 98, a match on a comparison in any place: `log2_up`, `sqrt_up`, `Nat.compare` in a counter — the result (2026-11-10).**  Built as designed, with two things more:
- *The reader* (`KQRReify.v`): `rocq_lib`, `pm_named`, `pm_lib`, `pm_open`, `pm_lib_any`: a definition of Rocq's libraries, not a fixpoint, not one `lib_open` opens later and not one the rewriting knows by name, whose body calls a primitive the rewriting writes as its definition (`Nat.compare`), written out first; `y_conk`, `y_inner`, `y_inner_has`: a match on a choice of constructors without arguments, of a type other than `bool`, floated in any place, inside a fixpoint too; both in `y_all`.
- *Found by the table* (F82): the first version floated a match on any choice of constructors and opened any library definition that calls what the rewriting knows: seven cells read before were lost, `A_l_dec_ge`, `_gt`, `_le`, `_lt`, `_opnd` (`ge_dec` opened, though step 68 reads it by its name), `A_m_b_find_bind` (a choice of pairs, a monad's), `A_zc_r_chosen` (a choice of records of functions, step 84's).  Neither landed: the floating takes only constructors without arguments of a type other than `bool`, and `pm_open` only definitions nothing knows by name; all seven read again, the 21 new cells too.
- *Found by the C* (F81): `cint_fix`'s C changed though nothing of the step applies to it: the first version marked a function rewritten when `negb (teq 100000 new old)`, and `teq` answers false once its fuel runs out, on `lib/CInt.v`'s long `u64_top`, so `u64_top` got a rewritten row of its own.  Whether to float is decided by a scan for what `y_inner` floats (`y_inner_has`); `cint_fix` byte-identical.
- *Found by `A_zm_log2_up_sqrt_up`* (`Nat.log2_up (Nat.sqrt_up n)`): a program's equation is proved by case on its tests, and a test's answer that its case contradicts, `(S m =? 0) = true`, was left open.  The five step tactics of `KQRWf.v` close such a dead branch (`cbn` and `discriminate` on a hypothesis), tried after `reflexivity`, so only where the others found nothing.
- *The C*: 97 of the 99 programs byte-identical.  `lib2_fix`, `prim_fix`: a match on a comparison in a number's place, compiled as tests of its tag on constants (`if (1ULL == 1ULL) { if (1ULL == 3ULL) ..`), floated now: 252 to 228, 806 to 338 lines; clang's assembly (`-O2`) the same for `lib2_fix`, `prim_fix` 1495 to 1373 instructions.  No corpus program changes.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 95's files / these, step 97's `KQR.v` among them): `HWP_kernel` 3.00 / 2.99 s, `HWP_own` 2.07 / 2.07, `HWP_irqnow` 1.74 / 1.73 — the same.
- *Cells*: 21 more, all proved: `log2_up`, `sqrt_up` as a number, a test, a let, under `Arith`, in a recursion, at 0 and at a written number, one of the other; `Nat.compare` matched in a counter, against a counter of a machine number, in a test, nested; a match on a choice written by hand in a counter; `PrimInt63.compare` matched in a counter.  Two gaps read: `A_zi_log2_up`, `A_zi_sqrt_up`.
- The C: 97 of the 99 programs byte-identical, `lib2_fix` and `prim_fix` as above.  The construct table (on `a4ac67c`): **3813 of
  3953 through the verified compiler**, 66 by design, 73 gaps, 1 not Rocq (was 3790 of 3932: the 21 new cells read; 2 gaps read;
  no cell lost).  The gate on `a4ac67c`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the
  same C: undefined behaviour trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five
  kernels and `grow` (21 / 21 / 24 / 19 / 19 / 9 s); **109 programs through the verified compiler, 0 refused**, their 109 end
  theorems each within the list; `check_trust.py`: `trust unchanged`.  Next: a counter chosen by a match on a counter (step 99),
  built and its cells read locally.

**Step 99, a counter chosen by a match on a counter (§3.5, §12.A; the gap `A_c2_match_cnt`) — the design (2026-11-10).**  `ff (match n with O => 1 | S m => m end) a`: a counter's value chosen by a match on another, natural, was not read in a counter's place.  A match on a counter is read where it gives a number (F19); where it gives a counter it has no node, and it binds a counter.
- *The reader* (`KQRReify.v`): in `y_all`, a match on a counter that gives a counter, in a counter's place (an argument, a `let` of a counter, a branch of such a match), is written `if Nat.eqb c 0 then x else y`, the predecessor `Nat.pred c` for the second branch's variable (`y_natm`, `y_natm_c`); decided by a scan (`y_natm_has`, F81).  Not where a branch applies a variable: a recursion's own call stays on the variable it is structural on.
- *What is proved*: each such program's equation, by `kitc.py`, the dead branch closed by step 98's tactic step; nothing new in `KQR.v`.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zn_*`: such a match as a number, in a test, a let, a branch's counter used twice, nested, on an expression, on a counter of a machine number, with a call and a helper in a branch, given to a callee, in a recursion's accumulator and in its counter's argument.  `A_c2_match_cnt` read.

**Step 99, a counter chosen by a match on a counter — the result (2026-11-10).**  Built as designed:
- *The reader* (`KQRReify.v`): `calls_rel`, `ym_tmpl` (the test and its branches as a quoted `if`, so that no case of the reader's own is built), `ym_nat`, `ym_ok`, `y_natm` and `y_natm_c` (a term in a counter's place: an argument, a branch of such a match), `y_natm_has`; in `y_all` after step 98's floating.  A `let` of a counter takes its value in a counter's place.
- *Found by the cells*: a branch's own match on a counter (`A_zn_nested`) and a `let` of one (`A_zn_let`) were not in a counter's place in the first version: the branches and a counter's `let` are now.  The equations of a recursion's own body (`A_zn_rec`, `A_zn_rec_arg`) close with step 98's dead-branch step in `own_step`.
- *The C*: the 99 programs byte-identical.
- *Cells*: 13 more, all proved: such a match as a number, in a test, a let, a branch's counter used twice, nested, on an expression, on a counter of a machine number, with a call and a helper in a branch, given to a callee, in a recursion's accumulator and in its counter's argument.  One gap read: `A_c2_match_cnt`.
- The C: the 99 programs byte-identical.  The construct table (on `5bf8172`): **3827 of 3966 through the verified compiler**, 66
  by design, 72 gaps, 1 not Rocq (was 3813 of 3953: the 13 new cells read; 1 gap read; no cell lost).  The gate on `5bf8172`, the
  walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour trapped 63 / 63,
  `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (22 / 22 / 24 / 19 / 19 / 8
  s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within the list; `check_trust.py`:
  `trust unchanged`.  Next: a function giving back a counter whose recursion goes more than one step down (step 100), built and
  its cells read locally.

**Step 100, a function giving back a counter whose recursion goes more than one step down (§3.5, §12.A; the gaps `A_z_s_match_counter`, `A_zb_s_deep`) — the design (2026-11-10).**  `tw (S (S m)) = S (tw m)`, a counter given back: the reader reads it, as a row giving a number (step 82) and that row as a recursion two steps down with its copies (step 58), but `kitc.py` stated the copies' equation of `tw` itself, whose copies were never made: the reader's record of such recursions (`pf_info`) is of the program as written, the copies of the row the reading used.
- *The reader* (`KQRReify.v`): `pf_info_r`, the record of the environment the reading used: the program's own where the copies it names were made, else `y_all`'s, a row named by its short name in the reader's file (`strip_pre`).  `kitc.py` asks for it.
- *What is proved*: nothing new; the copies' equation, as for any such recursion.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zo_*`: such a counter as a budget, a number, a test, a let, a callee's; three steps down; with an accumulator; with a memory; two of them.  `A_z_s_match_counter`, `A_zb_s_deep` read.

**Step 100, a function giving back a counter whose recursion goes more than one step down — the result (2026-11-10).**  Built as designed:
- *The reader* (`KQRReify.v`): `strip_pre`, `pf_info_r`; *`kitc.py`* asks for `pf_info_r q r0` where it asked for `pf_info q`.  Measured on the two gaps: the reader's record named `tw` with the stem of `tw`'s copies, `KQG'_.._tw__w`, never made; of `y_all`'s environment it names the row, `kqcopy.KQG'_.._tw__k0__rp__wy`, whose copies were, and the row's name in the reader's file is its short name.
- *The C*: the 99 programs byte-identical.
- *Cells*: 9 more, all proved: such a counter as a budget, a number, a test, a let, a callee's; three steps down; with an accumulator; with a memory; two of them.  Two gaps read: `A_z_s_match_counter`, `A_zb_s_deep`.
- The C: the 99 programs byte-identical.  The construct table (on `1de1259`): **3838 of 3975 through the verified compiler**, 66
  by design, 70 gaps, 1 not Rocq (was 3827 of 3966: the 9 new cells read; 2 gaps read; no cell lost).  The gate on `1de1259`, the
  walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour trapped 63 / 63,
  `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (22 / 22 / 25 / 19 / 19 / 9
  s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within the list; `check_trust.py`:
  `trust unchanged`.  Next: the other places of a counter in a value (a local fix giving back one, a closed term computed), from
  the notes of step 100.

**Step 101, a function giving back a counter built by a bit operation (§3.5, §12.A, step 92's follow-up; the gap `A_zh_row_land`) — the design (2026-11-10).**  `cb (S j) = Nat.land (cb j m) 7`: a counter given back is read as a row giving its number (step 82), each operation of the counter the machine's, proved by a lemma (`nr_add`, `nr_mul`); the bit operations had none, and a row's bound (step 83) had no rule for them.
- *The row* (`KQRReify.v`, `nr_tr`): `land`, `lor`, `lxor` the machine's, `ldiff` the `land` of the first and the `lxor` of the second with the 63 ones: each the same modulo a word at every counter, since their low 63 bits are those of the operands' low 63 bits, so no bound is asked.  `shiftr`, `clearbit` are not the same modulo a word: not read in a row.
- *What is proved* (`KQRWf.v`): `nr_land`, `nr_lor`, `nr_lxor`, `nr_ldiff`, from Rocq's axioms of its machine numbers alone, by bits; `kq_nr` rewrites by them.
- *The bound* (`nb_go`, `nb_step`): `land` at most a written operand, else its first; `ldiff` its first; `lor`, `lxor` the sum; `nb_bitf` gives `lia` those facts (`nb_land_l`, `nb_land_r`, `nb_ldiff`, `nb_lor`, `nb_lxor`).
- *Left, with cells*: a test on a row's own result (`A_zh_row_testbit_own`) and a row's `shiftr` (`A_zh_row_shiftr`), which want the row's bound; a counter a function gives back used inside a bit operation elsewhere (`A_zr_land_budget`): step 83's reading of such a counter takes `S`, `+`, `*`, a §12.A follow-up.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zr_*`: a row's `lor`, `lxor`, `ldiff`, a `land` with a parameter, of two own results, two steps down, mixed, its result in a test and as a budget.

**Step 101, a function giving back a counter built by a bit operation — the result (2026-11-10).**  Built as designed:
- *The row* (`KQRReify.v`): `nr_land_i`, `nr_lor_i`, `nr_lxor_i`; `nr_tr` reads `land`, `lor`, `lxor`, `ldiff` by step 92's `nbop_of`, `shiftr` and `clearbit` not.  *The bound*: `nb_go`'s four rules.
- *What is proved* (`KQRWf.v`): `nr_nbit`, `nr_nbits`, `nr_zland` .. `nr_zldiff`, `nr_mod63`, `nr_land` .. `nr_ldiff`, `nr_zland_ldiff`, `nr_zlxor_add`, `nb_land_l`, `nb_land_r`, `nb_ldiff`, `nb_lor`, `nb_lxor`, from Rocq's axioms of its machine numbers alone; `kq_nr`'s four rules, `nb_bitf` in `nb_step`.  Step 92 proved the same facts of `Z` in `KQR.v`, which `KQRWf.v` comes before: they are proved again here under other names rather than `KQR.v` importing `KQRWf.v`'s whole name space.
- *Found by the cells*: a row's result used in a test (`A_zr_lxor_test`) wanted the row's bound, so the bound took its rules in the same step; a row's result used inside a bit operation in another function (`A_zr_land_budget`) goes through step 83's reading of such a counter, which takes `S`, `+`, `*`: a §12.A follow-up.
- *The C*: the 99 programs byte-identical.
- *Cells*: 9 more: 8 proved, a row's `lor`, `lxor`, `ldiff`, a `land` with a parameter, of two own results, two steps down, mixed, its result in a test; gap `A_zr_land_budget` (the follow-up).  One gap read: `A_zh_row_land`; `A_zh_row_shiftr` and `A_zh_row_testbit_own` named by what they want.
- The C: the 99 programs byte-identical.  The construct table (on `2667bb1`): **3847 of 3984 through the verified compiler**, 66
  by design, 70 gaps, 1 not Rocq (was 3838 of 3975: 8 of the 9 new cells read; 1 gap read; no cell lost).  The gate on `2667bb1`,
  the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour trapped 63 /
  63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (22 / 22 / 24 / 19 / 19
  / 9 s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within the list;
  `check_trust.py`: `trust unchanged`.  Next: step 102, the follow-up: a counter a function gives back, used as a counter inside a
  bit operation (`A_zr_land_budget`).

**Step 102, a counter a function gives back, used as a counter inside an operation (§3.5, §12.A, step 101's follow-up; the gap `A_zr_land_budget`) — the design (2026-11-10).**  `ff (Nat.land (cb n n) 255) a`, `cb` built by a bit operation (step 101).  Step 101 named the cause as step 83's reading of such a counter taking only `S`, `+`, `*`.  Measured on the cell, that was not it: the reader made `cb`'s row, but its bound `cb k m <= k + m + 1023` was not kept, since `nb_all` keeps a bound only where its multiples and its constant together are at most 1000.  With the bound kept, the counter is read where it is used as step 83 reads it and the operation around it as any counter's (step 92): `land`, `lor`, `lxor`, `ldiff`, `shiftr`, `setbit`, `clearbit`, `testbit`, `/`, `mod`, `min`, `max`, `-`, `pred`, `div2` all read with no rule of their own.  Rules for the bit operations in step 83's reading (`nc_has`, `nc_c`, `nc_tr`), built first, gave the same C, byte for byte, on the 26 cells then proved: not kept (F83).
- *The bound's constant* (`nb_all`): its multiples at most 1000 as before, its constant apart, at most `2^20`: the step by which the counters' bounds go down from one function to the next (`kitc.py`'s `bnz`), the room a constant has where it is used; in `Z`, not counted one `S` at a time.
- *A written number in a row* (`nr_tr`, `nb_go`, `nc_c`): one constant, where a chain of 1023 successors ran out of a fuel of 1000 (step 94's trap again); `kq_nr` computes it in the row's equation at once.
- *A written number in step 83's walks* (`nc_has`, `nc_any`, `nc_sub`): a leaf.  They walked its chain once per link with a test that walks it again: 2 s at 1023, three times per function, so `A_zr_land_budget` took 18 s to read (5 s now).  The same results by construction: a written number holds no call.
- *A shift left by a written number* (`Nat.shiftl x k`), the one operation of these that grows its operand: a product by `2^k` in step 83's reading, the machine's `lsl` (`nr_shiftl`, from `lsl_spec`, which is listed; an amount below `wB`, as a written one is).  By 3 or more, or by a counter, past a word (up to 8 times a counter of up to `2^60`, or `2^n`): by design, as `A_zh_shiftl_big` and `A_zh_shiftl_var` are, with the shifts by 1 and 2 as controls.
- *An operation inside a sum or a product* (`Nat.land (cnt n a s) 255 + cnt n b s`): there the site of step 83's reading is the whole sum, the operation one counter to it, so `lia` is given what each is at most: `nb_bitf`'s facts (step 101) and `nc_opf`'s (`shiftr`, `/`, `mod`, `div2`, `clearbit`, `setbit`, `double`); `min`, `max`, `-`, `pred` it knows.  Without them the check fell to a path that unfolds `Nat.land`: no answer in 300 s.
- *A definition of Rocq's libraries around such a counter* (`Nat.double`): written out where that brings the counter into the reading (`nc_ul`), as the program's own helpers are (`nc_uh`, step 83).
- *Left, with a cell*: a bound whose constant is above `2^20` (`A_zs_big_const`: `Nat.mul (Nat.land (S (cbm j m)) 4095) 300`, `cbm k m <= k + m + 1228500`): not kept, the room its use has not reckoned yet; a §12.A follow-up, a bound's constant reckoned where the counter is used, with its multiples, in `Z`.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zs_*`, 52: such a counter in `land` with a written number, a parameter, another such counter; `lor`, `lxor`, `ldiff`; nested; with a `+` inside and outside; in a test, an equality, a match, a let, a callee's argument, a recursion; `shiftr`, `shiftl` by 1, 2, 3 and by a counter, `setbit`, `clearbit`, `/`, `mod`, `min`, `max`, `-`, `pred`, `div2`, `double`, `testbit`; 15 of them inside a sum, `land` inside a product; a counter built by a bit operation used directly, at one counter, by `lor`; a bound whose constant is above `2^20`.

**Step 102, a counter a function gives back, used as a counter inside an operation — the result (2026-11-10).**  Built as designed, but the cap of a bound's constant:
- *The bound's constant*: designed at most `2^20`, the room its use has; measured, the bound's statement carries it as a chain of successors (`nb_nat`), and a constant of 76500 took 18 s and 2.4 GB to check where 1023 takes 5 s, so it would not fit in memory near `2^20`.  Kept below 5000, as Rocq writes a numeral of `nat` (4095: 7 s, 0.9 GB); from 5000 on a §12.A follow-up, the constant in `Z` (`A_zs_const_mid`, `A_zs_big_const`).
- *The reader* (`KQRReify.v`): `nb_all`'s bound kept with its multiples at most 1000 and its constant below 5000, apart; a written number one constant in `nr_tr`, `nb_go`, `nc_c`, a leaf in `nc_has`, `nc_any`, `nc_sub`; `Nat.shiftl` by a written number in `nc_has`, `nc_c`, `nc_tr` (`nr_lsl_i`).
- *What is proved* (`KQRWf.v`): `nr_shiftl`, from `lsl_spec`; `nc_fold`'s rule for `lsl`, `nc_shl` in `nc_side`; `kq_nr` computes a written number at once (`nr_numeral`).
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 101's files / these): `HWP_kernel` 2.91 / 2.90 s, `HWP_own` 1.95 / 1.96, `HWP_irqnow` 1.63 / 1.62 — the same.
- *The C*: the 99 programs byte-identical.
- *Cells*: 54 more: 50 proved; by design, each with controls: `A_zs_shiftl_three`, `A_zs_shiftl_var` (the shifts by 1 and 2); gaps `A_zs_const_mid`, `A_zs_big_const` (a bound's constant from 5000 on, §12.A).  One gap read: `A_zr_land_budget`.
- The C: the 99 programs byte-identical.  The construct table (on `f39c112`): **3898 of 4038 through the verified compiler**, 68
  by design, 71 gaps, 1 not Rocq (was 3847 of 3984: 50 of the 54 new cells read, 2 by design, 2 gaps; 1 gap read; no cell lost).
  The gate on `f39c112`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined
  behaviour trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow`
  (22 / 21 / 25 / 20 / 19 / 9 s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within
  the list; `check_trust.py`: `trust unchanged`.  Next: step 103, step 102's follow-up of a sum around such a counter with an
  operation the check knows nothing of (a hang, there since step 83), then step 104, a use where its value modulo a word is
  enough.

**Step 103, a sum around a counter a function gives back, with an operation the check knows nothing of (§3.5, §12.A, found at step 102; there since step 83) — the design (2026-11-10).**  `ff (cnt n a s + Nat.log2 n) b`: step 83's reading takes the whole sum as one site where its count (`nc_c`) says it is at most seven times its counters, and `nc_c` counted any call it has no rule for as one counter.  The check of the site then asks `lia` for a bound of `log2 n`, has none, and falls to a path that unfolds `Nat.log2`: no answer in 120 s, the same with `sqrt`, `gcd` (measured on step 101's tree too).  The same with a helper of the program, `hk k := 7 * k` (`cnt n a s + hk n`, counted one counter where it is seven), and with a function giving back a counter that has no bound (a doubling `tw`, counted one).  The reading's decision counted what the check cannot show.
- *The count* (`nc_opc`): a call by the bound the check is given of it: `land`, `min` the smaller operand; `lor`, `lxor`, `max`, `gcd` the sum; `ldiff`, `shiftr`, `/`, `mod`, `div2`, `clearbit`, `-`, `pred`, `log2`, `sqrt` the first; `setbit` by a written number below 13 the first (its `2^k` a constant below 5000); `double` twice; `b2n` none; any other function of Rocq's libraries past the limit, so no site holds it and the program is refused at once.  A helper of the program by its body written out, as the check writes it out (step 83's `__nch__wy`); a function giving back a counter with no bound, or a recursive function of the program that is no such row, past the limit.  `nc_c` and `nc_ok` take the environment and the rows for it.
- *The check* (`KQRWf.v`, `nc_opf`): `nc_log2_le`, `nc_sqrt_le`, `nc_gcd_le`, `nc_b2n_le` beside step 102's facts.
- *Left, with cells*: a sum with a power or a `lcm` of a counter, by design as for a plain counter (`A_c2_nat_square`, `A_zi_lcm`: a number that may need more than a word), refused at once, with `log2` and `gcd` as controls; a sum eight times its counters (`cnt n a s + hk7 n`: past a word from `2^60`, as `shiftl` by 3) and one with a doubling (`A_zb_s_power`'s reason), by design, with `hk2` as control; `setbit` by 13 or more, whose constant `2^k` is from 5000 on: step 102's follow-up of a constant in `Z`.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zt_*`, 16: such a counter in a sum with `log2`, `sqrt`, `gcd`, `b2n`, an `if`, a product, a power, `lcm`, `setbit` by 20, helpers of the program adding one, two and seven times, a doubling; `log2` and `sqrt` of such a counter in a sum; a sum with `log2` in a test.

**Step 103, a sum around a counter a function gives back, with an operation the check knows nothing of — the result (2026-11-10).**  Built as designed:
- *The reader* (`KQRReify.v`): `nc_opc`, the count of a call in a site; `kn_c_setbit`, `kn_c_double`, `kn_c_b2n`; `nc_c` and `nc_ok` take the environment and the rows.  *What is proved* (`KQRWf.v`): `nc_log2_le`, `nc_sqrt_le`, `nc_gcd_le`, `nc_b2n_le`, in `nc_opf`.
- *Measured*: `cnt n a s + Nat.log2 n` proved in 3.8 s where there was no answer in 120 s; the power, the `lcm`, the `setbit` by 20, the helper seven times and the doubling refused in about 2 s.  No cell of step 102's or of steps 82, 83, 100, 101's families changed.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 102's files / these): `HWP_kernel` 2.93 / 2.94 s, `HWP_own` 1.99 / 1.99, `HWP_irqnow` 1.66 / 1.66 — the same.
- *The C*: the 99 programs byte-identical.
- *Cells*: 16 more: 11 proved; by design, each with controls: `A_zt_sum_pow`, `A_zt_sum_lcm` (`A_zt_sum_log2`, `A_zt_sum_gcd`), `A_zt_sum_helper_seven`, `A_zt_sum_doubling` (`A_zt_sum_helper_two`); gap `A_zt_sum_setbit_big` (a constant `2^20`, step 102's follow-up of a constant from 5000 on).
- The C: the 99 programs byte-identical.  The construct table (on `841465a`): **3909 of 4054 through the verified compiler**, 72
  by design, 72 gaps, 1 not Rocq (was 3898 of 4038: 11 of the 16 new cells read, 4 by design, 1 gap; no cell lost).  The gate on
  `841465a`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour
  trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (22 / 22 /
  26 / 20 / 19 / 9 s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within the list;
  `check_trust.py`: `trust unchanged`.  Next: step 104, step 102's follow-up of a counter given back used where its value modulo a
  word is enough, then step 105, a bound's constant from 5000 on.

**Step 104, a counter a function gives back, used where its value modulo a word is enough (§3.5, §12.A, found at step 102) — the design (2026-11-10).**  `ff (Nat.land (tw n) 255) b`, `tw` a doubling: `tw n` is `2^n`, past a word, and has no bound, so step 83's reading does not take it.  But `Nat.land x 255` is the same at `x` and at `x` modulo a word, and a function giving back a counter is read as a row giving exactly that (steps 82, 101).  No bound is needed: where only the value modulo a word of an operand is used, the operand is the row's number.
- *Where* (`nc_lowp`): `land` with an operand below a word (a written number, or what step 83's count keeps below seven times its counters); `testbit` below 63; `even`, `odd`; `mod` by a written power of two.
- *The operand* (`nc_wx`, `nc_trw`): made of `+`, `*`, `S`, a shift left by a written number, `land`, `lor`, `lxor`, `ldiff`, written numbers, variables and functions read as rows, each the same modulo a word (steps 82, 101, 102); read this way where a row in it has no bound, so a program read before keeps its C.  The machine's operations there, folded back by `nc_fold`'s rules for the bit operations (built at step 102 and not kept then: here they are needed).
- *What is proved* (`KQRWf.v`): `nc_land_low` (`Nat.land x y` the same at the row's number where `y` is below a word: both are below `y`, and the same modulo a word by `nr_land`), `nc_land_low_l`, `nc_testbit_low`, `nc_even_low`, `nc_odd_low`, `nc_mod_low` (a divisor of `2^63`), from Rocq's axioms of its machine numbers; `nc_step` takes them where `nc_E`, which needs a bound, does not hold.
- *A `let` of such a counter* (`let c := tw n in .. Nat.land c 255 .. Nat.odd c ..`): held as the row's number where every use of it is such a use, as step 83 holds a let of a bounded one; `nc_ulow` checks each use: inside such an operand, at its operations, not inside a row's arguments.
- *The walks* (`y_all`) run where the program has a function read as a row, with a bound or not; *`kitc.py`* sets up step 83's check where there is such a use and no bound.
- *Left, with cells*: such a counter's whole value (a `land` of two of them, `mod 10`, bit 63): a number past a word, by design, with `land`, `mod 64`, `testbit 3` as controls; a bound's constant from 5000 on used as itself (`ff (cbm n n) a`): step 102's follow-up.  Step 102's `A_zs_const_mid` and `A_zs_big_const`, used inside `land`, need no bound now.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zu_*`, 23: a doubling inside `land` with a written number on either side and with a parameter, of two such, `testbit` 3 and 63, `even`, `odd`, `mod 64`, `mod 10`; with `+`, `*`, `lxor`, `shiftl` inside; with a bounded row beside; a quadratic; a bound's constant of 1228500 inside `land` and as itself, of 76500 as itself; in a test, a `let` named once and twice, a recursion.

**Step 104, a counter a function gives back, used where its value modulo a word is enough — the result (2026-11-10).**  Built as designed:
- *The reader* (`KQRReify.v`): `nc_rows`, `nc_rowa`, `nc_wx`, `nc_low`, `nc_pow2`, `nc_lowp`, `nc_ulow`, `nc_trw`; the sites and the lets in `nc_sub` and `nc_any`; `y_all`'s walks where the program has a row.  *`kitc.py`*: step 83's check set up where there is such a use and no bound.
- *What is proved* (`KQRWf.v`): `nr_ldiff_l`, `nc_low_of`, `nc_zlow`, `nc_land_low`, `nc_land_low_l`, `nc_testbit_low`, `nc_odd_low`, `nc_even_low`, `nc_mod_low`; `nc_fold`'s rules for the bit operations; `nc_low_rw` in `nc_step`.
- *Found while building*: `2^63` written as a `nat` in a lemma made the kernel compute it in unary (F77): the lemmas are said in `Z`, through `nr_land` and `nc_E`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 103's files / these, with the lets; the machine under a desktop's load, both about a tenth slower than step 103's measurement): `HWP_kernel` 3.24 / 3.24 s, `HWP_own` 2.18 / 2.21, `HWP_irqnow` 1.85 / 1.85 — the same within the load's noise (rounds of one tree differ by up to 0.13 s).
- *The C*: the 99 programs byte-identical.
- *Cells*: 23 more: 18 proved; by design, each with controls: `A_zu_land_two`, `A_zu_mod_ten`, `A_zu_testbit_63` (`A_zu_land`, `A_zu_mod_pow2`, `A_zu_testbit`); gaps `A_zu_big_direct`, `A_zu_mid_direct` (a bound's constant from 5000 on used as itself, step 102's follow-up).  Two gaps read: `A_zs_const_mid`, `A_zs_big_const`.
- The C: the 99 programs byte-identical.  The construct table (on `ba331f2`): **3929 of 4077 through the verified compiler**, 75
  by design, 72 gaps, 1 not Rocq (was 3909 of 4054: 18 of the 23 new cells read, 3 by design, 2 gaps; 2 gaps read; no cell lost).
  The gate on `ba331f2`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined
  behaviour trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow`
  (22 / 22 / 25 / 19 / 20 / 9 s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within
  the list; `check_trust.py`: `trust unchanged`.  Next: step 105, step 102's follow-up of a bound's constant from 5000 on.

**Step 105, a bound's constant from 5000 on, and a written number from 5000 on, where a counter given back is used (§3.5, §12.A, step 102's follow-up) — the design (2026-11-10).**  `cbm k m <= k + m + 1228500`: step 102 kept a bound only below 5000, its statement carrying the constant as a chain of successors, and step 83's count of a site took its multiples only, the constants below 5000 fitting in the room the counters' bounds leave.  A larger constant, or a number written from 5000 on in a site (`cnt n a s + 100000`), wants the constant counted.
- *The bound's constant in `Z`* (`nbf`, `nb_*`): in the reader, a number of `Z`; in the statement, below 5000 the chain Rocq writes, from 5000 on `Z.to_nat` of the number (`nb_cst`, `z_tm`), which `lia` reads; a written number from 5000 on read by step 94's `nu_z` (`nb_valz`), in a row's text too (`nr_tr`: the machine's literal).
- *The count of a site* (`nc_cd`): its multiples and its constant, `nc_c` its first part, so a decision made before is the same; a let's variable carries both.  *The fit* (`nc_fits`): the constant below `2^63`, `2^62`, `2^61` with the own bound, `2^59` with the own bound, at none, one, two, three to seven multiples, the counters being below `2^62` and below the next function's by `2^20`; two multiples with a constant above `2^20` ask for the own bound (`nc_needo`), as three to seven do.
- *What is proved* (`KQRWf.v`): step 94's `nu_z` and its proof again, since `KQRWf.v` comes before `KQR.v` (`nr_du_z`, `nr_hu_z`, `nr_nu_z`, `nr_nu_z_ok`); `nr_numf` gives `lia` a written number's value in `Z`, in `nb_step` and `nc_side`; `kq_nr` computes it in a row's equation (`nr_ofnum`); `setbit`'s bound in `Z` (`nc_setbit_lez`), where it was a unary `2^k`.
- *Left, with a cell*: such a counter plus a number past a word less one (`cnt n a s + 9223372036854775807`): past a word, by design, with `cnt n a s + 100000` as control.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zv_*`, 8: a written number from 5000 on in a site and in a row's text, alone and in a sum; two counters with a constant of 2000000; three; a `let`; a test; one past a word.  Step 104's `A_zu_big_direct`, `A_zu_mid_direct` and step 103's `A_zt_sum_setbit_big`, gaps of this follow-up, are read.

**Step 105, a bound's constant and a written number from 5000 on, where a counter given back is used — the result (2026-11-10).**  Built as designed:
- *The reader* (`KQRReify.v`): `nbf`'s constant in `Z`; `nb_valz`, `nb_cst`, `pos_tm`, `z_tm`; `nc_pmin`, `nc_padd`, `nc_opd` (where step 103's `nc_opc` was), `nc_cd`, `nc_c` its first part, `nc_needo`, `nc_fits`, `nc_lo`; `nv` with pairs; `nr_tr` reads a written number from 5000 on.
- *What is proved* (`KQRWf.v`): `nr_du_z`, `nr_hu_z`, `nr_nu_z`, `nr_du_z_ok`, `nr_hu_z_ok`, `nr_nu_z_ok`, `nr_ofnum`, `nr_numf`; `kq_nr`'s rule for such a number; `nc_setbit_lez`.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 104's files / these; the machine under a desktop's load, as at step 104): `HWP_kernel` 3.18 / 3.15 s, `HWP_own` 2.14 / 2.13, `HWP_irqnow` 1.80 / 1.79 — the same.
- *The C*: the 99 programs byte-identical.
- *Cells*: 8 more: 7 proved; by design, with its control: `A_zv_add_word` (`A_zv_add_big`).  Three gaps read: `A_zu_big_direct`, `A_zu_mid_direct`, `A_zt_sum_setbit_big`.
- The C: the 99 programs byte-identical.  The construct table (on `fa1247e`): **3939 of 4085 through the verified compiler**, 76
  by design, 69 gaps, 1 not Rocq (was 3929 of 4077: 7 of the 8 new cells read, 1 by design; 3 gaps read; no cell lost).  The gate
  on `fa1247e`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined
  behaviour trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow`
  (22 / 22 / 25 / 19 / 19 / 9 s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within
  the list; `check_trust.py`: `trust unchanged`.  Next: step 106, a value of a type holding a counter built and taken apart in the
  text, then step 107, the laws of a data type with many constructors in time.

**Step 106, a value of a type holding a counter, built and taken apart in the text (§3.5, §12.A; the gaps `A_q_nat_field`, `A_fx_nat_field`) — the design (2026-11-10).**  `Uint63.of_nat (ct (bump (mkcn n a)))`, `Record cn := mkcn { ct : nat; vl : int }`, `bump` a helper giving back a `cn`: the value is built and taken apart in the text, and nothing of it needs to exist at run time (§0.5), but a record is its fields only where they are numbers (D15), and a counter as a field of a value is read nowhere yet.  Where the value is built in the text, its counter is the field's expression: taken there.
- *Where* (`nf_red`): a match on a type holding a counter (a constructor with a counter field, `nf_ind`, or a pair or an option at `nat`), a projection of the program's on such a type, `fst`, `snd` of a pair at `nat`, whose value becomes a constructor once the program's helpers on the way are written out (`um_red`): reduced there.  A type with no counter field, as before, so a program read before keeps its C.
- *What is proved*: nothing new; the program's equation with its reading is by conversion (step 68's `own_step`).
- *Left*: a value holding a counter given back by a recursion, passed as a parameter, or kept in a memory: the gaps `A_z_o_*`, `A_q_st_mem_iter`, `A_fx_nat_pair`, as before.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zw_*`, 10: a record's counter field after a helper, in a match, as a budget; a record in a record; a pair built and matched, `fst` and `snd` of one; an option; a data type with a counter field, directly and from a helper; a record held in a `let`; a choice of constructors.  Eight of them were read before this step (measured on step 105's reader); they pin those places for counters.

**Step 106, a value of a type holding a counter, built and taken apart in the text — the result (2026-11-10).**  Built as designed:
- *The reader* (`KQRReify.v`): `nf_ind`, `nf_red`, applied to each function's body in `y_all` before the rows' rewriting.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 105's files / these; the machine under a desktop's load): `HWP_kernel` 3.03 / 3.02 s, `HWP_own` 2.05 / 2.07, `HWP_irqnow` 1.71 / 1.72 — the same.
- *The C*: the 99 programs byte-identical.
- *Cells*: 10 more, all proved (two of them read by this step, eight pins of places read before).  Two gaps read: `A_q_nat_field`, `A_fx_nat_field`.
- *Found*: `A_q_byte_lit` (a match on a `byte`) took about 100 s, there before these steps; the cause measured (§12.F), the next step.
- The C: the 99 programs byte-identical.  The construct table (on `6f6855a`): **3951 of 4095 through the verified compiler**, 76
  by design, 67 gaps, 1 not Rocq (was 3939 of 4085: the 10 new cells read; 2 gaps read; no cell lost).  The gate on `6f6855a`, the
  walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour trapped 63 / 63,
  `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (22 / 22 / 25 / 19 / 20 / 10
  s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within the list; `check_trust.py`:
  `trust unchanged`.  Next: step 107, the laws of a data type with many constructors in time (§12.F).

**Step 107, the laws of a data type with many constructors, in time (§7, §12.F, found at step 106) — the design (2026-11-11).**  `match x with x41 => 1 | _ => 0 end` on a `byte`: Rocq writes the `_` as the other 255 constructors, and the program took about 100 s to compile, 88 of them in one law of the type's representation (`rb_tag`, proved per program by `KQR.kq_rbt_case`).  Measured: each of its 256 arms takes 1 ms at its own tag; the loop that reaches arm k (`destruct c as [|c]`) leaves the tag as `S (.. (S O))`, and the representation's comparison of the tag word `ofn c` with each constructor's converted that unary number again, so arm k cost k levels of the 256-branch match: cubic in the constructors.  Simplifying the whole goal at each step instead unfolds the representation and runs out of memory.
- *The arm* (`KQR.kq_rbt_arm`): the tag's machine number computed once (`vm_compute` of `ofn k`, put in by `change`), so its comparisons are of literals.  A tactic: no statement, no theorem and nothing assumed changes.
- *Measured*: `A_q_byte_lit` 8.7 s for the whole program (about 100 s before); a type of few constructors, as before.
- *The C*: the same, since only a proof changes.
- *Cells*: none new; `A_q_byte_lit` is the measurement, the table and the gate the check that every law of every program still proves.

**Step 107, the laws of a data type with many constructors, in time — the result (2026-11-11).**  Built as designed:
- *`KQR.v`*: `kq_rbt_arm` computes the tag's machine number first.
- *Measured* (on one machine, the program alone): `A_q_byte_lit` 8.7 s for the whole program, about 100 s before (over 120 s on step 101's files); its law `rb_tag` 1.8 s, 87.8 s before.  The data-type families run alone (288 cells), as before, the slowest cell now `A_q_byte_lit`.
- *The C*: the 99 programs byte-identical.
- *Cells*: none new; the table the same as step 106's, cell for cell.  Its first run, 12 cells at a time, stopped when the laptop's container machine ran out of memory; run again at 6, as before (the run's record, not the work's).
- The C: the 99 programs byte-identical.  The construct table (on `603c071`): **3951 of 4095 through the verified compiler**, 76
  by design, 67 gaps, 1 not Rocq (was 3951 of 4095: the same, cell for cell).  The gate on `603c071`, the walk switched off:
  `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour trapped 63 / 63, `-O0` 63 / 63,
  `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (22 / 22 / 25 / 19 / 19 / 9 s); **109
  programs through the verified compiler, 0 refused**, their 109 end theorems each within the list; `check_trust.py`: `trust
  unchanged`.  Next: step 108, a local mutual fixpoint.

**Step 108, a local mutual fixpoint (§3.5, §12.A; the gap `A_l_fix_mut`) — the design (2026-11-11).**  `(fix f (m : nat) (x : int) : int := .. g .. with g (m : nat) (x : int) : int := .. f .. for f) n a`: a local fixpoint is read where it is one (steps 31, 79), a mutual block where it is a program's (step 45), a local mutual block nowhere.
- *The lifting* (`lm_lift`, in `lift_all`, as step 54 lifts a pattern's let): a local mutual block with no variable of the function in it becomes one function of the reader's own per member, each `fix .. for` that member, the block's binders named as those functions, which is how step 45 finds a block's members (`mem_kn`); the place where the block stood, the chosen member's function.  The same term up to delta.  A Fixpoint's own block is not lifted, its bodies are walked.
- *The reading*: the members are made for the proof as the lifted functions are, from `lift_all`'s table, but are no copies of a template: `reify_prog2c` sets them apart from the table it looks a call up in (`lm_ent`) and adds them to what it makes at the end.  The function's declaration is replaced where it stands (`set_decl`), not shadowed, so step 31's look for local fixpoints, which reads every declaration, sees the lifted body.
- *Left, with cells*: a block naming a variable of the function (`A_zy_capture`, a parameter; `A_zy_capture_let`, a let): its members want that variable as a parameter, given in each call (lambda lifting), and a variable bound by a match has no type in the term to give it, a §12.A follow-up; a mutual block giving back a counter (`A_zy_counter`, and at the top level `A_zy_top_counter`, there before this step): step 82's rows are of single functions, a §12.A follow-up.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zy_*`, 10: three members, two blocks in one function, the block's other member, inside a recursion, with a memory, giving back booleans in a test, giving back a counter locally and at the top level, naming a parameter and a let.

**Step 108, a local mutual fixpoint — the result (2026-11-11).**  Built as designed:
- *The reader* (`KQRReify.v`): `lm_lift`, in `lift_all`; `set_decl`; `lm_ent`, and `reify_prog2c`'s table of copies without the lifted members, which it makes at the end.
- *Found while building* (each by probing the reader's steps on the cell): the program's own top-level block was lifted at first (a pinned reading of `KQRReify.v`, `qmut`, caught it); the members were not found until their binders were named as the functions made; the table of copies took a call of a member as a call of a template's copy; the shadowed declaration was first kept out of step 31's look by reading each name's visible one, which costs a look-up per declaration, quadratic in them, and the kernels' reifier step measured slower (`HWP_irqnow` 1.69 to 1.76 s): the declaration is replaced in place instead.
- *The reifier's step on the kernels' programs* (one machine, one core, interleaved, three rounds, the fastest, F62, in clean copies of both trees; step 106's files / these; the quiet run): `HWP_kernel` 2.95 / 2.97 s, `HWP_own` 2.02 / 2.03, `HWP_irqnow` 1.69 / 1.76 — the walk for a local mutual block in each of the reading's tries, a §12.F item; runs under a desktop's load since gave the same difference.
- *The C*: the 99 programs byte-identical.
- *Cells*: 10 more: 6 proved; gaps `A_zy_capture`, `A_zy_capture_let` (a block naming a variable of the function), `A_zy_counter`, `A_zy_top_counter` (a mutual block giving back a counter, there before), two §12.A follow-ups.  One gap read: `A_l_fix_mut`.
- The C: the 99 programs byte-identical.  The construct table (on `e2d5b56`): **3958 of 4105 through the verified compiler**, 76
  by design, 70 gaps, 1 not Rocq (was 3951 of 4095: 6 of the 10 new cells read, 4 gaps; 1 gap read; no cell lost).  The gate on
  `e2d5b56`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour
  trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (23 / 23 /
  25 / 21 / 20 / 10 s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within the list;
  `check_trust.py`: `trust unchanged`.  Next: §12.A's follow-ups of step 108 (a local mutual block naming a variable; a mutual
  block giving back a counter), and §12.F's look once per program.

**Step 109, the look for a local mutual block once per program (§7, §12.F, found at step 108) — the design (2026-11-11).**  Step 108 walks every function's body for a local mutual block in each of the reading's tries, and `HWP_irqnow`'s reifier step measured about 0.1 s slower.  The reading already makes one walk of every declaration: step 31's look for a local fixpoint (`lf`).
- *The order* (`reify_prog2c`): that look made before the lifting (`lf0`); where it finds no local fixpoint, nothing is lifted and it is not made again after; where it finds one, both as at step 108.  So every decision is step 108's, and a program with no local fixpoint makes one walk fewer than at step 107.
- *`rec_info2`*: it lifts only where the reading made a member of a lifted block, which it sees in what the reading made, with no walk.
- *The C*: the same, cell for cell.
- *Cells*: none new; the kernels' reifier step is the measurement.

**Step 109, the look for a local mutual block once per program — the result (2026-11-11).**  Built as designed:
- *The reader* (`KQRReify.v`): `lift_all` takes whether to look; `reify_prog2c`'s `lf0` and `lfl`; `rec_info2` looks only where the reading made a lifted block's member.
- *Checked on the work laptop* (the repository at step 108 with this reader, the cells of step 108 and of the local fixpoints, the mutual blocks, the Sections, the records of functions: 485): every verdict step 108's.
- *The reifier's step on the kernels' programs* (on the work laptop, one core, interleaved, three rounds, the fastest, F62, in clean copies of two trees, the repository with step 107's reader / with this one): `HWP_kernel` 3.39 / 3.37 s, `HWP_own` 2.46 / 2.40, `HWP_irqnow` 2.04 / 2.05 — the same: step 108's follow-up accepted.  The laptop's core is not this record's earlier machine, so these numbers are not compared with theirs.
- *The C*: the 99 programs byte-identical.
- *Cells*: none new; the table the same as step 108's, cell for cell, run 3 cells at a time beside the laptop's other work.
- The C: the 99 programs byte-identical.  The construct table (on `3f1bef1`): **3958 of 4105 through the verified compiler**, 76
  by design, 70 gaps, 1 not Rocq (was 3958 of 4105: the same, cell for cell).  The gate on `3f1bef1`, the walk switched off:
  `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour trapped 63 / 63, `-O0` 63 / 63,
  `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (23 / 22 / 25 / 20 / 20 / 9 s); **109
  programs through the verified compiler, 0 refused**, their 109 end theorems each within the list; `check_trust.py`: `trust
  unchanged`.  Next: step 108's §12.A follow-ups, a local mutual block naming a variable of the function and a mutual block giving
  back a counter.

**Step 110, a local mutual fixpoint naming variables of the function, and a mutual block under parameters (§3.5, §12.A; found at step 108) — the design (2026-11-12).**  `(fix f (m : nat) (x : int) : int := .. g q (x + a) .. with g .. for f) n b`, the block naming `a`, a parameter of `go`: step 108 lifts a block that names nothing of its function.  Rocq writes a Section's mutual `Fixpoint` with a `Variable` as the same shape at the top level, `ev := fun k => fix ev .. with od .. for ev`, which no cell had and nothing read.
- *The lifting* (`lm_lift`): a block naming variables of the function is lifted under the variables it names, and those their types name, alone (`lm_need`), renumbered: each member `fun (x1 : T1) .. (xk : Tk) => fix .. for` that member, the block's place that member applied to those variables and to its own parameters (`fun m x => M x1 .. xk m x`, one beta step each where the block is applied, so `(fix ..) n b` becomes `M x1 .. xk n b`; a block that is a function's value under a `let`, `fun k => let y := .. in fix ..`, then floats as the functions read do, `fun k m x => let y := .. in ..`).  Beta steps give back the user's block, so the function's text is the same term up to delta and beta, which is what its check by conversion needs.  The variables are those a `fun` or a `let` binds, whose types the term gives, and those a `match` binds, whose types are their constructor's arguments with the match's parameters put in (`br_ctx`).  A block naming a fixpoint around it is left: that variable is a function.
- *Measured before deciding* (on the work laptop, the reader of this step's first form): members made as one fixpoint taking the variables first (`vm_norm`'s construction, as a Section's single fixpoint is read) were read, and the kernel refused the function's check: `(fix f' a b s m x := ..) a b s n b` and the user's `(fix f m x := ..) n b` are two fixpoints of different arities and convert nowhere.  The first form also gave the block every variable inside the outermost it named, so a variable a match binds between them stopped the lifting (`A_zz_in_rec`), and the members took parameters they never read.
- *The reading* (`reify_prog2c`, `blk_view`): a member whose body is a mutual block under parameters, a lifted block's or a Section's, is read with its block as step 45 reads one, through one block of them all (`vm_normm`, `vm_norm`'s construction for a block: each member takes the parameters first, its calls of the others give them on); the members stay as they are.  The block's meaning names each member's view (`read_part`): for a block under parameters, every member from one member's body with the fixpoint's index changed (a member no constant names is not in the quoted environment: a Section's `od` when only `ev` is called), for a block at the top level the block's fixpoint, as before; so the views convert with the members by delta and beta.  Such a constant of the program's file is one of its functions (`is_fn`), not a helper written out where it is called, as a definition with a single fixpoint under parameters is; so is a definition with a local mutual block in it, as one with a pattern's `let` is (step 54), so its block is lifted, not written out unread; a constant's own block under its parameters is not lifted (`own_blk`), its bodies are walked with the parameters' types.  The lifted members are made before what the reading makes (step 41's wrappers name them).  The look for a local mutual block in a helper is made only where the program has a local fixpoint (step 31's look, made before the program's functions are gathered, as step 109 made it before the lifting): made for every helper, a walk of each one's body, it measured `HWP_irqnow`'s reifier step 2.03 to 2.11 s.
- *The C*: a program read before, byte-identical.
- *Left, with cells*: a block calling the fixpoint it stands in (`A_zz_in_fix_call`): its members would take that function as a parameter, a §12.A follow-up.
- *Cells*: `A_zz_*`, 14: two variables, the memory, a counter, a boolean, a record, inside a recursion, a match's variable named and not, beside a local fixpoint, in a helper, given to a function unapplied, a Section's mutual `Fixpoint` with a `Variable` and with a `Let`, a block calling the fixpoint around it.

**Step 110, a local mutual fixpoint naming variables of the function, and a mutual block under parameters — the result (2026-11-12).**  Built as designed:
- *The reader* (`KQRReify.v`): `lm_lift` with the variables' types (`ctx`, `br_ctx`), `lm_need`, the place eta-expanded (`lm_pis`) and beta-reduced where applied (`lm_beta`); `blk_view`, `is_blk`, `own_blk`, `relams`, `vm_normm`; `is_fn` takes a block under parameters and a definition with a local mutual block (`lm_has`, moved before it); `lift_all` floats a lifted body's lets; `reify_prog2c`'s reading of a block member through `blk_view`; `read_part`'s views from one member's body; the lifted members made first.
- *Found while building* (each by probing the reader's steps on the work laptop): the first form, members taking the variables first, was read and refused by the kernel at the function's check (two fixpoints of different arities do not convert); the members' step-41 wrappers were made before the members; a Section's mutual `Fixpoint` was written out where it is called, as a helper, until `is_fn` took it; then its block function's equation was refused, the view of `od` (which no constant names, so Rocq's quote leaves it out) being the reader's block and that of `ev` the user's, until every view came from one member's body; a Section's `Let` before the block needed the place eta-expanded and floated after the lifting, `float_all` having run before it.  A second laptop run of the first form had not started (the laptop short of memory) and its results were read from the run before: the runner now leaves no results behind a run that does not start.
- *Checked on the work laptop* (the repository at step 109 with this reader, the cells of steps 108 and 110, the Sections, the mutual blocks, the local fixpoints, the records of functions: 570): every verdict step 109's but the cells read.
- *The reifier's step on the kernels' programs* (on the work laptop, one core, interleaved, three rounds, the fastest, F62, in clean copies of two trees, the repository with step 109's reader / with this one): `HWP_kernel` 3.34 / 3.34 s, `HWP_own` 2.37 / 2.38, `HWP_irqnow` 2.04 / 2.02 — the same.  With the look for a local mutual block in a helper made for every helper, 2.03 / 2.11: made only where the program has a local fixpoint.
- *The C*: the 99 programs byte-identical.
- *Cells*: 14 more: 13 proved; gap `A_zz_in_fix_call` (a block calling the fixpoint it stands in), a §12.A follow-up.  Two gaps read: `A_zy_capture`, `A_zy_capture_let`.  The table run 8 cells at a time, the laptop's other work stopped.
- The C: the 99 programs byte-identical.  The construct table (on `9280902`): **3973 of 4119 through the verified compiler**, 76
  by design, 69 gaps, 1 not Rocq (was 3958 of 4105: 13 of the 14 new cells read, 1 gap; 2 gaps read; no cell lost).  The gate on
  `9280902`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour
  trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (23 / 23 /
  26 / 20 / 19 / 9 s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within the list;
  `check_trust.py`: `trust unchanged`.  Next: §12.A's follow-ups, a mutual block giving back a counter (step 108's) and a local
  mutual block calling the fixpoint it stands in.

**Step 111, a mutual block giving back counters (§3.5, §12.A; found at step 108, `A_zy_top_counter`) — the design (2026-11-12).**  `Fixpoint ev (m : nat) : nat := .. S (od q) .. with od (m : nat) : nat := .. ev q ..`, made a number where it is used, `Uint63.of_nat (ev n)`: step 82 reads a function giving back a counter as a row, a number-valued function of its own proved equal at every argument, and its rows are of single fixpoints.
- *The rows* (`nr_rows`): a block whose members all give back a counter, at the top level or under parameters (`blk_view`), gets its rows together, one block of rows: each member's body translated as step 82's (`nr_trm`: its calls of any member of the block are the row block's), each member's row the row block's fixpoint for it, read as step 45 reads a block (`lmy`: such rows are read with their block, not as copies).  A row's number of parameters is its member's (`rp_ar`).
- *The statements*: each member's, the counter first, `F_j kqn xs = of_Z (Z.of_nat (f_j kqn xs))`, and at a counter (`__ra__wy`); proved by one mutual fixpoint over the members' statements at a counter, every hypothesis over every counter as a single row's (`kitc.py`; `KQRWf.nr_stepT`, `nr_step` with the hypotheses' rewriting given).  A member the program never names is no declaration of Rocq's quote, a constant of Rocq's environment all the same, so its statement names it.
- *The C*: a program read before, byte-identical.
- *Left, with cells*: a local block giving back a counter (`A_zy_counter`): the rows are made before the reading lifts a local block, so it has none; a block's counter used as a counter (`A_zx_as_counter`): step 83's bound, of single functions; §12.A follow-ups.
- *Cells*: `A_zx_*`, 10: three members, both members used, the other member, a number parameter, a sum, under a Section's variable, an accumulator, used as a counter, a block of different types (step 62's), inside a recursion.

**Step 111, a mutual block giving back counters — the result (2026-11-12).**  Built as designed, at the top level and under parameters:
- *The reader* (`KQRReify.v`): `nr_trm` (`nr_tr` the case of one member); `nr_rows`' block of rows (`rp_nrb`); `rp_def` leaves such a row as it is; `rp_ar`, a row's number of parameters, its member's; `nr_stmt`'s types from the row's own definition; `nr_at` and `ra_name`, the statement at a counter; `reify_prog2c` reads a block of rows with its block (`lmy`).  *`KQRWf.v`*: `nr_stepT`.  *`kitc.py`*: each member's statement by one mutual fixpoint over the block's statements at a counter; `kq_vm0` and the folded arithmetic where a block's rows are.
- *Found while building* (each by probing the reader's steps on the work laptop): the rows are made before the reading lifts a local block, so a local block giving back a counter has none (a follow-up); a block's rows were taken as copies, which are read as single functions, until they were set apart as a lifted block's members are; a row was looked up by its number of parameters, counted from its body's lambdas, which a block row's body, the row block itself, has none of; the members' hypotheses taken at the counter (a conjunction's) were rewritten back and forth by `nr_step`'s own rewriting with a hypothesis equation, until each was a hypothesis over every counter, one mutual fixpoint; a name of `kitc.py`'s own was overwritten by mine.
- *Checked on the work laptop* (the repository at step 110 with this step's files, the counters given back, the rows, the mutual blocks, the local fixpoints, the parameters: 706): every verdict step 110's but the cells read.
- *The reifier's step on the kernels' programs* (on the work laptop, one core, interleaved, three rounds, the fastest, F62, in clean copies of two trees, the repository with step 110's reader / with this one): `HWP_kernel` 3.06 / 3.03 s, `HWP_own` 2.15 / 2.13, `HWP_irqnow` 1.81 / 1.81 — the same (the laptop's other work stopped, so faster than step 110's numbers on the same machine).
- *The C*: the 99 programs byte-identical.
- *Cells*: 10 more: 8 proved; gaps `A_zx_as_counter` (a block's counter used as a counter), `A_zx_mixed` (a block of different types with a counter), §12.A follow-ups, with `A_zy_counter` (a local block giving back a counter).  One gap read: `A_zy_top_counter`.  The chain the first with the gate's examples and corpus side by side (19 minutes, was 31) and the table 10 cells at a time (45 minutes).
- The C: the 99 programs byte-identical.  The construct table (on `912136f`): **3982 of 4129 through the verified compiler**, 76
  by design, 70 gaps, 1 not Rocq (was 3973 of 4119: 8 of the 10 new cells read, 2 gaps; 1 gap read; no cell lost).  The gate on
  `912136f`, the walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour
  trapped 63 / 63, `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (21 / 21 /
  24 / 18 / 19 / 9 s); **109 programs through the verified compiler, 0 refused**, their 109 end theorems each within the list;
  `check_trust.py`: `trust unchanged`.  Next: §12.A's follow-ups: a local mutual block giving back a counter, a block's counter
  used as a counter, a block of different types with a counter, a local mutual block calling the fixpoint it stands in.

**Step 112, a local mutual block giving back counters (§3.5, §12.A; found at step 111, `A_zy_counter`) — the design (2026-11-12).**  `Uint63.of_nat ((fix ev (m : nat) : nat := .. S (od q) .. with od .. for ev) n)`: the reading lifts a local block (steps 108, 110), and a block giving back counters is read through its rows (step 111), which are made before the reading, on the program as written (`y_all`), where the block has no members yet.
- *The lifting first* (`y_all`): the local blocks lifted as the reading lifts them, before the rows are made, the members named for the rows' table (`__wy`, `lift_all_s`); the rows made over the lifted members as over the program's (`nr_rows`).  A lifted member giving back a counter is read through its row only: made, its rows' statements naming it, not read itself.
- *The statements*: a lifted member's names its body at the arguments, the block as the user's text has it, so that the text's equation with what is read rewrites (the member's constant would need a beta step under the rewrite); a member of the program's own names its constant, as the text does.
- *The C*: a program read before, byte-identical.
- *Cells*: `A_zx_loc_*`, 5: naming a variable of the function, three members, in a helper, both members used, a number parameter.

**Step 112, a local mutual block giving back counters — the result (2026-11-12).**  Built as designed:
- *The reader* (`KQRReify.v`): `lm_lift`'s suffix and `lift_all_s` (`lift_all` its case of none); `y_all` lifts first; `nr_rows` over a lifted member; `reify_prog2c` reads no lifted member giving back a counter (`lmyk`); `nr_src`, a row's statement's source.
- *Found while building* (each by probing the reader's steps on the work laptop): the lifted members, taken out of the table as blocks are, were read themselves and refused, a counter given back being read through a row only; the text's equation with what is read (the function in its place, `go__wy`) did not rewrite with a row's statement that named a member taking the variables it captures, until the statement named the member's body at the arguments.
- *Checked on the work laptop* (the repository at step 111 with this reader, the families of step 111's check and the new cells: 711): every verdict step 111's but the cells read.
- *The reifier's step on the kernels' programs* (on the work laptop, one core, interleaved, three rounds, the fastest, F62, in clean copies of two trees, the repository with step 111's reader / with this one): `HWP_kernel` 3.18 / 3.18 s, `HWP_own` 2.24 / 2.24, `HWP_irqnow` 1.88 / 1.90 — the same.
- *The C*: the 99 programs byte-identical.
- *Cells*: 5 more, all proved.  One gap read: `A_zy_counter`.
- The C: the 99 programs byte-identical.  The construct table (on `1041d8d`): **3988 of 4134 through the verified compiler**, 76
  by design, 69 gaps, 1 not Rocq (was 3982 of 4129: the 5 new cells read; 1 gap read; no cell lost).  The gate on `1041d8d`, the
  walk switched off: `make.sh` `core-ok`; examples 64 / 64, 63 / 63 freestanding; the same C: undefined behaviour trapped 63 / 63,
  `-O0` 63 / 63, `ccomp` 60 / 60 and 3 not built with it; corpus 36 / 36; the five kernels and `grow` (27 / 28 / 33 / 25 / 26 / 11
  s, taken while another check of this work ran on the same machine, so not a measurement of the kernels); **109 programs through
  the verified compiler, 0 refused**, their 109 end theorems each within the list; `check_trust.py`: `trust unchanged`.  Next:
  §12.A's follow-ups: a block's counter used as a counter, a block of different types with a counter, a local mutual block calling
  the fixpoint it stands in; then the other categories of §3.5.

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
python3 proved/kitc.py NAME ...         # the verified compiler: read, check by conversion, print the C, build bin/P_NAME
python3 proved/kitc.py prog.v [--main=F]  # the same from an ordinary Rocq file: no main, the arguments from F's signature (the last function by default)
python3 proved/kitc.py --no-proof --no-build NAME   # what the reifier reads, what it refuses (with its reasons)
python3 proved/kitc.py --walk NAME      # the retired route (translator + walk), the yardstick a program is timed against
python3 proved/kitc.py --walk --emit-first NAME  # the same, with the C and the binary first and the proofs behind
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
- `proved/check_trust.py --gate LOG` says `trust unchanged`: a difference is a stop (§13.9), never a line to write up; it compares the
  route's list and, since step 96, what each program's end theorem rests on (the `END-ASSUM` lines the gate's scripts print);
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

**Add a machine operation:** only for what passes §0.3's test, no definition except the machine: it is an assumption, the owner's decision first (§13.9), its line in `proved/TRUSTED.txt` in the same commit.  What Rocq can state gets a Rocq function and a proof instead.  The law proved for the model shows the laws do not contradict each other and says nothing about the C.  The primitive in `KQRun.v`; its law in `KQSpec.v` and the law proved for the model in
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

- The construction exists (translator rule, proof, library, operation) — not a description of it — **in its general form**:
  every place and type the construct can appear in, each with its cell in the table.  A narrower version is not done.
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
| make an operation of arithmetic a machine operation with a C body, because a CPU has an instruction for it or because Rocq's axioms "only relate it" | it is logic, and the C body is unproved code of ours; relating it is enough to prove a definition equal (F66) | a Rocq function proved equal; where the axioms are silent add no fact: compute a closed term, read a test in the text, or refuse with the reason |
| write up a difference in the trusted base in the record and carry on | a difference is a decision of the owner's that nobody asked for (F66) | stop; `proved/check_trust.py` makes it a stop |
| lower a safety threshold (disk guard, timeout) quietly | the owner relies on it | say so, with the reason, in the report |
| put host names, addresses, user names or local paths in the repository | it is public | keep them in local notes only |
| call a refusal "by design" because of the value's type (`option`, a list, a function) | type is not the cause; size and lifetime are (§0.5, F35) | by design only with a pin that shows the cause and a control (§3.6) |
| land a step narrower than its design ("only at the entry", "only in this order", "only one level") and record it as done, with the places it leaves in prose | completeness is strict (owner, 2026-11-02); a limit in prose closes nothing and the table, having no cell for it, then claims "0 gaps" falsely | build the general form; give every place left a table cell in the same commit; if the general form is blocked, stop and ask the owner |
| build an easier substitute for what the owner asked, and record the substitute as the decision | the owner's request silently leaves the plan (F36) | build the substitute if it is a real step, say plainly that it is not what was asked, and keep the request open in §12 |
| call the route "a verified compiler" before §12.V is done, or say the reifier is verified | until `compile` covers a program, that program's theorem comes from the walk; the reifier is never verified, its output is checked (`denote s = f`) | "proved end to end for every compiled program"; after §12.V: "`compile` is a verified compiler for `S`; a program is reified and checked by conversion" |
| verify the translator against MetaRocq's semantics of Rocq | that semantics has no rule for primitive operations (F38) and adds trust | reflection over our own syntax (§1.12) |
| take a settled decision of §10 as covering a case its reason does not cover | the reason is the decision; the wording is only its record | apply the reason; if the wording and the reason disagree, fix the wording and say so in the report |

### 13.9 When to stop and ask the owner

Deleting anything that is not this work's own output; changing a settled decision of §10; **any change to what is assumed: an
`Axiom` or `Parameter`, an operation in `hwop` or `hwfop`, a body in `hw/kq_hw.h`, a line of `proved/TRUSTED.txt`, a difference from
`proved/check_trust.py`** (the owner's standing "no need to wait" does not cover these; removing a line because it is now proved is what
§12.T is for, and is reported); anything touching the owner's other work or machines beyond this work's own containers and files; and any choice
between two designs that §0.9 does not order.  Everything else — design within §0.9, building, measuring, recording — goes ahead.

### 13.10 Reporting

State what ran and what it gave (the gate lines with their numbers), what did not run and why, and what is unverified.  A
number that was estimated is called an estimate.  A failure is reported with its output.  A change that turned out wrong is
recorded in §11 rather than silently reverted.

---

## §14. COMMIT LEDGER (newest first)

Pushed to the public repository up to `1041d8d` (2026-11-03); `git log --oneline origin/main..HEAD` lists what is local.

| Commit | What |
|---|---|
| (this commit) | §12.V: step 112 (a local mutual block giving back counters: the construct table 3988 of 4134, 76 by design, 69 gaps), the gate; §12.A |
| `1041d8d` | `proved/KQRReify.v` + matrix step 112: a local mutual block giving back counters: `y_all` lifts it first, the rows made over its members; 5 cells |
| `3e2db13` | §12.V: step 112's design -- a local mutual block giving back counters: y_all lifts it first |
| `6a182a5` | §12.V: step 111 (a mutual block giving back counters: the construct table 3982 of 4129, 76 by design, 70 gaps), the gate; §12.A: three follow-ups |
| `912136f` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + matrix step 111: a mutual block giving back counters: its rows made together, one block of rows, their statements proved by one mutual fixpoint; 10 cells |
| `ca7c79f` | §12.V: step 111's design -- a mutual block giving back counters, at the top level and under parameters: one block of rows |
| `509ad57` | §12.V: step 110 (a local mutual fixpoint naming variables of the function, a Section's mutual Fixpoint: the construct table 3973 of 4119, 76 by design, 69 gaps), the gate; §12.A: one follow-up |
| `9280902` | `proved/KQRReify.v` + matrix step 110: a local mutual fixpoint naming variables of the function, lifted under those it names; a mutual block under parameters (a Section's mutual Fixpoint) read with its block; 14 cells |
| `25df01b` | §12.V: step 110's design -- a local mutual fixpoint naming variables of the function, lifted under those it names; a mutual block under parameters (a Section's mutual Fixpoint) |
| `ce73e7f` | §12.V: step 109 (the look for a local mutual block once per program: the construct table the same), the gate; §12.F |
| `3f1bef1` | `proved/KQRReify.v` step 109: the look for a local mutual block once per program: step 31's look made before the lifting, nothing lifted where it finds no local fixpoint |
| `ba5d1cd` | §12.V: step 109's design -- the look for a local mutual block once per program |
| `ae78f0d` | §12.V: step 108 (a local mutual fixpoint: the construct table 3958 of 4105, 76 by design, 70 gaps), the gate; §12.A, §12.F: three follow-ups |
| `e2d5b56` | `proved/KQRReify.v` + matrix step 108: a local mutual fixpoint: lifted, each member a function of the reader's own, the block read as at the top level |
| `3921801` | §12.V: step 108's design -- a local mutual fixpoint |
| `56c507c` | §12.V: step 107 (the laws of a data type with many constructors, in time: the construct table 3951 of 4095, the same), the gate |
| `603c071` | `proved/KQR.v` step 107: the laws of a data type with many constructors in time: each arm's tag computed once |
| `54cf7ae` | §12.V: step 107's design -- the laws of a data type with many constructors, in time |
| `577992b` | §12.V: step 106 (a value of a type holding a counter, built and taken apart in the text: the construct table 3951 of 4095, 76 by design, 67 gaps), the gate; §12.F: the laws of a data type with many constructors |
| `6f6855a` | `proved/KQRReify.v` + matrix step 106: a value of a type holding a counter, built and taken apart in the text: taken apart where it is built |
| `382b2b1` | §12.V: step 106's design -- a value of a type holding a counter, built and taken apart in the text |
| `28a1143` | §12.V: step 105 (a bound's constant and a written number from 5000 on: the construct table 3939 of 4085, 76 by design, 69 gaps), the gate |
| `fa1247e` | `proved/KQRReify.v` + `KQRWf.v` + matrix step 105: a bound's constant and a written number from 5000 on, where a counter given back is used: in Z, in the statement and the reader, counted with the multiples at the site |
| `2237437` | §12.V: step 105's design -- a bound's constant and a written number from 5000 on, where a counter given back is used |
| `72b3ee8` | §12.V: step 104 (a counter a function gives back, used where its value modulo a word is enough: the construct table 3929 of 4077, 75 by design, 72 gaps), the gate |
| `ba331f2` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + matrix step 104: a counter a function gives back, used where its value modulo a word is enough: the operand the row's number, no bound asked; land with a number below a word, testbit, even, odd, mod by a power of two, a let of one |
| `244a100` | §12.V: step 104's design -- a counter a function gives back, used where its value modulo a word is enough |
| `cc5e636` | §12.V: step 103 (a sum around a counter a function gives back, with an operation the check knows nothing of: the construct table 3909 of 4054, 72 by design, 72 gaps), the gate |
| `841465a` | `proved/KQRReify.v` + `KQRWf.v` + matrix step 103: a sum around a counter a function gives back is one site only where the check has a bound of each part: the count of a call by its bound, the bounds of log2, sqrt, gcd, b2n, a helper by its body |
| `521f96a` | §12.V: step 103's design -- a sum around a counter a function gives back, with an operation the check knows nothing of |
| `26ddcd3` | §12.V: step 102 (a counter a function gives back, used as a counter inside an operation: the construct table 3898 of 4038, 68 by design, 71 gaps), the gate; §12.A: three follow-ups |
| `f39c112` | `proved/KQRReify.v` + `KQRWf.v` + matrix step 102: a counter a function gives back, used as a counter inside an operation: its bound kept with its constant apart, a written number one constant and a leaf of the walks, a shift left by a written number, an operation inside a sum given its bound, a library definition written out |
| `f64aac0` | §12.V: step 102's design -- a counter a function gives back, used as a counter inside an operation; F83, F84 |
| `c9b37d3` | §12.V: step 101 (a function giving back a counter built by a bit operation: the construct table 3847 of 3984, 66 by design, 70 gaps), the gate |
| `2667bb1` | `proved/KQRReify.v` + `KQRWf.v` + matrix step 101: a function giving back a counter built by a bit operation: land, lor, lxor, ldiff the machine's in a row, each proved the same modulo a word, and their bounds |
| `aa48ac4` | §12.V: step 101's design -- a function giving back a counter built by a bit operation |
| `2c48ca3` | §12.V: step 100 (a function giving back a counter whose recursion goes more than one step down: the construct table 3838 of 3975, 66 by design, 70 gaps), the gate |
| `1de1259` | `proved/KQRReify.v` + `kitc.py` + matrix step 100: a function giving back a counter whose recursion goes more than one step down: the record of such recursions of the environment the reading used |
| `c6d3894` | §12.V: step 100's design -- a function giving back a counter whose recursion goes more than one step down |
| `4a07678` | §12.V: step 99 (a counter chosen by a match on a counter: the construct table 3827 of 3966, 66 by design, 72 gaps), the gate |
| `5bf8172` | `proved/KQRReify.v` + matrix step 99: a counter chosen by a match on a counter, in a counter's place, the test with 0 and the predecessor |
| `a954405` | §12.V: step 99's design -- a counter chosen by a match on a counter |
| `8ef1e56` | §12.V: step 98 (a match on a comparison in any place, `log2_up`, `sqrt_up`: the construct table 3813 of 3953, 66 by design, 73 gaps), the C and its assembly, the gate; F81, F82 |
| `a4ac67c` | `proved/KQRReify.v` + `KQRWf.v` + matrix step 98: a match on a comparison in any place: a library definition calling `Nat.compare` written out first, a match on a choice of constructors floated anywhere, a dead branch closed in the equations |
| `a100b49` | §12.V: step 98's design -- a match on a comparison in any place: log2_up, sqrt_up, Nat.compare in a counter |
| `d6b44c0` | §12.V: step 97 (the bounds of a min and of a subtraction of counters exact: the construct table 3790 of 3932, 66 by design, 75 gaps), the gate |
| `94e26b0` | `proved/KQR.v` + matrix step 97: the bounds of a min and of a subtraction of counters exact, each operand asked to fit |
| `46e4f1f` | §12.V: step 97's design -- the bounds of a min and of a subtraction of counters exact |
| `73dddcb` | §12.V: step 96 (each program's own end theorem, and what it rests on, in the gate: the construct table 3774 of 3915, 64 by design, 76 gaps), the gate; F79, F80; §12.T's follow-up done |
| `e73b49b` | `proved/TRUSTED.txt` + `check_trust.py` step 96: what the programs' end theorems rest on besides the route's, Rocq's own definitions of five primitives the reader writes out, listed (the owner's decision); every name listed used by the route or by a program |
| `ca0513c` | `proved/KQREnd.v` + `kitc.py` + `check_trust.py` + `make.sh` + the gate's scripts step 96: each program's end theorem, the entry's said of the Clight; what it rests on printed and compared with the list |
| `30908ae` | §12.V: step 96's design -- each program's own end theorem, and what it rests on, in the gate |
| `0ae566a` | §12.V: step 95 (a power of two written numbers, its value one number in the C: the construct table 3774 of 3915, 64 by design, 76 gaps), the C, the gate; F78; §12.E's follow-up done |
| `c938ac6` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + matrix + `examples/pow_fix` step 95: a power of two written numbers, its value one number in the C: `CPowL`; the check files unfold the library's functions last; 25 cells |
| `1b3a620` | §12.V: step 95's design -- a power of two written numbers, its value one number in the C |
| `77d6540` | §12.V: step 94 (a counter written as a number, one number in the C: the construct table 3750 of 3890, 62 by design, 77 gaps), the C and its assembly, the gate; F77; §12.E's follow-up |
| `da8f5f1` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + matrix + `examples/lit_fix` step 94: a counter written as a number, one number in the C: `CLit`, `CNumU`, `CMulU`; the check files unfold `ofn` first; 37 cells |
| `8128bb2` | §12.V: step 94's design -- a counter written as a number, one number in the C |
| `564e5a8` | §12.V: step 93 (the recursive functions of Rocq's library on counters: the construct table 3716 of 3853, 60 by design, 76 gaps), the C, the gate; §12.E's follow-up |
| `b8758c7` | `KQRun.v` + `proved/KQR.v` + `KQRReify.v` + `kitc.py` + matrix + `examples/libn_fix` step 93: `Nat.gcd`, `Nat.sqrt`, `Nat.log2` on counters, a call of the kit's function; its signature known by the table of callees |
| `31d8f0e` | §12.V: step 93's design -- the recursive functions of Rocq's library on counters: gcd, sqrt, log2 |
| `347d98a` | §12.V: step 92 (the bit operations of Rocq's library on counters: the construct table 3680 of 3817, 59 by design, 77 gaps), the C, the gate; F76, the trust check made exact; §12.T's follow-up |
| `da6b1d1` | `proved/make.sh` + `TRUSTED.txt` step 92: what every lemma of the route rests on, printed from a file that imports nothing; each assumption listed once by its full name, `compare_spec` and `compares` among them (F76) |
| `af6b6ca` | `proved/KQR.v` + `KQRReify.v` + matrix + `examples/bitn_fix` step 92: the bit operations of Rocq's library on counters, each a case of the compiler's proof; a let in a counter named once |
| `e6e275c` | §12.V: step 92's design -- the bit operations of Rocq's library on counters |
| `cf1639c` | §12.V: step 91 (the printed C says what the Clight says: the construct table 3609 of 3742, 54 by design, 78 gaps), the C, the gate; F75 |
| `95b1f77` | `proved/KQLGen.v` + `KQLProof.v` + `kitc.py` + `examples.sh` + `sup/v4/kq_io.h` step 91: a signed number made unsigned before it is shifted left; the printed C through undefined behaviour traps, `-O0` and `ccomp` |
| `959bc83` | §12.V: step 91's design -- the printed C says what the Clight says, and the tools are asked |
| `64dac81` | §12.V: step 90 (the generated C on its own: the construct table 3608 of 3742, 54 by design, 79 gaps), the C, the gate |
| `925e035` | `sup/free` + `proved/kitc.py` + `examples.sh` + `hw/kq_bare.c` + `hw/grow` step 90: the generated C with no hosted header and no libc, `kq_grow` on the machine |
| `7cb061c` | §12.V: step 90's design -- the generated C on its own: no hosted header, no libc |
| `7f60eb1` | §12.V: step 89 (an ordinary `.v` file, as simply as `lean --c`: the construct table 3609 of 3742, 54 by design, 78 gaps), the C, the gate |
| `ec163ad` | `proved/kitc.py` + `examples.sh` + `vfiles` + `tests/vroute.py` step 89: an ordinary `.v` file, the entry read from its signature |
| `14d30b2` | §12.V: step 89's design -- an ordinary .v file, as simply as lean --c |
| `4869f65` | §12.V: step 88 (the integer types of C: the construct table 3609 of 3742, 54 by design, 78 gaps), the C, the gate; F74 |
| `42c08a7` | `KQRun.v` + `proved/KQW64.v` + `KQLGen.v` + `KQM.v` + `lib/CInt.v` + `lib/CIntSpec.v` + `proved/KQRReify.v` + `kitc.py` + `make.sh` + `matrix` + `examples/cint_fix` step 88: the integer types of C as ordinary functions, what each computes proved, `uint64_t`'s `/` and `%` a case of the generator's proof; 128 cells |
| `6b29fdd` | §12.V: step 88's design -- the integer types of C as ordinary functions, what each computes proved |
| `6b5e6e1` | §12.V: step 87 (a memory in a value of any data type: the construct table 3481 of 3614, 54 by design, 78 gaps, 3 gaps read), the C, the gate; D30, the proof ends at Clight |
| `720c58c` | `proved/KQRReify.v` + `matrix` + `examples/resm_fix` step 87: a memory in a value of any data type; a sixth probe; 51 cells |
| `9eccf19` | §12.V: step 87's design -- a memory in a value of any data type; a sixth probe |
| `b7505f1` | §12.V: step 86 (tests that cannot be moves, many in one expression: the construct table 3428 of 3563, 54 by design, 80 gaps, 2 gaps read), the C, the gate |
| `3ed96d9` | `proved/KQRReify.v` + `kitc.py` + `matrix` + `examples/jn_fix` step 86: tests that cannot be moves, many in one expression; 23 cells |
| `f2c5463` | §12.V: step 86's design -- tests that cannot be moves, many in one expression |
| `1a5ee67` | §12.V: step 85 (a memory inside an option, a helper's choice of a value and a memory: the construct table 3404 of 3540, 54 by design, 81 gaps, 2 gaps read), the C, the gate |
| `875c47b` | `proved/KQRReify.v` + `kitc.py` + `matrix` + `examples/optm_fix` step 85: what a fifth probe found: a memory inside an option, a helper's choice of a value and a memory; 76 cells |
| `59f3bf1` | §12.V: step 85's design -- what a fifth probe found: a memory inside an option, a helper's choice of a value and a memory |
| `c5eaa9b` | §12.V: step 84 (a class or a record of functions given to a recursive function: the construct table 3331 of 3464, 54 by design, 78 gaps, 4 gaps read), the C, the gate |
| `413a349` | `proved/KQRReify.v` step 84: a function given to a class's method is put in |
| `248f2d4` | `proved/KQRReify.v` + `kitc.py` + `matrix` + `examples/cls_fix` step 84: a class or a record of functions given to a recursive function; 38 cells |
| `02c4d50` | §12.V: step 84's design -- a class's instance read as a type, a record of functions given to a recursive function |
| `5d67ece` | §12.V: step 83 (a counter a function gives back, used as a counter: the construct table 3294 of 3426, 53 by design, 78 gaps, 7 cells read), the C, the gate |
| `95d192b` | `proved/KQR.v` + `KQRWf.v` + `KQRReify.v` + `kitc.py` + `matrix` + `examples/cuse_fix` step 83: a counter a function gives back, used as a counter; 70 cells |
| `90820ee` | §12.V: step 83's design -- a counter expression as a counter, its bound proved by induction |
| `1029a00` | §12.V: step 82 (a function giving back a counter: the construct table 3227 of 3356, 49 by design, 79 gaps, 4 gaps read), the C, the gate |
| `b017845` | `proved/KQRWf.v` + `KQRReify.v` + `kitc.py` + `matrix` + `examples/cret_fix` step 82: a function giving back a counter, made a number where it is used; 44 cells |
| `838a52f` | §12.V: step 82's design -- a function giving back a counter, made a number where it is used |
| `0284dba` | §12.V: step 81 (a proof as a parameter, a value with its proof as a parameter: the construct table 3189 of 3312, 49 by design, 73 gaps, 4 gaps read), the C, the gate |
| `6ce4511` | `proved/KQRReify.v` step 81: a helper giving back a sig stays on its own route |
| `0f4e425` | `proved/KQRReify.v` + `kitc.py` + `matrix` + `examples/prfp_fix` step 81: a proof as a parameter, a value with its proof as a parameter; 40 cells |
| `543746b` | §12.V: step 81's design -- a proof as a parameter, a value with its proof as a parameter |
| `e3613d8` | §12.V: step 80 (a memory in a record or a pair: the construct table 3146 of 3272, 49 by design, 76 gaps, 4 gaps read), the C, the gate |
| `d9b85b2` | `proved/KQRWf.v` + `KQRReify.v` + `kitc.py` + `matrix` + `examples/stat_fix` step 80: a memory in a record or a pair, at any place; 48 cells |
| `2b4f456` | §12.V: step 80's design -- a memory in a record or a pair, at any place |
| `c2120b8` | §12.V: step 79 (a value and a memory from the other forms of recursion: the construct table 3098 of 3224, 48 by design, 77 gaps, 6 gaps read), the C, the gate |
| `4000208` | `proved/KQRWf.v` + `KQRReify.v` + `kitc.py` + `matrix` + `examples/sect_fix` step 79: a value and a memory under parameters and from a local fix; 41 cells |
| `86d090f` | §12.V: step 79's design -- what is left of a value and a memory given back |
| `2e29a22` | §12.V: step 78 (a value of several numbers and a memory given back by a recursion: the construct table 3059 of 3183, 45 by design, 78 gaps, 9 gaps read), the C, the gate; F70, F71; D29, §12.H: the floor, the owner's |
| `89fd65c` | `proved/KQR.v` + `KQRWf.v` + `KQRReify.v` + `kitc.py` + `matrix` + `examples/vals_fix` step 78: a value of several numbers and a memory given back by a recursion: through the slot block; 78 cells |
| `3ffde58` | §12.V: step 78's design -- a value of several numbers and a memory given back by a recursion |
| `3d2398a` | §12.V: step 77 (a value and a memory written out: the construct table 2988 of 3105, 43 by design, 73 gaps), the C, the gate; F72; `examples.sh` counts no binary left by an earlier run |
| `67c0d1a` | `proved/KQRReify.v` + `kitc.py` + `matrix` + `examples/drv_fix` step 77: a fourth probe: a value and a memory written out, a program's own notations; 87 cells |
| `3d8a0a5` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` step 77: a projection floated into a choice is no conversion: by the equation |
| `94fb392` | §12.V: step 77's design -- what a fourth probe found: a value and a memory written out |
| `3db0886` | §12.V: step 76 (a value with a proof given back: the construct table 2921 of 3018, 41 by design, 55 gaps, one cell lost), the C, the gate; F69 |
| `64ac544` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + `matrix` + `examples/proof_fix` step 76: a function giving back a value with a proof: `sig`, `sumbool`; 37 cells |
| `1968a99` | §12.V: step 76's design -- a value and a proof given back |
| `26acb1d` | §12.V: step 75 (the bytes in bulk as ordinary functions, §12.T done: the construct table 2882 of 2981, 41 by design, 57 gaps), the C, the gate |
| `4898663` | `KQRun.v` + `KQSpec.v` + `KQModel.v` + `hw` + `proved/KQL.v` + `KQLGen.v` + `KQMSem.v` + `KQMTrans.v` + `KQRReify.v` + `kitc.py` + `TRUSTED.txt` + `matrix` + `examples/bulk_fix` step 75: `hw_copy`, `hw_fill`, `hw_cmp` as loops over a load and a store; three operations and their C bodies removed; 21 cells |
| `f951760` | §12.V: step 75's design -- the bytes in bulk as ordinary functions |
| `7c33817` | §12.V: step 74 (`divs_min_neg1` gone: the construct table 2861 of 2960, 41 by design, 57 gaps), the C, the gate |
| `c79685b` | `KQRun.v` + `proved/KQL.v` + `KQTArith.v` + `KQMTrans.v` + `KQPrim.v` + `KQRReify.v` + `KQRWf.v` + `TRUSTED.txt` + `matrix` step 74: the signed quotient as `kq_divs`, proved; `divs_min_neg1` taken away; 45 cells |
| `db25b11` | §12.V: step 74's design -- the signed quotient: divs_min_neg1 taken away |
| `bf35eb1` | §12.V: step 73 (`head0`, `tail0`, `mulc`, `diveucl_21` proved: the construct table 2825 of 2915, 34 by design, 55 gaps), the C, the gate; F67, F68 |
| `9f620a8` | `KQRun.v` + `hw/kq_hw.h` + `proved/KQPrim.v` + `KQL.v` + `KQLGen.v` + `KQMSem.v` + `KQRReify.v` + `KQRWf.v` + `kitc.py` + `TRUSTED.txt` + `matrix` + `examples/mach_fix` step 73: `head0`, `tail0`, the high half of `mulc`, `diveucl_21` as ordinary functions, proved from Rocq's own axioms; five operations and their C bodies removed; 83 cells |
| `8f3a57d` | §12.V: step 73's design -- head0, tail0, the high half of mulc, diveucl_21 as ordinary functions, proved |
| `858221d` | §12.V: step 72 (a procedure, a test in a monad: the construct table 2756 of 2832, 26 by design, 49 gaps), the C, the gate |
| `dcf40e2` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + `matrix` + `examples/proc_fix` step 72: a procedure and a test in a monad; 24 cells; `KQR.v` unchanged |
| `2d66f8a` | §12.V: step 72's design -- a procedure, a test in a monad |
| `3f2908e` | §12.V: step 71 (a third probe of natural programs: the construct table 2736 of 2808, 25 by design, 46 gaps), the C, the gate |
| `95e32a8` | `proved/KQRReify.v` + `kitc.py` + `matrix` + `examples/monad_fix` step 71: a third probe: a state monad, fixpoints over a literal, primitive projections; 111 cells; `KQR.v` unchanged |
| `bdc2431` | §12.V: step 71's design -- what a third probe of natural programs found |
| `55d6105` | §12.V: step 70 (counters and numbers: the construct table 2641 of 2697, 24 by design, 31 gaps), the C, the gate; `proved/TRUSTED.txt`: three spellings |
| `b682bd8` | `proved/KQR.v` + `KQRReify.v` + `matrix` + `examples/conv_fix` step 70: counters and numbers; 119 cells |
| `34ebaa6` | §12.V: step 70's design -- counters and numbers |
| `0739209` | §0.3's test, D29, F66, §1.10, §12.T, §13: only what has no definition except the machine is assumed; `proved/TRUSTED.txt`, `proved/check_trust.py`; `CLAUDE.md` |
| `f6290ad` | §12.V: step 69 (a function read in another form, its callers told by a lemma: the construct table 2534 of 2578, 19 by design, 24 gaps), the C, the gate |
| `a89c37b` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + `matrix` + `examples/poly_fix` step 69: a function read in another form, its callers told by a lemma; 26 cells; `KQR.v` unchanged |
| `309e6b6` | §12.V: step 69's design -- a function read in another form, its callers told by a lemma |
| `b45dfe3` | §12.V: step 68 (what Rocq's libraries and ordinary text spell otherwise: the construct table 2502 of 2552, 18 by design, 31 gaps), the C, the gate |
| `304ee51` | `proved/KQRReify.v` + `KQRWf.v` + `matrix` + `examples/lib2_fix` step 68: what Rocq's libraries and ordinary text spell otherwise; 87 cells; `KQR.v` unchanged |
| `a1f392f` | §12.V: step 68's design -- type aliases, the library's recursors, Rocq's lists written in the text, tests with a proof |
| `7b23a45` | §12.V: step 67 (values of a fixed size holding booleans, records and data types: the construct table 2425 of 2465, 15 by design, 24 gaps), the C, the gate |
| `c7ff7fc` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix` + `examples/value_fix` step 67: values of a fixed size holding booleans, records and data types; 223 cells |
| `f437907` | §12.V: step 67's design -- values of a fixed size holding booleans, records and data types |
| `e9d25bd` | §12.V: step 66 (counters: `Nat.min`, `Nat.max`, `Nat.sub`, `Nat.div2`: the construct table 2204 of 2242, 15 by design, 22 gaps), the C, the gate |
| `f3878f9` | `proved/KQR.v` + `KQRReify.v` + `matrix` + `examples/cnt_fix` step 66: counters: `Nat.min`, `Nat.max`, `Nat.sub`, `Nat.div2`; four constructs of the counters, each a case of the theorem; 9 cells |
| `d040b2e` | §12.V: step 66's design -- counters: Nat.min, Nat.max, Nat.sub, Nat.div2 |
| `ef3b1f6` | §12.V: step 65 (`head0`, `tail0`, `mulc`, `diveucl_21`: the construct table 2191 of 2233, 15 by design, 26 gaps), the C, the gate |
| `62cc800` | `KQRun.v` + `hw/kq_hw.h` + `proved/KQL.v` + `KQLGen.v` + `KQMSem.v` + `KQRReify.v` + `KQRWf.v` + `kitc.py` + `classify` + `examples/mach_fix` step 65: `head0`, `tail0`, the high half of `mulc`, `diveucl_21` as machine operations |
| `aee51b5` | §12.V: step 65's design -- head0, tail0, the high half of mulc, diveucl_21 as operations of the machine |
| `5592c0f` | §12.V: step 64 (the operations Rocq's axioms define by others: the construct table 2187 of 2233, 15 by design, 30 gaps), the C, the gate |
| `2442197` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + `matrix/gen.py` + `classify.py` + `examples/prim_fix` step 64: `compare`, `addc`, `subc`, `diveucl`, `addmuldiv` by Rocq's own axioms defining them; 12 cells; `KQR.v` unchanged |
| `8e75962` | §12.V: step 64's design -- the operations of Rocq's machine numbers that its own axioms define by others |
| `2649859` | §12.V: step 63 (natural forms from a probe: the construct table 2169 of 2221, 15 by design, 36 gaps), the C, the gate |
| `f1d978e` | `proved/KQRReify.v` + `matrix/gen.py` + `classify.py` + `examples/lib_fix` step 63: natural forms the table had no cell for, from a probe: what Rocq's libraries define, a motive, a cast, a value holding a proof, `unit`; 74 cells; `KQR.v` unchanged |
| `139fc4d` | §12.V: step 63's design -- natural forms the table had no cell for: a probe, what Rocq's libraries define, a motive, a cast, a value holding a proof |
| `c0f9a51` | §12.V: step 62 (a mutual block of different result types: the construct table 2115 of 2147, 15 by design, 16 gaps), the C, the gate |
| `4ed9b94` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + `matrix/gen.py` + `classify.py` step 62: a mutual block of different result types, the others written out in a hub; a member's match that gives a function; 6 cells; `KQR.v` unchanged |
| `8cd569a` | §12.V: step 62's design -- a mutual block of different result types, the other members read through a hub |
| `4bace15` | §12.V: step 61 (the own call under a choice and on a deeper counter: the construct table 2108 of 2141, 14 by design, 18 gaps), the C, the gate; READ THIS FIRST |
| `d3999c8` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + `matrix/gen.py` + `classify.py` + `examples/own_fix` step 61: the function's own call under a choice, the choice floated out; on a deeper counter, a budget of its own; 19 cells; `KQR.v` unchanged |
| `a207dda` | §12.V: step 61's design -- the function's own call under a choice, floated out; on a deeper counter, a budget function; each equal to the user's at every argument |
| `bb8dbc8` | §12.V: step 60 (`Equations`: the construct table 2053 of 2122, 13 by design, 55 gaps), the C, the gate; §4.5, §12.P, D12, READ THIS FIRST |
| `0efd280` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + `matrix/gen.py` + `classify.py` + `examples/equations_fix` step 60: `Equations`: `FixWf` over its functional, its clauses written out, one lemma and one tactic, no axiom; a match on the counter that gives a function; 28 cells; `KQR.v` unchanged |
| `91d188b` | §12.V: step 60's design -- Equations: FixWf over its functional, its clauses written out, one lemma and one tactic; a match on the counter that gives a function |
| `8850a47` | §12.V: step 59 (a function as a parameter of a measure recursion: the construct table 2026 of 2094, 13 by design, 54 gaps), the C, the gate |
| `2ba5d30` | `proved/KQRReify.v` + `kitc.py` + `matrix/gen.py` + `classify.py` + `examples/fun_fix` step 59: a function as a parameter of a measure recursion: a copy per function given, read as the wrapper written out, its theorem the function's equation at the function given; 26 cells; `KQR.v` and `KQRWf.v` unchanged |
| `140148d` | §12.V: step 59's design -- a function as a parameter of a measure recursion: a copy per function given, read as the wrapper written out, its theorem the function's equation at the function given |
| `909e731` | §12.V: step 58 (any measure with a bound: the construct table 2000 of 2068, 11 by design, 56 gaps), the C, the gate; §4.5, D18 |
| `6add419` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + `matrix/gen.py` + `classify.py` + `examples/program_fix_mem` step 58: any measure with a bound: the bound read from the measure, one tactic proves it; a budget in phases above a counter's range; `functional induction` for a `Function`; 18 cells; `KQR.v` unchanged |
| `10f00e2` | §12.V: step 58's design -- any measure with a bound: the bound read from the measure and proved by one tactic; a budget in phases above a counter's range; the binary search as Program Fixpoint |
| `42d96e3` | §12.V: step 57 (`Function`: the construct table 1980 of 2050, 11 by design, 58 gaps), the C, the gate; §4.5, §12.P, D12, READ THIS FIRST |
| `e2a5c2c` | `proved/KQRReify.v` + `KQRWf.v` + `kitc.py` + `matrix/gen.py` + `classify.py` + `examples/function_fix` step 57: `Function`: its plain functional, one tactic over its induction principle, the measure read back through its patterns; a lighter quote; 30 cells; `KQR.v` unchanged |
| `b6967e4` | §12.V: step 57's design -- Function: its plain functional, one tactic over its induction principle, the measure read back through its patterns; a lighter quote; a function as a parameter and a sum of machine numbers left, with their cells |
| `c69897e` | §12.V: step 56 (`Program Fixpoint`, the owner's "level 2": the construct table 1957 of 2020, 11 by design, 51 gaps), the C, the gate; §4.5, §12.P, D12, READ THIS FIRST |
| `cbae7b2` | `proved/KQR.v` + `KQRWf.v` + `KQRReify.v` + `kitc.py` + `make.sh` + `matrix/gen.py` + `classify.py` + `examples/program_fix` step 56: Rocq's own measure recursion: `Program Fixpoint` read as a budget function, equal to it at every argument by one lemma with no axiom; `callee_ok_eq`; 25 cells |
| `8b302ad` | §12.V: step 56's design (Rocq's own measure recursion, `Program Fixpoint`: one lemma from `Fix_sub` to a budget function, no extensionality; no cap in the theorem) |
| `56d7dd3` | §12.V: step 55 (the function's own call in every place: the construct table 1933 of 1995, 11 by design, 50 gaps, 36 of them one class), the C, the gate |
| `417fcc1` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` + `classify.py` step 55: the function's own call in every place: a family of the table, 225 programs; `BbLetRec`; bound where it stands in a body with no memory; `float_op` |
| `f7ae8f7` | §12.V: step 55's design (the function's own call in every place: a family of the table; `BbLetRec`; bound where it stands in a body with no memory; the own call under a choice in an operand left, 36 cells) |
| `2d315a4` | §12.V: step 54 (a family of the table crossing what writes with what is around it: the construct table 1736 of 1762, 11 by design, 14 gaps), the C, the gate |
| `e86d7c8` | `proved/KQRReify.v` + `kitc.py` + `matrix/gen.py` + `classify.py` step 54: a family of the table crossing what writes with what is around it, 591 programs; `unroll`, `lift_ops` |
| `01d17c6` | §12.V: step 54's design (a family of the table crossing what writes with what is around it; an operand that writes under a let or a match, a function of its own) |
| `112ef49` | §3.7, §12.V: step 53 (a second memory parameter: the construct table 1144 of 1169, 11 by design, 13 gaps), the C, the gate |
| `3fc8bcf` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix/gen.py` + `classify.py` + `examples/two_mems` step 53: a second memory parameter: the same memory by a wrapper; a memory never read by `callee_ok_dead`; 37 cells |
| `5dd81f5` | §12.V: step 53's design (a second memory parameter: the same memory by a wrapper, a memory never read by `callee_ok_dead`, both live by design) |
| `864e0be` | §12.V: step 52 (a memory made in place and read inside an expression: the construct table 1116 of 1132, 9 by design), the C, the gate |
| `3b60930` | §12.V: step 52's design, what narrowing it found (the function's own call on the memory a let made) |
| `99d5a45` | `proved/KQRReify.v` + `matrix/gen.py` + `classify.py` step 52: a memory made in place and read inside an expression, bound by a let; the function's own call on the memory a let made, bound; 39 cells |
| `d0f1875` | §12.V: step 52's design (a memory made in place and read inside an expression: bound by a let) |
| `001b5e2` | §11 F65, §0.5, §3.7: the changes `959967b` names, which that commit left out (its edit script stopped on a mismatch and the record went ahead) |
| `959967b` | §11 F65, §0.5, §3.7, §12.V: step 51 (programs across modules and files: the construct table 1079 of 1093, 7 by design), the C, the gate |
| `0b929ef` | `proved/KQRReify.v` + `kitc.py` + `matrix/gen.py` + `classify.py` + `examples/modules` step 51: programs across modules and files: `in_prog`, full names, nothing guessed from names or text, files, a section's let; 107 cells |
| `379bddc` | §12.V: step 51's design (programs across modules and files: in the program, full names, no guessing from names or text, files, sections; a constant with no body the fourth refusal) |
| `684dbda` | §12.V: step 50 (a read of the memory before a write, standing after it: the construct table 977 of 986, 2 by design), the C, the gate |
| `ddfc85b` | `proved/KQRReify.v` + `matrix/gen.py` + `classify.py` step 50: a read of the memory before a write, standing after it, bound before it (`hoist_read`); the pin of linearity moved; 14 cells |
| `e4188df` | §12.V: step 50's design (a read of the memory before a write, standing after it: bound before it, in the reader) |
| `381e3fa` | §11 F64, §12.V: step 48 continued (a call given the pair a let holds, by lifting the let: the construct table 963 of 972, 2 by design), the C, the gate |
| `ffd7312` | `proved/KQRReify.v` + `matrix/gen.py` step 48 continued: a let of a pair used bare lifted to a function of the pair (`lift_pm`, `lift_all`); `KQR.v` unchanged; 10 cells |
| `c632d1e` | §12.V: step 48 continued, a call given the pair a let holds, the design (the let lifted to a function of the pair, no new construct of `S`) |
| `dd55ebd` | §12.V: step 48 continued (the own call not at the end of a boolean or a record that writes, mutual blocks of them: the construct table 953 of 962, 2 by design; the pair a let holds goes on), the C, the gate |
| `9d5ee76` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` step 48 continued: `XBindRB`, `XBindRR`, `xnum`, `ctailxb_ok`; the reifier binds an own call of a boolean or a record, a boolean or a record that writes called at the end read as a bound call; 8 cells |
| `ba62ec6` | §12.V: step 48 continued, the own call not at the end of a boolean or a record that writes, the design (`XBindRB`, `XBindRR`, `xnum`, `ctailxb_ok`) |
| `c4a2005` | §12.V: step 48 continued (templates giving back a boolean or a record that writes: the construct table 943 of 954, 2 by design; the own call not at the end and the pair a let holds go on), the C, the gate |
| `4804dc5` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix/gen.py` step 48 continued: `compile_f_okrxb`, `compile_f_okrxr`, the meanings' independence of the own call; the reader of copies, the binding of a template's call; 2 cells |
| `ac84ef0` | §12.V: step 48 continued, templates giving back a boolean or a record that writes, the design (the copies' theorems for X bodies of booleans and records) |
| `454364a` | §12.V: step 48 continued (functions giving back a record whose body writes: the construct table 939 of 952, 2 by design; the own call not at the end, templates and the pair a let holds go on), the C, the gate |
| `2d66918` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` step 48 continued: `callmw`, `XRetR`, `XBindRM`, `denote_xr`, `ctailxr_ok`, a record whose body writes; the reifier reads it as an X body and looks into a let's bound term for a call to bind; 9 cells |
| `ffd7eed` | §12.V: step 48 continued's record half, the design (the contract keeps the slot block of a record that writes; `XRetR`, `denote_xr`, `ctailxr_ok`; `XBindRM`) |
| `6fd239e` | §12.V: step 49 (two versions of the memory both used: the boundary pinned; the construct table 933 of 943, 2 by design), the gate |
| `5057f75` | `proved/matrix/gen.py` + `classify.py` step 49: the pin `A_par_write_two_data` by design, its control `A_par_write_two_seq`, the fixed side's gaps `A_par_write_in_mem`, `P_mem_both`; 4 cells |
| `3d57a2e` | §0.5, §11 F63, §12.V: step 49's design (two versions of the memory both used: the third refusal by the size of the difference; a pin from the data with its control, the fixed side as gaps) |
| `4d17a62` | §12.V: step 48 continued (functions giving back a boolean whose body writes: the construct table 932 of 939, 1 by design; records and the pair a let holds go on), the C, the gate |
| `f70ad99` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` step 48 continued: `XRetB`, `denote_xb`, a boolean whose body writes, `after_free`; the reifier reads it as an X body; 2 cells |
| `7556d7b` | §11 F62, §12.V: the reifier's timing of steps 44 continued to 48 corrected (the working tree's scanned directories) |
| `dad6b6d` | §12.V: step 48 continued's design (functions giving back a boolean or a record that write the memory; a call given the pair a let holds) |
| `eee39e5` | §12.V: step 48 (a call given a pair, bound, giving back a record: the construct table 929 of 937, 1 by design; the bodies of the other sorts go on), the C, the gate |
| `10a5276` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` step 48: `XBindPR`, its fields from the slot block, `ctailx_ok`'s case; the reifier binds such a call with its record type; 2 cells |
| `45ecac0` | §12.V: step 48's design (calls given a pair inside expressions of every sort) |
| `f52b924` | §12.V: step 47 (calls inside expressions that write the memory or are given a pair: the construct table 926 of 931, 1 by design), the C, the gate |
| `1fab4bb` | `proved/matrix/gen.py`: 4 cells for the places step 47 leaves unread (a call given a pair inside an expression of a function of another sort) |
| `706834b` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` step 47: `XBind`, `XBindR`, `XBindP`, `ctailx_ok`'s cases; the reifier binds such a call first; 9 cells |
| `653b839` | §12.V: step 47's design (calls inside expressions that write the memory or are given a pair) |
| `f9131bd` | §12.V: step 46 (templates of any signature: the construct table 915 of 922, 1 by design), the C, the gate |
| `4283f5d` | `proved/KQRReify.v` + `kitc.py` + `matrix/gen.py` step 46: a copy read for every result sort, a record parameter a record, the pair as a parameter, checked with the program's record types; 13 cells |
| `4102c0a` | §12.V: step 46's design (templates of any signature) |
| `df2e4aa` | §12.V: step 45 (mutual blocks of any signature: the construct table 901 of 909, 1 by design), the C, the gate |
| `dcb282b` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix/gen.py` step 45: `blkT`; a block read per part of its call graph, written as a function over shared slots; 13 cells |
| `56c3242` | §12.V: step 45's design (mutual blocks of any signature) |
| `df72495` | §12.V: step 44 continued (a number-and-memory pair as a parameter: the construct table 887 of 896, 1 by design), the C, the gate |
| `be57d75` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix/gen.py` step 44 continued: the signature's pair flag, `callee_ok_unpair`, `MCallP` / `PvCallP` / `XCallP`; the reifier reads the pair on its components; 11 cells |
| `d8f1337` | §12.V: step 44 continued's design (a number-and-memory pair as a parameter) |
| `1e9da9c` | §12.V: step 44 (a memory function taking a number-and-memory pair apart: the construct table 877 of 885, 1 by design; the pair as a parameter goes on), the C, the gate |
| `4d99efa` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` step 44: the memory and pair sorts mutual, `MMatchP` / `MLetP`, `cmem_cpv_ok`; 6 cells |
| `80e2d78` | §12.V: step 44's design (a memory function taking a number-and-memory pair apart) |
| `f2d3996` | §12.V: step 43 done (records holding records as values: the construct table 870 of 879, 1 by design), the C, the gate |
| `4840d28` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix/gen.py` step 43: one-level match and constructor (`RS`, `RB`, `RJ`), `*SplitR` in every sort, `RMkR`; the reifier's fallback and the bodies' records in its table; 11 cells |
| `bf502ea` | §12.V: step 43's design (records holding records as values) |
| `d45b0f0` | §12.V: step 42 done (captures of every kind: the construct table 855 of 868, 1 by design), the C, the gate |
| `8ab60a6` | `proved/KQRReify.v` + `matrix/gen.py` step 42: captured counters and records, a match's variables their fields' kinds; 4 cells |
| `60915d3` | §12.V: step 42's design (captures of every kind) |
| `9d4beb8` | §12.V: step 41 continued (the copies with their parameters in any order: the construct table 848 of 864, 1 by design), the C, the gate |
| `c825e9a` | `proved/KQRReify.v` step 41 continued: a template's copy and a local fixpoint's copy in the syntax's order (`nonfn_perm`), the recursive call reordered before the functions are dropped |
| `f9c3e5f` | §12.V: step 41 (parameters in any order: the construct table 846 of 864, 1 by design; the copies' order goes on), the C, the gate |
| `3270bf7` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix/gen.py` step 41: wrappers in the syntax's order, `CCntP` / `CSelfP`, the copies' theorems for every result kind; 11 cells |
| `f04dc03` | §12.V: step 40 done (a function's bound from what its callers give it: the construct table 835 of 853, 1 by design), the C, the gate |
| `0d03935` | §12.V: step 41's design (parameters in any order) |
| `3dcc757` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` step 40: written bounds from 1, the let and flat rules checked against them; the call-graph bounds from 1; 2 cells |
| `7626def` | §12.V: step 39 done (counters grown by other counters, polynomial weighted sums: the construct table 831 of 851, 1 by design), the C, the gate |
| `f818f93` | §12.V: step 40's design (a function's bound from what its callers give it, however small) |
| `7fb6b50` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix/gen.py` + `classify.py` step 39: polynomial weights, `ppot_ok` / `ppot_sound`, `ppoly`; the first by-design cell; 5 cells |
| `4ab85fb` | §12.V: step 38 done (counters grown apart, several weighted sums: the construct table 827 of 846), the C, the gate |
| `e731b81` | §12.V: step 39's design (counters grown by other counters: polynomial weighted sums) |
| `03f83e9` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix/gen.py` step 38: weights a list of vectors, coverage, one vector per counter in the reifier; 3 cells |
| `d6a0025` | §12.V: step 37 done (counters grown by the recursion, bound by a weighted sum: the construct table 823 of 843), the C, the gate |
| `a98b0fd` | §12.V: step 38's design (counters grown apart: several weighted sums) |
| `6f87d43` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` + `matrix/gen.py` step 37: weights `sv`, linear bounds, `pot_ok`, `lin1`, `cnat_max`, the copies' theorems for any bound; `wts_of`, `wf_sig`; 18 cells |
| `2c4dfc3` | §12.V: step 36 done (the boolean and record sorts given the number sort's constructs: the construct table 807 of 825), the C, the gate |
| `c764f08` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` step 36: `BxIfB` .. `BxMatchR`, `RIfB` .. `RMatchCnt`; the boolean and record readers; 10 cells |
| `2c1bde4` | §12.V: step 37's design (counters grown by the recursion: a bound on a weighted sum) |
| `0c899f9` | §12.V: step 35 done (a bound for each counter variable: the construct table 792 of 815), the C, the gate, the kernels timed apart |
| `e79f85f` | `proved/KQR.v` + `KQRReify.v` + `matrix/gen.py` step 35: per-variable counter bounds in `wf` and the invariant, `let_scrut`, the call-graph bounds through lets; 11 cells |
| `e4a1b37` | §12.V: step 36's design (the boolean and record sorts given the constructs of the number sort) |
| `adf1658` | §12.V: step 35's design (a bound for each counter variable); `gen.py`: a match on a sum, the recursive call given a successor |
| `ef85399` | §12.V: step 34 done (counter bounds from the call graph: 782 of 802), the C, the gate, the kernels timed apart |
| `ca1ff4f` | `proved/KQRReify.v` step 34: `bounds_tab`, `cl_*`, the reading again with the bounds |
| `87bf37b` | §12.V: step 34's design (counter bounds worked out from the call graph) |
| `be10beb` | the construct table with the unread places as cells: 802 cells, 781 proved, 20 gaps |
| `7252fa8` | `proved/matrix/gen.py`: 22 cells for the places §12.V's steps left unread (802 cells) |
| `86e704b` | `CLAUDE.md` + READ THIS FIRST, §0.9, §13.7, §13.8: completeness is strict -- a construct is done only in its general form (owner) |
| `dfa6958` | §12.V: step 33 done (a sum of counters, counter bounds per function: the construct table 779 of 780, no gap), the C, the gate |
| `dfd4832` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 33: `CAdd`, `sig.sb` / `fbound`, `wf`'s call condition by `cmax`, `bok`; the reifier's `Nat.add` and own bound |
| `7879d05` | §12.V: step 33's design (a sum of counters given to a callee: counter bounds per function) |
| `2956187` | §12.V: step 32 done (records holding records: the construct table 778 of 780), the C, the gate |
| `1dcf4f8` | `proved/KQRReify.v` + `kitc.py` step 32: the record table's fields' widths, `rbr`, constructors flattened; `kitc.py`'s instance from the shape |
| `7a8bde8` | §12.V: step 32's design (records holding records) |
| `29ca4e5` | §12.V: step 31 done (a local `fix` naming the caller's variables: the construct table 777 of 780), F57, F58, the C, the gate |
| `c48dc6c` | `proved/KQRReify.v`: a helper's full scan for a local fixpoint only where the bounded scan finds one (F58) |
| `446e1c2` | `proved/KQRReify.v` + `kitc.py` step 31: a local fixpoint read as a copy whose parameters are its captured variables (`kn_lfix`, `lfix_key`, `lfix_meaning`, `read_def`); `teq` compares fixpoints (F57) |
| `92c32ab` | §12.V: step 31's design (a local `fix` naming the caller's variables) |
| `c70baa5` | §12.V: step 30 done (comparisons of counters and the predecessor: the construct table 776 of 780), the C, the gate |
| `d61d943` | `proved/KQR.v` + `KQRReify.v` step 30: `BCmpC`, `CPred` (`cmpn_ofn`, `ofn_pred_sel`); the reifier reads `Nat.eqb`, `Nat.ltb`, `Nat.leb`, `Nat.pred` of counters |
| `9f75ef1` | §12.V: step 30's design (comparisons of counters and the predecessor) |
| `283540d` | §12.V: step 29 done (the walk retired: the gate and the construct table with the walk switched off, 773 of 780), the C |
| `8b406b3` | `proved/kitc.py`: a program Rocq refuses is refused with Rocq's error (not Rocq in the table, as before) |
| `eadb665` | `proved/kitc.py` + `matrix/classify.py` + `README.md` step 29: the verified compiler is the route, `--walk` the retired one |
| `7b4fd2f` | §12.V: step 29's design (the walk retired) |
| `d819c8d` | §12.V: step 28 done (`option`, `sum` and their kind held as their tag and fields: the construct table 773 of 780), the C, the gate |
| `14e971d` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 28: `rtg`, `rl_mk_tag`, `canon_s`; the reifier's data types (`rec_shape`, `cindex`, `tag_parts`); `kitc.py`'s instances |
| `c648ca8` | §12.V: step 27 done (a template giving its own function parameter to another template: the construct table 769 of 780), the C, the gate |
| `e6b2aa4` | §12.V: step 28's design (`option`, `sum` and their kind held as their tag and fields) |
| `09d1b1d` | `proved/KQRReify.v` step 27: a copy's function parameter given to another template resolved (`fsub`, `tcall`, `sites`, `ensure`) |
| `2b8c70d` | §12.V: step 26 done (a number and a memory given back: the construct table 768 of 780), the C, the gate |
| `4fff28f` | §12.V: step 27's design (a template giving its own function parameter to another template) |
| `6b0d249` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 26: `sq = Some KNum`, pair values `spv` (`cpv_ok`, `ctailp_ok`, `compile_f_ok_pair`), `XMatchP`, `XLetP`; the reifier reads them |
| `e6853d4` | §12.V: step 25 done (a value of any inductive type built in place, taken apart: the construct table 764 of 780), the C, the gate |
| `9ab7709` | §12.V: step 26's design (a number and a memory given back: pair values) |
| `31bb4f4` | `proved/KQRReify.v` step 25: a let of a constructor of plain values put in, a match on a constructor its branch (`head_r`) |
| `d143561` | §12.V: step 24 done (functions giving back a boolean: the construct table 757 of 780), the C, the gate |
| `8780f64` | §12.V: step 25's design (a value of any inductive type built in place, taken apart) |
| `8da3b4d` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 24: `sq : option kind`, the body sort `sbb` (`ctailb_ok`, `compile_f_ok_bool`), `BCall` among the booleans; the reifier reads boolean results |
| `2220ad4` | §12.V: step 24's design (functions giving back a boolean) |
| `12e40c7` | §12.V: step 23 done (a pair built in place, taken apart: the construct table 752 of 780), the C, the gate |
| `e0c149e` | `proved/KQRReify.v` step 23: `iota_pair` in the readers, after the record reading |
| `9cf5da1` | §12.V: step 22 done (booleans chosen by a test or a counter's match: the construct table 744 of 780), the C, the gate; step 23's design (a pair built in place, taken apart) |
| `825c046` | `proved/KQR.v` + `KQRReify.v` step 22: `BIfCmp`, `BMatchCnt` in the three forms a boolean is compiled to |
| `7ae0f91` | §12.V: step 22's design (booleans chosen by a test or by a counter's match) |
| `ec2cedc` | §12.V: step 21 done (records chosen by a test or built from a record taken apart: the construct table 741 of 780), the C, the gate |
| `97b3ece` | `proved/KQR.v` + `KQRReify.v` step 21: `RIf ri`, `RMatchR ri` (the test and the match inside one record value) |
| `1751739` | §12.V: step 21's design (records chosen by a test or built from a record taken apart) |
| `39faaef` | §12.V: step 20 done (lets read by zeta: the construct table 735 of 780), the C, the gate |
| `0993a8b` | `proved/KQRReify.v` step 20: lets read by zeta (`zeta_head` in the readers) |
| `1c4ce89` | §12.V: step 20's design (lets read by zeta) |
| `2af2d8d` | §12.V: step 19 done (record types from the bodies: the construct table 729 of 780 through the verified compiler), the C, the gate |
| `d61befd` | `proved/KQRReify.v` step 19: record types from the bodies (`body_rtys`, `rtab_of` after the signatures') |
| `6e4a59c` | §12.V: step 19's design (record types from the bodies) |
| `9b7eac3` | §12.V: step 18 done (blocks shared with another processor: `lock` through the verified compiler), the C, the gate |
| `8642551` | `proved/KQR.v` + `kitc.py` step 18: `sh_ok`, the shared-block rule over the syntax tree, proved by the kernel beside each function's theorem; `kq_shared` programs read by the verified compiler |
| `30c1981` | §12.V: step 18's design (blocks shared with another processor) |
| `beff230` | §12.V: step 17 done (mutual recursion: 71 of 71), the C, the gate |
| `c6a1d3e` | `proved/KQR.v` + `KQRReify.v` step 17: mutual recursion -- a block as one function with a selector counter, its meaning `blk` of the user's own functions (`compile_f_okr`), each member one call of it; the reifier reads a fixpoint of several bodies |
| `b7dc4c7` | §12.V: step 17's design (mutual recursion) |
| `0dd75b3` | §12.V: step 16 done (`u64`: 70 of 71), the C, the gate |
| `6c6f038` | `proved/KQR.v` + `KQRReify.v` step 16: `u64` -- record variables with their types (`rk`, `rtyped`), `RW64` (one `Ew64`), records bound in memories (`MLetR`, `MMatchR`, `XLetR`, `XMatchR`), records under lets (`RLet`, `RLetR`); the reifier reads `w64_op`, primitive projections, lets inside records |
| `a0e1e6c` | §12.V: step 16's design (`u64`) |
| `59b5737` | §12.V: step 15 done (bytes: 68 of 71), the C, the gate |
| `93b17a4` | `proved/KQR.v` + `KQRReify.v` step 15: bytes (`SRd8`, `MUpd8`); the reifier reads `rd8` / `upd8` |
| `5c3f95c` | §12.V: step 15's design (bytes) |
| `a28ed5e` | §12.V: step 14 done (machine operations: 67 of 71, the kernels included, built in 10–12 s), the C, the boots, the gate, the tally |
| `6241ac9` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 14: machine operations (`MHw`, `SHwf`, `SSize`); the reifier reads the translator's tables; `kq_shared` programs stay with the translator |
| `8587156` | §12.V: step 14's design (machine operations) |
| `4e2504c` | §12.V: step 13 done (functions given that name the caller's variables: 57 of 71), the C, the gate, the tally |
| `b4899ef` | `proved/KQRReify.v` step 13: captures -- a copy takes the variables of the caller its functions given name as parameters, the call passes them |
| `3eb1143` | §12.V: step 13's design (captures); F56 |
| `25cd09b` | §12.V: step 12, part 3 done (records given back: 56 of 71), the C, the gate, the tally |
| `6fda012` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 12 part 3: records given back through the slot block (`RCall`, `sbr`, `ccallr_ok`, `compile_f_ok_rec`, `slot_room`); the reifier reads them, `kitc.py` the sixth part of a signature and the slot block |
| `d9216ac` | §12.V: step 12, part 3 in detail |
| `536603c` | §12.V: step 12, parts 1 and 2 done (kinds in signatures; records and pairs as values: 54 of 71), the gate |
| `a084907` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 12 part 2: records as values (`RecTypes`, `RecLaws`, `VRec`, `srec`, `rmatch`); the reifier reads them, `kitc.py` writes the instance |
| `d84bfe0` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 12 part 1: kinds in signatures and argument lists (numbers, booleans) |
| `79ae741` | §12.V: step 12's design (records and pairs) |
| `c6cffe6` | §12.V: step 11 done (loops that write and give a number: 52 of 71), the C, the timing, the gate, the tally |
| `00462c7` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 11: `XRec`, `XCall`, `FRecX`; `ctailx_ok` with the end memory chosen before the environment; `compile_f_okrx` |
| `4adbee1` | §12.V: step 11's design |
| `f755ecc` | §12.V: step 10 done (functions given to functions: 46 of 71), F54, the gate |
| `813404f` | `proved/KQR.v` + `KQRReify.v` + `kitc.py` step 10: copies per functions given; `compile_f_okr`, `compile_f_okrm`, `denote_rec_ext` |
| `8a9dd12` | §12.V: step 10's design |
| `55eeb6d` | §12.V: step 9 done (a `let` of a counter; the merge of tail calls in full: 42 of 71), F53, the timing, the gate |
| `d93a3d0` | `proved/KQR.v` + `KQRReify.v` step 9: `SLetC` / `MLetC` / `XLetC`; the general merge (`mt_e`, `mt_m`, `ctests`, `cposs`, `mrg_e_ok`, `mrg_m_ok`) |
| `e48afca` | §12.V: step 8 done (helpers written out: 39 of the gate's 71), F52, the timing, the gate, the tally |
| `7193406` | `proved/KQR.v` + `KQRReify.v` step 8: helpers written out; `csel`; `proved/examples/reflect_helpers` |
| `9be78c9` | §12.V: step 7 done (narrow memory: 29 of 70), its timing and gate; step 8's design (helpers written out) |
| `5881c07` | `proved/KQR.v` + `KQRReify.v` step 7: 4-byte cells |
| `f0f06ae` | §12.V: step 6 done (number functions that write the memory; merging calls; one number per variable): F51, the timing of all 16 programs, the tally (24 of 70), the gate |
| `345077b` | `proved/KQR.v` + `KQRReify.v` step 6; `compile`'s call merging and numbering; `kitc.py`; `proved/examples/reflect_writes` |
| `13b80d2` | §12.V: step 6's design |
| `a947eeb` | §12.V: step 5 done (booleans): its tests, the tally (17 of 69), the timing, F50, the gate |
| `82ef78f` | `kitc.py --reflect`: the program's functions unfolded last in the check (F50), pinned in `KQR.v`; `reflect_bools`' expected answer corrected |
| `2c93d56` | `proved/KQR.v` + `KQRReify.v` step 5: booleans; `proved/examples/reflect_bools` |
| `110913d` | §12.V: the if-conversion and its timing (F49); step 5's design (booleans) |
| `145a9ba` | `proved/KQR.v`: if-conversion in `compile` (`choice_ok`, the conditional move), its proof case, the `relax` test |
| `913445c` | §12.V: step 4 done, its gate with `KQ_REFLECT=1` (9 of 68 programs through the verified compiler), the tally after it; this ledger brought up to date |
| `3ecf3d9` | `proved/KQR.v` + `KQRReify.v` step 4: counters as values; `kitc.py`, `KQRChain.v` follow; `proved/examples/reflect_counters` |
| `9a384b3` | §12.V: step 4's design |
| `11cba9e` | `KQRReify.reify_why`: why a program is not read, printed by `kitc.py --reflect`; the tally over the gate's 67 programs and the order of constructs |
| `d82eea3` | §12.V: the gate with `KQ_REFLECT=1` on the fork passes; baseline 1 of 67 through the verified compiler |
| `eaedf81` | `kitc.py --reflect` (`KQ_REFLECT=1`): a program the reifier reads is compiled by the verified compiler; `proved/examples/reflect_calls` |
| `781ae61` | the per-program step by `exact_no_check`; `proved/KQRChain.v` (chains of 30, 100, 300 steps); §12.R done |
| `80d5a07`, `44ef5c4`, `9aced05` | §12.R (3): Rocq's test suite on the fork, memo on and off; the fork image and the cold gate on it; `images.sh`'s third image, `rocq-fork/rebuild.sh` |
| `0e2fd25`, `2771744` | F47: the image build that filled the heavy-run machine's disk; the guard's reading corrected |
| `4c3c22d` | F48: the proof cache's key names the Rocq executables and the memo's setting |
| `3afd777` | `rocq-fork/ConvMemo.v` (the memo proved over a model), `check_patch.py` |
| `19cf113` | `rocq-fork/conv-memo-v9.1.1.patch` (D28) |
| `1c6e0a0` | F46: the exponential check, not fixed upstream, the memo proposed there |
| `8b7304c` | `proved/KQR.v` + `KQRReify.v` step 3: memory writes (`smem`, `cmem_ok`, `ctailm_ok`, the memory cases of `compile_f_ok`; the reifier reads memory bodies, linearity by dead memories); F46 |
| `f342a3b`, `d598904`, `c1635c4` | §12.V: step 3's design; how `S` grows; the verified compiler's KQL is the translator's |
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
