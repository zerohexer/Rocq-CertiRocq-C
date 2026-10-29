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
naturalness  construct table: 775 cells, 733 translated and proved, 5 refused by design, 36 gaps (first full run: 533 / 231)
proof time   cold 35-54 s per test kernel (was 2m29-4m18); a rerun of an unchanged program ~15 s (per-function proof cache);
             corpus: 243 function proofs, 1.9 s on average
theorems     the slab heap keeps its invariant through init/set/free/take; views of one memory are consistent; loops whose budget
             is a measure end with their test false; measure recursion satisfies its equation and an induction principle
```

**Where the work is (§12 has the full ordered list):**
1. The 36 gaps of the construct table, in order of cells closed (§3.5): recursive functions returning a bool / a record of
   three / a number with a memory (9), `int * mem` (7), proof search of pair-valued choices (6), polymorphic and class-based
   helpers (5), arithmetic on counters (4), booleans made by `if`/`match` (3), a local `fix` naming the caller's variables (1),
   a choice between records (1).
2. Compiling from an ordinary `.v` file with one command (`Kq Compile`), entry arguments read from the signature, C printed at
   once and the proofs checked behind it (§12.B).
3. Freestanding: the generated C built and checked on its own; a freestanding `kq_grow` (§9.5).
4. The general passes, each proved once: removal of the bounds test on an access whose index is in range, forwarding a stored
   value to a later read, hoisting loop-invariant reads (§6.4).
5. An interleaving semantics for two programs (protocol properties proved once), a fair lock; checks of the trusted tools
   (`ccomp`, UBSan); hosted features (floating point, system calls, C libraries) when a program needs them.

**Do not (§10 has the reasons):** add a runtime or a collector; translate `nat`/`Z` arithmetic as if it were fixed-width; add
an optimization keyed to one benchmark; fix a refusal by looking at one sample program instead of the construct table; port a
processor family in C or assembly; put a scheduler, a memory manager, drivers or a filesystem into the toolchain; trust the
translator; use the proof cache as release evidence (use `KQ_MONO=1`); run two heavy jobs on one machine at once.

---

## CONTENTS

- §0  THE GOAL — the owner's words, the line between proved and assumed, what natural means, what is refused, the yardstick
- §1  THE ARCHITECTURE AS BUILT — pipeline, KQL, numbers, memory, translator, statements, generator, printer, hardware, libraries
- §2  WHAT C CAN DO, AND ITS COUNTERPART IN ROCQ — the capability table with today's state
- §3  NATURALNESS — THE CONSTRUCT TABLE: method, generator, classification, numbers, the 36 gaps, how to close one
- §4  LOOPS AND RECURSION — fuel, counted loops, measure loops, measure recursion (`wfix`) and its theory
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
  then: "make it level 2, stable, perfect and good" (§4).
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

1. **A value that would be allocated behind the programmer's back and outlive the call**: a list or tree built by `cons`,
   `Some`, `inl`; a closure that escapes (returned, stored in a pair).  In C such data is laid out by the programmer; here it is
   laid out in blocks with an allocator (`lib/Slab.v`), the same way.
2. **An unbounded number** used as a value (`Z`, `nat` arithmetic beyond counting down).  C has none; a bignum is a runtime.
3. **A memory used after it was handed on** (`let t := upd .. s in .. s ..`): the memory is linear, which is what lets a pure
   function be compiled to in-place updates.

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

### 1.6 The per-function statement and its proof

For a function `g` with KQL id `f`, the statement says that running `f` on the arguments from memory `M` gives the Rocq
result:

```
gives a memory:          forall xs M, bounds -> runk P f args M 0 (g xs M)
gives a number, reads:   forall xs M, bounds -> runk P f args M (g xs M) M
gives a number, writes:  forall xs M, bounds -> runx P f args M (g xs M)          (the end memory exists)
gives two numbers:       ... runk P f args M (fst (g ..)) (upd 63 0 (snd (g ..)) M), with 1 < kq_len 63
```

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
of a kernel), `--ext=` (the program's own routines).  Environment: `KQ_STRICT=1` (a proof that fails is an error, not
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
| unions | a layout in a narrow block with views | views proved; no union syntax (none needed) |
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

`kitc.py --no-build` runs the real translator and the real prover on each cell (`KQ_STRICT=1`, `KQ_TIMEOUT=120`);
`classify.py RESULTS... [--md FILE]` reads one line of output per cell and gives each a verdict: `ok`, `design` (the list
`DESIGN_CELLS`: `option`, `list`, sum, a function in a pair, a function returned, a memory used after it was handed on),
`invalid` (the generated program is not Rocq: no verdict), or `gap` with its category (regular expressions on the refusal
reason).  The summary is written to `proved/matrix/MATRIX.md`.

### 3.4 The numbers

| Run | Cells | Translated and proved | By design | Gaps | Not Rocq |
|---|---|---|---|---|---|
| first full run (2026-10-27) | 770 | 533 | 5 | 231 | 1 |
| after counter matches anywhere, local functions, captures, comparison of terms with tests, budgets of constants (2026-10-30) | 775 | **733** | 5 | **36** | 1 |

What closed the 195 cells: a `match` on a counter read anywhere, not only at the top of a recursion (≈190 cells of family N and
P — the single largest gap, found only because the nestings put a `match` inside every other construct); a `let`-bound local
function put in at each use (5); a function given to a template that names variables of the caller (the closure cells); two
functions compared as terms when they contain a test, a `let`, a projection or a local `fix`; a budget made only of numbers
written in the program read as a written budget.

### 3.5 The 36 gaps (the live list, from `MATRIX.md`)

| Cells | Category | Cells by name | What it takes |
|---|---|---|---|
| 9 | a recursive function giving back a **boolean**, a **record of three**, or a **number with a memory** | `P_bool_tail_rec`, `P_bool_rec_search`, `P_bool_nontail_and`, `P_bool_nontail_or`, `P_rec3_tail_rec`, `P_rec3_nontail`, `P_pairp_rec`, `P_intmem_tail_rec`, `P_intmem_nontail` | `result_kind` accepts only `int`, `mem`, a record of exactly two numbers.  A boolean result is a number 0/1 with the statement on `if r then 1 else 0` (as `tr_boolval` already does for helpers); a record of k fields generalizes the slot block from one cell to k-1 cells; `int * mem` is a writing function whose number is returned and whose memory is the end memory (`runx`-like statement with both) |
| 7 | a **pair of a number and a memory** (`int * mem`) as a value | `A_par_mem_pair`, `P_intmem_lit`, `P_intmem_wr`, `P_intmem_let`, `P_intmem_if`, `P_intmem_call`, `P_intmem_alloc_like` | `kind_of` refuses a record that contains a memory.  Split it: the number part as a `KRec` field, the memory part as the (single, linear) memory of the function; the destructuring `let '(x, s2) := ..` binds both |
| 6 | the translation is accepted, **the proof is not found** | `P_pair_if`, `P_pair_if_inside`, `P_pair_call_arith`, `P_pair_proj_pair`, `P_pair_nontail_if`, `P_int_match_nat2` | proof search only: a pair built by an `if` (each field a conditional move) needs the walk to take the record apart on the Rocq side the same way; `match n with O | S O | S (S _)` needs the nested counter test in `kqm_test` |
| 5 | **polymorphic / class-based helpers**, a memory inside a record | `A_par_poly_id`, `A_par_poly_pair`, `A_par_poly_hof`, `A_par_typeclass`, `A_par_mem_record` | specialization at the use (Lean's `fixedInst`): a type argument and an instance argument are put in like a known function; types are erased in KQL already |
| 4 | **arithmetic and comparisons on counters** | `A_par_nat_eqb`, `A_par_nat_ltb`, `A_par_nat_mul`, `A_par_nat_pred` | a counter is one machine number (`ofn`); `Nat.eqb`/`Nat.ltb` are comparisons of those, `pred` is `Esel`, `n + n` is an addition with the bound kept under `cbk` |
| 3 | a **boolean made by an `if` or a `match`** | `P_bool_if`, `P_bool_if_call`, `P_bool_match_nat` | `tr_cond` / `tr_boolval` accept `if c then true else false`-shaped terms only through comparisons; read a boolean-valued `if` as a choice between 0/1 |
| 1 | a local `fix` that names a variable of the caller | `P_int_local_fix` | a local `fix` is a template whose copy takes its free variables as parameters (lambda lifting, as captures do) |
| 1 | a **choice between records** | `P_rec3_if` | each field a conditional move (as for pairs, §1.5) |

**By design (5):** `A_par_option`, `A_par_list`, `A_par_sum` (a value built by a constructor that would be allocated),
`A_par_fun_in_pair` (a function stored in data), `P_mem_dup` (a memory used after it was handed on).  `A_par_fun_result` (a
function returned) is classified the same way when it is refused.  **Not Rocq (1):** `A_par_nat_arith` (`k (m + 0)` is not a
structurally smaller argument; the generated program itself is rejected by Rocq, so there is no verdict).

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

### 4.4 Recursion with a measure: the `wfix` family ("Level 2")

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
budget.  **Rocq's own `Program Fixpoint {measure ..}` (the `Acc`/`Fix_F` form) is not read** — see §4.5.

### 4.5 Reading Rocq's own `Program Fixpoint` (not done; why)

The `wfix` form gives the same equation (`Fix_eq`'s) and an induction principle, with the measure as an exact budget.  Reading
`Program Fixpoint {measure ..}` itself means: the translator reads `Fix_F_sub` / `Fix_sub` applied to opaque well-foundedness
proofs, erases the proof arguments of every recursive call, and the proof walker replaces "induction on the first counter" by
induction on the measure, rewriting with the unfolding lemma Rocq generates.  That is a separate project of several days with
regression risk across every proof, and it buys only the spelling.  It stays on the list (§12.C) as optional.

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
The key includes all tactic libraries and the printed text of everything the function mentions, so the risk is small, but
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
| D12 | **Loops: counted loops and measure recursion with the measure as the exact budget; the equation and the induction principle are proved; reading Rocq's own `Program Fixpoint` is optional** | removes the guessed fuel and its silent wrong answers with the same equation `Fix_eq` gives; the `Acc` form costs days for spelling only (2026-10-29) |
| D13 | **The only acceptance rules are §0.5.  The flat style of `WRITING-FAST-ROCQ.md` is performance advice, like keeping a C loop variable in a register** | a rule nobody can discover is an over-rejection; costs are the user's to choose |
| D14 | **One memory per function, linear** | lets a pure function be compiled to in-place updates and is what C programs do anyway |
| D15 | **Records and pairs are never built; they are their fields** | no allocation, and the C is what a programmer writes for a struct passed by value |
| D16 | **A function with two results returns the first and puts the second into the slot block, saved and restored** | no allocation; the statement states it exactly |
| D17 | **If-conversion at value choices (reads allowed); call-chain merges with plain arithmetic only** | measured both ways (§6.3) |
| D18 | **Budgets are capped at 2^60** | a counter always has room to count a few more, and no proof works a budget out; consequence: a measure must be below 2^60 |
| D19 | **Commits: authored by the owner only, no co-author trailer, no narration; push only when the owner says; no host details, addresses, user names or local paths in the repository** | owner's standing rules; the repository is public |

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

---

## §12. THE WORK LEFT — the live, ordered plan

Each item: what, why, and how it is accepted.  The order is by how much of the goal it closes per unit of risk.

**A. The construct-table gaps (36 cells, §3.5).**  In order: (1) recursive functions giving back a boolean, a record of three,
a number with a memory — 9; (2) `int * mem` values — 7; (3) proof search for pair-valued choices and nested counter tests — 6;
(4) polymorphic and class-based helpers by specialization — 5; (5) arithmetic and comparisons on counters — 4; (6) booleans made
by `if`/`match` — 3; (7) a local `fix` with captures — 1; (8) a choice between records — 1.  Accepted when: the category's cells
are `ok`, the full table is re-run and `MATRIX.md` updated, and the gate (examples, corpus, kernels if the walk changed) passes.

**B. Compiling from an ordinary `.v` file, as simply as `lean --c`.**
- A command (`Kq Compile solve.`) in an ordinary Rocq file: the entry's arguments are read from its signature (numbers from the
  command line, the memory from the memory file), replacing the `main` convention of `.body` files.
- Emit first, prove behind: the C is printed in seconds; the proofs run cached and in parallel; the program is reported proved
  when they finish.
- A check-only mode that runs the translator on every function and reports what is refused, in seconds.
- Refusal messages that say what to write instead (the library, the rewrite), with a pointer into this file.
Accepted when: every example and corpus program compiles from a `.v` file with the command, with the same C as today.

**C. Language beyond the table.**  Records of k numbers as results (the slot block with k-1 cells); strings and a formatting
library on byte blocks (`printf`-like, written in Rocq); an address type with proved arithmetic, and pointers beyond views;
specialization of type and instance arguments; optional: reading `Program Fixpoint {measure ..}` (§4.5); optional: `Z` where a
proof gives the range (D3).

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

---

## §13. HOW TO WORK ON IT

### 13.1 Environment and commands

Everything runs in the repository's CertiRocq image (Rocq 9 with MetaRocq, CompCert 3.17, clang), in the repository directory
(`setup.sh`, `images.sh` build it).

```
bash proved/make.sh                     # every proof of the route, "core-ok" at the end (ASSUME=1: print the assumptions)
python3 proved/kitc.py NAME ...         # translate, prove each function, print the C, build bin/P_NAME
bash proved/examples.sh                 # every proved/examples/*.body: proved, built, answer = NAME.expect
bash proved/corpus.sh [times]           # every program of hand.tsv; "times" also times each next to the kit's build
bash hw/spec.sh                         # the laws, the model, the demos, the library theorems rest on the laws alone
bash hw/check.sh                        # the kernels under QEMU's processor and under KVM, with their controls
bash hw/build_proved.sh NAME            # one kernel through the proved route; hw/run.sh NAME_p boots it
python3 proved/matrix/gen.py OUT        # the construct table's programs (then kitc.py --no-build on each)
python3 proved/matrix/classify.py RESULTS --md proved/matrix/MATRIX.md
python3 tools/mkloopspec.py > proved/KQLoopSpec.v
bash all.sh                             # everything from an empty directory (the kit route's gates too)
```

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

---

## §14. COMMIT LEDGER (newest first)

Pushed to the public repository up to `76e777a`.  Local, not pushed (2026-10-30): `3184a86` … `7e41ee8`.

| Commit | What |
|---|---|
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

---

## §16. RELATED DOCUMENTS

- `proved/GOAL.md` — the short statement of the goal (§0 contains it).
- `proved/README.md` — the proved route: steps, numbers, memory, what the translator reads, machine operations, kernels,
  several processors, what is trusted, the corpus table.
- `README.md` — the repository: the kit route, results, hardware, dynamic memory, the proved route, what is checked and trusted,
  limits.
- `WRITING-FAST-ROCQ.md` — the costs of each way of writing (to be split, §12.J).
- `proved/matrix/MATRIX.md` — the latest construct-table summary.
- In the KernelQ project: `docs/rocq-cost-shape-solution.md` (the cost-shape record: the word-RAM cost model, settled; the
  method of auditing by term former that §3 follows) and `docs/kernelq-pedagogy-goal.md` (why Rocq is the learning track; LS.30
  on Rocq computing, LS.31 on the roles of Coq, Clight, VST, RefinedC and CompCert).
