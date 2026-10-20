# A proved route from Rocq to C

The goal, and what is proved against what is assumed: `GOAL.md`.

A plain Rocq program (the programs of `hand/`: counters, 63-bit integers, loops, calls, the kit's memory blocks) is
translated to a small first-order language, KQL.  For every function the kernel checks the statement "the KQL function
computes this Rocq function".  KQL goes to CompCert's Clight by a generator that is proved once for all programs.  The
Clight is printed as C and built with clang next to the kit's support code; it takes about as long as the kit's own build
of the same program (table below).

```coq
Fixpoint qry (fuel : nat) (b l base res : int) (s : mem) : int := ...        (* plain Rocq, in hand/CF1100F.body *)
Definition main : int := kq_sum (solve (kq_nat (kq_arg 0)) (kq_nat (kq_arg 1)) (kq_input 0)).
```

```
python3 proved/kitc.py CF1100F        # translate, prove every function, print the C, build bin/P_CF1100F
```

## The steps

| Step | File | How it is justified |
|---|---|---|
| Rocq function -> KQL | `KQMTrans.v` (MetaRocq) | per program: the statement `runk P f args M (g xs M) M'` for each function, proved by `kqm_auto` (`KQMAuto.v`) and checked by the kernel.  The translator is not trusted |
| KQL -> Clight | `KQLGen.v` | proved once, for every program: `sim` (`KQLProof.v`) for the arithmetic, `simk` (`KQM.v`) with the kit's memory |
| Clight -> assembly | CompCert 3.17 | CompCert's pass theorems, composed in `KQLBack.v` (the builds measured here use clang instead) |
| Clight -> C text | `KQLPrint.v` | not proved.  It prints each Clight construct as the C that means the same, and a choice between two atoms as the kit's `kq_sel_*` |
| tables, driver | `kitc.py`, `sup/v4/kq_io3.c` | trusted C: fills the two tables below from the loader's blocks and calls the entry function |
| machine operations | `hw/kq_hw.h` | trusted C bodies of the external functions the generated code calls (see Machine operations) |

`kit_function_correct` (`KQMTop.v`): if the KQL program runs function `g` on `vs` from the kit's memory `M` to `v`
and `M'`, then the Clight function the generator made from it, called on the numbers of `vs`, from any Clight memory
that holds `M` in the two tables, returns the number `v` and leaves a Clight memory that holds `M'`.

## Numbers

A 63-bit number `n` is the 64-bit word `2n + 1`, the way the kit holds it.  Addition is `a + b - 1`, subtraction
`a - b + 1`, the orders are C's orders on the words (signed ones through a cast), `land` and `lor` are the same on the
words, `lxor` is `(a ^ b) | 1`, a shift amount or a divisor is `w >> 1`.  No mask is needed.  Division by zero, a shift
of 63 or more, and the signed remainder are tested first, so the C has no undefined behaviour.  The arithmetic lemmas
are in `KQTArith.v`.

## The kit's memory

The memory is the kit's abstract `mem` (`KQRun.v`) with `rd`, `upd`, `kq_size`; what is assumed of it is
`KQSpec.real_laws`, and `KQModel.v` proves the laws satisfiable.  A block number and a cell number are run-time
numbers; a read outside gives 0 and a write outside changes nothing (negative numbers included).  In C the memory is
two global tables set by the loader: `kq_tab` (the address of each of 64 blocks) and `kq_lens` (twice the size of
each); the narrow blocks (`rd32`, `upd32`: cells of 4 bytes, a signed 32-bit number) have two tables of their own,
`kq_tab32` and `kq_lens32`.  `kmrel M m` says a Clight memory `m` holds `M` in that layout; a cell holds the word of its number, so a read
or a write moves the word as it is.

## What the translator reads

Parameters `nat` (a counter; the one the function recurses on comes first), `int`, records and pairs of those, and at
most one memory, last; results `int` or `mem`.  In a body: `match` on a counter, `if` on comparisons joined by `&&`,
`||`, `negb`, `let` (numbers, booleans, memories, records), `PrimInt63` arithmetic (signed division `divs` and remainder `mods` included), `rd`, `upd`, `rd32`, `upd32`, calls
of the file's functions, closed constants.  A helper that does not call itself is written out where it is used, unless it is large (more than 40 nodes of its text): then it is a function of its own, proved once.  A budget written as a number (`kq_nat 100000000`) is read as that number (`Abud` atom in KQL: the printer and the proofs never build the unary `nat`).  A
memory is used only while it is the current one.

A record (`Record st := mkst { acc : int; cnt : int }`) or a pair of numbers and counters is never built: the
function takes its fields as separate KQL variables, `mkst a b` in a call passes the fields, and `match r with
mkst a b => ..`, a field function (`acc r`), `fst` and `snd` pick them.  A helper may give a record, a `let` or
`match` may end in one, and records nest.  The statement the kernel checks is about the original function applied to
`mkst x1 x2`.  `proved/examples/` has a record and a pair as the state of a loop (`proved/examples.sh`).

Two rewrites keep the C free of jumps on data, as the kit's own translator does:
- a choice between numbers (`if c then a else b`, nested ones included) is worked out both ways and taken with a
  conditional move (`Esel`); the two numbers may read the current memory (`rd`, `rd32`), up to three reads in all,
  because a read is total and can be run whether or not its arm is taken;
- `if c then f a1 .. an else f b1 .. bn` in tail position (a chain of tests, every end a call of the function itself,
  the arguments differing only in numbers and in the values `upd` writes) becomes one call whose arguments are such
  choices.  These stay plain arithmetic: a chain of tests on a state that cycles is predicted well, and a conditional
  move in its place makes each round wait for the one before.

8- and 16-bit cells: `rd8 h i s`, `upd8 h i v s`, `rd16`, `upd16` (defined in `KQRun.v` from the 32-bit cells of a narrow
block, little-endian, the machine's layout: byte `i` is byte `i mod 4` of cell `i / 4`; a read outside the block is 0 and a
write outside it does nothing).  `rd8` and `upd8` are one KQL instruction each (`Ekld8`, `Ekst8`) and one `unsigned char`
access in the C, with the guard on the index; `rd16` and `upd16` are two of them (clang merges the pair).  The meaning of
the instruction is the Rocq definition of `rd8` / `upd8`; the proof that the C byte access does the same on a cell is
`KQBytes.v` (CompCert's memory: four bytes of an `int`, one byte stored) and `KQByteArith.v` (the arithmetic of the
byte).  Nothing is added to the laws of the memory.  A sum over bytes of 10^6 bytes, 100 times: 136 ms as shifts and
masks of the 32-bit cell, 74 ms as byte loads (`tests/bytebench.body`, `tests/bytebench_c.c`).
`proved/examples/bytes.body` writes bytes and halfwords over each other and reads them back.

Functions that give back two numbers.  A recursive function whose result is a pair or a record of two numbers
(`Fixpoint minmax .. : int * int`, `.. : span` with two fields) is a KQL function that returns the first number and puts
the second into cell 0 of block 63; the caller keeps the cell's old number first, reads the new one after the call and
puts the old one back, so the memory is what it was.  The statement of such a function says exactly that:
`runk .. M (fst (f ..)) (upd 63 0 (snd (f ..)) M)`, under the premise that block 63 has room (`1 < kq_size 63 M`),
which the driver provides (8 cells).  The proof uses two laws of the kit's memory, `upd_upd` (a cell written twice
holds the second number) and `upd_rd_id` (a cell written with the number it has is unchanged), both proved for the
model in `KQModel.v`.  A tail call is a loop; a call whose result is used (`let '(a, b) := f m in ..`) is a call with the
save and the restore.  More than two numbers: a pair of pairs is not read yet (pass the extra results through memory
cells, as C does through pointers).  `proved/examples/pair_ret.body`, `rec_ret.body`.

Mutual recursion.  `Fixpoint ping (n : nat) .. with pong (n : nat) ..` (the counter first in each, as always; every call
to the other function passes a smaller counter) is read as one KQL function for each; a call of the other is a plain
call (clang turns a call in tail position into a jump).  The kernel checks the group with one lemma, by induction on the
counter, whose two parts are the statements of the two functions (`proved/examples/mutual.body`).

Functions as values.  A function known where it is used is a macro's argument: a helper that does not call itself and takes
a function (`twice f x := f (f x)`) is written out with the function put in, whether the function is a constant
(`twice add3 x`), a constant given numbers (`twice (scale 5) x`) or a lambda (`twice (fun z => z - 1) x`).  A recursive
function that takes functions (`Fixpoint fold_cells (n : nat) (f : int -> int -> int) ..`, the counter first as always) is
a template: every call that gives it known functions (closed terms) makes a copy for them, a KQL function of its own
(`fold_cells_3`), proved against the original applied to those functions (`proved/examples/hof_rec.body`,
`hof_cells.body`).  A function that names a variable of the caller (a closure) is refused with that reason: pass the
variable as an argument.  A function chosen at run time is a dispatch on an id with the environment as an argument,
an ordinary `if id =? 0 then f0 env x else if id =? 1 then ..` (`proved/examples/dispatch.body`); clang turns such a
chain into a jump table.

64-bit unsigned numbers.  A number of the kit is 63 bits wide, so `u64` (`KQRun.v`) is a record of two of them: `w_lo`, the
low 63 bits, and `w_hi`, the bit above.  Its meaning is `u64_val`, a number of Z in 0 .. 2^64 - 1, and every operation is
defined through it with C's wrap-around of `unsigned long long`: `u64_add`, `u64_sub`, `u64_mul`, `u64_and`, `u64_or`,
`u64_xor`, `u64_shl`, `u64_shr` (the amount modulo 64), the comparisons `u64_ltb`, `u64_leb`, `u64_eqb`, and the
conversions `u64_of_int`, `u64_to_int`, `u64_of_halves hi32 lo32`, `u64_lo32`, `u64_hi32`.  They all come down to
one operation, `w64_op o a b`, and that is one KQL instruction (`Ew64`): the C packs the two halves of each operand into
one `unsigned long long`, does the operation, and splits the result back into two variables.  The proof of the
instruction is `exec_w64` in `KQM.v`, from the packing lemmas of `KQW64.v`.  Two choices keep the per-program proofs
fast.  `w64_op` is sealed (its definition is behind a `Qed`; the equation `w64_op_unfold` is its meaning), so no
conversion, the kernel's included, works an operation out (the kernel does not evaluate chains of them).  And the rule for the instruction (`K_w64`) takes its operands as records with premises on their
two halves, and `u64` has primitive projections, so a term is never written as `mk_u64 (w_lo r) (w_hi r)`, which
would copy `r` at every step.  A u64 helper is written out where it is used, like any helper; a recursive function that
gives back a u64 is a function with two results (the second through block 63).
`proved/examples/w64.body` is FNV-1a over bytes, a splitmix-style mixer, a rotation and comparisons.

A heap that grows.  `kq_grow h n s` makes block h hold at least n cells (the new ones read 0, nothing else changes) and
`kq_size h s` gives a block's size now (KQRun.v, the laws are in KQSpec.v).  `kq_size` is one KQL instruction
(`Eksize`): a load of the block's limit from the table, proved like the loads.  `kq_grow` is one more machine operation
(`HGrow`, as the device accesses and atomics are): its law is the kit's (`size_grow`, `rd_grow`, ..., all proved for the model
in `KQModel.v`), its C body is assumed -- on a hosted run it is the kit's `kq_grow`, which moves the block with `realloc` and
fills the two tables of the theorem again (`HW_GROW` in `kitc.py`); on the machine itself the program's own allocator does
the same.  If memory runs out the hosted run stops with exit code 3: the laws cannot hold then and nothing is computed
past it.  `lib/Slab.v` (objects with generation-checked handles on one block that doubles when full) goes through the route
as it stands: `proved/examples/heap.body` is a hash set whose entries are slab objects, 18 functions proved, with the
answer equal to the same set written with `malloc` and `free` in C.  Three things the route needed for it:
a budget `kq_nat n` for a number n worked out while the program runs (it is at most 2^60 now, `kq_nat_le`, so a counter
always has room to count a few more), a bound on any such counter that the proof gets without working the number out, and
a first parameter of type `int` no longer tried as an induction.  Not read yet: a recursive function that gives back a
`bool` (return 0 or 1; a helper that is not recursive is fine).

Proof time of long straight-line code.  The proof of a function walks its KQL body one instruction at a time.  Two
costs grew with the length and are gone: the bindings of the variables are a chain of `PTree.set` that is looked up by
working all of it out each time (the walk now turns the chain into a tree every 24 bindings), and a rewrite for counters
that scanned the whole goal at every addition (now tried only where a counter is added to).  The 100-store table of the
interrupt kernel went from 119 s to 16 s, and the five test kernels now prove in 39 s to 1 m 33 s each (2 m 29 s to 4 m 18 s before).  What is left: a run in which each step reads the memory it writes
(`upd b i (rd b j s + 1) s`, ten, twenty times in a row) mentions the previous memory twice per step, so the memory term
doubles per step -- ten steps take 5 s, sixteen over five minutes (`proved/examples/helper_write.body` is the ten).  A
call of a function does not have the problem: the memory after it is `f args M`, not its text.  So put the steps in
functions or loops.  Also fixed: a helper that writes the memory is now seen as writing, so the function that uses it is
stated and proved with the memory it leaves.

Anything else is refused with the reason.  Not read yet: a function that gives back more than two numbers (and a choice
between two records), closures.

## Machine operations

The operations of `KQRun.v` that reach the machine (`hw_load`, `hw_store`, `hw_store64`, the atomics and compare-and-swap,
`hw_fence`, `hw_copy`, `hw_fill`, `hw_cmp`, `hw_call`, `hw_run`, `hw_code_sync`) are read like `upd`: each takes the memory
and gives it back, and what one reads goes into the cell it is told to fill.  In KQL they are one instruction, `Ehw`,
whose meaning is the kit's own operation on the abstract memory (`hw_sem`).  The generator emits it as a call of an
external function (`f91000` ..), and the C bodies are the kit's (`hw/kq_hw.h`: `volatile` accesses, C11 atomics,
`memmove`), so a device access is never merged, moved or left out.

`kit_function_correct` takes one more hypothesis, `hw_law`: called from a Clight memory that holds the kit's memory `M`,
each external function finishes with no event and leaves a Clight memory that holds `hw_sem o vs M`.  It is not an
axiom of Rocq; it is what the theorem assumes of the C bodies and of the machine, the same kind of statement as the
loader's.  `KQSpec.real_laws` says what each operation does to the memory (a load fills its cell and no other, a store
changes no wide cell, the trace records it); a proof about a program holds for every number a device could give back.
Numbers the machine gives without a memory (`hw_addr`, `hw_irq_info`, `hw_irq_entry`, `hw_cpu_code`, `hw_sym`) are one more
instruction, `Ehwf`, over external functions with the law `hwf_law` (the C function gives the number the abstract one
names and changes nothing); `hw_irq_take` is a memory operation like the others.  `proved/examples/hw_mmio.body` stores
to and loads from a page at `0x10000000` that the test driver maps to stand for a device.

### A kernel through this route

`hw/build_proved.sh NAME` takes `hw/NAME.body` (the program of the kit route's `hw/NAME.body`, or `hw/NAME_p.body`
when the proved route reads a different text), the instructions of `hw/X86.v` and the library `hw/lib.body` as one Rocq
text, translates it, has the kernel check that each of its functions computes its Rocq definition (two to four
minutes), prints the C, and builds `hw/NAME_p.elf` with the runtime of `hw/build.sh` (`hw/kq_bare.c`, `hw/boot.S`).
`hw/run.sh NAME_p` boots it in QEMU.  The five test kernels of `hw/` all go through it and give the answers of the kit
route's: `kernel` (serial line, screen, page tables, interrupt table, ten timer interrupts, the processor's registers,
PCI, atomics, bulk bytes, assembly routines of its own), `irqnow` (interrupts handled at once by a Rocq program),
`fault` (a page fault handled by a Rocq program that maps the page), `smp` (a second processor running a Rocq
program), `own` (the interrupt entry routine written in Rocq, byte by byte).  What that rests on is the list below
under "What is trusted" plus the machine itself: the code the kernel writes into memory and runs (`hw_run`) is as
correct as the encodings in `hw/X86.v`.

**Several programs in one kernel.**  `hw/NAME_irq.body` is run at an interrupt or a fault, `hw/NAME_ap.body` by a
second processor.  Each is its own Rocq text that is translated and proved (`kitc.py --secondary --prefix=irq_
--entry=kq_irq_body`), with the functions named `irq_f1000 ..`; they share the tables (the memory) and the machine's
`f91xxx` functions with the main program.  An interrupt program runs inside the interrupt, so it is compiled with
`-mgeneral-regs-only`.

**The program's own routines.**  A routine written in assembly or C (`hw/NAME.S`, `hw/NAME.c`), declared in the Rocq
text as `Axiom NAME : int -> .. -> mem -> mem` (or `.. -> int`) and listed in `hw/NAME.ext` (`ROCQNAME CNAME`), is
called through `hw_user` / `hw_userf` (`hw/User.v`, one number per routine, up to four arguments): operations like the
others (`Ehw HUser`, `Ehwf FUser`), assumed by `hw_law` / `hwf_law`.  `hw/p_prep.py` turns the kit-style `Axiom` into
those definitions and writes `NUMBER CNAME ARGUMENTS KIND`, from which `kitc.py --ext` writes the C dispatchers.  A
routine receives numbers as marked words (2n + 1) and the memory token and gives back a marked number or the token.

Two rules the long programs showed.  A helper larger than 40 nodes is a function of its own: written out into its
callers, a helper that uses its memory argument several times multiplies the size of every caller.  A choice on
`a && b`, `a || b` or `negb a` is translated as choices on the parts and the goal is rewritten the same way, so the
kernel's checks are compared with the text without a case split per test; write such a test where it is used, not in a
`let` that is a `bool` (the flag the translator keeps for that cannot be compared without a split).  A chain of
`&&` / `||` whose outcome is used much later is a split of everything after it: put the chain in a function of its own
(more than 40 nodes) or compute the number with one choice per test and add them (`(if a then 1 else 0) + (if b then
1 else 0)` is taken with conditional moves and splits nothing).

### Several processors

A second processor runs a program of its own (`hw/NAME_ap.body`), proved like the first as a sequential function of the
memory.  The programs share the tables of the kit's blocks but, by the rule below, not the cells.  What they share is
memory reached by address: a narrow block's address (`hw_addr h`) is given to the other program, and every access to it
is a marked operation: `hw_aload` (acquire), `hw_astore` (release), `hw_atomic`, `hw_cas`, `hw_fence`, which are external
calls with sequentially consistent or acquire/release C11 atomics, so the C compiler neither merges nor moves a plain
access across them.  The proof of each program holds for every number such an operation can give back (the laws say
"some number of the right size", and only the cell it fills changes).

A program that shares narrow blocks lists them: `Definition kq_shared : list int := [6].`  The translator then refuses
`rd32`, `upd32`, `rd8`, `upd8` on a listed block, and on any block whose number is not written in the program where it
is used: a plain access would read the cell the proof believes it holds while the other processor changes it.

`hw/lib.body` has a spinlock (`lock_take`, `lock_free`: a compare-and-swap from 0 to 1 with a pause between tries, and a
release store).  `hw/lock.body` and `hw/lock_ap.body` run on two processors (QEMU `-smp 2`) and each add 1 to a counter
100 000 times with a plain read and a plain write under the lock: the counter ends at 200 000 (the same loop without
the lock, `hw/smp.body`, loses updates).  That the lock admits one holder at a time is a property of the hardware's
atomics; a theorem about a program that uses it (the counter, a queue) is written in Rocq about its text, as for any
other property of the operating system.

## What is trusted

`Print Assumptions kit_function_correct` (`ASSUME=1 proved/make.sh`): Rocq's 63-bit integer axioms; one fact about
signed division that Rocq's axioms leave open and its own computation settles, `divs_min_neg1` (the smallest number
divided by -1 is the smallest number; `vm_compute` gives that); the kit's memory primitives `KQRun.rd` / `upd` /
`kq_size` / `mem` and `KQSpec.real_laws`; classical axioms CompCert uses.  No admits.
Outside the proofs: the loader that fills the tables, the driver in `kitc.py`, the printer, clang, and the C bodies of
the machine operations with the law `hw_law` that the theorem assumes of them.

## Corpus and speed

`proved/corpus.sh` takes every program of `hand.tsv` through the route, builds it, and compares its answer with the
C++ run's.  All 36 programs are proved, built and give the C++ answer.  A lemma the kernel does not finish within
`KQ_TIMEOUT` (300 s) is left `Admitted` by `kitc.py`, which then reports the program as `UNPROVED` with the function
names (the C is still made from the same proved generator); `KQ_STRICT=1` makes it an error.  None is left unproved.

Best of 5, ms, one pinned core (`bench.sh`); the kit's build is `bin/fin_H_C_NAME_gc`:

| program | problem | kit ms | proved ms | proved / kit |
|---|---|---|---|---|
| CF380C | CF380C | 66.7 | 68.2 | 1.02 |
| CF380Cp | CF380C | 49.5 | 54.1 | 1.09 |
| CF1100F | CF1100F | 139.0 | 141.0 | 1.01 |
| CF1100Fv2 | CF1100F | 98.4 | 124.6 | 1.27 |
| CF1100Fv3 | CF1100F | 95.6 | 105.2 | 1.10 |
| CF868F | CF868F | 103.2 | 116.2 | 1.13 |
| CF868Fv2 | CF868F | 63.3 | 66.9 | 1.06 |
| CF833B | CF833B | 336.7 | 343.7 | 1.02 |
| CF235C | CF235C | 67.9 | 67.6 | 1.00 |
| CF235Cv2 | CF235C | 79.9 | 84.3 | 1.05 |
| CF20C | CF20C | 7.2 | 7.0 | 0.97 |
| CF813F | CF813F | 46.5 | 47.6 | 1.03 |
| CF61E | CF61E | 88.8 | 78.8 | 0.89 |
| CF385C | CF385C | 235.4 | 240.1 | 1.02 |
| CF1167C | CF1167C | 9.4 | 9.9 | 1.05 |
| CF163A | CF163A | 24.3 | 25.5 | 1.05 |
| CF460C | CF460C | 46.4 | 44.9 | 0.97 |
| CF35C | CF35C | 33.1 | 37.9 | 1.14 |
| CF295B | CF295B | 114.2 | 138.3 | 1.21 |
| CF339D | CF339D | 211.7 | 207.3 | 0.98 |
| CF547B | CF547B | 35.5 | 32.4 | 0.91 |
| CF165E | CF165E | 108.3 | 96.4 | 0.89 |
| CF7D | CF7D | 20.6 | 22.4 | 1.09 |
| CF813Fv2 | CF813F | 43.7 | 44.6 | 1.02 |
| CF295Bv2 | CF295B | 83.0 | 128.3 | 1.55 |
| CF165Ev2 | CF165E | 88.2 | 85.7 | 0.97 |
| CF453B | CF453B | 385.1 | 447.7 | 1.16 |
| CF622F | CF622F | 86.4 | 87.0 | 1.01 |
| CF339Dn | CF339D | 120.6 | 120.3 | 1.00 |
| CF35Cn | CF35C | 22.3 | 27.1 | 1.21 |
| CF295Bn | CF295B | 100.9 | 146.2 | 1.45 |
| CF235Cn | CF235C | 46.6 | 44.3 | 0.95 |
| CF385Cn | CF385C | 161.1 | 175.4 | 1.09 |
| CF380Cn | CF380C | 61.0 | 60.2 | 0.99 |
| CF165En | CF165E | 56.9 | 60.6 | 1.06 |
| CF61En | CF61E | 57.6 | 51.1 | 0.89 |

Proved over kit: median 1.02, between 0.89 and 1.55.  The same program timed twice on that machine varies by about
15%.

## Running it

In the CertiRocq image, in the repository directory:

```
bash proved/make.sh               # every proof, "core-ok" at the end (ASSUME=1 prints the assumptions)
python3 proved/kitc.py NAME ...   # translate, prove, print, build bin/P_NAME
bash proved/corpus.sh [times]     # all of hand.tsv; "times" also times each next to the kit's build
```

`KQ_TIMEOUT` (seconds, default 300) bounds each proof.

## Why not CertiRocq's front end

CertiRocq's proof of its translation to λANF (`convert_top_anf_correct`) assumes the program has no primitive
operations (`no_prims`), and λANF's semantics for its optimisation passes (`bstep`) has no rule for them.  Every kit
program uses `PrimInt63`, so those theorems say nothing about it.  This route does not go through them.
