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
of the file's functions, closed constants.  A helper that does not call itself is written out where it is used.  A
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

Anything else is refused with the reason.  Not read yet: a function that gives back a record or pair (and a choice
between two records), growing blocks (`kq_grow`), functions as values.

## What is trusted

`Print Assumptions kit_function_correct` (`ASSUME=1 proved/make.sh`): Rocq's 63-bit integer axioms; one fact about
signed division that Rocq's axioms leave open and its own computation settles, `divs_min_neg1` (the smallest number
divided by -1 is the smallest number; `vm_compute` gives that); the kit's memory primitives `KQRun.rd` / `upd` /
`kq_size` / `mem` and `KQSpec.real_laws`; classical axioms CompCert uses.  No admits.
Outside the proofs: the loader that fills the tables, the driver in `kitc.py`, the printer, clang.

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
