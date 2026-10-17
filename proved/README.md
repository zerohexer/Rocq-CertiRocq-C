# A proved route from Rocq to C

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

Parameters `nat` (a counter; the one the function recurses on comes first), `int`, and at most one memory, last;
results `int` or `mem`.  In a body: `match` on a counter, `if` on comparisons joined by `&&`, `||`, `negb`, `let`
(numbers, booleans, memories), `PrimInt63` arithmetic, `rd`, `upd`, `rd32`, `upd32`, calls of the file's functions, closed constants.
A helper that does not call itself is written out where it is used.  A memory is used only while it is the current one.

Two rewrites keep the C free of jumps on data, as the kit's own translator does:
- a choice between numbers (`if c then a else b`, nested ones included) is worked out both ways and taken with a
  conditional move (`Esel`);
- `if c then f a1 .. an else f b1 .. bn` in tail position (a chain of tests, every end a call of the function itself,
  the arguments differing only in numbers and in the values `upd` writes) becomes one call whose arguments are such
  choices.

Anything else is refused with the reason.  Not read yet: signed division (`/` on `int` is unspecified at the smallest
number), growing blocks (`kq_grow`), functions as values, pairs.

## What is trusted

`Print Assumptions kit_function_correct` (`ASSUME=1 proved/make.sh`): Rocq's 63-bit integer axioms; the kit's memory
primitives `KQRun.rd` / `upd` / `kq_size` / `mem` and `KQSpec.real_laws`; classical axioms CompCert uses.  No admits.
Outside the proofs: the loader that fills the tables, the driver in `kitc.py`, the printer, clang.

## Corpus and speed

`proved/corpus.sh` takes every program of `hand.tsv` through the route, builds it, and compares its answer with the
C++ run's.  Of the 36 programs, 33 are proved, built and give the C++ answer.  Three are not done: CF20C (its function
`solve`), CF61E and CF61En (their function `rights`).  The kernel's check of that function's lemma does not finish
within `KQ_TIMEOUT`, 300 seconds (CF61E was given 25 minutes, with no result).

Best of 5, ms, one pinned core (`bench.sh`); the kit's build is `bin/fin_H_C_NAME_gc`:

| program | problem | kit ms | proved ms | proved / kit |
|---|---|---|---|---|
| CF380C | CF380C | 71.4 | 73.5 | 1.03 |
| CF380Cp | CF380C | 60.6 | 56.3 | 0.93 |
| CF1100F | CF1100F | 144.5 | 144.1 | 1.00 |
| CF1100Fv2 | CF1100F | 108.5 | 131.9 | 1.22 |
| CF1100Fv3 | CF1100F | 105.1 | 138.1 | 1.31 |
| CF868F | CF868F | 107.7 | 110.4 | 1.03 |
| CF868Fv2 | CF868F | 66.2 | 78.1 | 1.18 |
| CF833B | CF833B | 331.9 | 361.8 | 1.09 |
| CF235C | CF235C | 81.2 | 80.0 | 0.98 |
| CF235Cv2 | CF235C | 78.4 | 80.9 | 1.03 |
| CF813F | CF813F | 45.9 | 48.0 | 1.05 |
| CF385C | CF385C | 254.1 | 253.2 | 1.00 |
| CF1167C | CF1167C | 10.8 | 9.8 | 0.91 |
| CF163A | CF163A | 23.9 | 26.0 | 1.09 |
| CF460C | CF460C | 38.0 | 38.6 | 1.01 |
| CF35C | CF35C | 30.3 | 41.0 | 1.35 |
| CF295B | CF295B | 159.6 | 157.4 | 0.99 |
| CF339D | CF339D | 267.9 | 218.0 | 0.81 |
| CF547B | CF547B | 36.6 | 37.3 | 1.02 |
| CF165E | CF165E | 119.2 | 101.2 | 0.85 |
| CF7D | CF7D | 20.6 | 22.9 | 1.11 |
| CF813Fv2 | CF813F | 54.1 | 74.7 | 1.38 |
| CF295Bv2 | CF295B | 107.6 | 140.5 | 1.31 |
| CF165Ev2 | CF165E | 89.6 | 94.8 | 1.06 |
| CF453B | CF453B | 413.2 | 461.4 | 1.12 |
| CF622F | CF622F | 91.5 | 116.9 | 1.28 |
| CF339Dn | CF339D | 155.8 | 167.4 | 1.07 |
| CF35Cn | CF35C | 23.2 | 27.8 | 1.20 |
| CF295Bn | CF295B | 109.4 | 155.2 | 1.42 |
| CF235Cn | CF235C | 61.4 | 80.9 | 1.32 |
| CF385Cn | CF385C | 181.9 | 199.2 | 1.10 |
| CF380Cn | CF380C | 67.9 | 72.2 | 1.06 |
| CF165En | CF165E | 68.4 | 72.5 | 1.06 |

Proved over kit: median 1.06, between 0.81 and 1.42.  The same program timed twice on that machine varies by about
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
