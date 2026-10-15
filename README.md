# Rocq compiled to C, made fast -- and the same however it is written

Plain Rocq functions (machine integers, a memory of numbered blocks) compiled to C by CertiRocq and run natively, on
26 Codeforces problems: the 15 of the cost-shape corpus that can be timed, and 11 new ones written for this test.
What it took to bring them from 3x - 37x the C++ reference to about 1.1x; what decides whether a program gets there;
and, since 2026-10-14, a translator in front of the compiler that makes the result the same however the program is
written -- with Rocq checking every step it takes: by computation, by induction, or by a copy of the program that
carries the proofs -- plus narrow (4-byte) blocks, and, as a setting that is off by default, reads and writes without
the bounds test where a proof allows.  And a kernel written in Rocq (`hw/`, below): what C can do to hardware, generic;
the processor's instructions written in Rocq from its manual; laws for the generic part, with a model and proofs; and
kernels run in QEMU that check themselves.

Started 2026-10-13 as a spike; it supersedes a first harness, whose numbers were taken before the fixes described here.

Licence: MIT (`LICENSE`), the same as CertiRocq's, so that any of this can go into CertiRocq or a fork of it.  `patch/`
changes CertiRocq itself (MIT, its authors); the images are built from CertiRocq and MetaRocq as published.

## Result

One fast core of an Intel Core i9-12900H, pinned; best of 5; time of the computation only (`results/table.txt`, the
run of `all.sh` from an empty directory, with the default settings: every read and write tests its cell).  The laptop was busy with other work
during this run: between runs the figures move by up to about 10%, the C++ ones too, and a program whose time is
memory more (CF339D's C++: 62 ms in the run before this one, 78 ms in this one), so compare the ratios of one run.
Every Rocq run's answers are identical to its C++ run's.

| Problem | What the work is | C++ | C++, 8-byte cells | C++ written the same way | Rocq, corpus text | Rocq, by the guideline | best Rocq / C++ |
|---|---|---|---|---|---|---|---|
| CF455A | two loops over 5 million cells | 5.0 | 5.5 | - | 5.7 | as the corpus text | **1.15** |
| CF380C | segment tree, 100 000 queries | 52.7 | 69.8 | - | 85.2 | **56.2** | **1.07** |
| CF1100F | table of bases, 500 000 queries | 73.6 | 77.6 | 82.5 | 131 | **65.7** | **0.89** |
| CF868F | divide and conquer with a moving window | 94.9 | 98.2 | - | 185 (621 with the exact text) | **85.3** | **0.90** |
| CF631E | hull of lines, binary search | 6.2 | - | - | 6.0 | as the corpus text | **0.96** |
| CF833B | segment tree, add and maximum on ranges | 370 | - | 371 | 658 | **391** | **1.06** |
| CF17E | palindromes of 2 million letters | 34.4 | - | - | 45.1 | as the corpus text | **1.31** |
| CF20C | shortest paths with a heap | 11.4 | - | 7.1 | 13.8 | **8.7** | **0.76** |
| CF1039D | greedy on a tree, divide and conquer | 624 | - | - | 746 (2240 with the exact text) | as the corpus text | **1.20** |
| CF813F | offline: sort, segment tree, union-find with undo | 33.0 | - | - | 67.8 | **45.7** | **1.39** |
| CF235C | suffix automaton | 28.5 | 40.1 | - | 79.2 | **40.4** | **1.42** |
| CF1172F | segment tree of sorted arrays | 186 | - | - | 180 | as the corpus text | **0.97** |
| CF432D | prefix function of 2 million letters | 6.0 | - | - | 8.2 | as the corpus text | **1.37** |
| CF453B | table over sets of primes | 782 | - | 335 | 954 | **471** | **0.60** |
| CF622F | modular arithmetic, 1 million terms | 56.3 | - | - | 92.7 | **85.5** | **1.52** |
| CF61E (new) | tree of sums (binary indexed), used twice | 73.6 | 87.0 | - | - | **75.9** | **1.03** |
| CF385C (new) | sieve up to 10 million | 137 | 267 | - | - | **145** | **1.06** |
| CF1167C (new) | union-find | 6.4 | 6.8 | - | - | **10.6** | **1.64** |
| CF163A (new) | table of 25 million cells, two rows kept | 37.8 | - | - | - | **29.2** | **0.77** |
| CF460C (new) | binary search on the answer | 31.8 | 31.5 | - | - | **36.8** | **1.16** |
| CF35C (new) | walk over a 2000 x 2000 grid with a queue | 16.2 | 19.7 | - | - | **17.6** | **1.09** |
| CF295B (new) | all shortest ways, 500 vertices | 37.7 | 59.3 | - | - | **122** | **3.24** |
| CF339D (new) | tree updated from the bottom, 2 million changes | 77.7 | 96.5 | - | - | **115** | **1.48** |
| CF547B (new) | nearest smaller with a stack | 31.7 | 31.9 | - | - | **41.1** | **1.30** |
| CF165E (new) | table over sets of 22 bits | 63.9 | 71.6 | - | - | **67.8** | **1.06** |
| CF7D (new) | two running hashes over 5 million letters | 18.8 | - | - | - | **19.1** | **1.02** |

26 problems.  Best Rocq / C++: median 1.09; 17 at or below 1.25; 23 at or below 1.5; the largest 3.24.

With the bounds proofs (the setting `proofs`, step 3) the 36 programs of `hand/` take 2.0% fewer cycles on average
than with the default, timed side by side (`results/bounds_cost.txt`: 3.3% less time; 14 programs faster by more than
3%, 3 slower).  The most: CF295B's second version, 122 -> 98 ms (that problem's ratio 3.24 -> 2.6); CF453B 437 -> 387.

On a second machine -- an Intel Core Ultra 9 285H, the same image, Docker in a virtual machine on Windows -- `all.sh`
from an empty directory passes every check as well, with the same measured choices (`results/all_285H.txt`).  Its
table (`results/table_285H.md`, best of 7): median 1.23; 16 at or below 1.25; 21 at or below 1.5; the largest 2.65.
The ratios move with the processor, both ways: CF163A 0.77 -> 2.65 (the same C++ code runs 4.3 times faster there, the
Rocq program 1.25 times), CF631E 0.96 -> 1.37, CF61E 1.03 -> 1.28; CF380C 1.07 -> 0.94, CF295B 3.24 -> 2.65, CF1172F
0.97 -> 0.90.  So "about 1.1x" is this laptop's figure; on that one it is about 1.2x.

**Against CertiRocq as it comes** (`tests/stock.sh`, `results/stock_vs_ours.txt`; on the second machine, against its
table): the same Rocq text built by the unmodified compiler -- its defaults, its own runtime and integer operations, a
`nat` as a chain of cells, no translator, no clean-up of the C -- with the same memory support and the same clang
flags.  Every stock build gives the right answers.  Ours is faster on all 51 programs: 8.8 times on average (geometric
mean; median 6.7; from 2.7 to 61 times) -- 8.5 times on the programs written by the guideline, 9.4 times on the corpus
texts (which do not go through the translator).  Per problem, the fastest stock build is 13 times the C++ (median),
ours 1.2 times.  The checker adds no speed of its own: it is what makes writing the memory in place, and removing
saves from the C, safe.

How to read it:

- **C++** is an independent solution as a contestant writes it, with one care taken: it has all its memory before its
  clock starts (a Rocq program is handed its memory), so neither side is timed asking the operating system for pages.
- **C++, 8-byte cells** is the same C++ with every array 64 bits wide: the data layout a Rocq program is given (a cell
  holds one 63-bit integer).  Where this column is far from the first, the distance is the layout, not the language.
- **C++ written the same way** exists where the fast Rocq version does something the contestant's C++ does not (no
  jump on a bit of the data, a heap of its own, additions never pushed down).  Against THAT column the Rocq program
  shows what the route itself costs.
- **Rocq, corpus text**: the program as the corpus has it, with one change -- a returned pair is not taken apart and
  built again (`sv2fast.py --eta`; the corpus files were printed by a translator that does this).  Not through the
  translator of this folder.
- **Rocq, by the guideline**: the fastest of the programs in `hand/` for that problem (with wide or with narrow blocks),
  put in the standard form by the translator, its choices made as measured.  They are Rocq.  No C is written for any
  program.
- The laptop is shared with other work: between sessions the figures move by up to about 10%, the C++ ones too.

Where this started (the first harness): CF455A 32 ms, CF380C 255 ms, CF1100F 312 ms, CF868F 3300 ms.

## The scope (owner, 2026-10-14)

Speed comes from two places only: HOW THE ROCQ IS WRITTEN (`WRITING-FAST-ROCQ.md`) and a GENERAL PIPELINE that is the
same for every program (the translator; CertiRocq, patched once; the clean-up pass; the support code).  No C is
written for a program, and nothing in the pipeline knows which program it is compiling.  The test that every memory
access makes stays by default -- the most stable way, whatever it costs (owner, 2026-10-14) -- and the bounds proofs
of step 3 are a setting.

And: what the pipeline promises is settled BEFORE the C compiler runs.  The C compiler is used as it is; its own
choices are a spread that hand-written C has just the same (`results/compilers.txt`: the generated C under gcc
instead of clang is between 0.83 and 1.68 times as fast, the hand-written C++ references under g++ instead of clang++
between 0.70 and 2.46), and nothing here is tuned to them.

## What keeps a program fast, and the same however it is written

1. **The translator, step 1** (`KQFast.v`; a program ends with `MetaRocq Run (kq_fast_full 3 KQTests (PUse [..])
   main).` and `Lemma main_kq_eq : main_kq = main.`).  It defines, next to every function `f` of the program, a twin in ONE
   STANDARD FORM -- helpers written out, every step named, the same step named once (a cell read twice is read once),
   the order of independent steps fixed by a rule -- and proves it equal to `f`; the KERNEL checks each proof.  These
   steps are plain computation, so each proof is `eq_refl` (after the functions `f` calls are put back in place of
   their twins): there is no proof script, and nothing about the translator is trusted -- a mistake in it stops the
   build.  The compiler is given `main_kq`.
   - What the standard form makes equal: `results/same.txt`, column C (next section).  What it does not: the order of
     a function's parameters; `a + b` against `b + a`, `2 * o` against `o + o` (equal, but not by computation alone).
   - The rule for the order was chosen by measurement (`results/order.txt`): of the three tried on the 28 programs,
     "each piece of arithmetic as early as the numbers it needs exist" is on average as fast as the programs as
     written (1.00; the worst 1.10).  No rule is the fastest for every loop.
2. **Step 2: steps of the second kind.**  Two rewrites are equal to the text only CASE BY CASE, not by computation:
   two arms that do the same steps on numbers that may differ (two calls of one loop, two writes of one cell) made ONE
   sequence of steps with each differing number chosen without a jump; and a choice on a combination of tests
   (`c1 && c2`) made one conditional move per test.  They are made only where the measurement (4) says the test is
   guessed wrong often.  A function with such a step gets two twins -- `f_kq1` without them, equal to `f` by
   computation, and `f_kq` with them -- and "`f_kq` and `f_kq1` give the same result for every argument" is PROVED by
   one tactic, the same for every program (`kq_fast_qed`: induction on the loop's budget, then a case split on every
   test until both sides are the same text), for that function and for every function that calls it.  The kernel
   checks the proof; no axiom is added.  Measured (`results/step2.txt`): CF1100F as first written -- three `if`s
   choosing between recursive calls -- 125 ms before this step, 81 ms with it; its second version 101 ms, then 61.
3. **Step 3: reads and writes without the test** (`KQBound.v`) -- A SETTING, OFF BY DEFAULT.  Off (`KQTests`), every
   read and write tests its cell, as the model defines `rd` and `upd`: nothing more to believe, the same for every
   program and every way of writing a loop, and no correct program kept from building.  On (`KQProofs`: the word
   `proofs` in `hand/NAME.bounds` for one program, or `KQBOUNDS=proofs` for every program of a run; `bounds.sh` reads
   both), the following.  A loop that COUNTS -- its budget is the number of
   rounds left, a parameter p goes up by one every round -- reads or writes cells p (or p + d) of a block named by a
   number (or by a parameter it passes on unchanged), and they are all inside the block when the last one is.  The
   translator writes such a loop twice: with the tests, and without them (`rd_u` / `upd_u`: in Rocq the same
   functions as `rd` / `upd`, equal by computation; on the machine a load or a store and no test).  What callers call
   makes ONE test at the start (`kq_fits`: "is p + d + budget inside the block?") and takes the loop without tests
   only if it says yes.  That the loop without tests never leaves its block is a PROOF: the translator also writes a
   copy of the loop that carries the fact as an argument and a proof at every read and write (`rd_p` / `upd_p`, the
   fact passed on to the next round by lemmas of `KQBound.v`); Rocq's type checker checks that copy, which is never
   compiled, and the loop without tests is that copy with the proofs taken out -- both come out of ONE pass of the
   translator, and the kernel checks that the loop without tests is equal to the loop with them.  (A copy that carries
   its proofs cannot itself be the compiled loop: CertiRocq builds closures or a value per round for it, measured,
   also with its typed erasure.)  Measured (`results/step3.txt`, the machine's cycles, all 36 programs): 1.8% fewer on
   average; ten programs 3% - 15% fewer; four 3% - 14% more although each executes fewer instructions (in CF295B's
   narrow version the C compiler keeps two of the loop's numbers on the stack).  That gain depends on the C compiler
   and on the shape of a loop, and the proofs are made per program: hence off by default.  `all.sh` builds every
   program with them as well (set P), so the setting is checked every time -- every proof, every answer.
4. **The measured choice** (`prof.sh`, `kqsel.py`).  Whether a choice is faster as a jump or without one depends on the
   data and on nothing else (5x one way on a search, 3x the other way on a test that is true 99 times in 100).  So
   each test that can be made without a jump -- between two numbers, or between two arms doing the same steps -- is
   measured once: the program is built with every test counting how often a machine would guess it wrong, and run on
   its input; a test guessed wrong one time in ten or more is made without a jump (`hand/NAME.sel`).  "Without a
   jump" is the machine's conditional move written out in the support code (`kq_select`): no C compiler can turn it
   back into a jump.
5. **The checker** (`KQShape.v`, `MetaRocq Run (kq_gate main_kq).`) reads what is compiled and refuses four things and
   no other: a memory used after it was handed on (any number of readers, or one writer; after a write the old memory
   is gone -- the borrowing rule of Rust in small), a value built in a loop, a loop whose call to itself is not its
   last step, a function used as a value.  A refusal is an ERROR: the file does not compile and no C is made.  The
   first refusal is about being RIGHT (the memory is written in place); the other three are what would take memory
   from the collector, or stack, in a loop.  Nothing is refused for being possibly slow.  It accepts all 36 programs
   of `hand/` and refuses the corpus texts that build pairs (those use `kq_shape`, which only reports).
6. **What is left in the generated C** (`kq_post3.py`, printed for every build): values built inside a loop, closures
   built, calls through a closure.  All three at zero -- FLAT -- means the program never touches the collector in a
   loop.  It is read off the C that is compiled, so it also catches what no reading of the Rocq text can: the
   COMPILER leaving a heap object behind (which is how the third compiler patch below was found).

And **the rules** (`WRITING-FAST-ROCQ.md`): nine of them, each with its measured case -- what is left to the writer.
Rule 9 is new: numbers that fit in 32 bits go in NARROW blocks (`rd32` / `upd32`, cells of 4 bytes, a family of blocks
of their own; `mknarrowbody.py` / `mknarrow.py` make a narrow version of a program and of its memory).  Measured
(`results/narrow.txt`): CF35C 19.9 -> 13.6 ms, CF235C 42.7 -> 30.7, CF385C 167 -> 123 (the C++: 125), CF61E 79 -> 69
(the C++: 69); CF295B, whose time is arithmetic, is slower narrow.  The table keeps the faster version of each.

## The same loop written many ways (`tests/same.sh`, `results/same.txt`)

"Consistent" made into something a machine checks: eight small loops, each written in up to eighteen ways that mean
the same -- every step named or none, helpers, a wrapper, the `if` turned round, a cell read twice, the numbers of a
choice worked out before the `if` or inside it, `kq_select` written by hand.  Each way goes through the whole
pipeline.

| Loop | ways that must be the same | of them the very same C as the first | their times, ms | other ways (times the first) |
|---|---|---|---|---|
| sum: a loop that only looks | 14 | 7 | 5.8 - 6.4 | `second_test` (rule 8) 1.43; `from_the_end` (other arithmetic) 0.95; `two_loops_in_turn` (rule 2) 0.87; `state_in_a_cell` (rule 1) 1.54 |
| toss: a choice the machine cannot guess | 9 | 7 | 10.7 - 11.1 | `by_arithmetic` (other arithmetic) 1.00 |
| heavy: the same, more work on each side | 5 | 4 | 18.2 - 19.1 | - |
| rare: a choice nearly always the same way | 3 | 2 | 8.3 - 8.4 | `select_written` (rule 4) 2.98 |
| clamp: read one block, write another | 7 | 5 | 8.7 - 9.2 | - |
| count: read, then read and write | 4 | 4 | 9.9 - 10.3 | - |
| search: a choice at every step of a search | 6 | 5 | 146 - 148 | `second_test` (rule 8) 1.12 |
| tree: a function that calls itself twice | 2 | 2 | 10.2 - 10.3 | `doubled_by_adding` (other arithmetic) 1.06; `total_passed_on` (other arithmetic) 0.88 |

50 ways must be the same as the first way of their loop: all give the same answer, and 36 of them come out of the
translator as THE VERY SAME C, letter for letter (names aside) -- for those "the same speed" is not a measurement.
The other 14 differ in things the translator does not touch (the order of the parameters, `a + b` against `b + a`, a
test turned round) and run within 6% of the first way (`results/same.txt`, timed on the host with the machine's
counters: the instructions and wrong guesses of every way; default settings).  The four ways that used to be 4 to 7 times slower --
the same choice written as two calls, or as two writes -- are now among the `same` ones.  (The run inside `all.sh`
once marked a way 1.48 times slower whose C is the very same as its first way's, on a busy laptop: since then a way
of the very same C is not counted, and a way that seems slower is timed again side by side with its first way.)

Before the translator the same test gave (default build): ways of one loop between 0.74 and 1.44 times each other;
the search loop a jump in EVERY way (930 ms, where 136 ms is possible); a choice between two slightly heavier numbers
a jump or not according to where the numbers were worked out (66 ms against 18 ms).

The ways marked `rule N` break a rule of the guideline on purpose, and the table shows what that rule is worth;
`select_written` is a hand-written `kq_select` on a test that is nearly always the same way: an override against the
data, 3.0 times slower.

With the bounds proofs (`KQBOUNDS=proofs`; `results/same_proofs.txt`, the run before this setting existed) the test
passes as well (the slowest of the 14 at 1.08), and the loops are faster where step 3 applies (sum 4.5 - 4.9 ms,
clamp 6.0 - 6.4) -- but the way that counts DOWN (`from_the_end`) gets no step 3 and is 1.36 times the way that
counts up.  With the tests it is 0.95: that is the difference between the two settings in one line.

## What makes it fast (the pipeline; program text untouched)

In the order the program meets them.

1. **The translator** (above: steps 1, 2 and 3).
2. **A patched compiler** (`patch/kq_patch.py`, image `kernelq-certirocq:1b45a1aa-kq2`).  Three constants and a
   backport; every pass keeps its proof.
   - The inliner's budget.  CertiRocq halves it at every call it inlines and starts at 100, so about six inlines along
     a path.  It is now 100000 and an inlined body takes a sixteenth of it.  The one lemma about the split is
     re-proved.
   - `CertiRocq Extract Inline [ .. ]`, backported from upstream: definitions to write out at their uses.
   - What counts as a "small" function, written out at its calls: a body smaller than 10 became smaller than 40.
     Why it matters: calling a function of k parameters goes through k-1 small helpers that uncurrying leaves, and
     the helper for parameter 8 onward is just over 10.  So a RECURSIVE function with more than seven parameters,
     called from two or more places, kept two heap objects and a call through a pointer per call -- and, because a
     closure's parameters can be anything, saves round every call of that function.  CF813F with its text unchanged:
     90 ms before, 62 ms after.
3. **A loop budget is one machine number** (`KQNat.v`): `nat` is mapped to a machine integer, `match` on it to a test
   against 0.  Without this a budget of five million is a chain of five million cells.
4. **Safe helpers are written out** (`sv2fast.py`, for the corpus texts; the translator does it for the others).
5. **Compiler settings**: `--anf-variant 9 --c-args 1000 --allow-unsafe-erasure`.
   - `--c-args 1000`: every parameter of a function is a C argument.  By default about five are, and the rest go
     through an array in memory at every call (CF1100F: 480 -> 312 ms when this was raised).  1000 means no limit in
     practice: the largest generated function has 14 parameters, and the limits 14, 24, 100 and 1000 give the very
     same C (all 144 programs of `regen.sh F E H P I`, compared letter for letter).
   - `--anf-variant 9`: lambda lifting (an inner function gets the outer variables it uses as arguments, instead of
     a heap object carrying them) whatever the number of arguments: no closure environment is left.
   - `--allow-unsafe-erasure`: five optional passes of MetaRocq's erasure that carry no proof (hence the name; each
     always does the same thing to the same text).  Two do work here: the loop counter as one machine number
     (`KQNat.v`) and writing out the definitions named in `Extract Inline`; beta reduction and unboxing simplify; the
     fifth (coinductive types) never applies.
6. **A clean-up of the generated C** (`kq_post3.py`).  It removes or moves lines of exact shapes, adds one statement
   per loop, and stops on anything it does not recognise.
   - ROOTS.  Before every call the generated code saves each live variable where the collector can find it, and
     reloads it after.  A machine integer, a boolean or the memory token points to nothing.  A whole-program pass
     finds the variables that can only hold such values -- including a number taken back out of a pair, by tracking
     what each field of each built value can hold -- and removes their saves.  A function with nothing left to save
     links no frame, and its last call becomes a jump.  **This was the largest single cost**: CF868F built with the
     collector went from about 1000 ms to 205 ms when this was added.  The collector is untouched and still sees
     every pointer.
   - The check for free space made on entry moves into the cases that build something.
   - RECOMPUTE.  A loop's "go on or stop" boolean is computed by the caller and carried into the next round as a
     number.  When every caller computes it the same way from arguments it also passes, the function computes it
     again on entry -- same value, but the C compiler now sees the test next to the numbers.
   - MERGE.  When both arms of an `if` end by calling the same function, each arm only sets variables and one call is
     made after the `if`.
   - INLINE.  The pieces of one loop (every `if` of the program is its own C function) are marked to be written out
     into the function where the loop is entered.
   - DEAD, FLAT.  A function nothing reaches is not written out; and the report of what is left (above).
7. **Support code** (`sup/v4/`), the same for every program -- see the next section.
8. **Build**: `clang -O2 -flto`, the cleaned C and the support code together (`mk.sh`).  No other setting.

## The support code: what it is, and what it is not

A Rocq program of this kind uses a few things that have no body in Rocq.  The support code is their body, written
once.  Where it stands in for something that HAS a body in Rocq, the table says so.

| In Rocq | Has a body in Rocq? | In C |
|---|---|---|
| `rd`, `upd`, `mem` (the memory) | no: declared only | `kq_rdb` / `kq_updb` in `kq_io.h`: a test "inside the block?", then one load or store on a C array written in place |
| `+ - * < land lsl ..` on `int` | no: built into Rocq | inline C on the marked word (`kq_io.h`).  CertiRocq's runtime has these as function calls, and three of its versions are wrong (signed remainder, arithmetic shift, unsigned comparison) |
| `kq_arg`, `kq_input`, `kq_sum` | no: the outside world | the command line, the starting memory, a checksum (`kq_io3.c`: the test harness) |
| `kq_in`, `kq_out` (input, output) | no: the outside world | the next number of the input into a cell; a number added to the output (`kq_io3.c`) |
| `kq_nat` (a number as a loop budget) | yes -- C stands in for it | the number itself.  A `nat` is one machine number here (`KQNat.v`); Rocq can only make one by counting up to it |
| `kq_select`, `kq_sel_*` (a choice without a jump) | yes: each is `if .. then a else b` -- C stands in for it | the machine's conditional move, written out (x86-64); elsewhere three logical operations on a hidden mask.  The same value as the `if`; what differs is that it cannot become a jump |
| `kq_prof` (in a measuring build only) | yes: it gives back the test it is handed | the same, and counts |
| `/`, `mod` (Z's: rounding down) | **yes** (`KQRun.v`) | nothing: compiled from the Rocq text.  Until 2026-10-14 two C functions stood in for them; measured since, the Rocq text is as fast (`tests/TestDiv.v` checks it against Z) |
| `rd32`, `upd32` (narrow blocks) | no: declared only | `kq_rd32` / `kq_upd32`: the same test, a 4-byte cell, the number kept modulo 2^32 and read back signed |
| `rd_u`, `upd_u`, `rd32_u`, `upd32_u` (step 3) | **yes**: each IS `rd` / `upd` / `rd32` / `upd32` (`KQBound.v`) | one load or store and NO test.  Right only for a cell inside its block, so the translator writes them only where its checked copy carries a proof of that |
| `kq_len`, `kq_len32` (a block's length) | no: declared only (no operation changes a length) | the length the block was loaded with |
| `kq_fits` (the test at the start of a loop of step 3) | **yes** (`KQBound.v`, on Z) | the same comparison on machine numbers, without overflow |

Two changes to it made everything faster and are worth knowing:

- `rd` / `upd` test and address a cell on the marked number as it is (an `int` n reaches C as 2n+1): `x < 2*len`,
  then the cell at `p + 4x - 4`.
- The slow path of an access (outside the block: give 0, write nothing) is kept from being merged with the fast one.
  Left alone, the C compiler merges the two loads into one "load through a pointer", and every access of every loop
  must then first build that pointer: two more instructions per access.  One word in two lines of `kq_io.h`; up to a
  fifth of the time of a tight loop.

## Input, output, and two tasks at once (`demo/`)

A small program of the kind one writes in C, in the same fragment and through the same pipeline: a producer that
reads the input into a ring of 1024 cells, a consumer that takes numbers out and writes a checksum now and then, and
a scheduler that gives each one step in turn.

- A task is a STEP, a function from the memory to the memory; what a C thread keeps on its stack between two steps it
  keeps in cells of its own; a task that cannot go on gives the memory back unchanged.  This is concurrency as one
  processor does it -- the tasks are interleaved, and here the interleaving is the program's own, so it is a function
  like any other.
- Input and output are writers on the memory (`kq_in`, `kq_out`): the outside world is part of what a memory stands
  for, so the checker's one rule keeps them in order.

`demo/run.sh` runs it three ways: compiled (28.5 ms for 2 million numbers), as a C++ program doing the same
(16.3 ms; identical output), and BY ROCQ ITSELF -- the same text with the memory, the input and the output
defined as plain Rocq data (`demo/model_hdr.v`), computed on 2000 numbers: the output Rocq computes is the output the
compiled program writes.  The text that is compiled is an ordinary Rocq function, and can be reasoned about as one.

What this does not give: tasks that run at the same instant on two processors and share cells.  The memory is one
value handed from step to step; two processors writing it at once is outside the model (it is where CakeML, Pancake
and CompCert also stop, or go through a separate account of the outside world).

## The machine: a kernel written in Rocq (`hw/`)

The same pipeline, for a program with no operating system under it.  Everything C can do to hardware WITHOUT
assembly is in `KQRun.v`, generic and portable; what needs the processor's own instructions, the PROGRAM writes itself
in Rocq -- machine code from the processor's manual, put in memory and run (`hw_run`) -- so the kit's core knows no
instruction set; and what a program may assume about the generic part is a set of laws, `KQSpec.v`, against which its
logic is PROVED -- the hardware is trusted, the logic is not.

**The generic part** (`KQRun.v`; bodies in `hw/kq_hw.h`, plain C -- `volatile`, C11 atomics, `memmove` -- the same
text for every processor GCC or Clang build for):

| Operations | What for |
|---|---|
| `hw_load w a h i`, `hw_store w a v`, `hw_store64` | device registers and raw memory at an address, 1, 2, 4 or 8 bytes (8: two 32-bit halves) |
| `hw_atomic op w ..` (add, subtract, and, or, xor, exchange), `hw_cas w ..`, `hw_aload` (acquire), `hw_astore` (release), the 64-bit ones, `hw_fence` | atomics and fences |
| `hw_copy`, `hw_fill`, `hw_cmp` | bytes in bulk (`memmove`, `memset`, `memcmp`) |
| `hw_call` | code at an address (a function pointer) |
| `hw_run n a x0 .. x5 h i`, `hw_code_sync a n` | machine code the program wrote itself (into a narrow block): run as a C function of six words, its two results into cells; the processor told first that those bytes are code |
| `hw_addr` | where a narrow block is: for tables the processor or a device reads by itself, built in narrow blocks (cells of plain 32-bit numbers) |

**The processor's instructions, written in Rocq** (`hw/X86.v`; how to write one: `hw/WRITING-INSTRUCTIONS.md`).  C
has no portable way to switch interrupts off or set the page tables, and compiler intrinsics are per family.  Rather
than C bodies with inline assembly for a fixed list of operations, a program writes the instructions it needs: their
bytes, computed in Rocq from the processor's manual (the ModRM byte from its fields), are put in a narrow block and
called through `hw_run`.  `hw/X86.v` does this for every x86-64 instruction the kernels use, as an ordinary file a user
could have written: `x86_setup` writes 28 routines once, and then `hw_irq_off`, `hw_irq_on`, `hw_irq_wait`, `hw_pause`,
`hw_pt_set` / `hw_pt_get` (cr3), `hw_tlb_page` / `hw_tlb_all`, `hw_fault_addr` (cr2), `hw_vectors` (lidt),
`hw_sysreg_get` / `hw_sysreg_set` (MSRs), `hw_cycles` (rdtsc), `hw_port_in` / `hw_port_out`, `hw_cpuid`, `hw_cr_get` /
`hw_cr_set` are plain Rocq functions.  The build puts the file's text in front of every program (`ISA=X86`), so the
translator and the checker see inside it.  Another processor is another such file, from its own manual: a RISC-V one,
its encodings checked against the assembler but not run, is `hw/riscv/`; a program that keeps to the names the two
share builds for either.  A call costs little: 0.8 ns a round in a loop of calls to a routine that only returns,
against 0.3 - 0.6 ns for a loop of memory reads (KVM, the i9-12900H, the fastest of 20 rounds each).

**What the runtime gives** (`hw/Runtime.v`): `hw_irq_take` (the oldest interrupt noted), `hw_irq_info` (in a program
run at an interrupt: which one), `hw_irq_entry` (where the runtime's entry code of vector v is), `hw_cpu_code` (the
code another processor starts in), `hw_sym` (the runtime's own addresses, for code a program writes that must call
back into it: its C handler of interrupts, a second processor's C code).

**How it is all linked.**  Every operation of `KQRun.v` and `hw/Runtime.v` is declared the same way any routine of a
program's own is: an `Axiom` with a type, linked by the build to the C function `kq_hw_<name>` (`hw_load` ->
`kq_hw_load`, `hw_run` -> `kq_hw_run`; a program's own routines through `hw/NAME.ext`, written in `hw/NAME.S` or `.c`),
all of them plain C in `hw/kq_hw.h`.  The checker has one rule for all of them, read off the type: a routine declared
without a body is a machine operation (it may be called in a loop), and it writes the memory unless its result is a
plain number -- so each takes the memory and gives it back, and the checker keeps them in the program's order.  What
one reads goes into a cell.  `hw/boot.S` (the Multiboot entry, the switch to 64-bit mode, 256 interrupt entries, the
start of another processor) and `hw/kq_bare.c` (the memory's table, the serial line, the interrupt queue, an area for
values per program: no C library, no collector) take the place of the test harness; they are what is left of x86 in
the kit, with a handful of instructions in `hw/kq_bare.c` (its own serial output, stopping QEMU, interrupts off around
the queue, halting).  `hw/kq_hw.h` keeps every access in the program's order (`volatile`, a compiler barrier), which is
how C does it too -- CompCert included: a `volatile` access is kept as written; its proof covers volatile accesses to
global variables as input/output events, and assembly not at all.

**The laws** (`KQSpec.v`): what a proof may assume.  The memory's are its definition (a cell holds what was last
written; outside a block a read gives 0 and a write does nothing; wide and narrow blocks are apart).  The machine's are
the hardware's promises, kept small: a load of w bytes gives back SOME number in 0 .. 2^(8w) - 1, into the cell asked
for, and changes no other cell; a store, an atomic, a copy, a fill change no wide cell (`hw/kq_hw.h` refuses those
addresses), and no narrow one when their bytes fall outside every narrow block; what the devices see -- every load,
store, fence -- is recorded in order (`hw_trace`).  Nothing says WHICH number a device gives: a proof holds for every
number it could.  A call through a pointer promises nothing.  All of it is ONE axiom, `real_laws`; `KQModel.v` defines
every operation in Rocq and proves every law, so the laws cannot contradict each other -- that proof rests on nothing of
ours (`Print Assumptions`: Rocq's own 63-bit integers only).  `KQSpecDemo.v` proves kernel code against the laws, each
proof resting on `real_laws` alone:

- a byte from a device used as the index of a table of 256 entries is in bounds, whatever the device sends;
- a store to a device changes no cell of the program;
- the page-table fill of `hw/fault.body`: entry k is 2 MB * k + 131 (present, writable, 2 MB) for every k < 512, its
  high half 0 -- by induction on the loop, every number checked against 63-bit overflow.

`hw/spec.sh` (run by `hw/check.sh`) compiles all three and checks what each proof assumes.

Interrupts: the entry code either calls a Rocq program at once (below) or only notes the vector in a queue, which
the program takes with `hw_irq_take` at a point of its own.  So Rocq code never runs inside other Rocq code, and nothing needs a model of concurrency.  (The
processor's own faults -- a page fault, a protection fault -- cannot wait: they stop the machine with a message.)

`hw/kernel.body` is a kernel written in Rocq that uses all of it: a serial driver; the text screen through
memory-mapped accesses; its own page tables, the first 1 GB mapped to itself and the screen once more at 1 GB, the
processor switched to them; its own interrupt table, the interrupt controllers and the timer programmed through ports,
ten timer interrupts taken and acknowledged; the time-stamp counter, an MSR, `cpuid`; 8-, 32- and 64-bit accesses;
PCI configuration space through 32- and 16-bit ports; 32- and 64-bit atomics (add, exchange, a compare-and-swap that
succeeds and one that does not, acquire loads, release stores); bulk fill and copy; and two routines of its own in
assembly (`hw/kernel.S`: one pure, one that writes memory) -- every x86 instruction in it from `hw/X86.v`.  It goes
through the translator (47 functions with `hw/X86.v`'s, each equal to its twin, checked by the kernel) and the checker
(9 loops, nothing built in any) like every other program.  `hw/check.sh`
(on a host with QEMU) builds it, starts it under QEMU's own processor and under KVM (the host's), and runs a control:
the same kernel with one page-table entry pointing at the wrong 2 MB, which the page check must see.  2026-10-15:

```
Rocq kernel
mmio 0
page 0
time 10
cpu  GenuineIntel                 (under QEMU's own processor: AuthenticAMD)
ram  0
pci  4663                         (0x1237: the host bridge QEMU emulates)
atom 0
bulk 0
asm  0
KQ-RESULT 0 checksum .. interrupts lost 0         QEMU exit status 1: the program answered 0
control: page 16                  the wrong mapping is seen
```

**Rocq at the moment of an interrupt, faults, several processors** (`hw/irqnow`, `hw/fault`, `hw/smp`).  A kernel
may have up to three Rocq programs, each through the same pipeline, linked into one file (`hw/build.sh`):

- `hw/NAME.body`, the main one;
- `hw/NAME_irq.body`, run AT THE MOMENT an interrupt or a fault comes: the entry code calls it with its own area for
  values (and no vector registers: it is compiled without them); `hw_irq_info` says which interrupt; its answer 0 means
  handled -- for a fault, the instruction is tried again;
- `hw/NAME_ap.body`, run by a second processor, which the main program starts itself: the startup code copied to
  0x8000 (`hw_cpu_code`), INIT and STARTUP sent through the local interrupt controller's command register.

They share the memory's blocks; each leaves alone what another writes, or goes through the atomics.  Measured
(`hw/check.sh`, 2026-10-15, QEMU's own processor and KVM, the same lines on both):

| Kernel | What it shows | Result | Its control (must fail) |
|---|---|---|---|
| `irqnow` | the timer's interrupts counted by Rocq code run at the moment each comes (it acknowledges each); the main program only waits | `irq 10`, 10 handled at once | the handler does not acknowledge: `irq 1` |
| `fault` | a write to an unmapped address faults; the Rocq fault program maps that 2 MB to 64 MB; the write is tried again and lands | `map 0`, `flt 1` | the fault program maps the wrong 2 MB: `map 1` |
| `smp` | the second processor started by the Rocq program; both add 1 to a shared counter 1 000 000 times at the same moment | atomic counter `2000000`; the plain read-and-write one 1 000 837 (KVM) / 1 289 400 (QEMU): updates lost | the second processor never started: `cpus 1` |
| `own` | an interrupt entry routine the program writes itself (53 bytes of x86-64, in Rocq: registers saved, the runtime's C handler called through `hw_sym 0`, `iretq`), put in its interrupt table for the timer; and what `hw_run` costs | `own 10`: every timer interrupt came in through it; `run 2309`, `load 895` - `1732` (KVM: time-stamp ticks per 1000 calls / reads, the fastest of 20 rounds) | the routine hands the runtime vector 33: `own 0` |

The plain counter is what shows the two really ran at once (first written with the atomic loop first, it came out
exact: the two plain loops never met); only the atomic one keeps every update.

Still not covered: a Rocq program at an interrupt that interrupts ANOTHER Rocq program at an interrupt (interrupts stay
off while one runs), interrupts on the second processor (it has no interrupt table), and a fault inside the
interrupt program itself (it stops the machine).

Adding the operations, and then making them generic, changed no other program: all 144 generated C files and the 108
cleaned ones are the very same as before, letter for letter, and the checker's verdicts on all of them too.  Trusted,
beyond the list below: `real_laws` -- that the hardware and `hw/kq_hw.h`, `hw/boot.S`, `hw/kq_bare.c` do what the laws
say -- and the instructions a program writes (`hw/X86.v`): that their bytes are the instructions meant, which a model
of the processor could check, and what those instructions do.  The C of `hw/kq_hw.h` could be proved against the laws
with VeriFFI / VST (Korkut, Stark, Appel); what an instruction does cannot be proved by anything short of a model of the
processor and its devices.  

## What was checked

- **Every program of `hand/`, by the kernel** (36 of them; 17 steps of the second kind in the last run): what is
  compiled is equal to it (`main_kq = main`, by computation and by induction; the only axioms under that are the
  program's own primitives -- `Print Assumptions` lists `rd`, `upd`, the integer operations).
- **The same 36 programs with the bounds proofs** (the setting `proofs`; set P of `all.sh`; 98 loops without
  tests in the last run): equal to the program as above (`kq_len` joins the primitives), every loop without tests has
  a copy with a proof at each of its reads and writes, which Rocq's type checker accepts, and every answer on the
  large inputs equals the C++ run's, with both collectors.
- **All 18 corpus programs, two variants each** (text exactly; pairs not rebuilt): on a random input, result and a
  checksum of the whole memory equal those of the ORIGINAL program (Z, lists), computed inside Rocq by `vm_compute`.
- **All 26 timed problems, every program** (66 Rocq builds): every answer on the large inputs equal to the C++ run's.
- **The removal of saves** (the one step that could corrupt memory silently): everything above repeated with a
  collector that runs every few allocations (`sup/stress`, a nursery of 32 words), on the random inputs and the large
  ones.  As a control, the same with EVERY save removed gives wrong answers on CF380C and CF235C -- the test can see
  the fault it is there for.
- **The machine-integer operations** against a plain reference (`tests/test_arith.c`, negative numbers and the
  edges of 63 bits), and **Rocq's division against Z's** (`tests/TestDiv.v`, 961 pairs).
- **The checker** on 18 small programs with a known verdict (`tests/shape/`): ten faulty ones it must refuse -- each
  a way a memory written in place would give a wrong answer, or a loop a heap object -- and eight sound ones it must
  accept; and the gate itself (a refused program must not compile).
- **The same loop written many ways** (above): same answers, same speed.
- **The measured choices**: measured again from nothing and compared with the stored ones.
- **The two tasks**: same output as the C++, and as Rocq's own run of the same text.
- **The machine** (`hw/check.sh`, 16 GATE lines): the laws (every one proved for a model; the proofs about kernel code
  resting on them alone); five kernels, each checking itself, under QEMU's own processor and under KVM -- every x86
  instruction in them written in Rocq (`hw/X86.v`); and five controls, each a kernel changed in one place, which must
  fail.  And the RISC-V example (`hw/riscv/check.sh`): its 20 instruction words equal LLVM's assembler's.
- The whole folder rebuilt and re-measured from an empty directory by `all.sh`; its GATE lines say whether any of the
  above went wrong.

## What is trusted

CertiRocq's unverified parts (erasure options, the C code generator, its runtime), clang, the support code of
`sup/v4` (the memory, the integer operations, the conditional move, input and output; with the setting `proofs` also
the reads and writes without the test and `kq_fits`; for a program run on the bare machine, `hw/` as well), the convention that a `nat` is one machine number (`KQNat.v`), and the clean-up pass.  The memory
is written in place: that is faithful only for a program that never uses an old memory again -- which is what the
checker's first refusal is; the checker is tested, not proved.  With the setting `proofs`, a read without the test is
faithful because the copy of its loop that carries the proofs type-checks: a proof given at a read means the read is inside its block whenever
it runs -- the same reading of proofs that erasure itself rests on.  The TRANSLATOR is not in this list: what it
produces is checked by the kernel, every time.

## Faults found on the way

None was in a program.

- **Division** (harness).  Rocq reads an argument of type `int` in sint63's own scope whatever scope is open, so `/`
  and `mod` there were the machine's (rounding toward 0), not Z's.  `KQRun.v` now replaces the two notations in
  sint63's scope.
- **Timing** (harness).  A program whose answer is a memory ends with a checksum of the whole memory, and that pass
  was inside the timed region: 60 ms of CF1100F's time.  It is now measured apart.
- **The references** (measurement).  Two C++ references first touched their arrays inside the timed region (the
  operating system hands out each page at its first use: 12 ms of CF1100F's 87), and one built its data with the
  standard library's containers while the clock ran (CF813F: 60 ms; with arrays 30 ms).  Both flattered the Rocq
  side.  Every reference now has its memory before its clock starts.
- **Closures left behind** (compiler): the third patch above.
- **The merged slow path** (support code): above.
- **The checker refused a correct program** (checker; found by the translator's output).  A memory named inside one
  arm of an `if`, when the `if` itself is named, stands at the same depth as the `if`'s own name; the checker took
  the two for one and refused every later use.  No program of `hand/` was written that way; the standard form of
  CF35C is.  Fixed, with two test programs (`tests/shape/`).
- **A choice between two numbers was a jump or not by accident** (the C compiler; found by the test of many ways).
  Described above; closed by the measured choice and `kq_select`.
- **The kernel asked to compare two programs may start to run them.**  A budget is `kq_nat (kq_arg 0)`, a number
  nobody knows before the run; opened, it is 63 nested tests each naming the next one twice, and comparing two of
  those never ends.  `KQRun.v` tells Rocq not to open `kq_nat` when it compares; and the translator hands the kernel
  each comparison with the same functions on both sides, so that it has only arguments to look at.
- **Step 2's proof rewrote the wrong call** (proof tactic).  When a function's two twins have the very same text,
  Rocq's `rewrite` found an occurrence "up to computation" in the wrong place and left the real one.  The footer now
  sets `Keyed Unification` (rewriting matches by name).
- **The kernel ran a loop while comparing** (proof; found on CF460C).  The last step compares `main_kq` with the text
  of the program; the kernel chose to open the program's functions first and started to run `search 64 ..`
  symbolically.  The fact is now stated on the program's text and the footer says `Strategy expand [main_kq]`.
- **Step 3 depended on the spelling** (found by the test of many ways).  Its first version knew `i + 1` but not
  `1 + i`, and a block number but not a block held in a parameter: three ways of the same loop got no step 3 and were
  1.4 times slower than the others.  It now takes both.
- **A loop that carries its proofs cannot be what is compiled** (CertiRocq).  The usual Rocq ways of handing a proof
  from round to round, compiled, build a closure or a value every round, also with CertiRocq's typed erasure:
  measured.  Hence the copy that is checked and never compiled.
- **The checker took minutes on a correct program** (checker; found by `hw/kernel.body`).  After an `if` it joined the
  two arms' lists of memories handed on by appending them; each arm starts from the list before the `if`, so the list
  grew about three times at every `if` on a path, and nine `if`s after a dozen writes took minutes and gigabytes (7:
  30 s, 9: over 2 minutes).  It is a set: joined without repeats now (`union_nat`), 1.3 s, and every verdict on every
  program is the same as before.
- One fast core, pinned (`taskset`): the laptop has fast and slow cores; unpinned runs differ by 10% - 30%.

## What no way of writing removes

Measured (`WRITING-FAST-ROCQ.md` has the table, `results/floor.txt` the first row for every problem): the test
every access makes (nothing to 30% of a program's time) -- everywhere by default; with the setting `proofs` only where
step 3 does not apply: a loop that does not count, or counts but stops early, or reaches cells other than "parameter
plus a number" (a tree's `2 * p`, a queue);
cells of 8 bytes where C++ uses 4 -- now only where the numbers do not fit in 32 bits or the program was not made
narrow; and vector instructions the C compiler uses on the C++ and not on our loops (CF295B: 2.7 times the C++, its
largest distance in the table).

And the C compiler's own choices.  The same generated C built four ways (`results/compilers.txt`, 28 programs):
clang `-O3` against `-O2` changes one program by more than 10%; gcc against clang changes twelve, between 0.83 and
1.68 times, 8% slower on average.  The hand-written C++ references move as much between g++ and clang++ (nine of 26
by more than 10%, between 0.70 and 2.46).  The order of independent statements is part of the same spread: no fixed
order is the fastest for every loop (`results/order.txt`).

**Did not help** (within noise): `-march=native`, a profile-guided build of the C, one C type per block, larger
inlining thresholds, keeping every loop a separate function, telling clang to duplicate code so as to skip a repeated
test, telling clang never to turn a conditional move back into a jump (5.5x on one loop, 17% slower on one program:
not a setting to build on).

## Running it

The images first, once: `bash images.sh` (on the host; Docker, the network, about 25 minutes and 6 GB of memory)
builds `kernelq-certirocq:1b45a1aa` -- CertiRocq at commit 1b45a1aa installed in
`mattam82/metacoq:metarocq-1.5.1-rocq-9.1` by `docker/build.sh` -- and from it `kernelq-certirocq:1b45a1aa-kq2`, the
patched compiler (`patch/`).  Then:

```
docker run --rm --memory=3g --memory-swap=3g --network=none -v $PWD:/w kernelq-certirocq:1b45a1aa-kq2 bash /w/all.sh
```

makes the inputs, compiles everything, runs every check and prints the table (about 25 minutes;
`results/all.txt` is its output).  The image is `mattam82/metacoq:metarocq-1.5.1-rocq-9.1` with CertiRocq at 1b45a1aa
built in it, then `patch/rebuild.sh` (four minutes).  One program on its own: `bash one.sh NAME` (for
`hand/NAME.body`) measures its choices, builds it and prints what every step said; a few seconds.

A program's two settings, both kept next to it in `hand/`:

- `NAME.sel`: the tests made without a jump -- written by `prof.sh` from a measurement; edit it to decide by hand
  (in the text, `kq_select` and `kq_jump` decide one test whatever is measured);
- `NAME.bounds`: `tests` (also when there is no such file: the default) or `proofs` (step 3).  `KQBOUNDS=tests` or
  `KQBOUNDS=proofs` in the environment sets it for every program of a run (`docker run -e KQBOUNDS=proofs ..`).

`pstat.sh` and `tests/same.sh` read the machine's counters (instructions, wrong guesses), which a container may not
read: for those figures run them on the host, in this directory, after `all.sh`.

| File | What it is |
|---|---|
| `WRITING-FAST-ROCQ.md` | the guideline: nine rules, each with its measured case, and what no way of writing removes |
| `patch/` | the compiler patch and how it is rebuilt |
| `images.sh`, `docker/build.sh` | the two Docker images, built as they were: CertiRocq at 1b45a1aa, then patched |
| `KQRun.v`, `KQNat.v` | what a program imports: the memory, arithmetic, the choice without a jump, input and output; nat as a machine number |
| `KQFast.v` | the translator: the standard form (step 1), the steps of the second kind (step 2), the loops without tests (step 3), and the proofs that what is compiled is the program; the tactic `kq_fast_qed` |
| `KQBound.v` | the reads and writes without the test, a block's length, the start test, and the lemmas the proofs of step 3 are made of |
| `bounds.sh` | a program's bounds setting: `KQBOUNDS`, else `hand/NAME.bounds`, else tests |
| `mknarrowbody.py`, `mknarrow.py`, `narrow.tsv` | a program and its memory made narrow (rule 9), and the eight programs that are |
| `hw/` | the machine: `X86.v` (x86's instructions, written in Rocq; `WRITING-INSTRUCTIONS.md`: how to write one; `riscv/`: a RISC-V one, checked against the assembler), `Runtime.v` (what the runtime gives), `kq_hw.h` (the generic operations' C), `boot.S`, `kq_bare.c`, `link.ld`, `build.sh` and `spec.sh` (in the image), `run.sh` and `check.sh` (on the host, QEMU); `lib.body` (in Rocq: the serial line, printing, the interrupt table, controllers, timer); the kernels `kernel`, `irqnow` (+ `_irq`), `fault` (+ `_irq`), `smp` (+ `_ap`), `own`, and `kernel.S` / `kernel.ext`, a kernel's own assembly |
| `KQSpec.v`, `KQModel.v`, `KQSpecDemo.v` | the laws of the memory and the machine (one axiom), a model in which every law is proved, and proofs about kernel code against the laws |
| `KQShape.v` | the checker |
| `prof.sh`, `kqsel.py` | the choices measured; a measuring run turned into choices and advice |
| `sv2fast.py` | a corpus program (`sv/*.sv`) made ready for this route, word for word |
| `kq_post3.py` | the clean-up of the generated C, and the report of what is left in it |
| `sup/v4/` | the C support code (`kq_io.h` is what a loop sees; `kq_io3.c` the test harness; `kq_perf.h` the counters) |
| `hand/`, `hand.tsv` | the 36 programs written in Rocq by the guideline (`.body`), the choices measured for each (`.sel`), and a program's bounds setting where it is not the default (`.bounds`; none is) |
| `problems.tsv`, `big/` | the 26 timed problems and their C++ references |
| `cpp64/`, `cppw/` | the references with 8-byte cells; the references written the way the fast Rocq is |
| `demo/` | two tasks and a scheduler with input and output: the Rocq text, the C++, the model that lets Rocq run the text |
| `mkbig.py`, `mkcase.py`, `mkrefs.sh` | the large inputs; a random input per corpus program; the original's answer on it |
| `setup.sh`, `regen.sh`, `mk.sh`, `check.sh`, `shape.sh`, `bench.sh`, `table.sh`, `all.sh`, `one.sh` | make inputs; Rocq to C; build; compare with the originals; the checker's verdicts; time; the table; all of it; one program |
| `floor.sh`, `pstat.sh`, `mktable.py` | what the per-access test costs; the machine's counters (on the host); the table as Markdown |
| `tests/` | the same loop written many ways (`mksame.py`, `same.sh`, `cnorm.py`, `same_md.py`); the default against the bounds proofs (`bounds_cost.sh`, on the host); CertiRocq as it comes, for comparison (`stock.sh`, in the unmodified image); the integer operations against a plain reference; Rocq's division against Z's; the checker on programs with a known verdict; the control of the stress test |
| `results/` | the output of the last `all.sh` (`all.txt`), its table (`table.txt`, `table.md`); the same on a second machine (`all_285H.txt`, `table_285H.txt`, `table_285H.md`, `same_285H.txt`); unmodified CertiRocq on that machine and the comparison (`stock_285H.txt`, `stock_vs_ours.txt`); the same loop written many ways (`same.txt` on the host with the machine's counters, `same_gate.txt` the run inside `all.sh`, both with the default settings; `same_proofs.txt` with the bounds proofs; `same_before_merge.txt` before step 2); the default against the bounds proofs, side by side (`bounds_cost.txt`); step 2 (`step2.txt`), step 3 (`step3.txt`) and narrow blocks (`narrow.txt`) each measured on and off; the rules for the order compared (`order.txt`); the standard form against the programs as written (`standard_form.txt`); two C compilers (`compilers.txt`); `floor.txt`, `pstat.txt` (both from before the translator) |
