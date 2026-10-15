# Writing Rocq that is fast as C

Nine rules for programs in the plain-function style (machine integers, a memory of numbered blocks read with `rd` and
written with `upd`, loops as `Fixpoint`s on a budget), compiled by the route of this folder (Rocq -> CertiRocq C ->
clang).  Every rule comes from a measured case.  The times are from `results/table.txt` (one fast core, best of 5),
the instruction counts from the machine's counters (`pstat.sh`).

The rules were found on four Codeforces programs, then tried on eleven more programs of the corpus, then on ELEVEN NEW
PROBLEMS written by the rules from the start (`hand/CF61E.body` .. `hand/CF7D.body`).  Those eleven compiled, gave the
C++ reference's answers and built nothing in a loop at the first attempt; seven of them ran within 1.5x of the C++
at once, and what separates the other four is in "What no way of writing removes" below.

**The build puts every program in one standard form first** (`KQFast.v`, since 2026-10-14), and Rocq checks that the
standard form is equal to the program.  So a number of things a writer used to have to get right no longer matter at
all -- how the steps are named and nested, helper definitions, a cell read twice, where the two numbers of a choice
are worked out, two calls of a loop that differ only in numbers -- and one thing is decided by MEASURING instead of by
the writer: whether a choice is a jump (rule 4).  A loop that counts can also lose the test on each read and write
-- a setting, off unless it is asked for (rule 8).  `results/same.txt` is the test of it: eight small loops, each
written in up to eighteen ways.

## What costs what

| You write | The machine does |
|---|---|
| `x + y`, `x <? y`, `x land y` on `int` | one or two instructions |
| a parameter of a loop | a register |
| `rd h i s` / `upd h i v s` | one comparison (is `i` inside the block?), one load or store |
| a `match fuel with O => .. \| S f => ..` | one subtraction and one test (the budget is one machine number) |
| a loop whose call to itself is its last step | a jump back: no call, no stack |
| a function that calls itself twice (a tree) | real calls, as in C; nothing else |
| `(a, b)`, a function passed as a value | memory is taken from the collector: a few instructions each time, a collection now and then, and saves round every call near it |
| a non-recursive helper `Definition` | nothing: it is written out where it is used |
| `if c then a else b` between two plain numbers | what the build MEASURED for that test (rule 4): a conditional move, or a jump |
| `kq_select c a b` | both numbers, then one conditional move -- with a comparison as `c`, two instructions in all; never a jump |
| an `if` whose two sides do different work (a read, a write, another loop) | a jump: the side not taken is work not done |
| a proof, a specification, a type | nothing at all: it is gone before the compiler starts |

So: numbers in parameters are free, memory cells cost a little, pairs cost more, and anything that stops a loop from
being a jump costs the most.

## The rules

### 1. A loop's state goes in its parameters, not in memory cells

A number that changes every round (a position, a running total) should be a parameter of the `Fixpoint`.  Kept in a
cell it is read and written every round, and the C compiler cannot keep it in a register: it cannot prove that the
loop's other writes do not hit that cell.

```coq
(* slow: the running total lives in cell 2 of rST *)
Fixpoint sum (fuel : nat) (i : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => sum f (i + 1) (upd rST 2 (rd rST 2 s + rd rA i s) s)
  end.

(* fast: it lives in a parameter, and goes into the cell once, at the end *)
Fixpoint sum (fuel : nat) (i acc : int) (s : mem) : mem :=
  match fuel with
  | O => upd rST 2 acc s
  | S f => sum f (i + 1) (acc + rd rA i s) s
  end.
```

Measured (CF868F): the corpus text keeps the window's two ends and its cost in three cells; per candidate tried it
runs about 175 instructions, the rewrite 82, the C++ 69.  What does not change during a loop belongs in a parameter
too: worked out once before the loop, not read in every round (CF453B: the number `a[i]`, where the next layer
starts).

### 2. One question per loop; a loop that is done hands over to the next

A loop that asks several questions every round ("which of four things do I do now?") pays for all of them every round.
Give each question its own loop.  When a loop has nothing left to do it calls the next loop as its last step, passing
the state on in parameters.  Define the loops in reverse order (the last one first), so each can name the next.

```coq
Fixpoint shrink (fuel n : nat) (lo acc hi : int) (s : mem) : mem :=      (* second phase *)
  match fuel with
  | O => s
  | S f => if lo <? hi then shrink f n (lo + 1) (acc - rd rA lo s) hi s else upd rST 0 acc s
  end.

Fixpoint grow (fuel n : nat) (lo acc hi : int) (s : mem) : mem :=        (* first phase, then hands over *)
  match fuel with
  | O => s
  | S f => if hi <? lo then grow f n (lo - 1) (acc + rd rA (lo - 1) s) hi s else shrink n n lo acc hi s
  end.
```

Measured (CF868F, `hand/CF868F.body` against `hand/CF868Fv2.body`): one loop asking up to six questions a round,
138 ms; five loops asking one each, 79 ms (the C++: 93 ms).

### 3. A loop's call to itself is its last step

`let s1 := loop f .. in s1` is fine; `let r := loop f .. in something r` is not: the call must come back before
`something` runs, so every round keeps a stack frame.  In particular do not take a returned pair apart and build it
again:

```coq
let p := loop f (i + 1) s in (fst p, snd p)        (* a frame and a new pair per round *)
loop f (i + 1) s                                   (* the same value; a jump *)
```

Measured (CF868F): the corpus text does the first in its scan loop: 599 ms; with only that changed, 171 ms.  CF1039D:
2109 ms against 708 ms.

Recursion that really is a tree -- a segment tree's two calls, a divide and conquer, a merge sort -- is a different
thing and is fine: it is what the C++ does too.  The checker tells the two apart by counting: a function that calls
itself ONCE on a path must do so as its last step; one that calls itself twice or more may do so anywhere.

### 4. A choice is written the plain way -- the build measures it, and makes it without a jump where that pays

A test on the data can become one of two things on the machine.

- A JUMP: the machine guesses which side, and works out only that side.  A right guess costs nothing; a wrong one
  about fifteen cycles.
- A CHOICE WITHOUT A JUMP: both sides are worked out, then one is taken (a conditional move).  A cycle or two,
  always, and nothing to guess.

Which is faster depends on the data and on nothing else (`results/same_before_merge.txt`: the same loops, the jump
forced by writing the choice as two calls; each loop 20 million rounds):

| Loop | With a jump | Without |
|---|---|---|
| a search, the test goes either way | 867 ms | 136 ms |
| a choice between two numbers that take a few operations each, on a bit of the data | 70 ms | 17.6 ms |
| add or subtract, on a bit of the data | 65 ms | 9.5 ms |
| a test that is true 99 times in 100, on the path the loop waits for | 8.6 ms | 24.6 ms |

Nothing in a program's text says which kind its data is.  A C compiler guesses, from the size of the two sides; here
it is MEASURED: `prof.sh` builds the program once with every test counting, runs it on its input, and counts for
each test how often a machine would have guessed it wrong.  A test guessed wrong one time in ten or more is made
without a jump from then on; any other stays an `if`.  The choices are kept next to the program (`hand/NAME.sel`).

What can be made without a jump is decided by the translator, not by how the choice is written:

- a choice between two NUMBERS -- `if c then a else b`, wherever `a` and `b` are worked out: one conditional move
  (`kq_select`, written out in the support code; no C compiler can turn it back into a jump);
- two arms that do THE SAME STEPS ON NUMBERS THAT MAY DIFFER -- two calls of one loop, two writes of one cell, the same
  reads: ONE sequence of steps, each number that differs chosen by a conditional move.  These two give the same
  machine code when the measurement says "no jump":

```coq
if (l <=? q) && (res <? y) then qry f (b - 1) l base y s else qry f (b - 1) l base res s
qry f (b - 1) l base (if (l <=? q) && (res <? y) then y else res) s
```

- a choice on a COMBINATION of tests (`c1 && c2`, `c1 || c2`): one conditional move per test, nested.

The last two are equal to the text only case by case, not by computation, so the translator PROVES them (by
induction on the loop's budget, one tactic for every program) and the kernel checks the proof (`KQFast.v`, step 2).
Measured on the programs (`results/step2.txt`): CF1100F as first written -- three `if`s choosing between recursive
calls, the way that used to need rewriting by hand -- 125 ms before this step, 81 ms with it; its second version 101
ms, then 61.

Two overrides, for the cases a measurement does not settle: `kq_select c a b` is used as written (no jump, whatever was
measured), and `if kq_jump c then .. else ..` is never changed (a jump).  In Rocq both are just the `if`.  An override
against the data costs what the table says: `kq_select` on the test that is true 99 times in 100 is 2.9 times slower.

**When the two sides do different WORK** -- a read in one only, a division, another loop -- a jump skips the work of
the side not taken: that is an `if` between paths, and it stays a jump.  CF165E fills a table of 4 million cells 22
times; a cell changes rarely.  Written "always write": 101 ms.  Written "write only when it changes": 69 ms.

### 5. A loop gives back one thing

A `Fixpoint` in a hot path should return an `int` or the memory.  A pair or a triple is built in memory each time one
is returned.  Four ways out, all measured:

- **A function that only looks gives back a number.**  It may be given the memory as often as you like: the memory
  stays usable after it (the checker calls it a reader).  CF833B's `qmax` pushed pending additions down while it
  looked, so it had to return the maximum AND the memory; with the additions left where they were made it only reads:
  626 ms -> 358 ms (the C++: 347 ms).
- **Look, then remove.**  Taking the smallest entry off a heap returns the entry and the new heap.  Two steps do it,
  each giving back one thing: read the top, then remove it (CF20C: 12.7 ms -> 8.2 ms; the C++ with the standard
  library's queue: 11 ms).
- **Leave the extra result in a cell** -- once, when the loop ends, not every round (rule 1).  CF813F's `apply`
  leaves "did every edge fit" in a cell; CF460C's try leaves its yes / no.
- **Pack small numbers into one word**: three counts below 2^20 are one `int`
  (`t + (o << 20) + (c << 40)`, taken apart with `>>` and `land`).  CF380C: a query returning a triple 77 ms, its
  three numbers left in three cells 64 ms, packed into one word 55 ms (the C++, which returns a struct: 49 ms).

### 6. What is read together sits together -- when that saves a read

Two numbers that are always read at the same moment belong in the same cell, packed.  Half the reads, half the bounds
tests, half the memory touched.

Measured.  CF1100F, a vector and where it came from: two blocks 132 ms, one word per cell 103 ms.  CF20C, a heap
entry (distance, vertex) in one cell: comparing two entries is comparing two numbers.  CF385C, "how many numbers
equal v" and "v is marked" in one cell: 179 ms, where the C++ with the same 8-byte cells but two arrays takes 260 ms.
CF813F, the sort compares what it moves (edge * 2^17 + time in one cell) instead of looking a key up through an
index: 48 ms -> 43 ms.

**Where it did not help** (both kept on record): packing is only worth it when it REMOVES a read.
CF235C, one record of 30 cells per automaton state instead of five blocks: slower (51 ms against 45 ms) -- the walk
touches one or two of the 30 cells, and the record spreads them out.  CF339D, the two children of a tree node in one
cell: slower (179 ms against 149 ms when it was tried; that version is not kept here) -- taking the halves apart and
putting them together again lengthens the one chain of operations every level must wait for.

### 7. Arithmetic: say what the machine has

- `/` and `mod` by a number WRITTEN in the program cost little: by a power of two they are a shift or a mask, by any
  other constant a multiplication.  By a number known only at run time they are a real division (slow on every
  machine): keep that out of inner loops.
- A sum of two numbers below the modulus needs no remainder: `if MD <=? x then x - MD else x` (CF163A).
- "Is bit b of x set" inside a loop over b: carry the mask as a parameter and halve it (`pw >> 1`) rather than reading
  a table of powers or shifting by a variable.
- "Is it odd", "half of it": `x land 1` and `x >> 1`.  `x mod 2` and `x / 2` are Z's operations: right for negative
  numbers too, and they first ask whether the number is negative.
- Values must stay below 2^62 (an `int` has 63 bits).

Measured (CF622F, a million powers modulo 10^9 + 7): the corpus text 87 ms, with the three points above 80 ms.  The
C++ takes 54 ms: a long chain of modular multiplications stays about 1.5x the C++ however it is written, because every
product is asked for its sign (`mod` is Z's) and carries its mark.

### 8. The budget is the count

When the number of rounds is known before the loop starts, give the loop exactly that budget and let it ask nothing
else: `match fuel with O => .. | S f => ..` is then the loop's ONE test.  And carry the cell the loop is at, not a
start and an index to add.

```coq
(* two tests a round, and four numbers to keep at hand *)
Fixpoint relax (fuel : nat) (j n bi bv dik : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => if n <=? j then s else .. rd rD (bi + j) s .. relax f (j + 1) n bi bv dik ..
  end.

(* one test a round: the budget IS n *)
Fixpoint relax (fuel : nat) (pi pv dik : int) (s : mem) : mem :=
  match fuel with
  | O => s
  | S f => .. rd rD pi s .. relax f (pi + 1) (pv + 1) dik ..
  end.
```

Measured: CF295B 155 ms -> 117 ms.  It never cost anything; on CF460C it changed nothing.

And, WITH THE SETTING `proofs` (off by default), a loop whose budget is the count, with a parameter that goes up by
one every round, reads and writes WITHOUT A TEST (step 3 of the translator, `KQBound.v`): cells `p` or `p + d` of a
block named by a number (or by a parameter the loop passes on unchanged) are all inside the block when the last one
is, so the loop makes one test when it starts (`kq_fits`) and none per cell -- and the translator proves it, by a copy
of the loop that carries the proof at every read and write, which Rocq's type checker checks.  A loop that also stops
early on a test of its own (a budget larger than the count) keeps its tests: the start test cannot know where it
stops.  Measured on the 36 programs (`results/step3.txt`, the machine's cycles): 1.8% fewer on average; ten programs
3% to 15% fewer (CF295Bv2 15%, the third version of CF1100F 13%, CF295B, CF235C and CF165E's second version 9%); four
3% to 14% MORE although every one of them executes fewer instructions -- in CF295B's narrow version the C compiler
keeps two of the loop's numbers on the stack instead of in registers (its machine code); CF460C (11% more) was not
looked into.

Why it is off by default (the owner's choice, 2026-10-14: the most stable way, whatever it costs): the test on every
read and write is the memory model's own definition (`rd` gives 0 outside a block), so it needs nothing more to be
believed, it is the same for every program and every way of writing a loop, and it cannot keep a correct program from
building.  The proofs apply to loops of one shape only, their gain depends on the C compiler (the four programs
above), and they are made per program.  Both are correct; to have the proofs, write the word `proofs` in
`hand/NAME.bounds` (that program) or run the build with `KQBOUNDS=proofs` (every program of the run); in a file of
your own, `MetaRocq Run (kq_fast_full 3 KQProofs (PUse [..]) main).`  The gate builds every program both ways.

### 9. Numbers that fit in 32 bits go in narrow blocks

A cell holds one 63-bit number: 8 bytes, where a C++ `int` takes 4.  For a program whose data does not fit in the
machine's fast memory that is twice the memory to move.  A NARROW block (`rd32` / `upd32`, KQRun.v) has cells of 4
bytes: a number is kept modulo 2^32 and read back signed, so it is for numbers that fit (-2^31 .. 2^31 - 1).  Narrow
blocks are a family of their own, numbered from 0; the memory file gives them after the wide ones (`n32`).
`mknarrowbody.py` turns blocks of a program narrow by name and `mknarrow.py` its memory (`narrow.tsv`): nothing else
in the text changes.

Measured (`results/narrow.txt`, ms; the eight programs of `narrow.tsv`):

| Problem | C++ | C++ with 8-byte cells | wide blocks | narrow blocks |
|---|---|---|---|---|
| CF35C, a walk over a grid | 12.4 | 17.3 | 19.9 | 13.6 |
| CF235C, a suffix automaton | 24.4 | 33.9 | 42.7 | 30.7 |
| CF385C, a sieve up to 10 million | 125 | 252 | 167 | 123 |
| CF61E, a tree of sums | 68.6 | 79.6 | 79.2 | 68.6 |
| CF339D, a tree over 2^20 numbers | 61.7 | 89.7 | 113 | 103 |
| CF380C, a segment tree | 40.9 | 60.0 | 57.0 | 54.9 |
| CF165E, a table over sets of bits | 58.6 | 67.9 | 66.3 | 64.9 |
| CF295B, all shortest ways | 35.7 | 56.9 | 113 | 122 |

It pays where the time goes to memory, and does nothing (or harm: CF295B, whose time is arithmetic) elsewhere -- the
table times both versions and keeps the faster.

## What you do not need to worry about

- **Small helper definitions.**  A non-recursive `Definition` is written out at its uses, by the translator: a loop
  written with helpers is the same C as the loop written in one piece (`results/same.txt`, column C).
- **How the steps are named and nested.**  `loop f (i + 1) (acc + rd 0 i s) s` and the same with every step named by
  a `let`, in any order, are the same C.  The order of steps that do not depend on each other is fixed by the
  translator's rule, not by the text.
- **Reading a cell twice** from the same memory, or writing the same arithmetic twice: it is computed once.
- **Where the two numbers of a choice are worked out** -- before the `if` or inside it.  (Before the translator this
  decided, by itself, whether the C compiler made a jump: 66 ms against 18 ms on the same loop.)
- **Two calls of a loop, or two writes of a cell, that differ only in numbers.**  `if c then f a s else f b s` and
  `f (if c then a else b) s` give the same machine code (rule 4).
- **A choice on a combination of tests** (`c1 && c2`): it becomes one conditional move per test.
- **The budget.**  One subtraction and one test.  A budget that is larger than needed costs nothing.
- **`&&`, `||`, `negb`, `if` on a comparison.**  They become flags and conditional moves.
- **Names for block numbers** (`Local Notation rA := 0.`): they are constants by the time C sees them.  Passing a
  block number round a loop as a parameter cost nothing measurable either (CF163A, tried both ways).
- **The collector.**  A loop that builds nothing never calls it and pays nothing for it.
- **Many parameters.**  A function may have twenty.  (Until 2026-10-14 a recursive function with more than seven,
  called from two places, kept heap objects: that was the compiler, and is fixed in it.)
- **Proofs, specifications, `nat` budgets, `Prop`s.**  None of it reaches C.

## What no way of writing removes

Measured on the eleven new problems; these are properties of the memory model and of the route, not of a program.

| Cause | What it costs | Where it shows |
|---|---|---|
| A test on every access (`rd` outside a block gives 0, `upd` outside does nothing: so every access asks "inside?") -- EXCEPT, with the setting `proofs`, in a loop that counts (rule 8, step 3 of the translator) | between nothing and 30% of a program's time where it is left (`results/floor.txt`: every program built once more without the tests -- not a valid build, only to measure) | CF547B 36 ms, 30 ms without the tests: the C++'s 30 ms.  CF453B 442 ms, 314 ms without: the 313 ms of the C++ written the same way |
| A cell is 8 bytes; a C++ `int` is 4 -- EXCEPT in a narrow block (rule 9) | up to 1.9x when the data does not fit the machine's fast memory | CF339D: the C++ takes 64 ms, the same C++ with 8-byte cells 110 ms, the Rocq program 143 ms.  CF385C: 134 ms and 260 ms |
| The C compiler uses vector instructions on the C++ and cannot on a loop with a test per access | 1.5x on a dense loop over a table | CF295B: C++ 36 ms, without its vector instructions 54 ms, Rocq 117 ms |
| Integers carry a mark in their lowest bit; a loop has its budget to count | a few instructions a round | everywhere; the reason "same program, same layout" is 1.0x - 1.4x and not 1.0x |

## How to see whether a program follows the rules

Five things answer, in the order the build meets them.

1. **The translator** (KQFast.v) says how many functions it put in the standard form and how many it kept as written
   (a function it cannot read: one that builds a pair, for instance), how many steps of the second kind it made (rule
   4) and how many loops it made without tests (rule 8; none unless the setting `proofs` asks for them, and it says
   which setting it was given).  Each is equal to its function -- by computation, by
   induction, or by the copy that carries the proofs -- and the kernel has checked it, or the file does not compile.
2. **The checker** (KQShape.v) reads the standard form and answers in two parts; when it refuses, the file does not
   compile and no C is made.
   - REFUSALS, four kinds and no other: a memory is used after it was handed on to something that may write it (any
     number of functions may LOOK at a memory; once something writes it, the old one is gone); a loop builds something
     (rule 5); a function that calls itself once does not do so as its last step (rule 3); a function is made or
     passed as a value.  The first is about being right; the other three are what would take memory from the
     collector, or stack, in a loop.  Nothing is refused for being possibly slow.
   - ADVICE, for speed only: rule 1 ("cell 2 of block 4 is read AND written by this loop").
3. **The measuring run** (`prof.sh NAME`, or `one.sh NAME`) prints every test of the program: how often it was met,
   how often it was true, how often a machine would have guessed it wrong, and what was done with it.
4. **The build** ends each program's line with what is LEFT in the generated C: values built inside a loop, closures
   built, calls through a closure.  All three at zero is what the rules are for: such a program never touches the
   collector in a loop.  This is read off the C that is compiled, so it also catches what the checker cannot see --
   the compiler itself leaving a heap object behind.
5. **The counters**: `pstat.sh` prints, for the timed part of a run, the instructions executed and the wrong guesses.
   Divide by the number of rounds: a tight loop over the memory is 10 - 30 instructions a round.  More means a rule is
   broken somewhere.

Rules 2, 6, 8 and 9 are not checked by anything: they are about how the work is divided and where the data sits,
which a walk of the text cannot judge.
