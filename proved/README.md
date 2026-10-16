# A proved route from Rocq to C

A plain Rocq program goes to Clight, CompCert's C, with a proof that the C computes what the Rocq program computes,
and from there through CompCert's own proofs to assembly.  It covers the programs the kit's checker accepts: counters,
63-bit integers, calls, loops, and memory blocks.

```coq
Fixpoint inner (j : nat) (key : i63) (M : kmem) : kmem := ...      (* plain Rocq *)
Definition result : i63 := csum N 0 0 (outer (N - 1) 1 (fill N 0 1 mem0)).

MetaRocq Run (kql_translate result "sort_prog").    (* the KQL program, and one statement per function *)
Lemma inner_ok : inner_stmt. Proof. kql_auto. Qed.
```

## The steps

| Step | File | How it is justified |
|---|---|---|
| Rocq function -> KQL | `KQLTrans.v` (MetaRocq) | for each program: the statement "this KQL function computes this Rocq function", proved by `kql_auto` (`KQLAuto.v`) and checked by the kernel.  The translator is not trusted |
| KQL -> Clight | `KQLGen.v` | proved once for every program (`KQLProof.v`, `KQLTop.v`) |
| Clight -> assembly | CompCert 3.17 | CompCert's pass theorems, composed in `KQLBack.v` |
| Clight -> C text | `KQLPrint.v` | not proved; used to measure with ccomp, gcc and clang |

KQL is a first-order language in A-normal form: 63-bit integer arithmetic, a test on a comparison, a call, a loop (a
function calling itself last), and loads and stores on fixed-size memory blocks, with the kit's rule out of range (a
read gives 0, a write does nothing).  In C a number is an unsigned 64-bit temporary with the top bit clear; wrapping
operations are masked to 63 bits, division by zero and shifts of 63 or more are tested first, so the C has no
undefined behaviour.

`kql_compiled_correct` (`KQLTop.v`): if the KQL program computes v and CompCert accepts the generated Clight, the
assembly program exits with the low 32 bits of v.  The full 64-bit value is proved at the Clight level
(`prog_behaves`).

## What the translator reads

Parameters `nat` (a counter; the one the function recurses on comes first), `i63`, and at most one memory `kmem`, last;
a result `i63` or `kmem`.  In a body: `match` on a counter, `if` on a comparison of two numbers, `let`, `PrimInt63`
arithmetic, `rd` / `wr`, `ofn` of a counter, calls of the file's functions, closed constants.  A helper that does not
call itself is written out.  A memory is used only while it is the current one.  Anything else is refused with the
reason.

## Examples

| File | Program | |
|---|---|---|
| `ExLcg.v` | lcg (2^24 steps by binary splitting), sum of squares | translated, every function proved by `kql_auto` |
| `ExSort.v` | fill a block from an lcg, insertion sort in place, checksum | translated, proved by `kql_auto`, end to end (`sort_compiled`) |
| `KQLEx.v`, `KQLSort.v` | the same programs | KQL and proofs written by hand |

`Print Assumptions sort_compiled`: CompCert's parameters (its oracles, options and external calls, and the classical
axioms it uses) and Rocq's 63-bit integer axioms.  No admits.

## Speed

Best of 7, ms, one core, generated C against hand-written C of the same algorithm under the same compiler:

| | ccomp | gcc -O2 | clang -O2 |
|---|---|---|---|
| lcg, generated / hand | 32.7 / 36.0 | 20.7 / 19.6 | 27.8 / 25.4 |
| sum of squares 1e8, generated / hand | 53.8 / 54.2 | 54.0 / 48.1 | 55.4 / 37.1 |
| insertion sort 1e4, generated / hand | 17.0 / 12.5 | 5.9 / 12.4 | 12.9 / 8.5 |

## Why not CertiRocq's front end

CertiRocq's proof of its translation to λANF (`convert_top_anf_correct`) assumes the program has no primitive
operations (`no_prims`), and λANF's semantics for its optimisation passes (`bstep`) has no rule for them.  Every kit
program uses `PrimInt63`, so those theorems say nothing about it.  This route does not go through them.

## Not yet

- Programs over the kit's memory (`KQRun.v`, axioms with laws) rather than KQL's `kmem`.
- Recursion on a parameter other than the first; results that are pairs; functions as values.
- A function's proof is given its callees' facts by hand (`pose proof callee_ok`).
- The C text is printed by an unproved printer; a proved route would run the generator and CompCert's passes as one
  program.

## Running it

`./make.sh` checks every file in the CertiRocq image (CompCert 3.17 is installed there as a Rocq library and as ccomp),
prints the C of the examples and times it with ccomp, gcc and clang.
