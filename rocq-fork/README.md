# rocq-fork: our fork of Rocq's kernel

Rocq 9.1.1 with a conversion memo in its kernel: within one checked conversion, a pair of shared subterms already found
convertible (or not) is answered from a table instead of being compared again.  Without it, checking that a function whose
body reads a memory and then writes it, step after step, equals anything (its meaning in the verified compiler, or even a
copy of its own text) takes time exponential in the number of steps; with it, linear (Rocq-C-solution.md F46, D28, §12.R).

- `conv-memo-v9.1.1.patch` -- the memo, backported from rocq-prover/rocq#22309 to the V9.1.1 tree (`git apply -p1`).
  `ROCQ_CONV_CACHE=0` turns it off.
- `ConvMemo.v` -- its correctness, proved over a model of the kernel's closure machine: every outcome taken from the table
  is the true one for the current terms of the two cells (`lookup_correct`); the table never holds two outcomes for one key
  (`table_functional`).  Assumed only what the kernel already assumes.  `rocq c ConvMemo.v`.
- `check_patch.py ROCQ_SRC` -- the facts the model assumes of the OCaml, checked on a patched tree (every cell built with
  identity 0, one place gives identities, in-place writes keep a cell's meaning, the table only for checked conversion).
- `rebuild.sh` -- the image on the fork (`kernelq-certirocq:1b45a1aa-kq2-fork`): the V9.1.1 source fetched and checked by its
  SHA-256, the patch applied and checked, every package of the image recompiled on it, the kq2 CertiRocq patch again.  Run
  by `images.sh` (its third stage).  The image in use was built by the same steps from a copied source tree; this script
  itself has not yet been run end to end.

