#!/bin/bash
# hw/spec.sh   (inside the PATCHED image, in /w)   THE LAWS AND THE PROOFS: KQSpec.v (the laws of the memory and the
# machine, one axiom), KQModel.v (every law proved for a model: they cannot contradict each other), KQSpecDemo.v (proofs
# about kernel code against the laws).  The model's proof must rest on nothing of ours; the others on the one axiom.
cd /w; eval $(opam env)
for v in KQRun KQBound KQSpec KQModel KQSpecDemo; do
  rocq c -R . KQ $v.v > dbg_spec_$v.txt 2>&1 || { echo "GATE: $v.v DOES NOT COMPILE"; grep -A8 Error dbg_spec_$v.txt | head -10; exit 1; }
done
ours() { printf 'Require Import KQ.KQSpecDemo KQ.KQModel.\nPrint Assumptions %s.\n' $1 > /tmp/pa.v
         rocq c -R . KQ /tmp/pa.v 2>&1 | grep -E "^[A-Za-z0-9_.]+ :" | sed 's/ :.*//' | grep -E "^(KQRun|KQBound|KQSpec)\." | grep -v "^KQRun\.\(mem\|rd\|upd\|rd32\|upd32\|hw_[a-z0-9]*\)$\|^KQBound\.kq_len\(32\)\?$\|^KQSpec\.hw_trace$"; }
m=$(ours KQModel.laws_satisfiable); d=$(ours KQSpecDemo.pd_fill_entries); l=$(ours KQSpecDemo.lookup_index_in_bounds)
echo "claims assumed (beyond declarations and Rocq's integers): the model: [${m}]; the page-table proof: [$(echo $d)]; the index proof: [$(echo $l)]"
[ -z "$m" ] && [ "$(echo $d)" = KQSpec.real_laws ] && [ "$(echo $l)" = KQSpec.real_laws ] \
  && echo "GATE: the laws hold in a model (nothing of ours assumed), and the proofs about kernel code rest on them alone" \
  || echo "GATE: THE LAWS OR THE PROOFS ASSUME SOMETHING ELSE"
