#!/bin/bash
# make.sh   (inside the image, in /w)   check every proof of the proved route: the kit's logic files first (KQRun.v,
# KQSpec.v, KQModel.v ...), then proved/*.v in order.  "core-ok" at the end means the kernel accepted all of them.
#   ASSUME=1 also prints what the end theorem rests on.
cd "$(dirname "$0")/.."; eval $(opam env)
for f in KQRun KQBound KQSpec KQModel hw/Runtime hw/User lib/Loop lib/LoopSpec lib/CInt lib/CIntSpec; do coqc -w -all -R . KQ $f.v || exit 1; done
# what lib/CIntSpec.v's theorems rest on: Rocq's axioms of its machine numbers, nothing of ours
printf 'Require Import KQ.lib.CIntSpec.\nPrint Assumptions cint_all.\n' > /tmp/CIntAx.v
coqc -w -all -R . KQ /tmp/CIntAx.v 2>&1 | grep -E "^[A-Za-z0-9_.]+ :" | sed 's/ :.*//' | grep -vE "^(PrimInt63|Uint63Axioms|Sint63Axioms)\." | grep . && { echo "lib/CIntSpec.v RESTS ON SOMETHING ELSE"; exit 1; }
cd proved
for f in KQPrim KQLSigned KQL KQTArith KQW64 KQByteArith KQBytes KQLGen KQMSem KQLProof KQLAuto KQM KQMNames KQMAuto KQRWf KQLoopSpec KQLoopExamples KQMTrans KQMTop KQLPrint KQR KQRReify KQRChain; do
  coqc -w -all -R .. KQ -Q . KQC $f.v || { echo "FAILED $f"; exit 1; }
done
if [ -n "$ASSUME" ]; then
  # what the route rests on: the assumptions of every lemma of the generator's last file and of the verified compiler's files, printed
  # from a file that imports nothing, so that each name is the one constant it names (step 92, F76)
  { echo "From KQC Require KQMTop KQR KQRWf KQPrim."
    for m in KQMTop KQR KQRWf KQPrim; do grep -oE "^ *(Lemma|Theorem|Corollary|Fact|Remark|Proposition|Property) [A-Za-z_][A-Za-z_0-9']*" $m.v | awk -v m=$m '{print "Print Assumptions " m "." $2 "."}'; done; } > /tmp/Assump.v
  echo "== the assumptions"
  coqc -w -all -R .. KQ -Q . KQC /tmp/Assump.v 2>&1 | grep -E "^[A-Za-z_][A-Za-z_0-9.']* :" | sed 's/ :.*//' | sort -u
  echo "== end of the assumptions"
fi
echo core-ok
