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
  printf 'From KQC Require Import KQMTop.\nPrint Assumptions kit_function_correct.\nFrom KQC Require KQPrim.\nPrint Assumptions KQPrim.kq_mulc_def.\nPrint Assumptions KQPrim.kq_h0_eq.\nPrint Assumptions KQPrim.kq_t0_eq.\nPrint Assumptions KQPrim.kq_d21_eq.\nPrint Assumptions KQPrim.kq_d21_le.\n' > /tmp/Assump.v
  coqc -w -all -R .. KQ -Q . KQC /tmp/Assump.v
fi
echo core-ok
