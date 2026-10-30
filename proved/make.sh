#!/bin/bash
# make.sh   (inside the image, in /w)   check every proof of the proved route: the kit's logic files first (KQRun.v,
# KQSpec.v, KQModel.v ...), then proved/*.v in order.  "core-ok" at the end means the kernel accepted all of them.
#   ASSUME=1 also prints what the end theorem rests on.
cd "$(dirname "$0")/.."; eval $(opam env)
for f in KQRun KQBound KQSpec KQModel hw/Runtime hw/User lib/Loop lib/LoopSpec; do coqc -w -all -R . KQ $f.v || exit 1; done
cd proved
for f in KQLSigned KQL KQTArith KQW64 KQByteArith KQBytes KQLGen KQMSem KQLProof KQLBack KQLAuto KQM KQMNames KQMAuto KQLoopSpec KQLoopExamples KQMTrans KQMTop KQLPrint KQR KQRReify KQRChain; do
  coqc -w -all -R .. KQ -Q . KQC $f.v || { echo "FAILED $f"; exit 1; }
done
if [ -n "$ASSUME" ]; then
  printf 'From KQC Require Import KQMTop.\nPrint Assumptions kit_function_correct.\n' > /tmp/Assump.v
  coqc -w -all -R .. KQ -Q . KQC /tmp/Assump.v
fi
echo core-ok
