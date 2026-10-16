#!/bin/bash
# Check the proofs, print the generated C, build and time it with ccomp, gcc and clang.
# Runs in the CertiRocq image (CompCert 3.17 is installed there as a Rocq library and as ccomp).
set -e
cd "$(dirname "$0")"
IMG=${IMG:-kernelq-certirocq:1b45a1aa-kq2}
docker run --rm --memory=4g --memory-swap=6g -v "$PWD":/w -w /w "$IMG" bash -lc '
set -e
for f in KQL KQLGen KQLArith KQLSigned KQLProof KQLBack KQLTop KQLAuto KQLTrans KQLEx KQLSort KQLPrint Emit ExLcg ExSort; do
  echo "== $f"; coqc -w -notation-overridden -w -abstract-large-number -Q . KQC $f.v
done
for n in lcg sumsq sort; do
  python3 -I -c "import sys; s=open(\"${n}_gen.out\").read(); s=s[s.index(chr(34))+1:s.rindex(chr(34))].replace(2*chr(34),chr(34)); open(\"bench/${n}_gen.c\",\"w\").write(s)"
done'
docker run --rm --memory=2g --memory-swap=3g --cpuset-cpus=${KQ_CPU:-4} -v "$PWD/bench":/w "$IMG" bash -lc /w/build.sh
