#!/bin/bash
# one.sh NAME..   (inside the PATCHED image, in /w, after setup.sh)  hand/NAME.body only: its choices measured
# (prof.sh), then Rocq -> standard form -> C, what the translator and the checker say, the build under the tag `fin`,
# and what is left in its C.  For working on one program; all.sh does everything.
cd /w; eval $(opam env); ulimit -s unlimited
for b in "$@"; do n=H_C_$b
  echo "== $b"
  bash prof.sh $b | grep -v "^choices"
  HAND="$b" bash regen.sh H | grep -v "^set H"
  grep "KQ-FAST\|^KQ-SHAPE\|^  in " fast/$n.log | cut -c1-220 | head -${LINES_SHOWN:-8}
  MODES=gc SET="$n" bash mk.sh fin | tail -2
  sed 's/.*one-sided tests, /   left in the C: /' bld/fin/${n}_gc.post | cut -c1-220
done
