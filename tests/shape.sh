#!/bin/bash
# tests/shape.sh   (inside the PATCHED image, in /w)  the checker on small programs with a known verdict:
# faulty ones it must refuse (each a way a memory written in place would give a wrong answer, or a loop a heap object)
# and sound ones it must accept.  Each tests/shape/NAME.body starts with the verdict expected.
cd /w; eval $(opam env); mkdir -p dbg/shape
good=0; bad=0
for b in tests/shape/*.body; do n=$(basename $b .body); want=$(head -1 $b | sed 's/.*EXPECT: \([A-Z]*\).*/\1/')
  { echo 'From MetaRocq.Template Require Import All.'; echo 'Require Import KQ.KQRun KQ.KQShape KQ.KQNat.'
    echo 'Open Scope sint63_scope.'; echo 'Open Scope bool_scope.'; cat $b
    echo 'Definition main := solve.'; echo 'MetaRocq Run (kq_shape main).'; } > dbg/shape/$n.v
  rocq c -R . KQ dbg/shape/$n.v > dbg/shape/$n.log 2>&1
  got=$(grep -o "^KQ-SHAPE [A-Z]*" dbg/shape/$n.log | awk '{print $2}'); [ -n "$got" ] || got="NO-VERDICT"
  if [ "$got" = "$want" ]; then good=$((good+1)); else bad=$((bad+1)); echo "  $n: expected $want, got $got: $(grep -A3 '^KQ-SHAPE\|^Error' dbg/shape/$n.log | head -4 | tr '\n' ' ' | cut -c1-200)"; fi
done
# the gate itself: a refused program must not compile, an accepted one must
g=0
for n in no_pair_in_loop ok_tree; do
  sed 's/MetaRocq Run (kq_shape main)\./MetaRocq Run (kq_gate main)./' dbg/shape/$n.v > dbg/shape/gate_$n.v
  rocq c -R . KQ dbg/shape/gate_$n.v > dbg/shape/gate_$n.log 2>&1; echo $? > dbg/shape/gate_$n.rc
done
[ "$(cat dbg/shape/gate_no_pair_in_loop.rc)" != 0 ] && [ "$(cat dbg/shape/gate_ok_tree.rc)" = 0 ] || { bad=$((bad+1)); echo "  kq_gate: a refused program compiles, or an accepted one does not"; }
echo "checker on programs with a known verdict: $good as expected, $bad not"
[ $bad = 0 ] && echo "GATE: the checker refuses the faulty test programs and accepts the sound ones" || echo "GATE: THE CHECKER'S VERDICT IS WRONG ON A TEST PROGRAM"
