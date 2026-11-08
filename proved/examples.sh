#!/bin/bash
# examples.sh   (inside the image, in /w)   the programs of proved/examples/ through the proved route: translated, every
# function proved (a lemma the kernel does not finish is an error), built, and the answer compared with the value in
# NAME.expect (worked out apart from Rocq).  They run on the memory and the arguments of tests/mkworst.py.
cd /w && ulimit -s unlimited; eval $(opam env)
export KQ_STRICT=1
D=dbg/examples; mkdir -p $D
python3 tests/mkworst.py $D > /dev/null || exit 1
ok=0; bad=0
for b in proved/examples/*.body; do
  n=$(basename $b .body)
  rm -f bin/P_$n   # no answer from a binary an earlier run left (F72)
  python3 proved/kitc.py $b 2>&1 | grep -v "^Warning\|^to KQC" | grep -v "^$n built" | head -3
  mem=$D/same.mem; args=$D/same.args   # an example with its own memory and arguments has NAME.mem, NAME.args
  [ -f proved/examples/$n.mem ] && mem=proved/examples/$n.mem; [ -f proved/examples/$n.args ] && args=proved/examples/$n.args
  got=$(KQ_MEM=$mem bin/P_$n $(cat $args) 2>&1 | head -1 | awk '{print $2}')
  if [ "$got" = "$(cat proved/examples/$n.expect)" ]; then ok=$((ok + 1)); else bad=$((bad + 1)); echo "$n: got $got, expected $(cat proved/examples/$n.expect)"; fi
done
# an ordinary Rocq file: Rocq compiles it on its own, kitc.py reads the entry's arguments from its signature (Rocq-C-solution.md §12.B)
for v in proved/vfiles/*.v; do
  n=$(basename $v .v)
  rm -f bin/P_$n
  coqc -w -all -R . KQ $v > /dev/null 2>&1 || { bad=$((bad + 1)); echo "$n: Rocq refused the file on its own"; continue; }
  python3 proved/kitc.py $v 2>&1 | grep -v "^Warning\|^to KQC" | grep -v "^$n built" | head -3
  got=$(KQ_MEM=proved/vfiles/$n.mem bin/P_$n $(cat proved/vfiles/$n.args) 2>&1 | head -1 | awk '{print $2}')
  if [ "$got" = "$(cat proved/vfiles/$n.expect)" ]; then ok=$((ok + 1)); else bad=$((bad + 1)); echo "$n: got $got, expected $(cat proved/vfiles/$n.expect)"; fi
done
echo "examples: $ok give the expected answer, $bad do not"
[ $bad = 0 ]
