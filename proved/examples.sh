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
  python3 proved/kitc.py $b 2>&1 | grep -v "^Warning\|^to KQC" | grep -v "^$n built" | head -3
  mem=$D/same.mem; args=$D/same.args   # an example with its own memory and arguments has NAME.mem, NAME.args
  [ -f proved/examples/$n.mem ] && mem=proved/examples/$n.mem; [ -f proved/examples/$n.args ] && args=proved/examples/$n.args
  got=$(KQ_MEM=$mem bin/P_$n $(cat $args) 2>&1 | head -1 | awk '{print $2}')
  if [ "$got" = "$(cat proved/examples/$n.expect)" ]; then ok=$((ok + 1)); else bad=$((bad + 1)); echo "$n: got $got, expected $(cat proved/examples/$n.expect)"; fi
done
echo "examples: $ok give the expected answer, $bad do not"
[ $bad = 0 ]
