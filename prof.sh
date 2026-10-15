#!/bin/bash
# prof.sh [NAME..]   (inside the PATCHED image, in /w, after setup.sh)   MEASURE THE CHOICES.
# Whether a choice between two numbers is faster with a jump or without one depends on the data and on nothing else:
# a jump costs nothing when the machine guesses it right and about fifteen cycles when it guesses wrong; working out
# both numbers and taking one costs a cycle or two, always.  So it is measured.  Every program of hand/ (or the ones
# named) is built in the standard form with each test COUNTING (KQFast.v, PInstr), and run once on its large input.
# A test that may be made without a jump (between two plain numbers; or two arms doing the same steps on numbers that
# may differ) that was met at least MINN times (1000) and that a machine would have guessed wrong at least TH per cent
# of the time (10) is made WITHOUT a jump from then on: its number is written to hand/NAME.sel, which the build of
# set H reads.
#   CHECK=1   write nothing: only say whether a fresh measurement gives the choices that are stored.
cd /w; eval $(opam env); ulimit -s unlimited
TH=${TH:-10}; MINN=${MINN:-1000}; KQCPU=${KQCPU:-4}
names="$@"; [ -n "$names" ] || names=$(for b in hand/*.body; do basename $b .body; done)
HAND="$names" bash regen.sh I | grep -v "^set I"
S=""; for x in $names; do S="$S I_C_$x"; done
MODES=gc SET="$S" bash mk.sh prof | grep -i "fail"
mkdir -p dbg/prof; diff=0; total=0; chosen=0; advice=0
for x in $names; do
  line=$(grep -v '^#' hand.tsv | awk -v n=$x '$1 == n {print $2, $3}'); p=${line%% *}; mem=${line#* }
  [ -n "$p" ] || { echo "prof: $x is not in hand.tsv"; continue; }
  [ "$mem" = "-" ] && mem=big/$p.mem
  [ -x bin/prof_I_C_${x}_gc ] || { echo "prof: $x did not build"; continue; }
  KQ_MEM=$mem timeout 900 taskset -c $KQCPU bin/prof_I_C_${x}_gc $(cat big/$p.args) > dbg/prof/$x.txt 2>&1
  python3 kqsel.py dbg/prof/$x.txt fast/I_C_$x.log $TH $MINN > dbg/prof/$x.sel.txt
  sel=$(head -1 dbg/prof/$x.sel.txt)
  nt=$(grep -c "between two plain numbers\|between the same steps" dbg/prof/$x.sel.txt); ns=$(grep -c "made without a jump" dbg/prof/$x.sel.txt)
  na=$(grep -c "one sequence of steps" dbg/prof/$x.sel.txt); advice=$((advice + na))
  total=$((total + nt)); chosen=$((chosen + ns))
  if [ -n "$CHECK" ]; then
    old="[]"; [ -f hand/$x.sel ] && old=$(cat hand/$x.sel)
    [ "$old" = "$sel" ] || { diff=$((diff + 1)); echo "  $x: stored $old, measured $sel"; }
  else echo "$sel" > hand/$x.sel; fi
  if [ -n "$QUIET" ]; then grep "one sequence of steps" dbg/prof/$x.sel.txt | sed "s/^ /  $x:/"; else echo "  $x: $sel"; tail -n +2 dbg/prof/$x.sel.txt; fi
done
echo "choices: $total tests that may be made without a jump were met; $chosen of them are (guessed wrong $TH% of the time or more), $advice of those by making two arms one sequence of steps"
if [ -n "$CHECK" ]; then [ $diff = 0 ] && echo "GATE: the stored choices are what a fresh measurement gives" || echo "GATE: $diff PROGRAM(S) HAVE STORED CHOICES THAT A FRESH MEASUREMENT DOES NOT GIVE"; fi
