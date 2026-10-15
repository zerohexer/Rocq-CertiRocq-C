#!/bin/bash
# regen.sh [PREFIX..]   (inside the PATCHED image, in /w)   default: F E H
# Rocq -> C for every program of the given sets:
#   F  the corpus text unchanged (sv2fast.py)          E  the same with rebuilt pairs removed (sv2fast.py --eta)
#   H  the programs of hand/ THROUGH THE TRANSLATOR (KQFast.v): put in the standard form, each choice between two numbers
#      made the way hand/<name>.sel says (the numbers of the tests to make without a jump; prof.sh measures them), and
#      the bounds of blocks the way bounds.sh says (tests unless hand/<name>.bounds or KQBOUNDS says proofs)
#   P  the same with the bounds PROOFS for every program (step 3 of the translator): what keeps that setting working
#   W  the programs of hand/ AS WRITTEN (no translator), for comparison
#   I  the programs of hand/ in the standard form with every choice COUNTING its wrong guesses (what prof.sh runs)
# One line per program; the C lands in /w as <PREFIX>_<name>_prog.c.  HAND="a b" limits H / W / I to those programs.
eval $(opam env); cd /w && ulimit -s unlimited
{ rocq c -R . KQ KQRun.v && rocq c -R . KQ KQShape.v && rocq c -R . KQ KQNat.v && rocq c -R . KQ KQBound.v && rocq c -R . KQ KQFast.v; } 2>&1 | grep -i -A3 "^Error"
sets="$@"; [ -n "$sets" ] || sets="F E H"
hand=${HAND:-$(for b in hand/*.body; do basename $b .body; done)}
gen() {  # gen PREFIX NAME MODE [BOUNDS]   (MODE empty: as written;  BOUNDS: KQTests or KQProofs, else bounds.sh's)
  local n=$1_C_$2 b=${4:-$(bash bounds.sh $2)}
  if [ -z "$3" ]; then { cat hand/hdr.txt; echo; cat hand/$2.body; sed "s/%s/$n/" hand/ftr.txt; } > fast/$n.v
  else { cat hand/hdr.txt; echo; cat hand/$2.body; sed -e "s/%s/$n/" -e "s/%m/$3/" -e "s/%o/${KQORD:-3}/" -e "s/%b/$b/" hand/ftr_kq.txt; } > fast/$n.v; fi
}
for P in $sets; do
  rm -f fast/${P}_*.v
  case $P in
    F) for f in sv/*.sv; do n=$(basename $f .sv); python3 sv2fast.py $f F_$n > fast/F_$n.v 2> fast/F_$n.gen || echo "F_$n PORT-FAIL"; done;;
    E) for f in sv/*.sv; do n=$(basename $f .sv); python3 sv2fast.py --eta $f E_$n > fast/E_$n.v 2> fast/E_$n.gen || echo "E_$n PORT-FAIL"; done;;
    H) for x in $hand; do sel="[]"; [ -f hand/$x.sel ] && sel=$(cat hand/$x.sel); gen H $x "(PUse $sel)"; done;;
    P) for x in $hand; do sel="[]"; [ -f hand/$x.sel ] && sel=$(cat hand/$x.sel); gen P $x "(PUse $sel)" KQProofs; done;;
    W) for x in $hand; do gen W $x ""; done;;
    I) for x in $hand; do gen I $x PInstr; done;;
  esac
  ok=0; bad=0
  for v in fast/${P}_*.v; do n=$(basename $v .v)
    if timeout 300 rocq c -R . KQ $v > fast/$n.log 2>&1; then ok=$((ok+1)); else bad=$((bad+1)); echo "$n ROCQ-FAIL: $(grep -A4 '^Error' fast/$n.log | head -5 | tr '\n' ' ' | cut -c1-300)"; fi
  done
  echo "set $P: $ok compiled, $bad failed"
done
