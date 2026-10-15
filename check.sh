#!/bin/bash
# check.sh TAG PREFIX [MODES]   (in /w)  run bin/TAG_PREFIX_<name>_<mode> on the random case of every corpus program
# and compare result + whole-memory checksum with the ORIGINAL (Z) program's, computed inside Rocq (case/<name>.ref)
cd /w && ulimit -s unlimited
T=$1; P=$2; MODES=${3:-gc nogc}; bad=0; n=0
for r in case/*.ref; do b=$(basename $r .ref); ref=$(cat $r)
  for m in $MODES; do x=bin/${T}_${P}_${b}_$m
    [ -x $x ] || continue
    n=$((n+1)); o=$(KQ_MEM=case/$b.mem timeout 120 $x $(cat case/$b.args) 2>&1 | head -1)
    res=$(echo "$o" | awk '{print $2}'); sum=$(echo "$o" | awk '{print $4}'); set -- $ref
    if [ "$res" = "$1" ] && { [ "$2" = "0" ] || [ "$sum" = "$2" ]; }; then :; else echo "$b $m DIFFERENT (got $res $sum, want $ref)"; bad=$((bad+1)); fi
  done
done
echo "check $T $P: $n runs, $bad different"
