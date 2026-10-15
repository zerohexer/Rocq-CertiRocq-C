#!/bin/bash
# shape.sh   (inside the PATCHED image, in /w, after regen.sh)  what the checker (KQShape.v) says of every program:
# one line each -- OK, or the number of refusals -- then every refusal, then the advice.
#   set F / E: the corpus text;  set H: the programs written by the guideline (hand/*.body)
cd /w
ok=0; no=0
for l in fast/*.log; do n=$(basename $l .log)
  if grep -q "^KQ-SHAPE OK" $l; then ok=$((ok+1)); st="OK"
  else c=$(grep -o "^KQ-SHAPE REFUSE ([0-9]*)" $l | grep -o "[0-9]*"); [ -n "$c" ] || c="no verdict"; no=$((no+1)); st="REFUSED ($c)"; fi
  a=$(grep -o "^KQ-SHAPE ADVICE ([0-9]*)" $l | grep -o "[0-9]*"); [ -n "$a" ] && st="$st, advice $a"
  printf "%-18s %s\n" "$n" "$st"
done
echo "checker: $ok accepted, $no refused"
if [ -n "$DETAIL" ]; then
  for l in fast/${DETAIL}*.log; do echo "== $(basename $l .log)"; sed -n '/^KQ-SHAPE/,$p' $l | grep -v "^KQ-SHAPE OK" | cut -c1-230; done
fi
