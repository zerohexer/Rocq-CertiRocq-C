#!/bin/bash
# floor.sh  (inside the image, in /w, after all.sh; its output is results/floor.txt)  what the test on every access costs: each program built once more
# WITHOUT the tests (not a valid build in general: only right on an input that never leaves its blocks) and timed
cd /w; ulimit -s unlimited
H=""; for b in hand/*.body; do H="$H H_C_$(basename $b .body)"; done
MODES=gc SET="$H F_C_CF455A E_C_CF631E E_C_CF17E E_C_CF1039D E_C_CF1172F E_S3_CF432D" bash mk.sh vun -DKQ_UNCHECKED | tail -2
mkdir -p probe/cx
printf "%-9s %9s %9s %9s %9s\n" problem "C++" "Rocq" "no tests" "share"
while read -r p d prog; do
  [ -n "$p" ] || continue
  best=""; bt=999999; mem=""
  while read -r name prob m what; do
    [ "$prob" = "$p" ] || continue
    t=$(awk -v n="by the guideline, $what" -v p=$p 'index($0, n) == 1 { k = split($0, a, " "); if (a[k-3] == p) print a[k-2] }' results/table.txt | head -1)
    [ -n "$t" ] && awk -v a=$t -v b=$bt 'BEGIN { exit !(a < b) }' && { bt=$t; best=H_C_$name; mem=$m; }
  done < <(grep -v '^#' hand.tsv)
  [ -n "$best" ] || { case $p in CF455A) best=F_C_CF455A;; *) best=E_${prog};; esac; mem="-"; }
  [ -x bin/vun_${best}_gc ] || continue
  mm=""; [ "$mem" = "-" ] || mm=":$mem"
  out=$(N=5 bash bench.sh "c=cpp:$p" "r=bin/fin_${best}_gc:$p$mm" "u=bin/vun_${best}_gc:$p$mm" | tail -n +2)
  c=$(echo "$out" | awk '$1 == "c" {print $3}'); r=$(echo "$out" | awk '$1 == "r" {print $3}'); u=$(echo "$out" | awk '$1 == "u" {print $3}')
  printf "%-9s %9s %9s %9s %8s%%  %s\n" $p "$c" "$r" "$u" "$(awk -v r=$r -v u=$u 'BEGIN { printf "%.0f", 100 * (r - u) / r }')" "$(echo "$out" | awk '{printf "%s ", $NF}')"
done < <(grep -v '^#' problems.tsv)
