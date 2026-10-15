#!/bin/bash
# tests/bounds_cost.sh [TAG]   (ON THE HOST, in this directory, after all.sh)   WHAT THE DEFAULT COSTS.
# Every program of hand/ as built in set H (the bounds setting of each program; tests by default) against set P (the
# bounds proofs for every program), run IN TURN, R rounds (a busy machine slows both alike), one pinned fast core,
# the machine's counters on: the best time and the fewest cycles of each.
cd "$(dirname "$0")/.." && ulimit -s unlimited
T=${1:-fin}; R=${R:-5}; KQCPU=${KQCPU:-4}
one() { KQ_PERF=1 KQ_MEM=$2 taskset -c $KQCPU $1 $(cat $3) 2>&1 | awk '/^perf/ {c = $3} /^result/ {m = $NF} END {print m, c}'; }
printf "%-10s %9s %9s %9s %9s %7s %7s\n" program "ms H" "ms P" "Mcyc H" "Mcyc P" "H/P ms" "H/P cyc"
while read -r name p mem what; do
  [ -n "$name" ] || continue
  [ "$mem" = "-" ] && mem=big/$p.mem
  h=bin/${T}_H_C_${name}_gc; q=bin/${T}_P_C_${name}_gc
  [ -x $h ] && [ -x $q ] || { echo "$name: not built"; continue; }
  for i in $(seq $R); do one $h $mem big/$p.args | sed 's/^/H /'; one $q $mem big/$p.args | sed 's/^/P /'; done |
    awk -v n=$name '{ if (!($1 in m) || $2 + 0 < m[$1]) m[$1] = $2 + 0; if (!($1 in c) || $3 + 0 < c[$1]) c[$1] = $3 + 0 }
         END { printf "%-10s %9.1f %9.1f %9.1f %9.1f %7.3f %7.3f\n", n, m["H"], m["P"], c["H"] / 1e6, c["P"] / 1e6, m["H"] / m["P"], c["H"] / c["P"] }'
done < <(grep -v '^#' hand.tsv) | tee dbg/bounds_cost.txt
awk 'NR > 0 && $7 + 0 > 0 { n++; lm += log($6); lc += log($7); if ($6 > 1.03) sm++; if ($6 < 0.97) fm++; if ($6 > mx) { mx = $6; mn = $1 } }
     END { printf "%d programs: the default (tests) against the bounds proofs, H/P: time geometric mean %.3f, cycles %.3f; slower by more than 3%%: %d, faster by more than 3%%: %d; the largest %.2f (%s)\n", n, exp(lm / n), exp(lc / n), sm, fm, mx, mn }' dbg/bounds_cost.txt
