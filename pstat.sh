#!/bin/bash
# pstat.sh [TAG]                               (ON THE HOST, in this directory, after all.sh; a container may not read
# pstat.sh LABEL=BINARY:PROBLEM[:MEMFILE] ..    the machine's counters)
# One pinned run each (best of R) with the counters on, for the timed region only: time, cycles, instructions,
# instructions per cycle, branches, wrong guesses, cache misses.  Without entries: every row of the table (table.sh),
# built under TAG (default fin).  As BINARY, "cpp" / "cpp64" / "cppw" mean the C++ runs.
KQCPU=${KQCPU:-4}; R=${R:-3}; ulimit -s unlimited
E=("$@")
if [ ${#E[@]} -le 1 ] && [[ "${E[0]}" != *=* ]]; then
  T=${1:-fin}; E=()
  while read -r p d prog; do
    [ -n "$p" ] || continue
    E+=("C++=cpp:$p"); [ -x cppp/${p}_64 ] && E+=("C++ with 64-bit cells=cpp64:$p"); [ -x cppp/${p}_w ] && E+=("C++ written the same way=cppw:$p")
    [ "$prog" = "-" ] || E+=("corpus text, pairs not rebuilt=bin/${T}_E_${prog}_gc:$p")
    while read -r name prob mem what; do
      [ "$prob" = "$p" ] || continue
      m=""; [ "$mem" = "-" ] || m=":$mem"
      E+=("guideline, $what=bin/${T}_H_C_${name}_gc:$p$m")
    done < <(grep -v '^#' hand.tsv)
  done < <(grep -v '^#' problems.tsv)
fi
printf "%-58s %-8s %8s %8s %8s %5s %8s %8s %8s %8s\n" what problem ms Mcycles Minstr ipc Mbranch Kbrmiss Kl1dmiss Kllcmiss
for e in "${E[@]}"; do
  label=${e%%=*}; rest=${e#*=}; IFS=: read -r bin p mem <<< "$rest"; [ -n "$mem" ] || mem=big/$p.mem
  best=""
  for i in $(seq $R); do
    case $bin in cpp|cpp64|cppw) v=${bin#cpp}; b=cppp/$p; [ -n "$v" ] && b=cppp/${p}_$v
      o=$( { KQ_PERF=1 taskset -c $KQCPU $b < big/$p.in > /dev/null; } 2>&1 ); ms=$(echo "$o" | grep "compute" | awk '{print $3}');;
    *) o=$(KQ_PERF=1 KQ_MEM=$mem taskset -c $KQCPU $bin $(cat big/$p.args) 2>&1); ms=$(echo "$o" | grep "^result" | awk '{print $NF}');;
    esac
    pl=$(echo "$o" | grep "^perf")
    line=$(echo "$ms $pl" | awk '{printf "%8.2f %8.1f %8.1f %5.2f %8.1f %8.0f %8.0f %8.0f", $1, $4/1e6, $6/1e6, ($4>0?$6/$4:0), $8/1e6, $10/1e3, $12/1e3, $14/1e3}')
    best="$best$line\n"
  done
  printf "%-58s %-8s %s\n" "${label:0:58}" "$p" "$(printf "$best" | sort -n | head -1)"
done
