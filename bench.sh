#!/bin/bash
# bench.sh [LABEL=BINARY:PROBLEM[:MEMFILE[:ARGSFILE]]] ..   (inside the image, in /w)
# Every run is PINNED TO ONE FAST CORE (this laptop mixes fast and slow cores; an unpinned run lands on either).
# Per entry: one checked run (every answer compared with the C++ run), then N timed runs; prints the best and the median.
#   N=7 KQCPU=4 by default.  PROBLEM is a name of problems.tsv.  As BINARY, "cpp" means the C++ reference
#   (big/PROBLEM_timed.cpp), "cpp64" the same with every array 64 bits wide (cpp64/PROBLEM_64.cpp), "cppw" the C++
#   written the way the fast Rocq version is (cppw/PROBLEM_w.cpp).
#   ANSWERS=1: no timing, the checked run only.
cd /w && ulimit -s unlimited
N=${N:-7}; KQCPU=${KQCPU:-4}; LW=${LW:-34}
stat() { sort -n | awk '{a[NR]=$1} END {if (NR==0) printf "-"; else printf "%8.2f %8.2f", a[1], a[int((NR+1)/2)]}'; }
dumpof() { awk -v p="$1" '$1 == p {print $2}' problems.tsv; }
printf "%-${LW}s %-8s %8s %8s  %s\n" "what" "problem" "best" "median" "answers"
for e in "$@"; do
  label=${e%%=*}; rest=${e#*=}; IFS=: read -r bin p mem args <<< "$rest"
  [ -n "$mem" ] || mem=big/$p.mem; [ -n "$args" ] || args=big/$p.args
  [ -x big/${p}_cpp ] || clang++ -O2 -std=c++17 -o big/${p}_cpp big/${p}_timed.cpp
  [ -f big/$p.cpp.out ] || ./big/${p}_cpp < big/$p.in > big/$p.cpp.out 2>/dev/null
  case $bin in cpp|cpp64|cppw)
    b=big/${p}_cpp; v=${bin#cpp}
    if [ -n "$v" ]; then b=cpp$v/${p}_$v; [ -x $b ] || clang++ -O2 -std=c++17 -o $b cpp$v/${p}_$v.cpp 2>/dev/null; fi
    [ -x $b ] || { printf "%-${LW}s %-8s missing\n" "$label" "$p"; continue; }
    taskset -c $KQCPU $b < big/$p.in > dbg/bench.out 2>/dev/null; cmp -s dbg/bench.out big/$p.cpp.out && same=ok || same=WRONG
    t=$(for i in $(seq $N); do { taskset -c $KQCPU $b < big/$p.in > /dev/null; } 2>&1 | tail -1 | awk '{print $3}'; done | stat)
    printf "%-${LW}s %-8s %s  %s\n" "$label" "$p" "$t" "$same"; continue;;
  esac
  [ -x "$bin" ] || { printf "%-${LW}s %-8s missing %s\n" "$label" "$p" "$bin"; continue; }
  d=$(dumpof $p); [ -n "$d" ] || { printf "%-${LW}s %-8s not in problems.tsv\n" "$label" "$p"; continue; }
  if [ "$d" = "-" ]; then
    KQ_MEM=$mem timeout 900 taskset -c $KQCPU $bin $(cat $args) > dbg/bench.out 2>&1
    [ "$(head -1 big/$p.cpp.out)" = "$(head -1 dbg/bench.out | awk '{print $2}')" ] && same=ok || same="WRONG($(head -1 dbg/bench.out | cut -c1-50))"
  else
    IFS=: read -r dh ds dn <<< "$d"; [ "$dn" = r ] && dn=-1
    KQ_MEM=$mem KQ_DUMP="$dh $ds $dn" timeout 900 taskset -c $KQCPU $bin $(cat $args) > dbg/bench.out 2>&1
    tail -n +2 dbg/bench.out | cmp -s - big/$p.cpp.out && same=ok || same="WRONG($(head -1 dbg/bench.out | cut -c1-40))"
  fi
  if [ -n "$ANSWERS" ]; then t="       -        -"
  else t=$(for i in $(seq $N); do KQ_MEM=$mem timeout 900 taskset -c $KQCPU $bin $(cat $args) 2>&1 | head -1 | awk '{print $NF}'; done | stat); fi
  printf "%-${LW}s %-8s %s  %s\n" "$label" "$p" "$t" "$same"
done
