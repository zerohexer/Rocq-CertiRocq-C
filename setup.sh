#!/bin/bash
# setup.sh   (inside the PATCHED image, in /w)  everything the other scripts expect to find, made once:
#   big/      the large input of every timed problem (problems.tsv, mkbig.py) and the compiled C++ references
#   cpp64/    the references once more with every array 64 bits wide (the data layout a Rocq program is given),
#   cppw/     and once more written the way the fast Rocq version is -- for the problems that have such a file
#   cppp/     the references with the machine's counters around the timed region (for pstat.sh)
#   case/     a small random input per corpus program, and what the ORIGINAL (Z) program answers on it, computed
#             inside Rocq (mkcase.py seed 7, mkrefs.sh)
#   sup/stress  the support code plus CertiRocq's collector with a nursery of 32 words: a collection every few
#             allocations, to test that the clean-up pass removes no save the collector needs
eval $(opam env); cd /w && ulimit -s unlimited
mkdir -p big case bin bld dbg fast cppp
probs=$(grep -v '^#' problems.tsv | awk 'NF {print $1}')
miss=""; for p in $probs; do [ -f big/$p.mem ] || miss="$miss $p"; done
[ -z "$miss" ] || python3 mkbig.py big $miss
[ -f big/CF1100Fw.args ] || python3 mkbig.py big CF1100Fw
# the memories of the programs that keep blocks narrow (narrow.tsv)
grep -v '^#' narrow.tsv | while read -r v src idx; do
  [ -n "$v" ] || continue
  [ -f big/N_$v.mem ] && [ big/N_$v.mem -nt $src ] || python3 mknarrow.py $src big/N_$v.mem $idx || exit 1
done
counters() {   # counters SRC OUT: the same program with the counters started and stopped where its clock is
  sed -e 's|#include <bits/stdc++.h>|#include <bits/stdc++.h>\n#include "kq_perf.h"|' \
      -e 's|auto t0 = chrono::steady_clock::now();|kq_perf_start(); auto t0 = chrono::steady_clock::now();|' \
      -e 's#auto \(t1\|tt\) = chrono::steady_clock::now();#auto \1 = chrono::steady_clock::now(); kq_perf_stop();#' $1 > $2.cpp
  grep -q "kq_perf_start" $2.cpp && grep -q "kq_perf_stop" $2.cpp || { echo "setup: no clock found in $1"; exit 1; }
  clang++ -O2 -std=c++17 -Isup/v4 -o $2 $2.cpp
}
for p in $probs; do                                   # (a binary older than its source is built again)
  src=big/${p}_timed.cpp
  if [ ! -x big/${p}_cpp ] || [ $src -nt big/${p}_cpp ]; then
    clang++ -O2 -std=c++17 -o big/${p}_cpp $src || exit 1
    ./big/${p}_cpp < big/$p.in > big/$p.cpp.out 2>/dev/null
  fi
  [ -f big/$p.cpp.out ] || ./big/${p}_cpp < big/$p.in > big/$p.cpp.out 2>/dev/null
  [ -x cppp/$p ] && [ ! $src -nt cppp/$p ] || counters $src cppp/$p
  for v in 64 w; do                                   # 64: every array 64 bits wide;  w: written the way the fast Rocq is
    src=cpp$v/${p}_$v.cpp; [ -f $src ] || continue
    if [ ! -x cpp$v/${p}_$v ] || [ $src -nt cpp$v/${p}_$v ]; then clang++ -O2 -std=c++17 -o cpp$v/${p}_$v $src || exit 1; fi
    [ -x cppp/${p}_$v ] && [ ! $src -nt cppp/${p}_$v ] || counters $src cppp/${p}_$v
  done
done
if [ ! -f case/C_CF455A.ref ]; then
  for f in sv/*.sv; do python3 mkcase.py $(basename $f .sv) 7 > /dev/null; done
  bash mkrefs.sh > case/refs.log 2>&1
fi
if [ ! -f sup/stress/gc_stack.c ]; then
  RT=$(ls -d ~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime)
  mkdir -p sup/stress && cp sup/v4/* sup/stress/ && cp $RT/gc_stack.h $RT/gc_stack.c sup/stress/
  sed -i 's/^#define LOG_NURSERY_SIZE 16$/#define LOG_NURSERY_SIZE 5   \/* stress build: a collection every few values built *\//' sup/stress/gc_stack.h
  grep -q "LOG_NURSERY_SIZE 5 " sup/stress/gc_stack.h || { echo "setup: could not make the stress collector"; exit 1; }
fi
for f in kq_io.h kq_io3.c kq_prim63.c kq_perf.h; do cmp -s sup/v4/$f sup/stress/$f || cp sup/v4/$f sup/stress/$f; done   # the stress build tests THIS support code
echo "setup: $(ls big/*.mem | wc -l) memory images, $(ls big/*_cpp | wc -l) C++ references, $(ls case/*.ref | wc -l) reference answers"
