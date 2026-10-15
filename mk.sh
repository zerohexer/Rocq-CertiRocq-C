#!/bin/bash
# mk.sh TAG [clang flags..]   (inside the image, in /w)
# Build programs from the C already generated (regen.sh), under ONE configuration, into bin/TAG_<program>_<gc|nogc>.
#   SUP=sup/v4        the support code to use (kq_io.h, kq_io3.c, kq_prim63.c, kq_nogc.c, kq_perf.h); sup/stress brings
#                     its own collector (one that runs every few allocations)
#   PY=kq_post3.py    the clean-up pass          POST=".."   extra flags for it
#   SET=".."          programs (default: the four timed problems: unchanged / rebuilt-pairs-removed / hand-written)
#   MODES="gc"        gc = CertiRocq's collector;  nogc = every save removed + a runtime that never collects (comparison only)
# The cleaned C and the support code are put together in bld/TAG so that a generated file finds THAT kq_io.h.
cd /w && ulimit -s unlimited
T=$1; shift; X="$@"
SUP=${SUP:-sup/v4}; PY=${PY:-kq_post3.py}; MODES=${MODES:-gc}
SET=${SET:-F_C_CF455A F_C_CF380C F_C_CF1100F F_C_CF868F E_C_CF868F}
RT=$(ls -d ~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime)
B=bld/$T; mkdir -p $B; cp $SUP/*.h $SUP/*.c $B/
CC=${CC:-clang}
for n in $SET; do
  [ -f ${n}_prog.c ] || { echo "$n: no generated C"; continue; }
  for m in $MODES; do
    ng=""; rtc=$RT/gc_stack.c; [ -f $B/gc_stack.c ] && rtc=$B/gc_stack.c      # a support directory may bring its own collector (the stress build)
    [ $m = nogc ] && { ng="--nogc"; rtc=$B/kq_nogc.c; }
    python3 $PY ${n}_prog.c $B/${n}_$m.c $ng $POST > $B/${n}_$m.post 2>&1 || { echo "$n $m POST-FAIL: $(tail -1 $B/${n}_$m.post)"; continue; }
    $CC -w -O2 -flto -fomit-frame-pointer -I$B -I$RT -I. $X -o bin/${T}_${n}_$m $B/kq_io3.c $B/${n}_$m.c $rtc $B/kq_prim63.c 2> $B/${n}_$m.err || echo "$n $m CC-FAIL: $(grep -m2 error $B/${n}_$m.err)"
  done
done
