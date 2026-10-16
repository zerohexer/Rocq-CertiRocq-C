#!/bin/bash
set -e
cd /w

for cc in ccomp gcc clang; do
  command -v $cc >/dev/null || continue
  O=-O2; [ $cc = ccomp ] && O="-O -D_POSIX_C_SOURCE=199309L"
  $cc $O -Dmain=gen_main1 -c lcg_gen.c -o lcg_$cc.o
  $cc $O -Dmain=gen_main2 -c sumsq_gen.c -o sumsq_$cc.o
  $cc $O -Dmain=gen_main3 -c sort_gen.c -o sort_$cc.o
  $cc $O -c hand.c -o hand_$cc.o
  $cc $O -c drv.c -o drv_$cc.o
  $cc lcg_$cc.o sumsq_$cc.o sort_$cc.o hand_$cc.o drv_$cc.o -o run_$cc
  echo "== $cc"; ./run_$cc
done
