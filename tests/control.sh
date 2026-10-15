#!/bin/bash
# tests/control.sh   (inside the image, in /w, after regen.sh and setup.sh)  THE CONTROL of the stress test:
# two programs that build values in their loops, with EVERY save removed (kq_post3.py --nogc) and the collector that
# runs every few values built.  They must go wrong (a wrong answer or a crash): that is what shows the stress test can
# see a save that was wrongly removed.
cd /w; ulimit -s unlimited
RT=$(ls -d ~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime)
B=bld/ctl; mkdir -p $B; cp sup/stress/*.h sup/stress/*.c $B/
seen=0
for n in F_C_CF380C F_C_CF235C; do b=${n#F_}
  python3 kq_post3.py ${n}_prog.c $B/$n.c --nogc > $B/$n.post 2>&1 || { echo "  control: the clean-up stopped on $n"; continue; }
  clang -w -O2 -flto -fomit-frame-pointer -I$B -I$RT -I. -o bin/ctl_$n $B/kq_io3.c $B/$n.c $B/gc_stack.c $B/kq_prim63.c 2> $B/$n.err || { echo "  control: $n does not build"; continue; }
  o=$(KQ_MEM=case/$b.mem timeout 120 bin/ctl_$n $(cat case/$b.args) 2>&1 | head -1); set -- $(cat case/$b.ref)
  res=$(echo "$o" | awk '{print $2}'); sum=$(echo "$o" | awk '{print $4}')
  if [ "$res" = "$1" ] && { [ "$2" = "0" ] || [ "$sum" = "$2" ]; }; then echo "  control: $n still gives the right answer"; else seen=$((seen+1)); fi
done
[ $seen = 2 ] && echo "GATE: with every save removed, both control programs go wrong under the stress collector" || echo "GATE: THE CONTROL DID NOT GO WRONG ($seen of 2)"
