#!/bin/bash
# compile.sh FILE.body [numbers..]   (inside the image, in /w)   one program: Rocq -> C -> a program, then run with the
# numbers as its command line.  FILE.body defines `main : int` (examples/).  The translator puts it in the standard form
# and proves that equal to it, the checker reads it, CertiRocq compiles it, kq_post3.py cleans the C, clang builds it:
# bin/NAME.  Printed: the checker's verdict, what is left in the C, the program's output, and the number main answers.
# C FUNCTIONS -- any, from the C library or another: declared in FILE.body as `Axiom c_NAME ..` or `Axiom cr_NAME ..`
# (cffi.py says how); CINCLUDE="a.h b.h" adds headers, CLIBS="-lm" libraries.  FILE.c next to FILE.body, if there is
# one, is compiled and linked too (C functions of the program's own, called the same way).  FILE.mem, if there is one,
# is the starting memory (the format kq_io3.c reads).  A program that uses lib/Slab.v (a heap that grows) just calls its
# slab_ functions.
cd /w; eval $(opam env); ulimit -s unlimited
f=$1; [ -n "$f" ] && [ -f "$f" ] || { echo "usage: compile.sh FILE.body [numbers..]"; exit 1; }; shift
n=$(basename "$f" .body); n=U_${n//[^A-Za-z0-9_]/_}; base=${f%.body}
mkdir -p fast bld/user bin
stale=0; for v in KQRun KQShape KQNat KQBound KQFast; do [ $v.vo -nt $v.v ] || stale=1; done
if [ $stale = 1 ]; then
  echo "compiling the kit's Rocq files (once)"
  for v in KQRun KQShape KQNat KQBound KQFast; do rocq c -R . KQ $v.v 2>&1 | grep -A4 "^Error" && exit 1; done
fi
# a program that names a slab_ function gets lib/Slab.v's text in front of it: the checker and the translator read it
# as the program's own
src=bld/user/$n.full.body
{ grep -q '\bslab_' "$f" && sed -n '/(\* SLAB-BEGIN \*)/,/(\* SLAB-END \*)/p' lib/Slab.v
  cat "$f"; } > $src
ext=$(python3 cffi.py "$src" bld/user/${n}_ffi.h) || { echo "$ext"; exit 1; }
{ cat hand/hdr.txt; echo; cat "$src"
  sed -e "s/%s/$n/" -e "s/%m/(PUse [])/" -e "s/%o/3/" -e "s/%b/KQTests/" -e "s/kq_fits => \"kq_fits\" \]/kq_fits => \"kq_fits\"$ext ]/" hand/ftr_kq.txt
} > fast/$n.v
rocq c -R . KQ fast/$n.v > fast/$n.log 2>&1 || { grep -A12 "^Error" fast/$n.log | head -24; exit 1; }
grep "^KQ-SHAPE" fast/$n.log | cut -c1-200
RT=$(ls -d ~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime)
cp sup/v4/*.h sup/v4/*.c bld/user/
python3 kq_post3.py ${n}_prog.c bld/user/$n.c > bld/user/$n.post 2>&1 || { tail -3 bld/user/$n.post; exit 1; }
sed 's/.*one-sided tests, /left in the C: /' bld/user/$n.post | cut -c1-160
own=""; [ -f "$base.c" ] && own="$base.c"
CF="-w -O2 -flto -fomit-frame-pointer -Ibld/user -I$RT -I."
clang $CF -include bld/user/${n}_ffi.h -c bld/user/$n.c -o bld/user/$n.o || exit 1
clang $CF -o bin/$n bld/user/kq_io3.c bld/user/$n.o $RT/gc_stack.c bld/user/kq_prim63.c $own $CLIBS || exit 1
echo "built bin/$n"
mem=""; [ -f "$base.mem" ] && mem="$base.mem"
KQ_MEM=$mem ./bin/$n "$@" > bld/user/$n.res || { cat bld/user/$n.res; echo "the program stopped: exit $?"; exit 1; }
grep -v "^result -\?[0-9]* checksum -\?[0-9]* harness_ms " bld/user/$n.res
echo "main = $(awk '/^result -?[0-9]+ checksum/ {print $2}' bld/user/$n.res)"
