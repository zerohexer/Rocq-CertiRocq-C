#!/bin/bash
# examples.sh   (inside the image, in /w)   the programs of proved/examples/ through the proved route: translated, every
# function proved (a lemma the kernel does not finish is an error), built, and the answer compared with the value in
# NAME.expect (worked out apart from Rocq).  They run on the memory and the arguments of tests/mkworst.py.
cd /w && ulimit -s unlimited; eval $(opam env)
export KQ_STRICT=1
D=dbg/examples; mkdir -p $D
python3 tests/mkworst.py $D > /dev/null || exit 1
ok=0; bad=0; fok=0; fbad=0; uok=0; ubad=0; ook=0; obad=0; cok=0; cbad=0; cskip=0
FREE="-w -O2 -ffreestanding -fno-builtin -nostdinc -isystem $(clang -print-resource-dir)/include -fno-stack-protector -fno-pie -no-pie -static -fno-asynchronous-unwind-tables -fcf-protection=none -ffunction-sections -fdata-sections -Wl,--gc-sections -Isup/free -Isup/v4 -Ihw"
for b in proved/examples/*.body; do
  n=$(basename $b .body)
  rm -f bin/P_$n   # no answer from a binary an earlier run left (F72)
  python3 proved/kitc.py $b 2>&1 | grep -v "^Warning\|^to KQC" | grep -v "^$n built" | head -3
  mem=$D/same.mem; args=$D/same.args   # an example with its own memory and arguments has NAME.mem, NAME.args
  [ -f proved/examples/$n.mem ] && mem=proved/examples/$n.mem; [ -f proved/examples/$n.args ] && args=proved/examples/$n.args
  got=$(KQ_MEM=$mem bin/P_$n $(cat $args) 2>&1 | head -1 | awk '{print $2}')
  if [ "$got" = "$(cat proved/examples/$n.expect)" ]; then ok=$((ok + 1)); else bad=$((bad + 1)); echo "$n: got $got, expected $(cat proved/examples/$n.expect)"; fi
  # the same functions freestanding: no hosted header, no libc (sup/free/)
  rm -f bin/F_$n
  clang $FREE -nostdlib -o bin/F_$n proved/gen/${n}_bare.c sup/free/kq_mem.c sup/free/kq_start_linux.c 2>&1 | head -3
  got=$(KQ_MEM=$mem bin/F_$n $(cat $args) 2>&1 | head -1 | awk '{print $2}')
  if [ "$got" = "$(cat proved/examples/$n.expect)" ]; then fok=$((fok + 1)); else fbad=$((fbad + 1)); echo "$n freestanding: got $got, expected $(cat proved/examples/$n.expect)"; fi
  # the printed C is not under the theorem (Rocq-C-solution.md §12.H): so the same text through other tools, each to the same answer.
  # Undefined behaviour trapped: what Clight defines and C does not would stop the program.
  clang $FREE -O1 -fsanitize=undefined -fsanitize-trap=undefined -nostdlib -o bin/U_$n proved/gen/${n}_bare.c sup/free/kq_mem.c sup/free/kq_start_linux.c 2>&1 | head -3
  got=$(KQ_MEM=$mem bin/U_$n $(cat $args) 2>&1 | head -1 | awk '{print $2}')
  if [ "$got" = "$(cat proved/examples/$n.expect)" ]; then uok=$((uok + 1)); else ubad=$((ubad + 1)); echo "$n with undefined behaviour trapped: got $got, expected $(cat proved/examples/$n.expect)"; fi
  # no optimization, no use of C's aliasing rules
  clang $FREE -O0 -fno-strict-aliasing -nostdlib -o bin/O_$n proved/gen/${n}_bare.c sup/free/kq_mem.c sup/free/kq_start_linux.c 2>&1 | head -3
  got=$(KQ_MEM=$mem bin/O_$n $(cat $args) 2>&1 | head -1 | awk '{print $2}')
  if [ "$got" = "$(cat proved/examples/$n.expect)" ]; then ook=$((ook + 1)); else obad=$((obad + 1)); echo "$n at -O0: got $got, expected $(cat proved/examples/$n.expect)"; fi
  # CompCert's ccomp, when no operation of the machine is called (their C bodies are GNU C), and when it is here: its licence is
  # non-commercial, and nothing else depends on it (KQ_NO_CCOMP=1 leaves it out)
  if [ -n "$KQ_NO_CCOMP" ] || ! command -v ccomp > /dev/null || grep -q '#include "kq_hw.h"' proved/gen/${n}_bare.c; then cskip=$((cskip + 1)); else
    if ccomp -c -Isup/free -Isup/v4 -o /tmp/cc_$n.o proved/gen/${n}_bare.c 2>&1 | grep -v "warning" | head -3 | grep . ; then cbad=$((cbad + 1)); else
      clang $FREE -nostdlib -o bin/C_$n /tmp/cc_$n.o sup/free/kq_mem.c sup/free/kq_start_linux.c 2>&1 | head -3
      got=$(KQ_MEM=$mem bin/C_$n $(cat $args) 2>&1 | head -1 | awk '{print $2}')
      if [ "$got" = "$(cat proved/examples/$n.expect)" ]; then cok=$((cok + 1)); else cbad=$((cbad + 1)); echo "$n through ccomp: got $got, expected $(cat proved/examples/$n.expect)"; fi
    fi
  fi
  rm -f bin/U_$n bin/O_$n bin/C_$n /tmp/cc_$n.o
done
# an ordinary Rocq file: Rocq compiles it on its own, kitc.py reads the entry's arguments from its signature (Rocq-C-solution.md §12.B)
for v in proved/vfiles/*.v; do
  n=$(basename $v .v)
  rm -f bin/P_$n
  coqc -w -all -R . KQ $v > /dev/null 2>&1 || { bad=$((bad + 1)); echo "$n: Rocq refused the file on its own"; continue; }
  python3 proved/kitc.py $v 2>&1 | grep -v "^Warning\|^to KQC" | grep -v "^$n built" | head -3
  got=$(KQ_MEM=proved/vfiles/$n.mem bin/P_$n $(cat proved/vfiles/$n.args) 2>&1 | head -1 | awk '{print $2}')
  if [ "$got" = "$(cat proved/vfiles/$n.expect)" ]; then ok=$((ok + 1)); else bad=$((bad + 1)); echo "$n: got $got, expected $(cat proved/vfiles/$n.expect)"; fi
done
echo "examples: $ok give the expected answer, $bad do not"
echo "freestanding: $fok give the expected answer with no hosted header and no libc, $fbad do not"
echo "the same C: undefined behaviour trapped $uok right, $ubad not; -O0 $ook right, $obad not; ccomp $cok right, $cbad not, $cskip not built with it (an operation of the machine, or no ccomp)"
[ $bad = 0 ] && [ $fbad = 0 ] && [ $ubad = 0 ] && [ $obad = 0 ] && [ $cbad = 0 ]
