#!/bin/bash
# hw/build.sh [NAME]   (inside the PATCHED image, in /w)   hw/NAME.body (default: kernel) -> hw/NAME.elf, a kernel that
# QEMU (-kernel) or GRUB start as the machine's only program.  The same pipeline as every other program: the translator
# and the checker (KQFast.v, KQShape.v), CertiRocq, the clean-up of the C (kq_post3.py, without the collector's
# bookkeeping: nothing here collects) -- then, instead of the test harness of sup/v4, hw/kq_bare.c (no C library) and
# hw/boot.S, linked at 1 MB, and turned into the 32-bit file a Multiboot loader wants.  Put in front of every program:
# hw/$ISA.v (default X86: the processor's instructions, written in Rocq from its manual -- machine code the program
# puts in memory and runs with hw_run; the core knows no instruction set) and hw/lib.body (the PC's devices: the serial
# line, printing, the interrupt table and controllers, the timer).
# THE MACHINE'S ROUTINES ARE LINKED BY THEIR DECLARATIONS, not by a list: every `Axiom hw_..` of KQRun.v (the generic
# part) and of hw/Runtime.v (what the runtime gives) is linked to the C function kq_hw_<its name without hw_> (hw_load
# -> kq_hw_load, hw_run -> kq_hw_run), all in plain C in hw/kq_hw.h; a program's own routines, the same way through
# hw/NAME.ext.
# A kernel may have up to three Rocq programs, each through the same pipeline, linked together:
#   hw/NAME.body       the main one, on the first processor
#   hw/NAME_irq.body   if there is one: run AT THE MOMENT an interrupt or a fault comes (hw_vec says which); its answer
#                      0 means handled (a fault: the instruction is tried again)
#   hw/NAME_ap.body    if there is one: run by a second processor, once the main program has started it
# They share the memory's blocks; a program must leave alone what another one writes, or go through atomics (hw_rmw..).
# The program's OWN machine routines (assembly or C): declared in its text as `Axiom NAME : ..` (numbers, and the memory
# taken and given back as for every hw_ operation), listed in hw/NAME.ext, one per line, `ROCQNAME CNAME` (CNAME starts
# with kq_hw_), and written in hw/NAME.S or hw/NAME.c -- linked with the rest.  Such a routine is called as a C function
# (the System V convention): every number arrives marked, as the word 2n + 1, the memory as its token; it gives back the
# token, or a marked number.
cd /w; eval $(opam env); ulimit -s unlimited
x=${1:-kernel}; B=bld/hw; mkdir -p $B fast
RT=$(ls -d ~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime)
ISA=${ISA:-X86}; [ -f hw/$ISA.v ] || { echo "no hw/$ISA.v: the processor's instructions, written in Rocq (hw/X86.v is x86's)"; exit 1; }
for v in KQRun KQShape KQNat KQBound KQFast hw/Runtime hw/$ISA; do rocq c -R . KQ $v.v 2>&1 | grep -A4 "^Error" && exit 1; done
DECL=$(grep -ho "^Axiom hw_[a-z0-9_]*" KQRun.v hw/Runtime.v | sed 's/^Axiom //' | awk '{ c = $1; sub(/^hw_/, "", c); printf ", %s => \"kq_hw_%s\"", $1, c }')
CF="-O2 -ffreestanding -fno-stack-protector -mno-red-zone -fno-pic -fno-pie -fno-asynchronous-unwind-tables -fcf-protection=none -Ihw -Isup/v4 -I$RT -I$B -I."
objs=""
prog() {  # prog BODYNAME ENTRY [extra clang flags]: hw/BODYNAME.body -> one object whose only global is ENTRY
  local y=$1 entry=$2 n=HW_$1 ext=""; shift 2
  printf '#include "values.h"\n#include "kq_hw.h"\n' > $B/${n}_ext.h
  if [ -f hw/$y.ext ]; then
    while read -r r c; do
      [ -n "$r" ] || continue; case $r in \#*) continue;; esac
      case $c in kq_hw_*) ;; *) echo "hw/$y.ext: $c: a C name here starts with kq_hw_"; return 1;; esac
      ext="$ext, $r => \"$c\""; echo "extern value $c();" >> $B/${n}_ext.h
    done < hw/$y.ext
  fi
  { cat hand/hdr.txt; echo "Require Import KQ.hw.Runtime."; echo; cat hw/$ISA.v; echo; cat hw/lib.body; echo; cat hw/$y.body
    sed -e "s/%s/$n/" -e "s/%m/PPlain/" -e "s/%o/3/" -e "s/%b/$(bash bounds.sh $y)/" -e "s/@DECL@/$DECL$ext/" hw/ftr_hw.txt; } > fast/$n.v
  timeout 600 rocq c -R . KQ fast/$n.v > fast/$n.log 2>&1 || { echo "$y: ROCQ-FAIL"; grep -A10 "^Error" fast/$n.log | head -14; return 1; }
  echo "$y: $(grep "KQ-FAST" fast/$n.log | cut -c1-150)"; echo "$y: $(grep "^KQ-SHAPE" fast/$n.log | cut -c1-150)"
  python3 kq_post3.py ${n}_prog.c $B/$n.c --nogc > $B/$n.post 2>&1 || { echo "$y: POST-FAIL"; tail -3 $B/$n.post; return 1; }
  echo "$y: $(sed 's/.*one-sided tests, /left in the C: /' $B/$n.post | cut -c1-120)"
  clang -w $CF "$@" -Dbody=$entry -include $B/${n}_ext.h -c $B/$n.c -o $B/$n.o0 || return 1
  objcopy --keep-global-symbol=$entry $B/$n.o0 $B/$n.o || return 1
  objs="$objs $B/$n.o"
  [ -f hw/$y.S ] && { clang -c hw/$y.S -o $B/${y}_own_S.o || return 1; objs="$objs $B/${y}_own_S.o"; }
  [ -f hw/$y.c ] && { clang -w $CF -c hw/$y.c -o $B/${y}_own_c.o || return 1; objs="$objs $B/${y}_own_c.o"; }
  return 0
}
prog $x body || exit 1
[ -f hw/${x}_irq.body ] && { prog ${x}_irq kq_irq_body -mgeneral-regs-only || exit 1; }   # it runs inside an interrupt: no vector registers
[ -f hw/${x}_ap.body ] && { prog ${x}_ap kq_ap_body || exit 1; }
clang -w $CF -mgeneral-regs-only -c hw/kq_bare.c -o $B/kq_bare.o || exit 1
clang -w $CF -DKQ_NO_PRIM_INLINE -c sup/v4/kq_prim63.c -o $B/kq_prim63.o || exit 1
clang -c hw/boot.S -o $B/boot.o || exit 1
ld -m elf_x86_64 -n -T hw/link.ld -o $B/HW_$x.elf64 $B/boot.o $B/kq_bare.o $objs $B/kq_prim63.o 2>&1 | grep -v "RWX\|warning: .*elf64 has" ; [ -f $B/HW_$x.elf64 ] || exit 1
objcopy -I elf64-x86-64 -O elf32-i386 $B/HW_$x.elf64 hw/$x.elf && echo "built hw/$x.elf ($(stat -c %s hw/$x.elf) bytes)"
