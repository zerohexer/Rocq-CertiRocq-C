#!/bin/bash
# hw/build_proved.sh [NAME]   (inside the image, in /w)   hw/NAME.body (default: kernel) through the PROVED route, with the
# programs it has: hw/NAME_irq.body (run at an interrupt or a fault), hw/NAME_ap.body (run by a second processor) and the
# routines of hw/NAME.ext (the program's own assembly or C, hw/NAME.S, hw/NAME.c).  Each program is one Rocq text -- the
# ISA's instructions (hw/$ISA.v, default X86), the library (hw/lib.body) and the program -- that the translator reads, whose
# functions the kernel checks against it (a lemma that does not finish is an error), and whose Clight is printed as C.  The C
# is built with the machine's runtime of hw/build.sh (hw/kq_bare.c, hw/boot.S, linked at 1 MB, turned into the 32-bit file
# a Multiboot loader wants): hw/NAME.elf, for QEMU (hw/run.sh NAME) or GRUB.  The programs share the tables (the memory) and
# the machine's functions of the first; their own functions are named irq_f1000 .. and ap_f1000 ..
# What the proof assumes of the machine and of the C bodies of its operations (hw/kq_hw.h, the routines) is `hw_law` and
# `hwf_law` (proved/README.md).
cd /w; eval $(opam env); ulimit -s unlimited
x=${1:-kernel}; B=bld/hwp; mkdir -p $B proved/gen
RT=$(ls -d ~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime)
ISA=${ISA:-X86}
CF="-O2 -ffreestanding -fno-stack-protector -mno-red-zone -fno-pic -fno-pie -fno-asynchronous-unwind-tables -fcf-protection=none -Ihw -Isup/v4 -I$RT -I$B -I."
objs=""
prog() {  # prog SUFFIX [kitc flags]: hw/NAME{SUFFIX}.body -> one object; prog "" is the main program
  local suf=$1; shift
  local y=$x$suf n=HWP_$x$suf
  [ -f hw/$y.body ] || [ -f hw/${y}_p.body ] || return 0
  local src=hw/$y.body; [ -f hw/${y}_p.body ] && src=hw/${y}_p.body
  python3 hw/p_prep.py $src hw/$x.ext $B/$n.prep $B/$n.ext || return 1
  { echo "Require Import KQ.hw.Runtime."; echo "Require Import KQ.hw.User."; cat hw/$ISA.v; echo; cat hw/lib.body; echo; cat $B/$n.prep; } > $B/$n.body
  KQ_STRICT=1 python3 proved/kitc.py --bare --ext=$B/$n.ext "$@" $B/$n.body 2>&1 | grep -v "^Warning\|^to KQC" | awk '{ print substr($0, (length($0) > 700 ? length($0) - 700 : 1)) }'
  local C=proved/gen/${n}_bare.c; [ -f $C ] || { echo "$y: no C was made"; return 1; }
  clang -w $CF $FLAGS -c $C -o $B/$n.o || return 1
  objs="$objs $B/$n.o"
  [ -f hw/$y.S ] && { clang -c hw/$y.S -o $B/${y}_own_S.o || return 1; objs="$objs $B/${y}_own_S.o"; }
  [ -f hw/$y.c ] && { clang -w $CF -c hw/$y.c -o $B/${y}_own_c.o || return 1; objs="$objs $B/${y}_own_c.o"; }
  return 0
}
# the main program first: it writes the user-routine numbering (hw/$x.ext's order) the others read
FLAGS="" prog "" || exit 1
FLAGS="-mgeneral-regs-only" prog _irq --secondary --prefix=irq_ --entry=kq_irq_body || exit 1   # it runs inside an interrupt: no vector registers
FLAGS="" prog _ap --secondary --prefix=ap_ --entry=kq_ap_body || exit 1
clang -w $CF -mgeneral-regs-only -c hw/kq_bare.c -o $B/kq_bare.o || exit 1
clang -w $CF -DKQ_NO_PRIM_INLINE -c sup/v4/kq_prim63.c -o $B/kq_prim63.o || exit 1
clang -c hw/boot.S -o $B/boot.o || exit 1
ld -m elf_x86_64 -n -T hw/link.ld -o $B/HWP_$x.elf64 $B/boot.o $B/kq_bare.o $objs $B/kq_prim63.o 2>&1 | grep -v "RWX\|warning: .*elf64 has"
[ -f $B/HWP_$x.elf64 ] || exit 1
objcopy -I elf64-x86-64 -O elf32-i386 $B/HWP_$x.elf64 hw/${x}_p.elf && echo "built hw/${x}_p.elf ($(stat -c %s hw/${x}_p.elf) bytes)"
