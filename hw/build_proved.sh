#!/bin/bash
# hw/build_proved.sh [NAME]   (inside the image, in /w)   hw/NAME_p.body (default: kernel) through the PROVED route: the
# ISA's instructions (hw/$ISA.v, default X86), the library (hw/lib.body) and the program are one Rocq text; the translator
# reads it, the kernel checks that the generated functions compute it (a lemma that does not finish is an error), the
# Clight is printed as C, and that C is built with the machine's runtime of hw/build.sh (hw/kq_bare.c, hw/boot.S, linked at
# 1 MB, turned into the 32-bit file a Multiboot loader wants): hw/NAME_p.elf, for QEMU (hw/run.sh NAME_p) or GRUB.
# What the proof assumes of the machine and of the C bodies of its operations (hw/kq_hw.h) is `hw_law` (proved/README.md).
cd /w; eval $(opam env); ulimit -s unlimited
x=${1:-kernel}; B=bld/hwp; mkdir -p $B proved/gen
RT=$(ls -d ~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime)
ISA=${ISA:-X86}
n=HWP_$x
{ echo "Require Import KQ.hw.Runtime."; cat hw/$ISA.v; echo; cat hw/lib.body; echo; cat hw/${x}_p.body; } > $B/$n.body
KQ_STRICT=1 python3 proved/kitc.py --bare $B/$n.body 2>&1 | grep -v "^Warning\|^to KQC" | awk "{ print substr(\$0, (length(\$0) > 700 ? length(\$0) - 700 : 1)) }"
C=proved/gen/${n}_bare.c; [ -f $C ] || { echo "no C was made"; exit 1; }
CF="-O2 -ffreestanding -fno-stack-protector -mno-red-zone -fno-pic -fno-pie -fno-asynchronous-unwind-tables -fcf-protection=none -Ihw -Isup/v4 -I$RT -I$B -I."
clang -w $CF -c $C -o $B/$n.o || exit 1
clang -w $CF -mgeneral-regs-only -c hw/kq_bare.c -o $B/kq_bare.o || exit 1
clang -w $CF -DKQ_NO_PRIM_INLINE -c sup/v4/kq_prim63.c -o $B/kq_prim63.o || exit 1
clang -c hw/boot.S -o $B/boot.o || exit 1
ld -m elf_x86_64 -n -T hw/link.ld -o $B/$n.elf64 $B/boot.o $B/kq_bare.o $B/$n.o $B/kq_prim63.o 2>&1 | grep -v "RWX\|warning: .*elf64 has"
[ -f $B/$n.elf64 ] || exit 1
objcopy -I elf64-x86-64 -O elf32-i386 $B/$n.elf64 hw/${x}_p.elf && echo "built hw/${x}_p.elf ($(stat -c %s hw/${x}_p.elf) bytes)"
