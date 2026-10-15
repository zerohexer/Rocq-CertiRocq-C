#!/bin/bash
# hw/run.sh [NAME]   (on the HOST, in the kit's directory, after hw/build.sh)   start hw/NAME.elf (default: kernel) in
# QEMU as the machine's only program; its serial line comes out here.  QEMU's exit status is 2 * result + 1 (the
# isa-debug-exit device), so 1 means the program answered 0.   QEMU_ACCEL="-accel kvm" for the hardware's own processor;
# SMP=2 for two processors.
x=${1:-kernel}
[ -f hw/$x.elf ] || { echo "no hw/$x.elf: build it first (hw/build.sh $x, in the image)"; exit 2; }
timeout ${T:-120} qemu-system-x86_64 -kernel hw/$x.elf -serial stdio -display none -no-reboot -m 256M -smp ${SMP:-1} \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 ${QEMU_ACCEL:--accel tcg}
st=$?; echo "QEMU exit status $st: the program answered $(( (st - 1) / 2 ))"
