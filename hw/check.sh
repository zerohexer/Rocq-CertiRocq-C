#!/bin/bash
# hw/check.sh   (on the HOST, in the kit's directory)   THE MACHINE'S GATE.  First the laws (hw/spec.sh: KQSpec.v, its
# model, the proofs about kernel code).  Then every kernel of hw/ is built in the patched
# image and started in QEMU, under QEMU's own processor and under KVM (the host's, when /dev/kvm can be used); every
# check it makes must pass (QEMU's exit status 1: the program answered 0).  Each has a CONTROL, the same kernel changed
# in one place so that its checks must FAIL -- what shows the checks can see the fault they are there for:
#   kernel   devices, page tables, interrupts taken by the program, the processor, memory, PCI, atomics, bytes in bulk,
#            its own assembly            control: one page-table entry points at the wrong 2 MB      -> page 16
#   irqnow   Rocq run AT THE MOMENT each timer interrupt comes
#                                        control: the interrupt program does not acknowledge         -> irq 1
#   fault    a page fault handled by a Rocq program: the page mapped, the write tried again
#                                        control: the fault program maps the wrong 64 MB + 2 MB      -> map 1
#   smp      two processors (-smp 2), the second started by the Rocq program, an atomic counter
#                                        control: the second processor is never started             -> cpus 1
#   own      an interrupt entry routine the program writes itself (x86-64 bytes, in Rocq), through which the timer's
#            interrupts come; what a call through hw_run costs
#                                        control: the routine hands the runtime vector 33, not 32   -> own 0
# Every x86 instruction these kernels use is machine code written in Rocq (hw/X86.v), run through hw_run.
cd "$(dirname "$0")/.." || exit 1
IMG=${IMG:-kernelq-certirocq:1b45a1aa-kq2}
mk() {   # mk CONTROL FROM FILE-SUFFIX SED: a copy of kernel FROM, one file of it changed
  local c=$1 f=$2 suf=$3 ex=$4
  for x in hw/$f.body hw/${f}_irq.body hw/${f}_ap.body hw/$f.ext hw/$f.S; do
    [ -f $x ] || continue; y=${x/hw\/$f/hw\/$c}; cp $x $y
  done
  sed -i "$ex" hw/$c$suf.body
  cmp -s hw/$f$suf.body hw/$c$suf.body && { echo "GATE: THE CONTROL $c COULD NOT BE MADE"; exit 1; }
}
mk control_wrongmap kernel "" 's/upd32 PD1 0 131 s1/upd32 PD1 0 (MB2 + 131) s1/'
mk control_noeoi irqnow _irq 's/let s2 := hw_port_out 1 32 32 s1 in/let s2 := s1 in/'
mk control_wrongpage fault _irq 's/67108864 + k \* 2097152 + 131/69206016 + k * 2097152 + 131/'
mk control_nostart smp "" 's/(LAPIC + 768) 804360/(LAPIC + 896) 0/g'
mk control_wrongvec own "" 's/own_entry VEC/own_entry 33/'
docker run --rm --memory=2g --memory-swap=2g --network=none -v "$PWD":/w $IMG bash /w/hw/spec.sh 2>&1 | grep "GATE\|claims"
for x in kernel irqnow fault smp own control_wrongmap control_noeoi control_wrongpage control_nostart control_wrongvec; do
  docker run --rm --memory=2g --memory-swap=2g --network=none -v "$PWD":/w $IMG bash /w/hw/build.sh $x > dbg_hw_$x.txt 2>&1
  grep -q "^built hw/$x.elf" dbg_hw_$x.txt || { echo "GATE: hw/$x DID NOT BUILD"; tail -6 dbg_hw_$x.txt; exit 1; }
done
for x in kernel irqnow fault smp own; do grep "KQ-SHAPE" dbg_hw_$x.txt | cut -c1-110; done
run() {  # run NAME ACCEL: the program's lines and its answer
  local smp=1; case $1 in smp|control_nostart) smp=2;; esac
  local A="-accel tcg"; [ $2 = kvm ] && A="-accel kvm -cpu host"
  SMP=$smp QEMU_ACCEL="$A" T=180 bash hw/run.sh $1 2>&1 | grep -v "^KQ-BOOT"
}
for acc in tcg kvm; do
  [ $acc = kvm ] && ! [ -w /dev/kvm ] && { echo "(no KVM here)"; continue; }
  for x in kernel irqnow fault smp own; do
    out=$(run $x $acc); echo "$out" | grep -v "^Rocq kernel" | sed "s/^/  $acc $x: /"
    echo "$out" | grep -q "QEMU exit status 1:" && echo "GATE: $x passes every check ($acc)" || echo "GATE: $x FAILS ($acc)"
    [ $x = smp ] && echo "  (the plain read-and-write counter below 2000000: the two processors did run at the same time, and only the atomic one kept every update)"
  done
done
expect() {  # expect CONTROL LINE
  local out; out=$(run $1 tcg); echo "$out" | grep "^$2\|exit status\|EXCEPTION" | sed "s/^/  $1: /"
  echo "$out" | grep -q "^$2$" && echo "GATE: the control $1 fails as it must" || echo "GATE: THE CONTROL $1 DID NOT FAIL"
}
expect control_wrongmap "page 16"
expect control_noeoi "irq  1"
expect control_wrongpage "map  1"
expect control_nostart "cpus 1"
expect control_wrongvec "own  0"
