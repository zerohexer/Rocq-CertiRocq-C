#!/bin/bash
# hw/riscv/check.sh   (inside the image, in /w)   THE RISC-V EXAMPLE OF hw/WRITING-INSTRUCTIONS.md, checked without a
# RISC-V machine: Riscv.v compiles (its Example pins checked by Rocq's kernel), and the 20 instruction words it computes
# are the very words LLVM's assembler makes of the same assembly text (enc.S; without the compressed 2-byte forms,
# which the assembler would otherwise choose for some of them).
cd /w; eval $(opam env)
rocq c -R . KQ hw/riscv/Riscv.v > /tmp/rv.log 2>&1 || { grep -A8 Error /tmp/rv.log; exit 1; }; echo "Riscv.v compiles: its pins hold"
rocq c -R . KQ hw/riscv/EncList.v > /tmp/enc_rocq.txt 2>&1 || { head /tmp/enc_rocq.txt; exit 1; }
clang --target=riscv64-unknown-elf -march=rv64ima -c hw/riscv/enc.S -o /tmp/enc.o && python3 hw/riscv/text.py /tmp/enc.o > /tmp/enc_asm.txt
python3 - <<'PYEOF'
import re
r = [int(x) for x in re.findall(r'-?\d+', open('/tmp/enc_rocq.txt').read().split('=')[1].split(':')[0])]
a = [int(x) for x in open('/tmp/enc_asm.txt').read().split()]
asm = [l.strip() for l in open('hw/riscv/enc.S') if l.strip() and not l.strip().startswith(('.', '/'))]
same = sum(1 for x, y in zip(r, a) if x == y)
for x, y, t in zip(r, a, asm):
    print("  %-24s rocq 0x%08x  assembler 0x%08x  %s" % (t, x, y, "same" if x == y else "DIFFERENT"))
print("RISC-V encodings: %d words from Rocq, %d from the assembler, %d the same" % (len(r), len(a), same))
PYEOF
