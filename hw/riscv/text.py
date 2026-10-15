# hw/riscv/text.py: the .text words of a little-endian ELF64 object, one per line (decimal)
import sys, struct
b = open(sys.argv[1], 'rb').read()
shoff, = struct.unpack_from('<Q', b, 0x28); shentsize, shnum, shstrndx = struct.unpack_from('<HHH', b, 0x3A)
secs = [struct.unpack_from('<IIQQQQIIQQ', b, shoff + k * shentsize) for k in range(shnum)]
strtab = secs[shstrndx]
def name(s):
    o = strtab[4] + s[0]; return b[o:b.index(b'\0', o)].decode()
t = [s for s in secs if name(s) == '.text'][0]
data = b[t[4]:t[4] + t[5]]
for k in range(0, len(data), 4): print(struct.unpack_from('<I', data, k)[0])
