#!/usr/bin/env python3
"""cffi.py FILE.body HEADER.h : the C functions a program declares, connected.  A declaration names the C function
after a prefix that says how it is called; every argument is a number (an address too):

    Axiom c_putchar : int -> mem -> mem.        putchar(c) for its effect; the memory is passed on
    Axiom cr_rand : int -> int -> mem -> mem.   rand(): its result into cell i of block h (the last two numbers)
    Axiom c_labs : int -> int.                  labs(x), a function without effects: its result is the answer

Writes HEADER.h (the C that connects each one, with the C library's headers and those named in $CINCLUDE) and prints
the entries for CertiRocq's `Extract Constants` (`, c_putchar => "kq_c_putchar"` ..).  A program that names hw_addr
gets the address of a narrow block too, for a buffer handed to C; one that names kq_grow or kq_size, those two.  They
are added to the program's own footer, not the shared one, so no other program's C changes."""
import os, re, sys

body, header = sys.argv[1], sys.argv[2]
text = open(body).read()
decls = re.findall(r'^\s*Axiom\s+(c_|cr_)([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([^.]*)\.', text, re.M)
out = ['/* written by cffi.py from %s: the C functions the program declares */' % os.path.basename(body),
       '#include "kq_io.h"']
out += ['#include <%s>' % h for h in ('stdint.h', 'stdio.h', 'stdlib.h', 'string.h', 'unistd.h', 'math.h', 'time.h', 'ctype.h')]
out += ['#include "%s"' % h for h in os.environ.get('CINCLUDE', '').split()]
ext = []
for pre, name, ty in decls:
    parts = [t.strip() for t in ty.split('->')]
    if any(t not in ('int', 'mem') for t in parts):
        sys.exit('%s%s: only int and mem in the type of a C function (%s)' % (pre, name, ty.strip()))
    ints = len([t for t in parts if t == 'int'])
    effect = parts[-2:] == ['mem', 'mem'] and parts.count('mem') == 2
    pure = parts.count('mem') == 0 and parts[-1] == 'int'
    w = 'kq_%s%s' % (pre, name)
    if pre == 'c_' and effect:
        ps = ['value a%d' % k for k in range(ints)] + ['value s']
        call = '%s(%s)' % (name, ', '.join('KQ_N(a%d)' % k for k in range(ints)))
        out.append('static inline value %s(%s) { %s; return s; }' % (w, ', '.join(ps), call))
    elif pre == 'c_' and pure:
        ps = ['value a%d' % k for k in range(ints - 1)]
        call = '%s(%s)' % (name, ', '.join('KQ_N(a%d)' % k for k in range(ints - 1)))
        out.append('static inline value %s(%s) { return KQ_V((long) %s); }' % (w, ', '.join(ps) or 'void', call))
    elif pre == 'cr_' and effect and ints >= 2:
        n = ints - 2
        ps = ['value a%d' % k for k in range(n)] + ['value h', 'value i', 'value s']
        call = '%s(%s)' % (name, ', '.join('KQ_N(a%d)' % k for k in range(n)))
        out.append('static inline value %s(%s) { return kq_updb(h, i, KQ_V((long) %s), s); }' % (w, ', '.join(ps), call))
    else:
        sys.exit('%s%s: a C function is int -> .. -> mem -> mem (c_), int -> .. -> int (c_, no effects), or '
                 'int -> .. -> int -> int -> mem -> mem (cr_: the result into cell i of block h)' % (pre, name))
    ext.append(', %s%s => "%s"' % (pre, name, w))
if re.search(r'\bkq_(grow|size)\b', text):      # a block that grows (KQRun.v), named only by programs that use it
    ext.append(', kq_grow => "kq_grow", kq_size => "kq_size"')
if re.search(r'\bhw_addr\b', text):
    out.append('static inline value kq_hw_addr(value h) { kq_u k = (kq_u) h >> 1; '
               'return KQ_V(k < KQ_MAXB ? (long) (uintptr_t) kq_n[k].p : 0L); }')
    ext.append(', hw_addr => "kq_hw_addr"')
open(header, 'w').write('\n'.join(out) + '\n')
print(''.join(ext))
