/* sup/free/kq_start_linux.c -- a start for the gate's check, on x86-64 Linux, with no libc: the arguments from the command line, the
   memory from the file $KQ_MEM, the answer printed.  Only this file knows the operating system; a kernel has hw/boot.S and hw/kq_bare.c
   in its place. */
#include <stddef.h>
#include <stdint.h>
#include "gc_stack.h"
#define KQ_NO_PRIM_INLINE
#include "kq_io.h"
extern value body(struct thread_info *);
extern long kq_nb, kq_nn, kq_checksum(void);
extern char *kq_arena; extern unsigned long kq_arena_len;
extern void *kq_alloc(unsigned long);
uintptr_t kq_hw_wlo, kq_hw_whi;
static inline long sys3(long n, long a, long b, long c) {
  long r; __asm__ volatile ("syscall" : "=a"(r) : "a"(n), "D"(a), "S"(b), "d"(c) : "rcx", "r11", "memory"); return r;
}
static inline long sys6(long n, long a, long b, long c, long d, long e, long f) {
  long r; register long r10 __asm__("r10") = d; register long r8 __asm__("r8") = e; register long r9 __asm__("r9") = f;
  __asm__ volatile ("syscall" : "=a"(r) : "a"(n), "D"(a), "S"(b), "d"(c), "r"(r10), "r"(r8), "r"(r9) : "rcx", "r11", "memory"); return r;
}
__attribute__((noreturn)) void kq_stop(long code) { for (;;) sys3(60, code, 0, 0); }
static void put(const char *s, long n) { while (n > 0) { long k = sys3(1, 1, (long) s, n); if (k <= 0) kq_stop(4); s += k; n -= k; } }
static void puts0(const char *s) { long n = 0; while (s[n]) n++; put(s, n); }
static void putn(long v) { char b[24]; int i = 24; unsigned long u = v < 0 ? -(unsigned long) v : (unsigned long) v;
  do { b[--i] = '0' + u % 10; u /= 10; } while (u); if (v < 0) b[--i] = '-'; put(b + i, 24 - i); }
static int kq_argc; static char **kq_argv;
static long num(const char *s) { int neg = 0; long v = 0; if (*s == '-') { neg = 1; s++; } while (*s >= '0' && *s <= '9') v = v * 10 + (*s++ - '0'); return neg ? -v : v; }
value kq_arg(value i) { long k = KQ_N(i); return KQ_V((k >= 0 && k + 1 < kq_argc) ? num(kq_argv[k + 1]) : 0); }
/* input: read to the next number on standard input; output: one number a line */
static int peeked = -2; static char ibuf[65536]; static long ipos, ilen;
static int getc0(void) { if (ipos == ilen) { ilen = sys3(0, 0, (long) ibuf, sizeof ibuf); ipos = 0; if (ilen <= 0) { ilen = 0; return -1; } } return (unsigned char) ibuf[ipos++]; }
value kq_in(value h, value i, value s) {
  int c = peeked == -2 ? getc0() : peeked; peeked = -2;
  while (c != -1 && c != '-' && (c < '0' || c > '9')) c = getc0();
  long v = -1;
  if (c != -1) { int neg = 0; if (c == '-') { neg = 1; c = getc0(); } v = 0; while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); c = getc0(); } if (neg) v = -v; peeked = c; }
  return kq_updb(h, i, KQ_V(v), s);
}
value kq_out(value v, value s) { putn(KQ_N(v)); put("\n", 1); return s; }
/* the memory file, as sup/v4/kq_io3.c reads it */
static const char *fp, *fe;
static void skip(void) { while (fp < fe && (*fp == ' ' || *fp == '\n' || *fp == '\t' || *fp == '\r')) fp++; }
static long rdnum(void) { skip(); int neg = 0; long v = 0; if (fp < fe && *fp == '-') { neg = 1; fp++; } if (fp == fe || *fp < '0' || *fp > '9') kq_stop(2); while (fp < fe && *fp >= '0' && *fp <= '9') v = v * 10 + (*fp++ - '0'); return neg ? -v : v; }
static void load(const char *path) {
  long fd = sys3(2, (long) path, 0, 0); if (fd < 0) return;
  long cap = 1L << 30; char *buf = (char *) sys6(9, 0, cap, 3, 0x22, -1, 0); long n = 0, k;   /* mmap, private and anonymous */
  while ((k = sys3(0, fd, (long) buf + n, cap - n)) > 0) n += k;
  sys3(3, fd, 0, 0); fp = buf; fe = buf + n;
  kq_nb = rdnum(); if (kq_nb < 0 || kq_nb > KQ_MAXB) kq_stop(2);
  for (long h = 0; h < kq_nb; h++) {
    long len = rdnum(); if (len < 0 || len >= (1L << 31)) kq_stop(2);
    kq_b[h].len = (unsigned int) len; kq_b[h].lim = 2 * (unsigned int) len; kq_len0[h] = (unsigned int) len;
    kq_b[h].p = (value *) kq_alloc((len + 1) * sizeof(value));
    skip(); if (fp < fe && *fp == 'z') { fp++; for (long i = 0; i < len; i++) kq_b[h].p[i] = KQ_V(0); continue; }
    for (long i = 0; i < len; i++) kq_b[h].p[i] = KQ_V(rdnum());
  }
  skip();
  if (fe - fp >= 3 && fp[0] == 'n' && fp[1] == '3' && fp[2] == '2') {
    fp += 3; kq_nn = rdnum(); if (kq_nn < 0 || kq_nn > KQ_MAXB) kq_stop(2);
    for (long h = 0; h < kq_nn; h++) {
      long len = rdnum(); if (len < 0 || len >= (1L << 31)) kq_stop(2);
      kq_n[h].len = (unsigned int) len; kq_n[h].lim = 2 * (unsigned int) len; kq_n[h].p = (int *) kq_alloc((len + 1) * sizeof(int));
      skip(); if (fp < fe && *fp == 'z') { fp++; for (long i = 0; i < len; i++) kq_n[h].p[i] = 0; continue; }
      for (long i = 0; i < len; i++) kq_n[h].p[i] = (int) rdnum();
    }
  }
  sys3(11, (long) buf, cap, 0);   /* munmap */
}
__attribute__((used)) void kq_start(long *sp) {
  kq_argc = (int) sp[0]; kq_argv = (char **) (sp + 1); char **env = kq_argv + kq_argc + 1; const char *path = 0;
  for (; *env; env++) { const char *e = *env, *m = "KQ_MEM="; while (*m && *e == *m) { e++; m++; } if (!*m) path = e; }
  long room = 1L << 36;   /* lazily: nothing is taken until it is touched */
  kq_arena = (char *) sys6(9, 0, room, 3, 0x4022, -1, 0); kq_arena_len = room;   /* MAP_NORESERVE */
  if ((long) kq_arena < 0 && (long) kq_arena > -4096) kq_stop(2);
  if (path) load(path);
  kq_hw_wlo = (uintptr_t) -1; kq_hw_whi = 0;
  for (int h = 0; h < KQ_MAXB; h++) if (kq_b[h].lim) { uintptr_t p = (uintptr_t) kq_b[h].p, e = p + 4 * (uintptr_t) kq_b[h].lim; if (p < kq_hw_wlo) kq_hw_wlo = p; if (e > kq_hw_whi) kq_hw_whi = e; }
  sys6(9, 0x10000000, 4096, 3, 0x100022, -1, 0);   /* a page stands for a device, as in the hosted test */
  value val = body((struct thread_info *) 0);
  puts0("result "); putn(KQ_N(val)); puts0(" checksum "); putn(kq_checksum()); put("\n", 1);
  kq_stop(0);
}
__asm__(".globl _start\n_start:\n  xor %ebp, %ebp\n  mov %rsp, %rdi\n  and $-16, %rsp\n  call kq_start\n  hlt\n");
