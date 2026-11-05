// kq_hw.h -- THE MACHINE, the generic part: the bodies of KQRun.v's hw_ operations, in plain C -- `volatile` accesses,
// C11 atomics, memmove / memset / memcmp, a call through a pointer.  No assembly: the same text for every processor GCC
// or Clang build for.  No instruction set is known here: a program writes the instructions it needs itself, in Rocq,
// and runs them through hw_run (hw/X86.v).
//
// Order.  The program's order of these operations is kept by the Rocq text (each takes the memory the one before gave
// back).  Here, each also tells the C compiler not to move ANY memory access across it ("memory" clobber on an empty
// asm statement -- a compiler barrier, no instruction -- and `volatile`): a table written in a narrow block is in memory
// before a device is told about it; a register is read where the program reads it, never twice, never not at all.
// (C does it the same way, CompCert included: a `volatile` access is kept as written.)
//
// The program's own WIDE blocks are not reachable this way: a store, an atomic, a copy or a fill whose bytes would fall
// in their memory does nothing (KQSpec.v: these operations never change a wide cell).  NARROW blocks are reachable on
// purpose -- page tables and interrupt tables are built in them -- and their addresses come from hw_addr.
#ifndef KQ_HW_H
#define KQ_HW_H
#include "kq_io.h"
#include <stdint.h>
#include <stddef.h>
#define KQ_HW static inline __attribute__((always_inline))
#define KQ_A(a) ((uintptr_t) KQ_N(a))
#define KQ_BAR() __asm__ volatile ("" ::: "memory")
extern uintptr_t kq_hw_wlo, kq_hw_whi;            /* where the wide blocks are (the harness says) */
KQ_HW int kq_hw_wide(uintptr_t a, uintptr_t n) { return a < kq_hw_whi && a + n > kq_hw_wlo; }
KQ_HW value kq_hw_put(value h, value i, long x, value s) { return kq_updb(h, i, KQ_V(x), s); }
KQ_HW value kq_hw_put64(value h, value i, uint64_t x, value s) {
  s = kq_hw_put(h, i, (long) (x & 0xffffffffu), s); return kq_hw_put(h, KQ_V(KQ_N(i) + 1), (long) (x >> 32), s);
}
#define KQ_W64(lo, hi) (((uint64_t) (uint32_t) KQ_N(hi) << 32) | (uint32_t) KQ_N(lo))

// ---- loads and stores at an address
KQ_HW value kq_hw_load(value w, value a, value h, value i, value s) {
  KQ_BAR(); uint64_t x;
  switch (KQ_N(w)) { case 1: x = *(volatile uint8_t  *) KQ_A(a); break;
                     case 2: x = *(volatile uint16_t *) KQ_A(a); break;
                     case 4: x = *(volatile uint32_t *) KQ_A(a); break;
                     case 8: x = *(volatile uint64_t *) KQ_A(a); KQ_BAR(); return kq_hw_put64(h, i, x, s);
                     default: x = 0; }
  KQ_BAR(); return kq_hw_put(h, i, (long) x, s);
}
KQ_HW value kq_hw_store(value w, value a, value v, value s) {
  long n = KQ_N(w); if ((n != 1 && n != 2 && n != 4) || kq_hw_wide(KQ_A(a), (uintptr_t) n)) return s;
  KQ_BAR();
  switch (n) { case 1: *(volatile uint8_t  *) KQ_A(a) = (uint8_t)  KQ_N(v); break;
               case 2: *(volatile uint16_t *) KQ_A(a) = (uint16_t) KQ_N(v); break;
               default: *(volatile uint32_t *) KQ_A(a) = (uint32_t) KQ_N(v); }
  KQ_BAR(); return s;
}
KQ_HW value kq_hw_store64(value a, value lo, value hi, value s) {
  if (kq_hw_wide(KQ_A(a), 8)) return s;
  KQ_BAR(); *(volatile uint64_t *) KQ_A(a) = KQ_W64(lo, hi); KQ_BAR(); return s;
}
// ---- atomics (C11 builtins) and fences
#define KQ_RMW(T, op, p, x) ({ T kq_o_; switch (op) { \
    case 0: kq_o_ = __atomic_fetch_add((T *) (p), (T) (x), __ATOMIC_SEQ_CST); break; \
    case 1: kq_o_ = __atomic_fetch_sub((T *) (p), (T) (x), __ATOMIC_SEQ_CST); break; \
    case 2: kq_o_ = __atomic_fetch_and((T *) (p), (T) (x), __ATOMIC_SEQ_CST); break; \
    case 3: kq_o_ = __atomic_fetch_or ((T *) (p), (T) (x), __ATOMIC_SEQ_CST); break; \
    case 4: kq_o_ = __atomic_fetch_xor((T *) (p), (T) (x), __ATOMIC_SEQ_CST); break; \
    default: kq_o_ = __atomic_exchange_n((T *) (p), (T) (x), __ATOMIC_SEQ_CST); } kq_o_; })
KQ_HW value kq_hw_atomic(value op, value w, value a, value v, value h, value i, value s) {
  long n = KQ_N(w), o = KQ_N(op); uint64_t x = (uint64_t) KQ_N(v), old;
  if (kq_hw_wide(KQ_A(a), (uintptr_t) n)) return kq_hw_put(h, i, 0, s);
  switch (n) { case 1: old = KQ_RMW(uint8_t, o, KQ_A(a), x); break;
               case 2: old = KQ_RMW(uint16_t, o, KQ_A(a), x); break;
               case 4: old = KQ_RMW(uint32_t, o, KQ_A(a), x); break;
               default: old = 0; }
  return kq_hw_put(h, i, (long) old, s);
}
KQ_HW value kq_hw_atomic64(value op, value a, value lo, value hi, value h, value i, value s) {
  if (kq_hw_wide(KQ_A(a), 8)) return kq_hw_put64(h, i, 0, s);
  uint64_t old = KQ_RMW(uint64_t, KQ_N(op), KQ_A(a), KQ_W64(lo, hi));
  return kq_hw_put64(h, i, old, s);
}
KQ_HW value kq_hw_cas(value w, value a, value old, value nw, value h, value i, value s) {
  long n = KQ_N(w); int ok = 0; uint64_t e = 0;
  if (!kq_hw_wide(KQ_A(a), (uintptr_t) n)) switch (n) {
    case 1: { uint8_t  x = (uint8_t)  KQ_N(old); ok = __atomic_compare_exchange_n((uint8_t  *) KQ_A(a), &x, (uint8_t)  KQ_N(nw), 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST); e = x; break; }
    case 2: { uint16_t x = (uint16_t) KQ_N(old); ok = __atomic_compare_exchange_n((uint16_t *) KQ_A(a), &x, (uint16_t) KQ_N(nw), 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST); e = x; break; }
    case 4: { uint32_t x = (uint32_t) KQ_N(old); ok = __atomic_compare_exchange_n((uint32_t *) KQ_A(a), &x, (uint32_t) KQ_N(nw), 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST); e = x; break; } }
  s = kq_hw_put(h, i, (long) e, s); return kq_hw_put(h, KQ_V(KQ_N(i) + 1), ok, s);
}
KQ_HW value kq_hw_cas64(value a, value olo, value ohi, value nlo, value nhi, value h, value i, value s) {
  uint64_t e = KQ_W64(olo, ohi); int ok = 0;
  if (!kq_hw_wide(KQ_A(a), 8)) ok = __atomic_compare_exchange_n((uint64_t *) KQ_A(a), &e, KQ_W64(nlo, nhi), 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
  else e = 0;
  s = kq_hw_put64(h, i, e, s); return kq_hw_put(h, KQ_V(KQ_N(i) + 2), ok, s);
}
KQ_HW value kq_hw_aload(value w, value a, value h, value i, value s) {
  switch (KQ_N(w)) { case 1: return kq_hw_put(h, i, __atomic_load_n((uint8_t  *) KQ_A(a), __ATOMIC_ACQUIRE), s);
                     case 2: return kq_hw_put(h, i, __atomic_load_n((uint16_t *) KQ_A(a), __ATOMIC_ACQUIRE), s);
                     case 4: return kq_hw_put(h, i, __atomic_load_n((uint32_t *) KQ_A(a), __ATOMIC_ACQUIRE), s);
                     case 8: return kq_hw_put64(h, i, __atomic_load_n((uint64_t *) KQ_A(a), __ATOMIC_ACQUIRE), s);
                     default: return kq_hw_put(h, i, 0, s); }
}
KQ_HW value kq_hw_astore(value w, value a, value v, value s) {
  long n = KQ_N(w); if (kq_hw_wide(KQ_A(a), (uintptr_t) n)) return s;
  switch (n) { case 1: __atomic_store_n((uint8_t  *) KQ_A(a), (uint8_t)  KQ_N(v), __ATOMIC_RELEASE); break;
               case 2: __atomic_store_n((uint16_t *) KQ_A(a), (uint16_t) KQ_N(v), __ATOMIC_RELEASE); break;
               case 4: __atomic_store_n((uint32_t *) KQ_A(a), (uint32_t) KQ_N(v), __ATOMIC_RELEASE); break; }
  return s;
}
KQ_HW value kq_hw_astore64(value a, value lo, value hi, value s) {
  if (!kq_hw_wide(KQ_A(a), 8)) __atomic_store_n((uint64_t *) KQ_A(a), KQ_W64(lo, hi), __ATOMIC_RELEASE);
  return s;
}
KQ_HW value kq_hw_fence(value k, value s) {
  switch (KQ_N(k)) { case 1: __atomic_thread_fence(__ATOMIC_ACQUIRE); break;
                     case 2: __atomic_thread_fence(__ATOMIC_RELEASE); break;
                     default: __atomic_thread_fence(__ATOMIC_SEQ_CST); }
  return s;
}
// ---- bytes in bulk
KQ_HW value kq_hw_copy(value d, value src, value n, value s) {
  long k = KQ_N(n); if (k <= 0 || kq_hw_wide(KQ_A(d), (uintptr_t) k)) return s;
  KQ_BAR(); __builtin_memmove((void *) KQ_A(d), (const void *) KQ_A(src), (size_t) k); KQ_BAR(); return s;
}
KQ_HW value kq_hw_fill(value d, value b, value n, value s) {
  long k = KQ_N(n); if (k <= 0 || kq_hw_wide(KQ_A(d), (uintptr_t) k)) return s;
  KQ_BAR(); __builtin_memset((void *) KQ_A(d), (int) KQ_N(b), (size_t) k); KQ_BAR(); return s;
}
KQ_HW value kq_hw_cmp(value x, value y, value n, value h, value i, value s) {
  long k = KQ_N(n); int r = 0; KQ_BAR();
  if (k > 0) r = __builtin_memcmp((const void *) KQ_A(x), (const void *) KQ_A(y), (size_t) k);
  return kq_hw_put(h, i, r < 0 ? -1 : r > 0, s);
}
// ---- code at an address
KQ_HW value kq_hw_call(value a, value x, value h, value i, value s) {
  KQ_BAR(); uint64_t r = ((uint64_t (*)(uint64_t)) KQ_A(a))((uint64_t) KQ_N(x)); KQ_BAR();
  return kq_hw_put(h, i, (long) r, s);
}
// ---- machine code the program wrote itself: called as a C function of six words, two words back (the C calling
// convention of whatever processor this is compiled for -- the compiler's business, not ours)
typedef struct { uint64_t r0, r1; } kq_hw_two;
typedef kq_hw_two (*kq_hw_code)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
KQ_HW value kq_hw_run(value n, value a, value x0, value x1, value x2, value x3, value x4, value x5, value h, value i, value s) {
  KQ_BAR();
  kq_hw_two r = ((kq_hw_code) KQ_A(a))((uint64_t) KQ_N(x0), (uint64_t) KQ_N(x1), (uint64_t) KQ_N(x2),
                                       (uint64_t) KQ_N(x3), (uint64_t) KQ_N(x4), (uint64_t) KQ_N(x5));
  KQ_BAR();
  long k = KQ_N(n);
  if (k >= 1) s = kq_hw_put(h, i, (long) r.r0, s);
  if (k >= 2) s = kq_hw_put(h, KQ_V(KQ_N(i) + 1), (long) r.r1, s);
  return s;
}
// what the processor must be told before it runs bytes just written: the compiler's own builtin, which knows the target
// (x86: nothing at all; elsewhere it becomes the target's instruction-cache step)
KQ_HW value kq_hw_code_sync(value a, value n, value s) {
  long k = KQ_N(n); KQ_BAR();
  if (k > 0) __builtin___clear_cache((char *) KQ_A(a), (char *) KQ_A(a) + k);
  KQ_BAR(); return s;
}
// ---- operations of Rocq's machine numbers that no other instruction gives (PrimInt63: head0, tail0, the high half of mulc, diveucl_21)
KQ_HW value kq_hw_head0(value a) { return KQ_V((long) __builtin_clzll((kq_u) a)); }   /* a number's tag is the word's lowest bit, so the word is not 0, and its zeros on top are the number's */
KQ_HW value kq_hw_tail0(value a) { kq_u n = (kq_u) a >> 1; return KQ_V(n ? (long) __builtin_ctzll(n) : 63L); }
KQ_HW value kq_hw_mulhi(value a, value b) {
  kq_u x = (kq_u) a >> 1, y = (kq_u) b >> 1, x0 = x & 0xffffffffULL, x1 = x >> 32, y0 = y & 0xffffffffULL, y1 = y >> 32;
  kq_u p00 = x0 * y0, p01 = x0 * y1, p10 = x1 * y0, p11 = x1 * y1;
  kq_u mid = (p00 >> 32) + (p01 & 0xffffffffULL) + (p10 & 0xffffffffULL);
  kq_u hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32), lo = (mid << 32) | (p00 & 0xffffffffULL);
  return (value) (((hi << 1 | lo >> 63) << 1) | 1);
}
static inline void kq_div21(kq_u xh, kq_u xl, kq_u y, kq_u *q, kq_u *r) {
  /* as Rocq's own: (xh xl) / y on 63-bit digits, 0 and 0 when the quotient would not fit */
  if (y <= xh) { *q = 0; *r = 0; return; }
  kq_u qq = 0, rr = xh;
  for (int i = 62; i >= 0; i--) {
    rr = (rr << 1) | ((xl >> i) & 1);
    qq <<= 1;
    if (rr >= y) { rr -= y; qq |= 1; }
  }
  *q = qq & 0x7fffffffffffffffULL; *r = rr;
}
KQ_HW value kq_hw_div21q(value a, value b, value c) { kq_u q, r; kq_div21((kq_u) a >> 1, (kq_u) b >> 1, (kq_u) c >> 1, &q, &r); return (value) ((q << 1) | 1); }
KQ_HW value kq_hw_div21r(value a, value b, value c) { kq_u q, r; kq_div21((kq_u) a >> 1, (kq_u) b >> 1, (kq_u) c >> 1, &q, &r); return (value) ((r << 1) | 1); }
// ---- where a narrow block is
KQ_HW value kq_hw_addr(value h) { kq_u hh = (kq_u) h >> 1; return KQ_V(hh < KQ_MAXB ? (long) (uintptr_t) kq_n[hh].p : 0L); }
// ---- what the runtime gives (hw/Runtime.v; hw/kq_bare.c, hw/boot.S)
extern long kq_rt_irq_take(void);
KQ_HW value kq_hw_irq_take(value h, value i, value s) { KQ_BAR(); return kq_hw_put(h, i, kq_rt_irq_take(), s); }
extern volatile long kq_irq_cur[3];
KQ_HW value kq_hw_irq_info(value k) { long n = KQ_N(k); return KQ_V((n >= 0 && n < 3) ? kq_irq_cur[n] : -1L); }
extern uint64_t kq_hw_stubs[256];
KQ_HW value kq_hw_irq_entry(value v) { return KQ_V((long) kq_hw_stubs[(kq_u) KQ_N(v) & 255]); }
extern char kq_ap_tramp[], kq_ap_tramp_end[];
KQ_HW value kq_hw_cpu_code(value k) {
  switch (KQ_N(k)) { case 0: return KQ_V((long) (uintptr_t) kq_ap_tramp);
                     case 1: return KQ_V((long) (kq_ap_tramp_end - kq_ap_tramp));
                     default: return KQ_V(-1L); }
}
extern const uintptr_t kq_rt_sym[]; extern const long kq_rt_nsym;
KQ_HW value kq_hw_sym(value k) { long n = KQ_N(k); return KQ_V((n >= 0 && n < kq_rt_nsym) ? (long) kq_rt_sym[n] : -1L); }
#endif
