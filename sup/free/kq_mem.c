/* sup/free/kq_mem.c -- the memory's tables, with no hosted header and no libc: what kq_io.h asks of the support code.  It knows no
   operating system and no instruction set.  Whoever starts the program fills the tables (kq_b, kq_n, kq_nb, kq_nn), says where free
   memory is (kq_arena, kq_arena_len) and calls the entry.  Not proved: Rocq-C-solution.md §12.H. */
#include <stddef.h>
#include <stdint.h>
#include "gc_stack.h"
#define KQ_NO_PRIM_INLINE
#include "kq_io.h"
kq_block kq_b[KQ_MAXB];
kq_block32 kq_n[KQ_MAXB];
unsigned int kq_len0[KQ_MAXB];
long kq_nb, kq_nn;
char *kq_arena;
unsigned long kq_arena_len;
extern void kq_stop(long code) __attribute__((noreturn));

void *kq_alloc(unsigned long n) {
  n = (n + 15) & ~15UL;
  if (n > kq_arena_len) kq_stop(3);          /* no more memory: the laws cannot hold, and nothing is computed past this */
  void *p = kq_arena; kq_arena += n; kq_arena_len -= n;
  return p;
}
__attribute__((noinline)) KQ_SLOW_ATTR value *kq_cell_slow(value h, value i) {
  long hh = KQ_N(h), ii = KQ_N(i); if (hh < 0 || ii < 0) return 0;
  if (hh >= kq_nb || hh >= KQ_MAXB || (unsigned long) ii >= kq_b[hh].len) return 0;
  return kq_b[hh].p + ii;
}
__attribute__((noinline)) KQ_SLOW_ATTR int *kq_cell32_slow(value h, value i) {
  long hh = KQ_N(h), ii = KQ_N(i); if (hh < 0 || ii < 0) return 0;
  if (hh >= kq_nn || hh >= KQ_MAXB || (unsigned long) ii >= kq_n[hh].len) return 0;
  return kq_n[hh].p + ii;
}
/* KQRun.v kq_grow: block h holds at least n cells; the cells it had keep their numbers, the new ones hold 0.  The block moves unless
   it is the last one taken from the free memory; what it leaves is not used again. */
value kq_grow(value h, value n, value s) {
  kq_u hh = (kq_u) h >> 1; long nn = KQ_N(n);
  if (hh >= KQ_MAXB || nn < 0 || nn >= (1L << 31)) return s;
  if ((long) hh >= kq_nb) kq_nb = (long) hh + 1;
  kq_block *b = &kq_b[hh];
  if ((unsigned long) nn <= b->len) return s;
  value *p = (value *) kq_alloc(((unsigned long) nn + 1) * sizeof(value));
  for (long i = 0; i < (long) b->len; i++) p[i] = b->p[i];
  for (long i = (long) b->len; i <= nn; i++) p[i] = KQ_V(0);
  b->p = p; b->len = (unsigned int) nn; b->lim = 2 * (unsigned int) nn;
  return s;
}
long kq_checksum(void) {
  const long P = 1000000007L; long acc = 0;
  for (long h = 0; h < kq_nb; h++) for (long i = 0; i < (long) kq_b[h].len; i++) {
    long v = KQ_N(kq_b[h].p[i]) % P; if (v < 0) v += P;
    acc = (acc + (((h + 1) * (i + 1)) % P) * v) % P;
  }
  for (long h = 0; h < kq_nn; h++) for (long i = 0; i < (long) kq_n[h].len; i++) {
    long v = (long) kq_n[h].p[i] % P; if (v < 0) v += P;
    acc = (acc + (((h + 1001) * (i + 1)) % P) * v) % P;
  }
  return acc;
}
value kq_sum(value s) { return KQ_V(kq_checksum()); }
value kq_input(value x) { return 1; }
value kq_nat(value n) { return n; }
/* what clang may call by itself */
void *memcpy(void *d, const void *s, size_t n) { char *a = d; const char *b = s; while (n--) *a++ = *b++; return d; }
void *memmove(void *d, const void *s, size_t n) { char *a = d; const char *b = s; if (a < b) while (n--) *a++ = *b++; else { a += n; b += n; while (n--) *--a = *--b; } return d; }
void *memset(void *d, int c, size_t n) { char *a = d; while (n--) *a++ = (char) c; return d; }
int memcmp(const void *x, const void *y, size_t n) { const unsigned char *a = x, *b = y; for (; n--; a++, b++) if (*a != *b) return *a < *b ? -1 : 1; return 0; }
