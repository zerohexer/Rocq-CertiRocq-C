// test_arith.c -- the machine-integer operations of the support code against a plain reference, on many numbers
// including negative ones and the edges of 63 bits.  (Z's division and remainder are Rocq definitions now, compiled
// from their text; they are tested against Z inside Rocq, tests/TestDiv.v.)
#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"
#include "kq_io.h"
static long wrap63(__int128 v) { unsigned long u = (unsigned long) v; return ((long) (u << 1)) >> 1; }   /* as a 63-bit number */
static long bad = 0, total = 0;
static void chk(const char *what, long x, long y, long got, long want) {
  total++; if (got != want) { if (bad++ < 12) printf("WRONG %s(%ld, %ld): got %ld, want %ld\n", what, x, y, got, want); }
}
int main(void) {
  static long xs[4096]; int nx = 0;
  long edge[] = {0, 1, -1, 2, -2, 3, -3, 7, -7, 8, -8, 1000000006L, 1000000007L, 1000000008L, -1000000007L, -1000000008L,
                 (1L << 62) - 1, -(1L << 62), (1L << 62) - 2, -(1L << 62) + 1, (1L << 61), -(1L << 61), 4611686018427387903L};
  for (unsigned k = 0; k < sizeof edge / sizeof *edge; k++) xs[nx++] = edge[k];
  srand(12345);
  while (nx < 4096) { long v = ((long) rand() << 32) ^ ((long) rand() << 11) ^ rand(); v = (v << 1) >> 1; if (rand() % 3 == 0) v >>= (rand() % 60); xs[nx++] = v; }
  volatile long ys[] = {0, 1, -1, 2, -2, 3, -3, 7, -7, 10, -10, 1000000007L, -1000000007L, (1L << 62) - 1, -(1L << 62), 123456789012L, -98765432101L};
  for (unsigned j = 0; j < sizeof ys / sizeof *ys; j++) for (int i = 0; i < nx; i++) {
    long x = xs[i], y = ys[j];
    { /* the machine's four divisions: unsigned on the 63-bit patterns, signed rounding toward 0; by 0: 0 and the number */
      unsigned long ux = (unsigned long) x & 0x7fffffffffffffffUL, uy = (unsigned long) y & 0x7fffffffffffffffUL;
      chk("div (unsigned)", x, y, KQ_N(kq_p_div(KQ_V(x), KQ_V(y))), wrap63((__int128) (uy == 0 ? 0 : ux / uy)));
      chk("mod (unsigned)", x, y, KQ_N(kq_p_mod(KQ_V(x), KQ_V(y))), wrap63((__int128) (uy == 0 ? ux : ux % uy)));
      chk("div (signed)", x, y, KQ_N(kq_p_divs(KQ_V(x), KQ_V(y))), y == 0 ? 0 : wrap63((__int128) x / y));
      chk("mod (signed)", x, y, KQ_N(kq_p_mods(KQ_V(x), KQ_V(y))), y == 0 ? x : (long) ((__int128) x % y)); }
    chk("mul", x, y, KQ_N(kq_p_mul(KQ_V(x), KQ_V(y))), wrap63((__int128) x * y));
    chk("add", x, y, KQ_N(kq_p_add(KQ_V(x), KQ_V(y))), wrap63((__int128) x + y));
    chk("sub", x, y, KQ_N(kq_p_sub(KQ_V(x), KQ_V(y))), wrap63((__int128) x - y));
    chk("lt (signed)", x, y, kq_p_ltsb(KQ_V(x), KQ_V(y)) == KQ_TRUE, x < y);
    chk("le (signed)", x, y, kq_p_lesb(KQ_V(x), KQ_V(y)) == KQ_TRUE, x <= y);
    chk("eq", x, y, kq_p_eqb(KQ_V(x), KQ_V(y)) == KQ_TRUE, x == y);
    chk("and", x, y, KQ_N(kq_p_land(KQ_V(x), KQ_V(y))), x & y);
    chk("or", x, y, KQ_N(kq_p_lor(KQ_V(x), KQ_V(y))), x | y);
    chk("xor", x, y, KQ_N(kq_p_lxor(KQ_V(x), KQ_V(y))), x ^ y);
  }
  for (int i = 0; i < nx; i++) for (long n = 0; n < 63; n += 1 + (n > 8) * 6) {
    long x = xs[i];
    chk("shift right (keeps the sign)", x, n, KQ_N(kq_p_asr(KQ_V(x), KQ_V(n))), x >> n);
    chk("shift left", x, n, KQ_N(kq_p_lsl(KQ_V(x), KQ_V(n))), wrap63((__int128) x << n));
    chk("mul by the written 20", x, 20, KQ_N(kq_p_mul(KQ_V(x), KQ_V(20L))), wrap63((__int128) x * 20));
    chk("mul, written 20 first", 20, x, KQ_N(kq_p_mul(KQ_V(20L), KQ_V(x))), wrap63((__int128) x * 20));
  }
  printf("arithmetic: %ld checks, %ld wrong\n", total, bad);
  return bad != 0;
}
