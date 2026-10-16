// kq_io3.c (for the fourth kq_io.h) -- the support code that is NOT per round: the memory's table and its loading, the slow path, the
// command line, the checksum, and `main` (time the run, print the result).  See kq_io.h for the rest.
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "gc_stack.h"
#include "kq_perf.h"
#define KQ_NO_PRIM_INLINE
#include "kq_io.h"
extern value body(struct thread_info *);
kq_block kq_b[KQ_MAXB];
unsigned int kq_len0[KQ_MAXB];   /* each block's size when the program started (kq_len) */
static long kq_nb;
kq_block32 kq_n[KQ_MAXB];       /* the narrow blocks (KQRun.v: rd32, upd32) */
static long kq_nn;
static int kq_argc; static char **kq_argv;
value kq_arg(value i) { long k = KQ_N(i); return KQ_V((k >= 0 && k + 1 < kq_argc) ? strtoll(kq_argv[k + 1], 0, 10) : 0); }
value kq_input(value x) { return 1; }
// THE MEMORY, loaded from the file named by $KQ_MEM:  <number of blocks>, then per block <length> <cell> <cell> ..
// (or <length> z for a block of zeros)
// The model's edge rules (KQSpec.v): a negative block or cell number is outside; a read outside gives 0; a write outside does nothing.
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
static long kq_checksum(void) {
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
// `main` of a program whose answer is a memory ends with `kq_sum`: one number that depends on every cell.  That pass
// over the whole memory is the HARNESS's, not the program's (the C++ reference does nothing like it), so its time is
// taken out of the reported time and the counters are stopped for it.
static double kq_sum_ms;
value kq_sum(value s) {
  struct timespec a, b; kq_perf_pause(); clock_gettime(CLOCK_MONOTONIC, &a);
  long c = kq_checksum();
  clock_gettime(CLOCK_MONOTONIC, &b); kq_sum_ms += (b.tv_sec - a.tv_sec) * 1e3 + (b.tv_nsec - a.tv_nsec) / 1e6; kq_perf_resume();
  return KQ_V(c);
}
// GROWING A BLOCK (KQRun.v kq_grow): block h holds at least n cells; the cells it had keep their numbers, the new ones
// hold 0.  For h 0 .. 63 and n below 2^31, nothing otherwise.  The block may move (realloc).  If the machine has no more
// memory, the program stops (exit 3): the laws cannot hold then, and nothing is computed past that point.
value kq_grow(value h, value n, value s) {
  kq_u hh = (kq_u) h >> 1; long nn = KQ_N(n);
  if (hh >= KQ_MAXB || nn < 0 || nn >= (1L << 31)) return s;
  if ((long) hh >= kq_nb) kq_nb = (long) hh + 1;
  kq_block *b = &kq_b[hh];
  if ((unsigned long) nn <= b->len) return s;
  value *p = realloc(b->p, (nn + 1) * sizeof(value));
  if (!p) { fprintf(stderr, "kq_grow: no memory for %ld cells in block %lu\n", nn, hh); exit(3); }
  for (long i = (long) b->len; i <= nn; i++) p[i] = KQ_V(0);
  b->p = p; b->len = (unsigned int) nn; b->lim = 2 * (unsigned int) nn;
  return s;
}
// INPUT AND OUTPUT.  The input is the file named by $KQ_IN (numbers separated by anything), read whole at the first
// kq_in; the output is collected and written to the file named by $KQ_OUT when the program ends (or to the standard
// output, after the line with the result).
static char *kq_inbuf; static long kq_inlen, kq_inpos; static int kq_inopen;
static char *kq_outbuf; static long kq_outlen, kq_outcap;
value kq_in(value h, value i, value s) {
  if (!kq_inopen) {
    kq_inopen = 1; const char *p = getenv("KQ_IN"); FILE *f = p ? fopen(p, "rb") : stdin;
    if (f) { long cap = 1 << 20; kq_inbuf = malloc(cap); size_t k;
      while ((k = fread(kq_inbuf + kq_inlen, 1, cap - kq_inlen, f)) > 0) { kq_inlen += k; if (kq_inlen == cap) { cap *= 2; kq_inbuf = realloc(kq_inbuf, cap); } }
      if (p) fclose(f); }
  }
  while (kq_inpos < kq_inlen && kq_inbuf[kq_inpos] != '-' && (kq_inbuf[kq_inpos] < '0' || kq_inbuf[kq_inpos] > '9')) kq_inpos++;
  long v = -1;
  if (kq_inpos < kq_inlen) {
    int neg = 0; if (kq_inbuf[kq_inpos] == '-') { neg = 1; kq_inpos++; }
    v = 0; while (kq_inpos < kq_inlen && kq_inbuf[kq_inpos] >= '0' && kq_inbuf[kq_inpos] <= '9') v = v * 10 + (kq_inbuf[kq_inpos++] - '0');
    if (neg) v = -v;
  }
  return kq_updb(h, i, KQ_V(v), s);
}
value kq_out(value v, value s) {
  if (kq_outlen + 24 > kq_outcap) { kq_outcap = kq_outcap ? 2 * kq_outcap : 1 << 16; kq_outbuf = realloc(kq_outbuf, kq_outcap); }
  kq_outlen += sprintf(kq_outbuf + kq_outlen, "%ld\n", KQ_N(v));
  return s;
}
// the build that measures (kq_io.h: kq_prof)
unsigned long kq_prof_n[KQ_PROF_MAX], kq_prof_t[KQ_PROF_MAX], kq_prof_w[KQ_PROF_MAX];
unsigned int kq_prof_h[KQ_PROF_MAX]; unsigned char *kq_prof_tab[KQ_PROF_MAX];
unsigned char *kq_prof_new(kq_u k) { unsigned char *t = malloc(4096); for (int i = 0; i < 4096; i++) t[i] = 1; kq_prof_tab[k] = t; return t; }
// the nat n as the compiler's default builds it (n cells), in one piece of C memory -- for programs compiled WITHOUT
// KQNat.v
value kq_nat(value n) {
  long k = KQ_N(n); if (k <= 0) return 1;
  value *a = malloc(2 * k * sizeof(value)); value prev = 1;
  for (long i = 0; i < k; i++) { a[2 * i] = 1024; a[2 * i + 1] = prev; prev = (value) &a[2 * i + 1]; }
  return prev;
}
int main(int argc, char **argv) {
  kq_argc = argc; kq_argv = argv;
  const char *path = getenv("KQ_MEM"); FILE *f = path ? fopen(path, "r") : 0;
  if (f) {
    if (fscanf(f, "%ld", &kq_nb) != 1 || kq_nb > KQ_MAXB) return 2;
    for (long h = 0; h < kq_nb; h++) {
      long len; if (fscanf(f, "%ld", &len) != 1) return 2;
      if (len < 0 || len >= (1L << 31)) return 2;
      kq_b[h].len = (unsigned int) len; kq_b[h].lim = 2 * (unsigned int) len; kq_b[h].p = malloc((len + 1) * sizeof(value));
      kq_len0[h] = (unsigned int) len;
      if (!kq_b[h].p) return 2;
      int c; do c = fgetc(f); while (c == ' ' || c == '\n' || c == '\t' || c == '\r');
      if (c == 'z') { for (long i = 0; i < len; i++) kq_b[h].p[i] = KQ_V(0); continue; }
      if (c != EOF) ungetc(c, f);
      for (long i = 0; i < len; i++) { long v; if (fscanf(f, "%ld", &v) != 1) return 2; kq_b[h].p[i] = KQ_V(v); }
    }
    /* then, if the file goes on with `n32 <number of blocks>`, the narrow blocks, written the same way */
    char tag[8];
    if (fscanf(f, "%7s", tag) == 1 && tag[0] == 'n' && tag[1] == '3' && tag[2] == '2' && tag[3] == 0) {
      if (fscanf(f, "%ld", &kq_nn) != 1 || kq_nn < 0 || kq_nn > KQ_MAXB) return 2;
      for (long h = 0; h < kq_nn; h++) {
        long len; if (fscanf(f, "%ld", &len) != 1) return 2;
        if (len < 0 || len >= (1L << 31)) return 2;
        kq_n[h].len = (unsigned int) len; kq_n[h].lim = 2 * (unsigned int) len; kq_n[h].p = malloc((len + 1) * sizeof(int));
        if (!kq_n[h].p) return 2;
        int c; do c = fgetc(f); while (c == ' ' || c == '\n' || c == '\t' || c == '\r');
        if (c == 'z') { for (long i = 0; i < len; i++) kq_n[h].p[i] = 0; continue; }
        if (c != EOF) ungetc(c, f);
        for (long i = 0; i < len; i++) { long v; if (fscanf(f, "%ld", &v) != 1) return 2; kq_n[h].p[i] = (int) v; }
      }
    }
    fclose(f);
  }
  struct timespec t0, t1;
  struct thread_info *tinfo = make_tinfo();
  kq_perf_start();
  clock_gettime(CLOCK_MONOTONIC, &t0);
  value val = body(tinfo);
  clock_gettime(CLOCK_MONOTONIC, &t1);
  kq_perf_stop();
  printf("result %ld checksum %ld harness_ms %.3f ms %.3f\n", KQ_N(val), kq_checksum(), kq_sum_ms,
         (t1.tv_sec - t0.tv_sec) * 1e3 + (t1.tv_nsec - t0.tv_nsec) / 1e6 - kq_sum_ms);
  if (kq_outlen) { const char *p = getenv("KQ_OUT"); FILE *f = p ? fopen(p, "wb") : stdout; if (f) { fwrite(kq_outbuf, 1, kq_outlen, f); if (p) fclose(f); } }
  /* a build that measures: per numbered test that was met -- its number, times met, times true, times guessed wrong */
  for (long k = 0; k < KQ_PROF_MAX; k++) if (kq_prof_n[k]) printf("prof %ld %lu %lu %lu\n", k, kq_prof_n[k], kq_prof_t[k], kq_prof_w[k]);
  /* $KQ_DUMP = "h start n": print cells start .. start+n-1 of block h, one per line ("h n": from cell 0;
     n = -1: as many cells as the program's result says); "n<h> start n": the same of narrow block h */
  const char *dump = getenv("KQ_DUMP");
  if (dump && dump[0] == 'n') {
    long h, a, n, k = sscanf(dump + 1, "%ld %ld %ld", &h, &a, &n);
    if (k == 2) { n = a; a = 0; }
    if (k >= 2 && h >= 0 && h < kq_nn) {
      if (n < 0) n = KQ_N(val);
      for (long i = a; i < a + n && i < (long) kq_n[h].len; i++) printf("%ld\n", (long) kq_n[h].p[i]);
    }
    dump = 0;
  }
  if (dump) {
    long h, a, n, k = sscanf(dump, "%ld %ld %ld", &h, &a, &n);
    if (k == 2) { n = a; a = 0; }
    if (k >= 2 && h >= 0 && h < kq_nb) {
      if (n < 0) n = KQ_N(val);
      for (long i = a; i < a + n && i < (long) kq_b[h].len; i++) printf("%ld\n", KQ_N(kq_b[h].p[i]));
    }
  }
  return 0;
}
