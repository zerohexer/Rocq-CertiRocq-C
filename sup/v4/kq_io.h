// kq_io.h (fourth version) -- what the generated C sees of the support code.  Everything a loop does per round is
// HERE, as inline C, so that the C compiler sees it next to the generated code: the memory and the machine-integer
// operations.  These are the things Rocq only declares (the memory) or has built in (the integers).  ONE function here
// stands in for a Rocq definition: kq_nat_int, "a number as a loop budget" (the number itself: a nat is one machine
// number, KQNat.v).  Z's division and remainder are compiled from their Rocq text (KQRun.v).
#ifndef KQ_IO_H
#define KQ_IO_H
#include "values.h"
#define KQ_INL static inline __attribute__((always_inline))
typedef unsigned long kq_u;                       /* the machine word, unsigned */
#define KQ_V(n) ((value) ((((kq_u) (n)) << 1) | 1))
#define KQ_N(v) (((long) (v)) >> 1)

// ---------------------------------------------------------------- THE MEMORY
// Numbered blocks of cells.  A Rocq machine integer n reaches C as the word x = 2n+1 ("tagged").  Two things are done
// with a cell number, and both are done on the tagged word as it is, without first turning it back into n:
//     is it inside?        n < len          <=>   x < 2*len          (x is odd; a negative n is a huge unsigned x)
//     where is the cell?   p + 8*n           =    p + 4*x - 4        (one addressing mode of the machine)
// `lim` holds 2*len.  `p` is a pointer and `len`, `lim` are unsigned ints on purpose: a store into a cell (a long) can
// be none of them, so the C compiler may keep a block's address and limit in registers across a loop.
#define KQ_MAXB 64
typedef struct { value *p; unsigned int len; unsigned int lim; } kq_block;      /* len < 2^31 */
extern kq_block kq_b[KQ_MAXB];
// the slow path: where the cell of (h, i) is under the model's edge rules (a negative number is outside, as a number
// past the end), or 0 when there is none.  It only LOOKS, and says so.
#ifndef KQ_SLOW_ATTR
#define KQ_SLOW_ATTR
#endif
extern value *kq_cell_slow(value h, value i) __attribute__((pure, cold)) KQ_SLOW_ATTR;
// The slow path's own load and store are marked `volatile` for ONE reason: the C compiler then leaves them where they
// are.  Unmarked, it merges them with the fast path's ("both arms end with a load through a pointer"), and the fast
// path -- every access of every loop -- must then first put its address into a register that the slow path can share:
// two more instructions per access, and up to a fifth of the time of a tight loop (2026-10-14).
#ifdef KQ_UNCHECKED
// no bounds tests at all: ONLY right for a program whose every access is inside its block
#define KQ_IN(x, b) 1
#else
#define KQ_IN(x, b) __builtin_expect((kq_u) (x) < (kq_u) (b)->lim, 1)
#endif
#ifdef KQ_PLAINIDX      /* the third version's way: untag, then index */
#define KQ_CELL(b, x) ((b)->p + ((kq_u) (x) >> 1))
#else
#define KQ_CELL(b, x) ((value *) ((char *) (b)->p + (4 * (kq_u) (x) - 4)))
#endif
KQ_INL value kq_rdb(value h, value i, value s) {
  kq_u kq_hh = (kq_u) h >> 1;
  if (__builtin_expect(kq_hh < KQ_MAXB, 1)) {
    const kq_block *kq_bk = &kq_b[kq_hh];
    if (KQ_IN(i, kq_bk)) return *(const value *) KQ_CELL(kq_bk, i);
  }
  { value *c = kq_cell_slow(h, i); return c ? *(const volatile value *) c : KQ_V(0); }
}
KQ_INL value kq_updb(value h, value i, value v, value s) {
  kq_u kq_hh = (kq_u) h >> 1;
  if (__builtin_expect(kq_hh < KQ_MAXB, 1)) {
    const kq_block *kq_bk = &kq_b[kq_hh];
    if (KQ_IN(i, kq_bk)) { *KQ_CELL(kq_bk, i) = v; return s; }
  }
  { value *c = kq_cell_slow(h, i); if (c) *(volatile value *) c = v; return s; }
}
// NARROW BLOCKS (KQRun.v: rd32, upd32): cells of 4 bytes, a family of blocks of its own.  The same test as above on
// the marked number x = 2i+1, then the cell at p + 2x - 2 (= p + 4i).  A number is kept modulo 2^32 (C's conversion
// to int) and read back signed: the model's rule.
typedef struct { int *p; unsigned int len; unsigned int lim; } kq_block32;
extern kq_block32 kq_n[KQ_MAXB];
extern int *kq_cell32_slow(value h, value i) __attribute__((pure, cold)) KQ_SLOW_ATTR;
#define KQ_CELL32(b, x) ((int *) ((char *) (b)->p + (2 * (kq_u) (x) - 2)))
KQ_INL value kq_rd32(value h, value i, value s) {
  kq_u kq_hh = (kq_u) h >> 1;
  if (__builtin_expect(kq_hh < KQ_MAXB, 1)) {
    const kq_block32 *kq_bk = &kq_n[kq_hh];
    if (KQ_IN(i, kq_bk)) return KQ_V((long) *(const int *) KQ_CELL32(kq_bk, i));
  }
  { int *c = kq_cell32_slow(h, i); return c ? KQ_V((long) *(const volatile int *) c) : KQ_V(0); }
}
KQ_INL value kq_upd32(value h, value i, value v, value s) {
  kq_u kq_hh = (kq_u) h >> 1;
  if (__builtin_expect(kq_hh < KQ_MAXB, 1)) {
    const kq_block32 *kq_bk = &kq_n[kq_hh];
    if (KQ_IN(i, kq_bk)) { *KQ_CELL32(kq_bk, i) = (int) KQ_N(v); return s; }
  }
  { int *c = kq_cell32_slow(h, i); if (c) *(volatile int *) c = (int) KQ_N(v); return s; }
}
extern value kq_arg(value i);
// input and output (KQRun.v): the next number of the input into a cell; a number to the output.  Both give back the
// memory they were given: there is one memory, and the outside world is part of it.
extern value kq_in(value h, value i, value s);
extern value kq_out(value v, value s);
extern value kq_input(value x);
extern value kq_sum(value s);
extern value kq_nat(value n);
// a loop budget when the compiler keeps a nat as a machine number (KQNat.v): the number itself
KQ_INL value kq_nat_int(value n) { return KQ_N(n) <= 0 ? KQ_V(0) : n; }
// ---------------------------------------------------------------- THE MACHINE INTEGERS
// These work on the tagged words directly (2a+1 + 2b+1 - 1 = 2(a+b)+1), and three are CORRECTED with respect to the
// runtime's prim_int63.c: it computes the signed remainder and the arithmetic right shift on the unsigned value, and
// the unsigned comparisons as signed ones.
// The generated C names the runtime's functions; from here on those names mean the inline ones below.
#define KQ_TRUE ((value) 3)
#define KQ_FALSE ((value) 1)
// READS AND WRITES WITHOUT THE TEST (KQBound.v: rd_u, upd_u, rd32_u, upd32_u).  The translator writes them only where
// a proof shows the cell is inside its block; and the one test made at the start of such a loop: kq_fits L e n is
// "e + n <= L" (unsigned, so a negative e fails), L being kq_len h or kq_len32 h.
KQ_INL value kq_rd_u(value h, value i, value s) { return *(const value *) KQ_CELL(&kq_b[(kq_u) h >> 1], i); }
KQ_INL value kq_upd_u(value h, value i, value v, value s) { *KQ_CELL(&kq_b[(kq_u) h >> 1], i) = v; return s; }
KQ_INL value kq_rd32_u(value h, value i, value s) { return KQ_V((long) *(const int *) KQ_CELL32(&kq_n[(kq_u) h >> 1], i)); }
KQ_INL value kq_upd32_u(value h, value i, value v, value s) { *KQ_CELL32(&kq_n[(kq_u) h >> 1], i) = (int) KQ_N(v); return s; }
// kq_len h: block h's size when the program started (KQBound.v); a block that grew has more (kq_size below)
extern unsigned int kq_len0[KQ_MAXB];
KQ_INL value kq_len(value h) { kq_u hh = (kq_u) h >> 1; return KQ_V(hh < KQ_MAXB ? (long) kq_len0[hh] : 0L); }
KQ_INL value kq_len32(value h) { kq_u hh = (kq_u) h >> 1; return KQ_V(hh < KQ_MAXB ? (long) kq_n[hh].len : 0L); }
// GROWING A BLOCK (KQRun.v: kq_grow, kq_size).  kq_grow may move the block: called, it may change kq_b, and inlined its
// stores are in sight, so either way the C compiler reads the block's address and limit again after it.
KQ_INL value kq_size(value h, value s) { kq_u hh = (kq_u) h >> 1; return KQ_V(hh < KQ_MAXB ? (long) kq_b[hh].len : 0L); }
extern value kq_grow(value h, value n, value s);
KQ_INL value kq_fits(value L, value e, value n) {
  kq_u l = (kq_u) KQ_N(L), x = (kq_u) KQ_N(e), m = (kq_u) KQ_N(n);
  return (x <= l && m <= l - x) ? KQ_TRUE : KQ_FALSE;
}
// ---------------------------------------------------------------- A CHOICE THAT IS NEVER A JUMP (KQRun.v: kq_select, kq_sel_*)
// A C compiler asked for `c ? a : b` answers with a conditional move or with a jump, as it guesses best, and its guess
// changes with the size of a and b.  On a test that goes either way the jump costs several times the move (measured:
// a search of 1024 cells, 925 ms against 170 ms).  So these are not left to the compiler:
//   on x86-64   the machine's own conditional move, written out -- with the comparison, in the kq_sel_* forms: two
//               instructions in all, the same code the compiler makes when it chooses well;
//   elsewhere, or with KQ_SELECT_MASK   three logical operations on a mask the compiler is not allowed to look into.
// KQ_SELECT_PLAIN gives the plain `c ? a : b` back (to measure what a compiler does with it).
// kq_select takes a test that was worked out before (a combination of comparisons); it is handed over as 0 or 1, so
// that the C compiler stays free in how it works the combination out.  The `n` / ne / ge / gt forms are the same
// choices on the test turned round.
#if defined(KQ_SELECT_PLAIN)
#define KQ_SELDEF(name, T, cond, cc) KQ_INL value name(value x, value y, value a, value b) { return ((T) x cond (T) y) ? a : b; }
KQ_INL value kq_select(value c, value a, value b)  { return c == KQ_TRUE ? a : b; }
KQ_INL value kq_selectn(value c, value a, value b) { return c == KQ_TRUE ? b : a; }
#elif defined(__x86_64__) && !defined(KQ_SELECT_MASK)
#define KQ_SELDEF(name, T, cond, cc) KQ_INL value name(value x, value y, value a, value b) { \
  __asm__("cmp %[y], %[x]\n\tcmov" cc " %[a], %[b]" : [b] "+r" (b) : [x] "r" (x), [y] "re" (y), [a] "r" (a) : "cc"); return b; }
KQ_INL value kq_select(value c, value a, value b) {
  kq_u t = (c == KQ_TRUE); __asm__("test %[t], %[t]\n\tcmovne %[a], %[b]" : [b] "+r" (b) : [t] "r" (t), [a] "r" (a) : "cc"); return b; }
KQ_INL value kq_selectn(value c, value a, value b) {
  kq_u t = (c == KQ_TRUE); __asm__("test %[t], %[t]\n\tcmove %[a], %[b]" : [b] "+r" (b) : [t] "r" (t), [a] "r" (a) : "cc"); return b; }
#else
KQ_INL value kq_mask_pick(kq_u m, value a, value b) { __asm__("" : "+r" (m)); return (value) ((kq_u) b ^ (((kq_u) a ^ (kq_u) b) & m)); }
#define KQ_SELDEF(name, T, cond, cc) KQ_INL value name(value x, value y, value a, value b) { return kq_mask_pick((kq_u) 0 - (kq_u) ((T) x cond (T) y), a, b); }
KQ_INL value kq_select(value c, value a, value b)  { return kq_mask_pick((kq_u) 0 - (kq_u) (c == KQ_TRUE), a, b); }
KQ_INL value kq_selectn(value c, value a, value b) { return kq_mask_pick((kq_u) 0 - (kq_u) (c != KQ_TRUE), a, b); }
#endif
KQ_SELDEF(kq_sel_lts, long, <,  "l")
KQ_SELDEF(kq_sel_les, long, <=, "le")
KQ_SELDEF(kq_sel_ges, long, >=, "ge")
KQ_SELDEF(kq_sel_gts, long, >,  "g")
KQ_SELDEF(kq_sel_eq,  kq_u, ==, "e")
KQ_SELDEF(kq_sel_ne,  kq_u, !=, "ne")
KQ_SELDEF(kq_sel_ltu, kq_u, <,  "b")
KQ_SELDEF(kq_sel_leu, kq_u, <=, "be")
KQ_SELDEF(kq_sel_geu, kq_u, >=, "ae")
KQ_SELDEF(kq_sel_gtu, kq_u, >,  "a")
// ---------------------------------------------------------------- THE BUILD THAT MEASURES (KQRun.v: kq_prof)
// Test number k counts: how often it was met, how often it was true, and how often a machine would have guessed it
// WRONG.  The machine is modelled as real ones are built: per test, a table of two-bit counters, one for each pattern
// of that test's last twelve outcomes.  A test that is nearly always the same way, or that repeats a pattern, is
// guessed right; a test on a bit of the data is guessed wrong about half the time.  `main` prints the counts.
#define KQ_PROF_MAX 1024
extern unsigned long kq_prof_n[KQ_PROF_MAX], kq_prof_t[KQ_PROF_MAX], kq_prof_w[KQ_PROF_MAX];
extern unsigned int kq_prof_h[KQ_PROF_MAX]; extern unsigned char *kq_prof_tab[KQ_PROF_MAX];
extern unsigned char *kq_prof_new(kq_u k);
KQ_INL value kq_prof(value id, value c) {
  kq_u k = (kq_u) id >> 1; if (k >= KQ_PROF_MAX) return c;
  unsigned char *t = kq_prof_tab[k]; if (__builtin_expect(!t, 0)) t = kq_prof_new(k);
  unsigned int h = kq_prof_h[k] & 4095, taken = (c == KQ_TRUE); unsigned char ctr = t[h];
  kq_prof_n[k]++; kq_prof_t[k] += taken; kq_prof_w[k] += ((unsigned int) (ctr >= 2) != taken);
  t[h] = (unsigned char) (taken ? (ctr < 3 ? ctr + 1 : 3) : (ctr > 0 ? ctr - 1 : 0));
  kq_prof_h[k] = (h << 1) | taken;
  return c;
}
KQ_INL value kq_p_add(value x, value y)  { return (value) ((kq_u) x + (kq_u) y - 1); }
KQ_INL value kq_p_sub(value x, value y)  { return (value) ((kq_u) x - (kq_u) y + 1); }
// (2a+1, 2b+1) -> 2ab+1, two ways; the one that leaves a single instruction when a factor is written in the program.
// The tag is taken off with a mask and put back with an "or" (not -1 / +1): the C compiler then KNOWS the product is
// even before the tag goes on, and drops the tag again for nothing when the next operation takes it off.
KQ_INL value kq_p_mul(value x, value y)  { return __builtin_constant_p(y) ? (value) ((((kq_u) x & ~1UL) * ((kq_u) y >> 1)) | 1)
                                                                          : (value) ((((kq_u) x >> 1) * ((kq_u) y & ~1UL)) | 1); }
KQ_INL value kq_p_land(value x, value y) { return x & y; }
KQ_INL value kq_p_lor(value x, value y)  { return x | y; }
KQ_INL value kq_p_lxor(value x, value y) { return (x ^ y) | 1; }
KQ_INL value kq_p_lsl(value x, value y)  { kq_u n = (kq_u) y >> 1; return n < 63 ? (value) ((((kq_u) x - 1) << n) | 1) : KQ_V(0); }
KQ_INL value kq_p_lsr(value x, value y)  { kq_u n = (kq_u) y >> 1; return n < 63 ? (value) (((kq_u) x >> n) | 1) : KQ_V(0); }
KQ_INL value kq_p_asr(value x, value y)  { kq_u n = (kq_u) y >> 1; return n < 63 ? (value) (((long) x >> n) | 1) : (x < 0 ? KQ_V(-1L) : KQ_V(0)); }
KQ_INL value kq_p_eqb(value x, value y)  { return x == y ? KQ_TRUE : KQ_FALSE; }
KQ_INL value kq_p_ltb(value x, value y)  { return (kq_u) x <  (kq_u) y ? KQ_TRUE : KQ_FALSE; }
KQ_INL value kq_p_leb(value x, value y)  { return (kq_u) x <= (kq_u) y ? KQ_TRUE : KQ_FALSE; }
KQ_INL value kq_p_ltsb(value x, value y) { return (long) x <  (long) y ? KQ_TRUE : KQ_FALSE; }
KQ_INL value kq_p_lesb(value x, value y) { return (long) x <= (long) y ? KQ_TRUE : KQ_FALSE; }
KQ_INL value kq_p_div(value x, value y)  { kq_u a = (kq_u) x >> 1, b = (kq_u) y >> 1; return b == 0 ? KQ_V(0) : KQ_V(a / b); }
KQ_INL value kq_p_mod(value x, value y)  { kq_u a = (kq_u) x >> 1, b = (kq_u) y >> 1; return b == 0 ? x : KQ_V(a % b); }
KQ_INL value kq_p_divs(value x, value y) { long a = (long) x >> 1, b = (long) y >> 1; return b == 0 ? KQ_V(0) : (b == -1 ? KQ_V(0UL - (kq_u) a) : KQ_V(a / b)); }
KQ_INL value kq_p_mods(value x, value y) { long a = (long) x >> 1, b = (long) y >> 1; return b == 0 ? x : (b == -1 ? KQ_V(0) : KQ_V(a % b)); }
#ifndef KQ_NO_PRIM_INLINE
#define prim_int63_add  kq_p_add
#define prim_int63_sub  kq_p_sub
#define prim_int63_mul  kq_p_mul
#define prim_int63_land kq_p_land
#define prim_int63_lor  kq_p_lor
#define prim_int63_lxor kq_p_lxor
#define prim_int63_lsl  kq_p_lsl
#define prim_int63_lsr  kq_p_lsr
#define prim_int63_asr  kq_p_asr
#define prim_int63_eqb  kq_p_eqb
#define prim_int63_ltb  kq_p_ltb
#define prim_int63_leb  kq_p_leb
#define prim_int63_ltsb kq_p_ltsb
#define prim_int63_lesb kq_p_lesb
#define prim_int63_div  kq_p_div
#define prim_int63_mod  kq_p_mod
#define prim_int63_divs kq_p_divs
#define prim_int63_mods kq_p_mods
#endif
#endif
