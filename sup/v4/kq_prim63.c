// kq_prim63.c -- the machine-integer operations, in place of the runtime's prim_int63.c.
// A Rocq machine integer n is the C word 2n+1.  The runtime decodes, computes, encodes; here the common operations work
// on the encoded words directly (2a+1 + 2b+1 - 1 = 2(a+b)+1), and three are CORRECTED: the runtime computes the signed
// remainder and the arithmetic right shift on the unsigned value, and the unsigned comparisons as signed ones.
// The rest of the runtime's file (carries, double-word operations, ..) is taken as it is.
#define prim_int63_add  kq_orig_add
#define prim_int63_sub  kq_orig_sub
#define prim_int63_mul  kq_orig_mul
#define prim_int63_mod  kq_orig_mod
#define prim_int63_div  kq_orig_div
#define prim_int63_mods kq_orig_mods
#define prim_int63_divs kq_orig_divs
#define prim_int63_land kq_orig_land
#define prim_int63_lor  kq_orig_lor
#define prim_int63_lxor kq_orig_lxor
#define prim_int63_lsl  kq_orig_lsl
#define prim_int63_lsr  kq_orig_lsr
#define prim_int63_asr  kq_orig_asr
#define prim_int63_eqb  kq_orig_eqb
#define prim_int63_leb  kq_orig_leb
#define prim_int63_ltb  kq_orig_ltb
#define prim_int63_lesb kq_orig_lesb
#define prim_int63_ltsb kq_orig_ltsb
#include "prim_int63.c"
#undef prim_int63_add
#undef prim_int63_sub
#undef prim_int63_mul
#undef prim_int63_mod
#undef prim_int63_div
#undef prim_int63_mods
#undef prim_int63_divs
#undef prim_int63_land
#undef prim_int63_lor
#undef prim_int63_lxor
#undef prim_int63_lsl
#undef prim_int63_lsr
#undef prim_int63_asr
#undef prim_int63_eqb
#undef prim_int63_leb
#undef prim_int63_ltb
#undef prim_int63_lesb
#undef prim_int63_ltsb
typedef unsigned long kq_u;                      /* the word, unsigned */
#define KQ_T ((value) 3)                         /* true  */
#define KQ_F ((value) 1)                         /* false */
#define KQ_V(n) ((value) ((((kq_u) (n)) << 1) | 1))
value prim_int63_add(value x, value y)  { return (value) ((kq_u) x + (kq_u) y - 1); }
value prim_int63_sub(value x, value y)  { return (value) ((kq_u) x - (kq_u) y + 1); }
value prim_int63_mul(value x, value y)  { return (value) (((kq_u) x >> 1) * ((kq_u) y - 1) + 1); }
value prim_int63_land(value x, value y) { return x & y; }
value prim_int63_lor(value x, value y)  { return x | y; }
value prim_int63_lxor(value x, value y) { return (x ^ y) | 1; }
value prim_int63_lsl(value x, value y)  { kq_u n = (kq_u) y >> 1; return n < 63 ? (value) ((((kq_u) x - 1) << n) | 1) : KQ_V(0); }
value prim_int63_lsr(value x, value y)  { kq_u n = (kq_u) y >> 1; return n < 63 ? (value) (((kq_u) x >> n) | 1) : KQ_V(0); }
value prim_int63_asr(value x, value y)  { kq_u n = (kq_u) y >> 1; return n < 63 ? (value) (((long) x >> n) | 1) : (x < 0 ? KQ_V(-1L) : KQ_V(0)); }
value prim_int63_eqb(value x, value y)  { return x == y ? KQ_T : KQ_F; }
value prim_int63_ltb(value x, value y)  { return (kq_u) x <  (kq_u) y ? KQ_T : KQ_F; }
value prim_int63_leb(value x, value y)  { return (kq_u) x <= (kq_u) y ? KQ_T : KQ_F; }
value prim_int63_ltsb(value x, value y) { return (long) x <  (long) y ? KQ_T : KQ_F; }
value prim_int63_lesb(value x, value y) { return (long) x <= (long) y ? KQ_T : KQ_F; }
value prim_int63_div(value x, value y)  { kq_u a = (kq_u) x >> 1, b = (kq_u) y >> 1; return b == 0 ? KQ_V(0) : KQ_V(a / b); }
value prim_int63_mod(value x, value y)  { kq_u a = (kq_u) x >> 1, b = (kq_u) y >> 1; return b == 0 ? x : KQ_V(a % b); }
/* signed: quotient toward 0, remainder with the sign of the dividend; by 0: 0 and the number itself */
value prim_int63_divs(value x, value y) { long a = (long) x >> 1, b = (long) y >> 1; return b == 0 ? KQ_V(0) : (b == -1 ? KQ_V(0UL - (kq_u) a) : KQ_V(a / b)); }
value prim_int63_mods(value x, value y) { long a = (long) x >> 1, b = (long) y >> 1; return b == 0 ? x : (b == -1 ? KQ_V(0) : KQ_V(a % b)); }
