// kq_bare.c -- the support code for a Rocq program that IS the machine's only program (no operating system, no C
// library): in place of kq_io3.c (the memory's table, the slow path, the command line, the checksum, input and output)
// and of the collector (kq_nogc.c's idea: a program whose loops build nothing needs memory for values only now and
// then; it is handed out from one fixed area and never taken back).  Plus the two halves of an interrupt that are not
// Rocq: noting the vector (kq_hw_isr, called by boot.S) and handing it over (kq_rt_irq_take, for hw_irq_take) -- or, when the
// kernel has a Rocq program for interrupts (hw/NAME_irq.body, linked as kq_irq_body), calling it at once.  And the C
// entry of a second processor (kq_ap_main, from boot.S), which runs the kernel's program for it (hw/NAME_ap.body,
// linked as kq_ap_body).  Each Rocq program has its own area for the values it builds.
// Output: the serial line (COM1).  At the end the program's result is printed and QEMU is told to stop with it
// (the isa-debug-exit device, port 0xf4: QEMU's exit status is 2 * result + 1).
#include <stdint.h>
#include <stddef.h>
#include "gc_stack.h"
#define KQ_NO_PRIM_INLINE
#include "kq_io.h"
extern value body(struct thread_info *);

// ---- the memory: wide blocks (8-byte cells) and narrow blocks (4-byte cells, each on a page of its own)
#ifndef KQ_BARE_NB
#define KQ_BARE_NB 4          /* wide blocks */
#endif
#ifndef KQ_BARE_WLEN
#define KQ_BARE_WLEN 4096     /* cells in each */
#endif
#ifndef KQ_BARE_NN
#define KQ_BARE_NN 8          /* narrow blocks */
#endif
#ifndef KQ_BARE_NLEN
#define KQ_BARE_NLEN 1024     /* cells in each: 4096 bytes, one page */
#endif
kq_block kq_b[KQ_MAXB];   long kq_nb;
kq_block32 kq_n[KQ_MAXB]; long kq_nn;
static value kq_wide[KQ_BARE_NB][KQ_BARE_WLEN + 1];
static int kq_narrow[KQ_BARE_NN][KQ_BARE_NLEN] __attribute__((aligned(4096)));
uintptr_t kq_hw_wlo, kq_hw_whi;        /* where the wide blocks are: hw/kq_hw.h lets no raw store reach them */
__attribute__((noinline)) value *kq_cell_slow(value h, value i) {
  long hh = KQ_N(h), ii = KQ_N(i); if (hh < 0) hh = 0; if (ii < 0) ii = 0;
  if (hh >= kq_nb || hh >= KQ_MAXB || (unsigned long) ii >= kq_b[hh].len) return 0;
  return kq_b[hh].p + ii;
}
__attribute__((noinline)) int *kq_cell32_slow(value h, value i) {
  long hh = KQ_N(h), ii = KQ_N(i); if (hh < 0) hh = 0; if (ii < 0) ii = 0;
  if (hh >= kq_nn || hh >= KQ_MAXB || (unsigned long) ii >= kq_n[hh].len) return 0;
  return kq_n[hh].p + ii;
}

// ---- the serial line, for the harness's own messages
static inline void kq_outb(uint16_t p, uint8_t v) { __asm__ volatile ("outb %0, %w1" : : "a" (v), "Nd" (p)); }
static inline uint8_t kq_inb(uint16_t p) { uint8_t v; __asm__ volatile ("inb %w1, %0" : "=a" (v) : "Nd" (p)); return v; }
static void kq_ser_init(void) {
  kq_outb(0x3F9, 0); kq_outb(0x3FB, 0x80); kq_outb(0x3F8, 3); kq_outb(0x3F9, 0); kq_outb(0x3FB, 3); kq_outb(0x3FA, 0xC7); kq_outb(0x3FC, 0x0B);
}
static void kq_putc(char c) { while (!(kq_inb(0x3FD) & 0x20)) { } kq_outb(0x3F8, (uint8_t) c); }
static void kq_puts(const char *s) { while (*s) kq_putc(*s++); }
static void kq_putn(long n) {
  char b[24]; int k = 0; unsigned long u = n < 0 ? 0UL - (unsigned long) n : (unsigned long) n;
  if (n < 0) kq_putc('-');
  do { b[k++] = (char) ('0' + u % 10); u /= 10; } while (u);
  while (k) kq_putc(b[--k]);
}
static void kq_putx(unsigned long u) { kq_puts("0x"); for (int k = 60; k >= 0; k -= 4) kq_putc("0123456789abcdef"[(u >> k) & 15]); }
__attribute__((noreturn)) static void kq_exit(long code) {
  kq_outb(0xf4, (uint8_t) code);                     /* QEMU stops here (isa-debug-exit); elsewhere, halt */
  for (;;) __asm__ volatile ("cli; hlt");
}

// ---- what KQRun.v declares besides the memory
#ifndef KQ_BARE_ARGS
#define KQ_BARE_ARGS 10
#endif
static const long kq_args[] = { KQ_BARE_ARGS };
value kq_arg(value i) { long k = KQ_N(i); return KQ_V((k >= 0 && k < (long) (sizeof kq_args / sizeof kq_args[0])) ? kq_args[k] : 0); }
value kq_input(value x) { return 1; }
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
value kq_sum(value s) { return KQ_V(kq_checksum()); }
value kq_in(value h, value i, value s) { return kq_updb(h, i, KQ_V(-1), s); }          /* no input here */
value kq_out(value v, value s) { kq_puts("KQ-OUT "); kq_putn(KQ_N(v)); kq_putc('\n'); return s; }
value kq_nat(value n) { return n; }

// ---- values the program builds: one fixed area, handed out once, never taken back
#ifndef KQ_BARE_HEAP
#define KQ_BARE_HEAP (1L << 21)                         /* words: 16 MB */
#endif
static value kq_heap[KQ_BARE_HEAP];
static struct thread_info kq_ti;
static int kq_heap_given;
#define KQ_SIDE_HEAP (1L << 16)                         /* words, for the interrupt program and the second processor's */
static value kq_heap_irq[KQ_SIDE_HEAP], kq_heap_ap[KQ_SIDE_HEAP];
static struct thread_info kq_ti_irq, kq_ti_ap;
struct thread_info *make_tinfo(void) { return &kq_ti; }  /* alloc = limit = 0: the first request asks for the area */
void garbage_collect(struct thread_info *ti) {
  if (ti != &kq_ti || kq_heap_given || ti->nalloc + 16 > (uintnat) KQ_BARE_HEAP) { kq_puts("KQ-PANIC out of memory for values\n"); kq_exit(120); }
  kq_heap_given = 1; ti->alloc = kq_heap; ti->limit = kq_heap + KQ_BARE_HEAP;
}

// ---- interrupts: the entry code (boot.S) calls kq_hw_isr with the vector; the program takes them with hw_irq_take
#define KQ_IRQ_Q 256
static volatile long kq_irq_q[KQ_IRQ_Q];
static volatile unsigned kq_irq_head, kq_irq_tail;
static volatile unsigned long kq_irq_lost;
volatile long kq_irq_cur[3] = { -1, -1, -1 };          /* hw_vec: what the interrupt being handled is */
extern value kq_irq_body(struct thread_info *) __attribute__((weak));
static volatile int kq_in_handler;
static volatile unsigned long kq_irq_handled;
void kq_hw_isr(unsigned long v, unsigned long err, unsigned long rip) {
  if (kq_irq_body && !kq_in_handler) {                /* the kernel's Rocq program for interrupts, at once */
    kq_in_handler = 1; kq_irq_cur[0] = (long) v; kq_irq_cur[1] = (long) err; kq_irq_cur[2] = (long) rip;
    kq_ti_irq.alloc = kq_heap_irq; kq_ti_irq.limit = kq_heap_irq + KQ_SIDE_HEAP; kq_ti_irq.nalloc = 0;
    value r = kq_irq_body(&kq_ti_irq);
    kq_irq_cur[0] = kq_irq_cur[1] = kq_irq_cur[2] = -1; kq_in_handler = 0; kq_irq_handled++;
    if (KQ_N(r) == 0) return;                         /* 0: handled (a fault: the instruction is tried again) */
  }
  if (v < 32) {                                       /* the processor's own exceptions: the program cannot go on */
    kq_puts("KQ-EXCEPTION vector "); kq_putn((long) v); kq_puts(" error "); kq_putx(err); kq_puts(" at "); kq_putx(rip);
    if (v == 14) { unsigned long cr2; __asm__ volatile ("mov %%cr2, %0" : "=r" (cr2)); kq_puts(" address "); kq_putx(cr2); }
    kq_putc('\n'); kq_exit(100 + (long) v);
  }
  unsigned t = kq_irq_tail;
  if (t - kq_irq_head < KQ_IRQ_Q) { kq_irq_q[t % KQ_IRQ_Q] = (long) v; kq_irq_tail = t + 1; } else kq_irq_lost++;
}
long kq_rt_irq_take(void) {
  unsigned long fl; __asm__ volatile ("pushfq; pop %0; cli" : "=r" (fl) : : "memory");
  long v = -1; unsigned h = kq_irq_head;
  if (h != kq_irq_tail) { v = kq_irq_q[h % KQ_IRQ_Q]; kq_irq_head = h + 1; }
  __asm__ volatile ("push %0; popfq" : : "r" (fl) : "memory", "cc");
  return v;
}

// ---- what a C compiler may call on its own
void *memcpy(void *d, const void *s, size_t n) { char *a = d; const char *b = s; while (n--) *a++ = *b++; return d; }
void *memmove(void *d, const void *s, size_t n) { char *a = d; const char *b = s; if (a < b) while (n--) *a++ = *b++; else { a += n; b += n; while (n--) *--a = *--b; } return d; }
void *memset(void *d, int c, size_t n) { char *a = d; while (n--) *a++ = (char) c; return d; }
int memcmp(const void *x, const void *y, size_t n) { const unsigned char *a = x, *b = y; for (; n; n--, a++, b++) if (*a != *b) return *a - *b; return 0; }

// ---- a second processor (boot.S: the code at 0x8000 brings it to 64-bit mode on the same page tables, then here)
extern value kq_ap_body(struct thread_info *) __attribute__((weak));
volatile long kq_ap_ran;
void kq_ap_main(void) {
  kq_ti_ap.alloc = kq_heap_ap; kq_ti_ap.limit = kq_heap_ap + KQ_SIDE_HEAP;
  if (kq_ap_body) kq_ap_body(&kq_ti_ap);
  kq_ap_ran = 1;
  for (;;) __asm__ volatile ("cli; hlt");
}

// ---- the runtime's own addresses, for machine code a program writes itself (hw/Runtime.v: hw_sym k)
const uintptr_t kq_rt_sym[] = {
  (uintptr_t) kq_hw_isr,      /* 0: the C handler of interrupts: kq_hw_isr(vector, error code, interrupted address) */
  (uintptr_t) kq_ap_main,     /* 1: a second processor's C code (on a stack of its own) */
};
const long kq_rt_nsym = sizeof kq_rt_sym / sizeof kq_rt_sym[0];

void kq_bare_main(void) {
  kq_ser_init();
  kq_nb = KQ_BARE_NB; kq_nn = KQ_BARE_NN;
  for (long h = 0; h < KQ_BARE_NB; h++) {
    kq_b[h].p = kq_wide[h]; kq_b[h].len = KQ_BARE_WLEN; kq_b[h].lim = 2 * KQ_BARE_WLEN;
    for (long i = 0; i < KQ_BARE_WLEN; i++) kq_wide[h][i] = KQ_V(0);
  }
  for (long h = 0; h < KQ_BARE_NN; h++) { kq_n[h].p = kq_narrow[h]; kq_n[h].len = KQ_BARE_NLEN; kq_n[h].lim = 2 * KQ_BARE_NLEN; }
  kq_hw_wlo = (uintptr_t) kq_wide; kq_hw_whi = (uintptr_t) kq_wide + sizeof kq_wide;
  kq_puts("KQ-BOOT the Rocq program starts\n");
  value r = body(make_tinfo());
  kq_puts("KQ-RESULT "); kq_putn(KQ_N(r)); kq_puts(" checksum "); kq_putn(kq_checksum());
  kq_puts(" interrupts lost "); kq_putn((long) kq_irq_lost);
  if (kq_irq_body) { kq_puts(" handled by Rocq at once "); kq_putn((long) kq_irq_handled); }
  kq_putc('\n');
  kq_exit(KQ_N(r) & 0x7f);
}
