// kq_perf.h -- the machine's own counters around the timed region, when $KQ_PERF is set: cycles, instructions,
// branches and mispredicted branches, cache misses.  User space only (Linux perf_event_open).  For finding out WHY one
// build is slower than another: more instructions, or the same instructions waiting longer.
#ifndef KQ_PERF_H
#define KQ_PERF_H
#include <linux/perf_event.h>
#include <sys/syscall.h>
#include <sys/ioctl.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#define KQ_PN 6
static int kq_pfd[KQ_PN]; static int kq_pon;
static const char *kq_pname[KQ_PN] = { "cycles", "instr", "branches", "br-miss", "l1d-miss", "llc-miss" };
static int kq_pe(uint32_t type, uint64_t config) {
  struct perf_event_attr a; memset(&a, 0, sizeof a); a.type = type; a.size = sizeof a; a.config = config;
  a.disabled = 1; a.exclude_kernel = 1; a.exclude_hv = 1;
  return (int) syscall(SYS_perf_event_open, &a, 0, -1, -1, 0);
}
static void kq_perf_start(void) {
  if (!getenv("KQ_PERF")) return;
  kq_pfd[0] = kq_pe(PERF_TYPE_HARDWARE, PERF_COUNT_HW_CPU_CYCLES);
  kq_pfd[1] = kq_pe(PERF_TYPE_HARDWARE, PERF_COUNT_HW_INSTRUCTIONS);
  kq_pfd[2] = kq_pe(PERF_TYPE_HARDWARE, PERF_COUNT_HW_BRANCH_INSTRUCTIONS);
  kq_pfd[3] = kq_pe(PERF_TYPE_HARDWARE, PERF_COUNT_HW_BRANCH_MISSES);
  kq_pfd[4] = kq_pe(PERF_TYPE_HW_CACHE, PERF_COUNT_HW_CACHE_L1D | (PERF_COUNT_HW_CACHE_OP_READ << 8) | (PERF_COUNT_HW_CACHE_RESULT_MISS << 16));
  kq_pfd[5] = kq_pe(PERF_TYPE_HW_CACHE, PERF_COUNT_HW_CACHE_LL | (PERF_COUNT_HW_CACHE_OP_READ << 8) | (PERF_COUNT_HW_CACHE_RESULT_MISS << 16));
  kq_pon = 1;
  for (int i = 0; i < KQ_PN; i++) if (kq_pfd[i] >= 0) { ioctl(kq_pfd[i], PERF_EVENT_IOC_RESET, 0); ioctl(kq_pfd[i], PERF_EVENT_IOC_ENABLE, 0); }
}
static void kq_perf_pause(void)  { if (kq_pon) for (int i = 0; i < KQ_PN; i++) if (kq_pfd[i] >= 0) ioctl(kq_pfd[i], PERF_EVENT_IOC_DISABLE, 0); }
static void kq_perf_resume(void) { if (kq_pon) for (int i = 0; i < KQ_PN; i++) if (kq_pfd[i] >= 0) ioctl(kq_pfd[i], PERF_EVENT_IOC_ENABLE, 0); }
static void kq_perf_stop(void) {
  if (!kq_pon) return;
  for (int i = 0; i < KQ_PN; i++) if (kq_pfd[i] >= 0) ioctl(kq_pfd[i], PERF_EVENT_IOC_DISABLE, 0);
  fprintf(stderr, "perf");
  for (int i = 0; i < KQ_PN; i++) { uint64_t v = 0; if (kq_pfd[i] < 0 || read(kq_pfd[i], &v, sizeof v) != sizeof v) fprintf(stderr, " %s -", kq_pname[i]); else fprintf(stderr, " %s %lu", kq_pname[i], (unsigned long) v); }
  fprintf(stderr, "\n");
}
#endif
