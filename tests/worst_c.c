/* worst_c WAY MEMFILE R N M : every way of tests/mkworst.py written the same way in plain C -- the state in memory
   cells, the phases as a switch in one loop, the repeated reads -- with the pointers a C function would receive
   (no restrict).  Prints "WAY RESULT MS", the result being the one the Rocq ways give.
   Block 0 = data, 1 = output, 2 = sorted table, 3 = state cells, 4 = counters. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <linux/perf_event.h>
#include <string.h>
typedef long long ll;
#define NOINL __attribute__((noinline))
static int ioctl_(int fd, unsigned long r) { return syscall(SYS_ioctl, fd, r, 0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1e3 + t.tv_nsec / 1e6; }

/* ---- mix */
static inline int odd_(ll x) { return (x & 1) == 1; }
static inline int small_(ll x) { return x < 500; }
static inline ll bump_(int c, ll v, ll d) { return c ? v + d : v; }
static inline ll mixed_(ll x, ll a) { return odd_(x) ? a - x : a + x * 3; }

NOINL ll mix_guideline(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  for (int r = 0; r < R; r++) { ll acc = 0, cnt = 0;
    for (ll i = 0; i < N; i++) { ll x = A[i]; acc = (x & 1) == 0 ? acc + x * 3 : acc - x; cnt = x < 500 ? cnt + 1 : cnt; B[i] = acc & 1023; }
    C[0] = acc + cnt; }
  return C[0] + B[N - 1];
}
NOINL ll mix_state_in_cells(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  for (int r = 0; r < R; r++) { C[1] = 0; C[2] = 0;
    for (ll i = 0; i < N; i++) { ll x = A[i];
      C[1] = (x & 1) == 0 ? C[1] + x * 3 : C[1] - x;
      C[2] = x < 500 ? C[2] + 1 : C[2];
      B[i] = C[1] & 1023; }
    C[0] = C[1] + C[2]; }
  return C[0] + B[N - 1];
}
NOINL ll mix_phases(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  for (int r = 0; r < R; r++) { ll ph = 0, i = 0, x = 0, acc = 0, cnt = 0;
    for (ll f = 0; f < M; f++) {
      if (ph == 0) { x = A[i]; ph = 1; }
      else if (ph == 1) { acc = (x & 1) == 0 ? acc + x * 3 : acc - x; ph = 2; }
      else { cnt = x < 500 ? cnt + 1 : cnt; B[i] = acc & 1023; i++; ph = 0; } }
    C[0] = acc + cnt; }
  return C[0] + B[N - 1];
}
NOINL ll mix_phases_and_cells(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  for (int r = 0; r < R; r++) { C[1] = 0; C[2] = 0; ll ph = 0, i = 0;
    for (ll f = 0; f < M; f++) {
      if (ph == 0) { C[3] = A[i]; ph = 1; }
      else if (ph == 1) { C[1] = (C[3] & 1) == 0 ? C[1] + C[3] * 3 : C[1] - C[3]; ph = 2; }
      else { C[2] = C[3] < 500 ? C[2] + 1 : C[2]; B[i] = C[1] & 1023; i++; ph = 0; } }
    C[0] = C[1] + C[2]; }
  return C[0] + B[N - 1];
}
NOINL ll mix_everything(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  for (int r = 0; r < R; r++) { C[1] = 0; C[2] = 0; ll ph = 0, i = 0;
    for (ll f = 0; f < M; f++) {
      if (ph == 0) { C[3] = A[i]; ph = 1; }
      else if (ph == 1) { C[1] = mixed_(A[i], C[1]); ph = 2; }
      else { C[2] = bump_(small_(A[i]), C[2], 1); B[i] = C[1] & 1023; i++; ph = 0; } }
    C[0] = C[1] + C[2]; }
  return C[0] + B[N - 1];
}

/* ---- search */
NOINL ll search_guideline(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  ll acc = 0;
  for (int r = 0; r < R; r++) for (ll i = 0; i < N; i++) {
    ll lo = 0, len = 1024, key = A[i];
    for (int s = 0; s < 10; s++) { ll half = len >> 1; if (T[lo + half] < key) lo += half; len -= half; }
    acc += lo; }
  return acc;
}
NOINL ll search_state_in_cells(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  C[4] = 0;
  for (int r = 0; r < R; r++) for (ll i = 0; i < N; i++) {
    C[0] = 0; C[1] = 1024; C[2] = A[i];
    for (int s = 0; s < 10; s++) { ll half = C[1] >> 1; C[0] = T[C[0] + half] < C[2] ? C[0] + half : C[0]; C[1] = C[1] - half; }
    C[4] += C[0]; }
  return C[4];
}
NOINL ll search_phases(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  ll acc = 0;
  for (int r = 0; r < R; r++) for (ll i = 0; i < N; i++) {
    ll ph = 0, lo = 0, len = 1024, key = A[i], mid = 0, v = 0;
    for (int f = 0; f < 30; f++) {
      if (ph == 0) { mid = lo + (len >> 1); ph = 1; }
      else if (ph == 1) { v = T[mid]; ph = 2; }
      else { lo = v < key ? mid : lo; len = len - (len >> 1); ph = 0; } }
    acc += lo; }
  return acc;
}
NOINL ll search_phases_and_cells(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  C[4] = 0;
  for (int r = 0; r < R; r++) for (ll i = 0; i < N; i++) {
    C[0] = 0; C[1] = 1024; C[2] = A[i]; ll ph = 0;
    for (int f = 0; f < 30; f++) {
      if (ph == 0) { C[5] = C[0] + (C[1] >> 1); ph = 1; }
      else if (ph == 1) { C[6] = T[C[5]]; ph = 2; }
      else { C[1] = C[1] - (C[1] >> 1); C[0] = C[6] < C[2] ? C[5] : C[0]; ph = 0; } }
    C[4] += C[0]; }
  return C[4];
}

/* ---- hist */
NOINL ll hist_guideline(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  for (int r = 0; r < R; r++) for (ll i = 0; i < N; i++) { ll k = A[i] & 1023; H[k] = H[k] + 1; }
  return H[0] + H[1] + H[511] + H[1023];
}
NOINL ll hist_repeated_reads(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  for (int r = 0; r < R; r++) for (ll i = 0; i < N; i++) H[A[i] & 1023] = H[A[i] & 1023] + 1;
  return H[0] + H[1] + H[511] + H[1023];
}
NOINL ll hist_state_in_cells(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  for (int r = 0; r < R; r++) { C[8] = 0;
    for (ll f = 0; f < N; f++) { C[7] = A[C[8]] & 1023; H[C[7]] = H[C[7]] + 1; C[8] = C[8] + 1; } }
  return H[0] + H[1] + H[511] + H[1023];
}
static inline ll key_(ll *A, ll i) { return A[i] & 1023; }
static inline ll count_(ll *H, ll k) { return H[k]; }
NOINL ll hist_phases_and_helpers(ll *A, ll *B, ll *T, ll *C, ll *H, int R, ll N, ll M) {
  for (int r = 0; r < R; r++) { ll ph = 0, i = 0, k = 0, v = 0;
    for (ll f = 0; f < M; f++) {
      if (ph == 0) { k = key_(A, i); ph = 1; }
      else if (ph == 1) { v = count_(H, k); ph = 2; }
      else { H[k] = v + 1; i++; ph = 0; } } }
  return H[0] + H[1] + H[511] + H[1023];
}

typedef ll (*fn)(ll *, ll *, ll *, ll *, ll *, int, ll, ll);
static struct { const char *name; fn f; } W[] = {
  {"mix_guideline", mix_guideline}, {"mix_state_in_cells", mix_state_in_cells}, {"mix_phases", mix_phases},
  {"mix_phases_and_cells", mix_phases_and_cells}, {"mix_everything", mix_everything},
  {"search_guideline", search_guideline}, {"search_state_in_cells", search_state_in_cells},
  {"search_phases", search_phases}, {"search_phases_and_cells", search_phases_and_cells},
  {"hist_guideline", hist_guideline}, {"hist_repeated_reads", hist_repeated_reads},
  {"hist_state_in_cells", hist_state_in_cells}, {"hist_phases_and_helpers", hist_phases_and_helpers}, {0, 0} };

static int pfd[4];
static void pc_open(void) {
  unsigned cfg[4] = { PERF_COUNT_HW_CPU_CYCLES, PERF_COUNT_HW_INSTRUCTIONS, PERF_COUNT_HW_BRANCH_INSTRUCTIONS, PERF_COUNT_HW_BRANCH_MISSES };
  for (int i = 0; i < 4; i++) { struct perf_event_attr a; memset(&a, 0, sizeof a); a.type = PERF_TYPE_HARDWARE; a.size = sizeof a;
    a.config = cfg[i]; a.disabled = 1; a.exclude_kernel = 1; a.exclude_hv = 1; pfd[i] = syscall(SYS_perf_event_open, &a, 0, -1, -1, 0); } }
static void pc_start(void) { for (int i = 0; i < 4; i++) if (pfd[i] >= 0) { ioctl_(pfd[i], 0x2403); ioctl_(pfd[i], 0x2400); } }
static void pc_stop(long long *v) { for (int i = 0; i < 4; i++) { v[i] = -1; if (pfd[i] >= 0) { ioctl_(pfd[i], 0x2401); if (read(pfd[i], &v[i], 8) != 8) v[i] = -1; } } }
int main(int argc, char **argv) {
  if (argc < 6) return 2;
  ll *blk[5]; ll len_[5]; FILE *f = fopen(argv[2], "r"); int R = atoi(argv[3]); ll N = atoll(argv[4]), M = atoll(argv[5]);
  int nb; if (fscanf(f, "%d", &nb) != 1) return 2;
  for (int b = 0; b < nb; b++) { if (fscanf(f, "%lld", &len_[b]) != 1) return 2; blk[b] = calloc(len_[b] + 1, sizeof(ll));
    for (ll i = 0; i < len_[b]; i++) if (fscanf(f, "%lld", &blk[b][i]) != 1) return 2; }
  for (int w = 0; W[w].name; w++) if (!strcmp(W[w].name, argv[1])) {
    long long v[4]; pc_open(); pc_start(); double t0 = now(); ll r = W[w].f(blk[0], blk[1], blk[2], blk[3], blk[4], R, N, M); double t1 = now(); pc_stop(v);
    printf("%s %lld %.3f perf cycles %lld instr %lld branches %lld br-miss %lld\n", argv[1], r, t1 - t0, v[0], v[1], v[2], v[3]); return 0; }
  return 3;
}
