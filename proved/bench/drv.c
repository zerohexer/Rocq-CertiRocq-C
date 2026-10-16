#include <stdio.h>
#include <time.h>
unsigned long long f10(unsigned long long, unsigned long long);
unsigned long long f11(unsigned long long, unsigned long long, unsigned long long);
unsigned long long hand_lcg(void);
unsigned long long f45(void);
unsigned long long hand_sort(void);
unsigned long long hand_sumsq(unsigned long long, unsigned long long, unsigned long long);
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1e3 + t.tv_nsec / 1e6; }
#define BEST(name, expr) do { double b = 1e9; unsigned long long r = 0; \
  for (int k = 0; k < 7; k++) { double t0 = now(); r = (expr); double t = now() - t0; if (t < b) b = t; } \
  printf("%-12s %10.2f ms  %llu\n", name, b, r); } while (0)
int main(void) {
  BEST("lcg gen", f10(24, 1));
  BEST("lcg hand", hand_lcg());
  BEST("sumsq gen", f11(100000000ULL, 1, 0));
  BEST("sumsq hand", hand_sumsq(100000000ULL, 1, 0));
  BEST("sort gen", f45());
  BEST("sort hand", hand_sort());
  return 0;
}
