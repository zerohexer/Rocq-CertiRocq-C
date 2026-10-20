#include <stdio.h>
#include <stdlib.h>
#include <time.h>
typedef long long ll;
__attribute__((noinline)) ll solve(unsigned char *m, int r, ll n) {
  for (ll i = 0; i < n; i++) m[i] = (unsigned char)(i * 7 + 3);
  ll acc = 0;
  for (int k = 0; k < r; k++) { __asm__ volatile("" ::: "memory"); ll s = 0; for (ll i = 0; i < n; i++) s += m[i] * ((i & 7) + 1); acc += s; }
  return acc;
}
int main(int c, char **v) { int r = atoi(v[1]); ll n = atoll(v[2]); unsigned char *m = calloc(n + 8, 1);
  struct timespec a, b; clock_gettime(CLOCK_MONOTONIC, &a); ll x = solve(m, r, n); clock_gettime(CLOCK_MONOTONIC, &b);
  printf("%lld %.3f\n", x, (b.tv_sec - a.tv_sec) * 1e3 + (b.tv_nsec - a.tv_nsec) / 1e6); }
