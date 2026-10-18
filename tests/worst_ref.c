/* worst_ref KERNEL MEMFILE R N : the guideline way of each kernel of tests/mkworst.py in plain C (the C++ reference).
   Prints "KERNEL RESULT MS". */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef long long ll;
static ll *blk[5]; static ll len_[5];
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1e3 + t.tv_nsec / 1e6; }
int main(int argc, char **argv) {
  if (argc < 5) return 2;
  const char *k = argv[1]; FILE *f = fopen(argv[2], "r"); int R = atoi(argv[3]); ll N = atoll(argv[4]);
  int nb; if (fscanf(f, "%d", &nb) != 1) return 2;
  for (int b = 0; b < nb; b++) { if (fscanf(f, "%lld", &len_[b]) != 1) return 2; blk[b] = calloc(len_[b] + 1, sizeof(ll));
    for (ll i = 0; i < len_[b]; i++) if (fscanf(f, "%lld", &blk[b][i]) != 1) return 2; }
  ll *A = blk[0], *B = blk[1], *T = blk[2], *C = blk[3], *H = blk[4]; ll res = 0; double t0 = now();
  if (!strcmp(k, "mix")) {
    ll acc = 0, cnt = 0;
    for (int r = 0; r < R; r++) { acc = 0; cnt = 0;
      for (ll i = 0; i < N; i++) { ll x = A[i]; acc = (x & 1) == 0 ? acc + x * 3 : acc - x; if (x < 500) cnt++; B[i] = acc & 1023; }
      C[0] = acc + cnt; }
    res = C[0] + B[N - 1];
  } else if (!strcmp(k, "mixb")) {
    ll acc = 0, cnt = 0;
    for (int r = 0; r < R; r++) { acc = 0; cnt = 0;
      for (ll i = 0; i < N; i++) { ll x = A[i]; ll m = -(x & 1); acc += ((3 * x) & ~m) | ((-x) & m); cnt += (x < 500); B[i] = acc & 1023; }
      C[0] = acc + cnt; }
    res = C[0] + B[N - 1];
  } else if (!strcmp(k, "searchb")) {
    ll acc = 0;
    for (int r = 0; r < R; r++) for (ll i = 0; i < N; i++) {
      ll lo = 0, len = 1024, key = A[i];
      for (int s = 0; s < 10; s++) { ll half = len >> 1; lo += half & -(ll)(T[lo + half] < key); len -= half; }
      acc += lo; }
    res = acc;
  } else if (!strcmp(k, "search")) {
    ll acc = 0;
    for (int r = 0; r < R; r++) for (ll i = 0; i < N; i++) {
      ll lo = 0, len = 1024, key = A[i];
      for (int s = 0; s < 10; s++) { ll half = len >> 1; if (T[lo + half] < key) lo += half; len -= half; }
      acc += lo; }
    res = acc;
  } else if (!strcmp(k, "hist")) {
    for (int r = 0; r < R; r++) for (ll i = 0; i < N; i++) H[A[i] & 1023]++;
    res = H[0] + H[1] + H[511] + H[1023];
  }
  double t1 = now(); printf("%s %lld %.3f\n", k, res, t1 - t0); return 0;
}
