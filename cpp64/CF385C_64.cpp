// CF385C Bear and Prime Numbers -- f(p) = how many of the given numbers the prime p divides; a query asks for the
// sum of f over the primes of an interval.  A sieve that counts as it marks, then sums over the primes.
// (the same program with every array of numbers 64 bits wide: the data layout the Rocq program is given)
#include <bits/stdc++.h>
using namespace std;
const int MAX = 10000000;
static long long cnt[MAX + 2], pre[MAX + 2];
static long long comp[MAX + 2];
int main() {
    int n; scanf("%d", &n);
    vector<int> x(n); for (int i = 0; i < n; i++) scanf("%d", &x[i]);
    int q; scanf("%d", &q);
    vector<int> L(q), R(q); vector<long long> A(q);
    for (int i = 0; i < q; i++) scanf("%d %d", &L[i], &R[i]);
    // the arrays' pages are taken from the operating system before the clock starts (a Rocq program is handed its memory)
    memset(cnt, 0, sizeof cnt); memset(pre, 0, sizeof pre); memset(comp, 0, sizeof comp);
    auto t0 = chrono::steady_clock::now();
    for (int i = 0; i < n; i++) cnt[x[i]]++;
    for (int v = 2; v <= MAX; v++) {
        pre[v] = pre[v - 1];
        if (!comp[v]) {
            long long f = 0;
            for (int m = v; m <= MAX; m += v) { f += cnt[m]; comp[m] = true; }
            pre[v] += f;
        }
    }
    for (int i = 0; i < q; i++) A[i] = pre[min(R[i], MAX)] - pre[min(L[i] - 1, MAX)];
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int i = 0; i < q; i++) printf("%lld\n", A[i]);
}
