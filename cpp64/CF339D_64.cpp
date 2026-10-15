// CF339D Xenia and Bit Operations -- a tree over 2^n numbers; the level above the numbers takes the OR of its two
// children, the next one the XOR, and so on in turn; after every change of one number, the value at the top.
// (the same program with every array of numbers 64 bits wide: the data layout the Rocq program is given)
#include <bits/stdc++.h>
using namespace std;
int main() {
    int n, m; scanf("%d %d", &n, &m);
    const int N = 1 << n;
    vector<long long> t(2 * N, 0);
    for (int i = 0; i < N; i++) scanf("%lld", &t[N + i]);
    vector<long long> qp(m), qb(m), ans(m);
    for (int i = 0; i < m; i++) scanf("%lld %lld", &qp[i], &qb[i]);
    auto t0 = chrono::steady_clock::now();
    for (int b = N >> 1, isor = 1; b >= 1; b >>= 1, isor ^= 1)
        for (int p = b; p < 2 * b; p++) t[p] = isor ? (t[2 * p] | t[2 * p + 1]) : (t[2 * p] ^ t[2 * p + 1]);
    for (int i = 0; i < m; i++) {
        long long c = N + qp[i] - 1; int isor = 1;
        t[c] = qb[i];
        while (c > 1) { c >>= 1; t[c] = isor ? (t[2 * c] | t[2 * c + 1]) : (t[2 * c] ^ t[2 * c + 1]); isor ^= 1; }
        ans[i] = t[1];
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int i = 0; i < m; i++) printf("%lld\n", ans[i]);
}
