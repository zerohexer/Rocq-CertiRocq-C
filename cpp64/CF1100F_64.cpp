#include <bits/stdc++.h>
using namespace std;
const int N = 500005, B = 20;
long long bas[N][B], pos[N][B];
int main() {
    int n; scanf("%d", &n);
    vector<long long> c(n + 1); for (int r = 1; r <= n; r++) scanf("%lld", &c[r]);
    int q; scanf("%d", &q);
    vector<long long> L(q), R(q), A(q); for (int i = 0; i < q; i++) scanf("%lld %lld", &L[i], &R[i]);
    // the arrays' pages are taken from the operating system before the clock starts (a Rocq program is handed its memory)
    memset(bas, 0, sizeof bas); memset(pos, 0, sizeof pos);
    auto t0 = chrono::steady_clock::now();
    for (int r = 1; r <= n; r++) {
        long long x = c[r];
        memcpy(bas[r], bas[r - 1], sizeof bas[r]); memcpy(pos[r], pos[r - 1], sizeof pos[r]);
        long long p = r;
        for (int b = B - 1; b >= 0; b--) {
            if (!(x >> b & 1)) continue;
            if (!bas[r][b]) { bas[r][b] = x; pos[r][b] = p; break; }
            if (pos[r][b] < p) { swap(bas[r][b], x); swap(pos[r][b], p); }
            x ^= bas[r][b];
        }
    }
    for (int i = 0; i < q; i++) {
        long long l = L[i], r = R[i];
        long long res = 0;
        for (int b = B - 1; b >= 0; b--) if (pos[r][b] >= l && (res ^ bas[r][b]) > res) res ^= bas[r][b];
        A[i] = res;
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int i = 0; i < q; i++) printf("%lld\n", A[i]);
}
