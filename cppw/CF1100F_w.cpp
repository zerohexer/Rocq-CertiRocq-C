// CF1100F -- the C++ WRITTEN THE WAY THE FAST ROCQ VERSION IS (hand/CF1100Fv3.body): one 64-bit word per cell of the
// table (position * 2^20 + vector), a row made in one pass over the 20 bits, and every choice a choice between two
// numbers (no jump on a bit of the data).  What separates this from the Rocq program is the language route only.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const int N = 500005, B = 20; const ll M = (1 << 20) - 1;
static ll tab[N][B];
int main() {
    int n; scanf("%d", &n);
    vector<int> c(n + 1); for (int r = 1; r <= n; r++) scanf("%d", &c[r]);
    int q; scanf("%d", &q);
    vector<int> L(q), R(q), A(q); for (int i = 0; i < q; i++) scanf("%d %d", &L[i], &R[i]);
    // the arrays' pages are taken from the operating system before the clock starts (a Rocq program is handed its memory)
    memset(tab, 0, sizeof tab);
    auto t0 = chrono::steady_clock::now();
    for (int r = 1; r <= n; r++) {
        ll x = c[r], p = r; const ll *src = tab[r - 1]; ll *dst = tab[r];
        for (int b = B - 1; b >= 0; b--) {
            const ll w = src[b], cur = w & M, qq = w >> 20;
            const bool bit = (x >> b) & 1, fr = cur == 0, older = qq < p;
            dst[b] = (bit && (fr || older)) ? (p << 20) + x : w;
            const ll nx = bit ? (fr ? 0 : (x ^ cur)) : x;
            p = (bit && !fr && older) ? qq : p;
            x = nx;
        }
    }
    for (int i = 0; i < q; i++) {
        const ll l = L[i]; ll res = 0; const ll *rw = tab[R[i]];
        for (int b = B - 1; b >= 0; b--) { const ll w = rw[b], y = res ^ (w & M); res = (l <= (w >> 20) && res < y) ? y : res; }
        A[i] = (int) res;
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int i = 0; i < q; i++) printf("%d\n", A[i]);
}
