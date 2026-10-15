// CF20C -- the C++ WRITTEN THE WAY THE FAST ROCQ VERSION IS (hand/CF20C.body): a heap of its own in an array, an entry
// is one 64-bit word (distance * 2^17 + vertex), the entry on its way up or down travels in a variable and is written
// once, and the loop looks at the top and then removes it.  What separates this from the Rocq program is the language
// route only.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll INF = 1000000000000000000LL, VMASK = 131071, TOP = 4611686018427387903LL;
vector<ll> hp; int sz = 0;
static inline void sift_up(int i, ll x) {
    while (i > 1) { ll p = hp[i >> 1]; if (x < p) { hp[i] = p; i >>= 1; } else break; }
    hp[i] = x;
}
static inline void sift_down(int i, int n, ll x) {
    for (;;) {
        int l = 2 * i; if (l > n) break;
        ll a = hp[l], b = l < n ? hp[l + 1] : TOP;
        int c = b < a ? l + 1 : l; ll cv = b < a ? b : a;
        if (cv < x) { hp[i] = cv; i = c; } else break;
    }
    hp[i] = x;
}
int main() {
    int n, m; scanf("%d %d", &n, &m);
    vector<int> eu(m), ev(m), ew(m);
    for (int i = 0; i < m; i++) scanf("%d %d %d", &eu[i], &ev[i], &ew[i]);
    vector<int> head(n + 2, 0), nxt(2 * m + 4, 0), to(2 * m + 4, 0), wt(2 * m + 4, 0), par(n + 2, 0);
    vector<ll> dist(n + 2, INF);
    hp.assign(2 * m + 4, 0);
    auto t0 = chrono::steady_clock::now();
    for (int i = 0; i < m; i++) {
        int e = 2 * i + 1; to[e] = ev[i]; wt[e] = ew[i]; nxt[e] = head[eu[i]]; head[eu[i]] = e;
        e = 2 * i + 2;     to[e] = eu[i]; wt[e] = ew[i]; nxt[e] = head[ev[i]]; head[ev[i]] = e;
    }
    dist[1] = 0; sz = 1; sift_up(1, 1);
    while (sz) {
        const ll x = hp[1]; const int v = (int) (x & VMASK); const ll k = x >> 17;
        const ll last = hp[sz]; sz--; sift_down(1, sz, last);
        if (dist[v] < k) continue;
        for (int e = head[v]; e; e = nxt[e]) {
            const int w = to[e]; const ll nd = k + wt[e];
            if (nd < dist[w]) { dist[w] = nd; par[w] = v; sz++; sift_up(sz, (nd << 17) + w); }
        }
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int v = 1; v <= n; v++) printf("%lld\n", dist[v]);
}
