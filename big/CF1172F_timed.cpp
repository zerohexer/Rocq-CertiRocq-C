// CF1172F Nauuo and Bug -- sum a[l..r] with the buggy "if the sum is at least p, subtract p" after every addition.
// Per segment-tree node: c[x] = the smallest starting value for which p is subtracted at least x times inside the
// node.  Two children are merged with two pointers; a query walks its nodes from left to right with a binary search.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll INF = 1000000000000000000LL;
int n, q; ll p;
vector<ll> a, sum, pool;                              // pool: every node's array, one after the other
vector<int> off;
size_t top = 0;
void build(int o, int l, int r) {
    if (l == r) { sum[o] = a[l]; off[o] = top; pool[top] = -INF; pool[top + 1] = p - a[l]; pool[top + 2] = INF; top += 3; return; }
    int m = (l + r) / 2; build(2 * o, l, m); build(2 * o + 1, m + 1, r);
    sum[o] = sum[2 * o] + sum[2 * o + 1];
    const ll *L = &pool[off[2 * o]], *R = &pool[off[2 * o + 1]];
    int lenL = m - l + 1, lenR = r - m;
    off[o] = top; ll *C = &pool[top]; top += r - l + 3;
    C[0] = -INF; for (int i = 1; i <= r - l + 2; i++) C[i] = INF;
    ll sl = sum[2 * o];
    for (int x = 0, y = 0; x <= lenL; x++) {
        for (; y <= lenR; y++) {
            if (L[x + 1] - 1 + sl - (ll) x * p < R[y]) break;
            C[x + y] = min(C[x + y], max(L[x], R[y] + (ll) x * p - sl));
        }
        y--;
    }
}
ll query(int o, int l, int r, int ql, int qr, ll v) {
    if (qr < l || r < ql) return v;
    if (ql <= l && r <= qr) {
        const ll *C = &pool[off[o]];
        int k = int(upper_bound(C, C + (r - l + 2), v) - C) - 1;
        return v + sum[o] - (ll) k * p;
    }
    int m = (l + r) / 2;
    return query(2 * o + 1, m + 1, r, ql, qr, query(2 * o, l, m, ql, qr, v));
}
int main() {
    scanf("%d %d %lld", &n, &q, &p);
    a.resize(n + 1); for (int i = 1; i <= n; i++) scanf("%lld", &a[i]);
    vector<int> L(q), R(q); for (int i = 0; i < q; i++) scanf("%d %d", &L[i], &R[i]);
    sum.assign(4 * n + 8, 0); off.assign(4 * n + 8, 0); pool.assign(5500000, 0);
    vector<ll> ans(q);
    auto t0 = chrono::steady_clock::now();
    build(1, 1, n);
    for (int i = 0; i < q; i++) ans[i] = query(1, 1, n, L[i], R[i], 0);
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int i = 0; i < q; i++) printf("%lld\n", ans[i]);
}
