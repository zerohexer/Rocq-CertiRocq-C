// CF813F Bipartite Checking -- edges are switched on and off; after every query: is the graph bipartite?
// Offline: the queries are sorted by edge, which pairs every switching-on with its switching-off; every edge then
// lives on an interval of time; intervals are hung on a segment tree over time, and a walk of the tree keeps a
// union-find with parities that can undo its unions.  Arrays only: nothing is taken from the operating system while
// the clock runs.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int n, q, nrec = 0, top = 0;
vector<int> nh, ru, rv, rn, P, RK, PX, sta, stb, ans, qx, qy;   // nh: a node's first record; ru rv rn: a record's edge and the next record
void add(int o, int l, int r, int a, int b, int u, int v) {
    if (b < l || r < a) return;
    if (a <= l && r <= b) { int c = ++nrec; ru[c] = u; rv[c] = v; rn[c] = nh[o]; nh[o] = c; return; }
    int m = (l + r) / 2; add(2 * o, l, m, a, b, u, v); add(2 * o + 1, m + 1, r, a, b, u, v);
}
void dfs(int o, int l, int r) {
    int mark = top; bool ok = true;
    for (int e = nh[o]; e; e = rn[e]) {
        int u = ru[e], v = rv[e], pu = 0, pv = 0;
        while (P[u] != u) { pu ^= PX[u]; u = P[u]; }
        while (P[v] != v) { pv ^= PX[v]; v = P[v]; }
        if (u == v) { if (pu == pv) { ok = false; break; } continue; }
        int rs = u, rb = v;                                // rs goes under rb
        if (!(RK[u] < RK[v])) { rs = v; rb = u; }
        P[rs] = rb; PX[rs] = pu ^ pv ^ 1;
        int grew = RK[rs] == RK[rb]; RK[rb] += grew;
        sta[top] = rs; stb[top] = grew; top++;
    }
    if (ok) {
        if (l == r) ans[l] = 1;
        else { int m = (l + r) / 2; dfs(2 * o, l, m); dfs(2 * o + 1, m + 1, r); }
    }
    while (top > mark) { top--; int rs = sta[top], rb = P[rs]; RK[rb] -= stb[top]; P[rs] = rs; PX[rs] = 0; }
}
int main() {
    scanf("%d %d", &n, &q);
    qx.assign(q + 2, 0); qy.assign(q + 2, 0);
    for (int i = 1; i <= q; i++) scanf("%d %d", &qx[i], &qy[i]);
    const int R = 3600000;                                 // room for the records: an interval hangs on at most 34 nodes
    vector<ll> key(q, 0);
    nh.assign(4 * q + 8, 0); ru.assign(R, 0); rv.assign(R, 0); rn.assign(R, 0);
    P.assign(n + 2, 0); RK.assign(n + 2, 0); PX.assign(n + 2, 0); sta.assign(n + 2, 0); stb.assign(n + 2, 0); ans.assign(q + 2, 0);
    auto t0 = chrono::steady_clock::now();
    for (int i = 1; i <= q; i++) key[i - 1] = (((ll) qx[i] * (n + 1) + qy[i]) << 17) | i;   // by edge, then by time
    sort(key.begin(), key.end());
    for (int p = 0; p < q; ) {
        int on = int(key[p] & 131071);
        if (p + 1 < q && (key[p] >> 17) == (key[p + 1] >> 17)) { add(1, 1, q, on, int(key[p + 1] & 131071) - 1, qx[on], qy[on]); p += 2; }
        else { add(1, 1, q, on, q, qx[on], qy[on]); p += 1; }
    }
    for (int v = 1; v <= n; v++) P[v] = v;
    dfs(1, 1, q);
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int i = 1; i <= q; i++) printf("%d\n", ans[i]);
}
