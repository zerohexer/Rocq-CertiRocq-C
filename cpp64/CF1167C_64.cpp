// CF1167C News Distribution -- the users of a group pass the news on to each other; for every user, how many users
// end up knowing it.  A union-find with sizes; a walk to the root halves the way behind it.
// (the same program with every array of numbers 64 bits wide: the data layout the Rocq program is given)
#include <bits/stdc++.h>
using namespace std;
vector<long long> P, SZ;
long long find(long long v) { while (P[v] != v) { P[v] = P[P[v]]; v = P[v]; } return v; }
void unite(long long a, long long b) {
    a = find(a); b = find(b);
    if (a == b) return;
    if (SZ[a] < SZ[b]) swap(a, b);
    P[b] = a; SZ[a] += SZ[b];
}
int main() {
    int n, m; scanf("%d %d", &n, &m);
    vector<long long> g, gs(m + 1, 0);
    for (int i = 0; i < m; i++) {
        int k; scanf("%d", &k);
        for (int j = 0; j < k; j++) { int u; scanf("%d", &u); g.push_back(u); }
        gs[i + 1] = (int) g.size();
    }
    P.assign(n + 2, 0); SZ.assign(n + 2, 0);
    vector<long long> ans(n + 2, 0);
    auto t0 = chrono::steady_clock::now();
    for (int v = 1; v <= n; v++) { P[v] = v; SZ[v] = 1; }
    for (int i = 0; i < m; i++)
        for (int j = gs[i] + 1; j < gs[i + 1]; j++) unite(g[gs[i]], g[j]);
    for (int v = 1; v <= n; v++) ans[v] = SZ[find(v)];
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int v = 1; v <= n; v++) printf("%lld\n", ans[v]);
}
