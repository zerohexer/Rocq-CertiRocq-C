// CF1167C News Distribution -- the users of a group pass the news on to each other; for every user, how many users
// end up knowing it.  A union-find with sizes; a walk to the root halves the way behind it.
#include <bits/stdc++.h>
using namespace std;
vector<int> P, SZ;
int find(int v) { while (P[v] != v) { P[v] = P[P[v]]; v = P[v]; } return v; }
void unite(int a, int b) {
    a = find(a); b = find(b);
    if (a == b) return;
    if (SZ[a] < SZ[b]) swap(a, b);
    P[b] = a; SZ[a] += SZ[b];
}
int main() {
    int n, m; scanf("%d %d", &n, &m);
    vector<int> g, gs(m + 1, 0);
    for (int i = 0; i < m; i++) {
        int k; scanf("%d", &k);
        for (int j = 0; j < k; j++) { int u; scanf("%d", &u); g.push_back(u); }
        gs[i + 1] = (int) g.size();
    }
    P.assign(n + 2, 0); SZ.assign(n + 2, 0);
    vector<int> ans(n + 2, 0);
    auto t0 = chrono::steady_clock::now();
    for (int v = 1; v <= n; v++) { P[v] = v; SZ[v] = 1; }
    for (int i = 0; i < m; i++)
        for (int j = gs[i] + 1; j < gs[i + 1]; j++) unite(g[gs[i]], g[j]);
    for (int v = 1; v <= n; v++) ans[v] = SZ[find(v)];
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int v = 1; v <= n; v++) printf("%d\n", ans[v]);
}
