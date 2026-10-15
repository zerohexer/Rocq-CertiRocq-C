// CF1039D You Are Given a Tree -- for every k from 1 to n, the largest number of vertex-disjoint paths of k vertices.
// One greedy pass (deepest vertices first) answers one k; the answer never grows with k, so a range of k whose two
// ends have the same answer is filled without looking inside.
#include <bits/stdc++.h>
using namespace std;
int n;
vector<int> ord, par, t1, t2, ans;
int greedy(int k) {
    for (int v = 0; v <= n; v++) t1[v] = t2[v] = 0;
    int cnt = 0;
    for (int i = n - 1; i >= 0; i--) {
        int v = ord[i], a = t1[v], b = t2[v];
        if (a + b + 1 >= k) cnt++;
        else { int p = par[v], len = a + 1; if (t1[p] < len) { t2[p] = t1[p]; t1[p] = len; } else if (t2[p] < len) t2[p] = len; }
    }
    return cnt;
}
void dc(int l, int r, int al, int ar) {
    if (l > r) return;
    if (al == ar) { for (int i = l; i <= r; i++) ans[i] = al; return; }
    int mid = (l + r) / 2, g = greedy(mid);
    ans[mid] = g;
    dc(l, mid - 1, al, g); dc(mid + 1, r, g, ar);
}
int main() {
    scanf("%d", &n);
    vector<int> eu(n - 1), ev(n - 1);
    for (int i = 0; i < n - 1; i++) scanf("%d %d", &eu[i], &ev[i]);
    vector<int> head(n + 1, -1), nxt(2 * n), to(2 * n);
    ord.assign(n, 0); par.assign(n + 1, 0); t1.assign(n + 1, 0); t2.assign(n + 1, 0); ans.assign(n + 2, 0);
    auto t0 = chrono::steady_clock::now();
    for (int i = 0; i < n - 1; i++) {
        to[2 * i] = ev[i]; nxt[2 * i] = head[eu[i]]; head[eu[i]] = 2 * i;
        to[2 * i + 1] = eu[i]; nxt[2 * i + 1] = head[ev[i]]; head[ev[i]] = 2 * i + 1;
    }
    int cntq = 1; ord[0] = 1; par[1] = 0;
    for (int qi = 0; qi < n; qi++) {
        int v = ord[qi];
        for (int e = head[v]; e != -1; e = nxt[e]) if (to[e] != par[v]) { par[to[e]] = v; ord[cntq++] = to[e]; }
    }
    dc(1, n, n, 0);
    auto tt = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(tt - t0).count());
    for (int k = 1; k <= n; k++) printf("%d\n", ans[k]);
}
