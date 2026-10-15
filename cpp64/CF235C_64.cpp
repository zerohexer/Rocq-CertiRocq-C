// (the same program with every array of numbers 64 bits wide: the data layout the Rocq program is given)
// CF235C Cyclical Quest -- for every pattern x: how many substrings of s are a rotation of x.
// Suffix automaton of s with the number of occurrences of every state; a pattern of length m is walked twice round,
// and every state reached with at least m letters matched is counted once.
#include <bits/stdc++.h>
using namespace std;
static char s[1000005], x[1000005];
int main() {
    scanf("%s", s); int n = strlen(s);
    int q; scanf("%d", &q);
    vector<string> xs(q);
    for (int i = 0; i < q; i++) { scanf("%s", x); xs[i] = x; }
    int cap = 2 * n + 2;
    vector<array<long long, 26>> nxt(cap); vector<long long> link(cap, 0), len(cap, 0); vector<long long> cnt(cap, 0);
    for (auto &r : nxt) r.fill(0);
    vector<long long> bkt(n + 2, 0), ord(cap, 0), vis(cap, 0); vector<long long> ans(q);
    auto t0 = chrono::steady_clock::now();
    int sz = 1, last = 1;                                  // state 1 is the start; 0 means "none"
    for (int i = 0; i < n; i++) {
        int c = s[i] - 'a', cur = ++sz; len[cur] = len[last] + 1; cnt[cur] = 1;
        int p = last;
        while (p && !nxt[p][c]) { nxt[p][c] = cur; p = link[p]; }
        if (!p) link[cur] = 1;
        else {
            int qq = nxt[p][c];
            if (len[p] + 1 == len[qq]) link[cur] = qq;
            else {
                int cl = ++sz; len[cl] = len[p] + 1; nxt[cl] = nxt[qq]; link[cl] = link[qq];
                while (p && nxt[p][c] == qq) { nxt[p][c] = cl; p = link[p]; }
                link[qq] = cl; link[cur] = cl;
            }
        }
        last = cur;
    }
    for (int v = 1; v <= sz; v++) bkt[len[v]]++;
    for (int i = 1; i <= n; i++) bkt[i] += bkt[i - 1];
    for (int v = sz; v >= 1; v--) ord[--bkt[len[v]]] = v;
    for (int i = sz - 1; i >= 0; i--) { int v = ord[i]; cnt[link[v]] += cnt[v]; }
    for (int t = 0; t < q; t++) {
        const string &p = xs[t]; int m = p.size(), v = 1, l = 0; long long acc = 0;
        for (int i = 0; i < 2 * m - 1; i++) {
            int c = p[i % m] - 'a';
            while (v != 1 && !nxt[v][c]) { v = link[v]; l = len[v]; }
            if (nxt[v][c]) { v = nxt[v][c]; l++; } else { v = 1; l = 0; }
            while (len[link[v]] >= m) { v = link[v]; l = len[v]; }
            if (l >= m && vis[v] != t + 1) { vis[v] = t + 1; acc += cnt[v]; }
        }
        ans[t] = acc;
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int t = 0; t < q; t++) printf("%lld\n", ans[t]);
}
