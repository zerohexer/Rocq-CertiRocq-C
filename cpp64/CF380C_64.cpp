#include <bits/stdc++.h>
using namespace std;
struct Node { long long t, o, c; };
const int N = 1 << 20;
long long trT[2 * N], trO[2 * N], trC[2 * N]; char s[N];
Node merge(Node a, Node b) { long long m = min(a.o, b.c); return {a.t + b.t + 2 * m, a.o + b.o - m, a.c + b.c - m}; }
static inline Node node(int o) { return {trT[o], trO[o], trC[o]}; }
static inline void put(int o, Node x) { trT[o] = x.t; trO[o] = x.o; trC[o] = x.c; }
void build(int o, int l, int r) {
    if (l == r) { put(o, s[l] == '(' ? Node{0, 1, 0} : Node{0, 0, 1}); return; }
    int m = (l + r) / 2;
    build(2 * o, l, m); build(2 * o + 1, m + 1, r);
    put(o, merge(node(2 * o), node(2 * o + 1)));
}
Node query(int o, int l, int r, int ql, int qr) {
    if (qr < l || r < ql) return {0, 0, 0};
    if (ql <= l && r <= qr) return node(o);
    int m = (l + r) / 2;
    return merge(query(2 * o, l, m, ql, qr), query(2 * o + 1, m + 1, r, ql, qr));
}
int main() {
    scanf("%s", s + 1); int n = strlen(s + 1);
    int q; scanf("%d", &q);
    vector<int> L(q), R(q); vector<long long> A(q);
    for (int i = 0; i < q; i++) scanf("%d %d", &L[i], &R[i]);
    // the arrays' pages are taken from the operating system before the clock starts (a Rocq program is handed its memory)
    memset(trT, 0, sizeof trT); memset(trO, 0, sizeof trO); memset(trC, 0, sizeof trC);
    auto t0 = chrono::steady_clock::now();
    build(1, 1, n);
    for (int i = 0; i < q; i++) A[i] = query(1, 1, n, L[i], R[i]).t;
    auto t1 = chrono::steady_clock::now();
    fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int i = 0; i < q; i++) printf("%lld\n", A[i]);
}

