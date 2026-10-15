// CF833B The Bakery -- split n cakes into k consecutive boxes, maximise the total number of distinct kinds per box.
// dp over the number of boxes; a segment tree with range add and range maximum over the start of the last box.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll NEG = -1000000000000000000LL;
int n, k;
vector<ll> mx, lz;
void build(int o, int l, int r, const vector<ll> &src) {
    lz[o] = 0;
    if (l == r) { mx[o] = src[l]; return; }
    int m = (l + r) / 2; build(2 * o, l, m, src); build(2 * o + 1, m + 1, r, src);
    mx[o] = max(mx[2 * o], mx[2 * o + 1]);
}
void push(int o) { if (lz[o]) { for (int c = 2 * o; c <= 2 * o + 1; c++) { mx[c] += lz[o]; lz[c] += lz[o]; } lz[o] = 0; } }
void add(int o, int l, int r, int a, int b, ll v) {
    if (b < l || r < a) return;
    if (a <= l && r <= b) { mx[o] += v; lz[o] += v; return; }
    push(o); int m = (l + r) / 2; add(2 * o, l, m, a, b, v); add(2 * o + 1, m + 1, r, a, b, v);
    mx[o] = max(mx[2 * o], mx[2 * o + 1]);
}
ll qmax(int o, int l, int r, int a, int b) {
    if (b < l || r < a) return NEG;
    if (a <= l && r <= b) return mx[o];
    push(o); int m = (l + r) / 2; return max(qmax(2 * o, l, m, a, b), qmax(2 * o + 1, m + 1, r, a, b));
}
int main() {
    scanf("%d %d", &n, &k);
    vector<int> a(n + 1), last(n + 1, 0), prv(n + 1);
    for (int i = 1; i <= n; i++) scanf("%d", &a[i]);
    mx.assign(4 * n + 8, 0); lz.assign(4 * n + 8, 0);
    vector<ll> prev(n + 1, NEG), cur(n + 1, NEG);
    auto t0 = chrono::steady_clock::now();
    for (int i = 1; i <= n; i++) { prv[i] = last[a[i]]; last[a[i]] = i; }
    prev[0] = 0;
    for (int j = 1; j <= k; j++) {
        build(1, 0, n - 1, prev);
        cur[0] = NEG;
        for (int i = 1; i <= n; i++) { add(1, 0, n - 1, prv[i], i - 1, 1); cur[i] = qmax(1, 0, n - 1, 0, i - 1); }
        swap(prev, cur);
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n", prev[n]);
}
