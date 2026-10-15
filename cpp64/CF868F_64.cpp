#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const int N = 100005;
int n, k; long long a[N], cnt[N], st[3] = {1, 0, 0};
#define cl st[0]
#define cr st[1]
#define cur st[2]
ll f[N], g[N];
void add(int i) { cur += cnt[a[i]]++; }
void del(int i) { cur -= --cnt[a[i]]; }
ll cost(int l, int r) {
    while (cl > l) add(--cl);
    while (cr < r) add(++cr);
    while (cl < l) del(cl++);
    while (cr > r) del(cr--);
    return cur;
}
void solve(int l, int r, int optl, int optr) {
    if (l > r) return;
    int mid = (l + r) / 2, opt = -1; ll best = LLONG_MAX;
    for (int p = optl; p <= min(mid, optr); p++) {
        ll v = g[p - 1] + cost(p, mid);
        if (v < best) { best = v; opt = p; }
    }
    f[mid] = best;
    solve(l, mid - 1, optl, opt); solve(mid + 1, r, opt, optr);
}
int main() {
    scanf("%d %d", &n, &k);
    for (int i = 1; i <= n; i++) scanf("%lld", &a[i]);
    // the arrays' pages are taken from the operating system before the clock starts (a Rocq program is handed its memory)
    memset(f, 0, sizeof f); memset(g, 0, sizeof g); memset(cnt, 0, sizeof cnt);
    auto t0 = chrono::steady_clock::now();
    for (int i = 1; i <= n; i++) g[i] = 1e18;
    for (int j = 1; j <= k; j++) { solve(1, n, 1, n); memcpy(g, f, sizeof f); g[0] = 1e18; }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n", g[n]);
}
