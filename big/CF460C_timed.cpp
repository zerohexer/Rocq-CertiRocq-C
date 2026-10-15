// CF460C Present -- n flowers, m days, a watering makes w flowers in a row one higher; make the smallest flower as
// high as possible.  A binary search on the answer; one try walks the flowers once, watering where it must.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int n, w; ll m;
vector<int> a; vector<ll> d;
bool check(ll x) {
    ll add = 0, used = 0;
    for (int i = 1; i <= n; i++) {
        if (i > w) add -= d[i - w];
        ll need = x - a[i] - add, t = need > 0 ? need : 0;
        if (used + t > m) return false;
        d[i] = t; add += t; used += t;
    }
    return true;
}
int main() {
    scanf("%d %lld %d", &n, &m, &w);
    a.assign(n + 2, 0); d.assign(n + 2, 0);
    for (int i = 1; i <= n; i++) scanf("%d", &a[i]);
    auto t0 = chrono::steady_clock::now();
    ll lo = 2000000000LL;
    for (int i = 1; i <= n; i++) lo = min(lo, (ll) a[i]);
    ll hi = lo + m;
    while (lo < hi) { ll mid = (lo + hi + 1) >> 1; if (check(mid)) lo = mid; else hi = mid - 1; }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n", lo);
}
