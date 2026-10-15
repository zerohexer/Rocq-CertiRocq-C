// CF622F The Sum of the k-th Powers -- 1^k + .. + n^k modulo 10^9+7: a polynomial of degree k+1 in n, by Lagrange's
// formula on the points 0 .. k+1.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll MOD = 1000000007;
ll mpow(ll b, ll e) { ll r = 1; b %= MOD; while (e) { if (e & 1) r = r * b % MOD; b = b * b % MOD; e >>= 1; } return r; }
int main() {
    ll n; int k; scanf("%lld %d", &n, &k);
    int m = k + 1;
    vector<ll> y(m + 1, 0), fact(m + 1), inv(m + 1), pre(m + 2), suf(m + 2);
    auto t0 = chrono::steady_clock::now();
    for (int i = 1; i <= m; i++) y[i] = (y[i - 1] + mpow(i, k)) % MOD;
    ll ans;
    if (n <= m) ans = y[n];
    else {
        fact[0] = 1; for (int i = 1; i <= m; i++) fact[i] = fact[i - 1] * i % MOD;
        inv[m] = mpow(fact[m], MOD - 2); for (int i = m; i >= 1; i--) inv[i - 1] = inv[i] * i % MOD;
        pre[0] = 1; for (int i = 1; i <= m; i++) pre[i] = pre[i - 1] * ((n - (i - 1)) % MOD) % MOD;
        suf[m] = 1; for (int i = m; i >= 1; i--) suf[i - 1] = suf[i] * ((n - i) % MOD) % MOD;
        ans = 0;
        for (int i = 0; i <= m; i++) {
            ll t = y[i] * pre[i] % MOD * suf[i] % MOD * (inv[i] * inv[m - i] % MOD) % MOD;
            if ((m - i) & 1) t = (MOD - t) % MOD;
            ans = (ans + t) % MOD;
        }
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n", ans);
}
