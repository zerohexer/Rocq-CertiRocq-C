// CF631E Product Sum -- move one element to any position to maximise the sum of a[i] * i.
// Lines y = j*x - S[j-1] (j = 1..n+1) have increasing slopes: upper envelope by a stack, then a binary search per element.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef __int128 lll;
int main() {
    int n; scanf("%d", &n);
    vector<ll> a(n + 2), S(n + 2, 0);
    for (int i = 1; i <= n; i++) scanf("%lld", &a[i]);
    vector<ll> K(n + 2, 0), B(n + 2, 0);              // the envelope: slope, intercept (t lines on it)
    auto t0 = chrono::steady_clock::now();
    ll base = 0;
    for (int i = 1; i <= n; i++) { S[i] = S[i - 1] + a[i]; base += a[i] * i; }
    int t = 0;
    for (int j = 1; j <= n + 1; j++) {
        ll k = j, b = -S[j - 1];
        while (t >= 2 && (lll)(b - B[t - 2]) * (K[t - 1] - K[t - 2]) >= (lll)(B[t - 1] - B[t - 2]) * (k - K[t - 2])) t--;
        K[t] = k; B[t] = b; t++;
    }
    ll best = 0;
    for (int i = 1; i <= n; i++) {
        ll x = a[i];
        int lo = 0, hi = t - 1;
        while (lo < hi) { int m = (lo + hi) / 2; if (K[m] * x + B[m] <= K[m + 1] * x + B[m + 1]) lo = m + 1; else hi = m; }
        best = max(best, K[lo] * x + B[lo] - (x * i - S[i - 1]));
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n", base + best);
}
