#include <bits/stdc++.h>
using namespace std;
int main() {
    int n; scanf("%d", &n);
    vector<long long> cnt(100001, 0), dp(100001, 0);
    vector<int> a(n); for (int i = 0; i < n; i++) scanf("%d", &a[i]);
    auto t0 = chrono::steady_clock::now();
    for (int i = 0; i < n; i++) cnt[a[i]]++;
    dp[1] = cnt[1];
    for (int x = 2; x <= 100000; x++) dp[x] = max(dp[x - 1], dp[x - 2] + cnt[x] * x);
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n", dp[100000]);
}
