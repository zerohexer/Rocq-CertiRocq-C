// CF432D Prefixes and Suffixes -- every prefix that is also a suffix, with how often it occurs in the string.
// Printed here from the longest down, the count only (the Rocq program fills its answer block in that order).
#include <bits/stdc++.h>
using namespace std;
static char s[5000005];
int main() {
    scanf("%s", s); int n = strlen(s);
    vector<int> pi(n + 1, 0);
    vector<long long> cnt(n + 2, 0), out;
    out.reserve(n + 1);
    auto t0 = chrono::steady_clock::now();
    for (int i = 1; i < n; i++) {
        int k = pi[i - 1];
        while (k > 0 && s[i] != s[k]) k = pi[k - 1];
        if (s[i] == s[k]) k++;
        pi[i] = k;
    }
    for (int i = 0; i <= n; i++) cnt[i] = 1;
    for (int i = n; i >= 1; i--) { int p = pi[i - 1]; if (p > 0) cnt[p] += cnt[i]; }
    for (int len = n; len > 0; len = pi[len - 1]) out.push_back(cnt[len]);
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (long long c : out) printf("%lld\n", c);
}
