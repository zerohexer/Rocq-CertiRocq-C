// CF17E Palisection -- the number of pairs of palindromic substrings that share a position, modulo 51123987.
// Manacher, then: all pairs minus the pairs where one palindrome ends before the other starts.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll MOD = 51123987;
static char s[2000005];
int main() {
    int n; scanf("%d %s", &n, s);
    vector<int> d1(n), d2(n);
    vector<ll> st(n + 2, 0), en(n + 2, 0);            // how many palindromes start / end at each position (as differences)
    auto t0 = chrono::steady_clock::now();
    for (int i = 0, l = 0, r = -1; i < n; i++) {
        int k = i > r ? 1 : min(d1[l + r - i], r - i + 1);
        while (i - k >= 0 && i + k < n && s[i - k] == s[i + k]) k++;
        d1[i] = k; if (i + k - 1 > r) { l = i - k + 1; r = i + k - 1; }
    }
    for (int i = 0, l = 0, r = -1; i < n; i++) {
        int k = i > r ? 0 : min(d2[l + r - i + 1], r - i + 1);
        while (i - k - 1 >= 0 && i + k < n && s[i - k - 1] == s[i + k]) k++;
        d2[i] = k; if (i + k - 1 > r) { l = i - k; r = i + k - 1; }
    }
    for (int i = 0; i < n; i++) {
        st[i - d1[i] + 1]++; st[i + 1]--; en[i]++; en[i + d1[i]]--;
        st[i - d2[i]]++; st[i]--; en[i]++; en[i + d2[i]]--;
    }
    ll tot = 0, non = 0, ends_before = 0, cs = 0, ce = 0;
    for (int i = 0; i < n; i++) {
        cs += st[i]; tot += cs;
        non = (non + (cs % MOD) * ends_before) % MOD;
        ce += en[i]; ends_before = (ends_before + ce) % MOD;
    }
    ll pairs = tot % 2 == 0 ? ((tot / 2) % MOD) * ((tot - 1) % MOD) % MOD : (tot % MOD) * (((tot - 1) / 2) % MOD) % MOD;
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n", ((pairs - non) % MOD + MOD) % MOD);
}
