// CF163A Substring and Subsequence -- the number of pairs (a substring of s, a subsequence of t) with the same
// letters, modulo 10^9 + 7.  A table filled row by row; two rows are kept.
#include <bits/stdc++.h>
using namespace std;
const int MOD = 1000000007;
static char S[5005], T[5005];
int main() {
    scanf("%s %s", S + 1, T + 1);
    int n = strlen(S + 1), m = strlen(T + 1);
    vector<int> prev(m + 1, 0), cur(m + 1, 0);
    auto t0 = chrono::steady_clock::now();
    int ans = 0;
    for (int i = 1; i <= n; i++) {
        int left = 0; const char c = S[i];
        for (int j = 1; j <= m; j++) {
            if (T[j] == c) { left += prev[j - 1] + 1; if (left >= MOD) left -= MOD; }
            cur[j] = left;
        }
        ans += left; if (ans >= MOD) ans -= MOD;
        swap(prev, cur);
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%d\n", ans);
}
