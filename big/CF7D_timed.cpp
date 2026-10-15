// CF7D Palindrome Degree -- the degree of a string is 0 when it is not a palindrome, else one more than the degree of
// its first half; the sum of the degrees of all the prefixes.  Two running hashes of the prefix, one read forwards
// and one backwards (the Rocq program uses the same two).
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll P = 1000000007, B = 131;
static char s[5000005];
int main() {
    scanf("%s", s + 1); int n = strlen(s + 1);
    vector<int> deg(n + 2, 0);
    auto t0 = chrono::steady_clock::now();
    ll h1 = 0, h2 = 0, pw = 1, acc = 0;
    for (int i = 1; i <= n; i++) {
        ll c = s[i];
        h1 = (h1 * B + c) % P;
        h2 = (h2 + c * pw) % P;
        pw = pw * B % P;
        int d = h1 == h2 ? deg[i >> 1] + 1 : 0;
        deg[i] = d; acc += d;
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n", acc);
}
