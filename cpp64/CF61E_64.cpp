// CF61E Enemy is weak -- the number of triples i < j < k with a[i] > a[j] > a[k].
// A binary indexed tree over the values, used twice (the values here are 1 .. n, each once).
// (the same program with every array of numbers 64 bits wide: the data layout the Rocq program is given)
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int n; vector<long long> t;
long long query(int i) { long long r = 0; for (; i > 0; i -= i & -i) r += t[i]; return r; }
void add(int i) { for (; i <= n; i += i & -i) t[i]++; }
int main() {
    scanf("%d", &n);
    vector<long long> a(n + 1), L(n + 1, 0);
    for (int i = 1; i <= n; i++) scanf("%lld", &a[i]);
    t.assign(n + 2, 0);
    auto t0 = chrono::steady_clock::now();
    for (int j = 1; j <= n; j++) { L[j] = j - 1 - query(a[j]); add(a[j]); }
    fill(t.begin(), t.end(), 0);
    ll ans = 0;
    for (int j = n; j >= 1; j--) { ans += (ll) L[j] * query(a[j] - 1); add(a[j]); }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n", ans);
}
