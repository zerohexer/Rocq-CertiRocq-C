// CF295B Greg and Graph -- the vertices of a complete directed graph are taken away one by one; before each step,
// the sum of the shortest ways between all the vertices still there.  Backwards: the vertices come back one by one
// (Floyd and Warshall with the vertices in that order).
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
static int d[500][500];
int main() {
    int n; scanf("%d", &n);
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) scanf("%d", &d[i][j]);
    vector<int> x(n), in(n, 0); vector<ll> ans(n, 0);
    for (int i = 0; i < n; i++) { scanf("%d", &x[i]); x[i]--; }
    auto t0 = chrono::steady_clock::now();
    for (int k = n - 1; k >= 0; k--) {
        const int v = x[k]; in[v] = 1;
        for (int i = 0; i < n; i++) {
            const int dik = d[i][v];
            for (int j = 0; j < n; j++) d[i][j] = min(d[i][j], dik + d[v][j]);
        }
        ll sum = 0;
        for (int i = 0; i < n; i++) if (in[i]) for (int j = 0; j < n; j++) if (in[j]) sum += d[i][j];
        ans[k] = sum;
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int k = 0; k < n; k++) printf("%lld\n", ans[k]);
}
