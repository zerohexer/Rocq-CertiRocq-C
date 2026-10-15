// CF35C Fire Again -- a forest of N x M trees, fire starts at K of them and reaches the four neighbours every minute.
// Printed here: the minute the last tree catches fire, and how many trees catch fire in that minute (which tree is
// "the last" is not unique).  A walk in the order of the minutes; the cells round the forest count as reached.
// (the same program with every array of numbers 64 bits wide: the data layout the Rocq program is given)
#include <bits/stdc++.h>
using namespace std;
int main() {
    int N, M, K; scanf("%d %d %d", &N, &M, &K);
    const int w = M + 2;
    vector<int> src(K);
    for (int i = 0; i < K; i++) { int r, c; scanf("%d %d", &r, &c); src[i] = r * w + c; }
    vector<long long> dist((size_t) (N + 2) * w, 0), q((size_t) N * M + 1, 0);
    auto t0 = chrono::steady_clock::now();
    for (int c = 0; c < w; c++) dist[c] = dist[(N + 1) * w + c] = 1;
    for (int r = 0; r < N + 2; r++) dist[r * w] = dist[r * w + w - 1] = 1;
    int qh = 0, qt = 0;
    for (int i = 0; i < K; i++) { dist[src[i]] = 1; q[qt++] = src[i]; }
    const int dir[4] = {-1, 1, -w, w};
    while (qh < qt) {
        long long c = q[qh++], d = dist[c] + 1;
        for (int k = 0; k < 4; k++) { long long x = c + dir[k]; if (!dist[x]) { dist[x] = d; q[qt++] = x; } }
    }
    long long dmax = dist[q[qt - 1]]; int cnt = 0;
    for (int i = qt - 1; i >= 0 && dist[q[i]] == dmax; i--) cnt++;
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%lld\n%d\n", dmax - 1, cnt);
}
