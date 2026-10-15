// CF20C Dijkstra? -- shortest paths from vertex 1 in an undirected weighted graph.
// Printed here: the distance of every vertex (10^18 when it cannot be reached); a shortest path itself is not unique.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll INF = 1000000000000000000LL;
int main() {
    int n, m; scanf("%d %d", &n, &m);
    vector<int> eu(m), ev(m), ew(m);
    for (int i = 0; i < m; i++) scanf("%d %d %d", &eu[i], &ev[i], &ew[i]);
    vector<int> head(n + 1, -1), nxt(2 * m), to(2 * m), wt(2 * m), par(n + 1, 0);
    vector<ll> dist(n + 1, INF);
    vector<pair<ll, int>> room(2 * m + 2); room.clear();   // the heap's storage, taken before the clock starts
    priority_queue<pair<ll, int>, vector<pair<ll, int>>, greater<pair<ll, int>>> pq(greater<pair<ll, int>>(), std::move(room));
    auto t0 = chrono::steady_clock::now();
    for (int i = 0; i < m; i++) {
        to[2 * i] = ev[i]; wt[2 * i] = ew[i]; nxt[2 * i] = head[eu[i]]; head[eu[i]] = 2 * i;
        to[2 * i + 1] = eu[i]; wt[2 * i + 1] = ew[i]; nxt[2 * i + 1] = head[ev[i]]; head[ev[i]] = 2 * i + 1;
    }
    dist[1] = 0; pq.push({0, 1});
    while (!pq.empty()) {
        auto [d, v] = pq.top(); pq.pop();
        if (d > dist[v]) continue;
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int w = to[e]; ll nd = d + wt[e];
            if (nd < dist[w]) { dist[w] = nd; par[w] = v; pq.push({nd, w}); }
        }
    }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int v = 1; v <= n; v++) printf("%lld\n", dist[v]);
}
