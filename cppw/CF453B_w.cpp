// CF453B -- the C++ WRITTEN THE WAY THE FAST ROCQ VERSION IS (hand/CF453B.body): in the innermost loop nothing is
// decided by a jump -- "does b fit" and "is this cheaper" choose the number that is written, and the cell is always
// written.  What separates this from the Rocq program is the language route only.
#include <bits/stdc++.h>
using namespace std;
const int INF = 1000000000, FULL = 1 << 17;
int main() {
    int n; scanf("%d", &n);
    vector<int> a(n); for (int i = 0; i < n; i++) scanf("%d", &a[i]);
    vector<int> dp((size_t)(n + 1) * FULL, 0);
    auto t0 = chrono::steady_clock::now();
    const int primes[17] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59};
    int mask[59];
    for (int b = 1; b <= 58; b++) { mask[b] = 0; for (int j = 0; j < 17; j++) if (b % primes[j] == 0) mask[b] |= 1 << j; }
    fill(dp.begin(), dp.end(), INF);
    dp[0] = 0;
    for (int i = 0; i < n; i++) {
        const int *cur = &dp[(size_t) i * FULL]; int *nxt = &dp[(size_t)(i + 1) * FULL]; const int ai = a[i];
        for (int m = 0; m < FULL; m++) {
            const int c = cur[m]; if (c >= INF) continue;
            for (int b = 1; b <= 58; b++) {
                const int mb = mask[b], cost = c + abs(ai - b); int &slot = nxt[m | mb];
                slot = ((m & mb) == 0 && cost < slot) ? cost : slot;
            }
        }
    }
    int best = INF;
    for (int m = 0; m < FULL; m++) best = min(best, dp[(size_t) n * FULL + m]);
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    printf("%d\n", best);
}
