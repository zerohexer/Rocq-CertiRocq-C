// CF547B Mike and Feet -- bears in a row; for every size x, the largest "smallest bear" over all groups of x bears
// standing together.  For every bear the nearest smaller bear on each side (a stack); the bear is the smallest of the
// group between them.
#include <bits/stdc++.h>
using namespace std;
int main() {
    int n; scanf("%d", &n);
    vector<int> a(n + 2, 0), stk(n + 2, 0), L(n + 2, 0), R(n + 2, 0), ans(n + 2, 0);
    for (int i = 1; i <= n; i++) scanf("%d", &a[i]);
    auto t0 = chrono::steady_clock::now();
    int sp = 0;
    for (int i = 1; i <= n; i++) {
        while (sp > 0 && a[stk[sp - 1]] >= a[i]) sp--;
        L[i] = sp == 0 ? 0 : stk[sp - 1];
        stk[sp++] = i;
    }
    sp = 0;
    for (int i = n; i >= 1; i--) {
        while (sp > 0 && a[stk[sp - 1]] >= a[i]) sp--;
        R[i] = sp == 0 ? n + 1 : stk[sp - 1];
        stk[sp++] = i;
    }
    for (int i = 1; i <= n; i++) { int len = R[i] - L[i] - 1; ans[len] = max(ans[len], a[i]); }
    for (int x = n, best = 0; x >= 1; x--) { best = max(best, ans[x]); ans[x] = best; }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int x = 1; x <= n; x++) printf("%d\n", ans[x]);
}
