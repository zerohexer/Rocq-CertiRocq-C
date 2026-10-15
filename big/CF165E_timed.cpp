// CF165E Compatible Numbers -- for every number of the list, another number of the list that shares no bit with it
// (or -1).  A table over all sets of 22 bits, filled bit by bit: cell m holds one of the numbers whose bits all lie
// inside m.  (Which number is given is fixed by the order of the filling; the Rocq program fills in the same order.)
#include <bits/stdc++.h>
using namespace std;
const int FULL = 1 << 22;
static int f[FULL];
int main() {
    int n; scanf("%d", &n);
    vector<int> a(n), ans(n);
    for (int i = 0; i < n; i++) scanf("%d", &a[i]);
    // the table's pages are taken from the operating system before the clock starts (a Rocq program is handed its memory)
    memset(f, 0, sizeof f);
    auto t0 = chrono::steady_clock::now();
    for (int i = 0; i < n; i++) f[a[i]] = a[i];
    for (int bit = 1; bit < FULL; bit <<= 1)
        for (int m = 0; m < FULL; m++)
            if ((m & bit) && !f[m]) f[m] = f[m ^ bit];
    for (int i = 0; i < n; i++) { int x = f[(FULL - 1) ^ a[i]]; ans[i] = x ? x : -1; }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    for (int i = 0; i < n; i++) printf("%d\n", ans[i]);
}
