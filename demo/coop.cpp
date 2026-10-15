// coop.cpp -- the same two tasks and scheduler in C++, the way one writes them in C: each task a step function, its
// state in a struct, input and output through buffers.  For the answer and for the time.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
static char *ibuf; static long ilen, ipos; static string obuf;
static ll next_in() {
    while (ipos < ilen && ibuf[ipos] != '-' && (ibuf[ipos] < '0' || ibuf[ipos] > '9')) ipos++;
    if (ipos >= ilen) return -1;
    bool neg = false; if (ibuf[ipos] == '-') { neg = true; ipos++; }
    ll v = 0; while (ipos < ilen && ibuf[ipos] >= '0' && ibuf[ipos] <= '9') v = v * 10 + (ibuf[ipos++] - '0');
    return neg ? -v : v;
}
static void out(ll v) { char b[24]; obuf.append(b, sprintf(b, "%lld\n", v)); }
static ll ring[1024]; static ll head, tail_, doneA, doneB, sum, taken;
static void stepA() {
    if (doneA) return;
    if (tail_ - head == 1024) return;
    ll x = next_in();
    if (x < 0) { doneA = 1; return; }
    ring[tail_ & 1023] = x; tail_++;
}
static void stepB() {
    if (doneB) return;
    if (head == tail_) { if (doneA) { doneB = 1; out(sum); } return; }
    ll x = ring[head & 1023]; head++;
    sum = (sum * 31 + x) % 1000000007LL; taken++;
    if ((taken & 131071) == 0) out(sum);
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); fseek(f, 0, SEEK_END); ilen = ftell(f); fseek(f, 0, SEEK_SET);
    ibuf = (char *) malloc(ilen + 1); if (fread(ibuf, 1, ilen, f) != (size_t) ilen) return 1; fclose(f);
    auto t0 = chrono::steady_clock::now();
    for (;;) { stepA(); stepB(); if (doneA && doneB) break; }
    auto t1 = chrono::steady_clock::now(); fprintf(stderr, "C++ compute: %.3f ms\n", chrono::duration<double, milli>(t1 - t0).count());
    fwrite(obuf.data(), 1, obuf.size(), stdout);
}
