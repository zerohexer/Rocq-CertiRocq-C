static unsigned long long rep(int d, unsigned long long s) {
  if (d == 0) return (s * 1103515245ULL + 12345ULL) & 2147483647ULL;
  return rep(d - 1, rep(d - 1, s));
}
unsigned long long hand_lcg(void) { return rep(24, 1); }
unsigned long long hand_sumsq(unsigned long long k, unsigned long long i, unsigned long long a) {
  for (; k; k--, i++) a = (a + i * i) & 0x7fffffffffffffffULL;
  return a;
}
static unsigned long long arr[10000];
unsigned long long hand_sort(void) {
  unsigned long long s = 1;
  for (int i = 0; i < 10000; i++) { arr[i] = s & 1048575; s = (s * 1103515245ULL + 12345ULL) & 2147483647ULL; }
  for (int i = 1; i < 10000; i++) {
    unsigned long long key = arr[i]; int j = i;
    while (j > 0 && arr[j - 1] > key) { arr[j] = arr[j - 1]; j--; }
    arr[j] = key;
  }
  unsigned long long acc = 0;
  for (int i = 0; i < 10000; i++) acc = (acc + arr[i] * (unsigned long long)(i + 1)) & 0x7fffffffffffffffULL;
  return acc;
}
