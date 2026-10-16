/* examples/slab_set_malloc.c -- slab_set.body's set in C, with malloc and free, to compare (not linked with it):
   clang -O2 -o slab_set_c examples/slab_set_malloc.c && ./slab_set_c N */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
typedef struct node { long x; struct node *next; } node;
static node *table[65536];
static long bucket(long x) { return (x * 40503) & 65535; }
static long step(long x) { return (x * 1103515245 + 12345) & 2147483647; }
static void insert(long x) {
  long k = bucket(x);
  for (node *p = table[k]; p; p = p->next) if (p->x == x) return;
  node *e = malloc(sizeof *e); e->x = x; e->next = table[k]; table[k] = e;
}
static void remove_x(long x) {
  long k = bucket(x); node *prev = 0;
  for (node *p = table[k]; p; prev = p, p = p->next)
    if (p->x == x) { if (prev) prev->next = p->next; else table[k] = p->next; free(p); return; }
}
int main(int argc, char **argv) {
  long n = argc > 1 ? atol(argv[1]) : 1000;
  struct timespec a, b; clock_gettime(CLOCK_MONOTONIC, &a);
  long x = 7; for (long i = 0; i < n; i++) { insert(x & 1048575); x = step(x); }
  x = 7; for (long i = 0; i < n; i++) { long y = x & 1048575; if (y % 3 == 0) remove_x(y); x = step(x); }
  x = 99991; for (long i = 0; i < n / 2; i++) { insert(x & 1048575); x = step(x); }
  long len = 0, sum = 0;
  for (long k = 0; k < 65536; k++) for (node *p = table[k]; p; p = p->next) { len++; sum += p->x; }
  clock_gettime(CLOCK_MONOTONIC, &b);
  printf("slab_set_malloc.c: %ld entries, sum %ld   ran in %.2f ms\n", len, sum, (b.tv_sec - a.tv_sec) * 1e3 + (b.tv_nsec - a.tv_nsec) / 1e6);
  return 0;
}
