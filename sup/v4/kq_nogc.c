// kq_nogc.c -- a runtime WITHOUT a collector, in place of CertiRocq's gc_stack.c.
// Memory for the values a program builds is handed out in large pieces and never moved or taken back.  Because nothing
// ever moves, the generated code's bookkeeping for the collector (saving every live variable before a call, reloading
// it after) is not needed: strip_frames.py removes it, and the C compiler can then turn a loop's last call into a jump.
// Right for programs whose loops build nothing; a program that builds a value per round would grow without bound.
#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"
struct thread_info *make_tinfo(void) {
  struct thread_info *ti = calloc(1, sizeof(struct thread_info));
  if (!ti) { fprintf(stderr, "out of memory\n"); exit(1); }
  return ti;                                       /* alloc = limit = 0: the first request asks for a piece */
}
void garbage_collect(struct thread_info *ti) {
  uintnat chunk = (uintnat) 1 << 22;               /* 4M words = 32 MB */
  if (ti->nalloc + 16 > chunk) chunk = ti->nalloc + 16;
  value *p = malloc(chunk * sizeof(value));
  if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
  ti->alloc = p; ti->limit = p + chunk;
}
