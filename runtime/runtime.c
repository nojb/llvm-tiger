#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

struct FrameMap {
  int32_t NumRoots;
  int32_t NumMeta;
  const void *Meta[0];
};

struct StackEntry {
  struct StackEntry *Next;
  const struct FrameMap *Map;
  void *Roots[0];
};

extern struct StackEntry *llvm_gc_root_chain;

static void VisitGCRoots(void (*Visitor)(void **Root, const void *Meta, void *data), void *data)
{
  for (struct StackEntry *R = llvm_gc_root_chain; R; R = R->Next) {
    unsigned i = 0;

    // For roots [0, NumMeta), the metadata pointer is in the FrameMap.
    for (unsigned e = R->Map->NumMeta; i != e; ++i)
      Visitor(&R->Roots[i], R->Map->Meta[i], data);

    // For roots [NumMeta, NumRoots), the metadata pointer is null.
    for (unsigned e = R->Map->NumRoots; i != e; ++i)
      Visitor(&R->Roots[i], NULL, data);
  }
}

static void incr(void **Root, const void *Meta, void *count)
{
  int *c = (int *)count;
  ++*c;
}

static int CountGCRoots(void)
{
  int count = 0;
  VisitGCRoots(incr, &count);
  return count;
}

void TIG_printi(int n)
{
  printf("%d", n);
  fflush(stdout);
}

void TIG_print(char *s)
{
  fputs(s, stdout);
}

intptr_t* TIG_makearray(ssize_t n, intptr_t x)
{
  intptr_t *arr = calloc(n+1, sizeof(intptr_t));
  arr[0] = n;
  for (int i = 1; i <= n; i ++) {
    arr[i] = x;
  }
  return arr;
}

intptr_t* TIG_makerecord(ssize_t n)
{
  printf("# GC roots: %d\n", CountGCRoots()); fflush(stdout);
  return calloc(n, sizeof(intptr_t));
}

void TIG_nil_error(char *filename, intptr_t lineno, intptr_t column)
{
  fprintf(stderr, "%s:%ld:%ld: variable is nil\n", filename, lineno, column);
  fflush(stderr);
  exit(2);
}

void TIG_bounds_error(char *filename, intptr_t lineno, intptr_t column)
{
  fprintf(stderr, "%s:%ld:%ld: out of bounds\n", filename, lineno, column);
  fflush(stderr);
  exit(2);
}

extern void TIG_main(void);

int main(int argc, char **argv)
{
  TIG_main();
  return 0;
}