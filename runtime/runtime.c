#include <stdlib.h>
#include <stdio.h>

void TIG_printi(int n)
{
  printf("%d", n);
  fflush(stdout);
}

void TIG_print(char *s)
{
  fputs(s, stdout);
}

char* TIG_makestring(char *s)
{
  return s;
}

int* TIG_makeintarray(int n, int x)
{
  int *arr = calloc(n, 4);
  for (int i = 0; i < n; i ++) {
    arr[i] = x;
  }
  return arr;
}

void* TIG_makerecord(int n)
{
  return calloc(n, 8);
}

extern void TIG_main(void);

int main(int argc, char **argv)
{
  TIG_main();
  return 0;
}