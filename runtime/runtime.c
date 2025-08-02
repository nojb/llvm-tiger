#include <stdio.h>

void TIG_printi(int n)
{
  printf("%d", n);
  fflush(stdout);
}

extern void TIG_main(void);

int main(int argc, char **argv)
{
  TIG_main();
  return 0;
}