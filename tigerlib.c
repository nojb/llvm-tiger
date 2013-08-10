#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void __tiger__print (char* s) 
{
  puts (s);
}

void __tiger__printi (int i)
{
  printf ("%d", i);
}

void __tiger__flush ()
{
  fflush (stdout);
}

char* __tiger__getchar (void)
{
  char* s;
  char c = getchar ();
  if (c == EOF) {
    s = malloc(1);
    s[0] = '\0';
    return s;
  }

  s = malloc(2);
  s[0] = c;
  s[1] = '\0';

  return s;
}

int __tiger__ord (char* s)
{
  return s[0] == '\0' ? -1 : (int) s[0];
}

char* __tiger__chr (int i)
{
  char* s;

  if (i < 0 || i >= 256) {
    fprintf (stderr, "chr: out of range\n");
    exit (2);
  }
  s = malloc (2);

  s[0] = (char) i;
  s[1] = '\0';

  return s;
}

int __tiger__size (char* s)
{
  return strlen (s);
}

char* __tiger__substring (char* s, int off, int len)
{
  char* s1 = malloc (len+1);
  strncpy (s1, &s[off], len+1);
  return s1;
}

char* __tiger__concat (char* s1, char* s2)
{
  char* s = malloc (strlen (s1) + strlen (s2) + 1); /* this should be replaced by GC_allocator */

  strcpy (s, s1);
  strcpy (&s[strlen(s1)], s2);

  return s;
}

int __tiger__not (int i)
{
  if (i) { return 0; };

  return 1;
}

void __tiger__exit (int i)
{
  exit (i);
}
