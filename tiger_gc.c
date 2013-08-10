/*===-- semispace.c - Simple semi-space copying garbage collector ---------===*\
|*
|*                     The LLVM Compiler Infrastructure
|*
|* This file was developed by the LLVM research group and is distributed under
|* the University of Illinois Open Source License. See LICENSE.TXT for details.
|* 
|*===----------------------------------------------------------------------===*|
|* 
|* This garbage collector is an extremely simple copying collector.  It splits
|* the managed region of memory into two pieces: the current space to allocate
|* from, and the copying space.  When the portion being allocated from fills up,
|* a garbage collection cycle happens, which copies all live blocks to the other
|* half of the managed space.
|*
\*===----------------------------------------------------------------------===*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* AllocPtr - This points to the next byte that is available for allocation.
 */
static char *AllocPtr;

/* AllocEnd - This points to the first byte not available for allocation.  When
 * AllocPtr passes this, we have run out of space.
 */
static char *AllocEnd;

/* CurSpace/OtherSpace - These pointers point to the two regions of memory that
 * we switch between.  The unallocated portion of the CurSpace is known to be
 * zero'd out, but the OtherSpace contains junk.
 */
static void *CurSpace, *OtherSpace;

/* SpaceSize - The size of each space. */
static unsigned SpaceSize;

/* llvm_gc_initialize - Allocate the two spaces that we plan to switch between.
 */
void llvm_gc_initialize(unsigned InitialHeapSize) {
  printf ("initializing gc with %d bytes\n", InitialHeapSize);
  SpaceSize = InitialHeapSize/2;
  CurSpace = AllocPtr = calloc(1, SpaceSize);
  OtherSpace = malloc(SpaceSize);
  AllocEnd = AllocPtr + SpaceSize;
}

/* We always want to inline the fast path, but never want to inline the slow
 * path.
 */
void *llvm_gc_allocate(unsigned Size) __attribute__((always_inline));
static void* llvm_gc_alloc_slow(unsigned Size) __attribute__((noinline));

/* GC */

typedef struct FrameMap {
  int32_t NumRoots;    //< Number of roots in stack frame.
  int32_t NumMeta;     //< Number of metadata entries. May be < NumRoots.
  const void *Meta[0]; //< Metadata for each root.
} FrameMap;

typedef struct StackEntry {
  struct StackEntry *Next;    //< Link to next stack entry (the caller's).
  const FrameMap *Map; //< Pointer to constant FrameMap.
  void *Roots[0];      //< Stack roots (in-place array).
} StackEntry;

StackEntry *llvm_gc_root_chain;

void visitGCRoots(void (*Visitor)(void **Root, const void *Meta)) {
  unsigned i;
  unsigned e;

  for (StackEntry *R = llvm_gc_root_chain; R; R = R->Next) {
    i = 0;

    // For roots [0, NumMeta), the metadata pointer is in the FrameMap.
    for (e = R->Map->NumMeta; i != e; ++i)
      Visitor(&R->Roots[i], R->Map->Meta[i]);
    
    // For roots [NumMeta, NumRoots), the metadata pointer is null.
    for (e = R->Map->NumRoots; i != e; ++i)
      Visitor(&R->Roots[i], NULL);
  }
}

static void process_pointer(void **Root, const void *Meta) {
  printf("process_root[0x%p] = 0x%p meta=%c\n", (void*) Root, (void*) *Root, * (char *) Meta);
}

void llvm_gc_collect() {
  // Clear out the space we will be copying into.
  // FIXME: This should do the copy, then clear out whatever space is left.
  memset(OtherSpace, 0, SpaceSize);

  printf("Garbage collecting!!\n");

  visitGCRoots (process_pointer);
}

void *llvm_gc_allocate(unsigned Size) {
  char *OldAP = AllocPtr;
  char *NewEnd = OldAP+Size;
  printf ("allocating %d bytes\n", Size);
  if (NewEnd > AllocEnd)
    return llvm_gc_alloc_slow(Size);
  AllocPtr = NewEnd;
  return OldAP;
}

static void* llvm_gc_alloc_slow(unsigned Size) {
  llvm_gc_collect();

  if (AllocPtr+Size > AllocEnd) {
    fprintf(stderr, "Garbage collector ran out of memory "
            "allocating object of size: %d\n", Size);
    exit(1);
  }

  return llvm_gc_allocate(Size);
}

#define INITIAL_HEAP_SIZE 10000

void __tiger__main (void);

int main (void)
{
  char* initial_heap_size = getenv ("TIGERHEAPSIZE");
  if (initial_heap_size != NULL) {
    llvm_gc_initialize (atoi (initial_heap_size));
  } else {
    llvm_gc_initialize (INITIAL_HEAP_SIZE);
  };

  __tiger__main ();

  return 0;
}
