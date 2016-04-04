/*
 * EECS 322 Compiler Construction
 * Northwestern University
 *
 * L1 language runtime
 *
 * For proper GC behavior, L1 programs 
 * should adhere to the following constraints:
 * 1. immediately before each call to allocate(),
 *    the callee-save registers ebx/edi/esi
 *    should contain either a pointer value, or
 *    a numeric value x ENCODED as 2*x+1 (no
 *    unencoded numeric values!)
 * 2. similarly, immediately before a call to
 *    allocate(), the stack should not contain
 *    unencoded numeric values
 *
 */
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#define HEAP_SIZE 1048576    // one megabyte
//#define HEAP_SIZE 200      // small heap size for testing
//#define GC_DEBUG           // uncomment this to enable GC debugging
//#define GC_DUMP            // prints the entire heap before/after each gc

typedef struct {
   int64_t *allocptr;           // current allocation position
   int64_t words_allocated;
   void **data;
   char *valid;
} heap_t;

heap_t heap;      // the current heap
heap_t heap2;     // the heap for copying

int64_t *stack; // pointer to the bottom of the stack (i.e. value
                // upon program startup)

/*
 * Helper for the print() function
 */
void print_content(int64_t *in, int depth) {
   if(depth >= 4) {
     printf("...");
     return;
   }
   // NOTE: this function crashes quite messily if "in" is 0
   // so we've added this check
   if(in == NULL) {
     printf("nil");
     return;
   }
   int64_t x = (int64_t)in;
   if(x & 1) {
     printf("%" PRId64, x >> 1);
   } else {
     int64_t size = *((int64_t*)in);
     int64_t *data = in + 1;
     int i;
     printf("{s:%" PRId64, size);
     for(i = 0; i < size; i++) {
       printf(", ");
       print_content((int64_t *)(*data), depth + 1);
       data++;
     }
     printf("}");
     // check for bad pointers
     if (size==-1) {
       printf("\nfound -1 in an array; internal GC failure\n");
       exit(-1);
     }
   }
}

/*
 * Runtime "print" function
 */
int64_t print(void *l) {
   print_content(l, 0);
   printf("\n");

   return 1;
}

void reset_heap(heap_t *h) {
   h->allocptr = (int64_t*)h->data;
   h->words_allocated = 0;
}

int alloc_heap(heap_t *h) {
   h->data = (void*)malloc(HEAP_SIZE * sizeof(void*));
   h->valid = (void*)malloc(HEAP_SIZE * sizeof(char));
   reset_heap(h);
   return (h->data != NULL && h->valid != NULL);
}

void switch_heaps() {
   int64_t *temp_allocptr = heap.allocptr;
   int temp_words_allocated = heap.words_allocated;
   void **temp_data = heap.data;
   char *temp_valid = heap.valid;

   heap.allocptr = heap2.allocptr;
   heap.words_allocated = heap2.words_allocated;
   heap.data = heap2.data;
   heap.valid = heap2.valid;

   heap2.allocptr = temp_allocptr;
   heap2.words_allocated = temp_words_allocated;
   heap2.data = temp_data;
   heap2.valid = temp_valid;

   reset_heap(&heap);
}

/*
 * Helper for the gc() function.
 * Copies (compacts) an object from the old heap into
 * the empty heap
 */
int64_t *gc_copy(int64_t *old)  {
   int i, size, array_size;
   int64_t *old_array, *new_array, *first_array_location;
   int valid_index;
   char is_valid;
   char *valid;

   // If not a pointer or not a pointer to a heap location, return input value
   if((int64_t)old % 8 != 0 ||
      (void**)old < heap2.data ||
      (void**)old >= heap2.data + heap2.words_allocated) {
      return old;
   }
   
   // if not pointing at a valid heap object, return input value
   valid_index = (int64_t)((void**)old - heap2.data);
   is_valid = heap2.valid[valid_index];
   if(!is_valid) {
      return old;
   }

   old_array = (int64_t*)old;
   size = old_array[0];
   array_size = size + 1;

   // If the size is negative, the array has already been copied to the
   // new heap, so the first location of array will contain the new address
   if(size == -1) {
       return (int64_t*)old_array[1];
   }
   // If the size is zero, we still have one word of data to copy to the
   // new heap
   else if(size == 0) {
       array_size = 2;
   }

#ifdef GC_DEBUG
   // printf("gc_copy(): valid=%d old=%p new=%p: size=%d asize=%d total=%d\n", is_valid, old, heap.allocptr, size, array_size, heap.words_allocated);
#endif

   valid = heap.valid + heap.words_allocated;

   // Mark the old array as invalid, create the new array
   old_array[0] = -1;
   new_array = heap.allocptr;
   heap.allocptr += array_size;
   heap.words_allocated += array_size;

   // The value of old_array[1] needs to be handled specially
   // since it holds a pointer to the new heap object
   first_array_location = (int64_t*)old_array[1];
   old_array[1] = (int64_t)new_array;

   // Set the values of new_array handling the first two locations separately
   new_array[0] = size;
   new_array[1] = (int64_t)gc_copy(first_array_location);

   valid[0] = 1;
   valid[1] = 0;

   // Call gc_copy on the remaining values of the array
   for (i = 2; i < array_size; i++) {
      new_array[i] = (int64_t)gc_copy((int64_t*)old_array[i]);
      valid[i] = 0;
   }

   return new_array;
}

/*
 * Initiates garbage collection
 */
void gc(int64_t *rsp) {
   int i;
   int stack_size = stack - rsp + 1;       // calculate the stack size
#ifdef GC_DEBUG
   int prev_words_alloc = heap.words_allocated;

   printf("GC: stack=(%p,%p) (size %d): ", rsp, stack, stack_size);

#ifdef GC_DUMP
   printf("\n(");
   for (i=0;i<HEAP_SIZE;i++) {
     if (i != 0) printf (" ");
     printf("(%p %p)\n",&(heap.data[i]),heap.data[i]);
   }
   printf(")\n");
#endif
#endif

   // swap in the empty heap to use for storing
   // compacted objects
   switch_heaps();

   // NOTE: the edi/esi register contents could also be
   // roots, but these have been placed in the stack
   // by the allocate() assembly function.  Thus,
   // we only need to look at the stack at this point

   // Then, we need to copy anything pointed at
   // by the stack into our empty heap
   for(i = 0; i < stack_size; i++) {
      rsp[i] = (int64_t)gc_copy((int64_t*)rsp[i]);
   }

#ifdef GC_DEBUG
   printf("reclaimed %d words\n", (prev_words_alloc - heap.words_allocated));
#ifdef GC_DUMP
   printf("(");
   for (i=0;i<HEAP_SIZE;i++) {
     if (i != 0) printf (" ");
     printf("(%p %p)\n",&(heap.data[i]),heap.data[i]);
   }
   printf(")");
#endif
#endif
}

/*
 * The "allocate" runtime function
 * (assembly stub that calls the 3-argument
 * allocate_helper function)
 */
extern void* allocate(int64_t fw_size, int64_t *fw_fill);
asm(
   ".globl allocate\n"
   //   ".type allocate, @function\n"
   "allocate:\n"
   "# grab the arguments (into rax,rdx)\n"
   "subq   $48, %rsp\n"
   "movq   %rsp, %rdx\n"    // set up third argument to allocate_helper
   "movq   %rbx,(%rsp)\n"
   "movq   %rbp,8(%rsp)\n"
   "movq   %r12,16(%rsp)\n"
   "movq   %r13,24(%rsp)\n"
   "movq   %r14,32(%rsp)\n"
   "movq   %r15,40(%rsp)\n"
   "call allocate_helper\n" // make the call
   "movq   (%rsp),%rbx\n"
   "movq   8(%rsp),%rbp\n"
   "movq   16(%rsp),%r12\n"
   "movq   24(%rsp),%r13\n"
   "movq   32(%rsp),%r14\n"
   "movq   40(%rsp),%r15\n"
   "addq   $48, %rsp\n"
   "retq\n"
   /*
   "popq %rcx\n" // return val
   "popq %rax\n" // arg 1
   "popq %rdx\n" // arg 2
   "# put the original edi/esi on stack instead of args\n"
   "pushl %edi\n" // formerly edx
   "pushl %esi\n" // formerly eax
   "pushl %ebx\n" // formerly return addr  <-- this is the ESP we want
   "pushl %ecx\n" // ecx (return val)
   "pushl %eax\n" // eax (arg 1)
   "pushl %edx\n" // edx (arg 2)
   "# save the original esp (into ecx)\n"
   "movl %esp, %ecx\n"
   "addl $12, %ecx\n"
   "\n"
   "# save the caller's base pointer (so that LEAVE works)\n"
   "# body begins with base and\n"
   "# stack pointers equal\n"
   "pushl %ebp\n"
   "movl %esp, %ebp\n"
   "# push the first three args on stack\n"
   "pushl %ecx\n"
   "pushl %edx\n"
   "pushl %eax\n"
   "# call the real alloc\n"
   "call allocate_helper\n"
   "addl $12, %esp\n"
   "\n"
   "# restore the original base pointer (from stack)\n"
   "leave\n"
   "# restore esi/edi from stack\n"
   "popl %edx\n"  // arg 2
   "popl %ecx\n"  // arg 1
   "addl $4, %esp\n" // skip over return val (it hasn't changed)
   "popl %ebx\n"  // restore ebx
   "popl %esi\n"  // restore esi
   "popl %edi\n"  // restore edi
   "pushl %edx\n" // put back arg 2
   "pushl %ecx\n" // put back arg 1
   "subl $8, %esp\n" // skip over old ebx
   "popl %edx\n"  // original return addr
   "popl %ecx\n"  // junk
   "pushl %edx\n"  // restore return addr
   "ret\n" 
   */
);

/*
 * The real "allocate" runtime function
 * (called by the above assembly stub function)
 */
void* allocate_helper(int64_t fw_size, int64_t *fw_fill, int64_t *rsp)
{
   int i, data_size, array_size;
   char *valid;
   int64_t *ret;

   if(!(fw_size & 1)) {
      printf("allocate called with size input that was not an encoded integer, %" 
	     PRId64
	     "\n",
             fw_size);
      exit(-1);
   }

   data_size = fw_size >> 1;

   if(data_size < 0) {
      printf("allocate called with size of %i\n", data_size);
      exit(-1);
   }

#ifdef GC_DEBUG
   //printf("runtime.c: allocate(%d,%d (%p)) @ %p: ESP = %p (%d), EDI = %p (%d), ESI = %p (%d), EBX = %p (%d)\n",
   //       data_size, (int)fw_fill, fw_fill, heap.allocptr, esp, (int)esp, (int*)esp[2], esp[2], (int*)esp[1], esp[1], (int*)esp[0], esp[0]);
   //fflush(stdout);
#endif

   // Even if there is no data, allocate an array of two words
   // so we can hold a forwarding pointer and an int representing if
   // the array has already been garbage collected
   array_size = (data_size == 0) ? 2 : data_size + 1;



   // Check if the heap has space for the allocation
   if(heap.words_allocated + array_size >= HEAP_SIZE)
   {
      // Garbage collect
      gc(rsp);
      // get correct value of fw_fill
      fw_fill=gc_copy(fw_fill);

      // Check if the garbage collection free enough space for the allocation
      if(heap.words_allocated + array_size >= HEAP_SIZE) {
         printf("out of memory\n");
         exit(-1);
      }
   }

   // Do the allocation
   ret = heap.allocptr;
   valid = heap.valid + heap.words_allocated;
   heap.allocptr += array_size;
   heap.words_allocated += array_size;

   // Set the size of the array to be the desired size
   ret[0] = data_size;

   // record this as a heap object
   valid[0] = 1;

   // If there is no data, set the value of the array to be a number
   // so it can be properly garbage collected
   if(data_size == 0) {
      ret[1] = 1;
      valid[1] = 0;
      //printf(" set %p to 1\n", &ret[1]);
      //fflush(stdout);
   } else {
      // Fill the array with the fill value
      for(i = 1; i < array_size; i++) {
         ret[i] = (int64_t)fw_fill;
         valid[i] = 0;
         //printf(" set %p to %d (%p)", &ret[i], fw_fill, fw_fill);
      }
      //printf("\n");
      //fflush(stdout);
   }

   return ret;
}

/*
 * The "array-error" runtime function
 */
int array_error(int64_t *array, int64_t fw_x) {
   printf("attempted to use position %" PRId64
	  " in an array that only has %" PRId64
	  " position",
          fw_x >> 1, *array);
   if (*array != 1) printf("s");
   printf("\n");
   exit(0);
}

/*
 * Program entry-point
 */
int main() {
   int b1 = alloc_heap(&heap);
   int b2 = alloc_heap(&heap2);
   if(!b1 || !b2) {
      printf("malloc failed\n");
      exit(-1);
   }

   // Move esp into the bottom-of-stack pointer.
   // The "go" function's boilerplate, in conjunction
   // with the C calling convention dictates that 
   // we need 7 words to be added to the stack
   // before the body of "go" actually happens
   asm ("movq %%rsp, %%rax;"
        "subq $56, %%rax;" // 7 * 8
        "movq %%rax, %0;"
        "movq $1, %%rbx;"
        "movq $3, %%rdi;"
        "movq $5, %%rsi;"
        "call go;"
      : "=m"(stack) // outputs
      :             // inputs (none)
      : "%rax", "%rbx", "%rdi", "%rsi" // clobbered registers (eax)
   );  

#ifdef GC_DEBUG
   printf("runtime.c: main(): initial ESP value = %p (%" PRId64 ")\n", stack, (int64_t)stack);
#endif

   return 0;
}
