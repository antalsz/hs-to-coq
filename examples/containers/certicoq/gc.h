#include "values.h"

/* EXPLANATION OF THE CERTICOQ GENERATIONAL GARBAGE COLLECTOR.
 Andrew W. Appel, September 2016

The current Certicoq code generator uses Ocaml object formats,
as described in Chapter 20 of Real World Ocaml by Minsky et al.
https://realworldocaml.org/v1/en/html/memory-representation-of-values.html

That is:

       31   10 9       8 7        0
      +-------+---------+----------+
      | size  |  color  | tag byte |
      +-------+---------+----------+
v --> |              value[0]      |
      +----------------------------+
      |              value[1]      |
      +----------------------------+
      |                   .        |
      |                   .        |
      |                   .        |
      +----------------------------+
      |           value[size-1]    |
      +----------------------------+

This works for 32-bit or 64-bit words;
if 64-bit words, substitute "63" for "31" in the diagram above.
At present we'll assume 32-bit words.

The header file "values.h", from the OCaml distribution,
has macros (etc.) for accessing these fields and headers.

The header file "config.h", from the OCaml distribution, defines
typedef "intnat", the "natural integer type" for this compiler/machine,
and "uintnat", the "natural unsigned integer type".
Config.h also defines (BUT WE DO NOT USE) parameters for the Ocaml
generational garbage collector.

The important definitions we use from values.h are:

Is_block(v) : tests whether v is a pointer (even number)
Hd_val(v)   : contents of the header word, i.e., just before where v points to
Field(v,i)  : the i'th field of object v
Tag_hd(h)   : If h is a header-word, get the constructor-tag
Wosize_hd(h): If h is a header-word, get size of the object in words

We define the following ourselves, following Ocaml's format:

No_scan(t)  : If t is a constructor-tag, true if none of the object's
              data words are to be interpreted as pointers.
	      (For example, character-string data)

CALLING THE GARBAGE COLLECTOR (this part is NOT standard Ocaml):

The mutator runs in this environment:

                                 NURSERY              OLDER GENERATIONS
      +-------------+  start---->+-------------+      +-------------+
      |    args[0]  |            |             |      |             |
      +-------------+            | <-\         |  /-->|             |
      |    args[1] *----\        |   |       *---/    |             |
      +-------------+    \-----> | *-/         |      |             |
      |      .      |       +-+  |             |      |             |
      |      .      |  alloc|*-->+-------------+      |             |
      |      .      |       +-+  |             |      |             |
      +-------------+            |             |      |             |
      | args[argc-1]|       +-+  |             |      |             |
      +-------------+  limit|*-->+-------------+      |             |
                            +-+                       +-------------+

There is a global "args" array.  Certain words in "args" may
point into the heap (either the nursery or into older generations).
The nursery may point within itself, or into older generations.
Older generations may not point into the nursery.
The heap may not point into the args array.

The mutator creates a new object by using the N+1 words (including header)
starting at "alloc", and then adding N+1 to alloc.  This is only
permitted if alloc+N+1 <= limit.  Otherwise, the mutator must
first call the garbage collector.

The variables "alloc" and "limit" are owned by the mutator.
The "start" value is not actually a variable of the mutator,
but it was the value of "alloc" immediately after the most
recent collection.

To call the garbage collector, the mutator passes a fun_info and
a thread_info, as follows. */

typedef const uintnat *fun_info;
/* fi[0]: How many words the function might allocate
   fi[1]: How many slots of the args array contain live roots
   fi[2..(fi[1]-2)]: Indices of the live roots in the args array
*/

struct heap;     /* abstract, opaque */

#define MAX_ARGS 1024

struct thread_info {
  value *alloc; /* alloc pointer  */
  value *limit; /* limit pointer */
  struct heap *heap;  /* Description of the generations in the heap */
  value args[MAX_ARGS];   /* the args array */
};

struct thread_info *make_tinfo(void);

void garbage_collect(fun_info fi, struct thread_info *ti);
/* Performs one garbage collection; 
   or if ti->heap==NULL, initializes the heap. 

 The returns in a state where
 (1) the "after" graph of nodes reachable from args[indices[0..num_args]]
    is isomorphic to the "before" graph; and
 (2) the alloc pointer points to N words of unallocated heap space
  (where N>=num_allocs), such that limit-alloc=N.
*/

void free_heap(struct heap *h);
/* Deallocates all heap data associated with h, and returns the
 * memory to the operating system (via the malloc/free system).
 * After calling this function, h is a dangling pointer and should not be used.
 */

void reset_heap(struct heap *h);
/* Empties the heap without freeing its storage.
 * After a complete execution of the mutator,
 * and after whoever invoked the mutator copies whatever result they want
 * out of the heap, one can call this function before starting 
 * another mutator execution.  This saves the operating-system overhead of 
 * free_heap() followed by the implicit create_heap that would have been
 * done in the first garbage_collect() call of the next execution.
 */

/* which slot of the args array has the answer of a certicoq program */
#define answer_index 1

value* extract_answer(struct thread_info *ti);
/* y=extract_answer(x,ti) copies the dag rooted at ti->args[answer_index]
  into a compact data structure starting at y[1], outside the heap,
  in a single malloc'ed (therefore freeable) object at address y.
  All within-the-heap pointers will now be within the object y.
  If (the answer within) the heap pointed to records outside
  the heap, then those will point at their original locations
  outside the object y. 

  Note that the start is *(y+1), not (y+1); that is, there's an
  extra wrapper-record round the object.  That's so that the
  root-within-the-heap and the root-outside-the-heap (or root-unboxed)
  can be treated uniformly by the caller of extract_answer().
*/

