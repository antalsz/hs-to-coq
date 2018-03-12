/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*          Xavier Leroy and Damien Doligez, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#ifndef CONFIG_H
#define CONFIG_H

#if SIZEOF_PTR == SIZEOF_LONG
/* Standard models: ILP32 or I32LP64 */
typedef long intnat;
typedef unsigned long uintnat;
#define ARCH_INTNAT_PRINTF_FORMAT "l"
#elif SIZEOF_PTR == SIZEOF_INT
/* Hypothetical IP32L64 model */
typedef int intnat;
typedef unsigned int uintnat;
#define ARCH_INTNAT_PRINTF_FORMAT ""
#elif SIZEOF_PTR == 8
/* Win64 model: IL32P64 */
typedef int64_t intnat;
typedef uint64_t uintnat;
#define ARCH_INTNAT_PRINTF_FORMAT ARCH_INT64_PRINTF_FORMAT
#else
#error "No integer type available to represent pointers"
#endif

/* Endianness of floats */

/* ARCH_FLOAT_ENDIANNESS encodes the byte order of doubles as follows:
   the value [0xabcdefgh] means that the least significant byte of the
   float is at byte offset [a], the next lsb at [b], ..., and the
   most significant byte at [h]. */

#if defined(__arm__) && !defined(__ARM_EABI__)
#define ARCH_FLOAT_ENDIANNESS 0x45670123
#elif defined(ARCH_BIG_ENDIAN)
#define ARCH_FLOAT_ENDIANNESS 0x76543210
#else
#define ARCH_FLOAT_ENDIANNESS 0x01234567
#endif


/* We use threaded code interpretation if the compiler provides labels
   as first-class values (GCC 2.x). */

#if defined(__GNUC__) && __GNUC__ >= 2 && !defined(DEBUG) \
    && !defined (SHRINKED_GNUC) && !defined(CAML_JIT)
#define THREADED_CODE
#endif


/* Memory model parameters */

/* The size of a page for memory management (in bytes) is [1 << Page_log].
   [Page_size] must be a multiple of [sizeof (value)].
   [Page_log] must be be >= 8 and <= 20.
   Do not change the definition of [Page_size]. */
#define Page_log 12             /* A page is 4 kilobytes. */
#define Page_size (1 << Page_log)

/* Initial size of stack (bytes). */
#define Stack_size (4096 * sizeof(value))

/* Minimum free size of stack (bytes); below that, it is reallocated. */
#define Stack_threshold (256 * sizeof(value))

/* Default maximum size of the stack (words). */
#define Max_stack_def (1024 * 1024)


/* Maximum size of a block allocated in the young generation (words). */
/* Must be > 4 */
#define Max_young_wosize 256
#define Max_young_whsize (Whsize_wosize (Max_young_wosize))


/* Minimum size of the minor zone (words).
   This must be at least [2 * Max_young_whsize]. */
#define Minor_heap_min 4096

/* Maximum size of the minor zone (words).
   Must be greater than or equal to [Minor_heap_min].
*/
#define Minor_heap_max (1 << 28)

/* Default size of the minor zone. (words)  */
#define Minor_heap_def 262144


/* Minimum size increment when growing the heap (words).
   Must be a multiple of [Page_size / sizeof (value)]. */
#define Heap_chunk_min (15 * Page_size)

/* Default size increment when growing the heap.
   If this is <= 1000, it's a percentage of the current heap size.
   If it is > 1000, it's a number of words. */
#define Heap_chunk_def 2048 /* 15 (original value) */

/* Default initial size of the major heap (words);
   Must be a multiple of [Page_size / sizeof (value)]. */
#define Init_heap_def (31 * Page_size)
/* (about 512 kB for a 32-bit platform, 1 MB for a 64-bit platform.) */


/* Default speed setting for the major GC.  The heap will grow until
   the dead objects and the free list represent this percentage of the
   total size of live objects. */
#define Percent_free_def 80

/* Default setting for the compacter: 500%
   (i.e. trigger the compacter when 5/6 of the heap is free or garbage)
   This can be set quite high because the overhead is over-estimated
   when fragmentation occurs.
 */
#define Max_percent_free_def 500

/* Default setting for the major GC slice smoothing window: 1
   (i.e. no smoothing)
*/
#define Major_window_def 1

/* Maximum size of the major GC slice smoothing window. */
#define Max_major_window 50


/* Default size of the heap in words  */
#define Heap_def 8192


#endif /* CONFIG_H */
