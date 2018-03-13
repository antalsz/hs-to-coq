#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "config.h"
#include "values.h"
#include "gc.h"

/* A "space" describes one generation of the generational collector. */
struct space {
  value *start, *next, *limit;
};
/* Either start==NULL (meaning that this generation has not yet been created),
   or start <= next <= limit.  The words in start..next  are allocated
   and initialized, and the words from next..limit are available to allocate. */

#define MAX_SPACES 12  /* how many generations */

#ifndef RATIO
#define RATIO 2   /* size of generation i+1 / size of generation i */
/*  Using RATIO=2 is faster than larger ratios, empirically */
#endif

#ifndef NURSERY_SIZE
#define NURSERY_SIZE (1<<16)
#endif
/* The size of generation 0 (the "nursery") should approximately match the 
   size of the level-2 cache of the machine, according to:
      Cache Performance of Fast-Allocating Programs, 
      by Marcelo J. R. Goncalves and Andrew W. Appel. 
      7th Int'l Conf. on Functional Programming and Computer Architecture,
      pp. 293-305, ACM Press, June 1995.
   We estimate this as 256 kilobytes 
     (which is the size of the Intel Core i7 per-core L2 cache).
    http://www.tomshardware.com/reviews/Intel-i7-nehalem-cpu,2041-10.html
    https://en.wikipedia.org/wiki/Nehalem_(microarchitecture)
   Empirical measurements show that 64k works well 
    (or anything in the range from 32k to 128k).
*/

#ifndef DEPTH
#define DEPTH 0  /* how much depth-first search to do */
#endif

struct heap {
  /* A heap is an array of generations; generation 0 must be already-created */
  struct space spaces[MAX_SPACES];
};

#ifdef DEBUG

int in_heap(struct heap *h, value v) {
  int i;
  for (i=0; i<MAX_SPACES; i++)
    if (h->spaces[i].start != NULL)
      if (h->spaces[i].start <= (value*)v &&
	  (value *)v <= h->spaces[i].limit)
	return 1;
  return 0;
}

void printtree(FILE *f, struct heap *h, value v) {
  if(Is_block(v))
    if (in_heap(h,v)) {
      header_t hd = Field(v,-1);
      int sz = Wosize_hd(hd);
      int i;
      fprintf(f,"%d(", Tag_hd(hd));
      for(i=0; i<sz-1; i++) {
	printtree(f,h,Field(v,i));
	fprintf(f,",");
      }
      if (i<sz)
	printtree(f,h,Field(v,i));
      fprintf(f,")");
    }
    else {
      fprintf(f,"%8x",v);
    }
  else fprintf(f,"%d",v>>1);
}

void printroots (FILE *f, struct heap *h,
		  fun_info fi,   /* which args contain live roots? */
		  struct thread_info *ti) /* where's the args array? */
 {
   value *args; int n; uintnat i, *roots;
   roots = fi+2;
   n = fi[1];
   args = ti->args;
  
  for(i = 0; i < n; i++) {
    fprintf(f,"%d[%8x]:",roots[i],args[roots[i]]);
    printtree(f, h, args[roots[i]]);
    fprintf(f,"\n");
  }
  fprintf(f,"\n");
}  

#endif

void abort_with(char *s) {
  fprintf(stderr, s);
  exit(1);
}

#define Is_from(from_start, from_limit, v)			\
   (from_start <= (value*)(v) && (value*)(v) < from_limit)
/* Assuming v is a pointer (Is_block(v)), tests whether v points
   somewhere into the "from-space" defined by from_start and from_limit */

void forward (value *from_start,  /* beginning of from-space */
	      value *from_limit,  /* end of from-space */
	      value **next,       /* next available spot in to-space */
	      value *p,           /* location of word to forward */
	      int depth)          /* how much depth-first search to do */
/* What it does:  If *p is a pointer, AND it points into from-space,
   then make *p point at the corresponding object in to-space.
   If such an object did not already exist, create it at address *next
    (and increment *next by the size of the object).
   If *p is not a pointer into from-space, then leave it alone. 

   The depth parameter may be set to 0 for ordinary breadth-first
   collection.  Setting depth to a small integer (perhaps 10)
   may improve the cache locality of the copied graph.
*/
 {
  value v = *p;
  if(Is_block(v)) {
    if(Is_from(from_start, from_limit, v)) {
      header_t hd = Hd_val(v); 
      if(hd == 0) { /* already forwarded */
	*p = Field(v,0);
      } else {
	int i;
	int sz;
	value *new;
        sz = Wosize_hd(hd);
	new = *next+1;
	*next = new+sz; 
	for(i = -1; i < sz; i++) {
	  Field(new, i) = Field(v, i);
	}
	Hd_val(v) = 0;
	Field(v, 0) = (value)new;
	*p = (value)new;
	if (depth>0)
	  for (i=0; i<sz; i++)
	    forward(from_start, from_limit, next, &Field(new,i), depth-1);
      }
    }
  }
}

void forward_roots (value *from_start,  /* beginning of from-space */
		    value *from_limit,  /* end of from-space */
		    value **next,       /* next available spot in to-space */
		    fun_info fi,        /* which args contain live roots? */
		    struct thread_info *ti) /* where's the args array? */
/* Forward each live root in the args array */
 {
   value *args; int n; uintnat i;
   const uintnat *roots = fi+2;
   n = fi[1];
   args = ti->args;
  
   for(i = 0; i < n; i++) {
     assert (roots[i] < MAX_ARGS);
     forward(from_start, from_limit, next, args+roots[i], DEPTH);
   }
}  

#define No_scan_tag 251
#define No_scan(t) ((t) >= No_scan_tag)

void do_scan(value *from_start,  /* beginning of from-space */
	     value *from_limit,  /* end of from-space */
	     value *scan,        /* start of unforwarded part of to-space */
 	     value **next)       /* next available spot in to-space */
/* Forward each word in the to-space between scan and *next.
  In the process, next may increase, so keep doing it until scan catches up.
  Leave alone:  header words, and "no_scan" (nonpointer) data. 
*/
{
  value *s;
  s = scan;
  while(s < *next) {
    header_t hd = *s;
    mlsize_t sz = Wosize_hd(hd);
    int tag = Tag_hd(hd);
    if (!No_scan(tag)) {
      intnat j;
      for(j = 1; j <= sz; j++) {
	forward (from_start, from_limit, next, &Field(s, j), DEPTH);
      }
    }
    s += 1+sz;
  }
}
	     
void do_generation (struct space *from,  /* descriptor of from-space */
		    struct space *to,    /* descriptor of to-space */
		    fun_info fi,         /* which args contain live roots? */
		    struct thread_info *ti)  /* where's the args array? */
/* Copy the live objects out of the "from" space, into the "to" space,
   using fi and ti to determine the roots of liveness. */
{
  value *p = to->next;
  assert(from->next-from->start <= to->limit-to->next);
  forward_roots(from->start, from->limit, &to->next, fi, ti);
  do_scan(from->start, from->limit, p, &to->next);
  if(0)  fprintf(stderr,"%5.3f%% occupancy\n",
	  (to->next-p)/(double)(from->next-from->start));
  from->next=from->start;
}  

#if 0
/* This "gensize" function is only useful if the desired ratio is >2,
   but empirical measurements show that ratio=2 is better than ratio>2. */
uintnat gensize(uintnat words)
/* words is size of one generation; calculate size of the next generation */
{
  uintnat maxint = 0u-1u;
  uintnat n,d;
  /* The next few lines calculate a value "n" that's at least words*2,
     preferably words*RATIO, and without overflowing the size of an
     unsigned integer. */
  /* minor bug:  this assumes sizeof(uintnat)==sizeof(void*)==sizeof(value) */
  if (words > maxint/(2*sizeof(value)))
    abort_with("Next generation would be too big for address space\n");
  d = maxint/RATIO;
  if (words<d) d=words;
  n = d*RATIO;
  assert (n >= 2*words);
  return n;
}  
#endif

void create_space(struct space *s,  /* which generation to create */
		  uintnat n) /* size of the generation */
  /* malloc an array of words for generation "s", and
     set s->start and s->next to the beginning, and s->limit to the end.
  */

 {
  value *p;
  p = (value *)malloc(n * sizeof(value));
  if (p==NULL)
    abort_with ("Could not create the next generation\n");
  /*  fprintf(stderr, "Created a generation of %d words\n", n); */
  s->start=p;
  s->next=p;
  s->limit = p+n;
}

struct heap *create_heap()
/* To create a heap, first malloc the array of space-descriptors,
   then create only generation 0.  */
{
  int i;
  struct heap *h = (struct heap *)malloc(sizeof (struct heap));
  if (h==NULL)
    abort_with("Could not create the heap\n");
  create_space(h->spaces+0, NURSERY_SIZE);
  for(i=1; i<MAX_SPACES; i++) {
    h->spaces[i].start = NULL;
    h->spaces[i].next = NULL;
    h->spaces[i].limit = NULL;
  }
  return h;
}

struct thread_info *make_tinfo(void) {
  struct heap *h;
  struct thread_info *tinfo;
  h = create_heap();
  tinfo = (struct thread_info *)malloc(sizeof(struct thread_info));
  if (!tinfo) {
    fprintf(stderr, "Could not allocate thread_info struct\n");
    exit(1);
  }
  

    
  tinfo->heap=h;
  tinfo->alloc=h->spaces[0].start;
  tinfo->limit=h->spaces[0].limit;

  return tinfo;
}

void resume(fun_info fi, struct thread_info *ti)
/* When the garbage collector is all done, it does not "return"
   to the mutator; instead, it uses this function (which does not return)
   to resume the mutator by invoking the continuation, fi->fun.  
   But first, "resume" informs the mutator
   of the new values for the alloc and limit pointers.
*/
 {
  struct heap *h = ti->heap;
  value *lo, *hi;
  uintnat num_allocs = fi[0];
  assert (h);
  lo = h->spaces[0].start;
  hi = h->spaces[0].limit;
  if (hi-lo < num_allocs)
    abort_with ("Nursery is too small for function's num_allocs\n");
  ti->alloc = lo;
  ti->limit = hi;
}  

void garbage_collect(fun_info fi, struct thread_info *ti)
/* See the header file for the interface-spec of this function. */
{
  struct heap *h = ti->heap;
  if (h==NULL) {
    /* If the heap has not yet been initialized, create it and resume */
    h = create_heap();
    ti->heap = h;
    resume(fi,ti);
    return;
  } else {
    int i;
    assert (h->spaces[0].limit == ti->limit);  
    h->spaces[0].next = ti->alloc; /* this line is probably unnecessary */
    for (i=0; i<MAX_SPACES-1; i++) {
      /* Starting with the youngest generation, collect each generation
         into the next-older generation.  Usually, when doing that,
         there will be enough space left in the next-older generation
         so that we can break the loop by resuming the mutator. */

      /* If the next generation does not yet exist, create it */
      if (h->spaces[i+1].start==NULL) {
	int w = h->spaces[i].limit-h->spaces[i].start;
	create_space(h->spaces+(i+1), RATIO*w);
      }
      /* Copy all the objects in generation i, into generation i+1 */
  if(0)
      fprintf(stderr, "Generation %d:  ", i);
      do_generation(h->spaces+i, h->spaces+(i+1), fi, ti);
      /* If there's enough space in gen i+1 to guarantee that the
         NEXT collection into i+1 will succeed, we can stop here */
      if (h->spaces[i].limit - h->spaces[i].start
	  <= h->spaces[i+1].limit - h->spaces[i+1].next) {
	 resume(fi,ti);
	 return;
      }
    }
    /* If we get to i==MAX_SPACES, that's bad news */
    abort_with("Ran out of generations\n");
  }
  /* Can't reach this point */
  assert(0);
} 

/* REMARK.  The generation-management policy in the garbage_collect function
   has a potential flaw.  Whenever a record is copied, it is promoted to
   a higher generation.  This is generally a good idea.  But there is
   a bounded number of generations.  A useful improvement would be:
   when it's time to collect the oldest generation (and we can tell
   it's the oldest, at least because create_space() fails), do some
   reorganization instead of failing.
 */

void reset_heap (struct heap *h) {
  fprintf(stderr, "Debug: in reset_heap\n");
  int i;
  for (i=0; i<MAX_SPACES; i++)
    h->spaces[i].next = h->spaces[i].start;
}
  

void free_heap (struct heap *h) {
  fprintf(stderr, "Debug: in free_heap\n");
  int i;
  for (i=0; i<MAX_SPACES; i++) {
    value *p = h->spaces[i].start;
    if (p!=NULL)
      free(p);
  }
  free (h);
}
