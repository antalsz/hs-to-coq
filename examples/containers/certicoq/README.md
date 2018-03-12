# Certicoq Demo

This directory demonstrates Certicoq being used to compile 
the output of `hs-to-coq`.

## Certicoq is a plugin for coq-8.7.1

You must use coq-8.7.1 to run this demo. If you are Stephanie, you can switch
to the 8.7.1 pin on your laptop via `opam switch coq871`. Don't forget to run
the opam env command afterwards (eval `opam config env`)! [If you are
Stephanie, you can switch back to coq-8.7.2 via the command `opam switch
coq87`]

Install Certicoq via directions here: https://github.com/PrincetonUniversity/certicoq

The files base/Makefile.conf and lib/Makefile.conf have been modified to 
work with coq-8.7.1. Do not run `coq_makefile -f _CoqProject -o Makefile` to generate these files. 

More specifically, the modifications required are to:
  - Add "" to the -Q and -R flags
  - Add the order to base

      COQMF_VFILES = GHC/DeferredFix.v GHC/Prim.v GHC/Wf.v GHC/Num.v GHC/Char.v GHC/Tuple.v GHC/Base.v GHC/List.v GHC/Enum.v GHC/Err.v GHC/Real.v GHC/Unicode.v Data/Maybe.v Data/Bits.v Data/Type/Equality.v Data/Monoid.v Data/Either.v Data/Proxy.v Data/Foldable.v Data/Functor/Const.v Data/Functor.v Data/Traversable.v Control/Monad.v Data/List.v Data/Ord.v Data/Tuple.v Data/OldList.v Data/Bool.v Data/Void.v Data/Function.v Control/Monad/Fail.v Control/Category.v Control/Arrow.v Data/List/NonEmpty.v Data/Semigroup.v Data/Functor/Identity.v Control/Applicative.v Data/Functor/Classes.v Data/Bifunctor.v Prelude.v

If you regenerate these files, you must make the same modifications

## The DEMO

   run `make`
   run `a.out`

Don't be scared of all of the gcc warnings.

## Notes from Olivier:

Here are the steps to compile Coq terms with Certicoq and run them, once the Certicoq plugin is installed:

1) Import Certicoq

From CertiCoq.Plugin Require Import CertiCoq.


2) Compile using Certicoq on the term you want to run, "foo" in the example. This should generate a file Top.foo.c

CertiCoq Compile foo.


3) Copy the following files from the certicoq/theories/Runtime folder: config.h main.c gc.h gc.c values.h

4) Compile the generated C file with the main handler and the garbage collector, e.g. in gcc

gcc -m32 -O2 main.c gc.c Top.foo.c

5) The output will be printed to the screen along with the time spend executing the compiled term (and garbage-collection during the execution). We are working on having an actual API for interacting with the compiled programs or at least printing using constructor names, but for the moment what is printed is the "tag" of each constructor, grouped as boxed and unboxed, starting from 0. For example, for lists, cons is 0 ( _ , _) and nil is 0, and for bool, false is 0 and true is 1.

