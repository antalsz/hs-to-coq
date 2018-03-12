# Certicoq Demo

This directory demonstrates Certicoq being used to compile 
the output of `hs-to-coq`.

## Certicoq is a plugin for coq-8.7.1

You must use coq-8.7.1 to run this demo. If you are Stephanie, you can switch
to the 8.7.1 pin on your laptop via `opam switch coq871`. Don't forget to run
the opam env command afterwards!

Install via directions here: https://github.com/PrincetonUniversity/certicoq

The files base/Makefile.conf and lib/Makefile.conf have been modified to 
work with coq-8.7.1. Do not run coq_makefile to generate these files. 

More specifically, the modifications required are to:
- Add "" to the -Q and -R flags
- Add the order to base

      COQMF_VFILES = GHC/DeferredFix.v GHC/Prim.v GHC/Wf.v GHC/Num.v GHC/Char.v GHC/Tuple.v GHC/Base.v GHC/List.v GHC/Enum.v GHC/Err.v GHC/Real.v GHC/Unicode.v Data/Maybe.v Data/Bits.v Data/Type/Equality.v Data/Monoid.v Data/Either.v Data/Proxy.v Data/Foldable.v Data/Functor/Const.v Data/Functor.v Data/Traversable.v Control/Monad.v Data/List.v Data/Ord.v Data/Tuple.v Data/OldList.v Data/Bool.v Data/Void.v Data/Function.v Control/Monad/Fail.v Control/Category.v Control/Arrow.v Data/List/NonEmpty.v Data/Semigroup.v Data/Functor/Identity.v Control/Applicative.v Data/Functor/Classes.v Data/Bifunctor.v Prelude.v

If you regenerate these files, you must make the same modifications

## The DEMO

   run `make`
   run `a.out`

Don't be scared of all of the gcc warnings.

