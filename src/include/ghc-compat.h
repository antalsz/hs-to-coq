#ifndef __GHC_COMPAT__
#define __GHC_COMPAT__

#if 0
GHC 8.6 started using extensively the "Trees That Grow" style of ASTs,
which extends many constructors with a new "extension field".

To maintain compatibility across that change, this header introduces some
macros that either expand to the new field when it exists (GHC >= 8.6)
or disappear when it doesn't exist (GHC < 8.6).

> f (HsApp NOEXTP x y) = ...  -- before CPP
> f (HsApp _ x y) = ...       -- after CPP, GHC >= 8.6
> f (HsApp x y) = ...         -- after CPP, GHC 8.4

- Since GHC 8.10, inactive extension fields have type 'NoExtField'
- On GHC 8.6 and GHC 8.8, inactive extension fields have a differently named
  type 'NoExt'
- On GHC 8.4, some AST nodes already had "Trees That Grow"-style extension fields,
  with the default type 'PlaceHolder', that we rename accordingly in newer versions
  by turning it into a macro.

- The macro 'NOEXT' expands to the constructor name ('NoExtField', 'NoExt'),
  which can be used as both an expression and a pattern.
- The macro 'NOEXTP' expands to a wildcard pattern, which can be used for
  pattern-matching when the extension field is not inactive (not of type
  'NoExtField' or 'NoExt').
#endif

#if __GLASGOW_HASKELL__ >= 810

#define PlaceHolder NoExtField
#define NOEXT NoExtField
#define NOEXTP _

#elif __GLASGOW_HASKELL__ >= 806

#define PlaceHolder NoExt
#define NOEXT NoExt
#define NOEXTP _

#else

#define NOEXT
#define NOEXTP

#endif

#endif
