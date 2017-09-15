This directory contains, in `orig/`, Haskell code taken from the `text` package
that implements their fusing *streams*. The goal here is to verify that the
*cached length field* that is part of a stream is always correctly updated,
e.g. that a bug like https://github.com/haskell/text/issues/197 is no longer
there.

This endeavor is currently blocked on:

 * (tool bug)
   constructor names defined in a different module do not get `Mk_`
   prepended. Presumably fixed once the move past the renamer is done.

 * (conceptional)
   Termination of function `compareLengthI` will not be provable in
   general, because the function takes an arbitrary `Integral`. And even
   if it were `Integer`, termination of the local `fix` would be
   non-structural.

