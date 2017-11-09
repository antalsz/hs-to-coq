module PolyInstance3 where

{-
This regressed after making type classes continuations, because
of this Coq bug:

https://sympa.inria.fr/sympa/arc/coq-club/2017-11/msg00035.html
-}

class N a where
  bar :: a

class N a => M a where
  foo :: a

instance N [a] where
  bar = []

instance M a => M [a] where
  foo = [foo]
