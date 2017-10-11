module PolyInstance3 where

class N a where
  bar :: a

class N a => M a where
  foo :: a

instance N [a] where
  bar = []

instance M a => M [a] where
  foo = [foo]
