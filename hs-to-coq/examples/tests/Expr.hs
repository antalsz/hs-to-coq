module Expr where

-- simplified version of compiler/coreSyn/coreSyn.hs

-- This file demonstrates the Coq 8.6 issue with universes.
--
-- Anomaly: Unable to handle arbitrary u+k <= v constraints. Please report at
-- http://coq.inria.fr/bugs/.
--

data Id

data Expr b
  = Var   Id
  | App   (Expr b) (Arg b)
  | Lam   b (Expr b)

-- | Type synonym for expressions that occur in function argument positions.
-- Only 'Arg' should contain a 'Type' at top level, general 'Expr' should not
type Arg b = Expr b
