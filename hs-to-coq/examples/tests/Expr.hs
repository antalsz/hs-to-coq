-- simplified version of compiler/coreSyn/coreSyn.hs

-- This file demonstrates the Coq 8.6 issue with universes.
--
-- Anomaly: Unable to handle arbitrary u+k <= v constraints. Please report at
-- http://coq.inria.fr/bugs/.
--

data Expr b
  = Var   Id
  | App   (Expr b) (Arg b)
  | Lam   b (Expr b)
  | Case  (Expr b) b Type [Alt b]       -- See #case_invariants#
  deriving Data

-- | Type synonym for expressions that occur in function argument positions.
-- Only 'Arg' should contain a 'Type' at top level, general 'Expr' should not
type Arg b = Expr b

type Alt b = (AltCon, [b], Expr b)
