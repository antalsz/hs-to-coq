{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module SkipMatches where

-- See also issue #130
skipEquation :: Bool -> Bool
skipEquation True  = False
skipEquation False = True
skipEquation _     = True -- This underscore case is redundant and needs to be eliminated

skipEquationMultipleArgs :: Bool -> Bool -> Bool
skipEquationMultipleArgs True  _     = False
skipEquationMultipleArgs False _     = True
skipEquationMultipleArgs _     True  = True  -- This case is redundant and needs to be eliminated
skipEquationMultipleArgs _     False = False -- This case is redundant and needs to be eliminated

skipCasePattern :: Bool -> Bool
skipCasePattern b = case b of
  True   -> False
  False  -> True
  _      -> True -- This underscore case is redundant and needs to be eliminated (locally)
  ignore -> True -- This variable case is redundant and needs to be eliminated (globally)

skipLambdaCasePattern :: Bool -> Bool
skipLambdaCasePattern = \case
  True   -> False
  False  -> True
  _      -> True -- This underscore case is redundant and needs to be eliminated (locally)
  ignore -> True -- This variable case is redundant and needs to be eliminated (globally)

preserveCasePattern :: Bool -> Bool
preserveCasePattern = \case
  True   -> False
  _      -> True -- This underscore case is NOT redundant
  ignore -> True -- This variable case is redundant and needs to be eliminated (globally)
