{-# LANGUAGE PatternSynonyms #-}

module HsToCoq.Coq.Gallina.Util (
  pattern Var, pattern App1, pattern App2, appList,
  pattern CoqVarPat, pattern App1Pat, pattern App2Pat, appListPat,
  ) where

import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import HsToCoq.Coq.Gallina

pattern Var  x       = Qualid (Bare x)
pattern App1 f x     = App f (PosArg x :| [])
pattern App2 f x1 x2 = App f (PosArg x1 :| PosArg x2 : [])

appList :: Term -> [Arg] -> Term
appList f = maybe f (App f) . nonEmpty

pattern CoqVarPat x       = QualidPat (Bare x)
pattern App1Pat   f x     = ArgsPat f (x :| [])
pattern App2Pat   f x1 x2 = ArgsPat f (x1 :| x2 : [])

appListPat :: Qualid -> [Pattern] -> Pattern
appListPat c = maybe (QualidPat c) (ArgsPat c) . nonEmpty
