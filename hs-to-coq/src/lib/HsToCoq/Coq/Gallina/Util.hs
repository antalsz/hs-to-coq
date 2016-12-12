{-# LANGUAGE PatternSynonyms #-}

module HsToCoq.Coq.Gallina.Util (
  pattern Var,    pattern App1,    pattern App2,    pattern App3,    appList,
  pattern VarPat, pattern App1Pat, pattern App2Pat, pattern App3Pat, appListPat,
  termHead,
  maybeForall
  ) where

import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import HsToCoq.Coq.Gallina

pattern Var  x          = Qualid (Bare x)
pattern App1 f x        = App f (PosArg x :| [])
pattern App2 f x1 x2    = App f (PosArg x1 :| PosArg x2 : [])
pattern App3 f x1 x2 x3 = App f (PosArg x1 :| PosArg x2 : PosArg x3 : [])

appList :: Term -> [Arg] -> Term
appList f = maybe f (App f) . nonEmpty

pattern VarPat  x          = QualidPat (Bare x)
pattern App1Pat f x        = ArgsPat f (x :| [])
pattern App2Pat f x1 x2    = ArgsPat f (x1 :| x2 : [])
pattern App3Pat f x1 x2 x3 = ArgsPat f (x1 :| x2 : x3 : [])

appListPat :: Qualid -> [Pattern] -> Pattern
appListPat c = maybe (QualidPat c) (ArgsPat c) . nonEmpty

termHead :: Term -> Maybe Qualid
termHead (Forall _ t)         = termHead t
termHead (HasType t _)        = termHead t
termHead (CheckType t _)      = termHead t
termHead (ToSupportType t)    = termHead t
termHead (Parens t)           = termHead t
termHead (InScope t _)        = termHead t
termHead (App t _)            = termHead t
termHead (ExplicitApp name _) = Just name
termHead (Infix _ op _)       = Just $ Bare op
termHead (Qualid name)        = Just name
termHead _                    = Nothing

maybeForall :: Foldable f => f Binder -> Term -> Term
maybeForall = maybe id Forall . nonEmpty . toList
{-# INLINABLE  maybeForall #-}
{-# SPECIALIZE maybeForall :: [Binder]        -> Term -> Term #-}
{-# SPECIALIZE maybeForall :: NonEmpty Binder -> Term -> Term #-}
