{-# LANGUAGE PatternSynonyms, OverloadedStrings, LambdaCase, TemplateHaskell #-}

module HsToCoq.Coq.Gallina.Util (
  -- * Common AST patterns
  pattern Var,    pattern App1,    pattern App2,    pattern App3,    appList,
  pattern VarPat, pattern App1Pat, pattern App2Pat, pattern App3Pat, appListPat,
  maybeForall,

  -- * Manipulating 'Term's
  termHead,
  
  -- * Manipulating 'Binder's, 'Name's, and 'Qualid's
  -- ** Optics
  _Ident, _UnderscoreName, nameToIdent,
  binderNames, binderIdents, binderExplicitness,
  -- ** Functions
  qualidToIdent,
  nameToTerm, nameToPattern,
  binderArgs
  ) where

import Control.Lens
import Data.Semigroup ((<>))
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

maybeForall :: Foldable f => f Binder -> Term -> Term
maybeForall = maybe id Forall . nonEmpty . toList
{-# INLINABLE  maybeForall #-}
{-# SPECIALIZE maybeForall :: [Binder]        -> Term -> Term #-}
{-# SPECIALIZE maybeForall :: NonEmpty Binder -> Term -> Term #-}

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

makePrisms ''Name

nameToIdent :: Iso' Name (Maybe Ident)
nameToIdent = iso (\case Ident x        -> Just x
                         UnderscoreName -> Nothing)
                  (maybe UnderscoreName Ident)
{-# INLINEABLE nameToIdent #-}

binderNames :: Traversal' Binder Name
binderNames f (Inferred        ei name)     =          f name  <&> \name'  -> Inferred        ei name'
binderNames f (Typed       gen ei names ty) = traverse f names <&> \names' -> Typed       gen ei names' ty
binderNames _ gen@Generalized{}             = pure gen
binderNames _ blet@BindLet{}                = pure blet
{-# INLINEABLE binderNames #-}

binderIdents :: Traversal' Binder Ident
binderIdents = binderNames._Ident
{-# INLINEABLE binderIdents #-}

binderExplicitness :: Traversal' Binder Explicitness
binderExplicitness f (Inferred        ei name)     = f ei <&> \ei' -> Inferred        ei' name
binderExplicitness f (Typed       gen ei names ty) = f ei <&> \ei' -> Typed       gen ei' names ty
binderExplicitness f (Generalized     ei       ty) = f ei <&> \ei' -> Generalized     ei'       ty
binderExplicitness _ blet@BindLet{}                = pure blet
{-# INLINEABLE binderExplicitness #-}

qualidToIdent :: Qualid -> Ident
qualidToIdent (Bare      ident)   = ident
qualidToIdent (Qualified qid aid) = qualidToIdent qid <> "." <> aid

nameToTerm :: Name -> Term
nameToTerm (Ident x)      = Var x
nameToTerm UnderscoreName = Underscore

nameToPattern :: Name -> Pattern
nameToPattern (Ident x)      = VarPat x
nameToPattern UnderscoreName = UnderscorePat

binderArgs :: Foldable f => f Binder -> [Arg]
binderArgs = map (PosArg . nameToTerm) . foldMap (toListOf binderNames)
           . filter (\b -> b^?binderExplicitness == Just Explicit) . toList
