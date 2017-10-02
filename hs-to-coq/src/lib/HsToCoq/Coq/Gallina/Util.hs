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
  qualidBase, qualidModule,
  qualidToIdent, identToQualid, identToBase,
  nameToTerm, nameToPattern,
  binderArgs
  ) where

import Control.Lens
import Data.Semigroup ((<>))
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import qualified Data.Text as T
import HsToCoq.Coq.Gallina

pattern Var  :: Ident                        -> Term
pattern App1 :: Term -> Term                 -> Term
pattern App2 :: Term -> Term -> Term         -> Term
pattern App3 :: Term -> Term -> Term -> Term -> Term
appList      :: Term -> [Arg]                -> Term

pattern Var  x          = Qualid (Bare x)
pattern App1 f x        = App f (PosArg x :| [])
pattern App2 f x1 x2    = App f (PosArg x1 :| PosArg x2 : [])
pattern App3 f x1 x2 x3 = App f (PosArg x1 :| PosArg x2 : PosArg x3 : [])
appList      f          = maybe f (App f) . nonEmpty

pattern VarPat  :: Ident                                   -> Pattern
pattern App1Pat :: Qualid -> Pattern                       -> Pattern
pattern App2Pat :: Qualid -> Pattern -> Pattern            -> Pattern
pattern App3Pat :: Qualid -> Pattern -> Pattern -> Pattern -> Pattern
appListPat      :: Qualid -> [Pattern]                     -> Pattern

pattern VarPat  x          = QualidPat (Bare x)
pattern App1Pat c x        = ArgsPat c (x :| [])
pattern App2Pat c x1 x2    = ArgsPat c (x1 :| x2 : [])
pattern App3Pat c x1 x2 x3 = ArgsPat c (x1 :| x2 : x3 : [])
appListPat      c          = maybe (QualidPat c) (ArgsPat c) . nonEmpty

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

qualidBase :: Qualid -> Ident
qualidBase (Bare      ident) = ident
qualidBase (Qualified _ aid) = aid

qualidModule :: Qualid -> Maybe Qualid
qualidModule (Bare      _)     = Nothing
qualidModule (Qualified qid _) = Just qid

qualidToIdent :: Qualid -> Ident
qualidToIdent (Bare      ident)   = ident
qualidToIdent (Qualified qid aid) = qualidToIdent qid <> "." <> aid

-- This doesn't handle all malformed 'Ident's
identToQualid :: Ident -> Maybe Qualid
identToQualid x = case T.splitOn "." x of
                    root:rest -> Just $ foldl' Qualified (Bare root) rest
                    []        -> Nothing

identToBase :: Ident -> Ident
identToBase = last . T.splitOn "."

nameToTerm :: Name -> Term
nameToTerm (Ident x)      = Var x
nameToTerm UnderscoreName = Underscore

nameToPattern :: Name -> Pattern
nameToPattern (Ident x)      = VarPat x
nameToPattern UnderscoreName = UnderscorePat

binderArgs :: Foldable f => f Binder -> [Arg]
binderArgs = map (PosArg . nameToTerm) . foldMap (toListOf binderNames)
           . filter (\b -> b^?binderExplicitness == Just Explicit) . toList
