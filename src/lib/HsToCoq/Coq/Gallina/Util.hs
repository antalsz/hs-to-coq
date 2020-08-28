{-# LANGUAGE PatternSynonyms, OverloadedStrings, LambdaCase, TemplateHaskell, ViewPatterns #-}

module HsToCoq.Coq.Gallina.Util (
  -- * Common AST patterns
  pattern Var,    pattern App1,    pattern App2,    pattern App3,    appList,
  pattern VarPat, pattern App1Pat, pattern App2Pat, pattern App3Pat,
  pattern BName,
  mkInfix,
  maybeForall,
  maybeFun,
  pattern IfBool, pattern IfCase,
  pattern LetFix, pattern LetCofix,
  collectArgs,
  collectBinders,

  -- * Manipulating 'Term's
  termHead,

  -- * Manipulating 'FixBody's
  fixBodyName, fixBodyArgs, fixBodyTermination, fixBodyResultType, fixBodyBody,

  -- * Manipulating 'Binder's, 'Name's, and 'Qualid's
  -- ** Manipulating one 'Binder' at a time, even when the 'Typed' case has multiple names
  caseOneBinder,
  unconsOneBinder, unconsOneBinderFromType,
  BinderInfo(..), biGeneralizability, biExplicitness, biMaybeName, biMaybeType,
  -- ** Optics
  _Ident, _UnderscoreName, nameToIdent,
  binderNames, binderIdents, binderExplicitness, binderGeneralizability,
  -- ** Functions
  qualidBase, qualidModule, qualidMapBase, qualidExtendBase,
  splitModule,
  qualidToIdent, identToQualid, identToBase,
  qualidIsOp, qualidToOp, qualidToPrefix,
  unsafeIdentToQualid,
  nameToTerm, nameToPattern,
  binderArgs,
  consolidateTypedBinders,
  stripBinderType,

  -- * Manipulating 'Sentence's
  isComment
  ) where

import Control.Lens

import Data.Bifunctor
import Data.Functor.Contravariant (phantom)
import Data.Semigroup ((<>))
import Data.Foldable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import qualified Data.List.NonEmpty as NEL

import qualified Data.Text as T

import GHC.Stack

import HsToCoq.Util.Monad (ErrorString)
import HsToCoq.Coq.Gallina
import HsToCoq.ConvertHaskell.InfixNames

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

pattern VarPat  x          = QualidPat (Bare x)
pattern App1Pat c x        = ArgsPat c [x]
pattern App2Pat c x1 x2    = ArgsPat c [x1, x2]
pattern App3Pat c x1 x2 x3 = ArgsPat c [x1, x2, x3]

pattern BName :: Ident -> Name
pattern BName  x          = Ident (Bare x)

-- Legacy combinator, to migrate away from the Infix constructor
mkInfix :: Term -> Qualid -> Term -> Term
mkInfix l op r = App2 (Qualid op) l r

maybeForall :: Foldable f => f Binder -> Term -> Term
maybeForall = maybe id Forall . nonEmpty . toList
{-# INLINABLE  maybeForall #-}
{-# SPECIALIZE maybeForall :: [Binder]        -> Term -> Term #-}
{-# SPECIALIZE maybeForall :: NonEmpty Binder -> Term -> Term #-}

maybeFun :: Foldable f => f Binder -> Term -> Term
maybeFun = maybe id Fun . nonEmpty . toList
{-# INLINABLE  maybeFun #-}
{-# SPECIALIZE maybeFun :: [Binder]        -> Term -> Term #-}
{-# SPECIALIZE maybeFun :: NonEmpty Binder -> Term -> Term #-}

-- Two possible desugarings of if-then-else
pattern IfBool :: IfStyle -> Term -> Term -> Term -> Term
pattern IfBool is c t e = If is (HasType c (Var "bool")) Nothing t e

pattern IfCase :: IfStyle -> Term -> Term -> Term -> Term
pattern IfCase is c t e = If is (App1 (Var "Bool.Sumbool.sumbool_of_bool") c) Nothing t e

isLetFix :: Term -> Maybe (FixBody, Term)
isLetFix (Let f [] Nothing (Fix (FixOne fb@(FixBody f' _ _ _ _))) body)
    | f == f'   = Just (fb, body)
isLetFix _ = Nothing

pattern LetFix :: FixBody -> Term -> Term
pattern LetFix fb body <- (isLetFix -> Just (fb, body))
  where LetFix fb@(FixBody f _ _ _ _) body = Let f [] Nothing (Fix (FixOne fb)) body

isLetCofix :: Term -> Maybe (FixBody, Term)
isLetCofix (Let f [] Nothing (Cofix (FixOne fb@(FixBody f' _ _ _ _))) body)
    | f == f'   = Just (fb, body)
isLetCofix _ = Nothing

pattern LetCofix :: FixBody -> Term -> Term
pattern LetCofix fb body <- (isLetCofix -> Just (fb, body))
  where LetCofix fb@(FixBody f _ _ _ _) body = Let f [] Nothing (Cofix (FixOne fb)) body

termHead :: Term -> Maybe Qualid
termHead (Forall _ t)         = termHead t
termHead (HasType t _)        = termHead t
termHead (CheckType t _)      = termHead t
termHead (ToSupportType t)    = termHead t
termHead (Parens t)           = termHead t
termHead (InScope t _)        = termHead t
termHead (App t _)            = termHead t
termHead (ExplicitApp name _) = Just name
termHead (Qualid name)        = Just name
termHead _                    = Nothing

fixBodyName :: Lens' FixBody Qualid
fixBodyName = lens (\(FixBody name _ _ _ _) -> name)
                   (\(FixBody _ args mord mty body) name -> FixBody name args mord mty body)

fixBodyArgs :: Lens' FixBody Binders
fixBodyArgs = lens (\(FixBody _ args _ _ _) -> args)
                   (\(FixBody name _ mord mty body) args -> FixBody name args mord mty body)

fixBodyTermination :: Lens' FixBody (Maybe Order)
fixBodyTermination = lens (\(FixBody _ _ mord _ _) -> mord)
                   (\(FixBody name args _ mty body) mord -> FixBody name args mord mty body)

fixBodyResultType :: Lens' FixBody (Maybe Term)
fixBodyResultType = lens (\(FixBody _ _ _ mty _) -> mty)
                   (\(FixBody name args mord _ body) mty -> FixBody name args mord mty body)

fixBodyBody :: Lens' FixBody Term
fixBodyBody = lens (\(FixBody _ _ _ _ body) -> body)
                   (\(FixBody name args mord mty _) body -> FixBody name args mord mty body)


makePrisms ''Name

nameToIdent :: Iso' Name (Maybe Qualid)
nameToIdent = iso (\case Ident x        -> Just x
                         UnderscoreName -> Nothing)
                  (maybe UnderscoreName Ident)
{-# INLINEABLE nameToIdent #-}

binderNames :: Traversal' Binder Name
binderNames f (Inferred        ei name)     =          f name  <&> \name'  -> Inferred        ei name'
binderNames f (Typed       gen ei names ty) = traverse f names <&> \names' -> Typed       gen ei names' ty
binderNames _ gen@Generalized{}             = pure gen
{-# INLINEABLE binderNames #-}

binderIdents :: Traversal' Binder Qualid
binderIdents = binderNames._Ident
{-# INLINEABLE binderIdents #-}

binderExplicitness :: Lens' Binder Explicitness
binderExplicitness f (Inferred        ei name)     = f ei <&> \ei' -> Inferred        ei' name
binderExplicitness f (Typed       gen ei names ty) = f ei <&> \ei' -> Typed       gen ei' names ty
binderExplicitness f (Generalized     ei       ty) = f ei <&> \ei' -> Generalized     ei'       ty
{-# INLINEABLE binderExplicitness #-}

binderGeneralizability :: Getter Binder Generalizability
binderGeneralizability f (Inferred        _ _)   = phantom $ f Ungeneralizable
binderGeneralizability f (Typed       gen _ _ _) = phantom $ f gen
binderGeneralizability f (Generalized     _   _) = phantom $ f Generalizable
{-# INLINEABLE binderGeneralizability #-}

qualidBase :: Qualid -> Ident
qualidBase (Bare      ident) = ident
qualidBase (Qualified _ aid) = aid

qualidModule :: Qualid -> Maybe ModuleIdent
qualidModule (Bare      _)     = Nothing
qualidModule (Qualified qid _) = Just qid

qualidMapBase :: (Ident -> Ident) -> Qualid -> Qualid
qualidMapBase f (Bare             base) = Bare             $ f base
qualidMapBase f (Qualified prefix base) = Qualified prefix $ f base

qualidExtendBase :: T.Text -> Qualid -> Qualid
qualidExtendBase suffix = qualidMapBase (<> suffix)

qualidToIdent :: Qualid -> Ident
qualidToIdent (Bare      ident)   = ident
qualidToIdent (Qualified qid aid) = qid <> "." <> aid

qualidIsOp :: Qualid -> Bool
qualidIsOp = identIsOp . qualidBase

qualidToOp :: Qualid -> Maybe Op
qualidToOp (Qualified qid aid) = ((qid <> ".") <>) <$> identToOp aid
qualidToOp (Bare aid)          =                       identToOp aid

qualidToPrefix :: Qualid -> Maybe Op
qualidToPrefix qid = infixToPrefix <$> qualidToOp qid


-- This doesn't handle all malformed 'Ident's
identToQualid :: HasCallStack => Ident -> Maybe Qualid
identToQualid x = case splitModule x of
    Just (mod, ident) -> Just (Qualified mod (toPrefix ident))
    _                 -> Just (Bare (toPrefix x))

identToBase :: Ident -> Ident
identToBase x = maybe x qualidBase $ identToQualid x

nameToTerm :: Name -> Term
nameToTerm (Ident x)      = Qualid x
nameToTerm UnderscoreName = Underscore

nameToPattern :: Name -> Pattern
nameToPattern (Ident x)      = QualidPat x
nameToPattern UnderscoreName = UnderscorePat

binderArgs :: Foldable f => f Binder -> [Arg]
binderArgs = map (PosArg . nameToTerm) . foldMap (toListOf binderNames)
           . filter (\b -> b^?binderExplicitness == Just Explicit) . toList


unsafeIdentToQualid :: HasCallStack => Ident -> Qualid
unsafeIdentToQualid i = fromMaybe (error $ "unsafeIdentToQualid: " ++ show i) (identToQualid i)

collectArgs :: Term -> Either ErrorString (Qualid, [Term])
collectArgs (Qualid qid) = return (qid, [])
collectArgs (App t args) = do
    (f, args1) <- collectArgs t
    args2 <- mapM fromArg (toList args)
    return $ (f, args1 ++ args2)
  where
    fromArg (PosArg t) = return t
    fromArg _          = Left "non-positional argument"
collectArgs (Arrow a1 a2) = return (arrow_qid, [a1, a2])
  where arrow_qid = Qualified "GHC.Prim" "arrow"
collectArgs (Parens t)    = collectArgs t
collectArgs (InScope t _) = collectArgs t
collectArgs (HasType t _) = collectArgs t
collectArgs t             = Left $ "collectArgs: " ++ show t

-- assuming that the term is in prenex normal form
collectBinders :: Term -> [Binder]
collectBinders (Forall bs t) = do
  toList bs ++ collectBinders t
collectBinders _ = []

consolidateTypedBinders :: Binders -> Binders
consolidateTypedBinders (Typed g1 ei1 xs1 t1 :| Typed g2 ei2 xs2 t2 : bs) | g1 == g2 , ei1 == ei2 , t1 == t2 =
  consolidateTypedBinders (Typed g1 ei1 (xs1 <> xs2) t1 :| bs)
consolidateTypedBinders (b1 :| b2 : bs) =
  b1 NEL.<| consolidateTypedBinders (b2 :| bs)
consolidateTypedBinders (b :| []) =
  b :| []

-- @`{Show t}@ is left alone.
stripBinderType :: Binder -> Binders
stripBinderType b@Inferred{}                    = b :| []
stripBinderType b@Generalized{}                 = b :| []
stripBinderType b@(Typed Generalizable _ _ _)   = b :| []
stripBinderType (Typed Ungeneralizable ei xs _) = Inferred ei <$> xs

-- |Case analysis on a 'Binder', but pulls out a single case from a
-- multiple-names-with-the-same-type binder.  (E.g., @x@ becomes @x@, @(x : t)@
-- becomes @(x : t)@, but @(x y z : t)@ becomes @(x : t)@ plus @(y z : t)@.)
caseOneBinder :: Binder
              -> (Explicitness -> Name -> a)
              -> (Generalizability -> Explicitness -> Name -> Term -> Maybe Binder -> a)
              -> (Explicitness -> Term -> a)
              -> a
caseOneBinder b inferred typed generalized = case b of
  Inferred ei x          -> inferred ei x
  Typed g ei (x :| xs) t -> typed g ei x t $ case nonEmpty xs of
                                               Just xs' -> Just (Typed g ei xs' t)
                                               Nothing  -> Nothing
  Generalized ei t       -> generalized ei t

data BinderInfo = BinderInfo { _biGeneralizability :: !Generalizability
                             , _biExplicitness     :: !Explicitness
                             , _biMaybeName        :: !(Maybe Name)
                             , _biMaybeType        :: !(Maybe Term) }
                 deriving (Eq, Ord, Show, Read)
makeLenses ''BinderInfo

unconsOneBinder :: Binders -> (BinderInfo, [Binder])
unconsOneBinder (b :| bs) = caseOneBinder b
  (\  ei x       -> (BinderInfo Ungeneralizable ei (Just x) Nothing,  bs))
  (\g ei x t mb' -> (BinderInfo g               ei (Just x) (Just t), maybeToList mb' ++ bs))
  (\  ei   t     -> (BinderInfo Generalizable   ei Nothing  (Just t), bs))

unconsOneBinderFromType :: Term -> Maybe (BinderInfo, Term)
unconsOneBinderFromType (Forall bbs t) = Just $ second (maybeForall ?? t) (unconsOneBinder bbs)
unconsOneBinderFromType (t `Arrow` t') = Just (BinderInfo Ungeneralizable Explicit Nothing (Just t), t')
unconsOneBinderFromType (Parens t)     = unconsOneBinderFromType t
unconsOneBinderFromType _              = Nothing

isComment :: Sentence -> Bool
isComment CommentSentence{} = True
isComment _ = False
