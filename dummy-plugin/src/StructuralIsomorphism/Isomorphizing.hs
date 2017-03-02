{-# LANGUAGE FlexibleContexts,
             GeneralizedNewtypeDeriving,
             NamedFieldPuns, RecordWildCards,
             LambdaCase, ViewPatterns,
             TemplateHaskell #-}

module StructuralIsomorphism.Isomorphizing (
  -- * Monad and monad transformer
  IsomorphizingT(..), Isomorphizing,
  -- * Run isomorphizing computations
  runIsomorphizingT, runIsomorphizing, spliceIsomorphizing,
  
  -- * Manipulate isomorphism data (error, reader, writer, state)
  isomorphizingError,
  withCurrentTypes, withCurrentConstructors,
  withTypeVariables, lookupTypeVariable,
  addDec, addDecs, addDecQ, addDecsQ,
  alreadyIsomorphic, learnIsomorphism,
  
  -- * Useful combinators
  learnTypeSynonym, reifyDataType,
  forBothWhat, forBothWhatWith,
  
  -- * Work with existing isomorphism data
  existingIsomorphisms, learnExistingIsomorphisms,
  
  -- * Underlying types
  IsomorphizingEnvironment(..),
  IsomorphizingContext(..), isoContextErrorDescription
) where

import Data.Bifunctor
import Control.Applicative
import Control.Monad

import Data.Functor.Identity
import Control.Monad.Trans
import Control.Monad.RWS.Strict
import Control.Monad.Except

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)

import StructuralIsomorphism.Util
import StructuralIsomorphism.TH.Util
import StructuralIsomorphism.Class
import StructuralIsomorphism.Declarations

--------------------------------------------------------------------------------

data IsomorphizingContext =
  IsomorphizingContext { typeIsoContext :: !(Maybe (Name,Name))
                       , ctorIsoContext :: !(Maybe (Name,Name)) }
                       deriving (Eq, Ord, Show)

-- NB. /Right/-biased!
instance Monoid IsomorphizingContext where
  mempty = IsomorphizingContext Nothing Nothing
  
  isoContext1 `mappend` isoContext2 =
    IsomorphizingContext { typeIsoContext =   typeIsoContext isoContext2
                                          <|> typeIsoContext isoContext1
                         , ctorIsoContext =   ctorIsoContext isoContext2
                                          <|> ctorIsoContext isoContext1 }

isoContextErrorDescription :: IsomorphizingContext -> String
isoContextErrorDescription IsomorphizingContext{..} =
  mismatch . join bimap pretty $ realign typeIsoContext ctorIsoContext where
    distribute Nothing      = (Nothing, Nothing)
    distribute (Just (x,y)) = (Just x, Just y)
    
    realign (distribute -> (ty1,ty2)) (distribute -> (con1,con2)) =
      ((ty1,con1),(ty2,con2))
    
    pretty (Nothing, Nothing)  = ""
    pretty (Just ty, Nothing)  = quoted ty
    pretty (Nothing, Just con) = quoted con ++ " (<unknown>)"
    pretty (Just ty, Just con) = quoted con ++ " (" ++ quoted ty ++ ")"
    
    mismatch (s1,s2) | null s1   = s2
                     | null s2   = s1
                     | otherwise = s1 ++ " <> " ++ s2

--------------------------------------------------------------------------------

data IsomorphizingEnvironment =
  IsomorphizingEnvironment { isoContexts  :: [IsomorphizingContext] -- Deepest first
                           , isoVariables :: Map Name Name }
  deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------

-- NB. /Right/-biased!
instance Monoid IsomorphizingEnvironment where
  mempty = IsomorphizingEnvironment mempty M.empty
  
  env1 `mappend` env2 =
    IsomorphizingEnvironment { isoContexts  = isoContexts  env2 ++        isoContexts  env1
                             , isoVariables = isoVariables env2 `M.union` isoVariables env1 }

--------------------------------------------------------------------------------

-- Better name?
newtype IsomorphizingT m a =
  IsomorphizingT { getIsomorphizingT :: RWST IsomorphizingEnvironment
                                             (ApplicativeMonoid Q [Dec])
                                             (Set (Name,Name))
                                             (ExceptT String m)
                                             a }
  deriving ( Functor, Applicative, Monad
           , Alternative, MonadPlus, MonadFix
           , MonadIO
           , MonadReader IsomorphizingEnvironment
           , MonadWriter (ApplicativeMonoid Q [Dec])
           , MonadState  (Set (Name,Name))
           , MonadError  String )
instance MonadTrans IsomorphizingT where lift = IsomorphizingT . lift . lift

instance Quasi m => Quasi (IsomorphizingT m) where
  qNewName          = lift . qNewName
  qReport           = (lift .) . qReport
  qRecover          = \_ _ -> throwError "Cannot `qRecover' in `IsomorphizingT'"
  qLookupName       = (lift .) . qLookupName
  qReify            = lift . qReify
  qReifyInstances   = (lift .) . qReifyInstances
  qReifyRoles       = lift . qReifyRoles
  qReifyAnnotations = lift . qReifyAnnotations
  qReifyModule      = lift . qReifyModule
  qLocation         = lift qLocation
  qRunIO            = lift . qRunIO
  qAddDependentFile = lift . qAddDependentFile
  qAddTopDecls      = lift . qAddTopDecls
  qAddModFinalizer  = \_ -> throwError "Cannot `qAddModFinalizer' in `IsomorphizingT'"
  qGetQ             = lift qGetQ
  qPutQ             = lift . qPutQ

type Isomorphizing = IsomorphizingT Identity

runIsomorphizingT :: Functor m
                  => IsomorphizingT m a -> m (Either String (a, Set (Name,Name), DecsQ))
runIsomorphizingT (IsomorphizingT act) =
  runExceptT . fmap munge $ runRWST act mempty S.empty
  where munge (a, kisos, ApplicativeMonoid decs) = (a, kisos, decs)

runIsomorphizing :: Isomorphizing a -> Either String (a, Set (Name,Name), DecsQ)
runIsomorphizing = runIdentity . runIsomorphizingT

spliceIsomorphizing :: IsomorphizingT Q () -> DecsQ
spliceIsomorphizing iso = runIsomorphizingT (learnExistingIsomorphisms *> iso) >>= \case
                            Left  err         -> [] <$ reportError err
                            Right ((),_,decs) -> decs

--------------------------------------------------------------------------------

existingIsomorphisms :: Quasi m => m [(Name,Name)]
existingIsomorphisms = qReify ''StructurallyIsomorphic <&> \case
  ClassI _ instances ->
    [ (srcCon, dstCon)
    | InstanceD _cxt (ConT si `AppT` src `AppT` dst) _body <- instances
    , si == ''StructurallyIsomorphic
    , ConT srcCon <- [headType src]
    , ConT dstCon <- [headType dst] ]
  _ ->
    []

learnExistingIsomorphisms :: Quasi m => IsomorphizingT m ()
learnExistingIsomorphisms = modify' . S.union . S.fromList =<< existingIsomorphisms

--------------------------------------------------------------------------------

isomorphizingError :: Monad m => String -> IsomorphizingT m a
isomorphizingError err = do
  (ctx,ctxs) <- asks isoContexts <&> map isoContextErrorDescription <&> \case
                  []       -> (isoContextErrorDescription mempty, [])
                  ctx:ctxs -> (ctx, filter (not . null) ctxs)
  
  let mainErr | null ctx  = err
              | otherwise = ctx ++ ": " ++ err
      breadcrumbs = concatMap ("\n      ...thus showing that " ++) ctxs
  
  throwError $ mainErr ++ breadcrumbs

--------------------------------------------------------------------------------

withCurrentTypes :: Monad m => Name -> Name -> IsomorphizingT m a -> IsomorphizingT m a
withCurrentTypes srcTy dstTy =
  local (<> mempty{isoContexts = [ mempty{typeIsoContext=Just (srcTy,dstTy)} ]})

withCurrentConstructors :: Monad m => Name -> Name -> IsomorphizingT m a -> IsomorphizingT m a
withCurrentConstructors srcCon dstCon =
  let ctorIsoContext = Just (srcCon, dstCon)
  in local $ \env -> case isoContexts env of
       []       -> env{isoContexts = [ mempty{ctorIsoContext} ]}
       ctx:ctxs -> env{isoContexts = ctx{ctorIsoContext} : ctxs}

--------------------------------------------------------------------------------

withTypeVariables :: Monad m => Map Name Name -> IsomorphizingT m a -> IsomorphizingT m a
withTypeVariables isoVariables = local (<> mempty{isoVariables})

lookupTypeVariable :: Monad m => Name -> IsomorphizingT m (Maybe Name)
lookupTypeVariable x = asks $ M.lookup x . isoVariables

--------------------------------------------------------------------------------

addDecsQ :: Quasi m => DecsQ -> IsomorphizingT m ()
addDecsQ = tell . ApplicativeMonoid

addDecs :: Quasi m => [Dec] -> IsomorphizingT m ()
addDecs = addDecsQ . pure

addDecQ :: Quasi m => DecQ -> IsomorphizingT m ()
addDecQ = addDecsQ . fmap pure

addDec :: Quasi m => Dec -> IsomorphizingT m ()
addDec = addDecs . pure

--------------------------------------------------------------------------------

alreadyIsomorphic :: Monad m => Name -> Name -> IsomorphizingT m Bool
alreadyIsomorphic n1 n2 = gets $ S.member (n1,n2)

learnIsomorphism :: Monad m => Name -> Name -> IsomorphizingT m ()
learnIsomorphism n1 n2 = modify' $ S.insert (n1,n2)

--------------------------------------------------------------------------------

learnTypeSynonym :: Monad m => Name -> [TyVarBndr] -> Type -> IsomorphizingT m Name
learnTypeSynonym lhs = go . reverse where
  go []         (ConT rhs) =
    rhs <$ learnIsomorphism lhs rhs
  go (tvb:tvbs) (tfn `AppT` VarT tv) | tyVarBndrName tvb == tv =
    go tvbs tfn
  go _ _ =
    isomorphizingError $ quoted lhs ++ " is a complex type synonym"

reifyDataType :: Quasi m => Name -> IsomorphizingT m DataType
reifyDataType ty =
  qReify ty >>= \case
    TyConI (TySynD _ty args def) -> reifyDataType =<< learnTypeSynonym ty args def
    TyConI dec                   -> maybe notAlgDT pure $ dataType dec
    _                            -> notAlgDT
  where notAlgDT = isomorphizingError $ quoted ty ++ " is not an algebraic data type"

-- Module-local
for_both_what_err :: Monad m => String -> IsomorphizingT m a
for_both_what_err = isomorphizingError . ("different numbers of " ++)
{-# INLINE for_both_what_err #-}

forBothWhatWith :: Monad m
                => String
                -> (a -> [b])
                -> a -> a
                -> (b -> b -> IsomorphizingT m c)
                -> IsomorphizingT m [c]
forBothWhatWith = forBothWithOr . for_both_what_err

forBothWhat :: Monad m
            => String
            -> [a] -> [b]
            -> (a -> b -> IsomorphizingT m c)
            -> IsomorphizingT m [c]
forBothWhat = forBothOr . for_both_what_err
