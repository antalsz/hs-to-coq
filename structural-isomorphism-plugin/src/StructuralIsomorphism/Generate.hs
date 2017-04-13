{-# LANGUAGE FlexibleContexts,
             NamedFieldPuns, RecordWildCards,
             LambdaCase, TupleSections,
             TemplateHaskell #-}

module StructuralIsomorphism.Generate (
  -- * Template Haskell entry point
  structurallyIsomorphic,
  
  -- * Isomorphism generation
  ensureIsomorphic,
  ensureIsomorphicTypes,
  ensureIsomorphicDeclarations,
  buildIsomorphismFunction,

  -- * Equivalences between constructors
  ConstructorEquivalence(..), swapConstructorEquivalence
) where

import Data.Bifunctor
import Control.Monad

import Data.Maybe
import Data.Foldable

import qualified Data.Map.Strict as M

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import StructuralIsomorphism.TH.Util
import StructuralIsomorphism.Class
import StructuralIsomorphism.Declarations
import StructuralIsomorphism.Isomorphizing

--------------------------------------------------------------------------------

data ConstructorEquivalence = ConstructorEquivalence { srcCon  :: !Name
                                                     , dstCon  :: !Name
                                                     , conArgs :: !Int }
                            deriving (Eq, Ord, Show)

swapConstructorEquivalence :: ConstructorEquivalence -> ConstructorEquivalence
swapConstructorEquivalence equiv =
  equiv{srcCon = dstCon equiv, dstCon = srcCon equiv}

--------------------------------------------------------------------------------

-- If @ensureIsomorphicTypes ty1 ty2@ returns successfully, then @ty1@ and @ty2@
-- were isomorphic and all the instances that proves this have been generated
-- (hence "ensure").
ensureIsomorphicTypes :: Quasi m => Type -> Type -> IsomorphizingT m ()
ensureIsomorphicTypes uty1 uty2 = case (outerNormalizeType uty1, outerNormalizeType uty2) of
  (VarT x1, VarT x2) -> do
    x2' <- lookupTypeVariable x1
    unless (x2' == Just x2) $
      isomorphizingError "mismatched type variables"
  
  (ConT c1, ConT c2) -> do
    ensureIsomorphic c1 c2
  
  (AppT lty1 rty1, AppT lty2 rty2) ->
    ensureIsomorphicTypes lty1 lty2 *> ensureIsomorphicTypes rty1 rty2
  
  (ForallT _tvs1 _cxt1 _ty1, ForallT _tvs2 _cxt2 _ty2) ->
    error "forall"

  -- If the types aren't inhabitable, we don't worry about it and let GHC
  -- complain later if there were any issues
  (PromotedT _p1,      PromotedT _p2)      -> pure ()
  (EqualityT,          EqualityT)          -> pure ()
  (PromotedTupleT _n1, PromotedTupleT _n2) -> pure ()
  (PromotedNilT,       PromotedNilT)       -> pure ()
  (PromotedConsT,      PromotedConsT)      -> pure ()
  (StarT,              StarT)              -> pure ()
  (ConstraintT,        ConstraintT)        -> pure ()
  (LitT _l1,           LitT _l2)           -> pure ()
  
  (ty1, ty2) ->
    isomorphizingError $  "type mismatch: " ++ quoted ty1 ++ " <> " ++ quoted ty2

-- If @ensureIsomorphicDeclarations dt1 dt2@ returns successfully, then @dt1@
-- and @dt2@ were isomorphic, all the necessary instances that prove this for
-- referenced types this have been generated (hence "ensure"), and the
-- constructor mappings that prove the isomorphism of @dt1@ and @dt2@ are
-- returned.  Notably, the instance(s) making @dt1@ and @dt2@ isomorphic is
-- (are) *not* generated.
ensureIsomorphicDeclarations :: Quasi m
                             => DataType -> DataType
                             -> IsomorphizingT m [ConstructorEquivalence]
ensureIsomorphicDeclarations dt1 dt2 = do
  -- Let GHC error about data type contexts later if there's an issue
  -- Skip the name; that's what we're isomorphizing
  -- Skip the deriving clause; it's irrelevant

  -- That leaves only parameters and constructors!
  params <- forBothWhatWith "data type parameters" dtParameters dt1 dt2 $ \tvb1 tvb2 ->
              case (tvb1,tvb2) of
                -- If only one has a kind, assume that they match and let GHC
                -- complain later if we're wrong
                (PlainTV a1,      PlainTV  a2)     -> pure (a1,a2)
                (PlainTV a1,      KindedTV a2 _k2) -> pure (a1,a2)
                (KindedTV a1 _k1, PlainTV  a2)     -> pure (a1,a2)
                (KindedTV a1 k1,  KindedTV a2 k2)  -> (a1,a2) <$ ensureIsomorphicTypes k1 k2
  
  withTypeVariables (M.fromList params) $
    forBothWhatWith "constructors" dtConstructors dt1 dt2 $ \con1 con2 ->
      withCurrentConstructors (conName con1) (conName con2) $ do
        conArgs <- fmap length
                .  forBothWhatWith "constructor arguments"
                                   -- Coq loses strictness information
                                   (map snd . conArguments) 
                                   con1 con2
                $  ensureIsomorphicTypes
        pure $ ConstructorEquivalence { srcCon = conName con1
                                      , dstCon = conName con2
                                      , conArgs }

buildIsomorphismFunction :: Exp -> [ConstructorEquivalence] -> ExpQ
buildIsomorphismFunction conv equivs = do
  arg <- newName "arg"
  lamE [varP arg] $ caseE (varE arg)
    [ do fields <- replicateM conArgs $ newName "field"
         pure $ Match (ConP srcCon $ map VarP fields)
                      (NormalB . foldl' AppE (ConE dstCon)
                               $ map ((conv `AppE`) . VarE) fields)
                      []
    |  ConstructorEquivalence{..} <- equivs ]

reifyRolesIfNonIsomorphic :: Quasi m
                          => Name -> Name
                          -> ([Role] -> [Role] -> IsomorphizingT m ())
                          -> IsomorphizingT m ()
reifyRolesIfNonIsomorphic n1 n2 cont = do
  knownIso <- alreadyIsomorphic n1 n2
  unless knownIso $ do
    roles1 <- qReifyRoles n1
    unless (n1 == n2 && null roles1) $ do
      roles2 <- qReifyRoles n2
      cont roles1 roles2

ensureIsomorphic :: Quasi m => Name -> Name -> IsomorphizingT m ()
ensureIsomorphic n1 n2 =
  withCurrentTypes n1 n2 . reifyRolesIfNonIsomorphic n1 n2 $ \roles1 roles2 -> do
    -- Optimistic insertion: helps avoid infinite recursion, handles the
    -- reflexivity case
    learnIsomorphism n1 n2
    learnIsomorphism n2 n1
    
    let structurallyIsomorphicT src dst =
          ConT ''StructurallyIsomorphic `AppT` src `AppT` dst
    
    ((args1,args2),cxt) <-
      fmap (bimap unzip catMaybes . unzip) .
      forBothWhat "data type parameters" roles1 roles2 $ \r1 r2 -> do
        unless (r1 == r2) $ isomorphizingError "role mismatch"
        
        src <- qNewName "src"
        dst <- qNewName "dst"
        
        let constraint = structurallyIsomorphicT (VarT src) (VarT dst)
        
        ((src,dst),) <$> case r1 of
          NominalR          -> pure $ Just constraint
          RepresentationalR -> pure $ Just constraint
          PhantomR          -> pure Nothing
          InferR            -> isomorphizingError "unknown type role"
    
    dt1 <- reifyDataType n1
    dt2 <- reifyDataType n2
     
    equivs <- ensureIsomorphicDeclarations dt1 dt2
    let sviuqe = map swapConstructorEquivalence equivs
     
    let defineIsomorphism fn equivs = do
          lambda <- buildIsomorphismFunction (VarE fn) equivs
          pure $ ValD (VarP fn) (NormalB lambda) []
        
        makeStructurallyIsomorphic n1 n2 equivs sviuqe = addDecQ $
          InstanceD Nothing cxt
                    (structurallyIsomorphicT (foldl' AppT (ConT n1) (map VarT args1))
                                             (foldl' AppT (ConT n2) (map VarT args2)))
                    <$> sequenceA [ defineIsomorphism 'to   equivs
                                  , defineIsomorphism 'from sviuqe ]
     
    makeStructurallyIsomorphic n1 n2 equivs sviuqe
    when (n1 /= n2) $ makeStructurallyIsomorphic n2 n1 sviuqe equivs

--------------------------------------------------------------------------------

structurallyIsomorphic :: Name -> Name -> DecsQ
structurallyIsomorphic = (spliceIsomorphizing .) . ensureIsomorphic
