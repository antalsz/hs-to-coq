{-# LANGUAGE TupleSections, LambdaCase, FlexibleContexts, FlexibleInstances #-}

module HsToCoq.ConvertHaskell.Sigs (
  convertSigs, convertLSigs, convertModuleSigs, convertModuleLSigs,
  HsSignature(..), collectSigs, collectSigsWithErrors, convertSignatures, convertSignature,
  convertFixity,
  recordFixitiesWithErrors
  ) where

import Prelude hiding (Num)

import Control.Lens hiding (Level)

import Data.Semigroup (Semigroup(..))
import Data.Bifunctor
import Data.Bitraversable (bitraverse)
import Data.Maybe
import Data.List (intercalate)
import qualified Data.Text as T

import Control.Monad.Except
import HsToCoq.Util.Monad.ListT

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import qualified Data.Set as S

import GHC hiding (Name)
import qualified GHC
import BasicTypes

import HsToCoq.Util.GHC
import HsToCoq.Util.GHC.Name (isOperator)
import HsToCoq.Coq.Gallina

import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type


--------------------------------------------------------------------------------

convertFixity :: Fixity -> (Associativity, Level)
convertFixity (Fixity _srcText hsLevel dir) = (assoc, coqLevel) where
  assoc = case dir of
            InfixL -> LeftAssociativity
            InfixR -> RightAssociativity
            InfixN -> NoAssociativity

  -- TODO These don't all line up between Coq and Haskell; for instance, Coq's
  -- @_ || _@ is at level 50 (Haskell 6), whereas Haskell's @(||)@ is at level 2
  -- (Coq 80).
  coqLevel = Level $ case (hsLevel, dir) of
               (0, InfixL) -> 90
               (0, InfixR) -> 91
               (0, InfixN) -> 92

               (1, InfixL) -> 86
               (1, InfixR) -> 85
               (1, InfixN) -> 87

               (2, InfixL) -> 81
               (2, InfixR) -> 80
               (2, InfixN) -> 82

               (3, InfixL) -> 76
               (3, InfixR) -> 75
               (3, InfixN) -> 77

               (4, InfixL) -> 71
               (4, InfixR) -> 72
               (4, InfixN) -> 70

               (5, InfixL) -> 61
               (5, InfixR) -> 60
               (5, InfixN) -> 62

               (6, InfixL) -> 50
               (6, InfixR) -> 51
               (6, InfixN) -> 52

               (7, InfixL) -> 40
               (7, InfixR) -> 41
               (7, InfixN) -> 42

               (8, InfixL) -> 31
               (8, InfixR) -> 30
               (8, InfixN) -> 32

               (_, _)      -> 99

--------------------------------------------------------------------------------

-- From Haskell declaration
data HsSignature = HsSignature { hsSigModule :: Maybe ModuleName
                               , hsSigType   :: HsType GHC.Name
                               , hsSigFixity :: Maybe Fixity }


-- Only collect fixity declarations
collectFixities :: [(Maybe ModuleName, Sig GHC.Name)] -> Map GHC.Name (Either (String, [ModuleName]) Fixity)
collectFixities modSigs =
  let  asFixity :: Maybe ModuleName -> Fixity -> (S.Set ModuleName,[Fixity])
       asFixity mname f = (maybe S.empty S.singleton mname, [f] )
       asFixities :: Maybe ModuleName -> [Located GHC.Name] -> Fixity -> Map GHC.Name (S.Set ModuleName, [Fixity])
       asFixities mname lnames fixity = M.fromListWith (<>) . map (, asFixity mname fixity) . filter isOperator $ map unLoc lnames

       processSig :: (Maybe ModuleName, Sig GHC.Name) -> Map GHC.Name (S.Set ModuleName, [Fixity])
       processSig (mname, FixSig  (FixitySig lnames fixity)) = asFixities mname lnames fixity
       processSig (_,_) = mempty

       processFixity :: (S.Set ModuleName, [Fixity]) -> Either (String, [ModuleName]) Fixity
       processFixity (_, [fixity]) = Right fixity
       processFixity (mnames, fixities) = Left ("Multiple fixities", S.toList mnames)
   in
     fmap processFixity (foldMap processSig modSigs)

recordFixitiesWithErrors :: ConversionMonad m => [(Maybe ModuleName, Sig GHC.Name)] -> m (Map GHC.Name ())
recordFixitiesWithErrors modSigs = M.traverseWithKey multiplesError (collectFixities modSigs) where
   multiplesError :: ConversionMonad m => GHC.Name -> Either (String, [ModuleName]) Fixity -> m ()
   multiplesError name (Left (err,mnames)) = do
       nameStr <- T.unpack <$> ghcPpr name
       convUnsupported $ err
                          ++ " for `" ++ nameStr ++ "'"
                          ++ case unsnoc $ map (("`" ++) . (++ "'") . moduleNameString) mnames of
                               Nothing              -> ""
                               Just ([],name)       -> " in the module " ++ name
                               Just ([name1],name2) -> " in the modules " ++ name1 ++ " and " ++ name2
                               Just (names, name')  -> " in the modules " ++ intercalate ", " names  ++ " and " ++ name'
   multiplesError name (Right sig) = ghcPpr name >>= \n -> recordFixity n (convertFixity sig)

collectSigs :: [(Maybe ModuleName, Sig GHC.Name)] -> Either String (Map GHC.Name (Either (String, [ModuleName]) HsSignature))
collectSigs modSigs = do
  let asType   mname = (S.singleton mname, , []) . pure
      --asFixity mname = (S.singleton mname, [], ) . pure

      asTypes    mname lnames ty     = list $ map ((, asType mname ty) . unLoc) lnames
      --asFixities mname lnames fixity = list . map (, asFixity mname fixity) . filter isRdrOperator $ map unLoc lnames


  -- TODO RENAMER implicitTyVars
  multimap <-  fmap (M.fromListWith (<>)) . runListT $ list modSigs >>= \case
    (mname, TypeSig lnames (HsIB implicitTyVars (HsWC wcs _ss (L _ ty))))
      | null wcs  -> asTypes mname lnames ty
      | otherwise -> throwError "type wildcards found"
    (mname, ClassOpSig False lnames (HsIB implicitTyVars (L _ ty)))  ->
      asTypes mname lnames ty
    --(mname, FixSig           (FixitySig lnames fixity))                                 -> asFixities mname lnames fixity
    
    (_, FixSig _)          -> mempty
    (_, InlineSig   _ _)   -> mempty
    (_, SpecSig     _ _ _) -> mempty
    (_, SpecInstSig _ _)   -> mempty
    (_, MinimalSig  _ _)   -> mempty
    
    (_, ClassOpSig True _ _) -> throwError "typeclass-based generic default method signatures"
    (_, PatSynSig  _ _)      -> throwError "pattern synonym signatures"
    (_, IdSig      _)        -> throwError "generated-code signatures"


  pure $ (flip M.mapWithKey (multimap & each._1 %~ S.toList) $ \key info@(mnames,_,_) ->

    let multiplesError = Left . (,catMaybes mnames)
    in case info of
         ([mname], [ty],  [fixity])  -> Right $ HsSignature mname ty (Just fixity)
         ([mname], [ty],  [])        -> Right $ HsSignature mname ty Nothing
         (_,       [_ty], [_fixity]) -> multiplesError $ "type and fixity signatures split across modules"
         (_,       [_ty], [])        -> multiplesError $ "duplicate type signatures across modules"
         (_,       [],    [_fixity]) -> multiplesError $ "a fixity annotation without a type signature"
         (_,       [],    _)         -> multiplesError $ "multiple fixity annotations without a type signature"
         (_,       _,     [])        -> multiplesError $ "multiple type signatures for the same identifier"
         (_,       _,     _)         -> multiplesError $ "multiple type and fixity signatures for the same identifier")

collectSigsWithErrors :: ConversionMonad m => [(Maybe ModuleName, Sig GHC.Name)] -> m (Map GHC.Name HsSignature)
collectSigsWithErrors =
  either convUnsupported (M.traverseWithKey multiplesError) . collectSigs
  where multiplesError name (Left (err, mnames)) = do
          nameStr <- T.unpack <$> ghcPpr name
          convUnsupported $ err
                          ++ " for `" ++ nameStr ++ "'"
                          ++ case unsnoc $ map (("`" ++) . (++ "'") . moduleNameString) mnames of
                               Nothing              -> ""
                               Just ([],name)       -> " in the module " ++ name
                               Just ([name1],name2) -> " in the modules " ++ name1 ++ " and " ++ name2
                               Just (names, name')  -> " in the modules " ++ intercalate ", " names  ++ " and " ++ name'
        multiplesError _ (Right sig) =
          pure sig

convertSignature :: ConversionMonad m => GHC.Name -> HsSignature -> m Signature
convertSignature rdrName (HsSignature hsMod hsTy hsFix) = do
  name <- ghcPpr rdrName
  maybeFix <- getFixity name
  maybeWithCurrentModule hsMod $ Signature <$> convertType (addForAll hsTy)
                                           <*> pure maybeFix
  where addForAll hsTy'@(HsForAllTy _ _) = hsTy'
        addForAll hsTy'                  = HsForAllTy [] $ noLoc hsTy'

  -- The top-level 'HsForAllTy' was added implicitly in GHC 7.10; we add it
  -- explicitly now.  Without it, we don't generate the implicit type variable
  -- bindings.  I can't decide if adding it is a huge hack or not.
  --
  -- TODO: Should generating implicit type variables be its own thing?  Does
  -- this same 'HsForAllTy' trick, however it's implemented, need to go
  -- elsewhere?  Should it be part of 'convertType'?

convertSignatures :: ConversionMonad m => Map GHC.Name HsSignature -> m (Map Ident Signature)
convertSignatures = fmap M.fromList . traverse (\(r,hs) -> (,) <$> (var ExprNS r) <*> convertSignature r hs) . M.toList

convertModuleSigs :: ConversionMonad m => [(Maybe ModuleName, Sig GHC.Name)] -> m (Map Ident Signature)
convertModuleSigs sigs =
  (convertSignatures <=< collectSigsWithErrors) sigs

convertModuleLSigs :: ConversionMonad m => [(Maybe ModuleName, LSig GHC.Name)] -> m (Map Ident Signature)
convertModuleLSigs = convertModuleSigs . map (second unLoc)

convertSigs :: ConversionMonad m => [Sig GHC.Name] -> m (Map Ident Signature)
convertSigs = convertModuleSigs . map (Nothing,)

convertLSigs :: ConversionMonad m => [LSig GHC.Name] -> m (Map Ident Signature)
convertLSigs = convertModuleLSigs . map (Nothing,)
