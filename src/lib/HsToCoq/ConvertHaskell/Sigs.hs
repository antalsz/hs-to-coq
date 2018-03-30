{-# LANGUAGE TupleSections, LambdaCase, FlexibleContexts, FlexibleInstances #-}

module HsToCoq.ConvertHaskell.Sigs (
  convertLSigs, convertModuleSigs, convertModuleLSigs,
  HsSignature(..), collectSigs, collectSigsWithErrors, convertSignatures, convertSignature,
  ) where

import Prelude hiding (Num)

import Control.Lens hiding (Level)

import Data.Semigroup (Semigroup(..))
import Data.Bifunctor
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

import HsToCoq.Util.GHC
import HsToCoq.Coq.Gallina

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type



-- From Haskell declaration
data HsSignature = HsSignature { hsSigModule :: Maybe ModuleName
                               , hsSigType   :: LHsSigType GhcRn
                               , hsSigFixity :: Maybe Fixity }


collectSigs :: [(Maybe ModuleName, Sig GhcRn)] -> Either String (Map GHC.Name (Either (String, [ModuleName]) HsSignature))
collectSigs modSigs = do
  let asType   mname = (S.singleton mname, , []) . pure
      --asFixity mname = (S.singleton mname, [], ) . pure

      asTypes    mname lnames sigTy = list $ map ((, asType mname sigTy) . unLoc) lnames
      --asFixities mname lnames fixity = list . map (, asFixity mname fixity) . filter isRdrOperator $ map unLoc lnames

  multimap <-  fmap (M.fromListWith (<>)) . runListT $ list modSigs >>= \case
    (mname, TypeSig lnames (HsWC wcs hsib))
      | null wcs  -> asTypes mname lnames hsib
      | otherwise -> throwError "type wildcards found"
    (mname, ClassOpSig False lnames sigTy) -> asTypes mname lnames sigTy
    --(mname, FixSig           (FixitySig lnames fixity))                                 -> asFixities mname lnames fixity

    (_, ClassOpSig True _ _) -> mempty -- Ignore default methods signatures
    (_, FixSig _)            -> mempty
    (_, InlineSig   _ _)     -> mempty
    (_, SpecSig     _ _ _)   -> mempty
    (_, SpecInstSig _ _)     -> mempty
    (_, MinimalSig  _ _)     -> mempty
    (_, SCCFunSig{})         -> mempty
    (_, CompleteMatchSig{})  -> mempty

--    (_, ClassOpSig True _ _) -> throwError "typeclass-based generic default method signatures"
    (_, PatSynSig  _ _)      -> throwError "pattern synonym signatures"
    (_, IdSig      _)        -> throwError "generated-code signatures"


  pure $ (flip M.mapWithKey (multimap & each._1 %~ S.toList) $ \_key info@(mnames,_,_) ->
    let multiplesError = Left . (,catMaybes mnames)
    in case info of
         ([mname], [ty],  [fixity])  -> Right $ HsSignature mname ty (Just fixity)
         ([mname], [ty],  [])        -> Right $ HsSignature mname ty Nothing
         (_,       [_ty], [_fixity]) -> multiplesError $ "type and fixity signatures split across modules"
         (_,       [_ty], [])        -> multiplesError $ "duplicate type signatures across modules"
         (_,       [],    [_fixity]) -> multiplesError $ "a fixity annotation without a type signature"
         (_,       [],    _)         -> multiplesError $ "multiple fixity annotations without a type signature"
         (_,       _,     [])        -> multiplesError $ "multiple type signatures for the same identifier"
         (_,       _,     _)         -> multiplesError $ "multiple type and fixity signatures for the same identifier"
         )

collectSigsWithErrors :: ConversionMonad m => [(Maybe ModuleName, Sig GhcRn)] -> m (Map GHC.Name HsSignature)
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
convertSignature rdrName (HsSignature hsMod sigTy _hsFix) = do
  name <- ghcPpr rdrName
  maybeFix <- getFixity name
  maybeWithCurrentModule hsMod $ Signature <$> convertLHsSigType sigTy
                                           <*> pure maybeFix

convertSignatures :: ConversionMonad m => Map GHC.Name HsSignature -> m (Map Qualid Signature)
convertSignatures = fmap M.fromList . traverse (\(r,hs) -> (,) <$> (var ExprNS r) <*> convertSignature r hs) . M.toList

convertModuleSigs :: ConversionMonad m => [(Maybe ModuleName, Sig GhcRn)] -> m (Map Qualid Signature)
convertModuleSigs = convertSignatures <=< collectSigsWithErrors

convertModuleLSigs :: ConversionMonad m => [(Maybe ModuleName, LSig GhcRn)] -> m (Map Qualid Signature)
convertModuleLSigs = convertModuleSigs . map (second unLoc)

convertLSigs :: ConversionMonad m => [LSig GhcRn] -> m (Map Qualid Signature)
convertLSigs = convertModuleLSigs . map (Nothing,)
