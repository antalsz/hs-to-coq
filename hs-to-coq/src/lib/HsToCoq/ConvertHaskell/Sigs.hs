{-# LANGUAGE TupleSections, LambdaCase, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Sigs (
  Signature(..), convertSigs, convertLSigs, convertModuleSigs, convertModuleLSigs,
  HsSignature(..), collectSigs, convertSignatures, convertSignature,
  convertFixity
  ) where

import Prelude hiding (Num)

import Control.Lens hiding (Level)

import Data.Semigroup (Semigroup(..))
import Data.Bifunctor
import Data.Bitraversable
import Data.Traversable

import Control.Monad.Except
import HsToCoq.Util.Monad.ListT

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import qualified Data.Set as S

import GHC hiding (Name)
import BasicTypes

import HsToCoq.Util.GHC.RdrName
import HsToCoq.Coq.Gallina

import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type

--------------------------------------------------------------------------------

convertFixity :: Fixity -> (Associativity, Level)
convertFixity (Fixity hsLevel dir) = (assoc, coqLevel) where
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
               
               (5, InfixL) -> 60
               (5, InfixR) -> 61
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

data HsSignature = HsSignature { hsSigModule :: Maybe ModuleName
                               , hsSigType   :: HsType RdrName
                               , hsSigFixity :: Maybe Fixity }

data Signature = Signature { sigType   :: Term
                           , sigFixity :: Maybe (Associativity, Level) }
               deriving (Eq, Ord, Show, Read)

collectSigs :: [(Maybe ModuleName, Sig RdrName)] -> Either String (Map RdrName HsSignature)
collectSigs modSigs = do
  let asType   mname = (S.singleton mname, , []) . pure
      asFixity mname = (S.singleton mname, [], ) . pure
  
  multimap <-  fmap (M.fromListWith (<>)) . runListT $ list modSigs >>= \case
                 (mname, TypeSig lnames (L _ ty) PlaceHolder) -> list $ map ((, asType mname ty) . unLoc) lnames
                 (mname, FixSig  (FixitySig lnames fixity))   -> list . map (, asFixity mname fixity) . filter isRdrOperator $ map unLoc lnames
                  
                 (_, InlineSig   _ _)   -> mempty
                 (_, SpecSig     _ _ _) -> mempty
                 (_, SpecInstSig _ _)   -> mempty
                 (_, MinimalSig  _ _)   -> mempty
                 
                 (_, GenericSig _ _)       -> throwError "typeclass-based default method signatures"
                 (_, PatSynSig  _ _ _ _ _) -> throwError "pattern synonym signatures"
                 (_, IdSig      _)         -> throwError "generated-code signatures"
  
  for (multimap & each._1 %~ S.toList) $ \case
    ([mname], [ty],  [fixity])  -> pure $ HsSignature mname ty (Just fixity)
    ([mname], [ty],  [])        -> pure $ HsSignature mname ty Nothing
    (_,       [_ty], [_fixity]) -> throwError "type and fixity signatures split across modules"
    (_,       [_ty], [])        -> throwError "duplicate type signatures across modules"
    (_,       [],    [_fixity]) -> throwError "a fixity annotation without a type signature"
    (_,       [],    _)         -> throwError "multiple fixity annotations without a type signature"
    (_,       _,     [])        -> throwError "multiple type signatures for the same identifier"
    (_,       _,     _)         -> throwError "multiple type and fixity signatures for the same identifier"

convertSignature :: ConversionMonad m => HsSignature -> m Signature
convertSignature (HsSignature hsMod hsTy hsFix) = maybeWithCurrentModule hsMod
                                                $ Signature <$> convertType hsTy <*> pure (convertFixity <$> hsFix)

convertSignatures :: ConversionMonad m => Map RdrName HsSignature -> m (Map Ident Signature)
convertSignatures = fmap M.fromList . traverse (bitraverse (var ExprNS) convertSignature) . M.toList

convertModuleSigs :: ConversionMonad m => [(Maybe ModuleName, Sig RdrName)] -> m (Map Ident Signature)
convertModuleSigs = either convUnsupported convertSignatures . collectSigs

convertModuleLSigs :: ConversionMonad m => [(Maybe ModuleName, LSig RdrName)] -> m (Map Ident Signature)
convertModuleLSigs = convertModuleSigs . map (second unLoc)

convertSigs :: ConversionMonad m => [Sig RdrName] -> m (Map Ident Signature)
convertSigs = convertModuleSigs . map (Nothing,)

convertLSigs :: ConversionMonad m => [LSig RdrName] -> m (Map Ident Signature)
convertLSigs = convertModuleLSigs . map (Nothing,)
