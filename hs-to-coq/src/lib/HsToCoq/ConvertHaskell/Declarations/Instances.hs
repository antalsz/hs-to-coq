{-# LANGUAGE LambdaCase, RecordWildCards,
             OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Instances (convertClsInstDecl, convertClsInstDecls) where

import Data.Semigroup (Semigroup(..))
import Data.Char
import Data.List.NonEmpty (nonEmpty)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

import qualified Data.Map.Strict as M

import GHC hiding (Name)
import Bag

import HsToCoq.PrettyPrint (renderOneLine, displayT)
import HsToCoq.Coq.Gallina

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Expr

--------------------------------------------------------------------------------

convertClsInstDecl :: ConversionMonad m => ClsInstDecl RdrName -> m InstanceDefinition
convertClsInstDecl ClsInstDecl{..} = do
  cdefs <-   map (\ConvertedDefinition{..} -> (convDefName, maybe id Fun (nonEmpty convDefArgs) $ convDefBody))
        <$> convertTypedBindings (map unLoc $ bagToList cid_binds) M.empty
                                 (\case ConvertedDefinitionBinding cdef -> pure cdef
                                        ConvertedPatternBinding    _ _  -> convUnsupported "pattern bindings in instances")
                                 Nothing
  headType <- convertLType cid_poly_ty
  
  -- TODO add a unique
  instanceNameCore <- fmap ( T.map (\c -> if isAlphaNum c || c == '\'' then c else '_')
                           . TL.toStrict . displayT . renderOneLine . renderGallina )
                   .  convertLType $ case cid_poly_ty of
                         L _ (HsForAllTy _ _ _ _ head) -> head
                         lty                           -> lty
  
  pure $ InstanceDefinition ("__instance_" <> instanceNameCore <> "__")
                            []
                            headType
                            cdefs

--------------------------------------------------------------------------------

convertClsInstDecls :: ConversionMonad m => [ClsInstDecl RdrName] -> m [Sentence]
convertClsInstDecls = traverse $ fmap InstanceSentence . convertClsInstDecl
