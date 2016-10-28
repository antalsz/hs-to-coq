{-# LANGUAGE RecordWildCards, LambdaCase, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Value (convertValDecls) where

import Control.Arrow ((&&&))
import HsToCoq.Util.Functor
import Data.Bitraversable
import Data.Maybe
import Data.Either

import qualified Data.Map as M

import Control.Monad.IO.Class

import GHC hiding (Name)
import Panic

import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Gallina as Coq

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Sigs
import HsToCoq.ConvertHaskell.Declarations.Notations
import HsToCoq.ConvertHaskell.Axiomatize

import HsToCoq.ConvertHaskell.InfixNames
import qualified Data.Set as S

--------------------------------------------------------------------------------

convertValDecls :: ConversionMonad m => [HsDecl RdrName] -> m [Sentence]
convertValDecls args = do
  (defns, sigs) <- bitraverse pure convertSigs . partitionEithers . flip mapMaybe args $ \case
                     ValD def -> Just $ Left def
                     SigD sig -> Just $ Right sig
                     _        -> Nothing
  
  bindings <- fmap M.fromList . (convertTypedBindings defns sigs ?? Just axiomatizeBinding)
           $  withConvertedBinding
                ((pure .) $   convDefName
                          &&& withConvertedDefinition (DefinitionDef Global)     (pure . DefinitionSentence)
                                                      (buildInfixNotations sigs) (map    NotationSentence))
                (\_ _ -> convUnsupported "top-level pattern bindings")
  
  -- TODO: Mutual recursion
  pure . foldMap (foldMap (bindings M.!)) . topoSortEnvironment $ NoBinding <$> bindings
  
  where axiomatizeBinding :: GhcMonad m => HsBind RdrName -> GhcException -> m (Ident, [Sentence])
        axiomatizeBinding FunBind{..} exn = do
          name <- freeVar $ unLoc fun_id
          pure (name, [translationFailedComment name exn, axiom name])
        axiomatizeBinding _ exn =
          liftIO $ throwGhcExceptionIO exn

