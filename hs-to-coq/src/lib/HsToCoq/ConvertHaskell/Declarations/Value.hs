{-# LANGUAGE RecordWildCards, TupleSections, LambdaCase, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Value (convertValDecls) where

import Control.Lens

import Data.Bitraversable
import Data.Maybe
import Data.Either

import qualified Data.Map as M

import Control.Monad.IO.Class

import GHC hiding (Name)
import Panic

import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Gallina as Coq

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Sigs
import HsToCoq.ConvertHaskell.Declarations.Notations
import HsToCoq.ConvertHaskell.Axiomatize

--------------------------------------------------------------------------------

convertValDecls :: ConversionMonad m => [HsDecl RdrName] -> m [Sentence]
convertValDecls args = do
  (defns, sigs) <- bitraverse pure convertSigs . partitionEithers . flip mapMaybe args $ \case
                     ValD def -> Just $ Left def
                     SigD sig -> Just $ Right sig
                     _        -> Nothing
  
  bindings <- (fmap M.fromList . (convertTypedBindings defns sigs ?? Just axiomatizeBinding))
           $  withConvertedBinding
                (\cdef@ConvertedDefinition{convDefName = name} ->
                   use (edits.redefinitions.at name) >>= ((name,) <$>) . \case
                     Nothing  ->
                       pure $ withConvertedDefinition
                         (DefinitionDef Global)     (pure . DefinitionSentence)
                         (buildInfixNotations sigs) (map    NotationSentence)
                         cdef
                     
                     Just def ->
                       [definitionSentence def] <$ case def of
                         CoqInductiveDef  _ -> editFailure "cannot redefine a value definition into an Inductive"
                         CoqDefinitionDef _ -> pure ()
                         CoqFixpointDef   _ -> pure ())
                (\_ _ -> convUnsupported "top-level pattern bindings")
  
  -- TODO: Mutual recursion
  pure . foldMap (foldMap (bindings M.!)) . topoSortEnvironment $ NoBinding <$> bindings
  
  where axiomatizeBinding :: GhcMonad m => HsBind RdrName -> GhcException -> m (Ident, [Sentence])
        axiomatizeBinding FunBind{..} exn = do
          name <- freeVar $ unLoc fun_id
          pure (name, [translationFailedComment name exn, axiom name])
        axiomatizeBinding _ exn =
          liftIO $ throwGhcExceptionIO exn

