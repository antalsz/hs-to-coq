{-# LANGUAGE LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Value (convertValDecls) where

import Data.Semigroup (Semigroup(..))
import Data.Bitraversable
import Data.Foldable
import Data.Maybe
import Data.Either
import qualified Data.Text as T

import Control.Monad.IO.Class

import GHC hiding (Name)
import Panic

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Sigs
import HsToCoq.ConvertHaskell.Declarations.Notations

--------------------------------------------------------------------------------

convertValDecls :: ConversionMonad m => [HsDecl RdrName] -> m [Sentence]
convertValDecls args = do
  (defns, sigs) <- bitraverse pure convertSigs . partitionEithers . flip mapMaybe args $ \case
                     ValD def -> Just $ Left def
                     SigD sig -> Just $ Right sig
                     _        -> Nothing
  
  let axiomatize :: GhcMonad m => HsBind RdrName -> GhcException -> m [Sentence]
      axiomatize FunBind{..} exn = do
        name <- freeVar $ unLoc fun_id
        pure [ CommentSentence . Comment
                 $ "Translating `" <> name <> "' failed: " <> T.pack (show exn)
             , AssumptionSentence . Assumption Axiom . UnparenthesizedAssums [name]
                 $ Forall [Typed Ungeneralizable Coq.Implicit [Ident "A"] $ Sort Type] (Var "A") ]
      axiomatize _ exn =
        liftIO $ throwGhcExceptionIO exn
  
  fold <$> convertTypedBindings defns sigs
             (withConvertedBinding
               (pure . withConvertedDefinition (DefinitionDef Global)     (pure . DefinitionSentence)
                                               (buildInfixNotations sigs) (map    NotationSentence))
               (\_ _ -> convUnsupported "top-level pattern bindings"))
             (Just axiomatize)
