{-# LANGUAGE RecordWildCards, TupleSections, LambdaCase, FlexibleContexts, MultiWayIf #-}

module HsToCoq.ConvertHaskell.Declarations.Value (convertValDecls, convertModuleValDecls) where

import Control.Lens

import Data.Bitraversable
import Data.Maybe
import Data.Either

import qualified Data.Map as M

import Control.Monad.IO.Class

import GHC hiding (Name)
import qualified GHC
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

convertModuleValDecls :: ConversionMonad m => [(Maybe ModuleName, HsDecl GHC.Name)] -> m [Sentence]
convertModuleValDecls mdecls = do
  -- TODO: Don't even convert the signatures for `skipped' things here
  (defns, sigs) <- bitraverse pure convertModuleSigs
                .  partitionEithers
                .  flip mapMaybe mdecls $ \case
                     (mname, ValD def) -> Just $ Left  (mname, def)
                     (mname, SigD sig) -> Just $ Right (mname, sig)
                     _                 -> Nothing

  bindings <- (fmap M.fromList . (convertTypedModuleBindings defns sigs ?? Just axiomatizeBinding))
           $  withConvertedBinding
                (\cdef@ConvertedDefinition{convDefName = name} -> ((name,) <$>) $ do
                   r <- use (edits.redefinitions.at name)
                   t <- use (edits.termination.at name)
                   if | Just def <- r               -- redefined
                      -> [definitionSentence def] <$ case def of
                          CoqInductiveDef        _ -> editFailure "cannot redefine a value definition into an Inductive"
                          CoqDefinitionDef       _ -> pure ()
                          CoqFixpointDef         _ -> pure ()
                          CoqProgramFixpointDef  _ -> pure ()
                          CoqInstanceDef         _ -> editFailure "cannot redefine a value definition into an Instance"
                      | Just (order, tactic) <- t  -- turn into Program Fixpoint
                      ->  pure <$> toProgramFixpointSentence cdef order tactic
                      | otherwise                   -- no edit
                      -> let def = DefinitionDef Global (convDefName cdef)
                                                        (convDefArgs cdef)
                                                        (convDefType cdef)
                                                        (convDefBody cdef)
                         in pure $
                            [ DefinitionSentence def ] ++
                            [ NotationSentence n | n <- buildInfixNotations sigs (convDefName cdef) ]
                )(\_ _ -> convUnsupported "top-level pattern bindings")

  -- TODO: Mutual recursion
  pure . foldMap (foldMap (bindings M.!)) . topoSortEnvironment $ NoBinding <$> bindings

  where axiomatizeBinding :: GhcMonad m => HsBind GHC.Name -> GhcException -> m (Qualid, [Sentence])
        axiomatizeBinding FunBind{..} exn = do
          name <- freeVar $ unLoc fun_id
          pure (Bare name, [translationFailedComment name exn, axiom (Bare name)])
        axiomatizeBinding _ exn =
          liftIO $ throwGhcExceptionIO exn

convertValDecls :: ConversionMonad m => [HsDecl GHC.Name] -> m [Sentence]
convertValDecls = convertModuleValDecls . map (Nothing,)
