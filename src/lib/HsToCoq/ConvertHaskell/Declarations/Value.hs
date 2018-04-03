{-# LANGUAGE RecordWildCards, TupleSections, LambdaCase, FlexibleContexts, MultiWayIf #-}

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

convertValDecls :: ConversionMonad m => [HsDecl GhcRn] -> m [Sentence]
convertValDecls mdecls = do
  -- TODO: Don't even convert the signatures for `skipped' things here
  (defns, sigs) <- bitraverse pure convertSigs
                .  partitionEithers
                .  flip mapMaybe mdecls $ \case
                     (ValD def) -> Just $ Left  def
                     (SigD sig) -> Just $ Right sig
                     _          -> Nothing

  bindings <- (fmap M.fromList . (convertTypedModuleBindings defns sigs ?? Just axiomatizeBinding))
           $  withConvertedBinding
                (\cdef@ConvertedDefinition{convDefName = name} -> ((name,) <$>) $ do
                   r <- use (edits.redefinitions.at name)
                   obl <- use (edits.obligations.at name)
                   t <- use (edits.termination.at name)
                   lt <- use (edits.local_termination.at name)
                   let isWellFounded (WellFounded {}) = True
                       isWellFounded _ = False
                   let useProgram = any isWellFounded t || any (any isWellFounded) lt
                   if | Just def <- r               -- redefined
                      -> [definitionSentence def] <$ case def of
                          CoqInductiveDef        _ -> editFailure "cannot redefine a value definition into an Inductive"
                          CoqDefinitionDef       _ -> pure ()
                          CoqFixpointDef         _ -> pure ()
                          CoqInstanceDef         _ -> editFailure "cannot redefine a value definition into an Instance"
                      | Just (WellFounded order) <- t  -- turn into Program Fixpoint
                      ->  pure <$> toProgramFixpointSentence cdef order obl
                      | otherwise                   -- no edit
                      -> let def = DefinitionDef Global (convDefName cdef)
                                                        (convDefArgs cdef)
                                                        (convDefType cdef)
                                                        (convDefBody cdef)
                         in pure $
                            [ if useProgram
                              then ProgramSentence (DefinitionSentence def) obl
                              else DefinitionSentence def ] ++
                            [ NotationSentence n | n <- buildInfixNotations sigs (convDefName cdef) ]
                )(\_ _ -> convUnsupported "top-level pattern bindings")

  -- TODO: Mutual recursion
  pure . foldMap (foldMap (bindings M.!)) . topoSortEnvironment $ NoBinding <$> bindings

  where axiomatizeBinding :: GhcMonad m => HsBind GhcRn -> GhcException -> m (Qualid, [Sentence])
        axiomatizeBinding FunBind{..} exn = do
          name <- freeVar $ unLoc fun_id
          pure (Bare name, [translationFailedComment name exn, axiom (Bare name)])
        axiomatizeBinding _ exn =
          liftIO $ throwGhcExceptionIO exn
