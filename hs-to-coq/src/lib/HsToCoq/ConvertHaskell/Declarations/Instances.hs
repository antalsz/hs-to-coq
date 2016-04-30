{-# LANGUAGE LambdaCase, RecordWildCards,
             OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Instances (
  convertClsInstDecl, convertClsInstDecls,
  convertInstanceName
  ) where

import Control.Lens

import Data.Semigroup (Semigroup(..))
import Data.Maybe
import Data.List.NonEmpty (nonEmpty)
import Data.Char
import qualified Data.Text as T

import Control.Monad

import qualified Data.Map.Strict as M

import GHC hiding (Name)
import Bag
import HsToCoq.Util.GHC.Exception

import HsToCoq.PrettyPrint (renderOneLineT)
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Axiomatize

--------------------------------------------------------------------------------

-- Take the instance head and make it into a valid identifier by replacing
-- non-alphanumerics with underscores.  Then, prepend "instance_".
convertInstanceName :: ConversionMonad m => LHsType RdrName -> m Ident
convertInstanceName =   gensym
                    .   ("instance_" <>)
                    .   T.map (\c -> if isAlphaNum c || c == '\'' then c else '_')
                    .   renderOneLineT . renderGallina
                    <=< ghandle (withGhcException $ const . pure $ Var "unknown_type")
                    .   convertLType
                    .   \case
                          L _ (HsForAllTy _ _ _ _ head) -> head
                          lty                           -> lty
  where withGhcException :: (GhcException -> a) -> (GhcException -> a)
        withGhcException = id

--------------------------------------------------------------------------------

data InstanceInfo = InstanceInfo { instanceName  :: !Ident
                                 , instanceHead  :: !Term
                                 , instanceClass :: !Ident }
                  deriving (Eq, Ord, Show, Read)

convertClsInstDeclInfo :: ConversionMonad m => ClsInstDecl RdrName -> m InstanceInfo
convertClsInstDeclInfo ClsInstDecl{..} = do
  let headName (Forall _ t)       = headName t
      headName (App (Var name) _) = pure name
      headName _                  = convUnsupported "strangely-formed instance heads"
  
  instanceName  <- convertInstanceName cid_poly_ty
  instanceHead  <- convertLType        cid_poly_ty
  instanceClass <- headName            instanceHead
  
  pure InstanceInfo{..}

--------------------------------------------------------------------------------

convertClsInstDecl :: ConversionMonad m
                   => ClsInstDecl RdrName
                   -> (InstanceDefinition -> m a)
                   -> Maybe (InstanceInfo -> GhcException -> m a)
                   -> m a
convertClsInstDecl cid@ClsInstDecl{..} rebuild mhandler = do
  info@InstanceInfo{..} <- convertClsInstDeclInfo cid
  
  maybe id (ghandle . ($ info)) mhandler $ do
    cdefs <-   map (\ConvertedDefinition{..} -> (convDefName, maybe id Fun (nonEmpty convDefArgs) $ convDefBody))
          <$> convertTypedBindings (map unLoc $ bagToList cid_binds) M.empty
                                   (\case ConvertedDefinitionBinding cdef -> pure cdef
                                          ConvertedPatternBinding    _ _  -> convUnsupported "pattern bindings in instances")
                                   Nothing
     
    defaults <-  use (defaultMethods.at instanceClass.non M.empty)
             <&> M.toList . M.filterWithKey (\meth _ -> isNothing $ lookup meth cdefs)
     
    rebuild $ InstanceDefinition instanceName [] instanceHead (cdefs ++ defaults) Nothing

--------------------------------------------------------------------------------

convertClsInstDecls :: ConversionMonad m => [ClsInstDecl RdrName] -> m [Sentence]
convertClsInstDecls = (fmap concat .) . traverse $ \cid ->
                         convertClsInstDecl cid
                                            (pure . pure . InstanceSentence)
                                            (Just axiomatizeInstance)
  where axiomatizeInstance InstanceInfo{..} exn = pure
          [ translationFailedComment ("instance " <> renderOneLineT (renderGallina instanceHead)) exn
          , InstanceSentence $ InstanceDefinition
              instanceName [] instanceHead [] (Just $ ProofAdmitted "") ]
