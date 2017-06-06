{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedStrings,
             ScopedTypeVariables,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Instances (
  convertClsInstDecl, convertClsInstDecls, convertModuleClsInstDecls,
  convertInstanceName
  ) where

import Control.Lens

import Data.Semigroup (Semigroup(..))
import HsToCoq.Util.Function
import Data.Maybe
import qualified Data.List.NonEmpty as NE
import Data.Char
import qualified Data.Text as T

import Control.Monad

import qualified Data.Map.Strict as M


import GHC hiding (Name)
import Bag
import HsToCoq.Util.GHC.Exception

import HsToCoq.PrettyPrint (renderOneLineT)
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Subst
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Axiomatize
import HsToCoq.ConvertHaskell.Declarations.Class

import Debug.Trace

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
                          L _ (HsForAllTy _ head) -> head
                          lty                     -> lty
  where withGhcException :: (GhcException -> a) -> (GhcException -> a)
        withGhcException = id

--------------------------------------------------------------------------------
{- Haskell:
      instance Functor ((->) r)
   InstanceInfo
      Name = "Functor__arr_r___"
      Head = "Functor (_(->)_ r)" as a Coq term, with free variable
      Class = "Functor"

   Haskell:
      instance Eq a => Eq [a]
   InstanceInfo
      Name = "Eq_list____"
      Head = "forall `{Eq a}, Eq (list a)"
      Class = "Eq"

-}
data InstanceInfo = InstanceInfo { instanceName  :: !Ident
                                 , instanceHead  :: !Term
                                 , instanceClass :: !Ident }
                  deriving (Eq, Ord, Show, Read)

convertClsInstDeclInfo :: ConversionMonad m => ClsInstDecl RdrName -> m InstanceInfo
convertClsInstDeclInfo ClsInstDecl{..} = do
  instanceName  <- convertInstanceName $ hsib_body cid_poly_ty
  instanceHead  <- convertLType        $ hsib_body cid_poly_ty
  instanceClass <- maybe (convUnsupported "strangely-formed instance heads")
                         (pure . renderOneLineT . renderGallina)
                    $ termHead instanceHead

  pure InstanceInfo{..}

--------------------------------------------------------------------------------

convertClsInstDecl :: ConversionMonad m
                   => ClsInstDecl RdrName          -- Haskell Instance we are converting
                   -> (InstanceDefinition -> m a)  --
                   -> Maybe (InstanceInfo -> GhcException -> m a) -- error handling argument
                   -> m a
convertClsInstDecl cid@ClsInstDecl{..} rebuild mhandler = do
  info@InstanceInfo{..} <- convertClsInstDeclInfo cid

  -- TODO: Do we need the 'HsForAllTy' trick here to handle instance
  -- superclasses?  Or is the generalization backtick enough?
  maybe id (ghandle . ($ info)) mhandler $ do

    cbinds   <- convertTypedBindings (map unLoc $ bagToList cid_binds) M.empty -- the type signatures (note: no InstanceSigs)
                                   (\case ConvertedDefinitionBinding cdef -> pure cdef
                                          ConvertedPatternBinding    _ _  -> convUnsupported "pattern bindings in instances")
                                   Nothing -- error handler

    cdefs <-  mapM (\ConvertedDefinition{..} -> do
                       typeArgs <- getImplicitBindersForClassMember instanceClass convDefName
                       return (convDefName, maybe id Fun (NE.nonEmpty (typeArgs ++ convDefArgs)) $ convDefBody)) cbinds

    defaults <-  use (defaultMethods.at instanceClass.non M.empty)
                 -- lookup default methods in the global state, using the empty map if the class name is not found
                 -- otherwise gives you a map
                 -- <$> is flip fmap
             <&> M.toList . M.filterWithKey (\meth _ -> isNothing $ lookup meth cdefs)

    rebuild $ InstanceDefinition instanceName [] instanceHead (cdefs ++ defaults) Nothing

--------------------------------------------------------------------------------

convertModuleClsInstDecls :: forall m. ConversionMonad m
                          => [(Maybe ModuleName, ClsInstDecl RdrName)] -> m [Sentence]
convertModuleClsInstDecls = fmap concat .: traverse $ maybeWithCurrentModule .*^ \cid ->
                               convertClsInstDecl cid rebuild
                                                  (Just axiomatizeInstance)
  where rebuild :: InstanceDefinition -> m [Sentence]
        rebuild = topoSort -- (pure . pure . InstanceSentence)

        -- what to do if instance conversion fails
        -- make an axiom that admits the instance declaration

        axiomatizeInstance InstanceInfo{..} exn = pure
          [ translationFailedComment ("instance " <> renderOneLineT (renderGallina instanceHead)) exn
          , InstanceSentence $ InstanceDefinition
              instanceName [] instanceHead [] (Just $ ProofAdmitted "") ]


--------------------------------------------------------------------------------

-- Topo sort the instance members and try to lift some of them outside of
-- the instance declaration.

topoSort :: forall m.  ConversionMonad m => InstanceDefinition -> m [Sentence]
topoSort (InstanceDefinition instanceName params ty members mp) = go sorted M.empty where

        go :: [ NE.NonEmpty Ident ] -> M.Map Ident Term -> m [ Sentence ]
        go []      sub = mkID sub
        go (hd:tl) sub = do (s1,bnds) <- mkDefnGrp (NE.toList hd) sub
                            s2        <- go tl bnds
                            return (s1 ++ s2)

        m        = M.fromList members
        sorted   = topoSortEnvironment m

        -- TODO: multiparameter type classes
        (className, instTy) = case ty of
                                App (Qualid (Bare cn)) ((PosArg a) NE.:| []) -> (cn, a)
                                _ -> error ("cannot deconstruct instance head" ++ (show ty))



        -- TODO: figure out which members can actually stay in the instance declaration
        keepable = M.empty

        -- lookup the type of the class member and then add extra quantifiers
        -- from the class & instance definitions
        mkTy :: Ident -> m (Maybe Term)
        mkTy memberName = do sigs      <- use (memberSigs.at className.non M.empty)
                             classDef  <- use (classDefns.at className)
                             case (classDef, M.lookup memberName sigs) of
                               (Just (ClassDefinition _ (Inferred Explicit (Ident var):_) _ _), Just Signature{..}) -> do
                                   -- TODO: the insTy could have a free variables in it, should generalize those in the type
                                   -- note: we don't keep track of inscope variables here, so currently this includes "list", for example
                                   let otherVars = getFreeVars instTy
                                   return $ Just (subst (M.singleton var instTy) sigType)
                               (Just cd,  Nothing) ->
                                  trace ("Cannot find sig for" ++ show memberName) $ return Nothing
                               _ -> trace ("OOPS! Cannot construct types for this class def: " ++ (show classDef) ++ "\n") $
                                   return Nothing

        -- given a group of identifiers turn them into
        mkDefnGrp :: [ Ident ] -> (M.Map Ident Term) -> m ([ Sentence ], M.Map Ident Term)
        mkDefnGrp [] sub = return ([], sub)
        mkDefnGrp [ v ] sub = do
           v'  <- gensym v
           mty <- mkTy v
           pure ([ DefinitionSentence (DefinitionDef Local v' [] mty (subst sub (m M.! v))) ], (M.insert v (Qualid (Bare v')) sub))
        mkDefnGrp many sub = -- TODO: mutual recursion (Now: give up)
           trace ("Giving up on mutual recursion" ++ show many) $
             return ([], sub)

        mkID :: M.Map Ident Term -> m [ Sentence ]
        mkID mems = do
           let kept = M.toList (M.map (subst mems) keepable)
           mems' <- mapM (\(v,b) -> do typeArgs <- getImplicitBindersForClassMember className v
                                       case (NE.nonEmpty typeArgs) of
                                         Nothing ->
                                           return (v,b)
                                         Just args ->
                                           return (v, Fun args b)) (M.toList mems)

           pure [InstanceSentence (InstanceDefinition instanceName params ty (kept ++ mems') mp)]




--------------------------------------------------------------------------------

convertClsInstDecls :: ConversionMonad m => [ClsInstDecl RdrName] -> m [Sentence]
convertClsInstDecls = convertModuleClsInstDecls . map (Nothing,)
