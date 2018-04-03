{-# LANGUAGE RecordWildCards, LambdaCase, FlexibleContexts, OverloadedStrings, OverloadedLists, ScopedTypeVariables #-}

module HsToCoq.ConvertHaskell.Declarations.Class (ClassBody(..), convertClassDecl, getImplicitBindersForClassMember, classSentences) where

import Control.Lens

import Data.Traversable
import qualified Data.List.NonEmpty as NE

import Control.Monad

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import GHC hiding (Name)
import qualified GHC
import Bag
import Class

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.FreeVars

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Sigs
import HsToCoq.ConvertHaskell.Declarations.Notations


data ClassBody = ClassBody ClassDefinition [Notation]
               deriving (Eq, Ord, Read, Show)

instance FreeVars ClassBody where
  freeVars (ClassBody cls nots) = binding' cls $ freeVars nots

-- lookup the signature of a class member and return the list of its
-- implicit binders
getImplicitBindersForClassMember  :: ConversionMonad m => Qualid -> Qualid -> m [Binder]
getImplicitBindersForClassMember className memberName = do
  classDef <- use (classDefns.at className)
  case classDef of
    (Just (ClassDefinition _ _ _ sigs)) ->
        case (lookup memberName sigs) of
          Just sigType -> return $ getImplicits sigType
          Nothing -> return []
    Nothing -> return []

-- strip off any implicit binders at the beginning of a (Coq) type
getImplicits :: Term -> [Binder]
getImplicits (Forall bs t) = if length bs == length imps then imps ++ getImplicits t else imps where
    imps = NE.takeWhile (\b -> case b of
                                 Inferred Implicit _ -> True
                                 Generalized Implicit _ -> True
                                 _ -> False) bs
getImplicits _ = []

convertClassDecl :: ConversionMonad m
                 => LHsContext GhcRn                      -- ^@tcdCtxt@    Context
                 -> Located GHC.Name                      -- ^@tcdLName@   name of the class
                 -> [LHsTyVarBndr GhcRn]                  -- ^@tcdTyVars@  class type variables
                 -> [Located (FunDep (Located GHC.Name))] -- ^@tcdFDs@     functional dependencies
                 -> [LSig GhcRn]                          -- ^@tcdSigs@    method signatures
                 -> LHsBinds GhcRn                        -- ^@tcdMeths@   default methods
                 -> [LFamilyDecl GhcRn]                   -- ^@tcdATs@     associated types
                 -> [LTyFamDefltEqn GhcRn]                -- ^@tcdATDefs@  associated types defaults
                 -> m ClassBody
convertClassDecl (L _ hsCtx) (L _ hsName) ltvs fds lsigs defaults types typeDefaults = do
  unless (null       fds)          $ convUnsupported "functional dependencies"
  unless (null       types)        $ convUnsupported "associated types"
  unless (null       typeDefaults) $ convUnsupported "default associated type definitions"

  name <- var TypeNS hsName
  ctx  <- traverse (fmap (Generalized Coq.Implicit) . convertLType) hsCtx

  args <- convertLHsTyVarBndrs Coq.Explicit ltvs
  kinds <- (++ repeat Nothing) . map Just . maybe [] NE.toList <$> use (edits.classKinds.at name)
  let args' = zipWith go args kinds
       where go (Inferred exp name) (Just t) = Typed Ungeneralizable exp (name NE.:| []) t
             go a _ = a


  (all_sigs :: M.Map Qualid Signature) <- convertLSigs lsigs

  -- implement the class part of "skip method"
  skippedMethodsS <- use (edits.skippedMethods)
  let sigs = (`M.filterWithKey` all_sigs) $ \meth _ ->
        (name,qualidBase meth) `S.notMember` skippedMethodsS

  -- ugh! doesnt work for operators
  -- memberSigs.at name ?= sigs

  defs <- fmap M.fromList $ for (bagToList defaults) $
          convertTypedModuleBinding Nothing . unLoc >=> \case
            Just (ConvertedDefinitionBinding ConvertedDefinition{..}) -> do
--                typeArgs <- getImplicitBindersForClassMember name convDefName
                pure (convDefName, maybe id Fun (NE.nonEmpty (convDefArgs)) convDefBody)
            Just (ConvertedPatternBinding    _ _)                     ->
                convUnsupported "pattern bindings in class declarations"
            Nothing                                                   ->
                convUnsupported $ "skipping a type class method in " ++ show name
  unless (null defs) $ defaultMethods.at name ?= defs

--  liftIO (traceIO (show name))
--  liftIO (traceIO (show defs))

  let classDefn = (ClassDefinition name (args' ++ ctx) Nothing (bimap id sigType <$> M.toList sigs))

  classDefns.at name ?= classDefn

  let nots = concatMap (buildInfixNotations sigs) $ M.keys sigs

  pure $ ClassBody classDefn nots

classSentences :: ClassBody -> [Sentence]
classSentences (ClassBody (ClassDefinition name args ty methods) nots) =
    [ RecordSentence dict_record
    , DefinitionSentence (DefinitionDef Global name args Nothing class_ty)
    , ExistingClassSentence name
    ] ++
    [ DefinitionSentence $
        DefinitionDef Global n
            [Typed Generalizable Implicit [Ident "g"] (app_args (Qualid name))]
            (Just ty)
            (App2 "g" Underscore (app_args (Qualid n')))
    | (n, ty) <- methods
    , let n' = qualidExtendBase "__" n
    ] ++
    map NotationSentence nots
  where
    dict_name = qualidExtendBase "__Dict" name
    dict_build = qualidExtendBase "__Dict_Build" name
    dict_methods = [ (qualidExtendBase "__" name, ty) | (name, ty) <- methods ]
    dict_record  = RecordDefinition dict_name inst_args ty (Just dict_build) dict_methods
    -- The dictionary needs all explicit (type) arguments,
    -- but none of the implicit (constraint) arguments
    inst_args = filter (\b -> b ^? binderExplicitness == Just Explicit) args
    app_args f = foldl App1 f (map Qualid (foldMap (toListOf binderIdents) inst_args))
    class_ty = Forall [ "r" ] $ (app_args (Qualid dict_name)  `Arrow` "r") `Arrow` "r"
