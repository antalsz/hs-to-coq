{-# LANGUAGE RecordWildCards, LambdaCase, FlexibleContexts, OverloadedStrings, OverloadedLists #-}

module HsToCoq.ConvertHaskell.Declarations.Class (ClassBody(..), convertClassDecl, getImplicitBindersForClassMember, classSentences) where

import Control.Lens

import Data.Traversable
import qualified Data.List.NonEmpty as NE

import Control.Monad
import Data.Monoid

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
import HsToCoq.ConvertHaskell.InfixNames
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Sigs
import HsToCoq.ConvertHaskell.Declarations.Notations

----------------------------
import Control.Monad.IO.Class
import Debug.Trace
----------------------------------------------------

data ClassBody = ClassBody ClassDefinition [Notation]
               deriving (Eq, Ord, Read, Show)

instance FreeVars ClassBody where
  freeVars (ClassBody cls nots) = binding' cls $ freeVars (NoBinding nots)

-- lookup the signature of a class member and return the list of its
-- implicit binders
getImplicitBindersForClassMember  :: ConversionMonad m => Ident -> Ident -> m [Binder]
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
                 => LHsContext GHC.Name                   -- ^@tcdCtxt@    Context
                 -> Located GHC.Name                      -- ^@tcdLName@   name of the class
                 -> [LHsTyVarBndr GHC.Name]               -- ^@tcdTyVars@  class type variables
                 -> [Located (FunDep (Located GHC.Name))] -- ^@tcdFDs@     functional dependencies
                 -> [LSig GHC.Name]                       -- ^@tcdSigs@    method signatures
                 -> LHsBinds GHC.Name                     -- ^@tcdMeths@   default methods
                 -> [LFamilyDecl GHC.Name]                -- ^@tcdATs@     associated types
                 -> [LTyFamDefltEqn GHC.Name]             -- ^@tcdATDefs@  associated types defaults
                 -> m ClassBody
convertClassDecl (L _ hsCtx) (L _ hsName) ltvs fds lsigs defaults types typeDefaults = do
  unless (null       fds)          $ convUnsupported "functional dependencies"
  unless (null       types)        $ convUnsupported "associated types"
  unless (null       typeDefaults) $ convUnsupported "default associated type definitions"

  name <- freeVar hsName
  ctx  <- traverse (fmap (Generalized Coq.Implicit) . convertLType) hsCtx

  args <- convertLHsTyVarBndrs Coq.Explicit ltvs
  kinds <- (++ repeat Nothing) . map Just . maybe [] NE.toList <$> use (edits.classKinds.at name)
  let args' = zipWith go args kinds
       where go (Inferred exp name) (Just t) = Typed Ungeneralizable exp (name NE.:| []) t
             go a _ = a


  all_sigs <- binding' args' $ convertLSigs lsigs

  -- implement the class part of "skip method"
  skippedMethodsS <- use (edits.skippedMethods)
  let sigs = (`M.filterWithKey` all_sigs) $ \meth _ ->
        (name,toCoqName meth) `S.notMember` skippedMethodsS

  -- ugh! doesnt work for operators
  -- memberSigs.at name ?= sigs

  defs <- fmap M.fromList $ for (bagToList defaults) $ convertTypedBinding Nothing . unLoc >=> \case
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

  let classDefn = (ClassDefinition name (args' ++ ctx) Nothing (bimap toCoqName sigType <$> M.toList sigs))

  classDefns.at name ?= classDefn



  pure $ ClassBody classDefn
                   (concatMap (buildInfixNotations sigs <*> infixToCoq) . filter identIsOperator $ M.keys sigs)

classSentences :: ClassBody -> [Sentence]
classSentences (ClassBody (ClassDefinition name args ty methods) nots) =
    [ RecordSentence dict_record
    , DefinitionSentence (DefinitionDef Global name args Nothing class_ty)
    , ExistingClassSentence name
    ] ++
    [ DefinitionSentence $
        DefinitionDef Global n
            [Typed Generalizable Implicit [Ident "g"] (app_args (Var name))]
            (Just ty)
            (App2 (Var "g") Underscore (app_args (Var (n <> "__"))))
    | (n, ty) <- methods ] ++
    map NotationSentence nots
  where
    dict_name = name <> "__Dict"
    dict_build = name <> "__Dict_Build"
    dict_methods = [ (name <> "__", ty) | (name, ty) <- methods ]
    dict_record  = RecordDefinition dict_name inst_args ty (Just dict_build) dict_methods
    -- The dictionary needs all explicit (type) arguments,
    -- but none of the implicit (constraint) arguments
    inst_args = filter (\b -> b ^? binderExplicitness == Just Explicit) args
    app_args f = foldl App1 f (map Var (foldMap (toListOf binderIdents) inst_args))
    class_ty = Forall [ Inferred Explicit (Ident "r")] $
            (app_args (Var dict_name)  `Arrow` Var "r") `Arrow` Var "r"
