{-# LANGUAGE RecordWildCards, LambdaCase, ViewPatterns, FlexibleContexts, OverloadedStrings, OverloadedLists, ScopedTypeVariables, MultiParamTypeClasses #-}

module HsToCoq.ConvertHaskell.Declarations.Class (ClassBody(..), convertClassDecl, getImplicitBindersForClassMember, classSentences, directClassSentences, cpsClassSentences, convertAssociatedType, convertAssociatedTypeDefault) where

import Control.Lens hiding (rewrite)

import Data.Bifunctor
import Data.Traversable
import qualified Data.List.NonEmpty as NE
import Data.Maybe

import Control.Monad

import Data.Generics

import qualified Data.Text as T

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import GHC hiding (Name)
import HsToCoq.Util.GHC
import qualified GHC
import Outputable (Outputable())
import Bag
import Class

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.Gallina.Rewrite
import HsToCoq.Coq.Pretty
import HsToCoq.Util.FVs

import HsToCoq.ConvertHaskell.TypeInfo
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

instance HasBV Qualid ClassBody where
  bvOf (ClassBody cls nots) = bvOf cls `telescope` foldMap bvOf nots

-- lookup the signature of a class member and return the list of its
-- implicit binders
getImplicitBindersForClassMember  :: ConversionMonad r m => Qualid -> Qualid -> m [Binder]
getImplicitBindersForClassMember className memberName = do
  classDef <- lookupClassDefn className
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

-- Module-local
convUnsupportedIn_lname :: (ConversionMonad r m, Outputable nm) => String -> String -> GenLocated l nm -> m a
convUnsupportedIn_lname what whatFam lname = do
  name <- T.unpack <$> ghcPpr (unLoc lname)
  convUnsupportedIn what whatFam name

convertAssociatedType :: ConversionMonad r m => [Qualid] -> FamilyDecl GhcRn -> m (Qualid, Term)
convertAssociatedType classArgs FamilyDecl{..} = do
  let badAssociation what whatFam = convUnsupportedIn_lname what whatFam fdLName
        
  case fdInfo of
    OpenTypeFamily     -> pure ()
    DataFamily         -> badAssociation "associated data types"           "data family"
    ClosedTypeFamily _ -> badAssociation "associated closed type families" "closed type family "
  -- Skipping 'fdFixity'
  unless (null fdInjectivityAnn) $ badAssociation "injective associated type families" "associated type"
  
  name   <- var TypeNS $ unLoc fdLName
  args   <- convertLHsTyVarBndrs Coq.Explicit $ hsq_explicit fdTyVars
  -- Could losen this in future?
  unless (classArgs == foldMap (toListOf binderIdents) args) $
    badAssociation "associated type families with argument lists that differ from the class's" "associated type"
  storeExplicitMethodArguments name args
  
  result <- case unLoc fdResultSig of
    NoSig                            -> pure $ Sort Type
    KindSig   k                      -> convertLType k
    TyVarSig (L _ (UserTyVar _))     -> pure $ Sort Type -- Maybe not a thing inside type classes?
    TyVarSig (L _ (KindedTyVar _ k)) -> convertLType k   -- Maybe not a thing inside type classes?
  
  pure (name, result)

convertAssociatedTypeDefault :: ConversionMonad r m => [Qualid] -> TyFamDefltEqn GhcRn -> m (Qualid, Term)
convertAssociatedTypeDefault classArgs FamEqn{..} = do
  args <- convertLHsTyVarBndrs Coq.Explicit $ hsq_explicit feqn_pats
  unless (classArgs == foldMap (toListOf binderIdents) args) $
    convUnsupportedIn_lname "associated type family defaults with argument lists that differ from the class's"
                            "associated type equation"
                            feqn_tycon
  (,) <$> var TypeNS (unLoc feqn_tycon)
      <*> convertLType feqn_rhs
  -- Skipping feqn_fixity
    
convertClassDecl :: ConversionMonad r m
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
  name <- var TypeNS hsName
  
  let convUnsupportedHere what = convUnsupportedIn what "type class" (showP name)
  unless (null fds) $ convUnsupportedHere "functional dependencies"

  ctx  <- traverse (fmap (Generalized Coq.Implicit) . convertLType) hsCtx
  storeSuperclassCount name . sum <=< for ctx $ \case
    Generalized _ (termHead -> Just super) -> maybe 1 (+ 1) <$> lookupSuperclassCount super
    _                                      -> pure 1

  args <- convertLHsTyVarBndrs Coq.Explicit ltvs
  kinds <- (++ repeat Nothing) . map Just . maybe [] NE.toList <$> view (edits.classKinds.at name)
  let args' = zipWith go args kinds
       where go (Inferred exp name) (Just t) = Typed Ungeneralizable exp (name NE.:| []) t
             go a _ = a
  
  let argNames = foldMap (toListOf binderIdents) args

  type_sigs  <- M.fromList . map (second $ Signature ?? Nothing)
                  <$> traverse (convertAssociatedType argNames . unLoc) types
  value_sigs <- convertLSigs lsigs
  storeClassTypes name $ M.keysSet type_sigs
  -- We don't use 'lookupSig' here because type classes depend on the exact list
  -- of signatures.  This also means all the signatures should be present, so
  -- just using the result of `convertLSigs` shouldn't pose a problem.
  
  hideTypeArgs <- for (M.keys type_sigs) $ \meth -> do
    count <- maybe 0 length <$> lookupExplicitMethodArguments meth
    let vars = map (\i -> T.pack $ "subst" ++ show i ++ "__") [1..count]
    pure $ Rewrite { patternVars = vars
                   , lhs         = Qualid meth `appList` map (PosArg . Var) vars
                   , rhs         = Qualid meth }
  let all_sigs = everywhere (mkT $ rewrite hideTypeArgs) <$> (type_sigs <> value_sigs)

  -- implement the class part of "skip method"
  skippedMethodsS <- view (edits.skippedMethods)
  let sigs = (`M.filterWithKey` all_sigs) $ \meth _ ->
        (name,qualidBase meth) `S.notMember` skippedMethodsS

  -- ugh! doesnt work for operators
  -- memberSigs.at name ?= sigs
  
  type_defs  <- M.fromList <$> traverse (convertAssociatedTypeDefault argNames . unLoc) typeDefaults
  value_defs <- fmap M.fromList $ for (bagToList defaults) $
                convertTypedModuleBinding Nothing . unLoc >=> \case
                  Just (ConvertedDefinitionBinding cd) -> do
--                      typeArgs <- getImplicitBindersForClassMember name convDefName
                      -- We have a tough time handling recursion (including mutual
                      -- recursion) here because of name overloading
                      pure (cd^.convDefName, maybe id Fun (NE.nonEmpty $ cd^.convDefArgs) $ cd^.convDefBody)
                  Just (ConvertedPatternBinding    _ _)                     ->
                      convUnsupportedHere "pattern bindings in class declarations"
                  Just (ConvertedAxiomBinding      _ _)                     ->
                      convUnsupportedHere "axiom bindings in class declarations"
                  Just (RedefinedBinding           _ _)                     ->
                      convUnsupportedHere "redefining class method declarations"
                  Nothing                                                   ->
                      convUnsupportedHere "skipping a type class method (use `skip method`)"
  let defs = type_defs <> value_defs
  unless (null defs) $ storeDefaultMethods name defs

--  liftIO (traceIO (show name))
--  liftIO (traceIO (show defs))

  let classDefn = (ClassDefinition name (args' ++ ctx) Nothing (second sigType <$> M.toList sigs))

  storeClassDefn name classDefn

  let nots = concatMap (buildInfixNotations sigs) $ M.keys sigs

  pure $ ClassBody classDefn nots

directClassSentences :: ConversionMonad r m => ClassBody -> m [Sentence]
directClassSentences (ClassBody clsDef@(ClassDefinition name args _ _) nots) = do
  supers <- fromMaybe 0      <$> lookupSuperclassCount name
  types  <- fromMaybe mempty <$> lookupClassTypes      name
  let argCount = length $ filter ((== Explicit) . view binderExplicitness) args
  pure $  ClassSentence clsDef
       :  map NotationSentence nots
       ++ map (\ty -> ArgumentsSentence . Arguments Nothing ty
                   .  map (\ie -> ArgumentSpec ie UnderscoreName Nothing)
                   $ replicate argCount ArgExplicit ++ replicate (1+supers) ArgMaximal)
              (S.toList types)

cpsClassSentences :: ConversionMonad r m => ClassBody -> m [Sentence]
cpsClassSentences (ClassBody (ClassDefinition name args ty methods) nots) = do
  -- TODO: These should probably be created with 'gensym'/'genqid', but then I
  -- have to be within a 'LocalConvMonad' and then I have to think exactly about
  -- what that means here.
  let result_ty, cont_name :: Qualid
      result_ty = "r__"
      cont_name = "g__0__" -- Can't use `g__` because it could collide with a CPSed class method
  -- result_ty <- genqid "r"
  -- cont_name <- genqid "g"
  let class_ty = Forall [ Inferred Explicit $ Ident result_ty ] $
                   (app_args dict_name `Arrow` Qualid result_ty) `Arrow` Qualid result_ty
  
  let wholeClassSentences =
        [ RecordSentence dict_record
        , DefinitionSentence (DefinitionDef Global name args Nothing class_ty)
        , ExistingClassSentence name ]

      notations = map NotationSentence nots
  
  methods <- traverse (fmap DefinitionSentence . uncurry (method_def cont_name)) methods

  pure $ wholeClassSentences ++ methods ++ notations
  where
    dict_name = qualidExtendBase "__Dict" name
    dict_build = qualidExtendBase "__Dict_Build" name
    dict_methods = [ (qualidExtendBase "__" name, ty) | (name, ty) <- methods ]
    dict_record  = RecordDefinition dict_name inst_args ty (Just dict_build) dict_methods
    
    -- The dictionary needs all explicit (type) arguments,
    -- but none of the implicit (constraint) arguments
    inst_args = filter (\b -> b ^? binderExplicitness == Just Explicit) args
    app_args f = foldl App1 (Qualid f) (map Qualid (foldMap (toListOf binderIdents) inst_args))
    
    method_def g meth ty = do
      explicitArgs <- fromMaybe [] <$> lookupExplicitMethodArguments meth
      pure $ DefinitionDef
               Global
               meth
               (explicitArgs ++ [Typed Generalizable Implicit [Ident g] $ app_args name])
               (Just ty)
               (App2 (Qualid g) Underscore . app_args $ qualidExtendBase "__" meth)

classSentences :: ConversionMonad r m => ClassBody -> m [Sentence]
classSentences cls@(ClassBody (ClassDefinition name _ _ _) _) =
  view (edits.simpleClasses.contains name) >>= \case
    True  -> directClassSentences cls
    False -> cpsClassSentences    cls
