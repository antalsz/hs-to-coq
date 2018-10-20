{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedStrings,
             ScopedTypeVariables,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Instances (
  convertClsInstDecls
) where

import Control.Lens

import Data.Semigroup (Semigroup(..), (<>))
import Data.Traversable
import HsToCoq.Util.Traversable
import Data.Maybe
import qualified Data.List.NonEmpty as NE
import Data.Bifunctor
import Data.Monoid
import qualified Data.Text as T
import Control.Monad.Reader.Class

import Control.Monad.State

import qualified Data.Map.Strict as M

import GHC hiding (Name)
import Bag
import HsToCoq.Util.GHC.Module

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Subst
import HsToCoq.Coq.Pretty
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.TypeInfo
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Axiomatize
import HsToCoq.ConvertHaskell.Declarations.Class

--------------------------------------------------------------------------------

-- Take the instance head and make it into a valid identifier.
convertInstanceName :: ConversionMonad r m => LHsType GhcRn -> m Qualid
convertInstanceName n = do
    coqType <- convertLType n
    qual <- Qualified . moduleNameText <$> view currentModule
    case skip coqType of
        Left err -> throwProgramError $ "Cannot derive instance name from `" ++ showP coqType ++ "': " ++ err
        Right name -> return $ qual name
  where
    -- Skip type variables and constraints
    skip (Forall _ t)  = skip t
    skip (Arrow _ t)   = skip t
    skip (InScope t _) = skip t
    skip t             = bfToName <$> bfTerm t

    bfToName :: [Qualid] -> T.Text
    bfToName qids | isVanilla = name
                  | otherwise = name <> "__" <> T.pack (show shapeNum)
      where
        tyCons = [ bn | Just bn <- unTyCon <$> qids]
        name = T.intercalate "__" tyCons
        shapeNum = bitsToInt $ map isTyCon qids

        -- A vanilla header is when all tyCons appear before all
        -- type variables. In this case, do not add the shapeNum
        isVanilla = not $ any isTyCon $ dropWhile isTyCon $ qids

        isTyCon = isJust . unTyCon

        unTyCon :: Qualid -> Maybe T.Text
        unTyCon (Qualified _ base)  = Just base
        unTyCon (Bare "bool")       = Just "bool"
        unTyCon (Bare "comparison") = Just "comparison"
        unTyCon (Bare "list")       = Just "list"
        unTyCon (Bare "option")     = Just "option"
        unTyCon (Bare "op_zt__")    = Just "op_zt__"
        unTyCon (Bare "unit")       = Just "unit"
        unTyCon (Bare "nat")        = Just "nat"      
        unTyCon _                   = Nothing

        bitsToInt :: [Bool] -> Integer
        bitsToInt []         = 0
        bitsToInt (True:xs)  = 2*bitsToInt xs + 1
        bitsToInt (False:xs) = 2*bitsToInt xs

    -- Breadth-first traversal listing all variables and type constructors
    bfTerm :: Monad m => Term -> m [Qualid]
    bfTerm = fmap concat . go
      where
        go :: Monad m => Term -> m [[Qualid]]
        go t = do
            (f, args) <- collectArgs t
            subtrees <- mapM go args
            return $ [f] : foldr merge [] subtrees

    merge :: [[a]] -> [[a]] -> [[a]]
    merge xs     []     = xs
    merge []     ys     = ys
    merge (x:xs) (y:ys) = (x ++ y) : merge xs ys

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
data InstanceInfo = InstanceInfo { instanceName       :: !Qualid
                                 , instanceHead       :: !Term
                                 , instanceClass      :: !Qualid
                                 }
                  deriving (Eq, Ord, Show, Read)

convertClsInstDeclInfo :: ConversionMonad r m => ClsInstDecl GhcRn -> m InstanceInfo
convertClsInstDeclInfo ClsInstDecl{..} = do
  instanceName  <- convertInstanceName $ hsib_body cid_poly_ty
  utvm          <- unusedTyVarModeFor instanceName
  instanceHead  <- convertLHsSigType utvm cid_poly_ty
  instanceClass <- termHead instanceHead
                     & maybe (convUnsupportedIn "strangely-formed instance heads"
                                                "type class instance"
                                                (showP instanceName))
                             pure
                    

  pure InstanceInfo{..}

--------------------------------------------------------------------------------

no_class_error :: MonadIO m => Qualid -> String -> m a
no_class_error cls extra = throwProgramError $  "Could not find information for the class " ++ quote_qualid cls
                                             ++ if null extra then [] else ' ':extra

no_class_instance_error :: MonadIO m => Qualid -> Qualid -> m a
no_class_instance_error cls inst = no_class_error cls $ "when defining the instance " ++ quote_qualid inst

no_class_method_error :: MonadIO m => Qualid -> Qualid -> m a
no_class_method_error cls meth = no_class_error cls $ "when defining the method " ++ quote_qualid meth


quote_qualid :: Qualid -> String
quote_qualid qid = "`" ++ showP qid ++ "'"

--------------------------------------------------------------------------------

unlessSkippedClass :: ConversionMonad r m => InstanceInfo -> m [Sentence] -> m [Sentence]
unlessSkippedClass InstanceInfo{..} act = do
  view (edits.skippedClasses.contains instanceClass) >>= \case
    True ->
      pure [CommentSentence . Comment $
              "Skipping all instances of class `" <> textP instanceClass <> "', \
              \including `" <> textP instanceName <> "'"]
    False ->
      act

bindToMap :: ConversionMonad r m => [HsBindLR GhcRn GhcRn] -> m (M.Map Qualid (HsBind GhcRn))
bindToMap binds = fmap M.fromList $ forM binds $ \hs_bind -> do
    name <- hsBindName hs_bind
    return (name, hs_bind)

clsInstFamiliesToMap :: ConversionMonad r m => [LTyFamInstDecl GhcRn] -> m (M.Map Qualid Term)
clsInstFamiliesToMap assocTys =
  fmap M.fromList . for assocTys $ \(L _ (TyFamInstDecl (HsIB {hsib_body = FamEqn{..}}))) ->
    (,) <$> var TypeNS (unLoc feqn_tycon) <*> convertLType feqn_rhs

-- Module-local
data Conv_Method = CM_Renamed            Sentence
                 | CM_Defined Conv_Level Term
                 deriving (Eq, Ord, Show, Read)

-- Module-local
data Conv_Level = CL_Term | CL_Type deriving (Eq, Ord, Enum, Bounded, Show, Read)

convertClsInstDecl :: forall r m. ConversionMonad r m => ClsInstDecl GhcRn -> m [Sentence]
convertClsInstDecl cid@ClsInstDecl{..} = do
  ii@InstanceInfo{..} <- convertClsInstDeclInfo cid
  let convUnsupportedHere what = convUnsupportedIn what "type class instance" (showP instanceName)
  
  let err_handler exn = pure [ translationFailedComment ("instance " <> qualidBase instanceName) exn ]
  unlessSkippedClass ii . handleIfPermissive err_handler $ definitionTask instanceName >>= \case
    SkipIt ->
      pure [CommentSentence . Comment $
              "Skipping instance `" <> textP instanceName <> "' of class `" <> textP instanceClass <> "'"]
    
    RedefineIt def ->
      [definitionSentence def] <$ case def of
        CoqInductiveDef        _ -> editFailure "cannot redefine an instance definition into an Inductive"
        CoqDefinitionDef       _ -> editFailure "cannot redefine an instance definition into a Definition"
        CoqFixpointDef         _ -> editFailure "cannot redefine an instance definition into a Fixpoint"
        CoqInstanceDef         _ -> pure ()
        CoqAxiomDef            _ -> editFailure "cannot redefine an instance definition into an Axiom"
    
    AxiomatizeIt axMode ->
      lookupClassDefn instanceClass >>= \case
        Just (ClassDefinition _ _ _ methods) ->
          pure $ [ InstanceSentence $ InstanceDefinition instanceName [] instanceHead []
                                    $ if null methods then Nothing else Just $ ProofAdmitted "" ]
        Nothing -> case axMode of
          GeneralAxiomatize  -> pure []
          SpecificAxiomatize -> no_class_instance_error instanceClass instanceName
    
    TranslateIt -> do
      cid_binds_map <- bindToMap (map unLoc $ bagToList cid_binds)
      cid_types_map <- clsInstFamiliesToMap cid_tyfam_insts
   
      let (binds, classTy) = decomposeForall instanceHead
   
      -- decomposeClassTy can fail, so run it in the monad so that
      -- failure will be caught and cause the instance to be skipped
      (className, instTy) <- either convUnsupportedHere pure $ decomposeClassTy classTy
   
      -- Get the methods of this class (this should already exclude skipped ones)
      (classMethods, classArgs) <- lookupClassDefn className >>= \case
        Just (ClassDefinition _ args _ sigs) -> pure $ (map fst sigs, args)
        _ -> no_class_instance_error className instanceName
      
      -- Associated types for this class
      classTypes <- fromMaybe mempty <$> lookupClassTypes className
      
      classDefaults <- fromMaybe M.empty <$> lookupDefaultMethods className
   
      let localNameFor :: Qualid -> Qualid
          localNameFor meth = qualidMapBase (<> ("_" <> qualidBase meth)) instanceName
      
      -- In the translation of meth1, we want all _other_ methods to be renamed
      -- to the concrete methods of the current instance (because type class methods
      -- usually refer to each other).
      -- We don’t do this for the current method (because type class methods are usually
      -- not recursive.)
      -- This is a heuristic, and the user can override it using `rewrite` rules.
      let envFor :: Qualid -> r -> r
          envFor meth = appEndo $ foldMap Endo
            [ edits.renamings.at (NamespacedIdent ns m) ?~ localNameFor m
            | m <- classMethods
            , m /= meth
            , let ns = if m `elem` classTypes then TypeNS else ExprNS]
      
      let allLocalNames = M.fromList $  [ (m, Qualid (localNameFor m)) | m <- classMethods ]
      
      let quantify meth body = (maybeFun ?? body) <$> getImplicitBindersForClassMember className meth
      
      -- For each method, look for
      --  * explicit definitions
      --  * default definitions
      -- in that order
      methodSentences <- forM classMethods $ \meth -> do
        let localMeth = localNameFor meth
        
        methBody <- case (M.lookup meth cid_binds_map, M.lookup meth cid_types_map, M.lookup meth classDefaults) of
          (Just bind, _, _) ->
            local (envFor meth) $ convertMethodBinding localMeth bind >>= \case
              ConvertedDefinitionBinding cd ->
                pure . CM_Defined CL_Term $ maybeFun (cd^.convDefArgs) (cd^.convDefBody)
                -- We have a tough time handling recursion (including mutual
                -- recursion) here because of name overloading
              ConvertedPatternBinding {} ->
                convUnsupportedHere "pattern bindings in instances"
              ConvertedAxiomBinding {} ->
                convUnsupportedHere "axiom bindings in instances"
              RedefinedBinding _ def ->
                CM_Renamed (definitionSentence def) <$ case def of
                  CoqInductiveDef        _ -> editFailure "cannot redefine an instance method definition into an Inductive"
                  CoqDefinitionDef       _ -> pure ()
                  CoqFixpointDef         _ -> pure ()
                  CoqInstanceDef         _ -> editFailure "cannot redefine an instance methoddefinition into an Instance"
                  CoqAxiomDef            _ -> pure ()
            
          (Nothing, Just assoc, _) ->
            pure . CM_Defined CL_Type $ subst allLocalNames assoc
           
          (Nothing, Nothing, Just term) ->
            let extraSubst
                  | meth `elem` classTypes =
                    let names = foldMap (^..binderIdents) . filter ((== Explicit) . view binderExplicitness)
                    in M.fromList $ zip (names classArgs) [instTy]
                  | otherwise =
                    mempty
            in -- In the body of the default definition, make methods names
               -- refer to their local version
               -- TODO: Associated type defaults should remember that they're types
               pure . CM_Defined CL_Term $ subst (allLocalNames <> extraSubst) term
           
          (Nothing, Nothing, Nothing) ->
            throwProgramError $ "The method `" <> showP meth <> "' has no definition and no default definition"
        
        case methBody of
          CM_Renamed renamed ->
            pure renamed
          CM_Defined level body    -> do
            let makeSig = case level of
                  CL_Term -> makeInstanceMethodTy
                  CL_Type -> makeAssociatedTypeTy
            -- We've converted the method, now sentenceify it
            (params, ty) <- makeSig className binds instTy meth
            qbody        <- quantify meth body
            pure . DefinitionSentence $ DefinitionDef Local
                                                      localMeth
                                                      (subst allLocalNames <$> params)
                                                      (Just $ subst allLocalNames ty)
                                                      qbody
   
      let instHeadTy = appList (Qualid className) [PosArg instTy]
      instance_sentence <- view (edits.simpleClasses.contains className) >>= \case
        True  -> do
          methods <- traverse (\m -> (m,) <$> quantify m (Qualid $ localNameFor m)) classMethods
          pure $ ProgramSentence
                   (InstanceSentence $ InstanceDefinition instanceName binds instHeadTy methods Nothing)
                   Nothing
        False -> do
          -- Assemble the actual record
          instRHS <- fmap Record $ forM classMethods $ \m -> do
                       method_body <- quantify m $ Qualid (localNameFor m)
                       return (qualidMapBase (<> "__") m, method_body)
          let instBody = Fun (Inferred Explicit UnderscoreName NE.:| [Inferred Explicit (Ident "k")])
                             (App1 (Var "k") instRHS)
          let instTerm = InstanceTerm instanceName binds instHeadTy instBody Nothing
          
          pure $ ProgramSentence (InstanceSentence instTerm) Nothing
      
      pure $ methodSentences ++ [instance_sentence]

--------------------------------------------------------------------------------

convertClsInstDecls :: ConversionMonad r m => [ClsInstDecl GhcRn] -> m [Sentence]
convertClsInstDecls = foldTraverse convertClsInstDecl

-- Look up the type class variable and the type of the class member without
-- postprocessing.
lookupInstanceTypeOrMethodVarTy :: ConversionMonad r m => Qualid -> Qualid -> m (Qualid, Term)
lookupInstanceTypeOrMethodVarTy className memberName =
  lookupClassDefn className >>= \case
    Just (ClassDefinition _ (b:_) _ sigs) | [var] <- toListOf binderIdents b ->
      case lookup memberName sigs of
        Just sigType -> pure (var, sigType)
        Nothing      -> throwProgramError $ "Cannot find signature for " ++ quote_qualid memberName
    _ ->
      no_class_method_error className memberName

makeAssociatedTypeTy :: ConversionMonad r m => Qualid -> [Binder] -> Term -> Qualid -> m ([Binder], Term)
makeAssociatedTypeTy className params instTy memberName = do
  (var, sigType) <- lookupInstanceTypeOrMethodVarTy className memberName
  pure (params, subst (M.singleton var instTy) sigType)

-- lookup the type of the class member
-- add extra quantifiers from the class & instance definitions
makeInstanceMethodTy :: ConversionMonad r m => Qualid -> [Binder] -> Term -> Qualid -> m ([Binder], Term)
makeInstanceMethodTy className params instTy memberName = do
  (var, sigType) <- lookupInstanceTypeOrMethodVarTy className memberName 
  -- GOAL: Consider
  -- @
  --     class Functor f where
  --       fmap :: (a -> b) -> f a -> f b
  --     instance Functor (Either a) where fmap = ...
  -- @
  -- When desugared naïvely into Coq, this will result in a term with type
  -- @
  --     forall {a₁}, forall {a₂ b},
  --       (a₂ -> b) -> f (Either a₁ a₂) -> f (Either a₁ b)
  -- @
  -- Except without the subscripts!  So we have to rename either
  -- the per-instance variables (here, @a₁@) or the type class
  -- method variables (here, @a₂@ and @b@).  We pick the
  -- per-instance variables, and rename @a₁@ to @inst_a₁@.
  --
  -- ASSUMPTION: type variables don't show up in terms.  Broken
  -- by ScopedTypeVariables.
  let renameInst UnderscoreName =
        pure UnderscoreName
      renameInst (Ident x) =
        let inst_x = qualidMapBase ("inst_" <>) x
        in Ident inst_x <$ modify' (M.insert x (Qualid inst_x))
  
      sub ty = ($ ty) <$> gets subst
  
      (instBnds, instSubst) = (runState ?? M.empty) $ for params $ \case
        Inferred      ei x     -> Inferred      ei <$> renameInst x
        Typed       g ei xs ty -> Typed       g ei <$> traverse renameInst xs <*> sub ty
        Generalized ei tm      -> Generalized   ei <$> sub tm
  
      -- Why the nested substitution?  The only place the
      -- per-instance variable name can show up is in the
      -- specific instance type!  It can't show up in the
      -- signature of the method, that's the whole point
      instSigType = subst (M.singleton var $ subst instSubst instTy) sigType
  pure $ (instBnds, instSigType)

-- from "instance C ty where" access C and ty
-- TODO: multiparameter type classes   "instance C t1 t2 where"
--       instances with contexts       "instance C a => C (Maybe a) where"
decomposeClassTy :: Term -> Either String (Qualid, Term)
decomposeClassTy (App1 (Qualid cn) a) = Right (cn, a)
decomposeClassTy ty                   =  Left $ "type class instance head `" ++ showP ty ++ "'"

decomposeForall :: Term -> ([Binder], Term)
decomposeForall (Forall bnds ty) = first (NE.toList bnds ++) (decomposeForall ty)
decomposeForall t                = ([], t)
