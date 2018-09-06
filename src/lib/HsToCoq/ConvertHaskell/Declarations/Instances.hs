{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedStrings,
             ScopedTypeVariables,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Instances (
  -- * Top-level entry point
  convertClsInstDecls,
  -- * Axiomatizing equivalents
  axiomatizeClsInstDecls,
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
import HsToCoq.Util.GHC.Exception
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
        Left err -> convUnsupported $ "Cannot derive instance name from " ++ show coqType ++ ": " ++ err
        Right name -> return $ qual name
  where
    -- Skip type vaiables and constraints
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
                  deriving (Eq, Ord)

convertClsInstDeclInfo :: ConversionMonad r m => ClsInstDecl GhcRn -> m InstanceInfo
convertClsInstDeclInfo ClsInstDecl{..} = do
  instanceName  <- convertInstanceName $ hsib_body cid_poly_ty
  instanceHead  <- convertLHsSigType cid_poly_ty
  instanceClass <- maybe (convUnsupported "strangely-formed instance heads") pure $
                    termHead instanceHead

  pure InstanceInfo{..}

--------------------------------------------------------------------------------

unlessSkipped :: ConversionMonad r m => InstanceInfo -> m [Sentence] -> m [Sentence]
unlessSkipped (InstanceInfo{..}) act = do
  view (edits.skipped.contains instanceClass) >>= \case
    True -> pure [ CommentSentence (Comment ("Skipping instance " <> qualidBase instanceName <> " of class " <> qualidBase instanceClass)) ]
    False -> do
      view (edits.skipped.contains instanceName) >>= \case
        True -> pure [ CommentSentence (Comment ("Skipping instance " <> qualidBase instanceName)) ]
        False -> act
        

bindToMap :: ConversionMonad r m => [HsBindLR GhcRn GhcRn] -> m (M.Map Qualid (HsBind GhcRn))
bindToMap binds = fmap M.fromList $ forM binds $ \hs_bind -> do
    name <- hsBindName hs_bind
    return (name, hs_bind)

clsInstFamiliesToMap :: ConversionMonad r m => [LTyFamInstDecl GhcRn] -> m (M.Map Qualid Term)
clsInstFamiliesToMap assocTys =
  fmap M.fromList . for assocTys $ \(L _ (TyFamInstDecl (HsIB {hsib_body = FamEqn{..}}))) ->
    (,) <$> var TypeNS (unLoc feqn_tycon) <*> convertLType feqn_rhs

convertClsInstDecl :: forall r m. ConversionMonad r m => ClsInstDecl GhcRn -> m [Sentence]
convertClsInstDecl cid@ClsInstDecl{..} = do
  ii@InstanceInfo{..} <- convertClsInstDeclInfo cid

  let err_handler exn = pure [ translationFailedComment ("instance " <> qualidBase instanceName) exn ]
  unlessSkipped ii $ ghandle err_handler $ do
    cid_binds_map <- bindToMap (map unLoc $ bagToList cid_binds)
    cid_types_map <- clsInstFamiliesToMap cid_tyfam_insts

    let (binds, classTy) = decomposeForall instanceHead

    -- decomposeClassTy can fail, so run it in the monad so that
    -- failure will be caught and cause the instance to be skipped
    (className, instTy) <- decomposeClassTy classTy

    -- Get the methods of this class (this should already exclude skipped ones)
    (classMethods, classArgs) <- do
      classDef <- lookupClassDefn className
      case classDef of
        (Just (ClassDefinition _ args _ sigs)) -> pure $ (map fst sigs, args)
        _ -> convUnsupported ("OOPS! Cannot find information for class " ++ show className)
    
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
    
    -- For each method, look for
    --  * explicit definitions
    --  * default definitions
    -- in that order
    cdefs <- forM classMethods $ \meth ->
      case (M.lookup meth cid_binds_map, M.lookup meth cid_types_map, M.lookup meth classDefaults) of
        (Just bind, _, _) ->
          fmap (\(_,body) -> (meth,body)) . local (envFor meth) $
            convertMethodBinding (localNameFor meth) bind >>= \case
              ConvertedDefinitionBinding cd
                  -> pure (cd^.convDefName, maybe id Fun (NE.nonEmpty $ cd^.convDefArgs) $ cd^.convDefBody)
                     -- We have a tough time handling recursion (including mutual
                     -- recursion) here because of name overloading
              ConvertedPatternBinding {}
                  -> convUnsupported "pattern bindings in instances"
              ConvertedAxiomBinding {}
                  -> convUnsupported "axiom bindings in instances"
          
        (Nothing, Just assoc, _) ->
          pure (meth, subst allLocalNames assoc)
        
        (Nothing, Nothing, Just term) ->
          let extraSubst
                | meth `elem` classTypes =
                  let names = foldMap (^..binderIdents) . filter ((== Explicit) . view binderExplicitness)
                  in M.fromList $ zip (names classArgs) [instTy]
                | otherwise =
                  mempty
          in -- In the body of the default definition, make methods names
             -- refer to their local version
            pure (meth, subst (allLocalNames <> extraSubst) term)
        
        (Nothing, Nothing, Nothing) ->
            convUnsupported $ "Method " <> showP meth <> " has no definition and no default definition"

    -- Turn definitions into sentences
    let quantify :: Qualid -> Term -> m Term
        quantify meth body =
            do typeArgs <- getImplicitBindersForClassMember className meth
               case (NE.nonEmpty typeArgs) of
                   Nothing -> return body
                   Just args -> return $ Fun args body

    methodSentences <- forM cdefs $ \(meth, body) -> do
        let v' = localNameFor meth
        -- implement redefinitions of methods
        view (edits.redefinitions.at v') >>= \case
            Just redef -> pure (definitionSentence redef)
            Nothing    -> do
              (params, mty) <- makeInstanceMethodTy className binds instTy meth
              qbody <- quantify meth body
              pure . DefinitionSentence $ DefinitionDef Local
                                                        v'
                                                        (subst allLocalNames <$> params)
                                                        (subst allLocalNames <$> mty)
                                                        qbody

    instance_sentence <- view (edits.redefinitions.at instanceName) >>= \case
      Nothing ->
        let instHeadTy = appList (Qualid className) [PosArg instTy]
        in view (edits.simpleClasses.contains className) >>= \case
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
      Just (CoqInstanceDef x) -> pure $ InstanceSentence x
      Just redef -> editFailure $ ("cannot redefine an Instance Definition to be " ++) $
        case redef of CoqDefinitionDef _ -> "a Definition"
                      CoqFixpointDef   _ -> "a Fixpoint"
                      CoqInductiveDef  _ -> "an Inductive"
                      CoqInstanceDef   _ -> "an Instance Definition"

    pure $ methodSentences ++ [instance_sentence]



axiomatizeClsInstDecl :: ConversionMonad r m
                      => ClsInstDecl GhcRn        -- Haskell instance we are converting
                      -> m [Sentence]
axiomatizeClsInstDecl cid@ClsInstDecl{..} = do
  ii@InstanceInfo{..} <- convertClsInstDeclInfo cid
  unlessSkipped ii $ do
      lookupClassDefn instanceClass >>= \case
        Just (ClassDefinition _ _ _ methods) ->
          pure $ [ InstanceSentence $ InstanceDefinition instanceName [] instanceHead []
                                    $ if null methods then Nothing else Just $ ProofAdmitted "" ]
        Nothing ->
          -- convUnsupported ("OOPS! Cannot find information for class " ++ show instanceClass)
          pure []

--------------------------------------------------------------------------------

convertClsInstDecls, axiomatizeClsInstDecls :: forall r m. ConversionMonad r m =>
    [ClsInstDecl GhcRn] -> m [Sentence]
convertClsInstDecls = foldTraverse convertClsInstDecl
axiomatizeClsInstDecls = foldTraverse axiomatizeClsInstDecl


-- lookup the type of the class member
-- add extra quantifiers from the class & instance definitions
makeInstanceMethodTy :: ConversionMonad r m => Qualid -> [Binder] -> Term -> Qualid -> m ([Binder], Maybe Term)
makeInstanceMethodTy className params instTy memberName = do
  classDef <- lookupClassDefn className
  case classDef of
    (Just (ClassDefinition _ (b:_) _ sigs)) | [var] <- toListOf binderIdents b ->
      case lookup memberName sigs of
        Just sigType ->
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
          in pure $ (instBnds, Just $ instSigType)
        Nothing ->
          convUnsupported ("Cannot find sig for " ++ showP memberName)
    _ -> convUnsupported ("OOPS! Cannot find information for class " ++ showP className)

-- from "instance C ty where" access C and ty
-- TODO: multiparameter type classes   "instance C t1 t2 where"
--       instances with contexts       "instance C a => C (Maybe a) where"
decomposeClassTy :: ConversionMonad r m => Term -> m (Qualid, Term)
decomposeClassTy ty = case ty of
   App1 (Qualid cn) a -> pure (cn, a)
   _ -> convUnsupported ("type class instance head:" ++ show ty)

decomposeForall :: Term -> ([Binder], Term)
decomposeForall (Forall bnds ty) = first (NE.toList bnds ++) (decomposeForall ty)
decomposeForall t = ([], t)
