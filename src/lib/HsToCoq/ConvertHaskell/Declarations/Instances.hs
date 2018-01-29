{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedStrings,
             ScopedTypeVariables,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Instances (
  -- * Top-level entry point
  convertModuleClsInstDecls,
  -- * Conversion building blocks
  convertClsInstDecl, convertClsInstDeclInfo, convertInstanceName,
  -- * Axiomatizing equivalents
  axiomatizeModuleClsInstDecls, axiomatizeClsInstDecl,
  -- ** Utility functions
  findHsClass, topoSortInstance,
  -- * Alternative entry points (you probably don't want to use these)
  convertClsInstDecls
) where

import Control.Lens

import Data.Semigroup (Semigroup(..), (<>))
import HsToCoq.Util.Function
import Data.Traversable
import HsToCoq.Util.Traversable
import Data.Maybe
import qualified Data.List.NonEmpty as NE
import Data.Bifunctor
import qualified Data.Text as T

import Control.Monad.State

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import GHC hiding (Name)
import qualified GHC
import BasicTypes (TopLevelFlag(..))
import Bag
import HsToCoq.Util.GHC.Exception
import HsToCoq.Util.GHC.Module

import HsToCoq.PrettyPrint (renderOneLineT)
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Pretty
import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Subst
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Axiomatize
import HsToCoq.ConvertHaskell.Declarations.Class

--------------------------------------------------------------------------------

-- Take the instance head and make it into a valid identifier.
convertInstanceName :: ConversionMonad m => LHsType GHC.Name -> m Qualid
convertInstanceName n = do
    coqType <- convertLType n
    qual <- maybe Bare (Qualified . moduleNameText) <$> use currentModule
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

    collectArgs :: Monad m => Term -> m (Qualid, [Term])
    collectArgs (Qualid qid) = return (qid, [])
    collectArgs (App t args) = do
        (f, args1) <- collectArgs t
        args2 <- mapM fromArg (NE.toList args)
        return $ (f, args1 ++ args2)
      where
        fromArg (PosArg t) = return t
        fromArg _          = fail "non-positional argument"
    collectArgs (Infix a1 f a2) = return (f, [a1, a2])
    collectArgs (Arrow a1 a2) = return (arrow_qid, [a1, a2])
      where arrow_qid = Qualified "GHC.Prim" "arrow"
    collectArgs (Parens t)    = collectArgs t
    collectArgs (InScope t _) = collectArgs t
    collectArgs t             = fail $ "collectArgs: " ++ show t

    merge :: [[a]] -> [[a]] -> [[a]]
    merge xs     []     = xs
    merge []     ys     = ys
    merge (x:xs) (y:ys) = (x ++ y) : merge xs ys

-- Looks up what GHC knows about this class (given by an instance head)
findHsClass :: ConversionMonad m => LHsSigType GHC.Name -> m Class
findHsClass insthead = case getLHsInstDeclClass_maybe insthead of
    Just className -> lookupTyThing (unLoc className) >>= \case
        Just (ATyCon tc) | Just cls <- tyConClass_maybe tc -> return cls
        _  -> convUnsupported "Lookup did not yield a class"
    Nothing -> convUnsupported "Cannot find class name in instance head"

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
data InstanceInfo = InstanceInfo { instanceName  :: !Qualid
                                 , instanceHead  :: !Term
                                 , instanceClass :: !Qualid
                                 , instanceHsClass :: Class}
                  deriving (Eq, Ord)

convertClsInstDeclInfo :: ConversionMonad m => ClsInstDecl GHC.Name -> m InstanceInfo
convertClsInstDeclInfo ClsInstDecl{..} = do
  instanceName  <- convertInstanceName $ hsib_body cid_poly_ty
  instanceHead  <- convertLHsSigType cid_poly_ty
  instanceClass <- maybe (convUnsupported "strangely-formed instance heads") pure $
                    termHead instanceHead
  instanceHsClass <- findHsClass cid_poly_ty

  pure InstanceInfo{..}

--------------------------------------------------------------------------------

convertClsInstDecl :: ConversionMonad m
                   => ClsInstDecl GHC.Name        -- Haskell instance we are converting
                   -> (InstanceDefinition -> m a) -- Final "rebuilding" pass
                   -> Maybe (InstanceInfo -> GhcException -> m a) -- error handling argument
                   -> m a
convertClsInstDecl cid@ClsInstDecl{..} rebuild mhandler = do
  info@InstanceInfo{..} <- convertClsInstDeclInfo cid

  -- TODO: Do we need the 'HsForAllTy' trick here to handle instance
  -- superclasses?  Or is the generalization backtick enough?
  maybe id (ghandle . ($ info)) mhandler $ do

    cbinds   <- convertTypedBindings TopLevel (map unLoc $ bagToList cid_binds) M.empty -- the type signatures (note: no InstanceSigs)
                                   (\case ConvertedDefinitionBinding cdef -> pure cdef
                                          ConvertedPatternBinding    _ _  -> convUnsupported "pattern bindings in instances")
                                   Nothing -- error handler

    cdefs <-  mapM (\ConvertedDefinition{..} -> do
                       return (convDefName, maybe id Fun (NE.nonEmpty (convDefArgs)) $ convDefBody)) cbinds

    defaults <-  use (defaultMethods.at instanceClass.non M.empty)
                 -- lookup default methods in the global state, using the empty map if the class name is not found
                 -- otherwise gives you a map
                 -- <&> is flip fmap
             <&> filter (\(meth, _) -> isNothing $ lookup meth cdefs) . M.toList

    -- implement the instance part of "skip method"
    skippedMethodsS <- use (edits.skippedMethods)

    let methods = filter (\(m,_) -> (instanceClass,qualidBase m) `S.notMember` skippedMethodsS) (cdefs ++ defaults)

    let (binds, classTy) = decomposeForall instanceHead

    rebuild $ InstanceDefinition instanceName binds classTy methods Nothing


decomposeForall :: Term -> ([Binder], Term)
decomposeForall (Forall bnds ty) = first (NE.toList bnds ++) (decomposeForall ty) 
decomposeForall t = ([], t)

axiomatizeClsInstDecl :: ConversionMonad m
                      => ClsInstDecl GHC.Name        -- Haskell instance we are converting
                      -> m (Maybe InstanceDefinition)
axiomatizeClsInstDecl cid@ClsInstDecl{..} = do
  InstanceInfo{..} <- convertClsInstDeclInfo cid
  use (classDefns.at instanceClass) >>= \case
    Just _ -> use (edits.skipped.contains instanceName) >>= \case
      True -> pure  Nothing
      False -> pure . Just . InstanceDefinition instanceName [] instanceHead []
         $ if null $ classMethods instanceHsClass
           then Nothing
           else Just $ ProofAdmitted ""
    Nothing ->
      -- convUnsupported ("OOPS! Cannot find information for class " ++ show instanceClass)
      pure Nothing

--------------------------------------------------------------------------------

convertModuleClsInstDecls :: forall m. ConversionMonad m
                          => [(Maybe ModuleName, ClsInstDecl GHC.Name)] -> m [Sentence]
convertModuleClsInstDecls = foldTraverse $ maybeWithCurrentModule .*^ \cid ->
                               convertClsInstDecl cid rebuild (Just axiomatizeInstance)
  where rebuild :: InstanceDefinition -> m [Sentence]
        rebuild instdef = do
            let coq_name = case instdef of
                    InstanceDefinition coq_name _ _ _ _ -> coq_name
                    InstanceTerm       coq_name _ _ _ _ -> coq_name
            use (edits.skipped.contains coq_name) >>= \case
                True -> do
                    let t = "Skipping instance " <> qualidBase coq_name
                    return [CommentSentence (Comment t)]
                False -> topoSortInstance instdef
        -- rebuild = pure . pure . InstanceSentence

        -- what to do if instance conversion fails
        -- make an axiom that admits the instance declaration
        axiomatizeInstance InstanceInfo{..} exn = pure
          [ translationFailedComment ("instance " <> renderOneLineT (renderGallina instanceHead)) exn ]
          {-
          [, InstanceSentence $ InstanceDefinition
              instanceName [] instanceHead [] (Just $ ProofAdmitted "") ]
          -}

axiomatizeModuleClsInstDecls :: forall m. ConversionMonad m
                             => [(Maybe ModuleName, ClsInstDecl GHC.Name)] -> m [Sentence]
axiomatizeModuleClsInstDecls insts =
  (fmap InstanceSentence .  catMaybes) <$>
    mapM (maybeWithCurrentModule .*^ axiomatizeClsInstDecl) insts

--------------------------------------------------------------------------------

-- Topo sort the instance members and lift (some of) them outside of
-- the instance declaration.

topoSortInstance :: forall m.  ConversionMonad m => InstanceDefinition -> m [Sentence]
topoSortInstance inst_def@(InstanceTerm _ _ _ _ _ ) =
    pure $ [InstanceSentence inst_def]
topoSortInstance (InstanceDefinition instanceName params ty members mp) = go sorted M.empty where

        m        = M.fromList members
        sorted   = topoSortEnvironment m
{-
        getFreeVarsIdent :: Ident -> S.Set Ident
        getFreeVarsIdent m = maybe S.empty getFreeVars (lookup m members)

        getFreeVarsNE :: NE.NonEmpty Ident -> S.Set Ident
        getFreeVarsNE ne = S.unions (map getFreeVarsIdent (NE.toList ne))

        containsNE :: NE.NonEmpty Ident -> S.Set Ident -> Bool
        containsNE ne s = any (\v -> S.member v s) ne

        compressLast :: [ NE.NonEmpty Ident ] -> ([ NE.NonEmpty Ident ], S.Set Ident)
        compressLast [ ]      = ([], S.empty)
        compressLast (h : []) =
            ([h], getFreeVarsNE h)
        compressLast (h : tl) =
            let extend set = S.union set (getFreeVarsNE h) in
            case compressLast tl of
              ([],s)         -> error "BUG: this case is impossible"
              ((h':[]), set) ->
                  if containsNE h set then
                      ([h , h'], extend set)
                  else
                      ([h <> h'], extend set)
              ((h':tl'), set) ->
                          (h : h' : tl', S.empty) -- don't care anymore
-}
        -- go through the toposort of members, constructing the final sentences
        go :: [ NE.NonEmpty Qualid ] -> M.Map Qualid Qualid -> m [ Sentence ]

        go []      sub = mkID sub
        go (hd:tl) sub = do (s1,bnds) <- mkDefnGrp (NE.toList hd) sub
                            s2        <- go tl bnds
                            return (s1 ++ s2)

        -- from "instance C ty where" access C and ty
        -- TODO: multiparameter type classes   "instance C t1 t2 where"
        --       instances with contexts       "instance C a => C (Maybe a) where"
        decomposeClassTy ty = case ty of
           App (Qualid cn) ((PosArg a) NE.:| []) -> (cn, a)
           _ -> error ("cannot deconstruct instance head: " ++ (show ty))

        (className, instTy) = decomposeClassTy ty

        buildName = qualidExtendBase "__Dict_Build" className

        -- lookup the type of the class member
        -- add extra quantifiers from the class & instance definitions
        mkTy :: Qualid -> m ([Binder], Maybe Term)
        mkTy memberName = do
          classDef <- use (classDefns.at className)
          -- TODO: May be broken by switch away from 'RdrName's
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
                        BindLet     x oty val  -> BindLet          <$> renameInst x <*> sub oty <*> sub val
                        Generalized ei tm      -> Generalized   ei <$> sub tm

                      -- Why the nested substitution?  The only place the
                      -- per-instance variable name can show up is in the
                      -- specific instance type!  It can't show up in the
                      -- signature of the method, that's the whole point
                      instSigType = subst (M.singleton var $ subst instSubst instTy) sigType
                  in pure $ (instBnds, Just $ instSigType)
                Nothing ->
                  convUnsupported ("Cannot find sig for " ++ show memberName)
            _ -> convUnsupported ("OOPS! Cannot find information for class " ++ show className)

        -- Methods often look recursive, but usually they are not really,
        -- so by default, we un-do the fix introduced by convertTypedBinding
        unFix :: Term -> Term
        unFix body = case body of
            Fun bnds t -> Fun bnds (unFix t)
            Fix (FixOne (FixBody _ bnds _ _ body'))
              -> Fun bnds body'
            App1 (Qualid (Bare "unsafeFix"))
                 (Fun (Inferred Explicit (Ident _) NE.:| bnds) body')
              -> Fun (NE.fromList bnds) body'
            _ -> body

        -- Gets the class method names, in the original
        getClassMethods = do
          classDef <- use (classDefns.at className)
          -- TODO: May be broken by switch away from 'RdrName's
          case classDef of
            (Just (ClassDefinition _ _ _ sigs)) ->
                pure $ map fst sigs
            _ -> convUnsupported ("OOPS! Cannot find information for class " ++ show className)

        -- This is the variant
        --   {| foo := fun {a} {b} => instance_foo |}
        -- which is too much for Coq’s type inference (without Program mode), see
        -- https://sympa.inria.fr/sympa/arc/coq-club/2017-11/msg00035.html
        quantify :: Qualid -> Term -> m Term
        quantify meth body =
            do typeArgs <- getImplicitBindersForClassMember className meth
               case (NE.nonEmpty typeArgs) of
                   Nothing -> return body
                   Just args -> return $ Fun args body

        -- This is the variant
        --   {| foo := @instance_foo _ _ |}
        -- which works only if params really are all arguments (no [{a} `{MonadArrow a}])
        _addArgs _meth impl = return $ ExplicitApp (Bare impl) (Underscore <$ params)

        -- given a group of member ids turn them into lifted definitions, keeping track of the current
        -- substitution
        mkDefnGrp :: [ Qualid ] -> (M.Map Qualid Qualid) -> m ([ Sentence ], M.Map Qualid Qualid)
        mkDefnGrp [] sub = return ([], sub)
        mkDefnGrp [ v ] sub = do
           let v' = qualidMapBase (<> ("_" <> qualidBase v)) instanceName
           (params, mty)  <- mkTy v
           body <- quantify v (subst (fmap Qualid sub) (m M.! v))
           let sub' = M.insert v v' sub

           -- implement redefinitions of methods
           use (edits.redefinitions.at v') >>= \case
               Just redef -> pure ([ definitionSentence redef], sub')
               Nothing    -> pure ([ DefinitionSentence (DefinitionDef Local v' params mty (unFix body)) ], sub')

        mkDefnGrp many _sub =
           -- TODO: mutual recursion
           convUnsupported ("Giving up on mutual recursion" ++ show many)

        -- make the final instance declaration, using the current substitution as the instance
        mkID :: M.Map Qualid Qualid -> m [ Sentence ]
        mkID mems = do
            -- Assemble members in the right order
            classMethods <- getClassMethods

            mems' <- forM classMethods $ \v -> do
                case M.lookup v mems of
                  Just v' -> do
                      t <- quantify v (Qualid v')
                      pure $ ((qualidMapBase (<> "__") v), t)
                  Nothing -> convUnsupported ("missing " ++ show v ++ " in " ++ show mems )

            -- When we can use record syntax, we can use this.
            -- `Instance` plus record syntax does sometimes not work,
            -- but `Program Instance` does.
            let body = Record mems'

            -- This variant uses the explicit `Build` command, which does
            -- works with `Instance`, but is ugly
            let _body = appList (Qualid buildName) $ map PosArg $
                    [ instTy ] ++ map snd mems'


            let instTerm = Fun (Inferred Explicit UnderscoreName NE.:| [Inferred Explicit (Ident "k")])
                               (App1 (Var "k") body)

            pure [ProgramSentence (InstanceSentence (InstanceTerm instanceName params ty instTerm mp)) Nothing]

--------------------------------------------------------------------------------

convertClsInstDecls :: ConversionMonad m => [ClsInstDecl GHC.Name] -> m [Sentence]
convertClsInstDecls = convertModuleClsInstDecls . map (Nothing,)
