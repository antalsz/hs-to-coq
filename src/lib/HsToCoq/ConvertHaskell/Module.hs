{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards, TypeApplications, FlexibleContexts, DeriveDataTypeable, OverloadedLists, OverloadedStrings, ScopedTypeVariables, MultiWayIf  #-}

module HsToCoq.ConvertHaskell.Module (
  -- * Convert whole module graphs and modules
  ConvertedModule(..),
  convertModules,
  -- ** Extract all the declarations from a module
  moduleDeclarations,
  -- * Convert declaration groups
  ConvertedModuleDeclarations(..), convertHsGroup,
) where

import Control.Lens

import HsToCoq.Util.Function
import Data.Traversable
import Data.Foldable
import Data.Maybe
import Data.Monoid
import Data.List.NonEmpty (NonEmpty(..))
import HsToCoq.Util.Containers

import Data.Generics

import Control.Monad.IO.Class
import Control.Exception (SomeException)
import qualified Data.Set as S
import qualified Data.Map as M

import qualified Data.Text as T

import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import GHC hiding (Name)
import qualified GHC
import HsToCoq.Util.GHC.Module
import BasicTypes (TopLevelFlag(..))
import Panic
import Bag

import Data.Data (Data(..))

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Sigs
import HsToCoq.ConvertHaskell.Declarations.TyCl
import HsToCoq.ConvertHaskell.Declarations.Instances
import HsToCoq.ConvertHaskell.Declarations.Notations
import HsToCoq.ConvertHaskell.Axiomatize

--------------------------------------------------------------------------------

data ConvertedModuleDeclarations =
  ConvertedModuleDeclarations { convertedTyClDecls    :: ![Sentence]
                              , convertedValDecls     :: ![Sentence]
                              , convertedClsInstDecls :: ![Sentence]
                              , convertedAddedDecls   :: ![Sentence]
                              }
  deriving (Eq, Ord, Show, Data)

convertHsGroup :: ConversionMonad m => ModuleName -> HsGroup GHC.Name -> m ConvertedModuleDeclarations
convertHsGroup mod HsGroup{..} = do
  convertedTyClDecls <- convertModuleTyClDecls
                     .  map ((Just mod,) . unLoc)
                     $  concatMap group_tyclds hs_tyclds
                          -- Ignore roles
  convertedValDecls  <- -- TODO RENAMER merge with convertLocalBinds / convertModuleValDecls
    case hs_valds of
      ValBindsIn{} ->
        convUnsupported "pre-renaming `ValBindsIn' construct post renaming"
      ValBindsOut binds lsigs -> do
        sigs  <- convertLSigs lsigs
        defns <- (convertTypedBindings TopLevel
                   (map unLoc $ concatMap (bagToList . snd) binds)
                   sigs
                   ??
                   (Just axiomatizeBinding))
              $  withConvertedBinding
                   (\cdef@ConvertedDefinition{convDefName = name} -> ((name,) <$>) $ do
                       t  <- use (edits.termination.at name)
                       lt <- use (edits.local_termination.at name)
                       obl <- use (edits.obligations.at name)
                       let useProgram = isJust t || isJust lt
                       if | Just order <- t  -- turn into Program Fixpoint
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
                   ) (\_ _ -> convUnsupported "top-level pattern bindings")

        defns' <- mapM applyRedefines defns
        let defnsMap = M.fromList defns'

        -- TODO RENAMER use RecFlag info to do recursion stuff
        pure . foldMap (foldMap (defnsMap M.!)) . topoSortEnvironment $ NoBinding <$> defnsMap

  convertedClsInstDecls <- convertModuleClsInstDecls [(Just mod, cid) | L _ (ClsInstD cid) <- hs_instds]

  convertedAddedDecls <- use (edits.additions.at mod.non [])

  pure ConvertedModuleDeclarations{..}

  where axiomatizeBinding :: ConversionMonad m => HsBind GHC.Name -> GhcException -> m (Qualid, [Sentence])
        axiomatizeBinding FunBind{..} exn = do
          name <- var ExprNS (unLoc fun_id)
          pure (name, [translationFailedComment (qualidBase name) exn, axiom name])
        axiomatizeBinding _ exn =
          liftIO $ throwGhcExceptionIO exn

        applyRedefines :: ConversionMonad m => (Qualid, [Sentence]) -> m (Qualid, [Sentence])
        applyRedefines (name, sentences)
            = use (edits.redefinitions.at name) >>= ((name,) <$>) . \case
                Just def ->
                     [definitionSentence def] <$ case def of
                      CoqInductiveDef        _ -> editFailure "cannot redefine a value definition into an Inductive"
                      CoqDefinitionDef       _ -> pure ()
                      CoqFixpointDef         _ -> pure ()
                      CoqInstanceDef         _ -> editFailure "cannot redefine a value definition into an Instance"
                Nothing -> pure sentences

axiomatizeHsGroup :: ConversionMonad m => ModuleName -> HsGroup GHC.Name -> m ConvertedModuleDeclarations
axiomatizeHsGroup mod HsGroup{..} = do
  convertedTyClDecls <- convertModuleTyClDecls
                     .  map ((Just mod,) . unLoc)
                     $  concatMap group_tyclds hs_tyclds
                          -- Ignore roles
  convertedValDecls  <-
    case hs_valds of
      ValBindsIn{} ->
        convUnsupported "pre-renaming `ValBindsIn' construct post renaming"
      ValBindsOut binds lsigs -> do
        sigs  <- convertLSigs lsigs `gcatch` const @_ @SomeException (pure M.empty)
        for (map unLoc $ concatMap (bagToList . snd) binds) $ \case
          FunBind{..} -> do
            name <- var ExprNS (unLoc fun_id)
            use (edits.skipped.contains name) >>= \case
                True -> pure (CommentSentence . Comment $ qualidBase name <> " skipped")
                False -> pure . typedAxiom name $ sigs^.at name.to (fmap sigType).non bottomType
          _ ->
            convUnsupported "non-type, non-class, non-value definitions in axiomatized modules"
  
  convertedClsInstDecls <- axiomatizeModuleClsInstDecls [(Just mod, cid) | L _ (ClsInstD cid) <- hs_instds]

  convertedAddedDecls <- use (edits.additions.at mod.non [])

  pure ConvertedModuleDeclarations{..}

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

data ConvertedModule =
  ConvertedModule { convModName         :: !ModuleName
                  , convModImports      :: ![Sentence]
                  , convModTyClDecls    :: ![Sentence]
                  , convModValDecls     :: ![Sentence]
                  , convModClsInstDecls :: ![Sentence]
                  , convModAddedDecls   :: ![Sentence]
                  }
  deriving (Eq, Ord, Show, Data)

-- Module-local
{-
convert_module_with_imports :: ConversionMonad m
                            => ModuleName -> RenamedSource ->
                            m (ConvertedModule, [ConvertedImportDecl])
convert_module_with_imports convModName (group, imports, _exports, _docstring) =
  withCurrentModule convModName $ do
    ConvertedModuleDeclarations { convertedTyClDecls    = convModTyClDecls
                                , convertedValDecls     = convModValDecls
                                , convertedClsInstDecls = convModClsInstDecls }
      <- convertHsGroup convModName group
    convImports    <- traverse (convertImportDecl . unLoc) imports
    convModImports <- foldTraverse importDeclSentences convImports
    pure (ConvertedModule{..}, convImports)
-}

-- Module-local
convert_module_with_requires_via :: ConversionMonad m
                                 => (ModuleName -> HsGroup GHC.Name -> m ConvertedModuleDeclarations)
                                 -> ModuleName -> RenamedSource ->
                                 m (ConvertedModule, [ModuleName])
convert_module_with_requires_via convGroup convModName (group, _imports, _exports, _docstring) =
  withCurrentModule convModName $ do
    ConvertedModuleDeclarations { convertedTyClDecls    = convModTyClDecls
                                , convertedValDecls     = convModValDecls
                                , convertedClsInstDecls = convModClsInstDecls
                                , convertedAddedDecls   = convModAddedDecls
                                }
      <- convGroup convModName group

    let allSentences = convModTyClDecls ++ convModValDecls ++ convModClsInstDecls ++ convModAddedDecls
    let freeVars = toList . getFreeVars $ NoBinding allSentences
    let modules = filter (/= convModName)
                     . map (mkModuleName . T.unpack)
                     . mapMaybe qualidModule $ freeVars
    let notationModules
                     = filter (/= convModName)
                     . map (mkModuleName . T.unpack)
                     . mapMaybe qualidModule
                     . filter qualidIsOp $ freeVars

    modules         <- skipModules $ S.toList $ S.fromList modules
    notationModules <- skipModules $ S.toList $ S.fromList notationModules

    let convModImports =
            [ ModuleSentence (Require Nothing Nothing [moduleNameText mn])
            | mn <- modules] ++
            [ ModuleSentence (ModuleImport Import [moduleNameText mn <> ".Notations"])
            | mn <- notationModules ]
    pure (ConvertedModule{..}, modules)

-- Module-local
convert_module_with_requires :: ConversionMonad m
                             => ModuleName -> RenamedSource ->
                             m (ConvertedModule, [ModuleName])
convert_module_with_requires = convert_module_with_requires_via convertHsGroup

-- Module-local
axiomatize_module_with_requires :: ConversionMonad m
                             => ModuleName -> RenamedSource ->
                             m (ConvertedModule, [ModuleName])
axiomatize_module_with_requires = convert_module_with_requires_via axiomatizeHsGroup

_convertModule :: ConversionMonad m => ModuleName -> RenamedSource -> m ConvertedModule
_convertModule = fmap fst .: convert_module_with_requires

_axiomatizeModule :: ConversionMonad m => ModuleName -> RenamedSource -> m ConvertedModule
_axiomatizeModule = fmap fst .: axiomatize_module_with_requires

-- NOT THE SAME as `traverse $ uncurry convertModule`!  Produces connected
-- components and can axiomatize individual modules as per edits
convertModules :: ConversionMonad m => [(ModuleName, RenamedSource)] -> m [NonEmpty ConvertedModule]
convertModules sources = do
  let convThisMod (mod,src) = use (edits.axiomatizedModules.contains mod) >>= \case
                                True  -> axiomatize_module_with_requires mod src
                                False -> convert_module_with_requires    mod src
  mods <- traverse convThisMod sources
  pure $
    stronglyConnCompNE [(cmod, convModName cmod, imps) | (cmod, imps) <- mods]

moduleDeclarations :: ConversionMonad m => ConvertedModule -> m ([Sentence], [Sentence])
moduleDeclarations ConvertedModule{..} = do
  orders <- use $ edits.orders
  let sorted = topoSortSentences orders $
        convModValDecls ++ convModClsInstDecls ++ convModAddedDecls
  ax_decls <- usedAxioms sorted
  not_decls <- qualifiedNotations convModName (convModTyClDecls ++ sorted)
  return $ deQualifyLocalNames convModName $ (convModTyClDecls ++ ax_decls, sorted ++ not_decls)

-- | This un-qualifies all variable names in the current module.
-- It should be called very late, just before pretty-printing.
deQualifyLocalNames :: Data a => ModuleName -> a -> a
deQualifyLocalNames modName = everywhere (mkT localize)
  where
    m' = moduleNameText modName

    localize :: Qualid -> Qualid
    localize (Qualified m b) | m == m' = Bare b
    localize qid = qid

usedAxioms :: forall m. ConversionMonad m => [Sentence] -> m [Sentence]
usedAxioms decls = do
    axs <- use axioms
    let ax_decls =
          [ AssumptionSentence (Assumption Axiom (UnparenthesizedAssums [i] t))
          | i <- toList (getFreeVars (NoBinding decls))
          , Just t <- return $ M.lookup i axs
          ]

        comment =
          [ CommentSentence (Comment "The Haskell code containes partial or \
             \untranslateable code, which needs the following")
          | not (null ax_decls)
          ]
    return $ comment ++ ax_decls

qualifiedNotations :: ConversionMonad m => ModuleName -> [Sentence] -> m [Sentence]
qualifiedNotations mod decls = do
    hmn <- use (edits . hasManualNotation . contains mod)
    return $ wrap $
        extra hmn ++
        [ NotationSentence qn
        | NotationSentence n <- decls, Just qn <- pure $ qualifyNotation mod n ]
  where
    wrap :: [Sentence] -> [Sentence]
    wrap []        = []
    wrap sentences = [ LocalModuleSentence (LocalModule "Notations" sentences) ]

    extra :: Bool -> [Sentence]
    extra True  = [ ModuleSentence (ModuleImport Export ["ManualNotations"]) ]
    extra False = []


