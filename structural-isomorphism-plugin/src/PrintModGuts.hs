{-# LANGUAGE TypeApplications, ScopedTypeVariables, LambdaCase,
             ViewPatterns, RecordWildCards,
             AllowAmbiguousTypes, GADTs, TypeFamilies, KindSignatures, DataKinds,
             TemplateHaskell #-}

module PrintModGuts (
  -- *Pieces of 'ModGuts' for printing
  ModGutsInfo(..), fullInfo, summaryInfo,
  -- *Printing 'ModGuts'
  formatModGuts, printModGuts,
  -- *Type hackery
  ModGutsInfoType, KnownInfo(..), SomeKnownModGutsInfo(..), known, unknown
) where

import qualified Language.Haskell.TH as TH

import Data.Generics (Proxy(..))

import Data.Bifunctor
import Data.Foldable
import Data.Traversable
import Data.Function
import Data.Maybe
import Data.List (sortBy)

import GHC
import Avail (AvailInfo())
import PatSyn (PatSyn())
import InstEnv (InstEnv(), instEnvElts, is_orphan)
import FamInstEnv (FamInstEnv(), famInstEnvElts)
import GhcPlugins
import PprCore
import Text.PrettyPrint.Util

-- These aren't in the order they show up in 'ModGuts', necessarily; they're in
-- the most useful order for printing.
data ModGutsInfo
  = MGI_Module
  | MGI_Location
  | MGI_Exports
  | MGI_InPackageImports
  | MGI_PackageDeps
  | MGI_OrphanInstanceDeps
  | MGI_TypeFamilyInstanceDeps
  | MGI_UsedFiles
  | MGI_UsedTemplateHaskell
  | MGI_Environment
  | MGI_Fixities
  | MGI_TypeConstructors
  | MGI_TypeClassInstances
  | MGI_TypeFamilyInstances
  | MGI_PatternSynonyms
  | MGI_Rules
  | MGI_ForeignStubs
  | MGI_Warnings
  | MGI_Annotations
  | MGI_HpcInfo
  | MGI_Breakpoints
  | MGI_VectorizationPragmas
  | MGI_VectorizedDeclarations
  | MGI_TypeClassInstanceEnvironment
  | MGI_TypeFamilyInstanceEnvironment
  | MGI_SafeHaskell
  | MGI_NeedToTrustSelfPkg
  | MGI_Contents
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

type family ModGutsInfoType (info :: ModGutsInfo) :: * where
  ModGutsInfoType 'MGI_Module                        = (Module, HscSource)
  ModGutsInfoType 'MGI_Location                      = SrcSpan
  ModGutsInfoType 'MGI_Exports                       = [AvailInfo]
  ModGutsInfoType 'MGI_InPackageImports              = [(ModuleName, IsBootInterface)]
  ModGutsInfoType 'MGI_PackageDeps                   = [(UnitId, Bool)]
  ModGutsInfoType 'MGI_OrphanInstanceDeps            = [Module]
  ModGutsInfoType 'MGI_TypeFamilyInstanceDeps        = [Module]
  ModGutsInfoType 'MGI_UsedFiles                     = [Usage]
  ModGutsInfoType 'MGI_UsedTemplateHaskell           = Bool
  ModGutsInfoType 'MGI_Environment                   = GlobalRdrEnv
  ModGutsInfoType 'MGI_Fixities                      = FixityEnv
  ModGutsInfoType 'MGI_TypeConstructors              = [TyCon]
  ModGutsInfoType 'MGI_TypeClassInstances            = [ClsInst]
  ModGutsInfoType 'MGI_TypeFamilyInstances           = [FamInst]
  ModGutsInfoType 'MGI_PatternSynonyms               = [PatSyn]
  ModGutsInfoType 'MGI_Rules                         = [CoreRule]
  ModGutsInfoType 'MGI_ForeignStubs                  = ForeignStubs
  ModGutsInfoType 'MGI_Warnings                      = Warnings
  ModGutsInfoType 'MGI_Annotations                   = [Annotation]
  ModGutsInfoType 'MGI_HpcInfo                       = HpcInfo
  ModGutsInfoType 'MGI_Breakpoints                   = Maybe ModBreaks
  ModGutsInfoType 'MGI_VectorizationPragmas          = [CoreVect]
  ModGutsInfoType 'MGI_VectorizedDeclarations        = VectInfo
  ModGutsInfoType 'MGI_TypeClassInstanceEnvironment  = InstEnv
  ModGutsInfoType 'MGI_TypeFamilyInstanceEnvironment = FamInstEnv
  ModGutsInfoType 'MGI_SafeHaskell                   = SafeHaskellMode
  ModGutsInfoType 'MGI_NeedToTrustSelfPkg            = Bool
  ModGutsInfoType 'MGI_Contents                      = CoreProgram

class KnownInfo (info :: ModGutsInfo) where
  knownInfo       :: ModGutsInfo
  infoDescription :: String
  infoData        :: ModGuts -> ModGutsInfoType info
  infoFormat      :: ModGutsInfoType info -> SDoc

data SomeKnownModGutsInfo where
  Known :: KnownInfo info => Proxy info -> SomeKnownModGutsInfo

unknown :: SomeKnownModGutsInfo -> ModGutsInfo
unknown (Known (Proxy :: Proxy info)) = knownInfo @info

instance Eq   SomeKnownModGutsInfo where (==)    = (==)    `on` unknown
instance Ord  SomeKnownModGutsInfo where compare = compare `on` unknown
instance Show SomeKnownModGutsInfo where
  showsPrec p (unknown -> info) =
    showParen (p >= 11) $ showString "Known @'" . shows info . showString " Proxy"

do sig <- TH.sigD (TH.mkName "known") [t|ModGutsInfo -> SomeKnownModGutsInfo|]
   TH.TyConI (TH.DataD _ _ _ _ cons _) <- TH.reify ''ModGutsInfo
   clauses <- fmap (TH.FunD $ TH.mkName "known") . for cons $ \case
     TH.NormalC info _ ->
       TH.clause [TH.conP info []]
                 (TH.normalB [e|Known (Proxy :: Proxy $(TH.promotedT info))|])
                 []
     _ ->
       fail "internal error: could not define `known'"
   pure [sig, clauses]

instance KnownInfo 'MGI_Module where
  knownInfo       = MGI_Module
  infoDescription = "Module"
  infoData        = (,) <$> mg_module <*> mg_hsc_src
  infoFormat      = \(mod, hscSrc) ->
    ppr mod <> case hscSrc of
                 HsSrcFile  -> empty
                 HsBootFile -> space <> text "[boot interface]"
                 HsigFile   -> space <> text "[signature]"

instance KnownInfo 'MGI_Location where
  knownInfo       = MGI_Location
  infoDescription = "Source locations"
  infoData        = mg_loc
  infoFormat      = ppr

instance KnownInfo 'MGI_Exports where
  knownInfo       = MGI_Exports
  infoDescription = "Exports"
  infoData        = mg_exports
  infoFormat      = ppr

instance KnownInfo 'MGI_InPackageImports where
  knownInfo       = MGI_InPackageImports
  infoDescription = "In-package imports"
  infoData        = dep_mods . mg_deps
  infoFormat      = pprListWith . pprAnnotated $ text "[boot]"

instance KnownInfo 'MGI_PackageDeps where
  knownInfo       = MGI_PackageDeps
  infoDescription = "Required packages"
  infoData        = dep_pkgs . mg_deps
  infoFormat      = pprListWith . pprAnnotated $ text "[must be trusted]"

instance KnownInfo 'MGI_OrphanInstanceDeps where
  knownInfo       = MGI_OrphanInstanceDeps
  infoDescription = "Orphan instances in"
  infoData        = dep_orphs . mg_deps
  infoFormat      = ppr

instance KnownInfo 'MGI_TypeFamilyInstanceDeps where
  knownInfo       = MGI_TypeFamilyInstanceDeps
  infoDescription = "Type family instantiations in"
  infoData        = dep_finsts . mg_deps
  infoFormat      = ppr

instance KnownInfo 'MGI_UsedFiles where
  knownInfo       = MGI_UsedFiles
  infoDescription = "Used files"
  infoData        = mg_usages
  infoFormat      = pprListWith (text . getUsageName)
                  . sortBy compareUsage
                  . map withUsageName
    where
      (UsageFile{},          name1) `compareUsage` (UsageFile{},          name2) =
        name1 `compare` name2
      (UsageHomeModule{},    name1) `compareUsage` (UsageHomeModule{},    name2) =
        name1 `compare` name2
      (UsagePackageModule{}, name1) `compareUsage` (UsagePackageModule{}, name2) =
        name1 `compare` name2
       
      (UsageFile{},          _) `compareUsage` _ = LT
      _ `compareUsage` (UsageFile{},          _) = GT
      
      (UsagePackageModule{}, _) `compareUsage` _ = GT
      _ `compareUsage` (UsagePackageModule{}, _) = LT
       
      usageName UsagePackageModule{..} = moduleNameString $ moduleName usg_mod
        -- TODO: include package?
      usageName UsageHomeModule{..}    = moduleNameString usg_mod_name
      usageName UsageFile{..}          = usg_file_path
       
      withUsageName u = (u, usageName u)
      getUsageName    = snd

instance KnownInfo 'MGI_UsedTemplateHaskell where
  knownInfo       = MGI_UsedTemplateHaskell
  infoDescription = "Template Haskell"
  infoData        = mg_used_th
  infoFormat      = yesNo

instance KnownInfo 'MGI_Environment where
  knownInfo       = MGI_Environment
  infoDescription = "Environment"
  infoData        = mg_rdr_env
  infoFormat      = pprListWith element
                  . sortBy (stableNameCmp `on` gre_name)
                  . concat . occEnvElts
    where
      element GRE{..} = ppr gre_name <> label [ parent   gre_par
                                              , nonlocal gre_lcl
                                              , imports  gre_imp ]
      
      label mlabels = case catMaybes mlabels of
                        []     -> empty
                        labels -> space <> pprListWith id labels

      parent NoParent =
        Nothing
      parent (ParentIs parent) =
        Just $ text "parent:" <+> ppr parent
      parent (FldParent parent mlabel) =
        Just $  text "parent:" <+> ppr parent
             <> case mlabel of
                  Just label -> text "." <> text (unpackFS label)
                  Nothing    -> empty
      parent PatternSynonym =
        Just $ text "pattern synonym"
      
      nonlocal True  = Nothing
      nonlocal False = Just $ text "nonlocal"

      imports _ = Nothing -- TODO

instance KnownInfo 'MGI_Fixities where
  knownInfo       = MGI_Fixities
  infoDescription = "Fixities"
  infoData        = mg_fix_env
  infoFormat      = ppr . nameEnvElts

instance KnownInfo 'MGI_TypeConstructors where
  knownInfo       = MGI_TypeConstructors
  infoDescription = "Type constructors"
  infoData        = mg_tcs
  infoFormat      = ppr

instance KnownInfo 'MGI_TypeClassInstances where
  knownInfo       = MGI_TypeClassInstances
  infoDescription = "Instances"
  infoData        = mg_insts
  infoFormat      = pprListWith $ \inst ->
                      pprInstanceHdr inst <> case is_orphan inst of
                                               IsOrphan    -> space <> text "[orphan]"
                                               NotOrphan _ -> empty

instance KnownInfo 'MGI_TypeFamilyInstances where
  knownInfo       = MGI_TypeFamilyInstances
  infoDescription = "Open type family instantiations"
  infoData        = mg_fam_insts
  infoFormat      = ppr

instance KnownInfo 'MGI_PatternSynonyms where
  knownInfo       = MGI_PatternSynonyms
  infoDescription = "Pattern synonyms"
  infoData        = mg_patsyns
  infoFormat      = ppr

instance KnownInfo 'MGI_Rules where
  knownInfo       = MGI_Rules
  infoDescription = "Rewrite rules"
  infoData        = mg_rules
  infoFormat      = pprListWith $ \case
                      Rule{..} ->
                        doubleQuotes (ftext ru_name) <+> ppr ru_act
                      BuiltinRule{..} ->
                        doubleQuotes (ftext ru_name) <+>
                        text "[builtin for" <+> ppr ru_fn <> text "]"

instance KnownInfo 'MGI_ForeignStubs where
  knownInfo       = MGI_ForeignStubs
  infoDescription = "Foreign stubs"
  infoData        = mg_foreign
  infoFormat      = \case
                      NoStubs ->
                        none
                      ForeignStubs prototypes cStubs ->
                        maybeEmpty none id $
                          labeled "Prototypes" prototypes $+$
                          labeled "C stubs"    cStubs
    where
      none = text "None"
      
      labeled label =
        maybeEmpty empty $ hang (text label <> colon) (length label + 1)

instance KnownInfo 'MGI_Warnings where
  knownInfo       = MGI_Warnings
  infoDescription = "Warning annotations"
  infoData        = mg_warns
  infoFormat      = pprListWith warning . \case
    NoWarnings    -> []
    WarnAll  txt  -> [(text "Whole module", txt)]
    WarnSome txts -> map (first ppr) txts
    where
      warning (what,txt) = warningFor what txt <+> warningText txt
      
      warningFor what (WarningTxt    _ _) = what <> colon
      warningFor what (DeprecatedTxt _ _) = what <> text ": [DEPRECATED]"
      
      warningText = fsep . map (ftext . sl_fs . unLoc) . \case
                      WarningTxt    _ lits -> lits
                      DeprecatedTxt _ lits -> lits

instance KnownInfo 'MGI_Annotations where
  knownInfo       = MGI_Annotations
  infoDescription = "Annotations"
  infoData        = mg_anns
  infoFormat      = pprListWith $ \Annotation{..} ->
    let target  = case ann_target of
                    NamedTarget  name -> ppr name
                    ModuleTarget mod  -> text "module" <+> ppr mod
        payload = case ann_value of
                    Serialized ty _bytes -> text (show ty)
    in parens $ target <> comma <+> payload

instance KnownInfo 'MGI_HpcInfo where
  knownInfo       = MGI_HpcInfo
  infoDescription = "HPC"
  infoData        = mg_hpc_info
  infoFormat      = \case
    HpcInfo ticks _ -> text "Used;" <+>
                       ppr ticks <+> text "tick" <> if ticks == 1 then empty else char 's'
    NoHpcInfo True  -> text "Unused, but depended on"
    NoHpcInfo False -> text "Unused"

instance KnownInfo 'MGI_Breakpoints where
  knownInfo       = MGI_Breakpoints
  infoDescription = "Breakpoints"
  infoData        = mg_modBreaks
  infoFormat      = ppr . maybe [] (toList . modBreaks_locs)
  -- TODO: We could inclode the other information, but the location is by far
  -- the simplest and is probably one of the most useful things

instance KnownInfo 'MGI_VectorizationPragmas where
  knownInfo       = MGI_VectorizationPragmas
  infoDescription = "Vectorization pragmas"
  infoData        = mg_vect_decls
  infoFormat      = ppr

instance KnownInfo 'MGI_VectorizedDeclarations where
  knownInfo       = MGI_VectorizedDeclarations
  infoDescription = "Vectorized declarations"
  infoData        = mg_vect_info
  infoFormat      = ppr

instance KnownInfo 'MGI_TypeClassInstanceEnvironment where
  knownInfo       = MGI_TypeClassInstanceEnvironment
  infoDescription = "Type class instance environment"
  infoData        = mg_inst_env
  infoFormat      = ppr . instEnvElts

instance KnownInfo 'MGI_TypeFamilyInstanceEnvironment where
  knownInfo       = MGI_TypeFamilyInstanceEnvironment
  infoDescription = "Type family instance environment"
  infoData        = mg_fam_inst_env
  infoFormat      = ppr . famInstEnvElts

instance KnownInfo 'MGI_SafeHaskell where
  knownInfo       = MGI_SafeHaskell
  infoDescription = "Safe Haskell"
  infoData        = mg_safe_haskell
  infoFormat      = ppr

instance KnownInfo 'MGI_NeedToTrustSelfPkg where
  knownInfo       = MGI_NeedToTrustSelfPkg
  infoDescription = "Needs to trust its own package"
  infoData        = mg_trust_pkg
  infoFormat      = yesNo

instance KnownInfo 'MGI_Contents where
  knownInfo       = MGI_Contents
  infoDescription = "Contents"
  infoData        = mg_binds
  infoFormat      = pprCoreBindings -- TODO: Newline first?
                    
formatModGuts :: [ModGutsInfo] -> ModGuts -> SDoc
formatModGuts infos guts =
  let format (known -> Known (Proxy :: Proxy info)) =
        text (infoDescription @info) <> colon
          <+> infoFormat @info (infoData @info guts)
  in foldr ($+$) empty $ map format infos

printModGuts :: [ModGutsInfo] -> ModGuts -> CoreM ()
printModGuts = (putMsg .) . formatModGuts

fullInfo :: [ModGutsInfo]
fullInfo = [minBound..maxBound]

summaryInfo :: [ModGutsInfo]
summaryInfo = [MGI_Module, MGI_Exports, MGI_Contents]
