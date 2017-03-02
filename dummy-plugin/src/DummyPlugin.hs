{-# LANGUAGE RecordWildCards, NamedFieldPuns, LambdaCase, StandaloneDeriving #-}
{-# LANGUAGE RankNTypes, ConstraintKinds, ScopedTypeVariables, MultiWayIf #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances,
             GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving, DeriveGeneric, DefaultSignatures, FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module DummyPlugin where

import Data.Ord
import Data.List (sortBy)

import Data.Generics hiding (Generic, empty, GT)

import Data.Map (Map)
import qualified Data.Map as M

import CmmType
import Var
import Type
import TypeRep
import TcType
import ForeignCall
import InstEnv
import GhcPlugins
import PprCore

import qualified CoqCoreBind as Coq
import Data.Functor.Identity
import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Control.Monad.Writer hiding ((<>))
import Control.Monad.State
import Data.Set (Set)
import GHC.Generics
import Data.Coerce

import Language.Haskell.TH hiding (ppr, Safety(), Type(), Kind(), Name())
import qualified Language.Haskell.TH as TH

coreTransformerPlugin :: String -> PluginPass -> Plugin
coreTransformerPlugin name pass =
  defaultPlugin{ installCoreToDos = \_ todos ->
                   (CoreDoPluginPass name pass : todos) <$ reinitializeGlobals }

putTagged :: String -> SDoc -> CoreM ()
putTagged info =
  let depth = length info + 1
  in putMsg . hang (text info) depth

putTaggedS :: String -> String -> CoreM ()
putTaggedS = (. text) . putTagged

printTagged :: Outputable a => String -> a -> CoreM ()
printTagged = (. ppr) . putTagged

logDoc :: SDoc -> CoreM ()
logDoc = putTagged "[dummy-plugin]"

logMsg :: String -> CoreM ()
logMsg = putTaggedS "[dummy-plugin]"

logObj :: Outputable a => a -> CoreM ()
logObj = printTagged "[dummy-plugin]"

-- data Field = MGModule
--            | MGExports
--            | MGImports
           
--            | MGTemplateHaskell
           
--            | MGLocalImports
--            | MGPackageDeps
--            | MGOrphanModules
--            | MGTypeFamilyModules
           
--            | MGNames
--            | MGEnvironment
           
--            | MGFixities
--            | MGRules
--            | MGOpenTypeFamilyInstantiations

printModGuts :: (Monad m, HasDynFlags m) => (SDoc -> m ()) -> ModGuts -> m ()
printModGuts put ModGuts{mg_deps=Deps{..}, ..} = do
  df <- getDynFlags

  let putField name field = put $ text name <> char ':' <+> field
      
      pprListWith f = brackets . pprWithCommas f
      
      addWhen True  doc = space <> doc
      addWhen False _   = empty
      
      annotated annot (obj, cond) = ppr obj <> addWhen cond annot
      
      alphabeticalBy f = sortBy (comparing $ showSDoc df . f)
      alphabetical     = alphabeticalBy ppr
  
  putField "Module" $ ppr mg_module <> addWhen mg_boot (text "[boot interface]")
  putField "Exports" $ ppr mg_exports
  putField "In-package imports" $ pprListWith (annotated $ text "[boot]") dep_mods
  putField "Required packages" $ pprListWith (annotated $ text "[must be trusted]") dep_pkgs
  putField "Orphan instances in" $ ppr dep_orphs
  putField "Type family instantiations in" $ ppr dep_finsts
  putField "Imports" . pprListWith (\(name,empty,_span,safe) ->
                                      ppr name <> addWhen empty (text "[instances]")
                                               <> addWhen safe  (text "[safe]"))
                     . concat $ moduleEnvElts mg_dir_imps
  putField "Referenced names" . ppr . alphabetical $ nameSetElems mg_used_names
  putField "Template Haskell" . text $ if mg_used_th then "Yes" else "No"
  putField "Environment" . pprListWith (\GRE{..} ->
                                          ppr gre_name <>
                                          case gre_par of
                                            NoParent ->
                                              empty
                                            ParentIs parent ->
                                              space <>
                                              text "[parent:" <+> ppr parent <> text "]")
                         . alphabeticalBy (ppr . gre_name)
                         . concat $ occEnvElts mg_rdr_env
  putField "Fixities" . ppr $ nameEnvElts mg_fix_env
  putField "Type constructors" $ ppr mg_tcs
  putField "Instances" $ pprListWith (\inst -> pprInstanceHdr inst
                                            <> case is_orphan inst of
                                                 IsOrphan    -> space <> text "[orphan]"
                                                 NotOrphan _ -> empty)
                                     mg_insts
  putField "Open type family instantiations" $ ppr mg_fam_insts
  putField "Pattern synonyms" $ ppr mg_patsyns
  putField "Rewrite rules" $ pprListWith (\case
                                             Rule{..} ->
                                               doubleQuotes (ftext ru_name) <+> ppr ru_act
                                             BuiltinRule{..} ->
                                               doubleQuotes (ftext ru_name) <+>
                                               text "[builtin for" <+> ppr ru_fn <> text "]")
                                         mg_rules
  -- putField "Module" $ ppr mg_binds
  -- putField "Foreign stubs" $ case mg_foreign of
  --                              NoStubs                         -> text "[]"
  --                              ForeignStubs prototypes c_stubs -> prototyes
  
  -- mg_module :: !Module,
  -- mg_boot :: IsBootInterface,
  -- mg_exports :: ![Avail.AvailInfo],
  -- mg_deps :: !Dependencies,
  -- mg_dir_imps :: !ImportedMods,
  -- mg_used_names :: !NameSet,
  -- mg_used_th :: !Bool,
  -- mg_rdr_env :: !GlobalRdrEnv,
  -- mg_fix_env :: !FixityEnv,
  -- mg_tcs :: ![TyCon],
  -- mg_insts :: ![InstEnv.ClsInst],
  -- mg_fam_insts :: ![FamInstEnv.FamInst],
  -- mg_patsyns :: ![PatSyn.PatSyn],
  -- mg_rules :: ![CoreRule],
-- mg_binds :: !CoreProgram,
  -- mg_foreign :: !ForeignStubs,
-- mg_warns :: !Warnings,
-- mg_anns :: [Annotation],
-- mg_hpc_info :: !HpcInfo,
-- mg_modBreaks :: !ModBreaks,
-- mg_vect_decls :: ![CoreVect],
-- mg_vect_info :: !VectInfo,
-- mg_inst_env :: InstEnv.InstEnv,
-- mg_fam_inst_env :: FamInstEnv.FamInstEnv,
-- mg_safe_haskell :: SafeHaskellMode,
-- mg_trust_pkg :: Bool,

printShortModGuts :: (Monad m, HasDynFlags m) => (SDoc -> m ()) -> ModGuts -> m ()
printShortModGuts put ModGuts{mg_deps=Deps{..}, ..} = do
  let putField name field = put $ text name <> char ':' <+> field
      
      pprListWith f = brackets . pprWithCommas f
      
      addWhen True  doc = space <> doc
      addWhen False _   = empty

  putField "Module" $ ppr mg_module <> addWhen mg_boot (text "[boot interface]")
  putField "Exports" $ ppr mg_exports
  putField "Imports" . pprListWith (\(name,empty,_span,safe) ->
                                      ppr name <> addWhen empty (text "[instances]")
                                               <> addWhen safe  (text "[safe]"))
                     . concat $ moduleEnvElts mg_dir_imps
  putField "Contents" $ pprCoreBindings mg_binds

--------------------------------------------------------------------------------

galloftype :: (Typeable a, Data b) => proxy a -> b -> [a]
galloftype pa = listify (always pa)
  where always :: proxy a -> a -> Bool
        always _ = const True

gcounttype :: (Typeable a, Data b) => proxy a -> b -> Int
gcounttype = (length .) . galloftype

gcontains :: (Typeable a, Data b) => proxy a -> b -> Bool
gcontains = ((not . null) .) . galloftype

idInfoP :: Proxy IdInfo
idInfoP = Proxy

varPx :: Proxy Var
varPx = Proxy

--------------------------------------------------------------------------------

(><) :: Monoid a => a -> a -> a
(><) = mappend
infixr 6 ><

newtype VarKey = VarKey { getVarKey :: Var }

deriving instance Eq MetaInfo
deriving instance Eq TcTyVarDetails
deriving instance Eq TickBoxOp
deriving instance Eq IdDetails

deriving instance Ord MetaInfo
deriving instance Ord TcLevel
instance Ord TcTyVarDetails where
  SkolemTv b1    `compare` SkolemTv b2    = b1 `compare` b2
  SkolemTv _     `compare` FlatSkol _     = LT
  SkolemTv _     `compare` RuntimeUnk     = LT
  SkolemTv _     `compare` MetaTv{}       = LT
  
  FlatSkol _     `compare` SkolemTv _     = GT
  FlatSkol t1    `compare` FlatSkol t2    = t1 `compare` t2
  FlatSkol _     `compare` RuntimeUnk     = LT
  FlatSkol _     `compare` MetaTv{}       = LT
  
  RuntimeUnk     `compare` SkolemTv _     = GT
  RuntimeUnk     `compare` FlatSkol _     = GT
  RuntimeUnk     `compare` RuntimeUnk     = GT
  RuntimeUnk     `compare` MetaTv{}       = LT
  
  MetaTv{}       `compare` SkolemTv _     = GT
  MetaTv{}       `compare` FlatSkol _     = GT
  MetaTv{}       `compare` RuntimeUnk     = GT
  MetaTv i1 _ l1 `compare` MetaTv i2 _ l2 = i1 `compare` i2 >< l1 `compare` l2
deriving instance Ord TickBoxOp
deriving instance Ord CCallConv
deriving instance Ord Safety
deriving instance Ord CCallTarget
deriving instance Ord CCallSpec
deriving instance Ord ForeignCall
deriving instance Ord Type
deriving instance Ord IdDetails

isTyVarNonTc :: Var -> Bool
isTyVarNonTc = (&&) <$> isTyVar <*> not . isTcTyVar

liftBinOpVarKey :: forall c a.
                   (c Bool, c Unique, c Name, c Kind, c IdDetails, c TcTyVarDetails)
                => Proxy c
                -> (forall b. c b => b -> b -> a)
                -> (a -> a -> a) -> (Var -> Var -> a)
                -> VarKey -> VarKey
                -> a
liftBinOpVarKey _ (~~) (#) different (VarKey v1) (VarKey v2)
  | same isTcTyVar    = linkedCommon
  | same isTyVarNonTc = linkedCommon # linked tcTyVarDetails
  | same isId         = linkedCommon # linked isGlobalId
                                     # linked isLocalId
                                     # linked isExportedId
                                     # linked idDetails
                                     -- Ignore the `IdInfo`
  | otherwise         = different v1 v2
  where
    same   f = f v1 == f v2
    linked :: c z => (Var -> z) -> a
    linked f = f v1 ~~ f v2
    linkedCommon = linked varUnique #  linked varName #  linked varType

instance Eq VarKey where
  (==) = liftBinOpVarKey (Proxy :: Proxy Eq) (==) (&&) (\_ _ -> False)

instance Ord VarKey where
  compare = liftBinOpVarKey (Proxy :: Proxy Ord) compare (><) $ \v1 v2 ->
              if | isTyVarNonTc v1 -> LT
                 | isTyVarNonTc v2 -> GT
                 | isId         v1 -> GT
                 | isId         v2 -> LT
                 | otherwise       -> error "compare{Ord VarKey}: impossible!"

--------------------------------------------------------------------------------

newtype ToCoqT m a = ToCoqT { getToCoqT :: WriterT (Map VarKey IdInfo) m a }
                   deriving ( Functor, Applicative, Monad
                            , Alternative, MonadPlus
                            , MonadFix, MonadIO
                            , MonadWriter (Map VarKey IdInfo)
                            , MonadTrans )
type ToCoq = ToCoqT Identity

runToCoqT :: ToCoqT m a -> m (a, Map VarKey IdInfo)
runToCoqT = runWriterT . getToCoqT

runToCoq :: ToCoq a -> (a, Map VarKey IdInfo)
runToCoq = runWriter . getToCoqT

newtype ToHST  m a = ToHST  { getToHST  :: ReaderT (Map VarKey IdInfo) m a }
                   deriving ( Functor, Applicative, Monad
                            , Alternative, MonadPlus
                            , MonadFix, MonadIO
                            , MonadReader (Map VarKey IdInfo)
                            , MonadTrans )
type ToHS  = ToHST  Identity

class Extracted hs coq | hs -> coq, coq -> hs where
  toCoq :: hs  -> ToCoq coq
  toHS  :: coq -> ToHS  hs

  default toCoq :: (Generic hs, Generic coq, Coercible (Rep hs) (Rep coq))
                => hs -> ToCoq coq
  toCoq = pure
        . (to     :: Rep coq x -> coq)
        . (coerce :: Rep hs x -> Rep coq x)
        . (from   :: hs -> Rep hs x)

  default toHS :: (Generic hs, Generic coq, Coercible (Rep hs) (Rep coq))
               => coq -> ToHS hs
  toHS = pure
       . (to     :: Rep hs x -> hs)
       . (coerce :: Rep coq x -> Rep hs x)
       . (from   :: coq -> Rep coq x)

deriving instance Generic Width
instance Extracted Width Coq.Width

instance Extracted Var Coq.Var where
  toCoq = undefined
  toHS  = undefined

instance Extracted hs_b coq_b => Extracted (Bind hs_b) (Coq.Bind coq_b) where
  toCoq = undefined
  toHS  = undefined

instance Extracted hs coq => Extracted [hs] [coq] where
  toCoq = traverse toCoq
  toHS  = traverse toHS

infos :: Map VarKey IdInfo
infos = M.fromList []

-- class GConvert' f1 f2 where
--   convert' :: f1 p -> f2 p

-- instance GConvert' V1 V1 where
--   convert' = \case

-- instance GConvert' V1 V1 where
--   convert' = \case

-- data    U1        p = U1                  -- lifted version of ()
-- data    (:+:) f g p = L1 (f p) | R1 (g p) -- lifted version of Either
-- data    (:*:) f g p = (f p) :*: (g p)     -- lifted version of (,)
-- newtype K1    i c p = K1 { unK1 :: c }    -- a container for a c
-- newtype M1  i t f p = M1 { unM1 :: f p }  -- a wrapper

data DataType = DataType { dtContext      :: Cxt
                         , dtName         :: TH.Name
                         , dtParameters   :: [TyVarBndr]
                         , dtKind         :: Maybe TH.Kind
                         , dtConstructors :: [Con]
                         , dtDeriving     :: Cxt }
              deriving (Eq, Ord, Show, Generic)

data Isomorphism = !TH.Name :~~~: !TH.Name deriving (Eq, Ord)

instance Show Isomorphism where
  showsPrec p (ty1 :~~: ty2) = showParen (p >= 5) $
    showsPrec 5 ty1 . showString " :~~: " . showsPrec 5 ty2
  showsPrec _ _ = error "impossible"

pattern ty1 :~~: ty2 <- ty1 :~~~: ty2 where
  ty1 :~~: ty2 | ty1 <= ty2 = ty1 :~~~: ty2
               | otherwise  = ty2 :~~~: ty1

infix 4 :~~: , :~~~:

newtype Isomorphize a = Isomorphize { getIsomorphize :: State (Set Isomorphism) a }
                      deriving ( Functor, Applicative, Monad
                               , MonadFix
                               , MonadState (Set Isomorphism) )

-- isomorphic :: DataType -> DataType -> Bool
-- isomorphic dt1 dt2 = _ where
--   isoCxt :: Cxt -> Cxt -> Bool
--   isoCxt 

-- isomorphic :: Dec -> Dec -> Bool
-- isomorphic (DataD 

--------------------------------------------------------------------------------

plugin :: Plugin
plugin = coreTransformerPlugin "Dummy Plugin" $ \guts -> do
    printShortModGuts logDoc guts
    let (coqBinds, _idInfos) = runToCoq . toCoq $ mg_binds guts
    case gcounttype varPx coqBinds of
      0 -> logMsg $ "No more `Var`s!"
      n -> logMsg $ "`Var` count: " ++ show n
    pure guts
