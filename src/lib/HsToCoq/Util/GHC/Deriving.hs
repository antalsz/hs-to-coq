{-# LANGUAGE RecordWildCards #-}

{-
This seems to work. But it is a hack!
A 10-line patch extending the GHC-API would make that go away
-}

module HsToCoq.Util.GHC.Deriving (initForDeriving, addDerivedInstances) where

import GHC

import Control.Monad

import Outputable
import TcRnMonad
import TcEnv
import InstEnv
import Var
import TyCoRep
import Type
import TcType
import HscTypes
import TcInstDcls
import Module
import SrcLoc
import FastString
import GHC.IO (throwIO)
import DynFlags
import qualified GHC.LanguageExtensions as LangExt

-- We need to allow IncoherentInstances for the hack in HsToCoq.Util.GHC.Deriving
initForDeriving :: GhcMonad m => m ()
initForDeriving =
  void $ getSessionDynFlags >>= setSessionDynFlags . (`xopt_set` LangExt.IncoherentInstances)

addDerivedInstances :: GhcMonad m => TypecheckedModule -> m TypecheckedModule
addDerivedInstances tcm = do
    let Just (hsgroup, a, b, c) = tm_renamed_source tcm

    (_gbl_env, inst_infos, _rn_binds) <- initTcHack tcm $ do
        let tcg_env = fst (tm_internals_ tcm)
            tcg_env_hack = tcg_env { tcg_mod = fakeDerivingMod }
                -- Set the module to make it look like we are in GHCi
                -- so that GHC will allow us to re-typecheck existing instances
        setGblEnv tcg_env_hack $ do
            tcInstDecls1 (hs_tyclds hsgroup) [] (hs_derivds hsgroup)

    let inst_decls = map instInfoToDecl $ inst_infos

    let hsgroup' = hsgroup { hs_instds = inst_decls ++ hs_instds hsgroup }

    return $ tcm { tm_renamed_source = Just (hsgroup', a, b, c) }

initTcHack :: GhcMonad m => TypecheckedModule -> TcM a -> m a
initTcHack tcm action = do
 hsc_env <- getSession
 let hsc_env_tmp = hsc_env
        { hsc_dflags = ms_hspp_opts (pm_mod_summary (tm_parsed_module tcm)) }
 let mod = fakeDerivingMod
 -- let mod = icInteractiveModule (hsc_IC hsc_env)
 let src_span = realSrcLocSpan (mkRealSrcLoc (fsLit "<deriving>") 1 1)

 (msgs, mba) <- liftIO $ initTc hsc_env_tmp HsSrcFile False mod src_span action
 case mba of Just x ->  return x
             Nothing -> liftIO $ throwIO $ mkSrcErr $ snd msgs

fakeDerivingMod :: Module
fakeDerivingMod = mkModule interactiveUnitId (mkModuleName "Deriving")


instInfoToDecl :: InstInfo Name -> LInstDecl Name
instInfoToDecl inst_info = noLoc $ ClsInstD (ClsInstDecl {..})
   where
    cid_poly_ty = HsIB tvars' $ noLoc (HsQualTy (noLoc ctxt) inst_head)
    cid_binds = ib_binds (iBinds inst_info)
    cid_sigs = []
    cid_tyfam_insts = []
    cid_datafam_insts = []
    cid_overlap_mode = Nothing

    (tvars, theta, cls, args) = instanceSig (iSpec inst_info)
    tvars' :: [Name]
    tvars' = map tyVarName tvars
    ctxt = map typeToLHsType' theta
    inst_head = foldl lHsAppTy (noLoc (HsTyVar (noLoc (getName cls)))) $
        map typeToLHsType' args

    lHsAppTy f x = noLoc (HsAppTy f x)

-- Taken from HsUtils. We need it to produce a Name, not a RdrName
typeToLHsType' :: Type -> LHsType Name
typeToLHsType' ty
  = go ty
  where
    go :: Type -> LHsType Name
    go ty@(ForAllTy (Anon arg) _)
      | isPredTy arg
      , (theta, tau) <- tcSplitPhiTy ty
      = noLoc (HsQualTy { hst_ctxt = noLoc (map go theta)
                        , hst_body = go tau })
    go (ForAllTy (Anon arg) res) = nlHsFunTy (go arg) (go res)
    go ty@(ForAllTy {})
      | (tvs, tau) <- tcSplitForAllTys ty
      = noLoc (HsForAllTy { hst_bndrs = map go_tv tvs
                          , hst_body = go tau })
    go (TyVarTy tv)         = nlHsTyVar (getName tv)
    go (AppTy t1 t2)        = nlHsAppTy (go t1) (go t2)
    go (LitTy (NumTyLit n)) = noLoc $ HsTyLit (HsNumTy "" n)
    go (LitTy (StrTyLit s)) = noLoc $ HsTyLit (HsStrTy "" s)
    go (TyConApp tc args)   = nlHsTyConApp (getName tc) (map go args')
       where
         args' = filterOutInvisibleTypes tc args
    go (CastTy ty _)        = go ty
    go (CoercionTy co)      = pprPanic "toLHsSigWcType" (ppr co)

         -- Source-language types have _invisible_ kind arguments,
         -- so we must remove them here (Trac #8563)

    go_tv :: TyVar -> LHsTyVarBndr Name
    go_tv tv = noLoc $ KindedTyVar (noLoc (getName tv))
                                   (go (tyVarKind tv))
