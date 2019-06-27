(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Core.
Require FV.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require Name.
Require OccName.
Require UniqSupply.
Require Unique.
Require Util.

(* Converted type declarations: *)

Inductive TyLit : Type
  := | NumTyLit : GHC.Num.Integer -> TyLit
  |  StrTyLit : FastString.FastString -> TyLit.

Definition KindOrType :=
  AxiomatizedTypes.Type_%type.

Definition CoercionR :=
  AxiomatizedTypes.Coercion%type.

Definition CoercionP :=
  AxiomatizedTypes.Coercion%type.

Definition CoercionN :=
  AxiomatizedTypes.Coercion%type.

Definition KindCoercion :=
  CoercionN%type.

Inductive UnivCoProvenance : Type
  := | UnsafeCoerceProv : UnivCoProvenance
  |  PhantomProv : KindCoercion -> UnivCoProvenance
  |  ProofIrrelProv : KindCoercion -> UnivCoProvenance
  |  PluginProv : GHC.Base.String -> UnivCoProvenance.

Axiom CoercionHole : Type.

Instance Default__UnivCoProvenance : GHC.Err.Default UnivCoProvenance :=
  GHC.Err.Build_Default _ UnsafeCoerceProv.

(* Converted value declarations: *)

Axiom zipTyEnv : list Core.TyVar ->
                 list AxiomatizedTypes.Type_ -> Core.TvSubstEnv.

Axiom zipTvSubst : list Core.TyVar ->
                   list AxiomatizedTypes.Type_ -> Core.TCvSubst.

Axiom zipCvSubst : list Core.CoVar ->
                   list AxiomatizedTypes.Coercion -> Core.TCvSubst.

Axiom zipCoEnv : list Core.CoVar ->
                 list AxiomatizedTypes.Coercion -> Core.CvSubstEnv.

Axiom zapTCvSubst : Core.TCvSubst -> Core.TCvSubst.

Axiom unionTCvSubst : Core.TCvSubst -> Core.TCvSubst -> Core.TCvSubst.

Axiom typeSize : AxiomatizedTypes.Type_ -> nat.

Axiom tyThingCategory : AxiomatizedTypes.TyThing -> GHC.Base.String.

Axiom tyCoVarsOfTypesSet : Core.TyVarEnv AxiomatizedTypes.Type_ ->
                           Core.TyCoVarSet.

Axiom tyCoVarsOfTypesList : list AxiomatizedTypes.Type_ -> list Core.TyCoVar.

Axiom tyCoVarsOfTypesDSet : list AxiomatizedTypes.Type_ -> Core.DTyCoVarSet.

Axiom tyCoVarsOfTypes : list AxiomatizedTypes.Type_ -> Core.TyCoVarSet.

Axiom tyCoVarsOfTypeList : AxiomatizedTypes.Type_ -> list Core.TyCoVar.

Axiom tyCoVarsOfTypeDSet : AxiomatizedTypes.Type_ -> Core.DTyCoVarSet.

Axiom tyCoVarsOfType : AxiomatizedTypes.Type_ -> Core.TyCoVarSet.

Axiom tyCoVarsOfProv : UnivCoProvenance -> Core.TyCoVarSet.

Axiom tyCoVarsOfCosSet : Core.CoVarEnv AxiomatizedTypes.Coercion ->
                         Core.TyCoVarSet.

Axiom tyCoVarsOfCos : list AxiomatizedTypes.Coercion -> Core.TyCoVarSet.

Axiom tyCoVarsOfCoList : AxiomatizedTypes.Coercion -> list Core.TyCoVar.

Axiom tyCoVarsOfCoDSet : AxiomatizedTypes.Coercion -> Core.DTyCoVarSet.

Axiom tyCoVarsOfCo : AxiomatizedTypes.Coercion -> Core.TyCoVarSet.

Axiom tyCoFVsOfTypes : list AxiomatizedTypes.Type_ -> FV.FV.

Axiom tyCoFVsOfType : AxiomatizedTypes.Type_ -> FV.FV.

Axiom tyCoFVsOfProv : UnivCoProvenance -> FV.FV.

Axiom tyCoFVsOfCos : list AxiomatizedTypes.Coercion -> FV.FV.

Axiom tyCoFVsOfCoVar : Core.CoVar -> FV.FV.

Axiom tyCoFVsOfCo : AxiomatizedTypes.Coercion -> FV.FV.

Axiom tyCoFVsBndr : Core.TyVarBinder -> FV.FV -> FV.FV.

Axiom tidyTypes : Core.TidyEnv ->
                  list AxiomatizedTypes.Type_ -> list AxiomatizedTypes.Type_.

Axiom tidyType : Core.TidyEnv ->
                 AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom tidyTyVarOcc : Core.TidyEnv -> Core.TyVar -> Core.TyVar.

Axiom tidyTyVarBinders : forall {vis},
                         Core.TidyEnv ->
                         list (Core.TyVarBndr Core.TyVar vis) ->
                         (Core.TidyEnv * list (Core.TyVarBndr Core.TyVar vis))%type.

Axiom tidyTyVarBinder : forall {vis},
                        Core.TidyEnv ->
                        Core.TyVarBndr Core.TyVar vis ->
                        (Core.TidyEnv * Core.TyVarBndr Core.TyVar vis)%type.

Axiom tidyTyCoVarBndrs : Core.TidyEnv ->
                         list Core.TyCoVar -> (Core.TidyEnv * list Core.TyCoVar)%type.

Axiom tidyTyCoVarBndr : Core.TidyEnv ->
                        Core.TyCoVar -> (Core.TidyEnv * Core.TyCoVar)%type.

Axiom tidyTopType : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom tidyOpenTypes : Core.TidyEnv ->
                      list AxiomatizedTypes.Type_ ->
                      (Core.TidyEnv * list AxiomatizedTypes.Type_)%type.

Axiom tidyOpenType : Core.TidyEnv ->
                     AxiomatizedTypes.Type_ -> (Core.TidyEnv * AxiomatizedTypes.Type_)%type.

Axiom tidyOpenTyCoVars : Core.TidyEnv ->
                         list Core.TyCoVar -> (Core.TidyEnv * list Core.TyCoVar)%type.

Axiom tidyOpenTyCoVar : Core.TidyEnv ->
                        Core.TyCoVar -> (Core.TidyEnv * Core.TyCoVar)%type.

Axiom tidyOpenKind : Core.TidyEnv ->
                     AxiomatizedTypes.Kind -> (Core.TidyEnv * AxiomatizedTypes.Kind)%type.

Axiom tidyKind : Core.TidyEnv -> AxiomatizedTypes.Kind -> AxiomatizedTypes.Kind.

Axiom tidyFreeTyCoVars : Core.TidyEnv -> list Core.TyCoVar -> Core.TidyEnv.

Axiom tidyCos : Core.TidyEnv ->
                list AxiomatizedTypes.Coercion -> list AxiomatizedTypes.Coercion.

Axiom tidyCo : Core.TidyEnv ->
               AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom subst_ty : Core.TCvSubst ->
                 AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom subst_co : Core.TCvSubst ->
                 AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom substTysWithCoVars : list Core.CoVar ->
                           list AxiomatizedTypes.Coercion ->
                           list AxiomatizedTypes.Type_ -> list AxiomatizedTypes.Type_.

Axiom substTysWith : list Core.TyVar ->
                     list AxiomatizedTypes.Type_ ->
                     list AxiomatizedTypes.Type_ -> list AxiomatizedTypes.Type_.

Axiom substTysUnchecked : Core.TCvSubst ->
                          list AxiomatizedTypes.Type_ -> list AxiomatizedTypes.Type_.

Axiom substTys : forall `{Util.HasDebugCallStack},
                 Core.TCvSubst -> list AxiomatizedTypes.Type_ -> list AxiomatizedTypes.Type_.

Axiom substTyWithUnchecked : list Core.TyVar ->
                             list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom substTyWithInScope : Core.InScopeSet ->
                           list Core.TyVar ->
                           list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom substTyWithCoVars : list Core.CoVar ->
                          list AxiomatizedTypes.Coercion ->
                          AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom substTyWith : forall `{Util.HasDebugCallStack},
                    list Core.TyVar ->
                    list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom substTyVars : Core.TCvSubst ->
                    list Core.TyVar -> list AxiomatizedTypes.Type_.

Axiom substTyVarBndrUnchecked : Core.TCvSubst ->
                                Core.TyVar -> (Core.TCvSubst * Core.TyVar)%type.

Axiom substTyVarBndrCallback : (Core.TCvSubst ->
                                AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_) ->
                               Core.TCvSubst -> Core.TyVar -> (Core.TCvSubst * Core.TyVar)%type.

Axiom substTyVarBndr : forall `{Util.HasDebugCallStack},
                       Core.TCvSubst -> Core.TyVar -> (Core.TCvSubst * Core.TyVar)%type.

Axiom substTyVar : Core.TCvSubst -> Core.TyVar -> AxiomatizedTypes.Type_.

Axiom substTyUnchecked : Core.TCvSubst ->
                         AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom substTyAddInScope : Core.TCvSubst ->
                          AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom substTy : forall `{Util.HasDebugCallStack},
                Core.TCvSubst -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom substThetaUnchecked : Core.TCvSubst ->
                            AxiomatizedTypes.ThetaType -> AxiomatizedTypes.ThetaType.

Axiom substTheta : forall `{Util.HasDebugCallStack},
                   Core.TCvSubst -> AxiomatizedTypes.ThetaType -> AxiomatizedTypes.ThetaType.

Axiom substForAllCoBndrUnchecked : Core.TCvSubst ->
                                   Core.TyVar ->
                                   AxiomatizedTypes.Coercion ->
                                   (Core.TCvSubst * Core.TyVar * AxiomatizedTypes.Coercion)%type.

Axiom substForAllCoBndrCallback : bool ->
                                  (AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion) ->
                                  Core.TCvSubst ->
                                  Core.TyVar ->
                                  AxiomatizedTypes.Coercion ->
                                  (Core.TCvSubst * Core.TyVar * AxiomatizedTypes.Coercion)%type.

Axiom substForAllCoBndr : Core.TCvSubst ->
                          Core.TyVar ->
                          AxiomatizedTypes.Coercion ->
                          (Core.TCvSubst * Core.TyVar * AxiomatizedTypes.Coercion)%type.

Axiom substCos : forall `{Util.HasDebugCallStack},
                 Core.TCvSubst ->
                 list AxiomatizedTypes.Coercion -> list AxiomatizedTypes.Coercion.

Axiom substCoWithUnchecked : list Core.TyVar ->
                             list AxiomatizedTypes.Type_ ->
                             AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom substCoWith : forall `{Util.HasDebugCallStack},
                    list Core.TyVar ->
                    list AxiomatizedTypes.Type_ ->
                    AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom substCoVars : Core.TCvSubst ->
                    list Core.CoVar -> list AxiomatizedTypes.Coercion.

Axiom substCoVarBndr : Core.TCvSubst ->
                       Core.CoVar -> (Core.TCvSubst * Core.CoVar)%type.

Axiom substCoVar : Core.TCvSubst -> Core.CoVar -> AxiomatizedTypes.Coercion.

Axiom substCoUnchecked : Core.TCvSubst ->
                         AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom substCo : forall `{Util.HasDebugCallStack},
                Core.TCvSubst -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom splitForAllTys' : AxiomatizedTypes.Type_ ->
                        (list Core.TyVar * list Core.ArgFlag * AxiomatizedTypes.Type_)%type.

Axiom setTvSubstEnv : Core.TCvSubst -> Core.TvSubstEnv -> Core.TCvSubst.

Axiom setCvSubstEnv : Core.TCvSubst -> Core.CvSubstEnv -> Core.TCvSubst.

Axiom provSize : UnivCoProvenance -> nat.

Axiom pprUserForAll : list Core.TyVarBinder -> GHC.Base.String.

Axiom pprTypeApp : Core.TyCon -> list AxiomatizedTypes.Type_ -> GHC.Base.String.

Axiom pprType : AxiomatizedTypes.Type_ -> GHC.Base.String.

Axiom pprTyVars : list Core.TyVar -> GHC.Base.String.

Axiom pprTyVar : Core.TyVar -> GHC.Base.String.

Axiom pprTyThingCategory : AxiomatizedTypes.TyThing -> GHC.Base.String.

Axiom pprTyLit : TyLit -> GHC.Base.String.

Axiom pprTvBndrs : list Core.TyVarBinder -> GHC.Base.String.

Axiom pprTvBndr : Core.TyVarBinder -> GHC.Base.String.

Axiom pprThetaArrowTy : AxiomatizedTypes.ThetaType -> GHC.Base.String.

Axiom pprTheta : AxiomatizedTypes.ThetaType -> GHC.Base.String.

Axiom pprSigmaType : AxiomatizedTypes.Type_ -> GHC.Base.String.

Axiom pprShortTyThing : AxiomatizedTypes.TyThing -> GHC.Base.String.

Axiom pprPrecType : BasicTypes.TyPrec ->
                    AxiomatizedTypes.Type_ -> GHC.Base.String.

Axiom pprParendType : AxiomatizedTypes.Type_ -> GHC.Base.String.

Axiom pprParendTheta : AxiomatizedTypes.ThetaType -> GHC.Base.String.

Axiom pprParendKind : AxiomatizedTypes.Kind -> GHC.Base.String.

Axiom pprParendCo : AxiomatizedTypes.Coercion -> GHC.Base.String.

Axiom pprKind : AxiomatizedTypes.Kind -> GHC.Base.String.

Axiom pprForAll : list Core.TyVarBinder -> GHC.Base.String.

Axiom pprDataCons : Core.TyCon -> GHC.Base.String.

Axiom pprDataConWithArgs : Core.DataCon -> GHC.Base.String.

Axiom pprCo : AxiomatizedTypes.Coercion -> GHC.Base.String.

Axiom pprClassPred : Core.Class ->
                     list AxiomatizedTypes.Type_ -> GHC.Base.String.

Axiom ppSuggestExplicitKinds : GHC.Base.String.

Axiom notElemTCvSubst : Core.Var -> Core.TCvSubst -> bool.

Axiom noFreeVarsOfType : AxiomatizedTypes.Type_ -> bool.

Axiom noFreeVarsOfProv : UnivCoProvenance -> bool.

Axiom noFreeVarsOfCo : AxiomatizedTypes.Coercion -> bool.

Axiom mkTyVarTys : list Core.TyVar -> list AxiomatizedTypes.Type_.

Axiom mkTyConTy : Core.TyCon -> AxiomatizedTypes.Type_.

Axiom mkTyCoInScopeSet : list AxiomatizedTypes.Type_ ->
                         list AxiomatizedTypes.Coercion -> Core.InScopeSet.

Axiom mkTvSubstPrs : list (Core.TyVar * AxiomatizedTypes.Type_)%type ->
                     Core.TCvSubst.

Axiom mkTvSubst : Core.InScopeSet -> Core.TvSubstEnv -> Core.TCvSubst.

Axiom mkTCvSubst : Core.InScopeSet ->
                   (Core.TvSubstEnv * Core.CvSubstEnv)%type -> Core.TCvSubst.

Axiom mkPiTys : list AxiomatizedTypes.TyBinder ->
                AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkPiTy : AxiomatizedTypes.TyBinder ->
               AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkFunTys : list AxiomatizedTypes.Type_ ->
                 AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkFunTy : AxiomatizedTypes.Type_ ->
                AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkForAllTys' : list (Core.TyVar * Core.ArgFlag)%type ->
                     AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkForAllTys : list Core.TyVarBinder ->
                    AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkForAllTy : Core.TyVar ->
                   Core.ArgFlag -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkEmptyTCvSubst : Core.InScopeSet -> Core.TCvSubst.

Axiom lookupTyVar : Core.TCvSubst ->
                    Core.TyVar -> option AxiomatizedTypes.Type_.

Axiom lookupCoVar : Core.TCvSubst ->
                    Core.Var -> option AxiomatizedTypes.Coercion.

Axiom is_TYPE : (AxiomatizedTypes.Type_ -> bool) ->
                AxiomatizedTypes.Kind -> bool.

Axiom isVisibleBinder : AxiomatizedTypes.TyBinder -> bool.

Axiom isValidTCvSubst : Core.TCvSubst -> bool.

Axiom isUnliftedTypeKind : AxiomatizedTypes.Kind -> bool.

Axiom isRuntimeRepVar : Core.TyVar -> bool.

Axiom isRuntimeRepTy : AxiomatizedTypes.Type_ -> bool.

Axiom isLiftedTypeKind : AxiomatizedTypes.Kind -> bool.

Axiom isInvisibleBinder : AxiomatizedTypes.TyBinder -> bool.

Axiom isInScope : Core.Var -> Core.TCvSubst -> bool.

Axiom isEmptyTCvSubst : Core.TCvSubst -> bool.

Axiom isCoercionType : AxiomatizedTypes.Type_ -> bool.

Axiom injectiveVarsOfType : AxiomatizedTypes.Type_ -> FV.FV.

Axiom injectiveVarsOfBinder : Core.TyConBinder -> FV.FV.

Axiom getTvSubstEnv : Core.TCvSubst -> Core.TvSubstEnv.

Axiom getTCvSubstRangeFVs : Core.TCvSubst -> Core.VarSet.

Axiom getTCvInScope : Core.TCvSubst -> Core.InScopeSet.

Axiom getHelpfulOccName : Core.TyCoVar -> OccName.OccName.

Axiom getCvSubstEnv : Core.TCvSubst -> Core.CvSubstEnv.

Axiom extendTvSubstWithClone : Core.TCvSubst ->
                               Core.TyVar -> Core.TyVar -> Core.TCvSubst.

Axiom extendTvSubstList : Core.TCvSubst ->
                          list Core.Var -> list AxiomatizedTypes.Type_ -> Core.TCvSubst.

Axiom extendTvSubstBinderAndInScope : Core.TCvSubst ->
                                      AxiomatizedTypes.TyBinder -> AxiomatizedTypes.Type_ -> Core.TCvSubst.

Axiom extendTvSubstAndInScope : Core.TCvSubst ->
                                Core.TyVar -> AxiomatizedTypes.Type_ -> Core.TCvSubst.

Axiom extendTvSubst : Core.TCvSubst ->
                      Core.TyVar -> AxiomatizedTypes.Type_ -> Core.TCvSubst.

Axiom extendTCvSubst : Core.TCvSubst ->
                       Core.TyCoVar -> AxiomatizedTypes.Type_ -> Core.TCvSubst.

Axiom extendTCvInScopeSet : Core.TCvSubst -> Core.VarSet -> Core.TCvSubst.

Axiom extendTCvInScopeList : Core.TCvSubst -> list Core.Var -> Core.TCvSubst.

Axiom extendTCvInScope : Core.TCvSubst -> Core.Var -> Core.TCvSubst.

Axiom extendCvSubstWithClone : Core.TCvSubst ->
                               Core.CoVar -> Core.CoVar -> Core.TCvSubst.

Axiom extendCvSubst : Core.TCvSubst ->
                      Core.CoVar -> AxiomatizedTypes.Coercion -> Core.TCvSubst.

Axiom emptyTvSubstEnv : Core.TvSubstEnv.

Axiom emptyTCvSubst : Core.TCvSubst.

Axiom emptyCvSubstEnv : Core.CvSubstEnv.

Axiom delBinderVar : Core.VarSet -> Core.TyVarBinder -> Core.VarSet.

Axiom debug_ppr_ty : BasicTypes.TyPrec ->
                     AxiomatizedTypes.Type_ -> GHC.Base.String.

Axiom debugPprType : AxiomatizedTypes.Type_ -> GHC.Base.String.

Axiom composeTCvSubstEnv : Core.InScopeSet ->
                           (Core.TvSubstEnv * Core.CvSubstEnv)%type ->
                           (Core.TvSubstEnv * Core.CvSubstEnv)%type ->
                           (Core.TvSubstEnv * Core.CvSubstEnv)%type.

Axiom composeTCvSubst : Core.TCvSubst -> Core.TCvSubst -> Core.TCvSubst.

Axiom coercionSize : AxiomatizedTypes.Coercion -> nat.

Axiom coVarsOfTypes : list AxiomatizedTypes.Type_ -> Core.TyCoVarSet.

Axiom coVarsOfType : AxiomatizedTypes.Type_ -> Core.CoVarSet.

Axiom coVarsOfProv : UnivCoProvenance -> Core.CoVarSet.

Axiom coVarsOfCos : list AxiomatizedTypes.Coercion -> Core.CoVarSet.

Axiom coVarsOfCoVar : Core.CoVar -> Core.CoVarSet.

Axiom coVarsOfCo : AxiomatizedTypes.Coercion -> Core.CoVarSet.

Axiom coHoleCoVar : CoercionHole -> Core.CoVar.

Axiom closeOverKindsList : list Core.TyVar -> list Core.TyVar.

Axiom closeOverKindsFV : list Core.TyVar -> FV.FV.

Axiom closeOverKindsDSet : Core.DTyVarSet -> Core.DTyVarSet.

Axiom closeOverKinds : Core.TyVarSet -> Core.TyVarSet.

Axiom cloneTyVarBndrs : Core.TCvSubst ->
                        list Core.TyVar ->
                        UniqSupply.UniqSupply -> (Core.TCvSubst * list Core.TyVar)%type.

Axiom cloneTyVarBndr : Core.TCvSubst ->
                       Core.TyVar -> Unique.Unique -> (Core.TCvSubst * Core.TyVar)%type.

Axiom checkValidSubst : forall {a},
                        forall `{Util.HasDebugCallStack},
                        Core.TCvSubst ->
                        list AxiomatizedTypes.Type_ -> list AxiomatizedTypes.Coercion -> a -> a.

Instance Eq___TyLit : GHC.Base.Eq_ TyLit := {}.
Proof.
Admitted.

Instance Ord__TyLit : GHC.Base.Ord TyLit := {}.
Proof.
Admitted.

(* Skipping all instances of class `Data.Data.Data', including
   `TyCoRep.Data__TyLit' *)

(* Skipping all instances of class `Data.Data.Data', including
   `TyCoRep.Data__Coercion' *)

(* Skipping all instances of class `Data.Data.Data', including
   `TyCoRep.Data__UnivCoProvenance' *)

(* Skipping all instances of class `Data.Data.Data', including
   `TyCoRep.Data__Type_' *)

(* Skipping all instances of class `Data.Data.Data', including
   `TyCoRep.Data__TyBinder' *)

Instance NamedThing__TyThing : Name.NamedThing AxiomatizedTypes.TyThing := {}.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `TyCoRep.Outputable__TyThing' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `TyCoRep.Outputable__TyLit' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `TyCoRep.Outputable__Coercion' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `TyCoRep.Outputable__Type_' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `TyCoRep.Outputable__CoercionHole' *)

(* Skipping all instances of class `Data.Data.Data', including
   `TyCoRep.Data__CoercionHole' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `TyCoRep.Outputable__UnivCoProvenance' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `TyCoRep.Outputable__TyBinder' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `TyCoRep.Outputable__TCvSubst' *)

(* External variables:
     Type bool list nat op_zt__ option AxiomatizedTypes.Coercion
     AxiomatizedTypes.Kind AxiomatizedTypes.ThetaType AxiomatizedTypes.TyBinder
     AxiomatizedTypes.TyThing AxiomatizedTypes.Type_ BasicTypes.TyPrec Core.ArgFlag
     Core.Class Core.CoVar Core.CoVarEnv Core.CoVarSet Core.CvSubstEnv
     Core.DTyCoVarSet Core.DTyVarSet Core.DataCon Core.InScopeSet Core.TCvSubst
     Core.TidyEnv Core.TvSubstEnv Core.TyCoVar Core.TyCoVarSet Core.TyCon
     Core.TyConBinder Core.TyVar Core.TyVarBinder Core.TyVarBndr Core.TyVarEnv
     Core.TyVarSet Core.Var Core.VarSet FV.FV FastString.FastString GHC.Base.Eq_
     GHC.Base.Ord GHC.Base.String GHC.Err.Build_Default GHC.Err.Default
     GHC.Num.Integer Name.NamedThing OccName.OccName UniqSupply.UniqSupply
     Unique.Unique Util.HasDebugCallStack
*)
