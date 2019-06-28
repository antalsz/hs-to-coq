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
Require CoAxiom.
Require Core.
Require GHC.Base.
Require Name.
Require Pair.
Require TyCoRep.
Require Unique.
Require Util.

(* Converted type declarations: *)

Inductive NormaliseStepResult ev : Type
  := | NS_Done : NormaliseStepResult ev
  |  NS_Abort : NormaliseStepResult ev
  |  NS_Step
   : Core.RecTcChecker -> AxiomatizedTypes.Type_ -> ev -> NormaliseStepResult ev.

Definition NormaliseStepper ev :=
  (Core.RecTcChecker ->
   Core.TyCon -> list AxiomatizedTypes.Type_ -> NormaliseStepResult ev)%type.

Definition LiftCoEnv :=
  (Core.VarEnv AxiomatizedTypes.Coercion)%type.

Inductive LiftingContext : Type
  := | LC : Core.TCvSubst -> LiftCoEnv -> LiftingContext.

Arguments NS_Done {_}.

Arguments NS_Abort {_}.

Arguments NS_Step {_} _ _ _.

(* Converted value declarations: *)

Axiom zapLiftingContext : LiftingContext -> LiftingContext.

Axiom unwrapNewTypeStepper : NormaliseStepper AxiomatizedTypes.Coercion.

Axiom ty_co_subst : LiftingContext ->
                    AxiomatizedTypes.Role -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom tyConRolesX : AxiomatizedTypes.Role ->
                    Core.TyCon -> list AxiomatizedTypes.Role.

Axiom tyConRolesRepresentational : Core.TyCon -> list AxiomatizedTypes.Role.

Axiom topNormaliseTypeX : forall {ev},
                          NormaliseStepper ev ->
                          (ev -> ev -> ev) ->
                          AxiomatizedTypes.Type_ -> option (ev * AxiomatizedTypes.Type_)%type.

Axiom topNormaliseNewType_maybe : AxiomatizedTypes.Type_ ->
                                  option (AxiomatizedTypes.Coercion * AxiomatizedTypes.Type_)%type.

Axiom toPhantomCo : AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom swapLiftCoEnv : LiftCoEnv -> LiftCoEnv.

Axiom substRightCo : LiftingContext ->
                     AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom substLeftCo : LiftingContext ->
                    AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom substForAllCoBndrCallbackLC : bool ->
                                    (AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion) ->
                                    LiftingContext ->
                                    Core.TyVar ->
                                    AxiomatizedTypes.Coercion ->
                                    (LiftingContext * Core.TyVar * AxiomatizedTypes.Coercion)%type.

Axiom splitTyConAppCo_maybe : AxiomatizedTypes.Coercion ->
                              option (Core.TyCon * list AxiomatizedTypes.Coercion)%type.

Axiom splitFunCo_maybe : AxiomatizedTypes.Coercion ->
                         option (AxiomatizedTypes.Coercion * AxiomatizedTypes.Coercion)%type.

Axiom splitForAllCo_maybe : AxiomatizedTypes.Coercion ->
                            option (Core.TyVar * AxiomatizedTypes.Coercion *
                                    AxiomatizedTypes.Coercion)%type.

Axiom splitAppCo_maybe : AxiomatizedTypes.Coercion ->
                         option (AxiomatizedTypes.Coercion * AxiomatizedTypes.Coercion)%type.

Axiom setNominalRole_maybe : AxiomatizedTypes.Coercion ->
                             option AxiomatizedTypes.Coercion.

Axiom setCoVarUnique : Core.CoVar -> Unique.Unique -> Core.CoVar.

Axiom setCoVarName : Core.CoVar -> Name.Name -> Core.CoVar.

Axiom seqProv : TyCoRep.UnivCoProvenance -> unit.

Axiom seqCos : list AxiomatizedTypes.Coercion -> unit.

Axiom seqCo : AxiomatizedTypes.Coercion -> unit.

Axiom promoteCoercion : AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom ppr_co_ax_branch : forall {br},
                         (Core.TyCon -> AxiomatizedTypes.Type_ -> GHC.Base.String) ->
                         AxiomatizedTypes.CoAxiom br -> CoAxiom.CoAxBranch -> GHC.Base.String.

Axiom pprCoAxiom : forall {br}, AxiomatizedTypes.CoAxiom br -> GHC.Base.String.

Axiom pprCoAxBranchHdr : forall {br},
                         AxiomatizedTypes.CoAxiom br -> CoAxiom.BranchIndex -> GHC.Base.String.

Axiom pprCoAxBranch : forall {br},
                      AxiomatizedTypes.CoAxiom br -> CoAxiom.CoAxBranch -> GHC.Base.String.

Axiom nthRole : AxiomatizedTypes.Role ->
                Core.TyCon -> nat -> AxiomatizedTypes.Role.

Axiom mkUnsafeCo : AxiomatizedTypes.Role ->
                   AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom mkUnivCo : TyCoRep.UnivCoProvenance ->
                 AxiomatizedTypes.Role ->
                 AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom mkUnbranchedAxInstRHS : AxiomatizedTypes.CoAxiom
                              AxiomatizedTypes.Unbranched ->
                              list AxiomatizedTypes.Type_ ->
                              list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Type_.

Axiom mkUnbranchedAxInstLHS : AxiomatizedTypes.CoAxiom
                              AxiomatizedTypes.Unbranched ->
                              list AxiomatizedTypes.Type_ ->
                              list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Type_.

Axiom mkUnbranchedAxInstCo : AxiomatizedTypes.Role ->
                             AxiomatizedTypes.CoAxiom AxiomatizedTypes.Unbranched ->
                             list AxiomatizedTypes.Type_ ->
                             list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkTyConAppCo : forall `{Util.HasDebugCallStack},
                     AxiomatizedTypes.Role ->
                     Core.TyCon -> list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkTransCo : AxiomatizedTypes.Coercion ->
                  AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkTransAppCo : AxiomatizedTypes.Role ->
                     AxiomatizedTypes.Coercion ->
                     AxiomatizedTypes.Type_ ->
                     AxiomatizedTypes.Type_ ->
                     AxiomatizedTypes.Role ->
                     AxiomatizedTypes.Coercion ->
                     AxiomatizedTypes.Type_ ->
                     AxiomatizedTypes.Type_ -> AxiomatizedTypes.Role -> AxiomatizedTypes.Coercion.

Axiom mkSymCo : AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkSubstLiftingContext : Core.TCvSubst -> LiftingContext.

Axiom mkSubCo : AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkRuntimeRepCo : forall `{Util.HasDebugCallStack},
                       AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkRepReflCo : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom mkReflCo : AxiomatizedTypes.Role ->
                 AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom mkProofIrrelCo : AxiomatizedTypes.Role ->
                       AxiomatizedTypes.Coercion ->
                       AxiomatizedTypes.Coercion ->
                       AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkPiCos : AxiomatizedTypes.Role ->
                list Core.Var -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkPiCo : AxiomatizedTypes.Role ->
               Core.Var -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkPhantomCo : AxiomatizedTypes.Coercion ->
                    AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom mkNthCoRole : AxiomatizedTypes.Role ->
                    nat -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkNthCo : nat -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkNomReflCo : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom mkLiftingContext : list (Core.TyCoVar * AxiomatizedTypes.Coercion)%type ->
                         LiftingContext.

Axiom mkLRCo : BasicTypes.LeftOrRight ->
               AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkKindCo : AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkInstCo : AxiomatizedTypes.Coercion ->
                 AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkHomoPhantomCo : AxiomatizedTypes.Type_ ->
                        AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom mkHomoForAllCos_NoRefl : list Core.TyVar ->
                               AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkHomoForAllCos : list Core.TyVar ->
                        AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkHoleCo : TyCoRep.CoercionHole -> AxiomatizedTypes.Coercion.

Axiom mkHeteroCoercionType : AxiomatizedTypes.Role ->
                             AxiomatizedTypes.Kind ->
                             AxiomatizedTypes.Kind ->
                             AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkFunCos : AxiomatizedTypes.Role ->
                 list AxiomatizedTypes.Coercion ->
                 AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkFunCo : AxiomatizedTypes.Role ->
                AxiomatizedTypes.Coercion ->
                AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkForAllCos : list (Core.TyVar * AxiomatizedTypes.Coercion)%type ->
                    AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkForAllCo : Core.TyVar ->
                   AxiomatizedTypes.Coercion ->
                   AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkCoherenceRightCo : AxiomatizedTypes.Coercion ->
                           AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkCoherenceLeftCo : AxiomatizedTypes.Coercion ->
                          AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkCoherenceCo : AxiomatizedTypes.Coercion ->
                      AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkCoercionType : AxiomatizedTypes.Role ->
                       AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkCoVarCos : list Core.CoVar -> list AxiomatizedTypes.Coercion.

Axiom mkCoVarCo : Core.CoVar -> AxiomatizedTypes.Coercion.

Axiom mkCoCast : AxiomatizedTypes.Coercion ->
                 AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkAxiomRuleCo : CoAxiom.CoAxiomRule ->
                      list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkAxiomInstCo : AxiomatizedTypes.CoAxiom AxiomatizedTypes.Branched ->
                      CoAxiom.BranchIndex ->
                      list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkAxInstRHS : forall {br},
                    AxiomatizedTypes.CoAxiom br ->
                    CoAxiom.BranchIndex ->
                    list AxiomatizedTypes.Type_ ->
                    list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Type_.

Axiom mkAxInstLHS : forall {br},
                    AxiomatizedTypes.CoAxiom br ->
                    CoAxiom.BranchIndex ->
                    list AxiomatizedTypes.Type_ ->
                    list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Type_.

Axiom mkAxInstCo : forall {br},
                   AxiomatizedTypes.Role ->
                   AxiomatizedTypes.CoAxiom br ->
                   CoAxiom.BranchIndex ->
                   list AxiomatizedTypes.Type_ ->
                   list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkAppCos : AxiomatizedTypes.Coercion ->
                 list AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mkAppCo : AxiomatizedTypes.Coercion ->
                AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom mapStepResult : forall {ev1} {ev2},
                      (ev1 -> ev2) -> NormaliseStepResult ev1 -> NormaliseStepResult ev2.

Axiom ltRole : AxiomatizedTypes.Role -> AxiomatizedTypes.Role -> bool.

Axiom liftEnvSubstRight : Core.TCvSubst -> LiftCoEnv -> Core.TCvSubst.

Axiom liftEnvSubstLeft : Core.TCvSubst -> LiftCoEnv -> Core.TCvSubst.

Axiom liftEnvSubst : (forall {a}, Pair.Pair a -> a) ->
                     Core.TCvSubst -> LiftCoEnv -> Core.TCvSubst.

Axiom liftCoSubstWithEx : AxiomatizedTypes.Role ->
                          list Core.TyVar ->
                          list AxiomatizedTypes.Coercion ->
                          list Core.TyVar ->
                          list AxiomatizedTypes.Type_ ->
                          ((AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion) *
                           list AxiomatizedTypes.Type_)%type.

Axiom liftCoSubstWith : AxiomatizedTypes.Role ->
                        list Core.TyCoVar ->
                        list AxiomatizedTypes.Coercion ->
                        AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom liftCoSubstVarBndrCallback : forall {a},
                                   (LiftingContext ->
                                    AxiomatizedTypes.Type_ -> (AxiomatizedTypes.Coercion * a)%type) ->
                                   LiftingContext ->
                                   Core.TyVar ->
                                   (LiftingContext * Core.TyVar * AxiomatizedTypes.Coercion * a)%type.

Axiom liftCoSubstVarBndr : LiftingContext ->
                           Core.TyVar -> (LiftingContext * Core.TyVar * AxiomatizedTypes.Coercion)%type.

Axiom liftCoSubstTyVar : LiftingContext ->
                         AxiomatizedTypes.Role -> Core.TyVar -> option AxiomatizedTypes.Coercion.

Axiom liftCoSubst : forall `{Util.HasDebugCallStack},
                    AxiomatizedTypes.Role ->
                    LiftingContext -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Coercion.

Axiom lcTCvSubst : LiftingContext -> Core.TCvSubst.

Axiom lcSubstRight : LiftingContext -> Core.TCvSubst.

Axiom lcSubstLeft : LiftingContext -> Core.TCvSubst.

Axiom lcInScopeSet : LiftingContext -> Core.InScopeSet.

Axiom isReflexiveCo_maybe : AxiomatizedTypes.Coercion ->
                            option (AxiomatizedTypes.Type_ * AxiomatizedTypes.Role)%type.

Axiom isReflexiveCo : AxiomatizedTypes.Coercion -> bool.

Axiom isReflCo_maybe : AxiomatizedTypes.Coercion ->
                       option (AxiomatizedTypes.Type_ * AxiomatizedTypes.Role)%type.

Axiom isReflCoVar_maybe : Core.CoVar -> option AxiomatizedTypes.Coercion.

Axiom isReflCo : AxiomatizedTypes.Coercion -> bool.

Axiom isMappedByLC : Core.TyCoVar -> LiftingContext -> bool.

Axiom isCoVar_maybe : AxiomatizedTypes.Coercion -> option Core.CoVar.

Axiom instNewTyCon_maybe : Core.TyCon ->
                           list AxiomatizedTypes.Type_ ->
                           option (AxiomatizedTypes.Type_ * AxiomatizedTypes.Coercion)%type.

Axiom instCoercions : AxiomatizedTypes.Coercion ->
                      list AxiomatizedTypes.Coercion -> option AxiomatizedTypes.Coercion.

Axiom instCoercion : Pair.Pair AxiomatizedTypes.Type_ ->
                     AxiomatizedTypes.Coercion ->
                     AxiomatizedTypes.Coercion -> option AxiomatizedTypes.Coercion.

Axiom getCoVar_maybe : AxiomatizedTypes.Coercion -> option Core.CoVar.

Axiom extendLiftingContextEx : LiftingContext ->
                               list (Core.TyVar * AxiomatizedTypes.Type_)%type -> LiftingContext.

Axiom extendLiftingContext : LiftingContext ->
                             Core.TyVar -> AxiomatizedTypes.Coercion -> LiftingContext.

Axiom eqCoercionX : Core.RnEnv2 ->
                    AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion -> bool.

Axiom eqCoercion : AxiomatizedTypes.Coercion ->
                   AxiomatizedTypes.Coercion -> bool.

Axiom emptyLiftingContext : Core.InScopeSet -> LiftingContext.

Axiom downgradeRole_maybe : AxiomatizedTypes.Role ->
                            AxiomatizedTypes.Role ->
                            AxiomatizedTypes.Coercion -> option AxiomatizedTypes.Coercion.

Axiom downgradeRole : AxiomatizedTypes.Role ->
                      AxiomatizedTypes.Role -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom decomposeFunCo : AxiomatizedTypes.Coercion ->
                       (AxiomatizedTypes.Coercion * AxiomatizedTypes.Coercion)%type.

Axiom decomposeCo : BasicTypes.Arity ->
                    AxiomatizedTypes.Coercion -> list AxiomatizedTypes.Coercion.

Axiom composeSteppers : forall {ev},
                        NormaliseStepper ev -> NormaliseStepper ev -> NormaliseStepper ev.

Axiom coercionType : AxiomatizedTypes.Coercion -> AxiomatizedTypes.Type_.

Axiom coercionRole : AxiomatizedTypes.Coercion -> AxiomatizedTypes.Role.

Axiom coercionKinds : list AxiomatizedTypes.Coercion ->
                      Pair.Pair (list AxiomatizedTypes.Type_).

Axiom coercionKindRole : AxiomatizedTypes.Coercion ->
                         (Pair.Pair AxiomatizedTypes.Type_ * AxiomatizedTypes.Role)%type.

Axiom coercionKind : AxiomatizedTypes.Coercion ->
                     Pair.Pair AxiomatizedTypes.Type_.

Axiom coVarTypes : Core.CoVar -> Pair.Pair AxiomatizedTypes.Type_.

Axiom coVarRole : Core.CoVar -> AxiomatizedTypes.Role.

Axiom coVarName : Core.CoVar -> Name.Name.

Axiom coVarKindsTypesRole : Core.CoVar ->
                            (AxiomatizedTypes.Kind * AxiomatizedTypes.Kind * AxiomatizedTypes.Type_ *
                             AxiomatizedTypes.Type_ *
                             AxiomatizedTypes.Role)%type.

Axiom coVarKind : Core.CoVar -> AxiomatizedTypes.Type_.

Axiom castCoercionKind : AxiomatizedTypes.Coercion ->
                         AxiomatizedTypes.Coercion ->
                         AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion.

Axiom applyRoles : Core.TyCon ->
                   list AxiomatizedTypes.Coercion -> list AxiomatizedTypes.Coercion.

(* Skipping all instances of class `Outputable.Outputable', including
   `Coercion.Outputable__LiftingContext' *)

(* External variables:
     bool list nat op_zt__ option unit AxiomatizedTypes.Branched
     AxiomatizedTypes.CoAxiom AxiomatizedTypes.Coercion AxiomatizedTypes.Kind
     AxiomatizedTypes.Role AxiomatizedTypes.Type_ AxiomatizedTypes.Unbranched
     BasicTypes.Arity BasicTypes.LeftOrRight CoAxiom.BranchIndex CoAxiom.CoAxBranch
     CoAxiom.CoAxiomRule Core.CoVar Core.InScopeSet Core.RecTcChecker Core.RnEnv2
     Core.TCvSubst Core.TyCoVar Core.TyCon Core.TyVar Core.Var Core.VarEnv
     GHC.Base.String Name.Name Pair.Pair TyCoRep.CoercionHole
     TyCoRep.UnivCoProvenance Unique.Unique Util.HasDebugCallStack
*)
