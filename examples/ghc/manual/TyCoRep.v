(**** This manual file is the grab bag. Has all of the stuff from the others ****)

(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Num.
Require GHC.Base.
Require Var.
Require ConLike.
Require CoAxiom.
Require FV.
Require Pair.
Require BasicTypes.

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require Data.OldList.
Require Data.Traversable.
Require Data.Tuple.
Require DataCon.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Require Name.
Require OccName.
Require Pair.
Require GHC.Err.
Require UniqFM.
Require UniqSupply.
Require Unique.
Require Util.
Require VarEnv.
Require VarSet.
Require PrelNames.
Require TyCon.
Require Digraph.

Import GHC.Base.Notations.
(* Import GHC.Prim.Notations. *)

Require Import Core.
Require TyCon.

Definition CvSubstEnv :=
  (VarEnv.CoVarEnv Coercion)%type.

Definition TvSubstEnv :=
  (VarEnv.TyVarEnv Type_)%type.

Inductive TCvSubst : Type :=
  Mk_TCvSubst : VarEnv.InScopeSet -> TvSubstEnv -> CvSubstEnv -> TCvSubst.

Definition emptyTvSubstEnv : TvSubstEnv :=
  VarEnv.emptyVarEnv.

Definition emptyCvSubstEnv : CvSubstEnv :=
  VarEnv.emptyVarEnv.

Definition mkEmptyTCvSubst : VarEnv.InScopeSet -> TCvSubst :=
  fun is_ => Mk_TCvSubst is_ emptyTvSubstEnv emptyCvSubstEnv.



Parameter chCoercion : CoercionHole -> Coercion.
Parameter chUnique  : CoercionHole -> Unique.Unique.

(* Coercion *)

Parameter coercionKind : Coercion -> Pair.Pair Type_.

Parameter coVarKindsTypesRole :
  CoVar -> (Kind * Kind * Type_ * Type_ * Role)%type.
Parameter mkCoercionType :  Role -> Type_ -> Type_ -> Type_.
Parameter mkSymCo : Coercion -> Coercion.
Parameter mkTransCo : Coercion -> Coercion -> Coercion.
Parameter mkCoVarCo : CoVar -> Coercion.
Parameter isReflCo  : Coercion -> bool.
Parameter mkTyConAppCo :  Role -> TyCon -> list
                          Coercion -> Coercion.
Parameter mkAppCo : Coercion -> Coercion -> Coercion.
Parameter mkForAllCo : forall {A : Type}, A.
Parameter mkAxiomInstCo : forall {A : Type}, A.
Parameter mkUnivCo : forall {A : Type}, A.
Parameter mkNthCo : forall {A : Type}, A.
Parameter mkLRCo : forall {A : Type}, A.
Parameter mkInstCo : forall {br}, Role -> CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Coercion .
Parameter Coercion_mkInstCo : Coercion -> Coercion -> Coercion.
Parameter mkKindKo : forall {A : Type}, A.
Parameter mkCoherenceCo :  forall {A : Type}, A.
Parameter mkSubCo : forall {A : Type}, A.
Parameter mkReflCo : forall {A:Type}, A.
Parameter mkKindCo : forall {A}, A.

(* From "Type" module *)
Definition Type_isCoercionTy (t : Type_) : bool :=
  match t with
  | CoercionTy _ => true | _ => false end.
Parameter Type_isCoercionTy_maybe : forall {A}, A.
Definition Type_isPredTy : Type_ -> bool. Admitted.
Axiom piResultTys : forall {A : Type}, A.
Axiom piResultTy : forall {A : Type}, A.
Parameter eqType : Core.Type_ -> Core.Type_ -> bool.

Definition Type_mkTyConApp : Core.TyCon -> list Core.Type_ -> Core.Type_ :=
  fun tycon tys =>
    let j_0__ := Core.TyConApp tycon tys in
    if TyCon.isFunTyCon tycon : bool
    then match tys with
           | cons ty1 (cons ty2 nil) => Core.ForAllTy (Core.Anon ty1) ty2
           | _ => j_0__
         end
    else j_0__.

Definition Type_mkAppTys : Core.Type_ -> list Core.Type_ -> Core.Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | ty1 , nil => ty1
      | Core.TyConApp tc tys1 , tys2 => Type_mkTyConApp tc (Coq.Init.Datatypes.app tys1
                                                                              tys2)
      | ty1 , tys2 => Data.Foldable.foldl Core.AppTy ty1 tys2
    end.

Definition Type_mkAppTy : Core.Type_ -> Core.Type_ -> Core.Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Core.TyConApp tc tys , ty2 => Type_mkTyConApp tc (Coq.Init.Datatypes.app tys (cons
                                                                            ty2 nil))
      | ty1 , ty2 => Core.AppTy ty1 ty2
    end.

Parameter Type_typeKind : Core.Type_ -> Kind.
(*
Definition typeLiteralKind : Core.TyLit -> Kind :=
  fun l =>
    match l with
      | NumTyLit _ => TysWiredIn.typeNatKind
      | StrTyLit _ => TysWiredIn.typeSymbolKind
    end.


Definition typeKind : Core.Type_ -> Kind :=
  fix typeKind arg_0__
        := match arg_0__ with
             | Core.TyConApp tc tys => piResultTys (Core.tyConKind tc) tys
             | Core.AppTy fun_ arg => piResultTy (typeKind fun_) arg
             | Core.LitTy l => typeLiteralKind l
             | Core.ForAllTy (Core.Anon _) _ => TysWiredIn.liftedTypeKind
             | Core.ForAllTy _ ty => typeKind ty
             | Core.TyVarTy tyvar => Core.tyVarKind tyvar
             | Core.CastTy _ty co => pSnd GHC.Base.$ Coercion_coercionKind co
             | Core.CoercionTy co => coercionType co
           end.
*)


(*--- end from Type *)

Instance DefaultPair {a:Type}{b:Type}`{GHC.Err.Default a}`{GHC.Err.Default b} : GHC.Err.Default (a * b)%type.
Admitted.

Instance Uniq_TyCon : Unique.Uniquable TyCon.
Admitted.

(* Converted imports: *)

(* Midamble *)

Definition Eqn := (Pair.Pair Type_)%type.


(* Converted value declarations: *)

(* Translating `instance Binary.Binary TyCoRep.VisibilityFlag' failed: OOPS!
   Cannot find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary TyCoRep.LeftOrRight' failed: OOPS! Cannot
   find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.UnivCoProvenance' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Data.Data.Data TyCoRep.CoercionHole' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.CoercionHole' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.TyThing' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Name.NamedThing TyCoRep.TyThing' failed: OOPS! Cannot
   find information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.TCvSubst' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.Type_' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.TyLit' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.TyBinder' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.VisibilityFlag' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.Coercion' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable TyCoRep.LeftOrRight' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Local Definition Eq___TyPrec_op_zeze__ : TyPrec -> TyPrec -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | TopPrec , TopPrec => true
      | FunPrec , FunPrec => true
      | TyOpPrec , TyOpPrec => true
      | TyConPrec , TyConPrec => true
      | _ , _ => false
    end.

Local Definition Eq___TyPrec_op_zsze__ : TyPrec -> TyPrec -> bool :=
  fun a b => negb (Eq___TyPrec_op_zeze__ a b).

Program Instance Eq___TyPrec : GHC.Base.Eq_ TyPrec := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___TyPrec_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___TyPrec_op_zsze__ |}.


Parameter Ord__TyPrec_compare : TyPrec -> TyPrec -> comparison.

Parameter Ord__TyPrec_op_zg__ : TyPrec -> TyPrec -> bool.

Parameter Ord__TyPrec_op_zgze__ : TyPrec -> TyPrec -> bool.

Parameter Ord__TyPrec_op_zl__ : TyPrec -> TyPrec -> bool.

Parameter Ord__TyPrec_op_zlze__ : TyPrec -> TyPrec -> bool.


Local Definition Ord__TyPrec_min : TyPrec -> TyPrec -> TyPrec :=
  fun x y => if Ord__TyPrec_op_zlze__ x y : bool then x else y.

Local Definition Ord__TyPrec_max : TyPrec -> TyPrec -> TyPrec :=
  fun x y => if Ord__TyPrec_op_zlze__ x y : bool then y else x.

Program Instance Ord__TyPrec : GHC.Base.Ord TyPrec := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__TyPrec_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__TyPrec_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__TyPrec_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__TyPrec_op_zgze__ ;
      GHC.Base.compare__ := Ord__TyPrec_compare ;
      GHC.Base.max__ := Ord__TyPrec_max ;
      GHC.Base.min__ := Ord__TyPrec_min |}.


Local Definition Ord__TyThing_compare : TyThing -> TyThing -> comparison :=
  fun a b =>
    match a with
      | AnId a1 => match b with
                     | AnId b1 => (GHC.Base.compare a1 b1)
                     | _ => Lt
                   end
      | AConLike a1 => match b with
                         | AnId _ => Gt
                         | AConLike b1 => (GHC.Base.compare a1 b1)
                         | _ => Lt
                       end
      | ATyCon a1 => match b with
                       | ACoAxiom _ => Lt
                       | ATyCon b1 => (GHC.Base.compare a1 b1)
                       | _ => Gt
                     end
      | ACoAxiom a1 => match b with
                         | ACoAxiom b1 => (GHC.Base.compare a1 b1)
                         | _ => Gt
                       end
    end.

Local Definition Ord__TyThing_op_zg__ : TyThing -> TyThing -> bool :=
  fun x y => _GHC.Base.==_ (Ord__TyThing_compare x y) Gt.

Local Definition Ord__TyThing_op_zgze__ : TyThing -> TyThing -> bool :=
  fun x y => _GHC.Base./=_ (Ord__TyThing_compare x y) Lt.

Local Definition Ord__TyThing_op_zl__ : TyThing -> TyThing -> bool :=
  fun x y => _GHC.Base.==_ (Ord__TyThing_compare x y) Lt.

Local Definition Ord__TyThing_op_zlze__ : TyThing -> TyThing -> bool :=
  fun x y => _GHC.Base./=_ (Ord__TyThing_compare x y) Gt.

Local Definition Ord__TyThing_max : TyThing -> TyThing -> TyThing :=
  fun x y => if Ord__TyThing_op_zlze__ x y : bool then y else x.

Local Definition Ord__TyThing_min : TyThing -> TyThing -> TyThing :=
  fun x y => if Ord__TyThing_op_zlze__ x y : bool then x else y.

Local Definition Eq___TyThing_op_zeze__ : TyThing -> TyThing -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | AnId a1 , AnId b1 => ((a1 GHC.Base.== b1))
      | AConLike a1 , AConLike b1 => ((a1 GHC.Base.== b1))
      | ATyCon a1 , ATyCon b1 => ((a1 GHC.Base.== b1))
      | ACoAxiom a1 , ACoAxiom b1 => ((a1 GHC.Base.== b1))
      | _ , _ => false
    end.

Local Definition Eq___TyThing_op_zsze__ : TyThing -> TyThing -> bool :=
  fun a b => negb (Eq___TyThing_op_zeze__ a b).

Program Instance Eq___TyThing : GHC.Base.Eq_ TyThing := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___TyThing_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___TyThing_op_zsze__ |}.


Program Instance Ord__TyThing : GHC.Base.Ord TyThing := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__TyThing_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__TyThing_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__TyThing_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__TyThing_op_zgze__ ;
      GHC.Base.compare__ := Ord__TyThing_compare ;
      GHC.Base.max__ := Ord__TyThing_max ;
      GHC.Base.min__ := Ord__TyThing_min |}.


(* Translating `instance Data.Data.Data TyCoRep.TyBinder' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data TyCoRep.Type_' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data TyCoRep.UnivCoProvenance' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data TyCoRep.Coercion' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data TyCoRep.LeftOrRight' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___LeftOrRight_op_zeze__
    : LeftOrRight -> LeftOrRight -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | CLeft , CLeft => true
      | CRight , CRight => true
      | _ , _ => false
    end.

Local Definition Eq___LeftOrRight_op_zsze__
    : LeftOrRight -> LeftOrRight -> bool :=
  fun a b => negb (Eq___LeftOrRight_op_zeze__ a b).

Program Instance Eq___LeftOrRight : GHC.Base.Eq_ LeftOrRight := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___LeftOrRight_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___LeftOrRight_op_zsze__ |}.

(* Translating `instance Data.Data.Data TyCoRep.VisibilityFlag' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___VisibilityFlag_op_zeze__
    : VisibilityFlag -> VisibilityFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Visible , Visible => true
      | Specified , Specified => true
      | Invisible , Invisible => true
      | _ , _ => false
    end.

Local Definition Eq___VisibilityFlag_op_zsze__
    : VisibilityFlag -> VisibilityFlag -> bool :=
  fun a b => negb (Eq___VisibilityFlag_op_zeze__ a b).

Program Instance Eq___VisibilityFlag : GHC.Base.Eq_ VisibilityFlag := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___VisibilityFlag_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___VisibilityFlag_op_zsze__ |}.

(* Translating `instance Data.Data.Data TyCoRep.TyLit' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Ord__TyLit_compare : TyLit -> TyLit -> comparison :=
  fun a b =>
    match a with
      | NumTyLit a1 => match b with
                         | NumTyLit b1 => (GHC.Base.compare a1 b1)
                         | _ => Lt
                       end
      | StrTyLit a1 => match b with
                         | StrTyLit b1 => (GHC.Base.compare a1 b1)
                         | _ => Gt
                       end
    end.

Local Definition Ord__TyLit_op_zg__ : TyLit -> TyLit -> bool :=
  fun a b =>
    match a with
      | NumTyLit a1 => match b with
                         | NumTyLit b1 => (a1 GHC.Base.> b1)
                         | _ => false
                       end
      | StrTyLit a1 => match b with
                         | StrTyLit b1 => (a1 GHC.Base.> b1)
                         | _ => true
                       end
    end.

Local Definition Ord__TyLit_op_zgze__ : TyLit -> TyLit -> bool :=
  fun a b =>
    match a with
      | NumTyLit a1 => match b with
                         | NumTyLit b1 => (a1 GHC.Base.>= b1)
                         | _ => false
                       end
      | StrTyLit a1 => match b with
                         | StrTyLit b1 => (a1 GHC.Base.>= b1)
                         | _ => true
                       end
    end.

Local Definition Ord__TyLit_op_zl__ : TyLit -> TyLit -> bool :=
  fun a b =>
    match a with
      | NumTyLit a1 => match b with
                         | NumTyLit b1 => (a1 GHC.Base.< b1)
                         | _ => true
                       end
      | StrTyLit a1 => match b with
                         | StrTyLit b1 => (a1 GHC.Base.< b1)
                         | _ => false
                       end
    end.

Local Definition Ord__TyLit_op_zlze__ : TyLit -> TyLit -> bool :=
  fun a b =>
    match a with
      | NumTyLit a1 => match b with
                         | NumTyLit b1 => (a1 GHC.Base.<= b1)
                         | _ => true
                       end
      | StrTyLit a1 => match b with
                         | StrTyLit b1 => (a1 GHC.Base.<= b1)
                         | _ => false
                       end
    end.

Local Definition Ord__TyLit_min : TyLit -> TyLit -> TyLit :=
  fun x y => if Ord__TyLit_op_zlze__ x y : bool then x else y.

Local Definition Ord__TyLit_max : TyLit -> TyLit -> TyLit :=
  fun x y => if Ord__TyLit_op_zlze__ x y : bool then y else x.

Local Definition Eq___TyLit_op_zeze__ : TyLit -> TyLit -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | NumTyLit a1 , NumTyLit b1 => ((a1 GHC.Base.== b1))
      | StrTyLit a1 , StrTyLit b1 => ((a1 GHC.Base.== b1))
      | _ , _ => false
    end.

Local Definition Eq___TyLit_op_zsze__ : TyLit -> TyLit -> bool :=
  fun a b => negb (Eq___TyLit_op_zeze__ a b).

Program Instance Eq___TyLit : GHC.Base.Eq_ TyLit := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___TyLit_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___TyLit_op_zsze__ |}.


Program Instance Ord__TyLit : GHC.Base.Ord TyLit := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__TyLit_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__TyLit_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__TyLit_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__TyLit_op_zgze__ ;
      GHC.Base.compare__ := Ord__TyLit_compare ;
      GHC.Base.max__ := Ord__TyLit_max ;
      GHC.Base.min__ := Ord__TyLit_min |}.


Axiom defaultRuntimeRepVars' : forall {A : Type}, A.

(* Translating `defaultRuntimeRepVars'' failed: invalid record upate with
   non-record-field `varType' unsupported *)

Definition binderType : TyBinder -> Type_ :=
  fun arg_0__ => match arg_0__ with | Named v _ => Var.varType v | Anon ty => ty end.

Definition defaultRuntimeRepVars : Type_ -> Type_ :=
  defaultRuntimeRepVars' VarSet.emptyVarSet.

(*
Definition eliminateRuntimeRep
    : (Type_ -> Outputable.SDoc) -> Type_ -> Outputable.SDoc :=
  fun f ty =>
    Outputable.sdocWithDynFlags GHC.Base.$ (fun dflags =>
      if DynFlags.gopt DynFlags.Opt_PrintExplicitRuntimeReps dflags : bool
      then f ty
      else f (defaultRuntimeRepVars ty)).
*)

Definition delBinderVar : VarSet.VarSet -> TyBinder -> VarSet.VarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | vars , Named tv _ => VarSet.delVarSet vars tv
      | vars , Anon _ => vars
    end.

(* SCW: This seems strange to me. Why do we find the coercion variables in the
   KIND of a type variable?
   What is this function used for? What do we need to know about
   these coercion variables?
   TODO: ask Richard.
*)
Parameter coVarsOfType  : Type_ -> VarSet.CoVarSet.
Parameter coVarsOfTypes : list Type_ -> VarSet.TyCoVarSet.
(* SCW: why not VarSet.TyCoVarSet ?? *)
Parameter coVarsOfCo    : Coercion -> VarSet.CoVarSet.
Parameter coVarsOfCos   : list Coercion -> VarSet.CoVarSet.
Parameter coVarsOfProv  : UnivCoProvenance -> VarSet.CoVarSet.

(*
Fixpoint coVarsOfType (arg_0__ : Type_) : VarSet.CoVarSet :=
  match arg_0__ with
  | TyVarTy v => coVarsOfType (tyVarKind v)
  | TyConApp _ tys => coVarsOfTypes tys
  | LitTy _ => VarSet.emptyVarSet
  | AppTy fun_ arg => VarSet.unionVarSet (coVarsOfType fun_) (coVarsOfType arg)
  | ForAllTy bndr ty => VarSet.unionVarSet (delBinderVar (coVarsOfType ty) bndr)
                                          (coVarsOfType (binderType bndr))
  | CastTy ty co => VarSet.unionVarSet (coVarsOfType ty) (coVarsOfCo co)
  | CoercionTy co => coVarsOfCo co
  end
with coVarsOfTypes (tys : list Type_) : VarSet.TyCoVarSet :=
  VarSet.mapUnionVarSet coVarsOfType tys
with coVarsOfCo (arg_0__ : Coercion) : VarSet.CoVarSet :=
        match arg_0__ with
             | Refl _ ty => coVarsOfType ty
             | TyConAppCo _ _ args => coVarsOfCos args
             | AppCo co arg => VarSet.unionVarSet (coVarsOfCo co) (coVarsOfCo arg)
             | ForAllCo tv kind_co co => VarSet.unionVarSet (VarSet.delVarSet (coVarsOfCo co)
                                                                              tv) (coVarsOfCo kind_co)
             | CoVarCo v => VarSet.unionVarSet (VarSet.unitVarSet v) (coVarsOfType (varType
                                                                                   v))
             | AxiomInstCo _ _ args => coVarsOfCos args
             | UnivCo p _ t1 t2 => VarSet.unionVarSet (coVarsOfProv p) (coVarsOfTypes (cons
                                                                                      t1 (cons t2 nil)))
             | SymCo co => coVarsOfCo co
             | TransCo co1 co2 => VarSet.unionVarSet (coVarsOfCo co1) (coVarsOfCo co2)
             | NthCo _ co => coVarsOfCo co
             | LRCo _ co => coVarsOfCo co
             | InstCo co arg => VarSet.unionVarSet (coVarsOfCo co) (coVarsOfCo arg)
             | CoherenceCo c1 c2 => coVarsOfCos (cons c1 (cons c2 nil))
             | KindCo co => coVarsOfCo co
             | SubCo co => coVarsOfCo co
             | AxiomRuleCo _ cs => coVarsOfCos cs
           end
with coVarsOfCos (cos : list Coercion) : VarSet.CoVarSet :=
   VarSet.mapUnionVarSet coVarsOfCo cos
with coVarsOfProv (arg_0__ : UnivCoProvenance) : VarSet.CoVarSet :=
    match arg_0__ with
      | UnsafeCoerceProv => VarSet.emptyVarSet
      | PhantomProv co => coVarsOfCo co
      | ProofIrrelProv co => coVarsOfCo co
      | PluginProv _ => VarSet.emptyVarSet
      | HoleProv _ => VarSet.emptyVarSet
    end.
*)


Definition delBinderVarFV : TyBinder -> FV.FV -> FV.FV :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ , arg_4__ with
      | Named tv _ , vars , fv_cand , in_scope , acc => FV.delFV tv vars fv_cand
                                                        in_scope acc
      | Anon _ , vars , fv_cand , in_scope , acc => vars fv_cand in_scope acc
    end.


(* TODO SCW: This will have the same issue as above.  *)
Parameter tyCoFVsBndr : TyBinder -> FV.FV -> FV.FV.
Parameter tyCoFVsOfType : Type_ -> FV.FV.
Parameter tyCoFVsOfCo : Coercion -> FV.FV.
Parameter tyCoFVsOfCos : list Coercion -> FV.FV.
Parameter tyCoFVsOfProv : UnivCoProvenance -> FV.FV.
Parameter tyCoFVsOfTypes : list Type_ -> FV.FV.
Parameter tyCoVarsOfCos : list Coercion -> VarSet.TyCoVarSet.
Parameter tyCoVarsOfProv : UnivCoProvenance -> VarSet.TyCoVarSet.
Parameter tyCoVarsOfCo : Coercion -> VarSet.TyCoVarSet.

(*

Definition tyCoFVsBndr : TyBinder -> FV.FV -> FV.FV :=
  fun bndr fvs =>
    FV.unionFV (delBinderVarFV bndr fvs) (tyCoFVsOfType (binderType bndr)).

Definition tyCoFVsOfType : Type_ -> FV.FV :=
  fix tyCoFVsOfType arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | TyVarTy v , a , b , c => (FV.unionFV (FV.unitFV v) (tyCoFVsOfType
                                                    (tyVarKind v))) a b c
             | TyConApp _ tys , a , b , c => tyCoFVsOfTypes tys a b c
             | LitTy _ , a , b , c => FV.emptyFV a b c
             | AppTy fun_ arg , a , b , c => (FV.unionFV (tyCoFVsOfType fun_) (tyCoFVsOfType
                                                         arg)) a b c
             | ForAllTy bndr ty , a , b , c => tyCoFVsBndr bndr (tyCoFVsOfType ty) a b c
             | CastTy ty co , a , b , c => (FV.unionFV (tyCoFVsOfType ty) (tyCoFVsOfCo co)) a
                                           b c
             | CoercionTy co , a , b , c => tyCoFVsOfCo co a b c
           end.

Definition tyCoFVsOfCo : Coercion -> FV.FV :=
  fix tyCoFVsOfCo arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | Refl _ ty , fv_cand , in_scope , acc => tyCoFVsOfType ty fv_cand in_scope acc
             | TyConAppCo _ _ cos , fv_cand , in_scope , acc => tyCoFVsOfCos cos fv_cand
                                                                in_scope acc
             | AppCo co arg , fv_cand , in_scope , acc => (FV.unionFV (tyCoFVsOfCo co)
                                                                      (tyCoFVsOfCo arg)) fv_cand in_scope acc
             | ForAllCo tv kind_co co , fv_cand , in_scope , acc => (FV.unionFV (FV.delFV tv
                                                                                (tyCoFVsOfCo co)) (tyCoFVsOfCo kind_co))
                                                                    fv_cand in_scope acc
             | CoVarCo v , fv_cand , in_scope , acc => (FV.unionFV (FV.unitFV v)
                                                                   (tyCoFVsOfType (varType v))) fv_cand in_scope acc
             | AxiomInstCo _ _ cos , fv_cand , in_scope , acc => tyCoFVsOfCos cos fv_cand
                                                                 in_scope acc
             | UnivCo p _ t1 t2 , fv_cand , in_scope , acc => (FV.unionFV (FV.unionFV
                                                                          (tyCoFVsOfProv p) (tyCoFVsOfType t1))
                                                                          (tyCoFVsOfType t2)) fv_cand in_scope acc
             | SymCo co , fv_cand , in_scope , acc => tyCoFVsOfCo co fv_cand in_scope acc
             | TransCo co1 co2 , fv_cand , in_scope , acc => (FV.unionFV (tyCoFVsOfCo co1)
                                                                         (tyCoFVsOfCo co2)) fv_cand in_scope acc
             | NthCo _ co , fv_cand , in_scope , acc => tyCoFVsOfCo co fv_cand in_scope acc
             | LRCo _ co , fv_cand , in_scope , acc => tyCoFVsOfCo co fv_cand in_scope acc
             | InstCo co arg , fv_cand , in_scope , acc => (FV.unionFV (tyCoFVsOfCo co)
                                                                       (tyCoFVsOfCo arg)) fv_cand in_scope acc
             | CoherenceCo c1 c2 , fv_cand , in_scope , acc => (FV.unionFV (tyCoFVsOfCo c1)
                                                                           (tyCoFVsOfCo c2)) fv_cand in_scope acc
             | KindCo co , fv_cand , in_scope , acc => tyCoFVsOfCo co fv_cand in_scope acc
             | SubCo co , fv_cand , in_scope , acc => tyCoFVsOfCo co fv_cand in_scope acc
             | AxiomRuleCo _ cs , fv_cand , in_scope , acc => tyCoFVsOfCos cs fv_cand
                                                              in_scope acc
           end.

Definition tyCoFVsOfCos : list Coercion -> FV.FV :=
  fix tyCoFVsOfCos arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | nil , fv_cand , in_scope , acc => FV.emptyFV fv_cand in_scope acc
             | cons co cos , fv_cand , in_scope , acc => (FV.unionFV (tyCoFVsOfCo co)
                                                                     (tyCoFVsOfCos cos)) fv_cand in_scope acc
           end.

Definition tyCoFVsOfProv : UnivCoProvenance -> FV.FV :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | UnsafeCoerceProv , fv_cand , in_scope , acc => FV.emptyFV fv_cand in_scope acc
      | PhantomProv co , fv_cand , in_scope , acc => tyCoFVsOfCo co fv_cand in_scope
                                                     acc
      | ProofIrrelProv co , fv_cand , in_scope , acc => tyCoFVsOfCo co fv_cand
                                                        in_scope acc
      | PluginProv _ , fv_cand , in_scope , acc => FV.emptyFV fv_cand in_scope acc
      | HoleProv _ , fv_cand , in_scope , acc => FV.emptyFV fv_cand in_scope acc
    end.

Definition tyCoFVsOfTypes : list Type_ -> FV.FV :=
  fix tyCoFVsOfTypes arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | cons ty tys , fv_cand , in_scope , acc => (FV.unionFV (tyCoFVsOfType ty)
                                                                     (tyCoFVsOfTypes tys)) fv_cand in_scope acc
             | nil , fv_cand , in_scope , acc => FV.emptyFV fv_cand in_scope acc
           end.

Definition tyCoVarsOfCos : list Coercion -> VarSet.TyCoVarSet :=
  fun cos => FV.fvVarSet GHC.Base.$ tyCoFVsOfCos cos.

Definition tyCoVarsOfProv : UnivCoProvenance -> VarSet.TyCoVarSet :=
  fun prov => FV.fvVarSet GHC.Base.$ tyCoFVsOfProv prov.

Definition tyCoVarsOfCo : Coercion -> VarSet.TyCoVarSet :=
  fun co => FV.fvVarSet GHC.Base.$ tyCoFVsOfCo co.
*)

Definition substForAllCoBndrCallback
    : bool -> (Coercion -> Coercion) -> TCvSubst -> TyVar -> Coercion -> (TCvSubst
      * TyVar * Coercion)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ , arg_4__ with
      | sym , sco , Mk_TCvSubst in_scope tenv cenv , old_var , old_kind_co =>
        let no_kind_change := VarSet.isEmptyVarSet (tyCoVarsOfCo old_kind_co) in
        let new_kind_co :=
          if no_kind_change : bool
          then old_kind_co
          else sco old_kind_co in
        match coercionKind new_kind_co with
        | Pair.Mk_Pair new_ki1 _ =>
          let new_var :=
              VarEnv.uniqAway in_scope (Var.setTyVarKind old_var new_ki1) in
          let no_change := andb no_kind_change (new_var GHC.Base.== old_var) in
          let new_env :=
              let j_11__ := VarEnv.extendVarEnv tenv old_var (TyVarTy new_var) in
              let j_12__ :=
                  if sym : bool
                  then VarEnv.extendVarEnv tenv old_var GHC.Base.$ CastTy (TyVarTy new_var)
                                           new_kind_co
                  else j_11__ in
              if andb no_change (negb sym) : bool
              then VarEnv.delVarEnv tenv old_var
              else j_12__ in
          pair (pair (Mk_TCvSubst (VarEnv.extendInScopeSet in_scope new_var) new_env cenv)
                     new_var) new_kind_co
        end
    end.

Definition tyCoVarsOfCoDSet : Coercion -> VarSet.DTyCoVarSet :=
  fun co => FV.fvDVarSet GHC.Base.$ tyCoFVsOfCo co.

Definition tyCoVarsOfCoList : Coercion -> list Var.TyCoVar :=
  fun co => FV.fvVarList GHC.Base.$ tyCoFVsOfCo co.

Definition tyCoVarsOfTypes : list Type_ -> VarSet.TyCoVarSet :=
  fun tys => FV.fvVarSet GHC.Base.$ tyCoFVsOfTypes tys.

Definition getTCvSubstRangeFVs : TCvSubst -> VarSet.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_TCvSubst _ tenv cenv => let cenvFVs :=
                                  tyCoVarsOfCos GHC.Base.$ VarEnv.varEnvElts cenv in
                                let tenvFVs := tyCoVarsOfTypes GHC.Base.$ VarEnv.varEnvElts tenv in
                                VarSet.unionVarSet tenvFVs cenvFVs
    end.

Definition isValidTCvSubst : TCvSubst -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_TCvSubst in_scope tenv cenv => let cenvFVs :=
                                         tyCoVarsOfCos GHC.Base.$ VarEnv.varEnvElts cenv in
                                       let tenvFVs := tyCoVarsOfTypes GHC.Base.$ VarEnv.varEnvElts tenv in
                                       andb (VarEnv.varSetInScope tenvFVs in_scope) (VarEnv.varSetInScope cenvFVs
                                                                                                          in_scope)
    end.

(* SCW: removed `{Callstack} implicit parameter as Coq can't figure it out. *)

Definition checkValidSubst {a} : TCvSubst -> list Type_ -> list
                                                Coercion -> a -> a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | (Mk_TCvSubst in_scope tenv cenv as subst) , tys , cos , a =>
        let substDomain :=
            Coq.Init.Datatypes.app (VarEnv.varEnvKeys tenv)
                                   (VarEnv.varEnvKeys cenv) in
        let needInScope :=
            UniqFM.delListFromUFM_Directly (VarSet.unionVarSet
                                              (tyCoVarsOfTypes tys)
                                              (tyCoVarsOfCos cos))
                                           substDomain in
        let tysCosFVsInScope :=
            VarEnv.varSetInScope needInScope in_scope in a
    end.

Definition mkTyCoInScopeSet : list Type_ -> list
                              Coercion -> VarEnv.InScopeSet :=
  fun tys cos =>
    VarEnv.mkInScopeSet (VarSet.unionVarSet (tyCoVarsOfTypes tys) (tyCoVarsOfCos
                                            cos)).

(* Need Num GHC.Integer!!! *)


Definition substCoVarBndrCallback
    : bool -> (TCvSubst -> Type_ -> Type_) -> TCvSubst -> CoVar -> (TCvSubst *
      CoVar)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | sym , subst_fun , (Mk_TCvSubst in_scope tenv cenv as subst) , old_var =>
        match coVarKindsTypesRole old_var with
          | pair (pair (pair (pair _ _) t1) t2) role =>
            let t1' := subst_fun subst t1 in
            let t2' := subst_fun subst t2 in
            let new_var_type :=
                Data.Tuple.uncurry (mkCoercionType role)
                                   (if sym : bool then pair t2' t1' else pair t1' t2') in
            let subst_old_var :=
                Var.mkCoVar (Var.varName old_var) new_var_type in
            let new_var := VarEnv.uniqAway in_scope subst_old_var in
            let no_kind_change :=
                VarSet.isEmptyVarSet (tyCoVarsOfTypes (cons t1 (cons t2
                                                                     nil))) in
            let new_co :=
                (if sym : bool
                 then mkSymCo
                 else GHC.Base.id) GHC.Base.$ mkCoVarCo new_var in
            let no_change :=
                andb (new_var GHC.Base.== old_var) (andb (negb
                                                            (isReflCo
                                                               new_co))
                                                         no_kind_change) in
            let new_cenv :=
                let j_13__ := VarEnv.extendVarEnv cenv old_var new_co in
                if no_change : bool
                then VarEnv.delVarEnv cenv old_var
                else j_13__ in
          pair (Mk_TCvSubst (VarEnv.extendInScopeSet in_scope new_var)
                                   tenv new_cenv) new_var
        end
    end.

Definition tyCoVarsOfTypesDSet : list Type_ -> VarSet.DTyCoVarSet :=
  fun tys => FV.fvDVarSet GHC.Base.$ tyCoFVsOfTypes tys.

Definition tyCoVarsOfTypesList : list Type_ -> list Var.TyCoVar :=
  fun tys => FV.fvVarList GHC.Base.$ tyCoFVsOfTypes tys.




Definition closeOverKindsFV : list TyVar -> FV.FV :=
  fun tvs =>
    FV.unionFV (FV.mapUnionFV (tyCoFVsOfType GHC.Base.∘ Var.tyVarKind) tvs)
               (FV.mkFVs tvs).

Definition closeOverKinds : VarSet.TyVarSet -> VarSet.TyVarSet :=
  FV.fvVarSet GHC.Base.∘ (closeOverKindsFV GHC.Base.∘ VarSet.varSetElems).

Definition closeOverKindsDSet : VarSet.DTyVarSet -> VarSet.DTyVarSet :=
  FV.fvDVarSet GHC.Base.∘ (closeOverKindsFV GHC.Base.∘ VarSet.dVarSetElems).

Definition closeOverKindsList : list TyVar -> list TyVar :=
  fun tvs => FV.fvVarList GHC.Base.$ closeOverKindsFV tvs.

Definition tyCoVarsOfType : Type_ -> VarSet.TyCoVarSet :=
  fun ty => FV.fvVarSet GHC.Base.$ tyCoFVsOfType ty.

Definition extendCvSubstWithClone
    : TCvSubst -> CoVar -> CoVar -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | Mk_TCvSubst in_scope tenv cenv , cv , cv' => let new_in_scope :=
                                                    VarSet.extendVarSet (tyCoVarsOfType (Var.varType cv')) cv' in
                                                  Mk_TCvSubst (VarEnv.extendInScopeSetSet in_scope new_in_scope) tenv
                                                  (VarEnv.extendVarEnv cenv cv (mkCoVarCo cv'))
    end.

Definition extendTvSubstAndInScope
    : TCvSubst -> TyVar -> Type_ -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | Mk_TCvSubst in_scope tenv cenv , tv , ty => Mk_TCvSubst (VarEnv.extendInScopeSetSet
                                                          in_scope (tyCoVarsOfType ty)) (VarEnv.extendVarEnv tenv tv ty)
                                                 cenv
    end.

Parameter isUnliftedTypeKind : Kind -> bool.

(*
Definition isUnliftedTypeKind : Kind -> bool :=
  fix isUnliftedTypeKind arg_0__
        := let j_2__ :=
             match arg_0__ with
               | TyConApp tc (cons arg nil) => andb (Unique.hasKey tc PrelNames_tYPETyConKey)
                                                    (VarSet.isEmptyVarSet (tyCoVarsOfType arg))
               | _ => false
             end in
           let j_4__ :=
             match arg_0__ with
               | TyConApp tc (cons (TyConApp ptr_rep nil) nil) =>
                 if andb (Unique.hasKey tc
                                        PrelNames_tYPETyConKey)
                         (Unique.hasKey ptr_rep
                                        PrelNames_ptrRepLiftedDataConKey) : bool
                 then false
                 else j_2__
               | _ => j_2__
             end in
           match arg_0__ with
             | ki => match coreView ki with
                       | Some ki' => isUnliftedTypeKind ki'
                       | _ => j_4__
                     end
           end. *)

Definition tyCoVarsOfTelescope : list
                                 Var -> VarSet.TyCoVarSet -> VarSet.TyCoVarSet :=
  fix tyCoVarsOfTelescope arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | nil , fvs => fvs
             | cons v vs , fvs => VarSet.unionVarSet (VarSet.delVarSet (tyCoVarsOfTelescope
                                                                       vs fvs) v) (tyCoVarsOfType (Var.varType v))
           end.

Definition tyCoVarsOfTypeDSet : Type_ -> VarSet.DTyCoVarSet :=
  fun ty => FV.fvDVarSet GHC.Base.$ tyCoFVsOfType ty.

Definition tyCoVarsOfTypeList : Type_ -> list Var.TyCoVar :=
  fun ty => FV.fvVarList GHC.Base.$ tyCoFVsOfType ty.

(*--- From module Type ---*)
Definition toposortTyVars : list TyVar -> list TyVar :=
  fun tvs =>
    let var_ids : VarEnv.VarEnv GHC.Num.Int :=
      VarEnv.mkVarEnv (GHC.List.zip tvs (GHC.Enum.enumFromTo (GHC.Num.fromInteger 1) (GHC.List.length tvs))) in
    let nodes :=
      Coq.Lists.List.flat_map (fun tv =>
                                cons (pair (pair tv (VarEnv.lookupVarEnv_NF var_ids tv)) (Data.Maybe.mapMaybe
                                           (VarEnv.lookupVarEnv var_ids) (tyCoVarsOfTypeList (Var.tyVarKind
                                                                                                     tv)))) nil) tvs in
    GHC.List.reverse GHC.Base.$ (let cont_2__ arg_3__ :=
      match arg_3__ with
        | pair (pair tv _) _ => cons tv nil
      end in
    Coq.Lists.List.flat_map cont_2__ (Digraph.topologicalSortG GHC.Base.$
                            Digraph.graphFromEdgedVertices nodes)).

Definition Type_tyCoVarsOfTypeWellScoped : Core.Type_ -> list TyVar :=
  toposortTyVars GHC.Base.∘ tyCoVarsOfTypeList.

Definition Type_tyCoVarsOfTypesWellScoped : list Core.Type_ -> list TyVar :=
  toposortTyVars GHC.Base.∘ tyCoVarsOfTypesList.
(*--- from Module Type ---*)


(*
Definition emptyCvSubstEnv : CvSubstEnv :=
  VarEnv.emptyVarEnv.
*)
Definition mkTvSubst : VarEnv.InScopeSet -> TvSubstEnv -> TCvSubst :=
  fun in_scope tenv => Mk_TCvSubst in_scope tenv emptyCvSubstEnv.

Definition isCoercionType : Type_ -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | TyConApp tc tys => if andb (orb (Unique.hasKey tc PrelNames.eqPrimTyConKey)
                                        (Unique.hasKey tc PrelNames.eqReprPrimTyConKey)) (Data.Foldable.length tys
                                   GHC.Base.== GHC.Num.fromInteger 4) : bool
                           then true
                           else false
      | _ => false
    end.


Definition mkTvSubstPrs : list (TyVar * Type_)%type -> TCvSubst :=
  fun prs =>
    let onlyTyVarsAndNoCoercionTy :=
      Data.Foldable.and (let cont_0__ arg_1__ :=
                          match arg_1__ with
                            | pair tv ty => cons (andb (Var.isTyVar tv) (negb (Type_isCoercionTy ty))) nil
                          end in
                        Coq.Lists.List.flat_map cont_0__ prs) in
    let in_scope :=
      VarEnv.mkInScopeSet GHC.Base.$ (tyCoVarsOfTypes GHC.Base.$ GHC.Base.map
      Data.Tuple.snd prs) in
    let tenv := VarEnv.mkVarEnv prs in
     mkTvSubst in_scope tenv.

Definition zipTyBinderSubst : list TyBinder -> list Type_ -> TCvSubst :=
  fun bndrs tys =>
    let tenv :=
      VarEnv.mkVarEnv (let cont_0__ arg_1__ :=
                        match arg_1__ with
                          | pair (Named tv _) ty => cons (pair tv ty) nil
                          | _ => nil
                        end in
                      Coq.Lists.List.flat_map cont_0__ (GHC.List.zip bndrs tys)) in
    let is_ := VarEnv.mkInScopeSet (tyCoVarsOfTypes tys) in mkTvSubst is_ tenv.

Definition emptyTCvSubst : TCvSubst :=
  Mk_TCvSubst VarEnv.emptyInScopeSet emptyTvSubstEnv emptyCvSubstEnv.


Definition extendCvSubst : TCvSubst -> CoVar -> Coercion -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | Mk_TCvSubst in_scope tenv cenv , v , co => Mk_TCvSubst in_scope tenv
                                                (VarEnv.extendVarEnv cenv v co)
    end.

Definition extendTCvInScope : TCvSubst -> Var -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst in_scope tenv cenv , var => Mk_TCvSubst (VarEnv.extendInScopeSet
                                                      in_scope var) tenv cenv
    end.

Definition extendTCvInScopeList : TCvSubst -> list Var -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst in_scope tenv cenv , vars => Mk_TCvSubst (VarEnv.extendInScopeSetList
                                                       in_scope vars) tenv cenv
    end.

Definition extendTCvInScopeSet : TCvSubst -> VarSet.VarSet -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst in_scope tenv cenv , vars => Mk_TCvSubst (VarEnv.extendInScopeSetSet
                                                       in_scope vars) tenv cenv
    end.

Definition extendTvSubst : TCvSubst -> TyVar -> Type_ -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | Mk_TCvSubst in_scope tenv cenv , tv , ty => Mk_TCvSubst in_scope
                                                 (VarEnv.extendVarEnv tenv tv ty) cenv
    end.

Definition extendTvSubstBinder : TCvSubst -> TyBinder -> Type_ -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | env , Anon _ , _ => env
      | env , Named tv _ , ty => extendTvSubst env tv ty
    end.

Definition extendTvSubstList : TCvSubst -> list Var -> list
                               Type_ -> TCvSubst :=
  fun subst tvs tys => Util.foldl2 extendTvSubst subst tvs tys.

Definition extendTCvSubst : TCvSubst -> Var.TyCoVar -> Type_ -> TCvSubst :=
  fun subst v ty =>
    let j_0__ :=
      Panic.panicStr (GHC.Base.hs_string__ "extendTCvSubst") (GHC.Base.mappend
                                                             (GHC.Base.mappend (Panic.noString v) (id
                                                                               (GHC.Base.hs_string__ "|->")))
                                                             (Panic.noString ty)) in
    let j_1__ :=
      match ty with
        | CoercionTy co => extendCvSubst subst v co
        | _ => j_0__
      end in
    if Var.isTyVar v : bool
    then extendTvSubst subst v ty
    else j_1__.

Definition getCvSubstEnv : TCvSubst -> CvSubstEnv :=
  fun arg_0__ => match arg_0__ with | Mk_TCvSubst _ _ env => env end.

Definition getTCvInScope : TCvSubst -> VarEnv.InScopeSet :=
  fun arg_0__ => match arg_0__ with | Mk_TCvSubst in_scope _ _ => in_scope end.

Definition getTvSubstEnv : TCvSubst -> TvSubstEnv :=
  fun arg_0__ => match arg_0__ with | Mk_TCvSubst _ env _ => env end.

(*
Definition if_print_coercions
    : Outputable.SDoc -> Outputable.SDoc -> Outputable.SDoc :=
  fun yes no =>
    Outputable.sdocWithDynFlags GHC.Base.$ (fun dflags =>
      Outputable.getPprStyle GHC.Base.$ (fun style =>
        if orb (DynFlags.gopt DynFlags.Opt_PrintExplicitCoercions dflags) (orb
               (Outputable.dumpStyle style) (Outputable.debugStyle style)) : bool
        then yes
        else no)).
*)
Definition isAnonBinder : TyBinder -> bool :=
  fun arg_0__ => match arg_0__ with | Anon _ => true | _ => false end.


Definition isEmptyTCvSubst : TCvSubst -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_TCvSubst _ tenv cenv => andb (VarEnv.isEmptyVarEnv tenv) (VarEnv.isEmptyVarEnv
                                     cenv)
    end.

Definition isInScope : Var -> TCvSubst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | v , Mk_TCvSubst in_scope _ _ => VarEnv.elemInScopeSet v in_scope
    end.

Definition isInvisibleBinder : TyBinder -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Named _ vis => vis GHC.Base./= Visible
      | Anon ty => Type_isPredTy ty
    end.

Definition isVisibleBinder : TyBinder -> bool :=
  negb GHC.Base.∘ isInvisibleBinder.


Definition isNamedBinder : TyBinder -> bool :=
  fun arg_0__ => match arg_0__ with | Named _ _ => true | _ => false end.


Definition lookupCoVar : TCvSubst -> Var -> option Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst _ _ cenv , v => VarEnv.lookupVarEnv cenv v
    end.

Definition lookupTyVar : TCvSubst -> TyVar -> option Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst _ tenv _ , tv => if andb Util.debugIsOn (negb (Var.isTyVar
                                                               tv)) : bool
                                  then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
                                       (GHC.Num.fromInteger 2142))
                                  else VarEnv.lookupVarEnv tenv tv
    end.

(*----- from Type ------ *)

Require Control.Arrow.

Parameter arrow_first : forall {b}{c}{d}, (b -> c) -> (b * d)%type -> (c * d)%type.
Parameter arrow_second : forall {b}{c}{d}, (b -> c) -> (d * b)%type -> (d * b)%type.

(* Also recurses through the kind of type variables. What!! *)
Parameter Type_partitionInvisibles : forall {a}, Core.TyCon -> (a -> Core.Type_) -> list
                                     a -> (list a * list a)%type.
(*  :=
  fun tc get_ty =>
    let go :=
      fix go arg_0__ arg_1__ arg_2__
            := let j_4__ :=
                 match arg_0__ , arg_1__ , arg_2__ with
                   | _ , _ , xs => pair nil xs
                 end in
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , _ , nil => pair nil nil
                 | subst , Core.ForAllTy bndr res_ki , cons x xs =>
                   let subst' :=
                       extendTvSubstBinder subst bndr (get_ty x) in
                   let j_8__ :=
                       arrow_first (fun arg_7__ =>
                                      cons x arg_7__)
                                   (go subst' res_ki xs) in
                   if isVisibleBinder bndr : bool
                   then arrow_second
                          (fun arg_9__ =>
                             cons x arg_9__)
                          (go subst' res_ki xs)
                   else j_8__
                 | subst , Core.TyVarTy tv , xs => match lookupTyVar subst tv with
                                                     | Some ki => go subst ki xs
                                                     | _ => j_4__
                                                   end
                 | _ , _ , _ => j_4__
               end in
    go emptyTCvSubst (tyConKind tc). *)
(* ---- end from Type *)

(*
Definition maybeParen
    : TyPrec -> TyPrec -> Outputable.SDoc -> Outputable.SDoc :=
  fun ctxt_prec inner_prec pretty =>
    let j_0__ := Outputable.parens pretty in
    if ctxt_prec GHC.Base.< inner_prec : bool
    then pretty
    else j_0__.

Definition pprArrowChain : TyPrec -> list Outputable.SDoc -> Outputable.SDoc :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | _ , nil => Outputable.empty
      | p , cons arg args => maybeParen p FunPrec GHC.Base.$ Outputable.sep (cons arg
                                                                                  (cons (Outputable.sep (GHC.Base.map
                                                                                                        (fun arg_2__ =>
                                                                                                          GHC.Base.mappend
                                                                                                          Outputable.arrow
                                                                                                          arg_2__)
                                                                                                        args)) nil))
    end.

Definition pprInfixApp {a}
    : TyPrec -> (TyPrec -> a -> Outputable.SDoc) -> Outputable.SDoc -> a -> a -> Outputable.SDoc :=
  fun p pp pp_tc ty1 ty2 =>
    maybeParen p TyOpPrec GHC.Base.$ Outputable.sep (cons (pp TyOpPrec ty1) (cons
                                                          (GHC.Base.mappend (Outputable.pprInfixVar true pp_tc) (pp
                                                                            TyOpPrec ty2)) nil)).

Definition pprPrefixApp : TyPrec -> Outputable.SDoc -> list
                          Outputable.SDoc -> Outputable.SDoc :=
  fun p pp_fun pp_tys =>
    let j_0__ :=
      maybeParen p TyConPrec GHC.Base.$ Outputable.hang pp_fun (GHC.Num.fromInteger 2)
      (Outputable.sep pp_tys) in
    if Data.Foldable.null pp_tys : bool
    then pp_fun
    else j_0__.

Definition pprTupleApp {a}
    : TyPrec -> (TyPrec -> a -> Outputable.SDoc) -> TyCon.TyCon -> BasicTypes.TupleSort -> list
      a -> Outputable.SDoc :=
  fun p pp tc sort tys =>
    let j_0__ :=
      TyCon.pprPromotionQuote tc Outputable.<> BasicTypes.tupleParens sort
      (Outputable.pprWithCommas (pp TopPrec) tys) in
    if Data.Foldable.null tys : bool
    then match sort with
           | BasicTypes.ConstraintTuple => if StaticFlags.opt_PprStyle_Debug : bool
                                           then id (GHC.Base.hs_string__ "(%%)")
                                           else maybeParen p FunPrec GHC.Base.$ id (GHC.Base.hs_string__
                                                                                   "() :: Constraint")
           | _ => j_0__
         end
    else j_0__.
*)

Definition mkForAllTys : list TyBinder -> Type_ -> Type_ :=
  fun tyvars ty => Data.Foldable.foldr ForAllTy ty tyvars.

Definition mkFunTy : Type_ -> Type_ -> Type_ :=
  fun arg res => ForAllTy (Anon arg) res.

Definition mkFunTys : list Type_ -> Type_ -> Type_ :=
  fun tys ty => Data.Foldable.foldr mkFunTy ty tys.

Definition mkTCvSubst : VarEnv.InScopeSet -> (TvSubstEnv *
                        CvSubstEnv)%type -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | in_scope , pair tenv cenv => Mk_TCvSubst in_scope tenv cenv
    end.

Definition mkTyConTy : TyCon -> Type_ :=
  fun tycon => TyConApp tycon nil.

Definition mkTyVarTy : TyVar -> Type_ :=
  fun v =>
 TyVarTy v.

Definition mkTyVarTys : list TyVar -> list Type_ :=
  GHC.Base.map mkTyVarTy.

Definition extendTvSubstWithClone
    : TCvSubst -> TyVar -> TyVar -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | Mk_TCvSubst in_scope tenv cenv , tv , tv' => let new_in_scope :=
                                                    VarSet.extendVarSet (tyCoVarsOfType (Var.tyVarKind tv')) tv' in
                                                  Mk_TCvSubst (VarEnv.extendInScopeSetSet in_scope new_in_scope)
                                                  (VarEnv.extendVarEnv tenv tv (mkTyVarTy tv')) cenv
    end.

Definition notElemTCvSubst : Var -> TCvSubst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | v , Mk_TCvSubst _ tenv cenv => let j_2__ := negb (VarEnv.elemVarEnv v cenv) in
                                    if Var.isTyVar v : bool
                                    then negb (VarEnv.elemVarEnv v tenv)
                                    else j_2__
    end.

Definition pickLR {a} : LeftOrRight -> (a * a)%type -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | CLeft , pair l _ => l
      | CRight , pair _ r => r
    end.

(*
Definition pprTyThingCategory : TyThing -> Outputable.SDoc :=
  fun arg_0__ =>
    match arg_0__ with
      | ATyCon tc => let j_1__ := id (GHC.Base.hs_string__ "Type constructor") in
                     if TyCon.isClassTyCon tc : bool
                     then id (GHC.Base.hs_string__ "Class")
                     else j_1__
      | ACoAxiom _ => id (GHC.Base.hs_string__ "Coercion axiom")
      | AnId _ => id (GHC.Base.hs_string__ "Identifier")
      | AConLike (ConLike.RealDataCon _) => id (GHC.Base.hs_string__
                                               "Data constructor")
      | AConLike (ConLike.PatSynCon _) => id (GHC.Base.hs_string__ "Pattern synonym")
    end.

Definition pprTyThing : TyThing -> Outputable.SDoc :=
  fun thing =>
    GHC.Base.mappend (pprTyThingCategory thing) (Outputable.quotes (Panic.noString
                                                                   (Name.getName thing))).

Definition ppr_tvar : TyVar -> Outputable.SDoc :=
  fun tv => OccName.parenSymOcc (Name.getOccName tv) (Panic.noString tv).

Definition ppr_tylit : TyPrec -> TyLit -> Outputable.SDoc :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | _ , tl => match tl with
                    | NumTyLit n => Outputable.integer n
                    | StrTyLit s => id (GHC.Show.show s)
                  end
    end.

Definition pprTyLit : TyLit -> Outputable.SDoc :=
  ppr_tylit TopPrec. *)

Definition sameVis : VisibilityFlag -> VisibilityFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Visible , Visible => true
      | Visible , _ => false
      | _ , Visible => false
      | _ , _ => true
    end.

Definition setCvSubstEnv : TCvSubst -> CvSubstEnv -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst in_scope tenv _ , cenv => Mk_TCvSubst in_scope tenv cenv
    end.

Definition setTvSubstEnv : TCvSubst -> TvSubstEnv -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst in_scope _ cenv , tenv => Mk_TCvSubst in_scope tenv cenv
    end.

Definition substCoVar : TCvSubst -> CoVar -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst _ _ cenv , cv => let scrut_2__ := VarEnv.lookupVarEnv cenv cv in
                                  match scrut_2__ with
                                    | Some co => co
                                    | None => CoVarCo cv
                                  end
    end.

Definition substCoVars : TCvSubst -> list CoVar -> list Coercion :=
  fun subst cvs => GHC.Base.map (substCoVar subst) cvs.

Definition substTyVar : TCvSubst -> TyVar -> Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst _ tenv _ , tv => let scrut_2__ := VarEnv.lookupVarEnv tenv tv in
                                       match scrut_2__ with
                                         | Some ty => ty
                                         | None => TyVarTy tv
                                       end
    end.

Definition substTyVars : TCvSubst -> list TyVar -> list Type_ :=
  fun subst => GHC.Base.map GHC.Base.$ substTyVar subst.


Parameter suppressInvisibles : forall {a},
     (a -> Type_) -> DynFlags.DynFlags -> TyCon -> list a -> list a.

(*
Definition suppressInvisibles {a}
    : (a -> Type_) -> DynFlags.DynFlags -> TyCon -> list a -> list a :=
  fun to_type dflags tc xs =>
    let j_0__ := Data.Tuple.snd GHC.Base.$ Type_partitionInvisibles tc to_type xs in
    if DynFlags.gopt DynFlags.Opt_PrintExplicitKinds dflags : bool
    then xs
    else j_0__.*)
(*
Definition pprTcApp_help {a}
    : (a -> Type_) -> TyPrec -> (TyPrec -> a -> Outputable.SDoc) -> TyCon.TyCon -> list
      a -> DynFlags.DynFlags -> Outputable.PprStyle -> Outputable.SDoc :=
  fun to_type p pp tc tys dflags style =>
    let print_eqs :=
      orb (DynFlags.gopt DynFlags.Opt_PrintEqualityRelations dflags) (orb
          (Outputable.dumpStyle style) (Outputable.debugStyle style)) in
    let print_kinds := DynFlags.gopt DynFlags.Opt_PrintExplicitKinds dflags in
    let hetero_eq_tc :=
      orb (Unique.hasKey tc PrelNames.eqPrimTyConKey) (orb (Unique.hasKey tc
                                                                          PrelNames.eqReprPrimTyConKey) (Unique.hasKey
                                                           tc PrelNames.heqTyConKey)) in
    let homo_eq_tc := Unique.hasKey tc PrelNames.eqTyConKey in
    let mb_saturated_equality :=
      let j_4__ :=
        if homo_eq_tc : bool
        then match tys with
               | cons k (cons t1 (cons t2 nil)) => Some (pair (pair (pair k k) t1) t2)
               | _ => None
             end
        else None in
      if hetero_eq_tc : bool
      then match tys with
             | cons k1 (cons k2 (cons t1 (cons t2 nil))) => Some (pair (pair (pair k1 k2) t1)
                                                                       t2)
             | _ => j_4__
           end
      else j_4__ in
    let tys_wo_kinds := suppressInvisibles to_type dflags tc tys in
    let pp_tc := Panic.noString tc in
    let print_equality :=
      fun arg_8__ =>
        match arg_8__ with
          | pair (pair (pair ki1 ki2) ty1) ty2 => let ppr_infix_eq :=
                                                    fun eq_op =>
                                                      Outputable.sep (cons (Outputable.parens (GHC.Base.mappend
                                                                                              (GHC.Base.mappend (pp
                                                                                                                TyOpPrec
                                                                                                                ty1)
                                                                                                                Outputable.dcolon)
                                                                                              (pp TyOpPrec ki1))) (cons
                                                                           eq_op (cons (Outputable.parens
                                                                                       (GHC.Base.mappend
                                                                                       (GHC.Base.mappend (pp TyOpPrec
                                                                                                         ty2)
                                                                                                         Outputable.dcolon)
                                                                                       (pp TyOpPrec ki2))) nil))) in
                                                  let j_10__ :=
                                                    if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool
                                                    then GHC.Base.mappend (id (GHC.Base.hs_string__ "Coercible"))
                                                                          (Outputable.sep (cons (pp TyConPrec ty1) (cons
                                                                                                (pp TyConPrec ty2)
                                                                                                nil)))
                                                    else Outputable.sep (cons (pp TyOpPrec ty1) (cons (id
                                                                                                      (GHC.Base.hs_string__
                                                                                                      "~")) (cons (pp
                                                                                                                  TyOpPrec
                                                                                                                  ty2)
                                                                                                                  nil))) in
                                                  let j_11__ :=
                                                    if andb hetero_eq_tc (orb print_kinds (negb (Type.eqType (to_type
                                                                                                             ki1)
                                                                                                             (to_type
                                                                                                             ki2)))) : bool
                                                    then ppr_infix_eq GHC.Base.$ (if Unique.hasKey tc
                                                                                                   PrelNames.eqPrimTyConKey : bool
                                                         then id (GHC.Base.hs_string__ "~~")
                                                         else pp_tc)
                                                    else j_10__ in
                                                  if print_eqs : bool
                                                  then ppr_infix_eq pp_tc
                                                  else j_11__
        end in
    let tc_name := tyConName tc in
    let j_15__ :=
      pprPrefixApp p (Outputable.parens (pp_tc)) (GHC.Base.map (pp TyConPrec)
                                                 tys_wo_kinds) in
    let j_16__ :=
      if orb (Unique.hasKey tc_name PrelNames.starKindTyConKey) (orb (Unique.hasKey
                                                                     tc_name PrelNames.unicodeStarKindTyConKey)
                                                                     (Unique.hasKey tc_name
                                                                                    PrelNames.unliftedTypeKindTyConKey)) : bool
      then pp_tc
      else j_15__ in
    let j_17__ :=
      match tys_wo_kinds with
        | cons ty1 (cons ty2 nil) => pprInfixApp p pp pp_tc ty1 ty2
        | _ => j_16__
      end in
    let j_18__ :=
      match mb_saturated_equality with
        | Some args => print_equality args
        | _ => j_17__
      end in
    if negb (OccName.isSymOcc (Name.nameOccName tc_name)) : bool
    then pprPrefixApp p pp_tc (GHC.Base.map (pp TyConPrec) tys_wo_kinds)
    else j_18__.

Definition pprTcApp {a}
    : Outputable.PprStyle -> (a -> Type_) -> TyPrec -> (TyPrec -> a -> Outputable.SDoc) -> TyCon.TyCon -> list
      a -> Outputable.SDoc :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ =>
    let j_18__ :=
      match arg_0__ , arg_1__ , arg_2__ , arg_3__ , arg_4__ , arg_5__ with
        | style , to_type , p , pp , tc , tys => let j_7__ :=
                                                   Outputable.sdocWithDynFlags GHC.Base.$ (fun dflags =>
                                                     pprTcApp_help to_type p pp tc tys dflags style) in
                                                 let j_11__ :=
                                                   if negb (Outputable.debugStyle style) : bool
                                                   then match TyCon.isPromotedDataCon_maybe tc with
                                                          | Some dc => let dc_tc := DataCon.dataConTyCon dc in
                                                                       match TyCon.tyConTuple_maybe dc_tc with
                                                                         | Some tup_sort => let arity :=
                                                                                              tyConArity dc_tc in
                                                                                            let ty_args :=
                                                                                              GHC.List.drop arity tys in
                                                                                            if Util.lengthIs ty_args
                                                                                                             arity : bool
                                                                                            then TyCon.pprPromotionQuote
                                                                                                 tc Outputable.<>
                                                                                                 (BasicTypes.tupleParens
                                                                                                 tup_sort GHC.Base.$
                                                                                                 Outputable.pprWithCommas
                                                                                                 (pp TopPrec) ty_args)
                                                                                            else j_7__
                                                                         | _ => j_7__
                                                                       end
                                                          | _ => j_7__
                                                        end
                                                   else j_7__ in
                                                 if negb (Outputable.debugStyle style) : bool
                                                 then match TyCon.tyConTuple_maybe tc with
                                                        | Some sort => let arity := tyConArity tc in
                                                                       if arity GHC.Base.== Data.Foldable.length
                                                                          tys : bool
                                                                       then let num_to_drop :=
                                                                              match sort with
                                                                                | BasicTypes.UnboxedTuple =>
                                                                                  GHC.Real.div arity
                                                                                               (GHC.Num.fromInteger 2)
                                                                                | _ => GHC.Num.fromInteger 0
                                                                              end in
                                                                            pprTupleApp p pp tc sort (GHC.List.drop
                                                                                                     num_to_drop tys)
                                                                       else j_11__
                                                        | _ => j_11__
                                                      end
                                                 else j_11__
      end in
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ , arg_4__ , arg_5__ with
      | _ , _ , _ , pp , tc , cons ty nil => let j_19__ :=
                                               if Unique.hasKey tc PrelNames.parrTyConKey : bool
                                               then TyCon.pprPromotionQuote tc Outputable.<> Outputable.paBrackets (pp
                                                                                                                   TopPrec
                                                                                                                   ty)
                                               else j_18__ in
                                             if Unique.hasKey tc PrelNames.listTyConKey : bool
                                             then TyCon.pprPromotionQuote tc Outputable.<> Outputable.brackets (pp
                                                                                                               TopPrec
                                                                                                               ty)
                                             else j_19__
      | _ , _ , _ , _ , _ , _ => j_18__
    end.

Definition pprTcAppCo
    : TyPrec -> (TyPrec -> Coercion -> Outputable.SDoc) -> TyCon.TyCon -> list
      Coercion -> Outputable.SDoc :=
  fun p pp tc cos =>
    Outputable.getPprStyle GHC.Base.$ (fun style =>
      pprTcApp style (pFst GHC.Base.∘ coercionKind) p pp tc cos).

Definition pprTcAppTy
    : TyPrec -> (TyPrec -> Type_ -> Outputable.SDoc) -> TyCon.TyCon -> list
      Type_ -> Outputable.SDoc :=
  fun p pp tc tys =>
    Outputable.getPprStyle GHC.Base.$ (fun style =>
      pprTcApp style GHC.Base.id p pp tc tys).

Definition pprTyTcApp : TyPrec -> TyCon.TyCon -> list
                        Type_ -> Outputable.SDoc :=
  fun p tc tys =>
    let ppr_deflt := pprTcAppTy p ppr_type tc tys in
    let j_1__ :=
      if Unique.hasKey tc PrelNames.tYPETyConKey : bool
      then match tys with
             | cons (TyConApp ptr_rep nil) nil => if Unique.hasKey ptr_rep
                                                                   PrelNames.ptrRepUnliftedDataConKey : bool
                                                  then Outputable.char (GHC.Char.hs_char__ "#")
                                                  else ppr_deflt
             | _ => ppr_deflt
           end
      else ppr_deflt in
    let j_2__ :=
      if Unique.hasKey tc PrelNames.tYPETyConKey : bool
      then match tys with
             | cons (TyConApp ptr_rep nil) nil => if Unique.hasKey ptr_rep
                                                                   PrelNames.ptrRepLiftedDataConKey : bool
                                                  then Outputable.unicodeSyntax (Outputable.char (GHC.Char.hs_char__
                                                                                                 "★")) (Outputable.char
                                                                                                       (GHC.Char.hs_char__
                                                                                                       "*"))
                                                  else j_1__
             | _ => j_1__
           end
      else j_1__ in
    let j_3__ :=
      if andb (negb StaticFlags.opt_PprStyle_Debug) (Unique.hasKey tc
                                                                   PrelNames.errorMessageTypeErrorFamKey) : bool
      then id (GHC.Base.hs_string__ "(TypeError ...)")
      else j_2__ in
    let j_5__ :=
      if Unique.hasKey tc PrelNames.consDataConKey : bool
      then match tys with
             | cons _kind (cons ty1 (cons ty2 nil)) => Outputable.sdocWithDynFlags GHC.Base.$
                                                       (fun dflags =>
                                                         if DynFlags.gopt DynFlags.Opt_PrintExplicitKinds dflags : bool
                                                         then ppr_deflt
                                                         else pprTyList p ty1 ty2)
             | _ => j_3__
           end
      else j_3__ in
    if Unique.hasKey tc PrelNames.ipClassKey : bool
    then match tys with
           | cons (LitTy (StrTyLit n)) (cons ty nil) => maybeParen p FunPrec GHC.Base.$
                                                        (((Outputable.char (GHC.Char.hs_char__ "?") Outputable.<>
                                                        Outputable.ftext n) Outputable.<> id (GHC.Base.hs_string__
                                                                                             "::")) Outputable.<>
                                                        ppr_type TopPrec ty)
           | _ => j_5__
         end
    else j_5__.

Definition ppr_type : TyPrec -> Type_ -> Outputable.SDoc :=
  fix ppr_type arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , TyVarTy tv => ppr_tvar tv
             | p , TyConApp tc tys => pprTyTcApp p tc tys
             | p , LitTy l => ppr_tylit p l
             | p , (ForAllTy _ _ as ty) => ppr_forall_type p ty
             | p , AppTy t1 t2 => let mk_app_tys :=
                                    fun arg_6__ arg_7__ =>
                                      match arg_6__ , arg_7__ with
                                        | TyConApp tc tys1 , tys2 => TyConApp tc (Coq.Init.Datatypes.app tys1 tys2)
                                        | ty1 , tys2 => Data.Foldable.foldl AppTy ty1 tys2
                                      end in
                                  let split_app_tys :=
                                    fix split_app_tys arg_11__ arg_12__
                                          := match arg_11__ , arg_12__ with
                                               | AppTy ty1 ty2 , args => split_app_tys ty1 (cons ty2 args)
                                               | head , args => pair head args
                                             end in
                                  let ppr_app_ty :=
                                    maybeParen p TyConPrec GHC.Base.$ GHC.Base.mappend (ppr_type FunPrec t1)
                                                                                       (ppr_type TyConPrec t2) in
                                  if_print_coercions ppr_app_ty (let scrut_17__ :=
                                                                  split_app_tys t1 (cons t2 nil) in
                                                                match scrut_17__ with
                                                                  | pair (CastTy head _) args => ppr_type p (mk_app_tys
                                                                                                            head args)
                                                                  | _ => ppr_app_ty
                                                                end)
             | p , CastTy ty co => if_print_coercions (Outputable.parens (GHC.Base.mappend
                                                                         (GHC.Base.mappend (ppr_type TopPrec ty) (id
                                                                                           (GHC.Base.hs_string__ "|>")))
                                                                         (Panic.noString co))) (ppr_type p ty)
             | _ , CoercionTy co => if_print_coercions (Outputable.parens (Panic.noString
                                                                          co)) (id (GHC.Base.hs_string__ "<>"))
           end.

Definition ppr_forall_type : TyPrec -> Type_ -> Outputable.SDoc :=
  fun p ty =>
    maybeParen p FunPrec GHC.Base.$ (Outputable.sdocWithDynFlags GHC.Base.$
    (fun dflags => ppr_sigma_type dflags true ty)).

Definition ppr_sigma_type
    : DynFlags.DynFlags -> bool -> Type_ -> Outputable.SDoc :=
  fun arg_0__ arg_1__ arg_2__ =>
    let j_17__ :=
      match arg_0__ , arg_1__ , arg_2__ with
        | _ , _ , ty => let split2 :=
                          fix split2 arg_3__ arg_4__
                                := let j_6__ :=
                                     match arg_3__ , arg_4__ with
                                       | ps , ty => pair (GHC.List.reverse ps) ty
                                     end in
                                   match arg_3__ , arg_4__ with
                                     | ps , ForAllTy (Anon ty1) ty2 => if Type.isPredTy ty1 : bool
                                                                       then split2 (cons ty1 ps) ty2
                                                                       else j_6__
                                     | _ , _ => j_6__
                                   end in
                        let split1 :=
                          fix split1 arg_9__ arg_10__
                                := match arg_9__ , arg_10__ with
                                     | bndrs , ForAllTy (Named _ _ as bndr) ty => split1 (cons bndr bndrs) ty
                                     | bndrs , ty => pair (GHC.List.reverse bndrs) ty
                                   end in
                        match split1 nil ty with
                          | pair bndrs rho => match split2 nil rho with
                                                | pair ctxt tau => Outputable.sep (cons (pprForAll bndrs) (cons
                                                                                        (pprThetaArrowTy ctxt) (cons
                                                                                        (pprArrowChain TopPrec
                                                                                        (ppr_fun_tail tau)) nil)))
                                              end
                        end
      end in
    match arg_0__ , arg_1__ , arg_2__ with
      | dflags , false , orig_ty => let split :=
                                      fix split arg_18__ arg_19__
                                            := let j_21__ :=
                                                 match arg_18__ , arg_19__ with
                                                   | acc , ty => pair (GHC.List.reverse acc) ty
                                                 end in
                                               match arg_18__ , arg_19__ with
                                                 | acc , ForAllTy bndr ty => if isInvisibleBinder bndr : bool
                                                                             then split (cons bndr acc) ty
                                                                             else j_21__
                                                 | _ , _ => j_21__
                                               end in
                                    match split nil orig_ty with
                                      | pair invis_bndrs tau => match Data.OldList.partition isNamedBinder
                                                                        invis_bndrs with
                                                                  | pair named ctxt => if andb (negb (DynFlags.gopt
                                                                                                     DynFlags.Opt_PrintExplicitForalls
                                                                                                     dflags))
                                                                                               (Data.Foldable.all
                                                                                               (VarSet.isEmptyVarSet
                                                                                               GHC.Base.∘
                                                                                               (tyCoVarsOfType
                                                                                               GHC.Base.∘ binderType))
                                                                                               named) : bool
                                                                                       then Outputable.sep (cons
                                                                                                           (pprThetaArrowTy
                                                                                                           (GHC.Base.map
                                                                                                           binderType
                                                                                                           ctxt)) (cons
                                                                                                           (pprArrowChain
                                                                                                           TopPrec
                                                                                                           (ppr_fun_tail
                                                                                                           tau)) nil))
                                                                                       else j_17__
                                                                end
                                    end
      | _ , _ , _ => j_17__
    end.

Definition pprForAll : list TyBinder -> Outputable.SDoc :=
  fix pprForAll arg_0__
        := match arg_0__ with
             | nil => Outputable.empty
             | (cons (Named _ vis) _ as bndrs) => let add_separator :=
                                                    fun stuff =>
                                                      match vis with
                                                        | Visible => GHC.Base.mappend stuff Outputable.arrow
                                                        | _inv => stuff Outputable.<> Outputable.dot
                                                      end in
                                                  match ppr_tv_bndrs bndrs vis with
                                                    | pair bndrs' doc => GHC.Base.mappend (add_separator
                                                                                          (GHC.Base.mappend
                                                                                          Outputable.forAllLit doc))
                                                                                          (pprForAll bndrs')
                                                  end
             | bndrs => Panic.panicStr (GHC.Base.hs_string__ "pprForAll: anonymous binder")
                        (Panic.noString bndrs)
           end.

Definition ppr_tv_bndrs : list TyBinder -> VisibilityFlag -> (list TyBinder *
                          Outputable.SDoc)%type :=
  fix ppr_tv_bndrs arg_0__ arg_1__
        := let j_4__ :=
             match arg_0__ , arg_1__ with
               | nil , _ => pair nil Outputable.empty
               | bndrs , _ => Panic.panicStr (GHC.Base.hs_string__
                                             "ppr_tv_bndrs: anonymous binder") (Panic.noString bndrs)
             end in
           match arg_0__ , arg_1__ with
             | (cons (Named tv vis) bndrs as all_bndrs) , vis1 => let j_5__ :=
                                                                    pair all_bndrs Outputable.empty in
                                                                  if sameVis vis vis1 : bool
                                                                  then let pp_tv :=
                                                                         Outputable.sdocWithDynFlags GHC.Base.$
                                                                         (fun dflags =>
                                                                           if andb (Invisible GHC.Base.== vis)
                                                                                   (DynFlags.gopt
                                                                                   DynFlags.Opt_PrintExplicitForalls
                                                                                   dflags) : bool
                                                                           then Outputable.braces (pprTvBndrNoParens tv)
                                                                           else pprTvBndr tv) in
                                                                       match ppr_tv_bndrs bndrs vis1 with
                                                                         | pair bndrs' doc => pair bndrs'
                                                                                                   (GHC.Base.mappend
                                                                                                   pp_tv doc)
                                                                       end
                                                                  else j_5__
             | _ , _ => j_4__
           end.

Definition pprTvBndr : TyVar -> Outputable.SDoc :=
  fun tv =>
    let kind := Var.tyVarKind tv in
    let j_1__ :=
      Outputable.parens (GHC.Base.mappend (GHC.Base.mappend (ppr_tvar tv)
                                                            Outputable.dcolon) (pprKind kind)) in
    if isLiftedTypeKind kind : bool
    then ppr_tvar tv
    else j_1__.

Definition pprKind : Kind -> Outputable.SDoc :=
  pprType.

Definition pprType : Type_ -> Outputable.SDoc :=
  fun ty => eliminateRuntimeRep (ppr_type TopPrec) ty.

Definition pprTvBndrNoParens : TyVar -> Outputable.SDoc :=
  fun tv =>
    let kind := Var.tyVarKind tv in
    let j_1__ :=
      GHC.Base.mappend (GHC.Base.mappend (ppr_tvar tv) Outputable.dcolon) (pprKind
                       kind) in
    if isLiftedTypeKind kind : bool
    then ppr_tvar tv
    else j_1__.

Definition pprThetaArrowTy : ThetaType -> Outputable.SDoc :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Outputable.empty
      | cons pred nil => GHC.Base.mappend (ppr_type TyOpPrec pred) Outputable.darrow
      | preds => GHC.Base.mappend (Outputable.parens (Outputable.fsep
                                                     (Outputable.punctuate Outputable.comma (GHC.Base.map (ppr_type
                                                                                                          TopPrec)
                                                                                            preds)))) Outputable.darrow
    end.

Definition ppr_fun_tail : Type_ -> list Outputable.SDoc :=
  fix ppr_fun_tail arg_0__
        := let j_2__ :=
             match arg_0__ with
               | other_ty => cons (ppr_type TopPrec other_ty) nil
             end in
           match arg_0__ with
             | ForAllTy (Anon ty1) ty2 => if negb (Type.isPredTy ty1) : bool
                                          then cons (ppr_type FunPrec ty1) (ppr_fun_tail ty2)
                                          else j_2__
             | _ => j_2__
           end.

Definition pprTyList : TyPrec -> Type_ -> Type_ -> Outputable.SDoc :=
  fun p ty1 ty2 =>
    let gather : Type_ -> (list Type_ * option Type_)%type :=
      fix gather arg_0__
            := let j_2__ := match arg_0__ with | ty => pair nil (Some ty) end in
               match arg_0__ with
                 | TyConApp tc tys => let j_3__ :=
                                        if Unique.hasKey tc PrelNames.nilDataConKey : bool
                                        then pair nil None
                                        else j_2__ in
                                      if Unique.hasKey tc PrelNames.consDataConKey : bool
                                      then match tys with
                                             | cons _kind (cons ty1 (cons ty2 nil)) => match gather ty2 with
                                                                                         | pair args tl => pair (cons
                                                                                                                ty1
                                                                                                                args) tl
                                                                                       end
                                             | _ => j_3__
                                           end
                                      else j_3__
                 | _ => j_2__
               end in
    let scrut_6__ := gather ty2 in
    match scrut_6__ with
      | pair arg_tys None => Outputable.char (GHC.Char.hs_char__ "'") Outputable.<>
                             Outputable.brackets (Outputable.fsep (Outputable.punctuate Outputable.comma
                                                                  (GHC.Base.map (ppr_type TopPrec) (cons ty1 arg_tys))))
      | pair arg_tys (Some tl) => maybeParen p FunPrec GHC.Base.$ Outputable.hang
                                  (ppr_type FunPrec ty1) (GHC.Num.fromInteger 2) (Outputable.fsep
                                                                                 (Coq.Lists.List.flat_map (fun ty =>
                                                                                                            cons
                                                                                                            (GHC.Base.mappend
                                                                                                            Outputable.colon
                                                                                                            (ppr_type
                                                                                                            FunPrec ty))
                                                                                                            nil)
                                                                                                          (Coq.Init.Datatypes.app
                                                                                                          arg_tys (cons
                                                                                                          tl nil))))
    end.

Definition pprTvBndrs : list TyVar -> Outputable.SDoc :=
  fun tvs => Outputable.sep (GHC.Base.map pprTvBndr tvs).
*)

(* SCW: in GHC, the substitution continues into the kind of the type variable. *)

Definition substTyVarBndrCallback
    : (TCvSubst -> Type_ -> Type_) -> TCvSubst -> TyVar -> (TCvSubst * TyVar)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | subst_fn , (Mk_TCvSubst in_scope tenv cenv as subst) , old_var =>
        let old_ki :=
            Var.tyVarKind old_var in
        let no_kind_change :=
            VarSet.isEmptyVarSet (tyCoVarsOfType old_ki) in
        let new_var := VarEnv.uniqAway in_scope old_var in
(*            if no_kind_change : bool
            then VarEnv.uniqAway in_scope old_var
            else VarEnv.uniqAway in_scope GHC.Base.$
                                 setTyVarKind old_var (subst_fn subst  old_ki)  *)

        let no_change :=
            andb no_kind_change (new_var GHC.Base.== old_var) in
        let _no_capture :=
            negb (VarSet.elemVarSet new_var (tyCoVarsOfTypes (VarEnv.varEnvElts tenv))) in
        let new_env :=
            if no_change : bool
            then VarEnv.delVarEnv tenv old_var
            else VarEnv.extendVarEnv tenv old_var (TyVarTy new_var) in
        pair (Mk_TCvSubst (VarEnv.extendInScopeSet in_scope new_var) new_env cenv) new_var
    end.




Fixpoint subst_ty (subst : TCvSubst) (ty : Type_) { struct ty } : Type_ :=
       let go :=
             fix go arg_0__
                   := match arg_0__ with
                        | TyVarTy tv => substTyVar subst tv
                        | AppTy fun_ arg => Type_mkAppTy (go fun_) GHC.Base.$! (go arg)
                        | TyConApp tc tys => let args := GHC.Base.map go tys in
                                             Util.seqList args (TyConApp tc args)
                        | ForAllTy (Anon arg) res => (ForAllTy GHC.Base.$! (Anon GHC.Base.$! go arg))
                                                     GHC.Base.$! go res
                        | ForAllTy (Named tv vis) ty =>
                          let scrut_6__ :=
                              substTyVarBndrCallback
                                (fun subst ty =>
                                   if isEmptyTCvSubst subst : bool
                                   then ty
                                   else subst_ty subst ty)
                                subst tv in
                          match scrut_6__ with
                          | pair subst' tv' =>
                            (ForAllTy GHC.Base.$! ((Named GHC.Base.$!
                                                          tv') vis)) GHC.Base.$! (subst_ty subst' ty)
                          end
                        | LitTy n => LitTy GHC.Base.$! n
                        | CastTy ty co => (CastTy GHC.Base.$! (go ty)) GHC.Base.$! (subst_co subst co)
                        | CoercionTy co => CoercionTy GHC.Base.$! (subst_co subst co)
                      end in
           go ty
with subst_co (subst : TCvSubst) (co: Coercion) {struct co} : Coercion :=
        let go_ty : Type_ -> Type_ := subst_ty subst in
           let go : Coercion -> Coercion :=
             fix go arg_1__
                   :=  let go_prov :=
                   fun arg_24__ =>
                     match arg_24__ with
                     | UnsafeCoerceProv => UnsafeCoerceProv
                     | PhantomProv kco => PhantomProv (go kco)
                     | ProofIrrelProv kco => ProofIrrelProv (go kco)
                     | (PluginProv _ as p) => p
                     | (HoleProv _ as p) => p
                     end in

                     match arg_1__ with
                        | Refl r ty => mkReflCo r GHC.Base.$! go_ty ty
                        | TyConAppCo r tc args => let args' := GHC.Base.map go args in
                                                  Util.seqList args' (mkTyConAppCo r tc args')
                        | AppCo co arg => (mkAppCo GHC.Base.$! go co) GHC.Base.$! go arg
                        | ForAllCo tv kind_co co =>
                          let scrut_6__ :=
                              substForAllCoBndrCallback false (fun co =>
                                                                 if isEmptyTCvSubst subst : bool
                                                                 then co
                                                                 else subst_co subst co)
                                                        subst tv kind_co in
                          match scrut_6__ with
                          | pair (pair subst' tv') kind_co' =>
                            ((mkForAllCo
                                GHC.Base.$! tv') GHC.Base.$!
                                                 kind_co') GHC.Base.$!
                                                           subst_co subst' co
                          end
                        | CoVarCo cv => substCoVar subst cv
                        | AxiomInstCo con ind cos => mkAxiomInstCo con ind GHC.Base.$!
                                                     GHC.Base.map go cos
                        | UnivCo p r t1 t2 => (((mkUnivCo GHC.Base.$! go_prov p) GHC.Base.$! r)
                                              GHC.Base.$! (go_ty t1)) GHC.Base.$! (go_ty t2)
                        | SymCo co => mkSymCo GHC.Base.$! (go co)
                        | TransCo co1 co2 => (mkTransCo GHC.Base.$! (go co1)) GHC.Base.$! (go
                                             co2)
                        | NthCo d co => mkNthCo d GHC.Base.$! (go co)
                        | LRCo lr co => mkLRCo lr GHC.Base.$! (go co)
                        | InstCo co arg => (Coercion_mkInstCo GHC.Base.$! (go co)) GHC.Base.$! go arg
                        | CoherenceCo co1 co2 => (mkCoherenceCo GHC.Base.$! (go co1))
                                                 GHC.Base.$! (go co2)
                        | KindCo co => mkKindCo GHC.Base.$! (go co)
                        | SubCo co => mkSubCo GHC.Base.$! (go co)
                        | AxiomRuleCo c cs => let cs1 := GHC.Base.map go cs in
                                              Util.seqList cs1 (AxiomRuleCo c cs1)
                      end in
           go co.

Definition substCoUnchecked (subst : TCvSubst) (co: Coercion) : Coercion :=
    if isEmptyTCvSubst subst : bool
    then co
    else subst_co subst co.

Definition substTyUnchecked (subst : TCvSubst) (ty:Type_) : Type_ :=
    if isEmptyTCvSubst subst : bool
    then ty
    else subst_ty subst ty.


Definition substTyWithBindersUnchecked : list TyBinder -> list
                                         Type_ -> Type_ -> Type_ :=
  fun bndrs tys =>
    substTyUnchecked (zipTyBinderSubst bndrs tys).

(* SCW: removed `{H: (CallStack)} *)
Definition substCo  : TCvSubst -> Coercion -> Coercion :=
  fun subst co =>
    if isEmptyTCvSubst subst : bool
    then co
    else checkValidSubst subst nil (cons co nil) GHC.Base.$ subst_co subst co.

Definition substForAllCoBndr : TCvSubst -> TyVar -> Coercion -> (TCvSubst *
                               TyVar * Coercion)%type :=
  fun subst => substForAllCoBndrCallback false (substCo subst) subst.

(* `{(CallStack)} *)
Definition substCos  : TCvSubst -> list Coercion -> list
                                     Coercion :=
  fun subst cos =>
    let j_0__ :=
      checkValidSubst subst nil cos GHC.Base.$ GHC.Base.map (subst_co subst) cos in
    if isEmptyTCvSubst subst : bool
    then cos
    else j_0__.

(* `{(CallStack)} *)
Definition substTy  : TCvSubst -> Type_ -> Type_ :=
  fun subst ty =>
    let j_0__ :=
      checkValidSubst subst (cons ty nil) nil GHC.Base.$ subst_ty subst ty in
    if isEmptyTCvSubst subst : bool
    then ty
    else j_0__.


Definition Type_coreView : Core.Type_ -> option Core.Type_ :=
  fun arg_0__ =>
    match arg_0__ with
      | Core.TyConApp tc tys =>
        match TyCon.expandSynTyCon_maybe tc tys with
        | Some (pair (pair tenv rhs) tys') =>
          Some (Type_mkAppTys (substTy (mkTvSubstPrs tenv) rhs) tys')
        | _ => None
        end
      | _ => None
    end.

Parameter isLiftedTypeKind : Kind -> bool.
(*
Definition isLiftedTypeKind : Kind -> bool :=
  fix isLiftedTypeKind arg_0__
        := let j_2__ :=
             match arg_0__ with
               | TyConApp tc (cons (TyConApp ptr_rep nil) nil) => andb (Unique.hasKey tc
                                                                                      PrelNames.tYPETyConKey)
                                                                       (Unique.hasKey ptr_rep
                                                                                      PrelNames.ptrRepLiftedDataConKey)
               | _ => false
             end in
           match arg_0__ with
             | ki => match Type_coreView ki with
                       | Some ki' => isLiftedTypeKind ki'
                       | _ => j_2__
                     end
           end. *)


Parameter  isRuntimeRepTy : Type_ -> bool.
(*
Definition isRuntimeRepTy : Type_ -> bool :=
  fix isRuntimeRepTy arg_0__
        := let j_2__ :=
             match arg_0__ with
               | TyConApp tc nil => Unique.hasKey tc PrelNames.runtimeRepTyConKey
               | _ => false
             end in
           match arg_0__ with
             | ty => match Type_coreView ty with
                       | Some ty' => isRuntimeRepTy ty'
                       | _ => j_2__
                     end
           end. *)

Definition isRuntimeRepVar : TyVar -> bool :=
  isRuntimeRepTy GHC.Base.∘ Var.tyVarKind.

Definition isRuntimeRepKindedTy : Type_ -> bool :=
  isRuntimeRepTy GHC.Base.∘ Type_typeKind.

Definition dropRuntimeRepArgs : list Type_ -> list Type_ :=
  GHC.List.dropWhile isRuntimeRepKindedTy.


Definition cloneTyVarBndr : TCvSubst -> TyVar -> Unique.Unique -> (TCvSubst
                            * TyVar)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | (Mk_TCvSubst in_scope tv_env cv_env as subst) , tv , uniq => let old_ki :=
                                                                    Var.tyVarKind tv in
                                                                  let no_kind_change :=
                                                                    VarSet.isEmptyVarSet (tyCoVarsOfType old_ki) in
                                                                  let tv1 :=
                                                                    let j_5__ :=
                                                                      Var.setTyVarKind tv (substTy subst old_ki) in
                                                                    if no_kind_change : bool
                                                                    then tv
                                                                    else j_5__ in
                                                                  let tv' := Var.setVarUnique tv1 uniq in
                                                                   pair (Mk_TCvSubst (VarEnv.extendInScopeSet in_scope
                                                                                      tv') (VarEnv.extendVarEnv tv_env
                                                                                           tv (mkTyVarTy tv')) cv_env)
                                                                            tv'
    end.

Definition cloneTyVarBndrs : TCvSubst -> list
                             TyVar -> UniqSupply.UniqSupply -> (TCvSubst * list TyVar)%type :=
  fix cloneTyVarBndrs arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | subst , nil , _usupply => pair subst nil
             | subst , cons t ts , usupply => match UniqSupply.takeUniqFromSupply
                                                      usupply with
                                                | pair uniq usupply' => match cloneTyVarBndr subst t uniq with
                                                                          | pair subst' tv => match cloneTyVarBndrs
                                                                                                      subst' ts
                                                                                                      usupply' with
                                                                                                | pair subst'' tvs =>
                                                                                                  pair subst'' (cons tv
                                                                                                                     tvs)
                                                                                              end
                                                                        end
                                              end
           end.

Definition substCoVarBndr : TCvSubst -> CoVar -> (TCvSubst *
                            CoVar)%type :=
  substCoVarBndrCallback false substTy.

Definition substTyAddInScope : TCvSubst -> Type_ -> Type_ :=
  fun subst ty =>
    substTy (extendTCvInScopeSet subst GHC.Base.$ tyCoVarsOfType ty) ty.

(*  `{(CallStack)} *)
Definition substTyWithBinders : list TyBinder -> list
                                               Type_ -> Type_ -> Type_ :=
  fun bndrs tys =>
    substTy (zipTyBinderSubst bndrs tys).

Definition composeTCvSubstEnv : VarEnv.InScopeSet -> (TvSubstEnv *
                                CvSubstEnv)%type -> (TvSubstEnv * CvSubstEnv)%type -> (TvSubstEnv *
                                CvSubstEnv)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | in_scope , pair tenv1 cenv1 , pair tenv2 cenv2 => let subst1 :=
                                                            Mk_TCvSubst in_scope tenv1 cenv1 in
                                                          pair (VarEnv.plusVarEnv tenv1 (VarEnv.mapVarEnv (substTy
                                                                                                          subst1)
                                                                                  tenv2)) (VarEnv.plusVarEnv cenv1
                                                                                                             (VarEnv.mapVarEnv
                                                                                                             (substCo
                                                                                                             subst1)
                                                                                                             cenv2))
    end.

Definition composeTCvSubst : TCvSubst -> TCvSubst -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst is1 tenv1 cenv1 , Mk_TCvSubst is2 tenv2 cenv2 => let is3 :=
                                                                 VarEnv.unionInScope is1 is2 in
                                                               match composeTCvSubstEnv is3 (pair tenv1 cenv1) (pair
                                                                                                               tenv2
                                                                                                               cenv2) with
                                                                 | pair tenv3 cenv3 => Mk_TCvSubst is3 tenv3 cenv3
                                                               end
    end.

(* `{(CallStack)}  *)
Definition substTys : TCvSubst -> list Type_ -> list Type_ :=
  fun subst tys =>
    let j_0__ :=
      checkValidSubst subst tys nil GHC.Base.$ GHC.Base.map (subst_ty subst) tys in
    if isEmptyTCvSubst subst : bool
    then tys
    else j_0__.

(* `{(CallStack)} *)
Definition substTheta  : TCvSubst -> ThetaType -> ThetaType :=
  substTys.

Definition substTysUnchecked : TCvSubst -> list Type_ -> list Type_ :=
  fun subst tys =>
    let j_0__ := GHC.Base.map (subst_ty subst) tys in
    if isEmptyTCvSubst subst : bool
    then tys
    else j_0__.

Definition substThetaUnchecked : TCvSubst -> ThetaType -> ThetaType :=
  substTysUnchecked.

(* `{(CallStack)} *)
Definition substTyVarBndr : TCvSubst -> TyVar -> (TCvSubst * TyVar)%type :=
  substTyVarBndrCallback substTy.

(*
Definition pprForAllImplicit : list TyVar -> Outputable.SDoc :=
  fun tvs => pprForAll (GHC.List.zipWith Named tvs (GHC.List.repeat Specified)).

Definition pprUserForAll : list TyBinder -> Outputable.SDoc :=
  fun bndrs =>
    let bndr_has_kind_var :=
      fun bndr => negb (VarSet.isEmptyVarSet (tyCoVarsOfType (binderType bndr))) in
    Outputable.sdocWithDynFlags GHC.Base.$ (fun dflags =>
      Outputable.ppWhen (orb (Data.Foldable.any bndr_has_kind_var bndrs)
                             (DynFlags.gopt DynFlags.Opt_PrintExplicitForalls dflags)) GHC.Base.$ pprForAll
      bndrs).

Definition pprSigmaType : Type_ -> Outputable.SDoc :=
  fun ty =>
    Outputable.sdocWithDynFlags GHC.Base.$ (fun dflags =>
      eliminateRuntimeRep (ppr_sigma_type dflags false) ty).

Definition pprParendType : Type_ -> Outputable.SDoc :=
  fun ty => eliminateRuntimeRep (ppr_type TyConPrec) ty.

Definition pprParendKind : Kind -> Outputable.SDoc :=
  pprParendType.

Definition pprDataConWithArgs : DataCon.DataCon -> Outputable.SDoc :=
  fun dc =>
    let ex_bndrs := DataCon.dataConExTyBinders dc in
    let univ_bndrs := DataCon.dataConUnivTyBinders dc in
    match DataCon.dataConFullSig dc with
      | pair (pair (pair (pair (pair _univ_tvs _ex_tvs) eq_spec) theta) arg_tys)
             _res_ty => let forAllDoc :=
                          pprUserForAll GHC.Base.$ (Coq.Init.Datatypes.app (DataCon.filterEqSpec eq_spec
                                                                           univ_bndrs) ex_bndrs) in
                        let thetaDoc := pprThetaArrowTy theta in
                        let argsDoc := Outputable.hsep (GHC.Base.fmap pprParendType arg_tys) in
                        Outputable.sep (cons forAllDoc (cons thetaDoc (cons (GHC.Base.mappend
                                                                            (Panic.noString dc) argsDoc) nil)))
    end.

Definition pprDataCons : TyCon.TyCon -> Outputable.SDoc :=
  let sepWithVBars :=
    fun arg_0__ =>
      match arg_0__ with
        | nil => Outputable.empty
        | docs => Outputable.sep (Outputable.punctuate (Outputable.space Outputable.<>
                                                       Outputable.vbar) docs)
      end in
  sepWithVBars GHC.Base.∘ (GHC.Base.fmap pprDataConWithArgs GHC.Base.∘
  TyCon.tyConDataCons).

Definition pprTheta : ThetaType -> Outputable.SDoc :=
  fun arg_0__ =>
    match arg_0__ with
      | cons pred nil => ppr_type TopPrec pred
      | theta => Outputable.parens (Outputable.sep (Outputable.punctuate
                                                   Outputable.comma (GHC.Base.map (ppr_type TopPrec) theta)))
    end.

Definition pprTypeApp : TyCon.TyCon -> list Type_ -> Outputable.SDoc :=
  fun tc tys => pprTyTcApp TopPrec tc tys.

Definition pprClassPred : Class.Class -> list Type_ -> Outputable.SDoc :=
  fun clas tys => pprTypeApp (classTyCon clas) tys.
*)

Definition  tidyTyCoVarBndr
            (arg_0__ : VarEnv.TidyEnv)
            (tyvar : Var.TyCoVar)  : (VarEnv.TidyEnv * Var.TyCoVar)%type :=
    match arg_0__  with
      | (pair occ_env subst as tidy_env) =>
        let name := Var.tyVarName tyvar in
        let occ := Name.getOccName name in
        let occ1 := if Name.isSystemName name : bool
                    then if Var.isTyVar tyvar : bool
                         then OccName.mkTyVarOcc (Coq.Init.Datatypes.app
                                                    (OccName.occNameString occ)
                                                    (GHC.Base.hs_string__ "0"))
                         else OccName.mkVarOcc (Coq.Init.Datatypes.app
                                                  (OccName.occNameString occ)
                                                  (GHC.Base.hs_string__ "0"))
                    else occ in
        let scrut_5__ := OccName.tidyOccName occ_env occ1 in
        match scrut_5__ with
        | pair tidy' occ' => let kind'  := Var.tyVarKind tyvar (* tidyType tidy_env (tyVarKind tyvar)*) in
                            let name'  := Name.tidyNameOcc name occ' in
                            let tyvar' := Var.setTyVarKind (Var.setTyVarName tyvar name') kind' in
                            let subst' := VarEnv.extendVarEnv subst tyvar tyvar' in
                            pair (pair tidy' subst') tyvar'
        end
    end.

Definition tidyTyVarOcc (arg_0__ : VarEnv.TidyEnv) (tv: TyVar) : TyVar :=
  match arg_0__ with
  | (pair _ subst as env) =>
    let scrut_2__ := VarEnv.lookupVarEnv subst tv in
    match scrut_2__ with
    | None => tv (* updateTyVarKind (tidyType env) tv *)
    | Some tv' => tv'
    end
  end.

Fixpoint tidyCo (arg_0__ : VarEnv.TidyEnv) (co : Coercion) {struct co} : Coercion :=
        match arg_0__ with
             | (pair _ subst as env) =>
               let go :=
                   fix go arg_2__ :=
                       let go_prov :=
                           fun arg_28__ =>
                             match arg_28__ with
                             | UnsafeCoerceProv => UnsafeCoerceProv
                             | PhantomProv co => PhantomProv (go co)
                             | ProofIrrelProv co => ProofIrrelProv (go co)
                             | (PluginProv _ as p) => p
                             | (HoleProv _ as p) => p
                             end in

                     match arg_2__ with
                        | Refl r ty => Refl r (tidyType env ty)
                        | TyConAppCo r tc cos => let args := GHC.Base.map go cos in
                                                Util.seqList args (TyConAppCo r tc
                                                                              args)
                        | AppCo co1 co2 => (AppCo GHC.Base.$! go co1) GHC.Base.$! go
                                                                     co2
                        | ForAllCo tv h co => match tidyTyCoVarBndr env tv with
                                             | pair envp tvp => ((ForAllCo
                                                                   GHC.Base.$! tvp)
                                                                  GHC.Base.$! (go h))
                                                                 GHC.Base.$! (tidyCo
                                                                                envp co)
                                             end
                        | CoVarCo cv => let scrut_9__ :=
                                           VarEnv.lookupVarEnv subst cv in
                                       match scrut_9__ with
                                       | None => CoVarCo cv
                                       | Some cv' => CoVarCo cv'
                                       end
                        | AxiomInstCo con ind cos => let args :=
                                                        GHC.Base.map go cos in
                                                    Util.seqList args (AxiomInstCo
                                                                         con ind args)
                        | UnivCo p r t1 t2 => (((UnivCo GHC.Base.$! (go_prov p))
                                                 GHC.Base.$! r) GHC.Base.$! tidyType env
                                                                t1) GHC.Base.$! tidyType env t2
                        | SymCo co => SymCo GHC.Base.$! go co
                        | TransCo co1 co2 => (TransCo GHC.Base.$! go co1) GHC.Base.$!
                                                                         go co2
                        | NthCo d co => NthCo d GHC.Base.$! go co
                        | LRCo lr co => LRCo lr GHC.Base.$! go co
                        | InstCo co ty => (InstCo GHC.Base.$! go co) GHC.Base.$! go ty
                        | CoherenceCo co1 co2 => (CoherenceCo GHC.Base.$! go co1)
                                                  GHC.Base.$! go co2
                        | KindCo co => KindCo GHC.Base.$! go co
                        | SubCo co => SubCo GHC.Base.$! go co
                        | AxiomRuleCo ax cos => let cos1 := (fun env => GHC.Base.map (tidyCo env)) env cos in
                                               Util.seqList cos1 (AxiomRuleCo ax
                                                                              cos1)
                        end in
               go co
           end
with tidyType (arg_0__ : VarEnv.TidyEnv) (arg_1__ : Type_) {struct arg_1__} : Type_
        := match arg_0__ , arg_1__ with
             | _ , LitTy n => LitTy n
             | env , TyVarTy tv => TyVarTy (tidyTyVarOcc env tv)
             | env , TyConApp tycon tys => let args := GHC.Base.map (tidyType env) tys
                                                      in
                                           Util.seqList args (TyConApp tycon args)
             | env , AppTy fun_ arg => (AppTy GHC.Base.$! (tidyType env fun_)) GHC.Base.$!
                                       (tidyType env arg)
             | env , ForAllTy (Anon fun_) arg => (ForAllTy GHC.Base.$! (Anon GHC.Base.$!
                                                 (tidyType env fun_))) GHC.Base.$! (tidyType env arg)
             | env , ForAllTy (Named tv vis) ty => match tidyTyCoVarBndr env tv with
                                                     | pair envp tvp => (ForAllTy GHC.Base.$! ((Named GHC.Base.$! tvp)
                                                                        GHC.Base.$! vis)) GHC.Base.$! (tidyType envp ty)
                                                   end
             | env , CastTy ty co => (CastTy GHC.Base.$! tidyType env ty) GHC.Base.$! (tidyCo
                                     env co)
             | env , CoercionTy co => CoercionTy GHC.Base.$! (tidyCo env co)
           end.

Definition tidyCos : VarEnv.TidyEnv -> list Coercion -> list Coercion :=
  fun env => GHC.Base.map (tidyCo env).
Definition tidyKind : VarEnv.TidyEnv -> Kind -> Kind :=
  tidyType.


Definition tidyTypes : VarEnv.TidyEnv -> list Type_ -> list Type_ :=
  fun env tys => GHC.Base.map (tidyType env) tys.

Definition tidyTyCoVarBndrs : VarEnv.TidyEnv -> list
                              Var.TyCoVar -> (VarEnv.TidyEnv * list Var.TyCoVar)%type :=
  fun env tvs => Data.Traversable.mapAccumL tidyTyCoVarBndr env tvs.

Definition tidyOpenTyCoVar (arg_0__ : VarEnv.TidyEnv) (tyvar: Var.TyCoVar) :
  (VarEnv.TidyEnv * Var.TyCoVar)%type :=
    match arg_0__  with
      | (pair _ subst as env) =>
        match (VarEnv.lookupVarEnv subst tyvar) with
        | Some tyvar' => pair env tyvar'
        | None => let env' := env in
(*                     tidyFreeTyCoVars env (tyCoVarsOfTypeList (tyVarKind tyvar)) in *)
                 tidyTyCoVarBndr env' tyvar
        end
    end.
Definition tidyFreeTyCoVars (arg_0__ : VarEnv.TidyEnv)
                      (tyvars : list Var.TyCoVar) : VarEnv.TidyEnv :=
    match arg_0__ with
      | pair full_occ_env var_env  =>
        Data.Tuple.fst (Data.Traversable.mapAccumL tidyOpenTyCoVar (pair full_occ_env var_env) tyvars)
    end.

Definition tidyOpenTyCoVars : VarEnv.TidyEnv -> list
                              Var.TyCoVar -> (VarEnv.TidyEnv * list Var.TyCoVar)%type :=
  fun env tyvars => Data.Traversable.mapAccumL tidyOpenTyCoVar env tyvars.


Definition tidyOpenTypes : VarEnv.TidyEnv -> list Type_ -> (VarEnv.TidyEnv * list Type_)%type :=
  fun env tys =>
    match tidyOpenTyCoVars env GHC.Base.$ Type_tyCoVarsOfTypesWellScoped tys with
      | pair (pair _ var_env as env') tvs' =>
        let trimmed_occ_env :=
            OccName.initTidyOccEnv (GHC.Base.map Name.getOccName tvs') in
        pair env' (tidyTypes (pair trimmed_occ_env var_env) tys)
    end.

Definition tidyOpenType : VarEnv.TidyEnv -> Type_ -> (VarEnv.TidyEnv * Type_)%type :=
  fun env ty =>
    match tidyOpenTypes env (cons ty nil) with
      | pair env' (cons ty' nil) => pair env' ty'
      | _ => Panic.panic (GHC.Base.hs_string__ "impossible")
    end.

Definition tidyOpenKind : VarEnv.TidyEnv -> Kind -> (VarEnv.TidyEnv *
                          Kind)%type :=
  tidyOpenType.

Definition tidyTopType : Type_ -> Type_ :=
  fun ty => tidyType VarEnv.emptyTidyEnv ty.

Definition tidyTyBinder : VarEnv.TidyEnv -> TyBinder -> (VarEnv.TidyEnv *
                          TyBinder)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | tidy_env , Named tv vis => match tidyTyCoVarBndr tidy_env tv with
                                     | pair tidy_env' tv' => pair tidy_env' (Named tv' vis)
                                   end
      | tidy_env , Anon ty => pair tidy_env (Anon GHC.Base.$ tidyType tidy_env ty)
    end.

Definition tidyTyBinders : VarEnv.TidyEnv -> list TyBinder -> (VarEnv.TidyEnv *
                           list TyBinder)%type :=
  Data.Traversable.mapAccumL tidyTyBinder.

Definition unionTCvSubst : TCvSubst -> TCvSubst -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TCvSubst in_scope1 tenv1 cenv1 , Mk_TCvSubst in_scope2 tenv2 cenv2 => if andb
                                                                              Util.debugIsOn (negb (andb (negb
                                                                                                         (VarEnv.intersectsVarEnv
                                                                                                         tenv1 tenv2))
                                                                                                         (negb
                                                                                                         (VarEnv.intersectsVarEnv
                                                                                                         cenv1
                                                                                                         cenv2)))) : bool
                                                                           then (Panic.assertPanic (GHC.Base.hs_string__
                                                                                                   "ghc/compiler/types/TyCoRep.hs")
                                                                                (GHC.Num.fromInteger 1758))
                                                                           else Mk_TCvSubst (VarEnv.unionInScope in_scope1
                                                                                                              in_scope2)
                                                                                (VarEnv.plusVarEnv tenv1 tenv2)
                                                                                (VarEnv.plusVarEnv cenv1 cenv2)
    end.

Definition zapTCvSubst : TCvSubst -> TCvSubst :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_TCvSubst in_scope _ _ => Mk_TCvSubst in_scope VarEnv.emptyVarEnv
                                 VarEnv.emptyVarEnv
    end.

Definition zipCoEnv : list CoVar -> list Coercion -> CvSubstEnv :=
  fun cvs cos =>
    VarEnv.mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipCoEnv") cvs cos).

Definition zipCvSubst : list CoVar -> list Coercion -> TCvSubst :=
  fun cvs cos =>
    let cenv := zipCoEnv cvs cos in
    Mk_TCvSubst (VarEnv.mkInScopeSet (tyCoVarsOfCos cos)) emptyTvSubstEnv cenv.

Definition substTyWithCoVars : list CoVar -> list
                               Coercion -> Type_ -> Type_ :=
  fun cvs cos => substTy (zipCvSubst cvs cos).

Definition substTysWithCoVars : list CoVar -> list Coercion -> list
                                Type_ -> list Type_ :=
  fun cvs cos =>
    if andb Util.debugIsOn (negb (Data.Foldable.length cvs GHC.Base.==
                                 Data.Foldable.length cos)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
         (GHC.Num.fromInteger 1959))
    else substTys (zipCvSubst cvs cos).

Definition zipTyEnv : list TyVar -> list Type_ -> TvSubstEnv :=
  fun tyvars tys =>
     VarEnv.mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipTyEnv") tyvars
                         tys).

Definition zipTvSubst : list TyVar -> list Type_ -> TCvSubst :=
  fun tvs tys =>
    let tenv := zipTyEnv tvs tys in
    let j_1__ := mkTvSubst (VarEnv.mkInScopeSet (tyCoVarsOfTypes tys)) tenv in
    j_1__.

Definition substTyWith `{(CallStack)} : list TyVar -> list
                                        Type_ -> Type_ -> Type_ :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                 Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
         (GHC.Num.fromInteger 1903))
    else substTy (zipTvSubst tvs tys).

Definition substTyWithUnchecked : list TyVar -> list
                                  Type_ -> Type_ -> Type_ :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                 Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
         (GHC.Num.fromInteger 1913))
    else substTyUnchecked (zipTvSubst tvs tys).

Definition substTysWith : list TyVar -> list Type_ -> list Type_ -> list
                          Type_ :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                 Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
         (GHC.Num.fromInteger 1954))
    else substTys (zipTvSubst tvs tys).

Definition substCoWith : list TyVar -> list
                                        Type_ -> Coercion -> Coercion :=
  fun tvs tys =>
    substCo (zipTvSubst tvs tys).

Definition substCoWithUnchecked : list TyVar -> list
                                  Type_ -> Coercion -> Coercion :=
  fun tvs tys =>
     substCoUnchecked (zipTvSubst tvs tys).

Definition substTyWithInScope : VarEnv.InScopeSet -> list TyVar -> list
                                Type_ -> Type_ -> Type_ :=
  fun in_scope tvs tys ty =>
    let tenv := zipTyEnv tvs tys in
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                 Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
         (GHC.Num.fromInteger 1922))
    else substTy (mkTvSubst in_scope tenv) ty.

(* Unbound variables:
     CallStack CoercionN Eq Gt KindCoercion KindOrType Lt None Some andb bool
     classTyCon coVarsOfCo coVarsOfCos coVarsOfProv coVarsOfTypes comparison cons
     false go_prov id list negb nil op_zt__ option orb pFst pair pprForAll pprKind
     pprThetaArrowTy pprTvBndr pprTvBndrNoParens pprTyList pprType ppr_forall_type
     ppr_fun_tail ppr_sigma_type ppr_tv_bndrs ppr_type substCoUnchecked
     substForAllCoBndrUnchecked substTyUnchecked subst_co subst_ty tidyCos
     tidyFreeTyCoVars tidyKind tidyOpenTyCoVars tidyTyCoVarBndr tidyTyVarOcc tidyType
     tidyTypes true tyCoFVsOfCo tyCoFVsOfCos tyCoFVsOfProv tyCoFVsOfType
     tyCoFVsOfTypes tyConArity tyConName varName varType BasicTypes.ConstraintTuple
     BasicTypes.TupleSort BasicTypes.UnboxedTuple BasicTypes.tupleParens
     Class.Class BranchIndex Branched CoAxiom
     CoAxiomRule Role Coercion.coVarKindsTypesRole
     Coercion.coercionKind Coercion.isReflCo Coercion.mkAppCo Coercion.mkAxiomInstCo
     Coercion.mkCoVarCo Coercion.mkCoercionType Coercion.mkCoherenceCo
     Coercion.mkForAllCo Coercion.mkInstCo Coercion.mkKindCo Coercion.mkLRCo
     Coercion.mkNthCo Coercion.mkReflCo Coercion.mkSubCo Coercion.mkSymCo
     Coercion.mkTransCo Coercion.mkTyConAppCo Coercion.mkUnivCo ConLike.ConLike
     ConLike.PatSynCon ConLike.RealDataCon Coq.Init.Datatypes.app
     Coq.Lists.List.flat_map Data.Foldable.all Data.Foldable.and Data.Foldable.any
     Data.Foldable.foldl Data.Foldable.foldr Data.Foldable.length Data.Foldable.null
     Data.OldList.partition Data.Traversable.mapAccumL Data.Tuple.fst Data.Tuple.snd
     Data.Tuple.uncurry DataCon.DataCon DataCon.dataConExTyBinders
     DataCon.dataConFullSig DataCon.dataConTyCon DataCon.dataConUnivTyBinders
     DataCon.filterEqSpec Deriving.op_zdcon2tagzuFe4fHaknkFc7AP9msRFEWZZ__
     DynFlags.DynFlags DynFlags.Opt_PrintEqualityRelations
     DynFlags.Opt_PrintExplicitCoercions DynFlags.Opt_PrintExplicitForalls
     DynFlags.Opt_PrintExplicitKinds DynFlags.Opt_PrintExplicitRuntimeReps
     DynFlags.gopt FV.FV FV.delFV FV.emptyFV FV.fvDVarSet FV.fvVarList FV.fvVarSet
     FV.mapUnionFV FV.mkFVs FV.unionFV FV.unitFV FastString.FastString GHC.Base.Eq_
     GHC.Base.Ord GHC.Base.String GHC.Base.Synonym GHC.Base.compare GHC.Base.fmap
     GHC.Base.id GHC.Base.map GHC.Base.mappend GHC.Base.op_z2218U__ GHC.Base.op_zd__
     GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.IORef.IORef
     GHC.List.drop GHC.List.dropWhile GHC.List.repeat GHC.List.reverse GHC.List.zip
     GHC.List.zipWith GHC.Num.Int GHC.Num.Integer GHC.Prim.op_tagToEnumzh__
     GHC.Prim.op_zezezh__ GHC.Prim.op_zgzezh__ GHC.Prim.op_zgzh__
     GHC.Prim.op_zlzezh__ GHC.Prim.op_zlzh__ GHC.Real.div GHC.Show.show Name.getName
     Name.getOccName Name.isSystemName Name.nameOccName Name.tidyNameOcc
     OccName.initTidyOccEnv OccName.isSymOcc OccName.mkTyVarOcc OccName.mkVarOcc
     OccName.occNameString OccName.parenSymOcc OccName.tidyOccName
     Outputable.PprStyle Outputable.SDoc Outputable.arrow Outputable.assertPprPanic
     Outputable.braces Outputable.brackets Outputable.char Outputable.colon
     Outputable.comma Outputable.darrow Outputable.dcolon Outputable.debugStyle
     Outputable.dot Outputable.dumpStyle Outputable.empty Outputable.forAllLit
     Outputable.fsep Outputable.ftext Outputable.getPprStyle Outputable.hang
     Outputable.hsep Outputable.integer Outputable.op_zdzd__ Outputable.op_zlzg__
     Outputable.paBrackets Outputable.parens Outputable.ppWhen Outputable.pprInfixVar
     Outputable.pprTrace Outputable.pprWithCommas Outputable.punctuate
     Outputable.quotes Outputable.sdocWithDynFlags Outputable.sep Outputable.space
     Outputable.unicodeSyntax Outputable.vbar Pair.Mk_Pair Panic.assertPanic
     Panic.noString Panic.panicStr PrelNames.consDataConKey PrelNames.eqPrimTyConKey
     PrelNames.eqReprPrimTyConKey PrelNames.eqTyConKey
     PrelNames.errorMessageTypeErrorFamKey PrelNames.heqTyConKey PrelNames.ipClassKey
     PrelNames.listTyConKey PrelNames.nilDataConKey PrelNames.parrTyConKey
     PrelNames.ptrRepLiftedDataConKey PrelNames.ptrRepUnliftedDataConKey
     PrelNames.runtimeRepTyConKey PrelNames.starKindTyConKey PrelNames.tYPETyConKey
     PrelNames.unicodeStarKindTyConKey PrelNames.unliftedTypeKindTyConKey
     StaticFlags.opt_PprStyle_Debug TyCon.TyCon TyCon.isClassTyCon
     TyCon.isPromotedDataCon_maybe TyCon.pprPromotionQuote TyCon.tyConDataCons
     TyCon.tyConTuple_maybe Type.coreView Type.eqType Type.isCoercionTy Type.isPredTy
     Type.mkAppTy Type.partitionInvisibles Type.tyCoVarsOfTypesWellScoped
     Type.typeKind UniqFM.delListFromUFM_Directly UniqSupply.UniqSupply
     UniqSupply.takeUniqFromSupply Unique.Unique Unique.hasKey Util.debugIsOn
     Util.foldl2 Util.lengthIs Util.seqList Util.zipEqual CoVar Var.Id
     Var.TyCoVar TyVar Var.Var Var.isCoVar Var.isTyVar Var.mkCoVar
     Var.setTyVarKind Var.setTyVarName Var.setVarUnique Var.tyVarKind Var.tyVarName
     Var.updateTyVarKind VarEnv.CoVarEnv VarEnv.InScopeSet VarEnv.TidyEnv
     VarEnv.TyVarEnv VarEnv.delVarEnv VarEnv.elemInScopeSet VarEnv.elemVarEnv
     VarEnv.emptyInScopeSet VarEnv.emptyTidyEnv VarEnv.emptyVarEnv
     VarEnv.extendInScopeSet VarEnv.extendInScopeSetList VarEnv.extendInScopeSetSet
     VarEnv.extendVarEnv VarEnv.intersectsVarEnv VarEnv.isEmptyVarEnv
     VarEnv.lookupVarEnv VarEnv.mapVarEnv VarEnv.mkInScopeSet VarEnv.mkVarEnv
     VarEnv.plusVarEnv VarEnv.unionInScope VarEnv.uniqAway VarEnv.varEnvElts
     VarEnv.varEnvKeys VarEnv.varSetInScope VarSet.CoVarSet VarSet.DTyCoVarSet
     VarSet.DTyVarSet VarSet.TyCoVarSet VarSet.TyVarSet VarSet.VarSet
     VarSet.dVarSetElems VarSet.delVarSet VarSet.elemVarSet VarSet.emptyVarSet
     VarSet.extendVarSet VarSet.isEmptyVarSet VarSet.mapUnionVarSet
     VarSet.unionVarSet VarSet.unitVarSet VarSet.varSetElems
*)
