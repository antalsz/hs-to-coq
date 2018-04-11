(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require BooleanFormula.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require GHC.Base.
Require GHC.Err.
Require IdInfo.
Require Name.
Require OccName.
Require SrcLoc.
Require Unique.
Require Var.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition FunDep a :=
  (list a * list a)%type%type.

Definition DefMethInfo :=
  (option (Name.Name * BasicTypes.DefMethSpec unit)%type)%type.

Definition ClassOpItem :=
  (Var.Id * DefMethInfo)%type%type.

Definition ClassMinimalDef :=
  (BooleanFormula.BooleanFormula Name.Name)%type.

Inductive ClassATItem : Type
  := ATI : IdInfo.TyConId -> (option (unit * SrcLoc.SrcSpan)%type) -> ClassATItem.

Inductive ClassBody : Type
  := AbstractClass : ClassBody
  |  ConcreteClass
   : list unit ->
     list Var.Id ->
     list ClassATItem -> list ClassOpItem -> ClassMinimalDef -> ClassBody.

Inductive Class : Type
  := Mk_Class
   : IdInfo.TyConId ->
     Name.Name ->
     Unique.Unique ->
     list Var.TyVar -> list (FunDep Var.TyVar) -> ClassBody -> Class.

Instance Default__ClassBody : GHC.Err.Default ClassBody :=
  GHC.Err.Build_Default _ AbstractClass.

Definition classATStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classATStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ classATStuff _ _ => classATStuff
  end.

Definition classMinimalDefStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classMinimalDefStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ _ _ classMinimalDefStuff => classMinimalDefStuff
  end.

Definition classOpStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classOpStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ _ classOpStuff _ => classOpStuff
  end.

Definition classSCSels (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classSCSels' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ classSCSels _ _ _ => classSCSels
  end.

Definition classSCThetaStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classSCThetaStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass classSCThetaStuff _ _ _ _ => classSCThetaStuff
  end.

Definition classBody (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ _ _ classBody := arg_0__ in
  classBody.

Definition classFunDeps (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ _ classFunDeps _ := arg_0__ in
  classFunDeps.

Definition classKey (arg_0__ : Class) :=
  let 'Mk_Class _ _ classKey _ _ _ := arg_0__ in
  classKey.

Definition className (arg_0__ : Class) :=
  let 'Mk_Class _ className _ _ _ _ := arg_0__ in
  className.

Definition classTyCon (arg_0__ : Class) :=
  let 'Mk_Class classTyCon _ _ _ _ _ := arg_0__ in
  classTyCon.

Definition classTyVars (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ classTyVars _ _ := arg_0__ in
  classTyVars.
(* Midamble *)

Parameter naturallyCoherentClass : Class -> bool.
(* Converted value declarations: *)

Local Definition Eq___Class_op_zeze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.== classKey c2.

Local Definition Eq___Class_op_zsze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base./= classKey c2.

Program Instance Eq___Class : GHC.Base.Eq_ Class :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Class_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Class_op_zsze__ |}.

Local Definition Uniquable__Class_getUnique : Class -> Unique.Unique :=
  fun c => classKey c.

Program Instance Uniquable__Class : Unique.Uniquable Class :=
  fun _ k => k {| Unique.getUnique__ := Uniquable__Class_getUnique |}.

Local Definition NamedThing__Class_getName : Class -> Name.Name :=
  fun clas => className clas.

Local Definition NamedThing__Class_getOccName : Class -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__Class_getName n).

Program Instance NamedThing__Class : Name.NamedThing Class :=
  fun _ k =>
    k {| Name.getName__ := NamedThing__Class_getName ;
         Name.getOccName__ := NamedThing__Class_getOccName |}.

(* Skipping instance Outputable__Class of class Outputable *)

(* Skipping instance Data__Class of class Data *)

Definition classATItems : Class -> list ClassATItem :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ at_stuff _ _) => at_stuff
    | _ => nil
    end.

Definition classATs : Class -> list IdInfo.TyConId :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ at_stuff _ _) =>
        let cont_1__ arg_2__ := let 'ATI tc _ := arg_2__ in cons tc nil in
        Coq.Lists.List.flat_map cont_1__ at_stuff
    | _ => nil
    end.

Definition classArity : Class -> BasicTypes.Arity :=
  fun clas => Data.Foldable.length (classTyVars clas).

Definition classBigSig
   : Class ->
     (list Var.TyVar * list unit * list Var.Id * list ClassOpItem)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ tyvars _ AbstractClass => pair (pair (pair tyvars nil) nil) nil
    | Mk_Class _ _ _ tyvars _ (ConcreteClass sc_theta sc_sels _ op_stuff _) =>
        pair (pair (pair tyvars sc_theta) sc_sels) op_stuff
    end.

Definition classExtraBigSig
   : Class ->
     (list Var.TyVar * list (FunDep Var.TyVar) * list unit * list Var.Id *
      list ClassATItem *
      list ClassOpItem)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ tyvars fundeps AbstractClass =>
        pair (pair (pair (pair (pair tyvars fundeps) nil) nil) nil) nil
    | Mk_Class _ _ _ tyvars fundeps (ConcreteClass sc_theta sc_sels ats op_stuff
     _) =>
        pair (pair (pair (pair (pair tyvars fundeps) sc_theta) sc_sels) ats) op_stuff
    end.

Definition classHasFds : Class -> bool :=
  fun '(Mk_Class _ _ _ _ fds _) => negb (Data.Foldable.null fds).

Definition classMethods : Class -> list Var.Id :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ _ op_stuff _) =>
        let cont_1__ arg_2__ := let 'pair op_sel _ := arg_2__ in cons op_sel nil in
        Coq.Lists.List.flat_map cont_1__ op_stuff
    | _ => nil
    end.

Definition classAllSelIds : Class -> list Var.Id :=
  fun arg_0__ =>
    match arg_0__ with
    | (Mk_Class _ _ _ _ _ (ConcreteClass _ sc_sels _ _ _) as c) =>
        Coq.Init.Datatypes.app sc_sels (classMethods c)
    | c => nil
    end.

Definition classMinimalDef : Class -> ClassMinimalDef :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ _ _ d) => d
    | _ => BooleanFormula.mkTrue
    end.

Definition classOpItems : Class -> list ClassOpItem :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ _ op_stuff _) => op_stuff
    | _ => nil
    end.

Definition classSCTheta : Class -> list unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass theta_stuff _ _ _ _) => theta_stuff
    | _ => nil
    end.

Definition classTvsFds
   : Class -> (list Var.TyVar * list (FunDep Var.TyVar))%type :=
  fun c => pair (classTyVars c) (classFunDeps c).

Definition isAbstractClass : Class -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ AbstractClass => true
    | _ => false
    end.

Definition mkAbstractClass
   : Name.Name ->
     list Var.TyVar -> list (FunDep Var.TyVar) -> IdInfo.TyConId -> Class :=
  fun cls_name tyvars fds tycon =>
    Mk_Class tycon cls_name (Name.nameUnique cls_name) tyvars fds AbstractClass.

Definition mkClass
   : Name.Name ->
     list Var.TyVar ->
     list (FunDep Var.TyVar) ->
     list unit ->
     list Var.Id ->
     list ClassATItem ->
     list ClassOpItem -> ClassMinimalDef -> IdInfo.TyConId -> Class :=
  fun cls_name
  tyvars
  fds
  super_classes
  superdict_sels
  at_stuff
  op_stuff
  mindef
  tycon =>
    Mk_Class tycon cls_name (Name.nameUnique cls_name) tyvars fds (ConcreteClass
              super_classes superdict_sels at_stuff op_stuff mindef).

(* External variables:
     bool cons false list negb nil op_zt__ option pair true unit BasicTypes.Arity
     BasicTypes.DefMethSpec BooleanFormula.BooleanFormula BooleanFormula.mkTrue
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map Data.Foldable.length
     Data.Foldable.null GHC.Base.Eq_ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.error IdInfo.TyConId Name.Name Name.NamedThing Name.getName__
     Name.getOccName__ Name.nameOccName Name.nameUnique OccName.OccName
     SrcLoc.SrcSpan Unique.Uniquable Unique.Unique Unique.getUnique__ Var.Id
     Var.TyVar
*)
