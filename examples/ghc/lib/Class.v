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
Require GHC.List.
Require GHC.Num.
Require Name.
Require SrcLoc.
Require Unique.
Require Util.
Require Var.
Import GHC.Base.Notations.
(* Import GHC.List.Notations. *)

(* Converted type declarations: *)

Definition FunDep a :=
  (list a * list a)%type%type.

Definition DefMethInfo :=
  (option (Name.Name * BasicTypes.DefMethSpec unit)%type)%type.

Definition ClassOpItem :=
  (Var.Id * DefMethInfo)%type%type.

Definition ClassMinimalDef :=
  (BooleanFormula.BooleanFormula Name.Name)%type.

Inductive ClassATItem : Type := ATI : unit -> (option (unit *
                                                             SrcLoc.SrcSpan)%type) -> ClassATItem.

Inductive Class : Type := Mk_Class
                         : unit -> Name.Name -> Unique.Unique -> list Var.TyVar -> list (FunDep
                                                                                               Var.TyVar) -> list
                           unit -> list Var.Id -> list ClassATItem -> list
                           ClassOpItem -> ClassMinimalDef -> Class.

Definition classATStuff (arg_0__ : Class) :=
  match arg_0__ with
    | Mk_Class _ _ _ _ _ _ _ classATStuff _ _ => classATStuff
  end.

Definition classFunDeps (arg_1__ : Class) :=
  match arg_1__ with
    | Mk_Class _ _ _ _ classFunDeps _ _ _ _ _ => classFunDeps
  end.

Definition classKey (arg_2__ : Class) :=
  match arg_2__ with
    | Mk_Class _ _ classKey _ _ _ _ _ _ _ => classKey
  end.

Definition classMinimalDef (arg_3__ : Class) :=
  match arg_3__ with
    | Mk_Class _ _ _ _ _ _ _ _ _ classMinimalDef => classMinimalDef
  end.

Definition className (arg_4__ : Class) :=
  match arg_4__ with
    | Mk_Class _ className _ _ _ _ _ _ _ _ => className
  end.

Definition classOpStuff (arg_5__ : Class) :=
  match arg_5__ with
    | Mk_Class _ _ _ _ _ _ _ _ classOpStuff _ => classOpStuff
  end.

Definition classSCSels (arg_6__ : Class) :=
  match arg_6__ with
    | Mk_Class _ _ _ _ _ _ classSCSels _ _ _ => classSCSels
  end.

Definition classSCTheta (arg_7__ : Class) :=
  match arg_7__ with
    | Mk_Class _ _ _ _ _ classSCTheta _ _ _ _ => classSCTheta
  end.

Definition classTyCon (arg_8__ : Class) :=
  match arg_8__ with
    | Mk_Class classTyCon _ _ _ _ _ _ _ _ _ => classTyCon
  end.

Definition classTyVars (arg_9__ : Class) :=
  match arg_9__ with
    | Mk_Class _ _ _ classTyVars _ _ _ _ _ _ => classTyVars
  end.
(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.

Local Definition Eq___Class_op_zeze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.== classKey c2.

Local Definition Eq___Class_op_zsze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base./= classKey c2.

Program Instance Eq___Class : GHC.Base.Eq_ Class := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Class_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Class_op_zsze__ |}.

Local Definition Ord__Class_compare : Class -> Class -> comparison :=
  fun c1 c2 => GHC.Base.compare (classKey c1) (classKey c2).

Local Definition Ord__Class_op_zg__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.> classKey c2.

Local Definition Ord__Class_op_zgze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.>= classKey c2.

Local Definition Ord__Class_op_zl__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.< classKey c2.

Local Definition Ord__Class_op_zlze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.<= classKey c2.

Local Definition Ord__Class_min : Class -> Class -> Class :=
  fun x y => if Ord__Class_op_zlze__ x y : bool then x else y.

Local Definition Ord__Class_max : Class -> Class -> Class :=
  fun x y => if Ord__Class_op_zlze__ x y : bool then y else x.

Program Instance Ord__Class : GHC.Base.Ord Class := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Class_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Class_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Class_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Class_op_zgze__ ;
      GHC.Base.compare__ := Ord__Class_compare ;
      GHC.Base.max__ := Ord__Class_max ;
      GHC.Base.min__ := Ord__Class_min |}.

(* Translating `instance Unique.Uniquable Class.Class' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Name.NamedThing Class.Class' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable.Outputable Class.Class' failed: OOPS! Cannot
   find information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Data.Data.Data Class.Class' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

Definition classATItems : Class -> list ClassATItem :=
  classATStuff.

Definition classATs : Class -> list unit :=
  fun arg_31__ =>
    match arg_31__ with
      | Mk_Class _ _ _ _ _ _ _ at_stuff _ _ => let cont_32__ arg_33__ :=
                                              match arg_33__ with
                                                | ATI tc _ => cons tc nil
                                              end in
                                            Coq.Lists.List.flat_map cont_32__ at_stuff
    end.

Definition classArity : Class -> BasicTypes.Arity :=
  fun clas => Data.Foldable.length (classTyVars clas).

Definition classBigSig : Class -> (list Var.TyVar * list unit * list
                         Var.Id * list ClassOpItem)%type :=
  fun arg_24__ =>
    match arg_24__ with
      | Mk_Class _ _ _ tyvars _ sc_theta sc_sels _ op_stuff _ => pair (pair (pair tyvars
                                                                               sc_theta) sc_sels) op_stuff
    end.

Definition classExtraBigSig : Class -> (list Var.TyVar * list (FunDep Var.TyVar)
                              * list unit * list Var.Id * list ClassATItem * list
                              ClassOpItem)%type :=
  fun arg_21__ =>
    match arg_21__ with
      | Mk_Class _ _ _ tyvars fundeps sc_theta sc_sels ats op_stuff _ => pair (pair (pair
                                                                                 (pair (pair tyvars fundeps) sc_theta)
                                                                                 sc_sels) ats) op_stuff
    end.

Definition classHasFds : Class -> bool :=
  fun arg_27__ =>
    match arg_27__ with
      | Mk_Class _ _ _ _ fds _ _ _ _ _ => negb (Data.Foldable.null fds)
    end.

Definition classMethods : Class -> list Var.Id :=
  fun arg_36__ =>
    match arg_36__ with
      | Mk_Class _ _ _ _ _ _ _ _ op_stuff _ => let cont_37__ arg_38__ :=
                                              match arg_38__ with
                                                | pair op_sel _ => cons op_sel nil
                                              end in
                                            Coq.Lists.List.flat_map cont_37__ op_stuff
    end.

Definition classAllSelIds : Class -> list Var.Id :=
  fun arg_45__ =>
    match arg_45__ with
      | (Mk_Class _ _ _ _ _ _ sc_sels _ _ _ as c) => Coq.Init.Datatypes.app sc_sels
                                                                         (classMethods c)
    end.

Definition classOpItems : Class -> list ClassOpItem :=
  classOpStuff.

(*
Definition classSCSelId : Class -> GHC.Num.Int -> Var.Id :=
  fun arg_41__ arg_42__ =>
    match arg_41__ , arg_42__ with
      | Class _ _ _ _ _ _ sc_sels _ _ _ , n => if andb Util.debugIsOn (negb (andb (n
                                                                                  GHC.Base.>= GHC.Num.fromInteger 0) (n
                                                                                  GHC.Base.< Data.Foldable.length
                                                                                  sc_sels))) : bool
                                               then (Panic.assertPanic (GHC.Base.hs_string__
                                                                       "ghc/compiler/types/Class.hs")
                                                    (GHC.Num.fromInteger 217))
                                               else sc_sels GHC.List.!! n
    end.
*)

Definition classTvsFds : Class -> (list Var.TyVar * list (FunDep
                                                         Var.TyVar))%type :=
  fun c => pair (classTyVars c) (classFunDeps c).

Definition mkClass : list Var.TyVar -> list (list Var.TyVar * list
                                            Var.TyVar)%type -> list unit -> list Var.Id -> list
                     ClassATItem -> list ClassOpItem -> ClassMinimalDef -> unit -> Class :=
  fun tyvars fds super_classes superdict_sels at_stuff op_stuff mindef tycon =>
    Mk_Class missingValue missingValue missingValue missingValue missingValue
          missingValue missingValue missingValue missingValue missingValue.

(*
Definition naturallyCoherentClass : Class -> bool :=
  fun cls =>
    orb (Unique.hasKey cls PrelNames.heqTyConKey) (orb (Unique.hasKey cls
                                                                      PrelNames.eqTyConKey) (orb (Unique.hasKey cls
                                                                                                                PrelNames.coercibleTyConKey)
                                                                                                 (Unique.hasKey cls
                                                                                                                PrelNames.typeableClassKey))). *)
(*
Definition pprDefMethInfo : DefMethInfo -> Outputable.SDoc :=
  fun arg_16__ =>
    match arg_16__ with
      | None => Outputable.empty
      | Some (pair n BasicTypes.VanillaDM) => Outputable.text (GHC.Base.hs_string__
                                                              "Default method") Outputable.<+> Panic.noString n
      | Some (pair n (BasicTypes.GenericDM ty)) => ((Outputable.text
                                                   (GHC.Base.hs_string__ "Generic default method") Outputable.<+>
                                                   Panic.noString n) Outputable.<+> Outputable.dcolon) Outputable.<+>
                                                   Panic.noString ty
    end.

Definition pprFunDep {a} `{Outputable.Outputable a} : FunDep
                                                      a -> Outputable.SDoc :=
  fun arg_10__ =>
    match arg_10__ with
      | pair us vs => Outputable.hsep (cons (Outputable.interppSP us) (cons
                                            Outputable.arrow (cons (Outputable.interppSP vs) nil)))
    end.

Definition pprFundeps {a} `{Outputable.Outputable a} : list (FunDep
                                                            a) -> Outputable.SDoc :=
  fun arg_13__ =>
    match arg_13__ with
      | nil => Outputable.empty
      | fds => Outputable.hsep (cons Outputable.vbar (Outputable.punctuate
                                     Outputable.comma (GHC.Base.map pprFunDep fds)))
    end. *)

(* Unbound variables:
     Some andb bool comparison cons list negb nil op_zt__ option orb pair
     BasicTypes.Arity BasicTypes.DefMethSpec BasicTypes.GenericDM
     BasicTypes.VanillaDM BooleanFormula.BooleanFormula Coq.Init.Datatypes.app
     Coq.Lists.List.flat_map Data.Foldable.length Data.Foldable.null GHC.Base.Eq_
     GHC.Base.Ord GHC.Base.compare GHC.Base.map GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__
     GHC.List.op_znzn__ GHC.Num.Int Name.Name Outputable.Outputable Outputable.SDoc
     Outputable.arrow Outputable.comma Outputable.dcolon Outputable.empty
     Outputable.hsep Outputable.interppSP Outputable.op_zlzpzg__ Outputable.punctuate
     Outputable.text Outputable.vbar Panic.assertPanic Panic.noString
     PrelNames.coercibleTyConKey PrelNames.eqTyConKey PrelNames.heqTyConKey
     PrelNames.typeableClassKey SrcLoc.SrcSpan unit unit
     unit Unique.Unique Unique.hasKey Util.debugIsOn Var.Id Var.TyVar
*)
