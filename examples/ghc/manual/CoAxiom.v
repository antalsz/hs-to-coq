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
Require Data.Foldable.
Require Data.Traversable.
Require Data.Tuple.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require Name.
Require Panic.
Require SrcLoc.
Require Unique.
Require Util.
(* Require Var. *)
Import GHC.Base.Notations.
Import GHC.Num.Notations.

Require Import Core.

(* Converted type declarations: *)
(*
Inductive Role : Type := Nominal : Role
                      |  Representational : Role
                      |  Phantom : Role.

Parameter CoAxiomRule : Type. *)
Parameter coaxrName : CoAxiomRule -> Name.Name.

(*
Inductive BuiltInSynFamily : Type := Mk_BuiltInSynFamily_Dummy.

Definition BranchIndex := GHC.Num.Int%type.


Inductive BranchFlag : Type := Branched : BranchFlag
                            |  Unbranched : BranchFlag.


Inductive BranchesTy ty (br:BranchFlag) : Type := MkBranches :
    list (BranchIndex * CoAxBranchTy ty)%type -> BranchesTy ty br.

Inductive CoAxiomTy ty tyc (br:BranchFlag) : Type := Mk_CoAxiom
                              : Unique.Unique -> Name.Name -> Role -> tyc ->
                                BranchesTy ty br -> bool -> CoAxiomTy ty tyc br.

Arguments MkBranches {_} _.

Arguments Mk_CoAxiom {_} _ _ _ _ _ _.
*)


Definition cab_cvs  (arg_0__ : CoAxBranch) :=
  match arg_0__ with
    | Mk_CoAxBranch _ _ cab_cvs _ _ _ _ => cab_cvs
  end.

Definition cab_incomps  (arg_1__ : CoAxBranch) :=
  match arg_1__ with
    | Mk_CoAxBranch _ _ _ _ _ _ cab_incomps => cab_incomps
  end.

Definition cab_lhs  (arg_2__ : CoAxBranch) :=
  match arg_2__ with
    | Mk_CoAxBranch _ _ _ _ cab_lhs _ _ => cab_lhs
  end.

Definition cab_loc  (arg_3__ : CoAxBranch) :=
  match arg_3__ with
    | Mk_CoAxBranch cab_loc _ _ _ _ _ _ => cab_loc
  end.

Definition cab_rhs  (arg_4__ : CoAxBranch) :=
  match arg_4__ with
    | Mk_CoAxBranch _ _ _ _ _ cab_rhs _ => cab_rhs
  end.

Definition cab_roles  (arg_5__ : CoAxBranch) :=
  match arg_5__ with
    | Mk_CoAxBranch _ _ _ cab_roles _ _ _ => cab_roles
  end.

Definition cab_tvs  (arg_6__ : CoAxBranch) :=
  match arg_6__ with
    | Mk_CoAxBranch _ cab_tvs _ _ _ _ _ => cab_tvs
  end.

Definition unMkBranches {br}  (arg_7__ : Branches br) :=
  match arg_7__ with
    | MkBranches _ unMkBranches => unMkBranches
  end.

Definition co_ax_branches {br} (arg_8__ : CoAxiom br) :=
  match arg_8__ with
    | Mk_CoAxiom _ _ _ _ _ co_ax_branches _ => co_ax_branches
  end.

Definition co_ax_implicit {br} (arg_9__ : CoAxiom br) :=
  match arg_9__ with
    | Mk_CoAxiom _ _ _ _ _ _ co_ax_implicit => co_ax_implicit
  end.

Definition co_ax_name {br} (arg_10__ : CoAxiom br) :=
  match arg_10__ with
    | Mk_CoAxiom _ _ co_ax_name _ _ _ _ => co_ax_name
  end.

Definition co_ax_role {br} (arg_11__ : CoAxiom br) :=
  match arg_11__ with
    | Mk_CoAxiom _ _ _ co_ax_role _ _ _ => co_ax_role
  end.

Definition co_ax_tc {br} (arg_12__ : CoAxiom br) :=
  match arg_12__ with
    | Mk_CoAxiom _ _ _ _ co_ax_tc _ _ => co_ax_tc
  end.

Definition co_ax_unique {br} (arg_13__ : CoAxiom br) :=
  match arg_13__ with
    | Mk_CoAxiom _ co_ax_unique _ _ _ _ _ => co_ax_unique
  end.
(* Converted value declarations: *)

Instance Uniq_CoAxiom {typ:Type}{tyc:Type}{inst_br:BranchFlag} :
 Unique.Uniquable (CoAxiom inst_br) := {}.
Admitted.

Parameter Ord__CoAxiom_compare : forall{inst_br}, (CoAxiom inst_br) -> (CoAxiom inst_br) -> comparison.
(*  fun a b => GHC.Base.compare (Unique.getUnique a) (Unique.getUnique b). *)


Local Definition Eq___CoAxiom_op_zeze__ {inst_br} :
 (CoAxiom inst_br) -> (CoAxiom inst_br) -> bool :=
  fun a b =>
    let scrut_0__ := (Ord__CoAxiom_compare a b) in
    match scrut_0__ with
      | Eq => true
      | _ => false
    end.

Local Definition Eq___CoAxiom_op_zsze__ {inst_br} : (CoAxiom
                                                    inst_br) -> (CoAxiom inst_br) -> bool :=
  fun a b =>
    let scrut_0__ := (Ord__CoAxiom_compare a b) in
    match scrut_0__ with
      | Eq => false
      | _ => true
    end.

Program Instance Eq___CoAxiom {br} : GHC.Base.Eq_ (CoAxiom br) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___CoAxiom_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___CoAxiom_op_zsze__ |}.


Local Definition Ord__CoAxiom_op_zg__ {inst_br} : (CoAxiom inst_br) -> (CoAxiom inst_br) -> bool :=
  fun a b =>
    let scrut_0__ := (Ord__CoAxiom_compare a b) in
    match scrut_0__ with
      | Lt => false
      | Eq => false
      | Gt => true
    end.

Local Definition Ord__CoAxiom_op_zgze__ {inst_br} : (CoAxiom inst_br) -> (CoAxiom inst_br) -> bool :=
  fun a b =>
    let scrut_0__ := (Ord__CoAxiom_compare a b) in
    match scrut_0__ with
      | Lt => false
      | Eq => true
      | Gt => true
    end.

Local Definition Ord__CoAxiom_op_zl__ {inst_br} : (CoAxiom inst_br) -> (CoAxiom inst_br) -> bool :=
  fun a b =>
    let scrut_0__ := (Ord__CoAxiom_compare a b) in
    match scrut_0__ with
      | Lt => true
      | Eq => false
      | Gt => false
    end.

Local Definition Ord__CoAxiom_op_zlze__ {inst_br} : (CoAxiom
                                                    inst_br) -> (CoAxiom inst_br) -> bool :=
  fun a b =>
    let scrut_0__ := (Ord__CoAxiom_compare a b) in
    match scrut_0__ with
      | Lt => true
      | Eq => true
      | Gt => false
    end.

Local Definition Ord__CoAxiom_max {inst_br} : (CoAxiom inst_br) -> (CoAxiom
                                              inst_br) -> (CoAxiom inst_br) :=
  fun x y => if Ord__CoAxiom_op_zlze__ x y : bool then y else x.

Local Definition Ord__CoAxiom_min {inst_br} : (CoAxiom inst_br) -> (CoAxiom
                                              inst_br) -> (CoAxiom inst_br) :=
  fun x y => if Ord__CoAxiom_op_zlze__ x y : bool then x else y.

Program Instance Ord__CoAxiom {br} : GHC.Base.Ord (CoAxiom br) := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__CoAxiom_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__CoAxiom_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__CoAxiom_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__CoAxiom_op_zgze__ ;
      GHC.Base.compare__ := Ord__CoAxiom_compare ;
      GHC.Base.max__ := Ord__CoAxiom_max ;
      GHC.Base.min__ := Ord__CoAxiom_min |}.

(* Translating `instance forall {br}, Unique.Uniquable (CoAxiom.CoAxiom ty tyc br)'
   failed: OOPS! Cannot find information for class Qualified "Unique" "Uniquable"
   unsupported *)

(* Translating `instance forall {br}, Outputable.Outputable (CoAxiom.CoAxiom
   br)' failed: OOPS! Cannot find information for class Qualified "Outputable"
   "Outputable" unsupported *)

(* Translating `instance forall {br}, Name.NamedThing (CoAxiom.CoAxiom ty tyc br)'
   failed: OOPS! Cannot find information for class Qualified "Name" "NamedThing"
   unsupported *)

(* Translating `instance forall {br}, forall `{Data.Typeable.Internal.Typeable
   br}, Data.Data.Data (CoAxiom.CoAxiom ty tyc br)' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable.Outputable CoAxiom.CoAxBranch' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable CoAxiom.Role' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary.Binary CoAxiom.Role' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Data.Data.Data CoAxiom.CoAxiomRule' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Unique.Uniquable CoAxiom.CoAxiomRule' failed: OOPS!
   Cannot find information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Eq___CoAxiomRule_op_zeze__
    : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => coaxrName x GHC.Base.== coaxrName y.

Local Definition Eq___CoAxiomRule_op_zsze__
    : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => negb (Eq___CoAxiomRule_op_zeze__ x y).

Program Instance Eq___CoAxiomRule : GHC.Base.Eq_ CoAxiomRule := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___CoAxiomRule_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___CoAxiomRule_op_zsze__ |}.

Local Definition Ord__CoAxiomRule_compare
    : CoAxiomRule -> CoAxiomRule -> comparison :=
  fun x y => GHC.Base.compare (coaxrName x) (coaxrName y).

Local Definition Ord__CoAxiomRule_op_zg__
    : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => _GHC.Base.==_ (Ord__CoAxiomRule_compare x y) Gt.

Local Definition Ord__CoAxiomRule_op_zgze__
    : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => _GHC.Base./=_ (Ord__CoAxiomRule_compare x y) Lt.

Local Definition Ord__CoAxiomRule_op_zl__
    : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => _GHC.Base.==_ (Ord__CoAxiomRule_compare x y) Lt.

Local Definition Ord__CoAxiomRule_op_zlze__
    : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => _GHC.Base./=_ (Ord__CoAxiomRule_compare x y) Gt.

Local Definition Ord__CoAxiomRule_max
    : CoAxiomRule -> CoAxiomRule -> CoAxiomRule :=
  fun x y => if Ord__CoAxiomRule_op_zlze__ x y : bool then y else x.

Local Definition Ord__CoAxiomRule_min
    : CoAxiomRule -> CoAxiomRule -> CoAxiomRule :=
  fun x y => if Ord__CoAxiomRule_op_zlze__ x y : bool then x else y.

Program Instance Ord__CoAxiomRule : GHC.Base.Ord CoAxiomRule := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__CoAxiomRule_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__CoAxiomRule_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__CoAxiomRule_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__CoAxiomRule_op_zgze__ ;
      GHC.Base.compare__ := Ord__CoAxiomRule_compare ;
      GHC.Base.max__ := Ord__CoAxiomRule_max ;
      GHC.Base.min__ := Ord__CoAxiomRule_min |}.

(* Translating `instance Outputable.Outputable CoAxiom.CoAxiomRule' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Data.Data.Data CoAxiom.CoAxBranch' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data CoAxiom.Role' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___Role_op_zeze__ : Role -> Role -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Nominal , Nominal => true
      | Representational , Representational => true
      | Phantom , Phantom => true
      | _ , _ => false
    end.

Local Definition Eq___Role_op_zsze__ : Role -> Role -> bool :=
  fun a b => negb (Eq___Role_op_zeze__ a b).

Program Instance Eq___Role : GHC.Base.Eq_ Role := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Role_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Role_op_zsze__ |}.


Parameter Ord__Role_compare : Role -> Role -> comparison.

Parameter Ord__Role_op_zg__ : Role -> Role -> bool.
Parameter Ord__Role_op_zgze__ : Role -> Role -> bool.
Parameter Ord__Role_op_zl__ : Role -> Role -> bool.
Parameter Ord__Role_op_zlze__ : Role -> Role -> bool.


Local Definition Ord__Role_min : Role -> Role -> Role :=
  fun x y => if Ord__Role_op_zlze__ x y : bool then x else y.

Local Definition Ord__Role_max : Role -> Role -> Role :=
  fun x y => if Ord__Role_op_zlze__ x y : bool then y else x.

Program Instance Ord__Role : GHC.Base.Ord Role := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Role_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Role_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Role_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Role_op_zgze__ ;
      GHC.Base.compare__ := Ord__Role_compare ;
      GHC.Base.max__ := Ord__Role_max ;
      GHC.Base.min__ := Ord__Role_min |}.

Axiom trivialBuiltInFamily : forall {A : Type}, A.

(* Translating `trivialBuiltInFamily' failed: creating a record with the unknown
   constructor `BuiltInSynFamily' unsupported *)

Parameter branchesNth : forall {br}, Branches br -> BranchIndex -> CoAxBranch.


Definition coAxiomNthBranch {br} : CoAxiom br -> BranchIndex -> CoAxBranch :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_CoAxiom _ _ _ _ _ bs _ , index => branchesNth bs index
    end.

Definition coAxiomArity {br} : CoAxiom br -> BranchIndex -> BasicTypes.Arity :=
  fun ax index =>
    match coAxiomNthBranch ax index with
      | Mk_CoAxBranch _ tvs cvs _ _ _ _ => Data.Foldable.length tvs GHC.Num.+
                                        Data.Foldable.length cvs
    end.

Definition coAxBranchCoVars  : CoAxBranch -> list CoVar :=
  cab_cvs.

Definition coAxBranchIncomps  : CoAxBranch -> list (CoAxBranch) :=
  cab_incomps.

Definition coAxBranchLHS  : CoAxBranch -> list Core.Type_ :=
  cab_lhs.

Definition coAxiomNumPats {br} : CoAxiom br -> GHC.Num.Int :=
  Data.Foldable.length GHC.Base.∘ (coAxBranchLHS GHC.Base.∘ (GHC.Base.flip
  coAxiomNthBranch (GHC.Num.fromInteger 0))).

Definition coAxBranchRHS  : CoAxBranch -> Core.Type_ :=
  cab_rhs.

Definition coAxBranchRoles  : CoAxBranch -> list Role :=
  cab_roles.

Definition coAxBranchSpan  : CoAxBranch -> SrcLoc.SrcSpan :=
  cab_loc.

Definition coAxBranchTyVars  : CoAxBranch -> list TyVar :=
  cab_tvs.

Definition coAxiomBranches {br} : CoAxiom br -> Branches br :=
  co_ax_branches.

Definition coAxiomName {br} : CoAxiom br -> Name.Name :=
  co_ax_name.

Definition coAxiomRole {br} : CoAxiom br -> Role :=
  co_ax_role.

Parameter coAxiomSingleBranch : CoAxiom Unbranched -> CoAxBranch.

Parameter coAxiomSingleBranch_maybe : forall {br}, CoAxiom br ->
                                                     option (CoAxBranch).

Definition coAxiomTyCon {br} : CoAxiom br -> Core.TyCon :=
  co_ax_tc.

Parameter fromBranches : forall {br}, Branches br -> list (CoAxBranch).


Definition fsFromRole : Role -> FastString.FastString :=
  fun arg_0__ =>
    match arg_0__ with
      | Nominal => FastString.fsLit (GHC.Base.hs_string__ "nominal")
      | Representational => FastString.fsLit (GHC.Base.hs_string__ "representational")
      | Phantom => FastString.fsLit (GHC.Base.hs_string__ "phantom")
    end.

Definition isImplicitCoAxiom {br} : CoAxiom br -> bool :=
  co_ax_implicit.

Parameter manyBranches : list (CoAxBranch) -> Branches Branched.


Parameter mapAccumBranches : forall {br}, (list(CoAxBranch) -> (CoAxBranch) -> (CoAxBranch)) -> Branches br -> Branches br.


Parameter numBranches : forall{br}, Branches br -> GHC.Num.Int.

Definition placeHolderIncomps  : list (CoAxBranch) :=
  Panic.panic (GHC.Base.hs_string__ "placeHolderIncomps").

Parameter toBranched : forall {br}, Branches br -> Branches Branched.


Definition toBranchedAxiom {br} : CoAxiom br -> CoAxiom Branched :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CoAxiom _ unique name role tc branches implicit =>
        Mk_CoAxiom unique name role tc (toBranched branches) implicit
    end.

Parameter toUnbranched : forall {br}, Branches br -> Branches Unbranched.

Definition toUnbranchedAxiom {br} : CoAxiom br -> CoAxiom Unbranched :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CoAxiom _ unique name role tc branches implicit =>
        Mk_CoAxiom unique name role tc (toUnbranched branches) implicit
    end.

Parameter unbranched : (CoAxBranch) -> Branches Unbranched.
