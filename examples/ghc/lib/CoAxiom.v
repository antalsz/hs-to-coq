(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Core.

(* Converted imports: *)

Require Core.
Require Data.Foldable.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require Name.
Require Pair.
Require Panic.
Require SrcLoc.
Require Unique.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Eqn :=
  (Pair.Pair Core.Type_)%type.
(* Midamble *)

Import GHC.Num.Notations.

Parameter coaxrName : CoAxiomRule -> Name.Name.

(*
Parameter co_ax_branches : forall {br}, Core.CoAxiom br -> Branches br.
Parameter co_ax_name : forall {br}, Core.CoAxiom br -> Name.Name.
Parameter co_ax_role : forall {br}, Core.CoAxiom br -> Core.Role.
Parameter co_ax_tc   : forall {br}, Core.CoAxiom br -> Core.TyCon.
Parameter co_ax_implicit : forall {br}, Core.CoAxiom br -> bool.
*)

(* ------ *)
(* Core data types are not generated. So these record selectors
   must be added here. *)

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


(* ---- *)
Parameter Ord__Role_compare : Role -> Role -> comparison.
Parameter Ord__Role_op_zg__ : Role -> Role -> bool.
Parameter Ord__Role_op_zgze__ : Role -> Role -> bool.
Parameter Ord__Role_op_zl__ : Role -> Role -> bool.
Parameter Ord__Role_op_zlze__ : Role -> Role -> bool.

(* ---- *)

Instance Uniq_CoAxiom {inst_br:BranchFlag} :
 Unique.Uniquable (CoAxiom inst_br) := {}.
Admitted.

(* ---- *)

(* Definition unMkBranches {br} ( x : Branches br) : list CoAxBranch :=
  match x with | MkBranches _ brs => brs end. *)

Definition fromBranches {br} ( x : Branches br) : list CoAxBranch :=
  match x with | MkBranches _ brs => brs end.

Definition manyBranches : list CoAxBranch -> Branches Core.Branched :=
  fun brs =>
    let bnds :=
      pair (GHC.Num.fromInteger 0) (Data.Foldable.length brs GHC.Num.-
           GHC.Num.fromInteger 1) in
    if andb Util.debugIsOn (negb (Data.Tuple.snd bnds GHC.Base.>= Data.Tuple.fst
                                 bnds)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/CoAxiom.hs")
         (GHC.Num.fromInteger 140))
    else MkBranches brs.

Definition mapAccumBranches {br} : (list
                                   CoAxBranch -> CoAxBranch -> CoAxBranch) -> Branches br -> Branches br :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , MkBranches _ arr => let go : list CoAxBranch -> CoAxBranch -> (list
                                       CoAxBranch * CoAxBranch)%type :=
                                fun prev_branches cur_branch =>
                                  pair (cons cur_branch prev_branches) (f prev_branches cur_branch) in
                              MkBranches (Data.Tuple.snd GHC.Base.$
                                                         Data.Traversable.mapAccumL go nil
                                                         arr)
    end.

Definition numBranches {br} : Branches br -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
      | MkBranches _ arr => (GHC.List.length arr) GHC.Num.+
                          GHC.Num.fromInteger 1
    end.

Definition toBranched {br} : Branches br -> Branches Core.Branched :=
  MkBranches GHC.Base.∘ unMkBranches.

Definition toUnbranched {br} : Branches br -> Branches Core.Unbranched :=
  fun arg_0__ =>
    match arg_0__ with
      | MkBranches _ arr => MkBranches arr
    end.

Definition unbranched : Core.CoAxBranch -> Core.Branches Core.Unbranched :=
  fun br =>
    Core.MkBranches (cons br nil).

Definition toUnbranchedAxiom {br} : Core.CoAxiom br -> Core.CoAxiom
                                    Core.Unbranched :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CoAxiom _ unique name role tc branches implicit =>
        Mk_CoAxiom unique name role tc (toUnbranched branches) implicit
    end.

(* Converted value declarations: *)

Local Definition Ord__CoAxiom_compare {inst_br} : (Core.CoAxiom
                                                  inst_br) -> (Core.CoAxiom inst_br) -> comparison :=
  fun a b => GHC.Base.compare (Unique.getUnique a) (Unique.getUnique b).

Local Definition Ord__CoAxiom_op_zg__ {inst_br} : (Core.CoAxiom
                                                  inst_br) -> (Core.CoAxiom inst_br) -> bool :=
  fun a b =>
    match (Ord__CoAxiom_compare a b) with
    | Lt => false
    | Eq => false
    | Gt => true
    end.

Local Definition Ord__CoAxiom_op_zgze__ {inst_br} : (Core.CoAxiom
                                                    inst_br) -> (Core.CoAxiom inst_br) -> bool :=
  fun a b =>
    match (Ord__CoAxiom_compare a b) with
    | Lt => false
    | Eq => true
    | Gt => true
    end.

Local Definition Ord__CoAxiom_op_zl__ {inst_br} : (Core.CoAxiom
                                                  inst_br) -> (Core.CoAxiom inst_br) -> bool :=
  fun a b =>
    match (Ord__CoAxiom_compare a b) with
    | Lt => true
    | Eq => false
    | Gt => false
    end.

Local Definition Ord__CoAxiom_op_zlze__ {inst_br} : (Core.CoAxiom
                                                    inst_br) -> (Core.CoAxiom inst_br) -> bool :=
  fun a b =>
    match (Ord__CoAxiom_compare a b) with
    | Lt => true
    | Eq => true
    | Gt => false
    end.

Local Definition Ord__CoAxiom_max {inst_br} : (Core.CoAxiom
                                              inst_br) -> (Core.CoAxiom inst_br) -> (Core.CoAxiom inst_br) :=
  fun x y => if Ord__CoAxiom_op_zlze__ x y : bool then y else x.

Local Definition Ord__CoAxiom_min {inst_br} : (Core.CoAxiom
                                              inst_br) -> (Core.CoAxiom inst_br) -> (Core.CoAxiom inst_br) :=
  fun x y => if Ord__CoAxiom_op_zlze__ x y : bool then x else y.

Definition Eq___CoAxiom_op_zeze__ {inst_br} : Core.CoAxiom
                                              inst_br -> Core.CoAxiom inst_br -> bool :=
  fun a b =>
    let scrut_0__ := Ord__CoAxiom_compare a b in
    match scrut_0__ with
    | Eq => true
    | _ => false
    end.

Definition Eq___CoAxiom_op_zsze__ {inst_br} : Core.CoAxiom
                                              inst_br -> Core.CoAxiom inst_br -> bool :=
  fun a b =>
    let scrut_0__ := Ord__CoAxiom_compare a b in
    match scrut_0__ with
    | Eq => false
    | _ => true
    end.

Program Instance Eq___CoAxiom {br} : GHC.Base.Eq_ (Core.CoAxiom br) := fun _
                                                                           k =>
    k {|GHC.Base.op_zeze____ := Eq___CoAxiom_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___CoAxiom_op_zsze__ |}.
Admit Obligations.

Program Instance Ord__CoAxiom {br} : GHC.Base.Ord (Core.CoAxiom br) := fun _
                                                                           k =>
    k {|GHC.Base.op_zl____ := Ord__CoAxiom_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__CoAxiom_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__CoAxiom_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__CoAxiom_op_zgze__ ;
      GHC.Base.compare__ := Ord__CoAxiom_compare ;
      GHC.Base.max__ := Ord__CoAxiom_max ;
      GHC.Base.min__ := Ord__CoAxiom_min |}.
Admit Obligations.

(* Translating `instance forall {br}, Unique.Uniquable (Core.CoAxiom br)'
   failed: OOPS! Cannot find information for class Qualified "Unique" "Uniquable"
   unsupported *)

(* Translating `instance forall {br}, Outputable.Outputable (Core.CoAxiom br)'
   failed: OOPS! Cannot find information for class Qualified "Outputable"
   "Outputable" unsupported *)

(* Translating `instance forall {br}, Name.NamedThing (Core.CoAxiom br)' failed:
   OOPS! Cannot find information for class Qualified "Name" "NamedThing"
   unsupported *)

(* Translating `instance forall {br}, forall `{Data.Typeable.Internal.Typeable
   br}, Data.Data.Data (Core.CoAxiom br)' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable.Outputable Core.CoAxBranch' failed: using a
   record pattern for the unknown constructor `CoAxBranch' unsupported *)

(* Translating `instance Outputable.Outputable Core.Role' failed: OOPS! Cannot
   find information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary.Binary Core.Role' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Data.Data.Data Core.CoAxiomRule' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Unique.Uniquable Core.CoAxiomRule' failed: OOPS! Cannot
   find information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Eq___CoAxiomRule_op_zeze__
    : Core.CoAxiomRule -> Core.CoAxiomRule -> bool :=
  fun x y => coaxrName x GHC.Base.== coaxrName y.

Local Definition Eq___CoAxiomRule_op_zsze__
    : Core.CoAxiomRule -> Core.CoAxiomRule -> bool :=
  fun x y => negb (Eq___CoAxiomRule_op_zeze__ x y).

Program Instance Eq___CoAxiomRule : GHC.Base.Eq_ Core.CoAxiomRule := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___CoAxiomRule_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___CoAxiomRule_op_zsze__ |}.
Admit Obligations.

Local Definition Ord__CoAxiomRule_compare
    : Core.CoAxiomRule -> Core.CoAxiomRule -> comparison :=
  fun x y => GHC.Base.compare (coaxrName x) (coaxrName y).

Local Definition Ord__CoAxiomRule_op_zg__
    : Core.CoAxiomRule -> Core.CoAxiomRule -> bool :=
  fun x y => _GHC.Base.==_ (Ord__CoAxiomRule_compare x y) Gt.

Local Definition Ord__CoAxiomRule_op_zgze__
    : Core.CoAxiomRule -> Core.CoAxiomRule -> bool :=
  fun x y => _GHC.Base./=_ (Ord__CoAxiomRule_compare x y) Lt.

Local Definition Ord__CoAxiomRule_op_zl__
    : Core.CoAxiomRule -> Core.CoAxiomRule -> bool :=
  fun x y => _GHC.Base.==_ (Ord__CoAxiomRule_compare x y) Lt.

Local Definition Ord__CoAxiomRule_op_zlze__
    : Core.CoAxiomRule -> Core.CoAxiomRule -> bool :=
  fun x y => _GHC.Base./=_ (Ord__CoAxiomRule_compare x y) Gt.

Local Definition Ord__CoAxiomRule_max
    : Core.CoAxiomRule -> Core.CoAxiomRule -> Core.CoAxiomRule :=
  fun x y => if Ord__CoAxiomRule_op_zlze__ x y : bool then y else x.

Local Definition Ord__CoAxiomRule_min
    : Core.CoAxiomRule -> Core.CoAxiomRule -> Core.CoAxiomRule :=
  fun x y => if Ord__CoAxiomRule_op_zlze__ x y : bool then x else y.

Program Instance Ord__CoAxiomRule : GHC.Base.Ord Core.CoAxiomRule := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__CoAxiomRule_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__CoAxiomRule_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__CoAxiomRule_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__CoAxiomRule_op_zgze__ ;
      GHC.Base.compare__ := Ord__CoAxiomRule_compare ;
      GHC.Base.max__ := Ord__CoAxiomRule_max ;
      GHC.Base.min__ := Ord__CoAxiomRule_min |}.
Admit Obligations.

(* Translating `instance Outputable.Outputable Core.CoAxiomRule' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Data.Data.Data Core.CoAxBranch' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data Core.Role' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Skipping instance Ord__Role *)

Local Definition Eq___Role_op_zeze__ : Core.Role -> Core.Role -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
    | Core.Nominal , Core.Nominal => true
    | Core.Representational , Core.Representational => true
    | Core.Phantom , Core.Phantom => true
    | _ , _ => false
    end.

Local Definition Eq___Role_op_zsze__ : Core.Role -> Core.Role -> bool :=
  fun a b => negb (Eq___Role_op_zeze__ a b).

Program Instance Eq___Role : GHC.Base.Eq_ Core.Role := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Role_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Role_op_zsze__ |}.
Admit Obligations.

Definition coAxBranchCoVars : Core.CoAxBranch -> list CoVar :=
  cab_cvs.

Definition coAxBranchIncomps : Core.CoAxBranch -> list Core.CoAxBranch :=
  cab_incomps.

Definition coAxBranchLHS : Core.CoAxBranch -> list Core.Type_ :=
  cab_lhs.

Definition coAxBranchRHS : Core.CoAxBranch -> Core.Type_ :=
  cab_rhs.

Definition coAxBranchRoles : Core.CoAxBranch -> list Core.Role :=
  cab_roles.

Definition coAxBranchSpan : Core.CoAxBranch -> SrcLoc.SrcSpan :=
  cab_loc.

Definition coAxBranchTyVars : Core.CoAxBranch -> list TyVar :=
  cab_tvs.

Axiom coAxiomArity : forall {A : Type}, A.

(* Translating `coAxiomArity' failed: using a record pattern for the unknown
   constructor `CoAxBranch' unsupported *)

Definition coAxiomBranches {br} : Core.CoAxiom br -> Core.Branches br :=
  co_ax_branches.

Definition coAxiomName {br} : Core.CoAxiom br -> Name.Name :=
  co_ax_name.

Axiom coAxiomNthBranch : forall {A : Type}, A.

Definition coAxiomNumPats {br} : Core.CoAxiom br -> GHC.Num.Int :=
  Data.Foldable.length GHC.Base.∘ (coAxBranchLHS GHC.Base.∘ (GHC.Base.flip
  coAxiomNthBranch #0)).

(* Translating `coAxiomNthBranch' failed: using a record pattern for the unknown
   constructor `CoAxiom' unsupported *)

Definition coAxiomRole {br} : Core.CoAxiom br -> Core.Role :=
  co_ax_role.

Axiom coAxiomSingleBranch : forall {A : Type}, A.

(* Translating `coAxiomSingleBranch' failed: using a record pattern for the
   unknown constructor `CoAxiom' unsupported *)

Axiom coAxiomSingleBranch_maybe : forall {A : Type}, A.

(* Translating `coAxiomSingleBranch_maybe' failed: using a record pattern for
   the unknown constructor `CoAxiom' unsupported *)

Definition coAxiomTyCon {br} : Core.CoAxiom br -> Core.TyCon :=
  co_ax_tc.

Definition fsFromRole : Core.Role -> FastString.FastString :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Nominal => FastString.fsLit (GHC.Base.hs_string__ "nominal")
    | Core.Representational =>
        FastString.fsLit (GHC.Base.hs_string__ "representational")
    | Core.Phantom => FastString.fsLit (GHC.Base.hs_string__ "phantom")
    end.

Definition isImplicitCoAxiom {br} : Core.CoAxiom br -> bool :=
  co_ax_implicit.

Definition placeHolderIncomps : list Core.CoAxBranch :=
  Panic.panic (GHC.Base.hs_string__ "placeHolderIncomps").

Axiom trivialBuiltInFamily : forall {A : Type}, A.

(* Translating `trivialBuiltInFamily' failed: creating a record with the unknown
   constructor `BuiltInSynFamily' unsupported *)

(* Unbound variables:
     CoVar Eq Gt Lt TyVar bool cab_cvs cab_incomps cab_lhs cab_loc cab_rhs cab_roles
     cab_tvs co_ax_branches co_ax_implicit co_ax_name co_ax_role co_ax_tc coaxrName
     comparison false list negb true Core.Branches Core.CoAxBranch Core.CoAxiom
     Core.CoAxiomRule Core.Nominal Core.Phantom Core.Representational Core.Role
     Core.TyCon Core.Type_ Data.Foldable.length FastString.FastString
     FastString.fsLit GHC.Base.Eq_ GHC.Base.Ord GHC.Base.compare GHC.Base.flip
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.Num.Int
     GHC.Num.fromInteger Name.Name Pair.Pair Panic.panic SrcLoc.SrcSpan
     Unique.getUnique
*)
