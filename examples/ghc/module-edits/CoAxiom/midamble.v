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
