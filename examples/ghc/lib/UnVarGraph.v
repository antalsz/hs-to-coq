(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Bag.
Require Coq.Init.Datatypes.
Require Data.Foldable.
Require Data.IntSet.Base.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require UniqFM.
Require Unique.
Require Var.
Require VarEnv.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UnVarSet : Type := Mk_UnVarSet
                            : (Data.IntSet.Base.IntSet) -> UnVarSet.

Inductive Gen : Type := CBPG : UnVarSet -> UnVarSet -> Gen
                     |  CG : UnVarSet -> Gen.

Inductive UnVarGraph : Type := Mk_UnVarGraph : (Bag.Bag Gen) -> UnVarGraph.
(* Midamble *)

Instance Unpeel_UnVarSet : Prim.Unpeel UnVarSet Data.IntSet.Base.IntSet :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarSet y => y end) Mk_UnVarSet.
Instance Unpeel_UnVarGraph : Prim.Unpeel UnVarGraph (Bag.Bag Gen) :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarGraph y => y end) Mk_UnVarGraph.
(* Converted value declarations: *)

(* Translating `instance Outputable.Outputable UnVarGraph.UnVarSet' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable UnVarGraph.Gen' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable UnVarGraph.UnVarGraph' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Local Definition Eq___UnVarSet_op_zeze__ : UnVarSet -> UnVarSet -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___UnVarSet_op_zsze__ : UnVarSet -> UnVarSet -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___UnVarSet : GHC.Base.Eq_ UnVarSet := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___UnVarSet_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___UnVarSet_op_zsze__ |}.

Definition emptyUnVarGraph : UnVarGraph :=
  Mk_UnVarGraph Bag.emptyBag.

Definition emptyUnVarSet : UnVarSet :=
  Mk_UnVarSet Data.IntSet.Base.empty.

Definition isEmptyUnVarSet : UnVarSet -> bool :=
  fun arg_11__ =>
    match arg_11__ with
      | Mk_UnVarSet s => Data.IntSet.Base.null s
    end.

Definition prune : UnVarGraph -> UnVarGraph :=
  fun arg_14__ =>
    match arg_14__ with
      | Mk_UnVarGraph g => let go :=
                             fun arg_15__ =>
                               match arg_15__ with
                                 | CG s => negb (isEmptyUnVarSet s)
                                 | CBPG s1 s2 => andb (negb (isEmptyUnVarSet s1)) (negb (isEmptyUnVarSet s2))
                               end in
                           Mk_UnVarGraph GHC.Base.$ Bag.filterBag go g
    end.

Definition completeGraph : UnVarSet -> UnVarGraph :=
  fun s =>
    prune GHC.Base.$ (Mk_UnVarGraph GHC.Base.$ (Bag.unitBag GHC.Base.$ CG s)).

Definition completeBipartiteGraph : UnVarSet -> UnVarSet -> UnVarGraph :=
  fun s1 s2 =>
    prune GHC.Base.$ (Mk_UnVarGraph GHC.Base.$ (Bag.unitBag GHC.Base.$ CBPG s1 s2)).

Definition k : Var.Var -> GHC.Num.Int :=
  fun v => Unique.getKey (Unique.getUnique v).

Definition mkUnVarSet : list Var.Var -> UnVarSet :=
  fun vs =>
    Mk_UnVarSet GHC.Base.$ (Data.IntSet.Base.fromList GHC.Base.$ GHC.Base.map k vs).

Definition elemUnVarSet : Var.Var -> UnVarSet -> bool :=
  fun arg_26__ arg_27__ =>
    match arg_26__ , arg_27__ with
      | v , Mk_UnVarSet s => Data.IntSet.Base.member (k v) s
    end.

Definition delUnVarSet : UnVarSet -> Var.Var -> UnVarSet :=
  fun arg_38__ arg_39__ =>
    match arg_38__ , arg_39__ with
      | Mk_UnVarSet s , v => Mk_UnVarSet GHC.Base.$ Data.IntSet.Base.delete (k v) s
    end.

Definition delNode : UnVarGraph -> Var.Var -> UnVarGraph :=
  fun arg_42__ arg_43__ =>
    match arg_42__ , arg_43__ with
      | Mk_UnVarGraph g , v => let go :=
                                 fun arg_44__ =>
                                   match arg_44__ with
                                     | CG s => CG (delUnVarSet s v)
                                     | CBPG s1 s2 => CBPG (delUnVarSet s1 v) (delUnVarSet s2 v)
                                   end in
                               prune GHC.Base.$ (Mk_UnVarGraph GHC.Base.$ Bag.mapBag go g)
    end.

Definition unionUnVarGraph : UnVarGraph -> UnVarGraph -> UnVarGraph :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_UnVarGraph g1 , Mk_UnVarGraph g2 => Mk_UnVarGraph (Bag.unionBags g1 g2)
    end.

Definition unionUnVarGraphs : list UnVarGraph -> UnVarGraph :=
  Data.Foldable.foldl' unionUnVarGraph emptyUnVarGraph.

Definition unionUnVarSet : UnVarSet -> UnVarSet -> UnVarSet :=
  fun arg_6__ arg_7__ =>
    match arg_6__ , arg_7__ with
      | Mk_UnVarSet set1 , Mk_UnVarSet set2 => Mk_UnVarSet (Data.IntSet.Base.union
                                                           set1 set2)
    end.

Definition unionUnVarSets : list UnVarSet -> UnVarSet :=
  Data.Foldable.foldr unionUnVarSet emptyUnVarSet.

Definition neighbors : UnVarGraph -> Var.Var -> UnVarSet :=
  fun arg_30__ arg_31__ =>
    match arg_30__ , arg_31__ with
      | Mk_UnVarGraph g , v => let go :=
                                 fun arg_32__ =>
                                   match arg_32__ with
                                     | CG s => (if elemUnVarSet v s : bool
                                               then cons s nil
                                               else nil)
                                     | CBPG s1 s2 => Coq.Init.Datatypes.app (if elemUnVarSet v s1 : bool
                                                                            then cons s2 nil
                                                                            else nil) (if elemUnVarSet v s2 : bool
                                                                            then cons s1 nil
                                                                            else nil)
                                   end in
                               unionUnVarSets GHC.Base.$ (Data.Foldable.concatMap go GHC.Base.$ Bag.bagToList
                               g)
    end.

Definition varEnvDom {a} : VarEnv.VarEnv a -> UnVarSet :=
  fun ae => Mk_UnVarSet GHC.Base.$ UniqFM.ufmToSet_Directly ae.

(* Unbound variables:
     andb bool cons list negb nil Bag.Bag Bag.bagToList Bag.emptyBag Bag.filterBag
     Bag.mapBag Bag.unionBags Bag.unitBag Coq.Init.Datatypes.app
     Data.Foldable.concatMap Data.Foldable.foldl' Data.Foldable.foldr
     Data.IntSet.Base.IntSet Data.IntSet.Base.delete Data.IntSet.Base.empty
     Data.IntSet.Base.fromList Data.IntSet.Base.member Data.IntSet.Base.null
     Data.IntSet.Base.union GHC.Base.Eq_ GHC.Base.map GHC.Base.op_zd__
     GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.Num.Int GHC.Prim.coerce
     UniqFM.ufmToSet_Directly Unique.getKey Unique.getUnique Var.Var VarEnv.VarEnv
*)
