(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require GHC.Base.
Require GHC.Prim.
Require UniqFM.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Polymorphic Definition UniqInv@{i} {a:Type@{i}} (fm : UniqFM.UniqFM a) `{Unique.Uniquable a} : Type@{i} :=
  forall  (x:a), 
    List.In x (UniqFM.eltsUFM fm) ->
    UniqFM.lookupUFM fm (Unique.getUnique x) = Some x. 

Polymorphic Inductive UniqSet@{i j} (a:Type@{i}) : Type@{j} := 
  Mk_UniqSet : forall `{Unique.Uniquable a} (fm : UniqFM.UniqFM a), UniqInv fm -> UniqSet a.


Arguments Mk_UniqSet {_} {_} _.

Definition getUniqSet' {a} (arg_0__ : UniqSet a) :=
  let 'Mk_UniqSet _ getUniqSet' _ := arg_0__ in
  getUniqSet'.

(* Converted value declarations: *)

(* SCW we DON'T want to coerce *)
(*
Instance Unpeel_UniqSet ele
   : GHC.Prim.Unpeel (UniqSet ele) (UniqFM.UniqFM ele) :=
  GHC.Prim.Build_Unpeel _ _ (fun '(Mk_UniqSet y) => y) Mk_UniqSet.
*)

(* Skipping instance Eq___UniqSet *)

(* Skipping instance Outputable__UniqSet of class Outputable *)

Program Definition Monoid__UniqSet_mempty {inst_a} `{Unique.Uniquable inst_a} : 
  UniqSet inst_a :=
  Mk_UniqSet GHC.Base.mempty _.
Next Obligation.
unfold UniqInv.
intros. simpl in *. contradiction.
Qed.

(*
Local Definition Monoid__UniqSet_mconcat {inst_a}
   : list (UniqSet inst_a) -> UniqSet inst_a :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__UniqSet_mappend {inst_a}
   : UniqSet inst_a -> UniqSet inst_a -> UniqSet inst_a :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Semigroup__UniqSet_op_zlzlzgzg__ {inst_a}
   : UniqSet inst_a -> UniqSet inst_a -> UniqSet inst_a :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__UniqSet {a} : GHC.Base.Semigroup (UniqSet a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__UniqSet_op_zlzlzgzg__ |}.

Program Instance Monoid__UniqSet {a} : GHC.Base.Monoid (UniqSet a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__UniqSet_mappend ;
         GHC.Base.mconcat__ := Monoid__UniqSet_mconcat ;
         GHC.Base.mempty__ := Monoid__UniqSet_mempty |}.
*)
(* Skipping instance Data__UniqSet of class Data *)

Program Definition addOneToUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ set _, x => Mk_UniqSet (UniqFM.addToUFM set x x) _
    end.
Next Obligation.
unfold UniqInv in *.
unfold UniqFM.addToUFM.
intros.
destruct set.
Admitted.

Definition addListToUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  Data.Foldable.foldl' addOneToUniqSet.

Program Definition delListFromUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, l => Mk_UniqSet (UniqFM.delListFromUFM s l) _
    end.
Next Obligation.
Admitted.

Program Definition delListFromUniqSet_Directly {a}
   : UniqSet a -> list Unique.Unique -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, l => Mk_UniqSet (UniqFM.delListFromUFM_Directly s l) _
    end.
Next Obligation.
Admitted.

Program Definition delOneFromUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, a => Mk_UniqSet (UniqFM.delFromUFM s a) _
    end.
Next Obligation.
Admitted.

Program Definition delOneFromUniqSet_Directly {a}
   : UniqSet a -> Unique.Unique -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, u => Mk_UniqSet (UniqFM.delFromUFM_Directly s u) _
    end.
Next Obligation.
Admitted.

Definition elemUniqSet_Directly {a} : Unique.Unique -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_UniqSet _ s _ => UniqFM.elemUFM_Directly a s 
    end.

Definition elementOfUniqSet {a} `{Unique.Uniquable a}
   : a -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_UniqSet _ s _ => UniqFM.elemUFM a s
    end.

Program Definition emptyUniqSet {a} `{Unique.Uniquable a}: UniqSet a :=
  Mk_UniqSet UniqFM.emptyUFM _.
Next Obligation.
Admitted.

Definition mkUniqSet {a} `{Unique.Uniquable a} : list a -> UniqSet a :=
  Data.Foldable.foldl' addOneToUniqSet emptyUniqSet.

Program Definition filterUniqSet {a} : (a -> bool) -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet _ s _ => Mk_UniqSet (UniqFM.filterUFM p s) _
    end.
Next Obligation.
Admitted.

Program Definition filterUniqSet_Directly {elt}
   : (Unique.Unique -> elt -> bool) -> UniqSet elt -> UniqSet elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_UniqSet _ s _ => Mk_UniqSet (UniqFM.filterUFM_Directly f s) _
    end.
Next Obligation.
Admitted.

Definition getUniqSet {a} : UniqSet a -> UniqFM.UniqFM a :=
  getUniqSet'.

Program Definition intersectUniqSets {a} : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, Mk_UniqSet _ t _ => Mk_UniqSet (UniqFM.intersectUFM s t) _
    end.
Next Obligation.
Admitted.

Definition isEmptyUniqSet {a} : UniqSet a -> bool :=
  fun '(Mk_UniqSet _ s _) => UniqFM.isNullUFM s.

Definition lookupUniqSet {a} {b} `{Unique.Uniquable a}
   : UniqSet b -> a -> option b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, k => UniqFM.lookupUFM s k
    end.

Definition lookupUniqSet_Directly {a}
   : UniqSet a -> Unique.Unique -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, k => UniqFM.lookupUFM_Directly s k
    end.

Program Definition minusUniqSet {a} : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, Mk_UniqSet _ t _ => Mk_UniqSet (UniqFM.minusUFM s t) _
    end.
Next Obligation.
Admitted.

Definition nonDetEltsUniqSet {elt} : UniqSet elt -> list elt :=
  UniqFM.nonDetEltsUFM GHC.Base.∘ getUniqSet'.

Definition mapUniqSet {b} {a} `{Unique.Uniquable b}
   : (a -> b) -> UniqSet a -> UniqSet b :=
  fun f => mkUniqSet GHC.Base.∘ (GHC.Base.map f GHC.Base.∘ nonDetEltsUniqSet).

Definition nonDetFoldUniqSet {elt} {a}
   : (elt -> a -> a) -> a -> UniqSet elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | c, n, Mk_UniqSet _ s _ => UniqFM.nonDetFoldUFM c n s
    end.

Definition nonDetFoldUniqSet_Directly {elt} {a}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqSet elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, n, Mk_UniqSet _ s _ => UniqFM.nonDetFoldUFM_Directly f n s
    end.

Definition nonDetKeysUniqSet {elt} : UniqSet elt -> list Unique.Unique :=
  UniqFM.nonDetKeysUFM GHC.Base.∘ getUniqSet'.

(*
Definition partitionUniqSet {a}
   : (a -> bool) -> UniqSet a -> (UniqSet a * UniqSet a)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet _ s _ => GHC.Prim.coerce (UniqFM.partitionUFM p s)
    end.
*)

Program Definition restrictUniqSetToUFM {a} {b}
   : UniqSet a -> UniqFM.UniqFM b -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, m => Mk_UniqSet (UniqFM.intersectUFM s m) _
    end.
Next Obligation.
Admitted.

Definition sizeUniqSet {a} : UniqSet a -> nat :=
  fun '(Mk_UniqSet _ s _) => UniqFM.sizeUFM s.

Program Definition unionUniqSets {a} : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, Mk_UniqSet _ t _ => Mk_UniqSet (UniqFM.plusUFM s t) _
    end.
Next Obligation.
Admitted.

Definition unionManyUniqSets {a} `{Unique.Uniquable a} (xs : list (UniqSet a)) : UniqSet a :=
  match xs with
  | nil => emptyUniqSet
  | cons set sets => Data.Foldable.foldr unionUniqSets set sets
  end.

Definition uniqSetAll {a} : (a -> bool) -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet _ s _ => UniqFM.allUFM p s
    end.

Definition uniqSetAny {a} : (a -> bool) -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet _ s _ => UniqFM.anyUFM p s
    end.

Program Definition uniqSetMinusUFM {a} {b}
   : UniqSet a -> UniqFM.UniqFM b -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet _ s _, t => Mk_UniqSet (UniqFM.minusUFM s t) _
    end.
Next Obligation.
Admitted.

Program Definition unitUniqSet {a} `{Unique.Uniquable a} : a -> UniqSet a :=
  fun x => Mk_UniqSet (UniqFM.unitUFM x x) _.
Next Obligation.
Admitted.

(* Definition unsafeUFMToUniqSet {a} : UniqFM.UniqFM a -> UniqSet a :=
  Mk_UniqSet. *)

(* External variables:
     bool cons list nat op_zt__ option Data.Foldable.foldl' Data.Foldable.foldr
     GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.map GHC.Base.mappend
     GHC.Base.mappend__ GHC.Base.mconcat GHC.Base.mconcat__ GHC.Base.mempty
     GHC.Base.mempty__ GHC.Base.op_z2218U__ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Prim.Build_Unpeel GHC.Prim.Unpeel GHC.Prim.coerce
     UniqFM.UniqFM UniqFM.addToUFM UniqFM.allUFM UniqFM.anyUFM UniqFM.delFromUFM
     UniqFM.delFromUFM_Directly UniqFM.delListFromUFM UniqFM.delListFromUFM_Directly
     UniqFM.elemUFM UniqFM.elemUFM_Directly UniqFM.emptyUFM UniqFM.filterUFM
     UniqFM.filterUFM_Directly UniqFM.intersectUFM UniqFM.isNullUFM UniqFM.lookupUFM
     UniqFM.lookupUFM_Directly UniqFM.minusUFM UniqFM.nonDetEltsUFM
     UniqFM.nonDetFoldUFM UniqFM.nonDetFoldUFM_Directly UniqFM.nonDetKeysUFM
     UniqFM.partitionUFM UniqFM.plusUFM UniqFM.sizeUFM UniqFM.unitUFM
     Unique.Uniquable Unique.Unique
*)
