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

Inductive UniqSet a : Type
  := Mk_UniqSet (getUniqSet' : UniqFM.UniqFM a) : UniqSet a.

Arguments Mk_UniqSet {_} _.

Definition getUniqSet' {a} (arg_0__ : UniqSet a) :=
  let 'Mk_UniqSet getUniqSet' := arg_0__ in
  getUniqSet'.

(* Converted value declarations: *)

Definition unsafeUFMToUniqSet {a} : UniqFM.UniqFM a -> UniqSet a :=
  Mk_UniqSet.

Definition unitUniqSet {a} `{Unique.Uniquable a} : a -> UniqSet a :=
  fun x => Mk_UniqSet (UniqFM.unitUFM x x).

Definition uniqSetMinusUFM {a} {b}
   : UniqSet a -> UniqFM.UniqFM b -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, t => Mk_UniqSet (UniqFM.minusUFM s t)
    end.

Definition uniqSetAny {a} : (a -> bool) -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => UniqFM.anyUFM p s
    end.

Definition uniqSetAll {a} : (a -> bool) -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => UniqFM.allUFM p s
    end.

Definition unionUniqSets {a} : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => Mk_UniqSet (UniqFM.plusUFM s t)
    end.

Definition sizeUniqSet {a} : UniqSet a -> nat :=
  fun '(Mk_UniqSet s) => UniqFM.sizeUFM s.

Definition restrictUniqSetToUFM {a} {b}
   : UniqSet a -> UniqFM.UniqFM b -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, m => Mk_UniqSet (UniqFM.intersectUFM s m)
    end.

Instance Unpeel_UniqSet ele
   : GHC.Prim.Unpeel (UniqSet ele) (UniqFM.UniqFM ele) :=
  GHC.Prim.Build_Unpeel _ _ (fun '(Mk_UniqSet y) => y) Mk_UniqSet.

Definition partitionUniqSet {a}
   : (a -> bool) -> UniqSet a -> (UniqSet a * UniqSet a)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => GHC.Prim.coerce (UniqFM.partitionUFM p s)
    end.

Definition nonDetKeysUniqSet {elt} : UniqSet elt -> list Unique.Unique :=
  UniqFM.nonDetKeysUFM GHC.Base.∘ getUniqSet'.

Definition nonDetFoldUniqSet_Directly {elt} {a}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqSet elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, n, Mk_UniqSet s => UniqFM.nonDetFoldUFM_Directly f n s
    end.

Definition nonDetFoldUniqSet {elt} {a}
   : (elt -> a -> a) -> a -> UniqSet elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | c, n, Mk_UniqSet s => UniqFM.nonDetFoldUFM c n s
    end.

Definition nonDetEltsUniqSet {elt} : UniqSet elt -> list elt :=
  UniqFM.nonDetEltsUFM GHC.Base.∘ getUniqSet'.

Definition minusUniqSet {a} : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => Mk_UniqSet (UniqFM.minusUFM s t)
    end.

Definition lookupUniqSet_Directly {a}
   : UniqSet a -> Unique.Unique -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, k => UniqFM.lookupUFM_Directly s k
    end.

Definition lookupUniqSet {a} {b} `{Unique.Uniquable a}
   : UniqSet b -> a -> option b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, k => UniqFM.lookupUFM s k
    end.

Definition isEmptyUniqSet {a} : UniqSet a -> bool :=
  fun '(Mk_UniqSet s) => UniqFM.isNullUFM s.

Definition intersectUniqSets {a} : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => Mk_UniqSet (UniqFM.intersectUFM s t)
    end.

Definition getUniqSet {a} : UniqSet a -> UniqFM.UniqFM a :=
  getUniqSet'.

Definition filterUniqSet_Directly {elt}
   : (Unique.Unique -> elt -> bool) -> UniqSet elt -> UniqSet elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_UniqSet s => Mk_UniqSet (UniqFM.filterUFM_Directly f s)
    end.

Definition filterUniqSet {a} : (a -> bool) -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => Mk_UniqSet (UniqFM.filterUFM p s)
    end.

Definition emptyUniqSet {a} : UniqSet a :=
  Mk_UniqSet UniqFM.emptyUFM.

Definition unionManyUniqSets {a} (xs : list (UniqSet a)) : UniqSet a :=
  match xs with
  | nil => emptyUniqSet
  | cons set sets => Data.Foldable.foldr unionUniqSets set sets
  end.

Definition elementOfUniqSet {a} `{Unique.Uniquable a}
   : a -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_UniqSet s => UniqFM.elemUFM a s
    end.

Definition elemUniqSet_Directly {a} : Unique.Unique -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_UniqSet s => UniqFM.elemUFM_Directly a s
    end.

Definition delOneFromUniqSet_Directly {a}
   : UniqSet a -> Unique.Unique -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, u => Mk_UniqSet (UniqFM.delFromUFM_Directly s u)
    end.

Definition delOneFromUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, a => Mk_UniqSet (UniqFM.delFromUFM s a)
    end.

Definition delListFromUniqSet_Directly {a}
   : UniqSet a -> list Unique.Unique -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, l => Mk_UniqSet (UniqFM.delListFromUFM_Directly s l)
    end.

Definition delListFromUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, l => Mk_UniqSet (UniqFM.delListFromUFM s l)
    end.

Definition addOneToUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet set, x => Mk_UniqSet (UniqFM.addToUFM set x x)
    end.

Definition mkUniqSet {a} `{Unique.Uniquable a} : list a -> UniqSet a :=
  Data.Foldable.foldl' addOneToUniqSet emptyUniqSet.

Definition mapUniqSet {b} {a} `{Unique.Uniquable b}
   : (a -> b) -> UniqSet a -> UniqSet b :=
  fun f => mkUniqSet GHC.Base.∘ (GHC.Base.map f GHC.Base.∘ nonDetEltsUniqSet).

Definition addListToUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  Data.Foldable.foldl' addOneToUniqSet.

(* Skipping all instances of class `Data.Data.Data', including
   `UniqSet.Data__UniqSet' *)

Local Definition Semigroup__UniqSet_op_zlzlzgzg__ {inst_a}
   : UniqSet inst_a -> UniqSet inst_a -> UniqSet inst_a :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__UniqSet {a} : GHC.Base.Semigroup (UniqSet a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__UniqSet_op_zlzlzgzg__ |}.

Local Definition Monoid__UniqSet_mappend {inst_a}
   : UniqSet inst_a -> UniqSet inst_a -> UniqSet inst_a :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Monoid__UniqSet_mconcat {inst_a}
   : list (UniqSet inst_a) -> UniqSet inst_a :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__UniqSet_mempty {inst_a} : UniqSet inst_a :=
  Mk_UniqSet GHC.Base.mempty.

Program Instance Monoid__UniqSet {a} : GHC.Base.Monoid (UniqSet a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__UniqSet_mappend ;
           GHC.Base.mconcat__ := Monoid__UniqSet_mconcat ;
           GHC.Base.mempty__ := Monoid__UniqSet_mempty |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `UniqSet.Outputable__UniqSet' *)

(* Skipping instance `UniqSet.Eq___UniqSet' of class `GHC.Base.Eq_' *)

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
