(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Base.

Module GHC.
  Module Err.
    Axiom error : forall {a}, GHC.Base.String -> a.
  End Err.
End GHC.

(* Converted imports: *)

Require Data.Bits.
Require Data.Either.
Require Data.Foldable.
Require GHC.Base.
Require GHC.Num.
Require Nat.
Require Utils.Containers.Internal.PtrEquality.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Size :=
  GHC.Num.Int%type.

Inductive Set_ a : Type := Bin : Size -> a -> (Set_ a) -> (Set_ a) -> Set_ a
                        |  Tip : Set_ a.

Inductive MergeSet a : Type := Mk_MergeSet : Set_ a -> MergeSet a.

Arguments Bin {_} _ _ _ _.

Arguments Tip {_}.

Arguments Mk_MergeSet {_} _.

Definition getMergeSet {a} (arg_0__ : MergeSet a) :=
  match arg_0__ with
    | Mk_MergeSet getMergeSet => getMergeSet
  end.
(* Midamble *)

Require Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Fixpoint set_size {a} (s : Set_ a) : nat :=
  match s with
  | Tip => 0
  | Bin _ _ s1 s2 => 1 + set_size s1 + set_size s2
  end.

(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom patternFailure : forall {a}, a.

Axiom unsafeFix : forall {a}, (a -> a) -> a.

(* Skipping instance Monoid__Set_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a},
   Data.Semigroup.Semigroup (Data.Set.Internal.Set_ a)' failed: OOPS! Cannot find
   information for class Qualified "Data.Semigroup" "Semigroup" unsupported *)

Local Definition Foldable__Set__elem : forall {a},
                                         forall `{GHC.Base.Eq_ a}, a -> Set_ a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | _ , Tip => false
                   | x , Bin _ y l r => orb (x GHC.Base.== y) (orb (go x l) (go x r))
                 end in
    go.

Local Definition Foldable__Set__fold : forall {m},
                                         forall `{GHC.Base.Monoid m}, Set_ m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    let fix go arg_0__
              := let j_3__ :=
                   match arg_0__ with
                     | Bin _ k l r => GHC.Base.mappend (go l) (GHC.Base.mappend k (go r))
                     | _ => patternFailure
                   end in
                 match arg_0__ with
                   | Tip => GHC.Base.mempty
                   | Bin num_1__ k _ _ => if num_1__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                          then k
                                          else j_3__
                 end in
    go.

Local Definition Foldable__Set__foldMap : forall {m} {a},
                                            forall `{GHC.Base.Monoid m}, (a -> m) -> Set_ a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f t =>
      let fix go arg_0__
                := let j_3__ :=
                     match arg_0__ with
                       | Bin _ k l r => GHC.Base.mappend (go l) (GHC.Base.mappend (f k) (go r))
                       | _ => patternFailure
                     end in
                   match arg_0__ with
                     | Tip => GHC.Base.mempty
                     | Bin num_1__ k _ _ => if num_1__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                            then f k
                                            else j_3__
                   end in
      go t.

(* Translating `instance forall {a}, forall `{Data.Data.Data a} `{GHC.Base.Ord
   a}, Data.Data.Data (Data.Set.Internal.Set_ a)' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Base.Ord a)}, GHC.Exts.IsList
   (Data.Set.Internal.Set_ a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Exts" "IsList" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Set.Internal.Set_ a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Data.Functor.Classes.Eq1 Data.Set.Internal.Set_'
   failed: OOPS! Cannot find information for class Qualified "Data.Functor.Classes"
   "Eq1" unsupported *)

(* Translating `instance Data.Functor.Classes.Ord1 Data.Set.Internal.Set_'
   failed: OOPS! Cannot find information for class Qualified "Data.Functor.Classes"
   "Ord1" unsupported *)

(* Translating `instance Data.Functor.Classes.Show1 Data.Set.Internal.Set_'
   failed: OOPS! Cannot find information for class Qualified "Data.Functor.Classes"
   "Show1" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a} `{GHC.Base.Ord
   a}, GHC.Read.Read (Data.Set.Internal.Set_ a)' failed: OOPS! Cannot find
   information for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{Control.DeepSeq.NFData a},
   Control.DeepSeq.NFData (Data.Set.Internal.Set_ a)' failed: OOPS! Cannot find
   information for class Qualified "Control.DeepSeq" "NFData" unsupported *)

(* Translating `instance forall {a}, Data.Semigroup.Semigroup
   (Data.Set.Internal.MergeSet a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Semigroup" "Semigroup" unsupported *)

(* Skipping instance Monoid__MergeSet *)

Definition combineEq {a} `{GHC.Base.Eq_ a} : list a -> list a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => nil
      | cons x xs => let fix combineEq' arg_1__ arg_2__
                               := match arg_1__ , arg_2__ with
                                    | z , nil => cons z nil
                                    | z , cons y ys => if z GHC.Base.== y : bool
                                                       then combineEq' z ys
                                                       else cons z (combineEq' y ys)
                                  end in
                     combineEq' x xs
    end.

Definition delta : GHC.Num.Int :=
  GHC.Num.fromInteger 3.

Definition empty {a} : Set_ a :=
  Tip.

Definition foldl {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ x l r => go (f (go z' l) x) r
                 end in
    go z.

Definition foldlFB {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  foldl.

Definition toDescList {a} : Set_ a -> list a :=
  foldl (GHC.Base.flip cons) nil.

Local Definition Foldable__Set__foldl : forall {b} {a},
                                          (b -> a -> b) -> b -> Set_ a -> b :=
  fun {b} {a} => foldl.

Definition foldl' {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ x l r => go (f (go z' l) x) r
                 end in
    go z.

Local Definition Foldable__Set__sum : forall {a},
                                        forall `{GHC.Num.Num a}, Set_ a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.+_ (GHC.Num.fromInteger 0).

Local Definition Foldable__Set__product : forall {a},
                                            forall `{GHC.Num.Num a}, Set_ a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.*_ (GHC.Num.fromInteger 1).

Local Definition Foldable__Set__foldl' : forall {b} {a},
                                           (b -> a -> b) -> b -> Set_ a -> b :=
  fun {b} {a} => foldl'.

Definition foldr {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ x l r => go (f x (go z' r)) l
                 end in
    go z.

Definition foldrFB {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  foldr.

Definition toAscList {a} : Set_ a -> list a :=
  foldr cons nil.

Definition toList {a} : Set_ a -> list a :=
  toAscList.

Local Definition Foldable__Set__toList : forall {a}, Set_ a -> list a :=
  fun {a} => toList.

Definition elems {a} : Set_ a -> list a :=
  toAscList.

Local Definition Ord__Set__compare {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                     inst_a) -> (Set_ inst_a) -> comparison :=
  fun s1 s2 => GHC.Base.compare (toAscList s1) (toAscList s2).

Local Definition Ord__Set__op_zg__ {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                     inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Set__compare x y) Gt.

Local Definition Ord__Set__op_zgze__ {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                       inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Set__compare x y) Lt.

Local Definition Ord__Set__op_zl__ {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                     inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Set__compare x y) Lt.

Local Definition Ord__Set__op_zlze__ {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                       inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Set__compare x y) Gt.

Local Definition Ord__Set__max {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                 inst_a) -> (Set_ inst_a) -> (Set_ inst_a) :=
  fun x y => if Ord__Set__op_zlze__ x y : bool then y else x.

Local Definition Ord__Set__min {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                 inst_a) -> (Set_ inst_a) -> (Set_ inst_a) :=
  fun x y => if Ord__Set__op_zlze__ x y : bool then x else y.

Definition fold {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  foldr.

Local Definition Foldable__Set__foldr : forall {a} {b},
                                          (a -> b -> b) -> b -> Set_ a -> b :=
  fun {a} {b} => foldr.

Definition foldr' {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ x l r => go (f x (go z' r)) l
                 end in
    go z.

Local Definition Foldable__Set__foldr' : forall {a} {b},
                                           (a -> b -> b) -> b -> Set_ a -> b :=
  fun {a} {b} => foldr'.

Definition lookupGE {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let fix goJust arg_0__ arg_1__ arg_2__
            := match arg_0__ , arg_1__ , arg_2__ with
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => match GHC.Base.compare x y with
                                               | Lt => goJust x y l
                                               | Eq => Some y
                                               | Gt => goJust x best r
                                             end
               end in
  let fix goNothing arg_11__ arg_12__
            := match arg_11__ , arg_12__ with
                 | _ , Tip => None
                 | x , Bin _ y l r => match GHC.Base.compare x y with
                                        | Lt => goJust x y l
                                        | Eq => Some y
                                        | Gt => goNothing x r
                                      end
               end in
  goNothing.

Definition lookupGT {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let fix goJust arg_0__ arg_1__ arg_2__
            := match arg_0__ , arg_1__ , arg_2__ with
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => if x GHC.Base.< y : bool
                                             then goJust x y l
                                             else goJust x best r
               end in
  let fix goNothing arg_7__ arg_8__
            := match arg_7__ , arg_8__ with
                 | _ , Tip => None
                 | x , Bin _ y l r => if x GHC.Base.< y : bool
                                      then goJust x y l
                                      else goNothing x r
               end in
  goNothing.

Definition lookupLE {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let fix goJust arg_0__ arg_1__ arg_2__
            := match arg_0__ , arg_1__ , arg_2__ with
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => match GHC.Base.compare x y with
                                               | Lt => goJust x best l
                                               | Eq => Some y
                                               | Gt => goJust x y r
                                             end
               end in
  let fix goNothing arg_11__ arg_12__
            := match arg_11__ , arg_12__ with
                 | _ , Tip => None
                 | x , Bin _ y l r => match GHC.Base.compare x y with
                                        | Lt => goNothing x l
                                        | Eq => Some y
                                        | Gt => goJust x y r
                                      end
               end in
  goNothing.

Definition lookupLT {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let fix goJust arg_0__ arg_1__ arg_2__
            := match arg_0__ , arg_1__ , arg_2__ with
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => if x GHC.Base.<= y : bool
                                             then goJust x best l
                                             else goJust x y r
               end in
  let fix goNothing arg_7__ arg_8__
            := match arg_7__ , arg_8__ with
                 | _ , Tip => None
                 | x , Bin _ y l r => if x GHC.Base.<= y : bool
                                      then goNothing x l
                                      else goJust x y r
               end in
  goNothing.

Definition lookupMaxSure {a} : a -> Set_ a -> a :=
  fix lookupMaxSure arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | x , Tip => x
             | _ , Bin _ x _ r => lookupMaxSure x r
           end.

Definition lookupMax {a} : Set_ a -> option a :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | Bin _ x _ r => Some GHC.Base.$! lookupMaxSure x r
    end.

Definition lookupMinSure {a} : a -> Set_ a -> a :=
  fix lookupMinSure arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | x , Tip => x
             | _ , Bin _ x l _ => lookupMinSure x l
           end.

Definition lookupMin {a} : Set_ a -> option a :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | Bin _ x l _ => Some GHC.Base.$! lookupMinSure x l
    end.

Definition mapMonotonic {a} {b} : (a -> b) -> Set_ a -> Set_ b :=
  fix mapMonotonic arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | f , Bin sz x l r => Bin sz (f x) (mapMonotonic f l) (mapMonotonic f r)
           end.

Definition member {a} `{GHC.Base.Ord a} : a -> Set_ a -> bool :=
  let fix go arg_0__ arg_1__
            := match arg_0__ , arg_1__ with
                 | _ , Tip => false
                 | x , Bin _ y l r => match GHC.Base.compare x y with
                                        | Lt => go x l
                                        | Gt => go x r
                                        | Eq => true
                                      end
               end in
  go.

Definition notMember {a} `{GHC.Base.Ord a} : a -> Set_ a -> bool :=
  fun a t => negb GHC.Base.$ member a t.

Definition node : GHC.Base.String :=
  GHC.Base.hs_string__ "+--".

Definition null {a} : Set_ a -> bool :=
  fun arg_0__ => match arg_0__ with | Tip => true | Bin _ _ _ _ => false end.

Local Definition Foldable__Set__null : forall {a}, Set_ a -> bool :=
  fun {a} => null.

Definition ordered {a} `{GHC.Base.Ord a} : Set_ a -> bool :=
  fun t =>
    let fix bounded lo hi t'
              := match t' with
                   | Tip => true
                   | Bin _ x l r => andb (lo x) (andb (hi x) (andb (bounded lo (fun arg_0__ =>
                                                                                 arg_0__ GHC.Base.< x) l) (bounded
                                                                   (fun arg_1__ => arg_1__ GHC.Base.> x) hi r)))
                 end in
    bounded (GHC.Base.const true) (GHC.Base.const true) t.

Definition ratio : GHC.Num.Int :=
  GHC.Num.fromInteger 2.

Definition singleton {a} : a -> Set_ a :=
  fun x => Bin (GHC.Num.fromInteger 1) x Tip Tip.

Definition splitRoot {a} : Set_ a -> list (Set_ a) :=
  fun orig =>
    match orig with
      | Tip => nil
      | Bin _ v l r => cons l (cons (singleton v) (cons r nil))
    end.

Definition size {a} : Set_ a -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => GHC.Num.fromInteger 0
      | Bin sz _ _ _ => sz
    end.

Definition validsize {a} : Set_ a -> bool :=
  fun t =>
    let fix realsize t'
              := match t' with
                   | Tip => Some (GHC.Num.fromInteger 0)
                   | Bin sz _ l r => match pair (realsize l) (realsize r) with
                                       | pair (Some n) (Some m) => if ((n GHC.Num.+ m) GHC.Num.+ GHC.Num.fromInteger 1)
                                                                      GHC.Base.== sz : bool
                                                                   then Some sz
                                                                   else None
                                       | _ => None
                                     end
                 end in
    (realsize t GHC.Base.== Some (size t)).

Definition lookupIndex {a} `{GHC.Base.Ord a} : a -> Set_ a -> option
                                               GHC.Num.Int :=
  let go {a} `{GHC.Base.Ord a} : GHC.Num.Int -> a -> Set_ a -> option
                                 GHC.Num.Int :=
    fix go arg_0__ arg_1__ arg_2__
          := match arg_0__ , arg_1__ , arg_2__ with
               | _ , _ , Tip => None
               | idx , x , Bin _ kx l r => match GHC.Base.compare x kx with
                                             | Lt => go idx x l
                                             | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ GHC.Num.fromInteger 1) x r
                                             | Eq => Some GHC.Base.$! (idx GHC.Num.+ size l)
                                           end
             end in
  go (GHC.Num.fromInteger 0).

Definition bin {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fun x l r =>
    Bin ((size l GHC.Num.+ size r) GHC.Num.+ GHC.Num.fromInteger 1) x l r.

Definition balanced {a} : Set_ a -> bool :=
  fix balanced t
        := match t with
             | Tip => true
             | Bin _ _ l r => andb (orb ((size l GHC.Num.+ size r) GHC.Base.<=
                                        GHC.Num.fromInteger 1) (andb (size l GHC.Base.<= (delta GHC.Num.* size r)) (size
                                                                     r GHC.Base.<= (delta GHC.Num.* size l)))) (andb
                                   (balanced l) (balanced r))
           end.

Definition valid {a} `{GHC.Base.Ord a} : Set_ a -> bool :=
  fun t => andb (balanced t) (andb (ordered t) (validsize t)).

Definition balanceR {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fun x l r =>
    match l with
      | Tip => match r with
                 | Tip => Bin (GHC.Num.fromInteger 1) x Tip Tip
                 | Bin _ _ Tip Tip => Bin (GHC.Num.fromInteger 2) x Tip r
                 | Bin _ rx Tip (Bin _ _ _ _ as rr) => Bin (GHC.Num.fromInteger 3) rx (Bin
                                                                                      (GHC.Num.fromInteger 1) x Tip Tip)
                                                       rr
                 | Bin _ rx (Bin _ rlx _ _) Tip => Bin (GHC.Num.fromInteger 3) rlx (Bin
                                                                                   (GHC.Num.fromInteger 1) x Tip Tip)
                                                   (Bin (GHC.Num.fromInteger 1) rx Tip Tip)
                 | Bin rs rx (Bin rls rlx rll rlr as rl) (Bin rrs _ _ _ as rr) => if rls
                                                                                     GHC.Base.< (ratio GHC.Num.*
                                                                                     rrs) : bool
                                                                                  then Bin (GHC.Num.fromInteger 1
                                                                                           GHC.Num.+ rs) rx (Bin
                                                                                                            (GHC.Num.fromInteger
                                                                                                            1 GHC.Num.+
                                                                                                            rls) x Tip
                                                                                                            rl) rr
                                                                                  else Bin (GHC.Num.fromInteger 1
                                                                                           GHC.Num.+ rs) rlx (Bin
                                                                                                             (GHC.Num.fromInteger
                                                                                                             1 GHC.Num.+
                                                                                                             size rll) x
                                                                                                             Tip rll)
                                                                                       (Bin ((GHC.Num.fromInteger 1
                                                                                            GHC.Num.+ rrs) GHC.Num.+
                                                                                            size rlr) rx rlr rr)
               end
      | Bin ls _ _ _ => match r with
                          | Tip => Bin (GHC.Num.fromInteger 1 GHC.Num.+ ls) x l Tip
                          | Bin rs rx rl rr => if rs GHC.Base.> (delta GHC.Num.* ls) : bool
                                               then let scrut_10__ := pair rl rr in
                                                    let j_12__ :=
                                                      match scrut_10__ with
                                                        | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                    "Failure in Data.Map.balanceR")
                                                      end in
                                                    match scrut_10__ with
                                                      | pair (Bin rls rlx rll rlr) (Bin rrs _ _ _) => if rls GHC.Base.<
                                                                                                         (ratio
                                                                                                         GHC.Num.*
                                                                                                         rrs) : bool
                                                                                                      then Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           ls) GHC.Num.+
                                                                                                           rs) rx (Bin
                                                                                                                  ((GHC.Num.fromInteger
                                                                                                                  1
                                                                                                                  GHC.Num.+
                                                                                                                  ls)
                                                                                                                  GHC.Num.+
                                                                                                                  rls) x
                                                                                                                  l rl)
                                                                                                           rr
                                                                                                      else Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           ls) GHC.Num.+
                                                                                                           rs) rlx (Bin
                                                                                                                   ((GHC.Num.fromInteger
                                                                                                                   1
                                                                                                                   GHC.Num.+
                                                                                                                   ls)
                                                                                                                   GHC.Num.+
                                                                                                                   size
                                                                                                                   rll)
                                                                                                                   x l
                                                                                                                   rll)
                                                                                                           (Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           rrs)
                                                                                                           GHC.Num.+
                                                                                                           size rlr) rx
                                                                                                           rlr rr)
                                                      | _ => j_12__
                                                    end
                                               else Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) x l r
                        end
    end.

Definition deleteMin {a} : Set_ a -> Set_ a :=
  fix deleteMin arg_0__
        := match arg_0__ with
             | Bin _ _ Tip r => r
             | Bin _ x l r => balanceR x (deleteMin l) r
             | Tip => Tip
           end.

Definition insertMax {a} : a -> Set_ a -> Set_ a :=
  fix insertMax x t
        := match t with
             | Tip => singleton x
             | Bin _ y l r => balanceR y l (insertMax x r)
           end.

Definition minViewSure {a} : a -> Set_ a -> Set_ a -> prod a (Set_ a) :=
  let fix go arg_0__ arg_1__ arg_2__
            := match arg_0__ , arg_1__ , arg_2__ with
                 | x , Tip , r => pair x r
                 | x , Bin _ xl ll lr , r => match go xl ll lr with
                                               | pair xm l' => pair xm (balanceR x l' r)
                                             end
               end in
  go.

Definition minView {a} : Set_ a -> option (a * Set_ a)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | Bin _ x l r => Some GHC.Base.$! (id GHC.Base.$ minViewSure x l r)
    end.

Definition balanceL {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fun x l r =>
    match r with
      | Tip => match l with
                 | Tip => Bin (GHC.Num.fromInteger 1) x Tip Tip
                 | Bin _ _ Tip Tip => Bin (GHC.Num.fromInteger 2) x l Tip
                 | Bin _ lx Tip (Bin _ lrx _ _) => Bin (GHC.Num.fromInteger 3) lrx (Bin
                                                                                   (GHC.Num.fromInteger 1) lx Tip Tip)
                                                   (Bin (GHC.Num.fromInteger 1) x Tip Tip)
                 | Bin _ lx (Bin _ _ _ _ as ll) Tip => Bin (GHC.Num.fromInteger 3) lx ll (Bin
                                                                                         (GHC.Num.fromInteger 1) x Tip
                                                                                         Tip)
                 | Bin ls lx (Bin lls _ _ _ as ll) (Bin lrs lrx lrl lrr as lr) => if lrs
                                                                                     GHC.Base.< (ratio GHC.Num.*
                                                                                     lls) : bool
                                                                                  then Bin (GHC.Num.fromInteger 1
                                                                                           GHC.Num.+ ls) lx ll (Bin
                                                                                                               (GHC.Num.fromInteger
                                                                                                               1
                                                                                                               GHC.Num.+
                                                                                                               lrs) x lr
                                                                                                               Tip)
                                                                                  else Bin (GHC.Num.fromInteger 1
                                                                                           GHC.Num.+ ls) lrx (Bin
                                                                                                             ((GHC.Num.fromInteger
                                                                                                             1 GHC.Num.+
                                                                                                             lls)
                                                                                                             GHC.Num.+
                                                                                                             size lrl)
                                                                                                             lx ll lrl)
                                                                                       (Bin (GHC.Num.fromInteger 1
                                                                                            GHC.Num.+ size lrr) x lrr
                                                                                       Tip)
               end
      | Bin rs _ _ _ => match l with
                          | Tip => Bin (GHC.Num.fromInteger 1 GHC.Num.+ rs) x Tip r
                          | Bin ls lx ll lr => if ls GHC.Base.> (delta GHC.Num.* rs) : bool
                                               then let scrut_10__ := pair ll lr in
                                                    let j_12__ :=
                                                      match scrut_10__ with
                                                        | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                    "Failure in Data.Map.balanceL")
                                                      end in
                                                    match scrut_10__ with
                                                      | pair (Bin lls _ _ _) (Bin lrs lrx lrl lrr) => if lrs GHC.Base.<
                                                                                                         (ratio
                                                                                                         GHC.Num.*
                                                                                                         lls) : bool
                                                                                                      then Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           ls) GHC.Num.+
                                                                                                           rs) lx ll
                                                                                                           (Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           rs) GHC.Num.+
                                                                                                           lrs) x lr r)
                                                                                                      else Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           ls) GHC.Num.+
                                                                                                           rs) lrx (Bin
                                                                                                                   ((GHC.Num.fromInteger
                                                                                                                   1
                                                                                                                   GHC.Num.+
                                                                                                                   lls)
                                                                                                                   GHC.Num.+
                                                                                                                   size
                                                                                                                   lrl)
                                                                                                                   lx ll
                                                                                                                   lrl)
                                                                                                           (Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           rs) GHC.Num.+
                                                                                                           size lrr) x
                                                                                                           lrr r)
                                                      | _ => j_12__
                                                    end
                                               else Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) x l r
                        end
    end.

Definition deleteMax {a} : Set_ a -> Set_ a :=
  fix deleteMax arg_0__
        := match arg_0__ with
             | Bin _ _ l Tip => l
             | Bin _ x l r => balanceL x l (deleteMax r)
             | Tip => Tip
           end.

Definition insert {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  fun x0 =>
    let go {a} `{GHC.Base.Ord a} : a -> a -> Set_ a -> Set_ a :=
      fix go arg_0__ arg_1__ arg_2__
            := match arg_0__ , arg_1__ , arg_2__ with
                 | orig , _ , Tip => singleton (id orig)
                 | orig , x , (Bin sz y l r as t) => match GHC.Base.compare x y with
                                                       | Lt => match go orig x l with
                                                                 | l' => if Utils.Containers.Internal.PtrEquality.ptrEq
                                                                            l' l : bool
                                                                         then t
                                                                         else balanceL y l' r
                                                               end
                                                       | Gt => match go orig x r with
                                                                 | r' => if Utils.Containers.Internal.PtrEquality.ptrEq
                                                                            r' r : bool
                                                                         then t
                                                                         else balanceR y l r'
                                                               end
                                                       | Eq => if (Utils.Containers.Internal.PtrEquality.ptrEq orig
                                                                                                               y) : bool
                                                               then t
                                                               else Bin sz (id orig) l r
                                                     end
               end in
    go x0 x0.

Definition insertMin {a} : a -> Set_ a -> Set_ a :=
  fix insertMin x t
        := match t with
             | Tip => singleton x
             | Bin _ y l r => balanceL y (insertMin x l) r
           end.

Definition insertR {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  fun x0 =>
    let go {a} `{GHC.Base.Ord a} : a -> a -> Set_ a -> Set_ a :=
      fix go arg_0__ arg_1__ arg_2__
            := match arg_0__ , arg_1__ , arg_2__ with
                 | orig , _ , Tip => singleton (id orig)
                 | orig , x , (Bin _ y l r as t) => match GHC.Base.compare x y with
                                                      | Lt => match go orig x l with
                                                                | l' => if Utils.Containers.Internal.PtrEquality.ptrEq
                                                                           l' l : bool
                                                                        then t
                                                                        else balanceL y l' r
                                                              end
                                                      | Gt => match go orig x r with
                                                                | r' => if Utils.Containers.Internal.PtrEquality.ptrEq
                                                                           r' r : bool
                                                                        then t
                                                                        else balanceR y l r'
                                                              end
                                                      | Eq => t
                                                    end
               end in
    go x0 x0.

Program Fixpoint link {a} (arg_0__ : a) (arg_1__ : Set_ a) (arg_2__ : Set_
                                                                      a) { measure (Nat.add (set_size arg_1__) (set_size
                                                                                            arg_2__)) } : Set_ a :=
match arg_0__ , arg_1__ , arg_2__ with
  | x , Tip , r => insertMin x r
  | x , l , Tip => insertMax x l
  | x , (Bin sizeL y ly ry as l) , (Bin sizeR z lz rz as r) => if (delta GHC.Num.*
                                                                  sizeL) GHC.Base.< sizeR : bool
                                                               then balanceL z (link x l lz) rz
                                                               else if (delta GHC.Num.* sizeR) GHC.Base.< sizeL : bool
                                                                    then balanceR y ly (link x ry r)
                                                                    else bin x l r
end.
Solve Obligations with (termination_by_omega).

Definition dropWhileAntitone {a} : (a -> bool) -> Set_ a -> Set_ a :=
  fix dropWhileAntitone arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | p , Bin _ x l r => if p x : bool
                                  then dropWhileAntitone p r
                                  else link x (dropWhileAntitone p l) r
           end.

Definition fromDistinctAscList {a} : list a -> Set_ a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Tip
      | cons x0 xs0 => let create :=
                         unsafeFix (fun create arg_1__ arg_2__ =>
                                     match arg_1__ , arg_2__ with
                                       | _ , nil => (pair Tip nil)
                                       | s , (cons x xs' as xs) => if s GHC.Base.== GHC.Num.fromInteger 1 : bool
                                                                   then (pair (Bin (GHC.Num.fromInteger 1) x Tip Tip)
                                                                              xs')
                                                                   else match create (Data.Bits.shiftR s
                                                                                                       (GHC.Num.fromInteger
                                                                                                       1)) xs with
                                                                          | (pair _ nil as res) => res
                                                                          | pair l (cons y ys) => match create
                                                                                                          (Data.Bits.shiftR
                                                                                                          s
                                                                                                          (GHC.Num.fromInteger
                                                                                                          1)) ys with
                                                                                                    | pair r zs => (pair
                                                                                                                   (link
                                                                                                                   y l
                                                                                                                   r)
                                                                                                                   zs)
                                                                                                  end
                                                                        end
                                     end) in
                       let go :=
                         unsafeFix (fun go arg_13__ arg_14__ arg_15__ =>
                                     match arg_13__ , arg_14__ , arg_15__ with
                                       | _ , t , nil => t
                                       | s , l , cons x xs => match create s xs with
                                                                | pair r ys => match link x l r with
                                                                                 | t' => go (Data.Bits.shiftL s
                                                                                                              (GHC.Num.fromInteger
                                                                                                              1)) t' ys
                                                                               end
                                                              end
                                     end) in
                       go (GHC.Num.fromInteger 1 : GHC.Num.Int) (Bin (GHC.Num.fromInteger 1) x0 Tip
                                                                Tip) xs0
    end.

Definition fromAscList {a} `{GHC.Base.Eq_ a} : list a -> Set_ a :=
  fun xs => fromDistinctAscList (combineEq xs).

Definition fromDistinctDescList {a} : list a -> Set_ a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Tip
      | cons x0 xs0 => let create :=
                         unsafeFix (fun create arg_1__ arg_2__ =>
                                     match arg_1__ , arg_2__ with
                                       | _ , nil => (pair Tip nil)
                                       | s , (cons x xs' as xs) => if s GHC.Base.== GHC.Num.fromInteger 1 : bool
                                                                   then (pair (Bin (GHC.Num.fromInteger 1) x Tip Tip)
                                                                              xs')
                                                                   else match create (Data.Bits.shiftR s
                                                                                                       (GHC.Num.fromInteger
                                                                                                       1)) xs with
                                                                          | (pair _ nil as res) => res
                                                                          | pair r (cons y ys) => match create
                                                                                                          (Data.Bits.shiftR
                                                                                                          s
                                                                                                          (GHC.Num.fromInteger
                                                                                                          1)) ys with
                                                                                                    | pair l zs => (pair
                                                                                                                   (link
                                                                                                                   y l
                                                                                                                   r)
                                                                                                                   zs)
                                                                                                  end
                                                                        end
                                     end) in
                       let go :=
                         unsafeFix (fun go arg_13__ arg_14__ arg_15__ =>
                                     match arg_13__ , arg_14__ , arg_15__ with
                                       | _ , t , nil => t
                                       | s , r , cons x xs => match create s xs with
                                                                | pair l ys => match link x l r with
                                                                                 | t' => go (Data.Bits.shiftL s
                                                                                                              (GHC.Num.fromInteger
                                                                                                              1)) t' ys
                                                                               end
                                                              end
                                     end) in
                       go (GHC.Num.fromInteger 1 : GHC.Num.Int) (Bin (GHC.Num.fromInteger 1) x0 Tip
                                                                Tip) xs0
    end.

Definition fromDescList {a} `{GHC.Base.Eq_ a} : list a -> Set_ a :=
  fun xs => fromDistinctDescList (combineEq xs).

Definition fromList {a} `{GHC.Base.Ord a} : list a -> Set_ a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Tip
      | cons x nil => Bin (GHC.Num.fromInteger 1) x Tip Tip
      | cons x0 xs0 => let fromList' :=
                         fun t0 xs =>
                           let ins := fun t x => insert x t in Data.Foldable.foldl ins t0 xs in
                       let not_ordered :=
                         fun arg_4__ arg_5__ =>
                           match arg_4__ , arg_5__ with
                             | _ , nil => false
                             | x , cons y _ => x GHC.Base.>= y
                           end in
                       let create :=
                         unsafeFix (fun create arg_8__ arg_9__ =>
                                     match arg_8__ , arg_9__ with
                                       | _ , nil => pair (pair Tip nil) nil
                                       | s , (cons x xss as xs) => if s GHC.Base.== GHC.Num.fromInteger 1 : bool
                                                                   then if not_ordered x xss : bool
                                                                        then pair (pair (Bin (GHC.Num.fromInteger 1) x
                                                                                        Tip Tip) nil) xss
                                                                        else pair (pair (Bin (GHC.Num.fromInteger 1) x
                                                                                        Tip Tip) xss) nil
                                                                   else match create (Data.Bits.shiftR s
                                                                                                       (GHC.Num.fromInteger
                                                                                                       1)) xs with
                                                                          | (pair (pair _ nil) _ as res) => res
                                                                          | pair (pair l (cons y nil)) zs => pair (pair
                                                                                                                  (insertMax
                                                                                                                  y l)
                                                                                                                  nil)
                                                                                                                  zs
                                                                          | pair (pair l (cons y yss as ys)) _ =>
                                                                            if not_ordered y yss : bool
                                                                            then pair (pair l nil) ys
                                                                            else match create (Data.Bits.shiftR s
                                                                                                                (GHC.Num.fromInteger
                                                                                                                1))
                                                                                         yss with
                                                                                   | pair (pair r zs) ws => pair (pair
                                                                                                                 (link y
                                                                                                                 l r)
                                                                                                                 zs) ws
                                                                                 end
                                                                        end
                                     end) in
                       let go :=
                         unsafeFix (fun go arg_22__ arg_23__ arg_24__ =>
                                     match arg_22__ , arg_23__ , arg_24__ with
                                       | _ , t , nil => t
                                       | _ , t , cons x nil => insertMax x t
                                       | s , l , (cons x xss as xs) => if not_ordered x xss : bool
                                                                       then fromList' l xs
                                                                       else match create s xss with
                                                                              | pair (pair r ys) nil => go
                                                                                                        (Data.Bits.shiftL
                                                                                                        s
                                                                                                        (GHC.Num.fromInteger
                                                                                                        1)) (link x l r)
                                                                                                        ys
                                                                              | pair (pair r _) ys => fromList' (link x
                                                                                                                l r) ys
                                                                            end
                                     end) in
                       if not_ordered x0 xs0 : bool
                       then fromList' (Bin (GHC.Num.fromInteger 1) x0 Tip Tip) xs0
                       else go (GHC.Num.fromInteger 1 : GHC.Num.Int) (Bin (GHC.Num.fromInteger 1) x0
                                                                     Tip Tip) xs0
    end.

Definition map {b} {a} `{GHC.Base.Ord b} : (a -> b) -> Set_ a -> Set_ b :=
  fun f => fromList GHC.Base.∘ (GHC.Base.map f GHC.Base.∘ toList).

Definition spanAntitone {a} : (a -> bool) -> Set_ a -> (Set_ a * Set_ a)%type :=
  fun p0 m =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | _ , Tip => pair Tip Tip
                   | p , Bin _ x l r => if p x : bool
                                        then match go p r with
                                               | pair u v => pair (link x l u) v
                                             end
                                        else match go p l with
                                               | pair u v => pair u (link x v r)
                                             end
                 end in
    id (go p0 m).

Definition splitMember {a} `{GHC.Base.Ord a} : a -> Set_ a -> (Set_ a * bool *
                                               Set_ a)%type :=
  fix splitMember arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => pair (pair Tip false) Tip
             | x , Bin _ y l r => match GHC.Base.compare x y with
                                    | Lt => match splitMember x l with
                                              | pair (pair lt found) gt => match link y gt r with
                                                                             | gt' => pair (pair lt found) gt'
                                                                           end
                                            end
                                    | Gt => match splitMember x r with
                                              | pair (pair lt found) gt => match link y l lt with
                                                                             | lt' => pair (pair lt' found) gt
                                                                           end
                                            end
                                    | Eq => pair (pair l true) r
                                  end
           end.

Definition disjoint {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> bool :=
  fix disjoint arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | Tip , _ => true
             | _ , Tip => true
             | Bin _ x l r , t => match splitMember x t with
                                    | pair (pair lt found) gt => andb (negb found) (andb (disjoint l lt) (disjoint r
                                                                                         gt))
                                  end
           end.

Definition isSubsetOfX {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> bool :=
  fix isSubsetOfX arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | Tip , _ => true
             | _ , Tip => false
             | Bin _ x l r , t => match splitMember x t with
                                    | pair (pair lt found) gt => andb found (andb (isSubsetOfX l lt) (isSubsetOfX r
                                                                                  gt))
                                  end
           end.

Definition splitS {a} `{GHC.Base.Ord a} : a -> Set_ a -> prod (Set_ a) (Set_
                                                                       a) :=
  fix splitS arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => (pair Tip Tip)
             | x , Bin _ y l r => match GHC.Base.compare x y with
                                    | Lt => match splitS x l with
                                              | pair lt gt => (pair lt (link y gt r))
                                            end
                                    | Gt => match splitS x r with
                                              | pair lt gt => (pair (link y l lt) gt)
                                            end
                                    | Eq => (pair l r)
                                  end
           end.

Definition split {a} `{GHC.Base.Ord a} : a -> Set_ a -> (Set_ a * Set_
                                         a)%type :=
  fun x t => id GHC.Base.$ splitS x t.

Definition takeWhileAntitone {a} : (a -> bool) -> Set_ a -> Set_ a :=
  fix takeWhileAntitone arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | p , Bin _ x l r => if p x : bool
                                  then link x l (takeWhileAntitone p r)
                                  else takeWhileAntitone p l
           end.

Definition union {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fix union arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | t1 , Tip => t1
             | t1 , Bin _ x Tip Tip => insertR x t1
             | Bin _ x Tip Tip , t2 => insert x t2
             | Tip , t2 => t2
             | (Bin _ x l1 r1 as t1) , t2 => match splitS x t2 with
                                               | pair l2 r2 => match union r1 r2 with
                                                                 | r1r2 => match union l1 l2 with
                                                                             | l1l2 => if andb
                                                                                          (Utils.Containers.Internal.PtrEquality.ptrEq
                                                                                          l1l2 l1)
                                                                                          (Utils.Containers.Internal.PtrEquality.ptrEq
                                                                                          r1r2 r1) : bool
                                                                                       then t1
                                                                                       else link x l1l2 r1r2
                                                                           end
                                                               end
                                             end
           end.

Definition unions {a} `{GHC.Base.Ord a} : list (Set_ a) -> Set_ a :=
  Data.Foldable.foldl union empty.

Definition maxViewSure {a} : a -> Set_ a -> Set_ a -> prod a (Set_ a) :=
  let fix go arg_0__ arg_1__ arg_2__
            := match arg_0__ , arg_1__ , arg_2__ with
                 | x , l , Tip => pair x l
                 | x , l , Bin _ xr rl rr => match go xr rl rr with
                                               | pair xm r' => pair xm (balanceL x l r')
                                             end
               end in
  go.

Definition maxView {a} : Set_ a -> option (a * Set_ a)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | Bin _ x l r => Some GHC.Base.$! (id GHC.Base.$ maxViewSure x l r)
    end.

Definition glue {a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Tip , r => r
      | l , Tip => l
      | (Bin sl xl ll lr as l) , (Bin sr xr rl rr as r) => if sl GHC.Base.> sr : bool
                                                           then match maxViewSure xl ll lr with
                                                                  | pair m l' => balanceR m l' r
                                                                end
                                                           else match minViewSure xr rl rr with
                                                                  | pair m r' => balanceL m l r'
                                                                end
    end.

Definition powerSet {a} : Set_ a -> Set_ (Set_ a) :=
  fun xs0 =>
    let step :=
      fun x pxs =>
        glue (insertMin (singleton x) (mapMonotonic (insertMin x) pxs)) pxs in
    insertMin empty (foldr' step Tip xs0).

Definition delete {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_0__ arg_1__
          := match arg_0__ , arg_1__ with
               | _ , Tip => Tip
               | x , (Bin _ y l r as t) => match GHC.Base.compare x y with
                                             | Lt => match go x l with
                                                       | l' => if Utils.Containers.Internal.PtrEquality.ptrEq l'
                                                                                                              l : bool
                                                               then t
                                                               else balanceR y l' r
                                                     end
                                             | Gt => match go x r with
                                                       | r' => if Utils.Containers.Internal.PtrEquality.ptrEq r'
                                                                                                              r : bool
                                                               then t
                                                               else balanceL y l r'
                                                     end
                                             | Eq => glue l r
                                           end
             end in
  go.

Program Fixpoint merge {a} (arg_0__ : Set_ a) (arg_1__ : Set_
                                                         a) { measure (Nat.add (set_size arg_0__) (set_size
                                                                               arg_1__)) } : Set_ a :=
match arg_0__ , arg_1__ with
  | Tip , r => r
  | l , Tip => l
  | (Bin sizeL x lx rx as l) , (Bin sizeR y ly ry as r) => if (delta GHC.Num.*
                                                              sizeL) GHC.Base.< sizeR : bool
                                                           then balanceL y (merge l ly) ry
                                                           else if (delta GHC.Num.* sizeR) GHC.Base.< sizeL : bool
                                                                then balanceR x lx (merge rx r)
                                                                else glue l r
end.
Solve Obligations with (termination_by_omega).

Definition disjointUnion {a} {b} : Set_ a -> Set_ b -> Set_ (Data.Either.Either
                                                            a b) :=
  fun as_ bs =>
    merge (mapMonotonic Data.Either.Left as_) (mapMonotonic Data.Either.Right bs).

Definition filter {a} : (a -> bool) -> Set_ a -> Set_ a :=
  fix filter arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | p , (Bin _ x l r as t) => match filter p r with
                                           | r' => match filter p l with
                                                     | l' => if p x : bool
                                                             then if andb (Utils.Containers.Internal.PtrEquality.ptrEq l
                                                                                                                       l')
                                                                          (Utils.Containers.Internal.PtrEquality.ptrEq r
                                                                                                                       r') : bool
                                                                  then t
                                                                  else link x l' r'
                                                             else merge l' r'
                                                   end
                                         end
           end.

Definition intersection {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fix intersection arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | Tip , _ => Tip
             | _ , Tip => Tip
             | (Bin _ x l1 r1 as t1) , t2 => match splitMember x t2 with
                                               | pair (pair l2 b) r2 => match intersection l1 l2 with
                                                                          | l1l2 => match intersection r1 r2 with
                                                                                      | r1r2 => if b : bool
                                                                                                then if andb
                                                                                                        (Utils.Containers.Internal.PtrEquality.ptrEq
                                                                                                        l1l2 l1)
                                                                                                        (Utils.Containers.Internal.PtrEquality.ptrEq
                                                                                                        r1r2 r1) : bool
                                                                                                     then t1
                                                                                                     else link x l1l2
                                                                                                          r1r2
                                                                                                else merge l1l2 r1r2
                                                                                    end
                                                                        end
                                             end
           end.

Definition partition {a} : (a -> bool) -> Set_ a -> (Set_ a * Set_ a)%type :=
  fun p0 t0 =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | _ , Tip => (pair Tip Tip)
                   | p , (Bin _ x l r as t) => match pair (go p l) (go p r) with
                                                 | pair (pair l1 l2) (pair r1 r2) => if p x : bool
                                                                                     then pair (if andb
                                                                                                   (Utils.Containers.Internal.PtrEquality.ptrEq
                                                                                                   l1 l)
                                                                                                   (Utils.Containers.Internal.PtrEquality.ptrEq
                                                                                                   r1 r) : bool
                                                                                               then t
                                                                                               else link x l1 r1) (merge
                                                                                               l2 r2)
                                                                                     else pair (merge l1 r1) (if andb
                                                                                                                 (Utils.Containers.Internal.PtrEquality.ptrEq
                                                                                                                 l2 l)
                                                                                                                 (Utils.Containers.Internal.PtrEquality.ptrEq
                                                                                                                 r2
                                                                                                                 r) : bool
                                                                                               then t
                                                                                               else link x l2 r2)
                                               end
                 end in
    id GHC.Base.$ go p0 t0.

Definition drop {a} : GHC.Num.Int -> Set_ a -> Set_ a :=
  fun arg_0__ arg_1__ =>
    let j_15__ :=
      match arg_0__ , arg_1__ with
        | i0 , m0 => let fix go arg_2__ arg_3__
                               := let j_11__ :=
                                    match arg_2__ , arg_3__ with
                                      | _ , Tip => Tip
                                      | i , Bin _ x l r => let sizeL := size l in
                                                           match GHC.Base.compare i sizeL with
                                                             | Lt => link x (go i l) r
                                                             | Gt => go ((i GHC.Num.- sizeL) GHC.Num.-
                                                                        GHC.Num.fromInteger 1) r
                                                             | Eq => insertMin x r
                                                           end
                                    end in
                                  match arg_2__ , arg_3__ with
                                    | i , m => if i GHC.Base.<= GHC.Num.fromInteger 0 : bool
                                               then m
                                               else j_11__
                                  end in
                     go i0 m0
      end in
    match arg_0__ , arg_1__ with
      | i , m => if i GHC.Base.>= size m : bool
                 then Tip
                 else j_15__
    end.

Definition splitAt {a} : GHC.Num.Int -> Set_ a -> (Set_ a * Set_ a)%type :=
  fun i0 m0 =>
    let fix go arg_0__ arg_1__
              := let j_16__ :=
                   match arg_0__ , arg_1__ with
                     | _ , Tip => pair Tip Tip
                     | i , Bin _ x l r => let sizeL := size l in
                                          match GHC.Base.compare i sizeL with
                                            | Lt => match go i l with
                                                      | pair ll lr => pair ll (link x lr r)
                                                    end
                                            | Gt => match go ((i GHC.Num.- sizeL) GHC.Num.- GHC.Num.fromInteger 1)
                                                            r with
                                                      | pair rl rr => pair (link x l rl) rr
                                                    end
                                            | Eq => pair l (insertMin x r)
                                          end
                   end in
                 match arg_0__ , arg_1__ with
                   | i , m => if i GHC.Base.<= GHC.Num.fromInteger 0 : bool
                              then pair Tip m
                              else j_16__
                 end in
    if i0 GHC.Base.>= size m0 : bool
    then pair m0 Tip
    else id GHC.Base.$ go i0 m0.

Definition isSubsetOf {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> bool :=
  fun t1 t2 => andb (size t1 GHC.Base.<= size t2) (isSubsetOfX t1 t2).

Definition isProperSubsetOf {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> bool :=
  fun s1 s2 => andb (size s1 GHC.Base.< size s2) (isSubsetOf s1 s2).

Definition take {a} : GHC.Num.Int -> Set_ a -> Set_ a :=
  fun arg_0__ arg_1__ =>
    let j_14__ :=
      match arg_0__ , arg_1__ with
        | i0 , m0 => let fix go arg_2__ arg_3__
                               := let j_10__ :=
                                    match arg_2__ , arg_3__ with
                                      | _ , Tip => Tip
                                      | i , Bin _ x l r => let sizeL := size l in
                                                           match GHC.Base.compare i sizeL with
                                                             | Lt => go i l
                                                             | Gt => link x l (go ((i GHC.Num.- sizeL) GHC.Num.-
                                                                                  GHC.Num.fromInteger 1) r)
                                                             | Eq => l
                                                           end
                                    end in
                                  match arg_2__ , arg_3__ with
                                    | i , _ => if i GHC.Base.<= GHC.Num.fromInteger 0 : bool
                                               then Tip
                                               else j_10__
                                  end in
                     go i0 m0
      end in
    match arg_0__ , arg_1__ with
      | i , m => if i GHC.Base.>= size m : bool
                 then m
                 else j_14__
    end.

Definition difference {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fix difference arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | Tip , _ => Tip
             | t1 , Tip => t1
             | t1 , Bin _ x l2 r2 => match split x t1 with
                                       | pair l1 r1 => match difference r1 r2 with
                                                         | r1r2 => match difference l1 l2 with
                                                                     | l1l2 => if (size l1l2 GHC.Num.+ size r1r2)
                                                                                  GHC.Base.== size t1 : bool
                                                                               then t1
                                                                               else merge l1l2 r1r2
                                                                   end
                                                       end
                                     end
           end.

Definition op_zrzr__ {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fun m1 m2 => difference m1 m2.

Notation "'_\\_'" := (op_zrzr__).

Infix "\\" := (_\\_) (at level 99).

Local Definition Eq___Set__op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : (Set_
                                                                       inst_a) -> (Set_ inst_a) -> bool :=
  fun t1 t2 =>
    andb (size t1 GHC.Base.== size t2) (toAscList t1 GHC.Base.== toAscList t2).

Local Definition Eq___Set__op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : (Set_
                                                                       inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => negb (Eq___Set__op_zeze__ x y).

Program Instance Eq___Set_ {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Set_ a) :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Set__op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Set__op_zsze__ |}.

Program Instance Ord__Set_ {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Set_ a) :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Set__op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Set__op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Set__op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Set__op_zgze__ ;
      GHC.Base.compare__ := Ord__Set__compare ;
      GHC.Base.max__ := Ord__Set__max ;
      GHC.Base.min__ := Ord__Set__min |}.

Local Definition Foldable__Set__length : forall {a}, Set_ a -> GHC.Num.Int :=
  fun {a} => size.

Program Instance Foldable__Set_ : Data.Foldable.Foldable Set_ := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Set__elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Set__fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Set__foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Set__foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Set__foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Set__foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Set__foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Set__length ;
      Data.Foldable.null__ := fun {a} => Foldable__Set__null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Set__product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Set__sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Set__toList |}.

Definition withBar : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "|  ") bars.

Definition withEmpty : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "   ") bars.

Module Notations.
Notation "'_Data.Set.Internal.\\_'" := (op_zrzr__).
Infix "Data.Set.Internal.\\" := (_\\_) (at level 99).
End Notations.

(* Unbound variables:
     Eq Gt Lt None Some andb bool comparison cons false id list negb nil op_zt__
     option orb pair prod set_size true Data.Bits.shiftL Data.Bits.shiftR
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Foldable.Foldable
     Data.Foldable.foldl GHC.Base.Eq_ GHC.Base.Monoid GHC.Base.Ord GHC.Base.String
     GHC.Base.compare GHC.Base.const GHC.Base.flip GHC.Base.map GHC.Base.mappend
     GHC.Base.mempty GHC.Base.op_z2218U__ GHC.Base.op_zd__ GHC.Base.op_zdzn__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Err.error GHC.Num.Int GHC.Num.Num
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ Nat.add
     Utils.Containers.Internal.PtrEquality.ptrEq
*)
