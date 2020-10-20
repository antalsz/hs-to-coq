(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BinInt.
Require Control.Monad.
Require Coq.Program.Basics.
Require Data.Either.
Require Data.Foldable.
Require Data.Maybe.
Require Data.OldList.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require MonadUtils.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Bag a : Type
  := | EmptyBag : Bag a
  |  UnitBag : a -> Bag a
  |  TwoBags : (Bag a) -> (Bag a) -> Bag a
  |  ListBag : list a -> Bag a.

Arguments EmptyBag {_}.

Arguments UnitBag {_} _.

Arguments TwoBags {_} _ _.

Arguments ListBag {_} _.

(* Midamble *)

Require ZArith.BinInt.

Instance Default_Bag {a} : GHC.Err.Default (Bag a):=
  GHC.Err.Build_Default _ EmptyBag.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Bag.Outputable__Bag' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Bag.Data__Bag' *)

Fixpoint mapBag {a} {b} (arg_0__ : (a -> b)) (arg_1__ : Bag a) : Bag b
           := match arg_0__, arg_1__ with
              | _, EmptyBag => EmptyBag
              | f, UnitBag x => UnitBag (f x)
              | f, TwoBags b1 b2 => TwoBags (mapBag f b1) (mapBag f b2)
              | f, ListBag xs => ListBag (GHC.Base.map f xs)
              end.

Local Definition Functor__Bag_fmap
   : forall {a} {b}, (a -> b) -> Bag a -> Bag b :=
  fun {a} {b} => mapBag.

Local Definition Functor__Bag_op_zlzd__ : forall {a} {b}, a -> Bag b -> Bag a :=
  fun {a} {b} => Functor__Bag_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Bag : GHC.Base.Functor Bag :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Bag_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Bag_op_zlzd__ |}.

Fixpoint foldrBag {a} {r} (arg_0__ : (a -> r -> r)) (arg_1__ : r) (arg_2__
                    : Bag a) : r
           := match arg_0__, arg_1__, arg_2__ with
              | _, z, EmptyBag => z
              | k, z, UnitBag x => k x z
              | k, z, TwoBags b1 b2 => foldrBag k (foldrBag k z b2) b1
              | k, z, ListBag xs => Data.Foldable.foldr k z xs
              end.

Local Definition Foldable__Bag_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Bag a -> b :=
  fun {a} {b} => foldrBag.

Local Definition Foldable__Bag_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Bag a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f => Foldable__Bag_foldr (GHC.Base.mappend GHC.Base.∘ f) GHC.Base.mempty.

Local Definition Foldable__Bag_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Bag m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Bag_foldMap GHC.Base.id.

Local Definition Foldable__Bag_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Bag a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Bag_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

Local Definition Foldable__Bag_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Bag a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Bag_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Bag_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Bag a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Bag_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Bag_length : forall {a}, Bag a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Bag_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

Local Definition Foldable__Bag_null : forall {a}, Bag a -> bool :=
  fun {a} => Foldable__Bag_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Bag_product
   : forall {a}, forall `{GHC.Num.Num a}, Bag a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Bag_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Bag_sum
   : forall {a}, forall `{GHC.Num.Num a}, Bag a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Bag_foldMap
                                Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Bag_toList : forall {a}, Bag a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Bag_foldr c n t)).

Program Instance Foldable__Bag : Data.Foldable.Foldable Bag :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Bag_fold ;
           Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
             Foldable__Bag_foldMap ;
           Data.Foldable.foldl__ := fun {b} {a} => Foldable__Bag_foldl ;
           Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Bag_foldl' ;
           Data.Foldable.foldr__ := fun {a} {b} => Foldable__Bag_foldr ;
           Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Bag_foldr' ;
           Data.Foldable.length__ := fun {a} => Foldable__Bag_length ;
           Data.Foldable.null__ := fun {a} => Foldable__Bag_null ;
           Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Bag_product ;
           Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Bag_sum ;
           Data.Foldable.toList__ := fun {a} => Foldable__Bag_toList |}.

Definition emptyBag {a} : Bag a :=
  EmptyBag.

Definition unitBag {a} : a -> Bag a :=
  UnitBag.

Fixpoint lengthBag {a} (arg_0__ : Bag a) : nat
           := match arg_0__ with
              | EmptyBag => #0
              | UnitBag _ => #1
              | TwoBags b1 b2 => lengthBag b1 GHC.Num.+ lengthBag b2
              | ListBag xs => BinInt.Z.to_nat (Data.Foldable.length xs)
              end.

Fixpoint elemBag {a} `{GHC.Base.Eq_ a} (arg_0__ : a) (arg_1__ : Bag a) : bool
           := match arg_0__, arg_1__ with
              | _, EmptyBag => false
              | x, UnitBag y => x GHC.Base.== y
              | x, TwoBags b1 b2 => orb (elemBag x b1) (elemBag x b2)
              | x, ListBag ys => Data.Foldable.any (fun arg_4__ => x GHC.Base.== arg_4__) ys
              end.

Definition unionBags {a} : Bag a -> Bag a -> Bag a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | EmptyBag, b => b
    | b, EmptyBag => b
    | b1, b2 => TwoBags b1 b2
    end.

Definition unionManyBags {a} : list (Bag a) -> Bag a :=
  fun xs => Data.Foldable.foldr unionBags EmptyBag xs.

Definition consBag {a} : a -> Bag a -> Bag a :=
  fun elt bag => unionBags (unitBag elt) bag.

Definition snocBag {a} : Bag a -> a -> Bag a :=
  fun bag elt => unionBags bag (unitBag elt).

Definition isEmptyBag {a} : Bag a -> bool :=
  fun arg_0__ => match arg_0__ with | EmptyBag => true | _ => false end.

Definition isSingletonBag {a} : Bag a -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | EmptyBag => false
    | UnitBag _ => true
    | TwoBags _ _ => false
    | ListBag xs => Util.isSingleton xs
    end.

Definition listToBag {a} : list a -> Bag a :=
  fun arg_0__ => match arg_0__ with | nil => EmptyBag | vs => ListBag vs end.

Fixpoint filterBag {a} (arg_0__ : (a -> bool)) (arg_1__ : Bag a) : Bag a
           := match arg_0__, arg_1__ with
              | _, EmptyBag => EmptyBag
              | pred, (UnitBag val as b) => if pred val : bool then b else EmptyBag
              | pred, TwoBags b1 b2 =>
                  let sat2 := filterBag pred b2 in
                  let sat1 := filterBag pred b1 in unionBags sat1 sat2
              | pred, ListBag vs => listToBag (GHC.List.filter pred vs)
              end.

Fixpoint filterBagM {m} {a} `{GHC.Base.Monad m} (arg_0__ : (a -> m bool))
                    (arg_1__ : Bag a) : m (Bag a)
           := match arg_0__, arg_1__ with
              | _, EmptyBag => GHC.Base.return_ EmptyBag
              | pred, (UnitBag val as b) =>
                  pred val GHC.Base.>>=
                  (fun flag =>
                     if flag : bool
                     then GHC.Base.return_ b
                     else GHC.Base.return_ EmptyBag)
              | pred, TwoBags b1 b2 =>
                  filterBagM pred b1 GHC.Base.>>=
                  (fun sat1 =>
                     filterBagM pred b2 GHC.Base.>>=
                     (fun sat2 => GHC.Base.return_ (unionBags sat1 sat2)))
              | pred, ListBag vs =>
                  Control.Monad.filterM pred vs GHC.Base.>>=
                  (fun sat => GHC.Base.return_ (listToBag sat))
              end.

Fixpoint allBag {a} (arg_0__ : (a -> bool)) (arg_1__ : Bag a) : bool
           := match arg_0__, arg_1__ with
              | _, EmptyBag => true
              | p, UnitBag v => p v
              | p, TwoBags b1 b2 => andb (allBag p b1) (allBag p b2)
              | p, ListBag xs => Data.Foldable.all p xs
              end.

Fixpoint anyBag {a} (arg_0__ : (a -> bool)) (arg_1__ : Bag a) : bool
           := match arg_0__, arg_1__ with
              | _, EmptyBag => false
              | p, UnitBag v => p v
              | p, TwoBags b1 b2 => orb (anyBag p b1) (anyBag p b2)
              | p, ListBag xs => Data.Foldable.any p xs
              end.

Fixpoint anyBagM {m} {a} `{GHC.Base.Monad m} (arg_0__ : (a -> m bool)) (arg_1__
                   : Bag a) : m bool
           := match arg_0__, arg_1__ with
              | _, EmptyBag => GHC.Base.return_ false
              | p, UnitBag v => p v
              | p, TwoBags b1 b2 =>
                  anyBagM p b1 GHC.Base.>>=
                  (fun flag => if flag : bool then GHC.Base.return_ true else anyBagM p b2)
              | p, ListBag xs => MonadUtils.anyM p xs
              end.

Definition concatBag {a} : Bag (Bag a) -> Bag a :=
  fun bss => let add := fun bs rs => unionBags bs rs in foldrBag add emptyBag bss.

Definition catBagMaybes {a} : Bag (option a) -> Bag a :=
  fun bs =>
    let add :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | None, rs => rs
        | Some x, rs => consBag x rs
        end in
    foldrBag add emptyBag bs.

Fixpoint partitionBag {a} (arg_0__ : (a -> bool)) (arg_1__ : Bag a) : (Bag a *
                                                                       Bag a)%type
           := match arg_0__, arg_1__ with
              | _, EmptyBag => pair EmptyBag EmptyBag
              | pred, (UnitBag val as b) =>
                  if pred val : bool
                  then pair b EmptyBag
                  else pair EmptyBag b
              | pred, TwoBags b1 b2 =>
                  let 'pair sat2 fail2 := partitionBag pred b2 in
                  let 'pair sat1 fail1 := partitionBag pred b1 in
                  pair (unionBags sat1 sat2) (unionBags fail1 fail2)
              | pred, ListBag vs =>
                  let 'pair sats fails := Data.OldList.partition pred vs in
                  pair (listToBag sats) (listToBag fails)
              end.

Fixpoint partitionBagWith {a} {b} {c} (arg_0__ : (a -> Data.Either.Either b c))
                          (arg_1__ : Bag a) : (Bag b * Bag c)%type
           := match arg_0__, arg_1__ with
              | _, EmptyBag => pair EmptyBag EmptyBag
              | pred, UnitBag val =>
                  match pred val with
                  | Data.Either.Left a => pair (UnitBag a) EmptyBag
                  | Data.Either.Right b => pair EmptyBag (UnitBag b)
                  end
              | pred, TwoBags b1 b2 =>
                  let 'pair sat2 fail2 := partitionBagWith pred b2 in
                  let 'pair sat1 fail1 := partitionBagWith pred b1 in
                  pair (unionBags sat1 sat2) (unionBags fail1 fail2)
              | pred, ListBag vs =>
                  let 'pair sats fails := Util.partitionWith pred vs in
                  pair (listToBag sats) (listToBag fails)
              end.

Fixpoint foldBag {r} {a} (arg_0__ : (r -> r -> r)) (arg_1__ : (a -> r)) (arg_2__
                   : r) (arg_3__ : Bag a) : r
           := match arg_0__, arg_1__, arg_2__, arg_3__ with
              | _, _, e, EmptyBag => e
              | t, u, e, UnitBag x => t (u x) e
              | t, u, e, TwoBags b1 b2 => foldBag t u (foldBag t u e b2) b1
              | t, u, e, ListBag xs => Data.Foldable.foldr (t GHC.Base.∘ u) e xs
              end.

Fixpoint foldlBag {r} {a} (arg_0__ : (r -> a -> r)) (arg_1__ : r) (arg_2__
                    : Bag a) : r
           := match arg_0__, arg_1__, arg_2__ with
              | _, z, EmptyBag => z
              | k, z, UnitBag x => k z x
              | k, z, TwoBags b1 b2 => foldlBag k (foldlBag k z b1) b2
              | k, z, ListBag xs => Data.Foldable.foldl k z xs
              end.

Fixpoint foldrBagM {m} {a} {b} `{(GHC.Base.Monad m)} (arg_0__ : (a -> b -> m b))
                   (arg_1__ : b) (arg_2__ : Bag a) : m b
           := match arg_0__, arg_1__, arg_2__ with
              | _, z, EmptyBag => GHC.Base.return_ z
              | k, z, UnitBag x => k x z
              | k, z, TwoBags b1 b2 =>
                  foldrBagM k z b2 GHC.Base.>>= (fun z' => foldrBagM k z' b1)
              | k, z, ListBag xs => MonadUtils.foldrM k z xs
              end.

Fixpoint foldlBagM {m} {b} {a} `{(GHC.Base.Monad m)} (arg_0__ : (b -> a -> m b))
                   (arg_1__ : b) (arg_2__ : Bag a) : m b
           := match arg_0__, arg_1__, arg_2__ with
              | _, z, EmptyBag => GHC.Base.return_ z
              | k, z, UnitBag x => k z x
              | k, z, TwoBags b1 b2 =>
                  foldlBagM k z b1 GHC.Base.>>= (fun z' => foldlBagM k z' b2)
              | k, z, ListBag xs => MonadUtils.foldlM k z xs
              end.

Fixpoint concatMapBag {a} {b} (arg_0__ : (a -> Bag b)) (arg_1__ : Bag a) : Bag b
           := match arg_0__, arg_1__ with
              | _, EmptyBag => EmptyBag
              | f, UnitBag x => f x
              | f, TwoBags b1 b2 => unionBags (concatMapBag f b1) (concatMapBag f b2)
              | f, ListBag xs => Data.Foldable.foldr (unionBags GHC.Base.∘ f) emptyBag xs
              end.

Fixpoint mapMaybeBag {a} {b} (arg_0__ : (a -> option b)) (arg_1__ : Bag a) : Bag
                                                                             b
           := match arg_0__, arg_1__ with
              | _, EmptyBag => EmptyBag
              | f, UnitBag x => match f x with | None => EmptyBag | Some y => UnitBag y end
              | f, TwoBags b1 b2 => unionBags (mapMaybeBag f b1) (mapMaybeBag f b2)
              | f, ListBag xs => ListBag (Data.Maybe.mapMaybe f xs)
              end.

Fixpoint mapBagM {m} {a} {b} `{GHC.Base.Monad m} (arg_0__ : (a -> m b)) (arg_1__
                   : Bag a) : m (Bag b)
           := match arg_0__, arg_1__ with
              | _, EmptyBag => GHC.Base.return_ EmptyBag
              | f, UnitBag x => f x GHC.Base.>>= (fun r => GHC.Base.return_ (UnitBag r))
              | f, TwoBags b1 b2 =>
                  mapBagM f b1 GHC.Base.>>=
                  (fun r1 =>
                     mapBagM f b2 GHC.Base.>>= (fun r2 => GHC.Base.return_ (TwoBags r1 r2)))
              | f, ListBag xs =>
                  Data.Traversable.mapM f xs GHC.Base.>>=
                  (fun rs => GHC.Base.return_ (ListBag rs))
              end.

Fixpoint mapBagM_ {m} {a} {b} `{GHC.Base.Monad m} (arg_0__ : (a -> m b))
                  (arg_1__ : Bag a) : m unit
           := match arg_0__, arg_1__ with
              | _, EmptyBag => GHC.Base.return_ tt
              | f, UnitBag x => f x GHC.Base.>> GHC.Base.return_ tt
              | f, TwoBags b1 b2 => mapBagM_ f b1 GHC.Base.>> mapBagM_ f b2
              | f, ListBag xs => Data.Foldable.mapM_ f xs
              end.

Fixpoint flatMapBagM {m} {a} {b} `{GHC.Base.Monad m} (arg_0__
                       : (a -> m (Bag b))) (arg_1__ : Bag a) : m (Bag b)
           := match arg_0__, arg_1__ with
              | _, EmptyBag => GHC.Base.return_ EmptyBag
              | f, UnitBag x => f x
              | f, TwoBags b1 b2 =>
                  flatMapBagM f b1 GHC.Base.>>=
                  (fun r1 =>
                     flatMapBagM f b2 GHC.Base.>>= (fun r2 => GHC.Base.return_ (unionBags r1 r2)))
              | f, ListBag xs =>
                  let k :=
                    fun x b2 => f x GHC.Base.>>= (fun b1 => GHC.Base.return_ (unionBags b1 b2)) in
                  MonadUtils.foldrM k EmptyBag xs
              end.

Fixpoint flatMapBagPairM {m} {a} {b} {c} `{GHC.Base.Monad m} (arg_0__
                           : (a -> m (Bag b * Bag c)%type)) (arg_1__ : Bag a) : m (Bag b * Bag c)%type
           := match arg_0__, arg_1__ with
              | _, EmptyBag => GHC.Base.return_ (pair EmptyBag EmptyBag)
              | f, UnitBag x => f x
              | f, TwoBags b1 b2 =>
                  let cont_4__ arg_5__ :=
                    let 'pair r1 s1 := arg_5__ in
                    let cont_6__ arg_7__ :=
                      let 'pair r2 s2 := arg_7__ in
                      GHC.Base.return_ (pair (unionBags r1 r2) (unionBags s1 s2)) in
                    flatMapBagPairM f b2 GHC.Base.>>= cont_6__ in
                  flatMapBagPairM f b1 GHC.Base.>>= cont_4__
              | f, ListBag xs =>
                  let k :=
                    fun arg_9__ arg_10__ =>
                      match arg_9__, arg_10__ with
                      | x, pair r2 s2 =>
                          let cont_11__ arg_12__ :=
                            let 'pair r1 s1 := arg_12__ in
                            GHC.Base.return_ (pair (unionBags r1 r2) (unionBags s1 s2)) in
                          f x GHC.Base.>>= cont_11__
                      end in
                  MonadUtils.foldrM k (pair EmptyBag EmptyBag) xs
              end.

Fixpoint mapAndUnzipBagM {m} {a} {b} {c} `{GHC.Base.Monad m} (arg_0__
                           : (a -> m (b * c)%type)) (arg_1__ : Bag a) : m (Bag b * Bag c)%type
           := match arg_0__, arg_1__ with
              | _, EmptyBag => GHC.Base.return_ (pair EmptyBag EmptyBag)
              | f, UnitBag x =>
                  let cont_3__ arg_4__ :=
                    let 'pair r s := arg_4__ in
                    GHC.Base.return_ (pair (UnitBag r) (UnitBag s)) in
                  f x GHC.Base.>>= cont_3__
              | f, TwoBags b1 b2 =>
                  let cont_6__ arg_7__ :=
                    let 'pair r1 s1 := arg_7__ in
                    let cont_8__ arg_9__ :=
                      let 'pair r2 s2 := arg_9__ in
                      GHC.Base.return_ (pair (TwoBags r1 r2) (TwoBags s1 s2)) in
                    mapAndUnzipBagM f b2 GHC.Base.>>= cont_8__ in
                  mapAndUnzipBagM f b1 GHC.Base.>>= cont_6__
              | f, ListBag xs =>
                  Data.Traversable.mapM f xs GHC.Base.>>=
                  (fun ts =>
                     let 'pair rs ss := GHC.List.unzip ts in
                     GHC.Base.return_ (pair (ListBag rs) (ListBag ss)))
              end.

Fixpoint mapAccumBagL {acc} {x} {y} (arg_0__ : (acc -> x -> (acc * y)%type))
                      (arg_1__ : acc) (arg_2__ : Bag x) : (acc * Bag y)%type
           := match arg_0__, arg_1__, arg_2__ with
              | _, s, EmptyBag => pair s EmptyBag
              | f, s, UnitBag x => let 'pair s1 x1 := f s x in pair s1 (UnitBag x1)
              | f, s, TwoBags b1 b2 =>
                  let 'pair s1 b1' := mapAccumBagL f s b1 in
                  let 'pair s2 b2' := mapAccumBagL f s1 b2 in
                  pair s2 (TwoBags b1' b2')
              | f, s, ListBag xs =>
                  let 'pair s' xs' := Data.Traversable.mapAccumL f s xs in
                  pair s' (ListBag xs')
              end.

Fixpoint mapAccumBagLM {m} {acc} {x} {y} `{GHC.Base.Monad m} (arg_0__
                         : (acc -> x -> m (acc * y)%type)) (arg_1__ : acc) (arg_2__ : Bag x) : m (acc *
                                                                                                  Bag y)%type
           := match arg_0__, arg_1__, arg_2__ with
              | _, s, EmptyBag => GHC.Base.return_ (pair s EmptyBag)
              | f, s, UnitBag x =>
                  let cont_4__ arg_5__ :=
                    let 'pair s1 x1 := arg_5__ in
                    GHC.Base.return_ (pair s1 (UnitBag x1)) in
                  f s x GHC.Base.>>= cont_4__
              | f, s, TwoBags b1 b2 =>
                  let cont_7__ arg_8__ :=
                    let 'pair s1 b1' := arg_8__ in
                    let cont_9__ arg_10__ :=
                      let 'pair s2 b2' := arg_10__ in
                      GHC.Base.return_ (pair s2 (TwoBags b1' b2')) in
                    mapAccumBagLM f s1 b2 GHC.Base.>>= cont_9__ in
                  mapAccumBagLM f s b1 GHC.Base.>>= cont_7__
              | f, s, ListBag xs =>
                  let cont_12__ arg_13__ :=
                    let 'pair s' xs' := arg_13__ in
                    GHC.Base.return_ (pair s' (ListBag xs')) in
                  MonadUtils.mapAccumLM f s xs GHC.Base.>>= cont_12__
              end.

Definition bagToList {a} : Bag a -> list a :=
  fun b => foldrBag cons nil b.

(* External variables:
     None Some andb bool cons false list nat nil op_zt__ option orb pair true tt unit
     BinInt.Z.to_nat Control.Monad.filterM Coq.Program.Basics.compose
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Foldable.Foldable
     Data.Foldable.all Data.Foldable.any Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl Data.Foldable.foldl'__ Data.Foldable.foldl__
     Data.Foldable.foldr Data.Foldable.foldr'__ Data.Foldable.foldr__
     Data.Foldable.length Data.Foldable.length__ Data.Foldable.mapM_
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.Maybe.mapMaybe Data.OldList.partition
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.mapAccumL Data.Traversable.mapM GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.build' GHC.Base.const GHC.Base.flip
     GHC.Base.fmap__ GHC.Base.id GHC.Base.map GHC.Base.mappend GHC.Base.mempty
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.op_zlzd____ GHC.Base.return_ GHC.List.filter GHC.List.unzip GHC.Num.Int
     GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ MonadUtils.anyM
     MonadUtils.foldlM MonadUtils.foldrM MonadUtils.mapAccumLM Util.isSingleton
     Util.partitionWith
*)
