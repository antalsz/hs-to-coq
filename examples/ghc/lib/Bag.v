(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.
Require Data.Either.
Require Data.Foldable.
Require Data.OldList.
Require Data.Traversable.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require MonadUtils.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Bag a : Type := EmptyBag : Bag a
                       |  UnitBag : a -> Bag a
                       |  TwoBags : (Bag a) -> (Bag a) -> Bag a
                       |  ListBag : list a -> Bag a.

Arguments EmptyBag {_}.

Arguments UnitBag {_} _.

Arguments TwoBags {_} _ _.

Arguments ListBag {_} _.
(* Converted value declarations: *)

(* Skipping instance Outputable__Bag *)

(* Skipping instance Data__Bag *)

(* Skipping instance Foldable__Bag *)

Definition anyBag {a} : (a -> bool) -> Bag a -> bool :=
  fix anyBag arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => false
             | p , UnitBag v => p v
             | p , TwoBags b1 b2 => orb (anyBag p b1) (anyBag p b2)
             | p , ListBag xs => Data.Foldable.any p xs
           end.

Definition anyBagM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> Bag a -> m
                                                 bool :=
  fix anyBagM arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => GHC.Base.return_ false
             | p , UnitBag v => p v
             | p , TwoBags b1 b2 => anyBagM p b1 GHC.Base.>>= (fun flag =>
                                      if flag : bool
                                      then GHC.Base.return_ true
                                      else anyBagM p b2)
             | p , ListBag xs => MonadUtils.anyM p xs
           end.

Definition elemBag {a} `{GHC.Base.Eq_ a} : a -> Bag a -> bool :=
  fix elemBag arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => false
             | x , UnitBag y => x GHC.Base.== y
             | x , TwoBags b1 b2 => orb (elemBag x b1) (elemBag x b2)
             | x , ListBag ys => Data.Foldable.any (fun arg_4__ => x GHC.Base.== arg_4__) ys
           end.

Definition emptyBag {a} : Bag a :=
  EmptyBag.

Definition foldBag {r} {a} : (r -> r -> r) -> (a -> r) -> r -> Bag a -> r :=
  fix foldBag arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | _ , _ , e , EmptyBag => e
             | t , u , e , UnitBag x => t (u x) e
             | t , u , e , TwoBags b1 b2 => foldBag t u (foldBag t u e b2) b1
             | t , u , e , ListBag xs => Data.Foldable.foldr (t GHC.Base.∘ u) e xs
           end.

Definition foldlBag {r} {a} : (r -> a -> r) -> r -> Bag a -> r :=
  fix foldlBag arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | _ , z , EmptyBag => z
             | k , z , UnitBag x => k z x
             | k , z , TwoBags b1 b2 => foldlBag k (foldlBag k z b1) b2
             | k , z , ListBag xs => Data.Foldable.foldl k z xs
           end.

Definition foldlBagM {m} {b} {a} `{(GHC.Base.Monad m)} : (b -> a -> m
                                                         b) -> b -> Bag a -> m b :=
  fix foldlBagM arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | _ , z , EmptyBag => GHC.Base.return_ z
             | k , z , UnitBag x => k z x
             | k , z , TwoBags b1 b2 => foldlBagM k z b1 GHC.Base.>>= (fun z' =>
                                          foldlBagM k z' b2)
             | k , z , ListBag xs => MonadUtils.foldlM k z xs
           end.

Definition foldrBag {a} {r} : (a -> r -> r) -> r -> Bag a -> r :=
  fix foldrBag arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | _ , z , EmptyBag => z
             | k , z , UnitBag x => k x z
             | k , z , TwoBags b1 b2 => foldrBag k (foldrBag k z b2) b1
             | k , z , ListBag xs => Data.Foldable.foldr k z xs
           end.

Definition bagToList {a} : Bag a -> list a :=
  fun b => foldrBag cons nil b.

Definition foldrBagM {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> b -> m
                                                         b) -> b -> Bag a -> m b :=
  fix foldrBagM arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | _ , z , EmptyBag => GHC.Base.return_ z
             | k , z , UnitBag x => k x z
             | k , z , TwoBags b1 b2 => foldrBagM k z b2 GHC.Base.>>= (fun z' =>
                                          foldrBagM k z' b1)
             | k , z , ListBag xs => MonadUtils.foldrM k z xs
           end.

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

Definition lengthBag {a} : Bag a -> GHC.Num.Int :=
  fix lengthBag arg_0__
        := match arg_0__ with
             | EmptyBag => GHC.Num.fromInteger 0
             | UnitBag _ => GHC.Num.fromInteger 1
             | TwoBags b1 b2 => lengthBag b1 GHC.Num.+ lengthBag b2
             | ListBag xs => Data.Foldable.length xs
           end.

Definition listToBag {a} : list a -> Bag a :=
  fun arg_0__ => match arg_0__ with | nil => EmptyBag | vs => ListBag vs end.

Definition mapAccumBagLM {m} {acc} {x} {y} `{GHC.Base.Monad m} : (acc -> x -> m
                                                                 (acc * y)%type) -> acc -> Bag x -> m (acc * Bag
                                                                                                      y)%type :=
  fix mapAccumBagLM arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | _ , s , EmptyBag => GHC.Base.return_ (pair s EmptyBag)
             | f , s , UnitBag x => let cont_4__ arg_5__ :=
                                      match arg_5__ with
                                        | pair s1 x1 => GHC.Base.return_ (pair s1 (UnitBag x1))
                                      end in
                                    f s x GHC.Base.>>= cont_4__
             | f , s , TwoBags b1 b2 => let cont_7__ arg_8__ :=
                                          match arg_8__ with
                                            | pair s1 b1' => let cont_9__ arg_10__ :=
                                                               match arg_10__ with
                                                                 | pair s2 b2' => GHC.Base.return_ (pair s2 (TwoBags b1'
                                                                                                         b2'))
                                                               end in
                                                             mapAccumBagLM f s1 b2 GHC.Base.>>= cont_9__
                                          end in
                                        mapAccumBagLM f s b1 GHC.Base.>>= cont_7__
             | f , s , ListBag xs => let cont_12__ arg_13__ :=
                                       match arg_13__ with
                                         | pair s' xs' => GHC.Base.return_ (pair s' (ListBag xs'))
                                       end in
                                     MonadUtils.mapAccumLM f s xs GHC.Base.>>= cont_12__
           end.

Definition mapAndUnzipBagM {m} {a} {b} {c} `{GHC.Base.Monad m} : (a -> m (b *
                                                                         c)%type) -> Bag a -> m (Bag b * Bag c)%type :=
  fix mapAndUnzipBagM arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => GHC.Base.return_ (pair EmptyBag EmptyBag)
             | f , UnitBag x => let cont_3__ arg_4__ :=
                                  match arg_4__ with
                                    | pair r s => GHC.Base.return_ (pair (UnitBag r) (UnitBag s))
                                  end in
                                f x GHC.Base.>>= cont_3__
             | f , TwoBags b1 b2 => let cont_6__ arg_7__ :=
                                      match arg_7__ with
                                        | pair r1 s1 => let cont_8__ arg_9__ :=
                                                          match arg_9__ with
                                                            | pair r2 s2 => GHC.Base.return_ (pair (TwoBags r1 r2)
                                                                                                   (TwoBags s1 s2))
                                                          end in
                                                        mapAndUnzipBagM f b2 GHC.Base.>>= cont_8__
                                      end in
                                    mapAndUnzipBagM f b1 GHC.Base.>>= cont_6__
             | f , ListBag xs => Data.Traversable.mapM f xs GHC.Base.>>= (fun ts =>
                                   match GHC.List.unzip ts with
                                     | pair rs ss => GHC.Base.return_ (pair (ListBag rs) (ListBag ss))
                                   end)
           end.

Definition mapBag {a} {b} : (a -> b) -> Bag a -> Bag b :=
  fix mapBag arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => EmptyBag
             | f , UnitBag x => UnitBag (f x)
             | f , TwoBags b1 b2 => TwoBags (mapBag f b1) (mapBag f b2)
             | f , ListBag xs => ListBag (GHC.Base.map f xs)
           end.

Definition mapBagM {m} {a} {b} `{GHC.Base.Monad m} : (a -> m b) -> Bag a -> m
                                                     (Bag b) :=
  fix mapBagM arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => GHC.Base.return_ EmptyBag
             | f , UnitBag x => f x GHC.Base.>>= (fun r => GHC.Base.return_ (UnitBag r))
             | f , TwoBags b1 b2 => mapBagM f b1 GHC.Base.>>= (fun r1 =>
                                      mapBagM f b2 GHC.Base.>>= (fun r2 => GHC.Base.return_ (TwoBags r1 r2)))
             | f , ListBag xs => Data.Traversable.mapM f xs GHC.Base.>>= (fun rs =>
                                   GHC.Base.return_ (ListBag rs))
           end.

Definition mapBagM_ {m} {a} {b} `{GHC.Base.Monad m} : (a -> m b) -> Bag a -> m
                                                      unit :=
  fix mapBagM_ arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => GHC.Base.return_ tt
             | f , UnitBag x => f x GHC.Base.>> GHC.Base.return_ tt
             | f , TwoBags b1 b2 => mapBagM_ f b1 GHC.Base.>> mapBagM_ f b2
             | f , ListBag xs => Data.Foldable.mapM_ f xs
           end.

Definition unionBags {a} : Bag a -> Bag a -> Bag a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | EmptyBag , b => b
      | b , EmptyBag => b
      | b1 , b2 => TwoBags b1 b2
    end.

Definition unionManyBags {a} : list (Bag a) -> Bag a :=
  fun xs => Data.Foldable.foldr unionBags EmptyBag xs.

Definition partitionBag {a} : (a -> bool) -> Bag a -> (Bag a * Bag a)%type :=
  fix partitionBag arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => pair EmptyBag EmptyBag
             | pred , (UnitBag val as b) => if pred val : bool
                                            then pair b EmptyBag
                                            else pair EmptyBag b
             | pred , TwoBags b1 b2 => match partitionBag pred b2 with
                                         | pair sat2 fail2 => match partitionBag pred b1 with
                                                                | pair sat1 fail1 => pair (unionBags sat1 sat2)
                                                                                          (unionBags fail1 fail2)
                                                              end
                                       end
             | pred , ListBag vs => match Data.OldList.partition pred vs with
                                      | pair sats fails => pair (listToBag sats) (listToBag fails)
                                    end
           end.

Definition partitionBagWith {a} {b} {c} : (a -> Data.Either.Either b c) -> Bag
                                          a -> (Bag b * Bag c)%type :=
  fix partitionBagWith arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => pair EmptyBag EmptyBag
             | pred , UnitBag val => let scrut_3__ := pred val in
                                     match scrut_3__ with
                                       | Data.Either.Left a => pair (UnitBag a) EmptyBag
                                       | Data.Either.Right b => pair EmptyBag (UnitBag b)
                                     end
             | pred , TwoBags b1 b2 => match partitionBagWith pred b2 with
                                         | pair sat2 fail2 => match partitionBagWith pred b1 with
                                                                | pair sat1 fail1 => pair (unionBags sat1 sat2)
                                                                                          (unionBags fail1 fail2)
                                                              end
                                       end
             | pred , ListBag vs => match Util.partitionWith pred vs with
                                      | pair sats fails => pair (listToBag sats) (listToBag fails)
                                    end
           end.

Definition flatMapBagPairM {m} {a} {b} {c} `{GHC.Base.Monad m} : (a -> m (Bag b
                                                                         * Bag c)%type) -> Bag a -> m (Bag b * Bag
                                                                                                      c)%type :=
  fix flatMapBagPairM arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => GHC.Base.return_ (pair EmptyBag EmptyBag)
             | f , UnitBag x => f x
             | f , TwoBags b1 b2 => let cont_4__ arg_5__ :=
                                      match arg_5__ with
                                        | pair r1 s1 => let cont_6__ arg_7__ :=
                                                          match arg_7__ with
                                                            | pair r2 s2 => GHC.Base.return_ (pair (unionBags r1 r2)
                                                                                                   (unionBags s1 s2))
                                                          end in
                                                        flatMapBagPairM f b2 GHC.Base.>>= cont_6__
                                      end in
                                    flatMapBagPairM f b1 GHC.Base.>>= cont_4__
             | f , ListBag xs => let k :=
                                   fun arg_9__ arg_10__ =>
                                     match arg_9__ , arg_10__ with
                                       | x , pair r2 s2 => let cont_11__ arg_12__ :=
                                                             match arg_12__ with
                                                               | pair r1 s1 => GHC.Base.return_ (pair (unionBags r1 r2)
                                                                                                      (unionBags s1 s2))
                                                             end in
                                                           f x GHC.Base.>>= cont_11__
                                     end in
                                 MonadUtils.foldrM k (pair EmptyBag EmptyBag) xs
           end.

Definition flatMapBagM {m} {a} {b} `{GHC.Base.Monad m} : (a -> m (Bag b)) -> Bag
                                                         a -> m (Bag b) :=
  fix flatMapBagM arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => GHC.Base.return_ EmptyBag
             | f , UnitBag x => f x
             | f , TwoBags b1 b2 => flatMapBagM f b1 GHC.Base.>>= (fun r1 =>
                                      flatMapBagM f b2 GHC.Base.>>= (fun r2 => GHC.Base.return_ (unionBags r1 r2)))
             | f , ListBag xs => let k :=
                                   fun x b2 => f x GHC.Base.>>= (fun b1 => GHC.Base.return_ (unionBags b1 b2)) in
                                 MonadUtils.foldrM k EmptyBag xs
           end.

Definition filterBagM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> Bag a -> m
                                                    (Bag a) :=
  fix filterBagM arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => GHC.Base.return_ EmptyBag
             | pred , (UnitBag val as b) => pred val GHC.Base.>>= (fun flag =>
                                              if flag : bool
                                              then GHC.Base.return_ b
                                              else GHC.Base.return_ EmptyBag)
             | pred , TwoBags b1 b2 => filterBagM pred b1 GHC.Base.>>= (fun sat1 =>
                                         filterBagM pred b2 GHC.Base.>>= (fun sat2 =>
                                           GHC.Base.return_ (unionBags sat1 sat2)))
             | pred , ListBag vs => Control.Monad.filterM pred vs GHC.Base.>>= (fun sat =>
                                      GHC.Base.return_ (listToBag sat))
           end.

Definition filterBag {a} : (a -> bool) -> Bag a -> Bag a :=
  fix filterBag arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , EmptyBag => EmptyBag
             | pred , (UnitBag val as b) => if pred val : bool
                                            then b
                                            else EmptyBag
             | pred , TwoBags b1 b2 => let sat2 := filterBag pred b2 in
                                       let sat1 := filterBag pred b1 in unionBags sat1 sat2
             | pred , ListBag vs => listToBag (GHC.List.filter pred vs)
           end.

Definition concatBag {a} : Bag (Bag a) -> Bag a :=
  fun bss => let add := fun bs rs => unionBags bs rs in foldrBag add emptyBag bss.

Definition unitBag {a} : a -> Bag a :=
  UnitBag.

Definition snocBag {a} : Bag a -> a -> Bag a :=
  fun bag elt => unionBags bag (unitBag elt).

Definition consBag {a} : a -> Bag a -> Bag a :=
  fun elt bag => unionBags (unitBag elt) bag.

Definition catBagMaybes {a} : Bag (option a) -> Bag a :=
  fun bs =>
    let add :=
      fun arg_0__ arg_1__ =>
        match arg_0__ , arg_1__ with
          | None , rs => rs
          | Some x , rs => consBag x rs
        end in
    foldrBag add emptyBag bs.

(* Unbound variables:
     Some bool cons false list nil op_zt__ option orb pair true tt unit
     Control.Monad.filterM Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Foldable.any Data.Foldable.foldl Data.Foldable.foldr Data.Foldable.length
     Data.Foldable.mapM_ Data.OldList.partition Data.Traversable.mapM GHC.Base.Eq_
     GHC.Base.Monad GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.List.filter
     GHC.List.unzip GHC.Num.Int GHC.Num.op_zp__ MonadUtils.anyM MonadUtils.foldlM
     MonadUtils.foldrM MonadUtils.mapAccumLM Util.isSingleton Util.partitionWith
*)
