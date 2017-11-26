(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Import GHC.Base.
Open Scope type_scope.

(* Converted imports: *)

Require Control.Monad.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.OldList.
Require Data.Traversable.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require MonadUtils.

(* Converted declarations: *)

(* Skipping instance
   instance_forall____Outputable_Outputable_a____Outputable_Outputable__Bag_a_ *)

(* Skipping instance
   instance_forall___Data_Data_Data_a___Data_Data_Data__Bag_a_ *)

(* Skipping instance instance_Data_Foldable_Foldable_Bag *)

Inductive Bag a : Type := Mk_EmptyBag : Bag a
                       |  Mk_UnitBag : a -> Bag a
                       |  Mk_TwoBags : (Bag a) -> (Bag a) -> Bag a
                       |  Mk_ListBag : list a -> Bag a.

Arguments Mk_EmptyBag {_}.

Arguments Mk_UnitBag {_} _.

Arguments Mk_TwoBags {_} _ _.

Arguments Mk_ListBag {_} _.

Definition unitBag {a} : a -> Bag a :=
  Mk_UnitBag.

Definition unionBags {a} : Bag a -> Bag a -> Bag a :=
  fun arg_109__ arg_110__ =>
    match arg_109__ , arg_110__ with
      | Mk_EmptyBag , b => b
      | b , Mk_EmptyBag => b
      | b1 , b2 => Mk_TwoBags b1 b2
    end.

Definition unionManyBags {a} : list (Bag a) -> Bag a :=
  fun arg_166__ =>
    match arg_166__ with
      | xs => Data.Foldable.foldr unionBags Mk_EmptyBag xs
    end.

Definition snocBag {a} : Bag a -> a -> Bag a :=
  fun arg_186__ arg_187__ =>
    match arg_186__ , arg_187__ with
      | bag , elt => unionBags bag (unitBag elt)
    end.

Definition mapBagM_ {m} {a} {b} `{GHC.Base.Monad m} : (a -> m b) -> Bag a -> m
                                                      unit :=
  fix mapBagM_ arg_33__ arg_34__
        := match arg_33__ , arg_34__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ tt
             | f , (Mk_UnitBag x) => GHC.Base.op_zgzg__ (f x) (GHC.Base.return_ tt)
             | f , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzg__ (mapBagM_ f b1) (mapBagM_ f b2)
             | f , (Mk_ListBag xs) => Data.Foldable.mapM_ f xs
           end.

Definition mapBagM {m} {a} {b} `{GHC.Base.Monad m} : (a -> m b) -> Bag a -> m
                                                     (Bag b) :=
  fix mapBagM arg_40__ arg_41__
        := match arg_40__ , arg_41__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ Mk_EmptyBag
             | f , (Mk_UnitBag x) => GHC.Base.op_zgzgze__ (f x) (fun r =>
                                                            GHC.Base.return_ (Mk_UnitBag r))
             | f , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (mapBagM f b1) (fun r1 =>
                                                                GHC.Base.op_zgzgze__ (mapBagM f b2) (fun r2 =>
                                                                                       GHC.Base.return_ (Mk_TwoBags r1
                                                                                                        r2)))
             | f , (Mk_ListBag xs) => GHC.Base.op_zgzgze__ (Data.Traversable.mapM f xs)
                                                           (fun rs => GHC.Base.return_ (Mk_ListBag rs))
           end.

Definition mapBag {a} {b} : (a -> b) -> Bag a -> Bag b :=
  fix mapBag arg_47__ arg_48__
        := match arg_47__ , arg_48__ with
             | _ , Mk_EmptyBag => Mk_EmptyBag
             | f , (Mk_UnitBag x) => Mk_UnitBag (f x)
             | f , (Mk_TwoBags b1 b2) => Mk_TwoBags (mapBag f b1) (mapBag f b2)
             | f , (Mk_ListBag xs) => Mk_ListBag (GHC.Base.map f xs)
           end.

Definition mapAndUnzipBagM {m} {a} {b} {c} `{GHC.Base.Monad m} : (a -> m (b *
                                                                         c)) -> Bag a -> m (Bag b * Bag c) :=
  fix mapAndUnzipBagM arg_19__ arg_20__
        := match arg_19__ , arg_20__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ (pair Mk_EmptyBag Mk_EmptyBag)
             | f , (Mk_UnitBag x) => let cont_22__ arg_23__ :=
                                       match arg_23__ with
                                         | (pair r s) => GHC.Base.return_ (pair (Mk_UnitBag r) (Mk_UnitBag s))
                                       end in
                                     GHC.Base.op_zgzgze__ (f x) cont_22__
             | f , (Mk_TwoBags b1 b2) => let cont_25__ arg_26__ :=
                                           match arg_26__ with
                                             | (pair r1 s1) => let cont_27__ arg_28__ :=
                                                                 match arg_28__ with
                                                                   | (pair r2 s2) => GHC.Base.return_ (pair (Mk_TwoBags
                                                                                                            r1 r2)
                                                                                                            (Mk_TwoBags
                                                                                                            s1 s2))
                                                                 end in
                                                               GHC.Base.op_zgzgze__ (mapAndUnzipBagM f b2) cont_27__
                                           end in
                                         GHC.Base.op_zgzgze__ (mapAndUnzipBagM f b1) cont_25__
             | f , (Mk_ListBag xs) => GHC.Base.op_zgzgze__ (Data.Traversable.mapM f xs)
                                                           (fun ts =>
                                                             match GHC.List.unzip ts with
                                                               | (pair rs ss) => GHC.Base.return_ (pair (Mk_ListBag rs)
                                                                                                        (Mk_ListBag ss))
                                                             end)
           end.

Definition mapAccumBagLM {m} {acc} {x} {y} `{GHC.Base.Monad m} : (acc -> x -> m
                                                                 (acc * y)) -> acc -> Bag x -> m (acc * Bag y) :=
  fix mapAccumBagLM arg_3__ arg_4__ arg_5__
        := match arg_3__ , arg_4__ , arg_5__ with
             | _ , s , Mk_EmptyBag => GHC.Base.return_ (pair s Mk_EmptyBag)
             | f , s , (Mk_UnitBag x) => let cont_7__ arg_8__ :=
                                           match arg_8__ with
                                             | (pair s1 x1) => GHC.Base.return_ (pair s1 (Mk_UnitBag x1))
                                           end in
                                         GHC.Base.op_zgzgze__ (f s x) cont_7__
             | f , s , (Mk_TwoBags b1 b2) => let cont_10__ arg_11__ :=
                                               match arg_11__ with
                                                 | (pair s1 b1') => let cont_12__ arg_13__ :=
                                                                      match arg_13__ with
                                                                        | (pair s2 b2') => GHC.Base.return_ (pair s2
                                                                                                                  (Mk_TwoBags
                                                                                                                  b1'
                                                                                                                  b2'))
                                                                      end in
                                                                    GHC.Base.op_zgzgze__ (mapAccumBagLM f s1 b2)
                                                                                         cont_12__
                                               end in
                                             GHC.Base.op_zgzgze__ (mapAccumBagLM f s b1) cont_10__
             | f , s , (Mk_ListBag xs) => let cont_15__ arg_16__ :=
                                            match arg_16__ with
                                              | (pair s' xs') => GHC.Base.return_ (pair s' (Mk_ListBag xs'))
                                            end in
                                          GHC.Base.op_zgzgze__ (MonadUtils.mapAccumLM f s xs) cont_15__
           end.

Definition listToBag {a} : list a -> Bag a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Mk_EmptyBag
      | vs => Mk_ListBag vs
    end.

Definition partitionBag {a} : (a -> bool) -> Bag a -> Bag a * Bag a :=
  fix partitionBag arg_128__ arg_129__
        := match arg_128__ , arg_129__ with
             | _ , Mk_EmptyBag => pair Mk_EmptyBag Mk_EmptyBag
             | pred , ((Mk_UnitBag val) as b) => if pred val : bool
                                                 then pair b Mk_EmptyBag
                                                 else pair Mk_EmptyBag b
             | pred , (Mk_TwoBags b1 b2) => match partitionBag pred b2 with
                                              | (pair sat2 fail2) => match partitionBag pred b1 with
                                                                       | (pair sat1 fail1) => pair (unionBags sat1 sat2)
                                                                                                   (unionBags fail1
                                                                                                              fail2)
                                                                     end
                                            end
             | pred , (Mk_ListBag vs) => match Data.OldList.partition pred vs with
                                           | (pair sats fails) => pair (listToBag sats) (listToBag fails)
                                         end
           end.

Definition lengthBag {a} : Bag a -> GHC.Num.Int :=
  fix lengthBag arg_176__
        := match arg_176__ with
             | Mk_EmptyBag => GHC.Num.fromInteger 0
             | (Mk_UnitBag _) => GHC.Num.fromInteger 1
             | (Mk_TwoBags b1 b2) => GHC.Num.op_zp__ (lengthBag b1) (lengthBag b2)
             | (Mk_ListBag xs) => Data.Foldable.length xs
           end.

Definition isEmptyBag {a} : Bag a -> bool :=
  fun arg_107__ => match arg_107__ with | Mk_EmptyBag => true | _ => false end.

Definition foldrBagM {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> b -> m
                                                         b) -> b -> Bag a -> m b :=
  fix foldrBagM arg_61__ arg_62__ arg_63__
        := match arg_61__ , arg_62__ , arg_63__ with
             | _ , z , Mk_EmptyBag => GHC.Base.return_ z
             | k , z , (Mk_UnitBag x) => k x z
             | k , z , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (foldrBagM k z b2)
                                                                  (fun z' => foldrBagM k z' b1)
             | k , z , (Mk_ListBag xs) => MonadUtils.foldrM k z xs
           end.

Definition foldrBag {a} {r} : (a -> r -> r) -> r -> Bag a -> r :=
  fix foldrBag arg_76__ arg_77__ arg_78__
        := match arg_76__ , arg_77__ , arg_78__ with
             | _ , z , Mk_EmptyBag => z
             | k , z , (Mk_UnitBag x) => k x z
             | k , z , (Mk_TwoBags b1 b2) => foldrBag k (foldrBag k z b2) b1
             | k , z , (Mk_ListBag xs) => Data.Foldable.foldr k z xs
           end.

Definition foldlBagM {m} {b} {a} `{(GHC.Base.Monad m)} : (b -> a -> m
                                                         b) -> b -> Bag a -> m b :=
  fix foldlBagM arg_53__ arg_54__ arg_55__
        := match arg_53__ , arg_54__ , arg_55__ with
             | _ , z , Mk_EmptyBag => GHC.Base.return_ z
             | k , z , (Mk_UnitBag x) => k z x
             | k , z , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (foldlBagM k z b1)
                                                                  (fun z' => foldlBagM k z' b2)
             | k , z , (Mk_ListBag xs) => MonadUtils.foldlM k z xs
           end.

Definition foldlBag {r} {a} : (r -> a -> r) -> r -> Bag a -> r :=
  fix foldlBag arg_69__ arg_70__ arg_71__
        := match arg_69__ , arg_70__ , arg_71__ with
             | _ , z , Mk_EmptyBag => z
             | k , z , (Mk_UnitBag x) => k z x
             | k , z , (Mk_TwoBags b1 b2) => foldlBag k (foldlBag k z b1) b2
             | k , z , (Mk_ListBag xs) => Data.Foldable.foldl k z xs
           end.

Definition foldBag {r} {a} : (r -> r -> r) -> (a -> r) -> r -> Bag a -> r :=
  fix foldBag arg_86__ arg_87__ arg_88__ arg_89__
        := match arg_86__ , arg_87__ , arg_88__ , arg_89__ with
             | _ , _ , e , Mk_EmptyBag => e
             | t , u , e , (Mk_UnitBag x) => t (u x) e
             | t , u , e , (Mk_TwoBags b1 b2) => foldBag t u (foldBag t u e b2) b1
             | t , u , e , (Mk_ListBag xs) => Data.Foldable.foldr (Coq.Program.Basics.compose
                                                                  t u) e xs
           end.

Definition flatMapBagPairM {m} {a} {b} {c} `{GHC.Base.Monad m} : (a -> m (Bag b
                                                                         * Bag c)) -> Bag a -> m (Bag b * Bag c) :=
  fix flatMapBagPairM arg_149__ arg_150__
        := match arg_149__ , arg_150__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ (pair Mk_EmptyBag Mk_EmptyBag)
             | f , (Mk_UnitBag x) => f x
             | f , (Mk_TwoBags b1 b2) => let cont_153__ arg_154__ :=
                                           match arg_154__ with
                                             | (pair r1 s1) => let cont_155__ arg_156__ :=
                                                                 match arg_156__ with
                                                                   | (pair r2 s2) => GHC.Base.return_ (pair (unionBags
                                                                                                            r1 r2)
                                                                                                            (unionBags
                                                                                                            s1 s2))
                                                                 end in
                                                               GHC.Base.op_zgzgze__ (flatMapBagPairM f b2) cont_155__
                                           end in
                                         GHC.Base.op_zgzgze__ (flatMapBagPairM f b1) cont_153__
             | f , (Mk_ListBag xs) => let k :=
                                        fun arg_158__ arg_159__ =>
                                          match arg_158__ , arg_159__ with
                                            | x , (pair r2 s2) => let cont_160__ arg_161__ :=
                                                                    match arg_161__ with
                                                                      | (pair r1 s1) => GHC.Base.return_ (pair
                                                                                                         (unionBags r1
                                                                                                                    r2)
                                                                                                         (unionBags s1
                                                                                                                    s2))
                                                                    end in
                                                                  GHC.Base.op_zgzgze__ (f x) cont_160__
                                          end in
                                      MonadUtils.foldrM k (pair Mk_EmptyBag Mk_EmptyBag) xs
           end.

Definition flatMapBagM {m} {a} {b} `{GHC.Base.Monad m} : (a -> m (Bag b)) -> Bag
                                                         a -> m (Bag b) :=
  fix flatMapBagM arg_138__ arg_139__
        := match arg_138__ , arg_139__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ Mk_EmptyBag
             | f , (Mk_UnitBag x) => f x
             | f , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (flatMapBagM f b1) (fun r1 =>
                                                                GHC.Base.op_zgzgze__ (flatMapBagM f b2) (fun r2 =>
                                                                                       GHC.Base.return_ (unionBags r1
                                                                                                                   r2)))
             | f , (Mk_ListBag xs) => let k :=
                                        fun arg_143__ arg_144__ =>
                                          match arg_143__ , arg_144__ with
                                            | x , b2 => GHC.Base.op_zgzgze__ (f x) (fun b1 =>
                                                                               GHC.Base.return_ (unionBags b1 b2))
                                          end in
                                      MonadUtils.foldrM k Mk_EmptyBag xs
           end.

Definition filterBagM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> Bag a -> m
                                                    (Bag a) :=
  fix filterBagM arg_121__ arg_122__
        := match arg_121__ , arg_122__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ Mk_EmptyBag
             | pred , ((Mk_UnitBag val) as b) => GHC.Base.op_zgzgze__ (pred val) (fun flag =>
                                                                        if flag : bool
                                                                        then GHC.Base.return_ b
                                                                        else GHC.Base.return_ Mk_EmptyBag)
             | pred , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (filterBagM pred b1)
                                                                 (fun sat1 =>
                                                                   GHC.Base.op_zgzgze__ (filterBagM pred b2)
                                                                                        (fun sat2 =>
                                                                                          GHC.Base.return_ (unionBags
                                                                                                           sat1 sat2)))
             | pred , (Mk_ListBag vs) => GHC.Base.op_zgzgze__ (Control.Monad.filterM pred vs)
                                                              (fun sat => GHC.Base.return_ (listToBag sat))
           end.

Definition filterBag {a} : (a -> bool) -> Bag a -> Bag a :=
  fix filterBag arg_113__ arg_114__
        := match arg_113__ , arg_114__ with
             | _ , Mk_EmptyBag => Mk_EmptyBag
             | pred , ((Mk_UnitBag val) as b) => if pred val : bool
                                                 then b
                                                 else Mk_EmptyBag
             | pred , (Mk_TwoBags b1 b2) => let sat2 := filterBag pred b2 in
                                            let sat1 := filterBag pred b1 in unionBags sat1 sat2
             | pred , (Mk_ListBag vs) => listToBag (GHC.List.filter pred vs)
           end.

Definition emptyBag {a} : Bag a :=
  Mk_EmptyBag.

Definition elemBag {a} `{GHC.Base.Eq_ a} : a -> Bag a -> bool :=
  fix elemBag arg_169__ arg_170__
        := match arg_169__ , arg_170__ with
             | _ , Mk_EmptyBag => false
             | x , (Mk_UnitBag y) => GHC.Base.op_zeze__ x y
             | x , (Mk_TwoBags b1 b2) => orb (elemBag x b1) (elemBag x b2)
             | x , (Mk_ListBag ys) => Data.Foldable.any (fun arg_173__ =>
                                                          GHC.Base.op_zeze__ x arg_173__) ys
           end.

Definition consBag {a} : a -> Bag a -> Bag a :=
  fun arg_182__ arg_183__ =>
    match arg_182__ , arg_183__ with
      | elt , bag => unionBags (unitBag elt) bag
    end.

Definition concatBag {a} : Bag (Bag a) -> Bag a :=
  fun arg_190__ =>
    match arg_190__ with
      | bss => let add :=
                 fun arg_191__ arg_192__ =>
                   match arg_191__ , arg_192__ with
                     | bs , rs => unionBags bs rs
                   end in
               foldrBag add emptyBag bss
    end.

Definition catBagMaybes {a} : Bag (option a) -> Bag a :=
  fun arg_197__ =>
    match arg_197__ with
      | bs => let add :=
                fun arg_198__ arg_199__ =>
                  match arg_198__ , arg_199__ with
                    | None , rs => rs
                    | (Some x) , rs => consBag x rs
                  end in
              foldrBag add emptyBag bs
    end.

Definition bagToList {a} : Bag a -> list a :=
  fun arg_83__ => match arg_83__ with | b => foldrBag cons nil b end.

Definition anyBagM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> Bag a -> m
                                                 bool :=
  fix anyBagM arg_94__ arg_95__
        := match arg_94__ , arg_95__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ false
             | p , (Mk_UnitBag v) => p v
             | p , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (anyBagM p b1) (fun flag =>
                                                                if flag : bool
                                                                then GHC.Base.return_ true
                                                                else anyBagM p b2)
             | p , (Mk_ListBag xs) => MonadUtils.anyM p xs
           end.

Definition anyBag {a} : (a -> bool) -> Bag a -> bool :=
  fix anyBag arg_101__ arg_102__
        := match arg_101__ , arg_102__ with
             | _ , Mk_EmptyBag => false
             | p , (Mk_UnitBag v) => p v
             | p , (Mk_TwoBags b1 b2) => orb (anyBag p b1) (anyBag p b2)
             | p , (Mk_ListBag xs) => Data.Foldable.any p xs
           end.

(* Unbound variables:
     * Control.Monad.filterM Coq.Program.Basics.compose Data.Foldable.any
     Data.Foldable.foldl Data.Foldable.foldr Data.Foldable.length Data.Foldable.mapM_
     Data.OldList.partition Data.Traversable.mapM GHC.Base.Eq_ GHC.Base.Monad
     GHC.Base.map GHC.Base.op_zeze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.return_ GHC.List.filter GHC.List.unzip GHC.Num.Int GHC.Num.op_zp__
     MonadUtils.anyM MonadUtils.foldlM MonadUtils.foldrM MonadUtils.mapAccumLM Some
     bool cons false list nil option orb pair true tt unit
*)
