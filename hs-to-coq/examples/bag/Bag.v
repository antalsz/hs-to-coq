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
  fun arg_93__ arg_94__ =>
    match arg_93__ , arg_94__ with
      | Mk_EmptyBag , b => b
      | b , Mk_EmptyBag => b
      | b1 , b2 => Mk_TwoBags b1 b2
    end.

Definition unionManyBags {a} : list (Bag a) -> Bag a :=
  fun arg_150__ =>
    match arg_150__ with
      | xs => Data.Foldable.foldr unionBags Mk_EmptyBag xs
    end.

Definition snocBag {a} : Bag a -> a -> Bag a :=
  fun arg_170__ arg_171__ =>
    match arg_170__ , arg_171__ with
      | bag , elt => unionBags bag (unitBag elt)
    end.

Definition mapBagM_ {m} {a} {b} `{GHC.Base.Monad m} : (a -> m b) -> Bag a -> m
                                                      unit :=
  fix mapBagM_ arg_17__ arg_18__
        := match arg_17__ , arg_18__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ tt
             | f , (Mk_UnitBag x) => GHC.Base.op_zgzg__ (f x) (GHC.Base.return_ tt)
             | f , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzg__ (mapBagM_ f b1) (mapBagM_ f b2)
             | f , (Mk_ListBag xs) => Data.Foldable.mapM_ f xs
           end.

Definition mapBagM {m} {a} {b} `{GHC.Base.Monad m} : (a -> m b) -> Bag a -> m
                                                     (Bag b) :=
  fix mapBagM arg_24__ arg_25__
        := match arg_24__ , arg_25__ with
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
  fix mapBag arg_31__ arg_32__
        := match arg_31__ , arg_32__ with
             | _ , Mk_EmptyBag => Mk_EmptyBag
             | f , (Mk_UnitBag x) => Mk_UnitBag (f x)
             | f , (Mk_TwoBags b1 b2) => Mk_TwoBags (mapBag f b1) (mapBag f b2)
             | f , (Mk_ListBag xs) => Mk_ListBag (GHC.Base.map f xs)
           end.

Definition mapAndUnzipBagM {m} {a} {b} {c} `{GHC.Base.Monad m} : (a -> m (b *
                                                                         c)) -> Bag a -> m (Bag b * Bag c) :=
  fix mapAndUnzipBagM arg_3__ arg_4__
        := match arg_3__ , arg_4__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ (pair Mk_EmptyBag Mk_EmptyBag)
             | f , (Mk_UnitBag x) => let cont_6__ arg_7__ :=
                                       match arg_7__ with
                                         | (pair r s) => GHC.Base.return_ (pair (Mk_UnitBag r) (Mk_UnitBag s))
                                       end in
                                     GHC.Base.op_zgzgze__ (f x) cont_6__
             | f , (Mk_TwoBags b1 b2) => let cont_9__ arg_10__ :=
                                           match arg_10__ with
                                             | (pair r1 s1) => let cont_11__ arg_12__ :=
                                                                 match arg_12__ with
                                                                   | (pair r2 s2) => GHC.Base.return_ (pair (Mk_TwoBags
                                                                                                            r1 r2)
                                                                                                            (Mk_TwoBags
                                                                                                            s1 s2))
                                                                 end in
                                                               GHC.Base.op_zgzgze__ (mapAndUnzipBagM f b2) cont_11__
                                           end in
                                         GHC.Base.op_zgzgze__ (mapAndUnzipBagM f b1) cont_9__
             | f , (Mk_ListBag xs) => GHC.Base.op_zgzgze__ (Data.Traversable.mapM f xs)
                                                           (fun ts =>
                                                             match GHC.List.unzip ts with
                                                               | (pair rs ss) => GHC.Base.return_ (pair (Mk_ListBag rs)
                                                                                                        (Mk_ListBag ss))
                                                             end)
           end.

Definition listToBag {a} : list a -> Bag a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Mk_EmptyBag
      | vs => Mk_ListBag vs
    end.

Definition partitionBag {a} : (a -> bool) -> Bag a -> Bag a * Bag a :=
  fix partitionBag arg_112__ arg_113__
        := match arg_112__ , arg_113__ with
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
  fix lengthBag arg_160__
        := match arg_160__ with
             | Mk_EmptyBag => GHC.Num.fromInteger 0
             | (Mk_UnitBag _) => GHC.Num.fromInteger 1
             | (Mk_TwoBags b1 b2) => GHC.Num.op_zp__ (lengthBag b1) (lengthBag b2)
             | (Mk_ListBag xs) => Data.Foldable.length xs
           end.

Definition isEmptyBag {a} : Bag a -> bool :=
  fun arg_91__ => match arg_91__ with | Mk_EmptyBag => true | _ => false end.

Definition foldrBagM {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> b -> m
                                                         b) -> b -> Bag a -> m b :=
  fix foldrBagM arg_45__ arg_46__ arg_47__
        := match arg_45__ , arg_46__ , arg_47__ with
             | _ , z , Mk_EmptyBag => GHC.Base.return_ z
             | k , z , (Mk_UnitBag x) => k x z
             | k , z , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (foldrBagM k z b2)
                                                                  (fun z' => foldrBagM k z' b1)
             | k , z , (Mk_ListBag xs) => MonadUtils.foldrM k z xs
           end.

Definition foldrBag {a} {r} : (a -> r -> r) -> r -> Bag a -> r :=
  fix foldrBag arg_60__ arg_61__ arg_62__
        := match arg_60__ , arg_61__ , arg_62__ with
             | _ , z , Mk_EmptyBag => z
             | k , z , (Mk_UnitBag x) => k x z
             | k , z , (Mk_TwoBags b1 b2) => foldrBag k (foldrBag k z b2) b1
             | k , z , (Mk_ListBag xs) => Data.Foldable.foldr k z xs
           end.

Definition foldlBagM {m} {b} {a} `{(GHC.Base.Monad m)} : (b -> a -> m
                                                         b) -> b -> Bag a -> m b :=
  fix foldlBagM arg_37__ arg_38__ arg_39__
        := match arg_37__ , arg_38__ , arg_39__ with
             | _ , z , Mk_EmptyBag => GHC.Base.return_ z
             | k , z , (Mk_UnitBag x) => k z x
             | k , z , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (foldlBagM k z b1)
                                                                  (fun z' => foldlBagM k z' b2)
             | k , z , (Mk_ListBag xs) => MonadUtils.foldlM k z xs
           end.

Definition foldlBag {r} {a} : (r -> a -> r) -> r -> Bag a -> r :=
  fix foldlBag arg_53__ arg_54__ arg_55__
        := match arg_53__ , arg_54__ , arg_55__ with
             | _ , z , Mk_EmptyBag => z
             | k , z , (Mk_UnitBag x) => k z x
             | k , z , (Mk_TwoBags b1 b2) => foldlBag k (foldlBag k z b1) b2
             | k , z , (Mk_ListBag xs) => Data.Foldable.foldl k z xs
           end.

Definition foldBag {r} {a} : (r -> r -> r) -> (a -> r) -> r -> Bag a -> r :=
  fix foldBag arg_70__ arg_71__ arg_72__ arg_73__
        := match arg_70__ , arg_71__ , arg_72__ , arg_73__ with
             | _ , _ , e , Mk_EmptyBag => e
             | t , u , e , (Mk_UnitBag x) => t (u x) e
             | t , u , e , (Mk_TwoBags b1 b2) => foldBag t u (foldBag t u e b2) b1
             | t , u , e , (Mk_ListBag xs) => Data.Foldable.foldr (Coq.Program.Basics.compose
                                                                  t u) e xs
           end.

Definition flatMapBagPairM {m} {a} {b} {c} `{GHC.Base.Monad m} : (a -> m (Bag b
                                                                         * Bag c)) -> Bag a -> m (Bag b * Bag c) :=
  fix flatMapBagPairM arg_133__ arg_134__
        := match arg_133__ , arg_134__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ (pair Mk_EmptyBag Mk_EmptyBag)
             | f , (Mk_UnitBag x) => f x
             | f , (Mk_TwoBags b1 b2) => let cont_137__ arg_138__ :=
                                           match arg_138__ with
                                             | (pair r1 s1) => let cont_139__ arg_140__ :=
                                                                 match arg_140__ with
                                                                   | (pair r2 s2) => GHC.Base.return_ (pair (unionBags
                                                                                                            r1 r2)
                                                                                                            (unionBags
                                                                                                            s1 s2))
                                                                 end in
                                                               GHC.Base.op_zgzgze__ (flatMapBagPairM f b2) cont_139__
                                           end in
                                         GHC.Base.op_zgzgze__ (flatMapBagPairM f b1) cont_137__
             | f , (Mk_ListBag xs) => let k :=
                                        fun arg_142__ arg_143__ =>
                                          match arg_142__ , arg_143__ with
                                            | x , (pair r2 s2) => let cont_144__ arg_145__ :=
                                                                    match arg_145__ with
                                                                      | (pair r1 s1) => GHC.Base.return_ (pair
                                                                                                         (unionBags r1
                                                                                                                    r2)
                                                                                                         (unionBags s1
                                                                                                                    s2))
                                                                    end in
                                                                  GHC.Base.op_zgzgze__ (f x) cont_144__
                                          end in
                                      MonadUtils.foldrM k (pair Mk_EmptyBag Mk_EmptyBag) xs
           end.

Definition flatMapBagM {m} {a} {b} `{GHC.Base.Monad m} : (a -> m (Bag b)) -> Bag
                                                         a -> m (Bag b) :=
  fix flatMapBagM arg_122__ arg_123__
        := match arg_122__ , arg_123__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ Mk_EmptyBag
             | f , (Mk_UnitBag x) => f x
             | f , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (flatMapBagM f b1) (fun r1 =>
                                                                GHC.Base.op_zgzgze__ (flatMapBagM f b2) (fun r2 =>
                                                                                       GHC.Base.return_ (unionBags r1
                                                                                                                   r2)))
             | f , (Mk_ListBag xs) => let k :=
                                        fun arg_127__ arg_128__ =>
                                          match arg_127__ , arg_128__ with
                                            | x , b2 => GHC.Base.op_zgzgze__ (f x) (fun b1 =>
                                                                               GHC.Base.return_ (unionBags b1 b2))
                                          end in
                                      MonadUtils.foldrM k Mk_EmptyBag xs
           end.

Definition filterBagM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> Bag a -> m
                                                    (Bag a) :=
  fix filterBagM arg_105__ arg_106__
        := match arg_105__ , arg_106__ with
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
  fix filterBag arg_97__ arg_98__
        := match arg_97__ , arg_98__ with
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
  fix elemBag arg_153__ arg_154__
        := match arg_153__ , arg_154__ with
             | _ , Mk_EmptyBag => false
             | x , (Mk_UnitBag y) => GHC.Base.op_zeze__ x y
             | x , (Mk_TwoBags b1 b2) => orb (elemBag x b1) (elemBag x b2)
             | x , (Mk_ListBag ys) => Data.Foldable.any (fun arg_157__ =>
                                                          GHC.Base.op_zeze__ x arg_157__) ys
           end.

Definition consBag {a} : a -> Bag a -> Bag a :=
  fun arg_166__ arg_167__ =>
    match arg_166__ , arg_167__ with
      | elt , bag => unionBags (unitBag elt) bag
    end.

Definition concatBag {a} : Bag (Bag a) -> Bag a :=
  fun arg_174__ =>
    match arg_174__ with
      | bss => let add :=
                 fun arg_175__ arg_176__ =>
                   match arg_175__ , arg_176__ with
                     | bs , rs => unionBags bs rs
                   end in
               foldrBag add emptyBag bss
    end.

Definition catBagMaybes {a} : Bag (option a) -> Bag a :=
  fun arg_181__ =>
    match arg_181__ with
      | bs => let add :=
                fun arg_182__ arg_183__ =>
                  match arg_182__ , arg_183__ with
                    | None , rs => rs
                    | (Some x) , rs => consBag x rs
                  end in
              foldrBag add emptyBag bs
    end.

Definition bagToList {a} : Bag a -> list a :=
  fun arg_67__ => match arg_67__ with | b => foldrBag cons nil b end.

Definition anyBagM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> Bag a -> m
                                                 bool :=
  fix anyBagM arg_78__ arg_79__
        := match arg_78__ , arg_79__ with
             | _ , Mk_EmptyBag => GHC.Base.return_ false
             | p , (Mk_UnitBag v) => p v
             | p , (Mk_TwoBags b1 b2) => GHC.Base.op_zgzgze__ (anyBagM p b1) (fun flag =>
                                                                if flag : bool
                                                                then GHC.Base.return_ true
                                                                else anyBagM p b2)
             | p , (Mk_ListBag xs) => MonadUtils.anyM p xs
           end.

Definition anyBag {a} : (a -> bool) -> Bag a -> bool :=
  fix anyBag arg_85__ arg_86__
        := match arg_85__ , arg_86__ with
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
     MonadUtils.anyM MonadUtils.foldlM MonadUtils.foldrM Some bool cons false list
     nil option orb pair true tt unit
*)
