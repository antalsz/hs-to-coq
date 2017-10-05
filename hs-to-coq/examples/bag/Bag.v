(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted imports: *)

Require Coq.Lists.List.
Require Coq.Program.Basics.
Require GHC.Base.
Require GHC.List.

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

Definition unitBag {a} : a -> Bag a :=
  Mk_UnitBag.

Definition unionBags {a} : Bag a -> Bag a -> Bag a :=
  fun arg_29__ arg_30__ =>
    match arg_29__ , arg_30__ with
      | Mk_EmptyBag , b => b
      | b , Mk_EmptyBag => b
      | b1 , b2 => Mk_TwoBags b1 b2
    end.

Definition unionManyBags {a} : list (Bag a) -> Bag a :=
  fun arg_41__ =>
    match arg_41__ with
      | xs => Coq.Lists.List.fold_right unionBags Mk_EmptyBag xs
    end.

Definition snocBag {a} : Bag a -> a -> Bag a :=
  fun arg_48__ arg_49__ =>
    match arg_48__ , arg_49__ with
      | bag , elt => unionBags bag (unitBag elt)
    end.

Definition mapBag {a} {b} : (a -> b) -> Bag a -> Bag b :=
  fix mapBag arg_3__ arg_4__
        := match arg_3__ , arg_4__ with
             | _ , Mk_EmptyBag => Mk_EmptyBag
             | f , (Mk_UnitBag x) => Mk_UnitBag (f x)
             | f , (Mk_TwoBags b1 b2) => Mk_TwoBags (mapBag f b1) (mapBag f b2)
             | f , (Mk_ListBag xs) => Mk_ListBag (GHC.Base.map f xs)
           end.

Definition listToBag {a} : list a -> Bag a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Mk_EmptyBag
      | vs => Mk_ListBag vs
    end.

Definition isEmptyBag {a} : Bag a -> bool :=
  fun arg_27__ => match arg_27__ with | Mk_EmptyBag => true | _ => false end.

Definition foldrBag {a} {r} : (a -> r -> r) -> r -> Bag a -> r :=
  fix foldrBag arg_9__ arg_10__ arg_11__
        := match arg_9__ , arg_10__ , arg_11__ with
             | _ , z , Mk_EmptyBag => z
             | k , z , (Mk_UnitBag x) => k x z
             | k , z , (Mk_TwoBags b1 b2) => foldrBag k (foldrBag k z b2) b1
             | k , z , (Mk_ListBag xs) => Coq.Lists.List.fold_right k z xs
           end.

Definition foldBag {r} {a} : (r -> r -> r) -> (a -> r) -> r -> Bag a -> r :=
  fix foldBag arg_19__ arg_20__ arg_21__ arg_22__
        := match arg_19__ , arg_20__ , arg_21__ , arg_22__ with
             | _ , _ , e , Mk_EmptyBag => e
             | t , u , e , (Mk_UnitBag x) => t (u x) e
             | t , u , e , (Mk_TwoBags b1 b2) => foldBag t u (foldBag t u e b2) b1
             | t , u , e , (Mk_ListBag xs) => Coq.Lists.List.fold_right
                                              (Coq.Program.Basics.compose t u) e xs
           end.

Definition filterBag {a} : (a -> bool) -> Bag a -> Bag a :=
  fix filterBag arg_33__ arg_34__
        := match arg_33__ , arg_34__ with
             | _ , Mk_EmptyBag => Mk_EmptyBag
             | pred , ((Mk_UnitBag val) as b) => if pred val
                                                 then b
                                                 else Mk_EmptyBag
             | pred , (Mk_TwoBags b1 b2) => let sat2 := filterBag pred b2 in
                                            let sat1 := filterBag pred b1 in unionBags sat1 sat2
             | pred , (Mk_ListBag vs) => listToBag (GHC.List.filter pred vs)
           end.

Definition emptyBag {a} : Bag a :=
  Mk_EmptyBag.

Definition consBag {a} : a -> Bag a -> Bag a :=
  fun arg_44__ arg_45__ =>
    match arg_44__ , arg_45__ with
      | elt , bag => unionBags (unitBag elt) bag
    end.

Definition concatBag {a} : Bag (Bag a) -> Bag a :=
  fun arg_52__ =>
    match arg_52__ with
      | bss => let add :=
                 fun arg_53__ arg_54__ =>
                   match arg_53__ , arg_54__ with
                     | bs , rs => unionBags bs rs
                   end in
               foldrBag add emptyBag bss
    end.

Definition catBagMaybes {a} : Bag (option a) -> Bag a :=
  fun arg_59__ =>
    match arg_59__ with
      | bs => let add :=
                fun arg_60__ arg_61__ =>
                  match arg_60__ , arg_61__ with
                    | None , rs => rs
                    | (Some x) , rs => consBag x rs
                  end in
              foldrBag add emptyBag bs
    end.

Definition bagToList {a} : Bag a -> list a :=
  fun arg_16__ => match arg_16__ with | b => foldrBag cons nil b end.

(* Unbound variables:
     Coq.Lists.List.fold_right Coq.Program.Basics.compose GHC.Base.map
     GHC.List.filter Some bool cons false list nil option true
*)
