(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted imports: *)

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
  fun arg_11__ arg_12__ =>
    match arg_11__ , arg_12__ with
      | Mk_EmptyBag , b => b
      | b , Mk_EmptyBag => b
      | b1 , b2 => Mk_TwoBags b1 b2
    end.

Definition snocBag {a} : Bag a -> a -> Bag a :=
  fun arg_27__ arg_28__ =>
    match arg_27__ , arg_28__ with
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
  fun arg_9__ => match arg_9__ with | Mk_EmptyBag => true | _ => false end.

Definition filterBag {a} : (a -> bool) -> Bag a -> Bag a :=
  fix filterBag arg_15__ arg_16__
        := match arg_15__ , arg_16__ with
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
  fun arg_23__ arg_24__ =>
    match arg_23__ , arg_24__ with
      | elt , bag => unionBags (unitBag elt) bag
    end.

(* Unbound variables:
     GHC.Base.map GHC.List.filter bool false list true
*)
