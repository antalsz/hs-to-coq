(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Data.Monoid.
(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Either.
Require Data.Maybe.
Require Data.Monoid.
Require Data.Proxy.
Require Data.Semigroup.Internal.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Tuple.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Record Foldable__Dict t := Foldable__Dict_Build {
  elem__ : forall {a}, forall `{GHC.Base.Eq_ a}, a -> t a -> bool ;
  fold__ : forall {m}, forall `{GHC.Base.Monoid m}, t m -> m ;
  foldMap__ : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m ;
  foldl__ : forall {b} {a}, (b -> a -> b) -> b -> t a -> b ;
  foldl'__ : forall {b} {a}, (b -> a -> b) -> b -> t a -> b ;
  foldr__ : forall {a} {b}, (a -> b -> b) -> b -> t a -> b ;
  foldr'__ : forall {a} {b}, (a -> b -> b) -> b -> t a -> b ;
  length__ : forall {a}, t a -> GHC.Num.Int ;
  null__ : forall {a}, t a -> bool ;
  product__ : forall {a}, forall `{GHC.Num.Num a}, t a -> a ;
  sum__ : forall {a}, forall `{GHC.Num.Num a}, t a -> a ;
  toList__ : forall {a}, t a -> list a }.

Definition Foldable t :=
  forall r, (Foldable__Dict t -> r) -> r.

Existing Class Foldable.

Definition elem `{g : Foldable t}
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> t a -> bool :=
  g _ (elem__ t).

Definition fold `{g : Foldable t}
   : forall {m}, forall `{GHC.Base.Monoid m}, t m -> m :=
  g _ (fold__ t).

Definition foldMap `{g : Foldable t}
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m :=
  g _ (foldMap__ t).

Definition foldl `{g : Foldable t}
   : forall {b} {a}, (b -> a -> b) -> b -> t a -> b :=
  g _ (foldl__ t).

Definition foldl' `{g : Foldable t}
   : forall {b} {a}, (b -> a -> b) -> b -> t a -> b :=
  g _ (foldl'__ t).

Definition foldr `{g : Foldable t}
   : forall {a} {b}, (a -> b -> b) -> b -> t a -> b :=
  g _ (foldr__ t).

Definition foldr' `{g : Foldable t}
   : forall {a} {b}, (a -> b -> b) -> b -> t a -> b :=
  g _ (foldr'__ t).

Definition length `{g : Foldable t} : forall {a}, t a -> GHC.Num.Int :=
  g _ (length__ t).

Definition null `{g : Foldable t} : forall {a}, t a -> bool :=
  g _ (null__ t).

Definition product `{g : Foldable t}
   : forall {a}, forall `{GHC.Num.Num a}, t a -> a :=
  g _ (product__ t).

Definition sum `{g : Foldable t}
   : forall {a}, forall `{GHC.Num.Num a}, t a -> a :=
  g _ (sum__ t).

Definition toList `{g : Foldable t} : forall {a}, t a -> list a :=
  g _ (toList__ t).
(* Midamble *)

Definition default_elem {t : Type -> Type} {a} `{GHC.Base.Eq_ a} (foldMap : (a -> Data.Semigroup.Internal.Any) -> t a -> Data.Semigroup.Internal.Any) :
  a -> t a -> bool :=
   fun x xs => Data.Semigroup.Internal.getAny (foldMap (fun y => Data.Semigroup.Internal.Mk_Any (GHC.Base.op_zeze__ x y)) xs).

Definition default_foldable {f:Type -> Type}
  (foldMap : forall m a, forall (S : GHC.Base.Semigroup m) (M : GHC.Base.Monoid m), (a -> m) -> f a -> m)
  (foldr : forall a b, (a -> b -> b) -> b -> f a -> b):=
  let foldl : forall b a, (b -> a -> b) -> b -> f a -> b :=
      (fun b a =>
         fun f  z t => Data.Semigroup.Internal.appEndo
                    (Data.Semigroup.Internal.getDual
                       (foldMap _ _ _ _ (Coq.Program.Basics.compose
                                   Data.Semigroup.Internal.Mk_Dual
                                   (Coq.Program.Basics.compose
                                      Data.Semigroup.Internal.Mk_Endo
                                      (GHC.Base.flip f))) t)) z)
  in
  let foldl' : forall b a, (b -> a -> b) -> b -> f a -> b :=
      (fun {b} {a} =>
         fun f  z0  xs =>
           let f' :=  fun  x  k  z => GHC.Base.op_zdzn__ k (f z x)
           in foldr _ _ f' GHC.Base.id xs z0)
  in
  Foldable__Dict_Build
    f
    (fun {a} `{GHC.Base.Eq_ a} =>
       Coq.Program.Basics.compose
         (fun p => Coq.Program.Basics.compose
                  Data.Semigroup.Internal.getAny
                  (foldMap _ _ _ _ (fun x => Data.Semigroup.Internal.Mk_Any (p x))))
         GHC.Base.op_zeze__ )
    (* fold *)
    (fun m (S : GHC.Base.Semigroup m) (M : GHC.Base.Monoid m) => foldMap _ _ _ _ GHC.Base.id)
    (* foldMap *)
    (@foldMap)
    (* foldl *)
    (@foldl)
    (* foldl' *)
    (@foldl')
    (* foldr  *)
    (@foldr)
    (* foldr' *)
    (fun a b f z0 xs =>
       let f' := fun k  x  z => GHC.Base.op_zdzn__ k (f x z)
       in
       @foldl _ _ f' GHC.Base.id xs z0)
    (* length *)
    (fun a => @foldl' _ a (fun c  _ => GHC.Num.op_zp__ c (GHC.Num.fromInteger 1))
                    (GHC.Num.fromInteger 0))
    (* null *)
    (fun a => @foldr _ _ (fun arg_61__ arg_62__ => false) true)
    (* product *)
    (fun a `{GHC.Num.Num a} =>
       Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                                  (foldMap _ _ _ _ Data.Semigroup.Internal.Mk_Product))
    (* sum *)
    (fun a `{GHC.Num.Num a} =>
       Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                                  (foldMap _ _ _ _ Data.Semigroup.Internal.Mk_Sum))
    (* toList *)
    (fun a => fun t => GHC.Base.build (fun _ c n => @foldr _ _ c n t)).

Definition default_foldable_foldMap {f : Type -> Type}
  (foldMap : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> f a -> m)
 :=
  let foldr : forall {a} {b}, (a -> b -> b) -> b -> f a -> b :=
  fun a b f z t =>
    Data.Semigroup.Internal.appEndo
      (foldMap
         (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Endo f) t) z
  in
  default_foldable (fun {m}{a} `{GHC.Base.Monoid m} => foldMap) foldr.

Definition default_foldable_foldr (f : Type -> Type)
  (foldr : forall {a} {b}, (a -> b -> b) -> b -> f a -> b) :=
  let foldMap :  forall {m} {a} `{GHC.Base.Monoid m}, (a -> m) -> f a -> m :=
  fun m a (S : GHC.Base.Semigroup m) (H : GHC.Base.Monoid m) =>
    fun f => foldr
            (Coq.Program.Basics.compose GHC.Base.mappend
                                        f) GHC.Base.mempty
  in
  default_foldable foldMap (fun {a} {b} => foldr).

(* Converted value declarations: *)

Local Definition Foldable__option_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> option a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => Data.Maybe.maybe GHC.Base.mempty.

Local Definition Foldable__option_product
   : forall {a}, forall `{GHC.Num.Num a}, option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__option_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__option_sum
   : forall {a}, forall `{GHC.Num.Num a}, option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__option_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__option_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, option m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__option_foldMap GHC.Base.id.

Local Definition Foldable__option_elem {a} {H : GHC.Base.Eq_ a}
   : a -> option a -> bool :=
  default_elem Foldable__option_foldMap.

Local Definition Foldable__option_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> option a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, None => z
      | f, z, Some x => f z x
      end.

Local Definition Foldable__option_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> option a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__option_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__option_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> option a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, None => z
      | f, z, Some x => f x z
      end.

Local Definition Foldable__option_null : forall {a}, option a -> bool :=
  fun {a} => Foldable__option_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__option_toList : forall {a}, option a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__option_foldr c n t)).

Local Definition Foldable__option_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> option a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__option_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__option_length
   : forall {a}, option a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__option_foldl' (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | c, _ => c GHC.Num.+ #1
                               end) #0.

Program Instance Foldable__option : Foldable option :=
  fun _ k =>
    k {| elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__option_elem ;
         fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__option_fold ;
         foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} => Foldable__option_foldMap ;
         foldl__ := fun {b} {a} => Foldable__option_foldl ;
         foldl'__ := fun {b} {a} => Foldable__option_foldl' ;
         foldr__ := fun {a} {b} => Foldable__option_foldr ;
         foldr'__ := fun {a} {b} => Foldable__option_foldr' ;
         length__ := fun {a} => Foldable__option_length ;
         null__ := fun {a} => Foldable__option_null ;
         product__ := fun {a} `{GHC.Num.Num a} => Foldable__option_product ;
         sum__ := fun {a} `{GHC.Num.Num a} => Foldable__option_sum ;
         toList__ := fun {a} => Foldable__option_toList |}.

Local Definition Foldable__list_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> list a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => GHC.List.elem.

Local Definition Foldable__list_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> list a -> b :=
  fun {b} {a} => GHC.Base.foldl.

Local Definition Foldable__list_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> list a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__list_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__list_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> list a -> b :=
  fun {b} {a} => GHC.Base.foldl'.

Local Definition Foldable__list_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> list a -> b :=
  fun {a} {b} => GHC.Base.foldr.

Local Definition Foldable__list_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> list a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f => Foldable__list_foldr (GHC.Base.mappend GHC.Base.∘ f) GHC.Base.mempty.

Local Definition Foldable__list_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, list m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__list_foldMap GHC.Base.id.

Local Definition Foldable__list_length : forall {a}, list a -> GHC.Num.Int :=
  fun {a} => GHC.List.length.

Local Definition Foldable__list_null : forall {a}, list a -> bool :=
  fun {a} => GHC.List.null.

Local Definition Foldable__list_product
   : forall {a}, forall `{GHC.Num.Num a}, list a -> a :=
  fun {a} `{GHC.Num.Num a} => GHC.List.product.

Local Definition Foldable__list_sum
   : forall {a}, forall `{GHC.Num.Num a}, list a -> a :=
  fun {a} `{GHC.Num.Num a} => GHC.List.sum.

Local Definition Foldable__list_toList : forall {a}, list a -> list a :=
  fun {a} => GHC.Base.id.

Program Instance Foldable__list : Foldable list :=
  fun _ k =>
    k {| elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__list_elem ;
         fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__list_fold ;
         foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} => Foldable__list_foldMap ;
         foldl__ := fun {b} {a} => Foldable__list_foldl ;
         foldl'__ := fun {b} {a} => Foldable__list_foldl' ;
         foldr__ := fun {a} {b} => Foldable__list_foldr ;
         foldr'__ := fun {a} {b} => Foldable__list_foldr' ;
         length__ := fun {a} => Foldable__list_length ;
         null__ := fun {a} => Foldable__list_null ;
         product__ := fun {a} `{GHC.Num.Num a} => Foldable__list_product ;
         sum__ := fun {a} `{GHC.Num.Num a} => Foldable__list_sum ;
         toList__ := fun {a} => Foldable__list_toList |}.

Local Definition Foldable__NonEmpty_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, GHC.Base.NonEmpty m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    fun arg_0__ =>
      let 'GHC.Base.NEcons m ms := arg_0__ in
      GHC.Base.mappend m (fold ms).

Local Definition Foldable__NonEmpty_foldMap
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GHC.Base.NonEmpty a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Base.NEcons a as_ => GHC.Base.mappend (f a) (foldMap f as_)
      end.

Local Definition Foldable__NonEmpty_product
   : forall {a}, forall `{GHC.Num.Num a}, GHC.Base.NonEmpty a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__NonEmpty_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__NonEmpty_sum
   : forall {a}, forall `{GHC.Num.Num a}, GHC.Base.NonEmpty a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__NonEmpty_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__NonEmpty_elem {a} {H : GHC.Base.Eq_ a}
   : a -> GHC.Base.NonEmpty a -> bool :=
  default_elem Foldable__NonEmpty_foldMap.

Local Definition Foldable__NonEmpty_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> GHC.Base.NonEmpty a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Base.NEcons a as_ => GHC.Base.foldl f (f z a) as_
      end.

Local Definition Foldable__NonEmpty_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> GHC.Base.NonEmpty a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__NonEmpty_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__NonEmpty_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> GHC.Base.NonEmpty a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, GHC.Base.NEcons a as_ => f a (GHC.Base.foldr f z as_)
      end.

Local Definition Foldable__NonEmpty_null
   : forall {a}, GHC.Base.NonEmpty a -> bool :=
  fun {a} => Foldable__NonEmpty_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__NonEmpty_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> GHC.Base.NonEmpty a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__NonEmpty_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__NonEmpty_length
   : forall {a}, GHC.Base.NonEmpty a -> GHC.Num.Int :=
  fun {a} =>
    fun arg_0__ =>
      let 'GHC.Base.NEcons _ as_ := arg_0__ in
      #1 GHC.Num.+ GHC.List.length as_.

Local Definition Foldable__NonEmpty_toList
   : forall {a}, GHC.Base.NonEmpty a -> list a :=
  fun {a} => fun arg_0__ => let 'GHC.Base.NEcons a as_ := arg_0__ in cons a as_.

Program Instance Foldable__NonEmpty : Foldable GHC.Base.NonEmpty :=
  fun _ k =>
    k {| elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__NonEmpty_elem ;
         fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__NonEmpty_fold ;
         foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} => Foldable__NonEmpty_foldMap ;
         foldl__ := fun {b} {a} => Foldable__NonEmpty_foldl ;
         foldl'__ := fun {b} {a} => Foldable__NonEmpty_foldl' ;
         foldr__ := fun {a} {b} => Foldable__NonEmpty_foldr ;
         foldr'__ := fun {a} {b} => Foldable__NonEmpty_foldr' ;
         length__ := fun {a} => Foldable__NonEmpty_length ;
         null__ := fun {a} => Foldable__NonEmpty_null ;
         product__ := fun {a} `{GHC.Num.Num a} => Foldable__NonEmpty_product ;
         sum__ := fun {a} `{GHC.Num.Num a} => Foldable__NonEmpty_sum ;
         toList__ := fun {a} => Foldable__NonEmpty_toList |}.

Local Definition Foldable__Either_foldMap {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Data.Either.Either inst_a) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Data.Either.Left _ => GHC.Base.mempty
      | f, Data.Either.Right y => f y
      end.

Local Definition Foldable__Either_foldl {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Data.Either.Either inst_a) a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                       (Foldable__Either_foldMap (Data.Semigroup.Internal.Mk_Dual GHC.Base.∘
                                                                  (Data.Semigroup.Internal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

Local Definition Foldable__Either_foldr' {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Data.Either.Either inst_a) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Either_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Either_product {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (Data.Either.Either inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__Either_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__Either_sum {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (Data.Either.Either inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__Either_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__Either_fold {inst_a}
   : forall {m},
     forall `{GHC.Base.Monoid m}, (Data.Either.Either inst_a) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Either_foldMap GHC.Base.id.

Local Definition Foldable__Either_elem {inst_a} {a} {H : GHC.Base.Eq_ a}
   : a -> Data.Either.Either inst_a a -> bool :=
  default_elem Foldable__Either_foldMap.

Local Definition Foldable__Either_foldr {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Data.Either.Either inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, Data.Either.Left _ => z
      | f, z, Data.Either.Right y => f y z
      end.

Local Definition Foldable__Either_toList {inst_a}
   : forall {a}, (Data.Either.Either inst_a) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Either_foldr c n t)).

Local Definition Foldable__Either_foldl' {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Data.Either.Either inst_a) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Either_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Either_length {inst_a}
   : forall {a}, (Data.Either.Either inst_a) a -> GHC.Num.Int :=
  fun {a} =>
    fun arg_0__ =>
      match arg_0__ with
      | Data.Either.Left _ => #0
      | Data.Either.Right _ => #1
      end.

Local Definition Foldable__Either_null {inst_a}
   : forall {a}, (Data.Either.Either inst_a) a -> bool :=
  fun {a} => Data.Either.isLeft.

Program Instance Foldable__Either {a} : Foldable (Data.Either.Either a) :=
  fun _ k =>
    k {| elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Either_elem ;
         fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Either_fold ;
         foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} => Foldable__Either_foldMap ;
         foldl__ := fun {b} {a} => Foldable__Either_foldl ;
         foldl'__ := fun {b} {a} => Foldable__Either_foldl' ;
         foldr__ := fun {a} {b} => Foldable__Either_foldr ;
         foldr'__ := fun {a} {b} => Foldable__Either_foldr' ;
         length__ := fun {a} => Foldable__Either_length ;
         null__ := fun {a} => Foldable__Either_null ;
         product__ := fun {a} `{GHC.Num.Num a} => Foldable__Either_product ;
         sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Either_sum ;
         toList__ := fun {a} => Foldable__Either_toList |}.

Local Definition Foldable__pair_type_foldMap {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (GHC.Tuple.pair_type inst_a) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, pair _ y => f y end.

Local Definition Foldable__pair_type_foldl {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (GHC.Tuple.pair_type inst_a) a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                       (Foldable__pair_type_foldMap (Data.Semigroup.Internal.Mk_Dual GHC.Base.∘
                                                                     (Data.Semigroup.Internal.Mk_Endo GHC.Base.∘
                                                                      GHC.Base.flip f)) t)) z.

Local Definition Foldable__pair_type_foldr' {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (GHC.Tuple.pair_type inst_a) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__pair_type_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__pair_type_product {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (GHC.Tuple.pair_type inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__pair_type_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__pair_type_sum {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (GHC.Tuple.pair_type inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__pair_type_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__pair_type_fold {inst_a}
   : forall {m},
     forall `{GHC.Base.Monoid m}, (GHC.Tuple.pair_type inst_a) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__pair_type_foldMap GHC.Base.id.

Local Definition Foldable__pair_type_elem {inst_a} {a} {H : GHC.Base.Eq_ a}
   : a -> GHC.Tuple.pair_type inst_a a -> bool :=
  default_elem Foldable__pair_type_foldMap.

Local Definition Foldable__pair_type_foldr {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (GHC.Tuple.pair_type inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, pair _ y => f y z
      end.

Local Definition Foldable__pair_type_null {inst_a}
   : forall {a}, (GHC.Tuple.pair_type inst_a) a -> bool :=
  fun {a} => Foldable__pair_type_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__pair_type_toList {inst_a}
   : forall {a}, (GHC.Tuple.pair_type inst_a) a -> list a :=
  fun {a} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__pair_type_foldr c n t)).

Local Definition Foldable__pair_type_foldl' {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (GHC.Tuple.pair_type inst_a) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__pair_type_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__pair_type_length {inst_a}
   : forall {a}, (GHC.Tuple.pair_type inst_a) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__pair_type_foldl' (fun arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | c, _ => c GHC.Num.+ #1
                                  end) #0.

Program Instance Foldable__pair_type {a} : Foldable (GHC.Tuple.pair_type a) :=
  fun _ k =>
    k {| elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__pair_type_elem ;
         fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__pair_type_fold ;
         foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} => Foldable__pair_type_foldMap ;
         foldl__ := fun {b} {a} => Foldable__pair_type_foldl ;
         foldl'__ := fun {b} {a} => Foldable__pair_type_foldl' ;
         foldr__ := fun {a} {b} => Foldable__pair_type_foldr ;
         foldr'__ := fun {a} {b} => Foldable__pair_type_foldr' ;
         length__ := fun {a} => Foldable__pair_type_length ;
         null__ := fun {a} => Foldable__pair_type_null ;
         product__ := fun {a} `{GHC.Num.Num a} => Foldable__pair_type_product ;
         sum__ := fun {a} `{GHC.Num.Num a} => Foldable__pair_type_sum ;
         toList__ := fun {a} => Foldable__pair_type_toList |}.

(* Skipping instance Foldable__Array *)

Local Definition Foldable__Proxy_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> Data.Proxy.Proxy a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => fun arg_0__ arg_1__ => false.

Local Definition Foldable__Proxy_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Data.Proxy.Proxy m -> m :=
  fun {m} `{GHC.Base.Monoid m} => fun arg_0__ => GHC.Base.mempty.

Local Definition Foldable__Proxy_foldMap
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Proxy.Proxy a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => fun arg_0__ arg_1__ => GHC.Base.mempty.

Local Definition Foldable__Proxy_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, _ => z
      end.

Local Definition Foldable__Proxy_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Proxy_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Proxy_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, _ => z
      end.

Local Definition Foldable__Proxy_toList
   : forall {a}, Data.Proxy.Proxy a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Proxy_foldr c n t)).

Local Definition Foldable__Proxy_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Proxy_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Proxy_length
   : forall {a}, Data.Proxy.Proxy a -> GHC.Num.Int :=
  fun {a} => fun arg_0__ => #0.

Local Definition Foldable__Proxy_null
   : forall {a}, Data.Proxy.Proxy a -> bool :=
  fun {a} => fun arg_0__ => true.

Local Definition Foldable__Proxy_product
   : forall {a}, forall `{GHC.Num.Num a}, Data.Proxy.Proxy a -> a :=
  fun {a} `{GHC.Num.Num a} => fun arg_0__ => #1.

Local Definition Foldable__Proxy_sum
   : forall {a}, forall `{GHC.Num.Num a}, Data.Proxy.Proxy a -> a :=
  fun {a} `{GHC.Num.Num a} => fun arg_0__ => #0.

Program Instance Foldable__Proxy : Foldable Data.Proxy.Proxy :=
  fun _ k =>
    k {| elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Proxy_elem ;
         fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Proxy_fold ;
         foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} => Foldable__Proxy_foldMap ;
         foldl__ := fun {b} {a} => Foldable__Proxy_foldl ;
         foldl'__ := fun {b} {a} => Foldable__Proxy_foldl' ;
         foldr__ := fun {a} {b} => Foldable__Proxy_foldr ;
         foldr'__ := fun {a} {b} => Foldable__Proxy_foldr' ;
         length__ := fun {a} => Foldable__Proxy_length ;
         null__ := fun {a} => Foldable__Proxy_null ;
         product__ := fun {a} `{GHC.Num.Num a} => Foldable__Proxy_product ;
         sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Proxy_sum ;
         toList__ := fun {a} => Foldable__Proxy_toList |}.

Local Definition Foldable__Dual_elem
   : forall {a},
     forall `{GHC.Base.Eq_ a}, a -> Data.Semigroup.Internal.Dual a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_0__ =>
                                  arg_0__ GHC.Base.∘ Data.Semigroup.Internal.getDual) _GHC.Base.==_.

Local Definition Foldable__Dual_foldMap
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Semigroup.Internal.Dual a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

Local Definition Foldable__Dual_fold
   : forall {m},
     forall `{GHC.Base.Monoid m}, Data.Semigroup.Internal.Dual m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Dual_foldMap GHC.Base.id.

Local Definition Foldable__Dual_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Data.Semigroup.Internal.Dual a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition Foldable__Dual_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Data.Semigroup.Internal.Dual a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition Foldable__Dual_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Data.Semigroup.Internal.Dual a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Data.Semigroup.Internal.Mk_Dual x => f x z
      end.

Local Definition Foldable__Dual_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Data.Semigroup.Internal.Dual a -> b :=
  fun {a} {b} => Foldable__Dual_foldr.

Local Definition Foldable__Dual_length
   : forall {a}, Data.Semigroup.Internal.Dual a -> GHC.Num.Int :=
  fun {a} => fun arg_0__ => #1.

Local Definition Foldable__Dual_null
   : forall {a}, Data.Semigroup.Internal.Dual a -> bool :=
  fun {a} => fun arg_0__ => false.

Local Definition Foldable__Dual_product
   : forall {a}, forall `{GHC.Num.Num a}, Data.Semigroup.Internal.Dual a -> a :=
  fun {a} `{GHC.Num.Num a} => Data.Semigroup.Internal.getDual.

Local Definition Foldable__Dual_sum
   : forall {a}, forall `{GHC.Num.Num a}, Data.Semigroup.Internal.Dual a -> a :=
  fun {a} `{GHC.Num.Num a} => Data.Semigroup.Internal.getDual.

Local Definition Foldable__Dual_toList
   : forall {a}, Data.Semigroup.Internal.Dual a -> list a :=
  fun {a} =>
    fun arg_0__ => let 'Data.Semigroup.Internal.Mk_Dual x := arg_0__ in cons x nil.

Program Instance Foldable__Dual : Foldable Data.Semigroup.Internal.Dual :=
  fun _ k =>
    k {| elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Dual_elem ;
         fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Dual_fold ;
         foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} => Foldable__Dual_foldMap ;
         foldl__ := fun {b} {a} => Foldable__Dual_foldl ;
         foldl'__ := fun {b} {a} => Foldable__Dual_foldl' ;
         foldr__ := fun {a} {b} => Foldable__Dual_foldr ;
         foldr'__ := fun {a} {b} => Foldable__Dual_foldr' ;
         length__ := fun {a} => Foldable__Dual_length ;
         null__ := fun {a} => Foldable__Dual_null ;
         product__ := fun {a} `{GHC.Num.Num a} => Foldable__Dual_product ;
         sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Dual_sum ;
         toList__ := fun {a} => Foldable__Dual_toList |}.

Local Definition Foldable__Sum_elem
   : forall {a},
     forall `{GHC.Base.Eq_ a}, a -> Data.Semigroup.Internal.Sum a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_0__ =>
                                  arg_0__ GHC.Base.∘ Data.Semigroup.Internal.getSum) _GHC.Base.==_.

Local Definition Foldable__Sum_foldMap
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Data.Semigroup.Internal.Sum a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

Local Definition Foldable__Sum_fold
   : forall {m},
     forall `{GHC.Base.Monoid m}, Data.Semigroup.Internal.Sum m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Sum_foldMap GHC.Base.id.

Local Definition Foldable__Sum_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Data.Semigroup.Internal.Sum a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition Foldable__Sum_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Data.Semigroup.Internal.Sum a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition Foldable__Sum_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Data.Semigroup.Internal.Sum a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Data.Semigroup.Internal.Mk_Sum x => f x z
      end.

Local Definition Foldable__Sum_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Data.Semigroup.Internal.Sum a -> b :=
  fun {a} {b} => Foldable__Sum_foldr.

Local Definition Foldable__Sum_length
   : forall {a}, Data.Semigroup.Internal.Sum a -> GHC.Num.Int :=
  fun {a} => fun arg_0__ => #1.

Local Definition Foldable__Sum_null
   : forall {a}, Data.Semigroup.Internal.Sum a -> bool :=
  fun {a} => fun arg_0__ => false.

Local Definition Foldable__Sum_product
   : forall {a}, forall `{GHC.Num.Num a}, Data.Semigroup.Internal.Sum a -> a :=
  fun {a} `{GHC.Num.Num a} => Data.Semigroup.Internal.getSum.

Local Definition Foldable__Sum_sum
   : forall {a}, forall `{GHC.Num.Num a}, Data.Semigroup.Internal.Sum a -> a :=
  fun {a} `{GHC.Num.Num a} => Data.Semigroup.Internal.getSum.

Local Definition Foldable__Sum_toList
   : forall {a}, Data.Semigroup.Internal.Sum a -> list a :=
  fun {a} =>
    fun arg_0__ => let 'Data.Semigroup.Internal.Mk_Sum x := arg_0__ in cons x nil.

Program Instance Foldable__Sum : Foldable Data.Semigroup.Internal.Sum :=
  fun _ k =>
    k {| elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Sum_elem ;
         fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Sum_fold ;
         foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} => Foldable__Sum_foldMap ;
         foldl__ := fun {b} {a} => Foldable__Sum_foldl ;
         foldl'__ := fun {b} {a} => Foldable__Sum_foldl' ;
         foldr__ := fun {a} {b} => Foldable__Sum_foldr ;
         foldr'__ := fun {a} {b} => Foldable__Sum_foldr' ;
         length__ := fun {a} => Foldable__Sum_length ;
         null__ := fun {a} => Foldable__Sum_null ;
         product__ := fun {a} `{GHC.Num.Num a} => Foldable__Sum_product ;
         sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Sum_sum ;
         toList__ := fun {a} => Foldable__Sum_toList |}.

Local Definition Foldable__Product_elem
   : forall {a},
     forall `{GHC.Base.Eq_ a}, a -> Data.Semigroup.Internal.Product a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_0__ =>
                                  arg_0__ GHC.Base.∘ Data.Semigroup.Internal.getProduct) _GHC.Base.==_.

Local Definition Foldable__Product_foldMap
   : forall {m} {a},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> Data.Semigroup.Internal.Product a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

Local Definition Foldable__Product_fold
   : forall {m},
     forall `{GHC.Base.Monoid m}, Data.Semigroup.Internal.Product m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Product_foldMap GHC.Base.id.

Local Definition Foldable__Product_foldl
   : forall {b} {a},
     (b -> a -> b) -> b -> Data.Semigroup.Internal.Product a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition Foldable__Product_foldl'
   : forall {b} {a},
     (b -> a -> b) -> b -> Data.Semigroup.Internal.Product a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition Foldable__Product_foldr
   : forall {a} {b},
     (a -> b -> b) -> b -> Data.Semigroup.Internal.Product a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Data.Semigroup.Internal.Mk_Product x => f x z
      end.

Local Definition Foldable__Product_foldr'
   : forall {a} {b},
     (a -> b -> b) -> b -> Data.Semigroup.Internal.Product a -> b :=
  fun {a} {b} => Foldable__Product_foldr.

Local Definition Foldable__Product_length
   : forall {a}, Data.Semigroup.Internal.Product a -> GHC.Num.Int :=
  fun {a} => fun arg_0__ => #1.

Local Definition Foldable__Product_null
   : forall {a}, Data.Semigroup.Internal.Product a -> bool :=
  fun {a} => fun arg_0__ => false.

Local Definition Foldable__Product_product
   : forall {a},
     forall `{GHC.Num.Num a}, Data.Semigroup.Internal.Product a -> a :=
  fun {a} `{GHC.Num.Num a} => Data.Semigroup.Internal.getProduct.

Local Definition Foldable__Product_sum
   : forall {a},
     forall `{GHC.Num.Num a}, Data.Semigroup.Internal.Product a -> a :=
  fun {a} `{GHC.Num.Num a} => Data.Semigroup.Internal.getProduct.

Local Definition Foldable__Product_toList
   : forall {a}, Data.Semigroup.Internal.Product a -> list a :=
  fun {a} =>
    fun arg_0__ =>
      let 'Data.Semigroup.Internal.Mk_Product x := arg_0__ in
      cons x nil.

Program Instance Foldable__Product : Foldable Data.Semigroup.Internal.Product :=
  fun _ k =>
    k {| elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Product_elem ;
         fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Product_fold ;
         foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} => Foldable__Product_foldMap ;
         foldl__ := fun {b} {a} => Foldable__Product_foldl ;
         foldl'__ := fun {b} {a} => Foldable__Product_foldl' ;
         foldr__ := fun {a} {b} => Foldable__Product_foldr ;
         foldr'__ := fun {a} {b} => Foldable__Product_foldr' ;
         length__ := fun {a} => Foldable__Product_length ;
         null__ := fun {a} => Foldable__Product_null ;
         product__ := fun {a} `{GHC.Num.Num a} => Foldable__Product_product ;
         sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Product_sum ;
         toList__ := fun {a} => Foldable__Product_toList |}.

(* Skipping instance Foldable__First *)

(* Skipping instance Foldable__Last *)

(* Skipping instance Foldable__U1 *)

(* Skipping instance Foldable__V1 *)

(* Skipping instance Foldable__Par1 *)

(* Skipping instance Foldable__Rec1 *)

(* Skipping instance Foldable__K1 *)

(* Skipping instance Foldable__M1 *)

(* Skipping instance Foldable__op_ZCzpZC__ *)

(* Skipping instance Foldable__op_ZCztZC__ *)

(* Skipping instance Foldable__op_ZCziZC__ *)

(* Skipping instance Foldable__URec__Ptr__unit *)

(* Skipping instance Foldable__URec__Char *)

(* Skipping instance Foldable__URec__Double *)

(* Skipping instance Foldable__URec__Float *)

(* Skipping instance Foldable__URec__Int *)

(* Skipping instance Foldable__URec__Word *)

Definition all {t} {a} `{Foldable t} : (a -> bool) -> t a -> bool :=
  fun p =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getAll (foldMap
                                (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_All p)).

Definition and {t} `{Foldable t} : t bool -> bool :=
  Coq.Program.Basics.compose Data.Semigroup.Internal.getAll (foldMap
                              Data.Semigroup.Internal.Mk_All).

Definition any {t} {a} `{Foldable t} : (a -> bool) -> t a -> bool :=
  fun p =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getAny (foldMap
                                (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Any p)).

Definition asum {t} {f} {a} `{Foldable t} `{GHC.Base.Alternative f}
   : t (f a) -> f a :=
  foldr _GHC.Base.<|>_ GHC.Base.empty.

Definition msum {t} {m} {a} `{Foldable t} `{GHC.Base.MonadPlus m}
   : t (m a) -> m a :=
  asum.

Definition concat {t} {a} `{Foldable t} : t (list a) -> list a :=
  fun xs =>
    GHC.Base.build' (fun _ =>
                       fun c n => foldr (fun x y => (@foldr _ Foldable__list _ _ c y x)) n xs).

Definition concatMap {t} {a} {b} `{Foldable t}
   : (a -> list b) -> t a -> list b :=
  fun f xs =>
    GHC.Base.build' (fun _ => (fun c n => foldr (fun x b => foldr c b (f x)) n xs)).

Definition find {t} {a} `{Foldable t} : (a -> bool) -> t a -> option a :=
  fun p =>
    Data.Monoid.getFirst GHC.Base.∘
    foldMap (fun x => Data.Monoid.Mk_First (if p x : bool then Some x else None)).

Definition foldlM {t} {m} {b} {a} `{Foldable t} `{GHC.Base.Monad m}
   : (b -> a -> m b) -> b -> t a -> m b :=
  fun f z0 xs =>
    let f' := fun x k z => f z x GHC.Base.>>= k in foldr f' GHC.Base.return_ xs z0.

Definition foldrM {t} {m} {a} {b} `{Foldable t} `{GHC.Base.Monad m}
   : (a -> b -> m b) -> b -> t a -> m b :=
  fun f z0 xs =>
    let f' := fun k x z => f x z GHC.Base.>>= k in foldl f' GHC.Base.return_ xs z0.

Definition mapM_ {t} {m} {a} {b} `{Foldable t} `{GHC.Base.Monad m}
   : (a -> m b) -> t a -> m unit :=
  fun f => foldr (_GHC.Base.>>_ GHC.Base.∘ f) (GHC.Base.return_ tt).

Definition forM_ {t} {m} {a} {b} `{Foldable t} `{GHC.Base.Monad m}
   : t a -> (a -> m b) -> m unit :=
  GHC.Base.flip mapM_.

Definition notElem {t} {a} `{Foldable t} `{GHC.Base.Eq_ a} : a -> t a -> bool :=
  fun x => negb GHC.Base.∘ elem x.

Definition or {t} `{Foldable t} : t bool -> bool :=
  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny (foldMap
                              Data.Semigroup.Internal.Mk_Any).

Definition sequenceA_ {t} {f} {a} `{Foldable t} `{GHC.Base.Applicative f}
   : t (f a) -> f unit :=
  foldr _GHC.Base.*>_ (GHC.Base.pure tt).

Definition sequence_ {t} {m} {a} `{Foldable t} `{GHC.Base.Monad m}
   : t (m a) -> m unit :=
  foldr _GHC.Base.>>_ (GHC.Base.return_ tt).

Definition traverse_ {t} {f} {a} {b} `{Foldable t} `{GHC.Base.Applicative f}
   : (a -> f b) -> t a -> f unit :=
  fun f => foldr (_GHC.Base.*>_ GHC.Base.∘ f) (GHC.Base.pure tt).

Definition for__ {t} {f} {a} {b} `{Foldable t} `{GHC.Base.Applicative f}
   : t a -> (a -> f b) -> f unit :=
  GHC.Base.flip traverse_.

(* External variables:
     None Some bool cons default_elem false list negb nil option pair true tt unit
     Coq.Program.Basics.compose Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Either.isLeft Data.Maybe.maybe Data.Monoid.Mk_First Data.Monoid.getFirst
     Data.Proxy.Proxy Data.Semigroup.Internal.Dual Data.Semigroup.Internal.Mk_All
     Data.Semigroup.Internal.Mk_Any Data.Semigroup.Internal.Mk_Dual
     Data.Semigroup.Internal.Mk_Endo Data.Semigroup.Internal.Mk_Product
     Data.Semigroup.Internal.Mk_Sum Data.Semigroup.Internal.Product
     Data.Semigroup.Internal.Sum Data.Semigroup.Internal.appEndo
     Data.Semigroup.Internal.getAll Data.Semigroup.Internal.getAny
     Data.Semigroup.Internal.getDual Data.Semigroup.Internal.getProduct
     Data.Semigroup.Internal.getSum GHC.Base.Alternative GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Monad GHC.Base.MonadPlus GHC.Base.Monoid GHC.Base.NEcons
     GHC.Base.NonEmpty GHC.Base.build' GHC.Base.empty GHC.Base.flip GHC.Base.foldl
     GHC.Base.foldl' GHC.Base.foldr GHC.Base.id GHC.Base.mappend GHC.Base.mempty
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.op_zlzbzg__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.Base.return_
     GHC.List.elem GHC.List.length GHC.List.null GHC.List.product GHC.List.sum
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.coerce
     GHC.Tuple.pair_type
*)
