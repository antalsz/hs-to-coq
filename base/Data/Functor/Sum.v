(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Classes.
Require Data.Monoid.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Sum f g a : Type
  := InL : (f a) -> Sum f g a
  |  InR : (g a) -> Sum f g a.

Arguments InL {_} {_} {_} _.

Arguments InR {_} {_} {_} _.
(* Midamble *)

Definition mempty_Sum {a} `{Num a} : Sum a := Mk_Sum #0.
Definition mappend_Sum {a} `{Num a} (x: Sum a) (y :Sum a)  : Sum a :=
  match x , y with
    | Mk_Sum i , Mk_Sum j => Mk_Sum (i + j)
  end.
Instance instance_GHC_Base_Monoid__Sum_a_ {a} `{Num a}:
  GHC.Base.Monoid (Sum a) := fun _ k => k
 {| mappend__ := mappend_Sum;
    mempty__  := mempty_Sum;
    mconcat__ := foldr mappend_Sum mempty_Sum |}.


(* Converted value declarations: *)

Local Definition Eq1__Sum_liftEq {inst_f} {inst_g} `{Data.Functor.Classes.Eq1
  inst_f} `{Data.Functor.Classes.Eq1 inst_g}
   : forall {a} {b},
     (a -> b -> bool) -> (Sum inst_f inst_g) a -> (Sum inst_f inst_g) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, InL x1, InL x2 => Data.Functor.Classes.liftEq eq x1 x2
      | _, InL _, InR _ => false
      | _, InR _, InL _ => false
      | eq, InR y1, InR y2 => Data.Functor.Classes.liftEq eq y1 y2
      end.

Program Instance Eq1__Sum {f} {g} `{Data.Functor.Classes.Eq1 f}
  `{Data.Functor.Classes.Eq1 g}
   : Data.Functor.Classes.Eq1 (Sum f g) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__Sum_liftEq |}.

Local Definition Ord1__Sum_liftCompare {inst_f} {inst_g}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Sum inst_f inst_g) a -> (Sum inst_f inst_g) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, InL x1, InL x2 => Data.Functor.Classes.liftCompare comp x1 x2
      | _, InL _, InR _ => Lt
      | _, InR _, InL _ => Gt
      | comp, InR y1, InR y2 => Data.Functor.Classes.liftCompare comp y1 y2
      end.

Program Instance Ord1__Sum {f} {g} `{Data.Functor.Classes.Ord1 f}
  `{Data.Functor.Classes.Ord1 g}
   : Data.Functor.Classes.Ord1 (Sum f g) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
           Ord1__Sum_liftCompare |}.

(* Translating `instance Read1__Sum' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Show1__Sum' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Show1" unsupported *)

Local Definition Eq___Sum_op_zeze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
  `{GHC.Base.Eq_ inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Sum_op_zsze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
  `{GHC.Base.Eq_ inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => negb (Eq___Sum_op_zeze__ x y).

Program Instance Eq___Sum {f} {g} {a} `{Data.Functor.Classes.Eq1 f}
  `{Data.Functor.Classes.Eq1 g} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Sum f g a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Sum_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Sum_op_zsze__ |}.

Local Definition Ord__Sum_compare {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Sum_op_zg__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base.== Gt.

Local Definition Ord__Sum_op_zgze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base./= Lt.

Local Definition Ord__Sum_op_zl__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base.== Lt.

Local Definition Ord__Sum_op_zlze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base./= Gt.

Local Definition Ord__Sum_max {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) ->
     (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) :=
  fun x y => if Ord__Sum_op_zlze__ x y : bool then y else x.

Local Definition Ord__Sum_min {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) ->
     (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) :=
  fun x y => if Ord__Sum_op_zlze__ x y : bool then x else y.

Program Instance Ord__Sum {f} {g} {a} `{Data.Functor.Classes.Ord1 f}
  `{Data.Functor.Classes.Ord1 g} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Sum f g a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Sum_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Sum_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Sum_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Sum_op_zgze__ ;
         GHC.Base.compare__ := Ord__Sum_compare ;
         GHC.Base.max__ := Ord__Sum_max ;
         GHC.Base.min__ := Ord__Sum_min |}.

(* Translating `instance Read__Sum' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Sum' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Functor__Sum_fmap {inst_f} {inst_g} `{GHC.Base.Functor inst_f}
  `{GHC.Base.Functor inst_g}
   : forall {a} {b}, (a -> b) -> (Sum inst_f inst_g) a -> (Sum inst_f inst_g) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, InL x => InL (GHC.Base.fmap f x)
      | f, InR y => InR (GHC.Base.fmap f y)
      end.

Local Definition Functor__Sum_op_zlzd__ {inst_f} {inst_g} `{GHC.Base.Functor
  inst_f} `{GHC.Base.Functor inst_g}
   : forall {a} {b}, a -> (Sum inst_f inst_g) b -> (Sum inst_f inst_g) a :=
  fun {a} {b} => fun x => Functor__Sum_fmap (GHC.Base.const x).

Program Instance Functor__Sum {f} {g} `{GHC.Base.Functor f} `{GHC.Base.Functor
  g}
   : GHC.Base.Functor (Sum f g) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Sum_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Sum_fmap |}.

Local Definition Foldable__Sum_foldMap {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Sum inst_f inst_g) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, InL x => Data.Foldable.foldMap f x
      | f, InR y => Data.Foldable.foldMap f y
      end.

Local Definition Foldable__Sum_foldl {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Sum inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Monoid.appEndo (Data.Monoid.getDual (Foldable__Sum_foldMap
                                                    (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                (Coq.Program.Basics.compose
                                                                                 Data.Monoid.Mk_Endo (GHC.Base.flip f)))
                                                    t)) z
      end.

Local Definition Foldable__Sum_foldr' {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Sum inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Sum_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Sum_foldr {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Sum inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Monoid.appEndo (Foldable__Sum_foldMap (Data.Foldable.hash_compose
                                                      Data.Monoid.Mk_Endo f) t) z
      end.

Local Definition Foldable__Sum_foldl' {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Sum inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Sum_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Sum_length {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Sum inst_f inst_g) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Sum_foldl' (fun arg_64__ arg_65__ =>
                            match arg_64__, arg_65__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

Local Definition Foldable__Sum_null {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Sum inst_f inst_g) a -> bool :=
  fun {a} => Foldable__Sum_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Sum_toList {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Sum inst_f inst_g) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Sum_foldr c n t
                        end).

Local Definition Foldable__Sum_product {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Sum inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Sum_foldMap
                                Data.Monoid.Mk_Product).

Local Definition Foldable__Sum_sum {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Sum inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Sum_foldMap
                                Data.Monoid.Mk_Sum).

Local Definition Foldable__Sum_fold {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Sum inst_f inst_g) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Sum_foldMap GHC.Base.id.

Local Definition Foldable__Sum_elem {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> (Sum inst_f inst_g) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Sum_foldMap
                                                              (Coq.Program.Basics.compose Data.Monoid.Mk_Any p)))
                               _GHC.Base.==_.

Program Instance Foldable__Sum {f} {g} `{Data.Foldable.Foldable f}
  `{Data.Foldable.Foldable g}
   : Data.Foldable.Foldable (Sum f g) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Sum_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Sum_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Sum_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Sum_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Sum_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Sum_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Sum_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Sum_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Sum_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Sum_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Sum_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Sum_toList |}.

Local Definition Traversable__Sum_traverse {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Sum inst_f inst_g) a -> f ((Sum inst_f inst_g) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, InL x => InL Data.Functor.<$> Data.Traversable.traverse f x
      | f, InR y => InR Data.Functor.<$> Data.Traversable.traverse f y
      end.

Local Definition Traversable__Sum_sequenceA {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (Sum inst_f inst_g) (f a) -> f ((Sum inst_f inst_g) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Sum_traverse GHC.Base.id.

Local Definition Traversable__Sum_sequence {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (Sum inst_f inst_g) (m a) -> m ((Sum inst_f inst_g) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Sum_sequenceA.

Local Definition Traversable__Sum_mapM {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Sum inst_f inst_g) a -> m ((Sum inst_f inst_g) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Sum_traverse.

Program Instance Traversable__Sum {f} {g} `{Data.Traversable.Traversable f}
  `{Data.Traversable.Traversable g}
   : Data.Traversable.Traversable (Sum f g) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Sum_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Sum_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Sum_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Sum_traverse |}.

(* Translating `instance Generic1__Sum__5' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic1" unsupported *)

(* Translating `instance Generic__Sum' failed: OOPS! Cannot find information for
   class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__Sum' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Unbound variables:
     Gt Lt bool comparison false list negb true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.hash_compose
     Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1 Data.Functor.Classes.Ord1
     Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftEq Data.Monoid.Mk_Any
     Data.Monoid.Mk_Dual Data.Monoid.Mk_Endo Data.Monoid.Mk_Product
     Data.Monoid.Mk_Sum Data.Monoid.appEndo Data.Monoid.getAny Data.Monoid.getDual
     Data.Monoid.getProduct Data.Monoid.getSum Data.Traversable.Traversable
     Data.Traversable.traverse GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.build GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.id GHC.Base.op_zdzn__ GHC.Base.op_zeze__
     GHC.Base.op_zsze__ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
