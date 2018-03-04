(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)



(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.
Require Data.Monoid.
Require Data.OldList.
Require Data.Ord.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive NonEmpty a : Type := NEcons : a -> list a -> NonEmpty a.

Arguments NEcons {_} _ _.
(* Midamble *)

Definition NonEmpty_foldr1 {a} (f : a -> a -> a) (x: NonEmpty a) : a :=
  match x with 
    | NEcons a as_ => List.fold_right f a as_
  end.

Definition NonEmpty_maximum {a} `{GHC.Base.Ord a} (x:NonEmpty a) : a :=
  NonEmpty_foldr1 GHC.Base.max x.

Definition NonEmpty_minimum {a} `{GHC.Base.Ord a} (x:NonEmpty a) : a :=
  NonEmpty_foldr1 GHC.Base.min x.

Definition toList {a} : NonEmpty a -> list a :=
  fun arg_0__ => match arg_0__ with | NEcons a as_ => cons a as_ end.


Definition List_size {a} : list a -> nat :=
List.fold_right (fun x y => S y) O .
Definition NonEmpty_size {a} : NonEmpty a -> nat :=
  fun arg_0__ =>
    match arg_0__ with
      | NEcons _ xs => 1 + List_size xs
    end.

Program Fixpoint insertBy {a} (cmp: a -> a -> comparison) (x : a)
        (xs : NonEmpty a) {measure (NonEmpty_size xs)} : NonEmpty a :=
  match xs with
  | NEcons x nil => NEcons x nil
  | (NEcons y ((cons y1 ys') as ys)) => 
    match cmp x y with
    | Gt  => NEcons y (toList (insertBy cmp x (NEcons y1 ys')))
    | _   => NEcons x ys
    end
  end.

Program Fixpoint insertBy' {a} (cmp: a -> a -> comparison) (x : a)
        (xs : list a) {measure (List_size xs)} : NonEmpty a :=
  match xs with
  | nil => NEcons x nil
  | cons x nil => NEcons x nil
  | (cons y ((cons y1 ys') as ys)) => 
    match cmp x y with
    | Gt  => NEcons y (toList (insertBy' cmp x (cons y1 ys')))
    | _   => NEcons x ys
    end
  end.


Definition insert {a} `{GHC.Base.Ord a} : a ->  NonEmpty a -> NonEmpty a :=
  insertBy GHC.Base.compare.

Definition sortBy {a} : (a -> a -> comparison) -> NonEmpty a -> NonEmpty a :=
  fun f ne => match ne with
           | NEcons x xs => insertBy' f x (Data.OldList.sortBy f xs)
           end.

Definition sort {a} `{GHC.Base.Ord a} : NonEmpty a -> NonEmpty a :=
             sortBy GHC.Base.compare.



(* Converted value declarations: *)

(* Translating `instance forall {a}, GHC.Exts.IsList
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Exts" "IsList" unsupported *)

(* Translating `instance Control.Monad.Fix.MonadFix Data.List.NonEmpty.NonEmpty'
   failed: OOPS! Cannot find information for class Qualified "Control.Monad.Fix"
   "MonadFix" unsupported *)

(* Translating `instance Control.Monad.Zip.MonadZip Data.List.NonEmpty.NonEmpty'
   failed: OOPS! Cannot find information for class Qualified "Control.Monad.Zip"
   "MonadZip" unsupported *)

Local Definition Functor__NonEmpty_fmap
   : forall {a} {b}, (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, NEcons a as_ => NEcons (f a) (GHC.Base.fmap f as_)
      end.

Local Definition Functor__NonEmpty_op_zlzd__
   : forall {a} {b}, a -> NonEmpty b -> NonEmpty a :=
  fun {a} {b} f x => let 'NEcons a as_ := x in NEcons f (_GHC.Base.<$_ f as_).

Program Instance Functor__NonEmpty : GHC.Base.Functor NonEmpty :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__NonEmpty_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__NonEmpty_fmap |}.
Admit Obligations.

Local Definition Applicative__NonEmpty_pure : forall {a}, a -> NonEmpty a :=
  fun {a} => fun a => NEcons a nil.

Local Definition Traversable__NonEmpty_traverse
   : forall {f} {a} {b} {H : GHC.Base.Functor f} {_ : GHC.Base.Applicative f},
     (a -> f b) -> NonEmpty a -> f (NonEmpty b) :=
  fun {f} {a} {b} {_} {_} =>
    fun arg_144__ arg_145__ =>
      match arg_144__, arg_145__ with
      | f, NEcons a as_ =>
          _GHC.Base.<*>_ (_Data.Functor.<$>_ NEcons (f a)) (Data.Traversable.traverse f
                                                                                      as_)
      end.

Local Definition Traversable__NonEmpty_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, NonEmpty (f a) -> f (NonEmpty a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__NonEmpty_traverse GHC.Base.id.

Local Definition Traversable__NonEmpty_sequence
   : forall {m} {a},
     forall `{GHC.Base.Monad m}, NonEmpty (m a) -> m (NonEmpty a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__NonEmpty_sequenceA.

Local Definition Traversable__NonEmpty_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> NonEmpty a -> m (NonEmpty b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__NonEmpty_traverse.

Local Definition Foldable__NonEmpty_fold
   : forall {m} {_ : GHC.Base.Monoid m}, NonEmpty m -> m :=
  fun {m} {_} =>
    fun arg_141__ =>
      let 'NEcons m ms := arg_141__ in
      GHC.Base.mappend m (Data.Foldable.fold ms).

Local Definition Foldable__NonEmpty_foldMap
   : forall {m} {a} {_ : GHC.Base.Monoid m}, (a -> m) -> NonEmpty a -> m :=
  fun {m} {a} {_} =>
    fun f arg_141__ =>
      let 'NEcons m ms := arg_141__ in
      GHC.Base.mappend (f m) (Data.Foldable.foldMap f ms).

Local Definition Foldable__NonEmpty_product
   : forall {a}, forall `{GHC.Num.Num a}, NonEmpty a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__NonEmpty_foldMap
                                Data.Monoid.Mk_Product).

Local Definition Foldable__NonEmpty_sum
   : forall {a}, forall `{GHC.Num.Num a}, NonEmpty a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__NonEmpty_foldMap
                                Data.Monoid.Mk_Sum).

Local Definition Foldable__NonEmpty_elem
   : forall {a}, forall `{_ : GHC.Base.Eq_ a}, a -> NonEmpty a -> bool :=
  fun {a} `{_ : GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun p =>
                                  Data.Foldable.hash_compose Data.Monoid.getAny (Foldable__NonEmpty_foldMap
                                                              (Data.Foldable.hash_compose Data.Monoid.Mk_Any p)))
                               _GHC.Base.==_.

Local Definition Foldable__NonEmpty_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> NonEmpty a -> b :=
  fun {b} {a} =>
    fun arg_128__ arg_129__ arg_130__ =>
      match arg_128__, arg_129__, arg_130__ with
      | f, z, NEcons a as_ => Data.Foldable.foldl f (f z a) as_
      end.

Local Definition Foldable__NonEmpty_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> NonEmpty a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => _GHC.Base.$!_ k (f x z)
              end in
          Foldable__NonEmpty_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__NonEmpty_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> NonEmpty a -> b :=
  fun {a} {b} =>
    fun arg_128__ arg_129__ arg_130__ =>
      match arg_128__, arg_129__, arg_130__ with
      | f, z, NEcons a as_ => f a (Data.Foldable.foldr f z as_)
      end.

Local Definition Foldable__NonEmpty_null : forall {a}, NonEmpty a -> bool :=
  fun {a} => Foldable__NonEmpty_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__NonEmpty_toList : forall {a}, NonEmpty a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__NonEmpty_foldr c n t
                        end).

Local Definition Monad__NonEmpty_op_zgzgze__
   : forall {a} {b}, NonEmpty a -> (a -> NonEmpty b) -> NonEmpty b :=
  fun {a} {b} =>
    fun arg_148__ arg_149__ =>
      match arg_148__, arg_149__ with
      | NEcons a as_, f =>
          let 'NEcons b bs := f a in
          NEcons b (Coq.Init.Datatypes.app bs (_GHC.Base.>>=_ as_ (_GHC.Base.∘_
                                                               Foldable__NonEmpty_toList f)))
      end.

Local Definition Foldable__NonEmpty_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> NonEmpty a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => _GHC.Base.$!_ k (f z x)
              end in
          Foldable__NonEmpty_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__NonEmpty_length
   : forall {a}, NonEmpty a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__NonEmpty_foldl' (fun arg_64__ arg_65__ =>
                                 match arg_64__, arg_65__ with
                                 | c, _ => _GHC.Num.+_ c #1
                                 end) #0.

Program Instance Foldable__NonEmpty : Data.Foldable.Foldable NonEmpty :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__NonEmpty_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__NonEmpty_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__NonEmpty_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__NonEmpty_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__NonEmpty_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__NonEmpty_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__NonEmpty_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__NonEmpty_length ;
         Data.Foldable.null__ := fun {a} => Foldable__NonEmpty_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__NonEmpty_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__NonEmpty_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__NonEmpty_toList |}.
Admit Obligations.

Program Instance Traversable__NonEmpty
   : Data.Traversable.Traversable NonEmpty :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__NonEmpty_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__NonEmpty_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__NonEmpty_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__NonEmpty_traverse |}.
Admit Obligations.

(* Translating `instance GHC.Generics.Generic1 Data.List.NonEmpty.NonEmpty'
   failed: OOPS! Cannot find information for class Qualified "GHC.Generics"
   "Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

(* Skipping instance Ord__NonEmpty *)

Local Definition Eq___NonEmpty_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : NonEmpty inst_a -> NonEmpty inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NEcons a1 a2, NEcons b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___NonEmpty_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : NonEmpty inst_a -> NonEmpty inst_a -> bool :=
  fun a b => negb (Eq___NonEmpty_op_zeze__ a b).

Program Instance Eq___NonEmpty {a} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (NonEmpty a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___NonEmpty_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___NonEmpty_op_zsze__ |}.
Admit Obligations.

Definition drop {a} : GHC.Num.Int -> NonEmpty a -> list a :=
  fun n => GHC.List.drop n GHC.Base.∘ toList.

Definition dropWhile {a} : (a -> bool) -> NonEmpty a -> list a :=
  fun p => GHC.List.dropWhile p GHC.Base.∘ toList.

Definition filter {a} : (a -> bool) -> NonEmpty a -> list a :=
  fun p => GHC.List.filter p GHC.Base.∘ toList.

Definition head {a} : NonEmpty a -> a :=
  fun arg_0__ => let 'NEcons a _ := arg_0__ in a.

Definition isPrefixOf {a} `{GHC.Base.Eq_ a} : list a -> NonEmpty a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, _ => true
    | cons y ys, NEcons x xs =>
        andb (y GHC.Base.== x) (Data.OldList.isPrefixOf ys xs)
    end.

Definition length {a} : NonEmpty a -> GHC.Num.Int :=
  fun arg_0__ =>
    let 'NEcons _ xs := arg_0__ in
    #1 GHC.Num.+ Data.Foldable.length xs.

Definition map {a} {b} : (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, NEcons a as_ => NEcons (f a) (GHC.Base.fmap f as_)
    end.

Definition nonEmpty {a} : list a -> option (NonEmpty a) :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => None
    | cons a as_ => Some (NEcons a as_)
    end.

Definition uncons {a} : NonEmpty a -> (a * option (NonEmpty a))%type :=
  fun arg_0__ => let 'NEcons a as_ := arg_0__ in pair a (nonEmpty as_).

Definition nubBy {a} : (a -> a -> bool) -> NonEmpty a -> NonEmpty a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | eq, NEcons a as_ =>
        NEcons a (Data.OldList.nubBy eq (GHC.List.filter (fun b => negb (eq a b)) as_))
    end.

Definition nub {a} `{GHC.Base.Eq_ a} : NonEmpty a -> NonEmpty a :=
  nubBy _GHC.Base.==_.

Definition op_zlzb__ {a} : a -> NonEmpty a -> NonEmpty a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, NEcons b bs => NEcons a (cons b bs)
    end.

Notation "'_<|_'" := (op_zlzb__).

Infix "<|" := (_<|_) (at level 99).

Definition cons_ {a} : a -> NonEmpty a -> NonEmpty a :=
  _<|_.

Definition partition {a}
   : (a -> bool) -> NonEmpty a -> (list a * list a)%type :=
  fun p => Data.OldList.partition p GHC.Base.∘ toList.

Definition some1 {f} {a} `{GHC.Base.Alternative f} : f a -> f (NonEmpty a) :=
  fun x => (NEcons Data.Functor.<$> x) GHC.Base.<*> GHC.Base.many x.

Definition sortWith {o} {a} `{GHC.Base.Ord o}
   : (a -> o) -> NonEmpty a -> NonEmpty a :=
  sortBy GHC.Base.∘ Data.Ord.comparing.

Definition span {a} : (a -> bool) -> NonEmpty a -> (list a * list a)%type :=
  fun p => GHC.List.span p GHC.Base.∘ toList.

Definition break {a} : (a -> bool) -> NonEmpty a -> (list a * list a)%type :=
  fun p => span (negb GHC.Base.∘ p).

Definition splitAt {a} : GHC.Num.Int -> NonEmpty a -> (list a * list a)%type :=
  fun n => GHC.List.splitAt n GHC.Base.∘ toList.

Definition tail {a} : NonEmpty a -> list a :=
  fun arg_0__ => let 'NEcons _ as_ := arg_0__ in as_.

Definition take {a} : GHC.Num.Int -> NonEmpty a -> list a :=
  fun n => GHC.List.take n GHC.Base.∘ toList.

Definition takeWhile {a} : (a -> bool) -> NonEmpty a -> list a :=
  fun p => GHC.List.takeWhile p GHC.Base.∘ toList.

Definition unzip {f} {a} {b} `{GHC.Base.Functor f}
   : f (a * b)%type -> (f a * f b)%type :=
  fun xs =>
    pair (Data.Tuple.fst Data.Functor.<$> xs) (Data.Tuple.snd Data.Functor.<$> xs).

Definition xor : NonEmpty bool -> bool :=
  fun arg_0__ =>
    let 'NEcons x xs := arg_0__ in
    let xor' :=
      fun arg_1__ arg_2__ =>
        match arg_1__, arg_2__ with
        | true, y => negb y
        | false, y => y
        end in
    Data.Foldable.foldr xor' x xs.

Definition zip {a} {b} : NonEmpty a -> NonEmpty b -> NonEmpty (a * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NEcons x xs, NEcons y ys => NEcons (pair x y) (GHC.List.zip xs ys)
    end.

Definition zipWith {a} {b} {c}
   : (a -> b -> c) -> NonEmpty a -> NonEmpty b -> NonEmpty c :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, NEcons x xs, NEcons y ys => NEcons (f x y) (GHC.List.zipWith f xs ys)
    end.

Local Definition Applicative__NonEmpty_op_zlztzg__
   : forall {a} {b}, NonEmpty (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun {a} {b} => zipWith id.

Local Definition Applicative__NonEmpty_op_ztzg__
   : forall {a} {b}, NonEmpty a -> NonEmpty b -> NonEmpty b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__NonEmpty_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x)
                                        y.

Program Instance Applicative__NonEmpty : GHC.Base.Applicative NonEmpty :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__NonEmpty_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__NonEmpty_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__NonEmpty_pure |}.
Admit Obligations.

Local Definition Monad__NonEmpty_op_zgzg__
   : forall {a} {b}, NonEmpty a -> NonEmpty b -> NonEmpty b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__NonEmpty_return_ : forall {a}, a -> NonEmpty a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__NonEmpty : GHC.Base.Monad NonEmpty :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__NonEmpty_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__NonEmpty_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__NonEmpty_return_ |}.
Admit Obligations.

Module Notations.
Notation "'_Data.List.NonEmpty.<|_'" := (op_zlzb__).
Infix "Data.List.NonEmpty.<|" := (_<|_) (at level 99).
End Notations.

(* Unbound variables:
     None Some andb bool cons false id list negb nil op_zt__ option pair sortBy
     toList true Coq.Init.Datatypes.app Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.fold Data.Foldable.foldMap
     Data.Foldable.foldl Data.Foldable.foldr Data.Foldable.hash_compose
     Data.Foldable.length Data.Functor.op_zlzdzg__ Data.Monoid.Mk_Any
     Data.Monoid.Mk_Product Data.Monoid.Mk_Sum Data.Monoid.getAny
     Data.Monoid.getProduct Data.Monoid.getSum Data.OldList.isPrefixOf
     Data.OldList.nubBy Data.OldList.partition Data.Ord.comparing
     Data.Traversable.Traversable Data.Traversable.traverse Data.Tuple.fst
     Data.Tuple.snd GHC.Base.Alternative GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.build
     GHC.Base.const GHC.Base.fmap GHC.Base.id GHC.Base.many GHC.Base.mappend
     GHC.Base.op_z2218U__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zgzgze__
     GHC.Base.op_zlzd__ GHC.Base.op_zlztzg__ GHC.Base.op_ztzg__ GHC.Base.pure
     GHC.List.drop GHC.List.dropWhile GHC.List.filter GHC.List.span GHC.List.splitAt
     GHC.List.take GHC.List.takeWhile GHC.List.zip GHC.List.zipWith GHC.Num.Int
     GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
