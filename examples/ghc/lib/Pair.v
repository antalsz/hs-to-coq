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
Require Data.Monoid.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Pair a : Type := Mk_Pair : a -> a -> Pair a.

Arguments Mk_Pair {_} _ _.

Definition pFst {a} (arg_0__ : Pair a) :=
  match arg_0__ with
    | Mk_Pair pFst _ => pFst
  end.

Definition pSnd {a} (arg_1__ : Pair a) :=
  match arg_1__ with
    | Mk_Pair _ pSnd => pSnd
  end.
(* Converted value declarations: *)

Local Definition Functor__Pair_fmap : forall {a} {b},
                                        (a -> b) -> Pair a -> Pair b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_Pair x y => Mk_Pair (f x) (f y)
      end.

Local Definition Functor__Pair_op_zlzd__ : forall {a} {b},
                                             a -> Pair b -> Pair a :=
  fun {a} {b} => fun x => Functor__Pair_fmap (GHC.Base.const x).

Program Instance Functor__Pair : GHC.Base.Functor Pair := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Pair_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Pair_fmap |}.

Local Definition Applicative__Pair_op_zlztzg__ : forall {a} {b},
                                                   Pair (a -> b) -> Pair a -> Pair b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | Mk_Pair f g , Mk_Pair x y => Mk_Pair (f x) (g y)
      end.

Local Definition Applicative__Pair_op_ztzg__ : forall {a} {b},
                                                 Pair a -> Pair b -> Pair b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Pair_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition Applicative__Pair_pure : forall {a}, a -> Pair a :=
  fun {a} => fun x => Mk_Pair x x.

Program Instance Applicative__Pair : GHC.Base.Applicative Pair := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Pair_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Pair_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__Pair_pure |}.

Local Definition Foldable__Pair_foldMap : forall {m} {a},
                                            forall `{GHC.Base.Monoid m}, (a -> m) -> Pair a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_Pair x y => GHC.Base.mappend (f x) (f y)
      end.

Local Definition Foldable__Pair_foldl : forall {b} {a},
                                          (b -> a -> b) -> b -> Pair a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => Data.Monoid.appEndo (Data.Monoid.getDual (Foldable__Pair_foldMap
                                                                (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                            (Coq.Program.Basics.compose
                                                                                            Data.Monoid.Mk_Endo
                                                                                            (GHC.Base.flip f))) t)) z
      end.

Local Definition Foldable__Pair_foldr' : forall {a} {b},
                                           (a -> b -> b) -> b -> Pair a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Pair_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Pair_foldr : forall {a} {b},
                                          (a -> b -> b) -> b -> Pair a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__ , arg_5__ , arg_6__ with
        | f , z , t => Data.Monoid.appEndo (Foldable__Pair_foldMap
                                           (Data.Foldable.hash_compose Data.Monoid.Mk_Endo f) t) z
      end.

Local Definition Foldable__Pair_foldl' : forall {b} {a},
                                           (b -> a -> b) -> b -> Pair a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Pair_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Pair_length : forall {a}, Pair a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Pair_foldl' (fun arg_64__ arg_65__ =>
                            match arg_64__ , arg_65__ with
                              | c , _ => _GHC.Num.+_ c (GHC.Num.fromInteger 1)
                            end) (GHC.Num.fromInteger 0).

Local Definition Foldable__Pair_null : forall {a}, Pair a -> bool :=
  fun {a} => Foldable__Pair_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Pair_toList : forall {a}, Pair a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Pair_foldr c n t
                                end)
      end.

Local Definition Foldable__Pair_product : forall {a},
                                            forall `{GHC.Num.Num a}, Pair a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Pair_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Pair_sum : forall {a},
                                        forall `{GHC.Num.Num a}, Pair a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Pair_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Pair_fold : forall {m},
                                         forall `{GHC.Base.Monoid m}, Pair m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Pair_foldMap GHC.Base.id.

Local Definition Foldable__Pair_elem : forall {a},
                                         forall `{GHC.Base.Eq_ a}, a -> Pair a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Pair_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Program Instance Foldable__Pair : Data.Foldable.Foldable Pair := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Pair_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Pair_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Pair_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Pair_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Pair_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Pair_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Pair_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Pair_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Pair_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Pair_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Pair_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Pair_toList |}.

Local Definition Traversable__Pair_traverse : forall {f} {a} {b},
                                                forall `{GHC.Base.Applicative f}, (a -> f b) -> Pair a -> f (Pair b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_Pair x y => (Mk_Pair Data.Functor.<$> f x) GHC.Base.<*> f y
      end.

Local Definition Traversable__Pair_sequenceA : forall {f} {a},
                                                 forall `{GHC.Base.Applicative f}, Pair (f a) -> f (Pair a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Pair_traverse GHC.Base.id.

Local Definition Traversable__Pair_sequence : forall {m} {a},
                                                forall `{GHC.Base.Monad m}, Pair (m a) -> m (Pair a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Pair_sequenceA.

Local Definition Traversable__Pair_mapM : forall {m} {a} {b},
                                            forall `{GHC.Base.Monad m}, (a -> m b) -> Pair a -> m (Pair b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Pair_traverse.

Program Instance Traversable__Pair : Data.Traversable.Traversable Pair := fun _
                                                                              k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Pair_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Pair_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Pair_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Pair_traverse |}.

Local Definition Monoid__Pair_mappend {inst_a} `{GHC.Base.Monoid inst_a} : (Pair
                                                                           inst_a) -> (Pair inst_a) -> (Pair inst_a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_Pair a1 b1 , Mk_Pair a2 b2 => Mk_Pair (GHC.Base.mappend a1 a2)
                                         (GHC.Base.mappend b1 b2)
    end.

Local Definition Monoid__Pair_mempty {inst_a} `{GHC.Base.Monoid inst_a} : (Pair
                                                                          inst_a) :=
  Mk_Pair GHC.Base.mempty GHC.Base.mempty.

Local Definition Monoid__Pair_mconcat {inst_a} `{GHC.Base.Monoid inst_a} : list
                                                                           (Pair inst_a) -> (Pair inst_a) :=
  GHC.Base.foldr Monoid__Pair_mappend Monoid__Pair_mempty.

Program Instance Monoid__Pair {a} `{GHC.Base.Monoid a} : GHC.Base.Monoid (Pair
                                                                         a) := fun _ k =>
    k {|GHC.Base.mappend__ := Monoid__Pair_mappend ;
      GHC.Base.mconcat__ := Monoid__Pair_mconcat ;
      GHC.Base.mempty__ := Monoid__Pair_mempty |}.

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (Pair.Pair a)' failed: OOPS! Cannot find information for
   class Qualified "Outputable" "Outputable" unsupported *)

Definition pLiftFst {a} : (a -> a) -> Pair a -> Pair a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , Mk_Pair a b => Mk_Pair (f a) b
    end.

Definition pLiftSnd {a} : (a -> a) -> Pair a -> Pair a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , Mk_Pair a b => Mk_Pair a (f b)
    end.

Definition swap {a} : Pair a -> Pair a :=
  fun arg_0__ => match arg_0__ with | Mk_Pair x y => Mk_Pair y x end.

Definition toPair {a} : (a * a)%type -> Pair a :=
  fun arg_0__ => match arg_0__ with | pair x y => Mk_Pair x y end.

Definition unPair {a} : Pair a -> (a * a)%type :=
  fun arg_0__ => match arg_0__ with | Mk_Pair x y => pair x y end.

(* Unbound variables:
     bool false list op_zt__ pair true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.hash_compose Data.Functor.op_zlzdzg__
     Data.Monoid.Mk_Any Data.Monoid.Mk_Dual Data.Monoid.Mk_Endo
     Data.Monoid.Mk_Product Data.Monoid.Mk_Sum Data.Monoid.appEndo Data.Monoid.getAny
     Data.Monoid.getDual Data.Monoid.getProduct Data.Monoid.getSum
     Data.Traversable.Traversable GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.build GHC.Base.const GHC.Base.flip
     GHC.Base.fmap GHC.Base.foldr GHC.Base.id GHC.Base.mappend GHC.Base.mempty
     GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zlztzg__ GHC.Num.Int
     GHC.Num.Num GHC.Num.op_zp__
*)
