(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)

Open Scope type_scope.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.
Require Data.OldList.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.

(* Converted type declarations: *)

Inductive NonEmpty a : Type := NEcons : a -> list a -> NonEmpty a.

Arguments NEcons {_} _ _.
(* Converted value declarations: *)

(* Translating `instance forall {a}, GHC.Exts.IsList (NonEmpty a)' failed: OOPS!
   Cannot find information for class "GHC.Exts.IsList" unsupported *)

(* Translating `instance Control.Monad.Fix.MonadFix NonEmpty' failed: OOPS!
   Cannot find information for class "Control.Monad.Fix.MonadFix" unsupported *)

(* Translating `instance Control.Monad.Zip.MonadZip NonEmpty' failed: OOPS!
   Cannot find information for class "Control.Monad.Zip.MonadZip" unsupported *)

Local Definition instance_GHC_Base_Functor_NonEmpty_fmap : forall {a} {b},
                                                             (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun {a} {b} =>
    fun arg_184__ arg_185__ =>
      match arg_184__ , arg_185__ with
        | f , NEcons a as_ => NEcons (f a) (GHC.Base.fmap f as_)
      end.

Local Definition instance_GHC_Base_Functor_NonEmpty_op_zlzd__ : forall {a} {b},
                                                                  a -> NonEmpty b -> NonEmpty a :=
  fun {a} {b} =>
    fun arg_188__ arg_189__ =>
      match arg_188__ , arg_189__ with
        | b , NEcons _ as_ => NEcons b (GHC.Base.op_zlzd__ b as_)
      end.

Instance instance_GHC_Base_Functor_NonEmpty : GHC.Base.Functor NonEmpty := fun _
                                                                               k =>
    k (GHC.Base.Functor__Dict_Build NonEmpty (fun {a} {b} =>
                                      instance_GHC_Base_Functor_NonEmpty_op_zlzd__) (fun {a} {b} =>
                                      instance_GHC_Base_Functor_NonEmpty_fmap)).

Local Definition instance_GHC_Base_Applicative_NonEmpty_pure : forall {a},
                                                                 a -> NonEmpty a :=
  fun {a} => fun arg_181__ => match arg_181__ with | a => NEcons a nil end.

Local Definition instance_Data_Traversable_Traversable_NonEmpty_traverse
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f}, (a -> f b) -> NonEmpty a -> f (NonEmpty b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_171__ arg_172__ =>
      match arg_171__ , arg_172__ with
        | f , NEcons a as_ => GHC.Base.op_zlztzg__ (Data.Functor.op_zlzdzg__ NEcons (f
                                                                             a)) (Data.Traversable.traverse f as_)
      end.

Local Definition instance_Data_Traversable_Traversable_NonEmpty_sequenceA
    : forall {f} {a},
        forall `{GHC.Base.Applicative f}, NonEmpty (f a) -> f (NonEmpty a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable_NonEmpty_traverse GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable_NonEmpty_sequence
    : forall {m} {a},
        forall `{GHC.Base.Monad m}, NonEmpty (m a) -> m (NonEmpty a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_NonEmpty_sequenceA.

Local Definition instance_Data_Traversable_Traversable_NonEmpty_mapM
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m}, (a -> m b) -> NonEmpty a -> m (NonEmpty b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_NonEmpty_traverse.

Instance instance_Data_Traversable_Traversable_NonEmpty
  : Data.Traversable.Traversable NonEmpty := fun _ k =>
    k (Data.Traversable.Traversable__Dict_Build NonEmpty (fun {m}
                                                              {a}
                                                              {b}
                                                              `{GHC.Base.Monad m} =>
                                                  instance_Data_Traversable_Traversable_NonEmpty_mapM) (fun {m}
                                                                                                            {a}
                                                                                                            `{GHC.Base.Monad
                                                                                                            m} =>
                                                  instance_Data_Traversable_Traversable_NonEmpty_sequence) (fun {f}
                                                                                                                {a}
                                                                                                                `{GHC.Base.Applicative
                                                                                                                f} =>
                                                  instance_Data_Traversable_Traversable_NonEmpty_sequenceA) (fun {f}
                                                                                                                 {a}
                                                                                                                 {b}
                                                                                                                 `{GHC.Base.Applicative
                                                                                                                 f} =>
                                                  instance_Data_Traversable_Traversable_NonEmpty_traverse)).

(* Translating `instance Data.Foldable.Foldable NonEmpty' failed: Cannot find
   sig for "foldr1" unsupported *)

(* Translating `instance GHC.Generics.Generic1 NonEmpty' failed: OOPS! Cannot
   find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (NonEmpty a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (NonEmpty a)' failed: OOPS! Cannot find information for class "Data.Data.Data"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (NonEmpty a)' failed: OOPS! Cannot find information for class "GHC.Read.Read"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (NonEmpty a)' failed: OOPS! Cannot find information for class "GHC.Show.Show"
   unsupported *)

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__compare {inst_a}
                                                                                      `{GHC.Base.Ord inst_a} : NonEmpty
                                                                                                               inst_a -> NonEmpty
                                                                                                               inst_a -> comparison :=
  fun arg_116__ arg_117__ =>
    match arg_116__ , arg_117__ with
      | a , b => match a with
                   | NEcons a1 a2 => match b with
                                       | NEcons b1 b2 => let scrut_118__ := (GHC.Base.compare a1 b1) in
                                                         match scrut_118__ with
                                                           | Lt => Lt
                                                           | Eq => (GHC.Base.compare a2 b2)
                                                           | Gt => Gt
                                                         end
                                     end
                 end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zg__ {inst_a}
                                                                                      `{GHC.Base.Ord inst_a} : NonEmpty
                                                                                                               inst_a -> NonEmpty
                                                                                                               inst_a -> bool :=
  fun arg_160__ arg_161__ =>
    match arg_160__ , arg_161__ with
      | a , b => match a with
                   | NEcons a1 a2 => match b with
                                       | NEcons b1 b2 => let scrut_162__ := (GHC.Base.compare a1 b1) in
                                                         match scrut_162__ with
                                                           | Lt => false
                                                           | Eq => (GHC.Base.op_zg__ a2 b2)
                                                           | Gt => true
                                                         end
                                     end
                 end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zgze__ {inst_a}
                                                                                        `{GHC.Base.Ord inst_a}
    : NonEmpty inst_a -> NonEmpty inst_a -> bool :=
  fun arg_149__ arg_150__ =>
    match arg_149__ , arg_150__ with
      | a , b => match a with
                   | NEcons a1 a2 => match b with
                                       | NEcons b1 b2 => let scrut_151__ := (GHC.Base.compare a1 b1) in
                                                         match scrut_151__ with
                                                           | Lt => false
                                                           | Eq => (GHC.Base.op_zgze__ a2 b2)
                                                           | Gt => true
                                                         end
                                     end
                 end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zl__ {inst_a}
                                                                                      `{GHC.Base.Ord inst_a} : NonEmpty
                                                                                                               inst_a -> NonEmpty
                                                                                                               inst_a -> bool :=
  fun arg_127__ arg_128__ =>
    match arg_127__ , arg_128__ with
      | a , b => match a with
                   | NEcons a1 a2 => match b with
                                       | NEcons b1 b2 => let scrut_129__ := (GHC.Base.compare a1 b1) in
                                                         match scrut_129__ with
                                                           | Lt => true
                                                           | Eq => (GHC.Base.op_zl__ a2 b2)
                                                           | Gt => false
                                                         end
                                     end
                 end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zlze__ {inst_a}
                                                                                        `{GHC.Base.Ord inst_a}
    : NonEmpty inst_a -> NonEmpty inst_a -> bool :=
  fun arg_138__ arg_139__ =>
    match arg_138__ , arg_139__ with
      | a , b => match a with
                   | NEcons a1 a2 => match b with
                                       | NEcons b1 b2 => let scrut_140__ := (GHC.Base.compare a1 b1) in
                                                         match scrut_140__ with
                                                           | Lt => true
                                                           | Eq => (GHC.Base.op_zlze__ a2 b2)
                                                           | Gt => false
                                                         end
                                     end
                 end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__min {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : NonEmpty
                                                                                                           inst_a -> NonEmpty
                                                                                                           inst_a -> NonEmpty
                                                                                                           inst_a :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zlze__ x
                                                                              y : bool
    then x
    else y.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__max {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : NonEmpty
                                                                                                           inst_a -> NonEmpty
                                                                                                           inst_a -> NonEmpty
                                                                                                           inst_a :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zlze__ x
                                                                              y : bool
    then y
    else x.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___NonEmpty_a__op_zeze__ {inst_a}
                                                                                        `{GHC.Base.Eq_ inst_a}
    : NonEmpty inst_a -> NonEmpty inst_a -> bool :=
  fun arg_108__ arg_109__ =>
    match arg_108__ , arg_109__ with
      | NEcons a1 a2 , NEcons b1 b2 => (andb ((GHC.Base.op_zeze__ a1 b1))
                                             ((GHC.Base.op_zeze__ a2 b2)))
    end.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___NonEmpty_a__op_zsze__ {inst_a}
                                                                                        `{_ : GHC.Base.Eq_ inst_a}
    : NonEmpty inst_a -> NonEmpty inst_a -> bool :=
  fun arg_198__ arg_199__ =>
    match arg_198__ , arg_199__ with
      | a , b => negb
                 (instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___NonEmpty_a__op_zeze__ a b)
    end.

Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___NonEmpty_a_ {a}
                                                                      `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (NonEmpty a) :=
  fun _ k =>
    k (GHC.Base.Eq___Dict_Build (NonEmpty a)
                                instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___NonEmpty_a__op_zeze__
                                instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___NonEmpty_a__op_zsze__).

Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a_ {a}
                                                                      `{GHC.Base.Ord a} : GHC.Base.Ord (NonEmpty a) :=
  fun _ k =>
    k (GHC.Base.Ord__Dict_Build (NonEmpty a)
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zl__
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zlze__
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zg__
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__op_zgze__
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__compare
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__max
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__NonEmpty_a__min).

Definition fromList {a} : list a -> NonEmpty a :=
  fun arg_61__ =>
    match arg_61__ with
      | cons a as_ => NEcons a as_
      | nil => GHC.Base.errorWithoutStackTrace (GHC.Base.hs_string__
                                               "NonEmpty.fromList: empty list")
    end.

Definition insert {f} {a} `{Data.Foldable.Foldable f} `{GHC.Base.Ord a} : a -> f
                                                                          a -> NonEmpty a :=
  fun arg_69__ =>
    match arg_69__ with
      | a => Coq.Program.Basics.compose fromList (Coq.Program.Basics.compose
                                        (Data.OldList.insert a) Data.Foldable.toList)
    end.

Definition lift {f} {a} {b} `{Data.Foldable.Foldable f} : (list a -> list
                                                          b) -> f a -> NonEmpty b :=
  fun arg_65__ =>
    match arg_65__ with
      | f => Coq.Program.Basics.compose fromList (Coq.Program.Basics.compose f
                                                                             Data.Foldable.toList)
    end.

Definition scanl {f} {b} {a} `{Data.Foldable.Foldable f}
    : (b -> a -> b) -> b -> f a -> NonEmpty b :=
  fun arg_72__ arg_73__ =>
    match arg_72__ , arg_73__ with
      | f , z => Coq.Program.Basics.compose fromList (Coq.Program.Basics.compose
                                            (GHC.List.scanl f z) Data.Foldable.toList)
    end.

Definition scanl1 {a} : (a -> a -> a) -> NonEmpty a -> NonEmpty a :=
  fun arg_80__ arg_81__ =>
    match arg_80__ , arg_81__ with
      | f , NEcons a as_ => fromList (GHC.List.scanl f a as_)
    end.

Definition scanr {f} {a} {b} `{Data.Foldable.Foldable f}
    : (a -> b -> b) -> b -> f a -> NonEmpty b :=
  fun arg_76__ arg_77__ =>
    match arg_76__ , arg_77__ with
      | f , z => Coq.Program.Basics.compose fromList (Coq.Program.Basics.compose
                                            (GHC.List.scanr f z) Data.Foldable.toList)
    end.

Definition tails {f} {a} `{Data.Foldable.Foldable f} : f a -> NonEmpty (list
                                                                       a) :=
  Coq.Program.Basics.compose fromList (Coq.Program.Basics.compose
                             Data.OldList.tails Data.Foldable.toList).

Definition head {a} : NonEmpty a -> a :=
  fun arg_90__ => match arg_90__ with | NEcons a _ => a end.

Definition isPrefixOf {a} `{GHC.Base.Eq_ a} : list a -> NonEmpty a -> bool :=
  fun arg_20__ arg_21__ =>
    match arg_20__ , arg_21__ with
      | nil , _ => true
      | cons y ys , NEcons x xs => andb (GHC.Base.op_zeze__ y x)
                                        (Data.OldList.isPrefixOf ys xs)
    end.

Definition length {a} : NonEmpty a -> GHC.Num.Int :=
  fun arg_105__ =>
    match arg_105__ with
      | NEcons _ xs => GHC.Num.op_zp__ (GHC.Num.fromInteger 1) (Data.Foldable.length
                                       xs)
    end.

Definition map {a} {b} : (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun arg_27__ arg_28__ =>
    match arg_27__ , arg_28__ with
      | f , NEcons a as_ => NEcons (f a) (GHC.Base.fmap f as_)
    end.

Definition nonEmpty {a} : list a -> option (NonEmpty a) :=
  fun arg_92__ =>
    match arg_92__ with
      | nil => None
      | cons a as_ => Some (NEcons a as_)
    end.

Definition uncons {a} : NonEmpty a -> a * option (NonEmpty a) :=
  fun arg_95__ => match arg_95__ with | NEcons a as_ => pair a (nonEmpty as_) end.

Definition nubBy {a} : (a -> a -> bool) -> NonEmpty a -> NonEmpty a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | eq , NEcons a as_ => NEcons a (Data.OldList.nubBy eq (GHC.List.filter
                                                             (fun arg_2__ =>
                                                               match arg_2__ with
                                                                 | b => negb (eq a b)
                                                               end) as_))
    end.

Definition nub {a} `{GHC.Base.Eq_ a} : NonEmpty a -> NonEmpty a :=
  nubBy GHC.Base.op_zeze__.

Definition op_zlzb__ {a} : a -> NonEmpty a -> NonEmpty a :=
  fun arg_84__ arg_85__ =>
    match arg_84__ , arg_85__ with
      | a , NEcons b bs => NEcons a (cons b bs)
    end.

Infix "<|" := (op_zlzb__) (at level 99).

Notation "'_<|_'" := (op_zlzb__).

Definition cons_ {a} : a -> NonEmpty a -> NonEmpty a :=
  op_zlzb__.

Definition some1 {f} {a} `{GHC.Base.Alternative f} : f a -> f (NonEmpty a) :=
  fun arg_24__ =>
    match arg_24__ with
      | x => GHC.Base.op_zlztzg__ (Data.Functor.op_zlzdzg__ NEcons x) (GHC.Base.many
                                  x)
    end.

Definition tail {a} : NonEmpty a -> list a :=
  fun arg_88__ => match arg_88__ with | NEcons _ as_ => as_ end.

Definition toList {a} : NonEmpty a -> list a :=
  fun arg_31__ => match arg_31__ with | NEcons a as_ => cons a as_ end.

Definition takeWhile {a} : (a -> bool) -> NonEmpty a -> list a :=
  fun arg_43__ =>
    match arg_43__ with
      | p => Coq.Program.Basics.compose (GHC.List.takeWhile p) toList
    end.

Definition take {a} : GHC.Num.Int -> NonEmpty a -> list a :=
  fun arg_34__ =>
    match arg_34__ with
      | n => Coq.Program.Basics.compose (GHC.List.take n) toList
    end.

Definition splitAt {a} : GHC.Num.Int -> NonEmpty a -> list a * list a :=
  fun arg_40__ =>
    match arg_40__ with
      | n => Coq.Program.Basics.compose (GHC.List.splitAt n) toList
    end.

Definition span {a} : (a -> bool) -> NonEmpty a -> list a * list a :=
  fun arg_49__ =>
    match arg_49__ with
      | p => Coq.Program.Basics.compose (GHC.List.span p) toList
    end.

Definition break {a} : (a -> bool) -> NonEmpty a -> list a * list a :=
  fun arg_52__ =>
    match arg_52__ with
      | p => span (Coq.Program.Basics.compose negb p)
    end.

Definition partition {a} : (a -> bool) -> NonEmpty a -> list a * list a :=
  fun arg_58__ =>
    match arg_58__ with
      | p => Coq.Program.Basics.compose (Data.OldList.partition p) toList
    end.

Definition filter {a} : (a -> bool) -> NonEmpty a -> list a :=
  fun arg_55__ =>
    match arg_55__ with
      | p => Coq.Program.Basics.compose (GHC.List.filter p) toList
    end.

Definition dropWhile {a} : (a -> bool) -> NonEmpty a -> list a :=
  fun arg_46__ =>
    match arg_46__ with
      | p => Coq.Program.Basics.compose (GHC.List.dropWhile p) toList
    end.

Definition drop {a} : GHC.Num.Int -> NonEmpty a -> list a :=
  fun arg_37__ =>
    match arg_37__ with
      | n => Coq.Program.Basics.compose (GHC.List.drop n) toList
    end.

Local Definition instance_GHC_Base_Monad_NonEmpty_op_zgzgze__ : forall {a} {b},
                                                                  NonEmpty a -> (a -> NonEmpty b) -> NonEmpty b :=
  fun {a} {b} =>
    fun arg_175__ arg_176__ =>
      match arg_175__ , arg_176__ with
        | NEcons a as_ , f => let bs' :=
                                GHC.Base.op_zgzgze__ as_ (Coq.Program.Basics.compose toList f) in
                              match f a with
                                | NEcons b bs => NEcons b (Coq.Init.Datatypes.app bs bs')
                              end
      end.

Definition unzip {f} {a} {b} `{GHC.Base.Functor f} : f (a * b) -> f a * f b :=
  fun arg_8__ =>
    match arg_8__ with
      | xs => pair (Data.Functor.op_zlzdzg__ Data.Tuple.fst xs)
                   (Data.Functor.op_zlzdzg__ Data.Tuple.snd xs)
    end.

Definition xor : NonEmpty bool -> bool :=
  fun arg_98__ =>
    match arg_98__ with
      | NEcons x xs => let xor' :=
                         fun arg_99__ arg_100__ =>
                           match arg_99__ , arg_100__ with
                             | true , y => negb y
                             | false , y => y
                           end in
                       Data.Foldable.foldr xor' x xs
    end.

Definition zip {a} {b} : NonEmpty a -> NonEmpty b -> NonEmpty (a * b) :=
  fun arg_16__ arg_17__ =>
    match arg_16__ , arg_17__ with
      | NEcons x xs , NEcons y ys => NEcons (pair x y) (GHC.List.zip xs ys)
    end.

Definition zipWith {a} {b} {c} : (a -> b -> c) -> NonEmpty a -> NonEmpty
                                 b -> NonEmpty c :=
  fun arg_11__ arg_12__ arg_13__ =>
    match arg_11__ , arg_12__ , arg_13__ with
      | f , NEcons x xs , NEcons y ys => NEcons (f x y) (GHC.List.zipWith f xs ys)
    end.

Local Definition instance_GHC_Base_Applicative_NonEmpty_op_zlztzg__ : forall {a}
                                                                             {b},
                                                                        NonEmpty (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun {a} {b} => zipWith id.

Local Definition instance_GHC_Base_Applicative_NonEmpty_op_ztzg__ : forall {a}
                                                                           {b},
                                                                      NonEmpty a -> NonEmpty b -> NonEmpty b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_NonEmpty_op_zlztzg__ (GHC.Base.fmap
                                                         (GHC.Base.const GHC.Base.id) x) y.

Instance instance_GHC_Base_Applicative_NonEmpty : GHC.Base.Applicative
                                                  NonEmpty := fun _ k =>
    k (GHC.Base.Applicative__Dict_Build NonEmpty (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_NonEmpty_op_ztzg__) (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_NonEmpty_op_zlztzg__) (fun {a} =>
                                          instance_GHC_Base_Applicative_NonEmpty_pure)).

Local Definition instance_GHC_Base_Monad_NonEmpty_op_zgzg__ : forall {a} {b},
                                                                NonEmpty a -> NonEmpty b -> NonEmpty b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Monad_NonEmpty_return_ : forall {a},
                                                              a -> NonEmpty a :=
  fun {a} => GHC.Base.pure.

Instance instance_GHC_Base_Monad_NonEmpty : GHC.Base.Monad NonEmpty := fun _
                                                                           k =>
    k (GHC.Base.Monad__Dict_Build NonEmpty (fun {a} {b} =>
                                    instance_GHC_Base_Monad_NonEmpty_op_zgzg__) (fun {a} {b} =>
                                    instance_GHC_Base_Monad_NonEmpty_op_zgzgze__) (fun {a} =>
                                    instance_GHC_Base_Monad_NonEmpty_return_)).

(* Unbound variables:
     * Coq.Init.Datatypes.app Coq.Program.Basics.compose Data.Foldable.Foldable
     Data.Foldable.foldr Data.Foldable.length Data.Foldable.toList
     Data.Functor.op_zlzdzg__ Data.OldList.insert Data.OldList.isPrefixOf
     Data.OldList.nubBy Data.OldList.partition Data.OldList.tails
     Data.Traversable.Traversable Data.Traversable.Traversable__Dict_Build
     Data.Traversable.traverse Data.Tuple.fst Data.Tuple.snd GHC.Base.Alternative
     GHC.Base.Applicative GHC.Base.Applicative__Dict_Build GHC.Base.Eq_
     GHC.Base.Eq___Dict_Build GHC.Base.Functor GHC.Base.Functor__Dict_Build
     GHC.Base.Monad GHC.Base.Monad__Dict_Build GHC.Base.Ord GHC.Base.Ord__Dict_Build
     GHC.Base.compare GHC.Base.const GHC.Base.errorWithoutStackTrace GHC.Base.fmap
     GHC.Base.id GHC.Base.many GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlzd__ GHC.Base.op_zlze__
     GHC.Base.op_zlztzg__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.List.drop
     GHC.List.dropWhile GHC.List.filter GHC.List.scanl GHC.List.scanr GHC.List.span
     GHC.List.splitAt GHC.List.take GHC.List.takeWhile GHC.List.zip GHC.List.zipWith
     GHC.Num.Int GHC.Num.op_zp__ None Some andb bool comparison cons false id list
     negb nil option pair true
*)
