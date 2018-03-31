(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Signatures.
Require Control.Monad.Trans.Class.
Require Coq.Program.Basics.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Import Data.Functor.Classes.
Require Import Data.Functor.Identity.
Require Import Data.Monoid.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive ExceptT e m a : Type
  := Mk_ExceptT : (m (Data.Either.Either e a)) -> ExceptT e m a.

Definition Except e :=
  (ExceptT e Identity)%type.

Arguments Mk_ExceptT {_} {_} {_} _.
(* Converted value declarations: *)

Local Definition Eq1__ExceptT_liftEq {inst_e} {inst_m} `{GHC.Base.Eq_ inst_e}
  `{Eq1 inst_m}
   : forall {a} {b},
     (a -> b -> bool) ->
     (ExceptT inst_e inst_m) a -> (ExceptT inst_e inst_m) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_ExceptT x, Mk_ExceptT y => (@liftEq inst_m _ _ _ (liftEq eq)) x y
      end.

Program Instance Eq1__ExceptT {e} {m} `{GHC.Base.Eq_ e} `{Eq1 m}
   : Eq1 (ExceptT e m) :=
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__ExceptT_liftEq |}.

Local Definition Ord1__ExceptT_liftCompare {inst_e} {inst_m} `{GHC.Base.Ord
  inst_e} `{Ord1 inst_m}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (ExceptT inst_e inst_m) a -> (ExceptT inst_e inst_m) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_ExceptT x, Mk_ExceptT y =>
          (@liftCompare inst_m _ _ _ _ (liftCompare comp)) x y
      end.

Program Instance Ord1__ExceptT {e} {m} `{GHC.Base.Ord e} `{Ord1 m}
   : Ord1 (ExceptT e m) :=
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__ExceptT_liftCompare |}.

(* Translating `instance Read1__ExceptT' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Show1__ExceptT' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

Local Definition Eq___ExceptT_op_zeze__ {inst_e} {inst_m} {inst_a}
  `{GHC.Base.Eq_ inst_e} `{Eq1 inst_m} `{GHC.Base.Eq_ inst_a}
   : (ExceptT inst_e inst_m inst_a) -> (ExceptT inst_e inst_m inst_a) -> bool :=
  eq1.

Local Definition Eq___ExceptT_op_zsze__ {inst_e} {inst_m} {inst_a}
  `{GHC.Base.Eq_ inst_e} `{Eq1 inst_m} `{GHC.Base.Eq_ inst_a}
   : (ExceptT inst_e inst_m inst_a) -> (ExceptT inst_e inst_m inst_a) -> bool :=
  fun x y => negb (Eq___ExceptT_op_zeze__ x y).

Program Instance Eq___ExceptT {e} {m} {a} `{GHC.Base.Eq_ e} `{Eq1 m}
  `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (ExceptT e m a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___ExceptT_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___ExceptT_op_zsze__ |}.

Local Definition Ord__ExceptT_compare {inst_e} {inst_m} {inst_a} `{GHC.Base.Ord
  inst_e} `{Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (ExceptT inst_e inst_m inst_a) ->
     (ExceptT inst_e inst_m inst_a) -> comparison :=
  compare1.

Local Definition Ord__ExceptT_op_zg__ {inst_e} {inst_m} {inst_a} `{GHC.Base.Ord
  inst_e} `{Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (ExceptT inst_e inst_m inst_a) -> (ExceptT inst_e inst_m inst_a) -> bool :=
  fun x y => Ord__ExceptT_compare x y GHC.Base.== Gt.

Local Definition Ord__ExceptT_op_zgze__ {inst_e} {inst_m} {inst_a}
  `{GHC.Base.Ord inst_e} `{Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (ExceptT inst_e inst_m inst_a) -> (ExceptT inst_e inst_m inst_a) -> bool :=
  fun x y => Ord__ExceptT_compare x y GHC.Base./= Lt.

Local Definition Ord__ExceptT_op_zl__ {inst_e} {inst_m} {inst_a} `{GHC.Base.Ord
  inst_e} `{Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (ExceptT inst_e inst_m inst_a) -> (ExceptT inst_e inst_m inst_a) -> bool :=
  fun x y => Ord__ExceptT_compare x y GHC.Base.== Lt.

Local Definition Ord__ExceptT_op_zlze__ {inst_e} {inst_m} {inst_a}
  `{GHC.Base.Ord inst_e} `{Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (ExceptT inst_e inst_m inst_a) -> (ExceptT inst_e inst_m inst_a) -> bool :=
  fun x y => Ord__ExceptT_compare x y GHC.Base./= Gt.

Local Definition Ord__ExceptT_max {inst_e} {inst_m} {inst_a} `{GHC.Base.Ord
  inst_e} `{Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (ExceptT inst_e inst_m inst_a) ->
     (ExceptT inst_e inst_m inst_a) -> (ExceptT inst_e inst_m inst_a) :=
  fun x y => if Ord__ExceptT_op_zlze__ x y : bool then y else x.

Local Definition Ord__ExceptT_min {inst_e} {inst_m} {inst_a} `{GHC.Base.Ord
  inst_e} `{Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (ExceptT inst_e inst_m inst_a) ->
     (ExceptT inst_e inst_m inst_a) -> (ExceptT inst_e inst_m inst_a) :=
  fun x y => if Ord__ExceptT_op_zlze__ x y : bool then x else y.

Program Instance Ord__ExceptT {e} {m} {a} `{GHC.Base.Ord e} `{Ord1 m}
  `{GHC.Base.Ord a}
   : GHC.Base.Ord (ExceptT e m a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__ExceptT_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__ExceptT_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__ExceptT_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__ExceptT_op_zgze__ ;
         GHC.Base.compare__ := Ord__ExceptT_compare ;
         GHC.Base.max__ := Ord__ExceptT_max ;
         GHC.Base.min__ := Ord__ExceptT_min |}.

(* Translating `instance Read__ExceptT' failed: OOPS! Cannot find information
   for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__ExceptT' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Foldable__ExceptT_foldMap {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (ExceptT inst_e inst_f) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_ExceptT a =>
          Data.Foldable.foldMap (Data.Either.either (GHC.Base.const GHC.Base.mempty) f) a
      end.

Local Definition Foldable__ExceptT_foldl {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (ExceptT inst_e inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          appEndo (getDual (Foldable__ExceptT_foldMap (Coq.Program.Basics.compose Mk_Dual
                                                                                  (Coq.Program.Basics.compose Mk_Endo
                                                                                                              (GHC.Base.flip
                                                                                                               f))) t))
          z
      end.

Local Definition Foldable__ExceptT_foldr' {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (ExceptT inst_e inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__ExceptT_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__ExceptT_foldr {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (ExceptT inst_e inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          appEndo (Foldable__ExceptT_foldMap (Data.Foldable.hash_compose Mk_Endo f) t) z
      end.

Local Definition Foldable__ExceptT_foldl' {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (ExceptT inst_e inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__ExceptT_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__ExceptT_length {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (ExceptT inst_e inst_f) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__ExceptT_foldl' (fun arg_64__ arg_65__ =>
                                match arg_64__, arg_65__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

Local Definition Foldable__ExceptT_null {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (ExceptT inst_e inst_f) a -> bool :=
  fun {a} => Foldable__ExceptT_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__ExceptT_toList {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (ExceptT inst_e inst_f) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__ExceptT_foldr c n t
                        end).

Local Definition Foldable__ExceptT_product {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (ExceptT inst_e inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose getProduct (Foldable__ExceptT_foldMap Mk_Product).

Local Definition Foldable__ExceptT_sum {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (ExceptT inst_e inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose getSum (Foldable__ExceptT_foldMap Mk_Sum).

Local Definition Foldable__ExceptT_fold {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m}, forall `{GHC.Base.Monoid m}, (ExceptT inst_e inst_f) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__ExceptT_foldMap GHC.Base.id.

Local Definition Foldable__ExceptT_elem {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a},
     forall `{GHC.Base.Eq_ a}, a -> (ExceptT inst_e inst_f) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose getAny (Foldable__ExceptT_foldMap
                                                              (Coq.Program.Basics.compose Mk_Any p))) _GHC.Base.==_.

Program Instance Foldable__ExceptT {f} {e} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (ExceptT e f) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__ExceptT_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__ExceptT_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__ExceptT_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__ExceptT_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__ExceptT_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__ExceptT_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__ExceptT_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__ExceptT_length ;
         Data.Foldable.null__ := fun {a} => Foldable__ExceptT_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__ExceptT_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__ExceptT_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__ExceptT_toList |}.

Local Definition Traversable__ExceptT_traverse {inst_f} {inst_e}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (ExceptT inst_e inst_f) a -> f ((ExceptT inst_e inst_f) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_ExceptT a =>
          Mk_ExceptT Data.Functor.<$>
          Data.Traversable.traverse (Data.Either.either (GHC.Base.pure GHC.Base.∘
                                                         Data.Either.Left) (GHC.Base.fmap Data.Either.Right GHC.Base.∘
                                                                            f)) a
      end.

Local Definition Traversable__ExceptT_sequenceA {inst_f} {inst_e}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (ExceptT inst_e inst_f) (f a) -> f ((ExceptT inst_e inst_f) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__ExceptT_traverse GHC.Base.id.

Local Definition Traversable__ExceptT_sequence {inst_f} {inst_e}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (ExceptT inst_e inst_f) (m a) -> m ((ExceptT inst_e inst_f) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__ExceptT_sequenceA.

Local Definition Traversable__ExceptT_mapM {inst_f} {inst_e}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (ExceptT inst_e inst_f) a -> m ((ExceptT inst_e inst_f) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__ExceptT_traverse.

Local Definition Applicative__ExceptT_op_zlztzg__ {inst_m} {inst_e}
  `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (ExceptT inst_e inst_m) (a -> b) ->
     (ExceptT inst_e inst_m) a -> (ExceptT inst_e inst_m) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_ExceptT f, Mk_ExceptT v =>
          Mk_ExceptT (f GHC.Base.>>=
                      (fun mf =>
                         match mf with
                         | Data.Either.Left e => GHC.Base.return_ (Data.Either.Left e)
                         | Data.Either.Right k =>
                             v GHC.Base.>>=
                             (fun mv =>
                                match mv with
                                | Data.Either.Left e => GHC.Base.return_ (Data.Either.Left e)
                                | Data.Either.Right x => GHC.Base.return_ (Data.Either.Right (k x))
                                end)
                         end))
      end.

(* Translating `instance Alternative__ExceptT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

(* Translating `instance MonadFail__ExceptT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

(* Translating `instance MonadPlus__ExceptT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "MonadPlus" unsupported *)

(* Translating `instance MonadFix__ExceptT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

Local Definition MonadTrans__ExceptT_lift {inst_e}
   : forall {m} {a} `{GHC.Base.Monad m}, m a -> (ExceptT inst_e) m a :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    Mk_ExceptT GHC.Base.∘ GHC.Base.liftM Data.Either.Right.

Program Instance MonadTrans__ExceptT {e}
   : Control.Monad.Trans.Class.MonadTrans (ExceptT e) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{GHC.Base.Monad m} =>
           MonadTrans__ExceptT_lift |}.

(* Translating `instance MonadIO__ExceptT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.IO.Class" "MonadIO" unsupported *)

(* Translating `instance MonadZip__ExceptT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Zip" "MonadZip" unsupported *)

Definition except {e} {a} : Data.Either.Either e a -> Except e a :=
  fun m => Mk_ExceptT (Mk_Identity m).

Definition runExcept {e} {a} : Except e a -> Data.Either.Either e a :=
  fun arg_0__ => let 'Mk_ExceptT m := arg_0__ in runIdentity m.

Definition runExceptT {e} {m} {a}
   : ExceptT e m a -> m (Data.Either.Either e a) :=
  fun arg_0__ => let 'Mk_ExceptT m := arg_0__ in m.

Definition mapExceptT {m} {e} {a} {n} {e'} {b}
   : (m (Data.Either.Either e a) -> n (Data.Either.Either e' b)) ->
     ExceptT e m a -> ExceptT e' n b :=
  fun f m => Mk_ExceptT (f (runExceptT m)).

Definition withExceptT {m} {e} {e'} {a} `{(GHC.Base.Functor m)}
   : (e -> e') -> ExceptT e m a -> ExceptT e' m a :=
  fun f =>
    mapExceptT (GHC.Base.fmap (Data.Either.either (Data.Either.Left GHC.Base.∘ f)
                                                  Data.Either.Right)).

Definition withExcept {e} {e'} {a} : (e -> e') -> Except e a -> Except e' a :=
  withExceptT.

Definition mapExcept {e} {a} {e'} {b}
   : (Data.Either.Either e a -> Data.Either.Either e' b) ->
     Except e a -> Except e' b :=
  fun f => mapExceptT (Mk_Identity GHC.Base.∘ (f GHC.Base.∘ runIdentity)).

Definition liftPass {m} {w} {e} {a} `{(GHC.Base.Monad m)}
   : Control.Monad.Signatures.Pass w m (Data.Either.Either e a) ->
     Control.Monad.Signatures.Pass w (ExceptT e m) a :=
  fun pass =>
    mapExceptT (fun m =>
                  pass (m GHC.Base.>>=
                        (fun a =>
                           GHC.Base.return_ (match a with
                                             | Data.Either.Left l => pair (Data.Either.Left l) GHC.Base.id
                                             | Data.Either.Right (pair r f) => pair (Data.Either.Right r) f
                                             end)))).

Definition liftListen {m} {w} {e} {a} `{(GHC.Base.Monad m)}
   : Control.Monad.Signatures.Listen w m (Data.Either.Either e a) ->
     Control.Monad.Signatures.Listen w (ExceptT e m) a :=
  fun listen =>
    mapExceptT (fun m =>
                  let cont_0__ arg_1__ :=
                    let 'pair a w := arg_1__ in
                    GHC.Base.return_ (GHC.Base.fmap (fun r => pair r w) a) in
                  listen m GHC.Base.>>= cont_0__).

Definition liftCallCC {m} {e} {a} {b}
   : Control.Monad.Signatures.CallCC m (Data.Either.Either e a)
     (Data.Either.Either e b) ->
     Control.Monad.Signatures.CallCC (ExceptT e m) a b :=
  fun callCC f =>
    Mk_ExceptT (callCC (fun c =>
                          runExceptT (f (fun a => Mk_ExceptT (c (Data.Either.Right a)))))).

Definition catchE {m} {e} {a} {e'} `{(GHC.Base.Monad m)}
   : ExceptT e m a -> (e -> ExceptT e' m a) -> ExceptT e' m a :=
  fun m h =>
    Mk_ExceptT (runExceptT m GHC.Base.>>=
                (fun a =>
                   match a with
                   | Data.Either.Left l => runExceptT (h l)
                   | Data.Either.Right r => GHC.Base.return_ (Data.Either.Right r)
                   end)).

Local Definition Functor__ExceptT_fmap {inst_m} {inst_e} `{(GHC.Base.Functor
   inst_m)}
   : forall {a} {b},
     (a -> b) -> (ExceptT inst_e inst_m) a -> (ExceptT inst_e inst_m) b :=
  fun {a} {b} =>
    fun f =>
      Mk_ExceptT GHC.Base.∘ (GHC.Base.fmap (GHC.Base.fmap f) GHC.Base.∘ runExceptT).

Local Definition Functor__ExceptT_op_zlzd__ {inst_m} {inst_e}
  `{(GHC.Base.Functor inst_m)}
   : forall {a} {b},
     a -> (ExceptT inst_e inst_m) b -> (ExceptT inst_e inst_m) a :=
  fun {a} {b} => fun x => Functor__ExceptT_fmap (GHC.Base.const x).

Program Instance Functor__ExceptT {m} {e} `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (ExceptT e m) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__ExceptT_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__ExceptT_fmap |}.

Local Definition Applicative__ExceptT_pure {inst_m} {inst_e} `{GHC.Base.Functor
  inst_m} `{GHC.Base.Monad inst_m}
   : forall {a}, a -> (ExceptT inst_e inst_m) a :=
  fun {a} => fun a => Mk_ExceptT (GHC.Base.return_ (Data.Either.Right a)).

Definition Applicative__ExceptT_op_ztzg__ {inst_m} {inst_s} `{_
   : GHC.Base.Monad inst_m}
   : forall {a} {b},
     ExceptT inst_s inst_m a -> ExceptT inst_s inst_m b -> ExceptT inst_s inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Applicative__ExceptT_op_zlztzg__ (Applicative__ExceptT_op_zlztzg__
                                        (Applicative__ExceptT_pure (fun x y => x)) k) m.

Program Instance Applicative__ExceptT {m} {e} `{GHC.Base.Functor m}
  `{GHC.Base.Monad m}
   : GHC.Base.Applicative (ExceptT e m) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__ExceptT_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__ExceptT_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__ExceptT_pure |}.

Local Definition Monad__ExceptT_op_zgzg__ {inst_m} {inst_e} `{(GHC.Base.Monad
   inst_m)}
   : forall {a} {b},
     (ExceptT inst_e inst_m) a ->
     (ExceptT inst_e inst_m) b -> (ExceptT inst_e inst_m) b :=
  fun {a} {b} => _GHC.Base.*>_.

Definition Monad__ExceptT_op_zgzgze__ {inst_m} {inst_e} `{_
   : GHC.Base.Monad inst_m}
   : forall {a} {b},
     ExceptT inst_e inst_m a ->
     (a -> ExceptT inst_e inst_m b) -> ExceptT inst_e inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Mk_ExceptT (runExceptT m GHC.Base.>>=
                  (fun a =>
                     match a with
                     | Data.Either.Left e => GHC.Base.return_ (Data.Either.Left e)
                     | Data.Either.Right x => runExceptT (k x)
                     end)).

Local Definition Monad__ExceptT_return_ {inst_m} {inst_e} `{(GHC.Base.Monad
   inst_m)}
   : forall {a}, a -> (ExceptT inst_e inst_m) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__ExceptT {m} {e} `{(GHC.Base.Monad m)}
   : GHC.Base.Monad (ExceptT e m) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__ExceptT_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__ExceptT_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__ExceptT_return_ |}.

Program Instance Traversable__ExceptT {f} {e} `{(Data.Traversable.Traversable
   f)}
   : Data.Traversable.Traversable (ExceptT e f) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__ExceptT_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__ExceptT_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__ExceptT_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__ExceptT_traverse |}.

Definition throwE {m} {e} {a} `{(GHC.Base.Monad m)} : e -> ExceptT e m a :=
  Mk_ExceptT GHC.Base.∘ (GHC.Base.return_ GHC.Base.∘ Data.Either.Left).

(* Unbound variables:
     Eq1 Gt Identity Lt Mk_Any Mk_Dual Mk_Endo Mk_Identity Mk_Product Mk_Sum Ord1
     appEndo bool compare1 comparison eq1 false getAny getDual getProduct getSum
     liftCompare liftEq list negb pair runIdentity true
     Control.Monad.Signatures.CallCC Control.Monad.Signatures.Listen
     Control.Monad.Signatures.Pass Control.Monad.Trans.Class.MonadTrans
     Coq.Program.Basics.compose Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Either.either Data.Foldable.Foldable Data.Foldable.foldMap
     Data.Foldable.hash_compose Data.Functor.op_zlzdzg__ Data.Traversable.Traversable
     Data.Traversable.traverse GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.build GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.id GHC.Base.liftM GHC.Base.mempty
     GHC.Base.op_z2218U__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zgzgze__
     GHC.Base.op_zsze__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.Base.return_ GHC.Num.Int
     GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
