(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Fail.
Require Control.Monad.Signatures.
Require Control.Monad.Trans.Class.
Require Coq.Program.Basics.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Import Data.Functor.Classes.
Require Import Data.Functor.Identity.
Require Data.SemigroupInternal.
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

(* Skipping instance Read1__ExceptT of class Read1 *)

(* Skipping instance Show1__ExceptT of class Show1 *)

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

(* Skipping instance Read__ExceptT of class Read *)

(* Skipping instance Show__ExceptT of class Show *)

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
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__ExceptT_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

Local Definition Foldable__ExceptT_foldr' {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (ExceptT inst_e inst_f) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__ExceptT_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__ExceptT_foldr {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (ExceptT inst_e inst_f) a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__ExceptT_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__ExceptT_foldl' {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (ExceptT inst_e inst_f) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__ExceptT_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__ExceptT_length {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (ExceptT inst_e inst_f) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__ExceptT_foldl' (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

Local Definition Foldable__ExceptT_null {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (ExceptT inst_e inst_f) a -> bool :=
  fun {a} => Foldable__ExceptT_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__ExceptT_toList {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (ExceptT inst_e inst_f) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__ExceptT_foldr c n t)).

Local Definition Foldable__ExceptT_product {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (ExceptT inst_e inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__ExceptT_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__ExceptT_sum {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (ExceptT inst_e inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__ExceptT_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__ExceptT_fold {inst_f} {inst_e}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m}, forall `{GHC.Base.Monoid m}, (ExceptT inst_e inst_f) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__ExceptT_foldMap GHC.Base.id.

Program Instance Foldable__ExceptT {f} {e} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (ExceptT e f) :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__ExceptT_fold ;
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

(* Skipping instance Alternative__ExceptT of class Alternative *)

(* Skipping instance MonadPlus__ExceptT of class MonadPlus *)

(* Skipping instance MonadFix__ExceptT of class MonadFix *)

Local Definition MonadTrans__ExceptT_lift {inst_e}
   : forall {m} {a}, forall `{(GHC.Base.Monad m)}, m a -> (ExceptT inst_e) m a :=
  fun {m} {a} `{(GHC.Base.Monad m)} =>
    Mk_ExceptT GHC.Base.∘ GHC.Base.liftM Data.Either.Right.

Program Instance MonadTrans__ExceptT {e}
   : Control.Monad.Trans.Class.MonadTrans (ExceptT e) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{(GHC.Base.Monad m)} =>
           MonadTrans__ExceptT_lift |}.

(* Skipping instance MonadIO__ExceptT of class MonadIO *)

(* Skipping instance MonadZip__ExceptT of class MonadZip *)

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

Local Definition Monad__ExceptT_op_zgzg__ {inst_m} {inst_e} `{(GHC.Base.Monad
   inst_m)}
   : forall {a} {b},
     (ExceptT inst_e inst_m) a ->
     (ExceptT inst_e inst_m) b -> (ExceptT inst_e inst_m) b :=
  fun {a} {b} => fun m k => Monad__ExceptT_op_zgzgze__ m (fun arg_0__ => k).

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
  fun {a} {b} => Functor__ExceptT_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__ExceptT {m} {e} `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (ExceptT e m) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__ExceptT_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__ExceptT_op_zlzd__ |}.

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

Local Definition Applicative__ExceptT_liftA2 {inst_m} {inst_e}
  `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (ExceptT inst_e inst_m) a ->
     (ExceptT inst_e inst_m) b -> (ExceptT inst_e inst_m) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__ExceptT_op_zlztzg__ (GHC.Base.fmap f x).

Program Instance Applicative__ExceptT {m} {e} `{GHC.Base.Functor m}
  `{GHC.Base.Monad m}
   : GHC.Base.Applicative (ExceptT e m) :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__ExceptT_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__ExceptT_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__ExceptT_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__ExceptT_pure |}.

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

Local Definition MonadFail__ExceptT_fail {inst_m} {inst_e}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a}, GHC.Base.String -> (ExceptT inst_e inst_m) a :=
  fun {a} => Mk_ExceptT GHC.Base.∘ Control.Monad.Fail.fail.

Program Instance MonadFail__ExceptT {m} {e} `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (ExceptT e m) :=
  fun _ k =>
    k {| Control.Monad.Fail.fail__ := fun {a} => MonadFail__ExceptT_fail |}.

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

(* External variables:
     Eq1 Gt Identity Lt Mk_Identity Ord1 bool compare1 comparison eq1 false
     liftCompare liftCompare__ liftEq liftEq__ list negb pair runIdentity true
     Control.Monad.Fail.MonadFail Control.Monad.Fail.fail Control.Monad.Fail.fail__
     Control.Monad.Signatures.CallCC Control.Monad.Signatures.Listen
     Control.Monad.Signatures.Pass Control.Monad.Trans.Class.MonadTrans
     Control.Monad.Trans.Class.lift__ Coq.Program.Basics.compose Data.Either.Either
     Data.Either.Left Data.Either.Right Data.Either.either Data.Foldable.Foldable
     Data.Foldable.foldMap Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.String GHC.Base.build' GHC.Base.compare__ GHC.Base.const GHC.Base.flip
     GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__ GHC.Base.liftM
     GHC.Base.max__ GHC.Base.mempty GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return_
     GHC.Base.return___ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
