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
Require Control.Monad.Trans.Except.
Require Coq.Program.Basics.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Classes.
Require Data.Maybe.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive MaybeT m a : Type
  := Mk_MaybeT (runMaybeT : m (option a)) : MaybeT m a.

Arguments Mk_MaybeT {_} {_} _.

Definition runMaybeT {m} {a} (arg_0__ : MaybeT m a) :=
  let 'Mk_MaybeT runMaybeT := arg_0__ in
  runMaybeT.

(* Midamble *)

Local Definition Monad_tmp {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a} {b},
     (MaybeT inst_m) a -> (a -> (MaybeT inst_m) b) -> (MaybeT inst_m) b :=
  fun {a} {b} =>
    fun x f =>
      Mk_MaybeT (runMaybeT x GHC.Base.>>=
                 (fun v =>
                    match v with
                    | None => GHC.Base.return_ None
                    | Some y => runMaybeT (f y)
                    end)).

(* Converted value declarations: *)

Definition maybeToExceptT {m} {e} {a} `{(GHC.Base.Functor m)}
   : e -> MaybeT m a -> Control.Monad.Trans.Except.ExceptT e m a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | e, Mk_MaybeT m =>
        Control.Monad.Trans.Except.Mk_ExceptT (GHC.Base.fmap (Data.Maybe.maybe
                                                              (Data.Either.Left e) Data.Either.Right) m)
    end.

Definition mapMaybeT {m} {a} {n} {b}
   : (m (option a) -> n (option b)) -> MaybeT m a -> MaybeT n b :=
  fun f => Mk_MaybeT GHC.Base.∘ (f GHC.Base.∘ runMaybeT).

Definition liftPass {m} {w} {a} `{(GHC.Base.Monad m)}
   : Control.Monad.Signatures.Pass w m (option a) ->
     Control.Monad.Signatures.Pass w (MaybeT m) a :=
  fun pass =>
    mapMaybeT (fun m =>
                 pass (m GHC.Base.>>=
                       (fun a =>
                          GHC.Base.return_ (match a with
                                            | None => pair None GHC.Base.id
                                            | Some (pair v f) => pair (Some v) f
                                            end)))).

Definition liftListen {m} {w} {a} `{(GHC.Base.Monad m)}
   : Control.Monad.Signatures.Listen w m (option a) ->
     Control.Monad.Signatures.Listen w (MaybeT m) a :=
  fun listen =>
    mapMaybeT (fun m =>
                 let cont_0__ arg_1__ :=
                   let 'pair a w := arg_1__ in
                   GHC.Base.return_ (GHC.Base.fmap (fun r => pair r w) a) in
                 listen m GHC.Base.>>= cont_0__).

Definition liftCallCC {m} {a} {b}
   : Control.Monad.Signatures.CallCC m (option a) (option b) ->
     Control.Monad.Signatures.CallCC (MaybeT m) a b :=
  fun callCC f =>
    Mk_MaybeT (callCC (fun c =>
                         runMaybeT (f (Mk_MaybeT GHC.Base.∘ (c GHC.Base.∘ Some))))).

Definition exceptToMaybeT {m} {e} {a} `{(GHC.Base.Functor m)}
   : Control.Monad.Trans.Except.ExceptT e m a -> MaybeT m a :=
  fun '(Control.Monad.Trans.Except.Mk_ExceptT m) =>
    Mk_MaybeT (GHC.Base.fmap (Data.Either.either (GHC.Base.const None) Some) m).

(* Skipping all instances of class `Control.Monad.Zip.MonadZip', including
   `Control.Monad.Trans.Maybe.MonadZip__MaybeT' *)

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `Control.Monad.Trans.Maybe.MonadIO__MaybeT' *)

Local Definition MonadTrans__MaybeT_lift
   : forall {m} {a}, forall `{(GHC.Base.Monad m)}, m a -> MaybeT m a :=
  fun {m} {a} `{(GHC.Base.Monad m)} => Mk_MaybeT GHC.Base.∘ GHC.Base.liftM Some.

Program Instance MonadTrans__MaybeT
   : Control.Monad.Trans.Class.MonadTrans MaybeT :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{(GHC.Base.Monad m)} =>
           MonadTrans__MaybeT_lift |}.

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Control.Monad.Trans.Maybe.MonadFix__MaybeT' *)

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Monad.Trans.Maybe.MonadPlus__MaybeT' *)

Definition Monad__MaybeT_op_zgzgze__ {inst_m} `{_ : GHC.Base.Monad inst_m} :=
  fun {a} {b} => (@Monad_tmp inst_m _ _ _ a b).

Local Definition Monad__MaybeT_op_zgzg__ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a} {b},
     (MaybeT inst_m) a -> (MaybeT inst_m) b -> (MaybeT inst_m) b :=
  fun {a} {b} => fun m k => Monad__MaybeT_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Applicative__MaybeT_op_zlztzg__ {inst_m} `{GHC.Base.Functor
  inst_m} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (MaybeT inst_m) (a -> b) -> (MaybeT inst_m) a -> (MaybeT inst_m) b :=
  fun {a} {b} =>
    fun mf mx =>
      Mk_MaybeT (runMaybeT mf GHC.Base.>>=
                 (fun mb_f =>
                    match mb_f with
                    | None => GHC.Base.return_ None
                    | Some f =>
                        runMaybeT mx GHC.Base.>>=
                        (fun mb_x =>
                           match mb_x with
                           | None => GHC.Base.return_ None
                           | Some x => GHC.Base.return_ (Some (f x))
                           end)
                    end)).

Local Definition Functor__MaybeT_fmap {inst_m} `{(GHC.Base.Functor inst_m)}
   : forall {a} {b}, (a -> b) -> (MaybeT inst_m) a -> (MaybeT inst_m) b :=
  fun {a} {b} => fun f => mapMaybeT (GHC.Base.fmap (GHC.Base.fmap f)).

Local Definition Functor__MaybeT_op_zlzd__ {inst_m} `{(GHC.Base.Functor inst_m)}
   : forall {a} {b}, a -> (MaybeT inst_m) b -> (MaybeT inst_m) a :=
  fun {a} {b} => Functor__MaybeT_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__MaybeT {m} `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (MaybeT m) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__MaybeT_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__MaybeT_op_zlzd__ |}.

Local Definition Applicative__MaybeT_liftA2 {inst_m} `{GHC.Base.Functor inst_m}
  `{GHC.Base.Monad inst_m}
   : forall {a} {b} {c},
     (a -> b -> c) -> (MaybeT inst_m) a -> (MaybeT inst_m) b -> (MaybeT inst_m) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__MaybeT_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__MaybeT_pure {inst_m} `{GHC.Base.Functor inst_m}
  `{GHC.Base.Monad inst_m}
   : forall {a}, a -> (MaybeT inst_m) a :=
  fun {a} => Mk_MaybeT GHC.Base.∘ (GHC.Base.return_ GHC.Base.∘ Some).

Local Definition Applicative__MaybeT_op_ztzg__ {inst_m} `{GHC.Base.Monad inst_m}
   : forall {a} {b}, MaybeT inst_m a -> MaybeT inst_m b -> MaybeT inst_m b :=
  fun {a} {b} => fun m k => Monad_tmp m (fun arg_0__ => k).

Program Instance Applicative__MaybeT {m} `{GHC.Base.Functor m} `{GHC.Base.Monad
  m}
   : GHC.Base.Applicative (MaybeT m) :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__MaybeT_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__MaybeT_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__MaybeT_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__MaybeT_pure |}.

Local Definition Monad__MaybeT_return_ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a}, a -> (MaybeT inst_m) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__MaybeT {m} `{(GHC.Base.Monad m)}
   : GHC.Base.Monad (MaybeT m) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__MaybeT_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__MaybeT_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__MaybeT_return_ |}.

Local Definition MonadFail__MaybeT_fail {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a}, GHC.Base.String -> (MaybeT inst_m) a :=
  fun {a} => fun arg_0__ => Mk_MaybeT (GHC.Base.return_ None).

Program Instance MonadFail__MaybeT {m} `{(GHC.Base.Monad m)}
   : Control.Monad.Fail.MonadFail (MaybeT m) :=
  fun _ k =>
    k {| Control.Monad.Fail.fail__ := fun {a} => MonadFail__MaybeT_fail |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Monad.Trans.Maybe.Alternative__MaybeT' *)

Local Definition Traversable__MaybeT_traverse {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (MaybeT inst_f) a -> f ((MaybeT inst_f) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_MaybeT a =>
          Mk_MaybeT Data.Functor.<$>
          Data.Traversable.traverse (Data.Traversable.traverse f) a
      end.

Local Definition Traversable__MaybeT_mapM {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (MaybeT inst_f) a -> m ((MaybeT inst_f) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__MaybeT_traverse.

Local Definition Traversable__MaybeT_sequenceA {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (MaybeT inst_f) (f a) -> f ((MaybeT inst_f) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__MaybeT_traverse GHC.Base.id.

Local Definition Traversable__MaybeT_sequence {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monad m}, (MaybeT inst_f) (m a) -> m ((MaybeT inst_f) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__MaybeT_sequenceA.

Local Definition Foldable__MaybeT_foldMap {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (MaybeT inst_f) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_MaybeT a =>
          (@Data.Foldable.foldMap inst_f _ _ _ _ _ (Data.Foldable.foldMap f)) a
      end.

Local Definition Foldable__MaybeT_fold {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m}, forall `{GHC.Base.Monoid m}, (MaybeT inst_f) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__MaybeT_foldMap GHC.Base.id.

Local Definition Foldable__MaybeT_foldl {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (MaybeT inst_f) a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__MaybeT_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                 (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                  GHC.Base.flip f)) t)) z.

Local Definition Foldable__MaybeT_foldr {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (MaybeT inst_f) a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__MaybeT_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__MaybeT_foldl' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (MaybeT inst_f) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__MaybeT_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__MaybeT_foldr' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (MaybeT inst_f) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__MaybeT_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__MaybeT_length {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (MaybeT inst_f) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__MaybeT_foldl' (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | c, _ => c GHC.Num.+ #1
                               end) #0.

Local Definition Foldable__MaybeT_null {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (MaybeT inst_f) a -> bool :=
  fun {a} => Foldable__MaybeT_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__MaybeT_product {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (MaybeT inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__MaybeT_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__MaybeT_sum {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (MaybeT inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__MaybeT_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__MaybeT_toList {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (MaybeT inst_f) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__MaybeT_foldr c n t)).

Program Instance Foldable__MaybeT {f} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (MaybeT f) :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__MaybeT_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__MaybeT_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__MaybeT_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__MaybeT_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__MaybeT_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__MaybeT_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__MaybeT_length ;
         Data.Foldable.null__ := fun {a} => Foldable__MaybeT_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__MaybeT_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__MaybeT_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__MaybeT_toList |}.

Program Instance Traversable__MaybeT {f} `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (MaybeT f) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__MaybeT_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__MaybeT_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__MaybeT_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__MaybeT_traverse |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Monad.Trans.Maybe.Show__MaybeT' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Control.Monad.Trans.Maybe.Read__MaybeT' *)

Local Definition Ord1__MaybeT_liftCompare {inst_m} `{(Data.Functor.Classes.Ord1
   inst_m)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (MaybeT inst_m) a -> (MaybeT inst_m) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_MaybeT x, Mk_MaybeT y =>
          Data.Functor.Classes.liftCompare (Data.Functor.Classes.liftCompare comp) x y
      end.

Local Definition Eq1__MaybeT_liftEq {inst_m} `{(Data.Functor.Classes.Eq1
   inst_m)}
   : forall {a} {b},
     (a -> b -> bool) -> (MaybeT inst_m) a -> (MaybeT inst_m) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_MaybeT x, Mk_MaybeT y =>
          Data.Functor.Classes.liftEq (Data.Functor.Classes.liftEq eq) x y
      end.

Program Instance Eq1__MaybeT {m} `{(Data.Functor.Classes.Eq1 m)}
   : Data.Functor.Classes.Eq1 (MaybeT m) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__MaybeT_liftEq |}.

Program Instance Ord1__MaybeT {m} `{(Data.Functor.Classes.Ord1 m)}
   : Data.Functor.Classes.Ord1 (MaybeT m) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
           Ord1__MaybeT_liftCompare |}.

Local Definition Ord__MaybeT_compare {inst_m} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__MaybeT_op_zl__ {inst_m} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) -> bool :=
  fun x y => Ord__MaybeT_compare x y GHC.Base.== Lt.

Local Definition Ord__MaybeT_op_zlze__ {inst_m} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) -> bool :=
  fun x y => Ord__MaybeT_compare x y GHC.Base./= Gt.

Local Definition Ord__MaybeT_op_zg__ {inst_m} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) -> bool :=
  fun x y => Ord__MaybeT_compare x y GHC.Base.== Gt.

Local Definition Ord__MaybeT_op_zgze__ {inst_m} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_m} `{GHC.Base.Ord inst_a}
   : (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) -> bool :=
  fun x y => Ord__MaybeT_compare x y GHC.Base./= Lt.

Local Definition Ord__MaybeT_max {inst_m} {inst_a} `{Data.Functor.Classes.Ord1
  inst_m} `{GHC.Base.Ord inst_a}
   : (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) :=
  fun x y => if Ord__MaybeT_op_zlze__ x y : bool then y else x.

Local Definition Ord__MaybeT_min {inst_m} {inst_a} `{Data.Functor.Classes.Ord1
  inst_m} `{GHC.Base.Ord inst_a}
   : (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) :=
  fun x y => if Ord__MaybeT_op_zlze__ x y : bool then x else y.

Local Definition Eq___MaybeT_op_zeze__ {inst_m} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_m} `{GHC.Base.Eq_ inst_a}
   : (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___MaybeT_op_zsze__ {inst_m} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_m} `{GHC.Base.Eq_ inst_a}
   : (MaybeT inst_m inst_a) -> (MaybeT inst_m inst_a) -> bool :=
  fun x y => negb (Eq___MaybeT_op_zeze__ x y).

Program Instance Eq___MaybeT {m} {a} `{Data.Functor.Classes.Eq1 m}
  `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (MaybeT m a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___MaybeT_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___MaybeT_op_zsze__ |}.

Program Instance Ord__MaybeT {m} {a} `{Data.Functor.Classes.Ord1 m}
  `{GHC.Base.Ord a}
   : GHC.Base.Ord (MaybeT m a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__MaybeT_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__MaybeT_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__MaybeT_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__MaybeT_op_zgze__ ;
         GHC.Base.compare__ := Ord__MaybeT_compare ;
         GHC.Base.max__ := Ord__MaybeT_max ;
         GHC.Base.min__ := Ord__MaybeT_min |}.

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Control.Monad.Trans.Maybe.Show1__MaybeT' *)

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Control.Monad.Trans.Maybe.Read1__MaybeT' *)

(* External variables:
     Gt Lt Monad_tmp None Some bool comparison false list negb option pair true
     Control.Monad.Fail.MonadFail Control.Monad.Fail.fail__
     Control.Monad.Signatures.CallCC Control.Monad.Signatures.Listen
     Control.Monad.Signatures.Pass Control.Monad.Trans.Class.MonadTrans
     Control.Monad.Trans.Class.lift__ Control.Monad.Trans.Except.ExceptT
     Control.Monad.Trans.Except.Mk_ExceptT Coq.Program.Basics.compose
     Data.Either.Left Data.Either.Right Data.Either.either Data.Foldable.Foldable
     Data.Foldable.foldMap Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1 Data.Functor.Classes.Ord1
     Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__ Data.Maybe.maybe
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.String GHC.Base.build' GHC.Base.compare__ GHC.Base.const GHC.Base.flip
     GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__ GHC.Base.liftM
     GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return_
     GHC.Base.return___ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
