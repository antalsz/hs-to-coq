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
Require Control.Monad.Trans.Class.
Require Data.Functor.Identity.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ContT (r : Type) (m : Type -> Type) a : Type
  := Mk_ContT : ((a -> m r) -> m r) -> ContT r m a.

Definition Cont r :=
  (ContT r Data.Functor.Identity.Identity)%type.

Arguments Mk_ContT {_} {_} {_} _.

Definition runContT {r : Type} {m : Type -> Type} {a} (arg_0__ : ContT r m a) :=
  let 'Mk_ContT runContT := arg_0__ in
  runContT.
(* Converted value declarations: *)

Local Definition Functor__ContT_fmap {inst_r} {inst_m}
   : forall {a} {b},
     (a -> b) -> (ContT inst_r inst_m) a -> (ContT inst_r inst_m) b :=
  fun {a} {b} => fun f m => Mk_ContT (fun c => runContT m (c GHC.Base.∘ f)).

Local Definition Functor__ContT_op_zlzd__ {inst_r} {inst_m}
   : forall {a} {b}, a -> (ContT inst_r inst_m) b -> (ContT inst_r inst_m) a :=
  fun {a} {b} => Functor__ContT_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__ContT {r} {m} : GHC.Base.Functor (ContT r m) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__ContT_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__ContT_op_zlzd__ |}.

Local Definition Applicative__ContT_pure {inst_r} {inst_m}
   : forall {a}, a -> (ContT inst_r inst_m) a :=
  fun {a} => fun x => Mk_ContT (fun arg_0__ => arg_0__ x).

Local Definition Applicative__ContT_op_zlztzg__ {inst_r} {inst_m}
   : forall {a} {b},
     (ContT inst_r inst_m) (a -> b) ->
     (ContT inst_r inst_m) a -> (ContT inst_r inst_m) b :=
  fun {a} {b} =>
    fun f v =>
      Mk_ContT (fun c => runContT f (fun g => runContT v (c GHC.Base.∘ g))).

Definition Applicative__ContT_op_ztzg__ {inst_m} {inst_s}
   : forall {a} {b},
     ContT inst_s inst_m a -> ContT inst_s inst_m b -> ContT inst_s inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Applicative__ContT_op_zlztzg__ (Applicative__ContT_op_zlztzg__
                                      (Applicative__ContT_pure (fun x y => x)) k) m.

Local Definition Applicative__ContT_liftA2 {inst_r} {inst_m}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (ContT inst_r inst_m) a -> (ContT inst_r inst_m) b -> (ContT inst_r inst_m) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__ContT_op_zlztzg__ (GHC.Base.fmap f x).

Program Instance Applicative__ContT {r} {m}
   : GHC.Base.Applicative (ContT r m) :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__ContT_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__ContT_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__ContT_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__ContT_pure |}.

Local Definition Monad__ContT_return_ {inst_r} {inst_m}
   : forall {a}, a -> (ContT inst_r inst_m) a :=
  fun {a} => GHC.Base.pure.

Local Definition Monad__ContT_op_zgzgze__ {inst_r} {inst_m}
   : forall {a} {b},
     (ContT inst_r inst_m) a ->
     (a -> (ContT inst_r inst_m) b) -> (ContT inst_r inst_m) b :=
  fun {a} {b} =>
    fun m k => Mk_ContT (fun c => runContT m (fun x => runContT (k x) c)).

Local Definition Monad__ContT_op_zgzg__ {inst_r} {inst_m}
   : forall {a} {b},
     (ContT inst_r inst_m) a -> (ContT inst_r inst_m) b -> (ContT inst_r inst_m) b :=
  fun {a} {b} => fun m k => Monad__ContT_op_zgzgze__ m (fun arg_0__ => k).

Program Instance Monad__ContT {r} {m} : GHC.Base.Monad (ContT r m) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__ContT_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__ContT_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__ContT_return_ |}.

Local Definition MonadFail__ContT_fail {inst_m} {inst_r}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a}, GHC.Base.String -> (ContT inst_r inst_m) a :=
  fun {a} => fun msg => Mk_ContT (fun arg_0__ => Control.Monad.Fail.fail msg).

Program Instance MonadFail__ContT {m} {r} `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (ContT r m) :=
  fun _ k =>
    k {| Control.Monad.Fail.fail__ := fun {a} => MonadFail__ContT_fail |}.

Local Definition MonadTrans__ContT_lift {inst_r}
   : forall {m} {a}, forall `{(GHC.Base.Monad m)}, m a -> (ContT inst_r) m a :=
  fun {m} {a} `{(GHC.Base.Monad m)} =>
    fun m => Mk_ContT (fun arg_0__ => m GHC.Base.>>= arg_0__).

Program Instance MonadTrans__ContT {r}
   : Control.Monad.Trans.Class.MonadTrans (ContT r) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{(GHC.Base.Monad m)} =>
           MonadTrans__ContT_lift |}.

(* Skipping instance MonadIO__ContT of class MonadIO *)

Definition callCC {a} {r} {m} {b}
   : ((a -> ContT r m b) -> ContT r m a) -> ContT r m a :=
  fun f =>
    Mk_ContT (fun c => runContT (f (fun x => Mk_ContT (fun arg_0__ => c x))) c).

Definition cont {a} {r} : ((a -> r) -> r) -> Cont r a :=
  fun f =>
    Mk_ContT (fun c =>
                Data.Functor.Identity.Mk_Identity (f (Data.Functor.Identity.runIdentity
                                                      GHC.Base.∘
                                                      c))).

Definition evalContT {m} {r} `{(GHC.Base.Monad m)} : ContT r m r -> m r :=
  fun m => runContT m GHC.Base.return_.

Definition resetT {m} {r} {r'} `{(GHC.Base.Monad m)}
   : ContT r m r -> ContT r' m r :=
  Control.Monad.Trans.Class.lift GHC.Base.∘ evalContT.

Definition reset {r} {r'} : Cont r r -> Cont r' r :=
  resetT.

Definition shiftT {m} {a} {r} `{(GHC.Base.Monad m)}
   : ((a -> m r) -> ContT r m r) -> ContT r m a :=
  fun f => Mk_ContT (evalContT GHC.Base.∘ f).

Definition shift {a} {r} : ((a -> r) -> Cont r r) -> Cont r a :=
  fun f =>
    shiftT (f GHC.Base.∘
            (fun arg_0__ => Data.Functor.Identity.runIdentity GHC.Base.∘ arg_0__)).

Definition evalCont {r} : Cont r r -> r :=
  fun m => Data.Functor.Identity.runIdentity (evalContT m).

Definition liftLocal {m} {r'} {r} {a} `{(GHC.Base.Monad m)}
   : m r' ->
     ((r' -> r') -> m r -> m r) -> (r' -> r') -> ContT r m a -> ContT r m a :=
  fun ask local f m =>
    Mk_ContT (fun c =>
                ask GHC.Base.>>=
                (fun r => local f (runContT m (local (GHC.Base.const r) GHC.Base.∘ c)))).

Definition mapContT {m} {r} {a} : (m r -> m r) -> ContT r m a -> ContT r m a :=
  fun f m => Mk_ContT (f GHC.Base.∘ runContT m).

Definition mapCont {r} {a} : (r -> r) -> Cont r a -> Cont r a :=
  fun f =>
    mapContT (Data.Functor.Identity.Mk_Identity GHC.Base.∘
              (f GHC.Base.∘ Data.Functor.Identity.runIdentity)).

Definition runCont {r} {a} : Cont r a -> (a -> r) -> r :=
  fun m k =>
    Data.Functor.Identity.runIdentity (runContT m (Data.Functor.Identity.Mk_Identity
                                                   GHC.Base.∘
                                                   k)).

Definition withContT {b} {m} {r} {a}
   : ((b -> m r) -> (a -> m r)) -> ContT r m a -> ContT r m b :=
  fun f m => Mk_ContT (runContT m GHC.Base.∘ f).

Definition withCont {b} {r} {a}
   : ((b -> r) -> (a -> r)) -> Cont r a -> Cont r b :=
  fun f =>
    withContT ((fun arg_0__ => Data.Functor.Identity.Mk_Identity GHC.Base.∘ arg_0__)
               GHC.Base.∘
               (f GHC.Base.∘
                (fun arg_1__ => Data.Functor.Identity.runIdentity GHC.Base.∘ arg_1__))).

(* External variables:
     Type Control.Monad.Fail.MonadFail Control.Monad.Fail.fail
     Control.Monad.Fail.fail__ Control.Monad.Trans.Class.MonadTrans
     Control.Monad.Trans.Class.lift Control.Monad.Trans.Class.lift__
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Functor.Identity.runIdentity GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.String GHC.Base.const GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.liftA2__ GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__
     GHC.Base.op_zgzgze____ GHC.Base.op_zlzd____ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return_
     GHC.Base.return___
*)
