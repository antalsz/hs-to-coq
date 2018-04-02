(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Trans.Class.
Require Import Data.Functor.Identity.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ContT (r : Type) (m : Type -> Type) a : Type
  := Mk_ContT : ((a -> m r) -> m r) -> ContT r m a.

Definition Cont r :=
  (ContT r Identity)%type.

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
  fun {a} {b} => fun x => Functor__ContT_fmap (GHC.Base.const x).

Program Instance Functor__ContT {r} {m} : GHC.Base.Functor (ContT r m) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__ContT_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__ContT_fmap |}.

Local Definition Applicative__ContT_op_zlztzg__ {inst_r} {inst_m}
   : forall {a} {b},
     (ContT inst_r inst_m) (a -> b) ->
     (ContT inst_r inst_m) a -> (ContT inst_r inst_m) b :=
  fun {a} {b} =>
    fun f v =>
      Mk_ContT (fun c => runContT f (fun g => runContT v (c GHC.Base.∘ g))).

Local Definition Applicative__ContT_liftA2 {inst_r} {inst_m}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (ContT inst_r inst_m) a -> (ContT inst_r inst_m) b -> (ContT inst_r inst_m) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__ContT_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__ContT_pure {inst_r} {inst_m}
   : forall {a}, a -> (ContT inst_r inst_m) a :=
  fun {a} => fun x => Mk_ContT (fun arg_0__ => arg_0__ x).

Definition Applicative__ContT_op_ztzg__ {inst_m} {inst_s}
   : forall {a} {b},
     ContT inst_s inst_m a -> ContT inst_s inst_m b -> ContT inst_s inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Applicative__ContT_op_zlztzg__ (Applicative__ContT_op_zlztzg__
                                      (Applicative__ContT_pure (fun x y => x)) k) m.

Program Instance Applicative__ContT {r} {m}
   : GHC.Base.Applicative (ContT r m) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__ContT_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__ContT_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__ContT_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__ContT_pure |}.

Local Definition Monad__ContT_op_zgzg__ {inst_r} {inst_m}
   : forall {a} {b},
     (ContT inst_r inst_m) a -> (ContT inst_r inst_m) b -> (ContT inst_r inst_m) b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__ContT_op_zgzgze__ {inst_r} {inst_m}
   : forall {a} {b},
     (ContT inst_r inst_m) a ->
     (a -> (ContT inst_r inst_m) b) -> (ContT inst_r inst_m) b :=
  fun {a} {b} =>
    fun m k => Mk_ContT (fun c => runContT m (fun x => runContT (k x) c)).

Local Definition Monad__ContT_return_ {inst_r} {inst_m}
   : forall {a}, a -> (ContT inst_r inst_m) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__ContT {r} {m} : GHC.Base.Monad (ContT r m) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__ContT_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__ContT_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__ContT_return_ |}.

(* Translating `instance MonadFail__ContT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

Local Definition MonadTrans__ContT_lift {inst_r}
   : forall {m} {a} `{GHC.Base.Monad m}, m a -> (ContT inst_r) m a :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    fun m => Mk_ContT (fun arg_0__ => m GHC.Base.>>= arg_0__).

Program Instance MonadTrans__ContT {r}
   : Control.Monad.Trans.Class.MonadTrans (ContT r) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{GHC.Base.Monad m} =>
           MonadTrans__ContT_lift |}.

(* Translating `instance MonadIO__ContT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.IO.Class" "MonadIO" unsupported *)

Definition callCC {a} {r} {m} {b}
   : ((a -> ContT r m b) -> ContT r m a) -> ContT r m a :=
  fun f =>
    Mk_ContT (fun c => runContT (f (fun x => Mk_ContT (fun arg_0__ => c x))) c).

Definition cont {a} {r} : ((a -> r) -> r) -> Cont r a :=
  fun f => Mk_ContT (fun c => Mk_Identity (f (runIdentity GHC.Base.∘ c))).

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
  fun f => shiftT (f GHC.Base.∘ (fun arg_0__ => runIdentity GHC.Base.∘ arg_0__)).

Definition evalCont {r} : Cont r r -> r :=
  fun m => runIdentity (evalContT m).

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
  fun f => mapContT (Mk_Identity GHC.Base.∘ (f GHC.Base.∘ runIdentity)).

Definition runCont {r} {a} : Cont r a -> (a -> r) -> r :=
  fun m k => runIdentity (runContT m (Mk_Identity GHC.Base.∘ k)).

Definition withContT {b} {m} {r} {a}
   : ((b -> m r) -> (a -> m r)) -> ContT r m a -> ContT r m b :=
  fun f m => Mk_ContT (runContT m GHC.Base.∘ f).

Definition withCont {b} {r} {a}
   : ((b -> r) -> (a -> r)) -> Cont r a -> Cont r b :=
  fun f =>
    withContT ((fun arg_0__ => Mk_Identity GHC.Base.∘ arg_0__) GHC.Base.∘
               (f GHC.Base.∘ (fun arg_1__ => runIdentity GHC.Base.∘ arg_1__))).

(* External variables:
     Identity Mk_Identity Type runIdentity Control.Monad.Trans.Class.MonadTrans
     Control.Monad.Trans.Class.lift GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.const GHC.Base.fmap GHC.Base.op_z2218U__
     GHC.Base.op_zgzgze__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.Base.return_
*)
