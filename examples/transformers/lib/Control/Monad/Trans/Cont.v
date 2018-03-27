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
Require Import GHC.Base.

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
  fun {a} {b} => fun f m => Mk_ContT (fun c => runContT m (c ∘ f)).

Local Definition Functor__ContT_op_zlzd__ {inst_r} {inst_m}
   : forall {a} {b}, a -> (ContT inst_r inst_m) b -> (ContT inst_r inst_m) a :=
  fun {a} {b} => fun x => Functor__ContT_fmap (const x).

Program Instance Functor__ContT {r} {m} : Functor (ContT r m) :=
  fun _ k =>
    k {| op_zlzd____ := fun {a} {b} => Functor__ContT_op_zlzd__ ;
         fmap__ := fun {a} {b} => Functor__ContT_fmap |}.

Local Definition Applicative__ContT_op_zlztzg__ {inst_r} {inst_m}
   : forall {a} {b},
     (ContT inst_r inst_m) (a -> b) ->
     (ContT inst_r inst_m) a -> (ContT inst_r inst_m) b :=
  fun {a} {b} =>
    fun f v => Mk_ContT (fun c => runContT f (fun g => runContT v (c ∘ g))).

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

Program Instance Applicative__ContT {r} {m} : Applicative (ContT r m) :=
  fun _ k =>
    k {| op_ztzg____ := fun {a} {b} => Applicative__ContT_op_ztzg__ ;
         op_zlztzg____ := fun {a} {b} => Applicative__ContT_op_zlztzg__ ;
         pure__ := fun {a} => Applicative__ContT_pure |}.

Local Definition Monad__ContT_op_zgzg__ {inst_r} {inst_m}
   : forall {a} {b},
     (ContT inst_r inst_m) a -> (ContT inst_r inst_m) b -> (ContT inst_r inst_m) b :=
  fun {a} {b} => _*>_.

Local Definition Monad__ContT_op_zgzgze__ {inst_r} {inst_m}
   : forall {a} {b},
     (ContT inst_r inst_m) a ->
     (a -> (ContT inst_r inst_m) b) -> (ContT inst_r inst_m) b :=
  fun {a} {b} =>
    fun m k => Mk_ContT (fun c => runContT m (fun x => runContT (k x) c)).

Local Definition Monad__ContT_return_ {inst_r} {inst_m}
   : forall {a}, a -> (ContT inst_r inst_m) a :=
  fun {a} => pure.

Program Instance Monad__ContT {r} {m} : Monad (ContT r m) :=
  fun _ k =>
    k {| op_zgzg____ := fun {a} {b} => Monad__ContT_op_zgzg__ ;
         op_zgzgze____ := fun {a} {b} => Monad__ContT_op_zgzgze__ ;
         return___ := fun {a} => Monad__ContT_return_ |}.

(* Translating `instance MonadFail__ContT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

Local Definition MonadTrans__ContT_lift {inst_r}
   : forall {m} {a} `{Monad m}, m a -> (ContT inst_r) m a :=
  fun {m} {a} `{Monad m} => fun m => Mk_ContT (fun arg_0__ => m >>= arg_0__).

Program Instance MonadTrans__ContT {r}
   : Control.Monad.Trans.Class.MonadTrans (ContT r) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{Monad m} =>
           MonadTrans__ContT_lift |}.

(* Translating `instance MonadIO__ContT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.IO.Class" "MonadIO" unsupported *)

Definition callCC {a} {r} {m} {b}
   : ((a -> ContT r m b) -> ContT r m a) -> ContT r m a :=
  fun f =>
    Mk_ContT (fun c => runContT (f (fun x => Mk_ContT (fun arg_0__ => c x))) c).

Definition cont {a} {r} : ((a -> r) -> r) -> Cont r a :=
  fun f => Mk_ContT (fun c => Mk_Identity (f (runIdentity ∘ c))).

Definition evalContT {m} {r} `{(Monad m)} : ContT r m r -> m r :=
  fun m => runContT m return_.

Definition resetT {m} {r} {r'} `{(Monad m)} : ContT r m r -> ContT r' m r :=
  Control.Monad.Trans.Class.lift ∘ evalContT.

Definition reset {r} {r'} : Cont r r -> Cont r' r :=
  resetT.

Definition shiftT {m} {a} {r} `{(Monad m)}
   : ((a -> m r) -> ContT r m r) -> ContT r m a :=
  fun f => Mk_ContT (evalContT ∘ f).

Definition shift {a} {r} : ((a -> r) -> Cont r r) -> Cont r a :=
  fun f => shiftT (f ∘ (fun arg_0__ => runIdentity ∘ arg_0__)).

Definition evalCont {r} : Cont r r -> r :=
  fun m => runIdentity (evalContT m).

Definition liftLocal {m} {r'} {r} {a} `{(Monad m)}
   : m r' ->
     ((r' -> r') -> m r -> m r) -> (r' -> r') -> ContT r m a -> ContT r m a :=
  fun ask local f m =>
    Mk_ContT (fun c =>
                ask >>= (fun r => local f (runContT m (local (const r) ∘ c)))).

Definition mapContT {m} {r} {a} : (m r -> m r) -> ContT r m a -> ContT r m a :=
  fun f m => Mk_ContT (_∘_ f (runContT m)).

Definition mapCont {r} {a} : (r -> r) -> Cont r a -> Cont r a :=
  fun f => mapContT (Mk_Identity ∘ (f ∘ runIdentity)).

Definition runCont {r} {a} : Cont r a -> (a -> r) -> r :=
  fun m k => runIdentity (runContT m (Mk_Identity ∘ k)).

Definition withContT {b} {m} {r} {a}
   : ((b -> m r) -> (a -> m r)) -> ContT r m a -> ContT r m b :=
  fun f m => Mk_ContT (_∘_ (runContT m) f).

Definition withCont {b} {r} {a}
   : ((b -> r) -> (a -> r)) -> Cont r a -> Cont r b :=
  fun f =>
    withContT ((fun arg_0__ => Mk_Identity ∘ arg_0__) ∘
               (f ∘ (fun arg_1__ => runIdentity ∘ arg_1__))).

(* Unbound variables:
     Applicative Functor Identity Mk_Identity Monad Type const op_z2218U__
     op_zgzgze__ op_ztzg__ pure return_ runIdentity
     Control.Monad.Trans.Class.MonadTrans Control.Monad.Trans.Class.lift
*)
