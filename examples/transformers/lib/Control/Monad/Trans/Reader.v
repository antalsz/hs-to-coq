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
Require Import Data.Functor.Identity.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ReaderT (r : Type) (m : Type -> Type) a : Type
  := Mk_ReaderT : (r -> m a) -> ReaderT r m a.

Definition Reader r :=
  (ReaderT r Identity)%type.

Arguments Mk_ReaderT {_} {_} {_} _.

Definition runReaderT {r : Type} {m : Type -> Type} {a} (arg_0__
    : ReaderT r m a) :=
  let 'Mk_ReaderT runReaderT := arg_0__ in
  runReaderT.
(* Converted value declarations: *)

Local Definition Applicative__ReaderT_op_zlztzg__ {inst_m} {inst_r}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) (a -> b) ->
     (ReaderT inst_r inst_m) a -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} =>
    fun f v => Mk_ReaderT (fun r => runReaderT f r GHC.Base.<*> runReaderT v r).

(* Translating `instance Alternative__ReaderT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Monad__ReaderT_op_zgzgze__ {inst_m} {inst_r} `{(GHC.Base.Monad
   inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) a ->
     (a -> (ReaderT inst_r inst_m) b) -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_ReaderT (fun r => runReaderT m r GHC.Base.>>= (fun a => runReaderT (k a) r)).

(* Translating `instance MonadFail__ReaderT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

(* Translating `instance MonadPlus__ReaderT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "MonadPlus" unsupported *)

(* Translating `instance MonadFix__ReaderT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

(* Translating `instance MonadIO__ReaderT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.IO.Class" "MonadIO" unsupported *)

(* Translating `instance MonadZip__ReaderT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Zip" "MonadZip" unsupported *)

Definition ask {m} {r} `{(GHC.Base.Monad m)} : ReaderT r m r :=
  Mk_ReaderT GHC.Base.return_.

Definition asks {m} {r} {a} `{(GHC.Base.Monad m)} : (r -> a) -> ReaderT r m a :=
  fun f => Mk_ReaderT (GHC.Base.return_ GHC.Base.∘ f).

Definition liftCallCC {m} {a} {b} {r}
   : Control.Monad.Signatures.CallCC m a b ->
     Control.Monad.Signatures.CallCC (ReaderT r m) a b :=
  fun callCC f =>
    Mk_ReaderT (fun r =>
                  callCC (fun c =>
                            runReaderT (f (Mk_ReaderT GHC.Base.∘ (GHC.Base.const GHC.Base.∘ c))) r)).

Definition liftReaderT {m} {a} {r} : m a -> ReaderT r m a :=
  fun m => Mk_ReaderT (GHC.Base.const m).

Local Definition MonadTrans__ReaderT_lift {inst_r}
   : forall {m} {a} `{GHC.Base.Monad m}, m a -> (ReaderT inst_r) m a :=
  fun {m} {a} `{GHC.Base.Monad m} => liftReaderT.

Program Instance MonadTrans__ReaderT {r}
   : Control.Monad.Trans.Class.MonadTrans (ReaderT r) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{GHC.Base.Monad m} =>
           MonadTrans__ReaderT_lift |}.

Local Definition Applicative__ReaderT_pure {inst_m} {inst_r}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a}, a -> (ReaderT inst_r inst_m) a :=
  fun {a} => liftReaderT GHC.Base.∘ GHC.Base.pure.

Definition mapReaderT {m} {a} {n} {b} {r}
   : (m a -> n b) -> ReaderT r m a -> ReaderT r n b :=
  fun f m => Mk_ReaderT (f GHC.Base.∘ runReaderT m).

Definition mapReader {a} {b} {r} : (a -> b) -> Reader r a -> Reader r b :=
  fun f => mapReaderT (Mk_Identity GHC.Base.∘ (f GHC.Base.∘ runIdentity)).

Local Definition Functor__ReaderT_fmap {inst_m} {inst_r} `{(GHC.Base.Functor
   inst_m)}
   : forall {a} {b},
     (a -> b) -> (ReaderT inst_r inst_m) a -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} => fun f => mapReaderT (GHC.Base.fmap f).

Local Definition Functor__ReaderT_op_zlzd__ {inst_m} {inst_r}
  `{(GHC.Base.Functor inst_m)}
   : forall {a} {b},
     a -> (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) a :=
  fun {a} {b} => fun x => Functor__ReaderT_fmap (GHC.Base.const x).

Program Instance Functor__ReaderT {m} {r} `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (ReaderT r m) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__ReaderT_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__ReaderT_fmap |}.

Local Definition Applicative__ReaderT_op_ztzg__ {inst_m} {inst_r}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) a ->
     (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__ReaderT_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x)
                                       y.

Program Instance Applicative__ReaderT {m} {r} `{(GHC.Base.Applicative m)}
   : GHC.Base.Applicative (ReaderT r m) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__ReaderT_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__ReaderT_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__ReaderT_pure |}.

Local Definition Monad__ReaderT_op_zgzg__ {inst_m} {inst_r} `{(GHC.Base.Monad
   inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) a ->
     (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__ReaderT_return_ {inst_m} {inst_r} `{(GHC.Base.Monad
   inst_m)}
   : forall {a}, a -> (ReaderT inst_r inst_m) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__ReaderT {m} {r} `{(GHC.Base.Monad m)}
   : GHC.Base.Monad (ReaderT r m) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__ReaderT_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__ReaderT_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__ReaderT_return_ |}.

Definition reader {m} {r} {a} `{(GHC.Base.Monad m)}
   : (r -> a) -> ReaderT r m a :=
  fun f => Mk_ReaderT (GHC.Base.return_ GHC.Base.∘ f).

Definition runReader {r} {a} : Reader r a -> r -> a :=
  fun m => runIdentity GHC.Base.∘ runReaderT m.

Definition withReaderT {r'} {r} {m} {a}
   : (r' -> r) -> ReaderT r m a -> ReaderT r' m a :=
  fun f m => Mk_ReaderT (runReaderT m GHC.Base.∘ f).

Definition withReader {r'} {r} {a} : (r' -> r) -> Reader r a -> Reader r' a :=
  withReaderT.

Definition local {r} {m} {a} : (r -> r) -> ReaderT r m a -> ReaderT r m a :=
  withReaderT.

(* Unbound variables:
     Identity Mk_Identity Type runIdentity Control.Monad.Signatures.CallCC
     Control.Monad.Trans.Class.MonadTrans GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.const GHC.Base.fmap GHC.Base.id GHC.Base.op_z2218U__
     GHC.Base.op_zgzgze__ GHC.Base.op_zlztzg__ GHC.Base.op_ztzg__ GHC.Base.pure
     GHC.Base.return_
*)
