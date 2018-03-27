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
Require Import GHC.Base.

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
  `{(Applicative inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) (a -> b) ->
     (ReaderT inst_r inst_m) a -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} =>
    fun f v => Mk_ReaderT (fun r => runReaderT f r <*> runReaderT v r).

Local Definition Applicative__ReaderT_op_ztzg__ {inst_m} {inst_r} `{(Applicative
   inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) a ->
     (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} =>
    fun u v => Mk_ReaderT (fun r => runReaderT u r *> runReaderT v r).

(* Translating `instance Alternative__ReaderT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Monad__ReaderT_op_zgzgze__ {inst_m} {inst_r} `{(Monad inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) a ->
     (a -> (ReaderT inst_r inst_m) b) -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_ReaderT (fun r => runReaderT m r >>= (fun a => runReaderT (k a) r)).

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

Definition ask {m} {r} `{(Monad m)} : ReaderT r m r :=
  Mk_ReaderT return_.

Definition asks {m} {r} {a} `{(Monad m)} : (r -> a) -> ReaderT r m a :=
  fun f => Mk_ReaderT (return_ ∘ f).

Definition liftCallCC {m} {a} {b} {r}
   : Control.Monad.Signatures.CallCC m a b ->
     Control.Monad.Signatures.CallCC (ReaderT r m) a b :=
  fun callCC f =>
    Mk_ReaderT (fun r =>
                  callCC (fun c => runReaderT (f (Mk_ReaderT ∘ (const ∘ c))) r)).

Definition liftReaderT {m} {a} {r} : m a -> ReaderT r m a :=
  fun m => Mk_ReaderT (const m).

Local Definition MonadTrans__ReaderT_lift {inst_r}
   : forall {m} {a} `{Monad m}, m a -> (ReaderT inst_r) m a :=
  fun {m} {a} `{Monad m} => liftReaderT.

Program Instance MonadTrans__ReaderT {r}
   : Control.Monad.Trans.Class.MonadTrans (ReaderT r) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{Monad m} =>
           MonadTrans__ReaderT_lift |}.

Local Definition Applicative__ReaderT_pure {inst_m} {inst_r} `{(Applicative
   inst_m)}
   : forall {a}, a -> (ReaderT inst_r inst_m) a :=
  fun {a} => liftReaderT ∘ pure.

Definition mapReaderT {m} {a} {n} {b} {r}
   : (m a -> n b) -> ReaderT r m a -> ReaderT r n b :=
  fun f m => Mk_ReaderT (_∘_ f (runReaderT m)).

Definition mapReader {a} {b} {r} : (a -> b) -> Reader r a -> Reader r b :=
  fun f => mapReaderT (Mk_Identity ∘ (f ∘ runIdentity)).

Local Definition Functor__ReaderT_op_zlzd__ {inst_m} {inst_r} `{(Functor
   inst_m)}
   : forall {a} {b},
     a -> (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) a :=
  fun {a} {b} => fun x v => mapReaderT (fun arg_0__ => x <$ arg_0__) v.

Local Definition Functor__ReaderT_fmap {inst_m} {inst_r} `{(Functor inst_m)}
   : forall {a} {b},
     (a -> b) -> (ReaderT inst_r inst_m) a -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} => fun f => mapReaderT (fmap f).

Program Instance Functor__ReaderT {m} {r} `{(Functor m)}
   : Functor (ReaderT r m) :=
  fun _ k =>
    k {| op_zlzd____ := fun {a} {b} => Functor__ReaderT_op_zlzd__ ;
         fmap__ := fun {a} {b} => Functor__ReaderT_fmap |}.

Program Instance Applicative__ReaderT {m} {r} `{(Applicative m)}
   : Applicative (ReaderT r m) :=
  fun _ k =>
    k {| op_ztzg____ := fun {a} {b} => Applicative__ReaderT_op_ztzg__ ;
         op_zlztzg____ := fun {a} {b} => Applicative__ReaderT_op_zlztzg__ ;
         pure__ := fun {a} => Applicative__ReaderT_pure |}.

Local Definition Monad__ReaderT_op_zgzg__ {inst_m} {inst_r} `{(Monad inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) a ->
     (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} => _*>_.

Local Definition Monad__ReaderT_return_ {inst_m} {inst_r} `{(Monad inst_m)}
   : forall {a}, a -> (ReaderT inst_r inst_m) a :=
  fun {a} => pure.

Program Instance Monad__ReaderT {m} {r} `{(Monad m)} : Monad (ReaderT r m) :=
  fun _ k =>
    k {| op_zgzg____ := fun {a} {b} => Monad__ReaderT_op_zgzg__ ;
         op_zgzgze____ := fun {a} {b} => Monad__ReaderT_op_zgzgze__ ;
         return___ := fun {a} => Monad__ReaderT_return_ |}.

Definition reader {m} {r} {a} `{(Monad m)} : (r -> a) -> ReaderT r m a :=
  fun f => Mk_ReaderT (return_ ∘ f).

Definition runReader {r} {a} : Reader r a -> r -> a :=
  fun m => runIdentity ∘ runReaderT m.

Definition withReaderT {r'} {r} {m} {a}
   : (r' -> r) -> ReaderT r m a -> ReaderT r' m a :=
  fun f m => Mk_ReaderT (_∘_ (runReaderT m) f).

Definition withReader {r'} {r} {a} : (r' -> r) -> Reader r a -> Reader r' a :=
  withReaderT.

Definition local {r} {m} {a} : (r -> r) -> ReaderT r m a -> ReaderT r m a :=
  withReaderT.

(* Unbound variables:
     Applicative Functor Identity Mk_Identity Monad Type const fmap op_z2218U__
     op_zgzgze__ op_zlzd__ op_zlztzg__ op_ztzg__ pure return_ runIdentity
     Control.Monad.Signatures.CallCC Control.Monad.Trans.Class.MonadTrans
*)
