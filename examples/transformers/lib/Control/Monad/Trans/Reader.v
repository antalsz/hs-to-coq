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
Require Data.Functor.Identity.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ReaderT (r : Type) (m : Type -> Type) a : Type
  := | Mk_ReaderT (runReaderT : r -> m a) : ReaderT r m a.

Definition Reader r :=
  (ReaderT r Data.Functor.Identity.Identity)%type.

Arguments Mk_ReaderT {_} {_} {_} _.

Definition runReaderT {r : Type} {m : Type -> Type} {a} (arg_0__
    : ReaderT r m a) :=
  let 'Mk_ReaderT runReaderT := arg_0__ in
  runReaderT.

(* Converted value declarations: *)

Definition withReaderT {r'} {r} {m} {a}
   : (r' -> r) -> ReaderT r m a -> ReaderT r' m a :=
  fun f m => Mk_ReaderT (runReaderT m GHC.Base.∘ f).

Definition withReader {r'} {r} {a} : (r' -> r) -> Reader r a -> Reader r' a :=
  withReaderT.

Definition runReader {r} {a} : Reader r a -> r -> a :=
  fun m => Data.Functor.Identity.runIdentity GHC.Base.∘ runReaderT m.

Definition reader {m} {r} {a} `{(GHC.Base.Monad m)}
   : (r -> a) -> ReaderT r m a :=
  fun f => Mk_ReaderT (GHC.Base.return_ GHC.Base.∘ f).

Definition mapReaderT {m} {a} {n} {b} {r}
   : (m a -> n b) -> ReaderT r m a -> ReaderT r n b :=
  fun f m => Mk_ReaderT (f GHC.Base.∘ runReaderT m).

Definition mapReader {a} {b} {r} : (a -> b) -> Reader r a -> Reader r b :=
  fun f =>
    mapReaderT (Data.Functor.Identity.Mk_Identity GHC.Base.∘
                (f GHC.Base.∘ Data.Functor.Identity.runIdentity)).

Definition local {r} {m} {a} : (r -> r) -> ReaderT r m a -> ReaderT r m a :=
  withReaderT.

Definition liftReaderT {m} {a} {r} : m a -> ReaderT r m a :=
  fun m => Mk_ReaderT (GHC.Base.const m).

Definition liftCallCC {m} {a} {b} {r}
   : Control.Monad.Signatures.CallCC m a b ->
     Control.Monad.Signatures.CallCC (ReaderT r m) a b :=
  fun callCC f =>
    Mk_ReaderT (fun r =>
                  callCC (fun c =>
                            runReaderT (f (Mk_ReaderT GHC.Base.∘ (GHC.Base.const GHC.Base.∘ c))) r)).

Definition asks {m} {r} {a} `{(GHC.Base.Monad m)} : (r -> a) -> ReaderT r m a :=
  fun f => Mk_ReaderT (GHC.Base.return_ GHC.Base.∘ f).

Definition ask {m} {r} `{(GHC.Base.Monad m)} : ReaderT r m r :=
  Mk_ReaderT GHC.Base.return_.

(* Skipping all instances of class `Control.Monad.Zip.MonadZip', including
   `Control.Monad.Trans.Reader.MonadZip__ReaderT' *)

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `Control.Monad.Trans.Reader.MonadIO__ReaderT' *)

Local Definition MonadTrans__ReaderT_lift {inst_r}
   : forall {m} {a}, forall `{(GHC.Base.Monad m)}, m a -> (ReaderT inst_r) m a :=
  fun {m} {a} `{(GHC.Base.Monad m)} => liftReaderT.

Program Instance MonadTrans__ReaderT {r}
   : Control.Monad.Trans.Class.MonadTrans (ReaderT r) :=
  fun _ k__ =>
    k__ {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{(GHC.Base.Monad m)} =>
             MonadTrans__ReaderT_lift |}.

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Control.Monad.Trans.Reader.MonadFix__ReaderT' *)

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Monad.Trans.Reader.MonadPlus__ReaderT' *)

Local Definition Applicative__ReaderT_op_zlztzg__ {inst_m} {inst_r}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) (a -> b) ->
     (ReaderT inst_r inst_m) a -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} =>
    fun f v => Mk_ReaderT (fun r => runReaderT f r GHC.Base.<*> runReaderT v r).

Local Definition Functor__ReaderT_fmap {inst_m} {inst_r} `{(GHC.Base.Functor
   inst_m)}
   : forall {a} {b},
     (a -> b) -> (ReaderT inst_r inst_m) a -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} => fun f => mapReaderT (GHC.Base.fmap f).

Local Definition Functor__ReaderT_op_zlzd__ {inst_m} {inst_r}
  `{(GHC.Base.Functor inst_m)}
   : forall {a} {b},
     a -> (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) a :=
  fun {a} {b} => fun x v => mapReaderT (fun arg_0__ => x GHC.Base.<$ arg_0__) v.

Program Instance Functor__ReaderT {m} {r} `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (ReaderT r m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__ReaderT_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__ReaderT_op_zlzd__ |}.

Local Definition Applicative__ReaderT_liftA2 {inst_m} {inst_r}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (ReaderT inst_r inst_m) a ->
     (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__ReaderT_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__ReaderT_op_ztzg__ {inst_m} {inst_r}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) a ->
     (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} =>
    fun u v => Mk_ReaderT (fun r => runReaderT u r GHC.Base.*> runReaderT v r).

Local Definition Applicative__ReaderT_pure {inst_m} {inst_r}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a}, a -> (ReaderT inst_r inst_m) a :=
  fun {a} => liftReaderT GHC.Base.∘ GHC.Base.pure.

Program Instance Applicative__ReaderT {m} {r} `{(GHC.Base.Applicative m)}
   : GHC.Base.Applicative (ReaderT r m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__ReaderT_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__ReaderT_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__ReaderT_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__ReaderT_pure |}.

Local Definition Monad__ReaderT_op_zgzg__ {inst_m} {inst_r} `{(GHC.Base.Monad
   inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) a ->
     (ReaderT inst_r inst_m) b -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__ReaderT_op_zgzgze__ {inst_m} {inst_r} `{(GHC.Base.Monad
   inst_m)}
   : forall {a} {b},
     (ReaderT inst_r inst_m) a ->
     (a -> (ReaderT inst_r inst_m) b) -> (ReaderT inst_r inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_ReaderT (fun r => runReaderT m r GHC.Base.>>= (fun a => runReaderT (k a) r)).

Local Definition Monad__ReaderT_return_ {inst_m} {inst_r} `{(GHC.Base.Monad
   inst_m)}
   : forall {a}, a -> (ReaderT inst_r inst_m) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__ReaderT {m} {r} `{(GHC.Base.Monad m)}
   : GHC.Base.Monad (ReaderT r m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__ReaderT_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__ReaderT_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__ReaderT_return_ |}.

Local Definition MonadFail__ReaderT_fail {inst_m} {inst_r}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a}, GHC.Base.String -> (ReaderT inst_r inst_m) a :=
  fun {a} =>
    fun msg => Control.Monad.Trans.Class.lift (Control.Monad.Fail.fail msg).

Program Instance MonadFail__ReaderT {m} {r} `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (ReaderT r m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun {a} => MonadFail__ReaderT_fail |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Monad.Trans.Reader.Alternative__ReaderT' *)

(* External variables:
     Type Control.Monad.Fail.MonadFail Control.Monad.Fail.fail
     Control.Monad.Fail.fail__ Control.Monad.Signatures.CallCC
     Control.Monad.Trans.Class.MonadTrans Control.Monad.Trans.Class.lift
     Control.Monad.Trans.Class.lift__ Data.Functor.Identity.Identity
     Data.Functor.Identity.Mk_Identity Data.Functor.Identity.runIdentity
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.String
     GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.liftA2__
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__
     GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg__
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return_
     GHC.Base.return___
*)
