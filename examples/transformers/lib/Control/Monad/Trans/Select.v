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
Require Control.Monad.Trans.Cont.
Require Import Data.Functor.Identity.
Require Import GHC.Base.

(* Converted type declarations: *)

Inductive SelectT r m a : Type
  := Mk_SelectT : ((a -> m r) -> m a) -> SelectT r m a.

Definition Select r :=
  (SelectT r Identity)%type.

Arguments Mk_SelectT {_} {_} {_} _.
(* Converted value declarations: *)

Local Definition Functor__SelectT_fmap {inst_m} {inst_r} `{(Functor inst_m)}
   : forall {a} {b},
     (a -> b) -> (SelectT inst_r inst_m) a -> (SelectT inst_r inst_m) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_SelectT g => Mk_SelectT (fmap f ∘ (g ∘ (fun arg_2__ => arg_2__ ∘ f)))
      end.

Local Definition Functor__SelectT_op_zlzd__ {inst_m} {inst_r} `{(Functor
   inst_m)}
   : forall {a} {b},
     a -> (SelectT inst_r inst_m) b -> (SelectT inst_r inst_m) a :=
  fun {a} {b} => fun x => Functor__SelectT_fmap (const x).

Local Definition Applicative__SelectT_op_zlztzg__ {inst_m} {inst_r} `{Functor
  inst_m} `{Monad inst_m}
   : forall {a} {b},
     (SelectT inst_r inst_m) (a -> b) ->
     (SelectT inst_r inst_m) a -> (SelectT inst_r inst_m) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_SelectT gf, Mk_SelectT gx =>
          Mk_SelectT (fun k =>
                        let h := fun f => liftM f (gx (k ∘ f)) in
                        gf ((fun arg_3__ => arg_3__ >>= k) ∘ h) >>= (fun f => h f))
      end.

(* Translating `instance Alternative__SelectT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

(* Translating `instance MonadFail__SelectT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

(* Translating `instance MonadPlus__SelectT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "MonadPlus" unsupported *)

Local Definition MonadTrans__SelectT_lift {inst_r}
   : forall {m} {a} `{Monad m}, m a -> (SelectT inst_r) m a :=
  fun {m} {a} `{Monad m} => Mk_SelectT ∘ const.

Program Instance MonadTrans__SelectT {r}
   : Control.Monad.Trans.Class.MonadTrans (SelectT r) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{Monad m} =>
           MonadTrans__SelectT_lift |}.

Program Instance Functor__SelectT {m} {r} `{(Functor m)}
   : Functor (SelectT r m) :=
  fun _ k =>
    k {| op_zlzd____ := fun {a} {b} => Functor__SelectT_op_zlzd__ ;
         fmap__ := fun {a} {b} => Functor__SelectT_fmap |}.

Local Definition Applicative__SelectT_pure {inst_m} {inst_r} `{Functor inst_m}
  `{Monad inst_m}
   : forall {a}, a -> (SelectT inst_r inst_m) a :=
  fun {a} => Control.Monad.Trans.Class.lift ∘ return_.

Definition Applicative__SelectT_op_ztzg__ {inst_m} {inst_s} `{_ : Monad inst_m}
   : forall {a} {b},
     SelectT inst_s inst_m a -> SelectT inst_s inst_m b -> SelectT inst_s inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Applicative__SelectT_op_zlztzg__ (Applicative__SelectT_op_zlztzg__
                                        (Applicative__SelectT_pure (fun x y => x)) k) m.

Program Instance Applicative__SelectT {m} {r} `{Functor m} `{Monad m}
   : Applicative (SelectT r m) :=
  fun _ k =>
    k {| op_ztzg____ := fun {a} {b} => Applicative__SelectT_op_ztzg__ ;
         op_zlztzg____ := fun {a} {b} => Applicative__SelectT_op_zlztzg__ ;
         pure__ := fun {a} => Applicative__SelectT_pure |}.

Local Definition Monad__SelectT_op_zgzg__ {inst_m} {inst_r} `{(Monad inst_m)}
   : forall {a} {b},
     (SelectT inst_r inst_m) a ->
     (SelectT inst_r inst_m) b -> (SelectT inst_r inst_m) b :=
  fun {a} {b} => _*>_.

Local Definition Monad__SelectT_return_ {inst_m} {inst_r} `{(Monad inst_m)}
   : forall {a}, a -> (SelectT inst_r inst_m) a :=
  fun {a} => pure.

(* Translating `instance MonadIO__SelectT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.IO.Class" "MonadIO" unsupported *)

Definition runSelectT {r} {m} {a} : SelectT r m a -> (a -> m r) -> m a :=
  fun arg_0__ => let 'Mk_SelectT g := arg_0__ in g.

Definition runSelect {r} {a} : Select r a -> (a -> r) -> a :=
  fun m k => runIdentity (runSelectT m (Mk_Identity ∘ k)).

Definition mapSelectT {m} {a} {r}
   : (m a -> m a) -> SelectT r m a -> SelectT r m a :=
  fun f m => Mk_SelectT (_∘_ f (runSelectT m)).

Definition mapSelect {a} {r} : (a -> a) -> Select r a -> Select r a :=
  fun f => mapSelectT (Mk_Identity ∘ (f ∘ runIdentity)).

Local Definition Monad__SelectT_op_zgzgze__ {inst_m} {inst_r} `{(Monad inst_m)}
   : forall {a} {b},
     (SelectT inst_r inst_m) a ->
     (a -> (SelectT inst_r inst_m) b) -> (SelectT inst_r inst_m) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_SelectT g, f =>
          Mk_SelectT (fun k =>
                        let h := fun x => runSelectT (f x) k in
                        g ((fun arg_3__ => arg_3__ >>= k) ∘ h) >>= (fun y => h y))
      end.

Program Instance Monad__SelectT {m} {r} `{(Monad m)} : Monad (SelectT r m) :=
  fun _ k =>
    k {| op_zgzg____ := fun {a} {b} => Monad__SelectT_op_zgzg__ ;
         op_zgzgze____ := fun {a} {b} => Monad__SelectT_op_zgzgze__ ;
         return___ := fun {a} => Monad__SelectT_return_ |}.

Definition select {a} {r} : ((a -> r) -> a) -> Select r a :=
  fun f => Mk_SelectT (fun k => Mk_Identity (f (runIdentity ∘ k))).

Definition selectToContT {m} {r} {a} `{(Monad m)}
   : SelectT r m a -> Control.Monad.Trans.Cont.ContT r m a :=
  fun arg_0__ =>
    let 'Mk_SelectT g := arg_0__ in
    Control.Monad.Trans.Cont.Mk_ContT (fun k => g k >>= k).

Definition selectToCont {m} {r} {a} `{(Monad m)}
   : SelectT r m a -> Control.Monad.Trans.Cont.ContT r m a :=
  selectToContT.

(* Unbound variables:
     Applicative Functor Identity Mk_Identity Monad const fmap liftM op_z2218U__
     op_zgzgze__ op_ztzg__ pure return_ runIdentity
     Control.Monad.Trans.Class.MonadTrans Control.Monad.Trans.Class.lift
     Control.Monad.Trans.Cont.ContT Control.Monad.Trans.Cont.Mk_ContT
*)
