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
Require Data.Tuple.
Require Import GHC.Base.

(* Converted type declarations: *)

Inductive StateT s m a : Type
  := Mk_StateT : (s -> m (a * s)%type) -> StateT s m a.

Definition State s :=
  (StateT s Identity)%type.

Arguments Mk_StateT {_} {_} {_} _.

Definition runStateT {s} {m} {a} (arg_0__ : StateT s m a) :=
  let 'Mk_StateT runStateT := arg_0__ in
  runStateT.
(* Converted value declarations: *)

Local Definition Functor__StateT_fmap {inst_m} {inst_s} `{(Functor inst_m)}
   : forall {a} {b},
     (a -> b) -> (StateT inst_s inst_m) a -> (StateT inst_s inst_m) b :=
  fun {a} {b} =>
    fun f m =>
      Mk_StateT (fun s =>
                   fmap (fun arg_0__ => let 'pair a s' := arg_0__ in pair (f a) s') (runStateT m
                                                                                               s)).

Local Definition Functor__StateT_op_zlzd__ {inst_m} {inst_s} `{(Functor inst_m)}
   : forall {a} {b}, a -> (StateT inst_s inst_m) b -> (StateT inst_s inst_m) a :=
  fun {a} {b} => fun x => Functor__StateT_fmap (const x).

Program Instance Functor__StateT {m} {s} `{(Functor m)}
   : Functor (StateT s m) :=
  fun _ k =>
    k {| op_zlzd____ := fun {a} {b} => Functor__StateT_op_zlzd__ ;
         fmap__ := fun {a} {b} => Functor__StateT_fmap |}.

Local Definition Applicative__StateT_op_zlztzg__ {inst_m} {inst_s} `{Functor
  inst_m} `{Monad inst_m}
   : forall {a} {b},
     (StateT inst_s inst_m) (a -> b) ->
     (StateT inst_s inst_m) a -> (StateT inst_s inst_m) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_StateT mf, Mk_StateT mx =>
          Mk_StateT (fun s =>
                       let cont_2__ arg_3__ :=
                         let 'pair f s' := arg_3__ in
                         let cont_4__ arg_5__ :=
                           let 'pair x s'' := arg_5__ in
                           return_ (pair (f x) s'') in
                         mx s' >>= cont_4__ in
                       mf s >>= cont_2__)
      end.

Local Definition Applicative__StateT_pure {inst_m} {inst_s} `{Functor inst_m}
  `{Monad inst_m}
   : forall {a}, a -> (StateT inst_s inst_m) a :=
  fun {a} => fun a => Mk_StateT (fun s => return_ (pair a s)).

Definition Applicative__StateT_op_ztzg__ {inst_m} {inst_s} `{_ : Functor inst_m}
  `{_ : Monad inst_m}
   : forall {a} {b},
     StateT inst_s inst_m a -> StateT inst_s inst_m b -> StateT inst_s inst_m b :=
  fun {a} {b} =>
    fun m k =>
      Applicative__StateT_op_zlztzg__ (Applicative__StateT_op_zlztzg__
                                       (Applicative__StateT_pure (fun x y => x)) k) m.

Program Instance Applicative__StateT {m} {s} `{Functor m} `{Monad m}
   : Applicative (StateT s m) :=
  fun _ k =>
    k {| op_ztzg____ := fun {a} {b} => Applicative__StateT_op_ztzg__ ;
         op_zlztzg____ := fun {a} {b} => Applicative__StateT_op_zlztzg__ ;
         pure__ := fun {a} => Applicative__StateT_pure |}.

(* Translating `instance Alternative__StateT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Monad__StateT_op_zgzg__ {inst_m} {inst_s} `{(Monad inst_m)}
   : forall {a} {b},
     (StateT inst_s inst_m) a ->
     (StateT inst_s inst_m) b -> (StateT inst_s inst_m) b :=
  fun {a} {b} => _*>_.

Local Definition Monad__StateT_op_zgzgze__ {inst_m} {inst_s} `{(Monad inst_m)}
   : forall {a} {b},
     (StateT inst_s inst_m) a ->
     (a -> (StateT inst_s inst_m) b) -> (StateT inst_s inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_StateT (fun s =>
                   let cont_0__ arg_1__ := let 'pair a s' := arg_1__ in runStateT (k a) s' in
                   runStateT m s >>= cont_0__).

Local Definition Monad__StateT_return_ {inst_m} {inst_s} `{(Monad inst_m)}
   : forall {a}, a -> (StateT inst_s inst_m) a :=
  fun {a} => pure.

Program Instance Monad__StateT {m} {s} `{(Monad m)} : Monad (StateT s m) :=
  fun _ k =>
    k {| op_zgzg____ := fun {a} {b} => Monad__StateT_op_zgzg__ ;
         op_zgzgze____ := fun {a} {b} => Monad__StateT_op_zgzgze__ ;
         return___ := fun {a} => Monad__StateT_return_ |}.

(* Translating `instance MonadFail__StateT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

(* Translating `instance MonadPlus__StateT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "MonadPlus" unsupported *)

(* Translating `instance MonadFix__StateT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

Local Definition MonadTrans__StateT_lift {inst_s}
   : forall {m} {a} `{Monad m}, m a -> (StateT inst_s) m a :=
  fun {m} {a} `{Monad m} =>
    fun m => Mk_StateT (fun s => m >>= (fun a => return_ (pair a s))).

Program Instance MonadTrans__StateT {s}
   : Control.Monad.Trans.Class.MonadTrans (StateT s) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{Monad m} =>
           MonadTrans__StateT_lift |}.

(* Translating `instance MonadIO__StateT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.IO.Class" "MonadIO" unsupported *)

Definition evalStateT {m} {s} {a} `{(Monad m)} : StateT s m a -> s -> m a :=
  fun m s =>
    let cont_0__ arg_1__ := let 'pair a _ := arg_1__ in return_ a in
    runStateT m s >>= cont_0__.

Definition execStateT {m} {s} {a} `{(Monad m)} : StateT s m a -> s -> m s :=
  fun m s =>
    let cont_0__ arg_1__ := let 'pair _ s' := arg_1__ in return_ s' in
    runStateT m s >>= cont_0__.

Definition liftCallCC {m} {a} {s} {b}
   : Control.Monad.Signatures.CallCC m (a * s)%type (b * s)%type ->
     Control.Monad.Signatures.CallCC (StateT s m) a b :=
  fun callCC f =>
    Mk_StateT (fun s =>
                 callCC (fun c =>
                           runStateT (f (fun a => Mk_StateT (fun arg_0__ => c (pair a s)))) s)).

Definition liftCallCC' {m} {a} {s} {b}
   : Control.Monad.Signatures.CallCC m (a * s)%type (b * s)%type ->
     Control.Monad.Signatures.CallCC (StateT s m) a b :=
  fun callCC f =>
    Mk_StateT (fun s =>
                 callCC (fun c =>
                           runStateT (f (fun a => Mk_StateT (fun s' => c (pair a s')))) s)).

Definition liftListen {m} {w} {a} {s} `{(Monad m)}
   : Control.Monad.Signatures.Listen w m (a * s)%type ->
     Control.Monad.Signatures.Listen w (StateT s m) a :=
  fun listen m =>
    Mk_StateT (fun s =>
                 let cont_0__ arg_1__ :=
                   let 'pair (pair a s') w := arg_1__ in
                   return_ (pair (pair a w) s') in
                 listen (runStateT m s) >>= cont_0__).

Definition liftPass {m} {w} {a} {s} `{(Monad m)}
   : Control.Monad.Signatures.Pass w m (a * s)%type ->
     Control.Monad.Signatures.Pass w (StateT s m) a :=
  fun pass m =>
    Mk_StateT (fun s =>
                 pass (let cont_0__ arg_1__ :=
                         let 'pair (pair a f) s' := arg_1__ in
                         return_ (pair (pair a s') f) in
                       runStateT m s >>= cont_0__)).

Definition mapStateT {m} {a} {s} {n} {b}
   : (m (a * s)%type -> n (b * s)%type) -> StateT s m a -> StateT s n b :=
  fun f m => Mk_StateT (_∘_ f (runStateT m)).

Definition mapState {a} {s} {b}
   : ((a * s)%type -> (b * s)%type) -> State s a -> State s b :=
  fun f => mapStateT (Mk_Identity ∘ (f ∘ runIdentity)).

Definition runState {s} {a} : State s a -> s -> (a * s)%type :=
  fun m => runIdentity ∘ runStateT m.

Definition execState {s} {a} : State s a -> s -> s :=
  fun m s => Data.Tuple.snd (runState m s).

Definition evalState {s} {a} : State s a -> s -> a :=
  fun m s => Data.Tuple.fst (runState m s).

Definition state {m} {s} {a} `{(Monad m)}
   : (s -> (a * s)%type) -> StateT s m a :=
  fun f => Mk_StateT (return_ ∘ f).

Definition put {m} {s} `{(Monad m)} : s -> StateT s m unit :=
  fun s => state (fun arg_0__ => pair tt s).

Definition modify {m} {s} `{(Monad m)} : (s -> s) -> StateT s m unit :=
  fun f => state (fun s => pair tt (f s)).

Definition gets {m} {s} {a} `{(Monad m)} : (s -> a) -> StateT s m a :=
  fun f => state (fun s => pair (f s) s).

Definition get {m} {s} `{(Monad m)} : StateT s m s :=
  state (fun s => pair s s).

Definition modify' {m} {s} `{(Monad m)} : (s -> s) -> StateT s m unit :=
  fun f => get >>= (fun s => put (f s)).

Definition withStateT {s} {m} {a} : (s -> s) -> StateT s m a -> StateT s m a :=
  fun f m => Mk_StateT (_∘_ (runStateT m) f).

Definition withState {s} {a} : (s -> s) -> State s a -> State s a :=
  withStateT.

(* Unbound variables:
     Applicative Functor Identity Mk_Identity Monad const fmap op_z2218U__
     op_zgzgze__ op_zt__ op_ztzg__ pair pure return_ runIdentity tt unit
     Control.Monad.Signatures.CallCC Control.Monad.Signatures.Listen
     Control.Monad.Signatures.Pass Control.Monad.Trans.Class.MonadTrans
     Data.Tuple.fst Data.Tuple.snd
*)
