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
Require Control.Monad.Trans.Reader.
Require Control.Monad.Trans.State.Lazy.
Require Control.Monad.Trans.Writer.Lazy.
Require Import Data.Functor.Identity.
Require Data.Tuple.
Require Import GHC.Base.

(* Converted type declarations: *)

Inductive AccumT w m a : Type
  := Mk_AccumT : (w -> m (a * w)%type) -> AccumT w m a.

Definition Accum w :=
  (AccumT w Identity)%type.

Arguments Mk_AccumT {_} {_} {_} _.
(* Midamble *)

Import Notations.

Definition runAccumT {w} {m} {a} : AccumT w m a -> w -> m (a * w)%type :=
  fun arg_0__ => let 'Mk_AccumT f := arg_0__ in f.

Local Definition Monad__AccumT_tmp {inst_w} {inst_m} `{GHC.Base.Monoid
  inst_w} `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (AccumT inst_w inst_m) a ->
     (a -> (AccumT inst_w inst_m) b) -> (AccumT inst_w inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_AccumT (fun w =>
                   let cont_0__ arg_1__ :=
                     let 'pair a w' := arg_1__ in
                     let cont_2__ arg_3__ :=
                       let 'pair b w'' := arg_3__ in
                       GHC.Base.return_ (pair b (GHC.Base.mappend w' w'')) in
                     runAccumT (k a) (GHC.Base.mappend w w') GHC.Base.>>= cont_2__ in
                   runAccumT m w GHC.Base.>>= cont_0__).
(* Converted value declarations: *)

Local Definition Applicative__AccumT_op_zlztzg__ {inst_w} {inst_m} `{Monoid
  inst_w} `{Functor inst_m} `{Monad inst_m}
   : forall {a} {b},
     (AccumT inst_w inst_m) (a -> b) ->
     (AccumT inst_w inst_m) a -> (AccumT inst_w inst_m) b :=
  fun {a} {b} =>
    fun mf mv =>
      Mk_AccumT (fun w =>
                   let cont_0__ arg_1__ :=
                     let 'pair f w' := arg_1__ in
                     let cont_2__ arg_3__ :=
                       let 'pair v w'' := arg_3__ in
                       return_ (pair (f v) (mappend w' w'')) in
                     runAccumT mv (mappend w w') >>= cont_2__ in
                   runAccumT mf w >>= cont_0__).

Local Definition Applicative__AccumT_pure {inst_w} {inst_m} `{Monoid inst_w}
  `{Functor inst_m} `{Monad inst_m}
   : forall {a}, a -> (AccumT inst_w inst_m) a :=
  fun {a} => fun a => Mk_AccumT (const (return_ (pair a mempty))).

(* Translating `instance Alternative__AccumT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Definition Monad__AccumT_op_zgzgze__ {inst_w} {inst_m} `{_ : Monoid inst_w} `{_
   : Monad inst_m}
   : forall {a} {b},
     AccumT inst_w inst_m a ->
     (a -> AccumT inst_w inst_m b) -> AccumT inst_w inst_m b :=
  fun {a} {b} => Monad__AccumT_tmp.

(* Translating `instance MonadFail__AccumT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

(* Translating `instance MonadPlus__AccumT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "MonadPlus" unsupported *)

(* Translating `instance MonadFix__AccumT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

Local Definition MonadTrans__AccumT_lift {inst_w} `{(Monoid inst_w)}
   : forall {m} {a} `{Monad m}, m a -> (AccumT inst_w) m a :=
  fun {m} {a} `{Monad m} =>
    fun m => Mk_AccumT (const (_>>=_ m (fun a => return_ (pair a mempty)))).

Program Instance MonadTrans__AccumT {w} `{(Monoid w)}
   : Control.Monad.Trans.Class.MonadTrans (AccumT w) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{Monad m} =>
           MonadTrans__AccumT_lift |}.

(* Translating `instance MonadIO__AccumT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.IO.Class" "MonadIO" unsupported *)

Definition accum {m} {w} {a} `{(Monad m)}
   : (w -> (a * w)%type) -> AccumT w m a :=
  fun f => Mk_AccumT (fun w => return_ (f w)).

Definition add {m} {w} `{(Monad m)} : w -> AccumT w m unit :=
  fun w => accum (const (pair tt w)).

Definition accumToStateT {m} {s} {a} `{Functor m} `{Monoid s}
   : AccumT s m a -> Control.Monad.Trans.State.Lazy.StateT s m a :=
  fun arg_0__ =>
    let 'Mk_AccumT f := arg_0__ in
    Control.Monad.Trans.State.Lazy.Mk_StateT (fun w =>
                                                fmap (fun arg_1__ => let 'pair a w' := arg_1__ in pair a (mappend w w'))
                                                (f w)).

Definition evalAccumT {m} {w} {a} `{Monad m} `{Monoid w}
   : AccumT w m a -> w -> m a :=
  fun m w =>
    let cont_0__ arg_1__ := let 'pair a _ := arg_1__ in return_ a in
    runAccumT m w >>= cont_0__.

Definition execAccumT {m} {w} {a} `{(Monad m)} : AccumT w m a -> w -> m w :=
  fun m w =>
    let cont_0__ arg_1__ := let 'pair _ w' := arg_1__ in return_ w' in
    runAccumT m w >>= cont_0__.

Definition liftCallCC {m} {a} {w} {b}
   : Control.Monad.Signatures.CallCC m (a * w)%type (b * w)%type ->
     Control.Monad.Signatures.CallCC (AccumT w m) a b :=
  fun callCC f =>
    Mk_AccumT (fun w =>
                 callCC (fun c =>
                           runAccumT (f (fun a => Mk_AccumT (fun arg_0__ => c (pair a w)))) w)).

Definition liftCallCC' {m} {a} {w} {b}
   : Control.Monad.Signatures.CallCC m (a * w)%type (b * w)%type ->
     Control.Monad.Signatures.CallCC (AccumT w m) a b :=
  fun callCC f =>
    Mk_AccumT (fun s =>
                 callCC (fun c =>
                           runAccumT (f (fun a => Mk_AccumT (fun s' => c (pair a s')))) s)).

Definition liftListen {m} {w} {a} {s} `{(Monad m)}
   : Control.Monad.Signatures.Listen w m (a * s)%type ->
     Control.Monad.Signatures.Listen w (AccumT s m) a :=
  fun listen m =>
    Mk_AccumT (fun s =>
                 let cont_0__ arg_1__ :=
                   let 'pair (pair a s') w := arg_1__ in
                   return_ (pair (pair a w) s') in
                 listen (runAccumT m s) >>= cont_0__).

Definition liftPass {m} {w} {a} {s} `{(Monad m)}
   : Control.Monad.Signatures.Pass w m (a * s)%type ->
     Control.Monad.Signatures.Pass w (AccumT s m) a :=
  fun pass m =>
    Mk_AccumT (fun s =>
                 pass (let cont_0__ arg_1__ :=
                         let 'pair (pair a f) s' := arg_1__ in
                         return_ (pair (pair a s') f) in
                       runAccumT m s >>= cont_0__)).

Definition look {w} {m} `{Monoid w} `{Monad m} : AccumT w m w :=
  Mk_AccumT (fun w => return_ (pair w mempty)).

Definition looks {w} {m} {a} `{Monoid w} `{Monad m}
   : (w -> a) -> AccumT w m a :=
  fun f => Mk_AccumT (fun w => return_ (pair (f w) mempty)).

Definition mapAccumT {m} {a} {w} {n} {b}
   : (m (a * w)%type -> n (b * w)%type) -> AccumT w m a -> AccumT w n b :=
  fun f m => Mk_AccumT (f ∘ runAccumT m).

Definition mapAccum {a} {w} {b}
   : ((a * w)%type -> (b * w)%type) -> Accum w a -> Accum w b :=
  fun f => mapAccumT (Mk_Identity ∘ (f ∘ runIdentity)).

Local Definition Functor__AccumT_fmap {inst_m} {inst_w} `{(Functor inst_m)}
   : forall {a} {b},
     (a -> b) -> (AccumT inst_w inst_m) a -> (AccumT inst_w inst_m) b :=
  fun {a} {b} =>
    fun f =>
      mapAccumT (fmap (fun arg_0__ => let 'pair a w := arg_0__ in pair (f a) w)).

Local Definition Functor__AccumT_op_zlzd__ {inst_m} {inst_w} `{(Functor inst_m)}
   : forall {a} {b}, a -> (AccumT inst_w inst_m) b -> (AccumT inst_w inst_m) a :=
  fun {a} {b} => fun x => Functor__AccumT_fmap (const x).

Program Instance Functor__AccumT {m} {w} `{(Functor m)}
   : Functor (AccumT w m) :=
  fun _ k =>
    k {| op_zlzd____ := fun {a} {b} => Functor__AccumT_op_zlzd__ ;
         fmap__ := fun {a} {b} => Functor__AccumT_fmap |}.

Local Definition Applicative__AccumT_op_ztzg__ {inst_w} {inst_m} `{Monoid
  inst_w} `{Functor inst_m} `{Monad inst_m}
   : forall {a} {b},
     (AccumT inst_w inst_m) a ->
     (AccumT inst_w inst_m) b -> (AccumT inst_w inst_m) b :=
  fun {a} {b} => fun x y => Applicative__AccumT_op_zlztzg__ (fmap (const id) x) y.

Program Instance Applicative__AccumT {w} {m} `{Monoid w} `{Functor m} `{Monad m}
   : Applicative (AccumT w m) :=
  fun _ k =>
    k {| op_ztzg____ := fun {a} {b} => Applicative__AccumT_op_ztzg__ ;
         op_zlztzg____ := fun {a} {b} => Applicative__AccumT_op_zlztzg__ ;
         pure__ := fun {a} => Applicative__AccumT_pure |}.

Local Definition Monad__AccumT_op_zgzg__ {inst_w} {inst_m} `{Monoid inst_w}
  `{Functor inst_m} `{Monad inst_m}
   : forall {a} {b},
     (AccumT inst_w inst_m) a ->
     (AccumT inst_w inst_m) b -> (AccumT inst_w inst_m) b :=
  fun {a} {b} => _*>_.

Local Definition Monad__AccumT_return_ {inst_w} {inst_m} `{Monoid inst_w}
  `{Functor inst_m} `{Monad inst_m}
   : forall {a}, a -> (AccumT inst_w inst_m) a :=
  fun {a} => pure.

Program Instance Monad__AccumT {w} {m} `{Monoid w} `{Functor m} `{Monad m}
   : Monad (AccumT w m) :=
  fun _ k =>
    k {| op_zgzg____ := fun {a} {b} => Monad__AccumT_op_zgzg__ ;
         op_zgzgze____ := fun {a} {b} => Monad__AccumT_op_zgzgze__ ;
         return___ := fun {a} => Monad__AccumT_return_ |}.

Definition readerToAccumT {m} {w} {a} `{Functor m} `{Monoid w}
   : Control.Monad.Trans.Reader.ReaderT w m a -> AccumT w m a :=
  fun arg_0__ =>
    let 'Control.Monad.Trans.Reader.Mk_ReaderT f := arg_0__ in
    Mk_AccumT (fun w => fmap (fun a => pair a mempty) (f w)).

Definition runAccum {w} {a} : Accum w a -> w -> (a * w)%type :=
  fun m => runIdentity ∘ runAccumT m.

Definition execAccum {w} {a} : Accum w a -> w -> w :=
  fun m w => Data.Tuple.snd (runAccum m w).

Definition evalAccum {w} {a} `{(Monoid w)} : Accum w a -> w -> a :=
  fun m w => Data.Tuple.fst (runAccum m w).

Definition writerToAccumT {w} {m} {a}
   : Control.Monad.Trans.Writer.Lazy.WriterT w m a -> AccumT w m a :=
  fun arg_0__ =>
    let 'Control.Monad.Trans.Writer.Lazy.Mk_WriterT m := arg_0__ in
    Mk_AccumT (const m).

(* Unbound variables:
     Applicative Functor Identity Mk_Identity Monad Monad__AccumT_tmp Monoid const
     fmap id mappend mempty op_z2218U__ op_zgzgze__ op_zt__ op_ztzg__ pair pure
     return_ runAccumT runIdentity tt unit Control.Monad.Signatures.CallCC
     Control.Monad.Signatures.Listen Control.Monad.Signatures.Pass
     Control.Monad.Trans.Class.MonadTrans Control.Monad.Trans.Reader.Mk_ReaderT
     Control.Monad.Trans.Reader.ReaderT Control.Monad.Trans.State.Lazy.Mk_StateT
     Control.Monad.Trans.State.Lazy.StateT Control.Monad.Trans.Writer.Lazy.Mk_WriterT
     Control.Monad.Trans.Writer.Lazy.WriterT Data.Tuple.fst Data.Tuple.snd
*)
