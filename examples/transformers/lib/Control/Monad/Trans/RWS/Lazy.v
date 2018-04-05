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
Require Import Data.Monoid.
Require Data.Tuple.
Require Import GHC.Base.

(* Converted type declarations: *)

Inductive RWST r w s m a : Type
  := Mk_RWST : (r -> s -> m (a * s * w)%type) -> RWST r w s m a.

Definition RWS r w s :=
  (RWST r w s Identity)%type.

Arguments Mk_RWST {_} {_} {_} {_} {_} _.

Definition runRWST {r} {w} {s} {m} {a} (arg_0__ : RWST r w s m a) :=
  let 'Mk_RWST runRWST := arg_0__ in
  runRWST.
(* Midamble *)

Local Definition Monad__RWST_tmp {inst_w} {inst_m} {inst_r} {inst_s}
  `{Monoid inst_w} `{Monad inst_m}
   : forall {a} {b},
     (RWST inst_r inst_w inst_s inst_m) a ->
     (a -> (RWST inst_r inst_w inst_s inst_m) b) ->
     (RWST inst_r inst_w inst_s inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_RWST (fun r s =>
                 let cont_0__ arg_1__ :=
                   let 'pair (pair a s') w := arg_1__ in
                   let cont_2__ arg_3__ :=
                     let 'pair (pair b s'') w' := arg_3__ in
                     GHC.Base.return_ (pair (pair b s'') (mappend w w')) in
                   runRWST (k a) r s' >>= cont_2__ in
                 runRWST m r s >>= cont_0__).

(* Converted value declarations: *)

Local Definition Functor__RWST_fmap {inst_m} {inst_r} {inst_w} {inst_s}
  `{(Functor inst_m)}
   : forall {a} {b},
     (a -> b) ->
     (RWST inst_r inst_w inst_s inst_m) a -> (RWST inst_r inst_w inst_s inst_m) b :=
  fun {a} {b} =>
    fun f m =>
      Mk_RWST (fun r s =>
                 fmap (fun arg_0__ =>
                         let 'pair (pair a s') w := arg_0__ in
                         pair (pair (f a) s') w) (runRWST m r s)).

Local Definition Functor__RWST_op_zlzd__ {inst_m} {inst_r} {inst_w} {inst_s}
  `{(Functor inst_m)}
   : forall {a} {b},
     a ->
     (RWST inst_r inst_w inst_s inst_m) b -> (RWST inst_r inst_w inst_s inst_m) a :=
  fun {a} {b} => fun x => Functor__RWST_fmap (const x).

Program Instance Functor__RWST {m} {r} {w} {s} `{(Functor m)}
   : Functor (RWST r w s m) :=
  fun _ k =>
    k {| op_zlzd____ := fun {a} {b} => Functor__RWST_op_zlzd__ ;
         fmap__ := fun {a} {b} => Functor__RWST_fmap |}.

Local Definition Applicative__RWST_op_zlztzg__ {inst_w} {inst_m} {inst_r}
  {inst_s} `{Monoid inst_w} `{Functor inst_m} `{Monad inst_m}
   : forall {a} {b},
     (RWST inst_r inst_w inst_s inst_m) (a -> b) ->
     (RWST inst_r inst_w inst_s inst_m) a -> (RWST inst_r inst_w inst_s inst_m) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_RWST mf, Mk_RWST mx =>
          Mk_RWST (fun r s =>
                     let cont_2__ arg_3__ :=
                       let 'pair (pair f s') w := arg_3__ in
                       let cont_4__ arg_5__ :=
                         let 'pair (pair x s'') w' := arg_5__ in
                         return_ (pair (pair (f x) s'') (mappend w w')) in
                       mx r s' >>= cont_4__ in
                     mf r s >>= cont_2__)
      end.

Local Definition Applicative__RWST_op_ztzg__ {inst_w} {inst_m} {inst_r} {inst_s}
  `{Monoid inst_w} `{Functor inst_m} `{Monad inst_m}
   : forall {a} {b},
     (RWST inst_r inst_w inst_s inst_m) a ->
     (RWST inst_r inst_w inst_s inst_m) b -> (RWST inst_r inst_w inst_s inst_m) b :=
  fun {a} {b} => fun x y => Applicative__RWST_op_zlztzg__ (fmap (const id) x) y.

Local Definition Applicative__RWST_liftA2 {inst_w} {inst_m} {inst_r} {inst_s}
  `{Monoid inst_w} `{Functor inst_m} `{Monad inst_m}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (RWST inst_r inst_w inst_s inst_m) a ->
     (RWST inst_r inst_w inst_s inst_m) b -> (RWST inst_r inst_w inst_s inst_m) c :=
  fun {a} {b} {c} => fun f x => Applicative__RWST_op_zlztzg__ (fmap f x).

Local Definition Applicative__RWST_pure {inst_w} {inst_m} {inst_r} {inst_s}
  `{Monoid inst_w} `{Functor inst_m} `{Monad inst_m}
   : forall {a}, a -> (RWST inst_r inst_w inst_s inst_m) a :=
  fun {a} =>
    fun a =>
      Mk_RWST (fun arg_0__ arg_1__ =>
                 match arg_0__, arg_1__ with
                 | _, s => return_ (pair (pair a s) mempty)
                 end).

Program Instance Applicative__RWST {w} {m} {r} {s} `{Monoid w} `{Functor m}
  `{Monad m}
   : Applicative (RWST r w s m) :=
  fun _ k =>
    k {| op_ztzg____ := fun {a} {b} => Applicative__RWST_op_ztzg__ ;
         op_zlztzg____ := fun {a} {b} => Applicative__RWST_op_zlztzg__ ;
         liftA2__ := fun {a} {b} {c} => Applicative__RWST_liftA2 ;
         pure__ := fun {a} => Applicative__RWST_pure |}.

(* Translating `instance Alternative__RWST' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Monad__RWST_op_zgzg__ {inst_w} {inst_m} {inst_r} {inst_s}
  `{Monoid inst_w} `{Monad inst_m}
   : forall {a} {b},
     (RWST inst_r inst_w inst_s inst_m) a ->
     (RWST inst_r inst_w inst_s inst_m) b -> (RWST inst_r inst_w inst_s inst_m) b :=
  fun {a} {b} => _*>_.

Definition Monad__RWST_op_zgzgze__ {inst_w} {inst_m} {inst_r} {inst_s} `{_
   : Monoid inst_w} `{_ : Monad inst_m}
   : forall {a} {b},
     RWST inst_r inst_w inst_s inst_m a ->
     (a -> RWST inst_r inst_w inst_s inst_m b) ->
     RWST inst_r inst_w inst_s inst_m b :=
  fun {a} {b} => Monad__RWST_tmp.

Local Definition Monad__RWST_return_ {inst_w} {inst_m} {inst_r} {inst_s}
  `{Monoid inst_w} `{Monad inst_m}
   : forall {a}, a -> (RWST inst_r inst_w inst_s inst_m) a :=
  fun {a} => pure.

Program Instance Monad__RWST {w} {m} {r} {s} `{Monoid w} `{Monad m}
   : Monad (RWST r w s m) :=
  fun _ k =>
    k {| op_zgzg____ := fun {a} {b} => Monad__RWST_op_zgzg__ ;
         op_zgzgze____ := fun {a} {b} => Monad__RWST_op_zgzgze__ ;
         return___ := fun {a} => Monad__RWST_return_ |}.

(* Translating `instance MonadFail__RWST' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

(* Translating `instance MonadPlus__RWST' failed: OOPS! Cannot find information
   for class Qualified "GHC.Base" "MonadPlus" unsupported *)

(* Translating `instance MonadFix__RWST' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

Local Definition MonadTrans__RWST_lift {inst_w} {inst_r} {inst_s} `{(Monoid
   inst_w)}
   : forall {m} {a} `{Monad m}, m a -> (RWST inst_r inst_w inst_s) m a :=
  fun {m} {a} `{Monad m} =>
    fun m =>
      Mk_RWST (fun arg_0__ arg_1__ =>
                 match arg_0__, arg_1__ with
                 | _, s => m >>= (fun a => return_ (pair (pair a s) mempty))
                 end).

Program Instance MonadTrans__RWST {w} {r} {s} `{(Monoid w)}
   : Control.Monad.Trans.Class.MonadTrans (RWST r w s) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{Monad m} =>
           MonadTrans__RWST_lift |}.

(* Translating `instance MonadIO__RWST' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.IO.Class" "MonadIO" unsupported *)

Definition ask {w} {m} {r} {s} `{Monoid w} `{Monad m} : RWST r w s m r :=
  Mk_RWST (fun r s => return_ (pair (pair r s) mempty)).

Definition asks {w} {m} {r} {a} {s} `{Monoid w} `{Monad m}
   : (r -> a) -> RWST r w s m a :=
  fun f => Mk_RWST (fun r s => return_ (pair (pair (f r) s) mempty)).

Definition reader {w} {m} {r} {a} {s} `{Monoid w} `{Monad m}
   : (r -> a) -> RWST r w s m a :=
  asks.

Definition censor {m} {w} {r} {s} {a} `{(Monad m)}
   : (w -> w) -> RWST r w s m a -> RWST r w s m a :=
  fun f m =>
    Mk_RWST (fun r s =>
               let cont_0__ arg_1__ :=
                 let 'pair (pair a s') w := arg_1__ in
                 return_ (pair (pair a s') (f w)) in
               runRWST m r s >>= cont_0__).

Definition evalRWST {m} {r} {w} {s} {a} `{(Monad m)}
   : RWST r w s m a -> r -> s -> m (a * w)%type :=
  fun m r s =>
    let cont_0__ arg_1__ :=
      let 'pair (pair a _) w := arg_1__ in
      return_ (pair a w) in
    runRWST m r s >>= cont_0__.

Definition execRWST {m} {r} {w} {s} {a} `{(Monad m)}
   : RWST r w s m a -> r -> s -> m (s * w)%type :=
  fun m r s =>
    let cont_0__ arg_1__ :=
      let 'pair (pair _ s') w := arg_1__ in
      return_ (pair s' w) in
    runRWST m r s >>= cont_0__.

Definition get {w} {m} {r} {s} `{Monoid w} `{Monad m} : RWST r w s m s :=
  Mk_RWST (fun arg_0__ arg_1__ =>
             match arg_0__, arg_1__ with
             | _, s => return_ (pair (pair s s) mempty)
             end).

Definition gets {w} {m} {s} {a} {r} `{Monoid w} `{Monad m}
   : (s -> a) -> RWST r w s m a :=
  fun f =>
    Mk_RWST (fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | _, s => return_ (pair (pair (f s) s) mempty)
               end).

Definition liftCallCC {w} {m} {a} {s} {b} {r} `{(Monoid w)}
   : Control.Monad.Signatures.CallCC m (a * s * w)%type (b * s * w)%type ->
     Control.Monad.Signatures.CallCC (RWST r w s m) a b :=
  fun callCC f =>
    Mk_RWST (fun r s =>
               callCC (fun c =>
                         runRWST (f (fun a =>
                                       Mk_RWST (fun arg_0__ arg_1__ => c (pair (pair a s) mempty)))) r s)).

Definition liftCallCC' {w} {m} {a} {s} {b} {r} `{(Monoid w)}
   : Control.Monad.Signatures.CallCC m (a * s * w)%type (b * s * w)%type ->
     Control.Monad.Signatures.CallCC (RWST r w s m) a b :=
  fun callCC f =>
    Mk_RWST (fun r s =>
               callCC (fun c =>
                         runRWST (f (fun a =>
                                       Mk_RWST (fun arg_0__ arg_1__ =>
                                                  match arg_0__, arg_1__ with
                                                  | _, s' => c (pair (pair a s') mempty)
                                                  end))) r s)).

Definition listen {m} {r} {w} {s} {a} `{(Monad m)}
   : RWST r w s m a -> RWST r w s m (a * w)%type :=
  fun m =>
    Mk_RWST (fun r s =>
               let cont_0__ arg_1__ :=
                 let 'pair (pair a s') w := arg_1__ in
                 return_ (pair (pair (pair a w) s') w) in
               runRWST m r s >>= cont_0__).

Definition listens {m} {w} {b} {r} {s} {a} `{(Monad m)}
   : (w -> b) -> RWST r w s m a -> RWST r w s m (a * b)%type :=
  fun f m =>
    Mk_RWST (fun r s =>
               let cont_0__ arg_1__ :=
                 let 'pair (pair a s') w := arg_1__ in
                 return_ (pair (pair (pair a (f w)) s') w) in
               runRWST m r s >>= cont_0__).

Definition local {r} {w} {s} {m} {a}
   : (r -> r) -> RWST r w s m a -> RWST r w s m a :=
  fun f m => Mk_RWST (fun r s => runRWST m (f r) s).

Definition mapRWST {m} {a} {s} {w} {n} {b} {w'} {r}
   : (m (a * s * w)%type -> n (b * s * w')%type) ->
     RWST r w s m a -> RWST r w' s n b :=
  fun f m => Mk_RWST (fun r s => f (runRWST m r s)).

Definition mapRWS {a} {s} {w} {b} {w'} {r}
   : ((a * s * w)%type -> (b * s * w')%type) -> RWS r w s a -> RWS r w' s b :=
  fun f => mapRWST (Mk_Identity ∘ (f ∘ runIdentity)).

Definition modify {w} {m} {s} {r} `{Monoid w} `{Monad m}
   : (s -> s) -> RWST r w s m unit :=
  fun f =>
    Mk_RWST (fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | _, s => return_ (pair (pair tt (f s)) mempty)
               end).

Definition pass {m} {r} {w} {s} {a} `{(Monad m)}
   : RWST r w s m (a * (w -> w))%type -> RWST r w s m a :=
  fun m =>
    Mk_RWST (fun r s =>
               let cont_0__ arg_1__ :=
                 let 'pair (pair (pair a f) s') w := arg_1__ in
                 return_ (pair (pair a s') (f w)) in
               runRWST m r s >>= cont_0__).

Definition put {w} {m} {s} {r} `{Monoid w} `{Monad m}
   : s -> RWST r w s m unit :=
  fun s => Mk_RWST (fun arg_0__ arg_1__ => return_ (pair (pair tt s) mempty)).

Definition runRWS {r} {w} {s} {a} : RWS r w s a -> r -> s -> (a * s * w)%type :=
  fun m r s => runIdentity (runRWST m r s).

Definition execRWS {r} {w} {s} {a} : RWS r w s a -> r -> s -> (s * w)%type :=
  fun m r s => let 'pair (pair _ s') w := runRWS m r s in pair s' w.

Definition evalRWS {r} {w} {s} {a} : RWS r w s a -> r -> s -> (a * w)%type :=
  fun m r s => let 'pair (pair a _) w := runRWS m r s in pair a w.

Definition rws {r} {s} {a} {w} : (r -> s -> (a * s * w)%type) -> RWS r w s a :=
  fun f => Mk_RWST (fun r s => Mk_Identity (f r s)).

Definition state {w} {m} {s} {a} {r} `{Monoid w} `{Monad m}
   : (s -> (a * s)%type) -> RWST r w s m a :=
  fun f =>
    Mk_RWST (fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | _, s => let 'pair a s' := f s in return_ (pair (pair a s') mempty)
               end).

Definition tell {m} {w} {r} {s} `{(Monad m)} : w -> RWST r w s m unit :=
  fun w =>
    Mk_RWST (fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | _, s => return_ (pair (pair tt s) w)
               end).

Definition withRWST {r'} {s} {r} {w} {m} {a}
   : (r' -> s -> (r * s)%type) -> RWST r w s m a -> RWST r' w s m a :=
  fun f m => Mk_RWST (fun r s => Data.Tuple.uncurry (runRWST m) (f r s)).

Definition withRWS {r'} {s} {r} {w} {a}
   : (r' -> s -> (r * s)%type) -> RWS r w s a -> RWS r' w s a :=
  withRWST.

Definition writer {m} {a} {w} {r} {s} `{(Monad m)}
   : (a * w)%type -> RWST r w s m a :=
  fun arg_0__ =>
    let 'pair a w := arg_0__ in
    Mk_RWST (fun arg_1__ arg_2__ =>
               match arg_1__, arg_2__ with
               | _, s => return_ (pair (pair a s) w)
               end).

(* External variables:
     Applicative Functor Identity Mk_Identity Monad Monad__RWST_tmp Monoid const fmap
     fmap__ id liftA2__ mappend mempty op_z2218U__ op_zgzg____ op_zgzgze__
     op_zgzgze____ op_zlzd____ op_zlztzg____ op_zt__ op_ztzg__ op_ztzg____ pair pure
     pure__ return_ return___ runIdentity tt unit Control.Monad.Signatures.CallCC
     Control.Monad.Trans.Class.MonadTrans Control.Monad.Trans.Class.lift__
     Data.Tuple.uncurry
*)
