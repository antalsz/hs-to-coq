(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Num.
Require GHC.Tuple.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Counter a : Type
  := | MkCounter (runC : GHC.Num.Int -> (a * GHC.Num.Int)%type) : Counter a.

Arguments MkCounter {_} _.

Definition runC {a} (arg_0__ : Counter a) :=
  let 'MkCounter runC := arg_0__ in
  runC.

(* Converted value declarations: *)

Definition inc : Counter unit :=
  MkCounter (fun x => pair tt (x GHC.Num.+ #1)).

Local Definition Monad__Counter_op_zgzgze__
   : forall {a} {b}, Counter a -> (a -> Counter b) -> Counter b :=
  fun {a} {b} =>
    fun m f => MkCounter (fun s => let 'pair a s' := runC m s in runC (f a) s').

Local Definition Monad__Counter_op_zgzg__
   : forall {a} {b}, Counter a -> Counter b -> Counter b :=
  fun {a} {b} => fun m k => Monad__Counter_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Counter_return_ : forall {a}, a -> Counter a :=
  fun {a} => fun a => MkCounter (GHC.Tuple.pair2 a).

Local Definition Applicative__Counter_op_zlztzg__
   : forall {a} {b}, Counter (a -> b) -> Counter a -> Counter b :=
  fun {a} {b} =>
    fun f a =>
      MkCounter (fun s =>
                   let 'pair f' s' := runC f s in
                   let 'pair a' s'' := runC a s' in
                   pair (f' a') s'').

Local Definition Functor__Counter_fmap
   : forall {a} {b}, (a -> b) -> Counter a -> Counter b :=
  fun {a} {b} =>
    fun f x => MkCounter (fun s => let 'pair a s' := runC x s in pair (f a) s').

Local Definition Functor__Counter_op_zlzd__
   : forall {a} {b}, a -> Counter b -> Counter a :=
  fun {a} {b} => Functor__Counter_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Counter : GHC.Base.Functor Counter :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Counter_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Counter_op_zlzd__ |}.

Local Definition Applicative__Counter_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Counter a -> Counter b -> Counter c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Counter_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Counter_op_ztzg__
   : forall {a} {b}, Counter a -> Counter b -> Counter b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Counter_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Counter_pure : forall {a}, a -> Counter a :=
  fun {a} => fun a => MkCounter (GHC.Tuple.pair2 a).

Program Instance Applicative__Counter : GHC.Base.Applicative Counter :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Counter_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Counter_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Counter_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Counter_pure |}.

Program Instance Monad__Counter : GHC.Base.Monad Counter :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Counter_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Counter_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Counter_return_ |}.

(* External variables:
     op_zt__ pair tt unit GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg____ GHC.Base.pure__ GHC.Base.return___ GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Tuple.pair2
*)
