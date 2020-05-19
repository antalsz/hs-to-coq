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
Require GHC.Char.
Require GHC.List.
Require GHC.Tuple.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Output a : Type
  := | MkOutput (runO : GHC.Base.String -> (a * GHC.Base.String)%type) : Output a.

Arguments MkOutput {_} _.

Definition runO {a} (arg_0__ : Output a) :=
  let 'MkOutput runO := arg_0__ in
  runO.

(* Converted value declarations: *)

Definition out : GHC.Char.Char -> Output unit :=
  fun c => MkOutput (fun s => pair tt (cons c s)).

Definition collect : Output unit -> GHC.Base.String :=
  fun m => let 'pair tt s := runO m nil in GHC.List.reverse s.

Local Definition Monad__Output_op_zgzgze__
   : forall {a} {b}, Output a -> (a -> Output b) -> Output b :=
  fun {a} {b} =>
    fun m f => MkOutput (fun s => let 'pair a s' := runO m s in runO (f a) s').

Local Definition Monad__Output_op_zgzg__
   : forall {a} {b}, Output a -> Output b -> Output b :=
  fun {a} {b} => fun m k => Monad__Output_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Output_return_ : forall {a}, a -> Output a :=
  fun {a} => fun a => MkOutput (GHC.Tuple.pair2 a).

Local Definition Applicative__Output_op_zlztzg__
   : forall {a} {b}, Output (a -> b) -> Output a -> Output b :=
  fun {a} {b} =>
    fun f a =>
      MkOutput (fun s =>
                  let 'pair f' s' := runO f s in
                  let 'pair a' s'' := runO a s' in
                  pair (f' a') s'').

Local Definition Functor__Output_fmap
   : forall {a} {b}, (a -> b) -> Output a -> Output b :=
  fun {a} {b} =>
    fun f x => MkOutput (fun s => let 'pair a s' := runO x s in pair (f a) s').

Local Definition Functor__Output_op_zlzd__
   : forall {a} {b}, a -> Output b -> Output a :=
  fun {a} {b} => Functor__Output_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Output : GHC.Base.Functor Output :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Output_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Output_op_zlzd__ |}.

Local Definition Applicative__Output_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Output a -> Output b -> Output c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Output_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Output_op_ztzg__
   : forall {a} {b}, Output a -> Output b -> Output b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Output_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Output_pure : forall {a}, a -> Output a :=
  fun {a} => fun a => MkOutput (GHC.Tuple.pair2 a).

Program Instance Applicative__Output : GHC.Base.Applicative Output :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Output_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Output_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Output_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Output_pure |}.

Program Instance Monad__Output : GHC.Base.Monad Output :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Output_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Output_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Output_return_ |}.

(* External variables:
     cons nil op_zt__ pair tt unit GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.String GHC.Base.const GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.id GHC.Base.liftA2__ GHC.Base.op_z2218U__ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure__ GHC.Base.return___
     GHC.Char.Char GHC.List.reverse GHC.Tuple.pair2
*)
