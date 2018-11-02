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
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive State s a : Type
  := Mk_State (runState' : s -> (a * s)%type) : State s a.

Arguments Mk_State {_} {_} _.

Definition runState' {s} {a} (arg_0__ : State s a) :=
  let 'Mk_State runState' := arg_0__ in
  runState'.

(* Converted value declarations: *)

Definition runState {s} {a} : State s a -> s -> (a * s)%type :=
  fun s i => let 'pair a s' := runState' s i in pair a s'.

Definition put {s} : s -> State s unit :=
  fun s' => Mk_State (fun arg_0__ => pair tt s').

Definition modify {s} : (s -> s) -> State s unit :=
  fun f => Mk_State (fun s => pair tt (f s)).

Definition gets {s} {a} : (s -> a) -> State s a :=
  fun f => Mk_State (fun s => pair (f s) s).

Definition get {s} : State s s :=
  Mk_State (fun s => pair s s).

Definition execState {s} {a} : State s a -> s -> s :=
  fun s i => let 'pair _ s' := runState' s i in s'.

Definition evalState {s} {a} : State s a -> s -> a :=
  fun s i => let 'pair a _ := runState' s i in a.

Local Definition Monad__State_op_zgzgze__ {inst_s}
   : forall {a} {b},
     (State inst_s) a -> (a -> (State inst_s) b) -> (State inst_s) b :=
  fun {a} {b} =>
    fun m n =>
      Mk_State (fun s => let 'pair r s' := runState' m s in runState' (n r) s').

Local Definition Monad__State_op_zgzg__ {inst_s}
   : forall {a} {b}, (State inst_s) a -> (State inst_s) b -> (State inst_s) b :=
  fun {a} {b} => fun m k => Monad__State_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Applicative__State_op_zlztzg__ {inst_s}
   : forall {a} {b},
     (State inst_s) (a -> b) -> (State inst_s) a -> (State inst_s) b :=
  fun {a} {b} =>
    fun m n =>
      Mk_State (fun s =>
                  let 'pair f s' := runState' m s in
                  let 'pair x s'' := runState' n s' in
                  pair (f x) s'').

Local Definition Functor__State_fmap {inst_s}
   : forall {a} {b}, (a -> b) -> (State inst_s) a -> (State inst_s) b :=
  fun {a} {b} =>
    fun f m => Mk_State (fun s => let 'pair r s' := runState' m s in pair (f r) s').

Local Definition Functor__State_op_zlzd__ {inst_s}
   : forall {a} {b}, a -> (State inst_s) b -> (State inst_s) a :=
  fun {a} {b} => Functor__State_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__State {s} : GHC.Base.Functor (State s) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__State_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__State_op_zlzd__ |}.

Local Definition Applicative__State_liftA2 {inst_s}
   : forall {a} {b} {c},
     (a -> b -> c) -> (State inst_s) a -> (State inst_s) b -> (State inst_s) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__State_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__State_op_ztzg__ {inst_s}
   : forall {a} {b}, (State inst_s) a -> (State inst_s) b -> (State inst_s) b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__State_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__State_pure {inst_s}
   : forall {a}, a -> (State inst_s) a :=
  fun {a} => fun x => Mk_State (fun s => pair x s).

Program Instance Applicative__State {s} : GHC.Base.Applicative (State s) :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__State_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__State_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__State_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__State_pure |}.

Local Definition Monad__State_return_ {inst_s}
   : forall {a}, a -> (State inst_s) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__State {s} : GHC.Base.Monad (State s) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__State_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__State_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__State_return_ |}.

(* External variables:
     op_zt__ pair tt unit GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlztzg____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return___
*)
