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

Inductive Freer e r : Type
  := | Ret : r -> Freer e r
  |  Vis {x} : (e x) -> (x -> Freer e r) -> Freer e r.

Arguments Ret {_} {_} _.

Arguments Vis {_} {_} {_} _ _.

(* Converted value declarations: *)

Definition ret {x} {e} : x -> Freer e x :=
  Ret.

Definition vis {e} {x} : e x -> Freer e x :=
  fun m => Vis m ret.

Definition bind {e} {x} {y} : Freer e x -> (x -> Freer e y) -> Freer e y :=
  fix bind (arg_0__ : Freer e x) (arg_1__ : (x -> Freer e y)) : Freer e y
        := match arg_0__, arg_1__ with
           | Ret x, f => f x
           | Vis e k, f => Vis e (fun x => bind (k x) f)
           end.

Local Definition Monad__Freer_op_zgzgze__ {inst_e}
   : forall {a} {b},
     (Freer inst_e) a -> (a -> (Freer inst_e) b) -> (Freer inst_e) b :=
  fun {a} {b} => fun xs f => bind xs f.

Local Definition Monad__Freer_op_zgzg__ {inst_e}
   : forall {a} {b}, (Freer inst_e) a -> (Freer inst_e) b -> (Freer inst_e) b :=
  fun {a} {b} => fun m k => Monad__Freer_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Functor__Freer_fmap {inst_e}
   : forall {a} {b}, (a -> b) -> (Freer inst_e) a -> (Freer inst_e) b :=
  fun {a} {b} => fun f x => bind x (ret GHC.Base.∘ f).

Local Definition Functor__Freer_op_zlzd__ {inst_e}
   : forall {a} {b}, a -> (Freer inst_e) b -> (Freer inst_e) a :=
  fun {a} {b} => Functor__Freer_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Freer {e} : GHC.Base.Functor (Freer e) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Freer_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Freer_op_zlzd__ |}.

Local Definition Applicative__Freer_op_zlztzg__ {inst_e}
   : forall {a} {b},
     (Freer inst_e) (a -> b) -> (Freer inst_e) a -> (Freer inst_e) b :=
  fun {a} {b} => fun fs xs => bind fs (fun arg_0__ => GHC.Base.fmap arg_0__ xs).

Local Definition Applicative__Freer_liftA2 {inst_e}
   : forall {a} {b} {c},
     (a -> b -> c) -> (Freer inst_e) a -> (Freer inst_e) b -> (Freer inst_e) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Freer_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Freer_op_ztzg__ {inst_e}
   : forall {a} {b}, (Freer inst_e) a -> (Freer inst_e) b -> (Freer inst_e) b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Freer_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Freer_pure {inst_e}
   : forall {a}, a -> (Freer inst_e) a :=
  fun {a} => ret.

Program Instance Applicative__Freer {e} : GHC.Base.Applicative (Freer e) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Freer_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Freer_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Freer_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Freer_pure |}.

Local Definition Monad__Freer_return_ {inst_e}
   : forall {a}, a -> (Freer inst_e) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Freer {e} : GHC.Base.Monad (Freer e) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Freer_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Freer_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Freer_return_ |}.

(* External variables:
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.const
     GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__ GHC.Base.op_z2218U__
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Base.return___
*)
