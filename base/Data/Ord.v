(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.
Require Import GHC.Num.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Prim.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Down a : Type := Mk_Down : a -> Down a.

Arguments Mk_Down {_} _.
(* Midamble *)

Instance instance_Down_Eq {a} `(Eq_ a) : Eq_ (Down a) := fun _ k => k {|
  op_zeze____ := (fun x y =>
                match x, y with
                | Mk_Down x0, Mk_Down y0 => x0 == y0
                end);
  op_zsze____ := (fun x y =>
                match x, y with
                | Mk_Down x0, Mk_Down y0 => x0 /= y0
                end)
|}.

(* Converted value declarations: *)

Local Definition Ord__Down_compare {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => GHC.Base.compare y x
    end.

Local Definition Ord__Down_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base.== Gt.

Local Definition Ord__Down_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base./= Lt.

Local Definition Ord__Down_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base.== Lt.

Local Definition Ord__Down_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base./= Gt.

Local Definition Ord__Down_max {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> (Down inst_a) :=
  fun x y => if Ord__Down_op_zlze__ x y : bool then y else x.

Local Definition Ord__Down_min {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> (Down inst_a) :=
  fun x y => if Ord__Down_op_zlze__ x y : bool then x else y.

Program Instance Ord__Down {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Down a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Down_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Down_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Down_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Down_op_zgze__ ;
         GHC.Base.compare__ := Ord__Down_compare ;
         GHC.Base.max__ := Ord__Down_max ;
         GHC.Base.min__ := Ord__Down_min |}.

Local Definition Functor__Down_fmap
   : forall {a} {b}, (a -> b) -> Down a -> Down b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Down_op_zlzd__
   : forall {a} {b}, a -> Down b -> Down a :=
  fun {a} {b} => fun x => Functor__Down_fmap (GHC.Base.const x).

Program Instance Functor__Down : GHC.Base.Functor Down :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Down_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Down_fmap |}.

Local Definition Applicative__Down_op_zlztzg__
   : forall {a} {b}, Down (a -> b) -> Down a -> Down b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Down_op_ztzg__
   : forall {a} {b}, Down a -> Down b -> Down b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Down_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition Applicative__Down_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Down a -> Down b -> Down c :=
  fun {a} {b} {c} => fun f x => Applicative__Down_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Down_pure : forall {a}, a -> Down a :=
  fun {a} => Mk_Down.

Program Instance Applicative__Down : GHC.Base.Applicative Down :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Down_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Down_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Down_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Down_pure |}.

Local Definition Monad__Down_op_zgzg__
   : forall {a} {b}, Down a -> Down b -> Down b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Down_op_zgzgze__
   : forall {a} {b}, Down a -> (a -> Down b) -> Down b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Down a, k => k a end.

Local Definition Monad__Down_return_ : forall {a}, a -> Down a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Down : GHC.Base.Monad Down :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Down_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Down_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Down_return_ |}.

Local Definition Monoid__Down_mappend {inst_a} `{GHC.Base.Monoid inst_a}
   : Down inst_a -> Down inst_a -> Down inst_a :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Monoid__Down_mconcat {inst_a} `{GHC.Base.Monoid inst_a}
   : list (Down inst_a) -> Down inst_a :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__Down_mempty {inst_a} `{GHC.Base.Monoid inst_a}
   : Down inst_a :=
  GHC.Prim.coerce GHC.Base.mempty.

Program Instance Monoid__Down {a} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Down a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Down_mappend ;
         GHC.Base.mconcat__ := Monoid__Down_mconcat ;
         GHC.Base.mempty__ := Monoid__Down_mempty |}.

(* Translating `instance Semigroup__Down' failed: OOPS! Cannot find information
   for class Qualified "GHC.Base" "Semigroup" unsupported *)

(* Translating `instance Num__Down' failed: OOPS! Cannot find information for
   class Qualified "GHC.Num" "Num" unsupported *)

(* Translating `instance Read__Down' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Down' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Eq___Down_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Down_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Down {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Down a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Down_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Down_op_zsze__ |}.

Definition comparing {a} {b} `{(GHC.Base.Ord a)}
   : (b -> a) -> b -> b -> comparison :=
  fun p x y => GHC.Base.compare (p x) (p y).

(* Unbound variables:
     Gt Lt bool comparison list GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.compare GHC.Base.const
     GHC.Base.fmap GHC.Base.id GHC.Base.mappend GHC.Base.mconcat GHC.Base.mempty
     GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.Base.op_ztzg__ GHC.Base.pure
     GHC.Prim.coerce
*)
