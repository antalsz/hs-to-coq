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
Require GHC.Prim.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Down a : Type := Mk_Down : a -> Down a.

Arguments Mk_Down {_} _.
(* Converted value declarations: *)

Instance Unpeel_Down a : GHC.Prim.Unpeel (Down a) a :=
  GHC.Prim.Build_Unpeel _ _ (fun '(Mk_Down x) => x) Mk_Down.

Local Definition Ord__Down_compare {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => GHC.Base.compare y x
    end.

Local Definition Ord__Down_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base./= Lt.

Local Definition Ord__Down_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base.== Gt.

Local Definition Ord__Down_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base./= Gt.

Local Definition Ord__Down_max {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> (Down inst_a) :=
  fun x y => if Ord__Down_op_zlze__ x y : bool then y else x.

Local Definition Ord__Down_min {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> (Down inst_a) :=
  fun x y => if Ord__Down_op_zlze__ x y : bool then x else y.

Local Definition Ord__Down_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => Ord__Down_compare x y GHC.Base.== Lt.

Local Definition Functor__Down_fmap
   : forall {a} {b}, (a -> b) -> Down a -> Down b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Down_op_zlzd__
   : forall {a} {b}, a -> Down b -> Down a :=
  fun {a} {b} => Functor__Down_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Down : GHC.Base.Functor Down :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__Down_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Down_op_zlzd__ |}.

Local Definition Applicative__Down_pure : forall {a}, a -> Down a :=
  fun {a} => Mk_Down.

Local Definition Applicative__Down_op_zlztzg__
   : forall {a} {b}, Down (a -> b) -> Down a -> Down b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Down_op_ztzg__
   : forall {a} {b}, Down a -> Down b -> Down b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Down_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Down_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Down a -> Down b -> Down c :=
  fun {a} {b} {c} => fun f x => Applicative__Down_op_zlztzg__ (GHC.Base.fmap f x).

Program Instance Applicative__Down : GHC.Base.Applicative Down :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Down_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Down_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Down_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Down_pure |}.

Local Definition Monad__Down_return_ : forall {a}, a -> Down a :=
  fun {a} => GHC.Base.pure.

Local Definition Monad__Down_op_zgzgze__
   : forall {a} {b}, Down a -> (a -> Down b) -> Down b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Down a, k => k a end.

Local Definition Monad__Down_op_zgzg__
   : forall {a} {b}, Down a -> Down b -> Down b :=
  fun {a} {b} => fun m k => Monad__Down_op_zgzgze__ m (fun arg_0__ => k).

Program Instance Monad__Down : GHC.Base.Monad Down :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Down_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Down_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Down_return_ |}.

Local Definition Monoid__Down_mempty {inst_a} `{GHC.Base.Monoid inst_a}
   : Down inst_a :=
  GHC.Prim.coerce GHC.Base.mempty.

Local Definition Monoid__Down_mconcat {inst_a} `{GHC.Base.Monoid inst_a}
   : list (Down inst_a) -> Down inst_a :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__Down_mappend {inst_a} `{GHC.Base.Monoid inst_a}
   : Down inst_a -> Down inst_a -> Down inst_a :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Semigroup__Down_op_zlzlzgzg__ {inst_a} `{GHC.Base.Semigroup
  inst_a}
   : Down inst_a -> Down inst_a -> Down inst_a :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__Down {a} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Down a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__Down_op_zlzlzgzg__ |}.

Program Instance Monoid__Down {a} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Down a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Down_mappend ;
         GHC.Base.mconcat__ := Monoid__Down_mconcat ;
         GHC.Base.mempty__ := Monoid__Down_mempty |}.

(* Translating `instance Num__Down' failed: Could not find information for the
   class `GHC.Num.Num' when defining the instance `Data.Ord.Num__Down' *)

(* Skipping instance Read__Down of class Read *)

(* Skipping instance Show__Down of class Show *)

Local Definition Eq___Down_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Local Definition Eq___Down_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Program Instance Eq___Down {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Down a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Down_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Down_op_zsze__ |}.

Program Instance Ord__Down {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Down a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Down_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Down_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Down_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Down_op_zgze__ ;
         GHC.Base.compare__ := Ord__Down_compare ;
         GHC.Base.max__ := Ord__Down_max ;
         GHC.Base.min__ := Ord__Down_min |}.

Definition comparing {a} {b} `{(GHC.Base.Ord a)}
   : (b -> a) -> b -> b -> comparison :=
  fun p x y => GHC.Base.compare (p x) (p y).

(* External variables:
     Gt Lt bool comparison list GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.compare
     GHC.Base.compare__ GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.mappend GHC.Base.mappend__ GHC.Base.max__
     GHC.Base.mconcat GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze____ GHC.Base.op_zl____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return___ GHC.Prim.Build_Unpeel GHC.Prim.Unpeel GHC.Prim.coerce
*)
