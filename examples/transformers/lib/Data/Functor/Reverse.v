(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Fail.
Require Data.Functor.Classes.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Reverse (f : Type -> Type) (a : Type) : Type
  := Mk_Reverse (getReverse : f a) : Reverse f a.

Arguments Mk_Reverse {_} {_} _.

Definition getReverse {f : Type -> Type} {a : Type} (arg_0__ : Reverse f a) :=
  let 'Mk_Reverse getReverse := arg_0__ in
  getReverse.
(* Converted value declarations: *)

Local Definition Eq1__Reverse_liftEq {inst_f} `{(Data.Functor.Classes.Eq1
   inst_f)}
   : forall {a} {b},
     (a -> b -> bool) -> (Reverse inst_f) a -> (Reverse inst_f) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_Reverse x, Mk_Reverse y => Data.Functor.Classes.liftEq eq x y
      end.

Program Instance Eq1__Reverse {f} `{(Data.Functor.Classes.Eq1 f)}
   : Data.Functor.Classes.Eq1 (Reverse f) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__Reverse_liftEq |}.

Local Definition Ord1__Reverse_liftCompare {inst_f} `{(Data.Functor.Classes.Ord1
   inst_f)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Reverse inst_f) a -> (Reverse inst_f) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_Reverse x, Mk_Reverse y => Data.Functor.Classes.liftCompare comp x y
      end.

Program Instance Ord1__Reverse {f} `{(Data.Functor.Classes.Ord1 f)}
   : Data.Functor.Classes.Ord1 (Reverse f) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
           Ord1__Reverse_liftCompare |}.

(* Skipping instance Read1__Reverse of class Read1 *)

(* Skipping instance Show1__Reverse of class Show1 *)

Local Definition Eq___Reverse_op_zeze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Reverse_op_zsze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => negb (Eq___Reverse_op_zeze__ x y).

Program Instance Eq___Reverse {f} {a} `{Data.Functor.Classes.Eq1 f}
  `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Reverse f a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Reverse_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Reverse_op_zsze__ |}.

Local Definition Ord__Reverse_compare {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Reverse_op_zgze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base./= Lt.

Local Definition Ord__Reverse_op_zg__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base.== Gt.

Local Definition Ord__Reverse_op_zlze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base./= Gt.

Local Definition Ord__Reverse_max {inst_f} {inst_a} `{Data.Functor.Classes.Ord1
  inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) ->
     (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) :=
  fun x y => if Ord__Reverse_op_zlze__ x y : bool then y else x.

Local Definition Ord__Reverse_min {inst_f} {inst_a} `{Data.Functor.Classes.Ord1
  inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) ->
     (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) :=
  fun x y => if Ord__Reverse_op_zlze__ x y : bool then x else y.

Local Definition Ord__Reverse_op_zl__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base.== Lt.

Program Instance Ord__Reverse {f} {a} `{Data.Functor.Classes.Ord1 f}
  `{GHC.Base.Ord a}
   : GHC.Base.Ord (Reverse f a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Reverse_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Reverse_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Reverse_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Reverse_op_zgze__ ;
         GHC.Base.compare__ := Ord__Reverse_compare ;
         GHC.Base.max__ := Ord__Reverse_max ;
         GHC.Base.min__ := Ord__Reverse_min |}.

(* Skipping instance Read__Reverse of class Read *)

(* Skipping instance Show__Reverse of class Show *)

Local Definition Functor__Reverse_fmap {inst_f} `{(GHC.Base.Functor inst_f)}
   : forall {a} {b}, (a -> b) -> (Reverse inst_f) a -> (Reverse inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Reverse a => Mk_Reverse (GHC.Base.fmap f a)
      end.

Local Definition Functor__Reverse_op_zlzd__ {inst_f} `{(GHC.Base.Functor
   inst_f)}
   : forall {a} {b}, a -> (Reverse inst_f) b -> (Reverse inst_f) a :=
  fun {a} {b} => Functor__Reverse_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Reverse {f} `{(GHC.Base.Functor f)}
   : GHC.Base.Functor (Reverse f) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__Reverse_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Reverse_op_zlzd__ |}.

Local Definition Applicative__Reverse_pure {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a}, a -> (Reverse inst_f) a :=
  fun {a} => fun a => Mk_Reverse (GHC.Base.pure a).

Local Definition Applicative__Reverse_op_zlztzg__ {inst_f}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a} {b},
     (Reverse inst_f) (a -> b) -> (Reverse inst_f) a -> (Reverse inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Reverse f, Mk_Reverse a => Mk_Reverse (f GHC.Base.<*> a)
      end.

Local Definition Applicative__Reverse_op_ztzg__ {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a} {b},
     (Reverse inst_f) a -> (Reverse inst_f) b -> (Reverse inst_f) b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Reverse_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Reverse_liftA2 {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Reverse inst_f) a -> (Reverse inst_f) b -> (Reverse inst_f) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Reverse_op_zlztzg__ (GHC.Base.fmap f x).

Program Instance Applicative__Reverse {f} `{(GHC.Base.Applicative f)}
   : GHC.Base.Applicative (Reverse f) :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Reverse_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Reverse_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Reverse_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Reverse_pure |}.

(* Skipping instance Alternative__Reverse of class Alternative *)

Local Definition Monad__Reverse_op_zgzgze__ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a} {b},
     (Reverse inst_m) a -> (a -> (Reverse inst_m) b) -> (Reverse inst_m) b :=
  fun {a} {b} =>
    fun m f => Mk_Reverse (getReverse m GHC.Base.>>= (getReverse GHC.Base.∘ f)).

Local Definition Monad__Reverse_op_zgzg__ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a} {b},
     (Reverse inst_m) a -> (Reverse inst_m) b -> (Reverse inst_m) b :=
  fun {a} {b} => fun m k => Monad__Reverse_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Reverse_return_ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a}, a -> (Reverse inst_m) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Reverse {m} `{(GHC.Base.Monad m)}
   : GHC.Base.Monad (Reverse m) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Reverse_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Reverse_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Reverse_return_ |}.

Local Definition MonadFail__Reverse_fail {inst_m}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a}, GHC.Base.String -> (Reverse inst_m) a :=
  fun {a} => fun msg => Mk_Reverse (Control.Monad.Fail.fail msg).

Program Instance MonadFail__Reverse {m} `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (Reverse m) :=
  fun _ k =>
    k {| Control.Monad.Fail.fail__ := fun {a} => MonadFail__Reverse_fail |}.

(* Skipping instance MonadPlus__Reverse of class MonadPlus *)

(* Skipping instance Foldable__Reverse *)

(* Skipping instance Traversable__Reverse *)

(* External variables:
     Gt Lt Type bool comparison negb Control.Monad.Fail.MonadFail
     Control.Monad.Fail.fail Control.Monad.Fail.fail__ Data.Functor.Classes.Eq1
     Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Ord GHC.Base.String
     GHC.Base.compare__ GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return___
*)
