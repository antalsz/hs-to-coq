(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Open Scope type_scope.

(* Converted imports: *)

Require Control.Category.
Require Data.Either.
Require GHC.Base.
Require GHC.Prim.
Import Control.Category.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Kleisli (m : Type -> Type) a b : Type
  := Mk_Kleisli : (a -> m b) -> Kleisli m a b.

Inductive ArrowMonad (a : Type -> Type -> Type) b : Type
  := Mk_ArrowMonad : (a unit b) -> ArrowMonad a b.

Record Arrow__Dict (a : Type -> Type -> Type) := Arrow__Dict_Build {
  arr__ : forall {b} {c}, (b -> c) -> a b c ;
  first__ : forall {b} {c} {d}, a b c -> a (b * d)%type (c * d)%type ;
  op_zazaza____ : forall {b} {c} {c'}, a b c -> a b c' -> a b (c * c')%type ;
  op_ztztzt____ : forall {b} {c} {b'} {c'},
  a b c -> a b' c' -> a (b * b')%type (c * c')%type ;
  second__ : forall {b} {c} {d}, a b c -> a (d * b)%type (d * c)%type }.

Definition Arrow (a : Type -> Type -> Type) `{Control.Category.Category a} :=
  forall r, (Arrow__Dict a -> r) -> r.

Existing Class Arrow.

Definition arr `{g : Arrow a} : forall {b} {c}, (b -> c) -> a b c :=
  g _ (arr__ a).

Definition first `{g : Arrow a}
   : forall {b} {c} {d}, a b c -> a (b * d)%type (c * d)%type :=
  g _ (first__ a).

Definition op_zazaza__ `{g : Arrow a}
   : forall {b} {c} {c'}, a b c -> a b c' -> a b (c * c')%type :=
  g _ (op_zazaza____ a).

Definition op_ztztzt__ `{g : Arrow a}
   : forall {b} {c} {b'} {c'},
     a b c -> a b' c' -> a (b * b')%type (c * c')%type :=
  g _ (op_ztztzt____ a).

Definition second `{g : Arrow a}
   : forall {b} {c} {d}, a b c -> a (d * b)%type (d * c)%type :=
  g _ (second__ a).

Notation "'_&&&_'" := (op_zazaza__).

Infix "&&&" := (_&&&_) (at level 99).

Notation "'_***_'" := (op_ztztzt__).

Infix "***" := (_***_) (at level 99).

Record ArrowApply__Dict (a : Type -> Type -> Type) := ArrowApply__Dict_Build {
  app__ : forall {b} {c}, a (a b c * b)%type c }.

Definition ArrowApply (a : Type -> Type -> Type) `{Arrow a} :=
  forall r, (ArrowApply__Dict a -> r) -> r.

Existing Class ArrowApply.

Definition app `{g : ArrowApply a} : forall {b} {c}, a (a b c * b)%type c :=
  g _ (app__ a).

Record ArrowChoice__Dict a := ArrowChoice__Dict_Build {
  left___ : forall {b} {c} {d},
  a b c -> a (Data.Either.Either b d) (Data.Either.Either c d) ;
  op_zbzbzb____ : forall {b} {d} {c},
  a b d -> a c d -> a (Data.Either.Either b c) d ;
  op_zpzpzp____ : forall {b} {c} {b'} {c'},
  a b c -> a b' c' -> a (Data.Either.Either b b') (Data.Either.Either c c') ;
  right___ : forall {b} {c} {d},
  a b c -> a (Data.Either.Either d b) (Data.Either.Either d c) }.

Definition ArrowChoice a `{Arrow a} :=
  forall r, (ArrowChoice__Dict a -> r) -> r.

Existing Class ArrowChoice.

Definition left_ `{g : ArrowChoice a}
   : forall {b} {c} {d},
     a b c -> a (Data.Either.Either b d) (Data.Either.Either c d) :=
  g _ (left___ a).

Definition op_zbzbzb__ `{g : ArrowChoice a}
   : forall {b} {d} {c}, a b d -> a c d -> a (Data.Either.Either b c) d :=
  g _ (op_zbzbzb____ a).

Definition op_zpzpzp__ `{g : ArrowChoice a}
   : forall {b} {c} {b'} {c'},
     a b c -> a b' c' -> a (Data.Either.Either b b') (Data.Either.Either c c') :=
  g _ (op_zpzpzp____ a).

Definition right_ `{g : ArrowChoice a}
   : forall {b} {c} {d},
     a b c -> a (Data.Either.Either d b) (Data.Either.Either d c) :=
  g _ (right___ a).

Notation "'_|||_'" := (op_zbzbzb__).

Infix "|||" := (_|||_) (at level 99).

Notation "'_+++_'" := (op_zpzpzp__).

Infix "+++" := (_+++_) (at level 99).

Record ArrowLoop__Dict a := ArrowLoop__Dict_Build {
  loop__ : forall {b} {d} {c}, a (b * d)%type (c * d)%type -> a b c }.

Definition ArrowLoop a `{Arrow a} :=
  forall r, (ArrowLoop__Dict a -> r) -> r.

Existing Class ArrowLoop.

Definition loop `{g : ArrowLoop a}
   : forall {b} {d} {c}, a (b * d)%type (c * d)%type -> a b c :=
  g _ (loop__ a).

Record ArrowZero__Dict (a : Type -> Type -> Type) := ArrowZero__Dict_Build {
  zeroArrow__ : forall {b} {c}, a b c }.

Definition ArrowZero (a : Type -> Type -> Type) `{Arrow a} :=
  forall r, (ArrowZero__Dict a -> r) -> r.

Existing Class ArrowZero.

Definition zeroArrow `{g : ArrowZero a} : forall {b} {c}, a b c :=
  g _ (zeroArrow__ a).

Record ArrowPlus__Dict (a : Type -> Type -> Type) := ArrowPlus__Dict_Build {
  op_zlzpzg____ : forall {b} {c}, a b c -> a b c -> a b c }.

Definition ArrowPlus (a : Type -> Type -> Type) `{ArrowZero a} :=
  forall r, (ArrowPlus__Dict a -> r) -> r.

Existing Class ArrowPlus.

Definition op_zlzpzg__ `{g : ArrowPlus a}
   : forall {b} {c}, a b c -> a b c -> a b c :=
  g _ (op_zlzpzg____ a).

Notation "'_<+>_'" := (op_zlzpzg__).

Infix "<+>" := (_<+>_) (at level 99).

Arguments Mk_Kleisli {_} {_} {_} _.

Arguments Mk_ArrowMonad {_} {_} _.

Definition runKleisli {m : Type -> Type} {a} {b} (arg_0__ : Kleisli m a b) :=
  let 'Mk_Kleisli runKleisli := arg_0__ in
  runKleisli.
(* Converted value declarations: *)

Local Definition Arrow__arrow_arr
   : forall {b} {c}, (b -> c) -> GHC.Prim.arrow b c :=
  fun {b} {c} => fun f => f.

Local Definition Arrow__arrow_op_ztztzt__
   : forall {b} {c} {b'} {c'},
     GHC.Prim.arrow b c ->
     GHC.Prim.arrow b' c' -> GHC.Prim.arrow (b * b')%type (c * c')%type :=
  fun {b} {c} {b'} {c'} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair x y => pair (f x) (g y)
      end.

Local Definition Arrow__arrow_second
   : forall {b} {c} {d},
     GHC.Prim.arrow b c -> GHC.Prim.arrow (d * b)%type (d * c)%type :=
  fun {b} {c} {d} =>
    (fun arg_0__ => Arrow__arrow_op_ztztzt__ Control.Category.id arg_0__).

Local Definition Arrow__arrow_first
   : forall {b} {c} {d},
     GHC.Prim.arrow b c -> GHC.Prim.arrow (b * d)%type (c * d)%type :=
  fun {b} {c} {d} =>
    (fun arg_0__ => Arrow__arrow_op_ztztzt__ arg_0__ Control.Category.id).

Local Definition Arrow__arrow_op_zazaza__
   : forall {b} {c} {c'},
     GHC.Prim.arrow b c -> GHC.Prim.arrow b c' -> GHC.Prim.arrow b (c * c')%type :=
  fun {b} {c} {c'} =>
    fun f g =>
      Arrow__arrow_arr (fun b => pair b b) Control.Category.>>>
      Arrow__arrow_op_ztztzt__ f g.

Program Instance Arrow__arrow : Arrow GHC.Prim.arrow :=
  fun _ k =>
    k {| arr__ := fun {b} {c} => Arrow__arrow_arr ;
         first__ := fun {b} {c} {d} => Arrow__arrow_first ;
         op_zazaza____ := fun {b} {c} {c'} => Arrow__arrow_op_zazaza__ ;
         op_ztztzt____ := fun {b} {c} {b'} {c'} => Arrow__arrow_op_ztztzt__ ;
         second__ := fun {b} {c} {d} => Arrow__arrow_second |}.

(* Skipping instance Category__Kleisli *)

(* Skipping instance Arrow__Kleisli *)

(* Skipping instance ArrowZero__Kleisli *)

(* Skipping instance ArrowPlus__Kleisli *)

(* Skipping instance ArrowChoice__arrow *)

(* Skipping instance ArrowChoice__Kleisli *)

Local Definition ArrowApply__arrow_app
   : forall {b} {c}, GHC.Prim.arrow (GHC.Prim.arrow b c * b)%type c :=
  fun {b} {c} => fun arg_0__ => let 'pair f x := arg_0__ in f x.

Program Instance ArrowApply__arrow : ArrowApply GHC.Prim.arrow :=
  fun _ k => k {| app__ := fun {b} {c} => ArrowApply__arrow_app |}.

(* Skipping instance ArrowApply__Kleisli *)

Local Definition Functor__ArrowMonad_fmap {inst_a} `{Arrow inst_a}
   : forall {a} {b}, (a -> b) -> (ArrowMonad inst_a) a -> (ArrowMonad inst_a) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_ArrowMonad m => Mk_ArrowMonad GHC.Base.$ (m Control.Category.>>> arr f)
      end.

Local Definition Functor__ArrowMonad_op_zlzd__ {inst_a} `{Arrow inst_a}
   : forall {a} {b}, a -> (ArrowMonad inst_a) b -> (ArrowMonad inst_a) a :=
  fun {a} {b} => fun x => Functor__ArrowMonad_fmap (GHC.Base.const x).

Program Instance Functor__ArrowMonad {a} `{Arrow a}
   : GHC.Base.Functor (ArrowMonad a) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__ArrowMonad_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__ArrowMonad_fmap |}.

(* Skipping instance Applicative__ArrowMonad *)

(* Skipping instance Monad__ArrowMonad *)

(* Skipping instance Alternative__ArrowMonad *)

(* Skipping instance MonadPlus__ArrowMonad *)

(* Skipping instance ArrowLoop__arrow *)

(* Skipping instance ArrowLoop__Kleisli *)

Definition op_zczgzg__ {a} {b} {c} {d} `{Arrow a}
   : (b -> c) -> a c d -> a b d :=
  fun f a => arr f Control.Category.>>> a.

Notation "'_^>>_'" := (op_zczgzg__).

Infix "^>>" := (_^>>_) (at level 99).

Definition op_zczlzl__ {a} {c} {d} {b} `{Arrow a}
   : (c -> d) -> a b c -> a b d :=
  fun f a => arr f Control.Category.<<< a.

Notation "'_^<<_'" := (op_zczlzl__).

Infix "^<<" := (_^<<_) (at level 99).

Definition op_zgzgzc__ {a} {b} {c} {d} `{Arrow a}
   : a b c -> (c -> d) -> a b d :=
  fun a f => a Control.Category.>>> arr f.

Notation "'_>>^_'" := (op_zgzgzc__).

Infix ">>^" := (_>>^_) (at level 99).

Definition op_zlzlzc__ {a} {c} {d} {b} `{Arrow a}
   : a c d -> (b -> c) -> a b d :=
  fun a f => a Control.Category.<<< arr f.

Notation "'_<<^_'" := (op_zlzlzc__).

Infix "<<^" := (_<<^_) (at level 99).

Definition returnA {a} {b} `{Arrow a} : a b b :=
  arr Control.Category.id.

Module Notations.
Notation "'_Control.Arrow.&&&_'" := (op_zazaza__).
Infix "Control.Arrow.&&&" := (_&&&_) (at level 99).
Notation "'_Control.Arrow.***_'" := (op_ztztzt__).
Infix "Control.Arrow.***" := (_***_) (at level 99).
Notation "'_Control.Arrow.|||_'" := (op_zbzbzb__).
Infix "Control.Arrow.|||" := (_|||_) (at level 99).
Notation "'_Control.Arrow.+++_'" := (op_zpzpzp__).
Infix "Control.Arrow.+++" := (_+++_) (at level 99).
Notation "'_Control.Arrow.<+>_'" := (op_zlzpzg__).
Infix "Control.Arrow.<+>" := (_<+>_) (at level 99).
Notation "'_Control.Arrow.^>>_'" := (op_zczgzg__).
Infix "Control.Arrow.^>>" := (_^>>_) (at level 99).
Notation "'_Control.Arrow.^<<_'" := (op_zczlzl__).
Infix "Control.Arrow.^<<" := (_^<<_) (at level 99).
Notation "'_Control.Arrow.>>^_'" := (op_zgzgzc__).
Infix "Control.Arrow.>>^" := (_>>^_) (at level 99).
Notation "'_Control.Arrow.<<^_'" := (op_zlzlzc__).
Infix "Control.Arrow.<<^" := (_<<^_) (at level 99).
End Notations.

(* Unbound variables:
     Type op_zt__ pair unit Control.Category.Category Control.Category.id
     Control.Category.op_zgzgzg__ Control.Category.op_zlzlzl__ Data.Either.Either
     GHC.Base.Functor GHC.Base.const GHC.Base.op_zd__ GHC.Prim.arrow
*)
