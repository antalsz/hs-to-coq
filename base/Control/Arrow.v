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

Inductive Kleisli (m : Type -> Type) a b : Type := Mk_Kleisli : (a -> m
                                                                b) -> Kleisli m a b.

Inductive ArrowMonad (a : Type -> Type -> Type) b : Type := Mk_ArrowMonad : (a
                                                                            unit b) -> ArrowMonad a b.

Record Arrow__Dict (a : Type -> Type -> Type) := Arrow__Dict_Build {
  arr__ : forall {b} {c}, (b -> c) -> a b c ;
  first__ : forall {b} {c} {d}, a b c -> a (b * d) (c * d) ;
  op_zazaza____ : forall {b} {c} {c'}, a b c -> a b c' -> a b (c * c') ;
  op_ztztzt____ : forall {b} {c} {b'} {c'},
    a b c -> a b' c' -> a (b * b') (c * c') ;
  second__ : forall {b} {c} {d}, a b c -> a (d * b) (d * c) }.

Definition Arrow (a : Type -> Type -> Type) `{Control.Category.Category a} :=
  forall r, (Arrow__Dict a -> r) -> r.

Existing Class Arrow.

Definition arr `{g : Arrow a} : forall {b} {c}, (b -> c) -> a b c :=
  g _ (arr__ a).

Definition first `{g : Arrow a} : forall {b} {c} {d},
                                    a b c -> a (b * d) (c * d) :=
  g _ (first__ a).

Definition op_zazaza__ `{g : Arrow a} : forall {b} {c} {c'},
                                          a b c -> a b c' -> a b (c * c') :=
  g _ (op_zazaza____ a).

Definition op_ztztzt__ `{g : Arrow a} : forall {b} {c} {b'} {c'},
                                          a b c -> a b' c' -> a (b * b') (c * c') :=
  g _ (op_ztztzt____ a).

Definition second `{g : Arrow a} : forall {b} {c} {d},
                                     a b c -> a (d * b) (d * c) :=
  g _ (second__ a).

Notation "'_&&&_'" := (op_zazaza__).

Infix "&&&" := (_&&&_) (at level 99).

Notation "'_***_'" := (op_ztztzt__).

Infix "***" := (_***_) (at level 99).

Record ArrowApply__Dict (a : Type -> Type -> Type) := ArrowApply__Dict_Build {
  app__ : forall {b} {c}, a (a b c * b) c }.

Definition ArrowApply (a : Type -> Type -> Type) `{Arrow a} :=
  forall r, (ArrowApply__Dict a -> r) -> r.

Existing Class ArrowApply.

Definition app `{g : ArrowApply a} : forall {b} {c}, a (a b c * b) c :=
  g _ (app__ a).

Record ArrowChoice__Dict a := ArrowChoice__Dict_Build {
  left__ : forall {b} {c} {d},
    a b c -> a (Data.Either.Either b d) (Data.Either.Either c d) ;
  op_zbzbzb____ : forall {b} {d} {c},
    a b d -> a c d -> a (Data.Either.Either b c) d ;
  op_zpzpzp____ : forall {b} {c} {b'} {c'},
    a b c -> a b' c' -> a (Data.Either.Either b b') (Data.Either.Either c c') ;
  right__ : forall {b} {c} {d},
    a b c -> a (Data.Either.Either d b) (Data.Either.Either d c) }.

Definition ArrowChoice a `{Arrow a} :=
  forall r, (ArrowChoice__Dict a -> r) -> r.

Existing Class ArrowChoice.

Definition left `{g : ArrowChoice a} : forall {b} {c} {d},
                                         a b c -> a (Data.Either.Either b d) (Data.Either.Either c d) :=
  g _ (left__ a).

Definition op_zbzbzb__ `{g : ArrowChoice a} : forall {b} {d} {c},
                                                a b d -> a c d -> a (Data.Either.Either b c) d :=
  g _ (op_zbzbzb____ a).

Definition op_zpzpzp__ `{g : ArrowChoice a} : forall {b} {c} {b'} {c'},
                                                a b c -> a b' c' -> a (Data.Either.Either b b') (Data.Either.Either c
                                                                                                c') :=
  g _ (op_zpzpzp____ a).

Definition right `{g : ArrowChoice a} : forall {b} {c} {d},
                                          a b c -> a (Data.Either.Either d b) (Data.Either.Either d c) :=
  g _ (right__ a).

Notation "'_|||_'" := (op_zbzbzb__).

Infix "|||" := (_|||_) (at level 99).

Notation "'_+++_'" := (op_zpzpzp__).

Infix "+++" := (_+++_) (at level 99).

Record ArrowLoop__Dict a := ArrowLoop__Dict_Build {
  loop__ : forall {b} {d} {c}, a (b * d) (c * d) -> a b c }.

Definition ArrowLoop a `{Arrow a} :=
  forall r, (ArrowLoop__Dict a -> r) -> r.

Existing Class ArrowLoop.

Definition loop `{g : ArrowLoop a} : forall {b} {d} {c},
                                       a (b * d) (c * d) -> a b c :=
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

Definition op_zlzpzg__ `{g : ArrowPlus a} : forall {b} {c},
                                              a b c -> a b c -> a b c :=
  g _ (op_zlzpzg____ a).

Notation "'_<+>_'" := (op_zlzpzg__).

Infix "<+>" := (_<+>_) (at level 99).

Arguments Mk_Kleisli {_} {_} {_} _.

Arguments Mk_ArrowMonad {_} {_} _.

Definition runKleisli {m : Type -> Type} {a} {b} (arg_22__ : Kleisli m a b) :=
  match arg_22__ with
    | Mk_Kleisli runKleisli => runKleisli
  end.
(* Converted value declarations: *)

Local Definition instance_Control_Arrow_Arrow_GHC_Prim_arrow_arr : forall {b}
                                                                          {c},
                                                                     (b -> c) -> GHC.Prim.arrow b c :=
  fun {b} {c} => fun f => f.

Local Definition instance_Control_Arrow_Arrow_GHC_Prim_arrow_op_ztztzt__
    : forall {b} {c} {b'} {c'},
        GHC.Prim.arrow b c -> GHC.Prim.arrow b' c' -> GHC.Prim.arrow (b * b') (c *
                                                                              c') :=
  fun {b} {c} {b'} {c'} =>
    fun arg_104__ arg_105__ arg_106__ =>
      match arg_104__ , arg_105__ , arg_106__ with
        | f , g , pair x y => pair (f x) (g y)
      end.

Local Definition instance_Control_Arrow_Arrow_GHC_Prim_arrow_second : forall {b}
                                                                             {c}
                                                                             {d},
                                                                        GHC.Prim.arrow b c -> GHC.Prim.arrow (d * b) (d
                                                                                                                     *
                                                                                                                     c) :=
  fun {b} {c} {d} =>
    (fun arg_2__ =>
      instance_Control_Arrow_Arrow_GHC_Prim_arrow_op_ztztzt__ Control.Category.id
                                                              arg_2__).

Local Definition instance_Control_Arrow_Arrow_GHC_Prim_arrow_first : forall {b}
                                                                            {c}
                                                                            {d},
                                                                       GHC.Prim.arrow b c -> GHC.Prim.arrow (b * d) (c *
                                                                                                                    d) :=
  fun {b} {c} {d} =>
    (fun arg_0__ =>
      instance_Control_Arrow_Arrow_GHC_Prim_arrow_op_ztztzt__ arg_0__
                                                              Control.Category.id).

Local Definition instance_Control_Arrow_Arrow_GHC_Prim_arrow_op_zazaza__
    : forall {b} {c} {c'},
        GHC.Prim.arrow b c -> GHC.Prim.arrow b c' -> GHC.Prim.arrow b (c * c') :=
  fun {b} {c} {c'} =>
    fun f g =>
      instance_Control_Arrow_Arrow_GHC_Prim_arrow_arr (fun b => pair b b)
      Control.Category.>>> instance_Control_Arrow_Arrow_GHC_Prim_arrow_op_ztztzt__ f
                                                                                   g.

Program Instance instance_Control_Arrow_Arrow_GHC_Prim_arrow : Arrow
                                                               GHC.Prim.arrow := fun _ k =>
    k {|arr__ := fun {b} {c} => instance_Control_Arrow_Arrow_GHC_Prim_arrow_arr ;
      first__ := fun {b} {c} {d} =>
        instance_Control_Arrow_Arrow_GHC_Prim_arrow_first ;
      op_zazaza____ := fun {b} {c} {c'} =>
        instance_Control_Arrow_Arrow_GHC_Prim_arrow_op_zazaza__ ;
      op_ztztzt____ := fun {b} {c} {b'} {c'} =>
        instance_Control_Arrow_Arrow_GHC_Prim_arrow_op_ztztzt__ ;
      second__ := fun {b} {c} {d} =>
        instance_Control_Arrow_Arrow_GHC_Prim_arrow_second |}.

(* Skipping instance
   instance_forall___GHC_Base_Monad_m___Control_Category_Category__Control_Arrow_Kleisli_m_ *)

(* Skipping instance
   instance_forall___GHC_Base_Monad_m___Control_Arrow_Arrow__Control_Arrow_Kleisli_m_ *)

(* Skipping instance
   instance_forall___GHC_Base_MonadPlus_m___Control_Arrow_ArrowZero__Control_Arrow_Kleisli_m_ *)

(* Skipping instance
   instance_forall___GHC_Base_MonadPlus_m___Control_Arrow_ArrowPlus__Control_Arrow_Kleisli_m_ *)

(* Skipping instance instance_Control_Arrow_ArrowChoice_GHC_Prim_arrow *)

(* Skipping instance
   instance_forall___GHC_Base_Monad_m___Control_Arrow_ArrowChoice__Control_Arrow_Kleisli_m_ *)

Local Definition instance_Control_Arrow_ArrowApply_GHC_Prim_arrow_app
    : forall {b} {c}, GHC.Prim.arrow (GHC.Prim.arrow b c * b) c :=
  fun {b} {c} => fun arg_63__ => match arg_63__ with | pair f x => f x end.

Program Instance instance_Control_Arrow_ArrowApply_GHC_Prim_arrow : ArrowApply
                                                                    GHC.Prim.arrow := fun _ k =>
    k {|app__ := fun {b} {c} =>
        instance_Control_Arrow_ArrowApply_GHC_Prim_arrow_app |}.

(* Skipping instance
   instance_forall___GHC_Base_Monad_m___Control_Arrow_ArrowApply__Control_Arrow_Kleisli_m_ *)

Local Definition instance_forall___Control_Arrow_Arrow_a___GHC_Base_Functor__Control_Arrow_ArrowMonad_a__fmap {inst_a}
                                                                                                              `{Arrow
                                                                                                              inst_a}
    : forall {a} {b}, (a -> b) -> (ArrowMonad inst_a) a -> (ArrowMonad inst_a) b :=
  fun {a} {b} =>
    fun arg_55__ arg_56__ =>
      match arg_55__ , arg_56__ with
        | f , Mk_ArrowMonad m => Mk_ArrowMonad GHC.Base.$ (m Control.Category.>>> arr f)
      end.

Local Definition instance_forall___Control_Arrow_Arrow_a___GHC_Base_Functor__Control_Arrow_ArrowMonad_a__op_zlzd__ {inst_a}
                                                                                                                   `{Arrow
                                                                                                                   inst_a}
    : forall {a} {b}, a -> (ArrowMonad inst_a) b -> (ArrowMonad inst_a) a :=
  fun {a} {b} =>
    fun x =>
      instance_forall___Control_Arrow_Arrow_a___GHC_Base_Functor__Control_Arrow_ArrowMonad_a__fmap
      (GHC.Base.const x).

Program Instance instance_forall___Control_Arrow_Arrow_a___GHC_Base_Functor__Control_Arrow_ArrowMonad_a_ {a}
                                                                                                         `{Arrow a}
  : GHC.Base.Functor (ArrowMonad a) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_forall___Control_Arrow_Arrow_a___GHC_Base_Functor__Control_Arrow_ArrowMonad_a__op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_forall___Control_Arrow_Arrow_a___GHC_Base_Functor__Control_Arrow_ArrowMonad_a__fmap |}.

(* Skipping instance
   instance_forall___Control_Arrow_Arrow_a___GHC_Base_Applicative__Control_Arrow_ArrowMonad_a_ *)

(* Skipping instance
   instance_forall___Control_Arrow_ArrowApply_a___GHC_Base_Monad__Control_Arrow_ArrowMonad_a_ *)

(* Skipping instance
   instance_forall___Control_Arrow_ArrowPlus_a___GHC_Base_Alternative__Control_Arrow_ArrowMonad_a_ *)

(* Skipping instance
   instance_forall___Control_Arrow_ArrowApply_a____Control_Arrow_ArrowPlus_a___GHC_Base_MonadPlus__Control_Arrow_ArrowMonad_a_ *)

(* Skipping instance instance_Control_Arrow_ArrowLoop_GHC_Prim_arrow *)

(* Skipping instance
   instance_forall___Control_Monad_Fix_MonadFix_m___Control_Arrow_ArrowLoop__Control_Arrow_Kleisli_m_ *)

Definition op_zczgzg__ {a} {b} {c} {d} `{Arrow a} : (b -> c) -> a c d -> a b
                                                    d :=
  fun f a => arr f Control.Category.>>> a.

Notation "'_^>>_'" := (op_zczgzg__).

Infix "^>>" := (_^>>_) (at level 99).

Definition op_zczlzl__ {a} {c} {d} {b} `{Arrow a} : (c -> d) -> a b c -> a b
                                                    d :=
  fun f a => arr f Control.Category.<<< a.

Notation "'_^<<_'" := (op_zczlzl__).

Infix "^<<" := (_^<<_) (at level 99).

Definition op_zgzgzc__ {a} {b} {c} {d} `{Arrow a} : a b c -> (c -> d) -> a b
                                                    d :=
  fun a f => a Control.Category.>>> arr f.

Notation "'_>>^_'" := (op_zgzgzc__).

Infix ">>^" := (_>>^_) (at level 99).

Definition op_zlzlzc__ {a} {c} {d} {b} `{Arrow a} : a c d -> (b -> c) -> a b
                                                    d :=
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
