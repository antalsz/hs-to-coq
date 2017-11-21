(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)

Open Scope type_scope.

(* Converted imports: *)

Require Control.Category.
Require Data.Either.
Require GHC.Base.
Require GHC.Prim.

(* Converted type declarations: *)

Inductive Kleisli (m : Type -> Type) a b : Type := Mk_Kleisli : (a -> m
                                                                b) -> Kleisli m a b.

Inductive ArrowMonad (a : Type -> Type -> Type) b : Type := Mk_ArrowMonad : (a
                                                                            unit b) -> ArrowMonad a b.

Record Arrow__Dict (a : Type -> Type -> Type) := Arrow__Dict_Build {
  op_zazaza____ : forall {b} {c} {c'}, a b c -> a b c' -> a b (c * c') ;
  op_ztztzt____ : forall {b} {c} {b'} {c'},
    a b c -> a b' c' -> a (b * b') (c * c') ;
  arr__ : forall {b} {c}, (b -> c) -> a b c ;
  first__ : forall {b} {c} {d}, a b c -> a (b * d) (c * d) ;
  second__ : forall {b} {c} {d}, a b c -> a (d * b) (d * c) }.

Definition Arrow (a : Type -> Type -> Type) `{Control.Category.Category a} :=
  forall r, (Arrow__Dict a -> r) -> r.

Existing Class Arrow.

Definition op_zazaza__ `{g : Arrow a} : forall {b} {c} {c'},
                                          a b c -> a b c' -> a b (c * c') :=
  g _ (op_zazaza____ a).

Definition op_ztztzt__ `{g : Arrow a} : forall {b} {c} {b'} {c'},
                                          a b c -> a b' c' -> a (b * b') (c * c') :=
  g _ (op_ztztzt____ a).

Definition arr `{g : Arrow a} : forall {b} {c}, (b -> c) -> a b c :=
  g _ (arr__ a).

Definition first `{g : Arrow a} : forall {b} {c} {d},
                                    a b c -> a (b * d) (c * d) :=
  g _ (first__ a).

Definition second `{g : Arrow a} : forall {b} {c} {d},
                                     a b c -> a (d * b) (d * c) :=
  g _ (second__ a).

Infix "&&&" := (op_zazaza__) (at level 99).

Notation "'_&&&_'" := (op_zazaza__).

Infix "***" := (op_ztztzt__) (at level 99).

Notation "'_***_'" := (op_ztztzt__).

Record ArrowApply__Dict (a : Type -> Type -> Type) := ArrowApply__Dict_Build {
  app__ : forall {b} {c}, a (a b c * b) c }.

Definition ArrowApply (a : Type -> Type -> Type) `{Arrow a} :=
  forall r, (ArrowApply__Dict a -> r) -> r.

Existing Class ArrowApply.

Definition app `{g : ArrowApply a} : forall {b} {c}, a (a b c * b) c :=
  g _ (app__ a).

Record ArrowChoice__Dict a := ArrowChoice__Dict_Build {
  op_zpzpzp____ : forall {b} {c} {b'} {c'},
    a b c -> a b' c' -> a (Data.Either.Either b b') (Data.Either.Either c c') ;
  left__ : forall {b} {c} {d},
    a b c -> a (Data.Either.Either b d) (Data.Either.Either c d) ;
  right__ : forall {b} {c} {d},
    a b c -> a (Data.Either.Either d b) (Data.Either.Either d c) ;
  op_zbzbzb____ : forall {b} {d} {c},
    a b d -> a c d -> a (Data.Either.Either b c) d }.

Definition ArrowChoice a `{Arrow a} :=
  forall r, (ArrowChoice__Dict a -> r) -> r.

Existing Class ArrowChoice.

Definition op_zpzpzp__ `{g : ArrowChoice a} : forall {b} {c} {b'} {c'},
                                                a b c -> a b' c' -> a (Data.Either.Either b b') (Data.Either.Either c
                                                                                                c') :=
  g _ (op_zpzpzp____ a).

Definition left `{g : ArrowChoice a} : forall {b} {c} {d},
                                         a b c -> a (Data.Either.Either b d) (Data.Either.Either c d) :=
  g _ (left__ a).

Definition right `{g : ArrowChoice a} : forall {b} {c} {d},
                                          a b c -> a (Data.Either.Either d b) (Data.Either.Either d c) :=
  g _ (right__ a).

Definition op_zbzbzb__ `{g : ArrowChoice a} : forall {b} {d} {c},
                                                a b d -> a c d -> a (Data.Either.Either b c) d :=
  g _ (op_zbzbzb____ a).

Infix "+++" := (op_zpzpzp__) (at level 99).

Notation "'_+++_'" := (op_zpzpzp__).

Infix "|||" := (op_zbzbzb__) (at level 99).

Notation "'_|||_'" := (op_zbzbzb__).

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

Infix "<+>" := (op_zlzpzg__) (at level 99).

Notation "'_<+>_'" := (op_zlzpzg__).

Arguments Mk_Kleisli {_} {_} {_} _.

Arguments Mk_ArrowMonad {_} {_} _.

Definition runKleisli {m : Type -> Type} {a} {b} (arg_36__ : Kleisli m a b) :=
  match arg_36__ with
    | Mk_Kleisli runKleisli => runKleisli
  end.
(* Converted value declarations: *)

Local Definition instance_Arrow_GHC_Prim_arrow_arr : forall {b} {c},
                                                       (b -> c) -> GHC.Prim.arrow b c :=
  fun {b} {c} => fun arg_164__ => match arg_164__ with | f => f end.

Local Definition instance_Arrow_GHC_Prim_arrow_op_ztztzt__ : forall {b}
                                                                    {c}
                                                                    {b'}
                                                                    {c'},
                                                               GHC.Prim.arrow b c -> GHC.Prim.arrow b'
                                                               c' -> GHC.Prim.arrow (b * b') (c * c') :=
  fun {b} {c} {b'} {c'} =>
    fun arg_166__ arg_167__ arg_168__ =>
      match arg_166__ , arg_167__ , arg_168__ with
        | f , g , pair x y => pair (f x) (g y)
      end.

Local Definition instance_Arrow_GHC_Prim_arrow_second : forall {b} {c} {d},
                                                          GHC.Prim.arrow b c -> GHC.Prim.arrow (d * b) (d * c) :=
  fun {b} {c} {d} =>
    (fun arg_2__ =>
      instance_Arrow_GHC_Prim_arrow_op_ztztzt__ Control.Category.id arg_2__).

Local Definition instance_Arrow_GHC_Prim_arrow_first : forall {b} {c} {d},
                                                         GHC.Prim.arrow b c -> GHC.Prim.arrow (b * d) (c * d) :=
  fun {b} {c} {d} =>
    (fun arg_0__ =>
      instance_Arrow_GHC_Prim_arrow_op_ztztzt__ arg_0__ Control.Category.id).

Local Definition instance_Arrow_GHC_Prim_arrow_op_zazaza__ : forall {b}
                                                                    {c}
                                                                    {c'},
                                                               GHC.Prim.arrow b c -> GHC.Prim.arrow b
                                                               c' -> GHC.Prim.arrow b (c * c') :=
  fun {b} {c} {c'} =>
    fun arg_11__ arg_12__ =>
      match arg_11__ , arg_12__ with
        | f , g => Control.Category.op_zgzgzg__ (instance_Arrow_GHC_Prim_arrow_arr
                                                (fun arg_13__ => match arg_13__ with | b => pair b b end))
                                                (instance_Arrow_GHC_Prim_arrow_op_ztztzt__ f g)
      end.

Instance instance_Arrow_GHC_Prim_arrow : Arrow GHC.Prim.arrow := fun _ k =>
    k (Arrow__Dict_Build GHC.Prim.arrow (fun {b} {c} {c'} =>
                           instance_Arrow_GHC_Prim_arrow_op_zazaza__) (fun {b} {c} {b'} {c'} =>
                           instance_Arrow_GHC_Prim_arrow_op_ztztzt__) (fun {b} {c} =>
                           instance_Arrow_GHC_Prim_arrow_arr) (fun {b} {c} {d} =>
                           instance_Arrow_GHC_Prim_arrow_first) (fun {b} {c} {d} =>
                           instance_Arrow_GHC_Prim_arrow_second)).

(* Skipping instance
   instance_forall___GHC_Base_Monad_m___Control_Category_Category__Kleisli_m_ *)

(* Skipping instance instance_forall___GHC_Base_Monad_m___Arrow__Kleisli_m_ *)

(* Skipping instance
   instance_forall___GHC_Base_MonadPlus_m___ArrowZero__Kleisli_m_ *)

(* Skipping instance
   instance_forall___GHC_Base_MonadPlus_m___ArrowPlus__Kleisli_m_ *)

(* Skipping instance instance_ArrowChoice_GHC_Prim_arrow *)

(* Skipping instance
   instance_forall___GHC_Base_Monad_m___ArrowChoice__Kleisli_m_ *)

Local Definition instance_ArrowApply_GHC_Prim_arrow_app : forall {b} {c},
                                                            GHC.Prim.arrow (GHC.Prim.arrow b c * b) c :=
  fun {b} {c} => fun arg_99__ => match arg_99__ with | pair f x => f x end.

Instance instance_ArrowApply_GHC_Prim_arrow : ArrowApply GHC.Prim.arrow := fun _
                                                                               k =>
    k (ArrowApply__Dict_Build GHC.Prim.arrow (fun {b} {c} =>
                                instance_ArrowApply_GHC_Prim_arrow_app)).

(* Skipping instance
   instance_forall___GHC_Base_Monad_m___ArrowApply__Kleisli_m_ *)

Local Definition instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__fmap {inst_a}
                                                                                  `{Arrow inst_a} : forall {a} {b},
                                                                                                      (a -> b) -> (ArrowMonad
                                                                                                      inst_a)
                                                                                                      a -> (ArrowMonad
                                                                                                      inst_a) b :=
  fun {a} {b} =>
    fun arg_91__ arg_92__ =>
      match arg_91__ , arg_92__ with
        | f , Mk_ArrowMonad m => GHC.Base.op_zd__ Mk_ArrowMonad
                                                  (Control.Category.op_zgzgzg__ m (arr f))
      end.

Local Definition instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__op_zlzd__ {inst_a}
                                                                                       `{Arrow inst_a} : forall {a} {b},
                                                                                                           a -> (ArrowMonad
                                                                                                           inst_a)
                                                                                                           b -> (ArrowMonad
                                                                                                           inst_a) a :=
  fun {a} {b} =>
    fun x =>
      instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__fmap (GHC.Base.const
                                                                       x).

Instance instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a_ {a} `{Arrow
                                                                     a} : GHC.Base.Functor (ArrowMonad a) := fun _ k =>
    k (GHC.Base.Functor__Dict_Build (ArrowMonad a) (fun {a} {b} =>
                                      instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__op_zlzd__) (fun {a}
                                                                                                                  {b} =>
                                      instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__fmap)).

(* Skipping instance
   instance_forall___Arrow_a___GHC_Base_Applicative__ArrowMonad_a_ *)

(* Skipping instance
   instance_forall___ArrowApply_a___GHC_Base_Monad__ArrowMonad_a_ *)

(* Skipping instance
   instance_forall___ArrowPlus_a___GHC_Base_Alternative__ArrowMonad_a_ *)

(* Skipping instance
   instance_forall___ArrowApply_a____ArrowPlus_a___GHC_Base_MonadPlus__ArrowMonad_a_ *)

(* Skipping instance instance_ArrowLoop_GHC_Prim_arrow *)

(* Skipping instance
   instance_forall___Control_Monad_Fix_MonadFix_m___ArrowLoop__Kleisli_m_ *)

Definition op_zczgzg__ {a} {b} {c} {d} `{Arrow a} : (b -> c) -> a c d -> a b
                                                    d :=
  fun arg_49__ arg_50__ =>
    match arg_49__ , arg_50__ with
      | f , a => Control.Category.op_zgzgzg__ (arr f) a
    end.

Infix "^>>" := (op_zczgzg__) (at level 99).

Notation "'_^>>_'" := (op_zczgzg__).

Definition op_zczlzl__ {a} {c} {d} {b} `{Arrow a} : (c -> d) -> a b c -> a b
                                                    d :=
  fun arg_37__ arg_38__ =>
    match arg_37__ , arg_38__ with
      | f , a => Control.Category.op_zlzlzl__ (arr f) a
    end.

Infix "^<<" := (op_zczlzl__) (at level 99).

Notation "'_^<<_'" := (op_zczlzl__).

Definition op_zgzgzc__ {a} {b} {c} {d} `{Arrow a} : a b c -> (c -> d) -> a b
                                                    d :=
  fun arg_45__ arg_46__ =>
    match arg_45__ , arg_46__ with
      | a , f => Control.Category.op_zgzgzg__ a (arr f)
    end.

Infix ">>^" := (op_zgzgzc__) (at level 99).

Notation "'_>>^_'" := (op_zgzgzc__).

Definition op_zlzlzc__ {a} {c} {d} {b} `{Arrow a} : a c d -> (b -> c) -> a b
                                                    d :=
  fun arg_41__ arg_42__ =>
    match arg_41__ , arg_42__ with
      | a , f => Control.Category.op_zlzlzl__ a (arr f)
    end.

Infix "<<^" := (op_zlzlzc__) (at level 99).

Notation "'_<<^_'" := (op_zlzlzc__).

Definition returnA {a} {b} `{Arrow a} : a b b :=
  arr Control.Category.id.

(* Unbound variables:
     * Control.Category.Category Control.Category.id Control.Category.op_zgzgzg__
     Control.Category.op_zlzlzl__ Data.Either.Either GHC.Base.Functor
     GHC.Base.Functor__Dict_Build GHC.Base.const GHC.Base.op_zd__ GHC.Prim.arrow Type
     pair unit
*)
