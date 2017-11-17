(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)


Open Scope type_scope.
(*
Inductive ArrowMonad (a : Type -> Type -> Type) b : Type := Mk_ArrowMonad : ((a unit b) -> ArrowMonad a b).

Arguments Mk_ArrowMonad {_} {_} _.

Inductive Kleisli (m : Type -> Type) a b : Type := Mk_Kleisli : (a -> m b) -> Kleisli m a b.

Arguments Mk_Kleisli {_} {_} _.
*)
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
    a b c -> a b' c' -> a (sum b b') (sum c c') ;
  left__ : forall {b} {c} {d}, a b c -> a (sum b d) (sum c d) ;
  right__ : forall {b} {c} {d}, a b c -> a (sum d b) (sum d c) ;
  op_zbzbzb____ : forall {b} {d} {c}, a b d -> a c d -> a (sum b c) d }.

Definition ArrowChoice a `{Arrow a} :=
  forall r, (ArrowChoice__Dict a -> r) -> r.

Existing Class ArrowChoice.

Definition op_zpzpzp__ `{g : ArrowChoice a} : forall {b} {c} {b'} {c'},
                                                a b c -> a b' c' -> a (sum b b') (sum c c') :=
  g _ (op_zpzpzp____ a).

Definition left `{g : ArrowChoice a} : forall {b} {c} {d},
                                         a b c -> a (sum b d) (sum c d) :=
  g _ (left__ a).

Definition right `{g : ArrowChoice a} : forall {b} {c} {d},
                                          a b c -> a (sum d b) (sum d c) :=
  g _ (right__ a).

Definition op_zbzbzb__ `{g : ArrowChoice a} : forall {b} {d} {c},
                                                a b d -> a c d -> a (sum b c) d :=
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

(* Translating `instance Arrow GHC.Prim.arrow' failed: OOPS! Cannot find
   information for class "Arrow" unsupported *)

(* Translating `instance forall {m}, forall `{GHC.Base.Monad m},
   Control.Category.Category (Kleisli m)' failed: OOPS! Cannot find information for
   class "Control.Category.Category" unsupported *)

(* Skipping instance instance_forall___GHC_Base_Monad_m___Arrow__Kleisli_m_ *)

(* Skipping instance
   instance_forall___GHC_Base_MonadPlus_m___ArrowZero__Kleisli_m_ *)

(* Skipping instance
   instance_forall___GHC_Base_MonadPlus_m___ArrowPlus__Kleisli_m_ *)

Local Definition instance_ArrowChoice_GHC_Prim_arrow_op_zbzbzb__ : forall {b}
                                                                          {d}
                                                                          {c},
                                                                     GHC.Prim.arrow b d -> GHC.Prim.arrow c
                                                                     d -> GHC.Prim.arrow (sum b c) d :=
  fun {b} {d} {c} => Data.Either.either.

Local Definition instance_ArrowChoice_GHC_Prim_arrow_op_zpzpzp__ : forall {b}
                                                                          {c}
                                                                          {b'}
                                                                          {c'},
                                                                     GHC.Prim.arrow b c -> GHC.Prim.arrow b'
                                                                     c' -> GHC.Prim.arrow (sum b b') (sum c c') :=
  fun {b} {c} {b'} {c'} =>
    fun arg_115__ arg_116__ =>
      match arg_115__ , arg_116__ with
        | f , g => instance_ArrowChoice_GHC_Prim_arrow_op_zbzbzb__
                   (Control.Category.op_z2218U__ inl f) (Control.Category.op_z2218U__ inr g)
      end.

Local Definition instance_ArrowChoice_GHC_Prim_arrow_right : forall {b} {c} {d},
                                                               GHC.Prim.arrow b c -> GHC.Prim.arrow (sum d b) (sum d
                                                                                                              c) :=
  fun {b} {c} {d} =>
    fun arg_112__ =>
      match arg_112__ with
        | f => instance_ArrowChoice_GHC_Prim_arrow_op_zpzpzp__ Control.Category.id f
      end.

Local Definition instance_ArrowChoice_GHC_Prim_arrow_left : forall {b} {c} {d},
                                                              GHC.Prim.arrow b c -> GHC.Prim.arrow (sum b d) (sum c
                                                                                                             d) :=
  fun {b} {c} {d} =>
    fun arg_109__ =>
      match arg_109__ with
        | f => instance_ArrowChoice_GHC_Prim_arrow_op_zpzpzp__ f Control.Category.id
      end.

Instance instance_ArrowChoice_GHC_Prim_arrow : ArrowChoice GHC.Prim.arrow :=
  fun _ k =>
    k (ArrowChoice__Dict_Build GHC.Prim.arrow (fun {b} {c} {b'} {c'} =>
                                 instance_ArrowChoice_GHC_Prim_arrow_op_zpzpzp__) (fun {b} {c} {d} =>
                                 instance_ArrowChoice_GHC_Prim_arrow_left) (fun {b} {c} {d} =>
                                 instance_ArrowChoice_GHC_Prim_arrow_right) (fun {b} {d} {c} =>
                                 instance_ArrowChoice_GHC_Prim_arrow_op_zbzbzb__)).

(* Skipping instance
   instance_forall___GHC_Base_Monad_m___ArrowChoice__Kleisli_m_ *)

(* Translating `instance ArrowApply GHC.Prim.arrow' failed: OOPS! Cannot find
   information for class "ArrowApply" unsupported *)

(* Translating `instance forall {m}, forall `{GHC.Base.Monad m}, ArrowApply
   (Kleisli m)' failed: OOPS! Cannot find information for class "ArrowApply"
   unsupported *)

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
     * Control.Category.Category Control.Category.id Control.Category.op_z2218U__
     Control.Category.op_zgzgzg__ Control.Category.op_zlzlzl__ Data.Either.either
     GHC.Base.Functor GHC.Base.Functor__Dict_Build GHC.Base.const GHC.Base.op_zd__
     GHC.Prim.arrow Type inl inr sum unit
*)
