(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Open Scope type_scope.

Inductive ArrowMonad (a : Type -> Type -> Type) b : Type := Mk_ArrowMonad : ((a unit b) -> ArrowMonad a b).

Arguments Mk_ArrowMonad {_} {_} _.

Inductive Kleisli (m : Type -> Type) a b : Type := Mk_Kleisli : (a -> m b) -> Kleisli m a b.

Arguments Mk_Kleisli {_} {_} _.

(* Converted imports: *)

Require Control.Category.
Require GHC.Base.
Require GHC.Prim.

(* Converted declarations: *)

Local Definition instance_Arrow_GHC_Prim_arrow_arr : forall {b} {c},
                                                       (b -> c) -> GHC.Prim.arrow b c :=
  fun {b} {c} => fun arg_162__ => match arg_162__ with | f => f end.

Local Definition instance_Arrow_GHC_Prim_arrow_op_ztztzt__ : forall {b}
                                                                    {c}
                                                                    {b'}
                                                                    {c'},
                                                               GHC.Prim.arrow b c -> GHC.Prim.arrow b'
                                                               c' -> GHC.Prim.arrow (b * b') (c * c') :=
  fun {b} {c} {b'} {c'} =>
    fun arg_164__ arg_165__ arg_166__ =>
      match arg_164__ , arg_165__ , arg_166__ with
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
  fun {b} {c} => fun arg_97__ => match arg_97__ with | pair f x => f x end.

(* Skipping instance
   instance_forall___GHC_Base_Monad_m___ArrowApply__Kleisli_m_ *)

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

Class Arrow a `{Control.Category.Category a} := {
  op_zazaza__ : forall {b} {c} {c'}, a b c -> a b c' -> a b (c * c') ;
  op_ztztzt__ : forall {b} {c} {b'} {c'},
    a b c -> a b' c' -> a (b * b') (c * c') ;
  arr : forall {b} {c}, (b -> c) -> a b c ;
  first : forall {b} {c} {d}, a b c -> a (b * d) (c * d) ;
  second : forall {b} {c} {d}, a b c -> a (d * b) (d * c) }.

Infix "&&&" := (op_zazaza__) (at level 99).

Notation "'_&&&_'" := (op_zazaza__).

Infix "***" := (op_ztztzt__) (at level 99).

Notation "'_***_'" := (op_ztztzt__).

Class ArrowApply a `{Arrow a} := {
  app : forall {b} {c}, a (a b c * b) c }.

Class ArrowChoice a `{Arrow a} := {
  op_zpzpzp__ : forall {b} {c} {b'} {c'},
    a b c -> a b' c' -> a (sum b b') (sum c c') ;
  left : forall {b} {c} {d}, a b c -> a (sum b d) (sum c d) ;
  right : forall {b} {c} {d}, a b c -> a (sum d b) (sum d c) ;
  op_zbzbzb__ : forall {b} {d} {c}, a b d -> a c d -> a (sum b c) d }.

Infix "+++" := (op_zpzpzp__) (at level 99).

Notation "'_+++_'" := (op_zpzpzp__).

Infix "|||" := (op_zbzbzb__) (at level 99).

Notation "'_|||_'" := (op_zbzbzb__).

Class ArrowLoop a `{Arrow a} := {
  loop : forall {b} {d} {c}, a (b * d) (c * d) -> a b c }.

Class ArrowZero a `{Arrow a} := {
  zeroArrow : forall {b} {c}, a b c }.

Class ArrowPlus a `{ArrowZero a} := {
  op_zlzpzg__ : forall {b} {c}, a b c -> a b c -> a b c }.

Infix "<+>" := (op_zlzpzg__) (at level 99).

Notation "'_<+>_'" := (op_zlzpzg__).

Definition op_zlzlzc__ {a} {c} {d} {b} `{Arrow a} : a c d -> (b -> c) -> a b
                                                    d :=
  fun arg_40__ arg_41__ =>
    match arg_40__ , arg_41__ with
      | a , f => Control.Category.op_zlzlzl__ a (arr f)
    end.

Infix "<<^" := (op_zlzlzc__) (at level 99).

Notation "'_<<^_'" := (op_zlzlzc__).

Definition op_zgzgzc__ {a} {b} {c} {d} `{Arrow a} : a b c -> (c -> d) -> a b
                                                    d :=
  fun arg_44__ arg_45__ =>
    match arg_44__ , arg_45__ with
      | a , f => Control.Category.op_zgzgzg__ a (arr f)
    end.

Infix ">>^" := (op_zgzgzc__) (at level 99).

Notation "'_>>^_'" := (op_zgzgzc__).

Definition op_zczlzl__ {a} {c} {d} {b} `{Arrow a} : (c -> d) -> a b c -> a b
                                                    d :=
  fun arg_36__ arg_37__ =>
    match arg_36__ , arg_37__ with
      | f , a => Control.Category.op_zlzlzl__ (arr f) a
    end.

Infix "^<<" := (op_zczlzl__) (at level 99).

Notation "'_^<<_'" := (op_zczlzl__).

Definition op_zczgzg__ {a} {b} {c} {d} `{Arrow a} : (b -> c) -> a c d -> a b
                                                    d :=
  fun arg_48__ arg_49__ =>
    match arg_48__ , arg_49__ with
      | f , a => Control.Category.op_zgzgzg__ (arr f) a
    end.

Infix "^>>" := (op_zczgzg__) (at level 99).

Notation "'_^>>_'" := (op_zczgzg__).

Local Definition instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__fmap {inst_a}
                                                                                  `{Arrow inst_a} : forall {a} {b},
                                                                                                      (a -> b) -> (ArrowMonad
                                                                                                      inst_a)
                                                                                                      a -> (ArrowMonad
                                                                                                      inst_a) b :=
  fun {a} {b} =>
    fun arg_89__ arg_90__ =>
      match arg_89__ , arg_90__ with
        | f , Mk_ArrowMonad m => GHC.Base.op_zd__ Mk_ArrowMonad
                                                  (Control.Category.op_zgzgzg__ m (arr f))
      end.

Local Definition instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__op_zlzd__ {inst_a}
                                                                                       `{Arrow inst_a} : forall {a} {b},
                                                                                                           b -> (ArrowMonad
                                                                                                           inst_a)
                                                                                                           a -> (ArrowMonad
                                                                                                           inst_a) b :=
  fun {a} {b} =>
    fun x =>
      instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__fmap (GHC.Base.const
                                                                       x).

Instance instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a_
  : forall {a}, forall `{Arrow a}, GHC.Base.Functor (ArrowMonad a) := {
  fmap := fun {a} {b} =>
    instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__fmap ;
  op_zlzd__ := fun {a} {b} =>
    instance_forall___Arrow_a___GHC_Base_Functor__ArrowMonad_a__op_zlzd__ }.

Instance instance_Arrow_GHC_Prim_arrow : Arrow GHC.Prim.arrow := {
  arr := fun {b} {c} => instance_Arrow_GHC_Prim_arrow_arr ;
  first := fun {b} {c} {d} => instance_Arrow_GHC_Prim_arrow_first ;
  op_zazaza__ := fun {b} {c} {c'} => instance_Arrow_GHC_Prim_arrow_op_zazaza__ ;
  op_ztztzt__ := fun {b} {c} {b'} {c'} =>
    instance_Arrow_GHC_Prim_arrow_op_ztztzt__ ;
  second := fun {b} {c} {d} => instance_Arrow_GHC_Prim_arrow_second }.

Instance instance_ArrowApply_GHC_Prim_arrow : ArrowApply GHC.Prim.arrow := {
  app := fun {b} {c} => instance_ArrowApply_GHC_Prim_arrow_app }.

(* Unbound variables:
     * ArrowMonad Control.Category.Category Control.Category.id
     Control.Category.op_zgzgzg__ Control.Category.op_zlzlzl__ GHC.Base.Functor
     GHC.Base.const GHC.Base.op_zd__ GHC.Prim.arrow Mk_ArrowMonad pair sum
*)
