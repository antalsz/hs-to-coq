(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Open Scope type_scope.
(* Converted imports: *)

Require Data.Tuple.
Require Data.Either.
Require Control.Monad.Fix.
Require Control.Category.
Require GHC.Base.
Require GHC.BaseGen.

(* Converted declarations: *)

(* Skipping instance instance_Arrow_GHC_Prim_____ *)

(* Translating `instance forall `{GHC.BaseGen.Monad m},
   Control.Category.Category (Kleisli m)' failed: OOPS! Cannot construct types for
   this class def: Nothing unsupported *)

(* Skipping instance instance_ArrowChoice_GHC_Prim_____ *)

(* Skipping instance instance_ArrowApply_GHC_Prim_____ *)

(* Translating `instance forall `{ArrowPlus a}, GHC.BaseGen.Alternative
   (ArrowMonad a)' failed: OOPS! Cannot construct types for this class def: Nothing
   unsupported *)

(* Translating `instance forall `{ArrowApply a} `{ArrowPlus a},
   GHC.Base.MonadPlus (ArrowMonad a)' failed: OOPS! Cannot construct types for this
   class def: Nothing unsupported *)

(* Skipping instance instance_ArrowLoop_GHC_Prim_____ *)

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
  fun arg_54__ arg_55__ =>
    match arg_54__ , arg_55__ with
      | a , f => Control.Category.op_zlzlzl__ a (arr f)
    end.

Infix "<<^" := (op_zlzlzc__) (at level 99).

Notation "'_<<^_'" := (op_zlzlzc__).

Definition op_zgzgzc__ {a} {b} {c} {d} `{Arrow a} : a b c -> (c -> d) -> a b
                                                    d :=
  fun arg_58__ arg_59__ =>
    match arg_58__ , arg_59__ with
      | a , f => Control.Category.op_zgzgzg__ a (arr f)
    end.

Infix ">>^" := (op_zgzgzc__) (at level 99).

Notation "'_>>^_'" := (op_zgzgzc__).

Definition op_zczlzl__ {a} {c} {d} {b} `{Arrow a} : (c -> d) -> a b c -> a b
                                                    d :=
  fun arg_50__ arg_51__ =>
    match arg_50__ , arg_51__ with
      | f , a => Control.Category.op_zlzlzl__ (arr f) a
    end.

Infix "^<<" := (op_zczlzl__) (at level 99).

Notation "'_^<<_'" := (op_zczlzl__).

Definition op_zczgzg__ {a} {b} {c} {d} `{Arrow a} : (b -> c) -> a c d -> a b
                                                    d :=
  fun arg_62__ arg_63__ =>
    match arg_62__ , arg_63__ with
      | f , a => Control.Category.op_zgzgzg__ (arr f) a
    end.

Infix "^>>" := (op_zczgzg__) (at level 99).

Notation "'_^>>_'" := (op_zczgzg__).

(*
Definition leftApp {a} {b} {c} {d} `{ArrowApply a} : a b c -> a (sum b d) (sum c
                                                                          d) :=
  fun arg_37__ =>
    match arg_37__ with
      | f => Control.Category.op_zgzgzg__ (arr (op_zbzbzb__ (fun arg_38__ =>
                                                              match arg_38__ with
                                                                | b => pair (Control.Category.op_zgzgzg__ (arr
                                                                                                          (fun arg_39__ =>
                                                                                                            match arg_39__ with
                                                                                                              | tt => b
                                                                                                            end))
                                                                                                          (Control.Category.op_zgzgzg__
                                                                                                          f (arr inr)))
                                                                            tt
                                                              end) (fun arg_43__ =>
                                                              match arg_43__ with
                                                                | d => pair (Control.Category.op_zgzgzg__ (arr
                                                                                                          (fun arg_44__ =>
                                                                                                            match arg_44__ with
                                                                                                              | tt => d
                                                                                                            end)) (arr
                                                                                                          inl)) tt
                                                              end))) app
    end.
*)
Inductive ArrowMonad (a : Type -> Type -> Type) b : Type := Mk_ArrowMonad : (a unit b) -> ArrowMonad a b.

Local Definition instance_forall___Arrow_a___GHC_BaseGen_Functor__ArrowMonad_a__fmap
      `{Arrow a0} : forall {a} {b},
                                                                                            (a -> b) -> (ArrowMonad a0)
                                                                                            a -> (ArrowMonad a0) b :=
  fun {a} {b} =>
    fun arg_93__ arg_94__ =>
      match arg_93__ , arg_94__ with
        | f , (Mk_ArrowMonad m) => GHC.BaseGen.id Mk_ArrowMonad
                                                  (Control.Category.op_zgzgzg__ m (arr f))
      end.

Local Definition instance_forall___Arrow_a___GHC_BaseGen_Functor__ArrowMonad_a__op_zlzd__ `{Arrow
                                                                                          a0} : forall {a} {b},
                                                                                                 b -> (ArrowMonad a0)
                                                                                                 a -> (ArrowMonad a0)
                                                                                                 b :=
  fun {a} {b} =>
    fun x =>
      instance_forall___Arrow_a___GHC_BaseGen_Functor__ArrowMonad_a__fmap
      (GHC.BaseGen.const x).

Instance instance_forall___Arrow_a___GHC_BaseGen_Functor__ArrowMonad_a_
  : !forall `{Arrow a}, GHC.BaseGen.Functor (ArrowMonad a) := {
  fmap := fun {a} {b} =>
    instance_forall___Arrow_a___GHC_BaseGen_Functor__ArrowMonad_a__fmap ;
  op_zlzd__ := fun {a} {b} =>
    instance_forall___Arrow_a___GHC_BaseGen_Functor__ArrowMonad_a__op_zlzd__ }.


Local Definition instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__pure `{Arrow
                                                                                         a0} : forall {a},
                                                                                                a -> (ArrowMonad a0) a :=
  fun {a} =>
    fun arg_86__ =>
      match arg_86__ with
        | x => Mk_ArrowMonad (arr (GHC.BaseGen.const x))
      end.

(*
Local Definition instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__op_zlztzg__ `{Arrow a0} : forall {a} {b},
                                                                                                       (ArrowMonad a0)
                                                                                                       (a -> b) -> (ArrowMonad
                                                                                                       a0)
                                                                                                       a -> (ArrowMonad
                                                                                                       a0) b :=
  fun {a} {b} =>
    fun arg_89__ arg_90__ =>
      match arg_89__ , arg_90__ with
        | (Mk_ArrowMonad f) , (Mk_ArrowMonad x) =>
          Mk_ArrowMonad
            (Control.Category.op_zgzgzg__ (op_zazaza__ f x)
                                          (arr
                                             (Data.Tuple.uncurry
                                                Control.Category.id)))
      end.
*)
(*
Local Definition instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__op_ztzg__ `{Arrow
                                                                                              a0} : forall {a} {b},
                                                                                                     (ArrowMonad a0)
                                                                                                     a -> (ArrowMonad a0)
                                                                                                     b -> (ArrowMonad a0)
                                                                                                     b :=
  fun {a} {b} =>
    fun x y =>
      instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__op_zlztzg__
      (GHC.BaseGen.fmap (GHC.BaseGen.const GHC.BaseGen.id) x) y. *)

(*
Local Definition instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__op_zlzt__ `{Arrow
                                                                                              a0} : forall {a} {b},
                                                                                                     (ArrowMonad a0)
                                                                                                     a -> (ArrowMonad a0)
                                                                                                     b -> (ArrowMonad a0)
                                                                                                     a :=
  fun {a} {b} =>
    fun x y =>
      instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__op_zlztzg__
      (GHC.BaseGen.fmap GHC.BaseGen.const x) y.

Instance instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a_
  : !forall `{Arrow a}, GHC.BaseGen.Applicative (ArrowMonad a) := {
  op_zlzt__ := fun {a} {b} =>
    instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__op_zlzt__ ;
  op_zlztzg__ := fun {a} {b} =>
    instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} =>
    instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__op_ztzg__ ;
  pure := fun {a} =>
    instance_forall___Arrow_a___GHC_BaseGen_Applicative__ArrowMonad_a__pure }.


Instance instance_forall___ArrowApply_a____ArrowPlus_a___GHC_Base_MonadPlus__ArrowMonad_a_
 {a} `{ArrowApply a} `{ArrowPlus a} : !GHC.BaseGen.MonadPlus (ArrowMonad a) :=
  {}.
Proof.
Admitted.


Instance instance_forall___ArrowPlus_a___GHC_BaseGen_Alternative__ArrowMonad_a_
  : !forall `{ArrowPlus a}, !GHC.BaseGen.Alternative (ArrowMonad a) := {}.
Proof.
Admitted.

Local Definition instance_forall___ArrowApply_a___GHC_BaseGen_Monad__ArrowMonad_a__return_ `{ArrowApply
                                                                                           a} : forall {a},
                                                                                                  a -> (ArrowMonad a)
                                                                                                  a :=
  fun {a} => GHC.BaseGen.pure.

Local Definition instance_forall___ArrowApply_a___GHC_BaseGen_Monad__ArrowMonad_a__op_zgzgze__ `{ArrowApply
                                                                                               a} : forall {a} {b},
                                                                                                      (ArrowMonad a)
                                                                                                      a -> (a -> (ArrowMonad
                                                                                                      a)
                                                                                                      b) -> (ArrowMonad
                                                                                                      a) b :=
  fun {a} {b} =>
    fun arg_78__ arg_79__ =>
      match arg_78__ , arg_79__ with
        | (Mk_ArrowMonad m) , f => GHC.BaseGen.id Mk_ArrowMonad
                                                  (Control.Category.op_zgzgzg__ m (Control.Category.op_zgzgzg__ (arr
                                                                                                                (fun arg_80__ =>
                                                                                                                  match arg_80__ with
                                                                                                                    | x =>
                                                                                                                      match f
                                                                                                                              x with
                                                                                                                        | (Mk_ArrowMonad
                                                                                                                          h) =>
                                                                                                                          pair
                                                                                                                          h
                                                                                                                          tt
                                                                                                                      end
                                                                                                                  end))
                                                                                                                app))
      end.

Local Definition instance_forall___ArrowApply_a___GHC_BaseGen_Monad__ArrowMonad_a__op_zgzg__ `{ArrowApply
                                                                                             a} : forall {a} {b},
                                                                                                    (ArrowMonad a)
                                                                                                    a -> (ArrowMonad a)
                                                                                                    b -> (ArrowMonad a)
                                                                                                    b :=
  fun {a} {b} => GHC.BaseGen.op_ztzg__.

Instance instance_forall___ArrowApply_a___GHC_BaseGen_Monad__ArrowMonad_a_
  : !forall `{ArrowApply a}, GHC.BaseGen.Monad (ArrowMonad a) := {
  op_zgzg__ := fun {a} {b} =>
    instance_forall___ArrowApply_a___GHC_BaseGen_Monad__ArrowMonad_a__op_zgzg__ ;
  op_zgzgze__ := fun {a} {b} =>
    instance_forall___ArrowApply_a___GHC_BaseGen_Monad__ArrowMonad_a__op_zgzgze__ ;
  return_ := fun {a} =>
    instance_forall___ArrowApply_a___GHC_BaseGen_Monad__ArrowMonad_a__return_ }.
*)

Inductive Kleisli (m : Type -> Type) a b : Type := Mk_Kleisli : (a -> m b) -> Kleisli m a b.

Definition runKleisli {m} {a} {b} (arg_36__ : Kleisli m a b) :=
  match arg_36__ with
    | (Mk_Kleisli runKleisli) => runKleisli
  end.

(*
Local Definition instance_forall___Control_Monad_Fix_MonadFix_m___ArrowLoop__Kleisli_m__loop `{Control.Monad.Fix.MonadFix
                                                                                             m} : forall {b} {d} {c},
                                                                                                    (Kleisli m) (b * d)
                                                                                                    (c * d) -> (Kleisli
                                                                                                    m) b c :=
  fun {b} {d} {c} =>
    fun arg_66__ =>
      match arg_66__ with
        | (Mk_Kleisli f) => let f' :=
                              fun arg_67__ arg_68__ =>
                                match arg_67__ , arg_68__ with
                                  | x , y => f (pair x (Data.Tuple.snd y))
                                end in
                            Mk_Kleisli (Control.Category.op_z2218U__ (GHC.Base.liftM Data.Tuple.fst)
                                                                     (Control.Category.op_z2218U__
                                                                     Control.Monad.Fix.mfix f'))
      end.

Instance instance_forall___Control_Monad_Fix_MonadFix_m___ArrowLoop__Kleisli_m_
  : !forall `{Control.Monad.Fix.MonadFix m}, ArrowLoop (Kleisli m) := {
  loop := fun {b} {d} {c} =>
    instance_forall___Control_Monad_Fix_MonadFix_m___ArrowLoop__Kleisli_m__loop }.
*)
Local Definition instance_forall___GHC_BaseGen_Monad_m___ArrowApply__Kleisli_m__app `{GHC.BaseGen.Monad
                                                                                    m} : forall {b} {c},
                                                                                           (Kleisli m) ((Kleisli m) b c
                                                                                                       * b) c :=
  fun {b} {c} =>
    Mk_Kleisli (fun arg_97__ =>
                 match arg_97__ with
                   | (pair (Mk_Kleisli f) x) => f x
                 end).

Instance instance_forall___GHC_BaseGen_Monad_m___Control_Category_Category__Kleisli_m_
  `{GHC.BaseGen.Monad m} : !Control.Category.Category (Kleisli m) := {}.
Proof.
  - intro a. eapply Mk_Kleisli. destruct H0. eapply pure.
  - intros b a c K1 K2. destruct K1. destruct K2.
    eapply Mk_Kleisli. intro xc. destruct H1. eapply op_zgzgze__.  eapply m1. exact xc.
    exact m0.
Defined.

Local Definition instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__second `{GHC.BaseGen.Monad
                                                                                  m} : forall {b} {c} {d},
                                                                                         (Kleisli m) b c -> (Kleisli m)
                                                                                         (d * b) (d * c) :=
  fun {b} {c} {d} =>
    fun arg_149__ =>
      match arg_149__ with
        | (Mk_Kleisli f) => Mk_Kleisli (fun arg_150__ =>
                                         match arg_150__ with
                                           | (pair d b) => GHC.BaseGen.op_zgzgze__ (f b) (fun arg_151__ =>
                                                                                  match arg_151__ with
                                                                                    | c => GHC.BaseGen.return_ (pair d c)
                                                                                  end)
                                         end)
      end.

Local Definition instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__first `{GHC.BaseGen.Monad
                                                                                 m} : forall {b} {c} {d},
                                                                                        (Kleisli m) b c -> (Kleisli m)
                                                                                        (b * d) (c * d) :=
  fun {b} {c} {d} =>
    fun arg_140__ =>
      match arg_140__ with
        | (Mk_Kleisli f) => Mk_Kleisli (fun arg_141__ =>
                                         match arg_141__ with
                                           | (pair b d) => GHC.BaseGen.op_zgzgze__ (f b) (fun arg_142__ =>
                                                                                  match arg_142__ with
                                                                                    | c => GHC.BaseGen.return_ (pair c d)
                                                                                  end)
                                         end)
      end.

(*
Local Definition instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__arr
      `{GHC.BaseGen.Monad m} : forall {b} {c}, (b -> c) -> (Kleisli m) b c :=
  fun {b} {c} =>
    fun arg_137__ =>
      match arg_137__ with
        | f => Mk_Kleisli (Control.Category.op_z2218U__ GHC.BaseGen.return_ f)
      end.

Local Definition instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__op_ztztzt__
      `{GHC.BaseGen.Monad
          m} : forall {b} {c} {b'} {c'},
    (Kleisli m) b
                c -> (Kleisli m) b'
                                c' -> (Kleisli m) (b * b')
                                                 (c * c') :=
  fun {b} {c} {b'} {c'} =>
    fun arg_4__ arg_5__ =>
      match arg_4__ , arg_5__ with
        | f , g => let swap :=
                     fun arg_6__ => match arg_6__ with | (pair x y) => pair y x end in
                   Control.Category.op_zgzgzg__
                   (instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__first f)
                   (Control.Category.op_zgzgzg__
                   (instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__arr swap)
                   (Control.Category.op_zgzgzg__
                   (instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__first g)
                   (instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__arr swap)))
      end.

Local Definition instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__op_zazaza__ `{GHC.BaseGen.Monad
                                                                                       m} : forall {b} {c} {c'},
                                                                                              (Kleisli m) b
                                                                                              c -> (Kleisli m) b
                                                                                              c' -> (Kleisli m) b (c *
                                                                                                                  c') :=
  fun {b} {c} {c'} =>
    fun arg_11__ arg_12__ =>
      match arg_11__ , arg_12__ with
        | f , g => Control.Category.op_zgzgzg__
                   (instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__arr (fun arg_13__ =>
                                                                                    match arg_13__ with
                                                                                      | b => pair b b
                                                                                    end))
                   (instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__op_ztztzt__ f g)
      end.

Instance instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m_
  : !forall `{GHC.BaseGen.Monad m}, Arrow (Kleisli m) := {
  arr := fun {b} {c} =>
    instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__arr ;
  first := fun {b} {c} {d} =>
    instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__first ;
  op_zazaza__ := fun {b} {c} {c'} =>
    instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__op_zazaza__ ;
  op_ztztzt__ := fun {b} {c} {b'} {c'} =>
    instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__op_ztztzt__ ;
  second := fun {b} {c} {d} =>
    instance_forall___GHC_BaseGen_Monad_m___Arrow__Kleisli_m__second }.



(*
Instance instance_forall___GHC_BaseGen_Monad_m___ArrowApply__Kleisli_m_
  `{GHC.BaseGen.Monad m} : !ArrowApply (Kleisli m) := {
  app := fun {b} {c} =>
    instance_forall___GHC_BaseGen_Monad_m___ArrowApply__Kleisli_m__app }.
*)
Local Definition instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__op_zbzbzb__ `{GHC.BaseGen.Monad
                                                                                             m} : forall {b} {d} {c},
                                                                                                    (Kleisli m) b
                                                                                                    d -> (Kleisli m) c
                                                                                                    d -> (Kleisli m)
                                                                                                    (sum b c) d :=
  fun {b} {d} {c} =>
    fun arg_114__ arg_115__ =>
      match arg_114__ , arg_115__ with
        | (Mk_Kleisli f) , (Mk_Kleisli g) => Mk_Kleisli (Data.Either.either f g)
      end.

Local Definition instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__op_zpzpzp__ `{GHC.BaseGen.Monad
                                                                                             m} : forall {b}
                                                                                                         {c}
                                                                                                         {b'}
                                                                                                         {c'},
                                                                                                    (Kleisli m) b
                                                                                                    c -> (Kleisli m) b'
                                                                                                    c' -> (Kleisli m)
                                                                                                    (sum b b') (sum c
                                                                                                               c') :=
  fun {b} {c} {b'} {c'} =>
    fun arg_110__ arg_111__ =>
      match arg_110__ , arg_111__ with
        | f , g =>
          instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__op_zbzbzb__
          (Control.Category.op_zgzgzg__ f (arr inr)) (Control.Category.op_zgzgzg__ g (arr
                                                                                   inl))
      end.

Local Definition instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__right `{GHC.BaseGen.Monad
                                                                                       m} : forall {b} {c} {d},
                                                                                              (Kleisli m) b
                                                                                              c -> (Kleisli m) (sum d b)
                                                                                              (sum d c) :=
  fun {b} {c} {d} =>
    fun arg_107__ =>
      match arg_107__ with
        | f =>
          instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__op_zpzpzp__ (arr
                                                                                      Control.Category.id) f
      end.

Local Definition instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__left `{GHC.BaseGen.Monad
                                                                                      m} : forall {b} {c} {d},
                                                                                             (Kleisli m) b c -> (Kleisli
                                                                                             m) (sum b d) (sum c d) :=
  fun {b} {c} {d} =>
    fun arg_104__ =>
      match arg_104__ with
        | f =>
          instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__op_zpzpzp__ f
                                                                                      (arr Control.Category.id)
      end.

Instance instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m_
  : !forall `{GHC.BaseGen.Monad m}, ArrowChoice (Kleisli m) := {
  left := fun {b} {c} {d} =>
    instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__left ;
  op_zbzbzb__ := fun {b} {d} {c} =>
    instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__op_zbzbzb__ ;
  op_zpzpzp__ := fun {b} {c} {b'} {c'} =>
    instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__op_zpzpzp__ ;
  right := fun {b} {c} {d} =>
    instance_forall___GHC_BaseGen_Monad_m___ArrowChoice__Kleisli_m__right }.

Local Definition instance_forall___GHC_Base_MonadPlus_m___ArrowPlus__Kleisli_m__op_zlzpzg__ `{GHC.Base.MonadPlus
                                                                                            m} : forall {b} {c},
                                                                                                   (Kleisli m) b
                                                                                                   c -> (Kleisli m) b
                                                                                                   c -> (Kleisli m) b
                                                                                                   c :=
  fun {b} {c} =>
    fun arg_128__ arg_129__ =>
      match arg_128__ , arg_129__ with
        | (Mk_Kleisli f) , (Mk_Kleisli g) => Mk_Kleisli (fun arg_130__ =>
                                                          match arg_130__ with
                                                            | x => GHC.Base.mplus (f x) (g x)
                                                          end)
      end.

Instance instance_forall___GHC_Base_MonadPlus_m___ArrowPlus__Kleisli_m_
  : !forall `{GHC.Base.MonadPlus m}, ArrowPlus (Kleisli m) := {
  op_zlzpzg__ := fun {b} {c} =>
    instance_forall___GHC_Base_MonadPlus_m___ArrowPlus__Kleisli_m__op_zlzpzg__ }.

Local Definition instance_forall___GHC_Base_MonadPlus_m___ArrowZero__Kleisli_m__zeroArrow `{GHC.Base.MonadPlus
                                                                                          m} : forall {b} {c},
                                                                                                 (Kleisli m) b c :=
  fun {b} {c} => Mk_Kleisli (fun arg_135__ => GHC.Base.mzero).

Instance instance_forall___GHC_Base_MonadPlus_m___ArrowZero__Kleisli_m_
  : !forall `{GHC.Base.MonadPlus m}, ArrowZero (Kleisli m) := {
  zeroArrow := fun {b} {c} =>
    instance_forall___GHC_Base_MonadPlus_m___ArrowZero__Kleisli_m__zeroArrow }.
*)


(* Unbound variables:
     * Control.Category.Category Control.Category.id Control.Category.op_z2218U__
     Control.Category.op_zgzgzg__ Control.Category.op_zlzlzl__
     Control.Monad.Fix.MonadFix Control.Monad.Fix.mfix Data.Either.either
     Data.Tuple.fst Data.Tuple.snd Data.Tuple.uncurry GHC.Base.MonadPlus
     GHC.Base.liftM GHC.Base.mplus GHC.Base.mzero GHC.Base.op_zgzgze__
     GHC.Base.return_ GHC.BaseGen.Alternative GHC.BaseGen.Applicative
     GHC.BaseGen.Functor GHC.BaseGen.Monad GHC.BaseGen.const GHC.BaseGen.fmap
     GHC.BaseGen.id GHC.BaseGen.op_ztzg__ GHC.BaseGen.pure inl inr pair sum tt unit
*)
