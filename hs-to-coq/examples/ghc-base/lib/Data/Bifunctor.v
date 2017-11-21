(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Either.
Require Data.Functor.Const.
Require GHC.Base.
Require GHC.Tuple.

(* Converted type declarations: *)

Record Bifunctor__Dict p := Bifunctor__Dict_Build {
  bimap__ : forall {a} {b} {c} {d}, (a -> b) -> (c -> d) -> p a c -> p b d ;
  first__ : forall {a} {b} {c}, (a -> b) -> p a c -> p b c ;
  second__ : forall {b} {c} {a}, (b -> c) -> p a b -> p a c }.

Definition Bifunctor p :=
  forall r, (Bifunctor__Dict p -> r) -> r.

Existing Class Bifunctor.

Definition bimap `{g : Bifunctor p} : forall {a} {b} {c} {d},
                                        (a -> b) -> (c -> d) -> p a c -> p b d :=
  g _ (bimap__ p).

Definition first `{g : Bifunctor p} : forall {a} {b} {c},
                                        (a -> b) -> p a c -> p b c :=
  g _ (first__ p).

Definition second `{g : Bifunctor p} : forall {b} {c} {a},
                                         (b -> c) -> p a b -> p a c :=
  g _ (second__ p).
(* Converted value declarations: *)

Local Definition instance_Bifunctor_GHC_Tuple_pair_type_bimap : forall {a}
                                                                       {b}
                                                                       {c}
                                                                       {d},
                                                                  (a -> b) -> (c -> d) -> GHC.Tuple.pair_type a
                                                                  c -> GHC.Tuple.pair_type b d :=
  fun {a} {b} {c} {d} =>
    fun arg_49__ arg_50__ arg_51__ =>
      match arg_49__ , arg_50__ , arg_51__ with
        | f , g , pair a b => pair (f a) (g b)
      end.

Local Definition instance_Bifunctor_GHC_Tuple_pair_type_first : forall {a}
                                                                       {b}
                                                                       {c},
                                                                  (a -> b) -> GHC.Tuple.pair_type a
                                                                  c -> GHC.Tuple.pair_type b c :=
  fun {a} {b} {c} =>
    fun arg_4__ =>
      match arg_4__ with
        | f => instance_Bifunctor_GHC_Tuple_pair_type_bimap f GHC.Base.id
      end.

Local Definition instance_Bifunctor_GHC_Tuple_pair_type_second : forall {b}
                                                                        {c}
                                                                        {a},
                                                                   (b -> c) -> GHC.Tuple.pair_type a
                                                                   b -> GHC.Tuple.pair_type a c :=
  fun {b} {c} {a} => instance_Bifunctor_GHC_Tuple_pair_type_bimap GHC.Base.id.

Program Instance instance_Bifunctor_GHC_Tuple_pair_type : Bifunctor
                                                          GHC.Tuple.pair_type := fun _ k =>
    k {|bimap__ := fun {a} {b} {c} {d} =>
        instance_Bifunctor_GHC_Tuple_pair_type_bimap ;
      first__ := fun {a} {b} {c} => instance_Bifunctor_GHC_Tuple_pair_type_first ;
      second__ := fun {b} {c} {a} => instance_Bifunctor_GHC_Tuple_pair_type_second |}.

Local Definition instance_Bifunctor__GHC_Tuple_triple_type_x1__bimap {inst_x1}
    : forall {a} {b} {c} {d},
        (a -> b) -> (c -> d) -> (GHC.Tuple.triple_type inst_x1) a
        c -> (GHC.Tuple.triple_type inst_x1) b d :=
  fun {a} {b} {c} {d} =>
    fun arg_44__ arg_45__ arg_46__ =>
      match arg_44__ , arg_45__ , arg_46__ with
        | f , g , pair (pair x1 a) b => pair (pair x1 (f a)) (g b)
      end.

Local Definition instance_Bifunctor__GHC_Tuple_triple_type_x1__first {inst_x1}
    : forall {a} {b} {c},
        (a -> b) -> (GHC.Tuple.triple_type inst_x1) a c -> (GHC.Tuple.triple_type
        inst_x1) b c :=
  fun {a} {b} {c} =>
    fun arg_4__ =>
      match arg_4__ with
        | f => instance_Bifunctor__GHC_Tuple_triple_type_x1__bimap f GHC.Base.id
      end.

Local Definition instance_Bifunctor__GHC_Tuple_triple_type_x1__second {inst_x1}
    : forall {b} {c} {a},
        (b -> c) -> (GHC.Tuple.triple_type inst_x1) a b -> (GHC.Tuple.triple_type
        inst_x1) a c :=
  fun {b} {c} {a} =>
    instance_Bifunctor__GHC_Tuple_triple_type_x1__bimap GHC.Base.id.

Program Instance instance_Bifunctor__GHC_Tuple_triple_type_x1_ {x1} : Bifunctor
                                                                      (GHC.Tuple.triple_type x1) := fun _ k =>
    k {|bimap__ := fun {a} {b} {c} {d} =>
        instance_Bifunctor__GHC_Tuple_triple_type_x1__bimap ;
      first__ := fun {a} {b} {c} =>
        instance_Bifunctor__GHC_Tuple_triple_type_x1__first ;
      second__ := fun {b} {c} {a} =>
        instance_Bifunctor__GHC_Tuple_triple_type_x1__second |}.

Local Definition instance_Bifunctor__GHC_Tuple_quad_type_x1_x2__bimap {inst_x1}
                                                                      {inst_x2} : forall {a} {b} {c} {d},
                                                                                    (a -> b) -> (c -> d) -> (GHC.Tuple.quad_type
                                                                                    inst_x1 inst_x2) a
                                                                                    c -> (GHC.Tuple.quad_type inst_x1
                                                                                    inst_x2) b d :=
  fun {a} {b} {c} {d} =>
    fun arg_39__ arg_40__ arg_41__ =>
      match arg_39__ , arg_40__ , arg_41__ with
        | f , g , pair (pair (pair x1 x2) a) b => pair (pair (pair x1 x2) (f a)) (g b)
      end.

Local Definition instance_Bifunctor__GHC_Tuple_quad_type_x1_x2__first {inst_x1}
                                                                      {inst_x2} : forall {a} {b} {c},
                                                                                    (a -> b) -> (GHC.Tuple.quad_type
                                                                                    inst_x1 inst_x2) a
                                                                                    c -> (GHC.Tuple.quad_type inst_x1
                                                                                    inst_x2) b c :=
  fun {a} {b} {c} =>
    fun arg_4__ =>
      match arg_4__ with
        | f => instance_Bifunctor__GHC_Tuple_quad_type_x1_x2__bimap f GHC.Base.id
      end.

Local Definition instance_Bifunctor__GHC_Tuple_quad_type_x1_x2__second {inst_x1}
                                                                       {inst_x2} : forall {b} {c} {a},
                                                                                     (b -> c) -> (GHC.Tuple.quad_type
                                                                                     inst_x1 inst_x2) a
                                                                                     b -> (GHC.Tuple.quad_type inst_x1
                                                                                     inst_x2) a c :=
  fun {b} {c} {a} =>
    instance_Bifunctor__GHC_Tuple_quad_type_x1_x2__bimap GHC.Base.id.

Program Instance instance_Bifunctor__GHC_Tuple_quad_type_x1_x2_ {x1} {x2}
  : Bifunctor (GHC.Tuple.quad_type x1 x2) := fun _ k =>
    k {|bimap__ := fun {a} {b} {c} {d} =>
        instance_Bifunctor__GHC_Tuple_quad_type_x1_x2__bimap ;
      first__ := fun {a} {b} {c} =>
        instance_Bifunctor__GHC_Tuple_quad_type_x1_x2__first ;
      second__ := fun {b} {c} {a} =>
        instance_Bifunctor__GHC_Tuple_quad_type_x1_x2__second |}.

Local Definition instance_Bifunctor__GHC_Tuple_quint_type_x1_x2_x3__bimap {inst_x1}
                                                                          {inst_x2} {inst_x3} : forall {a} {b} {c} {d},
                                                                                                  (a -> b) -> (c -> d) -> (GHC.Tuple.quint_type
                                                                                                  inst_x1 inst_x2
                                                                                                  inst_x3) a
                                                                                                  c -> (GHC.Tuple.quint_type
                                                                                                  inst_x1 inst_x2
                                                                                                  inst_x3) b d :=
  fun {a} {b} {c} {d} =>
    fun arg_34__ arg_35__ arg_36__ =>
      match arg_34__ , arg_35__ , arg_36__ with
        | f , g , pair (pair (pair (pair x1 x2) x3) a) b => pair (pair (pair (pair x1
                                                                                   x2) x3) (f a)) (g b)
      end.

Local Definition instance_Bifunctor__GHC_Tuple_quint_type_x1_x2_x3__first {inst_x1}
                                                                          {inst_x2} {inst_x3} : forall {a} {b} {c},
                                                                                                  (a -> b) -> (GHC.Tuple.quint_type
                                                                                                  inst_x1 inst_x2
                                                                                                  inst_x3) a
                                                                                                  c -> (GHC.Tuple.quint_type
                                                                                                  inst_x1 inst_x2
                                                                                                  inst_x3) b c :=
  fun {a} {b} {c} =>
    fun arg_4__ =>
      match arg_4__ with
        | f => instance_Bifunctor__GHC_Tuple_quint_type_x1_x2_x3__bimap f GHC.Base.id
      end.

Local Definition instance_Bifunctor__GHC_Tuple_quint_type_x1_x2_x3__second {inst_x1}
                                                                           {inst_x2} {inst_x3} : forall {b} {c} {a},
                                                                                                   (b -> c) -> (GHC.Tuple.quint_type
                                                                                                   inst_x1 inst_x2
                                                                                                   inst_x3) a
                                                                                                   b -> (GHC.Tuple.quint_type
                                                                                                   inst_x1 inst_x2
                                                                                                   inst_x3) a c :=
  fun {b} {c} {a} =>
    instance_Bifunctor__GHC_Tuple_quint_type_x1_x2_x3__bimap GHC.Base.id.

Program Instance instance_Bifunctor__GHC_Tuple_quint_type_x1_x2_x3_ {x1} {x2}
                                                                    {x3} : Bifunctor (GHC.Tuple.quint_type x1 x2 x3) :=
  fun _ k =>
    k {|bimap__ := fun {a} {b} {c} {d} =>
        instance_Bifunctor__GHC_Tuple_quint_type_x1_x2_x3__bimap ;
      first__ := fun {a} {b} {c} =>
        instance_Bifunctor__GHC_Tuple_quint_type_x1_x2_x3__first ;
      second__ := fun {b} {c} {a} =>
        instance_Bifunctor__GHC_Tuple_quint_type_x1_x2_x3__second |}.

Local Definition instance_Bifunctor__GHC_Tuple_sext_type_x1_x2_x3_x4__bimap {inst_x1}
                                                                            {inst_x2} {inst_x3} {inst_x4} : forall {a}
                                                                                                                   {b}
                                                                                                                   {c}
                                                                                                                   {d},
                                                                                                              (a -> b) -> (c -> d) -> (GHC.Tuple.sext_type
                                                                                                              inst_x1
                                                                                                              inst_x2
                                                                                                              inst_x3
                                                                                                              inst_x4) a
                                                                                                              c -> (GHC.Tuple.sext_type
                                                                                                              inst_x1
                                                                                                              inst_x2
                                                                                                              inst_x3
                                                                                                              inst_x4) b
                                                                                                              d :=
  fun {a} {b} {c} {d} =>
    fun arg_29__ arg_30__ arg_31__ =>
      match arg_29__ , arg_30__ , arg_31__ with
        | f , g , pair (pair (pair (pair (pair x1 x2) x3) x4) a) b => pair (pair (pair
                                                                                 (pair (pair x1 x2) x3) x4) (f a)) (g b)
      end.

Local Definition instance_Bifunctor__GHC_Tuple_sext_type_x1_x2_x3_x4__first {inst_x1}
                                                                            {inst_x2} {inst_x3} {inst_x4} : forall {a}
                                                                                                                   {b}
                                                                                                                   {c},
                                                                                                              (a -> b) -> (GHC.Tuple.sext_type
                                                                                                              inst_x1
                                                                                                              inst_x2
                                                                                                              inst_x3
                                                                                                              inst_x4) a
                                                                                                              c -> (GHC.Tuple.sext_type
                                                                                                              inst_x1
                                                                                                              inst_x2
                                                                                                              inst_x3
                                                                                                              inst_x4) b
                                                                                                              c :=
  fun {a} {b} {c} =>
    fun arg_4__ =>
      match arg_4__ with
        | f => instance_Bifunctor__GHC_Tuple_sext_type_x1_x2_x3_x4__bimap f GHC.Base.id
      end.

Local Definition instance_Bifunctor__GHC_Tuple_sext_type_x1_x2_x3_x4__second {inst_x1}
                                                                             {inst_x2} {inst_x3} {inst_x4} : forall {b}
                                                                                                                    {c}
                                                                                                                    {a},
                                                                                                               (b -> c) -> (GHC.Tuple.sext_type
                                                                                                               inst_x1
                                                                                                               inst_x2
                                                                                                               inst_x3
                                                                                                               inst_x4)
                                                                                                               a
                                                                                                               b -> (GHC.Tuple.sext_type
                                                                                                               inst_x1
                                                                                                               inst_x2
                                                                                                               inst_x3
                                                                                                               inst_x4)
                                                                                                               a c :=
  fun {b} {c} {a} =>
    instance_Bifunctor__GHC_Tuple_sext_type_x1_x2_x3_x4__bimap GHC.Base.id.

Program Instance instance_Bifunctor__GHC_Tuple_sext_type_x1_x2_x3_x4_ {x1} {x2}
                                                                      {x3} {x4} : Bifunctor (GHC.Tuple.sext_type x1 x2
                                                                                            x3 x4) := fun _ k =>
    k {|bimap__ := fun {a} {b} {c} {d} =>
        instance_Bifunctor__GHC_Tuple_sext_type_x1_x2_x3_x4__bimap ;
      first__ := fun {a} {b} {c} =>
        instance_Bifunctor__GHC_Tuple_sext_type_x1_x2_x3_x4__first ;
      second__ := fun {b} {c} {a} =>
        instance_Bifunctor__GHC_Tuple_sext_type_x1_x2_x3_x4__second |}.

Local Definition instance_Bifunctor__GHC_Tuple_sept_type_x1_x2_x3_x4_x5__bimap {inst_x1}
                                                                               {inst_x2} {inst_x3} {inst_x4} {inst_x5}
    : forall {a} {b} {c} {d},
        (a -> b) -> (c -> d) -> (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4
        inst_x5) a c -> (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) b
        d :=
  fun {a} {b} {c} {d} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , g , pair (pair (pair (pair (pair (pair x1 x2) x3) x4) x5) a) b => pair
                                                                                (pair (pair (pair (pair (pair x1 x2) x3)
                                                                                                  x4) x5) (f a)) (g b)
      end.

Local Definition instance_Bifunctor__GHC_Tuple_sept_type_x1_x2_x3_x4_x5__first {inst_x1}
                                                                               {inst_x2} {inst_x3} {inst_x4} {inst_x5}
    : forall {a} {b} {c},
        (a -> b) -> (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) a
        c -> (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) b c :=
  fun {a} {b} {c} =>
    fun arg_4__ =>
      match arg_4__ with
        | f => instance_Bifunctor__GHC_Tuple_sept_type_x1_x2_x3_x4_x5__bimap f
               GHC.Base.id
      end.

Local Definition instance_Bifunctor__GHC_Tuple_sept_type_x1_x2_x3_x4_x5__second {inst_x1}
                                                                                {inst_x2} {inst_x3} {inst_x4} {inst_x5}
    : forall {b} {c} {a},
        (b -> c) -> (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) a
        b -> (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) a c :=
  fun {b} {c} {a} =>
    instance_Bifunctor__GHC_Tuple_sept_type_x1_x2_x3_x4_x5__bimap GHC.Base.id.

Program Instance instance_Bifunctor__GHC_Tuple_sept_type_x1_x2_x3_x4_x5_ {x1}
                                                                         {x2} {x3} {x4} {x5} : Bifunctor
                                                                                               (GHC.Tuple.sept_type x1
                                                                                               x2 x3 x4 x5) := fun _
                                                                                                                   k =>
    k {|bimap__ := fun {a} {b} {c} {d} =>
        instance_Bifunctor__GHC_Tuple_sept_type_x1_x2_x3_x4_x5__bimap ;
      first__ := fun {a} {b} {c} =>
        instance_Bifunctor__GHC_Tuple_sept_type_x1_x2_x3_x4_x5__first ;
      second__ := fun {b} {c} {a} =>
        instance_Bifunctor__GHC_Tuple_sept_type_x1_x2_x3_x4_x5__second |}.

Local Definition instance_Bifunctor_Data_Either_Either_bimap : forall {a}
                                                                      {b}
                                                                      {c}
                                                                      {d},
                                                                 (a -> b) -> (c -> d) -> Data.Either.Either a
                                                                 c -> Data.Either.Either b d :=
  fun {a} {b} {c} {d} =>
    fun arg_18__ arg_19__ arg_20__ =>
      match arg_18__ , arg_19__ , arg_20__ with
        | f , _ , Data.Either.Mk_Left a => Data.Either.Mk_Left (f a)
        | _ , g , Data.Either.Mk_Right b => Data.Either.Mk_Right (g b)
      end.

Local Definition instance_Bifunctor_Data_Either_Either_first : forall {a}
                                                                      {b}
                                                                      {c},
                                                                 (a -> b) -> Data.Either.Either a
                                                                 c -> Data.Either.Either b c :=
  fun {a} {b} {c} =>
    fun arg_4__ =>
      match arg_4__ with
        | f => instance_Bifunctor_Data_Either_Either_bimap f GHC.Base.id
      end.

Local Definition instance_Bifunctor_Data_Either_Either_second : forall {b}
                                                                       {c}
                                                                       {a},
                                                                  (b -> c) -> Data.Either.Either a
                                                                  b -> Data.Either.Either a c :=
  fun {b} {c} {a} => instance_Bifunctor_Data_Either_Either_bimap GHC.Base.id.


Program Instance instance_Bifunctor_sum : Bifunctor sum := fun _ k =>
    k {|bimap__ := fun {a} {b} {c} {d} => instance_Bifunctor_sum_bimap ;
      first__ := fun {a} {b} {c} => instance_Bifunctor_sum_first ;
      second__ := fun {b} {c} {a} => instance_Bifunctor_sum_second |}.


Local Definition instance_Bifunctor_Data_Functor_Const_Const_bimap : forall {a}
                                                                            {b}
                                                                            {c}
                                                                            {d},
                                                                       (a -> b) -> (c -> d) -> Data.Functor.Const.Const
                                                                       a c -> Data.Functor.Const.Const b d :=
  fun {a} {b} {c} {d} =>
    fun arg_13__ arg_14__ arg_15__ =>
      match arg_13__ , arg_14__ , arg_15__ with
        | f , _ , Data.Functor.Const.Mk_Const a => Data.Functor.Const.Mk_Const (f a)
      end.

Local Definition instance_Bifunctor_Data_Functor_Const_Const_first : forall {a}
                                                                            {b}
                                                                            {c},
                                                                       (a -> b) -> Data.Functor.Const.Const a
                                                                       c -> Data.Functor.Const.Const b c :=
  fun {a} {b} {c} =>
    fun arg_4__ =>
      match arg_4__ with
        | f => instance_Bifunctor_Data_Functor_Const_Const_bimap f GHC.Base.id
      end.

Local Definition instance_Bifunctor_Data_Functor_Const_Const_second : forall {b}
                                                                             {c}
                                                                             {a},
                                                                        (b -> c) -> Data.Functor.Const.Const a
                                                                        b -> Data.Functor.Const.Const a c :=
  fun {b} {c} {a} =>
    instance_Bifunctor_Data_Functor_Const_Const_bimap GHC.Base.id.

Program Instance instance_Bifunctor_Data_Functor_Const_Const : Bifunctor
                                                               Data.Functor.Const.Const := fun _ k =>
    k {|bimap__ := fun {a} {b} {c} {d} =>
        instance_Bifunctor_Data_Functor_Const_Const_bimap ;
      first__ := fun {a} {b} {c} =>
        instance_Bifunctor_Data_Functor_Const_Const_first ;
      second__ := fun {b} {c} {a} =>
        instance_Bifunctor_Data_Functor_Const_Const_second |}.

(* Skipping instance instance_Bifunctor__GHC_Generics_K1_i_ *)

(* Unbound variables:
     Data.Either.Either Data.Either.Mk_Left Data.Either.Mk_Right
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const GHC.Base.id
     GHC.Tuple.pair_type GHC.Tuple.quad_type GHC.Tuple.quint_type GHC.Tuple.sept_type
     GHC.Tuple.sext_type GHC.Tuple.triple_type pair
*)
