(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Lists.List.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

(* Translating `EqEither' failed: type/data families unsupported *)

Inductive Either a b : Type := Mk_Left : a -> Either a b
                            |  Mk_Right : b -> Either a b.

Arguments Mk_Left {_} {_} _.

Arguments Mk_Right {_} {_} _.
(* Converted value declarations: *)

Local Definition instance_GHC_Base_Functor__Data_Either_Either_a__fmap {inst_a}
    : forall {a} {b}, (a -> b) -> (Either inst_a) a -> (Either inst_a) b :=
  fun {a} {b} =>
    fun arg_81__ arg_82__ =>
      match arg_81__ , arg_82__ with
        | _ , Mk_Left x => Mk_Left x
        | f , Mk_Right y => Mk_Right (f y)
      end.

Local Definition instance_GHC_Base_Functor__Data_Either_Either_a__op_zlzd__ {inst_a}
    : forall {a} {b}, a -> (Either inst_a) b -> (Either inst_a) a :=
  fun {a} {b} =>
    fun x =>
      instance_GHC_Base_Functor__Data_Either_Either_a__fmap (GHC.Base.const x).

Program Instance instance_GHC_Base_Functor__Data_Either_Either_a_ {a}
  : GHC.Base.Functor (Either a) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor__Data_Either_Either_a__op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor__Data_Either_Either_a__fmap |}.

Local Definition instance_GHC_Base_Applicative__Data_Either_Either_e__op_zlztzg__ {inst_e}
    : forall {a} {b},
        (Either inst_e) (a -> b) -> (Either inst_e) a -> (Either inst_e) b :=
  fun {a} {b} =>
    fun arg_76__ arg_77__ =>
      match arg_76__ , arg_77__ with
        | Mk_Left e , _ => Mk_Left e
        | Mk_Right f , r => GHC.Base.fmap f r
      end.

Local Definition instance_GHC_Base_Applicative__Data_Either_Either_e__op_ztzg__ {inst_e}
    : forall {a} {b}, (Either inst_e) a -> (Either inst_e) b -> (Either inst_e) b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative__Data_Either_Either_e__op_zlztzg__ (GHC.Base.fmap
                                                                       (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative__Data_Either_Either_e__pure {inst_e}
    : forall {a}, a -> (Either inst_e) a :=
  fun {a} => Mk_Right.

Program Instance instance_GHC_Base_Applicative__Data_Either_Either_e_ {e}
  : GHC.Base.Applicative (Either e) := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative__Data_Either_Either_e__op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative__Data_Either_Either_e__op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative__Data_Either_Either_e__pure |}.

Local Definition instance_GHC_Base_Monad__Data_Either_Either_e__op_zgzg__ {inst_e}
    : forall {a} {b}, (Either inst_e) a -> (Either inst_e) b -> (Either inst_e) b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition instance_GHC_Base_Monad__Data_Either_Either_e__op_zgzgze__ {inst_e}
    : forall {a} {b},
        (Either inst_e) a -> (a -> (Either inst_e) b) -> (Either inst_e) b :=
  fun {a} {b} =>
    fun arg_71__ arg_72__ =>
      match arg_71__ , arg_72__ with
        | Mk_Left l , _ => Mk_Left l
        | Mk_Right r , k => k r
      end.

Local Definition instance_GHC_Base_Monad__Data_Either_Either_e__return_ {inst_e}
    : forall {a}, a -> (Either inst_e) a :=
  fun {a} => GHC.Base.pure.

Program Instance instance_GHC_Base_Monad__Data_Either_Either_e_ {e}
  : GHC.Base.Monad (Either e) := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad__Data_Either_Either_e__op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad__Data_Either_Either_e__op_zgzgze__ ;
      GHC.Base.return___ := fun {a} =>
        instance_GHC_Base_Monad__Data_Either_Either_e__return_ |}.

(* Translating `instance forall {a} {b}, forall `{GHC.Show.Show b}
   `{GHC.Show.Show a}, GHC.Show.Show (Data.Either.Either a b)' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance forall {a} {b}, forall `{GHC.Read.Read b}
   `{GHC.Read.Read a}, GHC.Read.Read (Data.Either.Either a b)' failed: OOPS! Cannot
   find information for class Qualified "GHC.Read" "Read" unsupported *)

Local Definition instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__compare {inst_a}
                                                                                                                    {inst_b}
                                                                                                                    `{GHC.Base.Ord
                                                                                                                    inst_b}
                                                                                                                    `{GHC.Base.Ord
                                                                                                                    inst_a}
    : Either inst_a inst_b -> Either inst_a inst_b -> comparison :=
  fun a b =>
    match a with
      | Mk_Left a1 => match b with
                        | Mk_Left b1 => (GHC.Base.compare a1 b1)
                        | _ => Lt
                      end
      | Mk_Right a1 => match b with
                         | Mk_Right b1 => (GHC.Base.compare a1 b1)
                         | _ => Gt
                       end
    end.

Local Definition instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zg__ {inst_a}
                                                                                                                    {inst_b}
                                                                                                                    `{GHC.Base.Ord
                                                                                                                    inst_b}
                                                                                                                    `{GHC.Base.Ord
                                                                                                                    inst_a}
    : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b =>
    match a with
      | Mk_Left a1 => match b with
                        | Mk_Left b1 => (a1 GHC.Base.> b1)
                        | _ => false
                      end
      | Mk_Right a1 => match b with
                         | Mk_Right b1 => (a1 GHC.Base.> b1)
                         | _ => true
                       end
    end.

Local Definition instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zgze__ {inst_a}
                                                                                                                      {inst_b}
                                                                                                                      `{GHC.Base.Ord
                                                                                                                      inst_b}
                                                                                                                      `{GHC.Base.Ord
                                                                                                                      inst_a}
    : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b =>
    match a with
      | Mk_Left a1 => match b with
                        | Mk_Left b1 => (a1 GHC.Base.>= b1)
                        | _ => false
                      end
      | Mk_Right a1 => match b with
                         | Mk_Right b1 => (a1 GHC.Base.>= b1)
                         | _ => true
                       end
    end.

Local Definition instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zl__ {inst_a}
                                                                                                                    {inst_b}
                                                                                                                    `{GHC.Base.Ord
                                                                                                                    inst_b}
                                                                                                                    `{GHC.Base.Ord
                                                                                                                    inst_a}
    : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b =>
    match a with
      | Mk_Left a1 => match b with
                        | Mk_Left b1 => (a1 GHC.Base.< b1)
                        | _ => true
                      end
      | Mk_Right a1 => match b with
                         | Mk_Right b1 => (a1 GHC.Base.< b1)
                         | _ => false
                       end
    end.

Local Definition instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zlze__ {inst_a}
                                                                                                                      {inst_b}
                                                                                                                      `{GHC.Base.Ord
                                                                                                                      inst_b}
                                                                                                                      `{GHC.Base.Ord
                                                                                                                      inst_a}
    : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b =>
    match a with
      | Mk_Left a1 => match b with
                        | Mk_Left b1 => (a1 GHC.Base.<= b1)
                        | _ => true
                      end
      | Mk_Right a1 => match b with
                         | Mk_Right b1 => (a1 GHC.Base.<= b1)
                         | _ => false
                       end
    end.

Local Definition instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__min {inst_a}
                                                                                                                {inst_b}
                                                                                                                `{GHC.Base.Ord
                                                                                                                inst_b}
                                                                                                                `{GHC.Base.Ord
                                                                                                                inst_a}
    : Either inst_a inst_b -> Either inst_a inst_b -> Either inst_a inst_b :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zlze__
       x y : bool
    then x
    else y.

Local Definition instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__max {inst_a}
                                                                                                                {inst_b}
                                                                                                                `{GHC.Base.Ord
                                                                                                                inst_b}
                                                                                                                `{GHC.Base.Ord
                                                                                                                inst_a}
    : Either inst_a inst_b -> Either inst_a inst_b -> Either inst_a inst_b :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zlze__
       x y : bool
    then y
    else x.

Local Definition instance_forall___GHC_Base_Eq__b____GHC_Base_Eq__a___GHC_Base_Eq___Data_Either_Either_a_b__op_zeze__ {inst_a}
                                                                                                                      {inst_b}
                                                                                                                      `{GHC.Base.Eq_
                                                                                                                      inst_b}
                                                                                                                      `{GHC.Base.Eq_
                                                                                                                      inst_a}
    : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun arg_25__ arg_26__ =>
    match arg_25__ , arg_26__ with
      | Mk_Left a1 , Mk_Left b1 => ((a1 GHC.Base.== b1))
      | Mk_Right a1 , Mk_Right b1 => ((a1 GHC.Base.== b1))
      | _ , _ => false
    end.

Local Definition instance_forall___GHC_Base_Eq__b____GHC_Base_Eq__a___GHC_Base_Eq___Data_Either_Either_a_b__op_zsze__ {inst_a}
                                                                                                                      {inst_b}
                                                                                                                      `{_
                                                                                                                        : GHC.Base.Eq_
                                                                                                                          inst_b}
                                                                                                                      `{_
                                                                                                                        : GHC.Base.Eq_
                                                                                                                          inst_a}
    : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun arg_34__ arg_35__ =>
    match arg_34__ , arg_35__ with
      | a , b => negb
                 (instance_forall___GHC_Base_Eq__b____GHC_Base_Eq__a___GHC_Base_Eq___Data_Either_Either_a_b__op_zeze__
                 a b)
    end.

Program Instance instance_forall___GHC_Base_Eq__b____GHC_Base_Eq__a___GHC_Base_Eq___Data_Either_Either_a_b_ {a}
                                                                                                            {b}
                                                                                                            `{GHC.Base.Eq_
                                                                                                            b}
                                                                                                            `{GHC.Base.Eq_
                                                                                                            a}
  : GHC.Base.Eq_ (Either a b) := fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__b____GHC_Base_Eq__a___GHC_Base_Eq___Data_Either_Either_a_b__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__b____GHC_Base_Eq__a___GHC_Base_Eq___Data_Either_Either_a_b__op_zsze__ |}.

Program Instance instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b_ {a}
                                                                                                            {b}
                                                                                                            `{GHC.Base.Ord
                                                                                                            b}
                                                                                                            `{GHC.Base.Ord
                                                                                                            a}
  : GHC.Base.Ord (Either a b) := fun _ k =>
    k
    {|GHC.Base.op_zl____ := instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zl__ ;
    GHC.Base.op_zlze____ := instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zlze__ ;
    GHC.Base.op_zg____ := instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zg__ ;
    GHC.Base.op_zgze____ := instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__op_zgze__ ;
    GHC.Base.compare__ := instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__compare ;
    GHC.Base.max__ := instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__max ;
    GHC.Base.min__ := instance_forall___GHC_Base_Ord_b____GHC_Base_Ord_a___GHC_Base_Ord__Data_Either_Either_a_b__min |}.

Definition either {a} {c} {b} : (a -> c) -> (b -> c) -> Either a b -> c :=
  fun arg_10__ arg_11__ arg_12__ =>
    match arg_10__ , arg_11__ , arg_12__ with
      | f , _ , Mk_Left x => f x
      | _ , g , Mk_Right y => g y
    end.

Definition partitionEithers {a} {b} : list (Either a b) -> list a * list b :=
  let right :=
    fun arg_16__ arg_17__ =>
      match arg_16__ , arg_17__ with
        | a , pair l r => pair l (cons a r)
      end in
  let left :=
    fun arg_20__ arg_21__ =>
      match arg_20__ , arg_21__ with
        | a , pair l r => pair (cons a l) r
      end in
  GHC.Base.foldr (either left right) (pair nil nil).

Definition isLeft {a} {b} : Either a b -> bool :=
  fun arg_2__ => match arg_2__ with | Mk_Left _ => true | Mk_Right _ => false end.

Definition isRight {a} {b} : Either a b -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Left _ => false | Mk_Right _ => true end.

Definition lefts {a} {b} : list (Either a b) -> list a :=
  fun x =>
    let cont_7__ arg_8__ :=
      match arg_8__ with
        | Mk_Left a => cons a nil
        | _ => nil
      end in
    Coq.Lists.List.flat_map cont_7__ x.

Definition rights {a} {b} : list (Either a b) -> list b :=
  fun x =>
    let cont_4__ arg_5__ :=
      match arg_5__ with
        | Mk_Right a => cons a nil
        | _ => nil
      end in
    Coq.Lists.List.flat_map cont_4__ x.

(* Unbound variables:
     Gt Lt bool comparison cons false list negb nil op_zt__ pair true
     Coq.Lists.List.flat_map GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Ord GHC.Base.compare GHC.Base.const GHC.Base.fmap
     GHC.Base.foldr GHC.Base.id GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_ztzg__
     GHC.Base.pure
*)
