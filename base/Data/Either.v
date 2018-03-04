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

Inductive Either a b : Type
  := Left : a -> Either a b
  |  Right : b -> Either a b.

Arguments Left {_} {_} _.

Arguments Right {_} {_} _.
(* Converted value declarations: *)

Local Definition Functor__Either_fmap {inst_a}
   : forall {a} {b}, (a -> b) -> (Either inst_a) a -> (Either inst_a) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Left x => Left x
      | f, Right y => Right (f y)
      end.

Local Definition Functor__Either_op_zlzd__ {inst_a}
   : forall {a} {b}, a -> (Either inst_a) b -> (Either inst_a) a :=
  fun {a} {b} => fun x => Functor__Either_fmap (GHC.Base.const x).

Program Instance Functor__Either {a} : GHC.Base.Functor (Either a) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Either_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Either_fmap |}.

Local Definition Applicative__Either_op_zlztzg__ {inst_e}
   : forall {a} {b},
     (Either inst_e) (a -> b) -> (Either inst_e) a -> (Either inst_e) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Left e, _ => Left e
      | Right f, r => GHC.Base.fmap f r
      end.

Local Definition Applicative__Either_op_ztzg__ {inst_e}
   : forall {a} {b},
     (Either inst_e) a -> (Either inst_e) b -> (Either inst_e) b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Either_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x)
                                      y.

Local Definition Applicative__Either_pure {inst_e}
   : forall {a}, a -> (Either inst_e) a :=
  fun {a} => Right.

Program Instance Applicative__Either {e} : GHC.Base.Applicative (Either e) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Either_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Either_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Either_pure |}.

Local Definition Monad__Either_op_zgzg__ {inst_e}
   : forall {a} {b},
     (Either inst_e) a -> (Either inst_e) b -> (Either inst_e) b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Either_op_zgzgze__ {inst_e}
   : forall {a} {b},
     (Either inst_e) a -> (a -> (Either inst_e) b) -> (Either inst_e) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Left l, _ => Left l
      | Right r, k => k r
      end.

Local Definition Monad__Either_return_ {inst_e}
   : forall {a}, a -> (Either inst_e) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Either {e} : GHC.Base.Monad (Either e) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Either_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Either_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Either_return_ |}.

(* Translating `instance forall {a} {b}, forall `{GHC.Show.Show b}
   `{GHC.Show.Show a}, GHC.Show.Show (Data.Either.Either a b)' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance forall {a} {b}, forall `{GHC.Read.Read b}
   `{GHC.Read.Read a}, GHC.Read.Read (Data.Either.Either a b)' failed: OOPS! Cannot
   find information for class Qualified "GHC.Read" "Read" unsupported *)

Local Definition Ord__Either_compare {inst_a} {inst_b} `{GHC.Base.Ord inst_b}
  `{GHC.Base.Ord inst_a}
   : Either inst_a inst_b -> Either inst_a inst_b -> comparison :=
  fun a b =>
    match a with
    | Left a1 => match b with | Left b1 => (GHC.Base.compare a1 b1) | _ => Lt end
    | Right a1 => match b with | Right b1 => (GHC.Base.compare a1 b1) | _ => Gt end
    end.

Local Definition Ord__Either_op_zg__ {inst_a} {inst_b} `{GHC.Base.Ord inst_b}
  `{GHC.Base.Ord inst_a}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b =>
    match a with
    | Left a1 => match b with | Left b1 => (a1 GHC.Base.> b1) | _ => false end
    | Right a1 => match b with | Right b1 => (a1 GHC.Base.> b1) | _ => true end
    end.

Local Definition Ord__Either_op_zgze__ {inst_a} {inst_b} `{GHC.Base.Ord inst_b}
  `{GHC.Base.Ord inst_a}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b =>
    match a with
    | Left a1 => match b with | Left b1 => (a1 GHC.Base.>= b1) | _ => false end
    | Right a1 => match b with | Right b1 => (a1 GHC.Base.>= b1) | _ => true end
    end.

Local Definition Ord__Either_op_zl__ {inst_a} {inst_b} `{GHC.Base.Ord inst_b}
  `{GHC.Base.Ord inst_a}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b =>
    match a with
    | Left a1 => match b with | Left b1 => (a1 GHC.Base.< b1) | _ => true end
    | Right a1 => match b with | Right b1 => (a1 GHC.Base.< b1) | _ => false end
    end.

Local Definition Ord__Either_op_zlze__ {inst_a} {inst_b} `{GHC.Base.Ord inst_b}
  `{GHC.Base.Ord inst_a}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b =>
    match a with
    | Left a1 => match b with | Left b1 => (a1 GHC.Base.<= b1) | _ => true end
    | Right a1 => match b with | Right b1 => (a1 GHC.Base.<= b1) | _ => false end
    end.

Local Definition Ord__Either_min {inst_a} {inst_b} `{GHC.Base.Ord inst_b}
  `{GHC.Base.Ord inst_a}
   : Either inst_a inst_b -> Either inst_a inst_b -> Either inst_a inst_b :=
  fun x y => if Ord__Either_op_zlze__ x y : bool then x else y.

Local Definition Ord__Either_max {inst_a} {inst_b} `{GHC.Base.Ord inst_b}
  `{GHC.Base.Ord inst_a}
   : Either inst_a inst_b -> Either inst_a inst_b -> Either inst_a inst_b :=
  fun x y => if Ord__Either_op_zlze__ x y : bool then y else x.

Local Definition Eq___Either_op_zeze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_b}
  `{GHC.Base.Eq_ inst_a}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Left a1, Left b1 => ((a1 GHC.Base.== b1))
    | Right a1, Right b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___Either_op_zsze__ {inst_a} {inst_b} `{_
   : GHC.Base.Eq_ inst_b} `{_ : GHC.Base.Eq_ inst_a}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun arg_34__ arg_35__ =>
    match arg_34__, arg_35__ with
    | a, b => negb (Eq___Either_op_zeze__ a b)
    end.

Program Instance Eq___Either {a} {b} `{GHC.Base.Eq_ b} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Either a b) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Either_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Either_op_zsze__ |}.

Program Instance Ord__Either {a} {b} `{GHC.Base.Ord b} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Either a b) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Either_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Either_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Either_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Either_op_zgze__ ;
         GHC.Base.compare__ := Ord__Either_compare ;
         GHC.Base.max__ := Ord__Either_max ;
         GHC.Base.min__ := Ord__Either_min |}.

Definition either {a} {c} {b} : (a -> c) -> (b -> c) -> Either a b -> c :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, _, Left x => f x
    | _, g, Right y => g y
    end.

Definition partitionEithers {a} {b}
   : list (Either a b) -> (list a * list b)%type :=
  let right_ :=
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | a, pair l r => pair l (cons a r)
      end in
  let left_ :=
    fun arg_4__ arg_5__ =>
      match arg_4__, arg_5__ with
      | a, pair l r => pair (cons a l) r
      end in
  GHC.Base.foldr (either left_ right_) (pair nil nil).

Definition isLeft {a} {b} : Either a b -> bool :=
  fun arg_0__ => match arg_0__ with | Left _ => true | Right _ => false end.

Definition isRight {a} {b} : Either a b -> bool :=
  fun arg_0__ => match arg_0__ with | Left _ => false | Right _ => true end.

Definition lefts {a} {b} : list (Either a b) -> list a :=
  fun x =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | Left a => cons a nil
      | _ => nil
      end in
    Coq.Lists.List.flat_map cont_0__ x.

Definition rights {a} {b} : list (Either a b) -> list b :=
  fun x =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | Right a => cons a nil
      | _ => nil
      end in
    Coq.Lists.List.flat_map cont_0__ x.

(* Unbound variables:
     Gt Lt bool comparison cons false list negb nil op_zt__ pair true
     Coq.Lists.List.flat_map GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Ord GHC.Base.compare GHC.Base.const GHC.Base.fmap
     GHC.Base.foldr GHC.Base.id GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_ztzg__
     GHC.Base.pure
*)
