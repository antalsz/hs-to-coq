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

Inductive Either a b : Type
  := | Left : a -> Either a b
  |  Right : b -> Either a b.

Arguments Left {_} {_} _.

Arguments Right {_} {_} _.

(* Converted value declarations: *)

Local Definition Eq___Either_op_zeze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
  `{GHC.Base.Eq_ inst_b}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Left a1, Left b1 => ((a1 GHC.Base.== b1))
    | Right a1, Right b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___Either_op_zsze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
  `{GHC.Base.Eq_ inst_b}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun x y => negb (Eq___Either_op_zeze__ x y).

Program Instance Eq___Either {a} {b} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b}
   : GHC.Base.Eq_ (Either a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Either_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Either_op_zsze__ |}.

Local Definition Ord__Either_op_zl__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
  `{GHC.Base.Ord inst_b}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b =>
    match a with
    | Left a1 => match b with | Left b1 => (a1 GHC.Base.< b1) | _ => true end
    | Right a1 => match b with | Right b1 => (a1 GHC.Base.< b1) | _ => false end
    end.

Local Definition Ord__Either_op_zlze__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
  `{GHC.Base.Ord inst_b}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b => negb (Ord__Either_op_zl__ b a).

Local Definition Ord__Either_op_zg__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
  `{GHC.Base.Ord inst_b}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b => Ord__Either_op_zl__ b a.

Local Definition Ord__Either_op_zgze__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
  `{GHC.Base.Ord inst_b}
   : Either inst_a inst_b -> Either inst_a inst_b -> bool :=
  fun a b => negb (Ord__Either_op_zl__ a b).

Local Definition Ord__Either_compare {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
  `{GHC.Base.Ord inst_b}
   : Either inst_a inst_b -> Either inst_a inst_b -> comparison :=
  fun a b =>
    match a with
    | Left a1 => match b with | Left b1 => (GHC.Base.compare a1 b1) | _ => Lt end
    | Right a1 => match b with | Right b1 => (GHC.Base.compare a1 b1) | _ => Gt end
    end.

Local Definition Ord__Either_max {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
  `{GHC.Base.Ord inst_b}
   : Either inst_a inst_b -> Either inst_a inst_b -> Either inst_a inst_b :=
  fun x y => if Ord__Either_op_zlze__ x y : bool then y else x.

Local Definition Ord__Either_min {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
  `{GHC.Base.Ord inst_b}
   : Either inst_a inst_b -> Either inst_a inst_b -> Either inst_a inst_b :=
  fun x y => if Ord__Either_op_zlze__ x y : bool then x else y.

Program Instance Ord__Either {a} {b} `{GHC.Base.Ord a} `{GHC.Base.Ord b}
   : GHC.Base.Ord (Either a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Either_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Either_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Either_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Either_op_zgze__ ;
           GHC.Base.compare__ := Ord__Either_compare ;
           GHC.Base.max__ := Ord__Either_max ;
           GHC.Base.min__ := Ord__Either_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Either.Read__Either' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Either.Show__Either' *)

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
  fun {a} {b} => Functor__Either_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Either {a} : GHC.Base.Functor (Either a) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Either_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Either_op_zlzd__ |}.

Local Definition Semigroup__Either_op_zlzlzgzg__ {inst_a} {inst_b}
   : (Either inst_a inst_b) -> (Either inst_a inst_b) -> (Either inst_a inst_b) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Left _, b => b
    | a, _ => a
    end.

Program Instance Semigroup__Either {a} {b} : GHC.Base.Semigroup (Either a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Either_op_zlzlzgzg__ |}.

Local Definition Applicative__Either_op_zlztzg__ {inst_e}
   : forall {a} {b},
     (Either inst_e) (a -> b) -> (Either inst_e) a -> (Either inst_e) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Left e, _ => Left e
      | Right f, r => GHC.Base.fmap f r
      end.

Local Definition Applicative__Either_liftA2 {inst_e}
   : forall {a} {b} {c},
     (a -> b -> c) -> (Either inst_e) a -> (Either inst_e) b -> (Either inst_e) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Either_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Either_op_ztzg__ {inst_e}
   : forall {a} {b},
     (Either inst_e) a -> (Either inst_e) b -> (Either inst_e) b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Either_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Either_pure {inst_e}
   : forall {a}, a -> (Either inst_e) a :=
  fun {a} => Right.

Program Instance Applicative__Either {e} : GHC.Base.Applicative (Either e) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Either_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Either_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Either_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Either_pure |}.

Local Definition Monad__Either_op_zgzgze__ {inst_e}
   : forall {a} {b},
     (Either inst_e) a -> (a -> (Either inst_e) b) -> (Either inst_e) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Left l, _ => Left l
      | Right r, k => k r
      end.

Local Definition Monad__Either_op_zgzg__ {inst_e}
   : forall {a} {b},
     (Either inst_e) a -> (Either inst_e) b -> (Either inst_e) b :=
  fun {a} {b} => fun m k => Monad__Either_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Either_return_ {inst_e}
   : forall {a}, a -> (Either inst_e) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Either {e} : GHC.Base.Monad (Either e) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Either_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Either_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Either_return_ |}.

Definition either {a} {c} {b} : (a -> c) -> (b -> c) -> Either a b -> c :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, _, Left x => f x
    | _, g, Right y => g y
    end.

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

Definition fromLeft {a} {b} : a -> Either a b -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Left a => a
    | a, _ => a
    end.

Definition fromRight {b} {a} : b -> Either a b -> b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Right b => b
    | b, _ => b
    end.

(* External variables:
     Gt Lt bool comparison cons false list negb nil op_zt__ pair true
     Coq.Lists.List.flat_map GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Ord GHC.Base.Semigroup GHC.Base.compare
     GHC.Base.compare__ GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr
     GHC.Base.id GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return___
*)
