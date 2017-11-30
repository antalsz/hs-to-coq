(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Program.Basics.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.List.NonEmpty.
Require Data.Maybe.
Require Data.Monoid.
Require Data.Proxy.
Require Data.Traversable.
Require Data.Void.
Require GHC.Base.
Require GHC.Enum.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive WrappedMonoid m : Type := WrapMonoid : m -> WrappedMonoid m.

Record Semigroup__Dict a := Semigroup__Dict_Build {
  op_zlzg____ : a -> a -> a ;
  sconcat__ : Data.List.NonEmpty.NonEmpty a -> a ;
  stimes__ : forall {b}, forall `{GHC.Real.Integral b}, b -> a -> a }.

Definition Semigroup a :=
  forall r, (Semigroup__Dict a -> r) -> r.

Existing Class Semigroup.

Definition op_zlzg__ `{g : Semigroup a} : a -> a -> a :=
  g _ (op_zlzg____ a).

Definition sconcat `{g : Semigroup a} : Data.List.NonEmpty.NonEmpty a -> a :=
  g _ (sconcat__ a).

Definition stimes `{g : Semigroup a} : forall {b},
                                         forall `{GHC.Real.Integral b}, b -> a -> a :=
  g _ (stimes__ a).

Notation "'_<>_'" := (op_zlzg__).

Infix "<>" := (_<>_) (at level 70).

Inductive Option a : Type := Mk_Option : option a -> Option a.

Inductive Min a : Type := Mk_Min : a -> Min a.

Inductive Max a : Type := Mk_Max : a -> Max a.

Inductive Last a : Type := Mk_Last : a -> Last a.

Inductive First a : Type := Mk_First : a -> First a.

Inductive Arg a b : Type := Mk_Arg : a -> b -> Arg a b.

Definition ArgMax a b :=
  (Max (Arg a b))%type.

Definition ArgMin a b :=
  (Min (Arg a b))%type.

Arguments WrapMonoid {_} _.

Arguments Mk_Option {_} _.

Arguments Mk_Min {_} _.

Arguments Mk_Max {_} _.

Arguments Mk_Last {_} _.

Arguments Mk_First {_} _.

Arguments Mk_Arg {_} {_} _ _.

Definition unwrapMonoid {m} (arg_15__ : WrappedMonoid m) :=
  match arg_15__ with
    | WrapMonoid unwrapMonoid => unwrapMonoid
  end.

Definition getOption {a} (arg_16__ : Option a) :=
  match arg_16__ with
    | Mk_Option getOption => getOption
  end.

Definition getMin {a} (arg_17__ : Min a) :=
  match arg_17__ with
    | Mk_Min getMin => getMin
  end.

Definition getMax {a} (arg_18__ : Max a) :=
  match arg_18__ with
    | Mk_Max getMax => getMax
  end.

Definition getLast {a} (arg_19__ : Last a) :=
  match arg_19__ with
    | Mk_Last getLast => getLast
  end.

Definition getFirst {a} (arg_20__ : First a) :=
  match arg_20__ with
    | Mk_First getFirst => getFirst
  end.
(* Midamble *)

Require Import GHC.Prim.
Instance Unpeel_WrappedMonoid a : Unpeel (WrappedMonoid a) a := Build_Unpeel _ _ unwrapMonoid WrapMonoid.
Instance Unpeel_Last  a : Unpeel (Last a) a := Build_Unpeel _ _ getLast Mk_Last.
Instance Unpeel_First  a : Unpeel (First a) a := Build_Unpeel _ _ getFirst Mk_First.
Instance Unpeel_Max  a : Unpeel (Max a) a := Build_Unpeel _ _ getMax Mk_Max.
Instance Unpeel_Min  a : Unpeel (Min a) a := Build_Unpeel _ _ getMin Mk_Min.
Instance Unpeel_Option  a : Unpeel (Option a) (option a) := Build_Unpeel _ _ getOption Mk_Option.

(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom unsafeFix : forall {a}, (a -> a) -> a.

Local Definition Semigroup__unit_op_zlzg__ : unit -> unit -> unit :=
  fun arg_378__ arg_379__ => tt.

Local Definition Semigroup__unit_sconcat : Data.List.NonEmpty.NonEmpty
                                           unit -> unit :=
  fun arg_380__ => tt.

Local Definition Semigroup__unit_stimes : forall {b},
                                            forall `{GHC.Real.Integral b}, b -> unit -> unit :=
  fun {b} `{GHC.Real.Integral b} => fun arg_381__ arg_382__ => tt.

Program Instance Semigroup__unit : Semigroup unit := fun _ k =>
    k {|op_zlzg____ := Semigroup__unit_op_zlzg__ ;
      sconcat__ := Semigroup__unit_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__unit_stimes |}.

Local Definition Semigroup__arrow_op_zlzg__ {inst_b} {inst_a} `{Semigroup
                                            inst_b} : (inst_a -> inst_b) -> (inst_a -> inst_b) -> (inst_a -> inst_b) :=
  fun f g => fun a => f a <> g a.

Local Definition Semigroup__arrow_sconcat {inst_b} {inst_a} `{Semigroup inst_b}
    : Data.List.NonEmpty.NonEmpty (inst_a -> inst_b) -> (inst_a -> inst_b) :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__arrow_op_zlzg__ b (go c cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

Local Definition Semigroup__arrow_stimes {inst_b} {inst_a} `{Semigroup inst_b}
    : forall {b},
        forall `{GHC.Real.Integral b}, b -> (inst_a -> inst_b) -> (inst_a -> inst_b) :=
  fun {b} `{GHC.Real.Integral b} => fun n f e => stimes n (f e).

Program Instance Semigroup__arrow {b} {a} `{Semigroup b} : Semigroup (a -> b) :=
  fun _ k =>
    k {|op_zlzg____ := Semigroup__arrow_op_zlzg__ ;
      sconcat__ := Semigroup__arrow_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__arrow_stimes |}.

Local Definition Semigroup__list_op_zlzg__ {inst_a} : list inst_a -> list
                                                      inst_a -> list inst_a :=
  Coq.Init.Datatypes.app.

Local Definition Semigroup__list_sconcat {inst_a} : Data.List.NonEmpty.NonEmpty
                                                    (list inst_a) -> list inst_a :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__list_op_zlzg__ b (go c cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

Local Definition Semigroup__list_stimes {inst_a} : forall {b},
                                                     forall `{GHC.Real.Integral b}, b -> list inst_a -> list inst_a :=
  fun {b} `{GHC.Real.Integral b} =>
    fun n x =>
      let rep :=
        unsafeFix (fun rep arg_367__ =>
                    let j_370__ :=
                      match arg_367__ with
                        | i => Coq.Init.Datatypes.app x (rep (i GHC.Num.- GHC.Num.fromInteger 1))
                      end in
                    match arg_367__ with
                      | num_368__ => if num_368__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                                     then nil
                                     else j_370__
                    end) in
      let j_373__ := rep n in
      if n GHC.Base.< GHC.Num.fromInteger 0 : bool
      then GHC.Base.errorWithoutStackTrace (GHC.Base.hs_string__
                                           "stimes: [], negative multiplier")
      else j_373__.

Program Instance Semigroup__list {a} : Semigroup (list a) := fun _ k =>
    k {|op_zlzg____ := Semigroup__list_op_zlzg__ ;
      sconcat__ := Semigroup__list_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__list_stimes |}.

Local Definition Semigroup__option_op_zlzg__ {inst_a} `{Semigroup inst_a}
    : (option inst_a) -> (option inst_a) -> (option inst_a) :=
  fun arg_355__ arg_356__ =>
    match arg_355__ , arg_356__ with
      | None , b => b
      | a , None => a
      | Some a , Some b => Some (a <> b)
    end.

Local Definition Semigroup__option_sconcat {inst_a} `{Semigroup inst_a}
    : Data.List.NonEmpty.NonEmpty (option inst_a) -> (option inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__option_op_zlzg__ b (go c cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

Local Definition Semigroup__option_stimes {inst_a} `{Semigroup inst_a}
    : forall {b},
        forall `{GHC.Real.Integral b}, b -> (option inst_a) -> (option inst_a) :=
  fun {b} `{GHC.Real.Integral b} =>
    fun arg_359__ arg_360__ =>
      match arg_359__ , arg_360__ with
        | _ , None => None
        | n , Some a => let scrut_361__ := GHC.Base.compare n (GHC.Num.fromInteger 0) in
                        match scrut_361__ with
                          | Lt => GHC.Base.errorWithoutStackTrace (GHC.Base.hs_string__
                                                                  "stimes: Maybe, negative multiplier")
                          | Eq => None
                          | Gt => Some (stimes n a)
                        end
      end.

Program Instance Semigroup__option {a} `{Semigroup a} : Semigroup (option a) :=
  fun _ k =>
    k {|op_zlzg____ := Semigroup__option_op_zlzg__ ;
      sconcat__ := Semigroup__option_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__option_stimes |}.

Local Definition Semigroup__Either_op_zlzg__ {inst_a} {inst_b}
    : (Data.Either.Either inst_a inst_b) -> (Data.Either.Either inst_a
      inst_b) -> (Data.Either.Either inst_a inst_b) :=
  fun arg_352__ arg_353__ =>
    match arg_352__ , arg_353__ with
      | Data.Either.Left _ , b => b
      | a , _ => a
    end.

Local Definition Semigroup__Either_sconcat {inst_a} {inst_b}
    : Data.List.NonEmpty.NonEmpty (Data.Either.Either inst_a
                                  inst_b) -> (Data.Either.Either inst_a inst_b) :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__Either_op_zlzg__ b (go c cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

(* Skipping instance Semigroup__op_zt__ *)

(* Skipping instance Semigroup__op_zt__ *)

(* Skipping instance Semigroup__op_zt__ *)

(* Skipping instance Semigroup__op_zt__ *)

Local Definition Semigroup__comparison_op_zlzg__
    : comparison -> comparison -> comparison :=
  fun arg_317__ arg_318__ =>
    match arg_317__ , arg_318__ with
      | Lt , _ => Lt
      | Eq , y => y
      | Gt , _ => Gt
    end.

Local Definition Semigroup__comparison_sconcat : Data.List.NonEmpty.NonEmpty
                                                 comparison -> comparison :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__comparison_op_zlzg__ b (go c
                                                                                                              cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

Local Definition Semigroup__Dual_op_zlzg__ {inst_a} `{Semigroup inst_a}
    : (Data.Monoid.Dual inst_a) -> (Data.Monoid.Dual inst_a) -> (Data.Monoid.Dual
      inst_a) :=
  fun arg_309__ arg_310__ =>
    match arg_309__ , arg_310__ with
      | Data.Monoid.Mk_Dual a , Data.Monoid.Mk_Dual b => Data.Monoid.Mk_Dual (b <> a)
    end.

Local Definition Semigroup__Dual_sconcat {inst_a} `{Semigroup inst_a}
    : Data.List.NonEmpty.NonEmpty (Data.Monoid.Dual inst_a) -> (Data.Monoid.Dual
      inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__Dual_op_zlzg__ b (go c cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

Local Definition Semigroup__Dual_stimes {inst_a} `{Semigroup inst_a}
    : forall {b},
        forall `{GHC.Real.Integral b},
          b -> (Data.Monoid.Dual inst_a) -> (Data.Monoid.Dual inst_a) :=
  fun {b} `{GHC.Real.Integral b} =>
    fun arg_313__ arg_314__ =>
      match arg_313__ , arg_314__ with
        | n , Data.Monoid.Mk_Dual a => Data.Monoid.Mk_Dual (stimes n a)
      end.

Program Instance Semigroup__Dual {a} `{Semigroup a} : Semigroup
                                                      (Data.Monoid.Dual a) := fun _ k =>
    k {|op_zlzg____ := Semigroup__Dual_op_zlzg__ ;
      sconcat__ := Semigroup__Dual_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__Dual_stimes |}.

(* Skipping instance Semigroup__Endo *)

Local Definition Semigroup__All_op_zlzg__
    : Data.Monoid.All -> Data.Monoid.All -> Data.Monoid.All :=
  GHC.Prim.coerce andb.

Local Definition Semigroup__All_sconcat : Data.List.NonEmpty.NonEmpty
                                          Data.Monoid.All -> Data.Monoid.All :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__All_op_zlzg__ b (go c cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

Local Definition Semigroup__Any_op_zlzg__
    : Data.Monoid.Any -> Data.Monoid.Any -> Data.Monoid.Any :=
  GHC.Prim.coerce orb.

Local Definition Semigroup__Any_sconcat : Data.List.NonEmpty.NonEmpty
                                          Data.Monoid.Any -> Data.Monoid.Any :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__Any_op_zlzg__ b (go c cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

(* Skipping instance Semigroup__Sum *)

(* Skipping instance Semigroup__Product *)

(* Skipping instance Semigroup__Const *)

(* Skipping instance Semigroup__First *)

(* Skipping instance Semigroup__Last *)

(* Skipping instance Semigroup__Alt *)

Local Definition Semigroup__Void_op_zlzg__
    : Data.Void.Void -> Data.Void.Void -> Data.Void.Void :=
  fun arg_281__ arg_282__ => match arg_281__ , arg_282__ with | a , _ => a end.

Local Definition Semigroup__Void_sconcat : Data.List.NonEmpty.NonEmpty
                                           Data.Void.Void -> Data.Void.Void :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__Void_op_zlzg__ b (go c cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

Local Definition Semigroup__NonEmpty_op_zlzg__ {inst_a}
    : (Data.List.NonEmpty.NonEmpty inst_a) -> (Data.List.NonEmpty.NonEmpty
      inst_a) -> (Data.List.NonEmpty.NonEmpty inst_a) :=
  fun arg_277__ arg_278__ =>
    match arg_277__ , arg_278__ with
      | Data.List.NonEmpty.NEcons a as_ , Data.List.NonEmpty.NEcons b bs =>
        Data.List.NonEmpty.NEcons a (Coq.Init.Datatypes.app as_ (cons b bs))
    end.

Local Definition Semigroup__NonEmpty_sconcat {inst_a}
    : Data.List.NonEmpty.NonEmpty (Data.List.NonEmpty.NonEmpty
                                  inst_a) -> (Data.List.NonEmpty.NonEmpty inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let go :=
                                             unsafeFix (fun go arg_1__ arg_2__ =>
                                                         match arg_1__ , arg_2__ with
                                                           | b , cons c cs => Semigroup__NonEmpty_op_zlzg__ b (go c cs)
                                                           | b , nil => b
                                                         end) in
                                           go a as_
    end.

Local Definition Semigroup__NonEmpty_stimes {inst_a} : forall {b},
                                                         forall `{GHC.Real.Integral b},
                                                           b -> (Data.List.NonEmpty.NonEmpty
                                                           inst_a) -> (Data.List.NonEmpty.NonEmpty inst_a) :=
  fun {b} `{GHC.Real.Integral b} =>
    fun y0 x0 =>
      let g :=
        unsafeFix (fun g x y z =>
                    let j_7__ :=
                      g (Semigroup__NonEmpty_op_zlzg__ x x) (GHC.Real.quot (GHC.Enum.pred y)
                                                                           (GHC.Num.fromInteger 2))
                      (Semigroup__NonEmpty_op_zlzg__ x z) in
                    let j_8__ :=
                      if y GHC.Base.== GHC.Num.fromInteger 1 : bool
                      then Semigroup__NonEmpty_op_zlzg__ x z
                      else j_7__ in
                    if GHC.Real.even y : bool
                    then g (Semigroup__NonEmpty_op_zlzg__ x x) (GHC.Real.quot y (GHC.Num.fromInteger
                                                                              2)) z
                    else j_8__) in
      let f :=
        unsafeFix (fun f x y =>
                    let j_10__ :=
                      g (Semigroup__NonEmpty_op_zlzg__ x x) (GHC.Real.quot (GHC.Enum.pred y)
                                                                           (GHC.Num.fromInteger 2)) x in
                    let j_11__ :=
                      if y GHC.Base.== GHC.Num.fromInteger 1 : bool
                      then x
                      else j_10__ in
                    if GHC.Real.even y : bool
                    then f (Semigroup__NonEmpty_op_zlzg__ x x) (GHC.Real.quot y (GHC.Num.fromInteger
                                                                              2))
                    else j_11__) in
      let j_13__ := f x0 y0 in
      if y0 GHC.Base.<= GHC.Num.fromInteger 0 : bool
      then GHC.Base.errorWithoutStackTrace (GHC.Base.hs_string__
                                           "stimes: positive multiplier expected")
      else j_13__.

Program Instance Semigroup__NonEmpty {a} : Semigroup
                                           (Data.List.NonEmpty.NonEmpty a) := fun _ k =>
    k {|op_zlzg____ := Semigroup__NonEmpty_op_zlzg__ ;
      sconcat__ := Semigroup__NonEmpty_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__NonEmpty_stimes |}.

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Data.Semigroup.Min a)' failed: OOPS! Cannot find information
   for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Enum a}, GHC.Enum.Enum
   (Data.Semigroup.Min a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Enum" "Enum" unsupported *)

(* Skipping instance Semigroup__Min *)

(* Skipping instance Monoid__Min *)

Local Definition Functor__Min_fmap : forall {a} {b},
                                       (a -> b) -> Min a -> Min b :=
  fun {a} {b} =>
    fun arg_272__ arg_273__ =>
      match arg_272__ , arg_273__ with
        | f , Mk_Min x => Mk_Min (f x)
      end.

Local Definition Functor__Min_op_zlzd__ : forall {a} {b}, a -> Min b -> Min a :=
  fun {a} {b} => fun x => Functor__Min_fmap (GHC.Base.const x).

Program Instance Functor__Min : GHC.Base.Functor Min := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Min_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Min_fmap |}.

Local Definition Foldable__Min_foldMap : forall {m} {a},
                                           forall `{GHC.Base.Monoid m}, (a -> m) -> Min a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_268__ arg_269__ =>
      match arg_268__ , arg_269__ with
        | f , Mk_Min a => f a
      end.

Local Definition Foldable__Min_foldl : forall {b} {a},
                                         (b -> a -> b) -> b -> Min a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => Data.Monoid.appEndo (Data.Monoid.getDual (Foldable__Min_foldMap
                                                                (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                            (Coq.Program.Basics.compose
                                                                                            Data.Monoid.Mk_Endo
                                                                                            (GHC.Base.flip f))) t)) z
      end.

Local Definition Foldable__Min_foldr' : forall {a} {b},
                                          (a -> b -> b) -> b -> Min a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Min_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Min_foldr : forall {a} {b},
                                         (a -> b -> b) -> b -> Min a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__ , arg_5__ , arg_6__ with
        | f , z , t => Data.Monoid.appEndo (Foldable__Min_foldMap
                                           (Data.Foldable.hash_compose Data.Monoid.Mk_Endo f) t) z
      end.

Local Definition Foldable__Min_foldl' : forall {b} {a},
                                          (b -> a -> b) -> b -> Min a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Min_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Min_length : forall {a}, Min a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Min_foldl' (fun arg_64__ arg_65__ =>
                           match arg_64__ , arg_65__ with
                             | c , _ => _GHC.Num.+_ c (GHC.Num.fromInteger 1)
                           end) (GHC.Num.fromInteger 0).

Local Definition Foldable__Min_null : forall {a}, Min a -> bool :=
  fun {a} => Foldable__Min_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Min_toList : forall {a}, Min a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Min_foldr c n t
                                end)
      end.

Local Definition Foldable__Min_product : forall {a},
                                           forall `{GHC.Num.Num a}, Min a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Min_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Min_sum : forall {a},
                                       forall `{GHC.Num.Num a}, Min a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Min_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Min_fold : forall {m},
                                        forall `{GHC.Base.Monoid m}, Min m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Min_foldMap GHC.Base.id.

Local Definition Foldable__Min_elem : forall {a},
                                        forall `{GHC.Base.Eq_ a}, a -> Min a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Min_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Program Instance Foldable__Min : Data.Foldable.Foldable Min := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Min_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Min_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Min_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Min_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Min_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Min_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Min_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Min_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Min_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Min_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Min_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Min_toList |}.

Local Definition Traversable__Min_traverse : forall {f} {a} {b},
                                               forall `{GHC.Base.Applicative f}, (a -> f b) -> Min a -> f (Min b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_264__ arg_265__ =>
      match arg_264__ , arg_265__ with
        | f , Mk_Min a => Mk_Min Data.Functor.<$> f a
      end.

Local Definition Traversable__Min_sequenceA : forall {f} {a},
                                                forall `{GHC.Base.Applicative f}, Min (f a) -> f (Min a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Min_traverse GHC.Base.id.

Local Definition Traversable__Min_sequence : forall {m} {a},
                                               forall `{GHC.Base.Monad m}, Min (m a) -> m (Min a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Min_sequenceA.

Local Definition Traversable__Min_mapM : forall {m} {a} {b},
                                           forall `{GHC.Base.Monad m}, (a -> m b) -> Min a -> m (Min b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Min_traverse.

Program Instance Traversable__Min : Data.Traversable.Traversable Min := fun _
                                                                            k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Min_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Min_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Min_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Min_traverse |}.

Local Definition Applicative__Min_op_zlztzg__ : forall {a} {b},
                                                  Min (a -> b) -> Min a -> Min b :=
  fun {a} {b} =>
    fun arg_260__ arg_261__ =>
      match arg_260__ , arg_261__ with
        | Mk_Min f , Mk_Min x => Mk_Min (f x)
      end.

Local Definition Applicative__Min_op_ztzg__ : forall {a} {b},
                                                Min a -> Min b -> Min b :=
  fun {a} {b} =>
    fun arg_257__ arg_258__ => match arg_257__ , arg_258__ with | _ , a => a end.

Local Definition Applicative__Min_pure : forall {a}, a -> Min a :=
  fun {a} => Mk_Min.

Program Instance Applicative__Min : GHC.Base.Applicative Min := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Min_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Min_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__Min_pure |}.

Local Definition Monad__Min_op_zgzg__ : forall {a} {b},
                                          Min a -> Min b -> Min b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Min_op_zgzgze__ : forall {a} {b},
                                            Min a -> (a -> Min b) -> Min b :=
  fun {a} {b} =>
    fun arg_250__ arg_251__ =>
      match arg_250__ , arg_251__ with
        | Mk_Min a , f => f a
      end.

Local Definition Monad__Min_return_ : forall {a}, a -> Min a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Min : GHC.Base.Monad Min := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Min_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Min_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => Monad__Min_return_ |}.

(* Translating `instance Control.Monad.Fix.MonadFix Data.Semigroup.Min' failed:
   OOPS! Cannot find information for class Qualified "Control.Monad.Fix" "MonadFix"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Data.Semigroup.Min a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Num" "Num" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Data.Semigroup.Max a)' failed: OOPS! Cannot find information
   for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Enum a}, GHC.Enum.Enum
   (Data.Semigroup.Max a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Enum" "Enum" unsupported *)

(* Skipping instance Semigroup__Max *)

(* Skipping instance Monoid__Max *)

Local Definition Functor__Max_fmap : forall {a} {b},
                                       (a -> b) -> Max a -> Max b :=
  fun {a} {b} =>
    fun arg_245__ arg_246__ =>
      match arg_245__ , arg_246__ with
        | f , Mk_Max x => Mk_Max (f x)
      end.

Local Definition Functor__Max_op_zlzd__ : forall {a} {b}, a -> Max b -> Max a :=
  fun {a} {b} => fun x => Functor__Max_fmap (GHC.Base.const x).

Program Instance Functor__Max : GHC.Base.Functor Max := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Max_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Max_fmap |}.

Local Definition Foldable__Max_foldMap : forall {m} {a},
                                           forall `{GHC.Base.Monoid m}, (a -> m) -> Max a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_241__ arg_242__ =>
      match arg_241__ , arg_242__ with
        | f , Mk_Max a => f a
      end.

Local Definition Foldable__Max_foldl : forall {b} {a},
                                         (b -> a -> b) -> b -> Max a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => Data.Monoid.appEndo (Data.Monoid.getDual (Foldable__Max_foldMap
                                                                (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                            (Coq.Program.Basics.compose
                                                                                            Data.Monoid.Mk_Endo
                                                                                            (GHC.Base.flip f))) t)) z
      end.

Local Definition Foldable__Max_foldr' : forall {a} {b},
                                          (a -> b -> b) -> b -> Max a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Max_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Max_foldr : forall {a} {b},
                                         (a -> b -> b) -> b -> Max a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__ , arg_5__ , arg_6__ with
        | f , z , t => Data.Monoid.appEndo (Foldable__Max_foldMap
                                           (Data.Foldable.hash_compose Data.Monoid.Mk_Endo f) t) z
      end.

Local Definition Foldable__Max_foldl' : forall {b} {a},
                                          (b -> a -> b) -> b -> Max a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Max_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Max_length : forall {a}, Max a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Max_foldl' (fun arg_64__ arg_65__ =>
                           match arg_64__ , arg_65__ with
                             | c , _ => _GHC.Num.+_ c (GHC.Num.fromInteger 1)
                           end) (GHC.Num.fromInteger 0).

Local Definition Foldable__Max_null : forall {a}, Max a -> bool :=
  fun {a} => Foldable__Max_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Max_toList : forall {a}, Max a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Max_foldr c n t
                                end)
      end.

Local Definition Foldable__Max_product : forall {a},
                                           forall `{GHC.Num.Num a}, Max a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Max_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Max_sum : forall {a},
                                       forall `{GHC.Num.Num a}, Max a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Max_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Max_fold : forall {m},
                                        forall `{GHC.Base.Monoid m}, Max m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Max_foldMap GHC.Base.id.

Local Definition Foldable__Max_elem : forall {a},
                                        forall `{GHC.Base.Eq_ a}, a -> Max a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Max_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Program Instance Foldable__Max : Data.Foldable.Foldable Max := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Max_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Max_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Max_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Max_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Max_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Max_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Max_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Max_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Max_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Max_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Max_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Max_toList |}.

Local Definition Traversable__Max_traverse : forall {f} {a} {b},
                                               forall `{GHC.Base.Applicative f}, (a -> f b) -> Max a -> f (Max b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_237__ arg_238__ =>
      match arg_237__ , arg_238__ with
        | f , Mk_Max a => Mk_Max Data.Functor.<$> f a
      end.

Local Definition Traversable__Max_sequenceA : forall {f} {a},
                                                forall `{GHC.Base.Applicative f}, Max (f a) -> f (Max a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Max_traverse GHC.Base.id.

Local Definition Traversable__Max_sequence : forall {m} {a},
                                               forall `{GHC.Base.Monad m}, Max (m a) -> m (Max a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Max_sequenceA.

Local Definition Traversable__Max_mapM : forall {m} {a} {b},
                                           forall `{GHC.Base.Monad m}, (a -> m b) -> Max a -> m (Max b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Max_traverse.

Program Instance Traversable__Max : Data.Traversable.Traversable Max := fun _
                                                                            k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Max_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Max_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Max_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Max_traverse |}.

Local Definition Applicative__Max_op_zlztzg__ : forall {a} {b},
                                                  Max (a -> b) -> Max a -> Max b :=
  fun {a} {b} =>
    fun arg_233__ arg_234__ =>
      match arg_233__ , arg_234__ with
        | Mk_Max f , Mk_Max x => Mk_Max (f x)
      end.

Local Definition Applicative__Max_op_ztzg__ : forall {a} {b},
                                                Max a -> Max b -> Max b :=
  fun {a} {b} =>
    fun arg_230__ arg_231__ => match arg_230__ , arg_231__ with | _ , a => a end.

Local Definition Applicative__Max_pure : forall {a}, a -> Max a :=
  fun {a} => Mk_Max.

Program Instance Applicative__Max : GHC.Base.Applicative Max := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Max_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Max_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__Max_pure |}.

Local Definition Monad__Max_op_zgzg__ : forall {a} {b},
                                          Max a -> Max b -> Max b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Max_op_zgzgze__ : forall {a} {b},
                                            Max a -> (a -> Max b) -> Max b :=
  fun {a} {b} =>
    fun arg_223__ arg_224__ =>
      match arg_223__ , arg_224__ with
        | Mk_Max a , f => f a
      end.

Local Definition Monad__Max_return_ : forall {a}, a -> Max a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Max : GHC.Base.Monad Max := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Max_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Max_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => Monad__Max_return_ |}.

(* Translating `instance Control.Monad.Fix.MonadFix Data.Semigroup.Max' failed:
   OOPS! Cannot find information for class Qualified "Control.Monad.Fix" "MonadFix"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Data.Semigroup.Max a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Num" "Num" unsupported *)

Local Definition Functor__Arg_fmap {inst_a} : forall {a} {b},
                                                (a -> b) -> (Arg inst_a) a -> (Arg inst_a) b :=
  fun {a} {b} =>
    fun arg_219__ arg_220__ =>
      match arg_219__ , arg_220__ with
        | f , Mk_Arg x a => Mk_Arg x (f a)
      end.

Local Definition Functor__Arg_op_zlzd__ {inst_a} : forall {a} {b},
                                                     a -> (Arg inst_a) b -> (Arg inst_a) a :=
  fun {a} {b} => fun x => Functor__Arg_fmap (GHC.Base.const x).

Program Instance Functor__Arg {a} : GHC.Base.Functor (Arg a) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Arg_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Arg_fmap |}.

Local Definition Foldable__Arg_foldMap {inst_a} : forall {m} {a},
                                                    forall `{GHC.Base.Monoid m}, (a -> m) -> (Arg inst_a) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_215__ arg_216__ =>
      match arg_215__ , arg_216__ with
        | f , Mk_Arg _ a => f a
      end.

Local Definition Foldable__Arg_foldl {inst_a} : forall {b} {a},
                                                  (b -> a -> b) -> b -> (Arg inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => Data.Monoid.appEndo (Data.Monoid.getDual (Foldable__Arg_foldMap
                                                                (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                            (Coq.Program.Basics.compose
                                                                                            Data.Monoid.Mk_Endo
                                                                                            (GHC.Base.flip f))) t)) z
      end.

Local Definition Foldable__Arg_foldr' {inst_a} : forall {a} {b},
                                                   (a -> b -> b) -> b -> (Arg inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Arg_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Arg_foldr {inst_a} : forall {a} {b},
                                                  (a -> b -> b) -> b -> (Arg inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__ , arg_5__ , arg_6__ with
        | f , z , t => Data.Monoid.appEndo (Foldable__Arg_foldMap
                                           (Data.Foldable.hash_compose Data.Monoid.Mk_Endo f) t) z
      end.

Local Definition Foldable__Arg_foldl' {inst_a} : forall {b} {a},
                                                   (b -> a -> b) -> b -> (Arg inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Arg_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Arg_length {inst_a} : forall {a},
                                                   (Arg inst_a) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Arg_foldl' (fun arg_64__ arg_65__ =>
                           match arg_64__ , arg_65__ with
                             | c , _ => _GHC.Num.+_ c (GHC.Num.fromInteger 1)
                           end) (GHC.Num.fromInteger 0).

Local Definition Foldable__Arg_null {inst_a} : forall {a},
                                                 (Arg inst_a) a -> bool :=
  fun {a} => Foldable__Arg_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Arg_toList {inst_a} : forall {a},
                                                   (Arg inst_a) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Arg_foldr c n t
                                end)
      end.

Local Definition Foldable__Arg_product {inst_a} : forall {a},
                                                    forall `{GHC.Num.Num a}, (Arg inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Arg_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Arg_sum {inst_a} : forall {a},
                                                forall `{GHC.Num.Num a}, (Arg inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Arg_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Arg_fold {inst_a} : forall {m},
                                                 forall `{GHC.Base.Monoid m}, (Arg inst_a) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Arg_foldMap GHC.Base.id.

Local Definition Foldable__Arg_elem {inst_a} : forall {a},
                                                 forall `{GHC.Base.Eq_ a}, a -> (Arg inst_a) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Arg_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Program Instance Foldable__Arg {a} : Data.Foldable.Foldable (Arg a) := fun _
                                                                           k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Arg_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Arg_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Arg_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Arg_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Arg_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Arg_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Arg_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Arg_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Arg_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Arg_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Arg_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Arg_toList |}.

Local Definition Traversable__Arg_traverse {inst_a} : forall {f} {a} {b},
                                                        forall `{GHC.Base.Applicative f},
                                                          (a -> f b) -> (Arg inst_a) a -> f ((Arg inst_a) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_211__ arg_212__ =>
      match arg_211__ , arg_212__ with
        | f , Mk_Arg x a => Mk_Arg x Data.Functor.<$> f a
      end.

Local Definition Traversable__Arg_sequenceA {inst_a} : forall {f} {a},
                                                         forall `{GHC.Base.Applicative f},
                                                           (Arg inst_a) (f a) -> f ((Arg inst_a) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Arg_traverse GHC.Base.id.

Local Definition Traversable__Arg_sequence {inst_a} : forall {m} {a},
                                                        forall `{GHC.Base.Monad m},
                                                          (Arg inst_a) (m a) -> m ((Arg inst_a) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Arg_sequenceA.

Local Definition Traversable__Arg_mapM {inst_a} : forall {m} {a} {b},
                                                    forall `{GHC.Base.Monad m},
                                                      (a -> m b) -> (Arg inst_a) a -> m ((Arg inst_a) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Arg_traverse.

Program Instance Traversable__Arg {a} : Data.Traversable.Traversable (Arg a) :=
  fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Arg_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Arg_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Arg_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Arg_traverse |}.

Local Definition Eq___Arg_op_zeze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
    : (Arg inst_a inst_b) -> (Arg inst_a inst_b) -> bool :=
  fun arg_207__ arg_208__ =>
    match arg_207__ , arg_208__ with
      | Mk_Arg a _ , Mk_Arg b _ => a GHC.Base.== b
    end.

Local Definition Eq___Arg_op_zsze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
    : (Arg inst_a inst_b) -> (Arg inst_a inst_b) -> bool :=
  fun x y => negb (Eq___Arg_op_zeze__ x y).

Program Instance Eq___Arg {a} {b} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Arg a b) :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Arg_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Arg_op_zsze__ |}.

(* Skipping instance Ord__Arg *)

(* Translating `instance Data.Bifunctor.Bifunctor Data.Semigroup.Arg' failed:
   missing Qualified "Data.Bifunctor" "first" in fromList [(Qualified
   "Data.Bifunctor" "bimap",Qualified "Data.Semigroup" "Bifunctor__Arg_bimap")]
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Data.Semigroup.First a)' failed: OOPS! Cannot find information
   for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Enum a}, GHC.Enum.Enum
   (Data.Semigroup.First a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Enum" "Enum" unsupported *)

(* Skipping instance Semigroup__First *)

Local Definition Functor__First_fmap : forall {a} {b},
                                         (a -> b) -> First a -> First b :=
  fun {a} {b} =>
    fun arg_188__ arg_189__ =>
      match arg_188__ , arg_189__ with
        | f , Mk_First x => Mk_First (f x)
      end.

Local Definition Functor__First_op_zlzd__ : forall {a} {b},
                                              a -> First b -> First a :=
  fun {a} {b} => fun x => Functor__First_fmap (GHC.Base.const x).

Program Instance Functor__First : GHC.Base.Functor First := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__First_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__First_fmap |}.

Local Definition Foldable__First_foldMap : forall {m} {a},
                                             forall `{GHC.Base.Monoid m}, (a -> m) -> First a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_184__ arg_185__ =>
      match arg_184__ , arg_185__ with
        | f , Mk_First a => f a
      end.

Local Definition Foldable__First_foldl : forall {b} {a},
                                           (b -> a -> b) -> b -> First a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => Data.Monoid.appEndo (Data.Monoid.getDual (Foldable__First_foldMap
                                                                (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                            (Coq.Program.Basics.compose
                                                                                            Data.Monoid.Mk_Endo
                                                                                            (GHC.Base.flip f))) t)) z
      end.

Local Definition Foldable__First_foldr' : forall {a} {b},
                                            (a -> b -> b) -> b -> First a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__First_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__First_foldr : forall {a} {b},
                                           (a -> b -> b) -> b -> First a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__ , arg_5__ , arg_6__ with
        | f , z , t => Data.Monoid.appEndo (Foldable__First_foldMap
                                           (Data.Foldable.hash_compose Data.Monoid.Mk_Endo f) t) z
      end.

Local Definition Foldable__First_foldl' : forall {b} {a},
                                            (b -> a -> b) -> b -> First a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__First_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__First_length : forall {a}, First a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__First_foldl' (fun arg_64__ arg_65__ =>
                             match arg_64__ , arg_65__ with
                               | c , _ => _GHC.Num.+_ c (GHC.Num.fromInteger 1)
                             end) (GHC.Num.fromInteger 0).

Local Definition Foldable__First_null : forall {a}, First a -> bool :=
  fun {a} => Foldable__First_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__First_toList : forall {a}, First a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__First_foldr c n t
                                end)
      end.

Local Definition Foldable__First_product : forall {a},
                                             forall `{GHC.Num.Num a}, First a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__First_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__First_sum : forall {a},
                                         forall `{GHC.Num.Num a}, First a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__First_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__First_fold : forall {m},
                                          forall `{GHC.Base.Monoid m}, First m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__First_foldMap GHC.Base.id.

Local Definition Foldable__First_elem : forall {a},
                                          forall `{GHC.Base.Eq_ a}, a -> First a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__First_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Program Instance Foldable__First : Data.Foldable.Foldable First := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__First_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__First_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__First_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__First_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__First_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__First_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__First_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__First_length ;
      Data.Foldable.null__ := fun {a} => Foldable__First_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__First_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__First_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__First_toList |}.

Local Definition Traversable__First_traverse : forall {f} {a} {b},
                                                 forall `{GHC.Base.Applicative f},
                                                   (a -> f b) -> First a -> f (First b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_180__ arg_181__ =>
      match arg_180__ , arg_181__ with
        | f , Mk_First a => Mk_First Data.Functor.<$> f a
      end.

Local Definition Traversable__First_sequenceA : forall {f} {a},
                                                  forall `{GHC.Base.Applicative f}, First (f a) -> f (First a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__First_traverse GHC.Base.id.

Local Definition Traversable__First_sequence : forall {m} {a},
                                                 forall `{GHC.Base.Monad m}, First (m a) -> m (First a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__First_sequenceA.

Local Definition Traversable__First_mapM : forall {m} {a} {b},
                                             forall `{GHC.Base.Monad m}, (a -> m b) -> First a -> m (First b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__First_traverse.

Program Instance Traversable__First : Data.Traversable.Traversable First :=
  fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__First_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__First_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__First_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__First_traverse |}.

Local Definition Applicative__First_op_zlztzg__ : forall {a} {b},
                                                    First (a -> b) -> First a -> First b :=
  fun {a} {b} =>
    fun arg_176__ arg_177__ =>
      match arg_176__ , arg_177__ with
        | Mk_First f , Mk_First x => Mk_First (f x)
      end.

Local Definition Applicative__First_op_ztzg__ : forall {a} {b},
                                                  First a -> First b -> First b :=
  fun {a} {b} =>
    fun arg_173__ arg_174__ => match arg_173__ , arg_174__ with | _ , a => a end.

Local Definition Applicative__First_pure : forall {a}, a -> First a :=
  fun {a} => fun x => Mk_First x.

Program Instance Applicative__First : GHC.Base.Applicative First := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__First_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__First_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__First_pure |}.

Local Definition Monad__First_op_zgzg__ : forall {a} {b},
                                            First a -> First b -> First b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__First_op_zgzgze__ : forall {a} {b},
                                              First a -> (a -> First b) -> First b :=
  fun {a} {b} =>
    fun arg_165__ arg_166__ =>
      match arg_165__ , arg_166__ with
        | Mk_First a , f => f a
      end.

Local Definition Monad__First_return_ : forall {a}, a -> First a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__First : GHC.Base.Monad First := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} => Monad__First_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__First_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => Monad__First_return_ |}.

(* Translating `instance Control.Monad.Fix.MonadFix Data.Semigroup.First'
   failed: OOPS! Cannot find information for class Qualified "Control.Monad.Fix"
   "MonadFix" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Data.Semigroup.Last a)' failed: OOPS! Cannot find information
   for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Enum a}, GHC.Enum.Enum
   (Data.Semigroup.Last a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Enum" "Enum" unsupported *)

(* Skipping instance Semigroup__Last *)

Local Definition Functor__Last_fmap : forall {a} {b},
                                        (a -> b) -> Last a -> Last b :=
  fun {a} {b} =>
    fun arg_154__ arg_155__ =>
      match arg_154__ , arg_155__ with
        | f , Mk_Last x => Mk_Last (f x)
      end.

Local Definition Functor__Last_op_zlzd__ : forall {a} {b},
                                             a -> Last b -> Last a :=
  fun {a} {b} =>
    fun arg_158__ arg_159__ =>
      match arg_158__ , arg_159__ with
        | a , _ => Mk_Last a
      end.

Program Instance Functor__Last : GHC.Base.Functor Last := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Last_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Last_fmap |}.

Local Definition Foldable__Last_foldMap : forall {m} {a},
                                            forall `{GHC.Base.Monoid m}, (a -> m) -> Last a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_150__ arg_151__ =>
      match arg_150__ , arg_151__ with
        | f , Mk_Last a => f a
      end.

Local Definition Foldable__Last_foldl : forall {b} {a},
                                          (b -> a -> b) -> b -> Last a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => Data.Monoid.appEndo (Data.Monoid.getDual (Foldable__Last_foldMap
                                                                (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                            (Coq.Program.Basics.compose
                                                                                            Data.Monoid.Mk_Endo
                                                                                            (GHC.Base.flip f))) t)) z
      end.

Local Definition Foldable__Last_foldr' : forall {a} {b},
                                           (a -> b -> b) -> b -> Last a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Last_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Last_foldr : forall {a} {b},
                                          (a -> b -> b) -> b -> Last a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__ , arg_5__ , arg_6__ with
        | f , z , t => Data.Monoid.appEndo (Foldable__Last_foldMap
                                           (Data.Foldable.hash_compose Data.Monoid.Mk_Endo f) t) z
      end.

Local Definition Foldable__Last_foldl' : forall {b} {a},
                                           (b -> a -> b) -> b -> Last a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Last_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Last_length : forall {a}, Last a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Last_foldl' (fun arg_64__ arg_65__ =>
                            match arg_64__ , arg_65__ with
                              | c , _ => _GHC.Num.+_ c (GHC.Num.fromInteger 1)
                            end) (GHC.Num.fromInteger 0).

Local Definition Foldable__Last_null : forall {a}, Last a -> bool :=
  fun {a} => Foldable__Last_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Last_toList : forall {a}, Last a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Last_foldr c n t
                                end)
      end.

Local Definition Foldable__Last_product : forall {a},
                                            forall `{GHC.Num.Num a}, Last a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Last_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Last_sum : forall {a},
                                        forall `{GHC.Num.Num a}, Last a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Last_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Last_fold : forall {m},
                                         forall `{GHC.Base.Monoid m}, Last m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Last_foldMap GHC.Base.id.

Local Definition Foldable__Last_elem : forall {a},
                                         forall `{GHC.Base.Eq_ a}, a -> Last a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Last_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Program Instance Foldable__Last : Data.Foldable.Foldable Last := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Last_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Last_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Last_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Last_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Last_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Last_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Last_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Last_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Last_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Last_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Last_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Last_toList |}.

Local Definition Traversable__Last_traverse : forall {f} {a} {b},
                                                forall `{GHC.Base.Applicative f}, (a -> f b) -> Last a -> f (Last b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_146__ arg_147__ =>
      match arg_146__ , arg_147__ with
        | f , Mk_Last a => Mk_Last Data.Functor.<$> f a
      end.

Local Definition Traversable__Last_sequenceA : forall {f} {a},
                                                 forall `{GHC.Base.Applicative f}, Last (f a) -> f (Last a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Last_traverse GHC.Base.id.

Local Definition Traversable__Last_sequence : forall {m} {a},
                                                forall `{GHC.Base.Monad m}, Last (m a) -> m (Last a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Last_sequenceA.

Local Definition Traversable__Last_mapM : forall {m} {a} {b},
                                            forall `{GHC.Base.Monad m}, (a -> m b) -> Last a -> m (Last b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Last_traverse.

Program Instance Traversable__Last : Data.Traversable.Traversable Last := fun _
                                                                              k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Last_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Last_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Last_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Last_traverse |}.

Local Definition Applicative__Last_op_zlztzg__ : forall {a} {b},
                                                   Last (a -> b) -> Last a -> Last b :=
  fun {a} {b} =>
    fun arg_142__ arg_143__ =>
      match arg_142__ , arg_143__ with
        | Mk_Last f , Mk_Last x => Mk_Last (f x)
      end.

Local Definition Applicative__Last_op_ztzg__ : forall {a} {b},
                                                 Last a -> Last b -> Last b :=
  fun {a} {b} =>
    fun arg_139__ arg_140__ => match arg_139__ , arg_140__ with | _ , a => a end.

Local Definition Applicative__Last_pure : forall {a}, a -> Last a :=
  fun {a} => Mk_Last.

Program Instance Applicative__Last : GHC.Base.Applicative Last := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Last_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Last_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__Last_pure |}.

Local Definition Monad__Last_op_zgzg__ : forall {a} {b},
                                           Last a -> Last b -> Last b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Last_op_zgzgze__ : forall {a} {b},
                                             Last a -> (a -> Last b) -> Last b :=
  fun {a} {b} =>
    fun arg_132__ arg_133__ =>
      match arg_132__ , arg_133__ with
        | Mk_Last a , f => f a
      end.

Local Definition Monad__Last_return_ : forall {a}, a -> Last a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Last : GHC.Base.Monad Last := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Last_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Last_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => Monad__Last_return_ |}.

(* Translating `instance Control.Monad.Fix.MonadFix Data.Semigroup.Last' failed:
   OOPS! Cannot find information for class Qualified "Control.Monad.Fix" "MonadFix"
   unsupported *)

(* Skipping instance Semigroup__WrappedMonoid *)

(* Skipping instance Monoid__WrappedMonoid *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Data.Semigroup.WrappedMonoid a)' failed: OOPS! Cannot find
   information for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Enum a}, GHC.Enum.Enum
   (Data.Semigroup.WrappedMonoid a)' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Enum" unsupported *)

Local Definition Functor__Option_fmap : forall {a} {b},
                                          (a -> b) -> Option a -> Option b :=
  fun {a} {b} =>
    fun arg_126__ arg_127__ =>
      match arg_126__ , arg_127__ with
        | f , Mk_Option a => Mk_Option (GHC.Base.fmap f a)
      end.

Local Definition Functor__Option_op_zlzd__ : forall {a} {b},
                                               a -> Option b -> Option a :=
  fun {a} {b} => fun x => Functor__Option_fmap (GHC.Base.const x).

Program Instance Functor__Option : GHC.Base.Functor Option := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Option_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Option_fmap |}.

Local Definition Applicative__Option_op_zlztzg__ : forall {a} {b},
                                                     Option (a -> b) -> Option a -> Option b :=
  fun {a} {b} =>
    fun arg_118__ arg_119__ =>
      match arg_118__ , arg_119__ with
        | Mk_Option a , Mk_Option b => Mk_Option (a GHC.Base.<*> b)
      end.

Local Definition Applicative__Option_op_ztzg__ : forall {a} {b},
                                                   Option a -> Option b -> Option b :=
  fun {a} {b} =>
    fun arg_122__ arg_123__ =>
      match arg_122__ , arg_123__ with
        | Mk_Option None , _ => Mk_Option None
        | _ , b => b
      end.

Local Definition Applicative__Option_pure : forall {a}, a -> Option a :=
  fun {a} => fun a => Mk_Option (Some a).

Program Instance Applicative__Option : GHC.Base.Applicative Option := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Option_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Option_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__Option_pure |}.

Local Definition Monad__Option_op_zgzg__ : forall {a} {b},
                                             Option a -> Option b -> Option b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Option_op_zgzgze__ : forall {a} {b},
                                               Option a -> (a -> Option b) -> Option b :=
  fun {a} {b} =>
    fun arg_112__ arg_113__ =>
      match arg_112__ , arg_113__ with
        | Mk_Option (Some a) , k => k a
        | _ , _ => Mk_Option None
      end.

Local Definition Monad__Option_return_ : forall {a}, a -> Option a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Option : GHC.Base.Monad Option := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Option_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Option_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => Monad__Option_return_ |}.

(* Translating `instance GHC.Base.Alternative Data.Semigroup.Option' failed:
   OOPS! Cannot find information for class Qualified "GHC.Base" "Alternative"
   unsupported *)

(* Translating `instance GHC.Base.MonadPlus Data.Semigroup.Option' failed: OOPS!
   Cannot find information for class Qualified "GHC.Base" "MonadPlus"
   unsupported *)

(* Translating `instance Control.Monad.Fix.MonadFix Data.Semigroup.Option'
   failed: OOPS! Cannot find information for class Qualified "Control.Monad.Fix"
   "MonadFix" unsupported *)

Local Definition Foldable__Option_foldMap : forall {m} {a},
                                              forall `{GHC.Base.Monoid m}, (a -> m) -> Option a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_108__ arg_109__ =>
      match arg_108__ , arg_109__ with
        | f , Mk_Option (Some m) => f m
        | _ , Mk_Option None => GHC.Base.mempty
      end.

Local Definition Foldable__Option_foldl : forall {b} {a},
                                            (b -> a -> b) -> b -> Option a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => Data.Monoid.appEndo (Data.Monoid.getDual
                                           (Foldable__Option_foldMap (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                                 (Coq.Program.Basics.compose
                                                                                                 Data.Monoid.Mk_Endo
                                                                                                 (GHC.Base.flip f))) t))
                       z
      end.

Local Definition Foldable__Option_foldr' : forall {a} {b},
                                             (a -> b -> b) -> b -> Option a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Option_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Option_foldr : forall {a} {b},
                                            (a -> b -> b) -> b -> Option a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__ , arg_5__ , arg_6__ with
        | f , z , t => Data.Monoid.appEndo (Foldable__Option_foldMap
                                           (Data.Foldable.hash_compose Data.Monoid.Mk_Endo f) t) z
      end.

Local Definition Foldable__Option_foldl' : forall {b} {a},
                                             (b -> a -> b) -> b -> Option a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Option_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Option_length : forall {a},
                                             Option a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Option_foldl' (fun arg_64__ arg_65__ =>
                              match arg_64__ , arg_65__ with
                                | c , _ => _GHC.Num.+_ c (GHC.Num.fromInteger 1)
                              end) (GHC.Num.fromInteger 0).

Local Definition Foldable__Option_null : forall {a}, Option a -> bool :=
  fun {a} => Foldable__Option_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Option_toList : forall {a}, Option a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Option_foldr c n t
                                end)
      end.

Local Definition Foldable__Option_product : forall {a},
                                              forall `{GHC.Num.Num a}, Option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Option_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Option_sum : forall {a},
                                          forall `{GHC.Num.Num a}, Option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Option_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Option_fold : forall {m},
                                           forall `{GHC.Base.Monoid m}, Option m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Option_foldMap GHC.Base.id.

Local Definition Foldable__Option_elem : forall {a},
                                           forall `{GHC.Base.Eq_ a}, a -> Option a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Option_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Program Instance Foldable__Option : Data.Foldable.Foldable Option := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Option_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Option_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Option_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Option_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Option_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Option_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Option_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Option_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Option_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
        Foldable__Option_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Option_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Option_toList |}.

Local Definition Traversable__Option_traverse : forall {f} {a} {b},
                                                  forall `{GHC.Base.Applicative f},
                                                    (a -> f b) -> Option a -> f (Option b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_103__ arg_104__ =>
      match arg_103__ , arg_104__ with
        | f , Mk_Option (Some a) => (Mk_Option GHC.Base.∘ Some) Data.Functor.<$> f a
        | _ , Mk_Option None => GHC.Base.pure (Mk_Option None)
      end.

Local Definition Traversable__Option_sequenceA : forall {f} {a},
                                                   forall `{GHC.Base.Applicative f}, Option (f a) -> f (Option a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Option_traverse GHC.Base.id.

Local Definition Traversable__Option_sequence : forall {m} {a},
                                                  forall `{GHC.Base.Monad m}, Option (m a) -> m (Option a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Option_sequenceA.

Local Definition Traversable__Option_mapM : forall {m} {a} {b},
                                              forall `{GHC.Base.Monad m}, (a -> m b) -> Option a -> m (Option b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Option_traverse.

Program Instance Traversable__Option : Data.Traversable.Traversable Option :=
  fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Option_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Option_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Option_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Option_traverse |}.

(* Skipping instance Semigroup__Option *)

(* Skipping instance Monoid__Option *)

Local Definition Semigroup__Proxy_op_zlzg__ {inst_s} : (Data.Proxy.Proxy
                                                       inst_s) -> (Data.Proxy.Proxy inst_s) -> (Data.Proxy.Proxy
                                                       inst_s) :=
  fun arg_86__ arg_87__ => Data.Proxy.Mk_Proxy.

Local Definition Semigroup__Proxy_sconcat {inst_s} : Data.List.NonEmpty.NonEmpty
                                                     (Data.Proxy.Proxy inst_s) -> (Data.Proxy.Proxy inst_s) :=
  fun arg_88__ => Data.Proxy.Mk_Proxy.

Local Definition Semigroup__Proxy_stimes {inst_s} : forall {b},
                                                      forall `{GHC.Real.Integral b},
                                                        b -> (Data.Proxy.Proxy inst_s) -> (Data.Proxy.Proxy inst_s) :=
  fun {b} `{GHC.Real.Integral b} => fun arg_89__ arg_90__ => Data.Proxy.Mk_Proxy.

Program Instance Semigroup__Proxy {s} : Semigroup (Data.Proxy.Proxy s) := fun _
                                                                              k =>
    k {|op_zlzg____ := Semigroup__Proxy_op_zlzg__ ;
      sconcat__ := Semigroup__Proxy_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__Proxy_stimes |}.

(* Translating `instance GHC.Generics.Generic1 Data.Semigroup.Option' failed:
   OOPS! Cannot find information for class Qualified "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Semigroup.Option
   a)' failed: OOPS! Cannot find information for class Qualified "GHC.Generics"
   "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.Semigroup.Option a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Semigroup.Option a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Semigroup.Option a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__Option_compare {inst_a} `{GHC.Base.Ord inst_a} : Option
                                                                       inst_a -> Option inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Option_max {inst_a} `{GHC.Base.Ord inst_a} : Option
                                                                   inst_a -> Option inst_a -> Option inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Option_min {inst_a} `{GHC.Base.Ord inst_a} : Option
                                                                   inst_a -> Option inst_a -> Option inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Option_op_zg__ {inst_a} `{GHC.Base.Ord inst_a} : Option
                                                                       inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Option_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a} : Option
                                                                         inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Option_op_zl__ {inst_a} `{GHC.Base.Ord inst_a} : Option
                                                                       inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Option_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a} : Option
                                                                         inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Option_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : Option
                                                                         inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Option_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : Option
                                                                         inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Option {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Option a) :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Option_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Option_op_zsze__ |}.

Program Instance Ord__Option {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Option a) :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Option_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Option_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Option_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Option_op_zgze__ ;
      GHC.Base.compare__ := Ord__Option_compare ;
      GHC.Base.max__ := Ord__Option_max ;
      GHC.Base.min__ := Ord__Option_min |}.

(* Translating `instance GHC.Generics.Generic1 Data.Semigroup.WrappedMonoid'
   failed: OOPS! Cannot find information for class Qualified "GHC.Generics"
   "Generic1" unsupported *)

(* Translating `instance forall {m}, GHC.Generics.Generic
   (Data.Semigroup.WrappedMonoid m)' failed: OOPS! Cannot find information for
   class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance forall {m}, forall `{Data.Data.Data m}, Data.Data.Data
   (Data.Semigroup.WrappedMonoid m)' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {m}, forall `{GHC.Read.Read m}, GHC.Read.Read
   (Data.Semigroup.WrappedMonoid m)' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {m}, forall `{GHC.Show.Show m}, GHC.Show.Show
   (Data.Semigroup.WrappedMonoid m)' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__WrappedMonoid_compare {inst_m} `{GHC.Base.Ord inst_m}
    : WrappedMonoid inst_m -> WrappedMonoid inst_m -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__WrappedMonoid_max {inst_m} `{GHC.Base.Ord inst_m}
    : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__WrappedMonoid_min {inst_m} `{GHC.Base.Ord inst_m}
    : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__WrappedMonoid_op_zg__ {inst_m} `{GHC.Base.Ord inst_m}
    : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__WrappedMonoid_op_zgze__ {inst_m} `{GHC.Base.Ord inst_m}
    : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__WrappedMonoid_op_zl__ {inst_m} `{GHC.Base.Ord inst_m}
    : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__WrappedMonoid_op_zlze__ {inst_m} `{GHC.Base.Ord inst_m}
    : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___WrappedMonoid_op_zeze__ {inst_m} `{GHC.Base.Eq_ inst_m}
    : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___WrappedMonoid_op_zsze__ {inst_m} `{GHC.Base.Eq_ inst_m}
    : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___WrappedMonoid {m} `{GHC.Base.Eq_ m} : GHC.Base.Eq_
                                                            (WrappedMonoid m) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___WrappedMonoid_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___WrappedMonoid_op_zsze__ |}.

Program Instance Ord__WrappedMonoid {m} `{GHC.Base.Ord m} : GHC.Base.Ord
                                                            (WrappedMonoid m) := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__WrappedMonoid_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__WrappedMonoid_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__WrappedMonoid_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__WrappedMonoid_op_zgze__ ;
      GHC.Base.compare__ := Ord__WrappedMonoid_compare ;
      GHC.Base.max__ := Ord__WrappedMonoid_max ;
      GHC.Base.min__ := Ord__WrappedMonoid_min |}.

(* Translating `instance GHC.Generics.Generic1 Data.Semigroup.Last' failed:
   OOPS! Cannot find information for class Qualified "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Semigroup.Last
   a)' failed: OOPS! Cannot find information for class Qualified "GHC.Generics"
   "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.Semigroup.Last a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Semigroup.Last a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Semigroup.Last a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__Last_compare {inst_a} `{GHC.Base.Ord inst_a} : Last
                                                                     inst_a -> Last inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Last_max {inst_a} `{GHC.Base.Ord inst_a} : Last
                                                                 inst_a -> Last inst_a -> Last inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Last_min {inst_a} `{GHC.Base.Ord inst_a} : Last
                                                                 inst_a -> Last inst_a -> Last inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Last_op_zg__ {inst_a} `{GHC.Base.Ord inst_a} : Last
                                                                     inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Last_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a} : Last
                                                                       inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Last_op_zl__ {inst_a} `{GHC.Base.Ord inst_a} : Last
                                                                     inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Last_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a} : Last
                                                                       inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Last_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : Last
                                                                       inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Last_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : Last
                                                                       inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Last {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Last a) :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Last_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Last_op_zsze__ |}.

Program Instance Ord__Last {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Last a) :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Last_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Last_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Last_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Last_op_zgze__ ;
      GHC.Base.compare__ := Ord__Last_compare ;
      GHC.Base.max__ := Ord__Last_max ;
      GHC.Base.min__ := Ord__Last_min |}.

(* Translating `instance GHC.Generics.Generic1 Data.Semigroup.First' failed:
   OOPS! Cannot find information for class Qualified "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Semigroup.First
   a)' failed: OOPS! Cannot find information for class Qualified "GHC.Generics"
   "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.Semigroup.First a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Semigroup.First a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Semigroup.First a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__First_compare {inst_a} `{GHC.Base.Ord inst_a} : First
                                                                      inst_a -> First inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__First_max {inst_a} `{GHC.Base.Ord inst_a} : First
                                                                  inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__First_min {inst_a} `{GHC.Base.Ord inst_a} : First
                                                                  inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__First_op_zg__ {inst_a} `{GHC.Base.Ord inst_a} : First
                                                                      inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__First_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a} : First
                                                                        inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__First_op_zl__ {inst_a} `{GHC.Base.Ord inst_a} : First
                                                                      inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__First_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a} : First
                                                                        inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___First_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : First
                                                                        inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___First_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : First
                                                                        inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___First {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (First a) :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___First_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___First_op_zsze__ |}.

Program Instance Ord__First {a} `{GHC.Base.Ord a} : GHC.Base.Ord (First a) :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__First_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__First_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__First_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__First_op_zgze__ ;
      GHC.Base.compare__ := Ord__First_compare ;
      GHC.Base.max__ := Ord__First_max ;
      GHC.Base.min__ := Ord__First_min |}.

(* Translating `instance forall {a}, GHC.Generics.Generic1 (Data.Semigroup.Arg
   a)' failed: OOPS! Cannot find information for class Qualified "GHC.Generics"
   "Generic1" unsupported *)

(* Translating `instance forall {a} {b}, GHC.Generics.Generic
   (Data.Semigroup.Arg a b)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance forall {a} {b}, forall `{Data.Data.Data b}
   `{Data.Data.Data a}, Data.Data.Data (Data.Semigroup.Arg a b)' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a} {b}, forall `{GHC.Read.Read b}
   `{GHC.Read.Read a}, GHC.Read.Read (Data.Semigroup.Arg a b)' failed: OOPS! Cannot
   find information for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a} {b}, forall `{GHC.Show.Show b}
   `{GHC.Show.Show a}, GHC.Show.Show (Data.Semigroup.Arg a b)' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Generics.Generic1 Data.Semigroup.Max' failed: OOPS!
   Cannot find information for class Qualified "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Semigroup.Max
   a)' failed: OOPS! Cannot find information for class Qualified "GHC.Generics"
   "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.Semigroup.Max a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Semigroup.Max a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Semigroup.Max a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__Max_compare {inst_a} `{GHC.Base.Ord inst_a} : Max
                                                                    inst_a -> Max inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Max_max {inst_a} `{GHC.Base.Ord inst_a} : Max
                                                                inst_a -> Max inst_a -> Max inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Max_min {inst_a} `{GHC.Base.Ord inst_a} : Max
                                                                inst_a -> Max inst_a -> Max inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Max_op_zg__ {inst_a} `{GHC.Base.Ord inst_a} : Max
                                                                    inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Max_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a} : Max
                                                                      inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Max_op_zl__ {inst_a} `{GHC.Base.Ord inst_a} : Max
                                                                    inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Max_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a} : Max
                                                                      inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Max_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : Max
                                                                      inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Max_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : Max
                                                                      inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Max {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Max a) := fun _
                                                                              k =>
    k {|GHC.Base.op_zeze____ := Eq___Max_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Max_op_zsze__ |}.

Program Instance Ord__Max {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Max a) := fun _
                                                                              k =>
    k {|GHC.Base.op_zl____ := Ord__Max_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Max_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Max_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Max_op_zgze__ ;
      GHC.Base.compare__ := Ord__Max_compare ;
      GHC.Base.max__ := Ord__Max_max ;
      GHC.Base.min__ := Ord__Max_min |}.

(* Translating `instance GHC.Generics.Generic1 Data.Semigroup.Min' failed: OOPS!
   Cannot find information for class Qualified "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Semigroup.Min
   a)' failed: OOPS! Cannot find information for class Qualified "GHC.Generics"
   "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.Semigroup.Min a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Semigroup.Min a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Semigroup.Min a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__Min_compare {inst_a} `{GHC.Base.Ord inst_a} : Min
                                                                    inst_a -> Min inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Min_max {inst_a} `{GHC.Base.Ord inst_a} : Min
                                                                inst_a -> Min inst_a -> Min inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Min_min {inst_a} `{GHC.Base.Ord inst_a} : Min
                                                                inst_a -> Min inst_a -> Min inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Min_op_zg__ {inst_a} `{GHC.Base.Ord inst_a} : Min
                                                                    inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Min_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a} : Min
                                                                      inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Min_op_zl__ {inst_a} `{GHC.Base.Ord inst_a} : Min
                                                                    inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Min_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a} : Min
                                                                      inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Min_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : Min
                                                                      inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Min_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : Min
                                                                      inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Min {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Min a) := fun _
                                                                              k =>
    k {|GHC.Base.op_zeze____ := Eq___Min_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Min_op_zsze__ |}.

Program Instance Ord__Min {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Min a) := fun _
                                                                              k =>
    k {|GHC.Base.op_zl____ := Ord__Min_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Min_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Min_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Min_op_zgze__ ;
      GHC.Base.compare__ := Ord__Min_compare ;
      GHC.Base.max__ := Ord__Min_max ;
      GHC.Base.min__ := Ord__Min_min |}.

Definition diff {m} `{Semigroup m} : m -> Data.Monoid.Endo m :=
  Data.Monoid.Mk_Endo GHC.Base.∘ _<>_.

Definition option {b} {a} : b -> (a -> b) -> Option a -> b :=
  fun arg_22__ arg_23__ arg_24__ =>
    match arg_22__ , arg_23__ , arg_24__ with
      | n , j , Mk_Option m => Data.Maybe.maybe n j m
    end.

Definition stimesIdempotent {b} {a} `{GHC.Real.Integral b} : b -> a -> a :=
  fun n x =>
    if n GHC.Base.<= GHC.Num.fromInteger 0 : bool
    then GHC.Base.errorWithoutStackTrace (GHC.Base.hs_string__
                                         "stimesIdempotent: positive multiplier expected")
    else x.

Local Definition Semigroup__Void_stimes : forall {b},
                                            forall `{GHC.Real.Integral b}, b -> Data.Void.Void -> Data.Void.Void :=
  fun {b} `{GHC.Real.Integral b} => stimesIdempotent.

Program Instance Semigroup__Void : Semigroup Data.Void.Void := fun _ k =>
    k {|op_zlzg____ := Semigroup__Void_op_zlzg__ ;
      sconcat__ := Semigroup__Void_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__Void_stimes |}.

Local Definition Semigroup__Either_stimes {inst_a} {inst_b} : forall {b},
                                                                forall `{GHC.Real.Integral b},
                                                                  b -> (Data.Either.Either inst_a
                                                                  inst_b) -> (Data.Either.Either inst_a inst_b) :=
  fun {b} `{GHC.Real.Integral b} => stimesIdempotent.

Program Instance Semigroup__Either {a} {b} : Semigroup (Data.Either.Either a
                                                       b) := fun _ k =>
    k {|op_zlzg____ := Semigroup__Either_op_zlzg__ ;
      sconcat__ := Semigroup__Either_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__Either_stimes |}.

Definition stimesIdempotentMonoid {b} {a} `{GHC.Real.Integral b}
                                  `{GHC.Base.Monoid a} : b -> a -> a :=
  fun n x =>
    let scrut_28__ := GHC.Base.compare n (GHC.Num.fromInteger 0) in
    match scrut_28__ with
      | Lt => GHC.Base.errorWithoutStackTrace (GHC.Base.hs_string__
                                              "stimesIdempotentMonoid: negative multiplier")
      | Eq => GHC.Base.mempty
      | Gt => x
    end.

Local Definition Semigroup__Any_stimes : forall {b},
                                           forall `{GHC.Real.Integral b}, b -> Data.Monoid.Any -> Data.Monoid.Any :=
  fun {b} `{GHC.Real.Integral b} => stimesIdempotentMonoid.

Program Instance Semigroup__Any : Semigroup Data.Monoid.Any := fun _ k =>
    k {|op_zlzg____ := Semigroup__Any_op_zlzg__ ;
      sconcat__ := Semigroup__Any_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__Any_stimes |}.

Local Definition Semigroup__All_stimes : forall {b},
                                           forall `{GHC.Real.Integral b}, b -> Data.Monoid.All -> Data.Monoid.All :=
  fun {b} `{GHC.Real.Integral b} => stimesIdempotentMonoid.

Program Instance Semigroup__All : Semigroup Data.Monoid.All := fun _ k =>
    k {|op_zlzg____ := Semigroup__All_op_zlzg__ ;
      sconcat__ := Semigroup__All_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__All_stimes |}.

Local Definition Semigroup__comparison_stimes : forall {b},
                                                  forall `{GHC.Real.Integral b}, b -> comparison -> comparison :=
  fun {b} `{GHC.Real.Integral b} => stimesIdempotentMonoid.

Program Instance Semigroup__comparison : Semigroup comparison := fun _ k =>
    k {|op_zlzg____ := Semigroup__comparison_op_zlzg__ ;
      sconcat__ := Semigroup__comparison_sconcat ;
      stimes__ := fun {b} `{GHC.Real.Integral b} => Semigroup__comparison_stimes |}.

Module Notations.
Notation "'_Data.Semigroup.<>_'" := (op_zlzg__).
Infix "Data.Semigroup.<>" := (_<>_) (at level 70).
End Notations.

(* Unbound variables:
     None Some andb bool comparison cons false list negb nil option orb true tt unit
     Coq.Init.Datatypes.app Coq.Program.Basics.compose Data.Either.Either
     Data.Either.Left Data.Foldable.Foldable Data.Foldable.hash_compose
     Data.Functor.op_zlzdzg__ Data.List.NonEmpty.NEcons Data.List.NonEmpty.NonEmpty
     Data.Maybe.maybe Data.Monoid.All Data.Monoid.Any Data.Monoid.Dual
     Data.Monoid.Endo Data.Monoid.Mk_Any Data.Monoid.Mk_Dual Data.Monoid.Mk_Endo
     Data.Monoid.Mk_Product Data.Monoid.Mk_Sum Data.Monoid.appEndo Data.Monoid.getAny
     Data.Monoid.getDual Data.Monoid.getProduct Data.Monoid.getSum
     Data.Proxy.Mk_Proxy Data.Proxy.Proxy Data.Traversable.Traversable Data.Void.Void
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.build GHC.Base.compare GHC.Base.const
     GHC.Base.errorWithoutStackTrace GHC.Base.flip GHC.Base.fmap GHC.Base.id
     GHC.Base.max GHC.Base.mempty GHC.Base.min GHC.Base.op_z2218U__
     GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zlztzg__ GHC.Base.op_zsze__
     GHC.Base.op_ztzg__ GHC.Base.pure GHC.Enum.pred GHC.Num.Int GHC.Num.Num
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Prim.coerce GHC.Real.Integral GHC.Real.even
     GHC.Real.quot
*)
