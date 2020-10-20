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
Require Data.Functor.Identity.
Require Data.Proxy.
Require GHC.Base.
Require GHC.Tuple.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Record Eq2__Dict f := Eq2__Dict_Build {
  liftEq2__ : forall {a} {b} {c} {d},
  (a -> b -> bool) -> (c -> d -> bool) -> f a c -> f b d -> bool }.

Definition Eq2 f :=
  forall r__, (Eq2__Dict f -> r__) -> r__.
Existing Class Eq2.

Record Ord1__Dict f := Ord1__Dict_Build {
  liftCompare__ : forall {a} {b},
  (a -> b -> comparison) -> f a -> f b -> comparison }.

Definition liftEq2 `{g__0__ : Eq2 f}
   : forall {a} {b} {c} {d},
     (a -> b -> bool) -> (c -> d -> bool) -> f a c -> f b d -> bool :=
  g__0__ _ (liftEq2__ f).

Record Ord2__Dict f := Ord2__Dict_Build {
  liftCompare2__ : forall {a} {b} {c} {d},
  (a -> b -> comparison) ->
  (c -> d -> comparison) -> f a c -> f b d -> comparison }.

Definition Ord2 f `{(Eq2 f)} :=
  forall r__, (Ord2__Dict f -> r__) -> r__.
Existing Class Ord2.

Definition liftCompare2 `{g__0__ : Ord2 f}
   : forall {a} {b} {c} {d},
     (a -> b -> comparison) ->
     (c -> d -> comparison) -> f a c -> f b d -> comparison :=
  g__0__ _ (liftCompare2__ f).

Record Eq1__Dict f := Eq1__Dict_Build {
  liftEq__ : forall {a} {b}, (a -> b -> bool) -> f a -> f b -> bool }.

Definition Eq1 f :=
  forall r__, (Eq1__Dict f -> r__) -> r__.
Existing Class Eq1.

Definition liftEq `{g__0__ : Eq1 f}
   : forall {a} {b}, (a -> b -> bool) -> f a -> f b -> bool :=
  g__0__ _ (liftEq__ f).

Definition Ord1 f `{(Eq1 f)} :=
  forall r__, (Ord1__Dict f -> r__) -> r__.
Existing Class Ord1.

Definition liftCompare `{g__0__ : Ord1 f}
   : forall {a} {b}, (a -> b -> comparison) -> f a -> f b -> comparison :=
  g__0__ _ (liftCompare__ f).

(* Converted value declarations: *)

Local Definition Eq1__option_liftEq
   : forall {a} {b}, (a -> b -> bool) -> option a -> option b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, None, None => true
      | _, None, Some _ => false
      | _, Some _, None => false
      | eq, Some x, Some y => eq x y
      end.

Program Instance Eq1__option : Eq1 option :=
  fun _ k__ => k__ {| liftEq__ := fun {a} {b} => Eq1__option_liftEq |}.

Local Definition Ord1__option_liftCompare
   : forall {a} {b},
     (a -> b -> comparison) -> option a -> option b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, None, None => Eq
      | _, None, Some _ => Lt
      | _, Some _, None => Gt
      | comp, Some x, Some y => comp x y
      end.

Program Instance Ord1__option : Ord1 option :=
  fun _ k__ => k__ {| liftCompare__ := fun {a} {b} => Ord1__option_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Classes.Read1__option' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Classes.Show1__option' *)

Local Definition Eq1__list_liftEq
   : forall {a} {b}, (a -> b -> bool) -> list a -> list b -> bool :=
  fun {a} {b} =>
    fix liftEq arg_69__ arg_70__ arg_71__
          := match arg_69__, arg_70__, arg_71__ with
             | _, nil, nil => true
             | _, nil, cons _ _ => false
             | _, cons _ _, nil => false
             | eq, cons x xs, cons y ys => andb (eq x y) (liftEq eq xs ys)
             end.

Program Instance Eq1__list : Eq1 list :=
  fun _ k__ => k__ {| liftEq__ := fun {a} {b} => Eq1__list_liftEq |}.

Local Definition Ord1__list_liftCompare
   : forall {a} {b}, (a -> b -> comparison) -> list a -> list b -> comparison :=
  fun {a} {b} =>
    fix liftCompare arg_69__ arg_70__ arg_71__
          := match arg_69__, arg_70__, arg_71__ with
             | _, nil, nil => Eq
             | _, nil, cons _ _ => Lt
             | _, cons _ _, nil => Gt
             | comp, cons x xs, cons y ys =>
                 GHC.Base.mappend (comp x y) (liftCompare comp xs ys)
             end.

Program Instance Ord1__list : Ord1 list :=
  fun _ k__ => k__ {| liftCompare__ := fun {a} {b} => Ord1__list_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Classes.Read1__list' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Classes.Show1__list' *)

Local Definition Eq1__NonEmpty_liftEq
   : forall {a} {b},
     (a -> b -> bool) -> GHC.Base.NonEmpty a -> GHC.Base.NonEmpty b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, GHC.Base.NEcons a as_, GHC.Base.NEcons b bs =>
          andb (eq a b) (liftEq eq as_ bs)
      end.

Program Instance Eq1__NonEmpty : Eq1 GHC.Base.NonEmpty :=
  fun _ k__ => k__ {| liftEq__ := fun {a} {b} => Eq1__NonEmpty_liftEq |}.

Local Definition Ord1__NonEmpty_liftCompare
   : forall {a} {b},
     (a -> b -> comparison) ->
     GHC.Base.NonEmpty a -> GHC.Base.NonEmpty b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | cmp, GHC.Base.NEcons a as_, GHC.Base.NEcons b bs =>
          GHC.Base.mappend (cmp a b) (liftCompare cmp as_ bs)
      end.

Program Instance Ord1__NonEmpty : Ord1 GHC.Base.NonEmpty :=
  fun _ k__ =>
    k__ {| liftCompare__ := fun {a} {b} => Ord1__NonEmpty_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Classes.Read1__NonEmpty' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Classes.Show1__NonEmpty' *)

Local Definition Eq2__pair_type_liftEq2
   : forall {a} {b} {c} {d},
     (a -> b -> bool) ->
     (c -> d -> bool) ->
     GHC.Tuple.pair_type a c -> GHC.Tuple.pair_type b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | e1, e2, pair x1 y1, pair x2 y2 => andb (e1 x1 x2) (e2 y1 y2)
      end.

Program Instance Eq2__pair_type : Eq2 GHC.Tuple.pair_type :=
  fun _ k__ =>
    k__ {| liftEq2__ := fun {a} {b} {c} {d} => Eq2__pair_type_liftEq2 |}.

Local Definition Ord2__pair_type_liftCompare2
   : forall {a} {b} {c} {d},
     (a -> b -> comparison) ->
     (c -> d -> comparison) ->
     GHC.Tuple.pair_type a c -> GHC.Tuple.pair_type b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | comp1, comp2, pair x1 y1, pair x2 y2 =>
          GHC.Base.mappend (comp1 x1 x2) (comp2 y1 y2)
      end.

Program Instance Ord2__pair_type : Ord2 GHC.Tuple.pair_type :=
  fun _ k__ =>
    k__ {| liftCompare2__ := fun {a} {b} {c} {d} => Ord2__pair_type_liftCompare2 |}.

(* Skipping all instances of class `Data.Functor.Classes.Read2', including
   `Data.Functor.Classes.Read2__pair_type' *)

(* Skipping all instances of class `Data.Functor.Classes.Show2', including
   `Data.Functor.Classes.Show2__pair_type' *)

Local Definition Eq1__pair_type_liftEq {inst_a} `{(GHC.Base.Eq_ inst_a)}
   : forall {a} {b},
     (a -> b -> bool) ->
     (GHC.Tuple.pair_type inst_a) a -> (GHC.Tuple.pair_type inst_a) b -> bool :=
  fun {a} {b} => liftEq2 _GHC.Base.==_.

Program Instance Eq1__pair_type {a} `{(GHC.Base.Eq_ a)}
   : Eq1 (GHC.Tuple.pair_type a) :=
  fun _ k__ => k__ {| liftEq__ := fun {a} {b} => Eq1__pair_type_liftEq |}.

Local Definition Ord1__pair_type_liftCompare {inst_a} `{(GHC.Base.Ord inst_a)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (GHC.Tuple.pair_type inst_a) a ->
     (GHC.Tuple.pair_type inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Program Instance Ord1__pair_type {a} `{(GHC.Base.Ord a)}
   : Ord1 (GHC.Tuple.pair_type a) :=
  fun _ k__ =>
    k__ {| liftCompare__ := fun {a} {b} => Ord1__pair_type_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Classes.Read1__pair_type' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Classes.Show1__pair_type' *)

Local Definition Eq2__Either_liftEq2
   : forall {a} {b} {c} {d},
     (a -> b -> bool) ->
     (c -> d -> bool) -> Data.Either.Either a c -> Data.Either.Either b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | e1, _, Data.Either.Left x, Data.Either.Left y => e1 x y
      | _, _, Data.Either.Left _, Data.Either.Right _ => false
      | _, _, Data.Either.Right _, Data.Either.Left _ => false
      | _, e2, Data.Either.Right x, Data.Either.Right y => e2 x y
      end.

Program Instance Eq2__Either : Eq2 Data.Either.Either :=
  fun _ k__ => k__ {| liftEq2__ := fun {a} {b} {c} {d} => Eq2__Either_liftEq2 |}.

Local Definition Ord2__Either_liftCompare2
   : forall {a} {b} {c} {d},
     (a -> b -> comparison) ->
     (c -> d -> comparison) ->
     Data.Either.Either a c -> Data.Either.Either b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | comp1, _, Data.Either.Left x, Data.Either.Left y => comp1 x y
      | _, _, Data.Either.Left _, Data.Either.Right _ => Lt
      | _, _, Data.Either.Right _, Data.Either.Left _ => Gt
      | _, comp2, Data.Either.Right x, Data.Either.Right y => comp2 x y
      end.

Program Instance Ord2__Either : Ord2 Data.Either.Either :=
  fun _ k__ =>
    k__ {| liftCompare2__ := fun {a} {b} {c} {d} => Ord2__Either_liftCompare2 |}.

(* Skipping all instances of class `Data.Functor.Classes.Read2', including
   `Data.Functor.Classes.Read2__Either' *)

(* Skipping all instances of class `Data.Functor.Classes.Show2', including
   `Data.Functor.Classes.Show2__Either' *)

Local Definition Eq1__Either_liftEq {inst_a} `{(GHC.Base.Eq_ inst_a)}
   : forall {a} {b},
     (a -> b -> bool) ->
     (Data.Either.Either inst_a) a -> (Data.Either.Either inst_a) b -> bool :=
  fun {a} {b} => liftEq2 _GHC.Base.==_.

Program Instance Eq1__Either {a} `{(GHC.Base.Eq_ a)}
   : Eq1 (Data.Either.Either a) :=
  fun _ k__ => k__ {| liftEq__ := fun {a} {b} => Eq1__Either_liftEq |}.

Local Definition Ord1__Either_liftCompare {inst_a} `{(GHC.Base.Ord inst_a)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Data.Either.Either inst_a) a -> (Data.Either.Either inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Program Instance Ord1__Either {a} `{(GHC.Base.Ord a)}
   : Ord1 (Data.Either.Either a) :=
  fun _ k__ => k__ {| liftCompare__ := fun {a} {b} => Ord1__Either_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Classes.Read1__Either' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Classes.Show1__Either' *)

Local Definition Eq1__Identity_liftEq
   : forall {a} {b},
     (a -> b -> bool) ->
     Data.Functor.Identity.Identity a -> Data.Functor.Identity.Identity b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq
      , Data.Functor.Identity.Mk_Identity x
      , Data.Functor.Identity.Mk_Identity y =>
          eq x y
      end.

Program Instance Eq1__Identity : Eq1 Data.Functor.Identity.Identity :=
  fun _ k__ => k__ {| liftEq__ := fun {a} {b} => Eq1__Identity_liftEq |}.

Local Definition Ord1__Identity_liftCompare
   : forall {a} {b},
     (a -> b -> comparison) ->
     Data.Functor.Identity.Identity a ->
     Data.Functor.Identity.Identity b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp
      , Data.Functor.Identity.Mk_Identity x
      , Data.Functor.Identity.Mk_Identity y =>
          comp x y
      end.

Program Instance Ord1__Identity : Ord1 Data.Functor.Identity.Identity :=
  fun _ k__ =>
    k__ {| liftCompare__ := fun {a} {b} => Ord1__Identity_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Classes.Read1__Identity' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Classes.Show1__Identity' *)

Local Definition Eq2__Const_liftEq2
   : forall {a} {b} {c} {d},
     (a -> b -> bool) ->
     (c -> d -> bool) ->
     Data.Functor.Const.Const a c -> Data.Functor.Const.Const b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | eq, _, Data.Functor.Const.Mk_Const x, Data.Functor.Const.Mk_Const y => eq x y
      end.

Program Instance Eq2__Const : Eq2 Data.Functor.Const.Const :=
  fun _ k__ => k__ {| liftEq2__ := fun {a} {b} {c} {d} => Eq2__Const_liftEq2 |}.

Local Definition Ord2__Const_liftCompare2
   : forall {a} {b} {c} {d},
     (a -> b -> comparison) ->
     (c -> d -> comparison) ->
     Data.Functor.Const.Const a c -> Data.Functor.Const.Const b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | comp, _, Data.Functor.Const.Mk_Const x, Data.Functor.Const.Mk_Const y =>
          comp x y
      end.

Program Instance Ord2__Const : Ord2 Data.Functor.Const.Const :=
  fun _ k__ =>
    k__ {| liftCompare2__ := fun {a} {b} {c} {d} => Ord2__Const_liftCompare2 |}.

(* Skipping all instances of class `Data.Functor.Classes.Read2', including
   `Data.Functor.Classes.Read2__Const' *)

(* Skipping all instances of class `Data.Functor.Classes.Show2', including
   `Data.Functor.Classes.Show2__Const' *)

Local Definition Eq1__Const_liftEq {inst_a} `{(GHC.Base.Eq_ inst_a)}
   : forall {a} {b},
     (a -> b -> bool) ->
     (Data.Functor.Const.Const inst_a) a ->
     (Data.Functor.Const.Const inst_a) b -> bool :=
  fun {a} {b} => liftEq2 _GHC.Base.==_.

Program Instance Eq1__Const {a} `{(GHC.Base.Eq_ a)}
   : Eq1 (Data.Functor.Const.Const a) :=
  fun _ k__ => k__ {| liftEq__ := fun {a} {b} => Eq1__Const_liftEq |}.

Local Definition Ord1__Const_liftCompare {inst_a} `{(GHC.Base.Ord inst_a)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Data.Functor.Const.Const inst_a) a ->
     (Data.Functor.Const.Const inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Program Instance Ord1__Const {a} `{(GHC.Base.Ord a)}
   : Ord1 (Data.Functor.Const.Const a) :=
  fun _ k__ => k__ {| liftCompare__ := fun {a} {b} => Ord1__Const_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Classes.Read1__Const' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Classes.Show1__Const' *)

Local Definition Eq1__Proxy_liftEq
   : forall {a} {b},
     (a -> b -> bool) -> Data.Proxy.Proxy a -> Data.Proxy.Proxy b -> bool :=
  fun {a} {b} => fun arg_0__ arg_1__ arg_2__ => true.

Program Instance Eq1__Proxy : Eq1 Data.Proxy.Proxy :=
  fun _ k__ => k__ {| liftEq__ := fun {a} {b} => Eq1__Proxy_liftEq |}.

Local Definition Ord1__Proxy_liftCompare
   : forall {a} {b},
     (a -> b -> comparison) ->
     Data.Proxy.Proxy a -> Data.Proxy.Proxy b -> comparison :=
  fun {a} {b} => fun arg_0__ arg_1__ arg_2__ => Eq.

Program Instance Ord1__Proxy : Ord1 Data.Proxy.Proxy :=
  fun _ k__ => k__ {| liftCompare__ := fun {a} {b} => Ord1__Proxy_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Classes.Show1__Proxy' *)

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Classes.Read1__Proxy' *)

Definition eq1 {f} {a} `{Eq1 f} `{GHC.Base.Eq_ a} : f a -> f a -> bool :=
  liftEq _GHC.Base.==_.

Definition compare1 {f} {a} `{Ord1 f} `{GHC.Base.Ord a}
   : f a -> f a -> comparison :=
  liftCompare GHC.Base.compare.

(* Skipping definition `Data.Functor.Classes.readsPrec1' *)

(* Skipping definition `Data.Functor.Classes.readPrec1' *)

(* Skipping definition `Data.Functor.Classes.liftReadListDefault' *)

(* Skipping definition `Data.Functor.Classes.liftReadListPrecDefault' *)

(* Skipping definition `Data.Functor.Classes.showsPrec1' *)

Definition eq2 {f} {a} {b} `{Eq2 f} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b}
   : f a b -> f a b -> bool :=
  liftEq2 _GHC.Base.==_ _GHC.Base.==_.

Definition compare2 {f} {a} {b} `{Ord2 f} `{GHC.Base.Ord a} `{GHC.Base.Ord b}
   : f a b -> f a b -> comparison :=
  liftCompare2 GHC.Base.compare GHC.Base.compare.

(* Skipping definition `Data.Functor.Classes.readsPrec2' *)

(* Skipping definition `Data.Functor.Classes.readPrec2' *)

(* Skipping definition `Data.Functor.Classes.liftReadList2Default' *)

(* Skipping definition `Data.Functor.Classes.liftReadListPrec2Default' *)

(* Skipping definition `Data.Functor.Classes.showsPrec2' *)

(* Skipping definition `Data.Functor.Classes.readsData' *)

(* Skipping definition `Data.Functor.Classes.readData' *)

(* Skipping definition `Data.Functor.Classes.readsUnaryWith' *)

(* Skipping definition `Data.Functor.Classes.readUnaryWith' *)

(* Skipping definition `Data.Functor.Classes.readsBinaryWith' *)

(* Skipping definition `Data.Functor.Classes.readBinaryWith' *)

(* Skipping definition `Data.Functor.Classes.showsUnaryWith' *)

(* Skipping definition `Data.Functor.Classes.showsBinaryWith' *)

(* Skipping definition `Data.Functor.Classes.readsUnary' *)

(* Skipping definition `Data.Functor.Classes.readsUnary1' *)

(* Skipping definition `Data.Functor.Classes.readsBinary1' *)

(* Skipping definition `Data.Functor.Classes.showsUnary' *)

(* Skipping definition `Data.Functor.Classes.showsUnary1' *)

(* Skipping definition `Data.Functor.Classes.showsBinary1' *)

(* External variables:
     Eq Gt Lt None Some andb bool comparison cons false list option pair true
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Functor.Const.Const
     Data.Functor.Const.Mk_Const Data.Functor.Identity.Identity
     Data.Functor.Identity.Mk_Identity Data.Proxy.Proxy GHC.Base.Eq_ GHC.Base.NEcons
     GHC.Base.NonEmpty GHC.Base.Ord GHC.Base.compare GHC.Base.mappend
     GHC.Base.op_zeze__ GHC.Tuple.pair_type
*)
