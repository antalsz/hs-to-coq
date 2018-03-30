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
Require GHC.Num.
Require GHC.Read.
Require GHC.Tuple.
Require Text.ParserCombinators.ReadP.
Require Text.ParserCombinators.ReadPrec.
Require Text.Read.Lex.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Record Eq2__Dict f := Eq2__Dict_Build {
  liftEq2__ : forall {a} {b} {c} {d},
  (a -> b -> bool) -> (c -> d -> bool) -> f a c -> f b d -> bool }.

Definition Eq2 f :=
  forall r, (Eq2__Dict f -> r) -> r.

Existing Class Eq2.

Definition liftEq2 `{g : Eq2 f}
   : forall {a} {b} {c} {d},
     (a -> b -> bool) -> (c -> d -> bool) -> f a c -> f b d -> bool :=
  g _ (liftEq2__ f).

Record Ord2__Dict f := Ord2__Dict_Build {
  liftCompare2__ : forall {a} {b} {c} {d},
  (a -> b -> comparison) ->
  (c -> d -> comparison) -> f a c -> f b d -> comparison }.

Definition Ord2 f `{(Eq2 f)} :=
  forall r, (Ord2__Dict f -> r) -> r.

Existing Class Ord2.

Definition liftCompare2 `{g : Ord2 f}
   : forall {a} {b} {c} {d},
     (a -> b -> comparison) ->
     (c -> d -> comparison) -> f a c -> f b d -> comparison :=
  g _ (liftCompare2__ f).

Record Eq1__Dict f := Eq1__Dict_Build {
  liftEq__ : forall {a} {b}, (a -> b -> bool) -> f a -> f b -> bool }.

Definition Eq1 f :=
  forall r, (Eq1__Dict f -> r) -> r.

Existing Class Eq1.

Definition liftEq `{g : Eq1 f}
   : forall {a} {b}, (a -> b -> bool) -> f a -> f b -> bool :=
  g _ (liftEq__ f).

Record Ord1__Dict f := Ord1__Dict_Build {
  liftCompare__ : forall {a} {b},
  (a -> b -> comparison) -> f a -> f b -> comparison }.

Definition Ord1 f `{(Eq1 f)} :=
  forall r, (Ord1__Dict f -> r) -> r.

Existing Class Ord1.

Definition liftCompare `{g : Ord1 f}
   : forall {a} {b}, (a -> b -> comparison) -> f a -> f b -> comparison :=
  g _ (liftCompare__ f).
(* Converted value declarations: *)

(* Translating `instance Show2__pair_type' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show2" unsupported *)

(* Translating `instance Show1__pair_type' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

(* Translating `instance Show2__Either' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show2" unsupported *)

(* Translating `instance Show1__Either' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

(* Translating `instance Show2__Const' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Show2" unsupported *)

(* Translating `instance Show1__Const' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Show1" unsupported *)

(* Translating `instance Read2__pair_type' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read2" unsupported *)

(* Translating `instance Read1__pair_type' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Read2__Either' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read2" unsupported *)

(* Translating `instance Read1__Either' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Read2__Const' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Read2" unsupported *)

(* Translating `instance Read1__Const' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Read1" unsupported *)

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
  fun _ k =>
    k {| liftCompare2__ := fun {a} {b} {c} {d} => Ord2__pair_type_liftCompare2 |}.

Local Definition Ord1__pair_type_liftCompare {inst_a} `{(GHC.Base.Ord inst_a)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (GHC.Tuple.pair_type inst_a) a ->
     (GHC.Tuple.pair_type inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Program Instance Ord1__pair_type {a} `{(GHC.Base.Ord a)}
   : Ord1 (GHC.Tuple.pair_type a) :=
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__pair_type_liftCompare |}.

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
  fun _ k =>
    k {| liftCompare2__ := fun {a} {b} {c} {d} => Ord2__Either_liftCompare2 |}.

Local Definition Ord1__Either_liftCompare {inst_a} `{(GHC.Base.Ord inst_a)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Data.Either.Either inst_a) a -> (Data.Either.Either inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Program Instance Ord1__Either {a} `{(GHC.Base.Ord a)}
   : Ord1 (Data.Either.Either a) :=
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__Either_liftCompare |}.

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
  fun _ k =>
    k {| liftCompare2__ := fun {a} {b} {c} {d} => Ord2__Const_liftCompare2 |}.

Local Definition Ord1__Const_liftCompare {inst_a} `{(GHC.Base.Ord inst_a)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Data.Functor.Const.Const inst_a) a ->
     (Data.Functor.Const.Const inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Program Instance Ord1__Const {a} `{(GHC.Base.Ord a)}
   : Ord1 (Data.Functor.Const.Const a) :=
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__Const_liftCompare |}.

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
  fun _ k => k {| liftEq2__ := fun {a} {b} {c} {d} => Eq2__pair_type_liftEq2 |}.

Local Definition Eq1__pair_type_liftEq {inst_a} `{(GHC.Base.Eq_ inst_a)}
   : forall {a} {b},
     (a -> b -> bool) ->
     (GHC.Tuple.pair_type inst_a) a -> (GHC.Tuple.pair_type inst_a) b -> bool :=
  fun {a} {b} => liftEq2 _GHC.Base.==_.

Program Instance Eq1__pair_type {a} `{(GHC.Base.Eq_ a)}
   : Eq1 (GHC.Tuple.pair_type a) :=
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__pair_type_liftEq |}.

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
  fun _ k => k {| liftEq2__ := fun {a} {b} {c} {d} => Eq2__Either_liftEq2 |}.

Local Definition Eq1__Either_liftEq {inst_a} `{(GHC.Base.Eq_ inst_a)}
   : forall {a} {b},
     (a -> b -> bool) ->
     (Data.Either.Either inst_a) a -> (Data.Either.Either inst_a) b -> bool :=
  fun {a} {b} => liftEq2 _GHC.Base.==_.

Program Instance Eq1__Either {a} `{(GHC.Base.Eq_ a)}
   : Eq1 (Data.Either.Either a) :=
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__Either_liftEq |}.

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
  fun _ k => k {| liftEq2__ := fun {a} {b} {c} {d} => Eq2__Const_liftEq2 |}.

Local Definition Eq1__Const_liftEq {inst_a} `{(GHC.Base.Eq_ inst_a)}
   : forall {a} {b},
     (a -> b -> bool) ->
     (Data.Functor.Const.Const inst_a) a ->
     (Data.Functor.Const.Const inst_a) b -> bool :=
  fun {a} {b} => liftEq2 _GHC.Base.==_.

Program Instance Eq1__Const {a} `{(GHC.Base.Eq_ a)}
   : Eq1 (Data.Functor.Const.Const a) :=
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__Const_liftEq |}.

(* Translating `instance Show1__option' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

(* Translating `instance Show1__list' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Show1" unsupported *)

(* Translating `instance Show1__NonEmpty' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

(* Translating `instance Show1__Identity' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

(* Translating `instance Show1__Proxy' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Show1" unsupported *)

(* Translating `instance Read1__option' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Read1__list' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Read1__NonEmpty' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Read1__Identity' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Read1__Proxy' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Read1" unsupported *)

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
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__option_liftCompare |}.

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
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__list_liftCompare |}.

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
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__NonEmpty_liftCompare |}.

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
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__Identity_liftCompare |}.

Local Definition Ord1__Proxy_liftCompare
   : forall {a} {b},
     (a -> b -> comparison) ->
     Data.Proxy.Proxy a -> Data.Proxy.Proxy b -> comparison :=
  fun {a} {b} => fun arg_0__ arg_1__ arg_2__ => Eq.

Program Instance Ord1__Proxy : Ord1 Data.Proxy.Proxy :=
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__Proxy_liftCompare |}.

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
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__option_liftEq |}.

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
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__list_liftEq |}.

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
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__NonEmpty_liftEq |}.

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
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__Identity_liftEq |}.

Local Definition Eq1__Proxy_liftEq
   : forall {a} {b},
     (a -> b -> bool) -> Data.Proxy.Proxy a -> Data.Proxy.Proxy b -> bool :=
  fun {a} {b} => fun arg_0__ arg_1__ arg_2__ => true.

Program Instance Eq1__Proxy : Eq1 Data.Proxy.Proxy :=
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__Proxy_liftEq |}.

Definition compare1 {f} {a} `{Ord1 f} `{GHC.Base.Ord a}
   : f a -> f a -> comparison :=
  liftCompare GHC.Base.compare.

Definition compare2 {f} {a} {b} `{Ord2 f} `{GHC.Base.Ord a} `{GHC.Base.Ord b}
   : f a b -> f a b -> comparison :=
  liftCompare2 GHC.Base.compare GHC.Base.compare.

Definition eq1 {f} {a} `{Eq1 f} `{GHC.Base.Eq_ a} : f a -> f a -> bool :=
  liftEq _GHC.Base.==_.

Definition eq2 {f} {a} {b} `{Eq2 f} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b}
   : f a b -> f a b -> bool :=
  liftEq2 _GHC.Base.==_ _GHC.Base.==_.

Definition liftReadList2Default {f} {a} {b} `{Read2 f}
   : (GHC.Num.Int -> Text.ParserCombinators.ReadP.ReadS a) ->
     Text.ParserCombinators.ReadP.ReadS (list a) ->
     (GHC.Num.Int -> Text.ParserCombinators.ReadP.ReadS b) ->
     Text.ParserCombinators.ReadP.ReadS (list b) ->
     Text.ParserCombinators.ReadP.ReadS (list (f a b)) :=
  fun rp1 rl1 rp2 rl2 =>
    Text.ParserCombinators.ReadPrec.readPrec_to_S (liftReadListPrec2
                                                   (Text.ParserCombinators.ReadPrec.readS_to_Prec rp1)
                                                   (Text.ParserCombinators.ReadPrec.readS_to_Prec (GHC.Base.const rl1))
                                                   (Text.ParserCombinators.ReadPrec.readS_to_Prec rp2)
                                                   (Text.ParserCombinators.ReadPrec.readS_to_Prec (GHC.Base.const rl2)))
    #0.

Definition liftReadListDefault {f} {a} `{Read1 f}
   : (GHC.Num.Int -> Text.ParserCombinators.ReadP.ReadS a) ->
     Text.ParserCombinators.ReadP.ReadS (list a) ->
     Text.ParserCombinators.ReadP.ReadS (list (f a)) :=
  fun rp rl =>
    Text.ParserCombinators.ReadPrec.readPrec_to_S (liftReadListPrec
                                                   (Text.ParserCombinators.ReadPrec.readS_to_Prec rp)
                                                   (Text.ParserCombinators.ReadPrec.readS_to_Prec (GHC.Base.const rl)))
    #0.

Definition liftReadListPrec2Default {f} {a} {b} `{Read2 f}
   : Text.ParserCombinators.ReadPrec.ReadPrec a ->
     Text.ParserCombinators.ReadPrec.ReadPrec (list a) ->
     Text.ParserCombinators.ReadPrec.ReadPrec b ->
     Text.ParserCombinators.ReadPrec.ReadPrec (list b) ->
     Text.ParserCombinators.ReadPrec.ReadPrec (list (f a b)) :=
  fun rp1 rl1 rp2 rl2 => GHC.Read.list (liftReadPrec2 rp1 rl1 rp2 rl2).

Definition liftReadListPrecDefault {f} {a} `{Read1 f}
   : Text.ParserCombinators.ReadPrec.ReadPrec a ->
     Text.ParserCombinators.ReadPrec.ReadPrec (list a) ->
     Text.ParserCombinators.ReadPrec.ReadPrec (list (f a)) :=
  fun rp rl => GHC.Read.list (liftReadPrec rp rl).

Definition readBinaryWith {a} {b} {t}
   : Text.ParserCombinators.ReadPrec.ReadPrec a ->
     Text.ParserCombinators.ReadPrec.ReadPrec b ->
     GHC.Base.String ->
     (a -> b -> t) -> Text.ParserCombinators.ReadPrec.ReadPrec t :=
  fun rp1 rp2 name cons_ =>
    GHC.Read.expectP (Text.Read.Lex.Ident name) GHC.Base.>>
    (Text.ParserCombinators.ReadPrec.step rp1 GHC.Base.>>=
     (fun x =>
        Text.ParserCombinators.ReadPrec.step rp2 GHC.Base.>>=
        (fun y => GHC.Base.return_ (cons_ x y)))).

Definition readData {a}
   : Text.ParserCombinators.ReadPrec.ReadPrec a ->
     Text.ParserCombinators.ReadPrec.ReadPrec a :=
  fun reader => GHC.Read.parens (Text.ParserCombinators.ReadPrec.prec #10 reader).

Definition readPrec1 {f} {a} `{Read1 f} `{GHC.Read.Read a}
   : Text.ParserCombinators.ReadPrec.ReadPrec (f a) :=
  liftReadPrec GHC.Read.readPrec GHC.Read.readListPrec.

Definition readPrec2 {f} {a} {b} `{Read2 f} `{GHC.Read.Read a} `{GHC.Read.Read
  b}
   : Text.ParserCombinators.ReadPrec.ReadPrec (f a b) :=
  liftReadPrec2 GHC.Read.readPrec GHC.Read.readListPrec GHC.Read.readPrec
  GHC.Read.readListPrec.

Definition readUnaryWith {a} {t}
   : Text.ParserCombinators.ReadPrec.ReadPrec a ->
     GHC.Base.String -> (a -> t) -> Text.ParserCombinators.ReadPrec.ReadPrec t :=
  fun rp name cons_ =>
    GHC.Read.expectP (Text.Read.Lex.Ident name) GHC.Base.>>
    (Text.ParserCombinators.ReadPrec.step rp GHC.Base.>>=
     (fun x => GHC.Base.return_ (cons_ x))).

(* Unbound variables:
     Eq Gt Lt None Read1 Read2 Some andb bool comparison cons false liftReadListPrec
     liftReadListPrec2 liftReadPrec liftReadPrec2 list option pair true
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Functor.Const.Const
     Data.Functor.Const.Mk_Const Data.Functor.Identity.Identity
     Data.Functor.Identity.Mk_Identity Data.Proxy.Proxy GHC.Base.Eq_ GHC.Base.NEcons
     GHC.Base.NonEmpty GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.const
     GHC.Base.mappend GHC.Base.op_zeze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.return_ GHC.Num.Int GHC.Num.fromInteger GHC.Read.Read GHC.Read.expectP
     GHC.Read.list GHC.Read.parens GHC.Read.readListPrec GHC.Read.readPrec
     GHC.Tuple.pair_type Text.ParserCombinators.ReadP.ReadS
     Text.ParserCombinators.ReadPrec.ReadPrec Text.ParserCombinators.ReadPrec.prec
     Text.ParserCombinators.ReadPrec.readPrec_to_S
     Text.ParserCombinators.ReadPrec.readS_to_Prec
     Text.ParserCombinators.ReadPrec.step Text.Read.Lex.Ident
*)
