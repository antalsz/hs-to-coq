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
Require Data.Foldable.
Require Data.Semigroup.Internal.
Require Data.Traversable.
Require FastString.
Require FastStringEnv.
Require GHC.Base.
Require GHC.Num.
Require Name.
Require OccName.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition FieldLabelString :=
  FastString.FastString%type.

Inductive FieldLbl a : Type
  := Mk_FieldLabel : FieldLabelString -> bool -> a -> FieldLbl a.

Definition FieldLabel :=
  (FieldLbl Name.Name)%type.

Definition FieldLabelEnv :=
  (FastStringEnv.DFastStringEnv FieldLabel)%type.

Arguments Mk_FieldLabel {_} _ _ _.

Definition flIsOverloaded {a} (arg_0__ : FieldLbl a) :=
  let 'Mk_FieldLabel _ flIsOverloaded _ := arg_0__ in
  flIsOverloaded.

Definition flLabel {a} (arg_1__ : FieldLbl a) :=
  let 'Mk_FieldLabel flLabel _ _ := arg_1__ in
  flLabel.

Definition flSelector {a} (arg_2__ : FieldLbl a) :=
  let 'Mk_FieldLabel _ _ flSelector := arg_2__ in
  flSelector.
(* Converted value declarations: *)

(* Translating `instance Outputable__FieldLbl' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__FieldLbl' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

Local Definition Foldable__FieldLbl_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> FieldLbl a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_FieldLabel a1 a2 a3 => f a3
      end.

Local Definition Foldable__FieldLbl_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> FieldLbl a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__FieldLbl_foldMap (Coq.Program.Basics.compose
                                                                        Data.Semigroup.Internal.Mk_Dual
                                                                        (Coq.Program.Basics.compose
                                                                         Data.Semigroup.Internal.Mk_Endo (GHC.Base.flip
                                                                          f))) t)) z
      end.

Local Definition Foldable__FieldLbl_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> FieldLbl a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__FieldLbl_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__FieldLbl_product
   : forall {a}, forall `{GHC.Num.Num a}, FieldLbl a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__FieldLbl_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__FieldLbl_sum
   : forall {a}, forall `{GHC.Num.Num a}, FieldLbl a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__FieldLbl_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__FieldLbl_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, FieldLbl m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__FieldLbl_foldMap GHC.Base.id.

Local Definition Foldable__FieldLbl_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> FieldLbl a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny
                                                             (Foldable__FieldLbl_foldMap (Coq.Program.Basics.compose
                                                                                          Data.Semigroup.Internal.Mk_Any
                                                                                          p))) _GHC.Base.==_.

Local Definition Foldable__FieldLbl_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> FieldLbl a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_FieldLabel a1 a2 a3 => f a3 z
      end.

Local Definition Foldable__FieldLbl_toList : forall {a}, FieldLbl a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__FieldLbl_foldr c n t
                        end).

Local Definition Foldable__FieldLbl_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> FieldLbl a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__FieldLbl_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__FieldLbl_length
   : forall {a}, FieldLbl a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__FieldLbl_foldl' (fun arg_64__ arg_65__ =>
                                 match arg_64__, arg_65__ with
                                 | c, _ => c GHC.Num.+ #1
                                 end) #0.

Local Definition Foldable__FieldLbl_null : forall {a}, FieldLbl a -> bool :=
  fun {a} => fun arg_0__ => let 'Mk_FieldLabel _ _ _ := arg_0__ in false.

Program Instance Foldable__FieldLbl : Data.Foldable.Foldable FieldLbl :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__FieldLbl_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__FieldLbl_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__FieldLbl_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__FieldLbl_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__FieldLbl_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__FieldLbl_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__FieldLbl_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__FieldLbl_length ;
         Data.Foldable.null__ := fun {a} => Foldable__FieldLbl_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__FieldLbl_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__FieldLbl_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__FieldLbl_toList |}.

Local Definition Functor__FieldLbl_fmap
   : forall {a} {b}, (a -> b) -> FieldLbl a -> FieldLbl b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_FieldLabel a1 a2 a3 =>
          Mk_FieldLabel ((fun b1 => b1) a1) ((fun b2 => b2) a2) (f a3)
      end.

Local Definition Functor__FieldLbl_op_zlzd__
   : forall {a} {b}, a -> FieldLbl b -> FieldLbl a :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | z, Mk_FieldLabel a1 a2 a3 =>
          Mk_FieldLabel ((fun b1 => b1) a1) ((fun b2 => b2) a2) ((fun b3 => z) a3)
      end.

Program Instance Functor__FieldLbl : GHC.Base.Functor FieldLbl :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__FieldLbl_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__FieldLbl_fmap |}.

Local Definition Traversable__FieldLbl_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> FieldLbl a -> f (FieldLbl b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_FieldLabel a1 a2 a3 =>
          GHC.Base.fmap (fun b3 => Mk_FieldLabel a1 a2 b3) (f a3)
      end.

Local Definition Traversable__FieldLbl_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, FieldLbl (f a) -> f (FieldLbl a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__FieldLbl_traverse GHC.Base.id.

Local Definition Traversable__FieldLbl_sequence
   : forall {m} {a},
     forall `{GHC.Base.Monad m}, FieldLbl (m a) -> m (FieldLbl a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__FieldLbl_sequenceA.

Local Definition Traversable__FieldLbl_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> FieldLbl a -> m (FieldLbl b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__FieldLbl_traverse.

Program Instance Traversable__FieldLbl
   : Data.Traversable.Traversable FieldLbl :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__FieldLbl_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__FieldLbl_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__FieldLbl_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__FieldLbl_traverse |}.

Local Definition Eq___FieldLbl_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : FieldLbl inst_a -> FieldLbl inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_FieldLabel a1 a2 a3, Mk_FieldLabel b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    end.

Local Definition Eq___FieldLbl_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : FieldLbl inst_a -> FieldLbl inst_a -> bool :=
  fun x y => negb (Eq___FieldLbl_op_zeze__ x y).

Program Instance Eq___FieldLbl {a} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (FieldLbl a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___FieldLbl_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___FieldLbl_op_zsze__ |}.

(* Translating `instance Data__FieldLbl' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

Definition mkFieldLabelOccs
   : FieldLabelString -> OccName.OccName -> bool -> FieldLbl OccName.OccName :=
  fun lbl dc is_overloaded =>
    let str :=
      Coq.Init.Datatypes.app (GHC.Base.hs_string__ ":") (Coq.Init.Datatypes.app
                              (FastString.unpackFS lbl) (Coq.Init.Datatypes.app (GHC.Base.hs_string__ ":")
                                                                                (OccName.occNameString dc))) in
    let sel_occ :=
      if is_overloaded : bool then OccName.mkRecFldSelOcc str else
      OccName.mkVarOccFS lbl in
    Mk_FieldLabel lbl is_overloaded sel_occ.

(* Unbound variables:
     andb bool false list negb Coq.Init.Datatypes.app Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Semigroup.Internal.Mk_Any
     Data.Semigroup.Internal.Mk_Dual Data.Semigroup.Internal.Mk_Endo
     Data.Semigroup.Internal.Mk_Product Data.Semigroup.Internal.Mk_Sum
     Data.Semigroup.Internal.appEndo Data.Semigroup.Internal.getAny
     Data.Semigroup.Internal.getDual Data.Semigroup.Internal.getProduct
     Data.Semigroup.Internal.getSum Data.Traversable.Traversable
     FastString.FastString FastString.unpackFS FastStringEnv.DFastStringEnv
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.build GHC.Base.flip GHC.Base.fmap GHC.Base.id
     GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__ Name.Name OccName.OccName
     OccName.mkRecFldSelOcc OccName.mkVarOccFS OccName.occNameString
*)
