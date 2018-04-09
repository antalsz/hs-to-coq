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
Require Data.SemigroupInternal.
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

Definition flLabel {a} (arg_0__ : FieldLbl a) :=
  let 'Mk_FieldLabel flLabel _ _ := arg_0__ in
  flLabel.

Definition flSelector {a} (arg_0__ : FieldLbl a) :=
  let 'Mk_FieldLabel _ _ flSelector := arg_0__ in
  flSelector.
(* Converted value declarations: *)

(* Skipping instance Outputable__FieldLbl of class Outputable *)

(* Skipping instance Binary__FieldLbl of class Binary *)

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
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__FieldLbl_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                   (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                    GHC.Base.flip f)) t)) z.

Local Definition Foldable__FieldLbl_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> FieldLbl a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__FieldLbl_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__FieldLbl_product
   : forall {a}, forall `{GHC.Num.Num a}, FieldLbl a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__FieldLbl_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__FieldLbl_sum
   : forall {a}, forall `{GHC.Num.Num a}, FieldLbl a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__FieldLbl_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__FieldLbl_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, FieldLbl m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__FieldLbl_foldMap GHC.Base.id.

Local Definition Foldable__FieldLbl_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> FieldLbl a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_FieldLabel a1 a2 a3 => f a3 z
      end.

Local Definition Foldable__FieldLbl_toList : forall {a}, FieldLbl a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__FieldLbl_foldr c n t)).

Local Definition Foldable__FieldLbl_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> FieldLbl a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__FieldLbl_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__FieldLbl_length
   : forall {a}, FieldLbl a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__FieldLbl_foldl' (fun arg_0__ arg_1__ =>
                                 match arg_0__, arg_1__ with
                                 | c, _ => c GHC.Num.+ #1
                                 end) #0.

Local Definition Foldable__FieldLbl_null : forall {a}, FieldLbl a -> bool :=
  fun {a} => fun '(Mk_FieldLabel _ _ _) => false.

Program Instance Foldable__FieldLbl : Data.Foldable.Foldable FieldLbl :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
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
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__FieldLbl_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__FieldLbl_op_zlzd__ |}.

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

(* Skipping instance Data__FieldLbl of class Data *)

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

(* External variables:
     andb bool false list negb Coq.Init.Datatypes.app Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ FastString.FastString FastString.unpackFS
     FastStringEnv.DFastStringEnv GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.build' GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zlzd____ GHC.Base.op_zsze____ GHC.Num.Int
     GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ Name.Name OccName.OccName
     OccName.mkRecFldSelOcc OccName.mkVarOccFS OccName.occNameString
*)
