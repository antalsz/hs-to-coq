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
Require Data.Monoid.
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

Inductive FieldLbl a : Type := Mk_FieldLabel
                              : FieldLabelString -> bool -> a -> FieldLbl a.

Definition FieldLabel :=
  (FieldLbl Name.Name)%type.

Definition FieldLabelEnv :=
  (FastStringEnv.FastStringEnv FieldLabel)%type.

Arguments Mk_FieldLabel {_} _ _ _.

Definition flIsOverloaded {a} (arg_0__ : FieldLbl a) :=
  match arg_0__ with
    | Mk_FieldLabel _ flIsOverloaded _ => flIsOverloaded
  end.

Definition flLabel {a} (arg_1__ : FieldLbl a) :=
  match arg_1__ with
    | Mk_FieldLabel flLabel _ _ => flLabel
  end.

Definition flSelector {a} (arg_2__ : FieldLbl a) :=
  match arg_2__ with
    | Mk_FieldLabel _ _ flSelector => flSelector
  end.
(* Converted value declarations: *)

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (FieldLabel.FieldLbl a)' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance forall {a}, forall `{Binary.Binary a}, Binary.Binary
   (FieldLabel.FieldLbl a)' failed: OOPS! Cannot find information for class
   Qualified "Binary" "Binary" unsupported *)

Local Definition Foldable__FieldLbl_foldMap : forall {m} {a},
                                                forall `{GHC.Base.Monoid m}, (a -> m) -> FieldLbl a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_FieldLabel a1 a2 a3 => f a3
      end.

Local Definition Foldable__FieldLbl_foldl : forall {b} {a},
                                              (b -> a -> b) -> b -> FieldLbl a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => Data.Monoid.appEndo (Data.Monoid.getDual
                                           (Foldable__FieldLbl_foldMap (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                                   (Coq.Program.Basics.compose
                                                                                                   Data.Monoid.Mk_Endo
                                                                                                   (GHC.Base.flip f)))
                                           t)) z
      end.

Local Definition Foldable__FieldLbl_foldr' : forall {a} {b},
                                               (a -> b -> b) -> b -> FieldLbl a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__FieldLbl_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__FieldLbl_product : forall {a},
                                                forall `{GHC.Num.Num a}, FieldLbl a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__FieldLbl_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__FieldLbl_sum : forall {a},
                                            forall `{GHC.Num.Num a}, FieldLbl a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__FieldLbl_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__FieldLbl_fold : forall {m},
                                             forall `{GHC.Base.Monoid m}, FieldLbl m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__FieldLbl_foldMap GHC.Base.id.

Local Definition Foldable__FieldLbl_elem : forall {a},
                                             forall `{GHC.Base.Eq_ a}, a -> FieldLbl a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__FieldLbl_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Local Definition Foldable__FieldLbl_foldr : forall {a} {b},
                                              (a -> b -> b) -> b -> FieldLbl a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | f , z , Mk_FieldLabel a1 a2 a3 => f a3 z
      end.

Local Definition Foldable__FieldLbl_null : forall {a}, FieldLbl a -> bool :=
  fun {a} => Foldable__FieldLbl_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__FieldLbl_toList : forall {a}, FieldLbl a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__FieldLbl_foldr c n t
                                end)
      end.

Local Definition Foldable__FieldLbl_foldl' : forall {b} {a},
                                               (b -> a -> b) -> b -> FieldLbl a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__FieldLbl_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__FieldLbl_length : forall {a},
                                               FieldLbl a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__FieldLbl_foldl' (fun arg_64__ arg_65__ =>
                                match arg_64__ , arg_65__ with
                                  | c , _ => _GHC.Num.+_ c (GHC.Num.fromInteger 1)
                                end) (GHC.Num.fromInteger 0).

Program Instance Foldable__FieldLbl : Data.Foldable.Foldable FieldLbl := fun _
                                                                             k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
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

Local Definition Functor__FieldLbl_fmap : forall {a} {b},
                                            (a -> b) -> FieldLbl a -> FieldLbl b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_FieldLabel a1 a2 a3 => Mk_FieldLabel ((fun b1 => b1) a1) ((fun b2 =>
                                                                            b2) a2) (f a3)
      end.

Local Definition Functor__FieldLbl_op_zlzd__ : forall {a} {b},
                                                 a -> FieldLbl b -> FieldLbl a :=
  fun {a} {b} => fun x => Functor__FieldLbl_fmap (GHC.Base.const x).

Program Instance Functor__FieldLbl : GHC.Base.Functor FieldLbl := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__FieldLbl_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__FieldLbl_fmap |}.

Local Definition Traversable__FieldLbl_traverse : forall {f} {a} {b},
                                                    forall `{GHC.Base.Applicative f},
                                                      (a -> f b) -> FieldLbl a -> f (FieldLbl b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_FieldLabel a1 a2 a3 => GHC.Base.fmap (fun b3 => Mk_FieldLabel a1 a2 b3)
                                        (f a3)
      end.

Local Definition Traversable__FieldLbl_sequenceA : forall {f} {a},
                                                     forall `{GHC.Base.Applicative f},
                                                       FieldLbl (f a) -> f (FieldLbl a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__FieldLbl_traverse GHC.Base.id.

Local Definition Traversable__FieldLbl_sequence : forall {m} {a},
                                                    forall `{GHC.Base.Monad m}, FieldLbl (m a) -> m (FieldLbl a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__FieldLbl_sequenceA.

Local Definition Traversable__FieldLbl_mapM : forall {m} {a} {b},
                                                forall `{GHC.Base.Monad m},
                                                  (a -> m b) -> FieldLbl a -> m (FieldLbl b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__FieldLbl_traverse.

Program Instance Traversable__FieldLbl : Data.Traversable.Traversable
                                         FieldLbl := fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
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
    match arg_0__ , arg_1__ with
      | Mk_FieldLabel a1 a2 a3 , Mk_FieldLabel b1 b2 b3 => (andb (andb ((a1
                                                                       GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3
                                                                 GHC.Base.== b3)))
    end.

Local Definition Eq___FieldLbl_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
    : FieldLbl inst_a -> FieldLbl inst_a -> bool :=
  fun a b => negb (Eq___FieldLbl_op_zeze__ a b).

Program Instance Eq___FieldLbl {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (FieldLbl
                                                                    a) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___FieldLbl_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___FieldLbl_op_zsze__ |}.

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (FieldLabel.FieldLbl a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

Definition mkFieldLabelOccs
    : FieldLabelString -> OccName.OccName -> bool -> FieldLbl OccName.OccName :=
  fun lbl dc is_overloaded =>
    let str :=
      Coq.Init.Datatypes.app (GHC.Base.hs_string__ ":") (Coq.Init.Datatypes.app
                             (FastString.unpackFS lbl) (Coq.Init.Datatypes.app (GHC.Base.hs_string__ ":")
                                                                               (OccName.occNameString dc))) in
    let sel_occ :=
      if is_overloaded : bool
      then OccName.mkRecFldSelOcc str
      else OccName.mkVarOccFS lbl in
    Mk_FieldLabel lbl is_overloaded sel_occ.

(* Unbound variables:
     andb bool false list negb true Coq.Init.Datatypes.app Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.hash_compose Data.Monoid.Mk_Any
     Data.Monoid.Mk_Dual Data.Monoid.Mk_Endo Data.Monoid.Mk_Product
     Data.Monoid.Mk_Sum Data.Monoid.appEndo Data.Monoid.getAny Data.Monoid.getDual
     Data.Monoid.getProduct Data.Monoid.getSum Data.Traversable.Traversable
     FastString.FastString FastString.unpackFS FastStringEnv.FastStringEnv
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.build GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.id GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Num.Int GHC.Num.Num
     GHC.Num.op_zp__ Name.Name OccName.OccName OccName.mkRecFldSelOcc
     OccName.mkVarOccFS OccName.occNameString
*)
