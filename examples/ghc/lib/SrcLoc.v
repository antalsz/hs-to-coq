(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Semigroup.Internal.
Require Data.Traversable.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive RealSrcSpan : Type
  := RealSrcSpan'
   : FastString.FastString ->
     GHC.Num.Int -> GHC.Num.Int -> GHC.Num.Int -> GHC.Num.Int -> RealSrcSpan.

Inductive SrcSpan : Type
  := ARealSrcSpan : RealSrcSpan -> SrcSpan
  |  UnhelpfulSpan : FastString.FastString -> SrcSpan.

Inductive RealSrcLoc : Type
  := ASrcLoc : FastString.FastString -> GHC.Num.Int -> GHC.Num.Int -> RealSrcLoc.

Inductive SrcLoc : Type
  := ARealSrcLoc : RealSrcLoc -> SrcLoc
  |  UnhelpfulLoc : FastString.FastString -> SrcLoc.

Inductive GenLocated l e : Type := L : l -> e -> GenLocated l e.

Definition Located :=
  (GenLocated SrcSpan)%type.

Definition RealLocated :=
  (GenLocated RealSrcSpan)%type.

Arguments L {_} {_} _ _.

Definition srcSpanECol (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ _ _ _ srcSpanECol := arg_0__ in
  srcSpanECol.

Definition srcSpanELine (arg_1__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ _ _ srcSpanELine _ := arg_1__ in
  srcSpanELine.

Definition srcSpanFile (arg_2__ : RealSrcSpan) :=
  let 'RealSrcSpan' srcSpanFile _ _ _ _ := arg_2__ in
  srcSpanFile.

Definition srcSpanSCol (arg_3__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ _ srcSpanSCol _ _ := arg_3__ in
  srcSpanSCol.

Definition srcSpanSLine (arg_4__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ srcSpanSLine _ _ _ := arg_4__ in
  srcSpanSLine.
(* Midamble *)

(* Default values *)
Require Import GHC.Err.
Instance Default_SrcSpan : Default SrcSpan := Build_Default _ (UnhelpfulSpan default).

(* Converted value declarations: *)

(* Translating `instance Outputable__GenLocated' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Data__SrcSpan' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance ToJson__SrcSpan' failed: OOPS! Cannot find information
   for class Qualified "Json" "ToJson" unsupported *)

(* Translating `instance NFData__SrcSpan' failed: OOPS! Cannot find information
   for class Qualified "Control.DeepSeq" "NFData" unsupported *)

(* Translating `instance Outputable__SrcSpan' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Data__RealSrcSpan' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance ToJson__RealSrcSpan' failed: OOPS! Cannot find
   information for class Qualified "Json" "ToJson" unsupported *)

(* Translating `instance Show__RealSrcSpan' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Outputable__RealSrcSpan' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__SrcLoc' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__RealSrcLoc' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Show__RealSrcLoc' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Traversable__GenLocated_traverse {inst_l}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GenLocated inst_l a -> f (GenLocated inst_l b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, L a1 a2 => GHC.Base.fmap (fun b2 => L a1 b2) (f a2)
      end.

Local Definition Traversable__GenLocated_sequenceA {inst_l}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     GenLocated inst_l (f a) -> f (GenLocated inst_l a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__GenLocated_traverse GHC.Base.id.

Local Definition Traversable__GenLocated_sequence {inst_l}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     GenLocated inst_l (m a) -> m (GenLocated inst_l a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__GenLocated_sequenceA.

Local Definition Traversable__GenLocated_mapM {inst_l}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GenLocated inst_l a -> m (GenLocated inst_l b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__GenLocated_traverse.

Local Definition Foldable__GenLocated_foldMap {inst_l}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GenLocated inst_l a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, L a1 a2 => f a2 end.

Local Definition Foldable__GenLocated_foldl {inst_l}
   : forall {b} {a}, (b -> a -> b) -> b -> GenLocated inst_l a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__GenLocated_foldMap (Coq.Program.Basics.compose
                                                                          Data.Semigroup.Internal.Mk_Dual
                                                                          (Coq.Program.Basics.compose
                                                                           Data.Semigroup.Internal.Mk_Endo
                                                                           (GHC.Base.flip f))) t)) z
      end.

Local Definition Foldable__GenLocated_foldr' {inst_l}
   : forall {a} {b}, (a -> b -> b) -> b -> GenLocated inst_l a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__GenLocated_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__GenLocated_product {inst_l}
   : forall {a}, forall `{GHC.Num.Num a}, GenLocated inst_l a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__GenLocated_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__GenLocated_sum {inst_l}
   : forall {a}, forall `{GHC.Num.Num a}, GenLocated inst_l a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__GenLocated_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__GenLocated_fold {inst_l}
   : forall {m}, forall `{GHC.Base.Monoid m}, GenLocated inst_l m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__GenLocated_foldMap GHC.Base.id.

Local Definition Foldable__GenLocated_elem {inst_l}
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> GenLocated inst_l a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny
                                                             (Foldable__GenLocated_foldMap (Coq.Program.Basics.compose
                                                                                            Data.Semigroup.Internal.Mk_Any
                                                                                            p))) _GHC.Base.==_.

Local Definition Foldable__GenLocated_foldr {inst_l}
   : forall {a} {b}, (a -> b -> b) -> b -> GenLocated inst_l a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, L a1 a2 => f a2 z
      end.

Local Definition Foldable__GenLocated_toList {inst_l}
   : forall {a}, GenLocated inst_l a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__GenLocated_foldr c n t
                        end).

Local Definition Foldable__GenLocated_foldl' {inst_l}
   : forall {b} {a}, (b -> a -> b) -> b -> GenLocated inst_l a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__GenLocated_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__GenLocated_length {inst_l}
   : forall {a}, GenLocated inst_l a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__GenLocated_foldl' (fun arg_64__ arg_65__ =>
                                   match arg_64__, arg_65__ with
                                   | c, _ => c GHC.Num.+ #1
                                   end) #0.

Local Definition Foldable__GenLocated_null {inst_l}
   : forall {a}, GenLocated inst_l a -> bool :=
  fun {a} => fun arg_0__ => let 'L _ _ := arg_0__ in false.

Local Definition Functor__GenLocated_fmap {inst_l}
   : forall {a} {b}, (a -> b) -> GenLocated inst_l a -> GenLocated inst_l b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, L a1 a2 => L ((fun b1 => b1) a1) (f a2)
      end.

Local Definition Functor__GenLocated_op_zlzd__ {inst_l}
   : forall {a} {b}, a -> GenLocated inst_l b -> GenLocated inst_l a :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | z, L a1 a2 => L ((fun b1 => b1) a1) ((fun b2 => z) a2)
      end.

Program Instance Functor__GenLocated {l} : GHC.Base.Functor (GenLocated l) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__GenLocated_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__GenLocated_fmap |}.

Program Instance Foldable__GenLocated {l}
   : Data.Foldable.Foldable (GenLocated l) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__GenLocated_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__GenLocated_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__GenLocated_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__GenLocated_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__GenLocated_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__GenLocated_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__GenLocated_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__GenLocated_length ;
         Data.Foldable.null__ := fun {a} => Foldable__GenLocated_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__GenLocated_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__GenLocated_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__GenLocated_toList |}.

Program Instance Traversable__GenLocated {l}
   : Data.Traversable.Traversable (GenLocated l) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__GenLocated_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__GenLocated_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__GenLocated_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__GenLocated_traverse |}.

(* Translating `instance Data__GenLocated' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Skipping instance Ord__GenLocated *)

Local Definition Eq___GenLocated_op_zeze__ {inst_l} {inst_e} `{GHC.Base.Eq_
  inst_l} `{GHC.Base.Eq_ inst_e}
   : GenLocated inst_l inst_e -> GenLocated inst_l inst_e -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | L a1 a2, L b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___GenLocated_op_zsze__ {inst_l : Type} {inst_e : Type} `{H
   : GHC.Base.Eq_ inst_e} `{J : GHC.Base.Eq_ inst_l}
   : GenLocated inst_l inst_e -> GenLocated inst_l inst_e -> bool :=
  fun a b => negb (Eq___GenLocated_op_zeze__ a b).

Program Instance Eq___GenLocated {l} {e} `{GHC.Base.Eq_ l} `{GHC.Base.Eq_ e}
   : GHC.Base.Eq_ (GenLocated l e) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___GenLocated_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___GenLocated_op_zsze__ |}.

(* Translating `instance Show__SrcSpan' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Eq___RealSrcSpan_op_zeze__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RealSrcSpan' a1 a2 a3 a4 a5, RealSrcSpan' b1 b2 b3 b4 b5 =>
        (andb (andb (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3
                            GHC.Base.==
                            b3))) ((a4 GHC.Base.== b4))) ((a5 GHC.Base.== b5)))
    end.

Local Definition Eq___RealSrcSpan_op_zsze__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun arg_176__ arg_177__ =>
    match arg_176__, arg_177__ with
    | a, b => negb (Eq___RealSrcSpan_op_zeze__ a b)
    end.

Program Instance Eq___RealSrcSpan : GHC.Base.Eq_ RealSrcSpan :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___RealSrcSpan_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___RealSrcSpan_op_zsze__ |}.

Local Definition Eq___SrcSpan_op_zeze__ : SrcSpan -> SrcSpan -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ARealSrcSpan a1, ARealSrcSpan b1 => ((a1 GHC.Base.== b1))
    | UnhelpfulSpan a1, UnhelpfulSpan b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___SrcSpan_op_zsze__ : SrcSpan -> SrcSpan -> bool :=
  fun arg_185__ arg_186__ =>
    match arg_185__, arg_186__ with
    | a, b => negb (Eq___SrcSpan_op_zeze__ a b)
    end.

Program Instance Eq___SrcSpan : GHC.Base.Eq_ SrcSpan :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___SrcSpan_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___SrcSpan_op_zsze__ |}.

(* Translating `instance Show__SrcLoc' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__SrcLoc_compare : SrcLoc -> SrcLoc -> comparison :=
  fun a b =>
    match a with
    | ARealSrcLoc a1 =>
        match b with
        | ARealSrcLoc b1 => (GHC.Base.compare a1 b1)
        | _ => Lt
        end
    | UnhelpfulLoc a1 =>
        match b with
        | UnhelpfulLoc b1 => (GHC.Base.compare a1 b1)
        | _ => Gt
        end
    end.

Local Definition Ord__SrcLoc_op_zl__ : SrcLoc -> SrcLoc -> bool :=
  fun a b =>
    match a with
    | ARealSrcLoc a1 =>
        match b with
        | ARealSrcLoc b1 => (a1 GHC.Base.< b1)
        | _ => true
        end
    | UnhelpfulLoc a1 =>
        match b with
        | UnhelpfulLoc b1 => (a1 GHC.Base.< b1)
        | _ => false
        end
    end.

Local Definition Ord__SrcLoc_op_zlze__ : SrcLoc -> SrcLoc -> bool :=
  fun a b => negb (Ord__SrcLoc_op_zl__ b a).

Local Definition Ord__SrcLoc_min : SrcLoc -> SrcLoc -> SrcLoc :=
  fun x y => if Ord__SrcLoc_op_zlze__ x y : bool then x else y.

Local Definition Ord__SrcLoc_max : SrcLoc -> SrcLoc -> SrcLoc :=
  fun x y => if Ord__SrcLoc_op_zlze__ x y : bool then y else x.

Local Definition Ord__SrcLoc_op_zgze__ : SrcLoc -> SrcLoc -> bool :=
  fun a b => negb (Ord__SrcLoc_op_zl__ a b).

Local Definition Ord__SrcLoc_op_zg__ : SrcLoc -> SrcLoc -> bool :=
  fun a b => Ord__SrcLoc_op_zl__ b a.

Local Definition Eq___SrcLoc_op_zeze__ : SrcLoc -> SrcLoc -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ARealSrcLoc a1, ARealSrcLoc b1 => ((a1 GHC.Base.== b1))
    | UnhelpfulLoc a1, UnhelpfulLoc b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___SrcLoc_op_zsze__ : SrcLoc -> SrcLoc -> bool :=
  fun x y => negb (Eq___SrcLoc_op_zeze__ x y).

Program Instance Eq___SrcLoc : GHC.Base.Eq_ SrcLoc :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___SrcLoc_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___SrcLoc_op_zsze__ |}.

Program Instance Ord__SrcLoc : GHC.Base.Ord SrcLoc :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__SrcLoc_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__SrcLoc_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__SrcLoc_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__SrcLoc_op_zgze__ ;
         GHC.Base.compare__ := Ord__SrcLoc_compare ;
         GHC.Base.max__ := Ord__SrcLoc_max ;
         GHC.Base.min__ := Ord__SrcLoc_min |}.

Local Definition Ord__RealSrcLoc_compare
   : RealSrcLoc -> RealSrcLoc -> comparison :=
  fun a b =>
    let 'ASrcLoc a1 a2 a3 := a in
    let 'ASrcLoc b1 b2 b3 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => Lt
    | Eq =>
        match (GHC.Base.compare a2 b2) with
        | Lt => Lt
        | Eq => (GHC.Base.compare a3 b3)
        | Gt => Gt
        end
    | Gt => Gt
    end.

Local Definition Ord__RealSrcLoc_op_zl__ : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b =>
    let 'ASrcLoc a1 a2 a3 := a in
    let 'ASrcLoc b1 b2 b3 := b in
    match (Ord__RealSrcLoc_compare a1 b1) with
    | Lt => true
    | Eq =>
        match (Ord__RealSrcLoc_compare a2 b2) with
        | Lt => true
        | Eq => (a3 GHC.Base.< b3)
        | Gt => false
        end
    | Gt => false
    end.

Local Definition Ord__RealSrcLoc_op_zg__ : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b => Ord__RealSrcLoc_op_zl__ b a.

Local Definition Ord__RealSrcLoc_op_zgze__ : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b => negb (Ord__RealSrcLoc_op_zl__ a b).

Local Definition Ord__RealSrcLoc_op_zlze__ : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b => negb (Ord__RealSrcLoc_op_zl__ b a).

Local Definition Eq___RealSrcLoc_op_zeze__ : RealSrcLoc -> RealSrcLoc -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ASrcLoc a1 a2 a3, ASrcLoc b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    end.

Local Definition Eq___RealSrcLoc_op_zsze__ : RealSrcLoc -> RealSrcLoc -> bool :=
  fun x y => negb (Eq___RealSrcLoc_op_zeze__ x y).

Program Instance Eq___RealSrcLoc : GHC.Base.Eq_ RealSrcLoc :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___RealSrcLoc_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___RealSrcLoc_op_zsze__ |}.

Local Definition Ord__RealSrcLoc_min : RealSrcLoc -> RealSrcLoc -> RealSrcLoc :=
  fun x y => if Ord__RealSrcLoc_op_zlze__ x y : bool then x else y.

Local Definition Ord__RealSrcLoc_max : RealSrcLoc -> RealSrcLoc -> RealSrcLoc :=
  fun x y => if Ord__RealSrcLoc_op_zlze__ x y : bool then y else x.

Program Instance Ord__RealSrcLoc : GHC.Base.Ord RealSrcLoc :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__RealSrcLoc_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__RealSrcLoc_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__RealSrcLoc_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__RealSrcLoc_op_zgze__ ;
         GHC.Base.compare__ := Ord__RealSrcLoc_compare ;
         GHC.Base.max__ := Ord__RealSrcLoc_max ;
         GHC.Base.min__ := Ord__RealSrcLoc_min |}.

Definition generatedSrcLoc : SrcLoc :=
  UnhelpfulLoc (FastString.fsLit (GHC.Base.hs_string__
                                  "<compiler-generated code>")).

Definition getLoc {l} {e} : GenLocated l e -> l :=
  fun arg_0__ => let 'L l _ := arg_0__ in l.

Definition interactiveSrcLoc : SrcLoc :=
  UnhelpfulLoc (FastString.fsLit (GHC.Base.hs_string__ "<interactive>")).

Definition interactiveSrcSpan : SrcSpan :=
  UnhelpfulSpan (FastString.fsLit (GHC.Base.hs_string__ "<interactive>")).

Definition isGoodSrcSpan : SrcSpan -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan _ => true
    | UnhelpfulSpan _ => false
    end.

Definition isOneLineRealSpan : RealSrcSpan -> bool :=
  fun arg_0__ =>
    let 'RealSrcSpan' _ line1 _ line2 _ := arg_0__ in
    line1 GHC.Base.== line2.

Definition isPointRealSpan : RealSrcSpan -> bool :=
  fun arg_0__ =>
    let 'RealSrcSpan' _ line1 col1 line2 col2 := arg_0__ in
    andb (line1 GHC.Base.== line2) (col1 GHC.Base.== col2).

Definition mkGeneralSrcLoc : FastString.FastString -> SrcLoc :=
  UnhelpfulLoc.

Definition mkGeneralSrcSpan : FastString.FastString -> SrcSpan :=
  UnhelpfulSpan.

Definition mkGeneralLocated {e} : GHC.Base.String -> e -> Located e :=
  fun s e => L (mkGeneralSrcSpan (FastString.fsLit s)) e.

Definition mkRealSrcLoc
   : FastString.FastString -> GHC.Num.Int -> GHC.Num.Int -> RealSrcLoc :=
  fun x line col => ASrcLoc x line col.

Definition mkSrcLoc
   : FastString.FastString -> GHC.Num.Int -> GHC.Num.Int -> SrcLoc :=
  fun x line col => ARealSrcLoc (mkRealSrcLoc x line col).

Definition noSrcLoc : SrcLoc :=
  UnhelpfulLoc (FastString.fsLit (GHC.Base.hs_string__ "<no location info>")).

Definition noSrcSpan : SrcSpan :=
  UnhelpfulSpan (FastString.fsLit (GHC.Base.hs_string__ "<no location info>")).

Definition noLoc {e} : e -> Located e :=
  fun e => L noSrcSpan e.

Definition realSrcLocSpan : RealSrcLoc -> RealSrcSpan :=
  fun arg_0__ =>
    let 'ASrcLoc file line col := arg_0__ in
    RealSrcSpan' file line col line col.

Definition srcLocSpan : SrcLoc -> SrcSpan :=
  fun arg_0__ =>
    match arg_0__ with
    | UnhelpfulLoc str => UnhelpfulSpan str
    | ARealSrcLoc l => ARealSrcSpan (realSrcLocSpan l)
    end.

Definition srcLocCol : RealSrcLoc -> GHC.Num.Int :=
  fun arg_0__ => let 'ASrcLoc _ _ c := arg_0__ in c.

Definition srcLocFile : RealSrcLoc -> FastString.FastString :=
  fun arg_0__ => let 'ASrcLoc fname _ _ := arg_0__ in fname.

Definition srcLocLine : RealSrcLoc -> GHC.Num.Int :=
  fun arg_0__ => let 'ASrcLoc _ l _ := arg_0__ in l.

Definition mkRealSrcSpan : RealSrcLoc -> RealSrcLoc -> RealSrcSpan :=
  fun loc1 loc2 =>
    let file := srcLocFile loc1 in
    let col2 := srcLocCol loc2 in
    let col1 := srcLocCol loc1 in
    let line2 := srcLocLine loc2 in
    let line1 := srcLocLine loc1 in RealSrcSpan' file line1 col1 line2 col2.

Definition mkSrcSpan : SrcLoc -> SrcLoc -> SrcSpan :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UnhelpfulLoc str, _ => UnhelpfulSpan str
    | _, UnhelpfulLoc str => UnhelpfulSpan str
    | ARealSrcLoc loc1, ARealSrcLoc loc2 => ARealSrcSpan (mkRealSrcSpan loc1 loc2)
    end.

Definition srcSpanEndCol : RealSrcSpan -> GHC.Num.Int :=
  fun arg_0__ => let 'RealSrcSpan' _ _ _ _ c := arg_0__ in c.

Definition srcSpanEndLine : RealSrcSpan -> GHC.Num.Int :=
  fun arg_0__ => let 'RealSrcSpan' _ _ _ l _ := arg_0__ in l.

Definition realSrcSpanEnd : RealSrcSpan -> RealSrcLoc :=
  fun s => mkRealSrcLoc (srcSpanFile s) (srcSpanEndLine s) (srcSpanEndCol s).

Definition srcSpanEnd : SrcSpan -> SrcLoc :=
  fun arg_0__ =>
    match arg_0__ with
    | UnhelpfulSpan str => UnhelpfulLoc str
    | ARealSrcSpan s => ARealSrcLoc (realSrcSpanEnd s)
    end.

Definition srcSpanFileName_maybe : SrcSpan -> option FastString.FastString :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan s => Some (srcSpanFile s)
    | UnhelpfulSpan _ => None
    end.

Definition srcSpanStartCol : RealSrcSpan -> GHC.Num.Int :=
  fun arg_0__ => let 'RealSrcSpan' _ _ l _ _ := arg_0__ in l.

Definition srcSpanStartLine : RealSrcSpan -> GHC.Num.Int :=
  fun arg_0__ => let 'RealSrcSpan' _ l _ _ _ := arg_0__ in l.

Definition realSrcSpanStart : RealSrcSpan -> RealSrcLoc :=
  fun s => mkRealSrcLoc (srcSpanFile s) (srcSpanStartLine s) (srcSpanStartCol s).

Definition srcSpanFirstCharacter : SrcSpan -> SrcSpan :=
  fun arg_0__ =>
    match arg_0__ with
    | (UnhelpfulSpan _ as l) => l
    | ARealSrcSpan span =>
        let '(ASrcLoc f l c as loc1) := realSrcSpanStart span in
        let loc2 := ASrcLoc f l (c GHC.Num.+ #1) in
        ARealSrcSpan (mkRealSrcSpan loc1 loc2)
    end.

Definition srcSpanStart : SrcSpan -> SrcLoc :=
  fun arg_0__ =>
    match arg_0__ with
    | UnhelpfulSpan str => UnhelpfulLoc str
    | ARealSrcSpan s => ARealSrcLoc (realSrcSpanStart s)
    end.

Definition leftmost_largest : SrcSpan -> SrcSpan -> comparison :=
  fun a b =>
    Util.thenCmp (GHC.Base.compare (srcSpanStart a) (srcSpanStart b))
                 (GHC.Base.compare (srcSpanEnd b) (srcSpanEnd a)).

Definition isSubspanOf : SrcSpan -> SrcSpan -> bool :=
  fun src parent =>
    if srcSpanFileName_maybe parent GHC.Base./= srcSpanFileName_maybe src : bool
    then false else
    andb (srcSpanStart parent GHC.Base.<= srcSpanStart src) (srcSpanEnd parent
          GHC.Base.>=
          srcSpanEnd src).

Local Definition Ord__RealSrcSpan_compare
   : RealSrcSpan -> RealSrcSpan -> comparison :=
  fun a b =>
    Util.thenCmp (GHC.Base.compare (realSrcSpanStart a) (realSrcSpanStart b))
                 (GHC.Base.compare (realSrcSpanEnd a) (realSrcSpanEnd b)).

Local Definition Ord__RealSrcSpan_op_zg__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base.== Gt.

Local Definition Ord__RealSrcSpan_op_zgze__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base./= Lt.

Local Definition Ord__RealSrcSpan_op_zl__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base.== Lt.

Local Definition Ord__RealSrcSpan_op_zlze__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base./= Gt.

Local Definition Ord__RealSrcSpan_max
   : RealSrcSpan -> RealSrcSpan -> RealSrcSpan :=
  fun x y => if Ord__RealSrcSpan_op_zlze__ x y : bool then y else x.

Local Definition Ord__RealSrcSpan_min
   : RealSrcSpan -> RealSrcSpan -> RealSrcSpan :=
  fun x y => if Ord__RealSrcSpan_op_zlze__ x y : bool then x else y.

Program Instance Ord__RealSrcSpan : GHC.Base.Ord RealSrcSpan :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__RealSrcSpan_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__RealSrcSpan_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__RealSrcSpan_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__RealSrcSpan_op_zgze__ ;
         GHC.Base.compare__ := Ord__RealSrcSpan_compare ;
         GHC.Base.max__ := Ord__RealSrcSpan_max ;
         GHC.Base.min__ := Ord__RealSrcSpan_min |}.

Local Definition Ord__SrcSpan_op_zlze__ : SrcSpan -> SrcSpan -> bool :=
  fun a b => negb (Ord__SrcSpan_op_zl__ b a).

Local Definition Ord__SrcSpan_op_zl__ : SrcSpan -> SrcSpan -> bool :=
  fun a b =>
    match a with
    | ARealSrcSpan a1 =>
        match b with
        | ARealSrcSpan b1 => (a1 GHC.Base.< b1)
        | _ => true
        end
    | UnhelpfulSpan a1 =>
        match b with
        | UnhelpfulSpan b1 => (a1 GHC.Base.< b1)
        | _ => false
        end
    end.

Local Definition Ord__SrcSpan_op_zgze__ : SrcSpan -> SrcSpan -> bool :=
  fun a b => negb (Ord__SrcSpan_op_zl__ a b).

Local Definition Ord__SrcSpan_op_zg__ : SrcSpan -> SrcSpan -> bool :=
  fun a b => Ord__SrcSpan_op_zl__ b a.

Local Definition Ord__SrcSpan_compare : SrcSpan -> SrcSpan -> comparison :=
  fun a b =>
    match a with
    | ARealSrcSpan a1 =>
        match b with
        | ARealSrcSpan b1 => (GHC.Base.compare a1 b1)
        | _ => Lt
        end
    | UnhelpfulSpan a1 =>
        match b with
        | UnhelpfulSpan b1 => (GHC.Base.compare a1 b1)
        | _ => Gt
        end
    end.

Local Definition Ord__SrcSpan_min : SrcSpan -> SrcSpan -> SrcSpan :=
  fun x y => if Ord__SrcSpan_op_zlze__ x y : bool then x else y.

Local Definition Ord__SrcSpan_max : SrcSpan -> SrcSpan -> SrcSpan :=
  fun x y => if Ord__SrcSpan_op_zlze__ x y : bool then y else x.

Program Instance Ord__SrcSpan : GHC.Base.Ord SrcSpan :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__SrcSpan_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__SrcSpan_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__SrcSpan_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__SrcSpan_op_zgze__ ;
         GHC.Base.compare__ := Ord__SrcSpan_compare ;
         GHC.Base.max__ := Ord__SrcSpan_max ;
         GHC.Base.min__ := Ord__SrcSpan_min |}.

Definition rightmost : SrcSpan -> SrcSpan -> comparison :=
  GHC.Base.flip GHC.Base.compare.

Definition leftmost_smallest : SrcSpan -> SrcSpan -> comparison :=
  GHC.Base.compare.

Definition isOneLineSpan : SrcSpan -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan s => srcSpanStartLine s GHC.Base.== srcSpanEndLine s
    | UnhelpfulSpan _ => false
    end.

Definition unLoc {l} {e} : GenLocated l e -> e :=
  fun arg_0__ => let 'L _ e := arg_0__ in e.

Definition eqLocated {a} `{GHC.Base.Eq_ a} : Located a -> Located a -> bool :=
  fun a b => unLoc a GHC.Base.== unLoc b.

Definition cmpLocated {a} `{GHC.Base.Ord a}
   : Located a -> Located a -> comparison :=
  fun a b => GHC.Base.compare (unLoc a) (unLoc b).

Definition wiredInSrcSpan : SrcSpan :=
  UnhelpfulSpan (FastString.fsLit (GHC.Base.hs_string__ "<wired into compiler>")).

(* Unbound variables:
     Eq Gt Lt None Ord__SrcSpan_op_zl__ Some Type andb bool comparison false list
     negb option true Coq.Program.Basics.compose Data.Foldable.Foldable
     Data.Semigroup.Internal.Mk_Any Data.Semigroup.Internal.Mk_Dual
     Data.Semigroup.Internal.Mk_Endo Data.Semigroup.Internal.Mk_Product
     Data.Semigroup.Internal.Mk_Sum Data.Semigroup.Internal.appEndo
     Data.Semigroup.Internal.getAny Data.Semigroup.Internal.getDual
     Data.Semigroup.Internal.getProduct Data.Semigroup.Internal.getSum
     Data.Traversable.Traversable FastString.FastString FastString.fsLit
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.String GHC.Base.build GHC.Base.compare
     GHC.Base.flip GHC.Base.fmap GHC.Base.id GHC.Base.op_zdzn__ GHC.Base.op_zeze__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ Util.thenCmp
*)
