(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BinNums.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.SemigroupInternal.
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
     BinNums.N -> BinNums.N -> BinNums.N -> BinNums.N -> RealSrcSpan.

Inductive SrcSpan : Type
  := ARealSrcSpan : RealSrcSpan -> SrcSpan
  |  UnhelpfulSpan : FastString.FastString -> SrcSpan.

Inductive RealSrcLoc : Type
  := ASrcLoc : FastString.FastString -> BinNums.N -> BinNums.N -> RealSrcLoc.

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

Definition srcSpanELine (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ _ _ srcSpanELine _ := arg_0__ in
  srcSpanELine.

Definition srcSpanFile (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' srcSpanFile _ _ _ _ := arg_0__ in
  srcSpanFile.

Definition srcSpanSCol (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ _ srcSpanSCol _ _ := arg_0__ in
  srcSpanSCol.

Definition srcSpanSLine (arg_0__ : RealSrcSpan) :=
  let 'RealSrcSpan' _ srcSpanSLine _ _ _ := arg_0__ in
  srcSpanSLine.
(* Midamble *)

(* Default values *)
Require Import GHC.Err.
Instance Default__SrcSpan : Default SrcSpan := Build_Default _ (UnhelpfulSpan default).

Instance Default__RealSrcSpan : Default RealSrcSpan := 
  Build_Default _ (RealSrcSpan' GHC.Err.default GHC.Err.default  GHC.Err.default  
                   GHC.Err.default GHC.Err.default).

Definition Ord__RealSrcLoc_op_zl : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b =>
    let 'ASrcLoc a1 a2 a3 := a in
    let 'ASrcLoc b1 b2 b3 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => true
    | Eq =>
        match (GHC.Base.compare a2 b2) with
        | Lt => true
        | Eq => (a3 GHC.Base.< b3)
        | Gt => false
        end
    | Gt => false
    end.

(* Converted value declarations: *)

(* Skipping instance Outputable__GenLocated of class Outputable *)

(* Skipping instance Data__SrcSpan of class Data *)

(* Skipping instance ToJson__SrcSpan of class ToJson *)

(* Skipping instance NFData__SrcSpan of class NFData *)

(* Skipping instance Outputable__SrcSpan of class Outputable *)

(* Skipping instance Data__RealSrcSpan of class Data *)

(* Skipping instance ToJson__RealSrcSpan of class ToJson *)

(* Skipping instance Show__RealSrcSpan of class Show *)

(* Skipping instance Outputable__RealSrcSpan of class Outputable *)

(* Skipping instance Outputable__SrcLoc of class Outputable *)

(* Skipping instance Outputable__RealSrcLoc of class Outputable *)

(* Skipping instance Show__RealSrcLoc of class Show *)

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

Local Definition Foldable__GenLocated_null {inst_l}
   : forall {a}, GenLocated inst_l a -> bool :=
  fun {a} => fun '(L _ _) => false.

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
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__GenLocated_foldr c n t)).

Local Definition Foldable__GenLocated_foldl' {inst_l}
   : forall {b} {a}, (b -> a -> b) -> b -> GenLocated inst_l a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__GenLocated_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__GenLocated_length {inst_l}
   : forall {a}, GenLocated inst_l a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__GenLocated_foldl' (fun arg_0__ arg_1__ =>
                                   match arg_0__, arg_1__ with
                                   | c, _ => c GHC.Num.+ #1
                                   end) #0.

Local Definition Foldable__GenLocated_foldMap {inst_l}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> GenLocated inst_l a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, L a1 a2 => f a2 end.

Local Definition Foldable__GenLocated_foldl {inst_l}
   : forall {b} {a}, (b -> a -> b) -> b -> GenLocated inst_l a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__GenLocated_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                     (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                      GHC.Base.flip f)) t)) z.

Local Definition Foldable__GenLocated_foldr' {inst_l}
   : forall {a} {b}, (a -> b -> b) -> b -> GenLocated inst_l a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__GenLocated_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__GenLocated_product {inst_l}
   : forall {a}, forall `{GHC.Num.Num a}, GenLocated inst_l a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__GenLocated_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__GenLocated_sum {inst_l}
   : forall {a}, forall `{GHC.Num.Num a}, GenLocated inst_l a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__GenLocated_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__GenLocated_fold {inst_l}
   : forall {m}, forall `{GHC.Base.Monoid m}, GenLocated inst_l m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__GenLocated_foldMap GHC.Base.id.

Local Definition Functor__GenLocated_op_zlzd__ {inst_l}
   : forall {a} {b}, a -> GenLocated inst_l b -> GenLocated inst_l a :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | z, L a1 a2 => L ((fun b1 => b1) a1) ((fun b2 => z) a2)
      end.

Local Definition Functor__GenLocated_fmap {inst_l}
   : forall {a} {b}, (a -> b) -> GenLocated inst_l a -> GenLocated inst_l b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, L a1 a2 => L ((fun b1 => b1) a1) (f a2)
      end.

Program Instance Functor__GenLocated {l} : GHC.Base.Functor (GenLocated l) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__GenLocated_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__GenLocated_op_zlzd__ |}.

Program Instance Foldable__GenLocated {l}
   : Data.Foldable.Foldable (GenLocated l) :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
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

(* Skipping instance Data__GenLocated of class Data *)

(* Skipping instance Ord__GenLocated *)

Local Definition Eq___GenLocated_op_zeze__ {inst_l} {inst_e} `{GHC.Base.Eq_
  inst_l} `{GHC.Base.Eq_ inst_e}
   : GenLocated inst_l inst_e -> GenLocated inst_l inst_e -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | L a1 a2, L b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___GenLocated_op_zsze__ {inst_l} {inst_e} `{GHC.Base.Eq_
  inst_l} `{GHC.Base.Eq_ inst_e}
   : GenLocated inst_l inst_e -> GenLocated inst_l inst_e -> bool :=
  fun x y => negb (Eq___GenLocated_op_zeze__ x y).

Program Instance Eq___GenLocated {l} {e} `{GHC.Base.Eq_ l} `{GHC.Base.Eq_ e}
   : GHC.Base.Eq_ (GenLocated l e) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___GenLocated_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___GenLocated_op_zsze__ |}.

(* Skipping instance Show__SrcSpan of class Show *)

(* Skipping instance Ord__SrcSpan *)

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
  fun x y => negb (Eq___RealSrcSpan_op_zeze__ x y).

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
  fun x y => negb (Eq___SrcSpan_op_zeze__ x y).

Program Instance Eq___SrcSpan : GHC.Base.Eq_ SrcSpan :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___SrcSpan_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___SrcSpan_op_zsze__ |}.

(* Skipping instance Show__SrcLoc of class Show *)

(* Skipping instance Ord__SrcLoc *)

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

Definition Ord__RealSrcLoc_op_zl__ :=
  Ord__RealSrcLoc_op_zl.

Local Definition Ord__RealSrcLoc_op_zlze__ : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b => negb (Ord__RealSrcLoc_op_zl__ b a).

Local Definition Ord__RealSrcLoc_op_zg__ : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b => Ord__RealSrcLoc_op_zl__ b a.

Local Definition Ord__RealSrcLoc_op_zgze__ : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b => negb (Ord__RealSrcLoc_op_zl__ a b).

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

Local Definition Eq___SrcLoc_op_zeze__ : SrcLoc -> SrcLoc -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ARealSrcLoc a1, ARealSrcLoc b1 => ((a1 GHC.Base.== b1))
    | UnhelpfulLoc a1, UnhelpfulLoc b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Program Instance Ord__RealSrcLoc : GHC.Base.Ord RealSrcLoc :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__RealSrcLoc_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__RealSrcLoc_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__RealSrcLoc_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__RealSrcLoc_op_zgze__ ;
         GHC.Base.compare__ := Ord__RealSrcLoc_compare ;
         GHC.Base.max__ := Ord__RealSrcLoc_max ;
         GHC.Base.min__ := Ord__RealSrcLoc_min |}.

Local Definition Eq___SrcLoc_op_zsze__ : SrcLoc -> SrcLoc -> bool :=
  fun x y => negb (Eq___SrcLoc_op_zeze__ x y).

Program Instance Eq___SrcLoc : GHC.Base.Eq_ SrcLoc :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___SrcLoc_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___SrcLoc_op_zsze__ |}.

Definition generatedSrcLoc : SrcLoc :=
  UnhelpfulLoc (FastString.fsLit (GHC.Base.hs_string__
                                  "<compiler-generated code>")).

Definition getLoc {l} {e} : GenLocated l e -> l :=
  fun '(L l _) => l.

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
  fun '(RealSrcSpan' _ line1 _ line2 _) => line1 GHC.Base.== line2.

Definition isPointRealSpan : RealSrcSpan -> bool :=
  fun '(RealSrcSpan' _ line1 col1 line2 col2) =>
    andb (line1 GHC.Base.== line2) (col1 GHC.Base.== col2).

Definition mkGeneralSrcLoc : FastString.FastString -> SrcLoc :=
  UnhelpfulLoc.

Definition mkGeneralSrcSpan : FastString.FastString -> SrcSpan :=
  UnhelpfulSpan.

Definition mkGeneralLocated {e} : GHC.Base.String -> e -> Located e :=
  fun s e => L (mkGeneralSrcSpan (FastString.fsLit s)) e.

Definition mkRealSrcLoc
   : FastString.FastString -> BinNums.N -> BinNums.N -> RealSrcLoc :=
  fun x line col => ASrcLoc x line col.

Definition mkSrcLoc
   : FastString.FastString -> BinNums.N -> BinNums.N -> SrcLoc :=
  fun x line col => ARealSrcLoc (mkRealSrcLoc x line col).

Definition noSrcLoc : SrcLoc :=
  UnhelpfulLoc (FastString.fsLit (GHC.Base.hs_string__ "<no location info>")).

Definition noSrcSpan : SrcSpan :=
  UnhelpfulSpan (FastString.fsLit (GHC.Base.hs_string__ "<no location info>")).

Definition noLoc {e} : e -> Located e :=
  fun e => L noSrcSpan e.

Definition realSrcLocSpan : RealSrcLoc -> RealSrcSpan :=
  fun '(ASrcLoc file line col) => RealSrcSpan' file line col line col.

Definition srcLocSpan : SrcLoc -> SrcSpan :=
  fun arg_0__ =>
    match arg_0__ with
    | UnhelpfulLoc str => UnhelpfulSpan str
    | ARealSrcLoc l => ARealSrcSpan (realSrcLocSpan l)
    end.

Definition srcLocCol : RealSrcLoc -> BinNums.N :=
  fun '(ASrcLoc _ _ c) => c.

Definition srcLocFile : RealSrcLoc -> FastString.FastString :=
  fun '(ASrcLoc fname _ _) => fname.

Definition srcLocLine : RealSrcLoc -> BinNums.N :=
  fun '(ASrcLoc _ l _) => l.

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

Definition srcSpanEndCol : RealSrcSpan -> BinNums.N :=
  fun '(RealSrcSpan' _ _ _ _ c) => c.

Definition srcSpanEndLine : RealSrcSpan -> BinNums.N :=
  fun '(RealSrcSpan' _ _ _ l _) => l.

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

Definition srcSpanStartCol : RealSrcSpan -> BinNums.N :=
  fun '(RealSrcSpan' _ _ l _ _) => l.

Definition srcSpanStartLine : RealSrcSpan -> BinNums.N :=
  fun '(RealSrcSpan' _ l _ _ _) => l.

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

Local Definition Ord__RealSrcSpan_compare
   : RealSrcSpan -> RealSrcSpan -> comparison :=
  fun a b =>
    Util.thenCmp (GHC.Base.compare (realSrcSpanStart a) (realSrcSpanStart b))
                 (GHC.Base.compare (realSrcSpanEnd a) (realSrcSpanEnd b)).

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

Local Definition Ord__RealSrcSpan_op_zg__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base.== Gt.

Local Definition Ord__RealSrcSpan_op_zgze__
   : RealSrcSpan -> RealSrcSpan -> bool :=
  fun x y => Ord__RealSrcSpan_compare x y GHC.Base./= Lt.

Program Instance Ord__RealSrcSpan : GHC.Base.Ord RealSrcSpan :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__RealSrcSpan_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__RealSrcSpan_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__RealSrcSpan_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__RealSrcSpan_op_zgze__ ;
         GHC.Base.compare__ := Ord__RealSrcSpan_compare ;
         GHC.Base.max__ := Ord__RealSrcSpan_max ;
         GHC.Base.min__ := Ord__RealSrcSpan_min |}.

Definition isOneLineSpan : SrcSpan -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | ARealSrcSpan s => srcSpanStartLine s GHC.Base.== srcSpanEndLine s
    | UnhelpfulSpan _ => false
    end.

Definition unLoc {l} {e} : GenLocated l e -> e :=
  fun '(L _ e) => e.

Definition eqLocated {a} `{GHC.Base.Eq_ a} : Located a -> Located a -> bool :=
  fun a b => unLoc a GHC.Base.== unLoc b.

Definition cmpLocated {a} `{GHC.Base.Ord a}
   : Located a -> Located a -> comparison :=
  fun a b => GHC.Base.compare (unLoc a) (unLoc b).

Definition wiredInSrcSpan : SrcSpan :=
  UnhelpfulSpan (FastString.fsLit (GHC.Base.hs_string__ "<wired into compiler>")).

(* External variables:
     Eq Gt Lt None Ord__RealSrcLoc_op_zl Some andb bool comparison false list negb
     option true BinNums.N Coq.Program.Basics.compose Data.Foldable.Foldable
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr'__ Data.Foldable.foldr__
     Data.Foldable.length__ Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ FastString.FastString FastString.fsLit
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.String GHC.Base.build' GHC.Base.compare
     GHC.Base.compare__ GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zl____
     GHC.Base.op_zlzd____ GHC.Base.op_zlze____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
     Util.thenCmp
*)
