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
Require Data.Maybe.
Require Data.Monoid.
Require Data.OldList.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require MonadUtils.
Require SrcLoc.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive LBooleanFormula__raw : Type :=.

Reserved Notation "'LBooleanFormula'".

Inductive BooleanFormula a : Type := Var : a -> BooleanFormula a
                                  |  And : list (LBooleanFormula a) -> BooleanFormula a
                                  |  Or : list (LBooleanFormula a) -> BooleanFormula a
                                  |  Parens : (LBooleanFormula a) -> BooleanFormula a
where "'LBooleanFormula'" := (GHC.Base.Synonym LBooleanFormula__raw (fun a_ =>
                                                 (SrcLoc.Located (BooleanFormula a_))%type)).

Arguments Var {_} _.

Arguments And {_} _.

Arguments Or {_} _.

Arguments Parens {_} _.
(* Midamble *)

Local Fixpoint size {a} (bf: BooleanFormula a) : nat :=
  match bf with
    | Var a => 0
    | And xs => Coq.Lists.List.fold_right Nat.add 0 (Coq.Lists.List.map
        (fun lbf => match lbf with SrcLoc.L _ f => S (size f) end) xs)
    | Or xs => Coq.Lists.List.fold_right Nat.add 0 (Coq.Lists.List.map
        (fun lbf => match lbf with SrcLoc.L _ f => S (size f) end) xs)
    | Parens (SrcLoc.L _ bf) => S (size bf)
  end.

Fixpoint BooleanFormula_eq {a} `{GHC.Base.Eq_ a} (bf1 : BooleanFormula a) (bf2 : BooleanFormula a) : bool :=
  let eq' : GHC.Base.Eq_ (BooleanFormula a) := GHC.Base.eq_default BooleanFormula_eq in
    match bf1 , bf2 with
      | Var a1 , Var b1 => GHC.Base.op_zeze__ a1 b1
      | And a1 , And b1 => GHC.Base.op_zeze__ a1 b1
      | Or a1 , Or b1 => GHC.Base.op_zeze__ a1 b1
      | Parens a1 , Parens b1 => GHC.Base.op_zeze__  a1 b1
      | _ , _ => false
    end.

Instance Eq_BooleanFormula {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (BooleanFormula a) :=
  GHC.Base.eq_default BooleanFormula_eq.

(* We can fmap below once we cont'ified the Functor type class *)
Local Definition BooleanFormula_fmap
   : forall {a} {b}, (a -> b) -> BooleanFormula a -> BooleanFormula b :=
  fun {a} {b} => fix BooleanFormula_fmap arg_114__ arg_115__ :=
      match arg_114__ , arg_115__ with
        | f , Var a1 => Var (f a1)
        | f , And a1 => And (GHC.Base.fmap (GHC.Base.fmap (BooleanFormula_fmap f)) a1)
        | f , Or a1 => Or (GHC.Base.fmap (GHC.Base.fmap (BooleanFormula_fmap f)) a1)
        | f , Parens a1 => Parens (GHC.Base.fmap (BooleanFormula_fmap f) a1)
      end.

Local Definition BooleanFormula_traverse
    : forall {f} {a} {b},   forall `{GHC.Base.Applicative f}, (a -> f b) -> BooleanFormula a -> f (BooleanFormula b) :=
  fun {f0} {a} {b} `{GHC.Base.Applicative f0} => fix BooleanFormula_traverse arg_144__ arg_145__ :=
      match arg_144__ , arg_145__ with
        | f , Var a1 => GHC.Base.fmap  Var (f a1)
        | f , And a1 => GHC.Base.fmap And (Data.Traversable.traverse (Data.Traversable.traverse
                                                                           (BooleanFormula_traverse f)) a1)
        | f , Or a1 => GHC.Base.fmap Or
                        (@Data.Traversable.traverse _ _ _ _ f0 _ _ _ _ (Data.Traversable.traverse
                                                                          (BooleanFormula_traverse f)) a1)
        | f , Parens a1 => GHC.Base.fmap Parens
                             (@Data.Traversable.traverse _ _ _ _ f0 _ _ _ _  (BooleanFormula_traverse f) a1)
      end.

Local Definition BooleanFormula_foldMap
    : forall {m} {a},
        forall `{GHC.Base.Monoid m}, (a -> m) -> BooleanFormula a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => fix foldMap arg_137__ arg_138__ :=
      match arg_137__ , arg_138__ with
        | f , Var a1 => f a1
        | f , And a1 => Data.Foldable.foldMap (Data.Foldable.foldMap
                                                 (foldMap f)) a1
        | f , Or a1 => Data.Foldable.foldMap (Data.Foldable.foldMap
                                                (foldMap f)) a1
        | f , Parens a1 => Data.Foldable.foldMap (foldMap f) a1
      end.

Local Definition BooleanFormula_foldr
    : forall {a} {b}, (a -> b -> b) -> b -> BooleanFormula a -> b :=
  fun {a} {b} => fix foldr arg_97__ arg_98__ arg_99__ :=
      match arg_97__ , arg_98__ , arg_99__ with
        | f , z , Var a1 => f a1 z
        | f , z , And a1 => (fun arg_101__ arg_102__ =>
                                 match arg_101__ , arg_102__ with
                                   | b5 , b6 => Data.Foldable.foldr (fun arg_103__ arg_104__ =>
                                                                      match arg_103__ , arg_104__ with
                                                                        | b3 , b4 => Data.Foldable.foldr (fun arg_105__
                                                                                                              arg_106__ =>
                                                                                                           match arg_105__
                                                                                                               , arg_106__ with
                                                                                                             | b1 ,
                                                                                                               b2 =>
                                                                                                               foldr
                                                                                                               f b2 b1
                                                                                                           end) b4 b3
                                                                      end) b6 b5
                                 end) a1 z
        | f , z , Or a1 => (fun arg_114__ arg_115__ =>
                                match arg_114__ , arg_115__ with
                                  | b5 , b6 => Data.Foldable.foldr (fun arg_116__ arg_117__ =>
                                                                     match arg_116__ , arg_117__ with
                                                                       | b3 , b4 => Data.Foldable.foldr (fun arg_118__
                                                                                                             arg_119__ =>
                                                                                                          match arg_118__
                                                                                                              , arg_119__ with
                                                                                                            | b1 , b2 =>
                                                                                                              foldr
                                                                                                              f b2 b1
                                                                                                          end) b4 b3
                                                                     end) b6 b5
                                end) a1 z
        | f , z , Parens a1 => (fun arg_127__ arg_128__ =>
                                    match arg_127__ , arg_128__ with
                                      | b3 , b4 => Data.Foldable.foldr (fun arg_129__ arg_130__ =>
                                                                         match arg_129__ , arg_130__ with
                                                                           | b1 , b2 => foldr f b2 b1
                                                                         end) b4 b3
                                    end) a1 z
      end.

(* Converted value declarations: *)

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (BooleanFormula.BooleanFormula a)' failed: OOPS! Cannot
   find information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance forall {a}, forall `{Binary.Binary a}, Binary.Binary
   (BooleanFormula.BooleanFormula a)' failed: OOPS! Cannot find information for
   class Qualified "Binary" "Binary" unsupported *)

Local Definition Traversable__BooleanFormula_traverse {f} {a} {b} `{_
                                                        : GHC.Base.Applicative f} : (a -> f b) -> BooleanFormula a -> f
                                                                                    (BooleanFormula b) :=
  BooleanFormula_traverse.

Local Definition Traversable__BooleanFormula_sequenceA : forall {f} {a},
                                                           forall `{GHC.Base.Applicative f},
                                                             BooleanFormula (f a) -> f (BooleanFormula a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__BooleanFormula_traverse GHC.Base.id.

Local Definition Traversable__BooleanFormula_sequence : forall {m} {a},
                                                          forall `{GHC.Base.Monad m},
                                                            BooleanFormula (m a) -> m (BooleanFormula a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__BooleanFormula_sequenceA.

Local Definition Traversable__BooleanFormula_mapM : forall {m} {a} {b},
                                                      forall `{GHC.Base.Monad m},
                                                        (a -> m b) -> BooleanFormula a -> m (BooleanFormula b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__BooleanFormula_traverse.

Local Definition Foldable__BooleanFormula_foldMap {m} {a} `{_ : GHC.Base.Monoid
                                                                m} : (a -> m) -> BooleanFormula a -> m :=
  BooleanFormula_foldMap.

Local Definition Foldable__BooleanFormula_foldl : forall {b} {a},
                                                    (b -> a -> b) -> b -> BooleanFormula a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => Data.Monoid.appEndo (Data.Monoid.getDual
                                           (Foldable__BooleanFormula_foldMap (Coq.Program.Basics.compose
                                                                             Data.Monoid.Mk_Dual
                                                                             (Coq.Program.Basics.compose
                                                                             Data.Monoid.Mk_Endo (GHC.Base.flip f))) t))
                       z
      end.

Local Definition Foldable__BooleanFormula_foldr' : forall {a} {b},
                                                     (a -> b -> b) -> b -> BooleanFormula a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__BooleanFormula_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__BooleanFormula_product : forall {a},
                                                      forall `{GHC.Num.Num a}, BooleanFormula a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct
                               (Foldable__BooleanFormula_foldMap Data.Monoid.Mk_Product).

Local Definition Foldable__BooleanFormula_sum : forall {a},
                                                  forall `{GHC.Num.Num a}, BooleanFormula a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__BooleanFormula_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__BooleanFormula_fold : forall {m},
                                                   forall `{GHC.Base.Monoid m}, BooleanFormula m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__BooleanFormula_foldMap GHC.Base.id.

Local Definition Foldable__BooleanFormula_elem : forall {a},
                                                   forall `{GHC.Base.Eq_ a}, a -> BooleanFormula a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny
                                                                     (Foldable__BooleanFormula_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Local Definition Foldable__BooleanFormula_foldr {a} {b}
    : (a -> b -> b) -> b -> BooleanFormula a -> b :=
  BooleanFormula_foldr.

Local Definition Foldable__BooleanFormula_null : forall {a},
                                                   BooleanFormula a -> bool :=
  fun {a} => Foldable__BooleanFormula_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__BooleanFormula_toList : forall {a},
                                                     BooleanFormula a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__BooleanFormula_foldr c n t
                                end)
      end.

Local Definition Foldable__BooleanFormula_foldl' : forall {b} {a},
                                                     (b -> a -> b) -> b -> BooleanFormula a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__BooleanFormula_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__BooleanFormula_length : forall {a},
                                                     BooleanFormula a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__BooleanFormula_foldl' (fun arg_64__ arg_65__ =>
                                      match arg_64__ , arg_65__ with
                                        | c , _ => _GHC.Num.+_ c (GHC.Num.fromInteger 1)
                                      end) (GHC.Num.fromInteger 0).

Program Instance Foldable__BooleanFormula : Data.Foldable.Foldable
                                            BooleanFormula := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
        Foldable__BooleanFormula_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
        Foldable__BooleanFormula_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__BooleanFormula_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__BooleanFormula_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__BooleanFormula_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__BooleanFormula_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__BooleanFormula_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__BooleanFormula_length ;
      Data.Foldable.null__ := fun {a} => Foldable__BooleanFormula_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
        Foldable__BooleanFormula_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} =>
        Foldable__BooleanFormula_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__BooleanFormula_toList |}.
Admit Obligations.

Local Definition Functor__BooleanFormula_fmap {a} {b}
    : (a -> b) -> BooleanFormula a -> BooleanFormula b :=
  BooleanFormula_fmap.

Local Definition Functor__BooleanFormula_op_zlzd__ : forall {a} {b},
                                                       a -> BooleanFormula b -> BooleanFormula a :=
  fun {a} {b} => fun x => Functor__BooleanFormula_fmap (GHC.Base.const x).

Program Instance Functor__BooleanFormula : GHC.Base.Functor BooleanFormula :=
  fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__BooleanFormula_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__BooleanFormula_fmap |}.
Admit Obligations.

Program Instance Traversable__BooleanFormula : Data.Traversable.Traversable
                                               BooleanFormula := fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__BooleanFormula_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__BooleanFormula_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__BooleanFormula_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__BooleanFormula_traverse |}.
Admit Obligations.

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (BooleanFormula.BooleanFormula a)' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___BooleanFormula_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
    : BooleanFormula inst_a -> BooleanFormula inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Var a1 , Var b1 => ((a1 GHC.Base.== b1))
      | And a1 , And b1 => ((a1 GHC.Base.== b1))
      | Or a1 , Or b1 => ((a1 GHC.Base.== b1))
      | Parens a1 , Parens b1 => ((a1 GHC.Base.== b1))
      | _ , _ => false
    end.

Local Definition Eq___BooleanFormula_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
    : BooleanFormula inst_a -> BooleanFormula inst_a -> bool :=
  fun a b => negb (Eq___BooleanFormula_op_zeze__ a b).

Program Instance Eq___BooleanFormula {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_
                                                             (BooleanFormula a) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___BooleanFormula_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___BooleanFormula_op_zsze__ |}.
Admit Obligations.

Definition eval {a} : (a -> bool) -> BooleanFormula a -> bool :=
  fix eval arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | f , Var x => f x
             | f , And xs => Data.Foldable.all (eval f GHC.Base.∘ SrcLoc.unLoc) xs
             | f , Or xs => Data.Foldable.any (eval f GHC.Base.∘ SrcLoc.unLoc) xs
             | f , Parens x => eval f (SrcLoc.unLoc x)
           end.

Definition impliesAtom {a} `{GHC.Base.Eq_ a} : BooleanFormula a -> a -> bool :=
  fix impliesAtom arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | Var x , y => x GHC.Base.== y
             | And xs , y => Data.Foldable.any (fun x => impliesAtom (SrcLoc.unLoc x) y) xs
             | Or xs , y => Data.Foldable.all (fun x => impliesAtom (SrcLoc.unLoc x) y) xs
             | Parens x , y => impliesAtom (SrcLoc.unLoc x) y
           end.

Definition implies {a} `{GHC.Base.Eq_ a} : BooleanFormula a -> BooleanFormula
                                           a -> bool :=
  fix implies arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | x , Var y => impliesAtom x y
             | x , And ys => Data.Foldable.all (implies x GHC.Base.∘ SrcLoc.unLoc) ys
             | x , Or ys => Data.Foldable.any (implies x GHC.Base.∘ SrcLoc.unLoc) ys
             | x , Parens y => implies x (SrcLoc.unLoc y)
           end.

Definition isFalse {a} : BooleanFormula a -> bool :=
  fun arg_0__ => match arg_0__ with | Or nil => true | _ => false end.

Definition isTrue {a} : BooleanFormula a -> bool :=
  fun arg_0__ => match arg_0__ with | And nil => true | _ => false end.

Definition mkFalse {a} : BooleanFormula a :=
  Or nil.

Definition mkAnd {a} `{GHC.Base.Eq_ a} : list (LBooleanFormula
                                              a) -> BooleanFormula a :=
  let mkAnd' :=
    fun arg_0__ =>
      match arg_0__ with
        | cons x nil => SrcLoc.unLoc x
        | xs => And xs
      end in
  let fromAnd {a} : LBooleanFormula a -> option (list (LBooleanFormula a)) :=
    fun arg_4__ =>
      match arg_4__ with
        | SrcLoc.L _ (And xs) => Some xs
        | SrcLoc.L _ (Or nil) => None
        | x => Some (cons x nil)
      end in
  Data.Maybe.maybe mkFalse (mkAnd' GHC.Base.∘ Data.OldList.nub) GHC.Base.∘
  MonadUtils.concatMapM fromAnd.

Definition mkTrue {a} : BooleanFormula a :=
  And nil.

Definition mkOr {a} `{GHC.Base.Eq_ a} : list (LBooleanFormula
                                             a) -> BooleanFormula a :=
  let mkOr' :=
    fun arg_0__ =>
      match arg_0__ with
        | cons x nil => SrcLoc.unLoc x
        | xs => Or xs
      end in
  let fromOr :=
    fun arg_4__ =>
      match arg_4__ with
        | SrcLoc.L _ (Or xs) => Some xs
        | SrcLoc.L _ (And nil) => None
        | x => Some (cons x nil)
      end in
  Data.Maybe.maybe mkTrue (mkOr' GHC.Base.∘ Data.OldList.nub) GHC.Base.∘
  MonadUtils.concatMapM fromOr.

Definition mkBool {a} : bool -> BooleanFormula a :=
  fun arg_0__ => match arg_0__ with | false => mkFalse | true => mkTrue end.

Definition simplify {a} `{GHC.Base.Eq_ a} : (a -> option bool) -> BooleanFormula
                                            a -> BooleanFormula a :=
  fix simplify arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | f , Var a => match f a with
                              | None => Var a
                              | Some b => mkBool b
                            end
             | f , And xs => mkAnd (GHC.Base.map (fun arg_7__ =>
                                                   match arg_7__ with
                                                     | SrcLoc.L l x => SrcLoc.L l (simplify f x)
                                                   end) xs)
             | f , Or xs => mkOr (GHC.Base.map (fun arg_11__ =>
                                                 match arg_11__ with
                                                   | SrcLoc.L l x => SrcLoc.L l (simplify f x)
                                                 end) xs)
             | f , Parens x => simplify f (SrcLoc.unLoc x)
           end.

Definition isUnsatisfied {a} `{GHC.Base.Eq_ a} : (a -> bool) -> BooleanFormula
                                                 a -> option (BooleanFormula a) :=
  fun f bf =>
    let f' := fun x => if f x : bool then Some true else None in
    let bf' := simplify f' bf in if isTrue bf' : bool then None else Some bf'.

Definition mkVar {a} : a -> BooleanFormula a :=
  Var.

(* Unbound variables:
     BooleanFormula_fmap BooleanFormula_foldMap BooleanFormula_foldr
     BooleanFormula_traverse LBooleanFormula None Some bool cons false list negb nil
     option true Coq.Program.Basics.compose Data.Foldable.Foldable Data.Foldable.all
     Data.Foldable.any Data.Foldable.hash_compose Data.Maybe.maybe Data.Monoid.Mk_Any
     Data.Monoid.Mk_Dual Data.Monoid.Mk_Endo Data.Monoid.Mk_Product
     Data.Monoid.Mk_Sum Data.Monoid.appEndo Data.Monoid.getAny Data.Monoid.getDual
     Data.Monoid.getProduct Data.Monoid.getSum Data.OldList.nub
     Data.Traversable.Traversable GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Synonym GHC.Base.build GHC.Base.const
     GHC.Base.flip GHC.Base.id GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zdzn__
     GHC.Base.op_zeze__ GHC.Num.Int GHC.Num.Num GHC.Num.op_zp__ MonadUtils.concatMapM
     SrcLoc.L SrcLoc.Located SrcLoc.unLoc
*)
