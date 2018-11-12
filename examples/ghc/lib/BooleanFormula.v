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
Require Data.Maybe.
Require Data.OldList.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Num.
Require MonadUtils.
Require SrcLoc.
Require UniqSet.
Require Unique.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive LBooleanFormula__raw : Type :=.

Reserved Notation "'LBooleanFormula'".

Inductive BooleanFormula a : Type
  := Var : a -> BooleanFormula a
  |  And : list (LBooleanFormula a) -> BooleanFormula a
  |  Or : list (LBooleanFormula a) -> BooleanFormula a
  |  Parens : (LBooleanFormula a) -> BooleanFormula a
where "'LBooleanFormula'" := (GHC.Base.Synonym LBooleanFormula__raw (fun a_ =>
                                                  (SrcLoc.Located (BooleanFormula a_))%type)).

Inductive Clause a : Type
  := Mk_Clause (clauseAtoms : UniqSet.UniqSet a) (clauseExprs
    : list (BooleanFormula a))
   : Clause a.

Arguments Var {_} _.

Arguments And {_} _.

Arguments Or {_} _.

Arguments Parens {_} _.

Arguments Mk_Clause {_} _ _.

Definition clauseAtoms {a} (arg_0__ : Clause a) :=
  let 'Mk_Clause clauseAtoms _ := arg_0__ in
  clauseAtoms.

Definition clauseExprs {a} (arg_0__ : Clause a) :=
  let 'Mk_Clause _ clauseExprs := arg_0__ in
  clauseExprs.

(* Midamble *)

Import GHC.Err.
Instance Default_BooleanFormula {a} : Err.Default (BooleanFormula a) :=
  Err.Build_Default _ (And nil).

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

Definition mkVar {a} : a -> BooleanFormula a :=
  Var.

Definition mkTrue {a} : BooleanFormula a :=
  And nil.

Definition mkOr {a} `{GHC.Base.Eq_ a}
   : list (LBooleanFormula a) -> BooleanFormula a :=
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

Definition mkFalse {a} : BooleanFormula a :=
  Or nil.

Definition mkBool {a} : bool -> BooleanFormula a :=
  fun arg_0__ => match arg_0__ with | false => mkFalse | true => mkTrue end.

Definition mkAnd {a} `{GHC.Base.Eq_ a}
   : list (LBooleanFormula a) -> BooleanFormula a :=
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

Definition simplify {a} `{GHC.Base.Eq_ a}
   : (a -> option bool) -> BooleanFormula a -> BooleanFormula a :=
  fix simplify arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | f, Var a => match f a with | None => Var a | Some b => mkBool b end
           | f, And xs =>
               mkAnd (GHC.Base.map (fun '(SrcLoc.L l x) => SrcLoc.L l (simplify f x)) xs)
           | f, Or xs =>
               mkOr (GHC.Base.map (fun '(SrcLoc.L l x) => SrcLoc.L l (simplify f x)) xs)
           | f, Parens x => simplify f (SrcLoc.unLoc x)
           end.

Definition memberClauseAtoms {a} `{Unique.Uniquable a}
   : a -> Clause a -> bool :=
  fun x c => UniqSet.elementOfUniqSet x (clauseAtoms c).

Definition isTrue {a} : BooleanFormula a -> bool :=
  fun arg_0__ => match arg_0__ with | And nil => true | _ => false end.

Definition isUnsatisfied {a} `{GHC.Base.Eq_ a}
   : (a -> bool) -> BooleanFormula a -> option (BooleanFormula a) :=
  fun f bf =>
    let f' := fun x => if f x : bool then Some true else None in
    let bf' := simplify f' bf in if isTrue bf' : bool then None else Some bf'.

Definition isFalse {a} : BooleanFormula a -> bool :=
  fun arg_0__ => match arg_0__ with | Or nil => true | _ => false end.

Definition impliesAtom {a} `{GHC.Base.Eq_ a} : BooleanFormula a -> a -> bool :=
  fix impliesAtom arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | Var x, y => x GHC.Base.== y
           | And xs, y => Data.Foldable.any (fun x => impliesAtom (SrcLoc.unLoc x) y) xs
           | Or xs, y => Data.Foldable.all (fun x => impliesAtom (SrcLoc.unLoc x) y) xs
           | Parens x, y => impliesAtom (SrcLoc.unLoc x) y
           end.

Definition extendClauseAtoms {a} `{Unique.Uniquable a}
   : Clause a -> a -> Clause a :=
  fun c x =>
    let 'Mk_Clause clauseAtoms_0__ clauseExprs_1__ := c in
    Mk_Clause (UniqSet.addOneToUniqSet (clauseAtoms c) x) clauseExprs_1__.

Definition implies {a} `{Unique.Uniquable a}
   : BooleanFormula a -> BooleanFormula a -> bool :=
  fun e1 e2 =>
    let go {a} `{Unique.Uniquable a} : Clause a -> Clause a -> bool :=
      GHC.DeferredFix.deferredFix2 (fun go arg_0__ arg_1__ =>
                                      match arg_0__, arg_1__ with
                                      | (Mk_Clause _ (cons hyp hyps) as l), r =>
                                          match hyp with
                                          | Var x =>
                                              if memberClauseAtoms x r : bool then true else
                                              go (let 'Mk_Clause clauseAtoms_2__ clauseExprs_3__ := (extendClauseAtoms l
                                                                                                       x) in
                                                  Mk_Clause clauseAtoms_2__ hyps) r
                                          | Parens hyp' =>
                                              go (let 'Mk_Clause clauseAtoms_9__ clauseExprs_10__ := l in
                                                  Mk_Clause clauseAtoms_9__ (cons (SrcLoc.unLoc hyp') hyps)) r
                                          | And hyps' =>
                                              go (let 'Mk_Clause clauseAtoms_14__ clauseExprs_15__ := l in
                                                  Mk_Clause clauseAtoms_14__ (Coq.Init.Datatypes.app (GHC.Base.map
                                                                                                      SrcLoc.unLoc
                                                                                                      hyps') hyps)) r
                                          | Or hyps' =>
                                              Data.Foldable.all (fun hyp' =>
                                                                   go (let 'Mk_Clause clauseAtoms_19__
                                                                          clauseExprs_20__ := l in
                                                                       Mk_Clause clauseAtoms_19__ (cons (SrcLoc.unLoc
                                                                                                         hyp') hyps)) r)
                                              hyps'
                                          end
                                      | l, (Mk_Clause _ (cons con cons_) as r) =>
                                          match con with
                                          | Var x =>
                                              if memberClauseAtoms x l : bool then true else
                                              go l (let 'Mk_Clause clauseAtoms_27__ clauseExprs_28__ :=
                                                      (extendClauseAtoms r x) in
                                                    Mk_Clause clauseAtoms_27__ cons_)
                                          | Parens con' =>
                                              go l (let 'Mk_Clause clauseAtoms_34__ clauseExprs_35__ := r in
                                                    Mk_Clause clauseAtoms_34__ (cons (SrcLoc.unLoc con') cons_))
                                          | And cons' =>
                                              Data.Foldable.all (fun con' =>
                                                                   go l (let 'Mk_Clause clauseAtoms_39__
                                                                            clauseExprs_40__ := r in
                                                                         Mk_Clause clauseAtoms_39__ (cons (SrcLoc.unLoc
                                                                                                           con')
                                                                                                          cons_))) cons'
                                          | Or cons' =>
                                              go l (let 'Mk_Clause clauseAtoms_45__ clauseExprs_46__ := r in
                                                    Mk_Clause clauseAtoms_45__ (Coq.Init.Datatypes.app (GHC.Base.map
                                                                                                        SrcLoc.unLoc
                                                                                                        cons') cons_))
                                          end
                                      | _, _ => false
                                      end) in
    go (Mk_Clause UniqSet.emptyUniqSet (cons e1 nil)) (Mk_Clause
                                                       UniqSet.emptyUniqSet (cons e2 nil)).

Definition eval {a} : (a -> bool) -> BooleanFormula a -> bool :=
  fix eval arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | f, Var x => f x
           | f, And xs => Data.Foldable.all (eval f GHC.Base.∘ SrcLoc.unLoc) xs
           | f, Or xs => Data.Foldable.any (eval f GHC.Base.∘ SrcLoc.unLoc) xs
           | f, Parens x => eval f (SrcLoc.unLoc x)
           end.

Local Definition Eq___BooleanFormula_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : BooleanFormula inst_a -> BooleanFormula inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Var a1, Var b1 => ((a1 GHC.Base.== b1))
    | And a1, And b1 => ((a1 GHC.Base.== b1))
    | Or a1, Or b1 => ((a1 GHC.Base.== b1))
    | Parens a1, Parens b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___BooleanFormula_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : BooleanFormula inst_a -> BooleanFormula inst_a -> bool :=
  fun x y => negb (Eq___BooleanFormula_op_zeze__ x y).

Program Instance Eq___BooleanFormula {a} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (BooleanFormula a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___BooleanFormula_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___BooleanFormula_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BooleanFormula.Data__BooleanFormula' *)

Local Definition Functor__BooleanFormula_fmap {a} {b}
   : (a -> b) -> BooleanFormula a -> BooleanFormula b :=
  BooleanFormula_fmap.

Fixpoint Functor__BooleanFormula_op_zlzd__ {a} {b} (arg_0__ : a) (arg_1__
                                             : BooleanFormula b) : BooleanFormula a
           := match arg_0__, arg_1__ with
              | z, Var a1 => Var ((fun b1 => z) a1)
              | z, And a1 =>
                  And (GHC.Base.fmap (GHC.Base.fmap (Functor__BooleanFormula_op_zlzd__ z)) a1)
              | z, Or a1 =>
                  Or (GHC.Base.fmap (GHC.Base.fmap (Functor__BooleanFormula_op_zlzd__ z)) a1)
              | z, Parens a1 =>
                  Parens (GHC.Base.fmap (Functor__BooleanFormula_op_zlzd__ z) a1)
              end.

Program Instance Functor__BooleanFormula : GHC.Base.Functor BooleanFormula :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__BooleanFormula_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__BooleanFormula_op_zlzd__ |}.

Local Definition Foldable__BooleanFormula_foldMap {m} {a} `{_
   : GHC.Base.Monoid m}
   : (a -> m) -> BooleanFormula a -> m :=
  BooleanFormula_foldMap.

Local Definition Foldable__BooleanFormula_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, BooleanFormula m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__BooleanFormula_foldMap GHC.Base.id.

Local Definition Foldable__BooleanFormula_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> BooleanFormula a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__BooleanFormula_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                         (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                          GHC.Base.flip f)) t)) z.

Local Definition Foldable__BooleanFormula_foldr {a} {b}
   : (a -> b -> b) -> b -> BooleanFormula a -> b :=
  BooleanFormula_foldr.

Local Definition Foldable__BooleanFormula_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> BooleanFormula a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__BooleanFormula_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__BooleanFormula_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> BooleanFormula a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__BooleanFormula_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__BooleanFormula_length
   : forall {a}, BooleanFormula a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__BooleanFormula_foldl' (fun arg_0__ arg_1__ =>
                                       match arg_0__, arg_1__ with
                                       | c, _ => c GHC.Num.+ #1
                                       end) #0.

Fixpoint Foldable__BooleanFormula_null {a} (arg_0__ : BooleanFormula a) : bool
           := match arg_0__ with
              | Var _ => false
              | And a1 =>
                  Data.Foldable.all (Data.Foldable.all Foldable__BooleanFormula_null) a1
              | Or a1 =>
                  Data.Foldable.all (Data.Foldable.all Foldable__BooleanFormula_null) a1
              | Parens a1 => Data.Foldable.all Foldable__BooleanFormula_null a1
              end.

Local Definition Foldable__BooleanFormula_product
   : forall {a}, forall `{GHC.Num.Num a}, BooleanFormula a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__BooleanFormula_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__BooleanFormula_sum
   : forall {a}, forall `{GHC.Num.Num a}, BooleanFormula a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__BooleanFormula_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__BooleanFormula_toList
   : forall {a}, BooleanFormula a -> list a :=
  fun {a} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__BooleanFormula_foldr c n t)).

Program Instance Foldable__BooleanFormula
   : Data.Foldable.Foldable BooleanFormula :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
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

Local Definition Traversable__BooleanFormula_traverse {f} {a} {b} `{_
   : GHC.Base.Applicative f}
   : (a -> f b) -> BooleanFormula a -> f (BooleanFormula b) :=
  BooleanFormula_traverse.

Local Definition Traversable__BooleanFormula_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> BooleanFormula a -> m (BooleanFormula b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__BooleanFormula_traverse.

Local Definition Traversable__BooleanFormula_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     BooleanFormula (f a) -> f (BooleanFormula a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__BooleanFormula_traverse GHC.Base.id.

Local Definition Traversable__BooleanFormula_sequence
   : forall {m} {a},
     forall `{GHC.Base.Monad m}, BooleanFormula (m a) -> m (BooleanFormula a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__BooleanFormula_sequenceA.

Program Instance Traversable__BooleanFormula
   : Data.Traversable.Traversable BooleanFormula :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__BooleanFormula_mapM ;
           Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
             Traversable__BooleanFormula_sequence ;
           Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__BooleanFormula_sequenceA ;
           Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__BooleanFormula_traverse |}.

(* Skipping all instances of class `Binary.Binary', including
   `BooleanFormula.Binary__BooleanFormula' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BooleanFormula.Outputable__BooleanFormula' *)

(* External variables:
     BooleanFormula_fmap BooleanFormula_foldMap BooleanFormula_foldr
     BooleanFormula_traverse None Some bool cons false list negb nil option true
     Coq.Init.Datatypes.app Coq.Program.Basics.compose Data.Foldable.Foldable
     Data.Foldable.all Data.Foldable.any Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Maybe.maybe Data.OldList.nub Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Synonym GHC.Base.build' GHC.Base.flip
     GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zlzd____
     GHC.Base.op_zsze____ GHC.DeferredFix.deferredFix2 GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__ MonadUtils.concatMapM SrcLoc.L
     SrcLoc.Located SrcLoc.unLoc UniqSet.UniqSet UniqSet.addOneToUniqSet
     UniqSet.elementOfUniqSet UniqSet.emptyUniqSet Unique.Uniquable
*)
