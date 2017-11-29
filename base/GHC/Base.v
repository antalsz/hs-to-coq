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
Require Coq.Lists.List.
Require GHC.Prim.
Require GHC.Tuple.

(* Converted type declarations: *)

Record Monoid__Dict a := Monoid__Dict_Build {
  mappend__ : a -> a -> a ;
  mconcat__ : list a -> a ;
  mempty__ : a }.

Definition Monoid a :=
  forall r, (Monoid__Dict a -> r) -> r.

Existing Class Monoid.

Definition mappend `{g : Monoid a} : a -> a -> a :=
  g _ (mappend__ a).

Definition mconcat `{g : Monoid a} : list a -> a :=
  g _ (mconcat__ a).

Definition mempty `{g : Monoid a} : a :=
  g _ (mempty__ a).

Record Functor__Dict f := Functor__Dict_Build {
  fmap__ : forall {a} {b}, (a -> b) -> f a -> f b ;
  op_zlzd____ : forall {a} {b}, a -> f b -> f a }.

Definition Functor f :=
  forall r, (Functor__Dict f -> r) -> r.

Existing Class Functor.

Definition fmap `{g : Functor f} : forall {a} {b}, (a -> b) -> f a -> f b :=
  g _ (fmap__ f).

Definition op_zlzd__ `{g : Functor f} : forall {a} {b}, a -> f b -> f a :=
  g _ (op_zlzd____ f).

Infix "<$" := (op_zlzd__) (at level 99).

Notation "'_<$_'" := (op_zlzd__).

Record Applicative__Dict f := Applicative__Dict_Build {
  op_zlztzg____ : forall {a} {b}, f (a -> b) -> f a -> f b ;
  op_ztzg____ : forall {a} {b}, f a -> f b -> f b ;
  pure__ : forall {a}, a -> f a }.

Definition Applicative f `{Functor f} :=
  forall r, (Applicative__Dict f -> r) -> r.

Existing Class Applicative.

Definition op_zlztzg__ `{g : Applicative f} : forall {a} {b},
                                                f (a -> b) -> f a -> f b :=
  g _ (op_zlztzg____ f).

Definition op_ztzg__ `{g : Applicative f} : forall {a} {b}, f a -> f b -> f b :=
  g _ (op_ztzg____ f).

Definition pure `{g : Applicative f} : forall {a}, a -> f a :=
  g _ (pure__ f).

Infix "<*>" := (op_zlztzg__) (at level 99).

Notation "'_<*>_'" := (op_zlztzg__).

Infix "*>" := (op_ztzg__) (at level 99).

Notation "'_*>_'" := (op_ztzg__).

Record Monad__Dict m := Monad__Dict_Build {
  op_zgzg____ : forall {a} {b}, m a -> m b -> m b ;
  op_zgzgze____ : forall {a} {b}, m a -> (a -> m b) -> m b ;
  return___ : forall {a}, a -> m a }.

Definition Monad m `{Applicative m} :=
  forall r, (Monad__Dict m -> r) -> r.

Existing Class Monad.

Definition op_zgzg__ `{g : Monad m} : forall {a} {b}, m a -> m b -> m b :=
  g _ (op_zgzg____ m).

Definition op_zgzgze__ `{g : Monad m} : forall {a} {b},
                                          m a -> (a -> m b) -> m b :=
  g _ (op_zgzgze____ m).

Definition return_ `{g : Monad m} : forall {a}, a -> m a :=
  g _ (return___ m).

Infix ">>" := (op_zgzg__) (at level 99).

Notation "'_>>_'" := (op_zgzg__).

Infix ">>=" := (op_zgzgze__) (at level 99).

Notation "'_>>=_'" := (op_zgzgze__).

Record Alternative__Dict f := Alternative__Dict_Build {
  empty__ : forall {a}, f a ;
  many__ : forall {a}, f a -> f (list a) ;
  op_zlzbzg____ : forall {a}, f a -> f a -> f a ;
  some__ : forall {a}, f a -> f (list a) }.

Definition Alternative f `{Applicative f} :=
  forall r, (Alternative__Dict f -> r) -> r.

Existing Class Alternative.

Definition empty `{g : Alternative f} : forall {a}, f a :=
  g _ (empty__ f).

Definition many `{g : Alternative f} : forall {a}, f a -> f (list a) :=
  g _ (many__ f).

Definition op_zlzbzg__ `{g : Alternative f} : forall {a}, f a -> f a -> f a :=
  g _ (op_zlzbzg____ f).

Definition some `{g : Alternative f} : forall {a}, f a -> f (list a) :=
  g _ (some__ f).

Infix "<|>" := (op_zlzbzg__) (at level 99).

Notation "'_<|>_'" := (op_zlzbzg__).

Record MonadPlus__Dict (m : Type -> Type) := MonadPlus__Dict_Build {
  mplus__ : forall {a}, m a -> m a -> m a ;
  mzero__ : forall {a}, m a }.

Definition MonadPlus (m : Type -> Type) `{Alternative m} `{Monad m} :=
  forall r, (MonadPlus__Dict m -> r) -> r.

Existing Class MonadPlus.

Definition mplus `{g : MonadPlus m} : forall {a}, m a -> m a -> m a :=
  g _ (mplus__ m).

Definition mzero `{g : MonadPlus m} : forall {a}, m a :=
  g _ (mzero__ m).
(* Midamble *)

(* This includes everything that should be defined in GHC/Base.hs, but cannot
   be generated from Base.hs.

The types defined in GHC.Base:

  list, (), Int, Bool, Ordering, Char, String

are all mapped to corresponding Coq types. Therefore, the Eq/Ord classes must
be defined in this module so that we can create instances for these types.

 *)


(********************* Types ************************)

Require Export GHC.Prim.

Require Export GHC.Tuple.

(* List notation *)
Require Export Coq.Lists.List.

(* Booleans *)
Require Export Bool.Bool.

(* Int and Integer types *)
Require Export GHC.Num.

(* Char type *)
Require Export GHC.Char.


(* Strings *)
Require Coq.Strings.String.
Definition String := list Char.

Bind Scope string_scope with String.string.
Fixpoint hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: hs_string__ s
  end.
Notation "'&' s" := (hs_string__ s) (at level 1, format "'&' s").

(* IO --- PUNT *)
Definition FilePath := String.

(* ASZ: I've been assured that this is OK *)
Inductive IO (a : Type) : Type :=.
Inductive IORef (a : Type) : Type :=.
Inductive IOError : Type :=.

(****************************************************)

(* function composition *)
Require Export Coq.Program.Basics.

Notation "[,]"  := (fun x y => (x,y)).
Notation "[,,]" := (fun x0 y1 z2 => (x0, y1, z2)).
Notation "[,,,]" := (fun x0 x1 x2 x3 => (x0,x1,x2,x3)).
Notation "[,,,,]" := (fun x0 x1 x2 x3 x4 => (x0,x1,x2,x3,x4)).
Notation "[,,,,,]" := (fun x0 x1 x2 x3 x4 x5 => (x0,x1,x2,x3,x4,x5)).
Notation "[,,,,,,]" := (fun x0 x1 x2 x3 x4 x5 x6 => (x0,x1,x2,x3,x4,x5,x6)).
Notation "[,,,,,,,]" := (fun x0 x1 x2 x3 x4 x5 x6 x7 => (x0,x1,x2,x3,x4,x5,x6,x7)).

Notation "'_++_'"   := (fun x y => x ++ y).
Notation "'_::_'"   := (fun x y => x :: y).

Notation "[->]"  := arrow.



(* Configure type argument to be maximally inserted *)
Arguments List.app {_} _ _.

(****************************************************)


Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

(****************************************************)

Axiom errorWithoutStackTrace : forall {A : Type}, String -> A.


(*********** built in classes Eq & Ord **********************)

(* Don't clash with Eq constructor for the comparison type. *)
Record Eq___Dict a := Eq___Dict_Build {
  op_zeze____ : (a -> (a -> bool)) ;
  op_zsze____ : (a -> (a -> bool)) }.

Definition Eq_ a := forall r, (Eq___Dict a -> r) -> r.
Existing Class Eq_.

Definition op_zeze__ {a} {g : Eq_ a} := g _ (op_zeze____ _).
Definition op_zsze__ {a} {g : Eq_ a} := g _ (op_zsze____ _).

Infix "/=" := (op_zsze__) (no associativity, at level 70).

Notation "'_/=_'" := (op_zsze__).

Infix "==" := (op_zeze__) (no associativity, at level 70).

Notation "'_==_'" := (op_zeze__).

Definition eq_default {a} (eq : a -> a -> bool) : Eq_ a :=
  fun _ k => k {|op_zeze____ := eq; op_zsze____ := fun x y => negb (eq x y) |}.

Record Ord__Dict a := Ord__Dict_Build {
  op_zl____ : a -> a -> bool ;
  op_zlze____ : a -> a -> bool ;
  op_zg____ : a -> a -> bool ;
  op_zgze____ : a -> a -> bool ;
  compare__ : a -> a -> comparison ;
  max__ : a -> a -> a ;
  min__ : a -> a -> a }.

Definition Ord a `{Eq_ a} :=
  forall r, (Ord__Dict a -> r) -> r.

Existing Class Ord.

Definition op_zl__ `{g : Ord a} : a -> a -> bool :=
  g _ (op_zl____ a).

Definition op_zlze__ `{g : Ord a} : a -> a -> bool :=
  g _ (op_zlze____ a).

Definition op_zg__ `{g : Ord a} : a -> a -> bool :=
  g _ (op_zg____ a).

Definition op_zgze__ `{g : Ord a} : a -> a -> bool :=
  g _ (op_zgze____ a).

Definition compare `{g : Ord a} : a -> a -> comparison :=
  g _ (compare__ a).

Definition max `{g : Ord a} : a -> a -> a :=
  g _ (max__ a).

Definition min `{g : Ord a} : a -> a -> a :=
  g _ (min__ a).

(* Don't clash with Coq's standard ordering predicates. *)
Infix "<?" := (op_zl__) (no associativity, at level 70).

Notation "'_<?_'" := (op_zl__).

Infix "<=?" := (op_zlze__) (no associativity, at level 70).

Notation "'_<=?_'" := (op_zlze__).

Infix ">?" := (op_zg__) (no associativity, at level 70).

Notation "'_>?_'" := (op_zg__).

Infix ">=?" := (op_zgze__) (no associativity, at level 70).

Notation "'_>=?_'" := (op_zgze__).

(*********** Eq/Ord for primitive types **************************)

Require Coq.Structures.Equalities.
Require Coq.Structures.DecidableType.
Require Coq.Structures.DecidableTypeEx.
Require Coq.Structures.OrderedType.
Require Coq.Structures.OrderedTypeEx.

Module Type HsToCoqDecidableType.
  Include DecidableType.DecidableType.
  Declare Instance eq_t: Eq_ t.
End HsToCoqDecidableType.

Module Type HsToCoqOrderedType.
  Include OrderedType.OrderedType.
  Declare Instance eq_t: Eq_ t.
  Declare Instance ord_t: Ord t.
End HsToCoqOrderedType.

Instance Eq_Int___ : Eq_ Int := fun _ k => k {|
                               op_zeze____ := fun x y => (x =? y)%Z;
                               op_zsze____ := fun x y => negb (x =? y)%Z;
                               |}.

Module Int_DecidableType___ <: HsToCoqDecidableType.
  Include DecidableTypeEx.Z_as_DT.
  Definition eq_t := Eq_Int___.
End Int_DecidableType___.

Instance Ord_Int___ : Ord Int := fun _ k => k {|
  op_zl____   := fun x y => (x <? y)%Z;
  op_zlze____ := fun x y => (x <=? y)%Z;
  op_zg____   := fun x y => (y <? x)%Z;
  op_zgze____ := fun x y => (y <=? x)%Z;
  compare__   := Z.compare%Z ;
  max__       := Z.max%Z;
  min__       := Z.min%Z;
|}.

Module Int_OrderedType___ <: HsToCoqOrderedType.
  Include Int_DecidableType___.
  Definition ord_t := Ord_Int___.
End Int_OrderedType___.

Instance Eq_Integer___ : Eq_ Integer := fun _ k => k {|
                               op_zeze____ := fun x y => (x =? y)%Z;
                               op_zsze____ := fun x y => negb (x =? y)%Z;
                             |}.

(** This is the same as Int_DecidableType___, but we probably don't
    want to reuse that? *)
Module Integer_DecidableType___ <: HsToCoqDecidableType.
  Include DecidableTypeEx.Z_as_DT.
  Definition eq_t := Eq_Integer___.
End Integer_DecidableType___.

Instance Ord_Integer___ : Ord Integer := fun _ k => k {|
  op_zl____   := fun x y => (x <? y)%Z;
  op_zlze____ := fun x y => (x <=? y)%Z;
  op_zg____   := fun x y => (y <? x)%Z;
  op_zgze____ := fun x y => (y <=? x)%Z;
  compare__   := Z.compare%Z ;
  max__       := Z.max%Z;
  min__       := Z.min%Z;
|}.

Module Integer_OrderedType___ <: HsToCoqOrderedType.
  Include Integer_DecidableType___.
  Definition ord_t := Ord_Integer___.
End Integer_OrderedType___.

Instance Eq_Word___ : Eq_ Word := fun _ k => k {|
                               op_zeze____ := fun x y => (x =? y)%N;
                               op_zsze____ := fun x y => negb (x =? y)%N;
                             |}.

Module Word_DecidableType___ <: HsToCoqDecidableType.
  Include DecidableTypeEx.N_as_DT.
  Definition eq_t := Eq_Word___.
End Word_DecidableType___.

Instance Ord_Word___ : Ord Word := fun _ k => k {|
  op_zl____   := fun x y => (x <? y)%N;
  op_zlze____ := fun x y => (x <=? y)%N;
  op_zg____   := fun x y => (y <? x)%N;
  op_zgze____ := fun x y => (y <=? x)%N;
  compare__   := N.compare%N ;
  max__       := N.max%N;
  min__       := N.min%N;
|}.

Module Word_OrderedType___ <: HsToCoqOrderedType.
  Include Word_DecidableType___.
  Definition ord_t := Ord_Word___.
End Word_OrderedType___.

Instance Eq_Char___ : Eq_ Char := fun _ k => k {|
                               op_zeze____ := fun x y => (x =? y)%N;
                               op_zsze____ := fun x y => negb (x =? y)%N;
                             |}.

Module Char_DecidableType___ <: HsToCoqDecidableType.
  Include DecidableTypeEx.N_as_DT.
  Definition eq_t := Eq_Char___.
End Char_DecidableType___.

Instance Ord_Char___ : Ord Char := fun _ k => k {|
  op_zl____   := fun x y => (x <? y)%N;
  op_zlze____ := fun x y => (x <=? y)%N;
  op_zg____   := fun x y => (y <? x)%N;
  op_zgze____ := fun x y => (y <=? x)%N;
  compare__   := N.compare%N ;
  max__       := N.max%N;
  min__       := N.min%N;
|}.

Module Char_OrderedType___ <: HsToCoqOrderedType.
  Include Char_DecidableType___.
  Definition ord_t := Ord_Char___.
End Char_OrderedType___.


(** This is just a heuristic tactic. No guarantee that it will work
    for an arbitrary non-recursive type. *)
Ltac prove_non_rec_type :=
  repeat (match goal with
          | [ |- forall x, _ ] => destruct x
          | [ |- _ <-> _ ] => split
          | [ |- _ -> _ ] => inversion 1
          | [ |- ~ _ ] => inversion 1
          end; auto).

(** We can, of course, just use tactics like [repeat decide equality]
    to prove decidablity, but this one utilizes [op_zeze__] function
    of the [Eq] type class This means that the decidable equality
    proof relies on the [op_zeze__] function -- no duplicated
    deciders! *)
Ltac dec_eq_with_Eq eq_iff :=
  refine (fun x y =>
              (match eq_iff x y with
               | conj f g =>
                 (match (x == y) as b
                        return (x == y = b -> { eq x y } + { ~ eq x y }) with
                  | true =>
                    (fun Heq : x == y = true =>
                       left (f Heq))
                  | false =>
                    (fun Heq : x == y = false =>
                       right (fun H: eq x y =>
                                let contra :=
                                    eq_ind (x == y)
                                           (fun b => b = false) Heq true (g H)
                                    : true = false in _))
                  end)
               end) Logic.eq_refl);
  inversion contra.

Ltac dec_compare_with_Ord lt lt_gt_rev eq_iff_compare_eq :=
  refine (fun x y =>
            (match (compare x y) as c
                   return (compare x y = c -> OrderedType.Compare lt eq x y) with
             | Lt =>
               (fun Hlt: compare x y = Lt =>
                  OrderedType.LT Hlt)
             | Gt =>
               (fun Hlt: compare x y = Gt =>
                  match lt_gt_rev y x with
                  | conj _ f => OrderedType.GT (f Hlt)
                  end)
             | Eq =>
               (fun Hlt: compare x y = Eq =>
                  match eq_iff_compare_eq x y with
                  | conj f _ => OrderedType.EQ (f Hlt)
                  end)
             end) Logic.eq_refl).

Instance Eq_bool___ : Eq_ bool := fun _ k => k {|
                               op_zeze____ := eqb;
                               op_zsze____ := fun x y => negb (eqb x y);
                             |}.

Module bool_Typ <: Equalities.Typ.
  Definition t := bool.
End bool_Typ.

Module bool_DecidableType___ <: HsToCoqDecidableType.
  Include bool_Typ <+ Equalities.HasUsualEq <+ Equalities.UsualIsEqOrig.

  Definition eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
    dec_eq_with_Eq eqb_true_iff.
  Defined.

  Definition eq_t := Eq_bool___.
End bool_DecidableType___.

Definition compare_bool (b1:bool)(b2:bool) : comparison :=
  match b1 , b2 with
  | true , true => Eq
  | false, false => Eq
  | true , false => Gt
  | false , true => Lt
  end.

Instance Ord_bool___ : Ord bool := fun _ k => k {|
  op_zl____   := fun x y => andb (negb x) y;
  op_zlze____ := fun x y => orb (negb x) y;
  op_zg____   := fun x y => orb (negb y) x;
  op_zgze____ := fun x y => andb (negb y) x;
  compare__   := compare_bool;
  max__       := orb;
  min__       := andb
|}.

Module bool_OrderedType___ <: HsToCoqOrderedType.
  Include bool_DecidableType___.

  Hint Unfold eq.

  Definition lt (x y : t) := compare x y = Lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. prove_non_rec_type. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. prove_non_rec_type. Qed.

  Lemma lt_gt_rev: forall x y : t, compare x y = Lt <-> compare y x = Gt.
  Proof. prove_non_rec_type. Qed.

  Lemma eq_iff_compare_eq : forall x y : t, compare x y = Eq <-> eq x y.
  Proof. prove_non_rec_type. Qed.

  Definition compare : forall x y : t, OrderedType.Compare lt eq x y.
    dec_compare_with_Ord lt lt_gt_rev eq_iff_compare_eq.
  Defined.

  Definition ord_t := Ord_bool___.
End bool_OrderedType___.

Instance Eq_unit___ : Eq_ unit := fun _ k => k {|
                               op_zeze____ := fun x y => true;
                               op_zsze____ := fun x y => false;
                             |}.

Module unit_Typ <: Equalities.Typ.
  Definition t := unit.
End unit_Typ.

Module unit_DecidableType___ <: HsToCoqDecidableType.
  Include unit_Typ <+ Equalities.HasUsualEq <+ Equalities.UsualIsEqOrig.

  Lemma eq_iff : forall x y,
      x == y = true <-> x = y.
  Proof. prove_non_rec_type. Qed.

  Definition eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
    dec_eq_with_Eq eq_iff.
  Defined.

  Definition eq_t := Eq_unit___.
End unit_DecidableType___.

Instance Ord_unit___ : Ord unit := fun _ k => k {|
  op_zl____   := fun x y => false;
  op_zlze____ := fun x y => true;
  op_zg____   := fun x y => false;
  op_zgze____ := fun x y => true;
  compare__   := fun x y => Eq ;
  max__       := fun x y => tt;
  min__       := fun x y => tt;
|}.

Module unit_OrderedType___ <: HsToCoqOrderedType.
  Include unit_DecidableType___.

  Hint Unfold eq.

  Definition lt x y := compare x y = Lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. prove_non_rec_type. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. prove_non_rec_type. Qed.

  Lemma lt_gt_rev: forall x y : t, compare x y = Lt <-> compare y x = Gt.
  Proof. prove_non_rec_type. Qed.

  Lemma eq_iff_compare_eq : forall x y : t,
      compare x y = Eq <-> eq x y.
  Proof. prove_non_rec_type. Qed.

  Definition compare : forall x y : t, OrderedType.Compare lt eq x y.
    dec_compare_with_Ord lt lt_gt_rev eq_iff_compare_eq.
  Defined.

  Definition ord_t := Ord_unit___.
End unit_OrderedType___.

Definition eq_comparison (x : comparison) (y: comparison) :=
  match x , y with
  | Eq, Eq => true
  | Gt, Gt => true
  | Lt, Lt => true
  | _ , _  => false
end.

Instance Eq_comparison___ : Eq_ comparison := fun _ k => k
{|
  op_zeze____ := eq_comparison;
  op_zsze____ := fun x y => negb (eq_comparison x y);
|}.

Module comparison_Typ.
  Definition t := comparison.
End comparison_Typ.

Module comparison_DecidableType___ <: HsToCoqDecidableType.
  Include comparison_Typ <+ Equalities.HasUsualEq <+ Equalities.UsualIsEqOrig.

  Lemma eq_iff : forall x y : t,
      x == y = true <-> x = y.
  Proof. prove_non_rec_type. Qed.

  Definition eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
    dec_eq_with_Eq eq_iff.
  Defined.

  Definition eq_t := Eq_comparison___.
End comparison_DecidableType___.

Definition compare_comparison  (x : comparison) (y: comparison) :=
  match x , y with
  | Eq, Eq => Eq
  | _, Eq  => Gt
  | Eq, _  => Lt
  | Lt, Lt => Eq
  | _, Lt  => Lt
  | Lt, _  => Gt
  | Gt, Gt => Eq
end.

Definition ord_default {a} (comp : a -> a -> comparison) `{Eq_ a} : Ord a :=
  fun _ k => k (Ord__Dict_Build _
  (fun x y => (comp x y) == Lt)
  ( fun x y => negb ((comp x y) == Lt))
  (fun x y => (comp y x) == Lt)
  (fun x y => negb ((comp x y) == Lt))
  comp
  (fun x y =>
     match comp x y with
     | Lt => y
     | _  => x
     end)
  (fun x y =>   match comp x y with
             | Gt => y
             | _  => x
             end)).

Instance Ord_comparison___ : Ord comparison := ord_default compare_comparison.

Module comparison_OrderedType___ <: HsToCoqOrderedType.
  Include comparison_DecidableType___.

  Hint Unfold eq.

  Definition lt x y := compare x y = Lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. prove_non_rec_type. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. prove_non_rec_type. Qed.

  Lemma lt_gt_rev: forall x y : t, compare x y = Lt <-> compare y x = Gt.
  Proof. prove_non_rec_type. Qed.

  Lemma eq_iff_compare_eq : forall x y : t,
      compare x y = Eq <-> eq x y.
  Proof. prove_non_rec_type. Qed.

  Definition compare : forall x y : t, OrderedType.Compare lt eq x y.
    dec_compare_with_Ord lt lt_gt_rev eq_iff_compare_eq.
  Defined.

  Definition ord_t := Ord_comparison___.
End comparison_OrderedType___.

(* TODO: are these available in a library somewhere? *)
Definition eqlist {a} `{Eq_ a} : list a -> list a -> bool :=
	fix eqlist xs ys :=
	    match xs , ys with
	    | nil , nil => true
	    | x :: xs' , y :: ys' => andb (x == y) (eqlist xs' ys')
	    | _ ,  _ => false
	    end.

Fixpoint compare_list {a} `{Ord a} (xs :  list a) (ys : list a) : comparison :=
    match xs , ys with
    | nil , nil => Eq
    | nil , _   => Lt
    | _   , nil => Gt
    | x :: xs' , y :: ys' =>
      match compare x y with
          | Lt => Lt
          | Gt => Gt
          | Eq => compare_list xs' ys'
      end
    end.

Instance Eq_list {a} `{Eq_ a} : Eq_ (list a) := fun _ k => k
  {| op_zeze____ := eqlist;
     op_zsze____ := fun x y => negb (eqlist x y)
  |}.

Instance Ord_list {a} `{Ord a}: Ord (list a) :=
  ord_default compare_list.


(* ********************************************************* *)
(* Some Haskell functions we cannot translate (yet)          *)


(* The inner nil case is impossible. So it is left out of the Haskell version. *)
Fixpoint scanr {a b:Type} (f : a -> b -> b) (q0 : b) (xs : list a) : list b :=
  match xs with
  | nil => q0 :: nil
  | y :: ys => match scanr f q0 ys with
              | q :: qs =>  f y q :: (q :: qs)
              | nil => nil
              end
end.


(* The inner nil case is impossible. So it is left out of the Haskell version. *)
Fixpoint scanr1 {a :Type} (f : a -> a -> a) (q0 : a) (xs : list a) : list a :=
  match xs with
  | nil => q0 :: nil
  | y :: nil => y :: nil
  | y :: ys => match scanr1 f q0 ys with
              | q :: qs =>  f y q :: (q :: qs)
              | nil => nil
              end
end.

Definition foldl {a}{b} k z0 xs :=
  fold_right (fun (v:a) (fn:b->b) => (fun (z:b) => fn (k z v))) (id : b -> b) xs z0.

Definition foldl' {a}{b} k z0 xs :=
  fold_right (fun(v:a) (fn:b->b) => (fun(z:b) => fn (k z v))) (id : b -> b) xs z0.

(* Less general type for build *)
Definition build {a} : ((a -> list a -> list a) -> list a -> list a) -> list a :=
  fun g => g (fun x y => x :: y) nil.

(********************************************************************)

Definition oneShot {a} (x:a) := x.

(* Converted value declarations: *)

Local Definition instance_GHC_Base_Monoid__list_a__mappend {inst_a} : list
                                                                      inst_a -> list inst_a -> list inst_a :=
  Coq.Init.Datatypes.app.

Local Definition instance_GHC_Base_Monoid__list_a__mconcat {inst_a} : list (list
                                                                           inst_a) -> list inst_a :=
  fun xss =>
    Coq.Lists.List.flat_map (fun xs =>
                              Coq.Lists.List.flat_map (fun x => cons x nil) xs) xss.

Local Definition instance_GHC_Base_Monoid__list_a__mempty {inst_a} : list
                                                                     inst_a :=
  nil.

Program Instance instance_GHC_Base_Monoid__list_a_ {a} : Monoid (list a) :=
  fun _ k =>
    k {|mappend__ := instance_GHC_Base_Monoid__list_a__mappend ;
      mconcat__ := instance_GHC_Base_Monoid__list_a__mconcat ;
      mempty__ := instance_GHC_Base_Monoid__list_a__mempty |}.

Local Definition instance_forall___GHC_Base_Monoid_b___GHC_Base_Monoid__a____b__mappend {inst_b}
                                                                                        {inst_a} `{Monoid inst_b}
    : (inst_a -> inst_b) -> (inst_a -> inst_b) -> (inst_a -> inst_b) :=
  fun f g x => mappend (f x) (g x).

Local Definition instance_forall___GHC_Base_Monoid_b___GHC_Base_Monoid__a____b__mempty {inst_b}
                                                                                       {inst_a} `{Monoid inst_b}
    : (inst_a -> inst_b) :=
  fun arg_171__ => mempty.

Local Definition instance_GHC_Base_Monoid_unit_mappend : unit -> unit -> unit :=
  fun arg_168__ arg_169__ => tt.

Local Definition instance_GHC_Base_Monoid_unit_mconcat : list unit -> unit :=
  fun arg_170__ => tt.

Local Definition instance_GHC_Base_Monoid_unit_mempty : unit :=
  tt.

Program Instance instance_GHC_Base_Monoid_unit : Monoid unit := fun _ k =>
    k {|mappend__ := instance_GHC_Base_Monoid_unit_mappend ;
      mconcat__ := instance_GHC_Base_Monoid_unit_mconcat ;
      mempty__ := instance_GHC_Base_Monoid_unit_mempty |}.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b___GHC_Base_Monoid__a___b__mappend {inst_a}
                                                                                                            {inst_b}
                                                                                                            `{Monoid
                                                                                                            inst_a}
                                                                                                            `{Monoid
                                                                                                            inst_b}
    : inst_a * inst_b -> inst_a * inst_b -> inst_a * inst_b :=
  fun arg_164__ arg_165__ =>
    match arg_164__ , arg_165__ with
      | pair a1 b1 , pair a2 b2 => pair (mappend a1 a2) (mappend b1 b2)
    end.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b___GHC_Base_Monoid__a___b__mempty {inst_a}
                                                                                                           {inst_b}
                                                                                                           `{Monoid
                                                                                                           inst_a}
                                                                                                           `{Monoid
                                                                                                           inst_b}
    : inst_a * inst_b :=
  pair mempty mempty.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c___GHC_Base_Monoid__a___b___c__mappend {inst_a}
                                                                                                                                     {inst_b}
                                                                                                                                     {inst_c}
                                                                                                                                     `{Monoid
                                                                                                                                     inst_a}
                                                                                                                                     `{Monoid
                                                                                                                                     inst_b}
                                                                                                                                     `{Monoid
                                                                                                                                     inst_c}
    : inst_a * inst_b * inst_c -> inst_a * inst_b * inst_c -> inst_a * inst_b *
      inst_c :=
  fun arg_159__ arg_160__ =>
    match arg_159__ , arg_160__ with
      | pair (pair a1 b1) c1 , pair (pair a2 b2) c2 => pair (pair (mappend a1 a2)
                                                                  (mappend b1 b2)) (mappend c1 c2)
    end.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c___GHC_Base_Monoid__a___b___c__mempty {inst_a}
                                                                                                                                    {inst_b}
                                                                                                                                    {inst_c}
                                                                                                                                    `{Monoid
                                                                                                                                    inst_a}
                                                                                                                                    `{Monoid
                                                                                                                                    inst_b}
                                                                                                                                    `{Monoid
                                                                                                                                    inst_c}
    : inst_a * inst_b * inst_c :=
  pair (pair mempty mempty) mempty.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d___GHC_Base_Monoid__a___b___c___d__mappend {inst_a}
                                                                                                                                                              {inst_b}
                                                                                                                                                              {inst_c}
                                                                                                                                                              {inst_d}
                                                                                                                                                              `{Monoid
                                                                                                                                                              inst_a}
                                                                                                                                                              `{Monoid
                                                                                                                                                              inst_b}
                                                                                                                                                              `{Monoid
                                                                                                                                                              inst_c}
                                                                                                                                                              `{Monoid
                                                                                                                                                              inst_d}
    : inst_a * inst_b * inst_c * inst_d -> inst_a * inst_b * inst_c *
      inst_d -> inst_a * inst_b * inst_c * inst_d :=
  fun arg_154__ arg_155__ =>
    match arg_154__ , arg_155__ with
      | pair (pair (pair a1 b1) c1) d1 , pair (pair (pair a2 b2) c2) d2 => pair (pair
                                                                                (pair (mappend a1 a2) (mappend b1 b2))
                                                                                (mappend c1 c2)) (mappend d1 d2)
    end.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d___GHC_Base_Monoid__a___b___c___d__mempty {inst_a}
                                                                                                                                                             {inst_b}
                                                                                                                                                             {inst_c}
                                                                                                                                                             {inst_d}
                                                                                                                                                             `{Monoid
                                                                                                                                                             inst_a}
                                                                                                                                                             `{Monoid
                                                                                                                                                             inst_b}
                                                                                                                                                             `{Monoid
                                                                                                                                                             inst_c}
                                                                                                                                                             `{Monoid
                                                                                                                                                             inst_d}
    : inst_a * inst_b * inst_c * inst_d :=
  pair (pair (pair mempty mempty) mempty) mempty.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d____GHC_Base_Monoid_e___GHC_Base_Monoid__a___b___c___d___e__mappend {inst_a}
                                                                                                                                                                                       {inst_b}
                                                                                                                                                                                       {inst_c}
                                                                                                                                                                                       {inst_d}
                                                                                                                                                                                       {inst_e}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_a}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_b}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_c}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_d}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_e}
    : inst_a * inst_b * inst_c * inst_d * inst_e -> inst_a * inst_b * inst_c *
      inst_d * inst_e -> inst_a * inst_b * inst_c * inst_d * inst_e :=
  fun arg_149__ arg_150__ =>
    match arg_149__ , arg_150__ with
      | pair (pair (pair (pair a1 b1) c1) d1) e1 , pair (pair (pair (pair a2 b2) c2)
                                                              d2) e2 => pair (pair (pair (pair (mappend a1 a2) (mappend
                                                                                               b1 b2)) (mappend c1 c2))
                                                                                   (mappend d1 d2)) (mappend e1 e2)
    end.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d____GHC_Base_Monoid_e___GHC_Base_Monoid__a___b___c___d___e__mempty {inst_a}
                                                                                                                                                                                      {inst_b}
                                                                                                                                                                                      {inst_c}
                                                                                                                                                                                      {inst_d}
                                                                                                                                                                                      {inst_e}
                                                                                                                                                                                      `{Monoid
                                                                                                                                                                                      inst_a}
                                                                                                                                                                                      `{Monoid
                                                                                                                                                                                      inst_b}
                                                                                                                                                                                      `{Monoid
                                                                                                                                                                                      inst_c}
                                                                                                                                                                                      `{Monoid
                                                                                                                                                                                      inst_d}
                                                                                                                                                                                      `{Monoid
                                                                                                                                                                                      inst_e}
    : inst_a * inst_b * inst_c * inst_d * inst_e :=
  pair (pair (pair (pair mempty mempty) mempty) mempty) mempty.

Local Definition instance_GHC_Base_Monoid_comparison_mappend
    : comparison -> comparison -> comparison :=
  fun arg_145__ arg_146__ =>
    match arg_145__ , arg_146__ with
      | Lt , _ => Lt
      | Eq , y => y
      | Gt , _ => Gt
    end.

Local Definition instance_GHC_Base_Monoid_comparison_mempty : comparison :=
  Eq.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__option_a__mappend {inst_a}
                                                                                          `{Monoid inst_a} : (option
                                                                                                             inst_a) -> (option
                                                                                                             inst_a) -> (option
                                                                                                             inst_a) :=
  fun arg_141__ arg_142__ =>
    match arg_141__ , arg_142__ with
      | None , m => m
      | m , None => m
      | Some m1 , Some m2 => Some (mappend m1 m2)
    end.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__option_a__mempty {inst_a}
                                                                                         `{Monoid inst_a} : (option
                                                                                                            inst_a) :=
  None.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Applicative__GHC_Tuple_pair_type_a__op_zlztzg__ {inst_a}
                                                                                                                `{Monoid
                                                                                                                inst_a}
    : forall {a} {b},
        (GHC.Tuple.pair_type inst_a) (a -> b) -> (GHC.Tuple.pair_type inst_a)
        a -> (GHC.Tuple.pair_type inst_a) b :=
  fun {a} {b} =>
    fun arg_137__ arg_138__ =>
      match arg_137__ , arg_138__ with
        | pair u f , pair v x => pair (mappend u v) (f x)
      end.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Applicative__GHC_Tuple_pair_type_a__pure {inst_a}
                                                                                                         `{Monoid
                                                                                                         inst_a}
    : forall {a}, a -> (GHC.Tuple.pair_type inst_a) a :=
  fun {a} => fun x => pair mempty x.

(* Skipping instance
   instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__GHC_Types_IO_a_ *)

Local Definition instance_GHC_Base_Applicative__GHC_Prim_arrow_a__op_zlztzg__ {inst_a}
    : forall {a} {b},
        (GHC.Prim.arrow inst_a) (a -> b) -> (GHC.Prim.arrow inst_a) a -> (GHC.Prim.arrow
        inst_a) b :=
  fun {a} {b} => fun f g x => f x (g x).

Local Definition instance_GHC_Base_Monad__GHC_Prim_arrow_r__op_zgzgze__ {inst_r}
    : forall {a} {b},
        (GHC.Prim.arrow inst_r) a -> (a -> (GHC.Prim.arrow inst_r) b) -> (GHC.Prim.arrow
        inst_r) b :=
  fun {a} {b} => fun f k => fun r => k (f r) r.

Local Definition instance_GHC_Base_Monad__GHC_Prim_arrow_r__op_zgzg__ {inst_r}
    : forall {a} {b},
        (GHC.Prim.arrow inst_r) a -> (GHC.Prim.arrow inst_r) b -> (GHC.Prim.arrow
        inst_r) b :=
  fun {a} {b} =>
    fun m k =>
      instance_GHC_Base_Monad__GHC_Prim_arrow_r__op_zgzgze__ m (fun arg_8__ => k).

Local Definition instance_GHC_Base_Functor__GHC_Tuple_pair_type_a__fmap {inst_a}
    : forall {a} {b},
        (a -> b) -> (GHC.Tuple.pair_type inst_a) a -> (GHC.Tuple.pair_type inst_a) b :=
  fun {a} {b} =>
    fun arg_120__ arg_121__ =>
      match arg_120__ , arg_121__ with
        | f , pair x y => pair x (f y)
      end.

Local Definition instance_GHC_Base_Functor_option_fmap : forall {a} {b},
                                                           (a -> b) -> option a -> option b :=
  fun {a} {b} =>
    fun arg_116__ arg_117__ =>
      match arg_116__ , arg_117__ with
        | _ , None => None
        | f , Some a => Some (f a)
      end.

Local Definition instance_GHC_Base_Applicative_option_op_ztzg__ : forall {a}
                                                                         {b},
                                                                    option a -> option b -> option b :=
  fun {a} {b} =>
    fun arg_113__ arg_114__ =>
      match arg_113__ , arg_114__ with
        | Some _m1 , m2 => m2
        | None , _m2 => None
      end.

Local Definition instance_GHC_Base_Applicative_option_pure : forall {a},
                                                               a -> option a :=
  fun {a} => Some.

Local Definition instance_GHC_Base_Monad_option_op_zgzgze__ : forall {a} {b},
                                                                option a -> (a -> option b) -> option b :=
  fun {a} {b} =>
    fun arg_104__ arg_105__ =>
      match arg_104__ , arg_105__ with
        | Some x , k => k x
        | None , _ => None
      end.

(* Skipping instance instance_GHC_Base_Alternative_option *)

(* Skipping instance instance_GHC_Base_MonadPlus_option *)

Local Definition instance_GHC_Base_Applicative_list_op_zlztzg__ : forall {a}
                                                                         {b},
                                                                    list (a -> b) -> list a -> list b :=
  fun {a} {b} =>
    fun fs xs =>
      Coq.Lists.List.flat_map (fun f =>
                                Coq.Lists.List.flat_map (fun x => cons (f x) nil) xs) fs.

Local Definition instance_GHC_Base_Applicative_list_op_ztzg__ : forall {a} {b},
                                                                  list a -> list b -> list b :=
  fun {a} {b} =>
    fun xs ys =>
      Coq.Lists.List.flat_map (fun _ =>
                                Coq.Lists.List.flat_map (fun y => cons y nil) ys) xs.

Local Definition instance_GHC_Base_Applicative_list_pure : forall {a},
                                                             a -> list a :=
  fun {a} => fun x => cons x nil.

Local Definition instance_GHC_Base_Monad_list_op_zgzgze__ : forall {a} {b},
                                                              list a -> (a -> list b) -> list b :=
  fun {a} {b} =>
    fun xs f =>
      Coq.Lists.List.flat_map (fun x =>
                                Coq.Lists.List.flat_map (fun y => cons y nil) (f x)) xs.

(* Skipping instance instance_GHC_Base_Alternative_list *)

(* Skipping instance instance_GHC_Base_MonadPlus_list *)

(* Skipping instance instance_GHC_Base_Functor_GHC_Types_IO *)

(* Skipping instance instance_GHC_Base_Applicative_GHC_Types_IO *)

(* Skipping instance instance_GHC_Base_Monad_GHC_Types_IO *)

(* Skipping instance instance_GHC_Base_Alternative_GHC_Types_IO *)

(* Skipping instance instance_GHC_Base_MonadPlus_GHC_Types_IO *)

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__compare {inst_a}
                                                                                    `{Ord inst_a} : option
                                                                                                    inst_a -> option
                                                                                                    inst_a -> comparison :=
  fun a b =>
    match a with
      | None => match b with
                  | None => Eq
                  | _ => Lt
                end
      | Some a1 => match b with
                     | Some b1 => (compare a1 b1)
                     | _ => Gt
                   end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zg__ {inst_a}
                                                                                    `{Ord inst_a} : option
                                                                                                    inst_a -> option
                                                                                                    inst_a -> bool :=
  fun a b =>
    match a with
      | None => match b with
                  | None => false
                  | _ => false
                end
      | Some a1 => match b with
                     | Some b1 => (op_zg__ a1 b1)
                     | _ => true
                   end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zgze__ {inst_a}
                                                                                      `{Ord inst_a} : option
                                                                                                      inst_a -> option
                                                                                                      inst_a -> bool :=
  fun a b =>
    match a with
      | None => match b with
                  | None => true
                  | _ => false
                end
      | Some a1 => match b with
                     | Some b1 => (op_zgze__ a1 b1)
                     | _ => true
                   end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zl__ {inst_a}
                                                                                    `{Ord inst_a} : option
                                                                                                    inst_a -> option
                                                                                                    inst_a -> bool :=
  fun a b =>
    match a with
      | None => match b with
                  | None => false
                  | _ => true
                end
      | Some a1 => match b with
                     | Some b1 => (op_zl__ a1 b1)
                     | _ => false
                   end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zlze__ {inst_a}
                                                                                      `{Ord inst_a} : option
                                                                                                      inst_a -> option
                                                                                                      inst_a -> bool :=
  fun a b =>
    match a with
      | None => match b with
                  | None => true
                  | _ => true
                end
      | Some a1 => match b with
                     | Some b1 => (op_zlze__ a1 b1)
                     | _ => false
                   end
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__min {inst_a}
                                                                                `{Ord inst_a} : option inst_a -> option
                                                                                                inst_a -> option
                                                                                                inst_a :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zlze__ x
                                                                            y : bool
    then x
    else y.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__max {inst_a}
                                                                                `{Ord inst_a} : option inst_a -> option
                                                                                                inst_a -> option
                                                                                                inst_a :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zlze__ x
                                                                            y : bool
    then y
    else x.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___option_a__op_zeze__ {inst_a}
                                                                                      `{Eq_ inst_a} : option
                                                                                                      inst_a -> option
                                                                                                      inst_a -> bool :=
  fun arg_51__ arg_52__ =>
    match arg_51__ , arg_52__ with
      | None , None => true
      | Some a1 , Some b1 => ((op_zeze__ a1 b1))
      | _ , _ => false
    end.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___option_a__op_zsze__ {inst_a}
                                                                                      `{Eq_ inst_a} : option
                                                                                                      inst_a -> option
                                                                                                      inst_a -> bool :=
  fun a b =>
    negb (instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___option_a__op_zeze__ a b).

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___option_a_ {a}
                                                                            `{Eq_ a} : Eq_ (option a) := fun _ k =>
    k
    {|op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___option_a__op_zeze__ ;
    op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___option_a__op_zsze__ |}.

Program Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a_ {a}
                                                                            `{Ord a} : Ord (option a) := fun _ k =>
    k
    {|op_zl____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zl__ ;
    op_zlze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zlze__ ;
    op_zg____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zg__ ;
    op_zgze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__op_zgze__ ;
    compare__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__compare ;
    max__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__max ;
    min__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__option_a__min |}.

Definition ap {m} {a} {b} `{(Monad m)} : m (a -> b) -> m a -> m b :=
  fun m1 m2 =>
    op_zgzgze__ m1 (fun x1 => op_zgzgze__ m2 (fun x2 => return_ (x1 x2))).

Definition assert {a} : bool -> a -> a :=
  fun _pred r => r.

Definition breakpoint {a} : a -> a :=
  fun r => r.

Definition breakpointCond {a} : bool -> a -> a :=
  fun arg_19__ arg_20__ => match arg_19__ , arg_20__ with | _ , r => r end.

Definition const {a} {b} : a -> b -> a :=
  fun arg_16__ arg_17__ => match arg_16__ , arg_17__ with | x , _ => x end.

Definition asTypeOf {a} : a -> a -> a :=
  const.

Local Definition instance_GHC_Base_Applicative__GHC_Prim_arrow_a__pure {inst_a}
    : forall {a}, a -> (GHC.Prim.arrow inst_a) a :=
  fun {a} => const.

Definition eqString : String -> String -> bool :=
  fix eqString arg_22__ arg_23__
        := match arg_22__ , arg_23__ with
             | nil , nil => true
             | cons c1 cs1 , cons c2 cs2 => andb (op_zeze__ c1 c2) (eqString cs1 cs2)
             | _ , _ => false
           end.

Definition flip {a} {b} {c} : (a -> b -> c) -> b -> a -> c :=
  fun f x y => f y x.

Definition foldr {a} {b} : (a -> b -> b) -> b -> list a -> b :=
  fun k z =>
    let go :=
      fix go arg_32__
            := match arg_32__ with
                 | nil => z
                 | cons y ys => k y (go ys)
               end in
    go.

Definition mapM {m} {a} {b} `{Monad m} : (a -> m b) -> list a -> m (list b) :=
  fun f as_ =>
    let k :=
      fun a r =>
        op_zgzgze__ (f a) (fun x => op_zgzgze__ r (fun xs => return_ (cons x xs))) in
    foldr k (return_ nil) as_.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__option_a__mconcat {inst_a}
                                                                                          `{Monoid inst_a} : list
                                                                                                             (option
                                                                                                             inst_a) -> (option
                                                                                                             inst_a) :=
  foldr instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__option_a__mappend
  instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__option_a__mempty.

Program Instance instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__option_a_ {a}
                                                                                  `{Monoid a} : Monoid (option a) :=
  fun _ k =>
    k
    {|mappend__ := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__option_a__mappend ;
    mconcat__ := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__option_a__mconcat ;
    mempty__ := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__option_a__mempty |}.

Local Definition instance_GHC_Base_Monoid_comparison_mconcat : list
                                                               comparison -> comparison :=
  foldr instance_GHC_Base_Monoid_comparison_mappend
  instance_GHC_Base_Monoid_comparison_mempty.

Program Instance instance_GHC_Base_Monoid_comparison : Monoid comparison :=
  fun _ k =>
    k {|mappend__ := instance_GHC_Base_Monoid_comparison_mappend ;
      mconcat__ := instance_GHC_Base_Monoid_comparison_mconcat ;
      mempty__ := instance_GHC_Base_Monoid_comparison_mempty |}.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d____GHC_Base_Monoid_e___GHC_Base_Monoid__a___b___c___d___e__mconcat {inst_a}
                                                                                                                                                                                       {inst_b}
                                                                                                                                                                                       {inst_c}
                                                                                                                                                                                       {inst_d}
                                                                                                                                                                                       {inst_e}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_a}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_b}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_c}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_d}
                                                                                                                                                                                       `{Monoid
                                                                                                                                                                                       inst_e}
    : list (inst_a * inst_b * inst_c * inst_d * inst_e) -> inst_a * inst_b * inst_c
      * inst_d * inst_e :=
  foldr
  instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d____GHC_Base_Monoid_e___GHC_Base_Monoid__a___b___c___d___e__mappend
  instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d____GHC_Base_Monoid_e___GHC_Base_Monoid__a___b___c___d___e__mempty.

Program Instance instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d____GHC_Base_Monoid_e___GHC_Base_Monoid__a___b___c___d___e_ {a}
                                                                                                                                                                               {b}
                                                                                                                                                                               {c}
                                                                                                                                                                               {d}
                                                                                                                                                                               {e}
                                                                                                                                                                               `{Monoid
                                                                                                                                                                               a}
                                                                                                                                                                               `{Monoid
                                                                                                                                                                               b}
                                                                                                                                                                               `{Monoid
                                                                                                                                                                               c}
                                                                                                                                                                               `{Monoid
                                                                                                                                                                               d}
                                                                                                                                                                               `{Monoid
                                                                                                                                                                               e}
  : Monoid (a * b * c * d * e) := fun _ k =>
    k
    {|mappend__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d____GHC_Base_Monoid_e___GHC_Base_Monoid__a___b___c___d___e__mappend ;
    mconcat__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d____GHC_Base_Monoid_e___GHC_Base_Monoid__a___b___c___d___e__mconcat ;
    mempty__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d____GHC_Base_Monoid_e___GHC_Base_Monoid__a___b___c___d___e__mempty |}.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d___GHC_Base_Monoid__a___b___c___d__mconcat {inst_a}
                                                                                                                                                              {inst_b}
                                                                                                                                                              {inst_c}
                                                                                                                                                              {inst_d}
                                                                                                                                                              `{Monoid
                                                                                                                                                              inst_a}
                                                                                                                                                              `{Monoid
                                                                                                                                                              inst_b}
                                                                                                                                                              `{Monoid
                                                                                                                                                              inst_c}
                                                                                                                                                              `{Monoid
                                                                                                                                                              inst_d}
    : list (inst_a * inst_b * inst_c * inst_d) -> inst_a * inst_b * inst_c *
      inst_d :=
  foldr
  instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d___GHC_Base_Monoid__a___b___c___d__mappend
  instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d___GHC_Base_Monoid__a___b___c___d__mempty.

Program Instance instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d___GHC_Base_Monoid__a___b___c___d_ {a}
                                                                                                                                                      {b}
                                                                                                                                                      {c}
                                                                                                                                                      {d}
                                                                                                                                                      `{Monoid
                                                                                                                                                      a}
                                                                                                                                                      `{Monoid
                                                                                                                                                      b}
                                                                                                                                                      `{Monoid
                                                                                                                                                      c}
                                                                                                                                                      `{Monoid
                                                                                                                                                      d}
  : Monoid (a * b * c * d) := fun _ k =>
    k
    {|mappend__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d___GHC_Base_Monoid__a___b___c___d__mappend ;
    mconcat__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d___GHC_Base_Monoid__a___b___c___d__mconcat ;
    mempty__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c____GHC_Base_Monoid_d___GHC_Base_Monoid__a___b___c___d__mempty |}.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c___GHC_Base_Monoid__a___b___c__mconcat {inst_a}
                                                                                                                                     {inst_b}
                                                                                                                                     {inst_c}
                                                                                                                                     `{Monoid
                                                                                                                                     inst_a}
                                                                                                                                     `{Monoid
                                                                                                                                     inst_b}
                                                                                                                                     `{Monoid
                                                                                                                                     inst_c}
    : list (inst_a * inst_b * inst_c) -> inst_a * inst_b * inst_c :=
  foldr
  instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c___GHC_Base_Monoid__a___b___c__mappend
  instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c___GHC_Base_Monoid__a___b___c__mempty.

Program Instance instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c___GHC_Base_Monoid__a___b___c_ {a}
                                                                                                                             {b}
                                                                                                                             {c}
                                                                                                                             `{Monoid
                                                                                                                             a}
                                                                                                                             `{Monoid
                                                                                                                             b}
                                                                                                                             `{Monoid
                                                                                                                             c}
  : Monoid (a * b * c) := fun _ k =>
    k
    {|mappend__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c___GHC_Base_Monoid__a___b___c__mappend ;
    mconcat__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c___GHC_Base_Monoid__a___b___c__mconcat ;
    mempty__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b____GHC_Base_Monoid_c___GHC_Base_Monoid__a___b___c__mempty |}.

Local Definition instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b___GHC_Base_Monoid__a___b__mconcat {inst_a}
                                                                                                            {inst_b}
                                                                                                            `{Monoid
                                                                                                            inst_a}
                                                                                                            `{Monoid
                                                                                                            inst_b}
    : list (inst_a * inst_b) -> inst_a * inst_b :=
  foldr
  instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b___GHC_Base_Monoid__a___b__mappend
  instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b___GHC_Base_Monoid__a___b__mempty.

Program Instance instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b___GHC_Base_Monoid__a___b_ {a}
                                                                                                    {b} `{Monoid a}
                                                                                                    `{Monoid b} : Monoid
                                                                                                                  (a *
                                                                                                                  b) :=
  fun _ k =>
    k
    {|mappend__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b___GHC_Base_Monoid__a___b__mappend ;
    mconcat__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b___GHC_Base_Monoid__a___b__mconcat ;
    mempty__ := instance_forall___GHC_Base_Monoid_a____GHC_Base_Monoid_b___GHC_Base_Monoid__a___b__mempty |}.

Local Definition instance_forall___GHC_Base_Monoid_b___GHC_Base_Monoid__a____b__mconcat {inst_b}
                                                                                        {inst_a} `{Monoid inst_b} : list
                                                                                                                    (inst_a -> inst_b) -> (inst_a -> inst_b) :=
  foldr instance_forall___GHC_Base_Monoid_b___GHC_Base_Monoid__a____b__mappend
  instance_forall___GHC_Base_Monoid_b___GHC_Base_Monoid__a____b__mempty.

Program Instance instance_forall___GHC_Base_Monoid_b___GHC_Base_Monoid__a____b_ {b}
                                                                                {a} `{Monoid b} : Monoid (a -> b) :=
  fun _ k =>
    k
    {|mappend__ := instance_forall___GHC_Base_Monoid_b___GHC_Base_Monoid__a____b__mappend ;
    mconcat__ := instance_forall___GHC_Base_Monoid_b___GHC_Base_Monoid__a____b__mconcat ;
    mempty__ := instance_forall___GHC_Base_Monoid_b___GHC_Base_Monoid__a____b__mempty |}.

Definition id {a} : a -> a :=
  fun x => x.

Definition join {m} {a} `{(Monad m)} : m (m a) -> m a :=
  fun x => op_zgzgze__ x id.

Definition sequence {m} {a} `{Monad m} : list (m a) -> m (list a) :=
  mapM id.

Definition liftA {f} {a} {b} `{Applicative f} : (a -> b) -> f a -> f b :=
  fun f a => op_zlztzg__ (pure f) a.

Definition liftA2 {f} {a} {b} {c} `{Applicative f} : (a -> b -> c) -> f a -> f
                                                     b -> f c :=
  fun f a b => op_zlztzg__ (fmap f a) b.

Definition liftA3 {f} {a} {b} {c} {d} `{Applicative f} : (a -> b -> c -> d) -> f
                                                         a -> f b -> f c -> f d :=
  fun f a b c => op_zlztzg__ (op_zlztzg__ (fmap f a) b) c.

Definition liftM {m} {a1} {r} `{(Monad m)} : (a1 -> r) -> m a1 -> m r :=
  fun f m1 => op_zgzgze__ m1 (fun x1 => return_ (f x1)).

Definition liftM2 {m} {a1} {a2} {r} `{(Monad m)} : (a1 -> a2 -> r) -> m a1 -> m
                                                   a2 -> m r :=
  fun f m1 m2 =>
    op_zgzgze__ m1 (fun x1 => op_zgzgze__ m2 (fun x2 => return_ (f x1 x2))).

Definition liftM3 {m} {a1} {a2} {a3} {r} `{(Monad m)}
    : (a1 -> a2 -> a3 -> r) -> m a1 -> m a2 -> m a3 -> m r :=
  fun f m1 m2 m3 =>
    op_zgzgze__ m1 (fun x1 =>
                  op_zgzgze__ m2 (fun x2 => op_zgzgze__ m3 (fun x3 => return_ (f x1 x2 x3)))).

Definition liftM4 {m} {a1} {a2} {a3} {a4} {r} `{(Monad m)}
    : (a1 -> a2 -> a3 -> a4 -> r) -> m a1 -> m a2 -> m a3 -> m a4 -> m r :=
  fun f m1 m2 m3 m4 =>
    op_zgzgze__ m1 (fun x1 =>
                  op_zgzgze__ m2 (fun x2 =>
                                op_zgzgze__ m3 (fun x3 => op_zgzgze__ m4 (fun x4 => return_ (f x1 x2 x3 x4))))).

Definition liftM5 {m} {a1} {a2} {a3} {a4} {a5} {r} `{(Monad m)}
    : (a1 -> a2 -> a3 -> a4 -> a5 -> r) -> m a1 -> m a2 -> m a3 -> m a4 -> m a5 -> m
      r :=
  fun f m1 m2 m3 m4 m5 =>
    op_zgzgze__ m1 (fun x1 =>
                  op_zgzgze__ m2 (fun x2 =>
                                op_zgzgze__ m3 (fun x3 =>
                                              op_zgzgze__ m4 (fun x4 =>
                                                            op_zgzgze__ m5 (fun x5 => return_ (f x1 x2 x3 x4 x5)))))).

Definition map {A B : Type} (f : A -> B) xs :=
  Coq.Lists.List.map f xs.

Local Definition instance_GHC_Base_Functor_list_fmap : forall {a} {b},
                                                         (a -> b) -> list a -> list b :=
  fun {a} {b} => map.

Definition mapFB {elt} {lst} {a}
    : (elt -> lst -> lst) -> (a -> elt) -> a -> lst -> lst :=
  fun c f => fun x ys => c (f x) ys.

Definition op_z2218U__ {b} {c} {a} : (b -> c) -> (a -> b) -> a -> c :=
  fun f g => fun x => f (g x).

Infix "∘" := (op_z2218U__) (left associativity, at level 40).

Notation "'_∘_'" := (op_z2218U__).

Local Definition instance_GHC_Base_Functor_list_op_zlzd__ : forall {a} {b},
                                                              a -> list b -> list a :=
  fun {a} {b} => op_z2218U__ instance_GHC_Base_Functor_list_fmap const.

Program Instance instance_GHC_Base_Functor_list : Functor list := fun _ k =>
    k {|fmap__ := fun {a} {b} => instance_GHC_Base_Functor_list_fmap ;
      op_zlzd____ := fun {a} {b} => instance_GHC_Base_Functor_list_op_zlzd__ |}.

Program Instance instance_GHC_Base_Applicative_list : Applicative list := fun _
                                                                              k =>
    k {|op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_list_op_zlztzg__ ;
      op_ztzg____ := fun {a} {b} => instance_GHC_Base_Applicative_list_op_ztzg__ ;
      pure__ := fun {a} => instance_GHC_Base_Applicative_list_pure |}.

Local Definition instance_GHC_Base_Monad_list_return_ : forall {a},
                                                          a -> list a :=
  fun {a} => pure.

Local Definition instance_GHC_Base_Monad_list_op_zgzg__ : forall {a} {b},
                                                            list a -> list b -> list b :=
  fun {a} {b} => op_ztzg__.

Program Instance instance_GHC_Base_Monad_list : Monad list := fun _ k =>
    k {|op_zgzg____ := fun {a} {b} => instance_GHC_Base_Monad_list_op_zgzg__ ;
      op_zgzgze____ := fun {a} {b} => instance_GHC_Base_Monad_list_op_zgzgze__ ;
      return___ := fun {a} => instance_GHC_Base_Monad_list_return_ |}.

Local Definition instance_GHC_Base_Functor_option_op_zlzd__ : forall {a} {b},
                                                                a -> option b -> option a :=
  fun {a} {b} => op_z2218U__ instance_GHC_Base_Functor_option_fmap const.

Program Instance instance_GHC_Base_Functor_option : Functor option := fun _ k =>
    k {|fmap__ := fun {a} {b} => instance_GHC_Base_Functor_option_fmap ;
      op_zlzd____ := fun {a} {b} => instance_GHC_Base_Functor_option_op_zlzd__ |}.

Local Definition instance_GHC_Base_Applicative_option_op_zlztzg__ : forall {a}
                                                                           {b},
                                                                      option (a -> b) -> option a -> option b :=
  fun {a} {b} =>
    fun arg_109__ arg_110__ =>
      match arg_109__ , arg_110__ with
        | Some f , m => fmap f m
        | None , _m => None
      end.

Program Instance instance_GHC_Base_Applicative_option : Applicative option :=
  fun _ k =>
    k {|op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_option_op_zlztzg__ ;
      op_ztzg____ := fun {a} {b} => instance_GHC_Base_Applicative_option_op_ztzg__ ;
      pure__ := fun {a} => instance_GHC_Base_Applicative_option_pure |}.

Local Definition instance_GHC_Base_Monad_option_op_zgzg__ : forall {a} {b},
                                                              option a -> option b -> option b :=
  fun {a} {b} => op_ztzg__.

Local Definition instance_GHC_Base_Monad_option_return_ : forall {a},
                                                            a -> option a :=
  fun {a} => pure.

Program Instance instance_GHC_Base_Monad_option : Monad option := fun _ k =>
    k {|op_zgzg____ := fun {a} {b} => instance_GHC_Base_Monad_option_op_zgzg__ ;
      op_zgzgze____ := fun {a} {b} => instance_GHC_Base_Monad_option_op_zgzgze__ ;
      return___ := fun {a} => instance_GHC_Base_Monad_option_return_ |}.

Local Definition instance_GHC_Base_Functor__GHC_Tuple_pair_type_a__op_zlzd__ {inst_a}
    : forall {a} {b},
        a -> (GHC.Tuple.pair_type inst_a) b -> (GHC.Tuple.pair_type inst_a) a :=
  fun {a} {b} =>
    op_z2218U__ instance_GHC_Base_Functor__GHC_Tuple_pair_type_a__fmap const.

Program Instance instance_GHC_Base_Functor__GHC_Tuple_pair_type_a_ {a} : Functor
                                                                         (GHC.Tuple.pair_type a) := fun _ k =>
    k {|fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor__GHC_Tuple_pair_type_a__fmap ;
      op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor__GHC_Tuple_pair_type_a__op_zlzd__ |}.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Applicative__GHC_Tuple_pair_type_a__op_ztzg__ {inst_a}
                                                                                                              `{Monoid
                                                                                                              inst_a}
    : forall {a} {b},
        (GHC.Tuple.pair_type inst_a) a -> (GHC.Tuple.pair_type inst_a)
        b -> (GHC.Tuple.pair_type inst_a) b :=
  fun {a} {b} =>
    fun a1 a2 =>
      instance_forall___GHC_Base_Monoid_a___GHC_Base_Applicative__GHC_Tuple_pair_type_a__op_zlztzg__
      (op_zlzd__ id a1) a2.

Program Instance instance_forall___GHC_Base_Monoid_a___GHC_Base_Applicative__GHC_Tuple_pair_type_a_ {a}
                                                                                                    `{Monoid a}
  : Applicative (GHC.Tuple.pair_type a) := fun _ k =>
    k {|op_zlztzg____ := fun {a} {b} =>
        instance_forall___GHC_Base_Monoid_a___GHC_Base_Applicative__GHC_Tuple_pair_type_a__op_zlztzg__ ;
      op_ztzg____ := fun {a} {b} =>
        instance_forall___GHC_Base_Monoid_a___GHC_Base_Applicative__GHC_Tuple_pair_type_a__op_ztzg__ ;
      pure__ := fun {a} =>
        instance_forall___GHC_Base_Monoid_a___GHC_Base_Applicative__GHC_Tuple_pair_type_a__pure |}.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monad__GHC_Tuple_pair_type_a__return_ {inst_a}
                                                                                                      `{Monoid inst_a}
    : forall {a}, a -> (GHC.Tuple.pair_type inst_a) a :=
  fun {a} => pure.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monad__GHC_Tuple_pair_type_a__op_zgzgze__ {inst_a}
                                                                                                          `{Monoid
                                                                                                          inst_a}
    : forall {a} {b},
        (GHC.Tuple.pair_type inst_a) a -> (a -> (GHC.Tuple.pair_type inst_a)
        b) -> (GHC.Tuple.pair_type inst_a) b :=
  fun {a} {b} =>
    fun arg_129__ arg_130__ =>
      match arg_129__ , arg_130__ with
        | pair u a , k => let scrut_131__ := k a in
                          match scrut_131__ with
                            | pair v b => pair (mappend u v) b
                          end
      end.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monad__GHC_Tuple_pair_type_a__op_zgzg__ {inst_a}
                                                                                                        `{Monoid inst_a}
    : forall {a} {b},
        (GHC.Tuple.pair_type inst_a) a -> (GHC.Tuple.pair_type inst_a)
        b -> (GHC.Tuple.pair_type inst_a) b :=
  fun {a} {b} =>
    fun m k =>
      instance_forall___GHC_Base_Monoid_a___GHC_Base_Monad__GHC_Tuple_pair_type_a__op_zgzgze__
      m (fun arg_8__ => k).

Program Instance instance_forall___GHC_Base_Monoid_a___GHC_Base_Monad__GHC_Tuple_pair_type_a_ {a}
                                                                                              `{Monoid a} : Monad
                                                                                                            (GHC.Tuple.pair_type
                                                                                                            a) := fun _
                                                                                                                      k =>
    k {|op_zgzg____ := fun {a} {b} =>
        instance_forall___GHC_Base_Monoid_a___GHC_Base_Monad__GHC_Tuple_pair_type_a__op_zgzg__ ;
      op_zgzgze____ := fun {a} {b} =>
        instance_forall___GHC_Base_Monoid_a___GHC_Base_Monad__GHC_Tuple_pair_type_a__op_zgzgze__ ;
      return___ := fun {a} =>
        instance_forall___GHC_Base_Monoid_a___GHC_Base_Monad__GHC_Tuple_pair_type_a__return_ |}.

Local Definition instance_GHC_Base_Functor__GHC_Prim_arrow_r__fmap {inst_r}
    : forall {a} {b},
        (a -> b) -> (GHC.Prim.arrow inst_r) a -> (GHC.Prim.arrow inst_r) b :=
  fun {a} {b} => op_z2218U__.

Local Definition instance_GHC_Base_Functor__GHC_Prim_arrow_r__op_zlzd__ {inst_r}
    : forall {a} {b}, a -> (GHC.Prim.arrow inst_r) b -> (GHC.Prim.arrow inst_r) a :=
  fun {a} {b} =>
    op_z2218U__ instance_GHC_Base_Functor__GHC_Prim_arrow_r__fmap const.

Program Instance instance_GHC_Base_Functor__GHC_Prim_arrow_r_ {r} : Functor
                                                                    (GHC.Prim.arrow r) := fun _ k =>
    k {|fmap__ := fun {a} {b} => instance_GHC_Base_Functor__GHC_Prim_arrow_r__fmap ;
      op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor__GHC_Prim_arrow_r__op_zlzd__ |}.

Local Definition instance_GHC_Base_Applicative__GHC_Prim_arrow_a__op_ztzg__ {inst_a}
    : forall {a} {b},
        (GHC.Prim.arrow inst_a) a -> (GHC.Prim.arrow inst_a) b -> (GHC.Prim.arrow
        inst_a) b :=
  fun {a} {b} =>
    fun a1 a2 =>
      instance_GHC_Base_Applicative__GHC_Prim_arrow_a__op_zlztzg__ (op_zlzd__ id a1)
                                                                   a2.

Program Instance instance_GHC_Base_Applicative__GHC_Prim_arrow_a_ {a}
  : Applicative (GHC.Prim.arrow a) := fun _ k =>
    k {|op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative__GHC_Prim_arrow_a__op_zlztzg__ ;
      op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative__GHC_Prim_arrow_a__op_ztzg__ ;
      pure__ := fun {a} => instance_GHC_Base_Applicative__GHC_Prim_arrow_a__pure |}.

Local Definition instance_GHC_Base_Monad__GHC_Prim_arrow_r__return_ {inst_r}
    : forall {a}, a -> (GHC.Prim.arrow inst_r) a :=
  fun {a} => pure.

Program Instance instance_GHC_Base_Monad__GHC_Prim_arrow_r_ {r} : Monad
                                                                  (GHC.Prim.arrow r) := fun _ k =>
    k {|op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad__GHC_Prim_arrow_r__op_zgzg__ ;
      op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad__GHC_Prim_arrow_r__op_zgzgze__ ;
      return___ := fun {a} => instance_GHC_Base_Monad__GHC_Prim_arrow_r__return_ |}.

Definition op_zd__ {a} {b} : (a -> b) -> a -> b :=
  fun f x => f x.

Infix "$" := (op_zd__) (at level 99).

Notation "'_$_'" := (op_zd__).

Definition op_zlztztzg__ {f} {a} {b} `{Applicative f} : f a -> f (a -> b) -> f
                                                        b :=
  liftA2 (flip op_zd__).

Infix "<**>" := (op_zlztztzg__) (at level 99).

Notation "'_<**>_'" := (op_zlztztzg__).

Definition op_zdzn__ {a} {b} : (a -> b) -> a -> b :=
  fun f x => match x with | vx => f vx end.

Infix "$!" := (op_zdzn__) (at level 99).

Notation "'_$!_'" := (op_zdzn__).

Definition op_zezlzl__ {m} {a} {b} `{Monad m} : (a -> m b) -> m a -> m b :=
  fun f x => op_zgzgze__ x f.

Infix "=<<" := (op_zezlzl__) (at level 99).

Notation "'_=<<_'" := (op_zezlzl__).

Definition otherwise : bool :=
  true.

Definition when {f} `{(Applicative f)} : bool -> f unit -> f unit :=
  fun p s => if p : bool then s else pure tt.

(* Unbound variables:
     Eq Eq_ Gt Lt None Ord Some String Type andb bool compare comparison cons false
     list negb nil op_zeze__ op_zg__ op_zgze__ op_zl__ op_zlze__ op_zt__ option pair
     true tt unit Coq.Init.Datatypes.app Coq.Lists.List.flat_map Coq.Lists.List.map
     GHC.Prim.arrow GHC.Tuple.pair_type
*)
