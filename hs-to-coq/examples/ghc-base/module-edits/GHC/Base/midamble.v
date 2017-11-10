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


Instance Eq_option {a} `{Eq_ a} : Eq_ (option a) := fun _ k => k {|
   op_zeze____ := fun x y =>
                  match x,y with
                  | Some x0, Some y0 => x0 == y0
                  | None, None => true
                  | _,_ => false
                  end ;
   op_zsze____ := fun x y =>
                  match x,y with
                  | Some x0, Some y0 => x0 /= y0
                  | None, None => false
                  | _,_ => true
                  end
|}.

Definition compare_option {a} `{Ord a} (xs : option a) (ys : option a) : comparison :=
  match xs, ys with
  | None, None => Eq
  | None, _    => Lt
  | _   , None => Gt
  | Some x , Some y => compare x y
  end.

Instance Ord_option {a} `{Ord a} : Ord (option a) := ord_default compare_option.


(* ********************************************************* *)
(* Some Haskell functions we cannot translate (yet)          *)


(* Pattern guards, ugh. *)
(*
Fixpoint take {a:Type} (n:Int) (xs:list a) : list a :=
  match xs with
  | nil => nil
  | y :: ys => if Z.leb n #0 then nil else (y :: take (n - #1) ys)
  end.

Fixpoint drop {a:Type} (n:Int) (xs:list a) : list a :=
  match xs with
  | nil => nil
  | y :: ys => if Z.leb n #0 then (y :: ys) else drop (n - #1) ys
  end.
*)

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

(* ?? why doesn't this work? the infix variable k ? Or needed for foldl and foldl' below *)
(* Yes, We need foldr for foldl and foldl' *)
(*
Fixpoint foldr {a}{b} (f: a -> b -> b) (z:b) (xs: list a) : b :=
  match xs with
  | nil => z
  | y :: ys => f y (foldr f z ys)
  end.
*)

Definition foldl {a}{b} k z0 xs :=
  fold_right (fun (v:a) (fn:b->b) => (fun (z:b) => fn (k z v))) (id : b -> b) xs z0.

Definition foldl' {a}{b} k z0 xs :=
  fold_right (fun(v:a) (fn:b->b) => (fun(z:b) => fn (k z v))) (id : b -> b) xs z0.

(* Less general type for build *)
Definition build {a} : ((a -> list a -> list a) -> list a -> list a) -> list a :=
  fun g => g (fun x y => x :: y) nil.

(********************************************************************)

Definition oneShot {a} (x:a) := x.
