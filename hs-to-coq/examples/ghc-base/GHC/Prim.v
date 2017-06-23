(* This includes everything that should be defined in GHC/Base.hs, but cannot
   be generated from Base.hs.

The types defined in GHC.Base:

  list, (), Int, Bool, Ordering, Char, String

are all mapped to corresponding Coq types. Therefore, the Eq/Ord classes must
be defined in this module so that we can create instances for these types.

 *)

(* SSreflect library *)
Require Export mathcomp.ssreflect.ssreflect.

(********************* Types ************************)

(* List notation *)
Require Export Coq.Lists.List.

(* Booleans *)
Require Export Bool.Bool.

(* Int and Integer types *)
Require Export GHC.Num.

(* Char type *)
Require Export GHC.Char.

(* TODO: add appropriate definitions to GHC.Num and GHC.Char *)
Axiom primIntToChar      : Int -> Char.
Axiom primCharToInt      : Char -> Int.
Axiom primUnicodeMaxChar : Char.

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

Axiom primPutChar   : Char -> IO unit.
Axiom primReadFile  : String -> IO String.
Axiom primWriteFile : String -> String -> IO unit.
Axiom primGetContents : IO String.
Axiom primGetChar     : IO Char.
Axiom primCatch       : forall {a}, IO a -> (IOError -> IO a) -> IO a.
Axiom primAppendFile  : FilePath -> String -> IO unit.

(****************************************************)

(* function composition *)
Require Export Coq.Program.Basics.
Open Scope program_scope.
Notation "'_∘_'" := (compose).

Notation "[,]"  := (fun x y => (x,y)).
Notation "[,,]" := (fun x0 y1 z2 => (x0, y1, z2)).
Notation "[,,,]" := (fun x0 x1 x2 x3 => (x0,x1,x2,x3)).
Notation "[,,,,]" := (fun x0 x1 x2 x3 x4 => (x0,x1,x2,x3,x4)).
Notation "[,,,,,]" := (fun x0 x1 x2 x3 x4 x5 => (x0,x1,x2,x3,x4,x5)).
Notation "[,,,,,,]" := (fun x0 x1 x2 x3 x4 x5 x6 => (x0,x1,x2,x3,x4,x5,x6)).
Notation "[,,,,,,,]" := (fun x0 x1 x2 x3 x4 x5 x6 x7 => (x0,x1,x2,x3,x4,x5,x6,x7)).

Notation "'_++_'"   := (fun x y => x ++ y).
Notation "'_::_'"   := (fun x y => x :: y).

Notation "[->]"  := (fun x y => x -> y).

(****************************************************)


Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

(****************************************************)

Axiom primUserError : forall {A}, A.
Axiom primIOError   : forall {A}, A.
Axiom error         : forall {A : Type}, String -> A.
Axiom errorWithoutStackTrace : forall {A : Type}, String -> A.

(*********** built in classes Eq & Ord **********************)

(* Don't clash with Eq constructor for the comparison type. *)
Class Eq_ a := {
  op_zsze__ : (a -> (a -> bool)) ;
  op_zeze__ : (a -> (a -> bool)) }.

Infix "/=" := (op_zsze__) (no associativity, at level 70).

Notation "'_/=_'" := (op_zsze__).

Infix "==" := (op_zeze__) (no associativity, at level 70).

Notation "'_==_'" := (op_zeze__).


Class Ord a `{((Eq_ a))} := {
  op_zl__ : (a -> (a -> bool)) ;
  op_zlze__ : (a -> (a -> bool)) ;
  op_zg__ : (a -> (a -> bool)) ;
  op_zgze__ : (a -> (a -> bool)) ;
  compare : (a -> (a -> comparison)) ;
  max : (a -> (a -> a)) ;
  min : (a -> (a -> a)) }.

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

Instance Eq_Int___ : Eq_ Int := {
                               op_zsze__ := fun x y => (x =? y)%Z;
                               op_zeze__ := fun x y => negb (x =? y)%Z;
                             }.

Instance Ord_Int___ : Ord Int := {
  op_zl__   := fun x y => (x <? y)%Z;
  op_zlze__ := fun x y => (x <=? y)%Z;
  op_zg__   := fun x y => (y <? x)%Z;
  op_zgze__ := fun x y => (y <=? x)%Z;
  compare   := Z.compare%Z ;
  max       := Z.max%Z;
  min       := Z.min%Z;
}.

Instance Eq_Integer___ : Eq_ Integer := {
                               op_zsze__ := fun x y => (x =? y)%Z;
                               op_zeze__ := fun x y => negb (x =? y)%Z;
                             }.

Instance Ord_Integer___ : Ord Int := {
  op_zl__   := fun x y => (x <? y)%Z;
  op_zlze__ := fun x y => (x <=? y)%Z;
  op_zg__   := fun x y => (y <? x)%Z;
  op_zgze__ := fun x y => (y <=? x)%Z;
  compare   := Z.compare%Z ;
  max       := Z.max%Z;
  min       := Z.min%Z;
}.

Instance Eq_Word___ : Eq_ Word := {
                               op_zsze__ := fun x y => (x =? y)%N;
                               op_zeze__ := fun x y => negb (x =? y)%N;
                             }.

Instance Ord_Word___ : Ord Word := {
  op_zl__   := fun x y => (x <? y)%N;
  op_zlze__ := fun x y => (x <=? y)%N;
  op_zg__   := fun x y => (y <? x)%N;
  op_zgze__ := fun x y => (y <=? x)%N;
  compare   := N.compare%N ;
  max       := N.max%N;
  min       := N.min%N;
}.

Instance Eq_Char___ : Eq_ Char := {
                               op_zsze__ := fun x y => (x =? y)%N;
                               op_zeze__ := fun x y => negb (x =? y)%N;
                             }.

Instance Ord_Char___ : Ord Char := {
  op_zl__   := fun x y => (x <? y)%N;
  op_zlze__ := fun x y => (x <=? y)%N;
  op_zg__   := fun x y => (y <? x)%N;
  op_zgze__ := fun x y => (y <=? x)%N;
  compare   := N.compare%N ;
  max       := N.max%N;
  min       := N.min%N;
}.

Instance Eq_bool___ : Eq_ bool := {
                               op_zsze__ := eqb;
                               op_zeze__ := fun x y => negb (eqb x y);
                             }.

Definition compare_bool (b1:bool)(b2:bool) : comparison :=
  match b1 , b2 with
  | true , true => Eq
  | false, false => Eq
  | true , false => Lt
  | false , true => Gt
  end.


Instance Ord_bool___ : Ord bool := {
  op_zl__   := fun x y => andb (negb x) y;
  op_zlze__ := fun x y => orb (negb x) y;
  op_zg__   := fun x y => orb (negb y) x;
  op_zgze__ := fun x y => andb (negb y) x;
  compare   := compare_bool;
  max       := orb;
  min       := andb
}.

Instance Eq_unit___ : Eq_ unit := {
                               op_zsze__ := fun x y => true;
                               op_zeze__ := fun x y => false;
                             }.

Instance Ord_unit___ : Ord unit := {
  op_zl__   := fun x y => false;
  op_zlze__ := fun x y => true;
  op_zg__   := fun x y => false;
  op_zgze__ := fun x y => true;
  compare   := fun x y => Eq ;
  max       := fun x y => tt;
  min       := fun x y => tt;
}.

Definition eq_comparison (x : comparison) (y: comparison) :=
  match x , y with
  | Eq, Eq => true
  | Gt, Gt => true
  | Lt, Lt => true
  | _ , _  => false
end.

Instance Eq_comparison___ : Eq_ comparison :=
{
  op_zsze__ := eq_comparison;
  op_zeze__ := fun x y => negb (eq_comparison x y);
}.

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
  Build_Ord _ _
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
             end).

Instance Ord_comparison___ : Ord comparison := ord_default compare_comparison.


(* TODO: are these available in a library somewhere? *)
Fixpoint eqlist {a} `{Eq_ a} (xs :  list a) (ys : list a) : bool :=
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

Instance Eq_list {a} `{Eq_ a} : Eq_ (list a) :=
  { op_zsze__ := fun x y => true;
    op_zeze__ := fun x y => false;
  }.

Instance Ord_list {a} `{Ord a}: Ord (list a) :=
  ord_default compare_list.

(* ********************************************************* *)
(* Some Haskell functions we cannot translate (yet)          *)


(* Pattern guards, ugh. *)
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
Fixpoint foldr {a}{b} (f: a -> b -> b) (z:b) (xs: list a) : b :=
  match xs with
  | nil => z
  | y :: ys => f y (foldr f z ys)
  end.

Definition foldl {a}{b} k z0 xs :=
  foldr (fun (v:a) (fn:b->b) => (fun (z:b) => fn (k z v))) (id : b -> b) xs z0.

Definition foldl' {a}{b} k z0 xs :=
  foldr (fun(v:a) (fn:b->b) => (fun(z:b) => fn (k z v))) (id : b -> b) xs z0.

Definition concatMap {a}{b} (f : a -> list b) : list a -> list b :=
  foldr (compose (_++_) f) nil.

Definition build {a} : (forall {b},(a -> b -> b) -> b -> b) -> list a :=
  fun g => g _ (fun x y => x :: y) nil.


(********************************************************************)

Definition seq {A} {B} (a : A) (b:B) := b.

Definition oneShot {a} (x:a) := x.
