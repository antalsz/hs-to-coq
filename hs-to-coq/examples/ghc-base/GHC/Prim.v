(* This includes everything that should be defined in GHC/Base.hs, but is not. *)

(* SSreflect library *)
Require Export mathcomp.ssreflect.ssreflect.


(* List notation *)
Require Export Coq.Lists.List.

Notation "'_(,)_'"  := (fun x y => (x,y)).
Notation "'_(,,)_'" := (fun x y z => (x, y, z)).
Notation "'_++_'"   := (fun x y => x ++ y).
Notation "'_::_'"   := (fun x y => x :: y).

(* Int and Integer types *)
Require Export GHC.Num.

(* Char type *)
Require Export GHC.Char.


(****************************************************)

Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

(****************************************************)

Axiom primUserError : forall {A}, A.
Axiom primIOError   : forall {A}, A.

(*********** built in classes ***********************)

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

Infix "<?" := (op_zl__) (no associativity, at level 70).

Notation "'_<?_'" := (op_zl__).

Infix "<=?" := (op_zlze__) (no associativity, at level 70).

Notation "'_<=?_'" := (op_zlze__).

Infix ">?" := (op_zg__) (no associativity, at level 70).

Notation "'_>?_'" := (op_zg__).

Infix ">=?" := (op_zgze__) (no associativity, at level 70).

Notation "'_>=?_'" := (op_zgze__).

(*********** Eq/Ord for Int**************************)

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


(* ********************************************************* *)
(* Some Haskell functions we cannot translate                *)


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

Fixpoint foldr {a}{b} (f: a -> b -> b) (z:b) (xs: list a) : b :=
  match xs with
  | nil => z
  | y :: ys => f y (foldr f z ys)
  end.

Definition foldl {a}{b} k z0 xs :=
  foldr (fun (v:a) (fn:b->b) => (fun (z:b) => fn (k z v))) (id : b -> b) xs z0.

Definition foldl' {a}{b} k z0 xs :=
  foldr (fun(v:a) (fn:b->b) => (fun(z:b) => fn (k z v))) (id : b -> b) xs z0.

(********************************************************************)

(* Strings *)

Definition String := list Char.

Require Coq.Strings.String.

Bind Scope string_scope with String.string.

Fixpoint hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: hs_string__ s
  end.
Notation "'&' s" := (hs_string__ s) (at level 1, format "'&' s").

(********************************************************************)

Axiom error : forall {A : Type}, String -> A.
Axiom errorWithoutStackTrace : forall {A : Type}, String -> A.

(********************************************************************)

(* I've been assured that this is OK *)
Inductive IO (a : Type) : Type :=.
Inductive IORef (a : Type) : Type :=.
Inductive IOError : Type :=.

Definition FilePath := String.

Axiom primIntToChar      : Int -> Char.
Axiom primCharToInt      : Char -> Int.
Axiom primUnicodeMaxChar : Char.

Axiom primPutChar   : Char -> IO unit.
Axiom primReadFile  : String -> IO String.
Axiom primWriteFile : String -> String -> IO unit.
Axiom primGetContents : IO String.
Axiom primGetChar     : IO Char.
Axiom primCatch       : forall {a}, IO a -> (IOError -> IO a) -> IO a.
Axiom primAppendFile  : FilePath -> String -> IO unit.


Definition oneShot {a} (x:a) := x.