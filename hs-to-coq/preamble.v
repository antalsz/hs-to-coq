Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

Require Import ZArith.

Axiom Char     : Type.
Axiom Int      : Type.
Axiom Rational : Type.

Definition String     := list Char.
Definition FilePath   := String.

(* Temporary *)
Record Array  k v := ListToArray  { arrayToList  : list (k * v) }.
Record Set_     a := ListToSet    { setToList    : list a }.
Record Map    k v := ListToMap    { mapToList    : list (k * v) }.
Record IntSet     := ListToIntSet { intSetToList : list Int }.
Record IntMap   v := ListToIntMap { intMapToList : list (Int * v) }.

Axiom error : forall {A : Type}, String -> A.

(* Do we really need the definition of this?  It's a special error with
   formatting. *)
Axiom panic : forall {A : Type}, String -> A.

(* I've been assured that this is OK *)
Inductive IORef (a : Type) : Type :=.

(* List notation *)
Require Import Coq.Lists.List.

(* Temporary – but will probably need to be handled specially *)
Axiom DynFlags : Type.
Axiom wORD_SIZE       : DynFlags -> Int.
Axiom tARGET_MAX_WORD : DynFlags -> Z.
Axiom tARGET_MAX_INT  : DynFlags -> Z.

(* Temporary – this probably needs to map directly to a Coq type *)
Axiom ByteString : Type.

(* All we currently need from IdInfo. *)
Module IdInfo.

  Definition Arity     : Type := Int.
  Definition ArityInfo : Type := Int.
   
  Parameter IdInfo : Type.
  Parameter vanillaIdInfo : IdInfo.
   
  Parameter unknownArity  : Arity.
   
  Parameter arityInfo     : IdInfo -> ArityInfo.
  Parameter callArityInfo : IdInfo -> ArityInfo.
   
  Parameter setArityInfo     : IdInfo -> ArityInfo -> IdInfo.
  Parameter setCallArityInfo : IdInfo -> ArityInfo -> IdInfo.
   
  Axiom arityInfo_vanillaIdInfo : arityInfo vanillaIdInfo = unknownArity.
  Axiom callArityInfo_vanillaIdInfo : callArityInfo vanillaIdInfo = unknownArity.
   
  Axiom arityInfo_read_write  : forall i a,    arityInfo (setArityInfo i a) = a.
  Axiom arityInfo_write_read  : forall i,      setArityInfo i (arityInfo i) = i.
  Axiom arityInfo_write_write : forall i a a', setArityInfo (setArityInfo i a) a' = setArityInfo i a'.
   
  Axiom callArityInfo_read_write  : forall i a,    callArityInfo (setArityInfo i a) = a.
  Axiom callArityInfo_write_read  : forall i,      setArityInfo i (callArityInfo i) = i.
  Axiom callArityInfo_write_write : forall i a a', setArityInfo (setArityInfo i a) a' = setArityInfo i a'.

End IdInfo.

Import IdInfo.

(********************************************************************************)

(* Haskell Prelude stuff – this needs to be automated *)

Inductive Ordering : Type := Mk_LT : Ordering
                          |  Mk_EQ : Ordering
                          |  Mk_GT : Ordering.

Class Eq (a : Type) := {
  __op_zeze__ : a -> a -> bool;
  __op_zsze__ : a -> a -> bool
}.

Infix "==" := __op_zeze__ (at level 99).
Infix "/=" := __op_zsze__ (at level 99).

Notation "'_==_'" := __op_zeze__.
Notation "'_/=_'" := __op_zsze__.

Class Ord `{Eq a} := {
  compare : a -> a -> Ordering;
  
  __op_zl__   : a -> a -> bool;
  __op_zlze__ : a -> a -> bool;
  __op_zg__   : a -> a -> bool;
  __op_zgze__ : a -> a -> bool;
  
  max : a -> a -> a;
  min : a -> a -> a
}.
Arguments Ord _ {_}.

Infix "<"  := __op_zl__   (at level 70).
Infix "<=" := __op_zlze__ (at level 70).
Infix ">"  := __op_zg__   (at level 70).
Infix ">=" := __op_zgze__ (at level 70).

Notation "'_<_'"  := __op_zl__.
Notation "'_<=_'" := __op_zlze__.
Notation "'_>_'"  := __op_zg__.
Notation "'_>=_'" := __op_zgze__.

Class Functor (f : Type -> Type) := {
  fmap : forall {a b}, (a -> b) -> f a -> f b;
  __op_zlzd__ : forall {a b}, a -> f b -> f a
}.

Infix "<$"        := __op_zlzd__ (at level 99).

Notation "'_<$_'" := __op_zlzd__.
Infix "<$>"        := fmap (at level 99).
Notation "'_<$>_'" := fmap.

Class Applicative (f : Type -> Type) `{Functor f} := {
  pure          : forall {a},   a -> f a;
  op_zlztzg__ : forall {a b}, f (a -> b) -> f a -> f b;
  op_ztzg__   : forall {a b}, f a -> f b -> f b;
  op_zlzt__   : forall {a b}, f a -> f b -> f a
}.

Infix "<*>" := op_zlztzg__ (at level 99).
Infix "*>"  := op_ztzg__   (at level 99).
Infix "<*"  := op_zlzt__   (at level 99).

Notation "'_<*>_'" := op_zlztzg__.
Notation "'_*>_'"  := op_ztzg__.
Notation "'_<*_'"  := op_zlzt__.

Class Monad (m : Type -> Type) `{Applicative m} := {
  __op_zgzgze__ : forall {a b}, m a -> (a -> m b) -> m b;
  __op_zgzg__   : forall {a b}, m a -> m b -> m b;
  return_       : forall {a},   a -> m a;
  fail          : forall {a},   String -> m a
}.

Infix ">>=" := __op_zgzgze__ (at level 99).
Infix ">>"  := __op_zgzg__   (at level 99).

Notation "'_>>=_'" := __op_zgzgze__.
Notation "'_>>_'"  := __op_zgzg__.

Class Monoid (a : Type) := {
  mempty   : a;
  mappend  : a -> a -> a
}.

Class Foldable (t : Type -> Type) := {
  foldMap : forall {a m} `{Monoid m}, (a -> m) -> t a -> m
}.

Class Traversable (t : Type -> Type) `{Functor t} `{Foldable t}  := {
  traverse : forall {a b f} `{Applicative f}, (a -> f b) -> t a -> f (t b)
}.


Class Num a := {
  __op_zp__   : a -> a -> a ;
  __op_zm__   : a -> a -> a ;
  __op_zt__   : a -> a -> a ;
  abs         : a -> a ;
  fromInteger : Z -> a ;
  negate      : a -> a ;
  signum      : a -> a
}.

Infix    "+"     := __op_zp__ (at level 50, left associativity).
Notation "'_+_'" := __op_zp__.

Infix    "-"     := __op_zm__ (at level 50, left associativity).
Notation "'_-_'" := __op_zm__.

Infix    "*"     := __op_zt__ (at level 40, left associativity).
Notation "'_*_'" := __op_zt__.

(********************************************************************)

(* FastString *)

Record FastString := Mk_FS { unpackFS : String }.

Definition __with_fs__ {A : Type} (f : String -> A) (fs : FastString) : A :=
  match fs with Mk_FS s => f s end.
 
Definition fsLit        : String -> FastString := Mk_FS.
Definition mkFastString : String -> FastString := Mk_FS.

(* Can add more *)

(********************************************************************)

(* Fancy notation *)

Notation "'#' n" := (fromInteger n) (at level 1, format "'#' n").

Require Coq.Strings.String.
Require Coq.Strings.Ascii.

Bind Scope string_scope with String.string.
Bind Scope char_scope   with Ascii.ascii.

Axiom __hs_char__ : Ascii.ascii -> Char.
Notation "'&#' c" := (__hs_char__ c) (at level 1, format "'&#' c").

Fixpoint __hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: __hs_string__ s
  end.
Notation "'&' s" := (__hs_string__ s) (at level 1, format "'&' s").

(********************************************************************)

(* Instances *)

Instance __Eq_Int__  : Eq  Int. Admitted.
Instance __Ord_Int__ : Ord Int. Admitted.
Instance __Num_Int__ : Num Int. Admitted.

Instance __Eq_Z__  : Eq  Z. Admitted.
Instance __Ord_Z__ : Ord Z. Admitted.
Instance __Num_Z__ : Num Z. Admitted.
