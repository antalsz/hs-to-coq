Require Export Coq.Lists.List.
Require Export ZArith.

Definition Int : Type := Z.


Inductive Ordering : Type := Mk_LT : Ordering
                          |  Mk_EQ : Ordering
                          |  Mk_GT : Ordering.

Class Eq (a : Type) := {
  op_zeze__ : a -> a -> bool;
  op_zsze__ : a -> a -> bool
}.

Infix "==" := op_zeze__ (at level 99).
Infix "/=" := op_zsze__ (at level 99).

Notation "'_==_'" := op_zeze__.
Notation "'_/=_'" := op_zsze__.

Class Ord `{Eq a} := {
  compare : a -> a -> Ordering;

  op_zl__   : a -> a -> bool;
  op_zlze__ : a -> a -> bool;
  op_zg__   : a -> a -> bool;
  op_zgze__ : a -> a -> bool;

  max : a -> a -> a;
  min : a -> a -> a
}.
Arguments Ord _ {_}.

Infix "<?"  := op_zl__   (at level 70).
Infix "<=?" := op_zlze__ (at level 70).
Infix ">?"  := op_zg__   (at level 70).
Infix ">=?" := op_zgze__ (at level 70).

Class Num a := {
  op_zp__   : a -> a -> a ;
  op_zm__   : a -> a -> a ;
  op_zt__   : a -> a -> a ;
  abs         : a -> a ;
  fromInteger : Z -> a ;
  negate      : a -> a ;
  signum      : a -> a
}.

Infix    "+"     := op_zp__ (at level 50, left associativity).
Notation "'_+_'" := op_zp__.

Infix    "-"     := op_zm__ (at level 50, left associativity).
Notation "'_-_'" := op_zm__.

Infix    "*"     := op_zt__ (at level 40, left associativity).
Notation "'_*_'" := op_zt__.

Instance __Eq_Int__  : Eq  Int. Admitted.
Instance __Ord_Int__ : Ord Int. Admitted.
Instance __Num_Int__ : Num Int. Admitted.

Instance __Eq_Z__  : Eq  Z. Admitted.
Instance __Ord_Z__ : Ord Z. Admitted.
Instance __Num_Z__ : Num Z. Admitted.


Notation "'#' n" := (fromInteger n) (at level 1, format "'#' n").
