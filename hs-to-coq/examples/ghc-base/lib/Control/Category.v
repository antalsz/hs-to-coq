(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)


(* Converted imports: *)

Require GHC.Base.
Require Data.Type.Coercion.
Require Data.Type.Equality.

(* Converted declarations: *)

(* Skipping instance instance_Category_GHC_Prim_____ *)

(* Skipping instance instance_Category_Data_Type_Equality____ *)

(* Skipping instance instance_Category_Data_Type_Coercion_Coercion *)

Class Category (cat : Type -> Type -> Type) := {
  id : forall {a}, cat a a ;
  op_z2218U__ : forall {b} {c} {a}, cat b c -> cat a b -> cat a c }.

Infix "∘" := (op_z2218U__) (left associativity, at level 40).

Notation "'_∘_'" := (op_z2218U__).

Definition op_zlzlzl__ {cat} {b} {c} {a} `{Category cat} : cat b c -> cat a
                                                           b -> cat a c :=
  op_z2218U__.

Infix "<<<" := (op_zlzlzl__) (at level 99).

Notation "'_<<<_'" := (op_zlzlzl__).

Definition op_zgzgzg__ {cat} {a} {b} {c} `{Category cat} : cat a b -> cat b
                                                           c -> cat a c :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , g => op_z2218U__ g f
    end.

Infix ">>>" := (op_zgzgzg__) (at level 99).

Notation "'_>>>_'" := (op_zgzgzg__).
