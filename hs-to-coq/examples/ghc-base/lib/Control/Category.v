(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)


(* Converted imports: *)

Require Coq.Program.Basics.
Require GHC.Base.
Require GHC.Prim.

(* Converted declarations: *)

Local Definition instance_Category_GHC_Prim_arrow_id : forall {a},
                                                         GHC.Prim.arrow a a :=
  fun {a} => GHC.Base.id.

Local Definition instance_Category_GHC_Prim_arrow_op_z2218U__ : forall {b}
                                                                       {c}
                                                                       {a},
                                                                  GHC.Prim.arrow b c -> GHC.Prim.arrow a
                                                                  b -> GHC.Prim.arrow a c :=
  fun {b} {c} {a} => Coq.Program.Basics.compose.

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

Instance instance_Category_GHC_Prim_arrow : !Category GHC.Prim.arrow := {
  id := fun {a} => instance_Category_GHC_Prim_arrow_id ;
  op_z2218U__ := fun {b} {c} {a} =>
    instance_Category_GHC_Prim_arrow_op_z2218U__ }.

(* Unbound variables:
     Coq.Program.Basics.compose GHC.Base.id GHC.Prim.arrow
*)
