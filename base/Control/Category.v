(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require Coq.Program.Basics.
Require GHC.Base.
Require GHC.Prim.

(* Converted type declarations: *)

Record Category__Dict (cat : Type -> Type -> Type) := Category__Dict_Build {
  id__ : forall {a}, cat a a ;
  op_z2218U____ : forall {b} {c} {a}, cat b c -> cat a b -> cat a c }.

Definition Category (cat : Type -> Type -> Type) :=
  forall r, (Category__Dict cat -> r) -> r.

Existing Class Category.

Definition id `{g : Category cat} : forall {a}, cat a a :=
  g _ (id__ cat).

Definition op_z2218U__ `{g : Category cat} : forall {b} {c} {a},
                                               cat b c -> cat a b -> cat a c :=
  g _ (op_z2218U____ cat).

Infix "∘" := (op_z2218U__) (left associativity, at level 40).

Notation "'_∘_'" := (op_z2218U__).
(* Converted value declarations: *)

Local Definition instance_Category_GHC_Prim_arrow_id : forall {a},
                                                         GHC.Prim.arrow a a :=
  fun {a} => GHC.Base.id.

Local Definition instance_Category_GHC_Prim_arrow_op_z2218U__ : forall {b}
                                                                       {c}
                                                                       {a},
                                                                  GHC.Prim.arrow b c -> GHC.Prim.arrow a
                                                                  b -> GHC.Prim.arrow a c :=
  fun {b} {c} {a} => Coq.Program.Basics.compose.

Program Instance instance_Category_GHC_Prim_arrow : Category GHC.Prim.arrow :=
  fun _ k =>
    k {|id__ := fun {a} => instance_Category_GHC_Prim_arrow_id ;
      op_z2218U____ := fun {b} {c} {a} =>
        instance_Category_GHC_Prim_arrow_op_z2218U__ |}.

(* Skipping instance instance_Category_Data_Type_Equality____ *)

(* Skipping instance instance_Category_Data_Type_Coercion_Coercion *)

Definition op_zgzgzg__ {cat} {a} {b} {c} `{Category cat} : cat a b -> cat b
                                                           c -> cat a c :=
  fun f g => op_z2218U__ g f.

Infix ">>>" := (op_zgzgzg__) (at level 99).

Notation "'_>>>_'" := (op_zgzgzg__).

Definition op_zlzlzl__ {cat} {b} {c} {a} `{Category cat} : cat b c -> cat a
                                                           b -> cat a c :=
  op_z2218U__.

Infix "<<<" := (op_zlzlzl__) (at level 99).

Notation "'_<<<_'" := (op_zlzlzl__).

(* Unbound variables:
     Coq.Program.Basics.compose GHC.Base.id GHC.Prim.arrow Type
*)
