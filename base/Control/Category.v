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

Require Data.Type.Equality.
Require GHC.Base.
Require GHC.Prim.
Import Data.Type.Equality.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Record Category__Dict (cat : Type -> Type -> Type) := Category__Dict_Build {
  id__ : forall {a}, cat a a ;
  op_z2218U____ : forall {b} {c} {a}, cat b c -> cat a b -> cat a c }.

Definition Category (cat : Type -> Type -> Type) :=
  forall r, (Category__Dict cat -> r) -> r.

Existing Class Category.

Definition id `{g : Category cat} : forall {a}, cat a a :=
  g _ (id__ cat).

Definition op_z2218U__ `{g : Category cat}
   : forall {b} {c} {a}, cat b c -> cat a b -> cat a c :=
  g _ (op_z2218U____ cat).

Notation "'_∘_'" := (op_z2218U__).

Infix "∘" := (_∘_) (left associativity, at level 40).
(* Converted value declarations: *)

Local Definition Category__arrow_id : forall {a}, GHC.Prim.arrow a a :=
  fun {a} => GHC.Base.id.

Local Definition Category__arrow_op_z2218U__
   : forall {b} {c} {a},
     GHC.Prim.arrow b c -> GHC.Prim.arrow a b -> GHC.Prim.arrow a c :=
  fun {b} {c} {a} => _GHC.Base.∘_.

Program Instance Category__arrow : Category GHC.Prim.arrow :=
  fun _ k =>
    k {| id__ := fun {a} => Category__arrow_id ;
         op_z2218U____ := fun {b} {c} {a} => Category__arrow_op_z2218U__ |}.

(* Skipping instance Category__op_ZCz7eUZC__ *)

Local Definition Category__op_ZCz7eUz7eUZC___id
   : forall {a}, _Data.Type.Equality.:~~:_ a a :=
  fun {a} => Data.Type.Equality.HRefl.

Local Definition Category__op_ZCz7eUz7eUZC___op_z2218U__
   : forall {b} {c} {a},
     _Data.Type.Equality.:~~:_ b c ->
     _Data.Type.Equality.:~~:_ a b -> _Data.Type.Equality.:~~:_ a c :=
  fun {b} {c} {a} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Data.Type.Equality.HRefl, Data.Type.Equality.HRefl => Data.Type.Equality.HRefl
      end.

Program Instance Category__op_ZCz7eUz7eUZC__
   : Category _Data.Type.Equality.:~~:_ :=
  fun _ k =>
    k {| id__ := fun {a} => Category__op_ZCz7eUz7eUZC___id ;
         op_z2218U____ := fun {b} {c} {a} => Category__op_ZCz7eUz7eUZC___op_z2218U__ |}.

(* Skipping instance Category__Coercion *)

Definition op_zgzgzg__ {cat} {a} {b} {c} `{Category cat}
   : cat a b -> cat b c -> cat a c :=
  fun f g => g ∘ f.

Notation "'_>>>_'" := (op_zgzgzg__).

Infix ">>>" := (_>>>_) (at level 99).

Definition op_zlzlzl__ {cat} {b} {c} {a} `{Category cat}
   : cat b c -> cat a b -> cat a c :=
  _∘_.

Notation "'_<<<_'" := (op_zlzlzl__).

Infix "<<<" := (_<<<_) (at level 99).

Module Notations.
Notation "'_Control.Category.∘_'" := (op_z2218U__).
Infix "Control.Category.∘" := (_∘_) (left associativity, at level 40).
Notation "'_Control.Category.>>>_'" := (op_zgzgzg__).
Infix "Control.Category.>>>" := (_>>>_) (at level 99).
Notation "'_Control.Category.<<<_'" := (op_zlzlzl__).
Infix "Control.Category.<<<" := (_<<<_) (at level 99).
End Notations.

(* Unbound variables:
     Type Data.Type.Equality.HRefl Data.Type.Equality.op_ZCz7eUz7eUZC__ GHC.Base.id
     GHC.Base.op_z2218U__ GHC.Prim.arrow
*)
