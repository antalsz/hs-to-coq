(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require MySet.

(* Converted type declarations: *)

Inductive SetExt : Type -> Type
  := | Empty : forall {a}, SetExt a
  |  Singleton : forall {a}, a -> SetExt a
  |  Add : forall {a}, forall `{GHC.Base.Eq_ a}, a -> SetExt a -> SetExt a
  |  Union
   : forall {a}, forall `{GHC.Base.Eq_ a}, SetExt a -> SetExt a -> SetExt a
  |  PowerSet : forall {a}, SetExt a -> SetExt (MySet.Set_ a).

(* Converted value declarations: *)

Definition union {a} `{GHC.Base.Eq_ a} : SetExt a -> SetExt a -> SetExt a :=
  Union.

Definition singleton {a} : a -> SetExt a :=
  Singleton.

Definition powerSet {a} : SetExt a -> SetExt (MySet.Set_ a) :=
  PowerSet.

Fixpoint interp_ext {a} (arg_0__ : SetExt a) : MySet.Set_ a
           := match arg_0__ with
              | Empty => MySet.empty
              | Singleton a => MySet.singleton a
              | Add a s => MySet.add a (interp_ext s)
              | Union s1 s2 => MySet.union (interp_ext s1) (interp_ext s2)
              | PowerSet s => MySet.powerSet (interp_ext s)
              end.

Definition member {a} `{GHC.Base.Eq_ a} : a -> SetExt a -> bool :=
  fun a s => MySet.member a (interp_ext s).

Definition empty {a} : SetExt a :=
  Empty.

Definition add {a} `{GHC.Base.Eq_ a} : a -> SetExt a -> SetExt a :=
  Add.

(* External variables:
     Type bool GHC.Base.Eq_ MySet.Set_ MySet.add MySet.empty MySet.member
     MySet.powerSet MySet.singleton MySet.union
*)
