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
Require Name.
Require UniqFM.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition NameEnv :=
  UniqFM.UniqFM%type.

Definition DNameEnv :=
  UniqFM.UniqFM%type.

(* Converted value declarations: *)

(* Skipping definition `NameEnv.depAnal' *)

Definition nameEnvElts {a} : NameEnv a -> list a :=
  fun x => UniqFM.eltsUFM x.

Definition emptyNameEnv {a} : NameEnv a :=
  UniqFM.emptyUFM.

Definition isEmptyNameEnv {a} : NameEnv a -> bool :=
  UniqFM.isNullUFM.

Definition unitNameEnv {a} : Name.Name -> a -> NameEnv a :=
  fun x y => UniqFM.unitUFM x y.

Definition extendNameEnv {a} : NameEnv a -> Name.Name -> a -> NameEnv a :=
  fun x y z => UniqFM.addToUFM x y z.

Definition extendNameEnvList {a}
   : NameEnv a -> list (Name.Name * a)%type -> NameEnv a :=
  fun x l => UniqFM.addListToUFM x l.

Definition lookupNameEnv {a} : NameEnv a -> Name.Name -> option a :=
  fun x y => UniqFM.lookupUFM x y.

Definition alterNameEnv {a}
   : (option a -> option a) -> NameEnv a -> Name.Name -> NameEnv a :=
  UniqFM.alterUFM.

Definition mkNameEnv {a} : list (Name.Name * a)%type -> NameEnv a :=
  fun l => UniqFM.listToUFM l.

Definition elemNameEnv {a} : Name.Name -> NameEnv a -> bool :=
  fun x y => UniqFM.elemUFM x y.

Definition plusNameEnv {a} : NameEnv a -> NameEnv a -> NameEnv a :=
  fun x y => UniqFM.plusUFM x y.

Definition plusNameEnv_C {a}
   : (a -> a -> a) -> NameEnv a -> NameEnv a -> NameEnv a :=
  fun f x y => UniqFM.plusUFM_C f x y.

Definition extendNameEnv_C {a}
   : (a -> a -> a) -> NameEnv a -> Name.Name -> a -> NameEnv a :=
  fun f x y z => UniqFM.addToUFM_C f x y z.

Definition mapNameEnv {elt1} {elt2}
   : (elt1 -> elt2) -> NameEnv elt1 -> NameEnv elt2 :=
  fun f x => UniqFM.mapUFM f x.

Definition extendNameEnv_Acc {a} {b}
   : (a -> b -> b) -> (a -> b) -> NameEnv b -> Name.Name -> a -> NameEnv b :=
  fun x y z a b => UniqFM.addToUFM_Acc x y z a b.

Definition extendNameEnvList_C {a}
   : (a -> a -> a) -> NameEnv a -> list (Name.Name * a)%type -> NameEnv a :=
  fun x y z => UniqFM.addListToUFM_C x y z.

Definition delFromNameEnv {a} : NameEnv a -> Name.Name -> NameEnv a :=
  fun x y => UniqFM.delFromUFM x y.

Definition delListFromNameEnv {a} : NameEnv a -> list Name.Name -> NameEnv a :=
  fun x y => UniqFM.delListFromUFM x y.

Definition filterNameEnv {elt} : (elt -> bool) -> NameEnv elt -> NameEnv elt :=
  fun x y => UniqFM.filterUFM x y.

Definition anyNameEnv {elt} : (elt -> bool) -> NameEnv elt -> bool :=
  fun f x => UniqFM.foldUFM (orb GHC.Base.∘ f) false x.

Definition disjointNameEnv {a} : NameEnv a -> NameEnv a -> bool :=
  fun x y => UniqFM.isNullUFM (UniqFM.intersectUFM x y).

(* Skipping definition `NameEnv.lookupNameEnv_NF' *)

Definition emptyDNameEnv {a} : DNameEnv a :=
  UniqFM.emptyUFM.

Definition lookupDNameEnv {a} : DNameEnv a -> Name.Name -> option a :=
  UniqFM.lookupUFM.

Definition mapDNameEnv {a} {b} : (a -> b) -> DNameEnv a -> DNameEnv b :=
  UniqFM.mapUFM.

Definition alterDNameEnv {a}
   : (option a -> option a) -> DNameEnv a -> Name.Name -> DNameEnv a :=
  UniqFM.alterUFM.

(* External variables:
     bool false list op_zt__ option orb GHC.Base.op_z2218U__ Name.Name UniqFM.UniqFM
     UniqFM.addListToUFM UniqFM.addListToUFM_C UniqFM.addToUFM UniqFM.addToUFM_Acc
     UniqFM.addToUFM_C UniqFM.alterUFM UniqFM.delFromUFM UniqFM.delListFromUFM
     UniqFM.elemUFM UniqFM.eltsUFM UniqFM.emptyUFM UniqFM.filterUFM UniqFM.foldUFM
     UniqFM.intersectUFM UniqFM.isNullUFM UniqFM.listToUFM UniqFM.lookupUFM
     UniqFM.mapUFM UniqFM.plusUFM UniqFM.plusUFM_C UniqFM.unitUFM
*)
