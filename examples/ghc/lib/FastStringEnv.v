(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require FastString.
Require UniqFM.
Require Unique.

(* Converted type declarations: *)

Definition FastStringEnv :=
  UniqFM.UniqFM%type.
(* Converted value declarations: *)

Definition alterFsEnv {a}
   : (option a -> option a) ->
     FastStringEnv a -> FastString.FastString -> FastStringEnv a :=
  UniqFM.alterUFM.

Definition delFromFsEnv {a}
   : FastStringEnv a -> FastString.FastString -> FastStringEnv a :=
  fun x y => UniqFM.delFromUFM x y.

Definition delListFromFsEnv {a}
   : FastStringEnv a -> list FastString.FastString -> FastStringEnv a :=
  fun x y => UniqFM.delListFromUFM x y.

Definition elemFsEnv {a} : FastString.FastString -> FastStringEnv a -> bool :=
  fun x y => UniqFM.elemUFM x y.

Definition emptyFsEnv {a} : FastStringEnv a :=
  UniqFM.emptyUFM.

Definition extendFsEnv {a}
   : FastStringEnv a -> FastString.FastString -> a -> FastStringEnv a :=
  fun x y z => UniqFM.addToUFM x y z.

Definition extendFsEnvList {a}
   : FastStringEnv a ->
     list (FastString.FastString * a)%type -> FastStringEnv a :=
  fun x l => UniqFM.addListToUFM x l.

Definition extendFsEnvList_C {a}
   : (a -> a -> a) ->
     FastStringEnv a -> list (FastString.FastString * a)%type -> FastStringEnv a :=
  fun x y z => UniqFM.addListToUFM_C x y z.

Definition extendFsEnv_Acc {a} {b}
   : (a -> b -> b) ->
     (a -> b) -> FastStringEnv b -> FastString.FastString -> a -> FastStringEnv b :=
  fun x y z a b => UniqFM.addToUFM_Acc x y z a b.

Definition extendFsEnv_C {a}
   : (a -> a -> a) ->
     FastStringEnv a -> FastString.FastString -> a -> FastStringEnv a :=
  fun f x y z => UniqFM.addToUFM_C f x y z.

Definition filterFsEnv {elt}
   : (elt -> bool) -> FastStringEnv elt -> FastStringEnv elt :=
  fun x y => UniqFM.filterUFM x y.

Definition foldFsEnv {a} {b} : (a -> b -> b) -> b -> FastStringEnv a -> b :=
  fun a b c => UniqFM.foldUFM a b c.

Definition fsEnvElts {a} : FastStringEnv a -> list a :=
  fun x => UniqFM.eltsUFM x.

Definition fsEnvUniqueElts {a}
   : FastStringEnv a -> list (Unique.Unique * a)%type :=
  fun x => UniqFM.ufmToList x.

Definition lookupFsEnv {a}
   : FastStringEnv a -> FastString.FastString -> option a :=
  fun x y => UniqFM.lookupUFM x y.

Definition mapFsEnv {elt1} {elt2}
   : (elt1 -> elt2) -> FastStringEnv elt1 -> FastStringEnv elt2 :=
  fun f x => UniqFM.mapUFM f x.

Definition mkFsEnv {a}
   : list (FastString.FastString * a)%type -> FastStringEnv a :=
  fun l => UniqFM.listToUFM l.

Definition plusFsEnv {a}
   : FastStringEnv a -> FastStringEnv a -> FastStringEnv a :=
  fun x y => UniqFM.plusUFM x y.

Definition plusFsEnv_C {a}
   : (a -> a -> a) -> FastStringEnv a -> FastStringEnv a -> FastStringEnv a :=
  fun f x y => UniqFM.plusUFM_C f x y.

Definition unitFsEnv {a} : FastString.FastString -> a -> FastStringEnv a :=
  fun x y => UniqFM.unitUFM x y.

(* Unbound variables:
     bool list op_zt__ option FastString.FastString UniqFM.UniqFM UniqFM.addListToUFM
     UniqFM.addListToUFM_C UniqFM.addToUFM UniqFM.addToUFM_Acc UniqFM.addToUFM_C
     UniqFM.alterUFM UniqFM.delFromUFM UniqFM.delListFromUFM UniqFM.elemUFM
     UniqFM.eltsUFM UniqFM.emptyUFM UniqFM.filterUFM UniqFM.foldUFM UniqFM.listToUFM
     UniqFM.lookupUFM UniqFM.mapUFM UniqFM.plusUFM UniqFM.plusUFM_C UniqFM.ufmToList
     UniqFM.unitUFM Unique.Unique
*)
