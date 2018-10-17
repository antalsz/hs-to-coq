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
Require UniqDFM.
Require UniqFM.

(* Converted type declarations: *)

Definition FastStringEnv :=
  UniqFM.UniqFM%type.

Definition DFastStringEnv :=
  UniqDFM.UniqDFM%type.
(* Converted value declarations: *)

Definition unitFsEnv {a} : FastString.FastString -> a -> FastStringEnv a :=
  fun x y => UniqFM.unitUFM x y.

Definition plusFsEnv_C {a}
   : (a -> a -> a) -> FastStringEnv a -> FastStringEnv a -> FastStringEnv a :=
  fun f x y => UniqFM.plusUFM_C f x y.

Definition plusFsEnv {a}
   : FastStringEnv a -> FastStringEnv a -> FastStringEnv a :=
  fun x y => UniqFM.plusUFM x y.

Definition mkFsEnv {a}
   : list (FastString.FastString * a)%type -> FastStringEnv a :=
  fun l => UniqFM.listToUFM l.

Definition mkDFsEnv {a}
   : list (FastString.FastString * a)%type -> DFastStringEnv a :=
  fun l => UniqDFM.listToUDFM l.

Definition mapFsEnv {elt1} {elt2}
   : (elt1 -> elt2) -> FastStringEnv elt1 -> FastStringEnv elt2 :=
  fun f x => UniqFM.mapUFM f x.

Definition lookupFsEnv {a}
   : FastStringEnv a -> FastString.FastString -> option a :=
  fun x y => UniqFM.lookupUFM x y.

Definition lookupDFsEnv {a}
   : DFastStringEnv a -> FastString.FastString -> option a :=
  UniqDFM.lookupUDFM.

Definition filterFsEnv {elt}
   : (elt -> bool) -> FastStringEnv elt -> FastStringEnv elt :=
  fun x y => UniqFM.filterUFM x y.

Definition extendFsEnv_C {a}
   : (a -> a -> a) ->
     FastStringEnv a -> FastString.FastString -> a -> FastStringEnv a :=
  fun f x y z => UniqFM.addToUFM_C f x y z.

Definition extendFsEnv_Acc {a} {b}
   : (a -> b -> b) ->
     (a -> b) -> FastStringEnv b -> FastString.FastString -> a -> FastStringEnv b :=
  fun x y z a b => UniqFM.addToUFM_Acc x y z a b.

Definition extendFsEnvList_C {a}
   : (a -> a -> a) ->
     FastStringEnv a -> list (FastString.FastString * a)%type -> FastStringEnv a :=
  fun x y z => UniqFM.addListToUFM_C x y z.

Definition extendFsEnvList {a}
   : FastStringEnv a ->
     list (FastString.FastString * a)%type -> FastStringEnv a :=
  fun x l => UniqFM.addListToUFM x l.

Definition extendFsEnv {a}
   : FastStringEnv a -> FastString.FastString -> a -> FastStringEnv a :=
  fun x y z => UniqFM.addToUFM x y z.

Definition emptyFsEnv {a} : FastStringEnv a :=
  UniqFM.emptyUFM.

Definition emptyDFsEnv {a} : DFastStringEnv a :=
  UniqDFM.emptyUDFM.

Definition elemFsEnv {a} : FastString.FastString -> FastStringEnv a -> bool :=
  fun x y => UniqFM.elemUFM x y.

Definition delListFromFsEnv {a}
   : FastStringEnv a -> list FastString.FastString -> FastStringEnv a :=
  fun x y => UniqFM.delListFromUFM x y.

Definition delFromFsEnv {a}
   : FastStringEnv a -> FastString.FastString -> FastStringEnv a :=
  fun x y => UniqFM.delFromUFM x y.

Definition dFsEnvElts {a} : DFastStringEnv a -> list a :=
  UniqDFM.eltsUDFM.

Definition alterFsEnv {a}
   : (option a -> option a) ->
     FastStringEnv a -> FastString.FastString -> FastStringEnv a :=
  UniqFM.alterUFM.

(* External variables:
     bool list op_zt__ option FastString.FastString UniqDFM.UniqDFM UniqDFM.eltsUDFM
     UniqDFM.emptyUDFM UniqDFM.listToUDFM UniqDFM.lookupUDFM UniqFM.UniqFM
     UniqFM.addListToUFM UniqFM.addListToUFM_C UniqFM.addToUFM UniqFM.addToUFM_Acc
     UniqFM.addToUFM_C UniqFM.alterUFM UniqFM.delFromUFM UniqFM.delListFromUFM
     UniqFM.elemUFM UniqFM.emptyUFM UniqFM.filterUFM UniqFM.listToUFM
     UniqFM.lookupUFM UniqFM.mapUFM UniqFM.plusUFM UniqFM.plusUFM_C UniqFM.unitUFM
*)
