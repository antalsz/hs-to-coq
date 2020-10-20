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

(* Converted type declarations: *)

Definition FastStringEnv :=
  UniqFM.UniqFM%type.

Definition DFastStringEnv :=
  UniqFM.UniqFM%type.

(* Converted value declarations: *)

Axiom emptyFsEnv : forall {a}, FastStringEnv a.

Axiom unitFsEnv : forall {a}, FastString.FastString -> a -> FastStringEnv a.

Axiom extendFsEnv : forall {a},
                    FastStringEnv a -> FastString.FastString -> a -> FastStringEnv a.

Axiom extendFsEnvList : forall {a},
                        FastStringEnv a -> list (FastString.FastString * a)%type -> FastStringEnv a.

Axiom lookupFsEnv : forall {a},
                    FastStringEnv a -> FastString.FastString -> option a.

Axiom alterFsEnv : forall {a},
                   (option a -> option a) ->
                   FastStringEnv a -> FastString.FastString -> FastStringEnv a.

Axiom mkFsEnv : forall {a},
                list (FastString.FastString * a)%type -> FastStringEnv a.

Axiom elemFsEnv : forall {a}, FastString.FastString -> FastStringEnv a -> bool.

Axiom plusFsEnv : forall {a},
                  FastStringEnv a -> FastStringEnv a -> FastStringEnv a.

Axiom plusFsEnv_C : forall {a},
                    (a -> a -> a) -> FastStringEnv a -> FastStringEnv a -> FastStringEnv a.

Axiom extendFsEnv_C : forall {a},
                      (a -> a -> a) ->
                      FastStringEnv a -> FastString.FastString -> a -> FastStringEnv a.

Axiom mapFsEnv : forall {elt1} {elt2},
                 (elt1 -> elt2) -> FastStringEnv elt1 -> FastStringEnv elt2.

Axiom extendFsEnv_Acc : forall {a} {b},
                        (a -> b -> b) ->
                        (a -> b) -> FastStringEnv b -> FastString.FastString -> a -> FastStringEnv b.

Axiom extendFsEnvList_C : forall {a},
                          (a -> a -> a) ->
                          FastStringEnv a -> list (FastString.FastString * a)%type -> FastStringEnv a.

Axiom delFromFsEnv : forall {a},
                     FastStringEnv a -> FastString.FastString -> FastStringEnv a.

Axiom delListFromFsEnv : forall {a},
                         FastStringEnv a -> list FastString.FastString -> FastStringEnv a.

Axiom filterFsEnv : forall {elt},
                    (elt -> bool) -> FastStringEnv elt -> FastStringEnv elt.

Axiom lookupFsEnv_NF : forall {a},
                       FastStringEnv a -> FastString.FastString -> a.

Axiom emptyDFsEnv : forall {a}, DFastStringEnv a.

Axiom dFsEnvElts : forall {a}, DFastStringEnv a -> list a.

Axiom mkDFsEnv : forall {a},
                 list (FastString.FastString * a)%type -> DFastStringEnv a.

Axiom lookupDFsEnv : forall {a},
                     DFastStringEnv a -> FastString.FastString -> option a.

(* External variables:
     bool list op_zt__ option FastString.FastString UniqFM.UniqFM
*)
