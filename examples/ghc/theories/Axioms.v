(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

(* This file gathers and explains axioms about the GHC development. *)

From mathcomp.ssreflect
Require Import ssreflect ssrnat prime ssrbool.



Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Classes.Morphisms. 

Require Import GHC.Base.

Require Import PrelNames.
Require Import Id.
Require Import Core.
Require Import Unique.
Require Import CoreFVs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


(**

** Local uniques

The Uniques in GHC are partitioned in classes, e.g. local variables have a different
class than external names, which are different from data constructors and so on.

The class is encoded in the upper 8 bits of the Unique. Our representation does not have 
upper bits... and we hope we can make do with less details. For our proofs, it would suffice
to axiomatize what we need:

 * A predicate that distinguishes the uniques used for (module)-local variables, [isLocalUnique]
 * An axiom stating that [uniqAway] always generates local uniques (see below).
 * An axiom stating that some uniques are local: in particular, initExitJoinUnique.

But in order to prove our invariants for concrete Core terms as dumped from GHC, we
need the [isLocalUnique] function to compute. So hence it is a definition.

*)


(*

From Unique.hs:

Allocation of unique supply characters:
        v,t,u : for renumbering value-, type- and usage- vars.
        B:   builtin
        C-E: pseudo uniques     (used in native-code generator)
        X:   uniques derived by deriveUnique
        _:   unifiable tyvars   (above)
        0-9: prelude things below
             (no numbers left any more..)
        ::   (prelude) parallel array data constructors

        other a-z: lower case chars for unique supplies.  Used so far:

        d       desugarer
        f       AbsC flattener
        g       SimplStg
        k       constraint tuple tycons
        m       constraint tuple datacons
        n       Native codegen
        r       Hsc name cache
        s       simplifier
        z       anonymous sums
*)

(*
Open Scope N_scope.
Definition isLocalUnique  (u : Unique.Unique) : bool :=
  (u == mkPreludeMiscIdUnique  0) (* The wild card key is local *)
  || let '(c,i) := unpkUnique u in
     negb (List.elem c &"B0123456789:kmnrz").
*)

(** [initExitJoinUnique] better be a local unique *)
Axiom isLocalUnique_initExitJoinUnique:
  Unique.isLocalUnique Unique.initExitJoinUnique = true.



(** ** [uniqAway] axiomatization *)


(* If uniqAway returns a variable with the same unique, 
   it returns the same variable. *)      
Axiom uniqAway_eq_same : forall v in_scope_set,
    (uniqAway in_scope_set v == v) ->
    (uniqAway in_scope_set v = v).

(* The variable returned by uniqAway is fresh. *)
Axiom uniqAway_lookupVarSet_fresh : forall v in_scope_set,
    lookupVarSet (getInScopeVars in_scope_set) (uniqAway in_scope_set v) = None.

(* Unique away preserves the classification of Vars. *)   
Axiom idScope_uniqAway: forall iss v, idScope v = idScope (uniqAway iss v).
Axiom id_details_uniqAway: forall iss v, id_details v = id_details (uniqAway iss v).

(* Variables have a unique cached inside.  This unique *should* be 
   the same as the unique stored in the name of the variable. *)
Axiom nameUnique_varName_uniqAway:
  forall vss v,
  Name.nameUnique (varName v) = varUnique v ->
  Name.nameUnique (varName (uniqAway vss v)) = varUnique (uniqAway vss v).
Axiom isLocalId_uniqAway:
  forall iss v,
  isLocalId (uniqAway iss v) = isLocalId v.




Lemma isJoinId_maybe_uniqAway:
  forall s v, 
  isJoinId_maybe (uniqAway s v) = isJoinId_maybe v.
Proof.
  intros iss v.
  move: (id_details_uniqAway iss v) => h.
  destruct v; simpl in *. 
  unfold isJoinId_maybe, isId.
  destruct uniqAway.
  rewrite andb_false_r.
  simpl in *.
  subst.
  auto.
Qed.

Lemma isLocalUnique_uniqAway:
  forall iss v,
    Unique.isLocalUnique (varUnique v) -> 
    Unique.isLocalUnique (varUnique (uniqAway iss v)).
Proof.
  move=>iss v h.
  move: (isLocalId_uniqAway iss v) => h0.
  unfold isLocalId in h0.
  rewrite h0.
  auto.
Qed.



(* Because we removed constructors from the Var type, these 
   three are provable directly. However, in the full system, we would 
   have to know more about uniqAway to know that they are true. *)
Lemma isLocalVar_uniqAway:
  forall iss v,
  isLocalVar (uniqAway iss v) = isLocalVar v.
Proof.
  move=> iss v.
  move: (isLocalId_uniqAway iss v) => h.
  destruct v. 
  unfold isLocalId in *. unfold isLocalVar in *.
  unfold isGlobalId. 
  destruct uniqAway.
(*  destruct idScope0, idScope; done. *)
  rewrite h. auto.
Qed.

Lemma isId_uniqAway:
  forall iss v,
    isId (uniqAway iss v) = isId v.
Proof.
  intros iss v. unfold isId. destruct uniqAway. destruct v. 
  done.
Qed.

Lemma isCoVar_uniqAway:
  forall iss v,
    isCoVar (uniqAway iss v) = isCoVar v.
Proof.
  unfold isCoVar. destruct v, uniqAway. done.
Qed.

  
(**** *)

(* NOTE: are these better as rewrites? Or as axioms? *)
Lemma isJoinId_maybe_setIdOccInfo:
  forall v occ_info, 
  isJoinId_maybe (setIdOccInfo v occ_info) = isJoinId_maybe v.
Proof.
  destruct v.
  move=> oi. cbv.
  destruct Util.debugIsOn.
  auto.
  auto.
Qed.

(* SCW: this one has a precondition that v is VanillaId or JoinId *)
Lemma isJoinId_maybe_asJoinId:
  forall v a,
  ( match Core.idDetails v with
        | Core.VanillaId => true
        | Core.Mk_JoinId _ => true
        | _ => false
        end ) -> 
  isLocalId v ->
  isJoinId_maybe (asJoinId v a) = Some a.
Proof.
  intros. destruct v.
  simpl in *.
  unfold isJoinId_maybe. unfold isId.
  destruct asJoinId eqn:AS.
  rewrite andb_false_r.
  unfold asJoinId in AS. rewrite H0 in AS. 
  unfold Panic.warnPprTrace in AS. simpl in AS. 
  rewrite H in AS. simpl in AS. inversion AS.
  simpl.
  auto.
Qed.  


  
(** ** Valid VarSets *)

(* This property is an invariant of the VarSet/UniqFM type. We may want to either 
   axiomatize it or add it to a sigma type in one of the definitions. *)

Definition ValidVarSet (vs : VarSet) : Prop :=
  forall v1 v2, lookupVarSet vs v1 = Some v2 -> (v1 == v2).

Axiom ValidVarSet_Axiom : forall vs, ValidVarSet vs.


(********************************* *)



