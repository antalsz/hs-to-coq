Require Import GHC.Base.

Require Import Core.
Require Import Unique.

Require Import Proofs.GHC.Base.

Require Import Coq.NArith.BinNat.

Set Bullet Behavior "Strict Subproofs".

Ltac unfold_Unique_zeze :=
  repeat unfold Base.op_zeze__,
  Nat.Eq_nat,
  Eq_Char___,
  Unique.Eq___Unique,
  op_zeze____,
  Unique.Eq___Unique_op_zeze__,
  Unique.eqUnique.


Program Instance EqLaws_Unique : EqLaws Unique.Unique.
Next Obligation. repeat intro; destruct x; apply EqLaws_Word. Qed.
Next Obligation. repeat intro; destruct x, y; apply EqLaws_Word. Qed.
Next Obligation. do 3 intro; destruct x, y, z; apply EqLaws_Word. Qed.
Next Obligation. destruct x, y; apply EqLaws_Word. Qed.

Program Instance EqExact_Unique : EqExact Unique.Unique.
Next Obligation.
  assert (forall n n0 : N, (n =? n0)%N = (Unique.MkUnique n == Unique.MkUnique n0))
    by (now induction n, n0).
  destruct x, y.
  rewrite <- H.
  destruct (Eq_eq_Word n n0).
    subst.
    rewrite N.eqb_refl.
    now constructor.
  rewrite (proj2 (N.eqb_neq _ _) n1).
  constructor.
  intro; apply n1.
  now inversion H0.
Qed.

Lemma unique_word: forall v v', 
    ( v ==  v') =
    (Unique.getWordKey v == Unique.getWordKey v').
Proof.
  intros.
  unfold Unique.getWordKey.
  unfold Unique.getKey.
  destruct v.
  destruct v'.
  unfold_Unique_zeze.
  auto.
Qed.

Lemma unique_In : forall v vs,
 In v vs <->
 In (Unique.getWordKey v) (map Unique.getWordKey vs).
Proof.
  intros.
  split; intros.
  * apply in_map. assumption.
  * rewrite in_map_iff in H.
    destruct H as [u [Heq Hin]].
    enough (u = v) by (subst; assumption).
    clear Hin.
    destruct u, v.
    simpl in *.
    subst; reflexivity.
Qed.

Definition eqUnique_eq : forall u1 u2, eqUnique u1 u2 = true <-> u1 = u2.
Proof.
  intros.
  unfold eqUnique.
  destruct u1; destruct u2.
  unfold GHC.Base.op_zeze__.
  unfold Base.Eq_Char___.
  unfold Base.op_zeze____.
  rewrite BinNat.N.eqb_eq. 
  split. intros h; rewrite h; auto.
  intros h; inversion h; auto.
Qed.

Definition eqUnique_neq : forall u1 u2, eqUnique u1 u2 = false <-> u1 <> u2.
Proof.
  intros.
  unfold eqUnique.
  destruct u1; destruct u2.
  unfold GHC.Base.op_zeze__.
  unfold Base.Eq_Char___.
  unfold Base.op_zeze____.
  rewrite BinNat.N.eqb_neq. 
  split. unfold not. intros m h; inversion h; auto.
  unfold not. intros m h; rewrite h in m; auto.
Qed.

(**

** Local uniques

The Uniques in GHC are partitioned in classes, e.g. local variables have a different
class than external names, which are different from data constructors and so on.

The class is encoded in the upper 8 bits of the Unique. Our representation does not have 
upper bits... and we hope we can make do with less details. For our proofs, it would suffice
to axiomatize what we need:

 * A predicate that distinguishes the uniques used for (module)-local variables, [isLocalUnique]
 * An axiom stating that [uniqAway] always generates local uniques; that axiom lives in [VarSet.v].

But in order to prove our invariants for concrete Core terms as dumped from GHC, we
need the [isLocalUnique] function to compute. So hence it is a definition.

*)
Import ListNotations.
Require Import PrelNames.
Definition isLocalUnique  (u : Unique.Unique) : bool :=
  (u == mkPreludeMiscIdUnique  0) (* The wild card key is local *)
  || let '(c,i) := unpkUnique u in
     negb (List.elem c &"B0123456789:kmnrz").

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

(** [initExitJoinUnique] better be a local unique *)
Axiom isLocalUnique_initExitJoinUnique:
  isLocalUnique Unique.initExitJoinUnique = true.
