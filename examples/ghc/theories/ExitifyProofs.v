Require Import GHC.Base.
Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

Require Import Psatz.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.

Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.

Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

Require Import GhcProofs.JoinPointInvariants.
Require Import GhcProofs.ScopeInvariant.
Require Import GhcProofs.StateLogic.
Require Import GhcProofs.CoreInduct.
Require Import GhcProofs.Forall.
Require Import GhcProofs.CoreLemmas.
Require Import GhcProofs.CoreFVsLemmas.
Require Import GhcProofs.Tactics.
Require Import GhcProofs.NCore.
Require Import GhcProofs.VectorUtils.


Require Import IntSetProofs.
(* Require Import IntMapProofs. *)


(* Q: is there a way to do the automatic destructs safely? Sometimes 
   loses too much information. *)

Ltac unfold_VarSet :=
  unfold subVarSet,elemVarSet, isEmptyVarSet, 
         minusVarSet, extendVarSet, extendVarSetList in *;
  unfold UniqSet.elementOfUniqSet, 
         UniqSet.isEmptyUniqSet, 
         UniqSet.addOneToUniqSet,
         UniqSet.minusUniqSet,
         UniqSet.addListToUniqSet in *;
  try repeat match goal with
  | vs: VarSet, H : context[match ?vs with _ => _ end]  |- _ => destruct vs
  end;
  try repeat match goal with
  | vs: VarSet |- context[match ?vs with _ => _ end ] => destruct vs
  end;

  unfold UniqFM.addToUFM, 
         UniqFM.minusUFM, UniqFM.isNullUFM, 
         UniqFM.elemUFM in *;
  try repeat match goal with
  | u: UniqFM.UniqFM ?a, H : context[match ?u with _ => _ end]  |- _ => destruct u
  end;
  try repeat match goal with
  | u: UniqFM.UniqFM ?a |- context[match ?u with _ => _ end] => destruct u
  end.

Ltac safe_unfold_VarSet :=
  unfold subVarSet,elemVarSet, isEmptyVarSet, 
         minusVarSet, extendVarSet, extendVarSetList in *;
  unfold UniqSet.elementOfUniqSet, 
         UniqSet.isEmptyUniqSet, 
         UniqSet.addOneToUniqSet,
         UniqSet.minusUniqSet,
         UniqSet.addListToUniqSet in *;
  unfold UniqFM.addToUFM, 
         UniqFM.minusUFM, UniqFM.isNullUFM, 
         UniqFM.elemUFM in *.



(** ** Punted-on lemmas about GHC functions *)

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

Axiom mkLets_append:
  forall b binds1 binds2 (e : Expr b),
  mkLets (binds1 ++ binds2) e = mkLets binds1 (mkLets binds2 e).

Axiom mkLets_cons:
  forall b bind binds (e : Expr b),
  mkLets (bind :: binds) e = mkLet bind (mkLets binds e).

Axiom mkLets_nil:
  forall b (e : Expr b),
  mkLets [] e = e.



Lemma isJoinId_eq : forall v,
  isJoinId v = match isJoinId_maybe v with | None => false |Some _ => true end.
Proof.
  unfold isJoinId.
  induction v; auto.
  now destruct i0.
Qed.

Lemma isJoinId_isJoinId_maybe: forall v,
  isJoinId v = true ->
  isJoinId_maybe v = Some (idJoinArity v).
Proof.
  unfold isJoinId.
  induction v; simpl; intros; auto; try discriminate.
  now destruct i0.
Qed.

Lemma idJoinArity_join: forall v a,
  isJoinId_maybe v = Some a -> idJoinArity v = a.
Proof.
  unfold isJoinId, isJoinId_maybe, idJoinArity.
  induction v; simpl; intros; auto; try discriminate.
  destruct i0; simpl; try discriminate.
  now inversion H.
Qed.

Axiom isJoinId_maybe_uniqAway:
  forall s v, 
  isJoinId_maybe (uniqAway s v) = isJoinId_maybe v.

Axiom isJoinId_maybe_setIdOccInfo:
  forall v occ_info, 
  isJoinId_maybe (setIdOccInfo v occ_info) = isJoinId_maybe v.

Axiom isJoinId_maybe_asJoinId:
  forall v a,
  isJoinId_maybe (asJoinId v a) = Some a.

Axiom dVarSet_freeVarsOf_Ann:
  (* @lastland, this is one spec that you might want to do *)
  forall ann_e, dVarSetToVarSet (freeVarsOf ann_e) = exprFreeVars (deAnnotate ann_e).


Ltac unfold_Foldable :=
  unfold Foldable.foldr,
  Foldable.foldr__,
  Foldable.Foldable__list,
  Foldable.Foldable__list_foldr,
  Base.foldr.

Ltac unfold_Foldable_foldl' :=
  unfold Foldable.foldl',  Foldable.Foldable__list, 
  Foldable.foldl'__, Foldable.Foldable__list_foldl', foldl'.


Lemma extendVarSetList_nil:
  forall s,
  extendVarSetList s [] = s.
Proof.
  intro s. repeat unfold_VarSet.
  unfold_Foldable.
  unfold_Foldable_foldl'.
  simpl.
  auto.
Qed.

Lemma extendVarSetList_cons:
  forall s v vs,
  extendVarSetList s (v :: vs) = extendVarSetList (extendVarSet s v) vs.
Proof.
  intros.
  repeat unfold_VarSet.
  unfold_Foldable_foldl'.
  simpl.
  f_equal.
Qed.


Lemma List_foldl_foldr:
  forall {a b} f (x : b) (xs : list a),
    fold_left f xs x = List.fold_right (fun x g a => g (f a x)) id xs x.
Proof.
  intros. revert x.
  induction xs; intro.
  * reflexivity.
  * simpl. rewrite IHxs. reflexivity.
Qed.

Lemma Foldable_foldl'_app : forall a b (f:b -> a -> b) (s:b) 
                              (vs1 : list a) (vs2: list a),
    Foldable.foldl' f s (vs1 ++ vs2) =
    Foldable.foldl' f (Foldable.foldl' f s vs1) vs2.
Proof.
  unfold_Foldable_foldl'.
  intros.
  rewrite <- List_foldl_foldr.
  rewrite <- List_foldl_foldr.
  rewrite <- List_foldl_foldr.
  rewrite fold_left_app.
  auto.
Qed.

Lemma extendVarSetList_append:
  forall s vs1 vs2,
  extendVarSetList s (vs1 ++ vs2) = extendVarSetList (extendVarSetList s vs1) vs2.
Proof.
  intros.
  repeat unfold_VarSet.
  rewrite Foldable_foldl'_app.
  auto.
Qed.

Lemma getUnique_varUnique: 
    (Unique.getUnique : Var -> Unique.Unique) = varUnique.
Proof.
  unfold Unique.getUnique, Unique.getUnique__,Uniquable__Var,
     Core.Uniquable__Var_getUnique.
  auto.
Qed.

(* This looks really useful 
https://github.com/Zimmi48/transfer 
*)

Axiom member_in : forall k (i:Internal.IntMap Var) (vs: list Var)(f : Var -> Word), 
 IntMap.Internal.member k i = true <->
 In k (map f vs).

Lemma elemVarSet_mkVarset_iff_In:
  forall v vs,
  elemVarSet v (mkVarSet vs) = true <->  In (varUnique v) (map varUnique vs).
Proof.
  intros.
  unfold_VarSet.
  remember (mkVarSet vs) as vss.
  unfold_VarSet.
  unfold Unique.getWordKey. 
  rewrite <- getUnique_varUnique.

  unfold mkVarSet in *.
  unfold UniqSet.mkUniqSet in *.
  unfold UniqSet.addOneToUniqSet in *.
  unfold UniqSet.emptyUniqSet in *.
  unfold UniqFM.emptyUFM in *.
  unfold UniqFM.addToUFM in *.
  (* Need theory about IntMap. *)
Admitted. 

Lemma unique_word: forall v v', 
    ( v ==  v') =
    (Unique.getWordKey v == Unique.getWordKey v').
Proof.
  intros.
  unfold Unique.getWordKey.
  unfold Unique.getKey.
  destruct v.
  destruct v'.
  unfold GHC.Base.op_zeze__.
  unfold Unique.Eq___Unique.
  unfold Eq_Char___.
  unfold op_zeze____.
  unfold Unique.Eq___Unique_op_zeze__.
  unfold Unique.eqUnique.
  unfold GHC.Base.op_zeze__.
  unfold Eq_Char___.
  unfold op_zeze____.
  auto.
Qed.

Lemma member_insert : forall A k k' v (i : IntMap.Internal.IntMap A),
IntMap.Internal.member k (IntMap.Internal.insert k' v i) =
  (k == k')
  || IntMap.Internal.member k i.
Admitted.


Lemma elemVarSet_extendVarSet:
  forall v vs v',
  elemVarSet v (extendVarSet vs v') = (varUnique v == varUnique v') || elemVarSet v vs.
Proof.
  intros.
  safe_unfold_VarSet.
  destruct vs.
  destruct u.
  rewrite unique_word.
  rewrite <- getUnique_varUnique.
  apply member_insert.
Qed.
  
Lemma subVarSet_refl:
  forall vs1,
  subVarSet vs1 vs1 = true.
Proof.
  intros.
  safe_unfold_VarSet.
  destruct vs1.
  destruct u.
Admitted.

Axiom exprFreeVars_Var: forall v, exprFreeVars (Mk_Var v) = unitVarSet v.
Axiom elemVarSet_unitVarSet: forall v1 v2,
  (elemVarSet v1 (unitVarSet v2) = true) <-> (varUnique v1 = varUnique v2).
Axiom elemVarSet_delVarSet: forall v1 fvs v2,
  elemVarSet v1 (delVarSet fvs v2) = true <-> (varUnique v1 <> varUnique v2 /\ elemVarSet v1 fvs = true).
Axiom elemVarSet_false_true:
  forall v1 fvs v2,
  elemVarSet v1 fvs = false ->
  elemVarSet v2 fvs = true ->
  varUnique v1 <> varUnique v2.


Axiom subVarSet_elemVarSet_true:
  forall v vs vs',
  subVarSet vs vs' = true ->
  elemVarSet v vs = true ->
  elemVarSet v vs' = true.

Axiom subVarSet_elemVarSet_false:
  forall v vs vs',
  subVarSet vs vs' = true ->
  elemVarSet v vs' = false ->
  elemVarSet v vs = false.

Axiom subVarSet_extendVarSetList_l:
  forall vs1 vs2 vs,
  subVarSet vs1 vs2 = true ->
  subVarSet vs1 (extendVarSetList vs2 vs) = true.

Axiom subVarSet_extendVarSetList_r:
  forall vs1 vs2 vs,
  subVarSet vs1 (mkVarSet vs) = true ->
  subVarSet vs1 (extendVarSetList vs2 vs) = true.


Axiom subVarSet_extendVarSet:
  forall vs1 vs2 v,
  subVarSet vs1 vs2 = true ->
  subVarSet vs1 (extendVarSet vs2 v) = true.

Axiom subVarSet_delVarSetList:
  forall vs1 vs2,
  subVarSet (delVarSetList vs1 vs2) vs1 = true.

Axiom disjointVarSet_mkVarSet:
  forall vs1 vs2,
  disjointVarSet vs1 (mkVarSet vs2) = true <->
  Forall (fun v => elemVarSet v vs1 = false) vs2.

Axiom disjointVarSet_subVarSet_l:
  forall vs1 vs2 vs3,
  disjointVarSet vs2 vs3 = true ->
  subVarSet vs1 vs2 = true ->
  disjointVarSet vs1 vs3 = true.
  

Axiom getInScopeVars_extendInScopeSet:
  forall iss v,
  getInScopeVars (extendInScopeSet iss v) = extendVarSet (getInScopeVars iss) v.

Axiom getInScopeVars_extendInScopeSetList:
  forall iss vs,
  getInScopeVars (extendInScopeSetList iss vs) = extendVarSetList (getInScopeVars iss) vs.

Axiom elemVarSet_uniqAway:
  forall v iss vs,
  subVarSet vs (getInScopeVars iss) = true ->
  elemVarSet (uniqAway iss v) vs = false.

Axiom exprFreeVars_Lam:
  forall v e,
  exprFreeVars (Lam v e) = delVarSet (exprFreeVars e) v.

Axiom WellScoped_extendVarSetList_fresh:
  forall vs e vs1,
  disjointVarSet (exprFreeVars e) (mkVarSet vs) = true ->
  WellScoped e (extendVarSetList vs1 vs) <-> WellScoped e vs1.

Axiom WellScoped_extendVarSet_ae:
  forall e vs v1 v2,
  almostEqual v1 v2 ->
  WellScoped e (extendVarSet vs v1) <-> WellScoped e (extendVarSet vs v2).

Lemma delVarSet_ae:
  forall vs v1 v2,
  almostEqual v1 v2 ->
  delVarSet vs v1 = delVarSet vs v2.
Proof.
  induction 1; simpl;
  unfold UniqFM.delFromUFM; simpl; auto.
Qed.

Lemma elemVarSet_ae:
  forall vs v1 v2,
  almostEqual v1 v2 ->
  elemVarSet v1 vs = elemVarSet v2 vs.
Proof.
  induction 1; simpl;
  unfold UniqFM.delFromUFM; simpl; auto.
Qed.

Axiom WellScoped_extendVarSetList:
  forall vs e vs1,
  disjointVarSet vs1 (mkVarSet vs) = true ->
  WellScoped e vs1 -> WellScoped e (extendVarSetList vs1 vs).

Axiom WellScoped_subset:
  forall e vs,
  WellScoped e vs -> subVarSet (exprFreeVars e) vs = true.


Lemma WellScoped_extendVarSet_fresh:
  forall v e vs,
  elemVarSet v (exprFreeVars e) = false ->
  WellScoped e (extendVarSet vs v) <-> WellScoped e vs.
Proof.
  intros.
  split.
  intro h.
  pose (K := WellScoped_subset e _ h). clearbody K.
  set (fve := exprFreeVars e) in *.
  
  unfold_VarSet.

  set (key := Unique.getWordKey (Unique.getUnique v)) in *.
Admitted.  

Axiom WellScoped_Lam:
  forall v e isvs,
  WellScoped (Lam v e) isvs <-> WellScoped e (extendVarSet isvs v).

Axiom WellScoped_mkLams:
  forall vs e isvs,
  WellScoped (mkLams vs e) isvs <-> WellScoped e (extendVarSetList  isvs vs).

Axiom WellScoped_mkVarApps:
  forall e vs isvs,
  WellScoped (mkVarApps e vs) isvs <-> WellScoped e isvs /\ Forall (fun v => WellScopedVar v isvs) vs.
  
Axiom exprFreeVars_mkLams:
  forall vs e,
  exprFreeVars (mkLams vs e) = delVarSetList (exprFreeVars e) vs.

Axiom WellScopedVar_extendVarSet:
  forall v vs,
  WellScopedVar v (extendVarSet vs v).

Lemma WellScoped_extendVarSetList_fresh_under:
  forall vs1 vs2 e vs,
  disjointVarSet (exprFreeVars e) (mkVarSet vs1)  = true ->
  WellScoped e (extendVarSetList (extendVarSetList vs vs1) vs2) <-> WellScoped e (extendVarSetList vs vs2).
Proof.
  intros.
  rewrite <- WellScoped_mkLams.
  rewrite WellScoped_extendVarSetList_fresh.
  rewrite -> WellScoped_mkLams.
  reflexivity.
  rewrite exprFreeVars_mkLams.
  eapply disjointVarSet_subVarSet_l; only 1: eassumption.
  apply subVarSet_delVarSetList.
Qed.

Lemma WellScoped_MkLetRec: forall pairs body isvs,
  WellScoped (mkLetRec pairs body) isvs <-> WellScoped (Let (Rec pairs) body) isvs .
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

Lemma WellScoped_MkLet: forall bind body isvs,
  WellScoped (mkLet bind body) isvs <-> WellScoped (Let bind body) isvs .
Proof.
  intros.
  unfold mkLet.
  destruct bind; try reflexivity.
  destruct l; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

Axiom WellScoped_extended_filtered:
  forall vs e isvs,
  WellScoped e (extendVarSetList isvs vs) ->
  WellScoped e (extendVarSetList isvs (filter (fun v => elemVarSet v (exprFreeVars e)) vs)).

Axiom isJoinPointValidPair_extendVarSet:
  forall v rhs jps v',
  isJoinPointsValidPair v rhs jps = true ->
  isJoinPointsValidPair v rhs (extendVarSet jps v') = true.
  
Axiom WellScoped_collectNBinders:
  forall e n isvs body params,
  WellScoped e isvs ->
  collectNBinders n e = (params, body) ->
  WellScoped body (extendVarSetList isvs params).

Axiom WellScoped_collectNBinders2:
  forall e n isvs,
  WellScoped e isvs ->
  WellScoped (snd (collectNBinders n e)) (extendVarSetList isvs (fst (collectNBinders n e))).

Lemma deAnnBinds_AnnRec:
 forall {a v} (pairs : list (v * AnnExpr v a)),
 deAnnBind (AnnRec pairs) = Rec (map (fun p => (fst p, deAnnotate (snd p))) pairs).
Proof.
  unfold deAnnBind.
  symmetry.
  rewrite <- flat_map_cons_f.
  f_equal; f_equal.
  extensionality x.
  now destruct x.
Qed.

Lemma deAnnotate_AnnLet_AnnRec:
 forall {a v} fvs pairs (e : AnnExpr a v),
 deAnnotate (fvs, AnnLet (AnnRec pairs) e)
  = Let (Rec (map (fun p => (fst p, deAnnotate (snd p))) pairs)) (deAnnotate e).
Proof.
  induction pairs; simpl; intros; auto.
  f_equal; f_equal.
  destruct a0; simpl; f_equal.
  symmetry.
  rewrite <- flat_map_cons_f.
  f_equal.
  extensionality x.
  now destruct x.
Qed.

Lemma bindersOf_Rec:
  forall {v} (pairs : list (v * Expr v)),
  bindersOf (Rec pairs) = map fst pairs.
Proof.
  induction pairs; simpl; intros; auto.
  destruct a.
  now rewrite <- IHpairs.
Qed.

Lemma forallb_imp:
  forall a P Q (xs : list a),
  forallb P xs = true ->
  (forall x, P x = true -> Q x = true) ->
  forallb Q xs = true.
Proof.
  induction xs; simpl; intros; auto.
  apply andb_prop in H.
  apply andb_true_intro.
  intuition.
Qed.

Axiom WellScopedVar_extendVarSetList_l:
  forall v vs1 vs2,
  WellScopedVar v vs1 ->
  elemVarSet v (mkVarSet vs2) = false ->
  WellScopedVar v (extendVarSetList vs1 vs2).

Axiom WellScopedVar_extendVarSetList_r:
  forall v vs1 vs2,
  In v vs2 ->
  NoDup (map varUnique vs2) ->
  WellScopedVar v (extendVarSetList vs1 vs2).

Lemma snd_unzip:
  forall a b (xs : list (a * b)),
  snd (List.unzip xs) = map snd xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl. f_equal. apply IHxs.
Qed.

Lemma snd_unzip_map:
  forall a b c (f : a -> b) (g : a -> c) xs,
  snd (List.unzip (map (fun x => (f x, g x)) xs)) = map g xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl. f_equal. apply IHxs.
Qed.


Lemma zip_unzip_map:
  forall a b c (f : b -> c) (xs : list (a * b)),
  List.zip (fst (List.unzip xs)) (Base.map f (snd (List.unzip xs)))
  = map (fun '(x,y) => (x, f y)) xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl. f_equal. apply IHxs.
Qed.

Lemma flat_map_unpack_cons_f:
  forall (A B C : Type) (f : A -> B -> C ) (xs : list (A * B)),
   flat_map (fun '(x,y) => [f x y]) xs = map (fun '(x,y) => f x y) xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl.
    f_equal. apply IHxs.
Qed.

Lemma forM_map:
  forall (m : Type -> Type) (a b c : Type) `{Monad m}
  (xs : list a) (act : b -> m c) (f : a -> b),
  Traversable.forM (map f xs) act = Traversable.forM xs (fun x => act (f x)).
Proof.
  intros.
  induction xs.
  * reflexivity.
  * cbv. f_equal. apply IHxs.
Qed.

Lemma forM_cong:
  forall {a m b} `{Monad m} (f g : a -> m b) (xs : list a),
  (forall x, In x xs -> f x = g x) ->
  Traversable.forM xs f = Traversable.forM xs g.
Proof.
  intros.
  rewrite <- forM_map with (act := fun x => x) (f := f).
  rewrite <- forM_map with (act := fun x => x) (f := g).
  f_equal.
  apply map_ext_in.
  assumption.
Qed.

(* This section reflects the context of the local definition of exitifyRec *)
Section in_exitifyRec.
  (* Parameters of exitifyRec *)
  Variable in_scope : InScopeSet.
  Variable pairs : list NJPair.
  (* The actual parameter passed *)
  Definition in_scope2 := extendInScopeSetList in_scope (map (fun '(Mk_NJPair v _ _ _) => v) pairs).

  (* Parameters and assumptions of the proof *)
  Variable jps : VarSet.

  (* Giving names to the local functions of exitifyRec.
     See http://www.joachim-breitner.de/blog/738-Verifying_local_definitions_in_Coq
     for more on that idiom.
   *)
  Definition go_exit := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x := ?rhs in ?body) => 
      exact rhs
    end).

  Definition recursive_calls := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x := _ in let y := ?rhs in _) => 
      exact rhs
    end).

  Definition go := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let y := @?rhs x1 x2 in _) => 
      let def := eval cbv beta in (rhs go_exit recursive_calls) in
      exact def
    end).

  Definition ann_pairs := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let y := ?rhs in _) => 
      exact rhs
    end).

  Definition pairs'_exits := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let x4 := _ in let '(pairs',exits) := @?rhs x3 x4 in ?body) => 
      let def := eval cbv beta in (rhs go ann_pairs) in
      exact def
    end).
  Definition pairs' := fst pairs'_exits.
  Definition exits := snd pairs'_exits.

  (* Some useful definitions *)
  
  (* The names of the functions bound in this letrec *)
  Definition fs := map (fun '(Mk_NJPair v _ _ _) => v) pairs.

  (* [in_scope] and [in_scope2] should only be mentioned as concrete arguments
     to functions, but ideally quickly rewritten to these. *)
  (* The outermost scope *)
  Definition isvs := getInScopeVars in_scope.
  (* The let-scope, before *)
  Definition isvsp := extendVarSetList isvs fs .
  (* The outermost scope, including exits *)
  Definition isvs' := extendVarSetList isvs (map fst exits).
  (* The let-scope, after *)
  Definition isvsp' := extendVarSetList isvs' fs.

  (** Termination of [go] and a suitable induction lemma *)

  Definition go_f := ltac:(
    let rhs := eval cbv delta [go] in go in
    lazymatch rhs with
      | @DeferredFix.deferredFix2 ?a ?b ?r ?HDefault ?f =>
      exact f
    end).

  (* Termination of [go] *)
  Lemma go_eq :
     forall captured e,
     go captured (freeVars (toExpr e)) = go_f go captured (freeVars (toExpr e)).
  Proof.
    intros.
    unfold go; fold go_f.
    unfold DeferredFix.deferredFix2.
    unfold DeferredFix.curry.
    rewrite DeferredFix.deferredFix_eq_on with
      (P := fun p => exists u, snd p = freeVars (toExpr u))
      (R := fun p1 p2 => CoreLT (deAnnotate (snd p1)) (deAnnotate (snd p2))).
    * reflexivity.
    * apply Inverse_Image.wf_inverse_image.
      apply CoreLT_wf.
    * clear captured e.
      intros g h [captured ann_e] HP Hgh.
      destruct HP as [e Heq]. simpl in Heq. subst ann_e.

      simpl. cbv beta delta [go_f].
      repeat float_let; cse_let.

      enough (Hnext : j_40__ = j_40__0). {
        repeat (destruct_match; try reflexivity); try apply Hnext.
      }
      subst j_40__ j_40__0. cleardefs.

      destruct e;
        simpl; rewrite ?freeVarsBind1_freeVarsBind;
        try destruct n;
        simpl;
        try destruct (isLocalVar _);
        repeat expand_pairs;
        simpl;
        repeat destruct_match;
        simpl; rewrite ?freeVarsBind1_freeVarsBind;
        rewrite ?collectNAnnBndrs_freeVars_mkLams in *;
        try (simpl in Heq);
        try (inversion Heq; subst; clear Heq);
        try solve [congruence];
        try reflexivity.
      - f_equal.
        apply Hgh; simpl.
        + eexists; reflexivity.
        + simpl; rewrite ?freeVarsBind1_freeVarsBind.
          simpl.
          Core_termination.
      - f_equal.
        ** replace j with (length params) in Heq2 by congruence.
           rewrite collectNAnnBndrs_freeVars_mkLams in Heq2.
           inversion Heq2; subst; clear Heq2.
           apply Hgh; simpl.
           + eexists; reflexivity.
           + simpl; rewrite ?freeVarsBind1_freeVarsBind.
             simpl. repeat expand_pairs.
             rewrite !deAnnotate_freeVars, !deAnnotate'_snd_freeVars.
             Core_termination.
        ** extensionality join_body'.
           f_equal.
           apply Hgh.
           + eexists; reflexivity.
           + simpl. expand_pairs.
             Core_termination.
      - contradict H0.
        apply not_true_iff_false.
        rewrite zip_unzip_map.
        rewrite to_list_map.
        dependent inversion pairs0; subst.
        destruct h0.
        rewrite to_list_cons.
        simpl.
        rewrite isJoinId_eq. rewrite HnotJoin. reflexivity.
      - clear H0. f_equal.
        apply Hgh; simpl.
        + eexists; reflexivity.
        + simpl; rewrite ?freeVarsBind1_freeVarsBind.
          simpl. repeat expand_pairs. simpl.
          Core_termination.
      - clear H0.
        rewrite zip_unzip_map.
        rewrite to_list_map.
        rewrite !forM_map.
        f_equal.
        ** apply forM_cong. intros [j params rhs HiNJ] HIn.
           simpl.
           expand_pairs.
           erewrite idJoinArity_join by eassumption.
           rewrite collectNAnnBndrs_freeVars_mkLams.
           f_equal.
           apply Hgh.
           + eexists; reflexivity.
           + simpl.
             rewrite ?freeVarsBind1_freeVarsBind. simpl.
             repeat expand_pairs. simpl.
             rewrite !zip_unzip_map. rewrite !to_list_map.
             rewrite flat_map_unpack_cons_f.
             rewrite !map_map.
             eapply CoreLT_let_pairs_mkLam.
             rewrite in_map_iff.
             eexists. split. 2: eassumption. simpl.
             expand_pairs.
             rewrite ?deAnnotate_freeVars, ?deAnnotate'_snd_freeVars.
             reflexivity.
        ** extensionality pairs'.
           f_equal.
           apply Hgh.
           + eexists; reflexivity.
           + simpl.
             rewrite ?freeVarsBind1_freeVarsBind. simpl.
             repeat expand_pairs. simpl.
             Core_termination.
      - contradict H0.
        apply not_false_iff_true.
        rewrite zip_unzip_map.
        rewrite to_list_map.
        dependent inversion pairs0; subst.
        destruct h0.
        rewrite to_list_cons.
        simpl.
        rewrite isJoinId_eq. rewrite HisJoin. reflexivity.
      - f_equal.
        rewrite snd_unzip. rewrite !map_map, !forM_map.
        apply forM_cong. intros [[dc pats] rhs] HIn.
        simpl.
        f_equal. apply Hgh; clear Hgh.
        + eexists; reflexivity.
        + simpl. expand_pairs. simpl.
          rewrite snd_unzip, !map_map.
          simpl.
          eapply CoreLT_case_alts.
          rewrite in_map_iff.
          eexists. split. 2: eassumption. simpl.
          repeat expand_pairs. simpl.
          rewrite ?deAnnotate_freeVars, ?deAnnotate'_snd_freeVars.
          reflexivity.
  * eexists; reflexivity.
  Qed.

  Lemma go_ind_aux:
    forall (P : _ -> _ -> _ -> Prop),
    { IHs : Prop | 
    IHs ->
    forall e captured,
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    P captured e (go captured (freeVars (toExpr e)))
    }.
  Proof.
    intros P.
    eexists.
    intros IHs.
    pose proof IHs as IH1. eapply proj1 in IH1. eapply proj2 in IHs.
    pose proof IHs as IH2. eapply proj1 in IH2. eapply proj2 in IHs.
    pose proof IHs as IH3. eapply proj1 in IH3. eapply proj2 in IHs.
    pose proof IHs as IH4. eapply proj1 in IH4. eapply proj2 in IHs.
    pose proof IHs as IH5. eapply proj1 in IH5. eapply proj2 in IHs.
    pose proof IHs as IH6. eapply proj1 in IH6. eapply proj2 in IHs.
    rename IHs into IH7.
    refine (well_founded_ind NCoreLT_wf _ _).
    intros e IH captured HWS.

    rewrite go_eq.
    cbv beta delta [go_f]. (* No [zeta]! *)

    rewrite !dVarSet_freeVarsOf_Ann in *.
    rewrite !deAnnotate_freeVars in *.

    (* Float out lets *)
    repeat float_let.
    enough (Hnext : P captured e j_40__). {
      clearbody j_40__; cleardefs.
      destruct (disjointVarSet fvs recursive_calls) eqn:Hdisjoint; try apply Hnext.
      clear IH Hnext.
      revert e captured fvs HWS Hdisjoint.
      refine IH1.
    }

    cleardefs.
    (* No exitification here, so descend*)
    subst j_40__.
    enough (Hnext: P captured e j_22__). {
      clearbody j_22__.
      destruct e; try apply Hnext.
      * (* spurious case Mk_Var *)
        simpl in *. destruct (isLocalVar _); apply Hnext.
      * (* spurious case Lam *)
        simpl in *. repeat expand_pairs. apply Hnext.
      * (* Case [Let] *) 
        clear Hnext.
        repeat float_let.
        simpl.
        do 2 expand_pairs. simpl.
        rewrite freeVarsBind1_freeVarsBind.
        unfold freeVarsBind.
        destruct n as [[x rhs] | [j params rhs] | n pairs' | n pairs']; simpl.
        + replace (isJoinId_maybe x) with (@None nat) by apply HnotJoin.
          lazymatch goal with |- context [go ?x (freeVars (toExpr ?y))] => assert (P x y (go x (freeVars (toExpr y)) )) end. {
            apply IH.
            ** NCore_termination.
            ** simpl.
               rewrite  extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
               apply HWS.
          }
          clear IH.
          revert captured x rhs e HnotJoin HWS H.
          refine IH2.
        + unfold CoreBndr in *.
          replace (isJoinId_maybe j) with (Some (length params)) by apply HisJoin.
          rewrite collectNAnnBndrs_freeVars_mkLams.
          lazymatch goal with |- context [go ?x (freeVars (toExpr ?y))] => assert (P x y (go x (freeVars (toExpr y)) )) end. {
             apply IH.
             ** NCore_termination.
             ** rewrite extendVarSetList_append.
                rewrite <- WellScoped_mkLams.
                simpl in HWS.
                apply HWS.
          }
          assert (P (captured ++ [j]) e (go (captured ++ [j]) (freeVars (toExpr e)))). {
             apply IH.
             ** NCore_termination.
             ** rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
                apply HWS.
          } 
          clear IH.
          revert captured j params rhs e HisJoin HWS H H0.
          refine IH3.
        + expand_pairs. simpl.
          rewrite to_list_map.
          rewrite !zip_unzip_map.
          rewrite !map_map.

          destruct (isJoinId _) eqn:Heq_isJoinId.
          Focus 1.
            exfalso.
            rewrite <- not_false_iff_true in Heq_isJoinId.
            contradict Heq_isJoinId.
            dependent inversion pairs'; subst; clear.
            dependent inversion h. simpl.
            rewrite isJoinId_eq. rewrite HnotJoin. reflexivity.
          clear Heq_isJoinId.

          clear IH1 IH2 IH3.

          (* Destruct well-scopedness assumption *)
          destruct HWS as [HNoDup [HWSpairs HWSe]].
          rewrite Forall'_Forall in HWSpairs.
          rewrite to_list_map in HWSpairs.
          rewrite !map_map in HWSpairs.
          rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x) in HWSpairs
             by (intros; repeat expand_pairs; destruct a; reflexivity).
          rewrite Forall_map in HWSpairs.
          rewrite to_list_map in HWSe.
          rewrite !map_map in HWSe.
          rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x) in HWSe
             by (intros; repeat expand_pairs; destruct a; reflexivity).
          rewrite to_list_map in HNoDup.
          rewrite !map_map in HNoDup.
          rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => varUnique x) in HNoDup
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          do 2 rewrite flat_map_unpack_cons_f.
          repeat rewrite map_map.
          rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x)
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          lazymatch goal with |- context [go ?x (freeVars (toExpr ?y))] => assert (P x y (go x (freeVars (toExpr y)) )) end. {
            apply IH.
            ** NCore_termination.
            ** rewrite !extendVarSetList_append.
               apply HWSe.
          }
          clear IH.
          revert n pairs' e captured HNoDup HWSpairs HWSe H.
          refine IH4.
        + clear IH1 IH2 IH3 IH4.

          expand_pairs. simpl.
          rewrite to_list_map.
          rewrite !zip_unzip_map.
          rewrite !map_map.
          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x)
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          destruct (isJoinId _) eqn:Heq_isJoinId.
          Focus 2.
            exfalso.
            rewrite <- not_true_iff_false in Heq_isJoinId.
            contradict Heq_isJoinId.
            dependent inversion pairs'; subst; clear.
            dependent inversion h. simpl.
            rewrite isJoinId_eq. rewrite HisJoin. reflexivity.
          clear Heq_isJoinId.

          (* Destruct well-scopedness assumption *)
          destruct HWS as [HNoDup [HWSpairs HWSe]].
          rewrite Forall'_Forall in HWSpairs.
          rewrite to_list_map in HWSpairs.
          rewrite !map_map in HWSpairs.
          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in HWSpairs
             by (intros; repeat expand_pairs; destruct a; reflexivity).
          rewrite Forall_map in HWSpairs.
          rewrite Forall_forall in HWSpairs.
          rewrite to_list_map in HWSe.
          rewrite !map_map in HWSe.
          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in HWSe
             by (intros; repeat expand_pairs; destruct a; reflexivity).
          rewrite to_list_map in HNoDup.
          rewrite !map_map in HNoDup.
          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => varUnique x) in HNoDup
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          rewrite forM_map.
          assert (forall j params join_body HisJoin
            (HIn : In (Mk_NJPair j params join_body HisJoin) (Vector.to_list pairs')),
            P (captured ++ map (fun '(Mk_NJPair x0 _ _ _) => x0) (Vector.to_list pairs') ++ params) join_body
              (go (captured ++ map (fun '(Mk_NJPair x0 _ _ _) => x0) (Vector.to_list pairs') ++ params) (freeVars (toExpr join_body)))
          ). {
            intros j params rhs HisJoin HIn.
            apply IH.
            ** NCore_termination.
            ** rewrite !extendVarSetList_append.
               apply WellScoped_mkLams.
               eapply (HWSpairs _ HIn).
          }
          assert (P (captured ++ map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs')) e
                    (go (captured ++ map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs')) (freeVars (toExpr e)))).
          { 
            apply IH.
            ** NCore_termination.
            ** rewrite !extendVarSetList_append.
               apply HWSe.
          }
          clear IH. revert n pairs' e captured HNoDup HWSpairs HWSe H H0.
          refine IH5.
      * (* Case [Case] *)
        clear IH1 IH2 IH3 IH4 IH5.
        simpl in *.

        do 2 expand_pairs. simpl.
        rewrite snd_unzip, !map_map.
        rewrite forM_map.

        destruct HWS as [HWSscrut HWSalts].
        rewrite Forall'_Forall in HWSalts.
        rewrite Forall_map in HWSalts.
        rewrite Forall_forall in HWSalts.

        assert (forall dc pats rhs (HIn : In (dc, pats, rhs) l),
            P (captured ++ v :: pats) rhs (go (captured ++ v :: pats ) (freeVars (toExpr rhs)))). {
          intros.
          apply IH.
          ** NCore_termination.
          ** (* This needs automation! *)
             rewrite extendVarSetList_append.
             apply (HWSalts _ HIn).
        }
        clear IH Hnext. rename l into alts.
        revert e v alts captured HWSscrut HWSalts H.
        refine IH6.
    }

    subst j_22__.
    clear IH. revert e captured HWS.
    refine IH7.
  Defined. (* important! *)

  (* We now uncurry the induction hypotheses
     (since we can’t do that right away in [go_ind_aux] *)
  Lemma uncurry_and : forall {A B C},
    (A /\ B -> C) -> (A -> B -> C).
  Proof. intros. intuition. Qed.
  Lemma under_imp: forall {A B C},
    (B -> C) -> (A -> B) -> (A -> C).
  Proof. intros. intuition. Qed.
  Ltac iterate n f x := lazymatch n with
    | 0 => x
    | S ?n => iterate n f uconstr:(f x)
  end.
  Ltac uncurryN n x :=
    let n' := eval compute in n in
    lazymatch n' with
    | 0 => x
    | S ?n => let uc := iterate n uconstr:(under_imp) uconstr:(uncurry_and) in
              let x' := uncurryN n x in
              uconstr:(uc x')
  end.
  Definition go_ind P
    := ltac:(let x := uncurryN 6 (proj2_sig (go_ind_aux P)) in exact x).
  Opaque go_ind go_ind_aux.

  (* Actually, we can simplify P to only take captured and e *)
  Definition go_ind' P := go_ind (fun captured e r => P captured e).

  (** ** Scope validity *)

  (** This predicate describes when a list of non-recursive bindings
      is ok to wrap around the [Let (Rec [pairs] body)] pair.

      (Maybe this could be abstracted over isvs and moved to [ScopeInvariants])
  *)
  Definition WellScopedFloats floats :=
    (* All added bindings are fresh with regard to the environment *)
    Forall (fun 'p => elemVarSet (fst p) isvs = false) floats /\
    (* All added bindings are fresh with regard to each other  *)
    NoDup (map (fun p => varUnique (fst p)) floats) /\
    (* All added bindings are well-scoped in the original environment  *)
    Forall (fun 'p => WellScoped (snd p) isvs) floats.

  (* Here we do the actual wrapping *)
  Lemma mkLets_WellScoped:
    forall exits' e,
    (* The body is well-scoped in the extended environment *)
    WellScoped e (extendVarSetList isvs (map fst exits')) ->
    WellScopedFloats exits' ->
    (* Then wrapping these bindings around [e] is well-scoped *)
    WellScoped (mkLets (map (fun '(v,rhs) => NonRec v rhs) exits') e) isvs.
   Proof.
    intros ?.
    unfold WellScopedFloats.
    generalize isvs as isvs.
    clear in_scope pairs jps.
    induction exits' as [|[v rhs] exits']; intros isvs' e Hbase Hfloats.
    * simpl. unfold Base.id. assumption.
    * simpl in *.
      destruct Hfloats as [Hfreshs [HNoDup Hrhss]].
      inversion HNoDup; subst; clear HNoDup. rename H1 into Hfresh, H2 into HNoDup.
      inversion_clear Hrhss. rename H into Hrhs, H0 into Hrhss.
      inversion_clear Hfreshs. rename H into Hfresh_v, H0 into Hfreshs.
      simpl in *.
      rewrite extendVarSetList_cons in Hbase.
      split; only 1: apply Hrhs.
      apply IHexits'.
      - assumption.
      - repeat split.
        + rewrite Forall_forall.
          rewrite Forall_forall in Hfreshs.
          rewrite in_map_iff in Hfresh.
          intros [v' rhs'] HIn.
          rewrite elemVarSet_extendVarSet.
          simpl_bool.
          split.
          ** simpl.
             destruct (Eq_eq (varUnique v') (varUnique v)); (reflexivity || exfalso).
             contradict Hfresh.
             exists (v', rhs'). split; assumption.
          ** apply Hfreshs. assumption.
        + assumption.
        + rewrite Forall_forall.
          rewrite Forall_forall in Hrhss.
          intros pair HIn. simpl.
          rewrite WellScoped_extendVarSet_fresh.
          apply Hrhss; assumption.
          eapply subVarSet_elemVarSet_false; only 2: eassumption.
          apply WellScoped_subset.
          apply Hrhss; assumption.
  Qed.

  (* the [addExit] function ensures that the new exit floats are well-scoped
     where we are going to put them.
   *)
  Lemma addExit_all_WellScopedFloats:
    forall captured ja e,
    WellScoped e isvs ->
    StateInvariant WellScopedFloats
                   (addExit (extendInScopeSetList in_scope2 captured) ja e).
  Proof.
    intros.
    (* This is much easier to prove by breaking the State abstraction and turning
       it into a simple function. *)
    unfold addExit, mkExitJoinId.
    unfold StateInvariant, SP,
           op_zgzgze__, return_, State.Monad__State, op_zgzgze____, return___,
           State.Monad__State_op_zgzgze__,
           State.Monad__State_return_,
           pure, State.Applicative__State , pure__,
           State.Applicative__State_pure,
           State.runState', State.get, State.put.
    simpl.
    intros floats Hfloats.
    set (v := uniqAway _ _).
    constructor; only 2: trivial.
    constructor; only 2: constructor; simpl.
    * constructor; only 2: apply Hfloats; simpl.
      unfold isvs, in_scope2 in *.
      apply elemVarSet_uniqAway.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      repeat apply subVarSet_extendVarSetList_l.
      apply subVarSet_refl.
    * constructor; only 2: apply Hfloats; simpl.
      rewrite <- map_map.
      rewrite <- elemVarSet_mkVarset_iff_In.
      rewrite not_true_iff_false.
      apply elemVarSet_uniqAway.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      apply subVarSet_extendVarSetList_r.
      apply subVarSet_refl.
    * constructor; only 2: apply Hfloats; simpl.
      assumption.
  Qed.


  (** in [go_exit], we [pick] variables to abstract over and [zap] them.
      That is somewhat involved, ([pick] is weird mix between a left-fold
      and a right fold) so extract their definitions to the top level
      and state lemmas about them.
   *)
  Definition zap := ltac:(
    let rhs := eval cbv beta delta [go_exit] in (go_exit [] (Type_ tt)  emptyVarSet) in
    lazymatch rhs with (let zap := ?rhs in ?body) =>
      exact rhs
    end
   ).

   Definition pick := ltac:(
    let rhs := eval cbv beta delta [go_exit] in (go_exit [] (Type_ tt)  emptyVarSet) in
    lazymatch rhs with (let zap' := _ in let abs_vars := let pick := @?rhs zap' in _ in _) =>
      let e' := eval cbv beta in (rhs zap) in
      exact e'
    end
    ).

  Lemma zap_ae: forall x, almostEqual x (zap x).
  Proof. intro v; unfold zap; destruct v; simpl; constructor. Qed.

  Lemma fst_pick_list:
    forall fvs vs xs,
    fst (fold_right pick (fvs,vs) xs) = fst (fold_right pick (fvs,[]) xs).
  Proof.
    induction xs.
    * reflexivity.
    * simpl. unfold pick at 1 3. do 2 expand_pairs.
      rewrite !IHxs. destruct_match; simpl; reflexivity.
  Qed.
  Lemma snd_pick_list: 
    forall fvs vs xs,
    snd (fold_right pick (fvs,vs) xs) = snd (fold_right pick (fvs,[]) xs) ++ vs.
  Proof.
    induction xs.
    * reflexivity.
    * simpl. unfold pick at 1 3. do 2 expand_pairs.
      rewrite !fst_pick_list. simpl. destruct_match; simpl.
      + rewrite IHxs. reflexivity. 
      + rewrite IHxs. reflexivity. 
  Qed.
  
  Lemma WellScoped_picked:
    forall fvs captured e,
    WellScoped e (extendVarSetList fvs captured) ->
    WellScoped e (extendVarSetList fvs (snd (fold_right pick (exprFreeVars e, []) captured))).
  Proof.
    induction captured using rev_ind; intros e HWSe; simpl.
    * simpl. assumption.
    * simpl.
      rewrite fold_right_app.
      rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil in HWSe.
      simpl.
      destruct_match; simpl.
      + rewrite snd_pick_list.
        rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
        rewrite <- WellScoped_Lam.
        erewrite delVarSet_ae by (apply zap_ae).
        rewrite <- exprFreeVars_Lam.
        apply IHcaptured.
        rewrite -> WellScoped_Lam.
        rewrite <- WellScoped_extendVarSet_ae by apply zap_ae.
        assumption.
      + apply IHcaptured.
        rewrite WellScoped_extendVarSet_fresh in HWSe; assumption.
  Qed.
  
  Lemma Forall_app:
    forall a P (xs ys : list a),
    Forall P xs -> Forall P ys ->
    Forall P (xs ++ ys).
  Proof.
    intros. induction xs; try assumption. constructor.
    inversion H; assumption.
    apply IHxs. inversion H; assumption.
  Qed.

  (* This following lemma verifies the bugfix of #15110 *)
  Lemma WellScopedVar_picked_aux:
    forall vsis captured fvs,
    Forall (fun v => WellScopedVar v (extendVarSetList vsis captured))
           (snd (fold_right pick (fvs, []) captured)) /\
    Forall (fun v => elemVarSet v fvs = true)
           (snd (fold_right pick (fvs, []) captured)).
  Proof.
    induction captured using rev_ind; intros.
    * constructor; constructor.
    * simpl.
      rewrite fold_right_app.
      simpl.
      rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
      destruct_match.
      + rewrite snd_pick_list.
        specialize (IHcaptured (delVarSet fvs x)).
        destruct IHcaptured as [IH1 IH2].
        split; apply Forall_app.
        - rewrite Forall_forall in *.
          intros v HIn. specialize (IH1 v HIn). specialize (IH2 v HIn).
          change (WellScoped (Mk_Var v) (extendVarSet (extendVarSetList vsis captured) x)).
          apply WellScoped_extendVarSet_fresh; only 2: apply IH1.
          rewrite exprFreeVars_Var.
          apply not_true_is_false.
          rewrite elemVarSet_unitVarSet.
          rewrite elemVarSet_delVarSet in *.
          intuition.
        - constructor; only 2: constructor.
          change (WellScoped (Mk_Var (zap x)) (extendVarSet (extendVarSetList vsis captured) x)).
          rewrite WellScoped_extendVarSet_ae by (apply zap_ae).
          apply WellScopedVar_extendVarSet.
        - rewrite Forall_forall in *.
          intros v HIn. specialize (IH1 v HIn). specialize (IH2 v HIn).
          rewrite elemVarSet_delVarSet in *.
          intuition.
        - constructor; only 2: constructor.
          erewrite <- elemVarSet_ae by (apply zap_ae).
          assumption.
       + specialize (IHcaptured fvs).
         destruct IHcaptured as [IH1 IH2].
         split.
        - rewrite Forall_forall in *.
          intros v HIn. specialize (IH1 v HIn). specialize (IH2 v HIn).
          change (WellScoped (Mk_Var v) (extendVarSet (extendVarSetList vsis captured) x)).
          apply WellScoped_extendVarSet_fresh; only 2: apply IH1.
          rewrite exprFreeVars_Var.
          apply not_true_is_false.
          rewrite elemVarSet_unitVarSet.
          eapply elemVarSet_false_true; eassumption.
        - rewrite Forall_forall in *.
          intros v HIn. specialize (IH1 v HIn). specialize (IH2 v HIn).
          assumption.
  Qed.

  Lemma WellScopedVar_picked:
    forall vsis captured fvs,
    Forall (fun v => WellScopedVar v (extendVarSetList vsis captured))
           (snd (fold_right pick (fvs, []) captured)).
  Proof. intros. apply WellScopedVar_picked_aux. Qed.


  Lemma go_exit_all_WellScopedFloats captured e : 
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    disjointVarSet (exprFreeVars (toExpr e)) recursive_calls = true ->
    StateInvariant WellScopedFloats (go_exit captured (toExpr e) (exprFreeVars (toExpr e))).
  Proof.
    intros HWSe Hdisjoint.
    set (P := WellScopedFloats).
    cbv beta delta [go_exit]. (* No [zeta]! *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_16__). {
      clearbody j_16__; cleardefs.
      destruct (collectArgs _) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Second case *)
    subst j_16__.
    enough (Hnext: StateInvariant P j_15__). {
      destruct (negb is_interesting) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Third case *)
    subst j_15__.
    enough (Hnext: StateInvariant P j_14__). {
      destruct captures_join_points ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Third case: Actual exitification *)
    subst j_14__.
    unfold recursive_calls in Hdisjoint.
    apply StateInvariant_bind_return.
    apply addExit_all_WellScopedFloats.
    rewrite WellScoped_mkLams.
    subst abs_vars.
    float_let.
    cleardefs.

    rewrite Foldable.hs_coq_foldr_list.
    apply WellScoped_picked.

    (* [e] captures nothing in [fs] *)
    rewrite <- WellScoped_mkLams.
    rewrite <- WellScoped_mkLams in HWSe.
    unfold isvsp in HWSe.
    rewrite WellScoped_extendVarSetList_fresh in HWSe; only 1: assumption.
    rewrite hs_coq_map in Hdisjoint.
    rewrite map_map in Hdisjoint.
    rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in Hdisjoint
         by (intros; repeat expand_pairs; destruct a; reflexivity).
    fold fs in Hdisjoint.
    eapply disjointVarSet_subVarSet_l; only 1 : eassumption.
    rewrite exprFreeVars_mkLams.
    apply subVarSet_delVarSetList.
  Qed.

  Lemma go_all_WellScopedFloats captured e: 
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    StateInvariant WellScopedFloats (go captured (freeVars (toExpr e))).
  Proof.
    revert e captured.
    refine (go_ind (fun _ _ => _) _ _ _ _ _ _ _ ); intros.
    * apply go_exit_all_WellScopedFloats; assumption.
    * apply StateInvariant_bind_return.
      apply H.
    * apply StateInvariant_bind; only 1: apply H.
      intros. apply StateInvariant_bind_return. apply H0.
    * apply StateInvariant_bind_return.
      apply H.
    * apply StateInvariant_bind.
      - apply StateInvariant_forM.
        intros [j params rhs] HIn.
        simpl.
        erewrite idJoinArity_join by eassumption.
        rewrite collectNAnnBndrs_freeVars_mkLams.
        apply StateInvariant_bind_return.
        apply (H _ _ _ _ HIn).
      - intro x.
        apply StateInvariant_bind_return.
        apply H0.
    * (* Case [Case] *)
      simpl in *.
      apply StateInvariant_bind_return.
      apply StateInvariant_forM.
      intros [[dc pats] rhs] HIn.
      apply StateInvariant_bind_return.
      apply (H _ _ _ HIn).
    * apply StateInvariant_return.
  Qed.

  (* Clearly we expect the input pairs be well-scoped *)
  Variable pairs_WS :
    Forall (fun p => WellScoped (snd p) isvsp) (map toJPair pairs) .

  Lemma all_exists_WellScoped:
    WellScopedFloats exits.
  Proof.
    unfold exits.
    unfold pairs'_exits.
    unfold ann_pairs.
    rewrite hs_coq_map.
    do 2 rewrite forM_map.
    eapply SP_snd_runState.
    * apply StateInvariant_forM.
      intros [v params rhs HisJoin] HIn.
      do 2 expand_pairs. simpl.
      erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      apply StateInvariant_bind_return.
      apply go_all_WellScopedFloats.
      + rewrite <- WellScoped_mkLams.
        rewrite Forall_map in pairs_WS.
        rewrite Forall_forall in pairs_WS.
        unfold in_scope2.
        apply (pairs_WS _ HIn).
    * repeat split; constructor.
  Qed.

  Definition sublistOf {a} (xs ys : list a) := incl ys xs.

  Lemma sublistOf_cons {a} x (xs ys : list a):
    sublistOf ys (x :: xs) <-> (In x ys /\ sublistOf ys xs).
  Proof.
    intros.
    unfold sublistOf, incl.
    intuition.
    destruct H; subst; auto.
  Qed.

  Lemma isvs_to_isvs':
     forall e, WellScoped e isvs -> WellScoped e isvs'.
  Proof.
    intros.
    apply WellScoped_extendVarSetList.
    rewrite disjointVarSet_mkVarSet.
    rewrite Forall_map. simpl.
    apply all_exists_WellScoped.
    assumption.
  Qed.

  Lemma isvsp_to_isvsp':
     forall e, WellScoped e isvsp -> WellScoped e isvsp'.
  Proof.
    intros.
    unfold isvsp, isvsp' in *.
    rewrite <- WellScoped_mkLams.
    rewrite <- WellScoped_mkLams in H.
    apply isvs_to_isvs'.
    assumption.
  Qed.

  Lemma isvsp_to_isvsp'_extended:
     forall e vs, WellScoped e (extendVarSetList isvsp vs) -> WellScoped e (extendVarSetList isvsp' vs).
  Proof.
    intros.
    rewrite <- WellScoped_mkLams.
    rewrite <- WellScoped_mkLams in H.
    apply isvsp_to_isvsp'.
    assumption.
  Qed.

  Lemma isvsp_to_isvsp'_extended_Var:
     forall v vs, WellScopedVar v (extendVarSetList isvsp vs) -> WellScopedVar v (extendVarSetList isvsp' vs).
  Proof.
    intros.
    change (WellScoped (Mk_Var v) (extendVarSetList isvsp' vs)).
    apply isvsp_to_isvsp'_extended.
    assumption.
  Qed.


  Lemma isvsp_to_isvsp'_extended2:
     forall e vs1 vs2,
     WellScoped e (extendVarSetList (extendVarSetList isvsp vs1) vs2) ->
     WellScoped e (extendVarSetList (extendVarSetList isvsp' vs1) vs2).
  Proof.
    intros.
    rewrite <- WellScoped_mkLams.
    rewrite <- WellScoped_mkLams in H.
    apply isvsp_to_isvsp'_extended.
    assumption.
  Qed.

  Lemma addExit_all_WellScopedVar:
    forall captured ja e,
    let after := extendVarSetList isvsp' captured in
    RevStateInvariant (sublistOf exits) 
         (addExit (extendInScopeSetList in_scope2 captured) ja e)
         (fun v => WellScopedVar v after).
  Proof.
    intros.
    (* This is much easier to prove by breaking the State abstraction and turning
       it into a simple function. *)
    unfold addExit, mkExitJoinId.
    unfold RevStateInvariant, SP,
           op_zgzgze__, return_, State.Monad__State, op_zgzgze____, return___,
           State.Monad__State_op_zgzgze__,
           State.Monad__State_return_,
           pure, State.Applicative__State , pure__,
           State.Applicative__State_pure,
           State.runState', State.get, State.put.
    simpl.
    intros floats Hfloats.
    set (v := uniqAway _ _) in *.
    apply sublistOf_cons in Hfloats.
    destruct Hfloats as [HIn HsublistOf].
    apply in_map with (f := fst) in HIn. simpl in HIn.
    split; only 1: assumption.
    subst after.
    apply WellScopedVar_extendVarSetList_l; only 1: apply WellScopedVar_extendVarSetList_l.
    * apply WellScopedVar_extendVarSetList_r; only 1: assumption.
      rewrite map_map.
      apply all_exists_WellScoped.
    * apply elemVarSet_uniqAway.
      unfold in_scope2.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      apply subVarSet_extendVarSetList_l.
      apply subVarSet_extendVarSetList_l.
      apply subVarSet_extendVarSetList_r.
      apply subVarSet_refl.
    * apply elemVarSet_uniqAway.
      unfold in_scope2.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      apply subVarSet_extendVarSetList_l.
      apply subVarSet_extendVarSetList_r.
      apply subVarSet_refl.
  Qed.

  (* No we go through [go] again and see that pairs' is well-scoped.
     We start assuming that the result of the computation is a subset of exits'
     for which we already know [WellScopedFloats]. By going backwards,
     we will recover that [mkExit] produces a name of this set.
  *)

  Lemma go_exit_res_WellScoped captured e : 
    let orig := extendVarSetList isvsp captured in
    let after := extendVarSetList isvsp' captured in
    WellScoped (toExpr e) orig ->
    disjointVarSet (exprFreeVars (toExpr e)) recursive_calls = true ->
    RevStateInvariant (sublistOf exits) (go_exit captured (toExpr e) (exprFreeVars (toExpr e))) (fun e' => WellScoped e' after).
  Proof.
    intros ?? HWSe Hdisjoint.

    set (P := fun x => RevStateInvariant (sublistOf exits) x (fun e' => WellScoped e' after)).
    change (P (go_exit captured (toExpr e) (exprFreeVars (toExpr e)))).

    cbv beta delta [go_exit]. (* No [zeta]! *)
    repeat float_let.

    (* Common case *)
    assert (Hreturn : P (return_ (toExpr e))). {
       apply RevStateInvariant_return. cleardefs.
       apply isvsp_to_isvsp'_extended; assumption.
    } 

    (* First case *)
    enough (Hnext: P j_16__). {
      clearbody j_16__; cleardefs.
      destruct (collectArgs _) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply Hreturn.
    }
    cleardefs.

    (* Second case *)
    subst j_16__.
    enough (Hnext: P j_15__). {
      destruct (negb is_interesting) ; try apply Hnext.
      apply Hreturn.
    }
    cleardefs.

    (* Third case *)
    subst j_15__.
    enough (Hnext: P j_14__). {
      destruct (captures_join_points) ; try apply Hnext.
      apply Hreturn.
    }
    cleardefs.

    (* Third case: Actual exitification *)
    subst j_14__.
    subst P. cleardefs. 
    unfold recursive_calls in Hdisjoint.
    eapply RevStateInvariant_bind; only 1: apply addExit_all_WellScopedVar.
    intro v.
    apply RevStateInvariant_return.
    intro HWSv.
    rewrite WellScoped_mkVarApps.
    split; only 1 : apply HWSv.
    subst abs_vars.
    eapply Forall_impl.
    * intros v' HWSv'.
      apply isvsp_to_isvsp'_extended_Var.
      apply HWSv'.
    * subst zap0. fold zap. fold pick. simpl.
      rewrite Foldable.hs_coq_foldr_list.
      apply WellScopedVar_picked.
  Qed.

  Lemma go_res_WellScoped captured e: 
    let orig := extendVarSetList isvsp captured in
    let after := extendVarSetList isvsp' captured in
    WellScoped (toExpr e) orig ->
    RevStateInvariant (sublistOf exits) (go captured (freeVars (toExpr e))) (fun e' => WellScoped e' after).
  Proof.
    revert e captured.
    apply (go_ind (fun captured _ r => RevStateInvariant (sublistOf exits) r (fun e' => WellScoped e' (extendVarSetList isvsp' captured))));
      intros; set (after := extendVarSetList isvsp' captured).
    * apply go_exit_res_WellScoped; assumption.
    * eapply RevStateInvariant_bind.
      - apply H.
      - intro e'; apply RevStateInvariant_return; intro He'.
        rewrite  extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil in He'.
        simpl.
        rewrite deAnnotate_freeVars.
        split.
        ++ apply isvsp_to_isvsp'_extended. apply HWS.
        ++ apply He'.
    * unfold CoreBndr in *.
      eapply RevStateInvariant_bind; only 2: (intro body'; eapply RevStateInvariant_bind; only 2: intro hs').
      - apply H.
      - apply H0.
      - apply RevStateInvariant_return; intros Hrhs' Hbody'.
        split.
        ** rewrite WellScoped_mkLams.
           rewrite extendVarSetList_append in Hbody'.
           apply Hbody'.
        ** rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil in Hrhs'.
           apply Hrhs'.
   *  eapply RevStateInvariant_bind; only 1: apply H.
      intro body'. apply RevStateInvariant_return; intros Hbody'.
      rewrite extendVarSetList_append in Hbody'.
      split; only 2: split.
      ++ rewrite !map_map.
         rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => varUnique x)
           by (intros; repeat expand_pairs; destruct a; reflexivity).
         apply HNoDup.
      ++ rewrite Forall'_Forall.
         rewrite !map_map. 
         rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x)
           by (intros; repeat expand_pairs; destruct a; reflexivity).
         rewrite Forall_map.
         eapply Forall_impl; only 2: apply HWSpairs.
         intros [v rhs] HWSv. simpl in *.
         rewrite deAnnotate_freeVars.
         apply isvsp_to_isvsp'_extended2; assumption.
            ++ rewrite !map_map.
               rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x)
                  by (intros; repeat expand_pairs; destruct a; reflexivity).
               apply Hbody'.
     * eapply RevStateInvariant_bind.
       - apply RevStateInvariant_forM2 with
              (R := fun p p' =>
                  (fun '(Mk_NJPair x _ _ _) => x) p = fst p' /\
                  WellScoped (snd p') (extendVarSetList after (map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs'0)))).
         intros [j rhs] HIn.
         simpl.
         erewrite idJoinArity_join by eassumption.
         rewrite collectNAnnBndrs_freeVars_mkLams.
         eapply RevStateInvariant_bind.
         ++ apply (H _ _ _ _ HIn).
         ++ intro e'; apply RevStateInvariant_return; intro He'.
            simpl.
            rewrite WellScoped_mkLams.
            rewrite !extendVarSetList_append in He'.
            split; only 1: reflexivity.
            apply He'.
      - intro pairs''.
        eapply RevStateInvariant_bind; only 1: apply H0.
        intro e'; apply RevStateInvariant_return; intros He' Hpairs''.
        apply Forall2_and in Hpairs''.
        destruct Hpairs'' as [Hfst Hpairs''].
        apply Forall2_const_Forall in Hpairs''.
        eapply Forall2_eq with (f := (fun '(Mk_NJPair x _ _ _) => x)) (g := fst) in Hfst.
        symmetry in Hfst.
        change ((@map (CoreBndr * Expr CoreBndr) CoreBndr (@fst CoreBndr (Expr CoreBndr)) pairs'') = map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs'0)) in Hfst.
        simpl.
        rewrite Hfst.
        split; only 2: split.
        -- simpl in HNoDup.
           rewrite map_map.
           rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => varUnique x)
             by (intros; repeat expand_pairs; destruct a; reflexivity).
           apply HNoDup.
        -- rewrite Forall'_Forall.
           apply Hpairs''.
        -- rewrite !extendVarSetList_append in He'.
           apply He'.
      * (* [Case] *)
        simpl.
        eapply RevStateInvariant_bind.
        + apply RevStateInvariant_forM with (R := fun alt => WellScopedAlt v alt after).
          intros [[dc pats] rhs] HIn.
          eapply RevStateInvariant_bind.
          - apply (H _ _ _  HIn).
          - intro e'; apply RevStateInvariant_return; intro He'.
            rewrite extendVarSetList_append in He'.
            apply He'.
        + intros alts'; apply RevStateInvariant_return; intro He.
          simpl. split.
          - rewrite deAnnotate_freeVars.
            apply isvsp_to_isvsp'_extended; assumption.
          - rewrite Forall'_Forall.
            apply He.
  * apply RevStateInvariant_return.
    apply isvsp_to_isvsp'_extended.
    assumption.
  Qed.

  Lemma pairs'_WS:
    Forall (fun p => WellScoped (snd p) isvsp') pairs'.
  Proof.
    unfold pairs', pairs'_exits, ann_pairs.
    eapply RevStateInvariant_runState with (P := sublistOf exits).
    * rewrite hs_coq_map, !map_map, forM_map.
      apply RevStateInvariant_forM.
      intros [v param rhs HisJoin] HIn.
      unfold id.
      simpl.
      erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      eapply RevStateInvariant_bind.
      ++ apply go_res_WellScoped.
         ** rewrite <- WellScoped_mkLams.
            rewrite Forall_map in pairs_WS.
            rewrite Forall_forall in pairs_WS.
            apply (pairs_WS _ HIn).
        ++ intro e'; apply RevStateInvariant_return; intro He'.
           simpl.
           rewrite WellScoped_mkLams.
           apply He'.
    * change (sublistOf exits exits).
      intro. auto.
  Qed.

  Lemma map_fst_pairs':
    map (@fst CoreBndr (Expr CoreBndr)) pairs' = fs.
  Proof.
    intros.
    unfold fs.
    unfold pairs', pairs'_exits, ann_pairs.
    unfold Traversable.forM, flip.
    unfold Traversable.mapM, Traversable.Traversable__list, Traversable.mapM__, Traversable.Traversable__list_mapM.
    unfold Traversable.Traversable__list_traverse.
    unfold liftA2, State.Applicative__State, liftA2__, State.Applicative__State_liftA2.
    unfold State.Applicative__State_op_zlztzg__.
    unfold State.runState.
    expand_pairs; simpl.
    unfold pure, pure__, State.Applicative__State_pure.
    unfold op_zgzgze__, State.Monad__State, op_zgzgze____,State.Monad__State_op_zgzgze__.
    unfold Bifunctor.second, Bifunctor.Bifunctor__pair_type, Bifunctor.second__,
           Bifunctor.Bifunctor__pair_type_second, Bifunctor.Bifunctor__pair_type_bimap.
    unfold id.
    generalize (@nil (prod JoinId CoreExpr)) as s.
    clear pairs_WS.
    induction pairs.
    * reflexivity.
    * intro.
      simpl. repeat (expand_pairs; simpl); destruct a; simpl.
      f_equal.
      apply IHl.
  Qed.

  (** Main well-scopedness theorem:
      If the input is well-scoped, then so is the output of [exitifyRec].*)
  Theorem exitifyRec_WellScoped:
    forall body,
    NoDup (map varUnique fs) ->
    WellScoped body isvsp ->
    WellScoped (mkLets (exitifyRec (extendInScopeSetList in_scope fs) (map toJPair pairs)) body) isvs.
  Proof.
    intros ? HNoDup HWSbody.
    cbv beta delta [exitifyRec].
    zeta_with go_exit.
    zeta_with recursive_calls.
    zeta_with go.
    zeta_with ann_pairs.
    fold pairs'_exits.
    expand_pairs.
    fold pairs'.
    fold exits.
    rewrite flat_map_unpack_cons_f.
    change (WellScoped (mkLets (map (fun '(x, y) => NonRec x y) exits ++ [Rec pairs']) body) isvs).
    rewrite mkLets_append, mkLets_cons, mkLets_nil.
    apply mkLets_WellScoped.
    * rewrite WellScoped_MkLet.
      simpl in *.
      rewrite map_fst_pairs'.
      repeat split.
      + assumption.
      + rewrite Forall'_Forall in *.
        apply pairs'_WS.
      + apply isvsp_to_isvsp'.
        assumption.
    * apply all_exists_WellScoped.
  Qed.

(* Join point stuff commented after updating Exitify.hs to GHC HEAD


  (** ** Join point validity *)

  (** When is the result of [mkExitLets] valid? *)
  
  Lemma mkExitLets_JPI:
    forall exits' e jps',
    isJoinPointsValid e 0 (updJPSs jps' (map fst exits')) = true ->
    forallb (fun '(v,rhs) => isJoinId v) exits' = true ->
    forallb (fun '(v,rhs) => isJoinPointsValidPair v rhs jps') exits' = true ->
    isJoinPointsValid (mkExitLets exits' e) 0 jps' = true.
  Proof.
    intros ??.
    induction exits' as [|[v rhs] exits']; intros jps' Hbase HiJI Hpairs.
    * simpl. unfold Base.id. assumption.
    * simpl in *; fold isJoinPointsValidPair in *.
      simpl_bool.
      destruct HiJI as [HiJIv HiJIvs].
      destruct Hpairs as [Hpair Hpairs].
      split.
      - assumption. 
      - apply IHexits'.
        + assumption.
        + assumption.
        + eapply forallb_imp. apply Hpairs.
          intros [v' rhs'].
          unfold updJPS. rewrite HiJIv.
          apply isJoinPointValidPair_extendVarSet.
  Qed.


  Lemma addExit_all_joinIds:
    forall in_scope_set ty ja e,
    StateInvariant (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)
                   (addExit in_scope_set ty ja e).
  Proof.
    set (P := (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)).
    intros.
    unfold addExit.
    eapply SP_bind with (R := fun v => isJoinId v = true).
    * unfold mkExitJoinId.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply SP_return.
        (* Here we actually show that we only generate join ids *)
        rewrite isJoinId_eq.
        rewrite isJoinId_maybe_uniqAway.
        rewrite isJoinId_maybe_setIdOccInfo.
        rewrite isJoinId_maybe_asJoinId.
        reflexivity.
    * intros x HiJI.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply StateInvariant_bind_return.
        apply SP_put.
        subst P.
        simpl; simpl_bool. split; assumption.
  Qed.

  Lemma go_all_joinIds:
    forall captured ann_e,
    StateInvariant (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)
                   (go captured ann_e).
  Proof.
    set (P := (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)).
    (* This cannot be structural recursion. Will need a size on expression. *)
    fix 2. rename go_all_joinIds into IH.
    intros.
    replace go with (go_f go) by admit. (* Need to use [go_eq] here *)
    cbv beta delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_37__). {
      destruct (collectArgs e) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Second case *)
    subst j_37__.
    enough (Hnext: StateInvariant P j_36__). {
      destruct (is_exit && negb is_interesting) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Third case *)
    subst j_36__.
    enough (Hnext: StateInvariant P j_35__). {
      destruct (is_exit && captures_join_points ) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Third case: Actual exitification *)
    subst j_35__.
    enough (Hnext: StateInvariant P j_22__). {
      destruct is_exit ; try apply Hnext.
      apply StateInvariant_bind_return.
      apply addExit_all_joinIds.
    }
    clear is_exit isCapturedVarArg is_interesting captures_join_points args e fvs.

    (* Fourth case: No exitification here, so descend*)
    subst j_22__.
    enough (Hnext: StateInvariant P j_4__). {
      destruct ann_e as [fvs e] eqn:Hann.
      destruct e; try apply Hnext.
      * (* Case [Case] *)
        apply StateInvariant_bind_return.
        apply StateInvariant_forM.
        intros [[dc pats] rhs] HIn.
        apply StateInvariant_bind_return.
        apply IH.
      * (* Case Let *) 
        repeat float_let.

        enough (Hnext': StateInvariant P j_18__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId_maybe j) as [join_arity|] eqn:HiJI; try apply Hnext'.
          destruct (collectNAnnBndrs join_arity rhs) as [params join_body].
          apply StateInvariant_bind.
          + apply IH.
          + intros. apply StateInvariant_bind_return.
            apply IH.
        }

        subst j_18__.
        enough (Hnext': StateInvariant P j_10__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId (Tuple.fst (Panic.head pairs'))); try apply Hnext'.
          + intros.
            apply StateInvariant_bind.
            - apply StateInvariant_forM.
              intros [j rhs] HIn.
              repeat float_let.
              destruct (collectNAnnBndrs join_arity rhs) as [params join_body].
              apply StateInvariant_bind_return.
              apply IH.
            - intro x.
              apply StateInvariant_bind_return.
              apply IH.
        }

        subst j_10__.
        apply StateInvariant_bind_return.
        apply IH.
    }

    subst j_4__.
    apply StateInvariant_return.

  (* Not structurally recursive *)
  Fail Guarded.
  Admitted.

  Lemma all_exists_joinIds:
    forallb (fun '(v, _) => isJoinId v) exits = true.
  Proof.
    unfold exits.
    unfold pairs'_exits.
    eapply SP_snd_runState.
    * apply StateInvariant_forM.
      intros [v rhs] HIn.
      expand_pairs.
      apply StateInvariant_bind_return.
      apply go_all_joinIds.
    * reflexivity.
  Qed.

  (* TODO: There would be less repetition if we have a 
    [isJoinPointsValidJoinPair] that implies both 
    [isJoinPointsValidPair] and [isJoinId] *)
    
  Lemma isJoinPointsValid_delVarSet_nonJP:
    forall e jps n a,
    isJoinId a = false ->
    isJoinPointsValid e n (delVarSet jps a) = isJoinPointsValid e n jps.
  Admitted.
  Lemma isJoinPointsValid_delVarSetList_mono:
    forall e jps n vs,
    isJoinPointsValid e n (delVarSetList jps vs) = true -> isJoinPointsValid e n jps = true.
  Admitted.

  Lemma isJoinPointsValid_updJPSs_irrelevant:
    forall e jps n vs,
    forallb (fun v => negb (isJoinId v) || negb (elemVarSet v (exprFreeVars e))) vs = true ->
    isJoinPointsValid e n (updJPSs jps vs) = true ->
    isJoinPointsValid e n jps = true.
  Admitted.

  Lemma isJoinPointvalid_collectNBinders:
    forall v rhs jps ja args body,
    isJoinPointsValidPair v rhs jps = true ->
    isJoinId_maybe v = Some ja ->
    collectNBinders ja rhs = (args,body) ->
    isJoinPointsValid body 0 (updJPSs jps args) = true.
  Admitted.

  Lemma addExit_all_valid:
    forall in_scope_set jps ty ja args e,
    (* The RHS needs to be valid *)
    isJoinPointsValid e 0 jps = true -> 
    (* The join arity should match the number of lambdas added *)
    ja = (length args) ->
    (* No argument may be a join point *)
    forallb (fun a => negb (isJoinId a)) args = true ->

    StateInvariant (fun xs => forallb (fun '(v, rhs) => isJoinPointsValidPair v rhs jps) xs = true)
                   (addExit in_scope_set ty ja (mkLams args e)).
  Proof.
    clear jps.
    intros.
    set (P := (fun xs => forallb _ xs = true)).
    unfold addExit.
    eapply SP_bind with (R := fun v => isJoinId_maybe v = Some ja).
    * unfold mkExitJoinId.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply SP_return.
        (* Here we actually show that we only generate join ids *)
        rewrite isJoinId_maybe_uniqAway.
        rewrite isJoinId_maybe_setIdOccInfo.
        rewrite isJoinId_maybe_asJoinId.
        reflexivity.
    * intros x HiJI.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply StateInvariant_bind_return.
        apply SP_put.
        subst P.
        simpl; simpl_bool.
        split; only 2: assumption.
        unfold isJoinPointsValidPair, isJoinPointsValidPair_aux.
        rewrite HiJI.
        subst.
        (* Zoom past the Lams *)
        clear HPxs.
        clear HiJI.
        revert dependent jps.  clear jps.
        induction args; intros jps HiJPVe.
        + simpl. cbn. assumption.
        + replace ((length (a :: args))) with (1 + (length args)) by admit.
          destruct (Nat.eqb_spec (1 + (length args)) 0); only 1: lia.
          replace (mkLams (a :: args) e) with (Lam a (mkLams args e)) by reflexivity.
          cbn -[Nat.add].
          destruct (Nat.ltb_spec (1 + (length args)) 1); only 1: lia.
          replace (1 +  (length args) =? 1) with ((length args) =? 0) by admit.
          replace (1 +  (length args) - 1) with ( (length args)) by admit.
          simpl in H1. simpl_bool. destruct H1.
          apply IHargs.
          ** apply H1.
          ** rewrite negb_true_iff in H0.
             rewrite isJoinPointsValid_delVarSet_nonJP by assumption.
             assumption.
  Admitted.

  Lemma go_all_valid:
    forall captured ann_e,
    isJoinPointsValid (deAnnotate ann_e) 0 (updJPSs jps captured) = true ->
    StateInvariant (fun xs => forallb (fun '(v, rhs) => isJoinPointsValidPair v rhs jps) xs = true)
                   (go captured ann_e).
  Proof.
    set (P := (fun xs => forallb _ xs = true)).
    (* This cannot be structural recursion. Will need a size on expression. *)
    fix 2. rename go_all_valid into IH.
    intros ?? HiJPVe.
(*     rewrite go_eq. *)
    replace go with (go_f go) by admit. (* Need to use [go_eq] here *)
    cbv beta delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_37__). {
      destruct (collectArgs e) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Second case *)
    subst j_37__.
    enough (Hnext: StateInvariant P j_36__). {
      destruct (is_exit && negb is_interesting) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Third case *)
    subst j_36__.
    enough (Hnext: (is_exit && captures_join_points = false) ->
                   StateInvariant P j_35__). {
      destruct (is_exit && captures_join_points).
      * apply StateInvariant_return.
      * apply Hnext. reflexivity.
    }
    intro Hno_capture.

    (* Third case: Actual exitification *)
    subst j_35__.
    enough (Hnext: StateInvariant P j_22__). {
      clearbody j_22__ j_4__.
      destruct is_exit ; try apply Hnext.
      apply StateInvariant_bind_return.
      assert (HniJIargs: forallb (fun a : Var => negb (isJoinId a)) args = true)
        by admit. (* Needs to relate [any] to [forallb] *)
      apply addExit_all_valid.
      * apply isJoinPointsValid_updJPSs_irrelevant with (vs := captured).
        + admit. (* Need lemma about [forallb] and [filter] *)
        + assumption.
      * admit. (* Need Base theory here *)
      * assumption.
    }
    clear is_exit is_interesting captures_join_points args e fvs Hno_capture.

    (* Fourth case: No exitification here, so descend*)
    subst j_22__.
    enough (Hnext: StateInvariant P j_4__). {
      destruct ann_e as [fvs e] eqn:Hann.
      destruct e; try apply Hnext.
      * (* Case [Case] *)
        apply StateInvariant_bind_return.
        apply StateInvariant_forM.
        intros [[dc pats] rhs] HIn.
        apply StateInvariant_bind_return.
        apply IH.
        (* This is boring stuff here... *)
        simpl in HiJPVe. simpl_bool. destruct HiJPVe.
        rewrite forallb_forall in H0.
        specialize (H0 (dc, pats, deAnnotate rhs)).
        simpl; rewrite updJPSs_append, updJPSs_cons.
        simpl_bool.
        apply H0.
        rewrite in_map_iff.
        exists (dc, pats, rhs). split. reflexivity. assumption.

      * (* Case Let *) 
        repeat float_let.

        enough (Hnext': StateInvariant P j_18__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId_maybe j) as [join_arity|] eqn:HiJI; try apply Hnext'.
          destruct (collectNAnnBndrs _ _) as [params join_body] eqn:Hrhs.
          assert (collectNBinders join_arity (deAnnotate rhs) = (params, deAnnotate join_body)) by admit.
          apply StateInvariant_bind.
          + apply IH.
            (* Boring stuff *)
            simpl in HiJPVe. simpl_bool. destruct HiJPVe.
            rewrite updJPSs_append.
            eapply isJoinPointvalid_collectNBinders; try eassumption.
          + intros. apply StateInvariant_bind_return.
            apply IH.
            simpl in HiJPVe. simpl_bool. destruct HiJPVe.
            rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
            apply H1.
        }

        subst j_18__.
        enough (Hnext': StateInvariant P j_10__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          simpl deAnnotate in HiJPVe.
          replace (flat_map _ _) with (map (fun '(v,e) => (v, deAnnotate e)) pairs') in HiJPVe by admit.
          simpl in HiJPVe. simpl_bool. destruct HiJPVe. destruct H. destruct H0.
          rewrite orb_true_iff in H1.
          destruct H1.
          + (* No join ids *)
            replace (isJoinId (Tuple.fst _)) with false.
            assumption.
            symmetry.
            destruct pairs' as [|[j rhs] pairs'']; try inversion H.
            simpl in H1. simpl_bool. destruct H1. rewrite negb_true_iff in H1. simpl in H1.
            admit. (* Need to unfold Panic.head *)
          + (* All join ids *)
            replace (isJoinId (Tuple.fst _)) with true by admit. (* like above *)

            rewrite forallb_forall in H0.
            rewrite forallb_forall in H1.
            rewrite !map_map in *.
            replace (map _ _) with (map fst pairs') in H0
                  by (apply map_ext; intro; destruct a; reflexivity).
            replace (map _ _) with (map fst pairs') in H2
                  by (apply map_ext; intro; destruct a; reflexivity).

            apply StateInvariant_bind.
            - apply StateInvariant_forM.
              intros [j rhs] HIn.
              repeat float_let.
              destruct (collectNAnnBndrs join_arity rhs) as [params join_body] eqn:Hrhs.
              assert (collectNBinders join_arity (deAnnotate rhs) = (params, deAnnotate join_body)) by admit.
              apply StateInvariant_bind_return.
              apply IH.
              rewrite !updJPSs_append.
              eapply isJoinPointvalid_collectNBinders.
              ** Fail apply H0. (* ugh *)
                 specialize (H0 (j, deAnnotate rhs)).
                 simpl in H0.
                 apply H0.
                 apply in_map_iff. eexists. split; [|eassumption]. reflexivity.
              ** apply isJoinId_isJoinId_maybe.
                 specialize (H1 (j, deAnnotate rhs)). simpl in H1.
                 apply H1.
                 apply in_map_iff. eexists. split; [|eassumption]. reflexivity.
              ** apply H3.
            - intro x.
              apply StateInvariant_bind_return.
              apply IH.
              rewrite updJPSs_append.
              apply H2.
        }

        subst j_10__.
        apply StateInvariant_bind_return.
        apply IH.
        rewrite updJPSs_append.
        simpl (deAnnotate _) in HiJPVe.
        admit. (* We need to again look at both cases of Rec and NonRec,
                  deal with deAnnotate, to get to the statement about the base case.
                  (Or refactor isJoinPointsValid to not require that) *)
    }

    subst j_4__.
    apply StateInvariant_return.

  (* Not structurally recursive *)
  Fail Guarded.
  Admitted.

  Lemma all_exists_valid:
    forallb (fun '(v, rhs) => isJoinPointsValidPair v rhs jps) exits = true.
  Proof.
    unfold exits.
    unfold pairs'_exits.
    eapply SP_snd_runState.
    * apply StateInvariant_forM.
      intros [v rhs] HIn.
      expand_pairs.
      apply StateInvariant_bind_return.
      apply go_all_valid.
      eapply isJoinPointvalid_collectNBinders.
      + admit. (* Need to thread in invariant here *)
      + admit. (* Yeah, we really should also show that these are join ids here *)
      + admit. (* Lemma bout collectNBinders and collectNAnnBndrs. @lastland? *)
    * reflexivity.
  Admitted.

  (** Main result *)

  Theorem exitifyRec_JPI:
    forall body,
    pairs <> [] ->
    isJoinPointsValid (Let (Rec (map toJPair pairs)) body) 0 jps = true ->
    isJoinPointsValid (exitifyRec (extendInScopeSetList in_scope (map (fun '(Mk_NJPair v _ _ _) => v) pairs)) (map toJPair pairs) body) 0 jps = true.
  Proof.
    intros.
    cbv beta delta [exitifyRec].
    cbv zeta.
    fold recursive_calls.
    fold go.
    fold ann_pairs.
    fold pairs'_exits.
    fold mkExitLets.
    expand_pairs.
    fold pairs'.
    fold exits.
    change (isJoinPointsValid (mkExitLets exits (mkLetRec pairs' body)) 0 jps = true).
    apply mkExitLets_JPI.
    * admit.
    * apply all_exists_joinIds.
    * apply all_exists_valid.
  Admitted.
*)

End in_exitifyRec.
