Require Import GHC.Base.
Import GHC.Base.Notations.
Import GHC.Base.ManualNotations.

Require Import Core.
Require Import CoreSubst.

Require Import Coq.Lists.List.

Require Import Proofs.GhcTactics.
Require Import Proofs.Base.
Require Import Proofs.CoreInduct.
Require Import Proofs.Core.

(* Require Import Proofs.VarSetFSet. *)
Require Import Proofs.VarSet.
Require Import Proofs.Var.

Require Import Proofs.ScopeInvariant.


Opaque Base.hs_string__.
Opaque GHC.Err.default.

Open Scope nat_scope.
Set Bullet Behavior "Strict Subproofs".

Hint Constructors NoDup.

(* Actually from Coq.Program.Tactics. *)
Ltac destruct_one_pair :=
 match goal with
   | [H : (_ /\ _) |- _] => destruct H
   | [H : prod _ _ |- _] => destruct H
 end.


Lemma StateL_surjective_pairing : forall {s} {a} (x: Utils.StateL s a), 
    x = Utils.Mk_StateL (Utils.runStateL x).
Proof.
  intros. destruct x. simpl.
  auto.
Qed.


(** [mapAccumL] instance for lists *)

(*
-- |The 'mapAccumL' function behaves like a combination of 'fmap'
-- and 'foldl'; it applies a function to each element of a structure,
-- passing an accumulating parameter from left to right, and returning
-- a final value of this accumulator together with the new structure.
mapAccumL :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)
mapAccumL f s t = runStateL (traverse (StateL . flip f) t) s *)

(* 
mapAccumL               :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumL f s []        =  (s, [])
mapAccumL f s (x:xs)    =  (s'',y:ys)
                           where (s', y ) = f s x
                                 (s'',ys) = mapAccumL f s' xs
*)




Lemma mapAccumL_nil : forall a b c  (f : a -> b -> (a * c)) (s : a), 
   Traversable.mapAccumL f s nil = (s, nil).
Proof.
  intros a b c f s.
  unfold Traversable.mapAccumL.
  unfold Traversable.traverse,Traversable.Traversable__list, 
         Traversable.traverse__ , 
         Traversable.Traversable__list_traverse.
  simpl.
  auto.
Qed.

Lemma mapAccumL_cons : forall a b c x (xs : list b) (f : a -> b -> (a * c)) (s : a), 
   Traversable.mapAccumL f s (cons x xs) = 
   let '(s',y) := f s x in
   let '(s'',ys) := Traversable.mapAccumL f s' xs in
   (s'', cons y ys).
Proof.
  intros a b c x xs f s.
  unfold Traversable.mapAccumL.
  unfold Traversable.traverse,Traversable.Traversable__list, 
         Traversable.traverse__ , 
         Traversable.Traversable__list_traverse.
  rewrite Base.hs_coq_foldr_base.
  unfold op_z2218U__.
  simpl.
  unfold Utils.runStateL,liftA2, liftA2__, 
  Utils.Applicative__StateL,Utils.Applicative__StateL_liftA2,
  pure,pure__,Utils.Applicative__StateL_pure in *.
  destruct (fold_right
        (fun (x0 : b) (ys : Utils.StateL a (list c)) =>
         match ys with
         | Utils.Mk_StateL ky =>
             Utils.Mk_StateL
               (fun s0 : a =>
                let
                '(s', x1) := flip f x0 s0 in
                 let '(s'', y) := ky s' in (s'', x1 :: y))
         end) (Utils.Mk_StateL (fun s0 : a => (s0, nil))) xs) eqn:EQ.
  unfold flip.
  auto.
Qed.

(** [zip] and [unzip] *)

Lemma unzip_zip : forall A B l (la : list A)( lb : list B),
          List.unzip l = (la,lb) ->
          l = List.zip la lb.
Proof.
  induction l; intros; simpl. 
  - inversion H; simpl; auto.
  - destruct a as [a b].
    simpl in H.
    destruct (List.unzip l) as [as_ bs].
    inversion H. subst.
    simpl.
    erewrite IHl.
    eauto.
    eauto.
Qed.

Lemma unzip_equal_length : 
  forall A B l (al:list A) (bl:list B), 
    List.unzip l = (al,bl) -> length al = length bl.
Proof.                           
  induction l. intros; simpl in *. inversion H. auto.
  intros; simpl in *.
  destruct a as [a b].
  destruct (List.unzip l) eqn:UL.
  inversion H. subst.
  simpl.
  f_equal.
  eauto.
Qed.

 
Lemma length_zip : forall {a}{b} (xs : list a) (ys :list b), 
             length xs = length ys ->
             length xs = length (List.zip xs ys).
Proof.
  induction xs; intros; destruct ys; simpl in *; try discriminate.
  auto.
  inversion H.
  erewrite IHxs; eauto.
Qed.



Lemma map_fst_zip : forall A B  (l2:list B) (l1 : list A), 
    length l2 = length l1 -> List.map fst (List.zip l2 l1) = l2.
  intros A B l2. 
  induction l2; intros; simpl in *. auto.
  destruct l1; simpl in *.
  inversion H.
  f_equal. 
  apply IHl2.
  inversion H.
  auto.
Qed.  

(* SCW: this one seems a bit specialized. replace with the more 
   general analogue to the above? *)
Lemma map_snd_zip : 
  forall {a}{b}{c} (f:b -> c) (xs : list a) ys , 
    length xs = length ys ->
    (map (fun ps => f (snd ps)) (List.zip xs ys)) =
    (map f ys).
Proof.
  induction xs; intros; destruct ys; simpl in H; inversion H.
  - simpl. auto.
  - simpl. rewrite IHxs. auto. auto.
Qed.


Lemma In_zip_fst : forall {A B} {x:A}{y:B} {xs}{ys}{C}(zs: list C),
             In (x,y) (List.zip xs ys) ->
             length ys = length zs ->
             exists z, In (x,z) (List.zip xs zs).
Proof.
  induction xs; intros; destruct ys; destruct zs; 
    simpl in *; inversion H0; clear H0; try contradiction.
  - destruct H. inversion H; subst. eauto.
    edestruct IHxs; eauto.
Qed.

Lemma In_zip_snd : forall {A B} {x:A}{y:B} {xs}{ys}{C}(zs: list C),
             In (x,y) (List.zip xs ys) ->
             length xs = length zs ->
             exists z, In (z,y) (List.zip zs ys).
Proof.
  induction xs; intros; destruct ys; destruct zs; 
    simpl in *; inversion H0; clear H0; try contradiction.
  - destruct H. inversion H; subst. eauto.
    edestruct IHxs; eauto.
Qed.


Lemma In_zip_swap : forall {A B} {x:A}{y:B} {xs}{ys},
      In (x,y) (List.zip xs ys) -> In (y,x) (List.zip ys xs).
Proof.
  induction xs; intros; destruct ys; 
    simpl in *; inversion H; try contradiction.
  - inversion H0; subst. eauto.
  - right. eapply IHxs; eauto.
Qed.


Lemma In_zip_map : 
  forall {A B : Type} {f : A -> B} {x:A}{y:B}{xs},
       In (x,y) (List.zip xs (map f xs)) -> y = f x.
Proof.
  induction xs; intros; 
    simpl in *; inversion H; try contradiction.
  - inversion H0; subst. eauto.
  - eapply IHxs; eauto.
Qed.

Lemma In_zip : forall {a} {b} (x:a) (y:b) xs ys, 
    In (x,y) (List.zip xs ys) -> In x xs /\ In y ys.
Proof.
  induction xs;
  intros; destruct ys; simpl in H; try contradiction.
  destruct H as [h0 | h1].
  - inversion h0; subst.
    split; econstructor; eauto.
  - simpl. edestruct IHxs; eauto.
Qed.




(* ---------------------------- *)

(** [uniqAway] axiomatization *)

(* If uniqAway returns a variable with the same unique, 
   it returns the same variable. *)      
Axiom uniqAway_eq_same : forall v in_scope_set,
    (uniqAway in_scope_set v == v) = true ->
    (uniqAway in_scope_set v = v).

(* The variable returned by uniqAway is fresh. *)
Axiom uniqAway_lookupVarSet_fresh : forall v in_scope_set,
    lookupVarSet (getInScopeVars in_scope_set) (uniqAway in_scope_set v) = None.

(* If uniqAway returns a fresh variable, then the original was already in scope. *)
(* SCW: Maybe we could do without this axiom (and I would like to), 
   but it would complicate the reasoning. *)
Axiom uniqAway_fresh_in_scope : forall v in_scope_set, 
     (uniqAway in_scope_set v == v) = false ->
     exists v', lookupVarSet (getInScopeVars in_scope_set) v = Some v' /\ almostEqual v v'.


(* ---------------------------- *)
    
(** [InScopeSet] *) 
Require Import Coq.omega.Omega.

Lemma extend_getInScopeVars : forall in_scope_set v, 
      (extendVarSet (getInScopeVars in_scope_set) v) = 
      (getInScopeVars (extendInScopeSet in_scope_set v)).
Proof. 
  intros.
  unfold extendVarSet, getInScopeVars, extendInScopeSet.
  destruct in_scope_set.
  unfold extendVarSet. auto.
Qed.

Lemma extendList_getInScopeVars : forall in_scope_set v, 
      (extendVarSetList (getInScopeVars in_scope_set) v) = 
      (getInScopeVars (extendInScopeSetList in_scope_set v)).
Proof. 
  intros.
  unfold extendVarSetList, getInScopeVars, extendInScopeSetList.
  destruct in_scope_set.
  unfold extendVarSet. auto.
Qed.


Lemma extendInScopeSetList_cons : forall v vs in_scope_set,
           (extendInScopeSetList in_scope_set (v :: vs) = 
            (extendInScopeSetList (extendInScopeSet in_scope_set v) vs)).
Proof.
  unfold extendInScopeSetList.
  destruct in_scope_set.
  unfold_Foldable_foldl.
  simpl.
  f_equal.
  unfold Pos.to_nat.
  unfold Pos.iter_op.
  omega.
Qed.

Lemma extendInScopeSetList_nil : forall in_scope_set,
           extendInScopeSetList in_scope_set nil = in_scope_set.
Proof.
  unfold extendInScopeSetList.
  destruct in_scope_set.
  unfold_Foldable_foldl.
  simpl.
  f_equal.
  omega.
Qed.

Hint Rewrite extend_getInScopeVars extendList_getInScopeVars extendInScopeSetList_nil 
             extendInScopeSetList_cons : varset.

(** [VarSet] *)

Notation "s1 {<=} s2" := (StrongSubset s1 s2) (at level 70, no associativity).
Notation "s1 {=} s2" := (StrongSubset s1 s2 /\ StrongSubset s2 s1) (at level 70, no associativity).


Lemma lookupVarSet_extendVarSetList_self:
  forall vars v vs,
    In v vars -> 
    lookupVarSet (extendVarSetList vs vars) v = Some v.
Admitted.

Definition freshList vars vs :=
  (forall v, In v vars -> lookupVarSet vs v = None).

Lemma freshList_app :
  forall v l1 l2, freshList (l1 ++ l2) v <-> freshList l1 v /\ freshList l2 v.
Admitted.

Lemma StrongSubset_extendVarSet_fresh : 
  forall vs var, lookupVarSet vs var = None ->
            StrongSubset vs (extendVarSet vs var).
Admitted.

Lemma StrongSubset_extendVarSetList_fresh : 
  forall vs vars, freshList vars vs ->
             StrongSubset vs (extendVarSetList vs vars).
Admitted.


Lemma filterVarSet_extendVarSet : 
  forall f v vs,
    filterVarSet f (extendVarSet vs v) = 
    if (f v) then extendVarSet (filterVarSet f vs) v 
    else (filterVarSet f vs).
Proof.  
Admitted.


Lemma lookupVarSet_filterVarSet_true : forall f v vs,
  f v = true ->
  lookupVarSet (filterVarSet f vs) v = lookupVarSet vs v.
Proof.
  intros.
Admitted.

Lemma lookupVarSet_filterVarSet_false : forall f v vs,
  f v = false ->
  lookupVarSet (filterVarSet f vs) v = None.
Proof.
  intros.
Admitted.


Definition minusDom {a} (vs : VarSet) (e : VarEnv a) : VarSet :=
  let keep := fun v => negb (elemVarEnv v e) in
  filterVarSet keep vs.

Lemma StrongSubset_minusDom {a} : forall vs1 vs2 (e: VarEnv a), 
    vs1 {<=} vs2 ->
    minusDom vs1 e {<=} minusDom vs2 e.
Admitted.

Lemma StrongSubset_minusDom_right {a} : forall vs (e: VarEnv a), 
    vs {<=} minusDom vs e.
Admitted.


Lemma lookupVarSet_minusDom :
  forall a (env : VarEnv a) vs v,
    lookupVarEnv env v = None -> 
    lookupVarSet (minusDom vs env) v = lookupVarSet vs v.
Proof.
  intros.
  unfold minusDom.
Admitted.


Lemma lookup_minusDom_inDom : forall a vs (env:VarEnv a) v',
    elemVarEnv v' env = true ->
    lookupVarSet (minusDom vs env) v' = None.
Proof.
  intros.
  unfold minusDom in *.
  rewrite lookupVarSet_filterVarSet_false; auto.  
  rewrite H.
  auto.
Qed.


Lemma StrongSubset_filterVarSet : 
  forall f1 f2 vs,
  (forall v, f1 v = true -> f2 v = true) ->
  filterVarSet f1 vs {<=} filterVarSet f2 vs.
Proof.  
Admitted.

Lemma minusDom_extend : 
  forall a vs (env : VarEnv a) v,
    minusDom (extendVarSet vs v) (delVarEnv env v) {<=} 
    extendVarSet (minusDom vs env) v.
Proof.
  intros.
  unfold StrongSubset.
  intros var.
Admitted.



Lemma lookup_minusDom_extend : forall a vs (env:VarEnv a) v v' e,
    v ==  v' <> true ->
    lookupVarSet (minusDom (extendVarSet vs v) (extendVarEnv env v e)) v' =
    lookupVarSet (minusDom vs env) v'.
Proof.
  intros.
  unfold minusDom in *.
  destruct (elemVarEnv v' env) eqn:Eenv; auto.
  + (* v' is in dom of env. so cannot be lookup up. *)
    rewrite 2 lookupVarSet_filterVarSet_false; auto.  
    rewrite Eenv. simpl. auto.
    rewrite elemVarEnv_extendVarEnv_neq.
    rewrite Eenv. simpl. auto.
    auto.
  + rewrite 2 lookupVarSet_filterVarSet_true; auto.  
    rewrite lookupVarSet_extendVarSet_neq; auto.
    auto.
    rewrite Eenv. simpl. auto.
    rewrite elemVarEnv_extendVarEnv_neq.
    rewrite Eenv. simpl. auto.
    auto.
Qed.




(** [VarEnv] *)

Axiom lookupVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A),
    (v1 == v2) = true ->
    lookupVarEnv vs v1 = lookupVarEnv vs v2.

Axiom elemVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A),
    (v1 == v2) = true ->
    elemVarEnv v1 vs = elemVarEnv v2 vs.


Axiom lookupVarEnv_extendVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A) val, 
    v1 == v2 = true ->
    lookupVarEnv (extendVarEnv vs v1 val) v2 = Some val.

Axiom lookupVarEnv_extendVarEnv_neq :
  forall A v1 v2 (vs : VarEnv A) val, 
    v1 == v2 <> true ->
    lookupVarEnv (extendVarEnv vs v1 val) v2 = lookupVarEnv vs v2.

Axiom elemVarEnv_extendVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A) val, 
    v1 == v2 = true ->
    elemVarEnv v2 (extendVarEnv vs v1 val) = true.

Axiom elemVarEnv_extendVarEnv_neq :
  forall A v1 v2 (vs : VarEnv A) val, 
    v1 == v2 <> true ->
    elemVarEnv v2 (extendVarEnv vs v1 val) = elemVarEnv v2 vs.


Axiom elemVarEnv_delVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A), 
    v1 == v2 = true ->
    elemVarEnv v2 (delVarEnv vs v1) = false.


Axiom lookupVarEnv_delVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A), 
    v1 == v2 = true ->
    lookupVarEnv (delVarEnv vs v1) v2 = None.

Axiom lookupVarEnv_delVarEnv_neq :
  forall A v1 v2 (vs : VarEnv A), 
    v1 == v2 <> true ->
    lookupVarEnv (delVarEnv vs v1) v2 = lookupVarEnv vs v2.




(* ---------------------------------------------------------------- *)

(** [subst_expr] simplification lemmas *)

Lemma subst_expr_App : forall s subst e1 e2, 
    subst_expr s subst (App e1 e2) = 
    App (subst_expr s subst e1) (subst_expr s subst e2).
    Proof. 
      intros. unfold subst_expr. simpl. 
      f_equal.
      destruct e1; simpl; auto.
      destruct e2; simpl; auto.
Qed.

Lemma subst_expr_Tick : forall doc subst tic e, 
        subst_expr doc subst (Tick tic e) = 
        CoreUtils.mkTick (substTickish subst tic) (subst_expr doc subst e).
Proof.
  intros. 
  unfold subst_expr, CoreUtils.mkTick, substTickish. simpl.
  destruct e; simpl; auto.
Qed.

Lemma subst_expr_Lam : forall s subst bndr body,
        subst_expr s subst (Lam bndr body) = 
        let (subst', bndr') := substBndr subst bndr in
        Lam bndr' (subst_expr s subst' body).
Proof.
  intros.
  unfold subst_expr. simpl.
  destruct (substBndr subst bndr) as [subst' bndr']. 
  f_equal.
Qed.

Lemma subst_expr_LetNonRec : forall s subst c e0 body,
  subst_expr s subst (Let (NonRec c e0) body) = 
    let (subst', bndr') := substBndr subst c in 
    Let (NonRec bndr' (subst_expr &"substBind" subst e0)) (subst_expr s subst' body).
Proof.      
  intros.
  unfold subst_expr. simpl.
  destruct substBndr as [subst' bndr'].
  f_equal.
Qed.


Lemma subst_expr_Let : forall s subst bind body,
  subst_expr s subst (Let bind body) = 
   let '(subst', bind') := substBind subst bind in Let bind' (subst_expr s subst' body). 
Proof.
  intros.
  unfold subst_expr. fold subst_expr. 
  destruct substBind.
  auto.
Qed.

Lemma substBind_NonRec : forall subst c e0, 
    substBind subst (NonRec c e0) = 
    let '(subst', bndr') := substBndr subst c in 
    (subst', NonRec bndr' (subst_expr &"substBind" subst e0)).
Proof.
  intros.
  unfold substBind. 
  simpl.
  destruct substBndr.
  f_equal.
Qed.

Lemma substBind_Rec : forall subst pairs,
    substBind subst (Rec pairs) = 
    let '(bndrs, x)        := List.unzip pairs in 
    let '(subst'0, bndrs') := substRecBndrs subst bndrs in
    (subst'0 , Rec (List.zip bndrs' (map (fun ps : Var * CoreExpr => subst_expr &"substBind" subst'0 (snd ps)) pairs))).
Proof.
  intros.
  unfold substBind.
  simpl.
  destruct (List.unzip pairs).
  destruct (substRecBndrs subst l).
  f_equal.
Qed.


Definition substAlt str subst (alt:AltCon * list Core.Var * CoreExpr) := 
  let '((con,bndrs), rhs) := alt in
  let '(subst', bndrs') := substBndrs subst bndrs in
  (con, bndrs', subst_expr str subst' rhs).

Lemma subst_expr_Case : forall str s e b u l, 
    subst_expr str s (Case e b u l) = 
    let '(subst', bndr') := substBndr s b in 
    Case (subst_expr str s e) bndr' tt (map (substAlt str subst') l).
Proof. intros.  simpl.
destruct (substBndr s b) as [subst' bndr'].       
f_equal. destruct e; reflexivity.
Qed.

Lemma subst_expr_Cast : forall doc subst e co, 
   subst_expr doc subst (Cast e co) = 
   Cast (subst_expr doc subst e) tt.
Proof.
  intros. 
  unfold subst_expr. simpl.
  f_equal.
  destruct e; simpl; auto.
Qed.


Hint Rewrite subst_expr_App subst_expr_Case subst_expr_Cast 
     substBind_NonRec substBind_Rec subst_expr_Let subst_expr_Lam
     subst_expr_Tick : subst.


Tactic Notation "simp" "subst" "in" hyp(H) :=
  autorewrite with subst in H.

Tactic Notation "simp" "subst" "in" "*" :=
  autorewrite with subst in *.

Tactic Notation "simp" "subst" :=
  autorewrite with subst.



(* ---------------------------------------------------------------- *)


Definition getSubstInScopeVars (s : Subst) : VarSet :=
  match s with 
  | Mk_Subst i e _ _ => getInScopeVars i
  end.


(* When calling (subst subst tm) it should be the case that
   the in_scope_set in the substitution describes the scope after 
   the substituition has been applied.

  That means that it should be a superset of both:

  (SIa) The free vars of the range of the substitution
  (SIb) The free vars of ty minus the domain of the substitution

  We enforce this by requiring

    - the current scope minus the domain is a strongSubset of in_scope_set
    - the range of the subst_env is wellscoped according to the in_scope_set

*)


Definition WellScoped_Subst  (s : Subst) (vs:VarSet) :=
  match s with 
  | Mk_Subst in_scope_set subst_env _ _ => 

    (minusDom vs subst_env) {<=} (getInScopeVars in_scope_set) /\
    
    forall var, 
      (match lookupVarEnv subst_env var with
        | Some expr => WellScoped expr (getInScopeVars in_scope_set)
        | None => True
        end)
  end.

Ltac destruct_WellScoped_Subst := 
    match goal with
      | [H0 : WellScoped_Subst ?s ?vs |- _ ] => 
         unfold WellScoped_Subst in H0;
         try (is_var s ; destruct s);
         destruct H0
  end.


Lemma WellScoped_Subst_StrongSubset : forall vs1 s vs2,
  vs2 {<=} vs1 -> 
  WellScoped_Subst s vs1 ->
  WellScoped_Subst s vs2.
Proof.
  intros.
  destruct_WellScoped_Subst.
  repeat split; auto.
  eapply (StrongSubset_trans (minusDom vs1 i0)); auto.
  eapply StrongSubset_minusDom; eauto.
Qed.



(* ---------------------------------------- *)


Definition Disjoint {a} (l1 l2 : list a) :=
  Forall (fun x => ~ In x l2) l1. 

Lemma NoDup_append : forall {a} (l1 l2 : list a), 
    NoDup l1 ->
    NoDup l2 ->
    Disjoint l1 l2 ->
    NoDup (l1 ++ l2).
Proof.
  induction l1.
  intros. simpl. auto.
  intros. simpl.
  inversion H. inversion  H1.
  subst.
  econstructor.
  - intro x.
    apply in_app_or in x.
    destruct x; eauto.
  - eapply IHl1; eauto.
Qed.


(* ---------------------------------------- *)

(* This property describes the invariants we need about the freshened
   binder list and new substitution returned by substBndrs.  
  
  - [s2] is a substitution extended from [s1] by the freshened [vars'] 
  - This means that the inscope set of s2 is s1 ++ vars 

    [This prop does not talk about the part of the domain of s1 that is 
    eliminated from s2 because we've reused a bound variable.]
*)

Definition SubstExtends (s1 : Subst) (vars  : list Var) 
                        (s2 : Subst) (vars' : list Var) : Prop :=

  length vars = length vars' /\

  NoDup vars' /\

  match (s1, s2) with 
    | (Mk_Subst i1 e1 _ _ , Mk_Subst i2 e2 _ _) => 

      (* The new variables are fresh for the original substitution. *)
      freshList vars' (getInScopeVars i1) /\

      (* For the in_scope_set:  new = old + vars' *) 
      (getInScopeVars i2) {=} (extendVarSetList (getInScopeVars i1) vars') /\

      (* ... and we can subtract out the old binders. *)      
      (minusDom (extendVarSetList (getInScopeVars i1) vars) e2 {<=} 
                getInScopeVars i2) /\ 

      (* Anything in the new substitution is either a renamed variable from
         the old substitution or was already in the old substitution *)
      forall var val, lookupVarEnv e2 var = Some val -> 
                 (exists var2, val = (Mk_Var var2) /\ In var2 vars') \/
                 match lookupVarEnv e1 var with 
                   | Some val2 => val = val2
                   | None      => False
                 end 

  end.


Ltac destruct_SubstExtends := 
  repeat 
    match goal with 
    | [ H : SubstExtends ?s1 ?vs ?s2 ?vs1 |- _ ] => 
      try (is_var s1 ; destruct s1);
      try (is_var s2 ; destruct s2);
      unfold SubstExtends in H; repeat (destruct_one_pair)
    end.


(* Prove goals about lookupVarSet, given StrongSubset assumptions *)
Ltac lookup_StrongSubset :=
    match goal with 
      [ h1 : StrongSubset (extendVarSetList ?i3 ?vars1) ?i,
        h2 : forall v:Var, In v ?vars1 -> lookupVarSet ?i3 v = None,
        m  : lookupVarSet ?i ?v  = ?r |- 
             lookupVarSet ?i3 ?v = ?r ] =>
      let k := fresh in
      assert (k : StrongSubset i3 i); 
        [ eapply StrongSubset_trans with (vs2 := (extendVarSetList i3 vars1)); 
          eauto;
          eapply StrongSubset_extendVarSetList_fresh; eauto |
          unfold StrongSubset in k;
          specialize (k v);
          rewrite m in k;
          destruct (lookupVarSet i3 v) eqn:LY;
          [contradiction| auto]]
    end.


Lemma SubstExtends_refl : forall s vars, 
    NoDup vars ->
    SubstExtends s vars s vars.
Admitted.


Lemma SubstExtends_trans : forall s2 s1 s3 vars1 vars2 vars1' vars2', 
    Disjoint vars1' vars2' ->
    SubstExtends s1 vars1 s2 vars1' -> SubstExtends s2 vars2 s3 vars2'-> 
    SubstExtends s1 (vars1 ++ vars2) s3 (vars1' ++ vars2').
Proof.
  intros.
  destruct_SubstExtends.
  repeat split; auto.
  - rewrite app_length. rewrite app_length. auto.
  - admit.
  - rewrite freshList_app.
    split; auto.
    unfold freshList in *.
    intros v IN.
    match goal with [ f2 : forall v:Var, In v vars2' -> _ |- _ ] =>
                    pose (m := f2 _ IN); clearbody m end.
    lookup_StrongSubset.
  - 
Admitted.


(* To be usable with the induction hypothesis inside a renamed scope, 
   we need to know that the new substitution is wellscoped with respect 
   to the old list of binders. *)

Lemma SubstExtends_WellScoped_Subst : forall s1 s2 vs vars vars', 
    SubstExtends s1 vars s2 vars' ->
    WellScoped_Subst s1 vs ->
    WellScoped_Subst s2 (extendVarSetList vs vars).
Proof.
  intros.
  destruct_WellScoped_Subst.
  destruct_SubstExtends.
  simpl in *.
  split. 
  {
    eapply StrongSubset_trans; eauto.
    eapply StrongSubset_minusDom.  
    intro var.
Admitted. 
(*
  eapply StrongSubset_extendVarSetList; eauto.
  intro var.
  destruct lookupVarEnv eqn:LU; auto.
  specialize (H4 var c LU).
  destruct H4 as [[var2 [EQ IN]]| h0].
  + subst.
    unfold WellScoped.
    eapply WellScopedVar_StrongSubset; eauto.
    unfold WellScopedVar.
    rewrite lookupVarSet_extendVarSetList_self.
    eapply almostEqual_refl.
    auto.
  + specialize (H1 var).
    destruct lookupVarEnv.
    ++ subst.
       eapply WellScoped_StrongSubset; eauto.
       eapply StrongSubset_trans; eauto.
       eapply StrongSubset_extendVarSetList_fresh.
       auto.
    ++ contradiction.
Qed.    *)



Lemma WellScoped_substBody : forall doc vs vars vars' body s1 s2,
   forall (IH : forall subst,  
      WellScoped_Subst subst (extendVarSetList vs vars) ->
      WellScoped (subst_expr doc subst body) (getSubstInScopeVars subst)),
   SubstExtends s1 vars s2 vars' ->     
   WellScoped_Subst s1 vs ->      
   WellScoped (subst_expr doc s2 body) 
              (extendVarSetList (getSubstInScopeVars s1) vars').
Proof.
  intros.
  destruct s1.
  simpl.
  rewrite extendList_getInScopeVars.
  eapply WellScoped_StrongSubset.
  eapply IH.
  eapply SubstExtends_WellScoped_Subst; eauto.
  destruct s2.
  simpl.
  rewrite <- extendList_getInScopeVars.
  destruct_SubstExtends. auto.
Qed.  


(* THIS WORKS for the Lam case !!! *)
Lemma WellScoped_substIdBndr : forall doc s rec_subst in_scope_set 
                                 env subst' bndr' body v vs,
  forall (IH : forall (in_scope_set : InScopeSet) (env : IdSubstEnv),
      WellScoped_Subst (Mk_Subst in_scope_set env tt tt) (extendVarSet vs v) ->
      WellScoped (subst_expr s (Mk_Subst in_scope_set env tt tt) body) 
                 (getInScopeVars in_scope_set)),
  forall (SB : substIdBndr doc rec_subst (Mk_Subst in_scope_set env tt tt) v = 
          (subst', bndr')),
  WellScoped_Subst (Mk_Subst in_scope_set env tt tt) vs ->
  WellScoped (subst_expr s subst' body) 
             (extendVarSet (getInScopeVars in_scope_set) bndr').
Proof. 
  intros.
  rewrite extend_getInScopeVars.
  match goal with [ H0 : WellScoped_Subst ?ss ?vs |- _ ] => 
                  destruct H0 as [SS LVi] end.
  unfold substIdBndr in SB. simpl in SB. inversion SB. subst. clear SB. 
  (* Case analysis on whether we freshen the binder v. *)
  destruct (uniqAway in_scope_set v == v) eqn:NC.
  + (* Binder is already fresh enough. *)
    apply uniqAway_eq_same in NC.
    rewrite NC.
    eapply IH; auto.
    split.
    pose (K := uniqAway_lookupVarSet_fresh v in_scope_set). clearbody K.
    rewrite NC in K.
    -- rewrite <- extend_getInScopeVars.
       eapply StrongSubset_trans with 
           (vs2 := extendVarSet (minusDom vs env) v).
       eapply minusDom_extend.
       eapply StrongSubset_extend.
       auto.
    -- intro var.
       destruct (v == var) eqn:Evvar.
       rewrite lookupVarEnv_delVarEnv_eq; auto.
       rewrite lookupVarEnv_delVarEnv_neq.
       specialize (LVi var).
       destruct (lookupVarEnv env var); auto.
       rewrite <- extend_getInScopeVars.
       eapply WellScoped_StrongSubset; eauto.
       
       eapply StrongSubset_extend_fresh.
       rewrite <- NC.
       eapply uniqAway_lookupVarSet_fresh.
       unfold CoreBndr in *. intro h. rewrite h in Evvar. discriminate.
         
  + (* Binder needs to be freshened. *)
    eapply IH; auto.
    (* Need to prove that the new substitution (i.e. extended with the 
       fresh binder) is WellScoped with respect to the old vs with the 
       addition of the old binder. *)
    (* NOTE: the renamed binder *could* be in the domain of the subst env. *)
    pose (K := uniqAway_lookupVarSet_fresh v in_scope_set). clearbody K.
    set (v' := uniqAway in_scope_set v) in *.

    split.
    -- rewrite <- extend_getInScopeVars.
      pose (M := SS v'). clearbody M.
      rewrite K in M.
      destruct (lookupVarSet (minusDom vs env) v') eqn:LVS; try contradiction; clear M.

       intro var.
       destruct (v' == var) eqn:EQ;
       [rewrite (lookupVarSet_extendVarSet_eq); eauto|
        rewrite (lookupVarSet_extendVarSet_neq); auto].
       ++ assert (v == var = false). 
          admit.
          rewrite lookup_minusDom_extend.
          rewrite (lookupVarSet_eq) with (v2 := v'); eauto.
          rewrite LVS. auto.
          rewrite Base.Eq_sym. auto.
          intro h. rewrite h in H. discriminate.
       ++ destruct (var == v) eqn:EQ2.
         rewrite lookupVarSet_eq with (v2 := v); eauto.
         rewrite lookup_minusDom_inDom. auto.
         apply elemVarEnv_extendVarEnv_eq.
         apply Base.Eq_refl.
         rewrite lookup_minusDom_extend; eauto.
         eapply SS.
         rewrite Base.Eq_sym.
         intro h. rewrite h in EQ2. discriminate.
       ++ intro h. rewrite h in EQ. discriminate.
    -- intro var.
       destruct (v == var) eqn:Eq_vvar.
       rewrite lookupVarEnv_extendVarEnv_eq.
       unfold WellScoped.
       rewrite <- extend_getInScopeVars.
       unfold WellScopedVar.
       rewrite lookupVarSet_extendVarSet_eq.
       apply almostEqual_refl; auto.
       apply Base.Eq_refl; auto.
       auto.
       rewrite lookupVarEnv_extendVarEnv_neq.
       specialize (LVi var).
       destruct lookupVarEnv; auto.
       rewrite <- extend_getInScopeVars.
       eapply WellScoped_StrongSubset; eauto.
       eapply StrongSubset_extend_fresh.
       eapply uniqAway_lookupVarSet_fresh.
       unfold CoreBndr in *.
       intro h. rewrite h in Eq_vvar. discriminate.
Admitted.



Lemma WellScoped_Subst_substBndr : forall subst subst' bndr bndr' v vs,
  forall (SB : substBndr subst v = (subst', bndr')),
  WellScoped_Subst subst vs ->
  SubstExtends subst (cons bndr nil) subst' (cons bndr' nil) /\
  WellScoped_Subst subst' (extendVarSet (getSubstInScopeVars subst) bndr').
Proof. 
  intros.
  destruct subst as [in_scope_set env u u0].
  match goal with [ H0 : WellScoped_Subst ?ss ?vs |- _ ] => 
                  destruct H0 as [SS LVi] end.
  unfold substBndr, substIdBndr in SB. simpl in SB. inversion SB. subst. clear SB. 
  (* Case analysis on whether we freshen the binder v. *)
  destruct (uniqAway in_scope_set v == v) eqn:NC.
  + (* Binder is already fresh enough. *)
    apply uniqAway_eq_same in NC.
    rewrite NC.
    unfold WellScoped_Subst.
    repeat split.
    -- econstructor.
       intro H; inversion H.
       econstructor.
    -- unfold freshList.
       intros v1 InV.
       rewrite (IntSetProofs.In_cons_iff v1 v  nil) in InV.
       destruct InV. subst. 
       rewrite <- NC.
       apply uniqAway_lookupVarSet_fresh. 
       inversion H.
    -- rewrite extendList_getInScopeVars.
       rewrite extendInScopeSetList_cons.
       rewrite extendInScopeSetList_nil.
       eapply StrongSubset_refl.
    -- rewrite extendList_getInScopeVars. 
       rewrite extendInScopeSetList_cons.
       rewrite extendInScopeSetList_nil.
       eapply StrongSubset_refl.
    -- admit.
    -- intros var val LE.
       destruct (v == var) eqn:Evvar.
       rewrite lookupVarEnv_delVarEnv_eq in LE; auto. discriminate.
       rewrite lookupVarEnv_delVarEnv_neq in LE.
       rewrite LE. auto.
       unfold CoreBndr in *. intro h. rewrite h in Evvar. discriminate.
    -- simpl.
       rewrite extend_getInScopeVars.
       admit. (* eapply StrongSubset_refl. *)
    -- intro var.
       destruct (v == var) eqn:Evvar.
       rewrite lookupVarEnv_delVarEnv_eq; auto.
       rewrite lookupVarEnv_delVarEnv_neq.
       specialize (LVi var).
       destruct (lookupVarEnv env var); auto.
       rewrite <- extend_getInScopeVars.
       eapply WellScoped_StrongSubset; eauto.       
       eapply StrongSubset_extend_fresh.
       rewrite <- NC.
       eapply uniqAway_lookupVarSet_fresh.
       unfold CoreBndr in *. intro h. rewrite h in Evvar. discriminate.
         
  + (* Binder needs to be freshened. *)
    unfold WellScoped_Subst.
    unfold SubstExtends.
    repeat split.
    -- admit.
    -- unfold freshList.
       intros v0 InV.
       rewrite (IntSetProofs.In_cons_iff) in InV.
       destruct InV. subst. 
       apply uniqAway_lookupVarSet_fresh. 
       inversion H.
    -- rewrite extendList_getInScopeVars.
       rewrite extendInScopeSetList_cons.
       rewrite extendInScopeSetList_nil.
       eapply StrongSubset_refl.
    -- rewrite extendList_getInScopeVars.
       rewrite extendInScopeSetList_cons.
       rewrite extendInScopeSetList_nil.
       eapply StrongSubset_refl.       
    -- admit.
    -- intros var val H.
       destruct (v == var) eqn:Eq_vvar.
       - rewrite lookupVarEnv_extendVarEnv_eq in H; auto.
         inversion H. subst. clear H.
         left. eexists. split; eauto.
         econstructor; eauto.
       - rewrite lookupVarEnv_extendVarEnv_neq in H; auto.
         rewrite H.
         right. auto.
         intro h. rewrite h in Eq_vvar. discriminate.
    -- simpl.
       rewrite extend_getInScopeVars.
       admit. (* eapply StrongSubset_refl. *)
    -- intros var.
       destruct (v == var) eqn:Eq_vvar.
       - 
         rewrite lookupVarEnv_extendVarEnv_eq; auto.
         unfold WellScoped, WellScopedVar.
         rewrite <- extend_getInScopeVars.
         rewrite lookupVarSet_extendVarSet_self.
         eapply almostEqual_refl.
       - rewrite lookupVarEnv_extendVarEnv_neq; auto.
         specialize (LVi var).
         destruct lookupVarEnv eqn:LU.
         rewrite <- extend_getInScopeVars.
         eapply WellScoped_StrongSubset; eauto.
         eapply StrongSubset_extendVarSet_fresh.
         eapply uniqAway_lookupVarSet_fresh.
         auto.
         intro h. rewrite h in Eq_vvar. discriminate.
Admitted.


Lemma WellScoped_substBndr : forall s in_scope_set env subst' bndr' body v vs u u0,
  forall (IH : forall (in_scope_set : InScopeSet) (env : IdSubstEnv) u u0,
      WellScoped_Subst (Mk_Subst in_scope_set env u u0) (extendVarSet vs v) ->
      WellScoped (subst_expr s (Mk_Subst in_scope_set env u u0) body) 
                 (getInScopeVars in_scope_set)),
  forall (SB : substBndr (Mk_Subst in_scope_set env u u0) v = (subst', bndr')),
  WellScoped_Subst (Mk_Subst in_scope_set env u u0) vs ->
  WellScoped (subst_expr s subst' body) 
             (extendVarSet (getInScopeVars in_scope_set) bndr').

Proof. 
  intros.
  edestruct WellScoped_Subst_substBndr with (bndr := v); eauto.
  destruct_SubstExtends.
  rewrite extend_getInScopeVars.
  eapply WellScoped_StrongSubset.
  eapply IH. clear IH. 
  all: try solve [rewrite <- extend_getInScopeVars; auto].
  clear H0.
  rewrite extendVarSetList_cons in *.
  rewrite extendVarSetList_nil in *.
  unfold WellScoped_Subst.
  split.
  - destruct_WellScoped_Subst. 
    destruct_WellScoped_Subst.
    simpl in *.
    eapply StrongSubset_trans with 
        (vs2 :=  minusDom (extendVarSet (getInScopeVars in_scope_set) v) i0); auto.
    eapply StrongSubset_minusDom.
    eapply StrongSubset_extend.
    eapply StrongSubset_trans; eauto. 
    eapply StrongSubset_minusDom_right; eauto.

  - intro var. 
    destruct lookupVarEnv eqn:LU; auto.
    match goal with
      [ H4 : forall var val, _ -> _ |- _ ]  =>
                        specialize (H4 var c);
                        destruct (H4 LU) as [[var2 [EQ In2]]| ?]; 
                        clear H4
        end.
    + subst c. 
      rewrite IntSetProofs.In_cons_iff in In2.
      destruct In2 as [?|ii]; try inversion ii. 
      subst.
      unfold WellScoped.
      eapply WellScopedVar_StrongSubset with 
      (vs1 := extendVarSet (getInScopeVars in_scope_set) var2); eauto.
      unfold WellScopedVar.    
      rewrite lookupVarSet_extendVarSet_self; eauto.
      eapply almostEqual_refl.
    + destruct_WellScoped_Subst.
      specialize (H6 var).
      rewrite LU in H6.
      auto.
Qed.

(*
Lemma WellScoped_Subst_substBndr : forall subst subst' v vs,
  forall (SB : substBndr subst v = (subst', bndr')),
  WellScoped_Subst subst vs ->
  WellScoped_Subst subst' vs.
Proof.
  intros.
  unfold substBndr in SB.
  eapply WellScoped_Subst_substIdBndr in SB; eauto.
  destruct subst'.
  eapply WellScoped_StrongSubset.
  eapply IH.
  eapply WellScoped_Subst_StrongSubset; eauto.
  unfold WellScoped_Subst in *.
  destruct SB. destruct H.
  
Qed.
*)

Ltac lift_let_in_eq H :=
   match goal with 
      | [ SB : (let '(x,y) := ?sb in ?e1) = ?e2 |- _ ] => 
         destruct sb as [ x y ] eqn:H
      | [ SB : ?e2 = (let '(x,y) := ?sb in ?e1) |- _ ] => 
         destruct sb as [ x y ] eqn:H
    end.




Lemma SubstExtends_substBndrs : forall bndrs subst subst' bndrs' vs,
  forall (SB : substBndrs subst bndrs = (subst', bndrs')),
    NoDup bndrs ->
    WellScoped_Subst subst vs ->
    SubstExtends subst bndrs subst' bndrs'.
Proof.
  induction bndrs; unfold substBndrs; intros.
  + rewrite mapAccumL_nil in SB.
    inversion SB; subst; clear SB.
    eapply SubstExtends_refl; eauto.
  + rewrite mapAccumL_cons in SB.
    lift_let_in_eq Hsb1.
    lift_let_in_eq Hsb2.
    inversion SB. subst; clear SB.
    inversion H. subst. clear H.
    destruct (WellScoped_Subst_substBndr _ _ a _ _ _ Hsb1 H0) as [h0 h1].
    specialize (IHbndrs s' subst' ys _ Hsb2 ltac:(auto) h1).
    replace (y :: ys) with (cons y nil ++ ys); try reflexivity.
    replace (a :: bndrs) with (cons a nil ++ bndrs); try reflexivity.
    eapply SubstExtends_trans with (s2 := s'); auto.
    { 
      unfold Disjoint.
      rewrite Forall_forall.
      intros x I.
      inversion I. subst.
      admit.
      admit.
    }
Admitted.

Lemma SubstExtends_substRecBndrs : forall bndrs subst subst' bndrs' vs,
  forall (SB : substRecBndrs subst bndrs = (subst', bndrs')),
  WellScoped_Subst subst vs ->
  SubstExtends subst bndrs subst' bndrs'.
Proof.
  intros.
  unfold substRecBndrs in *.
  lift_let_in_eq h0.
  eapply SubstExtends_substBndrs in h0; eauto.
  inversion SB.
  subst.
  auto.
Qed.


Lemma substExpr : forall e s vs in_scope_set env u0 u1, 
    WellScoped_Subst (Mk_Subst in_scope_set env u0 u1) vs -> 
    WellScoped e vs -> 
    WellScoped (substExpr s (Mk_Subst in_scope_set env u0 u1) e) 
               (getInScopeVars in_scope_set).
Proof.
  intros e.
  apply (core_induct e); unfold substExpr.
  - unfold subst_expr. intros v s vs in_scope_set env u0 u1 WSsubst WSvar.
    unfold lookupIdSubst. 
    simpl in WSsubst. destruct WSsubst as [ ss vv] . specialize (vv v).         
    destruct (isLocalId v) eqn:HLocal; simpl.
    -- destruct (lookupVarEnv env v) eqn:HLookup. 
        + auto.
        + destruct (lookupInScope in_scope_set v) eqn:HIS.
          ++ unfold WellScoped, WellScopedVar in *.
             destruct (lookupVarSet vs v) eqn:LVS; try contradiction.
             unfold lookupInScope in HIS. destruct in_scope_set. simpl.
             assert (VV: ValidVarSet v2). admit.
             unfold ValidVarSet in VV.
             specialize (VV _ _ HIS).
             rewrite lookupVarSet_eq with (v2 := v).
             rewrite HIS.
             eapply Var.almostEqual_refl; auto.
             rewrite Base.Eq_sym. auto.
          ++ (* This case is impossible. *)
             unfold WellScoped, WellScopedVar in WSvar.
             unfold lookupInScope in HIS. destruct in_scope_set.
             unfold StrongSubset in ss.
             specialize (ss v). simpl in ss.
             rewrite HIS in ss.
             rewrite lookupVarSet_minusDom in ss; eauto.
             destruct (lookupVarSet vs v); try contradiction.
             
    -- unfold WellScoped in WSvar. 
       eapply WellScopedVar_StrongSubset; eauto.
       eapply StrongSubset_trans; eauto.
       eapply StrongSubset_minusDom_right; eauto.
  - unfold subst_expr. auto. 
  - intros. 
    rewrite subst_expr_App.
    unfold WellScoped; simpl; fold WellScoped.
    unfold WellScoped in H2; simpl; fold WellScoped in H2. destruct H2.
    split; eauto.
  - intros.
    rewrite subst_expr_Lam.
    destruct substBndr as [subst' bndr'] eqn:SB.
    unfold WellScoped in *; fold WellScoped in *.
    eapply WellScoped_substBndr; eauto.

  - destruct binds.
    + intros body He0 Hbody s vs in_scope_set env u u0 WSS WSL.
      rewrite subst_expr_Let.
      rewrite substBind_NonRec.
      destruct substBndr as [subst' bndr'] eqn:SB.
     
      unfold WellScoped in *. fold WellScoped in *.
      destruct WSL as [WSe WSb].
     
      split; eauto.
      unfold bindersOf in *.
      rewrite extendVarSetList_cons in *.
      rewrite extendVarSetList_nil  in *.
      eapply WellScoped_substBndr; eauto.

    + intros body IHrhs IHbody s vs in_scope_set env u u0 WSvs WSe.
      rewrite subst_expr_Let.
      rewrite substBind_Rec. 
      destruct WSe as [[ND FF] WSB].
      
      unfold bindersOf in WSB.
      rewrite bindersOf_Rec_cleanup in WSB.

      destruct (List.unzip l) as [vars rhss] eqn:UZ.      

      assert (EQL : length vars = length rhss).
      { eapply unzip_equal_length; eauto. }
      apply unzip_zip in UZ.
      subst l.

      rewrite map_fst_zip in *; auto.

      destruct substRecBndrs as [subst' bndrs'] eqn:SRB.
      pose (K := SubstExtends_substRecBndrs _ _ _ _ _ SRB WSvs). clearbody K.
      pose (J := SubstExtends_WellScoped_Subst _ _ _ _ _ K WSvs). clearbody J.
      rewrite Forall.Forall'_Forall in FF.
      rewrite Forall_forall in FF.     
      unfold WellScoped in *. fold WellScoped in *.
      repeat split.
      ++ destruct_SubstExtends.
         rewrite map_fst_zip in *; auto.
         admit.
         rewrite map_length.
         admit.

      ++ rewrite Forall.Forall'_Forall.
         rewrite Forall_forall.
         intros.
         destruct x as [bndr' rhs'].
         simpl.

         rewrite map_snd_zip in H; auto.
         set (rhss' := map (subst_expr &"substBind" subst') rhss) in *.
         unfold CoreBndr in *.
         assert (L: length rhss = length rhss').
         { unfold rhss'. rewrite map_length. auto. }

         assert (L1 : length bndrs' = length rhss' ).
         { 
           destruct_SubstExtends. congruence.  
         } 
         
         (* At this point we have 

            (bndr',rhs') in (bndrs',rhss')
            
            and we need to get 
            
            (bndr,rhs) in (vars, rhss)

          *)

         destruct (In_zip_snd rhss H) as [rhs InR]; try congruence.
         destruct (In_zip_fst vars InR) as [bndr InB]; try congruence.
         apply In_zip_swap in InB.

         specialize (IHrhs bndr rhs InB). 
         assert (rhs' = subst_expr &"substBind" subst' rhs).
         {
           unfold rhss' in InR.
           
           apply In_zip_map in InR. auto. }
         
         specialize (FF (bndr,rhs) InB).

         subst rhs'.
         replace (getInScopeVars in_scope_set) with 
             (getSubstInScopeVars (Mk_Subst in_scope_set env u u0)); auto.

         rewrite map_fst_zip.

         eapply WellScoped_substBody; eauto.
         intros subst0 WS0.
         destruct subst0.
         eapply IHrhs; eauto.

         rewrite map_length.
              
        rewrite <- length_zip.
        congruence.
        auto.
      ++ unfold bindersOf.
         rewrite bindersOf_Rec_cleanup.
         destruct_SubstExtends.
         rewrite map_fst_zip.
         rewrite extendList_getInScopeVars.
         eapply WellScoped_StrongSubset.
         eapply IHbody;eauto.
         rewrite <- extendList_getInScopeVars.
         eauto.
         unfold CoreBndr, CoreExpr in *.
         rewrite map_snd_zip.
         rewrite map_length.
         rewrite <- H.
         eauto.
         eauto.

  - intros.
    rewrite subst_expr_Case.
    destruct substBndr as [subst' bndr'] eqn:SB.
    unfold WellScoped in *. fold WellScoped in *.
    destruct H2 as [WS FF].
    split; eauto.
    rewrite Forall.Forall'_Forall in *.
    rewrite Forall_forall in *.
    intros alt IA.
    unfold substAlt in IA.
    rewrite in_map_iff in IA.
    destruct IA as [[[dc pats] rhs] [IAA IN]].
    destruct (substBndrs subst' pats) as [subst'' bndr''] eqn:SB2.
    destruct alt as [[dc0 bdnr''0] ss0]. inversion IAA. subst. clear IAA.
    simpl.
    pose (wf := FF _ IN). clearbody wf. simpl in wf.
(*    assert (WW : WellScoped_Subst (Mk_Subst in_scope_set env tt tt) 
                           (extendVarSetList vs (bndr :: pats))).  admit.
    pose (h := H0 dc0 pats rhs IN s _ _ _ WW wf). clearbody h. *)
    admit.

  - intros.

    rewrite subst_expr_Cast.
    unfold WellScoped in *. fold WellScoped in *.
    eauto.

  - intros.
    rewrite subst_expr_Tick.
    unfold WellScoped in *. fold WellScoped in *.
    eapply H; eauto.
  - intros.
    unfold subst_expr.
    unfold WellScoped in *. fold WellScoped in *.
    auto.
  - intros.
    unfold subst_expr.
    unfold WellScoped in *. fold WellScoped in *.
    auto.
Admitted.