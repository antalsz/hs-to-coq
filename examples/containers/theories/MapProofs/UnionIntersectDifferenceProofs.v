Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Import Data.Map.Internal.
Import GHC.Num.Notations.
Require Import OrdTactic.
Require Import Psatz.
Require Import Tactics.
Set Bullet Behavior "Strict Subproofs".
Require Import MapProofs.Bounds.
Require Import MapProofs.Tactics.
Require Import MapProofs.InsertProofs.
Require Import MapProofs.DeleteUpdateProofs.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Verification of [split] *)

Lemma split_Desc :
  forall x (s: Map e a) lb ub,
  Bounded s lb ub ->
  forall (P : Map e a * Map e a -> Prop),
  (forall s1 s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    size s = size s1 + size s2 + (if isSome (sem s x) then 1%Z else 0%Z) ->
    (forall i, sem s i = (if i == x then sem s i else sem s1 i ||| sem s2 i)) ->
    P (s1, s2)) ->
  P (split x s) : Prop.
Proof.
  intros ?? ?? HB.
  Ltac solveThis e := intros X HX; apply HX; clear X HX; [solve_Bounded e|solve_Bounded e| |f_solver e].
  induction HB.
  - solveThis e. reflexivity.
  - simpl.
    destruct (compare x x0) eqn:?.
  + solveThis e. replace (x == x0) with true by order e.
    simpl_options. lia.
  + apply IHHB1; intros s1_2 s1_3 HB1_2 HB1_3 Hsz Hsems1; clear IHHB1 IHHB2.
    applyDesc e (@link_Desc e a).
    solveThis e. destruct (sem s1 x); cbn -[Z.add] in *.
    * simpl. lia.
    * replace (x == x0) with false by order e. simpl.
      rewrite (sem_outside_below HB2) by solve_Bounds e. simpl. lia.
  + apply IHHB2; intros s2_2 s2_3 HB2_2 HB2_3 Hsz Hsems2; clear IHHB1 IHHB2.
    applyDesc e (@link_Desc e a).
    solveThis e. destruct (sem s2 x); cbn -[Z.add] in *.
    * simpl_options. lia.
    * replace (x == x0) with false by order e. simpl.
      rewrite (sem_outside_above HB1) by solve_Bounds e. simpl. lia.
Qed.

(** ** Verification of [union] *)

(* The [union] uses some nested pattern match that expand to a very large
   number of patterns in Coq. So let’s take them apart here *)
Lemma union_destruct :
  forall (P : Map e a -> Prop),
  forall s1 s2,
  (s2 = Tip -> P s1) ->
  (s1 = Tip -> P s2) ->
  (forall sz2 x vx, (s2 = Bin sz2 x vx Tip Tip) -> P (insertR x vx s1)) ->
  (forall sz1 x vx, (s1 = Bin sz1 x vx Tip Tip) -> P (insert x vx s2)) ->
  (forall sz1 x vx l1 r1, (s1 = Bin sz1 x vx l1 r1) -> 
    P (
      match split x s2 with
      | pair l2 r2 =>
      match union r1 r2 with
      | r1r2 =>
      match union l1 l2 with
      | l1l2 => if andb  (PtrEquality.ptrEq l1l2 l1)
                         (PtrEquality.ptrEq r1r2 r1) : bool
                then s1 else link x vx l1l2 r1r2
      end end end)) ->
  P (union s1 s2).
Proof.
  intros P s1 s2 HTipR HTipL HSingletonR HSingletonL HBins.
  destruct s1, s2; simpl union;
  try destruct s1_1, s1_2;
  try destruct s2_1, s2_2;
  first [ eapply HBins; reflexivity
        | eapply HSingletonL; reflexivity
        | eapply HSingletonR; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed. 

Lemma union_Desc :
  forall (s1: Map e a) s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (union s1 s2) lb ub (fun i => sem s1 i ||| sem s2 i).
(* We use [Desc'] here, because the result of [union] is passed to [link], which
   does a full rebalance, and hence does not need to know anything about the size.
   If it turns out we need [size (union s1 s2)], we can still add it.
*)
Proof.
  intros ???? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  * apply union_destruct; intros; subst; try congruence.
    + solve_Desc e. intros. reflexivity.
    + solve_Desc e. intros. reflexivity.
    + inversion HB3; subst; clear HB3.
      clear H4 H5.
      (* We need to give [applyDesc] a hint about the bounds that we care about: *)
      assert (Bounded (@Tip e a) lb ub) by constructor.
      applyDesc e (@insertR_Desc e a).
      solve_Desc e. f_solver e.
  * apply union_destruct; intros; subst; try congruence.
    + solve_Desc e. f_solver e.
    + inversion HB3; subst; clear HB3.
      applyDesc e (@insertR_Desc e a).
      solve_Desc e. f_solver e.
    + inversion H3; subst; clear H3.
      applyDesc e (@insert_Desc e a). solve_Desc e. f_solver e.
    + inversion H3; subst; clear H3.
      eapply split_Desc; try eassumption.
      intros.
      applyDesc e IHHB1_1.
      applyDesc e IHHB1_2.
      destruct_ptrEq.
      - solve_Desc e. f_solver e.
      - applyDesc e (@link_Desc e a).
        solve_Desc e. f_solver e.
Qed.

(** ** Verification of [unions] *)

(* This is a bit of a lazy specification, but goes a long way *)

Lemma Forall_rev:
  forall A P (l : list A), Forall P (rev l) <-> Forall P l.
Proof. intros. rewrite !Forall_forall. setoid_rewrite <- in_rev. reflexivity. Qed.

Lemma oro_assoc : forall {a} (o1 o2 o3: option a),
  (o1 ||| o2) ||| o3 = o1 ||| (o2 ||| o3).
Proof.
  intros. destruct o1. simpl. reflexivity. simpl. reflexivity.
Qed.

Lemma oro_app: forall o l1 l2 (i : e),
  (fold_right (fun (h: Map e a) t => sem h i ||| t) o (l1 ++ l2)) =
  (fold_right (fun h t => sem h i ||| t) None l1) |||
  (fold_right (fun h t => sem h i ||| t) o l2).
Proof.
  intros. generalize dependent o. generalize dependent l2. induction l1; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. rewrite oro_assoc. reflexivity.
Qed.

Require Proofs.Data.Foldable.

Lemma unions_Desc:
  forall (ss: list (Map e a)) lb ub,
  Forall (fun s => Bounded s lb ub) ss ->
  Desc' (unions ss) lb ub (fun i => fold_right (fun h t => sem h i ||| t) None ss).
Proof.
  intros.
  unfold unions.
  (* Switch to a fold right *)
  rewrite Proofs.Data.Foldable.hs_coq_foldl'_list.
  rewrite <- fold_left_rev_right.
  rewrite <- (rev_involutive ss).
  rewrite <- (rev_involutive ss), Forall_rev in H.
  generalize dependent (rev ss). intros.
  rewrite rev_involutive.

  induction H.
  * simpl. applyDesc e (@empty_Desc e a). solve_Desc e. f_solver e.
  * simpl fold_right.
    applyDesc e IHForall.
    applyDesc e union_Desc.
    solve_Desc e. 
    intro i.
    rewrite Hsem0, Hsem. rewrite oro_app. simpl. rewrite oro_None_r. reflexivity.
Qed.

(** ** Verification of [insertWithR] *)
Lemma insertWithR_Desc:
  forall (f: a -> a -> a) y v s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insertWithR f y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
      (fun i => (if i == y then match (sem s y) with
                                | None => Some v
                                | Some x => Some (f x v)
                                end  else None ||| sem s i )).
Proof.
  intros ?????? HB HLB HUB.
  induction HB; intros.
  * simpl.
    applyDesc e (@singleton_Desc e a); try eassumption; solve_Desc e.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in Heqc.
      rewrite Heqc.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      solve_Desc e.
    + clear IHHB2.
      applyDesc e IHHB1.
      rewrite (sem_outside_below HB2) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options. destruct (sem s1 y) eqn:?; simpl isSome in *; try lia;
      applyDesc e (@balanceL_Desc e a); solve_Desc e.
    + clear IHHB1.
      applyDesc e IHHB2.
      rewrite (sem_outside_above HB1) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options. destruct (sem s2 y) eqn:?; simpl_options; try lia; applyDesc e (@balanceR_Desc e a);
      solve_Desc e.
Qed.

(** ** Verification of [splitLookup] *)

(* Rewrite to avoid local [go] and StrictTriple *)
Fixpoint splitLookup' (k : e) (s : Map e a) : (Map e a * option a * Map e a) :=
  match s with
   | Tip => (Tip, None, Tip)
   | Bin _ kx x l r => match GHC.Base.compare k kx with
     | Lt => match splitLookup' k l with
               | (lt, z, gt) => match link kx x gt r with
                                              | gt' => (lt, z, gt')
                                            end
             end
     | Gt => match splitLookup' k r with
               | (lt, z, gt) => match link kx x l lt with
                                              | lt' => (lt', z, gt)
                                            end
             end
     | Eq => (l, Some x, r)
    end
 end.

Lemma splitLookup_splitLookup' : forall x map, splitLookup x map  = splitLookup' x map.
Proof.
  intros.
  unfold splitLookup.
  induction map.
  * simpl.
    rewrite <- IHmap1. clear IHmap1.
    rewrite <- IHmap2. clear IHmap2.
    destruct (compare x k).
    + reflexivity.
    + destruct (_ x map1); reflexivity.
    + destruct (_ x map2); reflexivity.
  * reflexivity.
Qed.

Lemma splitLookup_Desc:
  forall x s lb ub,
  Bounded s lb ub ->
  forall (P : Map e a * option a * Map e a -> Prop),
  (forall s1 b s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    b = sem s x ->
    (forall i, sem s i =
          (if i == x then sem s i
           else  (sem s1 i ||| sem s2 i))) ->
    P (s1, b, s2)) ->
  P (splitLookup x s) : Prop.
Proof.
  intros ?? ?? HB.
  rewrite splitLookup_splitLookup'.
  induction HB.
  Ltac solveThis e ::= intros X HX; apply HX; clear X HX; [solve_Bounded e|solve_Bounded e|try reflexivity |f_solver e].
  * solveThis e.
  * simpl.
    destruct (compare x x0) eqn:?.
    + solveThis e.
      replace (x == x0) with true by order_Bounds e.
      simpl_options.
      assert (sem s1 x = None). { eapply sem_outside_above. apply HB1. solve_Bounds e. }
      rewrite H3. simpl. reflexivity.
    + apply IHHB1.
      intros s1_2 b s1_3 HB1_2 HB1_3 Hb Hsems1.
      clear IHHB1 IHHB2.
      applyDesc e (@link_Desc e a).
      solveThis e.
      replace (x == x0) with false by order_Bounds e.
      rewrite (sem_outside_below HB2) by order_Bounds e.
      simpl_options. assumption.
    + apply IHHB2.
      intros s2_2 b s2_3 HB2_2 HB2_3 Hb Hsems2.
      clear IHHB1 IHHB2.
      applyDesc e (@link_Desc e a).
      solveThis e.
      replace (x == x0) with false by order_Bounds e.
      rewrite (sem_outside_above HB1) by order_Bounds e.
      simpl_options. assumption.
Qed.


(** ** Verification of [unionWith_Desc] *)
Lemma unionWith_destruct :
  forall (P : Map e a -> Prop),
  forall s1 s2 f,
  (s2 = Tip -> P s1) ->
  (s1 = Tip -> P s2) ->
  (forall sz2 x vx, (s2 = Bin sz2 x vx Tip Tip) -> P (insertWithR f x vx s1)) ->
  (forall sz1 x vx, (s1 = Bin sz1 x vx Tip Tip) -> P (insertWith f x vx s2)) ->
  (forall sz1 x vx l1 r1, (s1 = Bin sz1 x vx l1 r1) -> 
    P (
      match splitLookup x s2 with
      | (l2, mb, r2) =>
      match unionWith f r1 r2 with
      | r1r2 =>
      match unionWith f l1 l2 with
      | l1l2 => match mb with
                |None => link x vx l1l2 r1r2
                | Some y => link x (f vx y) l1l2 r1r2
                end
      end end end)) ->
  P (unionWith f s1 s2).
Proof.
  intros P s1 s2 f HTipR HTipL HSingletonR HSingletonL HBins.
  destruct s1, s2; simpl union;
  try destruct s1_1, s1_2;
  try destruct s2_1, s2_2;
  first [ eapply HBins; reflexivity
        | eapply HSingletonL; reflexivity
        | eapply HSingletonR; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed. 

Lemma unionWith_Desc :
  forall (s1: Map e a) s2 lb ub f,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (unionWith f s1 s2) lb ub (fun i => match sem s1 i, sem s2 i with
                                            |Some x, Some y => Some (f x y)
                                            | Some x, _ => Some x
                                            | _, Some y => Some y
                                            | _, _ => None
                                            end).
Proof.
intros ????? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  * apply unionWith_destruct; intros; subst; try congruence.
    + solve_Desc e. f_solver e.
    + solve_Desc e. f_solver e.
    + inversion HB3; subst; clear HB3.
      clear H4 H5.
      (* We need to give [applyDesc] a hint about the bounds that we care about: *)
      assert (Bounded (@Tip e a) lb ub) by constructor.
      applyDesc e insertWithR_Desc.
      solve_Desc e. f_solver e.
  * apply unionWith_destruct; intros; subst; try congruence.
    + solve_Desc e. f_solver e.
    + inversion HB3; subst; clear HB3.
      applyDesc e insertWithR_Desc.
      solve_Desc e. f_solver e.
      assert (sem s1 x0 = sem s1 i). apply sem_resp_eq. order e. rewrite H1 in Hsem.
      rewrite Heqo0 in Hsem. simpl in Hsem. symmetry. assumption.
      assert (sem s1 x0 = sem s1 i) by (apply sem_resp_eq; order e). rewrite H1 in Hsem.
      rewrite Heqo0 in Hsem. assert (x0 == x = true) by (order e). rewrite H3 in Hsem.
      simpl in Hsem. symmetry. assumption.
      assert (sem s2 i = sem s2 x0) by (apply sem_resp_eq; order e). 
      rewrite <- H1 in Hsem. rewrite Heqo1 in Hsem. 
      assert (sem s1 x0 = None). eapply sem_outside_above. eassumption. solve_Bounds e.
      rewrite H3 in Hsem. assert (x0 == x = false) by (order e). rewrite H4 in Hsem.
      simpl in Hsem. symmetry. assumption.
      assert (sem s1 x0 = None). erewrite sem_resp_eq. apply Heqo0. order e.
      rewrite H1 in Hsem. assert (x0 == x = false) by (order e). rewrite H3 in Hsem.
      simpl in Hsem. assert (sem s2 x0 = None). erewrite sem_resp_eq.
      apply Heqo1. order e. rewrite H4 in Hsem. symmetry. assumption.
      assert (sem s1 x0 = Some a0). erewrite sem_resp_eq. apply Heqo0. order e.
      rewrite H1 in Hsem. simpl in Hsem. symmetry. assumption.
      assert (sem s1 x0 = None). erewrite sem_resp_eq. apply Heqo0. order e.
      rewrite H1 in Hsem. assert (x0 == x = true) by (order e). rewrite H3 in Hsem.
      simpl in Hsem. symmetry. assumption.
      assert (sem s1 x0 = None). erewrite sem_resp_eq. apply Heqo0. order e.
      assert (x0 == x = false) by (order e). rewrite H1 in Hsem. rewrite H3 in Hsem.
      simpl in Hsem. assert (sem s2 x0 = Some a0). erewrite sem_resp_eq. apply Heqo1.
      order e. rewrite H4 in Hsem. symmetry. assumption.
      destruct (sem s1 x0); simpl in Hsem. inversion Hsem. destruct (x0 == x); simpl in Hsem.
      inversion Hsem. destruct (sem s2 x0); simpl in Hsem; inversion Hsem.
    + inversion H3; subst; clear H3.
      applyDesc e (@insertWith_Desc e a). solve_Desc e. f_solver e;
      assert (sem s3 x0 = sem s3 i) by (apply sem_resp_eq; order e); rewrite <- H1 in Heqo0;
      rewrite Heqo0 in Hsem; symmetry; assumption.
    + inversion H3; subst; clear H3.
      eapply splitLookup_Desc; try eassumption.
      intros.
      applyDesc e IHHB1_1.
      applyDesc e IHHB1_2. destruct b.
      - applyDesc e (@link_Desc e a). apply showDesc'. split. 
        (*Not using solve_Desc because it was very slow*)
        solve_Bounded e. f_solver e; rewrite H5 in Hsem0;
        rewrite <- Hsem1; assumption.
      - applyDesc e (@link_Desc e a). apply showDesc'. split.
        solve_Bounded e. f_solver e; rewrite H5 in Hsem0; rewrite <-Hsem1; assumption.
Qed. 

Require Import Coq.Classes.Morphisms.
(** ** Verification of [insertWithKeyR] *)
(*Need to add assumption that f is proper*)
Lemma insertWithKeyR_Desc:
  forall (f: e -> a -> a -> a) y v (s: Map e a) lb ub,
  Bounded s lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insertWithKeyR f y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
      (fun i => (if i == y then match (sem s y) with
                                | None => Some v
                                | Some x => Some (f i x v)
                                end  else None ||| sem s i )).
Proof.
  intros ?????? HB HP HLB HUB.
  induction HB; intros.
  * simpl.
    applyDesc e (@singleton_Desc e a); try eassumption; solve_Desc e.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in Heqc.
      rewrite Heqc.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      solve_Desc e. f_solver e. assert (f x v0 v = f i v0 v). apply equal_f.
      apply equal_f. apply HP. order e. rewrite H1. reflexivity.
    + clear IHHB2.
      applyDesc e IHHB1.
      rewrite (sem_outside_below HB2) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options. destruct (sem s1 y) eqn:?; simpl isSome in *; try lia;
      applyDesc e (@balanceL_Desc e a); solve_Desc e.
    + clear IHHB1.
      applyDesc e IHHB2.
      rewrite (sem_outside_above HB1) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options. destruct (sem s2 y) eqn:?; simpl_options; try lia; applyDesc e (@balanceR_Desc e a);
      solve_Desc e.
Qed.

(** ** Verification of [unionWithKey] *)

Lemma unionWithKey_destruct :
  forall (P : Map e a -> Prop),
  forall s1 s2 f,
  (s2 = Tip -> P s1) ->
  (s1 = Tip -> P s2) ->
  (forall sz2 x vx, (s2 = Bin sz2 x vx Tip Tip) -> P (insertWithKeyR f x vx s1)) ->
  (forall sz1 x vx, (s1 = Bin sz1 x vx Tip Tip) -> P (insertWithKey f x vx s2)) ->
  (forall sz1 x vx l1 r1, (s1 = Bin sz1 x vx l1 r1) -> 
    P (
      match splitLookup x s2 with
      | (l2, mb, r2) =>
      match unionWithKey f r1 r2 with
      | r1r2 =>
      match unionWithKey f l1 l2 with
      | l1l2 => match mb with
                |None => link x vx l1l2 r1r2
                | Some y => link x (f x vx y) l1l2 r1r2
                end
      end end end)) ->
  P (unionWithKey f s1 s2).
Proof.
  intros P s1 s2 f HTipR HTipL HSingletonR HSingletonL HBins.
  destruct s1, s2; simpl union;
  try destruct s1_1, s1_2;
  try destruct s2_1, s2_2;
  first [ eapply HBins; reflexivity
        | eapply HSingletonL; reflexivity
        | eapply HSingletonR; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed. 

Lemma unionWithKey_Desc :
  forall (s1: Map e a) s2 lb ub f,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  Desc' (unionWithKey f s1 s2) lb ub (fun i => match sem s1 i, sem s2 i with
                                            |Some x, Some y => Some (f i x y)
                                            | Some x, _ => Some x
                                            | _, Some y => Some y
                                            | _, _ => None
                                            end).
Proof.
intros ????? HB1 HB2 HP.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  * apply unionWithKey_destruct; intros; subst; try congruence.
    + solve_Desc e. f_solver e.
    + solve_Desc e. f_solver e.
    + inversion HB3; subst; clear HB3.
      clear H4 H5.
      (* We need to give [applyDesc] a hint about the bounds that we care about: *)
      assert (Bounded (@Tip e a) lb ub) by constructor.
      eapply insertWithKeyR_Desc. apply H. apply HP. assumption. assumption. intros.
      solve_Desc e. f_solver e.
  * apply unionWithKey_destruct; intros; subst; try congruence.
    + solve_Desc e. f_solver e.
    + inversion HB3; subst; clear HB3.
      eapply insertWithKeyR_Desc. solve_Bounded e. apply HP. assumption. assumption. intros.
      solve_Desc e. f_solver e.
      assert (sem s1 x0 = sem s1 i). apply sem_resp_eq. order e. rewrite H5 in H4.
      rewrite Heqo0 in H4. simpl in H4. symmetry. assumption.
      assert (sem s1 x0 = sem s1 i) by (apply sem_resp_eq; order e). rewrite H5 in H4.
      rewrite Heqo0 in H4. assert (x0 == x = true) by (order e). rewrite H6 in H4.
      simpl in H4. symmetry. assumption.
      assert (sem s2 i = sem s2 x0) by (apply sem_resp_eq; order e). 
      rewrite <- H5 in H4. rewrite Heqo1 in H4. 
      assert (sem s1 x0 = None). eapply sem_outside_above. eassumption. solve_Bounds e.
      rewrite H6 in H4. assert (x0 == x = false) by (order e). rewrite H9 in H4.
      simpl in H4. symmetry. assumption.
      assert (sem s1 x0 = None). erewrite sem_resp_eq. apply Heqo0. order e.
      rewrite H5 in H4. assert (x0 == x = false) by (order e). rewrite H6 in H4.
      simpl in H4. assert (sem s2 x0 = None). erewrite sem_resp_eq.
      apply Heqo1. order e. rewrite H9 in H4. symmetry. assumption.
      assert (sem s1 x0 = Some a0). erewrite sem_resp_eq. apply Heqo0. order e.
      rewrite H5 in H4. simpl in H4. symmetry. assumption.
      assert (sem s1 x0 = None). erewrite sem_resp_eq. apply Heqo0. order e.
      rewrite H5 in H4. assert (x0 == x = true) by (order e). rewrite H6 in H4.
      simpl in H4. symmetry. assumption.
      assert (sem s1 x0 = None). erewrite sem_resp_eq. apply Heqo0. order e.
      assert (x0 == x = false) by (order e). rewrite H6 in H4. rewrite H5 in H4.
      simpl in H4. assert (sem s2 x0 = Some a0). erewrite sem_resp_eq. apply Heqo1.
      order e. rewrite H9 in H4. symmetry. assumption.
      destruct (sem s1 x0); simpl in H4. inversion H4. destruct (x0 == x); simpl in H4.
      inversion H4. destruct (sem s2 x0); simpl in H4; inversion H4.
    + inversion H3; subst; clear H3.
      applyDesc e (@insertWithKey_Desc e a). solve_Desc e. f_solver e;
      assert (sem s3 x0 = sem s3 i) by (apply sem_resp_eq; order e); rewrite <- H1 in Heqo0.
      destruct (sem s3 x0). assert (f x0 vx a2 = f i vx a2). apply equal_f. apply equal_f.
      apply HP. order e. rewrite H3 in Hsem. rewrite Heqo0 in Hsem. symmetry. assumption.
      rewrite <- Hsem. assumption.
      destruct (sem s3 x0). assert (f x0 vx a1 = f i vx a1). apply equal_f. apply equal_f.
      apply HP. order e. rewrite H3 in Hsem. rewrite Heqo0 in Hsem. inversion Hsem.
      rewrite Heqo0 in Hsem. inversion Hsem.
      destruct (sem s3 x0). assert (f x0 vx a1 = f i vx a1). apply equal_f. apply equal_f.
      apply HP. order e. rewrite H3 in Hsem. rewrite Heqo0 in Hsem. inversion Hsem.
      rewrite Heqo0 in Hsem. inversion Hsem.
    + inversion H3; subst; clear H3.
      eapply splitLookup_Desc; try eassumption.
      intros.
      applyDesc e IHHB1_1.
      applyDesc e IHHB1_2. destruct b.
      - applyDesc e (@link_Desc e a). apply showDesc'. split. 
        (*Not using solve_Desc because it was very slow*)
        solve_Bounded e. f_solver e.
        assert (f x0 vx a0 = f i vx a0). apply equal_f. apply equal_f. apply HP. order e.
        rewrite H4. reflexivity.
        all : (rewrite H5 in Hsem0; rewrite <- Hsem1; assumption).
      - applyDesc e (@link_Desc e a). apply showDesc'. split.
        solve_Bounded e. f_solver e; rewrite H5 in Hsem0; rewrite <-Hsem1; assumption.
Qed. 

(** ** Verification of [unionsWith] *)
Lemma unionsWith_Desc:
  forall (ss: list (Map e a)) f lb ub,
  Forall (fun s => Bounded s lb ub) ss ->
  Desc' (unionsWith f ss) lb ub (fun i => fold_left (fun t h => match t with
                                                                 | Some y =>
                                                                   match (sem h i) with
                                                                    | Some x => Some (f y x)
                                                                    | _ => t
                                                                   end
                                                                  | _ => (sem h i)
                                                                  end) ss None).
Proof.
  intros.
  unfold unionsWith.
  (* Switch to a fold right *)
  rewrite Proofs.Data.Foldable.hs_coq_foldl'_list.
  rewrite <- fold_left_rev_right.
  rewrite <- (rev_involutive ss).
  rewrite <- (rev_involutive ss), Forall_rev in H.
  generalize dependent (rev ss). intros.
  rewrite rev_involutive.

  induction H.
  * simpl. applyDesc e (@empty_Desc e a). solve_Desc e. f_solver e. 
  * simpl fold_right.
    applyDesc e IHForall.
    applyDesc e unionWith_Desc.
    solve_Desc e. 
    intro i.
    rewrite Hsem0, Hsem. simpl. rewrite fold_left_app. simpl. destruct (fold_left
    (fun (t : option a) (h : Map e a) =>
     match t with
     | Some y => match sem h i with
                 | Some x0 => Some (f  y x0)
                 | None => t
                 end
     | None => sem h i
     end) (rev l) None); destruct (sem x i ) eqn : ?; reflexivity.
Qed. 

(** ** Verification of [link2] *)

(** This is called  [merge] for Set *)

Lemma link2_eq: forall (l r: Map e a), link2 l r = 
  match l, r with 
  | Tip, r => r
  | l, Tip => l
  | (Bin sizeL x vx lx rx as l), (Bin sizeR y vy ly ry as r) =>
    if Sumbool.sumbool_of_bool
         ((delta GHC.Num.* sizeL) GHC.Base.< sizeR)
    then balanceL y vy (link2 l ly) ry           
    else if Sumbool.sumbool_of_bool
              ((delta GHC.Num.* sizeR) GHC.Base.< sizeL)
         then balanceR x vx lx (link2 rx r)
         else glue l r
  end.
Proof.
  intros l r.
  destruct l; [|auto].
  destruct r; [|auto].
  unfold link2 at 1, link2_func at 1;
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.


Program Fixpoint link2_Desc (s1: Map e a)  (s2: Map e a)
  {measure (map_size s1 + map_size s2)} :
    forall x lb ub,
      Bounded s1 lb (Some x) ->
      Bounded s2 (Some x) ub  ->
      isLB lb x = true ->
      isUB ub x = true->
      Desc (link2 s1 s2) lb ub (size s1 + size s2)
           (fun i => sem s1 i ||| sem s2 i)
  := _.
Next Obligation.
  intros.
  rewrite link2_eq. 
  inversion H; subst; clear H;
    inversion H0; subst; clear H0;
      try solve [solve_Desc e].
  destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
  - applyDesc e link2_Desc.
    applyDesc e (@balanceL_Desc e a). rewrite size_Bin in Hsz. solve_size.
    solve_Desc e.
  - applyDesc e link2_Desc.
    applyDesc e (@balanceR_Desc e a). rewrite size_Bin in Hsz. solve_size.
    solve_Desc e.
  - applyDesc e (@glue_Desc e a).
    solve_Desc e.
Qed.


(** ** Verification of [splitMember] *)

(* Rewrite to avoid local [go] and StrictTriple *)
Fixpoint splitMember' (k : e) (s : Map e a) : (Map e a * bool * Map e a)%type :=
  match s with
   | Tip => (Tip, false, Tip)
   | Bin _ kx x l r => match GHC.Base.compare k kx with
     | Lt => match splitMember' k l with
               | (lt, z, gt) => match link kx x gt r with
                                              | gt' => (lt, z, gt')
                                            end
             end
     | Gt => match splitMember' k r with
               | (lt, z, gt) => match link kx x l lt with
                                              | lt' => (lt', z, gt)
                                            end
             end
     | Eq => (l, true, r)
    end
 end.

Lemma splitMember_splitMember' : forall x s, splitMember x s  = splitMember' x s.
Proof.
  intros.
  unfold splitMember.
  induction s.
  * simpl.
    rewrite <- IHs1. clear IHs1.
    rewrite <- IHs2. clear IHs2.
    destruct (compare x k).
    + reflexivity.
    + destruct (_ x s2); reflexivity.
    + destruct (_ x s3); reflexivity.
  * reflexivity.
Qed.

Lemma splitMember_Desc:
  forall x s lb ub,
  Bounded s lb ub ->
  forall (P : Map e a * bool * Map e a -> Prop),
  (forall s1 b s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    b = isSome (sem s x) ->
    (forall i, sem s i =
          (if i == x then sem s i
           else  (sem s1 i ||| sem s2 i))) ->
    P (s1, b, s2)) ->
  P (splitMember x s) : Prop.
Proof.
  intros ?? ?? HB.
  rewrite splitMember_splitMember'.
  induction HB.
  Ltac solveThis e ::= intros X HX; apply HX; clear X HX; [solve_Bounded e|solve_Bounded e|try reflexivity |f_solver e].
  * solveThis e.
  * simpl.
    destruct (compare x x0) eqn:?.
    + solveThis e.
      replace (x == x0) with true by order_Bounds e.
      simpl_options.
      reflexivity.
    + apply IHHB1.
      intros s1_2 b s1_3 HB1_2 HB1_3 Hb Hsems1.
      clear IHHB1 IHHB2.
      applyDesc e (@link_Desc e a).
      solveThis e.
      replace (x == x0) with false by order_Bounds e.
      rewrite (sem_outside_below HB2) by order_Bounds e.
      simpl_options. assumption.
    + apply IHHB2.
      intros s2_2 b s2_3 HB2_2 HB2_3 Hb Hsems2.
      clear IHHB1 IHHB2.
      applyDesc e (@link_Desc e a).
      solveThis e.
      replace (x == x0) with false by order_Bounds e.
      rewrite (sem_outside_above HB1) by order_Bounds e.
      simpl_options. assumption.
Qed.

(** ** Verification of [intersection] *)

Lemma intersection_Desc:
  forall (s1: Map e a) s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (intersection s1 s2) lb ub
        (fun i => sem s1 i &&& sem s2 i).
Proof.
  intros ???? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  - simpl. solve_Desc e. f_solver e.
  - simpl.
    destruct s3 eqn:Hs3.
    + rewrite <- Hs3 in *.
      clear Hs3 s e0 a0 m1 m2.
      eapply splitMember_Desc;
        only 1: eassumption.
      intros s4' b s5' HB1 HB2 Hb Hi.
      applyDesc e IHHB1_1.
      applyDesc e IHHB1_2.
      destruct b.
      * destruct_ptrEq.
        -- solve_Desc e. f_solver e.
        -- applyDesc e (@link_Desc e a).
           solve_Desc e. f_solver e.
      * applyDesc e link2_Desc.
        solve_Desc e. f_solver e.
    + solve_Desc e. f_solver e.
Qed.

(** Verificataion of [intersectionWith] *)
Lemma intersectionWith_Desc:
  forall (s1: Map e a) (s2: Map e a) (f: a -> a -> a) lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (intersectionWith f s1 s2) lb ub
        (fun i => match (sem s1 i), (sem s2 i) with
                  | Some x, Some b => Some (f x b)
                  | _, _ => None end).

Proof.
  intros ????? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  - simpl. solve_Desc e. f_solver e.
  - simpl.
    destruct s3 eqn:Hs3.
    + rewrite <- Hs3 in *.
      clear Hs3 s e0 a0 m1 m2.
      eapply splitLookup_Desc;
        only 1: eassumption.
      intros s4' b s5' HB1 HB2 Hb Hi.
      applyDesc e IHHB1_1.
      applyDesc e IHHB1_2.
      destruct b.
      applyDesc e (@link_Desc e a). 
      (*Also taking long see*)
      apply showDesc'. split. solve_Bounded e. f_solver e; rewrite Hi in Hsem0; 
      rewrite <- Hsem1; assumption.
      applyDesc e link2_Desc.
      apply showDesc'. split. solve_Bounded e. f_solver e; rewrite Hi in Hsem0;
      rewrite <-Hsem1; assumption.
    + solve_Desc e. f_solver e.
Qed.

(** ** Veritication of [intersectionWithKey] *)

(*Had to add assumption that f is Proper*)

Lemma intersectionWithKey_Desc:
  forall (s1: Map e a) s2 (f: e -> a -> a -> a) lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  Desc' (intersectionWithKey f s1 s2) lb ub
        (fun i => match (sem s1 i), (sem s2 i) with
                  | Some a, Some b => Some (f i a b)
                  | _, _ => None end).

Proof.
  intros ????? HB1 HB2 HP.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  - simpl. solve_Desc e. reflexivity.
  - simpl.
    destruct s3 eqn:Hs3.
    + rewrite <- Hs3 in *.
      clear Hs3 s e0 a0 m1 m2.
      eapply splitLookup_Desc;
        only 1: eassumption.
      intros s4' b s5' HB1 HB2 Hb Hi.
      applyDesc e IHHB1_1.
      applyDesc e IHHB1_2.
      destruct b.
      applyDesc e (@link_Desc e a). 
      (*Also taking long see*)
      apply showDesc'. split. solve_Bounded e. f_solver e.
      assert (f x v a0 = f i v a0). apply equal_f. apply equal_f. apply HP. order e.
      rewrite H1. reflexivity.
      all :( try (rewrite Hi in Hsem0; 
      rewrite <- Hsem1; assumption)).
      applyDesc e link2_Desc.
      apply showDesc'. split. solve_Bounded e. f_solver e; rewrite Hi in Hsem0;
      rewrite <-Hsem1; assumption.
    + solve_Desc e. f_solver e.
Qed.
      

(** ** Verification of [difference] *)

(** A wart: Because we are in a section that fixes [a], 
we get this proof only for invocations of [difference] where
boths maps have the same element type. This does not
affect the proof, but requires some Coq proof structure engineering
to fix. *)

Lemma difference_destruct :
  forall (P : Map e a -> Prop),
  forall s1 s2,
  (s1 = Tip -> P Tip) ->
  (s2 = Tip -> P s1) ->
  (forall sz2 x vx l2 r2, (s2 = Bin sz2 x vx l2 r2) -> 
    P (
      match split x s1 with
      | pair l1 r1 =>
      match difference r1 r2 with
      | r1r2 =>
      match difference l1 l2 with
      | l1l2 => if size l1l2 + size r1r2 == size s1
                then s1 else link2 l1l2 r1r2
      end end end)) ->
  P (@difference e a a _ _ s1 s2).
Proof.
  intros P s1 s2 HTipL HTipR HBins.
  destruct s1, s2; simpl difference;
  try destruct s1_1, s1_2;
  try destruct s2_1, s2_2;
  first [ eapply HBins; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed.

Require Import Coq.Program.Tactics.

Open Scope Z_scope.

Lemma difference_Desc :
  forall (s1: Map e a) s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  forall (P : Map e a -> Prop),
  (forall s,
    Bounded s lb ub ->
    size s <= size s1 ->
    (size s = size s1 -> forall i, sem s i = sem s1 i) ->
    (forall i, sem s i = diffo (sem s1 i) (sem s2 i)) ->
    P s) ->
  P (difference s1 s2).
Proof.
  intros s1 s2 lb ub Hb1 Hb2.
  revert s1 Hb1. induction Hb2; intros sl Hb1; apply hide.
  Ltac showP := apply unhide; intros X HX; apply HX; clear X HX; only 3: intro.
  - simpl.
    destruct sl; (showP; [assumption | reflexivity | reflexivity | f_solver e]).
  - apply difference_destruct; intros; subst.
    + (showP; [assumption | order Z | reflexivity | f_solver e]).
    + (showP; [assumption | order Z | reflexivity | f_solver e]). 
    + eapply split_Desc; try eassumption. 
      intros sl1 sl2 HBsl1 HBsl2 Hsz Hsem. inversion H3; subst; clear H3.
      eapply IHHb2_1. solve_Bounded e. intros sil ????. clear IHHb2_1.
      eapply IHHb2_2. solve_Bounded e. intros sir ????. clear IHHb2_2.
      destruct (_ == _) eqn:Hcomp.
      * showP; [assumption | reflexivity | reflexivity | ].
        assert (size sl1 + size sl2 <= size sl) by (destruct (sem sl x0); simpl in *;  lia).
        change (size sil + size sir =? size sl = true) in Hcomp.
        rewrite Z.eqb_eq in Hcomp.
        lapply H4; [intro; subst; clear H4|lia].
        lapply H8; [intro; subst; clear H8|lia].
        assert (sem sl x0 = None) by (destruct (sem sl x0); simpl in *; try reflexivity; lia).
        f_solver e. (* TODO: More stuff that [f_solver] should do *)
      * applyDesc e link2_Desc.
        showP.
        -- assumption.
        -- destruct (sem sl x0); simpl in *; lia.
        -- assert (sem sl x0 = None) by (destruct (sem sl x0); simpl in *; try reflexivity; lia).
           rewrite H11 in Hsz.
           simpl in Hsz.
           lapply H4; [intro; subst|lia].
           lapply H8; [intro; subst|lia].
           clear H4 H8.
           f_solver e.
        -- f_solver e.
Qed.

End WF.
