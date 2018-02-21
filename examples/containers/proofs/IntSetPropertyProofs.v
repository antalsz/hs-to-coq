From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
Set Bullet Behavior "Strict Subproofs".

Require Import GHC.Base      Proofs.GHC.Base.
Require Import Data.OldList  Proofs.Data.OldList.
Require Import Data.Foldable Proofs.Data.Foldable.
Notation list := Coq.Init.Datatypes.list.
Notation seq  := Coq.Lists.List.seq.

Infix "=="  := op_zeze__ : bool_scope.
Infix "===" := eq_op (at level 70, no associativity) : bool_scope.

Notation "x == y :> A"  := (op_zeze__ (x : A) (y : A)) : bool_scope.
Notation "x === y :> A" := (eq_op     (x : A) (y : A)) (at level 70, y at next level, no associativity) : bool_scope.

Notation reflect := ssrbool.reflect. (* Why do I need this? *)

Require Import Sorting.Sorted.
Notation sort := Data.OldList.sort.

Require Import Data.IntSet.Internal.
Require Import IntSetProperties.
Require Import IntSetProofs.
Module IntSetFSet := Foo.

Arguments "$"          {_ _}     / _ _.
Arguments id           {_}       / _.
Arguments Datatypes.id {_}       / _.
Arguments forAll       {_ _ _ _} / _.
Arguments "∘"          {_ _}     _ _ _ /.

Theorem thm_Valid : toProp prop_Valid.
Proof.
  rewrite /prop_Valid /forValidUnitTree /forValid /=; apply valid_correct.
Qed.

Lemma WF_Bin_children (p : Prefix) (m : Mask) (l r : IntSet) :
  WF (Bin p m l r) -> WF l /\ WF r.
Proof.
  case=> fn;
    inversion 1    as [|s bounds fn' desc];
    subst s fn';
    inversion desc as [|l' bounds_l fn_l r' bounds_r fn_r
                        p' m' bounds' fn'
                        desc_l desc_r is_pos sub_l sub_r def_p def_m spec_fn];
    subst p' m' l' r' bounds' fn'.
  split; [exists fn_l | exists fn_r]; eauto using DescSem.
Qed.

Corollary WF_Bin_left (p : Prefix) (m : Mask) (l r : IntSet) :
  WF (Bin p m l r) -> WF l.
Proof. by move=> /WF_Bin_children []. Qed.

Corollary WF_Bin_right (p : Prefix) (m : Mask) (l r : IntSet) :
  WF (Bin p m l r) -> WF r.
Proof. by move=> /WF_Bin_children []. Qed.

Fixpoint iterates (n : nat) {a} (f : a -> a) (z : a) : list a :=
  match n with
  | O    => nil
  | S n' => z :: iterates n' f (f z)
  end.

Lemma eftInt_aux_fuel_case (x y : Int) (p : GHC.Enum.eftInt_aux_fuel x y) :
  (exists (gt : (x >? y)%Z = true),                  p = @GHC.Enum.done x y gt) \/
  (exists (p' : GHC.Enum.eftInt_aux_fuel (x+1)%Z y), p = @GHC.Enum.step x y p').
Proof.
  case: p => [x' y' gt | x' y' p'].
  - by left; exists gt.
  - by right; exists p'.
Qed.

Require Import Coq.Logic.Eqdep_dec.

Theorem UIP_refl_dec {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x : A) (p : x = x) : p = erefl.
Proof. exact (UIP_dec dec p erefl). Qed.

Require Import GHC.Num.

Theorem eftInt_aux_iterates (from to : Int) p :
  @GHC.Enum.eftInt_aux from to p = iterates (Z.to_nat (to - from + #1)) (fun x => x + #1) from.
Proof.
  move: to p.
  elim: from => [| from IHfrom | from IHfrom].
  - elim=> [| to IHto | to IHto].
    + move=> p; move: (eftInt_aux_fuel_case _ _ p) => [[gt def_p] | [p' def_p]]; subst p.
      * by contradict gt.
      * admit.
    + simpl.
Admitted.

Require Import GHC.Num.
Theorem enumFromTo_Int_iterates (from to : Int) :
  enumFromTo from to = iterates (Z.to_nat (to - from + #1)) (fun x => x + #1) from.
Proof. apply eftInt_aux_iterates. Qed.

Theorem thm_MaskPow2 : toProp prop_MaskPow2.
Proof.
  simpl; elim=> [p m l IHl r IHr | p m | ] WF_s //=.
  apply/and3P; split.
  - rewrite /powersOf2 enumFromTo_Int_iterates.
    cbv -[Z.pow member fromList].

    inversion WF_s; inversion H; inversion HD; subst.
    rewrite /rMask.
    destruct r0 as [r0_1 r0_2].
    
(*     rewrite /powersOf2 enumFromTo_Int_iterates. *)
(*     cbv -[Zpow member fromList]. *)

    
(*     move: (WF_s) => /WF_Bin_children [/IHl Pl /IHr Pr]. *)
(*     move: Pl Pr; rewrite /prop_MaskPow2. *)

(* rewrite /powersOf2 enumFromTo_Int_iterates. *)
(*     cbv -[Zpow member fromList]. *)
    
(*     simpl *)

(*  /=. *)
(*     replace (GHC.Enum.eftInt 0%Z 63%Z) with (eftInt 0%Z 63%Z) by admit. *)
    

(*     cbv -[member fromList flat_map Zpow]. *)

(*     rewrite /Enum.eftInt_fuel. *)
    
(*   - apply IHl; move: WF_s; apply WF_Bin_left. *)
(*   - apply IHr; move: WF_s; apply WF_Bin_right. *)
Abort.

Theorem thm_AscDescList : toProp prop_AscDescList.
Proof.
  rewrite /prop_AscDescList /= => xs _.
  rewrite /fromList /foldl /Foldable__list /Data.Foldable.Foldable__list_foldl /foldl /=.
  rewrite /toAscList /toDescList.
  rewrite foldl_foldr; last admit.
  rewrite /flip.
  unfold "_==_", Eq_list => /=.
  
  elim: xs => [|x xs IH] //=.
Abort.

Theorem thm_DescList : toProp prop_DescList.
Proof.
Abort.

Theorem thm_Diff : toProp prop_Diff.
Proof.
  rewrite /prop_Diff /= => xs POS_xs ys POS_ys.
  
  move: (fromList_WF   xs POS_xs)       => WF_xs.
  move: (fromList_WF   ys POS_ys)       => WF_ys.
  move: (difference_WF _ _ WF_xs WF_ys) => WF_diff.
  
  split=> /=; first by apply valid_correct.
Abort.

Theorem thm_EmptyValid : toProp prop_EmptyValid.
Proof. done. Qed.

Lemma WRONG : forall x : Z, exists x' : N, x = Z.of_N x'. Admitted.
Lemma eqIntSetMemberP {s1 s2 : IntSet} :
  WF s1 -> WF s2 ->
  reflect (forall x, member x s1 == member x s2) (s1 == s2).
Proof.
  move=> WF1 WF2.
  set s1' := exist _ _ WF1; set s2' := exist _ _ WF2.
  move: (IntSetFSet.equal_1 s1' s2') (IntSetFSet.equal_2 s1' s2').
  rewrite /= /IntSetFSet.Equal /= /IntSetFSet.In_set => Equal_eq eq_Equal.
  apply iff_reflect; split.
  - move=> KEYS; apply Equal_eq=> n; apply eq_iff_eq_true.
    move: KEYS; cbv -[member Z.of_N eqb is_true].
    rewrite -eqb_true_iff; apply.
  - move=> /eq_Equal KEYS x; move: (WRONG x) => [n def_x]; subst x.
    move: (KEYS n); cbv -[member Z.of_N eqb iff].
    case: (member _ s1); case: (member _ s2); tauto.
Qed.

Theorem Sem_member (s : IntSet) :
  WF s ->
  Sem s (member ^~ s).
Proof.
  move=> [f def_f].
  apply Sem_change_f with f => //.
  by move: (def_f) => /member_Sem.
Qed.

Ltac member_by_Sem SEM :=
  repeat (move=> /Sem_member ? || move=> ?);
  erewrite member_Sem;
    last (eapply SEM; try eassumption; reflexivity);
    reflexivity.

Lemma insert_member (x : Int) (s : IntSet) :
  (0 <= x)%Z -> WF s ->
  forall k, member k (insert x s) = (k == x) || member k s.
Proof. member_by_Sem insert_Sem. Qed.

Lemma delete_member (x : Int) (s : IntSet) :
  (0 <= x)%Z -> WF s ->
  forall k, member k (delete x s) = (k /= x) && member k s.
Proof. member_by_Sem delete_Sem. Qed.

Lemma union_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  forall k, member k (union s1 s2) = member k s1 || member k s2.
Proof. member_by_Sem union_Sem. Qed.

Lemma intersection_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  forall k, member k (intersection s1 s2) = member k s1 && member k s2.
Proof. member_by_Sem intersection_Sem. Qed.

Lemma difference_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  forall k, member k (difference s1 s2) = member k s1 && ~~ member k s2.
Proof. member_by_Sem difference_Sem. Qed.

Lemma singleton_member (x : Int) :
  (0 <= x)%Z ->
  forall k, member k (singleton x) = (k == x).
Proof. member_by_Sem singleton_Sem. Qed.

Lemma EqExact_cases {A} `{EqExact A} (x y : A) :
  {x == y /\ x = y} + {x /= y /\ x <> y}.
Proof.
  rewrite Neq_inv; case CMP: (x == y).
  - by left; split=> //; apply/Eq_eq.
  - by right; split=> //; move=> /Eq_eq; rewrite CMP.
Qed.

Theorem thm_InsertDelete : toProp prop_InsertDelete.
Proof.
  rewrite /prop_InsertDelete /= => x POS s WF_s.

  move: (insert_WF x _ WF_s   POS) => WF_ins.
  move: (delete_WF x _ WF_ins POS) => WF_res.
  case x_nin_s: (~~ member x s) => //=; split=> /=; first by apply valid_correct.

  apply/eqIntSetMemberP => // k; apply/Eq_eq.
  rewrite delete_member // insert_member //.
  rewrite Eq_inv andb_orr andbN orFb.
  
  case: (EqExact_cases k x) => [[Beq Peq] | [Bneq Pneq]].
  - by rewrite Peq; move: x_nin_s => /negbTE->; rewrite andbF.
  - by rewrite Bneq andTb.
Qed.

Theorem empty_WF : WF empty.
Proof. by exists xpred0; constructor. Qed.
Hint Resolve empty_WF.

Theorem thm_InsertIntoEmptyValid : toProp prop_InsertIntoEmptyValid.
Proof.
  rewrite /prop_InsertIntoEmptyValid /= => x POS.
  by apply valid_correct, insert_WF.
Qed.

Hypothesis sorted_sort : forall {A} `{Ord A} (xs : list A),
  StronglySorted _<=_ (sort xs).

Theorem elem_by_In {A} `{EqExact A} (xs : list A) (x : A) :
  reflect (In x xs) (elem_by _==_ x xs).
Proof.
  elim: xs => [|x' xs IH] /=; first by constructor.
  apply iff_reflect; split;
    try move=> /orP;
    move=> [? | ?];
    try apply/orP;
    solve [by left; apply/Eq_eq | by right; apply/IH].
Qed.

Hypothesis nub_NoDup : forall {A} `{EqExact A} (xs : list A),
  NoDup (nub xs).

Theorem thm_Int : toProp prop_Int.
Proof.
  rewrite /prop_Int /= => xs POS_xs ys POS_ys.

  move: (fromList_WF     xs POS_xs)       => WF_xs.
  move: (fromList_WF     ys POS_ys)       => WF_ys.
  move: (intersection_WF _ _ WF_xs WF_ys) => WF_both.

  split=> /=; first by apply valid_correct.
  apply/Eq_eq; fold toList.
Abort.

Lemma Foldable_and_all {F} `{Foldable F} : and (t := F) =1 all id.
Proof. done. Qed.

Lemma toList_member_has (s : IntSet) :
  WF s ->
  forall k, has (_==_ k) (toList s) = member k s.
Proof.
  move=> /Sem_member/toList_In SEM k.
  case CONT: (member k s) (SEM k) => SEM_k.
  - have: In k (toList s) by apply SEM_k. clear SEM_k.
    elim: (toList s) => [|x xs IH] //= SEM_k.
    case: SEM_k => [-> | IN].
    + by rewrite Eq_refl orTb.
    + by rewrite IH // orbT.
  - have: ~ In k (toList s) by move=> /SEM_k. clear SEM_k=> SEM_k.
    apply negbTE; apply /negP; contradict SEM_k.
    elim: (toList s) SEM_k => [|x xs IH] //= SEM_k.
    move: SEM_k => /orP [/Eq_eq -> | H]; [by left | by right; apply IH].
Qed.

Lemma Int_eqbP : Equality.axiom (_==_ : Int -> Int -> bool).
Proof. exact Eq_eq. Qed.

Canonical Int_eqMixin := EqMixin Int_eqbP.
Canonical Int_eqType := Eval hnf in EqType Int Int_eqMixin.

Lemma InP {A : eqType} (x : A) (xs : list A) :
  reflect (In x xs) (x \in xs).
Proof.
  elim: xs => [|y ys IH] //=.
  - by rewrite seq.in_nil; constructor.
  - rewrite inE; case CMP: (x === y) => /=.
    + by constructor; left; apply/eqP; rewrite eq_sym.
    + apply/equivP; first exact IH.
      split; first by right.
      case=> // ?; subst.
      by move: CMP; rewrite eq_refl.
Qed.

Lemma elemC {A} `{Eq_ A} (a x : A) (xs : list A) : elem a (x :: xs) = (a == x) || elem a xs.
Proof. done. Qed.

Lemma elemN {A} `{Eq_ A} (a : A) : elem a [::] = false.
Proof. done. Qed.

Lemma elemP {A} `{EqExact A} (x : A) (xs : list A) :
  reflect (In x xs) (elem x xs).
Proof.
  elim: xs => [|y ys IH] //=; first by constructor.
  rewrite elemC; case CMP: (x == y) => /=.
  - by constructor; left; apply/Eq_eq; rewrite Eq_sym.
  - apply/equivP; first exact IH.
    split; first by right.
    case=> // ?; subst.
    by move: CMP; rewrite Eq_refl.
Qed.

Lemma eqType_EqExact {A : eqType} `{EqExact A} (x y : A) : (x === y) = (x == y).
Proof. by case E: (x === y); case E': (x == y)=> //; move: E E' => /eqP ? /Eq_eq ?. Qed.

Lemma EqExact_eqType {A : eqType} `{EqExact A} (x y : A) : (x == y) = (x === y).
Proof. by rewrite eqType_EqExact. Qed.

Lemma elem_in {A : eqType} `{EqExact A} (xs : list A) (a : A) :
  elem a xs = (a \in xs).
Proof. by elim: xs => [|x xs IH] //=; rewrite inE -IH eqType_EqExact. Qed.

Lemma in_elem {A : eqType} `{EqExact A} (xs : list A) (a : A) :
  a \in xs = elem a xs.
Proof. symmetry; apply elem_in. Qed.

Theorem Foldable_all_ssreflect {A} (p : A -> bool) (xs : list A) : all p xs = seq.all p xs.
Proof. by rewrite Foldable_all_forallb. Qed.

Lemma fromList_member (xs : list Int) :
  Forall (fun x => 0 <= x)%Z xs ->
  forall k, member k (fromList xs) = elem k xs.
Proof.
  move=> POS_xs k.
  move: (fromList_Sem xs POS_xs) => [f [SEM DEF]].
  erewrite member_Sem; last by eapply SEM.
  move: (DEF k); case: (f k) => DEF_k.
  all: by symmetry; apply/elemP/DEF_k.
Qed.

Lemma toList_member (s : IntSet) :
  WF s ->
  forall k, elem k (toList s) = member k s.
Proof.
  move=> /Sem_member/toList_In SEM k.
  by case CONT: (member k s) (SEM k) => SEM_k; apply/elemP/SEM_k.
Qed.

Theorem Sem_Desc0 : forall s f, Sem s f -> exists r, Desc0 s r f.
Proof.
  apply Sem_ind => [f false_f | s r f Desc_srf].
  - by exists (0%Z,0%N); apply Desc0Nil.
  - by exists r; apply (Desc0NotNil s r f r f); rewrite // isSubrange_refl.
Qed.

Theorem thm_LeftRight : toProp prop_LeftRight.
Proof.
  rewrite /prop_LeftRight /= => -[p m l r | // | // ] WF_x; move: (WF_x) => /WF_Bin_children [WF_l WF_r].
  rewrite !Foldable_and_all !Foldable_all_ssreflect !flat_map_cons_f;
    apply/andP; split; apply/allP => /= b /mapP [] x; rewrite in_elem toList_member // => x_in {b}->.
  - case: (WF_x) => [f /Sem_Desc0 [rng DESC0]].
    inversion_clear DESC0 as [|s rng' f' rng_ f'_ DESC rng'_rng f_f'].
    inversion DESC; subst.
Abort.

Require Import OrdTactic.

Theorem Sort_eq {A : eqType} `{OrdLaws A} `{!EqExact A} (xs ys : list A) :
  StronglySorted _<=_ xs ->
  StronglySorted _<=_ ys ->
  (xs == ys) = seq.all (fun a => a \in xs) ys && seq.all (fun b => b \in ys) xs.
Proof.
  elim: xs ys => [|x xs IH_xs] [|y ys] //=.
  inversion_clear 1 as [|X1 X2 SS_xs FA_xs X3]; inversion_clear 1 as [|X1 X2 SS_ys FA_ys X3].
  unfold "=="; rewrite /Eq_list /=; case CMP: (x == y).
  - move: CMP => /Eq_eq ? /=; subst y.
    replace (eqlist xs ys) with (xs == ys) by done; rewrite IH_xs //.
    admit.
  - 
Admitted.

Theorem thm_List : toProp prop_List.
Proof.
  rewrite /prop_List /=; rewrite -/toList => xs POS_xs.
Abort.
  

Theorem thm_Member : toProp prop_Member.
Proof.
  rewrite /prop_Member /= => xs POS_xs n POS_n.
  rewrite !Foldable_all_ssreflect; apply/allP => /= k.
  by rewrite fromList_member // Eq_refl.
Qed.

Lemma elem_app {A} `{Eq_ A} (a : A) (xs ys : list A) :
  elem a (xs ++ ys) = elem a xs || elem a ys.
Proof. by elim: xs => [|x xs] //=; rewrite !elemC -orbA => ->. Qed.

(* Cheating: manually forgetting POS constraint *)
Theorem thm_MemberFromList : toProp prop_MemberFromList.
Proof.
  rewrite /prop_MemberFromList /= => xs _(* POS_xs *).
  set abs_xs := flat_map _ xs.
  apply/andP; split.
  all: rewrite Foldable_all_ssreflect; apply/allP => /= k; rewrite in_elem.
  - rewrite fromList_member //.
    subst abs_xs; elim: xs => [|x xs IH] //=.
    case: (x /= #0) => //=.
    constructor; last assumption.
    apply Z.abs_nonneg.
  - rewrite /notMember /notElem /= fromList_member //.
    + move=> k_abs; have k_pos: (0 <= k)%Z. {
        subst abs_xs; elim: xs k_abs => [|x xs IH] //=.
        rewrite elem_app=> /orP[] //.
        case NZ: (x /= #0)=> //=.
        rewrite elemC elemN orbF => /Eq_eq ->.
        apply Z.abs_nonneg.
      }
      clear k_abs; subst abs_xs; elim: xs => [|x xs IH] //=.
      rewrite elem_app negb_orb IH andbT.
      by case: k k_pos {IH}; case: x.
    + apply Forall_forall=> {k} k; rewrite in_flat_map => -[x [_]].
      case CMP: (x /= #0) => //= -[] //= <-.
      apply Z.abs_nonneg.
Qed.      

Theorem thm_NotMember : toProp prop_NotMember.
Proof.
  rewrite /prop_NotMember /= => xs POS_xs n POS_n.
  rewrite !Foldable_all_ssreflect; apply/allP => /= k.
  by rewrite /notMember /notElem /= fromList_member // Eq_refl.
Qed.

Theorem thm_Prefix : toProp prop_Prefix.
Proof.
Abort.

Theorem thm_Single : toProp prop_Single.
Proof. by rewrite /prop_Single /= => x POS_x; apply/Eq_eq. Qed.

Theorem thm_SingletonValid : toProp prop_SingletonValid.
Proof.
  rewrite /prop_SingletonValid /= => x POS_x.
  by apply valid_correct, singleton_WF.
Qed.

Theorem thm_UnionAssoc : toProp prop_UnionAssoc.
Proof.
  rewrite /prop_UnionAssoc /= => s1 WF1 s2 WF2 s3 WF3.
  
  move: (union_WF _ _ WF1  WF2)  => WF12.
  move: (union_WF _ _ WF2  WF3)  => WF23.
  move: (union_WF _ _ WF12 WF3)  => WF123.
  move: (union_WF _ _ WF1  WF23) => WF123'.
  
  apply/eqIntSetMemberP => // k; apply/Eq_eq.
  by rewrite !union_member // orbA.
Qed.

Theorem thm_UnionComm : toProp prop_UnionComm.
Proof.
Proof.
  rewrite /prop_UnionComm /= => s1 WF1 s2 WF2.
  
  move: (union_WF _ _ WF1 WF2) => WF12.
  move: (union_WF _ _ WF2 WF1) => WF21.
  
  apply/eqIntSetMemberP => // k; apply/Eq_eq.
  by rewrite !union_member // orbC.
Qed.

Theorem thm_UnionInsert : toProp prop_UnionInsert.
Proof.
  rewrite /prop_UnionInsert /= => x POS_x s WF_s.

  move: (singleton_WF x POS_x)          => WF_sing.
  move: (union_WF     _ _ WF_s WF_sing) => WF_union.
  move: (insert_WF    x _ WF_s POS_x)   => WF_ins.

  split=> /=; first by apply valid_correct.
  
  apply/eqIntSetMemberP => // k; apply/Eq_eq.
  by rewrite union_member // singleton_member // insert_member // orbC.
Qed.

Theorem thm_disjoint : toProp prop_disjoint.
Proof.
  rewrite /prop_disjoint /= => s1 WF1 s2 WF2.
  
  move: (intersection_WF _ _ WF1 WF2) => WF12.
  
  elim: s1 WF1 WF12 => [p m l IHl r IHr | p b | ] WF1 WF12.
  - 
Abort.

Theorem thm_filter : toProp prop_filter.
Proof.
Abort.

Theorem thm_foldL : toProp prop_foldL.
Proof.
Abort.

Theorem thm_foldL : toProp prop_foldL.
Proof.
Abort.

Theorem thm_foldR : toProp prop_foldR.
Proof.
Abort.

Theorem thm_foldR : toProp prop_foldR.
Proof.
Abort.

Theorem thm_isProperSubsetOf : toProp prop_isProperSubsetOf.
Proof.
Abort.

Theorem thm_isSubsetOf : toProp prop_isSubsetOf.
Proof.
Abort.

Theorem thm_map : toProp prop_map.
Proof.
Abort.

Theorem thm_ord : toProp prop_ord.
Proof.
Abort.

Theorem thm_partition : toProp prop_partition.
Proof.
Abort.

Theorem thm_size : toProp prop_size.
Proof.
Abort.

Theorem thm_split : toProp prop_split.
Proof.
Abort.

Theorem thm_splitMember : toProp prop_splitMember.
Proof.
Abort.

Theorem thm_splitRoot : toProp prop_splitRoot.
Proof.
Abort.

Theorem thm_isSubsetOf : toProp prop_isSubsetOf.
Proof.
Abort.

Theorem thm_isProperSubsetOf : toProp prop_isProperSubsetOf.
Proof.
Abort.
