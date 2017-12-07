Require Import GHC.Base.
Import Notations.

Require Import Data.Set.Base.
Require Import Coq.FSets.FSetInterface.

From mathcomp Require Import ssrbool ssreflect.

Module Foo (E : OrderedType) : WSfun(E).
  Local Instance Eq_t : GHC.Base.Eq_ E.t :=
    fun _ k => k {|
                op_zeze____ := fun x y => E.eq_dec x y;
                op_zsze____ := fun x y => negb (E.eq_dec x y);
              |}.

  Local Definition compare (x y: E.t) : comparison :=
    match E.compare x y with
    | EQ _ => Eq
    | LT _ => Lt
    | GT _ => Gt
    end.
  
  Local Instance Ord_t : GHC.Base.Ord E.t := GHC.Base.ord_default compare.

  Module OrdFacts := OrderedTypeFacts(E).

  Definition elt := E.t.
  
  (* Well-formedness *)
  Definition WF (s : Set_ elt) := True. (* TODO. maybe simply [valid s = true]? *)
  Definition t := {s : Set_ elt | WF s}.
  Definition pack (s : Set_ elt) (H : WF s): t := exist _ s H.

  Definition In x (s' : t) := match s' with exist s P =>
     member x s = true
     end.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Definition empty : t := pack empty I.
  Definition is_empty : t -> bool := fun s' => match s' with exist s _ =>
     null s end.
  Definition mem : elt -> t -> bool := fun e s' => match s' with exist s _ =>
     member e s end.
  Definition add : elt -> t -> t. Admitted. (* must contain a WF proof *)
  Definition singleton : elt -> t. Admitted.
  Definition remove : elt -> t -> t. Admitted.
  Definition union : t -> t -> t. Admitted.
  Definition inter : t -> t -> t. Admitted.
  Definition diff : t -> t -> t. Admitted.
  Definition eq : t -> t -> Prop := Equal.
  Definition eq_dec : forall s s' : t, {eq s s'} + {~ eq s s'}.
    destruct s as [s]; destruct s' as [s']; simpl.
    destruct (s == s') eqn:Heq.
    (* LY: How should I proceed? *)
  Admitted.
    
  Definition equal : t -> t -> bool :=
    fun s s' =>
      match s, s' with
      | exist s _, exist s' _ => s == s'
      end.
  
  Definition subset : t -> t -> bool :=
    fun s s' =>
      match s, s' with
      | exist s _, exist s' _ => isSubsetOf s s'
      end.
        
  Definition fold : forall A : Type, (elt -> A -> A) -> t -> A -> A. Admitted.
  Definition for_all : (elt -> bool) -> t -> bool. Admitted.
  Definition exists_ : (elt -> bool) -> t -> bool. Admitted.
  Definition filter : (elt -> bool) -> t -> t. Admitted.
  Definition partition : (elt -> bool) -> t -> t * t. Admitted.
  Definition cardinal : t -> nat. Admitted.
  Definition elements : t -> list elt. Admitted.
  Definition choose : t -> option elt. Admitted.
  Lemma In_1 :
    forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.
  Proof.
    (* LY: Surely this can be simplified? *)
    unfold In; destruct s as [s']; induction s'; auto. intros.
    simpl in H0; destruct (Base.compare x a) eqn:Hcomp;
      vm_compute in Hcomp; destruct (E.compare x a);
        inversion Hcomp; clear Hcomp.
    - apply E.eq_sym in H. apply (E.eq_trans H) in e.
      apply OrdFacts.elim_compare_eq in e; destruct e as [? Heq].
      simpl. vm_compute. rewrite Heq; auto.
    - apply (OrdFacts.eq_lt (E.eq_sym H)) in l.
      apply OrdFacts.elim_compare_lt in l; destruct l as [? Hlt]. simpl.
      assert (Hcomp: Base.compare y a = Lt).
      { vm_compute. rewrite Hlt; auto. }
      rewrite Hcomp. eauto.
    - assert (Heq: E.eq x y) by apply H.
      apply (OrdFacts.lt_eq l) in H.
      apply OrdFacts.elim_compare_gt in H; destruct H as [? Hgt]. simpl.
      assert (Hcomp: Base.compare y a = Gt).
      { vm_compute. rewrite Hgt; auto. }
      rewrite Hcomp. eauto.
  Qed.
      
  Lemma eq_refl : forall s : t, eq s s.
  Proof. intros; constructor; auto. Qed.
    
  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. unfold eq; unfold Equal; symmetry; auto. Qed.
    
  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    unfold eq; unfold Equal; intros s s' s'' H1 H2 a.
    apply (iff_trans (H1 a) (H2 a)).
  Qed.
    
  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
    
  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
  
  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true. Admitted.
  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'. Admitted.
  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true. Admitted.
  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'. Admitted.
  
  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.
    
  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    unfold Empty; unfold In. destruct s; destruct x; auto.
    intros H. specialize (H e). simpl in H.
    assert (Heq: E.eq e e); auto.
    assert (Hcomp: Base.compare e e = Eq).
    { vm_compute. apply OrdFacts.elim_compare_eq in Heq.
      destruct Heq. rewrite H0; auto. }
    rewrite Hcomp in H. contradiction.
  Qed.
      
  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    unfold Empty; unfold In. destruct s; destruct x; auto.
  Qed.
      
  Lemma add_1 :
    forall (s : t) (x y : elt), E.eq x y -> In y (add x s). Admitted.
  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s). Admitted.
  Lemma add_3 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y (add x s) -> In y s. Admitted.
  Lemma remove_1 :
    forall (s : t) (x y : elt), E.eq x y -> ~ In y (remove x s). Admitted.
  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y s -> In y (remove x s). Admitted.
  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s. Admitted.
  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> E.eq x y. Admitted.
  Lemma singleton_2 :
    forall x y : elt, E.eq x y -> In y (singleton x). Admitted.
  Lemma union_1 :
    forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'. Admitted.
  Lemma union_2 :
    forall (s s' : t) (x : elt), In x s -> In x (union s s'). Admitted.
  Lemma union_3 :
    forall (s s' : t) (x : elt), In x s' -> In x (union s s'). Admitted.
  Lemma inter_1 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s. Admitted.
  Lemma inter_2 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s'. Admitted.
  Lemma inter_3 :
    forall (s s' : t) (x : elt), In x s -> In x s' -> In x (inter s s'). Admitted.
  Lemma diff_1 :
    forall (s s' : t) (x : elt), In x (diff s s') -> In x s. Admitted.
  Lemma diff_2 :
    forall (s s' : t) (x : elt), In x (diff s s') -> ~ In x s'. Admitted.
  Lemma diff_3 :
    forall (s s' : t) (x : elt), In x s -> ~ In x s' -> In x (diff s s'). Admitted.
  Lemma fold_1 :
    forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
    fold A f s i =
    fold_left (fun (a : A) (e : elt) => f e a) (elements s) i. Admitted.
  Lemma cardinal_1 : forall s : t, cardinal s = length (elements s). Admitted.
  Lemma filter_1 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x (filter f s) -> In x s. Admitted.
  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x (filter f s) -> f x = true. Admitted.
  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s). Admitted.
  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true. Admitted.
  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s. Admitted.
  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true. Admitted.
  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s. Admitted.
  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s). Admitted.
  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s). Admitted.
  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA E.eq x (elements s). Admitted.
  Lemma elements_2 :
    forall (s : t) (x : elt), InA E.eq x (elements s) -> In x s. Admitted.
  Lemma elements_3w : forall s : t, NoDupA E.eq (elements s). Admitted.
  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s. Admitted.
  Lemma choose_2 : forall s : t, choose s = None -> Empty s. Admitted.

End Foo.
