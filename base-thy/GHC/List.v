Require Import GHC.Num.
Require Import GHC.List.

(* -------------------------------------------------------------------- *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Lemma hs_coq_lenAcc_add {A} (l : list A) (acc1 acc2 : Z) :
  lenAcc l (acc1 + acc2)%Z = (lenAcc l acc1 + acc2)%Z.
Proof.
  generalize dependent acc1; generalize dependent acc2;
    induction l as [|x l IH]; simpl; auto; intros.
  rewrite <-Z.add_assoc, Z.add_comm, <-Z.add_assoc, Z.add_comm, IH; do 2 f_equal;
    apply Z.add_comm.
Qed.

Lemma hs_coq_lenAcc {A} (l : list A) (acc : Z) :
  lenAcc l acc = (Zlength l + acc)%Z.
Proof.
  generalize dependent acc; induction l as [|x l IH]; simpl; auto; intros.
  rewrite Zlength_cons, Z.add_succ_l, <-IH, hs_coq_lenAcc_add, Z.add_1_r; reflexivity.
Qed.

Theorem hs_coq_list_length {A} (l : list A) :
  length l = Zlength l.
Proof.
  unfold length; rewrite hs_coq_lenAcc, Z.add_0_r; reflexivity.
Qed.

Theorem hs_coq_filter {A} (p : A -> bool) (l : list A) :
  filter p l = Coq.Lists.List.filter p l.
Proof.
  induction l; simpl; auto.
  destruct (p _); f_equal; auto.
Qed.

Theorem hs_coq_reverse : forall A (xs : list A), 
    List.reverse xs = Coq.Lists.List.rev xs.
Proof.
  intros A.
  unfold List.reverse.
  set (rev := fix rev (arg_0__ arg_1__ : list A) {struct arg_0__} : 
   list A :=
     match arg_0__ with
     | nil => arg_1__
     | cons x xs => rev xs (cons x arg_1__)
     end).
  induction xs.
  simpl.
  auto.
  simpl.
  rewrite <- List.rev_append_rev.
  replace (List.rev_append xs (a :: nil)) with 
      (List.rev_append (a :: xs) nil); auto.
Qed.


(* -------------------------------------------------------------------- *)

(* Make sure by-hand definitions are suitable for reasoning. *)

Lemma take_drop : forall (a:Set) (xs : list a) n,
    xs = Coq.Lists.List.app (take n xs) (drop n xs).
Proof.
  intros a xs.
  induction xs; intro n.
  unfold take. unfold drop.
  destruct (n <=? 0)%Z; auto.
  unfold take. unfold drop.
  destruct (n <=? 0)%Z.
  auto.
  fold (@take a).
  fold (@drop a).
  simpl.
  f_equal.
  auto.
Qed.



Lemma List_foldl_foldr:
  forall {a b} f (x : b) (xs : list a),
    List.fold_left f xs x = Coq.Lists.List.fold_right (fun x g a => g (f a x)) id xs x.
Proof.
  intros. revert x.
  induction xs; intro.
  * reflexivity.
  * simpl. rewrite IHxs. reflexivity.
Qed.

Require Import Coq.Lists.List.

Import ListNotations.


Lemma reverse_append : forall A (vs1:list A) (vs0:list A)  a ,
  (List.reverse (a :: vs0) ++ vs1 = List.reverse vs0 ++ (a :: vs1)).
Proof.
  intros A.
  intros.
  rewrite hs_coq_reverse.
  rewrite hs_coq_reverse.
  rewrite <- List.rev_append_rev.
  rewrite <- List.rev_append_rev.
  simpl.
  auto.
Qed.


Ltac expand_pairs :=
match goal with
  |- context[let (_,_) := ?e in _] =>
  rewrite (surjective_pairing e)
end.


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


(* ---------------------------------- zip ----------------------------- *)


(** [zip] and [unzip] *)

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


Lemma map_snd_zip : forall A B  (l1:list B) (l2 : list A), 
    length l1 = length l2 -> List.map snd (List.zip l1 l2) = l2.
Proof.
  intros A B l1. 
  induction l1; intros; destruct l2; simpl in *; auto.
  inversion H.
  f_equal. 
  apply IHl1.
  inversion H.
  auto.
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
