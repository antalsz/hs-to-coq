Require Import Bag.
Require Import WellFormed.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.
Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.OldList.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import ListUtils.
Require Import Coq.ZArith.ZArith.

Require Data.Traversable.
Import GHC.Base.
Import Data.Functor.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Correctness.

From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Bullet Behavior "Strict Subproofs".

(***** Operators *****)

Infix "<$>" := Data.Functor.op_zlzdzg__ : hs_op_scope.
Infix "<*>" := GHC.Base.op_zlztzg__ : hs_op_scope.
Infix ">>=" := GHC.Base.op_zgzgze__ : hs_op_scope.
Infix ">>" := GHC.Base.op_zgzg__ : hs_op_scope.
Open Scope hs_op_scope.

(***** Working with extensionality *****)

(* Like the "extensionality" tactic, but doesn't intro -- nicer with ssreflect *)
Ltac funext :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality)
  end.

(* From https://stackoverflow.com/a/43853467/237428 *)
Instance pointwise_eq_ext {A B : Type} {RB : relation B} `(sb : subrelation B RB eq)
  : subrelation (pointwise_relation A RB) eq.
Proof. intros f g Hfg. apply functional_extensionality. intro x; apply sb, (Hfg x). Qed.

(***** Bag correctness theorems *****)

Theorem mapBagM_ok {M A B} `{MonadLaws M} (f : A -> M B) (b : Bag A) :
  GHC.Base.fmap bagToList (mapBagM f b) = Data.Traversable.mapM f (bagToList b).
Proof.
  rewrite /Data.Traversable.mapM /Traversable.instance_Traversable_list /Data.Traversable.mapM__
          /=
          /Data.Traversable.instance_Traversable_list_mapM 
          /Data.Traversable.instance_Traversable_list_traverse.
  replace (fmap bagToList (mapBagM f b)) with
          (_++_ <$> (fmap bagToList (mapBagM f b)) <*> pure [])
          by by unfold "<$>";
                rewrite functor_composition !applicative_fmap applicative_interchange
                        -applicative_composition !applicative_homomorphism;
                do 2 f_equal; funext=> ?; unfold "∘"; rewrite app_nil_r.
  generalize (pure ([] : list B)) => z.
  elim: b z => [| x | l IHl r IHr | xs] z //=.
  - rewrite applicative_fmap -monad_applicative_pure applicative_homomorphism.
    unfold "<$>"; rewrite applicative_fmap applicative_homomorphism.
    replace [eta app _] with (@GHC.Base.id (list B)) by by funext.
    apply applicative_identity.
  - unfold "<$>"; rewrite
      !applicative_fmap !monad_applicative_ap /ap !monad_applicative_pure !monad_left_id
      -!monad_composition.
    by f_equal; funext => ?; rewrite !monad_left_id.
  - rewrite bagToList_TwoBags hs_coq_foldr_base fold_right_app -!hs_coq_foldr_base.
    rewrite -IHr -IHl.
    unfold "<$>"; rewrite
      !functor_composition !applicative_fmap
      !monad_applicative_ap /ap !monad_applicative_pure !monad_left_id -!monad_composition.
    f_equal; funext=> ?.
    rewrite !monad_left_id -!monad_composition.
    f_equal; funext=> ?.
    rewrite !monad_left_id -!monad_composition.
    f_equal; funext=> ?.
    rewrite monad_left_id.
    f_equal.
    by unfold "∘"; rewrite /= bagToList_TwoBags app_assoc.
  - rewrite bagToList_ListBag
            /Data.Traversable.mapM /Traversable.instance_Traversable_list /Data.Traversable.mapM__
            /Data.Traversable.instance_Traversable_list_mapM
            /Data.Traversable.instance_Traversable_list_traverse.
    unfold "<$>"; rewrite
      functor_composition applicative_fmap
      !monad_applicative_ap /ap monad_applicative_pure monad_left_id.
    rewrite -!monad_composition.
    elim: xs z => [|x xs IH] z /=.
    + rewrite monad_applicative_pure !monad_left_id.
      replace (fun _ : list B => return_ _) with (return_ : list B -> M (list B));
        first by apply monad_right_id.
      by funext.
    + rewrite -(IH z).
      rewrite !applicative_fmap !monad_applicative_ap /ap monad_applicative_pure
              !monad_left_id -!monad_composition.
      f_equal; funext=> ?.
      rewrite !monad_left_id -!monad_composition.
      f_equal; funext=> ?.
      rewrite -!monad_composition !monad_left_id -!monad_composition.
      f_equal; funext=> ?.
      by rewrite !monad_left_id.
Qed.

Theorem foldr_app {A B} (f : A -> B -> B) (z : B) (xs ys : list A) :
  foldr f z (xs ++ ys) = foldr f (foldr f z ys) xs.
Proof. by rewrite hs_coq_foldr_base fold_right_app -!hs_coq_foldr_base. Qed.

Lemma monad_bind_return_fmap {M A B} `{MonadLaws M} (f : A -> B) (mx : M A) :
  (mx >>= fun x : A => return_ (f x)) = (f <$> mx).
Proof.
  by unfold "<$>"; rewrite applicative_fmap monad_applicative_ap monad_applicative_pure /ap
                           monad_left_id.
Qed.

Lemma monad_bind_return_fmap2 {M A B C} `{MonadLaws M} (f : A -> B -> C) (mx : M A) (my : M B) :
  (mx >>= fun x => (my >>= fun y => return_ (f x y))) = (f <$> mx <*> my).
Proof.
  unfold "<$>".
  rewrite applicative_fmap !monad_applicative_ap monad_applicative_pure /ap.
  rewrite monad_left_id -monad_composition.
  f_equal; funext; intros.
  rewrite monad_left_id.
  reflexivity.
Qed.

Lemma monad_bind_fmap_ap {M A B C} `{MonadLaws M} (f : A -> B -> C) (mx : M A) (my : M B) :
  (mx >>= fun x : A => fmap (f x) my) = (f <$> mx <*> my).
Proof.
  unfold "<$>";
    setoid_rewrite ->applicative_fmap;
    repeat setoid_rewrite ->monad_applicative_ap;
    setoid_rewrite ->monad_applicative_pure;
    unfold ap.
  by rewrite -!monad_composition monad_left_id -!monad_composition.
Qed.

Lemma applicative_fmap_pure {F A B} `{ApplicativeLaws F} (f : A -> B) (x : A) :
  fmap f (pure x) = pure (f x) :> F B.
Proof. by rewrite applicative_fmap applicative_homomorphism. Qed.

Lemma monad_fmap_return {M A B} `{MonadLaws M} (f : A -> B) (x : A) :
  fmap f (return_ x) = return_ (f x) :> M B.
Proof. by rewrite -!monad_applicative_pure applicative_fmap_pure. Qed.

Theorem mapBagM_ok' {M A B} `{MonadLaws M} (f : A -> M B) (b : Bag A) :
  GHC.Base.fmap bagToList (mapBagM f b) = Data.Traversable.mapM f (bagToList b).
Proof.
  rewrite /Data.Traversable.mapM /Traversable.instance_Traversable_list /Data.Traversable.mapM__ /=
          /Data.Traversable.instance_Traversable_list_mapM 
          /Data.Traversable.instance_Traversable_list_traverse.
  replace (fmap bagToList (mapBagM f b)) with
          (_++_ <$> (fmap bagToList (mapBagM f b)) <*> pure [])
          by by unfold "<$>";
                rewrite functor_composition !applicative_fmap applicative_interchange
                        -applicative_composition !applicative_homomorphism;
                do 2 f_equal; funext=> ?; unfold "∘"; rewrite app_nil_r.
  generalize (pure ([] : list B)) => z.
  elim: b z => [| x | l IHl r IHr | xs] z //=.
  - by unfold "<$>";
       rewrite functor_composition monad_fmap_return -monad_applicative_pure
               applicative_identity.
  - by rewrite monad_bind_return_fmap; unfold "<$>"; rewrite !functor_composition.
  - setoid_rewrite ->monad_bind_return_fmap; setoid_rewrite ->monad_bind_fmap_ap.
    rewrite bagToList_TwoBags foldr_app -IHl -IHr.
    unfold "<$>"; rewrite !functor_composition.
    rewrite !applicative_fmap -!applicative_composition !applicative_homomorphism; f_equal.
    rewrite !applicative_interchange -!applicative_fmap functor_composition; do 2 f_equal.
    funext=> l'; funext=> r'; funext=> z'.
    by unfold "∘"; rewrite bagToList_TwoBags app_assoc.
  - rewrite bagToList_ListBag
            /Data.Traversable.mapM /Traversable.instance_Traversable_list /Data.Traversable.mapM__
            /Data.Traversable.instance_Traversable_list_mapM
            /Data.Traversable.instance_Traversable_list_traverse.
    rewrite monad_bind_return_fmap; unfold "<$>"; rewrite !functor_composition.
    elim: xs => [|x xs IH] /=.
    + by rewrite applicative_fmap_pure applicative_identity.
    + rewrite -IH.
      rewrite !applicative_fmap -!applicative_composition !applicative_homomorphism.
      by rewrite applicative_interchange -applicative_composition !applicative_homomorphism.
Qed.

Ltac applicative_normalize :=
  simpl;
  unfold "<$>"; rewrite ?applicative_fmap -?monad_applicative_pure;
  repeat (rewrite applicative_identity     ||
          rewrite applicative_homomorphism || 
          rewrite applicative_interchange  || 
          rewrite -applicative_composition).

Ltac applicative_equal :=
  match goal with
    | |- (pure _    = pure _)    => f_equal
    | |- ((_ <*> _) = (_ <*> _)) => progress f_equal; applicative_equal
    | |- (_ = _)                 => idtac
  end.

Ltac applicative_normalize_equal :=
  applicative_normalize=> //; applicative_equal=> //; repeat funext=> ? //.

Ltac anf       := applicative_normalize.
Ltac anf_equal := applicative_normalize_equal.

Theorem mapBagM_ok'' {M A B} `{MonadLaws M} (f : A -> M B) (b : Bag A) :
  GHC.Base.fmap bagToList (mapBagM f b) = Data.Traversable.mapM f (bagToList b).
Proof.
  rewrite /Data.Traversable.mapM /Data.Traversable.mapM /Traversable.instance_Traversable_list /Data.Traversable.mapM__ /=
          /Data.Traversable.instance_Traversable_list_mapM 
          /Data.Traversable.instance_Traversable_list_traverse.
  replace (fmap bagToList (mapBagM f b)) with
          (_++_ <$> (fmap bagToList (mapBagM f b)) <*> pure [])
          by by anf_equal; unfold "∘"; rewrite app_nil_r.
  generalize (pure ([] : list B)) => z.
  elim: b z => [| x | l IHl r IHr | xs] z //=.
  - anf_equal.
  - rewrite monad_bind_return_fmap; anf_equal.
  - rewrite bagToList_TwoBags foldr_app -IHl -IHr.
    setoid_rewrite ->monad_bind_return_fmap; setoid_rewrite ->monad_bind_fmap_ap.
    by anf_equal; unfold "∘"; rewrite bagToList_TwoBags app_assoc.
  - rewrite bagToList_ListBag
            /Data.Traversable.mapM /Data.Traversable.mapM /Traversable.instance_Traversable_list /Data.Traversable.mapM__
            /Data.Traversable.instance_Traversable_list_mapM
            /Data.Traversable.instance_Traversable_list_traverse.
    rewrite monad_bind_return_fmap; anf.
    elim: xs => [|x xs /= <-]; anf_equal.
Qed.

  (* I forget what I was trying to do with this. —ASZ *)
Theorem mapBagM_ok''' {M A B} `{MonadLaws M} (f : A -> M B) (b : Bag A) :
  GHC.Base.fmap bagToList (mapBagM f b) = Data.Traversable.traverse f (bagToList b).
Proof.
(*
  rewrite /Data.Traversable.traverse /Traversable.instance_Traversable_list /Data.Traversable.traverse__
         /= /Data.Traversable.instance_Traversable_list_traverse.
  replace (fmap bagToList (mapBagM f b)) with
          (_++_ <$> (fmap bagToList (mapBagM f b)) <*> pure [])
          by by unfold "<$>";
                rewrite functor_composition !applicative_fmap applicative_interchange
                        -applicative_composition !applicative_homomorphism;
                do 2 f_equal; funext=> ?; unfold "∘"; rewrite app_nil_r.
  generalize (pure ([] : list B)) => z.
  elim: b z => [| x | l IHl r IHr | xs] z //=.
  - rewrite applicative_fmap -monad_applicative_pure applicative_homomorphism.
    unfold "<$>"; rewrite applicative_fmap applicative_homomorphism.
    replace [eta app _] with (@GHC.Base.id (list B)) by by funext.
    apply applicative_identity.
  - unfold "<$>". rewrite
      !applicative_fmap !monad_applicative_ap /ap !monad_applicative_pure.
 *)
Abort.

Lemma mapM_nil {M A B} `{MonadLaws M} (f : A -> M B):
  Traversable.mapM f [] = pure [].
Proof.
  by rewrite /Traversable.mapM /Traversable.instance_Traversable_list /Traversable.mapM__.
Qed.

Lemma mapM_cons {M A B} `{MonadLaws M} (f : A -> M B) x xs:
  Traversable.mapM f (x::xs) = ((cons <$> f x) <*> Traversable.mapM f xs).
Proof.
  by rewrite /Traversable.mapM /Traversable.instance_Traversable_list /Traversable.mapM__.
Qed.

Lemma mapM_app {M A B} `{MonadLaws M} (f : A -> M B) l1 l2:
  Traversable.mapM f (l1 ++ l2) = (app <$> Traversable.mapM f l1 <*> Traversable.mapM f l2).
Proof.
  intros. induction l1.
  * rewrite /Traversable.mapM /Traversable.instance_Traversable_list /Traversable.mapM__.
    anf. reflexivity.
  * rewrite /= !mapM_cons IHl1.
    anf. reflexivity.
Qed.

Lemma monad_fmap_bind1 {M A B C} `{MonadLaws M} (f : B -> C) (a : M A) k:
  fmap f (a >>= k) = (a >>= (fun x => fmap f (k x))).
Proof.
  (* Get LHS into monad-only land *)
  rewrite !applicative_fmap !monad_applicative_ap /ap monad_applicative_pure.
  (* Clean up a bit *)
  rewrite monad_left_id -monad_composition.
  f_equal; funext; intros.
  (* Get RHS into monad-only land *)
  rewrite !applicative_fmap !monad_applicative_ap /ap monad_applicative_pure.
  rewrite monad_left_id.
  reflexivity.
Qed.

Lemma monad_fmap_bind2 {M A B C} `{MonadLaws M} (f : A -> B) (a : M A) (k : B -> M C):
  (fmap f a >>= k) = (a >>= (fun x => k (f x))).
Proof.
  (* Get LHS into monad-only land *)
  rewrite !applicative_fmap !monad_applicative_ap /ap monad_applicative_pure.
  (* Clean up a bit *)
  rewrite monad_left_id -monad_composition.
  f_equal; funext; intros.
  rewrite monad_left_id.
  reflexivity.
Qed.

Theorem mapMBag_ok''' {M A B} `{MonadLaws M} (f : A -> M B) (b : Bag A) :
  GHC.Base.fmap bagToList (mapBagM f b) = Data.Traversable.mapM f (bagToList b).
Proof.
  induction b.
  * rewrite /= emptyBag_ok mapM_nil -monad_applicative_pure.
    anf_equal.
  * rewrite /= monad_bind_return_fmap bagToList_UnitBag mapM_cons mapM_nil.
    anf_equal.
  * rewrite /= bagToList_TwoBags.
    rewrite monad_bind_return_fmap2.
    rewrite mapM_app.
    rewrite -IHb1 -IHb2.
    anf_equal.
    by rewrite /op_z2218U__ bagToList_TwoBags.
  * rewrite /= monad_bind_return_fmap bagToList_ListBag.
    anf_equal.
    replace (_∘_ bagToList Mk_ListBag) with (@id (list B)).
    anf_equal.
    funext; intros.
    by rewrite /op_z2218U__ bagToList_ListBag.
Qed.

(* TODO mapBagM_ mapAndUnzipBagM *)


(* we need to add that to MonadLaws *)
Axiom extra_monad_then_bind:
  forall {M A B} `{Monad M} (x:M A) (y: M B),
    (x >> y) = (x >>= (fun _ => y)).


Lemma fold_right_then {M A B} `{MonadLaws M}
      (x : M B) (l: list (M A)):
    fold_right _>>_ x l =
     _>>_ (fold_right _>>_ (return_ tt) l) x.
Proof.
  induction l; simpl.
  - rewrite extra_monad_then_bind.
    rewrite monad_left_id.
    reflexivity.
  - rewrite IHl.
    rewrite !extra_monad_then_bind.
    rewrite monad_composition.
    reflexivity.
Qed.

Theorem mapBagM_is_ok {M A B} `{MonadLaws M} (f : A -> M B) (b : Bag A) :
  (mapBagM_ f b) =
  Data.Foldable.mapM_ f (bagToList b).
Proof.
  rewrite /Data.Foldable.mapM_ /=
          /Foldable.instance_Foldable_list_foldr
          /Foldable.foldr /Foldable.instance_Foldable_list
          /Foldable.foldr__
          /Foldable.instance_Foldable_list_foldr.
  induction b; simpl; try reflexivity.
  - rewrite bagToList_TwoBags foldr_app.
    rewrite -IHb2.
    rewrite !hs_coq_foldr_base -fold_right_map.
    rewrite fold_right_then.
    rewrite  fold_right_map -hs_coq_foldr_base.
    rewrite -IHb1. reflexivity.
  - rewrite /Foldable.mapM_
            hs_coq_foldr_list hs_coq_foldr_base.
    rewrite bagToList_ListBag. reflexivity.
Qed.

  
Theorem mapAndUnzipBagM_ok {M A B C} `{MonadLaws M}
        (f : A -> M (B*C)%type) (b : Bag A) :
  GHC.Base.fmap bagToList (GHC.Base.fmap (fst) (mapAndUnzipBagM f b)) =
  GHC.Base.fmap (map fst) (Data.Traversable.mapM f (bagToList b)) /\
  GHC.Base.fmap bagToList (GHC.Base.fmap (snd) (mapAndUnzipBagM f b)) =
  GHC.Base.fmap (map snd) (Data.Traversable.mapM f (bagToList b)).
Proof.
Admitted.
(* 
  rewrite
    /Data.Traversable.mapM
    /Traversable.instance_Traversable_list
    /Data.Traversable.mapM__
    /Data.Traversable.instance_Traversable_list_mapM
    /Data.Traversable.instance_Traversable_list_traverse.
  induction b; simpl;
    [split; anf_equal | | |].
  - split.
    + replace
        (fmap fst
           (f a >>=
              (fun arg_23__ : B * C =>
                 let (r, s) := arg_23__ in
                 return_ (Mk_UnitBag r, Mk_UnitBag s)))) with
        (fmap fst
          (f a >>=
             (fun x: B * C =>
                return_ (Mk_UnitBag (fst x),
                         Mk_UnitBag (snd x))))).
      * 
      * do 2 f_equal. funext=> p. destruct p. reflexivity.
      rewrite -monad_bind_fmap_ap !applicative_fmap.
   
      Print MonadLaws.
      
      Check @applicative_fmap.
      admit.
      unfold "<$>".
      rewrite functor_composition
              !applicative_fmap applicative_interchange
      -applicative_composition !applicative_homomorphism;
        do 2 f_equal; funext=> ?; unfold "∘";
                                rewrite app_nil_r.
      unfold bagToList.
      anf.
      rewrite applicative_fmap_pure.
      anf.
      replace
        (fmap fst
           (f a >>=
              (fun arg_23__ : B * C =>
                 let (r, s) := arg_23__ in
                 return_ (Mk_UnitBag r, Mk_UnitBag s)))) with
        (fmap fst
          (f a >>=
             (fun x: B * C =>
                return_ (Mk_UnitBag (fst x),
                         Mk_UnitBag (snd x))))).
      * admit.
      * repeat f_equal.
        anf.
        Search (_ = (let _ := _ in _)). split.
        destruct arg_23__. Hint View (let _ := _ in _) fst.
        idtac.
        Search (_ <$>  _).
      rewrite -monad_bind_fmap_ap.
 
      
      Search (fmap _ (fmap _ _)).
      rewrite applicative_fmap_pure. Search fmap.
      anf_equal.
      
      f_equal.
      

      apply monad_left_id.
      destruct arg_23__.
      Locate "let".
      ?x:=_ in _). admit.
    + admit.
  - split.
    
    Check @monad_fmap_return.
      Check  applicative_interchange.
      Search (_ <*> pure _).
      Search (_∘_ _ _).
      Locate "<*>".
      Search op_zlztzg__.
      Print MonadLaws.

      Print ApplicativeLaws. Search fmap.
      Search return_. simpl.
Admitted.
 *)
(* TODO foldrBagM foldlBagM *)
Check foldrBagM.
Print GHC.Base.fmap.
Check mapBagM.
Search foldr.
(*
Theorem foldrBagM_ok {M A B C} `{MonadLaws M}
        (f : A -> B -> M B) (d : B) (b : Bag A):
  (GHC.Base.fmap bagToList (foldrBagM f d b) =
  (fold_right f (bagToList b))).
Proof.
  
Admitted.
*)
(* TODO flatMapBagM flatMapBagPairM *)

(* TODO filterBagM *)

(* TODO anyBagM *)
