(*Contains only the rewriting Lemma for [toList] of Heap because it takes forever to compile*)
Require Import Data.Graph.Inductive.Internal.Heap.
Require Import Coq.Program.Wf.


Section Heap.

Context {A B : Type} `{Hord: Base.Ord A} {Hdefault : Err.Default A} {Hdefault' : Err.Default B}.

Definition expand_toList := 
  fun {a} {b} `{GHC.Base.Ord a} `{Err.Default (a * b)} (arg_0__ : Heap a b) =>
    match arg_0__ with
    | Heap.Empty => nil
    | h => let 'pair x r := pair (findMin h) (deleteMin h) in cons x (toList r)
    end.

Lemma unfold_toList : forall h, expand_toList h = toList h.
Proof.
  intros. destruct h; simpl. reflexivity. simpl.  f_equal. unfold toList at 2. unfold toList_func.
  rewrite fix_sub_eq; simpl.  reflexivity. intros. destruct x; simpl. destruct s; simpl. destruct s; simpl. destruct s; simpl.
  destruct s eqn : ?; simpl. destruct h eqn : ?. reflexivity. f_equal. rewrite H0. reflexivity.
Qed.

End Heap.

