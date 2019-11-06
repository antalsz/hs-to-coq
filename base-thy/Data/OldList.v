Require Import Data.OldList.
Require Import GHC.Base.
Require Import GHC.Char.
Require GHC.Unicode.
Require Import Omega.


(* -------------------------------------------------------------------- *)

(* Haskell-Coq equivalence *)


Theorem hs_coq_partition {A} (p : A -> bool) (l : list A) :
  Data.OldList.partition p l = Coq.Lists.List.partition p l.
Proof.
  unfold partition; induction l; simpl; auto.
Qed.

Require Coq.Lists.List.


Lemma words_def s : words s = 
  match (GHC.List.dropWhile GHC.Unicode.isSpace s) with 
    | nil => nil
    | s'  =>
     let 'pair w s'' := GHC.List.break GHC.Unicode.isSpace s' in
     cons w (words s'')
  end.
Admitted.
Lemma lines_def s : lines s = 
  if (List.null s) then nil else 
  let cons_ := fun '(pair h t) => cons h t in
  cons_ (let 'pair l s' := GHC.List.break 
                             (fun arg_4__ =>
                                arg_4__ == newline) s in
         pair l (match s' with | nil => nil | cons _ s'' => lines s'' end)).
Proof.
Admitted.


Lemma words_nil : words nil = nil. Proof. reflexivity. Qed.
Lemma lines_nil : lines nil = nil. reflexivity. Qed.


Lemma words_cons : forall c s, words (cons c s) = 
                   if Unicode.isSpace c then words s
                   else let (w, s'') := GHC.List.break Unicode.isSpace (cons c s) in 
                        (cons w (words s'')).
Proof. intros. 
       rewrite words_def.
       simpl.
       rewrite (words_def s).
       destruct (Unicode.isSpace c) eqn:S.
       - destruct (List.dropWhile Unicode.isSpace s) eqn:D. auto.
         reflexivity. 
       - rewrite S.
         reflexivity.
Qed.

Lemma lines_cons : forall c s, 
    lines (cons c s) = 
    (fun x => match x with | (pair h t) => cons h t end) 
      (match GHC.List.break (fun x => x == Char.newline) (cons c s) with
       | (l, s') => (l, match s' with 
                       | nil => nil
                       | cons _ s'' => lines s''
                       end)
       end).
Proof.
  intros.
  rewrite lines_def.
  simpl.
  reflexivity.
Qed.

Hint Rewrite words_nil lines_nil words_cons lines_cons : hs_simpl.


