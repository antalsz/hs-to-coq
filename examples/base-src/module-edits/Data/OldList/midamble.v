Require Import GHC.Char.
Require GHC.Unicode.
Require Coq.Lists.List.
Require Import Omega.
Import Ascii.AsciiSyntax.
Import String.StringSyntax.


Fixpoint ascending {a0} (arg_48__: a0 -> a0 -> comparison) (a:a0) (as_:list a0 -> list a0) (bs: list a0)
         {struct bs} : list (list a0)
        := let j_53__ : list (list a0) :=
             match arg_48__ , a , as_ , bs with
               | cmp , a , as_ , bs => cons (as_ (cons a nil))
                                           (match bs with
                                           | cons a (cons b xs) =>  if GHC.Base.eq_comparison (cmp a b) Gt : bool
                                                                   then descending cmp b (cons a nil) xs
                                                                   else ascending cmp b (fun y => cons a y) xs
                                           | xs => cons xs nil
                                           end)
             end in
           match arg_48__ , a , as_ , bs with
             | cmp , a , as_ , cons b bs => if negb (GHC.Base.eq_comparison (cmp a b) Gt)
                                            then ascending cmp b (fun arg_54__ =>
                                                                   match arg_54__ with
                                                                     | ys => as_ (cons a ys)
                                                                   end) bs
                                            else j_53__
             | _ , _ , _ , _ => j_53__
           end
with descending {a0} (arg_40__: a0 -> a0 -> comparison) (a:a0) (arg_42__:list a0) arg_43__
     {struct arg_43__} :=
       let j_45__  : list (list a0) :=
           match arg_40__ , a , arg_42__ , arg_43__ with
           | cmp , a , as_ , bs => cons (cons a as_)
                                       (match bs with
                                        | cons a (cons b xs) =>  if GHC.Base.eq_comparison (cmp a b) Gt : bool
                                                                then descending cmp b (cons a nil) xs
                                                                else ascending cmp b (fun y => cons a y) xs
                                        | xs => cons xs nil
                                        end)
           end in
       match arg_40__ , a , arg_42__ , arg_43__ with
       | cmp , a , as_ , cons b bs => if GHC.Base.eq_comparison (cmp a b) Gt : bool
                                     then descending cmp b (cons a as_) bs
                                     else j_45__
       | _ , _ , _ , _ => j_45__
       end.

Definition sequences {a0} (cmp : a0 -> a0 -> comparison) (ys:list a0) : list (list a0)  :=
    match ys with
      | cons a (cons b xs) =>  if GHC.Base.eq_comparison (cmp a b) Gt : bool
                              then descending cmp b (cons a nil) xs
                              else ascending cmp b (fun y => cons a y) xs
      | xs => cons xs nil
    end.


Fixpoint merge {a0} (cmp: a0 -> a0 -> comparison) (l1:list a0) (l2: list a0) : list a0 :=
  let fix merge_aux l2 :=
      match l1 , l2 with
      | (cons a as' as as_) , (cons b bs' as bs) =>
        if GHC.Base.eq_comparison (cmp a b) Gt : bool
        then cons b (merge_aux bs')
        else cons a (merge cmp as' bs)
      | nil , bs => bs
      | as_ , nil => as_
      end in
  merge_aux l2.

Fixpoint mergePairs {a0} (cmp: a0 -> a0 -> comparison) xs
        := match xs with
             | cons a (cons b xs) => cons (merge cmp a b) (mergePairs cmp xs)
             | xs => xs
           end.


Lemma mergePairs_length : forall n, forall a cmp (xs : list (list a)) x y,
      le (length xs) n ->
      lt (length (mergePairs cmp (cons x (cons y xs)))) (2 + n).
induction n. intros; simpl. destruct xs; inversion H. simpl. auto.
intros.
destruct xs.
simpl in *. omega.
destruct xs.
simpl in *. omega.
assert (L : le (length xs) n).
simpl in H. omega.
specialize (IHn a cmp xs l l0 L).
simpl in *. omega.
Qed.

Program Fixpoint mergeAll {a0} (cmp: a0 -> a0 -> comparison)
        (xs : list (list a0)) {measure (length xs) } : list a0 :=
  match xs with
  | nil        => nil
  | cons x nil => x
  | cons x (cons y xs) => mergeAll cmp (mergePairs cmp (cons x (cons y xs)))
  end.
Next Obligation.
simpl.
destruct xs. simpl. auto.
destruct xs. simpl. auto.
apply lt_n_S.
pose (MP := mergePairs_length (length xs) a0 cmp xs l l0 ltac:(auto)). clearbody MP.
simpl in *.
omega.
Defined.

Definition sortBy {a} (cmp : a -> a -> comparison) (xs : list a): list a :=
     mergeAll cmp (sequences cmp xs).

(* -------------------------------------------- *)

Lemma dropWhile_cons_prop : forall {A} (c:A) s p s',
  cons c s' = GHC.List.dropWhile p s ->
  p c = false.
Proof.
  induction s.
  + intros. simpl in *. discriminate.
  + intros p s' H. simpl in H.
    destruct (p a) eqn:Hp.
    ++ eapply IHs. eauto.
    ++ inversion H. subst. auto.
Qed.

Lemma dropWhile_cons_length : forall {A} (c:A) s p s',
  cons c s' = GHC.List.dropWhile p s ->
  lt (length s') (length s).
Proof.
  induction s.
  + intros. simpl in *. discriminate.
  + intros p s' H. simpl in *.
    destruct (p a) eqn:Hp.
    pose (K := IHs p s' H). clearbody K.
    omega.
    inversion H. subst.
    auto.
Qed.

Lemma break_length {A} {p} {s:list A} : forall {w} {s''},
  pair w s'' = List.break p s ->  le (length s'') (length s).
Proof.
  induction s.
  + simpl. intros w s'' h. inversion h. subst. simpl. auto.
  + simpl. intros w s'' h1.
    destruct (p a) eqn:Hp.
    ++ inversion h1. subst. simpl. auto.
    ++ destruct (List.break p s) as [ys zs] eqn:B.
       inversion h1. subst.
       pose (K := IHs ys zs eq_refl). clearbody K.
       auto.
Qed.


Program Fixpoint words (s : GHC.Base.String) { measure (length s) }
  : list GHC.Base.String :=
  match (GHC.List.dropWhile GHC.Unicode.isSpace s) with
    | nil => nil
    | s'  =>
     let 'pair w s'' := GHC.List.break GHC.Unicode.isSpace s' in
     cons w (words s'')
  end.
Next Obligation.
  destruct (List.dropWhile Unicode.isSpace s) eqn:D. contradiction.
  symmetry in D.
  pose (h0 := dropWhile_cons_prop _ _ _ _ D). clearbody h0.
  pose (h1 := dropWhile_cons_length _ _ _ _ D). clearbody h1.
  simpl in Heq_anonymous.
  rewrite h0 in Heq_anonymous.
  destruct (List.break Unicode.isSpace l) as [ys zs] eqn:B.
  inversion Heq_anonymous. subst.
  symmetry in B.
  pose (h2 := break_length B).
  omega.
Defined.

Program Fixpoint lines (s : GHC.Base.String) { measure (length s) }
  : list GHC.Base.String :=
  if (List.null s) then nil else
  let cons_ := fun '(pair h t) => cons h t in
  cons_ (let 'pair l s' := GHC.List.break
                             (fun arg_4__ =>
                                arg_4__ == newline) s in
         pair l (match s' with | nil => nil | cons _ s'' => lines s'' end)).
Next Obligation.
  pose (h0 := break_length Heq_anonymous). clearbody h0. simpl in h0.
  omega.
Defined.
