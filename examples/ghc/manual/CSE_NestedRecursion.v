Require Import GHC.Base. Import GHC.Base.Notations.
Require Import GHC.List.
Require Import Data.Traversable.
Require Import Data.Functor.Utils.

From Coq Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

(* We need to make sure `f` is constant between all the recursive calls.  That
   plus the fact that this is a `fun` that wraps a `fix` means that when we call
   into this, the `fix` is inlined, and said `fix` recurses without doing
   anything higher-order, thus enabling the termination checker to see through
   things and prove `CSE.cseBind` terminating.
   
   The idea behind this was gleaned from Hugo Heberlin on coq-club in an email
   from 2010:
   <https://sympa.inria.fr/sympa/arc/coq-club/2010-09/msg00111.html> *)
Definition zipMapAccumL {acc x1 x2 y}
                        (f : acc -> (x1 * x2) -> acc * y)
                          : acc -> list x1 -> list x2 -> acc * list y :=
  fix go (s : acc) (xs1 : list x1) (xs2 : list x2) {struct xs1} : acc * list y :=
    match xs1 , xs2 with
    | nil        , _          => (s, nil)
    | _          , nil        => (s, nil)
    | x1 :: xs1' , x2 :: xs2' => let: (s',  y)  := f s (x1,x2) in
                                 let: (s'', ys) := go s' xs1' xs2' in
                                 (s'', y :: ys)
    end%list.

Ltac term_head t :=
  match t with
  | ?f _ => term_head f
  | _    => t
  end.

Theorem zipMapAccumL_is_mapAccumL_zip {Acc X1 X2 Y}
                                      (f : Acc -> (X1 * X2) -> Acc * Y)
                                      (s : Acc)
                                      (xs1 : list X1)
                                      (xs2 : list X2) :
  zipMapAccumL f s xs1 xs2 = mapAccumL f s (zip xs1 xs2).
Proof.
  rewrite /mapAccumL.
  do 3 match goal with
       | |- context[runStateL ?app] => let f := term_head app in rewrite /f /=
       end.
  elim: xs1 s xs2 => [|x1 xs1 IH] s [|x2 xs2] //=.
  case app_f: (f s (x1, x2)) => [s' y].
  rewrite IH.
  case: (foldr _ _ _) => [result] /=.
  by rewrite /flip /= app_f.
Qed.
