(*
(* Useful for development *)
Add LoadPath "../../../base".
Add LoadPath "../lib".
*)

Require Import GHC.Base. Import GHC.Base.Notations.
Require Import GHC.List.
Require Import Util.
Require Import Data.Traversable.
Require Import Data.Functor.Utils.

From Coq Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

(******************************************************************************)
(** Ltac **)

(* Gets function application heading the given term.
   
       term_head (f ...) = f
 *)
Ltac term_head t :=
  match t with
  | ?f _ => term_head f
  | _    => t
  end.

(* Functions like `red` (plus `simpl`) within a function application.  Ignores
   implicit arguments, but requires you to pass the function as an `@name`.
   
       red_within @outer
   
   will find

       skipped (outer (f 0 y))
   
   unfold `f`, and simplify the whole thing; for instance, if `f x y = x + y`,
   it'll become
 
       skipped (outer y)
   
   (as `0 + y` will be simplified).
 *)
Ltac red_within outer :=
  match goal with
  | |- context[outer ?inner] =>
    match type of outer with
    | forall {a}, _ => red_within (outer inner)
    | _             => let f := term_head inner
                       in rewrite /f /= || fail 2 "nothing to reduce"
    end
  | |- _ =>
    fail 1 "no occurrences of" outer
  end.

(******************************************************************************)
(** CSE **)

(* `zipMapAccumL f s xs1 xs2 = mapAccumL f s (zip xs1 xs2)` (see
   `zipMapAccumL_is_mapAccumL_zip`).

   We need this for use in `CSE.cseBind` so Coq can see that it's terminating.
   
   We need to make sure `f` is constant between all the recursive calls.  That
   plus the fact that this is a `fun` that wraps a `fix` means that when we call
   into this, the `fix` is inlined, and said `fix` recurses without doing
   anything higher-order, thus enabling the termination checker to see through
   things and prove `CSE.cseBind` terminating.
   
   The idea behind this was gleaned from Hugo Heberlin on coq-club in an email
   from 2010: <https://sympa.inria.fr/sympa/arc/coq-club/2010-09/msg00111.html>
 *)
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

Theorem zipMapAccumL_is_mapAccumL_zip {Acc X1 X2 Y}
                                      (f : Acc -> (X1 * X2) -> Acc * Y)
                                      (s : Acc)
                                      (xs1 : list X1)
                                      (xs2 : list X2) :
  zipMapAccumL f s xs1 xs2 = mapAccumL f s (zip xs1 xs2).
Proof.
  rewrite /mapAccumL; do 3 red_within @runStateL.
  elim: xs1 s xs2 => [|x1 xs1 IH] s [|x2 xs2] //=.
  case app_f: (f s (x1, x2)) => [s' y].
  rewrite IH.
  case: (foldr _ _ _) => [result] /=.
  by rewrite /flip /= app_f.
Qed.

(******************************************************************************)
(** CoreUtils **)

(* `all2Map p f g xs ys = all2 p (map f xs) (map g ys)` (see
   `all2Map_is_all2_map_map`).
   
   We need this for use in `CoreUtils.eqExpr` so Coq can see that it's
   terminating.  We also need to replace `unzip` with `map snd`, which we don't
   justify here.

   For more on the idea behind why this function works for termination, see
   `zipMapAccumL`.  *)
Definition all2Map {a b a' b'} (p : a -> b -> bool) (f : a' -> a) (g : b' -> b) : list a' -> list b' -> bool :=
  fix all2Map xs0 ys0 :=
    match xs0 , ys0 with
    | nil     , nil     => true
    | x :: xs , y :: ys => p (f x) (g y) && all2Map xs ys
    | _       , _       => false
    end.

Theorem all2Map_is_all2_map_map {a b a' b'} (p : a -> b -> bool) (f : a' -> a) (g : b' -> b) xs ys :
  all2Map p f g xs ys = all2 p (map f xs) (map g ys).
Proof.
  elim: xs ys => [|x xs IH] [|y ys] //=.
  by rewrite IH.
Qed.  
