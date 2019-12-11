Require Import GHC.Base.
(* _==_ notation *)

Require Import ZArith.
Require Import ZArith.BinInt.
Import String.StringSyntax.

(* Hand-translated version of the prelude definitions
   of these functions. *)

Fixpoint take {a:Type} (n:Z) (xs:list a) : list a :=
  if (n <=? 0)%Z then nil
  else match xs with
       | nil => nil
       | cons y ys => cons y (take (n - 1) ys)
       end.

Fixpoint drop {a:Type} (n:Z) (xs:list a) : list a :=
  if (n <=? 0)%Z then xs
  else match xs with
       | nil => nil
       | cons y ys => drop (n - 1) ys
       end.

(* TODO: mark impossible case with default. *)

Fixpoint scanr {a b:Type} (f : a -> b -> b) (q0 : b)
        (xs: list a) :=
 match xs with
 | nil => (cons q0 nil)
 | cons y ys => match (scanr f q0 ys) with
               | cons q qs => cons (f y q) (cons q qs)
               | nil => nil  (* impossible case  *)
               end
end.


Definition splitAt {a : Type}(n:Z)(xs:list a) :=
  (take n xs, drop n xs).

Definition replicate {a:Type}(n:Z): a -> list a.
destruct (0 <=? n)%Z eqn:E; [|exact (fun _ => nil)].
apply Zle_bool_imp_le in E.
apply natlike_rec2 with (P := fun _ => a -> list a)(z := n).
- exact (fun _ => nil).
- intros n1 Pf rec x. exact (cons x (rec x)).
- exact E.
Defined.
