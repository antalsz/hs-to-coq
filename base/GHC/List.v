(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.
(* _==_ notation *)

Require Import ZArith.
Require Import ZArith.BinInt.

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

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition all {a} : (a -> bool) -> list a -> bool :=
  fix all arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => true
           | p, cons x xs => andb (p x) (all p xs)
           end.

Definition and : list bool -> bool :=
  fix and arg_0__
        := match arg_0__ with
           | nil => true
           | cons x xs => andb x (and xs)
           end.

Definition any {a} : (a -> bool) -> list a -> bool :=
  fix any arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => false
           | p, cons x xs => orb (p x) (any p xs)
           end.

Definition break {a} : (a -> bool) -> list a -> (list a * list a)%type :=
  fix break arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, (nil as xs) => pair xs xs
           | p, (cons x xs' as xs) =>
               if p x : bool then pair nil xs else
               let 'pair ys zs := break p xs' in
               pair (cons x ys) zs
           end.

Definition concat {a} : list (list a) -> list a :=
  GHC.Base.foldr Coq.Init.Datatypes.app nil.

Definition constScanl {a} {b} : a -> b -> a :=
  GHC.Base.const.

Definition dropWhile {a} : (a -> bool) -> list a -> list a :=
  fix dropWhile arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => nil
           | p, (cons x xs' as xs) => if p x : bool then dropWhile p xs' else xs
           end.

Definition elem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix elem arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => false
           | x, cons y ys => orb (x GHC.Base.== y) (elem x ys)
           end.

Definition filter {a} : (a -> bool) -> list a -> list a :=
  fix filter arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _pred, nil => nil
           | pred, cons x xs =>
               if pred x : bool then cons x (filter pred xs) else
               filter pred xs
           end.

Definition filterFB {a} {b} : (a -> b -> b) -> (a -> bool) -> a -> b -> b :=
  fun c p x r => if p x : bool then c x r else r.

Definition flipSeqScanl' {a} {b} : a -> b -> a :=
  fun a _b => a.

Definition flipSeqTake {a} : a -> GHC.Num.Int -> a :=
  fun x _n => x.

Definition foldr2 {a} {b} {c}
   : (a -> b -> c -> c) -> c -> list a -> list b -> c :=
  fun k z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | nil, _ys => z
                 | _xs, nil => z
                 | cons x xs, cons y ys => k x y (go xs ys)
                 end in
    go.

Definition foldr2_left {a} {b} {c} {d}
   : (a -> b -> c -> d) -> d -> a -> (list b -> c) -> list b -> d :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | _k, z, _x, _r, nil => z
    | k, _z, x, r, cons y ys => k x y (r ys)
    end.

Definition idLength : GHC.Num.Int -> GHC.Num.Int :=
  GHC.Base.id.

Definition lenAcc {a} : list a -> GHC.Num.Int -> GHC.Num.Int :=
  fix lenAcc arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, n => n
           | cons _ ys, n => lenAcc ys (n GHC.Num.+ #1)
           end.

Definition length {a} : list a -> GHC.Num.Int :=
  fun xs => lenAcc xs #0.

Definition lengthFB {x}
   : x -> (GHC.Num.Int -> GHC.Num.Int) -> GHC.Num.Int -> GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, r => fun a => r (a GHC.Num.+ #1)
    end.

Definition lookup {a} {b} `{(GHC.Base.Eq_ a)}
   : a -> list (a * b)%type -> option b :=
  fix lookup arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _key, nil => None
           | key, cons (pair x y) xys =>
               if key GHC.Base.== x : bool then Some y else
               lookup key xys
           end.

Definition notElem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix notElem arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => true
           | x, cons y ys => andb (x GHC.Base./= y) (notElem x ys)
           end.

Definition null {a} : list a -> bool :=
  fun arg_0__ => match arg_0__ with | nil => true | cons _ _ => false end.

Definition or : list bool -> bool :=
  fix or arg_0__
        := match arg_0__ with
           | nil => false
           | cons x xs => orb x (or xs)
           end.

Definition prel_list_str : GHC.Base.String :=
  GHC.Base.hs_string__ "Prelude.".

Definition product {a} `{(GHC.Num.Num a)} : list a -> a :=
  GHC.Base.foldl _GHC.Num.*_ #1.

Definition reverse {a} : list a -> list a :=
  fun l =>
    let fix rev arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | nil, a => a
                 | cons x xs, a => rev xs (cons x a)
                 end in
    rev l nil.

Definition scanl {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo f q ls
          := cons q (match ls with
                   | nil => nil
                   | cons x xs => scanlGo f (f q x) xs
                   end) in
  scanlGo.

Definition scanl1 {a} : (a -> a -> a) -> list a -> list a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, cons x xs => scanl f x xs
    | _, nil => nil
    end.

Definition scanl' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo' f q ls
          := cons q (match ls with
                   | nil => nil
                   | cons x xs => scanlGo' f (f q x) xs
                   end) in
  scanlGo'.

Definition scanlFB {b} {a} {c}
   : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun f c =>
    fun b g => GHC.Base.oneShot (fun x => let b' := f x b in c b' (g b')).

Definition scanlFB' {b} {a} {c}
   : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun f c =>
    fun b g => GHC.Base.oneShot (fun x => let 'b' := f x b in c b' (g b')).

Definition scanrFB {a} {b} {c}
   : (a -> b -> b) -> (b -> c -> c) -> a -> (b * c)%type -> (b * c)%type :=
  fun f c =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | x, pair r est => pair (f x r) (c r est)
      end.

Definition span {a} : (a -> bool) -> list a -> (list a * list a)%type :=
  fix span arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, (nil as xs) => pair xs xs
           | p, (cons x xs' as xs) =>
               if p x : bool then let 'pair ys zs := span p xs' in pair (cons x ys) zs else
               pair nil xs
           end.

Definition strictUncurryScanr {a} {b} {c}
   : (a -> b -> c) -> (a * b)%type -> c :=
  fun f pair_ => let 'pair x y := pair_ in f x y.

Definition sum {a} `{(GHC.Num.Num a)} : list a -> a :=
  GHC.Base.foldl _GHC.Num.+_ #0.

Definition takeFB {a} {b}
   : (a -> b -> b) -> b -> a -> (GHC.Num.Int -> b) -> GHC.Num.Int -> b :=
  fun c n x xs =>
    fun m =>
      let 'num_0__ := m in
      if num_0__ GHC.Base.== #1 : bool then c x n else
      c x (xs (m GHC.Num.- #1)).

Definition takeWhile {a} : (a -> bool) -> list a -> list a :=
  fix takeWhile arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => nil
           | p, cons x xs => if p x : bool then cons x (takeWhile p xs) else nil
           end.

Definition takeWhileFB {a} {b}
   : (a -> bool) -> (a -> b -> b) -> b -> a -> b -> b :=
  fun p c n => fun x r => if p x : bool then c x r else n.

Definition uncons {a} : list a -> option (a * list a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => None
    | cons x xs => Some (pair x xs)
    end.

Definition unzip {a} {b} : list (a * b)%type -> (list a * list b)%type :=
  GHC.Base.foldr (fun arg_0__ arg_1__ =>
                    match arg_0__, arg_1__ with
                    | pair a b, pair as_ bs => pair (cons a as_) (cons b bs)
                    end) (pair nil nil).

Definition unzip3 {a} {b} {c}
   : list (a * b * c)%type -> (list a * list b * list c)%type :=
  GHC.Base.foldr (fun arg_0__ arg_1__ =>
                    match arg_0__, arg_1__ with
                    | pair (pair a b) c, pair (pair as_ bs) cs =>
                        pair (pair (cons a as_) (cons b bs)) (cons c cs)
                    end) (pair (pair nil nil) nil).

Definition zip {a} {b} : list a -> list b -> list (a * b)%type :=
  fix zip arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, _bs => nil
           | _as, nil => nil
           | cons a as_, cons b bs => cons (pair a b) (zip as_ bs)
           end.

Definition zip3 {a} {b} {c}
   : list a -> list b -> list c -> list (a * b * c)%type :=
  fix zip3 arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | cons a as_, cons b bs, cons c cs => cons (pair (pair a b) c) (zip3 as_ bs cs)
           | _, _, _ => nil
           end.

Definition zipFB {a} {b} {c} {d}
   : ((a * b)%type -> c -> d) -> a -> b -> c -> d :=
  fun c => fun x y r => c (pair x y) r.

Definition zipWith {a} {b} {c} : (a -> b -> c) -> list a -> list b -> list c :=
  fix zipWith arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _f, nil, _bs => nil
           | _f, _as, nil => nil
           | f, cons a as_, cons b bs => cons (f a b) (zipWith f as_ bs)
           end.

Definition zipWith3 {a} {b} {c} {d}
   : (a -> b -> c -> d) -> list a -> list b -> list c -> list d :=
  fix zipWith3 arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | z, cons a as_, cons b bs, cons c cs => cons (z a b c) (zipWith3 z as_ bs cs)
           | _, _, _, _ => nil
           end.

Definition zipWithFB {a} {b} {c} {d} {e}
   : (a -> b -> c) -> (d -> e -> a) -> d -> e -> b -> c :=
  fun c f => fun x y r => c (f x y) r.

(* Unbound variables:
     None Some andb bool cons false list nil op_zt__ option orb pair true
     Coq.Init.Datatypes.app GHC.Base.Eq_ GHC.Base.String GHC.Base.const
     GHC.Base.foldl GHC.Base.foldr GHC.Base.id GHC.Base.oneShot GHC.Base.op_zeze__
     GHC.Base.op_zsze__ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Num.op_zt__
*)
