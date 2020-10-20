(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require String.
Export String.StringSyntax.

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
Require Import GHC.Base.
Require GHC.Err.
Require GHC.Num.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition prel_list_str : String :=
  GHC.Base.hs_string__ "Prelude.".

Definition errorEmptyList {a} `{_ : GHC.Err.Default a} : String -> a :=
  fun fun_ =>
    GHC.Err.errorWithoutStackTrace (Coq.Init.Datatypes.app prel_list_str
                                                           (Coq.Init.Datatypes.app fun_ (GHC.Base.hs_string__
                                                                                    ": empty list"))).

Definition badHead {a} `{_ : GHC.Err.Default a} : a :=
  errorEmptyList (GHC.Base.hs_string__ "head").

Definition head {a} `{_ : GHC.Err.Default a} : list a -> a :=
  fun arg_0__ => match arg_0__ with | cons x _ => x | nil => badHead end.

Definition uncons {a} : list a -> option (a * list a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => None
    | cons x xs => Some (pair x xs)
    end.

Definition tail {a} `{_ : GHC.Err.Default a} : list a -> list a :=
  fun arg_0__ =>
    match arg_0__ with
    | cons _ xs => xs
    | nil => errorEmptyList (GHC.Base.hs_string__ "tail")
    end.

(* Skipping definition `GHC.Base.foldl' *)

Definition lastError {a} `{_ : GHC.Err.Default a} : a :=
  errorEmptyList (GHC.Base.hs_string__ "last").

Definition last {a} `{_ : GHC.Err.Default a} : list a -> a :=
  fun xs =>
    foldl (fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, x => x end)
    lastError xs.

Definition init {a} `{_ : GHC.Err.Default a} : list a -> list a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => errorEmptyList (GHC.Base.hs_string__ "init")
    | cons x xs =>
        let fix init' arg_2__ arg_3__
                  := match arg_2__, arg_3__ with
                     | _, nil => nil
                     | y, cons z zs => cons y (init' z zs)
                     end in
        init' x xs
    end.

Definition null {a} : list a -> bool :=
  fun arg_0__ => match arg_0__ with | nil => true | cons _ _ => false end.

Fixpoint lenAcc {a} (arg_0__ : list a) (arg_1__ : GHC.Num.Int) : GHC.Num.Int
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

Definition idLength : GHC.Num.Int -> GHC.Num.Int :=
  id.

Fixpoint filter {a} (arg_0__ : (a -> bool)) (arg_1__ : list a) : list a
           := match arg_0__, arg_1__ with
              | _pred, nil => nil
              | pred, cons x xs =>
                  if pred x : bool then cons x (filter pred xs) else
                  filter pred xs
              end.

Definition filterFB {a} {b} : (a -> b -> b) -> (a -> bool) -> a -> b -> b :=
  fun c p x r => if p x : bool then c x r else r.

(* Skipping definition `GHC.Base.foldl'' *)

Definition foldl1 {a} `{_ : GHC.Err.Default a} : (a -> a -> a) -> list a -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, cons x xs => foldl f x xs
    | _, nil => errorEmptyList (GHC.Base.hs_string__ "foldl1")
    end.

Definition foldl1' {a} `{_ : GHC.Err.Default a}
   : (a -> a -> a) -> list a -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, cons x xs => foldl' f x xs
    | _, nil => errorEmptyList (GHC.Base.hs_string__ "foldl1'")
    end.

Definition sum {a} `{(GHC.Num.Num a)} : list a -> a :=
  foldl _GHC.Num.+_ #0.

Definition product {a} `{(GHC.Num.Num a)} : list a -> a :=
  foldl _GHC.Num.*_ #1.

Definition scanl {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo (f : (b -> a -> b)) (q : b) (ls : list a) : list b
          := cons q (match ls with
                   | nil => nil
                   | cons x xs => scanlGo f (f q x) xs
                   end) in
  scanlGo.

Definition scanlFB {b} {a} {c}
   : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun f c => fun b g => (fun x => let b' := f x b in c b' (g b')).

Definition constScanl {a} {b} : a -> b -> a :=
  const.

Definition scanl1 {a} : (a -> a -> a) -> list a -> list a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, cons x xs => scanl f x xs
    | _, nil => nil
    end.

Definition scanl' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo' (f : (b -> a -> b)) (q : b) (ls : list a) : list b
          := cons q (match ls with
                   | nil => nil
                   | cons x xs => scanlGo' f (f q x) xs
                   end) in
  scanlGo'.

Definition scanlFB' {b} {a} {c}
   : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun f c => fun b g => (fun x => let b' := f x b in c b' (g b')).

Definition flipSeqScanl' {a} {b} : a -> b -> a :=
  fun a _b => a.

Definition foldr1 {a} `{_ : GHC.Err.Default a} : (a -> a -> a) -> list a -> a :=
  fun f =>
    let fix go arg_0__
              := match arg_0__ with
                 | cons x nil => x
                 | cons x xs => f x (go xs)
                 | nil => errorEmptyList (GHC.Base.hs_string__ "foldr1")
                 end in
    go.

(* Skipping definition `GHC.List.scanr' *)

Definition strictUncurryScanr {a} {b} {c}
   : (a -> b -> c) -> (a * b)%type -> c :=
  fun f pair_ => let 'pair x y := pair_ in f x y.

Definition scanrFB {a} {b} {c}
   : (a -> b -> b) -> (b -> c -> c) -> a -> (b * c)%type -> (b * c)%type :=
  fun f c =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | x, pair r est => pair (f x r) (c r est)
      end.

Fixpoint scanr1 {a} `{_ : GHC.Err.Default a} (arg_0__ : a -> a -> a) (arg_1__
                  : list a) : list a
           := match arg_0__, arg_1__ with
              | _, nil => nil
              | _, cons x nil => cons x nil
              | f, cons x xs =>
                  match scanr1 f xs with
                  | (cons q _ as qs) => cons (f x q) qs
                  | _ => GHC.Err.patternFailure
                  end
              end.

Definition maximum {a} `{_ : GHC.Err.Default a} {_ : Eq_ a} {_ : Ord a}
   : list a -> a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => errorEmptyList (GHC.Base.hs_string__ "maximum")
    | xs => foldl1 max xs
    end.

Definition minimum {a} `{_ : GHC.Err.Default a} {_ : Eq_ a} {_ : Ord a}
   : list a -> a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => errorEmptyList (GHC.Base.hs_string__ "minimum")
    | xs => foldl1 min xs
    end.

(* Skipping definition `GHC.List.iterate' *)

(* Skipping definition `GHC.List.iterateFB' *)

(* Skipping definition `GHC.List.iterate'' *)

(* Skipping definition `GHC.List.iterate'FB' *)

(* Skipping definition `GHC.List.repeat' *)

(* Skipping definition `GHC.List.repeatFB' *)

(* Skipping definition `GHC.List.replicate' *)

(* Skipping definition `GHC.List.cycle' *)

Fixpoint takeWhile {a} (arg_0__ : (a -> bool)) (arg_1__ : list a) : list a
           := match arg_0__, arg_1__ with
              | _, nil => nil
              | p, cons x xs => if p x : bool then cons x (takeWhile p xs) else nil
              end.

Definition takeWhileFB {a} {b}
   : (a -> bool) -> (a -> b -> b) -> b -> a -> b -> b :=
  fun p c n => fun x r => if p x : bool then c x r else n.

Fixpoint dropWhile {a} (arg_0__ : (a -> bool)) (arg_1__ : list a) : list a
           := match arg_0__, arg_1__ with
              | _, nil => nil
              | p, (cons x xs' as xs) => if p x : bool then dropWhile p xs' else xs
              end.

(* Skipping definition `GHC.List.take' *)

(* Skipping definition `GHC.List.unsafeTake' *)

Definition flipSeqTake {a} : a -> GHC.Num.Int -> a :=
  fun x _n => x.

Definition takeFB {a} {b}
   : (a -> b -> b) -> b -> a -> (GHC.Num.Int -> b) -> GHC.Num.Int -> b :=
  fun c n x xs =>
    fun m =>
      let 'num_0__ := m in
      if num_0__ == #1 : bool then c x n else
      c x (xs (m GHC.Num.- #1)).

(* Skipping definition `GHC.List.drop' *)

(* Skipping definition `GHC.List.splitAt' *)

Fixpoint span {a} (arg_0__ : (a -> bool)) (arg_1__ : list a) : (list a *
                                                                list a)%type
           := match arg_0__, arg_1__ with
              | _, (nil as xs) => pair xs xs
              | p, (cons x xs' as xs) =>
                  if p x : bool then let 'pair ys zs := span p xs' in pair (cons x ys) zs else
                  pair nil xs
              end.

Fixpoint break {a} (arg_0__ : (a -> bool)) (arg_1__ : list a) : (list a *
                                                                 list a)%type
           := match arg_0__, arg_1__ with
              | _, (nil as xs) => pair xs xs
              | p, (cons x xs' as xs) =>
                  if p x : bool then pair nil xs else
                  let 'pair ys zs := break p xs' in
                  pair (cons x ys) zs
              end.

Definition reverse {a} : list a -> list a :=
  fun l =>
    let fix rev arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | nil, a => a
                 | cons x xs, a => rev xs (cons x a)
                 end in
    rev l nil.

Fixpoint and (arg_0__ : list bool) : bool
           := match arg_0__ with
              | nil => true
              | cons x xs => andb x (and xs)
              end.

Fixpoint or (arg_0__ : list bool) : bool
           := match arg_0__ with
              | nil => false
              | cons x xs => orb x (or xs)
              end.

Fixpoint any {a} (arg_0__ : (a -> bool)) (arg_1__ : list a) : bool
           := match arg_0__, arg_1__ with
              | _, nil => false
              | p, cons x xs => orb (p x) (any p xs)
              end.

Fixpoint all {a} (arg_0__ : (a -> bool)) (arg_1__ : list a) : bool
           := match arg_0__, arg_1__ with
              | _, nil => true
              | p, cons x xs => andb (p x) (all p xs)
              end.

Fixpoint elem {a} `{(Eq_ a)} (arg_0__ : a) (arg_1__ : list a) : bool
           := match arg_0__, arg_1__ with
              | _, nil => false
              | x, cons y ys => orb (x == y) (elem x ys)
              end.

Fixpoint notElem {a} `{(Eq_ a)} (arg_0__ : a) (arg_1__ : list a) : bool
           := match arg_0__, arg_1__ with
              | _, nil => true
              | x, cons y ys => andb (x /= y) (notElem x ys)
              end.

Fixpoint lookup {a} {b} `{(Eq_ a)} (arg_0__ : a) (arg_1__ : list (a * b)%type)
           : option b
           := match arg_0__, arg_1__ with
              | _key, nil => None
              | key, cons (pair x y) xys => if key == x : bool then Some y else lookup key xys
              end.

(* Skipping definition `Coq.Lists.List.flat_map' *)

Definition concat {a} : list (list a) -> list a :=
  foldr Coq.Init.Datatypes.app nil.

Definition tooLarge {a} `{_ : GHC.Err.Default a} : GHC.Num.Int -> a :=
  fun arg_0__ =>
    GHC.Err.errorWithoutStackTrace (Coq.Init.Datatypes.app prel_list_str
                                                           (GHC.Base.hs_string__ "!!: index too large")).

Definition negIndex {a} `{_ : GHC.Err.Default a} : a :=
  GHC.Err.errorWithoutStackTrace (Coq.Init.Datatypes.app prel_list_str
                                                         (GHC.Base.hs_string__ "!!: negative index")).

Definition op_znzn__ {a} `{_ : GHC.Err.Default a}
   : list a -> GHC.Num.Int -> a :=
  fun xs n =>
    if n < #0 : bool then negIndex else
    foldr (fun x r k =>
             let 'num_0__ := k in
             if num_0__ == #0 : bool then x else
             r (k GHC.Num.- #1)) tooLarge xs n.

Notation "'_!!_'" := (op_znzn__).

Infix "!!" := (_!!_) (at level 99).

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

Fixpoint zip {a} {b} (arg_0__ : list a) (arg_1__ : list b) : list (a * b)%type
           := match arg_0__, arg_1__ with
              | nil, _bs => nil
              | _as, nil => nil
              | cons a as_, cons b bs => cons (pair a b) (zip as_ bs)
              end.

Definition zipFB {a} {b} {c} {d}
   : ((a * b)%type -> c -> d) -> a -> b -> c -> d :=
  fun c => fun x y r => c (pair x y) r.

Fixpoint zip3 {a} {b} {c} (arg_0__ : list a) (arg_1__ : list b) (arg_2__
                : list c) : list (a * b * c)%type
           := match arg_0__, arg_1__, arg_2__ with
              | cons a as_, cons b bs, cons c cs => cons (pair (pair a b) c) (zip3 as_ bs cs)
              | _, _, _ => nil
              end.

Definition zipWith {a} {b} {c} : (a -> b -> c) -> list a -> list b -> list c :=
  fun f =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | nil, _ => nil
                 | _, nil => nil
                 | cons x xs, cons y ys => cons (f x y) (go xs ys)
                 end in
    go.

Definition zipWithFB {a} {b} {c} {d} {e}
   : (a -> b -> c) -> (d -> e -> a) -> d -> e -> b -> c :=
  fun c f => fun x y r => c (f x y) r.

Definition zipWith3 {a} {b} {c} {d}
   : (a -> b -> c -> d) -> list a -> list b -> list c -> list d :=
  fun z =>
    let fix go arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | cons a as_, cons b bs, cons c cs => cons (z a b c) (go as_ bs cs)
                 | _, _, _ => nil
                 end in
    go.

Definition unzip {a} {b} : list (a * b)%type -> (list a * list b)%type :=
  foldr (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | pair a b, pair as_ bs => pair (cons a as_) (cons b bs)
           end) (pair nil nil).

Definition unzip3 {a} {b} {c}
   : list (a * b * c)%type -> (list a * list b * list c)%type :=
  foldr (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | pair (pair a b) c, pair (pair as_ bs) cs =>
               pair (pair (cons a as_) (cons b bs)) (cons c cs)
           end) (pair (pair nil nil) nil).

Module Notations.
Notation "'_GHC.List.!!_'" := (op_znzn__).
Infix "GHC.List.!!" := (_!!_) (at level 99).
End Notations.

(* External variables:
     Eq_ None Ord Some String andb bool cons const false foldl foldl' foldr id list
     max min nil op_zeze__ op_zl__ op_zsze__ op_zt__ option orb pair true
     Coq.Init.Datatypes.app GHC.Err.Default GHC.Err.errorWithoutStackTrace
     GHC.Err.patternFailure GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__
*)
