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

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition all {a} : (a -> bool) -> list a -> bool :=
  fix all arg_61__ arg_62__
        := match arg_61__ , arg_62__ with
             | _ , nil => true
             | p , cons x xs => andb (p x) (all p xs)
           end.

Definition and : list bool -> bool :=
  fix and arg_72__
        := match arg_72__ with
             | nil => true
             | cons x xs => andb x (and xs)
           end.

Definition any {a} : (a -> bool) -> list a -> bool :=
  fix any arg_65__ arg_66__
        := match arg_65__ , arg_66__ with
             | _ , nil => false
             | p , cons x xs => orb (p x) (any p xs)
           end.

Definition break {a} : (a -> bool) -> list a -> list a * list a :=
  fix break arg_80__ arg_81__
        := match arg_80__ , arg_81__ with
             | _ , (nil as xs) => pair xs xs
             | p , (cons x xs' as xs) => let j_84__ :=
                                           match break p xs' with
                                             | pair ys zs => pair (cons x ys) zs
                                           end in
                                         if p x : bool
                                         then pair nil xs
                                         else j_84__
           end.

Definition concat {a} : list (list a) -> list a :=
  GHC.Base.foldr Coq.Init.Datatypes.app nil.

Definition constScanl {a} {b} : a -> b -> a :=
  GHC.Base.const.

Definition dropWhile {a} : (a -> bool) -> list a -> list a :=
  fix dropWhile arg_101__ arg_102__
        := match arg_101__ , arg_102__ with
             | _ , nil => nil
             | p , (cons x xs' as xs) => if p x : bool
                                         then dropWhile p xs'
                                         else xs
           end.

Definition elem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix elem arg_57__ arg_58__
        := match arg_57__ , arg_58__ with
             | _ , nil => false
             | x , cons y ys => orb (GHC.Base.op_zeze__ x y) (elem x ys)
           end.

Definition filter {a} : (a -> bool) -> list a -> list a :=
  fix filter arg_140__ arg_141__
        := match arg_140__ , arg_141__ with
             | _pred , nil => nil
             | pred , cons x xs => let j_142__ := filter pred xs in
                                   if pred x : bool
                                   then cons x (filter pred xs)
                                   else j_142__
           end.

Definition filterFB {a} {b} : (a -> b -> b) -> (a -> bool) -> a -> b -> b :=
  fun c p x r => if p x : bool then c x r else r.

Definition flipSeqScanl' {a} {b} : a -> b -> a :=
  fun a _b => a.

Definition flipSeqTake {a} : a -> GHC.Num.Int -> a :=
  fun x _n => x.

Definition foldr2 {a} {b} {c} : (a -> b -> c -> c) -> c -> list a -> list
                                b -> c :=
  fun k z =>
    let go :=
      fix go arg_42__ arg_43__
            := match arg_42__ , arg_43__ with
                 | nil , _ys => z
                 | _xs , nil => z
                 | cons x xs , cons y ys => k x y (go xs ys)
               end in
    go.

Definition foldr2_left {a} {b} {c} {d} : (a -> b -> c -> d) -> d -> a -> (list
                                         b -> c) -> list b -> d :=
  fun arg_35__ arg_36__ arg_37__ arg_38__ arg_39__ =>
    match arg_35__ , arg_36__ , arg_37__ , arg_38__ , arg_39__ with
      | _k , z , _x , _r , nil => z
      | k , _z , x , r , cons y ys => k x y (r ys)
    end.

Definition idLength : GHC.Num.Int -> GHC.Num.Int :=
  GHC.Base.id.

Definition lenAcc {a} : list a -> GHC.Num.Int -> GHC.Num.Int :=
  fix lenAcc arg_150__ arg_151__
        := match arg_150__ , arg_151__ with
             | nil , n => n
             | cons _ ys , n => lenAcc ys (GHC.Num.op_zp__ n (GHC.Num.fromInteger 1))
           end.

Definition length {a} : list a -> GHC.Num.Int :=
  fun xs => lenAcc xs (GHC.Num.fromInteger 0).

Definition lengthFB {x}
    : x -> (GHC.Num.Int -> GHC.Num.Int) -> GHC.Num.Int -> GHC.Num.Int :=
  fun arg_145__ arg_146__ =>
    match arg_145__ , arg_146__ with
      | _ , r => fun a => r (GHC.Num.op_zp__ a (GHC.Num.fromInteger 1))
    end.

Definition lookup {a} {b} `{(GHC.Base.Eq_ a)} : a -> list (a * b) -> option b :=
  fix lookup arg_48__ arg_49__
        := match arg_48__ , arg_49__ with
             | _key , nil => None
             | key , cons (pair x y) xys => let j_50__ := lookup key xys in
                                            if GHC.Base.op_zeze__ key x : bool
                                            then Some y
                                            else j_50__
           end.

Definition notElem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix notElem arg_53__ arg_54__
        := match arg_53__ , arg_54__ with
             | _ , nil => true
             | x , cons y ys => andb (GHC.Base.op_zsze__ x y) (notElem x ys)
           end.

Definition null {a} : list a -> bool :=
  fun arg_155__ => match arg_155__ with | nil => true | cons _ _ => false end.

Definition or : list bool -> bool :=
  fix or arg_69__
        := match arg_69__ with
             | nil => false
             | cons x xs => orb x (or xs)
           end.

Definition prel_list_str : GHC.Base.String :=
  GHC.Base.hs_string__ "Prelude.".

Definition negIndex {a} : a :=
  GHC.Base.op_zd__ GHC.Base.errorWithoutStackTrace (Coq.Init.Datatypes.app
                   prel_list_str (GHC.Base.hs_string__ "!!: negative index")).

Definition product {a} `{(GHC.Num.Num a)} : list a -> a :=
  GHC.Base.foldl GHC.Num.op_zt__ (GHC.Num.fromInteger 1).

Definition reverse {a} : list a -> list a :=
  fun l =>
    let rev :=
      fix rev arg_75__ arg_76__
            := match arg_75__ , arg_76__ with
                 | nil , a => a
                 | cons x xs , a => rev xs (cons x a)
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
  fun arg_133__ arg_134__ =>
    match arg_133__ , arg_134__ with
      | f , cons x xs => scanl f x xs
      | _ , nil => nil
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
    fun b g => GHC.Base.oneShot (fun x => match f x b with | b' => c b' (g b') end).

Definition scanrFB {a} {b} {c} : (a -> b -> b) -> (b -> c -> c) -> a -> b *
                                 c -> b * c :=
  fun f c =>
    fun arg_111__ arg_112__ =>
      match arg_111__ , arg_112__ with
        | x , pair r est => pair (f x r) (c r est)
      end.

Definition span {a} : (a -> bool) -> list a -> list a * list a :=
  fix span arg_87__ arg_88__
        := match arg_87__ , arg_88__ with
             | _ , (nil as xs) => pair xs xs
             | p , (cons x xs' as xs) => let j_90__ := pair nil xs in
                                         if p x : bool
                                         then match span p xs' with
                                                | pair ys zs => pair (cons x ys) zs
                                              end
                                         else j_90__
           end.

Definition strictUncurryScanr {a} {b} {c} : (a -> b -> c) -> a * b -> c :=
  fun f pair_ => match pair_ with | pair x y => f x y end.

Definition sum {a} `{(GHC.Num.Num a)} : list a -> a :=
  GHC.Base.foldl GHC.Num.op_zp__ (GHC.Num.fromInteger 0).

Definition takeFB {a} {b}
    : (a -> b -> b) -> b -> a -> (GHC.Num.Int -> b) -> GHC.Num.Int -> b :=
  fun c n x xs =>
    fun m =>
      let j_96__ := c x (xs (GHC.Num.op_zm__ m (GHC.Num.fromInteger 1))) in
      match m with
        | num_94__ => if (num_94__ == GHC.Num.fromInteger 1) : bool
                      then c x n
                      else j_96__
      end.

Definition takeWhile {a} : (a -> bool) -> list a -> list a :=
  fix takeWhile arg_107__ arg_108__
        := match arg_107__ , arg_108__ with
             | _ , nil => nil
             | p , cons x xs => if p x : bool
                                then cons x (takeWhile p xs)
                                else nil
           end.

Definition takeWhileFB {a} {b}
    : (a -> bool) -> (a -> b -> b) -> b -> a -> b -> b :=
  fun p c n => fun x r => if p x : bool then c x r else n.

Definition uncons {a} : list a -> option (a * list a) :=
  fun arg_157__ =>
    match arg_157__ with
      | nil => None
      | cons x xs => Some (pair x xs)
    end.

Definition unzip {a} {b} : list (a * b) -> list a * list b :=
  GHC.Base.foldr (fun arg_6__ arg_7__ =>
                   match arg_6__ , arg_7__ with
                     | pair a b , pair as_ bs => pair (cons a as_) (cons b bs)
                   end) (pair nil nil).

Definition unzip3 {a} {b} {c} : list (a * b * c) -> list a * list b * list c :=
  GHC.Base.foldr (fun arg_1__ arg_2__ =>
                   match arg_1__ , arg_2__ with
                     | pair (pair a b) c , pair (pair as_ bs) cs => pair (pair (cons a as_) (cons b
                                                                                                  bs)) (cons c cs)
                   end) (pair (pair nil nil) nil).

Definition zip {a} {b} : list a -> list b -> list (a * b) :=
  fix zip arg_31__ arg_32__
        := match arg_31__ , arg_32__ with
             | nil , _bs => nil
             | _as , nil => nil
             | cons a as_ , cons b bs => cons (pair a b) (zip as_ bs)
           end.

Definition zip3 {a} {b} {c} : list a -> list b -> list c -> list (a * b * c) :=
  fix zip3 arg_24__ arg_25__ arg_26__
        := match arg_24__ , arg_25__ , arg_26__ with
             | cons a as_ , cons b bs , cons c cs => cons (pair (pair a b) c) (zip3 as_ bs
                                                          cs)
             | _ , _ , _ => nil
           end.

Definition zipFB {a} {b} {c} {d} : (a * b -> c -> d) -> a -> b -> c -> d :=
  fun c => fun x y r => c (pair x y) r.

Definition zipWith {a} {b} {c} : (a -> b -> c) -> list a -> list b -> list c :=
  fix zipWith arg_19__ arg_20__ arg_21__
        := match arg_19__ , arg_20__ , arg_21__ with
             | _f , nil , _bs => nil
             | _f , _as , nil => nil
             | f , cons a as_ , cons b bs => cons (f a b) (zipWith f as_ bs)
           end.

Definition zipWith3 {a} {b} {c} {d} : (a -> b -> c -> d) -> list a -> list
                                      b -> list c -> list d :=
  fix zipWith3 arg_11__ arg_12__ arg_13__ arg_14__
        := match arg_11__ , arg_12__ , arg_13__ , arg_14__ with
             | z , cons a as_ , cons b bs , cons c cs => cons (z a b c) (zipWith3 z as_ bs
                                                              cs)
             | _ , _ , _ , _ => nil
           end.

Definition zipWithFB {a} {b} {c} {d} {e}
    : (a -> b -> c) -> (d -> e -> a) -> d -> e -> b -> c :=
  fun c f => fun x y r => c (f x y) r.

(* Unbound variables:
     * == Coq.Init.Datatypes.app GHC.Base.Eq_ GHC.Base.String GHC.Base.const
     GHC.Base.errorWithoutStackTrace GHC.Base.foldl GHC.Base.foldr GHC.Base.id
     GHC.Base.oneShot GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zsze__
     GHC.Num.Int GHC.Num.Num GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ None
     Some andb bool cons false list nil option orb pair true
*)
