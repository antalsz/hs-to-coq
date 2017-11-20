(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  fix all arg_77__ arg_78__
        := match arg_77__ , arg_78__ with
             | _ , nil => true
             | p , cons x xs => andb (p x) (all p xs)
           end.

Definition and : list bool -> bool :=
  fix and arg_88__
        := match arg_88__ with
             | nil => true
             | cons x xs => andb x (and xs)
           end.

Definition any {a} : (a -> bool) -> list a -> bool :=
  fix any arg_81__ arg_82__
        := match arg_81__ , arg_82__ with
             | _ , nil => false
             | p , cons x xs => orb (p x) (any p xs)
           end.

Definition break {a} : (a -> bool) -> list a -> list a * list a :=
  fix break arg_98__ arg_99__
        := match arg_98__ , arg_99__ with
             | _ , (nil as xs) => pair xs xs
             | p , (cons x xs' as xs) => let j_102__ :=
                                           match break p xs' with
                                             | pair ys zs => pair (cons x ys) zs
                                           end in
                                         if p x : bool
                                         then pair nil xs
                                         else j_102__
           end.

Definition concat {a} : list (list a) -> list a :=
  GHC.Base.foldr Coq.Init.Datatypes.app nil.

Definition constScanl {a} {b} : a -> b -> a :=
  GHC.Base.const.

Definition dropWhile {a} : (a -> bool) -> list a -> list a :=
  fix dropWhile arg_129__ arg_130__
        := match arg_129__ , arg_130__ with
             | _ , nil => nil
             | p , (cons x xs' as xs) => if p x : bool
                                         then dropWhile p xs'
                                         else xs
           end.

Definition elem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix elem arg_73__ arg_74__
        := match arg_73__ , arg_74__ with
             | _ , nil => false
             | x , cons y ys => orb (GHC.Base.op_zeze__ x y) (elem x ys)
           end.

Definition filter {a} : (a -> bool) -> list a -> list a :=
  fix filter arg_213__ arg_214__
        := match arg_213__ , arg_214__ with
             | _pred , nil => nil
             | pred , cons x xs => let j_215__ := filter pred xs in
                                   if pred x : bool
                                   then cons x (filter pred xs)
                                   else j_215__
           end.

Definition filterFB {a} {b} : (a -> b -> b) -> (a -> bool) -> a -> b -> b :=
  fun arg_207__ arg_208__ arg_209__ arg_210__ =>
    match arg_207__ , arg_208__ , arg_209__ , arg_210__ with
      | c , p , x , r => if p x : bool
                         then c x r
                         else r
    end.

Definition flipSeqScanl' {a} {b} : a -> b -> a :=
  fun arg_160__ arg_161__ => match arg_160__ , arg_161__ with | a , _b => a end.

Definition flipSeqTake {a} : a -> GHC.Num.Int -> a :=
  fun arg_126__ arg_127__ => match arg_126__ , arg_127__ with | x , _n => x end.

Definition foldr2 {a} {b} {c} : (a -> b -> c -> c) -> c -> list a -> list
                                b -> c :=
  fun arg_55__ arg_56__ =>
    match arg_55__ , arg_56__ with
      | k , z => let go :=
                   fix go arg_57__ arg_58__
                         := match arg_57__ , arg_58__ with
                              | nil , _ys => z
                              | _xs , nil => z
                              | cons x xs , cons y ys => k x y (go xs ys)
                            end in
                 go
    end.

Definition foldr2_left {a} {b} {c} {d} : (a -> b -> c -> d) -> d -> a -> (list
                                         b -> c) -> list b -> d :=
  fun arg_48__ arg_49__ arg_50__ arg_51__ arg_52__ =>
    match arg_48__ , arg_49__ , arg_50__ , arg_51__ , arg_52__ with
      | _k , z , _x , _r , nil => z
      | k , _z , x , r , cons y ys => k x y (r ys)
    end.

Definition idLength : GHC.Num.Int -> GHC.Num.Int :=
  GHC.Base.id.

Definition lenAcc {a} : list a -> GHC.Num.Int -> GHC.Num.Int :=
  fix lenAcc arg_225__ arg_226__
        := match arg_225__ , arg_226__ with
             | nil , n => n
             | cons _ ys , n => lenAcc ys (GHC.Num.op_zp__ n (GHC.Num.fromInteger 1))
           end.

Definition length {a} : list a -> GHC.Num.Int :=
  fun arg_229__ =>
    match arg_229__ with
      | xs => lenAcc xs (GHC.Num.fromInteger 0)
    end.

Definition lengthFB {x}
    : x -> (GHC.Num.Int -> GHC.Num.Int) -> GHC.Num.Int -> GHC.Num.Int :=
  fun arg_218__ arg_219__ =>
    match arg_218__ , arg_219__ with
      | _ , r => fun arg_220__ =>
                   match arg_220__ with
                     | a => r (GHC.Num.op_zp__ a (GHC.Num.fromInteger 1))
                   end
    end.

Definition lookup {a} {b} `{(GHC.Base.Eq_ a)} : a -> list (a * b) -> option b :=
  fix lookup arg_64__ arg_65__
        := match arg_64__ , arg_65__ with
             | _key , nil => None
             | key , cons (pair x y) xys => let j_66__ := lookup key xys in
                                            if GHC.Base.op_zeze__ key x : bool
                                            then Some y
                                            else j_66__
           end.

Definition notElem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix notElem arg_69__ arg_70__
        := match arg_69__ , arg_70__ with
             | _ , nil => true
             | x , cons y ys => andb (GHC.Base.op_zsze__ x y) (notElem x ys)
           end.

Definition null {a} : list a -> bool :=
  fun arg_232__ => match arg_232__ with | nil => true | cons _ _ => false end.

Definition or : list bool -> bool :=
  fix or arg_85__
        := match arg_85__ with
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
  fun arg_91__ =>
    match arg_91__ with
      | l => let rev :=
               fix rev arg_92__ arg_93__
                     := match arg_92__ , arg_93__ with
                          | nil , a => a
                          | cons x xs , a => rev xs (cons x a)
                        end in
             rev l nil
    end.

Definition scanl {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo arg_194__ arg_195__ arg_196__
          := match arg_194__ , arg_195__ , arg_196__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | cons x xs => scanlGo f (f q x) xs
                                    end)
             end in
  scanlGo.

Definition scanl1 {a} : (a -> a -> a) -> list a -> list a :=
  fun arg_201__ arg_202__ =>
    match arg_201__ , arg_202__ with
      | f , cons x xs => scanl f x xs
      | _ , nil => nil
    end.

Definition scanl' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo' arg_175__ arg_176__ arg_177__
          := match arg_175__ , arg_176__ , arg_177__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | cons x xs => scanlGo' f (f q x) xs
                                    end)
             end in
  scanlGo'.

Definition scanlFB {b} {a} {c}
    : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun arg_182__ arg_183__ =>
    match arg_182__ , arg_183__ with
      | f , c => fun arg_184__ arg_185__ =>
                   match arg_184__ , arg_185__ with
                     | b , g => GHC.Base.oneShot (fun arg_186__ =>
                                                   match arg_186__ with
                                                     | x => let b' := f x b in c b' (g b')
                                                   end)
                   end
    end.

Definition scanlFB' {b} {a} {c}
    : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun arg_163__ arg_164__ =>
    match arg_163__ , arg_164__ with
      | f , c => fun arg_165__ arg_166__ =>
                   match arg_165__ , arg_166__ with
                     | b , g => GHC.Base.oneShot (fun arg_167__ =>
                                                   match arg_167__ with
                                                     | x => match f x b with
                                                              | b' => c b' (g b')
                                                            end
                                                   end)
                   end
    end.

Definition scanrFB {a} {b} {c} : (a -> b -> b) -> (b -> c -> c) -> a -> b *
                                 c -> b * c :=
  fun arg_146__ arg_147__ =>
    match arg_146__ , arg_147__ with
      | f , c => fun arg_148__ arg_149__ =>
                   match arg_148__ , arg_149__ with
                     | x , pair r est => pair (f x r) (c r est)
                   end
    end.

Definition span {a} : (a -> bool) -> list a -> list a * list a :=
  fix span arg_105__ arg_106__
        := match arg_105__ , arg_106__ with
             | _ , (nil as xs) => pair xs xs
             | p , (cons x xs' as xs) => let j_108__ := pair nil xs in
                                         if p x : bool
                                         then match span p xs' with
                                                | pair ys zs => pair (cons x ys) zs
                                              end
                                         else j_108__
           end.

Definition strictUncurryScanr {a} {b} {c} : (a -> b -> c) -> a * b -> c :=
  fun arg_154__ arg_155__ =>
    match arg_154__ , arg_155__ with
      | f , pair_ => match pair_ with
                       | pair x y => f x y
                     end
    end.

Definition sum {a} `{(GHC.Num.Num a)} : list a -> a :=
  GHC.Base.foldl GHC.Num.op_zp__ (GHC.Num.fromInteger 0).

Definition takeFB {a} {b}
    : (a -> b -> b) -> b -> a -> (GHC.Num.Int -> b) -> GHC.Num.Int -> b :=
  fun arg_112__ arg_113__ arg_114__ arg_115__ =>
    match arg_112__ , arg_113__ , arg_114__ , arg_115__ with
      | c , n , x , xs => fun arg_116__ =>
                            match arg_116__ with
                              | m => let j_119__ := c x (xs (GHC.Num.op_zm__ m (GHC.Num.fromInteger 1))) in
                                     match m with
                                       | num_117__ => if (num_117__ == GHC.Num.fromInteger 1) : bool
                                                      then c x n
                                                      else j_119__
                                     end
                            end
    end.

Definition takeWhile {a} : (a -> bool) -> list a -> list a :=
  fix takeWhile arg_142__ arg_143__
        := match arg_142__ , arg_143__ with
             | _ , nil => nil
             | p , cons x xs => if p x : bool
                                then cons x (takeWhile p xs)
                                else nil
           end.

Definition takeWhileFB {a} {b}
    : (a -> bool) -> (a -> b -> b) -> b -> a -> b -> b :=
  fun arg_133__ arg_134__ arg_135__ =>
    match arg_133__ , arg_134__ , arg_135__ with
      | p , c , n => fun arg_136__ arg_137__ =>
                       match arg_136__ , arg_137__ with
                         | x , r => if p x : bool
                                    then c x r
                                    else n
                       end
    end.

Definition uncons {a} : list a -> option (a * list a) :=
  fun arg_234__ =>
    match arg_234__ with
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
  fix zip arg_44__ arg_45__
        := match arg_44__ , arg_45__ with
             | nil , _bs => nil
             | _as , nil => nil
             | cons a as_ , cons b bs => cons (pair a b) (zip as_ bs)
           end.

Definition zip3 {a} {b} {c} : list a -> list b -> list c -> list (a * b * c) :=
  fix zip3 arg_31__ arg_32__ arg_33__
        := match arg_31__ , arg_32__ , arg_33__ with
             | cons a as_ , cons b bs , cons c cs => cons (pair (pair a b) c) (zip3 as_ bs
                                                          cs)
             | _ , _ , _ => nil
           end.

Definition zipFB {a} {b} {c} {d} : (a * b -> c -> d) -> a -> b -> c -> d :=
  fun arg_36__ =>
    match arg_36__ with
      | c => fun arg_37__ arg_38__ arg_39__ =>
               match arg_37__ , arg_38__ , arg_39__ with
                 | x , y , r => c (pair x y) r
               end
    end.

Definition zipWith {a} {b} {c} : (a -> b -> c) -> list a -> list b -> list c :=
  fix zipWith arg_26__ arg_27__ arg_28__
        := match arg_26__ , arg_27__ , arg_28__ with
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
  fun arg_17__ arg_18__ =>
    match arg_17__ , arg_18__ with
      | c , f => fun arg_19__ arg_20__ arg_21__ =>
                   match arg_19__ , arg_20__ , arg_21__ with
                     | x , y , r => c (f x y) r
                   end
    end.

(* Unbound variables:
     * == Coq.Init.Datatypes.app GHC.Base.Eq_ GHC.Base.String GHC.Base.const
     GHC.Base.errorWithoutStackTrace GHC.Base.foldl GHC.Base.foldr GHC.Base.id
     GHC.Base.oneShot GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zsze__
     GHC.Num.Int GHC.Num.Num GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ None
     Some andb bool cons false list nil option orb pair true
*)
