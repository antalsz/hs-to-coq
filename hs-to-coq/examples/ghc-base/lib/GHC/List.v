(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Import GHC.Base.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require GHC.Base.
Require GHC.Num.

(* Converted declarations: *)

Definition all {a} : (a -> bool) -> list a -> bool :=
  fix all arg_76__ arg_77__
        := match arg_76__ , arg_77__ with
             | _ , nil => true
             | p , (cons x xs) => andb (p x) (all p xs)
           end.

Definition and : list bool -> bool :=
  fix and arg_87__
        := match arg_87__ with
             | nil => true
             | (cons x xs) => andb x (and xs)
           end.

Definition any {a} : (a -> bool) -> list a -> bool :=
  fix any arg_80__ arg_81__
        := match arg_80__ , arg_81__ with
             | _ , nil => false
             | p , (cons x xs) => orb (p x) (any p xs)
           end.

Definition break {a} : (a -> bool) -> list a -> list a * list a :=
  fix break arg_97__ arg_98__
        := match arg_97__ , arg_98__ with
             | _ , (nil as xs) => pair xs xs
             | p , ((cons x xs') as xs) => let j_101__ :=
                                             match break p xs' with
                                               | (pair ys zs) => pair (cons x ys) zs
                                             end in
                                           if p x
                                           then pair nil xs
                                           else j_101__
           end.

Definition concat {a} : list (list a) -> list a :=
  GHC.Base.foldr Coq.Init.Datatypes.app nil.

Definition constScanl {a} {b} : a -> b -> a :=
  GHC.Base.const.

Definition dropWhile {a} : (a -> bool) -> list a -> list a :=
  fix dropWhile arg_114__ arg_115__
        := match arg_114__ , arg_115__ with
             | _ , nil => nil
             | p , ((cons x xs') as xs) => if p x
                                           then dropWhile p xs'
                                           else xs
           end.

Definition elem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix elem arg_72__ arg_73__
        := match arg_72__ , arg_73__ with
             | _ , nil => false
             | x , (cons y ys) => orb (GHC.Base.op_zeze__ x y) (elem x ys)
           end.

Definition filter {a} : (a -> bool) -> list a -> list a :=
  fix filter arg_194__ arg_195__
        := match arg_194__ , arg_195__ with
             | _pred , nil => nil
             | pred , (cons x xs) => let j_196__ := filter pred xs in
                                     if pred x
                                     then cons x (filter pred xs)
                                     else j_196__
           end.

Definition filterFB {a} {b} : (a -> b -> b) -> (a -> bool) -> a -> b -> b :=
  fun arg_188__ arg_189__ arg_190__ arg_191__ =>
    match arg_188__ , arg_189__ , arg_190__ , arg_191__ with
      | c , p , x , r => if p x
                         then c x r
                         else r
    end.

Definition flipSeqScanl' {a} {b} : a -> b -> a :=
  fun arg_141__ arg_142__ => match arg_141__ , arg_142__ with | a , _b => a end.

Definition flipSeqTake {a} : a -> GHC.Num.Int -> a :=
  fun arg_111__ arg_112__ => match arg_111__ , arg_112__ with | x , _n => x end.

Definition foldr2 {a} {b} {c} : (a -> b -> c -> c) -> c -> list a -> list
                                b -> c :=
  fun arg_55__ arg_56__ =>
    match arg_55__ , arg_56__ with
      | k , z => let go :=
                   fix go arg_57__ arg_58__
                         := match arg_57__ , arg_58__ with
                              | nil , _ys => z
                              | _xs , nil => z
                              | (cons x xs) , (cons y ys) => k x y (go xs ys)
                            end in
                 go
    end.

Definition foldr2_left {a} {b} {c} {d} : (a -> b -> c -> d) -> d -> a -> (list
                                         b -> c) -> list b -> d :=
  fun arg_48__ arg_49__ arg_50__ arg_51__ arg_52__ =>
    match arg_48__ , arg_49__ , arg_50__ , arg_51__ , arg_52__ with
      | _k , z , _x , _r , nil => z
      | k , _z , x , r , (cons y ys) => k x y (r ys)
    end.

Definition idLength : GHC.Num.Int -> GHC.Num.Int :=
  GHC.Base.id.

Definition lenAcc {a} : list a -> GHC.Num.Int -> GHC.Num.Int :=
  fix lenAcc arg_206__ arg_207__
        := match arg_206__ , arg_207__ with
             | nil , n => n
             | (cons _ ys) , n => lenAcc ys (GHC.Num.op_zp__ n (GHC.Num.fromInteger 1))
           end.

Definition length {a} : list a -> GHC.Num.Int :=
  fun arg_210__ =>
    match arg_210__ with
      | xs => lenAcc xs (GHC.Num.fromInteger 0)
    end.

Definition lengthFB {x}
    : x -> (GHC.Num.Int -> GHC.Num.Int) -> GHC.Num.Int -> GHC.Num.Int :=
  fun arg_199__ arg_200__ =>
    match arg_199__ , arg_200__ with
      | _ , r => fun arg_201__ =>
                   match arg_201__ with
                     | a => r (GHC.Num.op_zp__ a (GHC.Num.fromInteger 1))
                   end
    end.

Definition lookup {a} {b} `{(GHC.Base.Eq_ a)} : a -> list (a * b) -> option b :=
  fix lookup arg_63__ arg_64__
        := match arg_63__ , arg_64__ with
             | _key , nil => None
             | key , (cons (pair x y) xys) => let j_65__ := lookup key xys in
                                              if GHC.Base.op_zeze__ key x
                                              then Some y
                                              else j_65__
           end.

Definition notElem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix notElem arg_68__ arg_69__
        := match arg_68__ , arg_69__ with
             | _ , nil => true
             | x , (cons y ys) => andb (GHC.Base.op_zsze__ x y) (notElem x ys)
           end.

Definition null {a} : list a -> bool :=
  fun arg_213__ => match arg_213__ with | nil => true | (cons _ _) => false end.

Definition or : list bool -> bool :=
  fix or arg_84__
        := match arg_84__ with
             | nil => false
             | (cons x xs) => orb x (or xs)
           end.

Definition prel_list_str : GHC.Base.String :=
  GHC.Base.hs_string__ "Prelude.".

Definition product {a} `{(GHC.Num.Num a)} : list a -> a :=
  GHC.Base.foldl GHC.Num.op_zt__ (GHC.Num.fromInteger 1).

Definition reverse {a} : list a -> list a :=
  fun arg_90__ =>
    match arg_90__ with
      | l => let rev :=
               fix rev arg_91__ arg_92__
                     := match arg_91__ , arg_92__ with
                          | nil , a => a
                          | (cons x xs) , a => rev xs (cons x a)
                        end in
             rev l nil
    end.

Definition scanl {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo arg_175__ arg_176__ arg_177__
          := match arg_175__ , arg_176__ , arg_177__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | (cons x xs) => scanlGo f (f q x) xs
                                    end)
             end in
  scanlGo.

Definition scanl1 {a} : (a -> a -> a) -> list a -> list a :=
  fun arg_182__ arg_183__ =>
    match arg_182__ , arg_183__ with
      | f , (cons x xs) => scanl f x xs
      | _ , nil => nil
    end.

Definition scanl' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo' arg_156__ arg_157__ arg_158__
          := match arg_156__ , arg_157__ , arg_158__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | (cons x xs) => scanlGo' f (f q x) xs
                                    end)
             end in
  scanlGo'.

Definition scanlFB {b} {a} {c}
    : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun arg_163__ arg_164__ =>
    match arg_163__ , arg_164__ with
      | f , c => fun arg_165__ arg_166__ =>
                   match arg_165__ , arg_166__ with
                     | b , g => GHC.Base.oneShot (fun arg_167__ =>
                                                   match arg_167__ with
                                                     | x => let b' := f x b in c b' (g b')
                                                   end)
                   end
    end.

Definition scanlFB' {b} {a} {c}
    : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun arg_144__ arg_145__ =>
    match arg_144__ , arg_145__ with
      | f , c => fun arg_146__ arg_147__ =>
                   match arg_146__ , arg_147__ with
                     | b , g => GHC.Base.oneShot (fun arg_148__ =>
                                                   match arg_148__ with
                                                     | x => match f x b with
                                                              | b' => c b' (g b')
                                                            end
                                                   end)
                   end
    end.

Definition scanrFB {a} {b} {c} : (a -> b -> b) -> (b -> c -> c) -> a -> b *
                                 c -> b * c :=
  fun arg_127__ arg_128__ =>
    match arg_127__ , arg_128__ with
      | f , c => fun arg_129__ arg_130__ =>
                   match arg_129__ , arg_130__ with
                     | x , (pair r est) => pair (f x r) (c r est)
                   end
    end.

Definition span {a} : (a -> bool) -> list a -> list a * list a :=
  fix span arg_104__ arg_105__
        := match arg_104__ , arg_105__ with
             | _ , (nil as xs) => pair xs xs
             | p , ((cons x xs') as xs) => let j_107__ := pair nil xs in
                                           if p x
                                           then match span p xs' with
                                                  | (pair ys zs) => pair (cons x ys) zs
                                                end
                                           else j_107__
           end.

Definition strictUncurryScanr {a} {b} {c} : (a -> b -> c) -> a * b -> c :=
  fun arg_135__ arg_136__ =>
    match arg_135__ , arg_136__ with
      | f , pair_ => match pair_ with
                       | (pair x y) => f x y
                     end
    end.

Definition sum {a} `{(GHC.Num.Num a)} : list a -> a :=
  GHC.Base.foldl GHC.Num.op_zp__ (GHC.Num.fromInteger 0).

Definition takeWhileFB {a} {b}
    : (a -> bool) -> (a -> b -> b) -> b -> a -> b -> b :=
  fun arg_118__ arg_119__ arg_120__ =>
    match arg_118__ , arg_119__ , arg_120__ with
      | p , c , n => fun arg_121__ arg_122__ =>
                       match arg_121__ , arg_122__ with
                         | x , r => if p x
                                    then c x r
                                    else n
                       end
    end.

Definition uncons {a} : list a -> option (a * list a) :=
  fun arg_215__ =>
    match arg_215__ with
      | nil => None
      | (cons x xs) => Some (pair x xs)
    end.

Definition unzip {a} {b} : list (a * b) -> list a * list b :=
  GHC.Base.foldr (fun arg_6__ arg_7__ =>
                   match arg_6__ , arg_7__ with
                     | (pair a b) , (pair as_ bs) => pair (cons a as_) (cons b bs)
                   end) (pair nil nil).

Definition unzip3 {a} {b} {c} : list (a * b * c) -> list a * list b * list c :=
  GHC.Base.foldr (fun arg_1__ arg_2__ =>
                   match arg_1__ , arg_2__ with
                     | (pair (pair a b) c) , (pair (pair as_ bs) cs) => pair (pair (cons a as_) (cons
                                                                                   b bs)) (cons c cs)
                   end) (pair (pair nil nil) nil).

Definition zip {a} {b} : list a -> list b -> list (a * b) :=
  fix zip arg_44__ arg_45__
        := match arg_44__ , arg_45__ with
             | nil , _bs => nil
             | _as , nil => nil
             | (cons a as_) , (cons b bs) => cons (pair a b) (zip as_ bs)
           end.

Definition zip3 {a} {b} {c} : list a -> list b -> list c -> list (a * b * c) :=
  fix zip3 arg_31__ arg_32__ arg_33__
        := match arg_31__ , arg_32__ , arg_33__ with
             | (cons a as_) , (cons b bs) , (cons c cs) => cons (pair (pair a b) c) (zip3 as_
                                                                bs cs)
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
             | f , (cons a as_) , (cons b bs) => cons (f a b) (zipWith f as_ bs)
           end.

Definition zipWith3 {a} {b} {c} {d} : (a -> b -> c -> d) -> list a -> list
                                      b -> list c -> list d :=
  fix zipWith3 arg_11__ arg_12__ arg_13__ arg_14__
        := match arg_11__ , arg_12__ , arg_13__ , arg_14__ with
             | z , (cons a as_) , (cons b bs) , (cons c cs) => cons (z a b c) (zipWith3 z as_
                                                                    bs cs)
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
     * Coq.Init.Datatypes.app GHC.Base.Eq_ GHC.Base.String GHC.Base.const
     GHC.Base.foldl GHC.Base.foldr GHC.Base.id GHC.Base.oneShot GHC.Base.op_zeze__
     GHC.Base.op_zsze__ GHC.Num.Int GHC.Num.Num GHC.Num.op_zp__ GHC.Num.op_zt__ None
     Some andb bool cons false list nil option orb pair true
*)
