(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

(* List notation *)
Require Import Coq.Lists.List.
Require Import GHC.Base.

(* Converted imports: *)

Require Data.Maybe.
Require GHC.Base.
Require GHC.Num.
Require GHC.Integer.
Require Coq.Init.Datatypes.

(* Converted declarations: *)

Definition all {a} : (a -> bool) -> list a -> bool :=
  fix all arg_82__ arg_83__
        := match arg_82__ , arg_83__ with
             | _ , nil => true
             | p , (cons x xs) => andb (p x) (all p xs)
           end.

Definition and : list bool -> bool :=
  fix and arg_93__
        := match arg_93__ with
             | nil => true
             | (cons x xs) => andb x (and xs)
           end.

Definition any {a} : (a -> bool) -> list a -> bool :=
  fix any arg_86__ arg_87__
        := match arg_86__ , arg_87__ with
             | _ , nil => false
             | p , (cons x xs) => orb (p x) (any p xs)
           end.

Definition break {a} : (a -> bool) -> list a -> list a * list a :=
  fix break arg_103__ arg_104__
        := match arg_103__ , arg_104__ with
             | _ , (nil as xs) => pair xs xs
             | p , ((cons x xs') as xs) => let j_107__ :=
                                             match break p xs' with
                                               | (pair ys zs) => pair (cons x ys) zs
                                             end in
                                           if p x
                                           then pair nil xs
                                           else j_107__
           end.

Definition concat {a} : list (list a) -> list a :=
  GHC.Base.foldr Coq.Init.Datatypes.app nil.

Definition constScanl {a} {b} : a -> b -> a :=
  GHC.Base.const.

Definition dropWhile {a} : (a -> bool) -> list a -> list a :=
  fix dropWhile arg_120__ arg_121__
        := match arg_120__ , arg_121__ with
             | _ , nil => nil
             | p , ((cons x xs') as xs) => if p x
                                           then dropWhile p xs'
                                           else xs
           end.

Definition elem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix elem arg_78__ arg_79__
        := match arg_78__ , arg_79__ with
             | _ , nil => false
             | x , (cons y ys) => orb (GHC.Base.op_zeze__ x y) (elem x ys)
           end.

Definition filter {a} : (a -> bool) -> list a -> list a :=
  fix filter arg_224__ arg_225__
        := match arg_224__ , arg_225__ with
             | _pred , nil => nil
             | pred , (cons x xs) => let j_226__ := filter pred xs in
                                     if pred x
                                     then cons x (filter pred xs)
                                     else j_226__
           end.

Definition filterFB {a} {b} : (a -> b -> b) -> (a -> bool) -> a -> b -> b :=
  fun arg_218__ arg_219__ arg_220__ arg_221__ =>
    match arg_218__ , arg_219__ , arg_220__ , arg_221__ with
      | c , p , x , r => if p x
                         then c x r
                         else r
    end.

Definition flipSeqScanl' {a} {b} : a -> b -> a :=
  fun arg_153__ arg_154__ => match arg_153__ , arg_154__ with | a , _b => a end.

Definition flipSeqTake {a} : a -> GHC.Num.Int -> a :=
  fun arg_117__ arg_118__ => match arg_117__ , arg_118__ with | x , _n => x end.

Definition foldr2 {a} {b} {c} : (a -> b -> c -> c) -> c -> list a -> list
                                b -> c :=
  fun arg_58__ arg_59__ =>
    match arg_58__ , arg_59__ with
      | k , z => let go :=
                   fix go arg_60__ arg_61__
                         := match arg_60__ , arg_61__ with
                              | nil , _ys => z
                              | _xs , nil => z
                              | (cons x xs) , (cons y ys) => k x y (go xs ys)
                            end in
                 go
    end.

Definition foldr2_left {a} {b} {c} {d} : (a -> b -> c -> d) -> d -> a -> (list
                                         b -> c) -> list b -> d :=
  fun arg_51__ arg_52__ arg_53__ arg_54__ arg_55__ =>
    match arg_51__ , arg_52__ , arg_53__ , arg_54__ , arg_55__ with
      | _k , z , _x , _r , nil => z
      | k , _z , x , r , (cons y ys) => k x y (r ys)
    end.

Definition idLength : GHC.Num.Int -> GHC.Num.Int :=
  GHC.Base.id.

Definition lenAcc {a} : list a -> GHC.Num.Int -> GHC.Num.Int :=
  fix lenAcc arg_236__ arg_237__
        := match arg_236__ , arg_237__ with
             | nil , n => n
             | (cons _ ys) , n => lenAcc ys (GHC.Num.op_zp__ n #1)
           end.

Definition length {a} : list a -> GHC.Num.Int :=
  fun arg_240__ => match arg_240__ with | xs => lenAcc xs #0 end.

Definition lengthFB {x}
    : x -> (GHC.Num.Int -> GHC.Num.Int) -> GHC.Num.Int -> GHC.Num.Int :=
  fun arg_229__ arg_230__ =>
    match arg_229__ , arg_230__ with
      | _ , r => fun arg_231__ =>
                   match arg_231__ with
                     | a => r (GHC.Num.op_zp__ a #1)
                   end
    end.

Definition lookup {a} {b} `{(GHC.Base.Eq_ a)} : a -> list (a * b) -> option b :=
  fix lookup arg_69__ arg_70__
        := match arg_69__ , arg_70__ with
             | _key , nil => None
             | key , (cons (pair x y) xys) => let j_71__ := lookup key xys in
                                              if GHC.Base.op_zeze__ key x
                                              then Some y
                                              else j_71__
           end.

Definition notElem {a} `{(GHC.Base.Eq_ a)} : a -> list a -> bool :=
  fix notElem arg_74__ arg_75__
        := match arg_74__ , arg_75__ with
             | _ , nil => true
             | x , (cons y ys) => andb (GHC.Base.op_zsze__ x y) (notElem x ys)
           end.

Definition null {a} : list a -> bool :=
  fun arg_243__ => match arg_243__ with | nil => true | (cons _ _) => false end.

Definition or : list bool -> bool :=
  fix or arg_90__
        := match arg_90__ with
             | nil => false
             | (cons x xs) => orb x (or xs)
           end.

Definition prel_list_str : GHC.Base.String :=
  &"Prelude.".

Definition tooLarge {a} : GHC.Num.Int -> a :=
  fun arg_65__ =>
    GHC.Base.errorWithoutStackTrace (Coq.Init.Datatypes.app prel_list_str
                                                            &"!!: index too large").

Definition errorEmptyList {a} : GHC.Base.String -> a :=
  fun arg_1__ =>
    match arg_1__ with
      | fun_ => GHC.Base.errorWithoutStackTrace (Coq.Init.Datatypes.app prel_list_str
                                                                        (Coq.Init.Datatypes.app fun_ &": empty list"))
    end.

Definition foldl1 {a} : (a -> a -> a) -> list a -> a :=
  fun arg_203__ arg_204__ =>
    match arg_203__ , arg_204__ with
      | f , (cons x xs) => foldl f x xs
      | _ , nil => errorEmptyList &"foldl1"
    end.

Definition foldl1' {a} : (a -> a -> a) -> list a -> a :=
  fun arg_198__ arg_199__ =>
    match arg_198__ , arg_199__ with
      | f , (cons x xs) => foldl' f x xs
      | _ , nil => errorEmptyList &"foldl1'"
    end.

Definition foldr1 {a} : (a -> a -> a) -> list a -> a :=
  fun arg_147__ =>
    match arg_147__ with
      | f => let go :=
               fix go arg_148__
                     := match arg_148__ with
                          | (cons x nil) => x
                          | (cons x xs) => f x (go xs)
                          | nil => errorEmptyList &"foldr1"
                        end in
             go
    end.

Definition init {a} : list a -> list a :=
  fun arg_245__ =>
    match arg_245__ with
      | nil => errorEmptyList &"init"
      | (cons x xs) => let init' :=
                         fix init' arg_247__ arg_248__
                               := match arg_247__ , arg_248__ with
                                    | _ , nil => nil
                                    | y , (cons z zs) => cons y (init' z zs)
                                  end in
                       init' x xs
    end.

Definition lastError {a} : a :=
  errorEmptyList &"last".

Definition last {a} : list a -> a :=
  fun arg_254__ =>
    match arg_254__ with
      | xs => foldl (fun arg_255__ arg_256__ =>
                      match arg_255__ , arg_256__ with
                        | _ , x => x
                      end) lastError xs
    end.

Definition maximum {a} `{(GHC.Base.Ord a)} : list a -> a :=
  fun arg_208__ =>
    match arg_208__ with
      | nil => errorEmptyList &"maximum"
      | xs => foldl1 GHC.Base.max xs
    end.

Definition minimum {a} `{(GHC.Base.Ord a)} : list a -> a :=
  fun arg_212__ =>
    match arg_212__ with
      | nil => errorEmptyList &"minimum"
      | xs => foldl1 GHC.Base.min xs
    end.

Definition tail {a} : list a -> list a :=
  fun arg_260__ =>
    match arg_260__ with
      | (cons _ xs) => xs
      | nil => errorEmptyList &"tail"
    end.

Definition product {a} `{(GHC.Num.Num a)} : list a -> a :=
  foldl GHC.Num.op_zt__ #1.

Definition reverse {a} : list a -> list a :=
  fun arg_96__ =>
    match arg_96__ with
      | l => let rev :=
               fix rev arg_97__ arg_98__
                     := match arg_97__ , arg_98__ with
                          | nil , a => a
                          | (cons x xs) , a => rev xs (cons x a)
                        end in
             rev l nil
    end.

Definition scanl {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo arg_187__ arg_188__ arg_189__
          := match arg_187__ , arg_188__ , arg_189__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | (cons x xs) => scanlGo f (f q x) xs
                                    end)
             end in
  scanlGo.

Definition scanl1 {a} : (a -> a -> a) -> list a -> list a :=
  fun arg_194__ arg_195__ =>
    match arg_194__ , arg_195__ with
      | f , (cons x xs) => scanl f x xs
      | _ , nil => nil
    end.

Definition scanl' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo' arg_168__ arg_169__ arg_170__
          := match arg_168__ , arg_169__ , arg_170__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | (cons x xs) => scanlGo' f (f q x) xs
                                    end)
             end in
  scanlGo'.

Definition scanlFB {b} {a} {c}
    : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun arg_175__ arg_176__ =>
    match arg_175__ , arg_176__ with
      | f , c => fun arg_177__ arg_178__ =>
                   match arg_177__ , arg_178__ with
                     | b , g => GHC.Base.oneShot (fun arg_179__ =>
                                                   match arg_179__ with
                                                     | x => let b' := f x b in c b' (g b')
                                                   end)
                   end
    end.

Definition scanlFB' {b} {a} {c}
    : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun arg_156__ arg_157__ =>
    match arg_156__ , arg_157__ with
      | f , c => fun arg_158__ arg_159__ =>
                   match arg_158__ , arg_159__ with
                     | b , g => GHC.Base.oneShot (fun arg_160__ =>
                                                   match arg_160__ with
                                                     | x => match f x b with
                                                              | b' => c b' (g b')
                                                            end
                                                   end)
                   end
    end.

Definition scanrFB {a} {b} {c} : (a -> b -> b) -> (b -> c -> c) -> a -> b *
                                 c -> b * c :=
  fun arg_133__ arg_134__ =>
    match arg_133__ , arg_134__ with
      | f , c => fun arg_135__ arg_136__ =>
                   match arg_135__ , arg_136__ with
                     | x , (pair r est) => pair (f x r) (c r est)
                   end
    end.

Definition span {a} : (a -> bool) -> list a -> list a * list a :=
  fix span arg_110__ arg_111__
        := match arg_110__ , arg_111__ with
             | _ , (nil as xs) => pair xs xs
             | p , ((cons x xs') as xs) => let j_113__ := pair nil xs in
                                           if p x
                                           then match span p xs' with
                                                  | (pair ys zs) => pair (cons x ys) zs
                                                end
                                           else j_113__
           end.

Definition strictUncurryScanr {a} {b} {c} : (a -> b -> c) -> a * b -> c :=
  fun arg_141__ arg_142__ =>
    match arg_141__ , arg_142__ with
      | f , pair_ => match pair_ with
                       | (pair x y) => f x y
                     end
    end.

Definition sum {a} `{(GHC.Num.Num a)} : list a -> a :=
  foldl GHC.Num.op_zp__ #0.

Definition takeWhileFB {a} {b}
    : (a -> bool) -> (a -> b -> b) -> b -> a -> b -> b :=
  fun arg_124__ arg_125__ arg_126__ =>
    match arg_124__ , arg_125__ , arg_126__ with
      | p , c , n => fun arg_127__ arg_128__ =>
                       match arg_127__ , arg_128__ with
                         | x , r => if p x
                                    then c x r
                                    else n
                       end
    end.

Definition uncons {a} : list a -> option (a * list a) :=
  fun arg_263__ =>
    match arg_263__ with
      | nil => None
      | (cons x xs) => Some (pair x xs)
    end.

Definition unzip {a} {b} : list (a * b) -> list a * list b :=
  GHC.Base.foldr (fun arg_9__ arg_10__ =>
                   match arg_9__ , arg_10__ with
                     | (pair a b) , (pair as_ bs) => pair (cons a as_) (cons b bs)
                   end) (pair nil nil).

Definition unzip3 {a} {b} {c} : list (a * b * c) -> list a * list b * list c :=
  GHC.Base.foldr (fun arg_4__ arg_5__ =>
                   match arg_4__ , arg_5__ with
                     | (pair (pair a b) c) , (pair (pair as_ bs) cs) => pair (pair (cons a as_) (cons
                                                                                   b bs)) (cons c cs)
                   end) (pair (pair nil nil) nil).

Definition zip {a} {b} : list a -> list b -> list (a * b) :=
  fix zip arg_47__ arg_48__
        := match arg_47__ , arg_48__ with
             | nil , _bs => nil
             | _as , nil => nil
             | (cons a as_) , (cons b bs) => cons (pair a b) (zip as_ bs)
           end.

Definition zip3 {a} {b} {c} : list a -> list b -> list c -> list (a * b * c) :=
  fix zip3 arg_34__ arg_35__ arg_36__
        := match arg_34__ , arg_35__ , arg_36__ with
             | (cons a as_) , (cons b bs) , (cons c cs) => cons (pair (pair a b) c) (zip3 as_
                                                                bs cs)
             | _ , _ , _ => nil
           end.

Definition zipFB {a} {b} {c} {d} : (a * b -> c -> d) -> a -> b -> c -> d :=
  fun arg_39__ =>
    match arg_39__ with
      | c => fun arg_40__ arg_41__ arg_42__ =>
               match arg_40__ , arg_41__ , arg_42__ with
                 | x , y , r => c (pair x y) r
               end
    end.

Definition zipWith {a} {b} {c} : (a -> b -> c) -> list a -> list b -> list c :=
  fix zipWith arg_29__ arg_30__ arg_31__
        := match arg_29__ , arg_30__ , arg_31__ with
             | _f , nil , _bs => nil
             | _f , _as , nil => nil
             | f , (cons a as_) , (cons b bs) => cons (f a b) (zipWith f as_ bs)
           end.

Definition zipWith3 {a} {b} {c} {d} : (a -> b -> c -> d) -> list a -> list
                                      b -> list c -> list d :=
  fix zipWith3 arg_14__ arg_15__ arg_16__ arg_17__
        := match arg_14__ , arg_15__ , arg_16__ , arg_17__ with
             | z , (cons a as_) , (cons b bs) , (cons c cs) => cons (z a b c) (zipWith3 z as_
                                                                    bs cs)
             | _ , _ , _ , _ => nil
           end.

Definition zipWithFB {a} {b} {c} {d} {e}
    : (a -> b -> c) -> (d -> e -> a) -> d -> e -> b -> c :=
  fun arg_20__ arg_21__ =>
    match arg_20__ , arg_21__ with
      | c , f => fun arg_22__ arg_23__ arg_24__ =>
                   match arg_22__ , arg_23__ , arg_24__ with
                     | x , y , r => c (f x y) r
                   end
    end.

(* Unbound variables:
     * Coq.Init.Datatypes.app GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String
     GHC.Base.const GHC.Base.errorWithoutStackTrace GHC.Base.foldr GHC.Base.id
     GHC.Base.max GHC.Base.min GHC.Base.oneShot GHC.Base.op_zeze__ GHC.Base.op_zsze__
     GHC.Num.Int GHC.Num.Num GHC.Num.op_zp__ GHC.Num.op_zt__ None Some andb bool cons
     false foldl foldl' list nil option orb pair true
*)
