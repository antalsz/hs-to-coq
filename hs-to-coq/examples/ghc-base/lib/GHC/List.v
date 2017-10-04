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
Require Coq.Program.Basics.
Require GHC.BaseGen.
Require GHC.Prim.

(* Converted declarations: *)

Definition all {a} : (a -> bool) -> list a -> bool :=
  fix all arg_85__ arg_86__
        := match arg_85__ , arg_86__ with
             | _ , nil => true
             | p , (cons x xs) => andb (p x) (all p xs)
           end.

Definition and : list bool -> bool :=
  fix and arg_96__
        := match arg_96__ with
             | nil => true
             | (cons x xs) => andb x (and xs)
           end.

Definition any {a} : (a -> bool) -> list a -> bool :=
  fix any arg_89__ arg_90__
        := match arg_89__ , arg_90__ with
             | _ , nil => false
             | p , (cons x xs) => orb (p x) (any p xs)
           end.

Definition break {a} : (a -> bool) -> list a -> list a * list a :=
  fix break arg_106__ arg_107__
        := match arg_106__ , arg_107__ with
             | _ , (nil as xs) => pair xs xs
             | p , ((cons x xs') as xs) => let j_110__ :=
                                             match break p xs' with
                                               | (pair ys zs) => pair (cons x ys) zs
                                             end in
                                           if p x
                                           then pair nil xs
                                           else j_110__
           end.

Definition concat {a} : list (list a) -> list a :=
  GHC.BaseGen.foldr GHC.Prim.app nil.

Definition concatMap {a} {b} : (a -> list b) -> list a -> list b :=
  fun arg_69__ =>
    match arg_69__ with
      | f => GHC.BaseGen.foldr (Coq.Program.Basics.compose GHC.Prim.app f) nil
    end.

Definition constScanl {a} {b} : a -> b -> a :=
  GHC.BaseGen.const.

Definition dropWhile {a} : (a -> bool) -> list a -> list a :=
  fix dropWhile arg_123__ arg_124__
        := match arg_123__ , arg_124__ with
             | _ , nil => nil
             | p , ((cons x xs') as xs) => if p x
                                           then dropWhile p xs'
                                           else xs
           end.

Definition elem {a} `{(GHC.Prim.Eq_ a)} : a -> list a -> bool :=
  fix elem arg_81__ arg_82__
        := match arg_81__ , arg_82__ with
             | _ , nil => false
             | x , (cons y ys) => orb (GHC.Prim.op_zeze__ x y) (elem x ys)
           end.

Definition filter {a} : (a -> bool) -> list a -> list a :=
  fix filter arg_227__ arg_228__
        := match arg_227__ , arg_228__ with
             | _pred , nil => nil
             | pred , (cons x xs) => let j_229__ := filter pred xs in
                                     if pred x
                                     then cons x (filter pred xs)
                                     else j_229__
           end.

Definition filterFB {a} {b} : (a -> b -> b) -> (a -> bool) -> a -> b -> b :=
  fun arg_221__ arg_222__ arg_223__ arg_224__ =>
    match arg_221__ , arg_222__ , arg_223__ , arg_224__ with
      | c , p , x , r => if p x
                         then c x r
                         else r
    end.

Definition flipSeqScanl' {a} {b} : a -> b -> a :=
  fun arg_156__ arg_157__ => match arg_156__ , arg_157__ with | a , _b => a end.

Definition flipSeqTake {a} : a -> GHC.Num.Int -> a :=
  fun arg_120__ arg_121__ => match arg_120__ , arg_121__ with | x , _n => x end.

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
  GHC.BaseGen.id.

Definition lenAcc {a} : list a -> GHC.Num.Int -> GHC.Num.Int :=
  fix lenAcc arg_239__ arg_240__
        := match arg_239__ , arg_240__ with
             | nil , n => n
             | (cons _ ys) , n => lenAcc ys (GHC.Num.op_zp__ n #1)
           end.

Definition length {a} : list a -> GHC.Num.Int :=
  fun arg_243__ => match arg_243__ with | xs => lenAcc xs #0 end.

Definition lengthFB {x}
    : x -> (GHC.Num.Int -> GHC.Num.Int) -> GHC.Num.Int -> GHC.Num.Int :=
  fun arg_232__ arg_233__ =>
    match arg_232__ , arg_233__ with
      | _ , r => fun arg_234__ =>
                   match arg_234__ with
                     | a => r (GHC.Num.op_zp__ a #1)
                   end
    end.

Definition lookup {a} {b} `{(GHC.Prim.Eq_ a)} : a -> list (a * b) -> option b :=
  fix lookup arg_72__ arg_73__
        := match arg_72__ , arg_73__ with
             | _key , nil => None
             | key , (cons (pair x y) xys) => let j_74__ := lookup key xys in
                                              if GHC.Prim.op_zeze__ key x
                                              then Some y
                                              else j_74__
           end.

Definition notElem {a} `{(GHC.Prim.Eq_ a)} : a -> list a -> bool :=
  fix notElem arg_77__ arg_78__
        := match arg_77__ , arg_78__ with
             | _ , nil => true
             | x , (cons y ys) => andb (GHC.Prim.op_zsze__ x y) (notElem x ys)
           end.

Definition null {a} : list a -> bool :=
  fun arg_246__ => match arg_246__ with | nil => true | (cons _ _) => false end.

Definition or : list bool -> bool :=
  fix or arg_93__
        := match arg_93__ with
             | nil => false
             | (cons x xs) => orb x (or xs)
           end.

Definition prel_list_str : GHC.Prim.String :=
  &"Prelude.".

Definition tooLarge {a} : GHC.Num.Int -> a :=
  fun arg_65__ =>
    GHC.Prim.errorWithoutStackTrace (GHC.Prim.app prel_list_str
                                                  &"!!: index too large").

Definition errorEmptyList {a} : GHC.Prim.String -> a :=
  fun arg_1__ =>
    match arg_1__ with
      | fun_ => GHC.Prim.errorWithoutStackTrace (GHC.Prim.app prel_list_str
                                                              (GHC.Prim.app fun_ &": empty list"))
    end.

Definition foldl1 {a} : (a -> a -> a) -> list a -> a :=
  fun arg_206__ arg_207__ =>
    match arg_206__ , arg_207__ with
      | f , (cons x xs) => foldl f x xs
      | _ , nil => errorEmptyList &"foldl1"
    end.

Definition foldl1' {a} : (a -> a -> a) -> list a -> a :=
  fun arg_201__ arg_202__ =>
    match arg_201__ , arg_202__ with
      | f , (cons x xs) => foldl' f x xs
      | _ , nil => errorEmptyList &"foldl1'"
    end.

Definition foldr1 {a} : (a -> a -> a) -> list a -> a :=
  fun arg_150__ =>
    match arg_150__ with
      | f => let go :=
               fix go arg_151__
                     := match arg_151__ with
                          | (cons x nil) => x
                          | (cons x xs) => f x (go xs)
                          | nil => errorEmptyList &"foldr1"
                        end in
             go
    end.

Definition init {a} : list a -> list a :=
  fun arg_248__ =>
    match arg_248__ with
      | nil => errorEmptyList &"init"
      | (cons x xs) => let init' :=
                         fix init' arg_250__ arg_251__
                               := match arg_250__ , arg_251__ with
                                    | _ , nil => nil
                                    | y , (cons z zs) => cons y (init' z zs)
                                  end in
                       init' x xs
    end.

Definition lastError {a} : a :=
  errorEmptyList &"last".

Definition last {a} : list a -> a :=
  fun arg_257__ =>
    match arg_257__ with
      | xs => foldl (fun arg_258__ arg_259__ =>
                      match arg_258__ , arg_259__ with
                        | _ , x => x
                      end) lastError xs
    end.

Definition maximum {a} `{(GHC.Prim.Ord a)} : list a -> a :=
  fun arg_211__ =>
    match arg_211__ with
      | nil => errorEmptyList &"maximum"
      | xs => foldl1 GHC.Prim.max xs
    end.

Definition minimum {a} `{(GHC.Prim.Ord a)} : list a -> a :=
  fun arg_215__ =>
    match arg_215__ with
      | nil => errorEmptyList &"minimum"
      | xs => foldl1 GHC.Prim.min xs
    end.

Definition tail {a} : list a -> list a :=
  fun arg_263__ =>
    match arg_263__ with
      | (cons _ xs) => xs
      | nil => errorEmptyList &"tail"
    end.

Definition product {a} `{(GHC.Num.Num a)} : list a -> a :=
  foldl GHC.Num.op_zt__ #1.

Definition reverse {a} : list a -> list a :=
  fun arg_99__ =>
    match arg_99__ with
      | l => let rev :=
               fix rev arg_100__ arg_101__
                     := match arg_100__ , arg_101__ with
                          | nil , a => a
                          | (cons x xs) , a => rev xs (cons x a)
                        end in
             rev l nil
    end.

Definition scanl {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo arg_190__ arg_191__ arg_192__
          := match arg_190__ , arg_191__ , arg_192__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | (cons x xs) => scanlGo f (f q x) xs
                                    end)
             end in
  scanlGo.

Definition scanl1 {a} : (a -> a -> a) -> list a -> list a :=
  fun arg_197__ arg_198__ =>
    match arg_197__ , arg_198__ with
      | f , (cons x xs) => scanl f x xs
      | _ , nil => nil
    end.

Definition scanl' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
  let scanlGo' {b} {a} : (b -> a -> b) -> b -> list a -> list b :=
    fix scanlGo' arg_171__ arg_172__ arg_173__
          := match arg_171__ , arg_172__ , arg_173__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | (cons x xs) => scanlGo' f (f q x) xs
                                    end)
             end in
  scanlGo'.

Definition scanlFB {b} {a} {c}
    : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun arg_178__ arg_179__ =>
    match arg_178__ , arg_179__ with
      | f , c => fun arg_180__ arg_181__ =>
                   match arg_180__ , arg_181__ with
                     | b , g => GHC.Prim.oneShot (fun arg_182__ =>
                                                   match arg_182__ with
                                                     | x => let b' := f x b in c b' (g b')
                                                   end)
                   end
    end.

Definition scanlFB' {b} {a} {c}
    : (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c :=
  fun arg_159__ arg_160__ =>
    match arg_159__ , arg_160__ with
      | f , c => fun arg_161__ arg_162__ =>
                   match arg_161__ , arg_162__ with
                     | b , g => GHC.Prim.oneShot (fun arg_163__ =>
                                                   match arg_163__ with
                                                     | x => match f x b with
                                                              | b' => c b' (g b')
                                                            end
                                                   end)
                   end
    end.

Definition scanrFB {a} {b} {c} : (a -> b -> b) -> (b -> c -> c) -> a -> b *
                                 c -> b * c :=
  fun arg_136__ arg_137__ =>
    match arg_136__ , arg_137__ with
      | f , c => fun arg_138__ arg_139__ =>
                   match arg_138__ , arg_139__ with
                     | x , (pair r est) => pair (f x r) (c r est)
                   end
    end.

Definition span {a} : (a -> bool) -> list a -> list a * list a :=
  fix span arg_113__ arg_114__
        := match arg_113__ , arg_114__ with
             | _ , (nil as xs) => pair xs xs
             | p , ((cons x xs') as xs) => let j_116__ := pair nil xs in
                                           if p x
                                           then match span p xs' with
                                                  | (pair ys zs) => pair (cons x ys) zs
                                                end
                                           else j_116__
           end.

Definition strictUncurryScanr {a} {b} {c} : (a -> b -> c) -> a * b -> c :=
  fun arg_144__ arg_145__ =>
    match arg_144__ , arg_145__ with
      | f , pair_ => match pair_ with
                       | (pair x y) => f x y
                     end
    end.

Definition sum {a} `{(GHC.Num.Num a)} : list a -> a :=
  foldl GHC.Num.op_zp__ #0.

Definition takeWhileFB {a} {b}
    : (a -> bool) -> (a -> b -> b) -> b -> a -> b -> b :=
  fun arg_127__ arg_128__ arg_129__ =>
    match arg_127__ , arg_128__ , arg_129__ with
      | p , c , n => fun arg_130__ arg_131__ =>
                       match arg_130__ , arg_131__ with
                         | x , r => if p x
                                    then c x r
                                    else n
                       end
    end.

Definition uncons {a} : list a -> option (a * list a) :=
  fun arg_266__ =>
    match arg_266__ with
      | nil => None
      | (cons x xs) => Some (pair x xs)
    end.

Definition unzip {a} {b} : list (a * b) -> list a * list b :=
  GHC.BaseGen.foldr (fun arg_9__ arg_10__ =>
                      match arg_9__ , arg_10__ with
                        | (pair a b) , (pair as_ bs) => pair (cons a as_) (cons b bs)
                      end) (pair nil nil).

Definition unzip3 {a} {b} {c} : list (a * b * c) -> list a * list b * list c :=
  GHC.BaseGen.foldr (fun arg_4__ arg_5__ =>
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
     * Coq.Program.Basics.compose GHC.BaseGen.const GHC.BaseGen.foldr GHC.BaseGen.id
     GHC.Num.Int GHC.Num.Num GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.Eq_
     GHC.Prim.Ord GHC.Prim.String GHC.Prim.app GHC.Prim.errorWithoutStackTrace
     GHC.Prim.max GHC.Prim.min GHC.Prim.oneShot GHC.Prim.op_zeze__ GHC.Prim.op_zsze__
     None Some andb bool cons false foldl foldl' list nil option orb pair true
*)
