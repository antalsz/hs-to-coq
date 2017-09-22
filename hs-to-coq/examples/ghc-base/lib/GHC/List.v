(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Let us be a bit explicit by having multiple axoims around *)
(* This one is for untranslatable expressions: *)
Local Axiom missingValue : forall {a}, a.
(* This one is for pattern match failures: *)
Local Axiom patternFailure : forall {a}, a.

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

Definition all {a} : (a -> bool) -> ((list a) -> bool) :=
  fix all arg_95__ arg_96__
        := let j_98__ :=
             match arg_95__ , arg_96__ with
               | p , (cons x xs) => andb (p x) (all p xs)
               | _ , _ => patternFailure
             end in
           match arg_95__ , arg_96__ with
             | _ , nil => true
             | _ , _ => j_98__
           end.

Definition and : (list bool) -> bool :=
  fix and arg_109__
        := let j_111__ :=
             match arg_109__ with
               | (cons x xs) => andb x (and xs)
               | _ => patternFailure
             end in
           match arg_109__ with
             | nil => true
             | _ => j_111__
           end.

Definition any {a} : (a -> bool) -> ((list a) -> bool) :=
  fix any arg_100__ arg_101__
        := let j_103__ :=
             match arg_100__ , arg_101__ with
               | p , (cons x xs) => orb (p x) (any p xs)
               | _ , _ => patternFailure
             end in
           match arg_100__ , arg_101__ with
             | _ , nil => false
             | _ , _ => j_103__
           end.

Definition break {a} : (a -> bool) -> ((list a) -> ((list a) * (list a))) :=
  fix break arg_121__ arg_122__
        := let j_126__ :=
             match arg_121__ , arg_122__ with
               | p , ((cons x xs') as xs) => let j_124__ :=
                                               match break p xs' with
                                                 | (pair ys zs) => pair (cons x ys) zs
                                               end in
                                             if p x
                                             then pair nil xs
                                             else j_124__
               | _ , _ => patternFailure
             end in
           match arg_121__ , arg_122__ with
             | _ , (nil as xs) => pair xs xs
             | _ , _ => j_126__
           end.

Definition concat {a} : (list (list a)) -> (list a) :=
  GHC.BaseGen.foldr GHC.Prim.app nil.

Definition concatMap {a} {b} : (a -> (list b)) -> ((list a) -> (list b)) :=
  fun arg_76__ =>
    match arg_76__ with
      | f => GHC.BaseGen.foldr (Coq.Program.Basics.compose GHC.Prim.app f) nil
    end.

Definition constScanl {a} {b} : a -> (b -> a) :=
  GHC.BaseGen.const.

Definition dropWhile {a} : (a -> bool) -> ((list a) -> (list a)) :=
  fix dropWhile arg_140__ arg_141__
        := let j_143__ :=
             match arg_140__ , arg_141__ with
               | p , ((cons x xs') as xs) => if p x
                                             then dropWhile p xs'
                                             else xs
               | _ , _ => patternFailure
             end in
           match arg_140__ , arg_141__ with
             | _ , nil => nil
             | _ , _ => j_143__
           end.

Definition elem {a} `{(GHC.Prim.Eq_ a)} : a -> ((list a) -> bool) :=
  fix elem arg_90__ arg_91__
        := let j_93__ :=
             match arg_90__ , arg_91__ with
               | x , (cons y ys) => orb (GHC.Prim.op_zeze__ x y) (elem x ys)
               | _ , _ => patternFailure
             end in
           match arg_90__ , arg_91__ with
             | _ , nil => false
             | _ , _ => j_93__
           end.

Definition filter {a} : (a -> bool) -> ((list a) -> (list a)) :=
  fix filter arg_254__ arg_255__
        := let j_258__ :=
             match arg_254__ , arg_255__ with
               | pred , (cons x xs) => let j_256__ := filter pred xs in
                                       if pred x
                                       then cons x (filter pred xs)
                                       else j_256__
               | _ , _ => patternFailure
             end in
           match arg_254__ , arg_255__ with
             | _pred , nil => nil
             | _ , _ => j_258__
           end.

Definition filterFB {a} {b}
    : (a -> (b -> b)) -> ((a -> bool) -> (a -> (b -> b))) :=
  fun arg_248__ arg_249__ arg_250__ arg_251__ =>
    match arg_248__ , arg_249__ , arg_250__ , arg_251__ with
      | c , p , x , r => if p x
                         then c x r
                         else r
    end.

Definition flipSeqScanl' {a} {b} : a -> (b -> a) :=
  fun arg_176__ arg_177__ => match arg_176__ , arg_177__ with | a , _b => a end.

Definition flipSeqTake {a} : a -> (GHC.Num.Int -> a) :=
  fun arg_137__ arg_138__ => match arg_137__ , arg_138__ with | x , _n => x end.

Definition foldr2 {a} {b} {c} : (a -> (b -> (c -> c))) -> (c -> ((list
                                a) -> ((list b) -> c))) :=
  fun arg_63__ arg_64__ =>
    match arg_63__ , arg_64__ with
      | k , z => let go :=
                   fix go arg_65__ arg_66__
                         := let j_68__ :=
                              match arg_65__ , arg_66__ with
                                | (cons x xs) , (cons y ys) => k x y (go xs ys)
                                | _ , _ => patternFailure
                              end in
                            let j_69__ :=
                              match arg_65__ , arg_66__ with
                                | _xs , nil => z
                                | _ , _ => j_68__
                              end in
                            match arg_65__ , arg_66__ with
                              | nil , _ys => z
                              | _ , _ => j_69__
                            end in
                 go
    end.

Definition foldr2_left {a} {b} {c} {d}
    : (a -> (b -> (c -> d))) -> (d -> (a -> (((list b) -> c) -> ((list
      b) -> d)))) :=
  fun arg_55__ arg_56__ arg_57__ arg_58__ arg_59__ =>
    let j_61__ :=
      match arg_55__ , arg_56__ , arg_57__ , arg_58__ , arg_59__ with
        | k , _z , x , r , (cons y ys) => k x y (r ys)
        | _ , _ , _ , _ , _ => patternFailure
      end in
    match arg_55__ , arg_56__ , arg_57__ , arg_58__ , arg_59__ with
      | _k , z , _x , _r , nil => z
      | _ , _ , _ , _ , _ => j_61__
    end.

Definition idLength : GHC.Num.Int -> GHC.Num.Int :=
  GHC.BaseGen.id.

Definition lenAcc {a} : (list a) -> (GHC.Num.Int -> GHC.Num.Int) :=
  fix lenAcc arg_267__ arg_268__
        := let j_270__ :=
             match arg_267__ , arg_268__ with
               | (cons _ ys) , n => lenAcc ys (GHC.Num.op_zp__ n #1)
               | _ , _ => patternFailure
             end in
           match arg_267__ , arg_268__ with
             | nil , n => n
             | _ , _ => j_270__
           end.

Definition length {a} : (list a) -> GHC.Num.Int :=
  fun arg_272__ => match arg_272__ with | xs => lenAcc xs #0 end.

Definition lengthFB {x}
    : x -> ((GHC.Num.Int -> GHC.Num.Int) -> (GHC.Num.Int -> GHC.Num.Int)) :=
  fun arg_260__ arg_261__ =>
    match arg_260__ , arg_261__ with
      | _ , r => fun arg_262__ =>
                   match arg_262__ with
                     | a => r (GHC.Num.op_zp__ a #1)
                   end
    end.

Definition lookup {a} {b} `{(GHC.Prim.Eq_ a)} : a -> ((list (a * b)) -> (option
                                                b)) :=
  fix lookup arg_79__ arg_80__
        := let j_83__ :=
             match arg_79__ , arg_80__ with
               | key , (cons (pair x y) xys) => let j_81__ := lookup key xys in
                                                if GHC.Prim.op_zeze__ key x
                                                then Some y
                                                else j_81__
               | _ , _ => patternFailure
             end in
           match arg_79__ , arg_80__ with
             | _key , nil => None
             | _ , _ => j_83__
           end.

Definition notElem {a} `{(GHC.Prim.Eq_ a)} : a -> ((list a) -> bool) :=
  fix notElem arg_85__ arg_86__
        := let j_88__ :=
             match arg_85__ , arg_86__ with
               | x , (cons y ys) => andb (GHC.Prim.op_zsze__ x y) (notElem x ys)
               | _ , _ => patternFailure
             end in
           match arg_85__ , arg_86__ with
             | _ , nil => true
             | _ , _ => j_88__
           end.

Definition null {a} : (list a) -> bool :=
  fun arg_275__ =>
    let j_276__ :=
      match arg_275__ with
        | (cons _ _) => false
        | _ => patternFailure
      end in
    match arg_275__ with
      | nil => true
      | _ => j_276__
    end.

Definition or : (list bool) -> bool :=
  fix or arg_105__
        := let j_107__ :=
             match arg_105__ with
               | (cons x xs) => orb x (or xs)
               | _ => patternFailure
             end in
           match arg_105__ with
             | nil => false
             | _ => j_107__
           end.

Definition prel_list_str : GHC.Prim.String :=
  &"Prelude.".

Definition tooLarge {a} : GHC.Num.Int -> a :=
  fun arg_72__ =>
    (GHC.Prim.errorWithoutStackTrace (GHC.Prim.app prel_list_str
                                                   &"!!: index too large")).

Definition errorEmptyList {a} : GHC.Prim.String -> a :=
  fun arg_1__ =>
    match arg_1__ with
      | fun_ => GHC.Prim.errorWithoutStackTrace (GHC.Prim.app prel_list_str
                                                              (GHC.Prim.app fun_ &": empty list"))
    end.

Definition foldl1 {a} : (a -> (a -> a)) -> ((list a) -> a) :=
  fun arg_230__ arg_231__ =>
    let j_233__ :=
      match arg_230__ , arg_231__ with
        | _ , nil => errorEmptyList &"foldl1"
        | _ , _ => patternFailure
      end in
    match arg_230__ , arg_231__ with
      | f , (cons x xs) => foldl f x xs
      | _ , _ => j_233__
    end.

Definition foldl1' {a} : (a -> (a -> a)) -> ((list a) -> a) :=
  fun arg_224__ arg_225__ =>
    let j_227__ :=
      match arg_224__ , arg_225__ with
        | _ , nil => errorEmptyList &"foldl1'"
        | _ , _ => patternFailure
      end in
    match arg_224__ , arg_225__ with
      | f , (cons x xs) => foldl' f x xs
      | _ , _ => j_227__
    end.

Definition foldr1 {a} : (a -> (a -> a)) -> ((list a) -> a) :=
  fun arg_168__ =>
    match arg_168__ with
      | f => let go :=
               fix go arg_169__
                     := let j_171__ :=
                          match arg_169__ with
                            | nil => errorEmptyList &"foldr1"
                            | _ => patternFailure
                          end in
                        let j_173__ :=
                          match arg_169__ with
                            | (cons x xs) => f x (go xs)
                            | _ => j_171__
                          end in
                        match arg_169__ with
                          | (x :: nil) => x
                          | _ => j_173__
                        end in
             go
    end.

Definition init {a} : (list a) -> (list a) :=
  fun arg_278__ =>
    let j_285__ :=
      match arg_278__ with
        | (cons x xs) => let init' :=
                           fix init' arg_279__ arg_280__
                                 := let j_282__ :=
                                      match arg_279__ , arg_280__ with
                                        | y , (cons z zs) => cons y (init' z zs)
                                        | _ , _ => patternFailure
                                      end in
                                    match arg_279__ , arg_280__ with
                                      | _ , nil => nil
                                      | _ , _ => j_282__
                                    end in
                         init' x xs
        | _ => patternFailure
      end in
    match arg_278__ with
      | nil => errorEmptyList &"init"
      | _ => j_285__
    end.

Definition lastError {a} : a :=
  errorEmptyList &"last".

Definition last {a} : (list a) -> a :=
  fun arg_289__ =>
    match arg_289__ with
      | xs => foldl (fun arg_290__ arg_291__ =>
                      match arg_290__ , arg_291__ with
                        | _ , x => x
                      end) lastError xs
    end.

Definition maximum {a} `{(GHC.Prim.Ord a)} : (list a) -> a :=
  fun arg_236__ =>
    let j_238__ := match arg_236__ with | xs => foldl1 GHC.Prim.max xs end in
    match arg_236__ with
      | nil => errorEmptyList &"maximum"
      | _ => j_238__
    end.

Definition minimum {a} `{(GHC.Prim.Ord a)} : (list a) -> a :=
  fun arg_241__ =>
    let j_243__ := match arg_241__ with | xs => foldl1 GHC.Prim.min xs end in
    match arg_241__ with
      | nil => errorEmptyList &"minimum"
      | _ => j_243__
    end.

Definition tail {a} : (list a) -> (list a) :=
  fun arg_295__ =>
    let j_297__ :=
      match arg_295__ with
        | nil => errorEmptyList &"tail"
        | _ => patternFailure
      end in
    match arg_295__ with
      | (cons _ xs) => xs
      | _ => j_297__
    end.

Definition product {a} `{(GHC.Num.Num a)} : (list a) -> a :=
  foldl GHC.Num.op_zt__ #1.

Definition reverse {a} : (list a) -> (list a) :=
  fun arg_113__ =>
    match arg_113__ with
      | l => let rev :=
               fix rev arg_114__ arg_115__
                     := let j_117__ :=
                          match arg_114__ , arg_115__ with
                            | (cons x xs) , a => rev xs (cons x a)
                            | _ , _ => patternFailure
                          end in
                        match arg_114__ , arg_115__ with
                          | nil , a => a
                          | _ , _ => j_117__
                        end in
             rev l nil
    end.

Definition scanl {b} {a} : (b -> (a -> b)) -> (b -> ((list a) -> (list b))) :=
  let scanlGo {b} {a} : (b -> (a -> b)) -> (b -> ((list a) -> (list b))) :=
    fix scanlGo arg_211__ arg_212__ arg_213__
          := match arg_211__ , arg_212__ , arg_213__ with
               | f , q , ls => cons q (let j_215__ :=
                                      match ls with
                                        | (cons x xs) => scanlGo f (f q x) xs
                                        | _ => patternFailure
                                      end in
                                    match ls with
                                      | nil => nil
                                      | _ => j_215__
                                    end)
             end in
  scanlGo.

Definition scanl1 {a} : (a -> (a -> a)) -> ((list a) -> (list a)) :=
  fun arg_219__ arg_220__ =>
    let j_221__ :=
      match arg_219__ , arg_220__ with
        | _ , nil => nil
        | _ , _ => patternFailure
      end in
    match arg_219__ , arg_220__ with
      | f , (cons x xs) => scanl f x xs
      | _ , _ => j_221__
    end.

Definition scanl' {b} {a} : (b -> (a -> b)) -> (b -> ((list a) -> (list b))) :=
  let scanlGo' {b} {a} : (b -> (a -> b)) -> (b -> ((list a) -> (list b))) :=
    fix scanlGo' arg_191__ arg_192__ arg_193__
          := match arg_191__ , arg_192__ , arg_193__ with
               | f , q , ls => cons q (let j_195__ :=
                                      match ls with
                                        | (cons x xs) => scanlGo' f (f q x) xs
                                        | _ => patternFailure
                                      end in
                                    match ls with
                                      | nil => nil
                                      | _ => j_195__
                                    end)
             end in
  scanlGo'.

Definition scanlFB {b} {a} {c}
    : (b -> (a -> b)) -> ((b -> (c -> c)) -> (a -> ((b -> c) -> (b -> c)))) :=
  fun arg_199__ arg_200__ =>
    match arg_199__ , arg_200__ with
      | f , c => fun arg_201__ arg_202__ =>
                   match arg_201__ , arg_202__ with
                     | b , g => GHC.Prim.oneShot (fun arg_203__ =>
                                                   match arg_203__ with
                                                     | x => let b' := f x b in c b' (g b')
                                                   end)
                   end
    end.

Definition scanlFB' {b} {a} {c}
    : (b -> (a -> b)) -> ((b -> (c -> c)) -> (a -> ((b -> c) -> (b -> c)))) :=
  fun arg_179__ arg_180__ =>
    match arg_179__ , arg_180__ with
      | f , c => fun arg_181__ arg_182__ =>
                   match arg_181__ , arg_182__ with
                     | b , g => GHC.Prim.oneShot (fun arg_183__ =>
                                                   match arg_183__ with
                                                     | x => match f x b with
                                                              | b' => c b' (g b')
                                                            end
                                                   end)
                   end
    end.

Definition scanrFB {a} {b} {c} : (a -> (b -> b)) -> ((b -> (c -> c)) -> (a -> (b
                                 * c -> (b * c)))) :=
  fun arg_154__ arg_155__ =>
    match arg_154__ , arg_155__ with
      | f , c => fun arg_156__ arg_157__ =>
                   match arg_156__ , arg_157__ with
                     | x , (pair r est) => pair (f x r) (c r est)
                   end
    end.

Definition span {a} : (a -> bool) -> ((list a) -> ((list a) * (list a))) :=
  fix span arg_129__ arg_130__
        := let j_134__ :=
             match arg_129__ , arg_130__ with
               | p , ((cons x xs') as xs) => let j_131__ := pair nil xs in
                                             if p x
                                             then match span p xs' with
                                                    | (pair ys zs) => pair (cons x ys) zs
                                                  end
                                             else j_131__
               | _ , _ => patternFailure
             end in
           match arg_129__ , arg_130__ with
             | _ , (nil as xs) => pair xs xs
             | _ , _ => j_134__
           end.

Definition strictUncurryScanr {a} {b} {c} : (a -> (b -> c)) -> (a * b -> c) :=
  fun arg_162__ arg_163__ =>
    match arg_162__ , arg_163__ with
      | f , pair_ => match pair_ with
                       | (pair x y) => f x y
                     end
    end.

Definition sum {a} `{(GHC.Num.Num a)} : (list a) -> a :=
  foldl GHC.Num.op_zp__ #0.

Definition takeWhileFB {a} {b}
    : (a -> bool) -> ((a -> (b -> b)) -> (b -> (a -> (b -> b)))) :=
  fun arg_145__ arg_146__ arg_147__ =>
    match arg_145__ , arg_146__ , arg_147__ with
      | p , c , n => fun arg_148__ arg_149__ =>
                       match arg_148__ , arg_149__ with
                         | x , r => if p x
                                    then c x r
                                    else n
                       end
    end.

Definition uncons {a} : (list a) -> (option (a * (list a))) :=
  fun arg_299__ =>
    let j_301__ :=
      match arg_299__ with
        | (cons x xs) => Some (pair x xs)
        | _ => patternFailure
      end in
    match arg_299__ with
      | nil => None
      | _ => j_301__
    end.

Definition unzip {a} {b} : (list (a * b)) -> ((list a) * (list b)) :=
  GHC.BaseGen.foldr (fun arg_9__ arg_10__ =>
                      match arg_9__ , arg_10__ with
                        | (pair a b) , (pair as_ bs) => pair (cons a as_) (cons b bs)
                      end) (pair nil nil).

Definition unzip3 {a} {b} {c} : (list (a * b * c)) -> ((list a) * (list b) *
                                (list c)) :=
  GHC.BaseGen.foldr (fun arg_4__ arg_5__ =>
                      match arg_4__ , arg_5__ with
                        | (pair (pair a b) c) , (pair (pair as_ bs) cs) => pair (pair (cons a as_) (cons
                                                                                      b bs)) (cons c cs)
                      end) (pair (pair nil nil) nil).

Definition zip {a} {b} : (list a) -> ((list b) -> (list (a * b))) :=
  fix zip arg_49__ arg_50__
        := let j_52__ :=
             match arg_49__ , arg_50__ with
               | (cons a as_) , (cons b bs) => cons (pair a b) (zip as_ bs)
               | _ , _ => patternFailure
             end in
           let j_53__ :=
             match arg_49__ , arg_50__ with
               | _as , nil => nil
               | _ , _ => j_52__
             end in
           match arg_49__ , arg_50__ with
             | nil , _bs => nil
             | _ , _ => j_53__
           end.

Definition zip3 {a} {b} {c} : (list a) -> ((list b) -> ((list c) -> (list (a * b
                                                                          * c)))) :=
  fix zip3 arg_36__ arg_37__ arg_38__
        := match arg_36__ , arg_37__ , arg_38__ with
             | (cons a as_) , (cons b bs) , (cons c cs) => cons (pair (pair a b) c) (zip3 as_
                                                                bs cs)
             | _ , _ , _ => nil
           end.

Definition zipFB {a} {b} {c} {d} : (a *
                                   b -> (c -> d)) -> (a -> (b -> (c -> d))) :=
  fun arg_41__ =>
    match arg_41__ with
      | c => fun arg_42__ arg_43__ arg_44__ =>
               match arg_42__ , arg_43__ , arg_44__ with
                 | x , y , r => c (pair x y) r
               end
    end.

Definition zipWith {a} {b} {c} : (a -> (b -> c)) -> ((list a) -> ((list
                                 b) -> (list c))) :=
  fix zipWith arg_29__ arg_30__ arg_31__
        := let j_33__ :=
             match arg_29__ , arg_30__ , arg_31__ with
               | f , (cons a as_) , (cons b bs) => cons (f a b) (zipWith f as_ bs)
               | _ , _ , _ => patternFailure
             end in
           let j_34__ :=
             match arg_29__ , arg_30__ , arg_31__ with
               | _f , _as , nil => nil
               | _ , _ , _ => j_33__
             end in
           match arg_29__ , arg_30__ , arg_31__ with
             | _f , nil , _bs => nil
             | _ , _ , _ => j_34__
           end.

Definition zipWith3 {a} {b} {c} {d} : (a -> (b -> (c -> d))) -> ((list
                                      a) -> ((list b) -> ((list c) -> (list d)))) :=
  fix zipWith3 arg_14__ arg_15__ arg_16__ arg_17__
        := match arg_14__ , arg_15__ , arg_16__ , arg_17__ with
             | z , (cons a as_) , (cons b bs) , (cons c cs) => cons (z a b c) (zipWith3 z as_
                                                                    bs cs)
             | _ , _ , _ , _ => nil
           end.

Definition zipWithFB {a} {b} {c} {d} {e}
    : (a -> (b -> c)) -> ((d -> (e -> a)) -> (d -> (e -> (b -> c)))) :=
  fun arg_20__ arg_21__ =>
    match arg_20__ , arg_21__ with
      | c , f => fun arg_22__ arg_23__ arg_24__ =>
                   match arg_22__ , arg_23__ , arg_24__ with
                     | x , y , r => c (f x y) r
                   end
    end.

(* Unbound variables:
     * :: Coq.Program.Basics.compose GHC.BaseGen.const GHC.BaseGen.foldr
     GHC.BaseGen.id GHC.Num.Int GHC.Num.Num GHC.Num.op_zp__ GHC.Num.op_zt__
     GHC.Prim.Eq_ GHC.Prim.Ord GHC.Prim.String GHC.Prim.app
     GHC.Prim.errorWithoutStackTrace GHC.Prim.max GHC.Prim.min GHC.Prim.oneShot
     GHC.Prim.op_zeze__ GHC.Prim.op_zsze__ None Some andb bool cons false foldl
     foldl' list nil option orb pair true
*)
