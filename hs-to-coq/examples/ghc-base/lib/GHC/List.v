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

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom patternFailure : (forall {a}, a).

Definition all {a} : (a -> bool) -> ((list a) -> bool) :=
  fix all arg_88__ arg_89__
        := match arg_88__ , arg_89__ with
             | _ , nil => true
             | p , (cons x xs) => andb (p x) (all p xs)
           end.

Definition and : (list bool) -> bool :=
  fix and arg_99__
        := match arg_99__ with
             | nil => true
             | (cons x xs) => andb x (and xs)
           end.

Definition any {a} : (a -> bool) -> ((list a) -> bool) :=
  fix any arg_92__ arg_93__
        := match arg_92__ , arg_93__ with
             | _ , nil => false
             | p , (cons x xs) => orb (p x) (any p xs)
           end.

Definition break {a} : (a -> bool) -> ((list a) -> ((list a) * (list a))) :=
  fix break arg_109__ arg_110__
        := match arg_109__ , arg_110__ with
             | _ , (nil as xs) => pair xs xs
             | p , ((cons x xs') as xs) => let j_113__ :=
                                             match break p xs' with
                                               | (pair ys zs) => pair (cons x ys) zs
                                             end in
                                           if p x
                                           then pair nil xs
                                           else j_113__
           end.

Definition concat {a} : (list (list a)) -> (list a) :=
  GHC.BaseGen.foldr GHC.Prim.app nil.

Definition concatMap {a} {b} : (a -> (list b)) -> ((list a) -> (list b)) :=
  fun arg_72__ =>
    match arg_72__ with
      | f => GHC.BaseGen.foldr (Coq.Program.Basics.compose GHC.Prim.app f) nil
    end.

Definition constScanl {a} {b} : a -> (b -> a) :=
  GHC.BaseGen.const.

Definition dropWhile {a} : (a -> bool) -> ((list a) -> (list a)) :=
  fix dropWhile arg_126__ arg_127__
        := match arg_126__ , arg_127__ with
             | _ , nil => nil
             | p , ((cons x xs') as xs) => if p x
                                           then dropWhile p xs'
                                           else xs
           end.

Definition elem {a} `{(GHC.Prim.Eq_ a)} : a -> ((list a) -> bool) :=
  fix elem arg_84__ arg_85__
        := match arg_84__ , arg_85__ with
             | _ , nil => false
             | x , (cons y ys) => orb (GHC.Prim.op_zeze__ x y) (elem x ys)
           end.

Definition filter {a} : (a -> bool) -> ((list a) -> (list a)) :=
  fix filter arg_233__ arg_234__
        := match arg_233__ , arg_234__ with
             | _pred , nil => nil
             | pred , (cons x xs) => let j_235__ := filter pred xs in
                                     if pred x
                                     then cons x (filter pred xs)
                                     else j_235__
           end.

Definition filterFB {a} {b}
    : (a -> (b -> b)) -> ((a -> bool) -> (a -> (b -> b))) :=
  fun arg_227__ arg_228__ arg_229__ arg_230__ =>
    match arg_227__ , arg_228__ , arg_229__ , arg_230__ with
      | c , p , x , r => if p x
                         then c x r
                         else r
    end.

Definition flipSeqScanl' {a} {b} : a -> (b -> a) :=
  fun arg_160__ arg_161__ => match arg_160__ , arg_161__ with | a , _b => a end.

Definition flipSeqTake {a} : a -> (GHC.Num.Int -> a) :=
  fun arg_123__ arg_124__ => match arg_123__ , arg_124__ with | x , _n => x end.

Definition foldr2 {a} {b} {c} : (a -> (b -> (c -> c))) -> (c -> ((list
                                a) -> ((list b) -> c))) :=
  fun arg_60__ arg_61__ =>
    match arg_60__ , arg_61__ with
      | k , z => let go :=
                   fix go arg_62__ arg_63__
                         := let j_65__ :=
                              match arg_62__ , arg_63__ with
                                | _xs , nil => z
                                | (cons x xs) , (cons y ys) => k x y (go xs ys)
                                | _ , _ => patternFailure
                              end in
                            match arg_62__ , arg_63__ with
                              | nil , _ys => z
                              | _ , _ => j_65__
                            end in
                 go
    end.

Definition foldr2_left {a} {b} {c} {d}
    : (a -> (b -> (c -> d))) -> (d -> (a -> (((list b) -> c) -> ((list
      b) -> d)))) :=
  fun arg_53__ arg_54__ arg_55__ arg_56__ arg_57__ =>
    match arg_53__ , arg_54__ , arg_55__ , arg_56__ , arg_57__ with
      | _k , z , _x , _r , nil => z
      | k , _z , x , r , (cons y ys) => k x y (r ys)
    end.

Definition idLength : GHC.Num.Int -> GHC.Num.Int :=
  GHC.BaseGen.id.

Definition lenAcc {a} : (list a) -> (GHC.Num.Int -> GHC.Num.Int) :=
  fix lenAcc arg_245__ arg_246__
        := match arg_245__ , arg_246__ with
             | nil , n => n
             | (cons _ ys) , n => lenAcc ys (GHC.Num.op_zp__ n #1)
           end.

Definition length {a} : (list a) -> GHC.Num.Int :=
  fun arg_249__ => match arg_249__ with | xs => lenAcc xs #0 end.

Definition lengthFB {x}
    : x -> ((GHC.Num.Int -> GHC.Num.Int) -> (GHC.Num.Int -> GHC.Num.Int)) :=
  fun arg_238__ arg_239__ =>
    match arg_238__ , arg_239__ with
      | _ , r => fun arg_240__ =>
                   match arg_240__ with
                     | a => r (GHC.Num.op_zp__ a #1)
                   end
    end.

Definition lookup {a} {b} `{(GHC.Prim.Eq_ a)} : a -> ((list (a * b)) -> (option
                                                b)) :=
  fix lookup arg_75__ arg_76__
        := match arg_75__ , arg_76__ with
             | _key , nil => None
             | key , (cons (pair x y) xys) => let j_77__ := lookup key xys in
                                              if GHC.Prim.op_zeze__ key x
                                              then Some y
                                              else j_77__
           end.

Definition notElem {a} `{(GHC.Prim.Eq_ a)} : a -> ((list a) -> bool) :=
  fix notElem arg_80__ arg_81__
        := match arg_80__ , arg_81__ with
             | _ , nil => true
             | x , (cons y ys) => andb (GHC.Prim.op_zsze__ x y) (notElem x ys)
           end.

Definition null {a} : (list a) -> bool :=
  fun arg_252__ => match arg_252__ with | nil => true | (cons _ _) => false end.

Definition or : (list bool) -> bool :=
  fix or arg_96__
        := match arg_96__ with
             | nil => false
             | (cons x xs) => orb x (or xs)
           end.

Definition prel_list_str : GHC.Prim.String :=
  &"Prelude.".

Definition tooLarge {a} : GHC.Num.Int -> a :=
  fun arg_68__ =>
    (GHC.Prim.errorWithoutStackTrace (GHC.Prim.app prel_list_str
                                                   &"!!: index too large")).

Definition errorEmptyList {a} : GHC.Prim.String -> a :=
  fun arg_1__ =>
    match arg_1__ with
      | fun_ => GHC.Prim.errorWithoutStackTrace (GHC.Prim.app prel_list_str
                                                              (GHC.Prim.app fun_ &": empty list"))
    end.

Definition foldl1 {a} : (a -> (a -> a)) -> ((list a) -> a) :=
  fun arg_210__ arg_211__ =>
    match arg_210__ , arg_211__ with
      | f , (cons x xs) => foldl f x xs
      | _ , nil => errorEmptyList &"foldl1"
    end.

Definition foldl1' {a} : (a -> (a -> a)) -> ((list a) -> a) :=
  fun arg_205__ arg_206__ =>
    match arg_205__ , arg_206__ with
      | f , (cons x xs) => foldl' f x xs
      | _ , nil => errorEmptyList &"foldl1'"
    end.

Definition foldr1 {a} : (a -> (a -> a)) -> ((list a) -> a) :=
  fun arg_153__ =>
    match arg_153__ with
      | f => let go :=
               fix go arg_154__
                     := let j_157__ :=
                          match arg_154__ with
                            | (cons x xs) => f x (go xs)
                            | nil => errorEmptyList &"foldr1"
                          end in
                        match arg_154__ with
                          | (cons x nil) => x
                          | _ => j_157__
                        end in
             go
    end.

Definition init {a} : (list a) -> (list a) :=
  fun arg_254__ =>
    match arg_254__ with
      | nil => errorEmptyList &"init"
      | (cons x xs) => let init' :=
                         fix init' arg_256__ arg_257__
                               := match arg_256__ , arg_257__ with
                                    | _ , nil => nil
                                    | y , (cons z zs) => cons y (init' z zs)
                                  end in
                       init' x xs
    end.

Definition lastError {a} : a :=
  errorEmptyList &"last".

Definition last {a} : (list a) -> a :=
  fun arg_263__ =>
    match arg_263__ with
      | xs => foldl (fun arg_264__ arg_265__ =>
                      match arg_264__ , arg_265__ with
                        | _ , x => x
                      end) lastError xs
    end.

Definition maximum {a} `{(GHC.Prim.Ord a)} : (list a) -> a :=
  fun arg_215__ =>
    let j_217__ := match arg_215__ with | xs => foldl1 GHC.Prim.max xs end in
    match arg_215__ with
      | nil => errorEmptyList &"maximum"
      | _ => j_217__
    end.

Definition minimum {a} `{(GHC.Prim.Ord a)} : (list a) -> a :=
  fun arg_220__ =>
    let j_222__ := match arg_220__ with | xs => foldl1 GHC.Prim.min xs end in
    match arg_220__ with
      | nil => errorEmptyList &"minimum"
      | _ => j_222__
    end.

Definition tail {a} : (list a) -> (list a) :=
  fun arg_269__ =>
    match arg_269__ with
      | (cons _ xs) => xs
      | nil => errorEmptyList &"tail"
    end.

Definition product {a} `{(GHC.Num.Num a)} : (list a) -> a :=
  foldl GHC.Num.op_zt__ #1.

Definition reverse {a} : (list a) -> (list a) :=
  fun arg_102__ =>
    match arg_102__ with
      | l => let rev :=
               fix rev arg_103__ arg_104__
                     := match arg_103__ , arg_104__ with
                          | nil , a => a
                          | (cons x xs) , a => rev xs (cons x a)
                        end in
             rev l nil
    end.

Definition scanl {b} {a} : (b -> (a -> b)) -> (b -> ((list a) -> (list b))) :=
  let scanlGo {b} {a} : (b -> (a -> b)) -> (b -> ((list a) -> (list b))) :=
    fix scanlGo arg_194__ arg_195__ arg_196__
          := match arg_194__ , arg_195__ , arg_196__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | (cons x xs) => scanlGo f (f q x) xs
                                    end)
             end in
  scanlGo.

Definition scanl1 {a} : (a -> (a -> a)) -> ((list a) -> (list a)) :=
  fun arg_201__ arg_202__ =>
    match arg_201__ , arg_202__ with
      | f , (cons x xs) => scanl f x xs
      | _ , nil => nil
    end.

Definition scanl' {b} {a} : (b -> (a -> b)) -> (b -> ((list a) -> (list b))) :=
  let scanlGo' {b} {a} : (b -> (a -> b)) -> (b -> ((list a) -> (list b))) :=
    fix scanlGo' arg_175__ arg_176__ arg_177__
          := match arg_175__ , arg_176__ , arg_177__ with
               | f , q , ls => cons q (match ls with
                                      | nil => nil
                                      | (cons x xs) => scanlGo' f (f q x) xs
                                    end)
             end in
  scanlGo'.

Definition scanlFB {b} {a} {c}
    : (b -> (a -> b)) -> ((b -> (c -> c)) -> (a -> ((b -> c) -> (b -> c)))) :=
  fun arg_182__ arg_183__ =>
    match arg_182__ , arg_183__ with
      | f , c => fun arg_184__ arg_185__ =>
                   match arg_184__ , arg_185__ with
                     | b , g => GHC.Prim.oneShot (fun arg_186__ =>
                                                   match arg_186__ with
                                                     | x => let b' := f x b in c b' (g b')
                                                   end)
                   end
    end.

Definition scanlFB' {b} {a} {c}
    : (b -> (a -> b)) -> ((b -> (c -> c)) -> (a -> ((b -> c) -> (b -> c)))) :=
  fun arg_163__ arg_164__ =>
    match arg_163__ , arg_164__ with
      | f , c => fun arg_165__ arg_166__ =>
                   match arg_165__ , arg_166__ with
                     | b , g => GHC.Prim.oneShot (fun arg_167__ =>
                                                   match arg_167__ with
                                                     | x => match f x b with
                                                              | b' => c b' (g b')
                                                            end
                                                   end)
                   end
    end.

Definition scanrFB {a} {b} {c} : (a -> (b -> b)) -> ((b -> (c -> c)) -> (a -> (b
                                 * c -> (b * c)))) :=
  fun arg_139__ arg_140__ =>
    match arg_139__ , arg_140__ with
      | f , c => fun arg_141__ arg_142__ =>
                   match arg_141__ , arg_142__ with
                     | x , (pair r est) => pair (f x r) (c r est)
                   end
    end.

Definition span {a} : (a -> bool) -> ((list a) -> ((list a) * (list a))) :=
  fix span arg_116__ arg_117__
        := match arg_116__ , arg_117__ with
             | _ , (nil as xs) => pair xs xs
             | p , ((cons x xs') as xs) => let j_119__ := pair nil xs in
                                           if p x
                                           then match span p xs' with
                                                  | (pair ys zs) => pair (cons x ys) zs
                                                end
                                           else j_119__
           end.

Definition strictUncurryScanr {a} {b} {c} : (a -> (b -> c)) -> (a * b -> c) :=
  fun arg_147__ arg_148__ =>
    match arg_147__ , arg_148__ with
      | f , pair_ => match pair_ with
                       | (pair x y) => f x y
                     end
    end.

Definition sum {a} `{(GHC.Num.Num a)} : (list a) -> a :=
  foldl GHC.Num.op_zp__ #0.

Definition takeWhileFB {a} {b}
    : (a -> bool) -> ((a -> (b -> b)) -> (b -> (a -> (b -> b)))) :=
  fun arg_130__ arg_131__ arg_132__ =>
    match arg_130__ , arg_131__ , arg_132__ with
      | p , c , n => fun arg_133__ arg_134__ =>
                       match arg_133__ , arg_134__ with
                         | x , r => if p x
                                    then c x r
                                    else n
                       end
    end.

Definition uncons {a} : (list a) -> (option (a * (list a))) :=
  fun arg_272__ =>
    match arg_272__ with
      | nil => None
      | (cons x xs) => Some (pair x xs)
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
  fix zip arg_48__ arg_49__
        := let j_51__ :=
             match arg_48__ , arg_49__ with
               | _as , nil => nil
               | (cons a as_) , (cons b bs) => cons (pair a b) (zip as_ bs)
               | _ , _ => patternFailure
             end in
           match arg_48__ , arg_49__ with
             | nil , _bs => nil
             | _ , _ => j_51__
           end.

Definition zip3 {a} {b} {c} : (list a) -> ((list b) -> ((list c) -> (list (a * b
                                                                          * c)))) :=
  fix zip3 arg_35__ arg_36__ arg_37__
        := match arg_35__ , arg_36__ , arg_37__ with
             | (cons a as_) , (cons b bs) , (cons c cs) => cons (pair (pair a b) c) (zip3 as_
                                                                bs cs)
             | _ , _ , _ => nil
           end.

Definition zipFB {a} {b} {c} {d} : (a *
                                   b -> (c -> d)) -> (a -> (b -> (c -> d))) :=
  fun arg_40__ =>
    match arg_40__ with
      | c => fun arg_41__ arg_42__ arg_43__ =>
               match arg_41__ , arg_42__ , arg_43__ with
                 | x , y , r => c (pair x y) r
               end
    end.

Definition zipWith {a} {b} {c} : (a -> (b -> c)) -> ((list a) -> ((list
                                 b) -> (list c))) :=
  fix zipWith arg_29__ arg_30__ arg_31__
        := let j_33__ :=
             match arg_29__ , arg_30__ , arg_31__ with
               | _f , _as , nil => nil
               | f , (cons a as_) , (cons b bs) => cons (f a b) (zipWith f as_ bs)
               | _ , _ , _ => patternFailure
             end in
           match arg_29__ , arg_30__ , arg_31__ with
             | _f , nil , _bs => nil
             | _ , _ , _ => j_33__
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
     * Coq.Program.Basics.compose GHC.BaseGen.const GHC.BaseGen.foldr GHC.BaseGen.id
     GHC.Num.Int GHC.Num.Num GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.Eq_
     GHC.Prim.Ord GHC.Prim.String GHC.Prim.app GHC.Prim.errorWithoutStackTrace
     GHC.Prim.max GHC.Prim.min GHC.Prim.oneShot GHC.Prim.op_zeze__ GHC.Prim.op_zsze__
     None Some andb bool cons false foldl foldl' list nil option orb pair true
*)
