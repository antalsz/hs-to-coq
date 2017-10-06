(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Coq.Program.Basics.
Require Data.Maybe.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.

(* Converted declarations: *)

Definition deleteBy {a} : (a -> a -> bool) -> a -> list a -> list a :=
  fix deleteBy arg_148__ arg_149__ arg_150__
        := match arg_148__ , arg_149__ , arg_150__ with
             | _ , _ , nil => nil
             | eq , x , (cons y ys) => if eq x y
                                       then ys
                                       else cons y (deleteBy eq x ys)
           end.

Definition deleteFirstsBy {a} : (a -> a -> bool) -> list a -> list a -> list
                                a :=
  fun arg_153__ =>
    match arg_153__ with
      | eq => GHC.Base.foldl (GHC.Base.flip (deleteBy eq))
    end.

Definition delete {a} `{(GHC.Base.Eq_ a)} : a -> list a -> list a :=
  deleteBy GHC.Base.op_zeze__.

Definition op_zrzr__ {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> list a :=
  GHC.Base.foldl (GHC.Base.flip delete).

Infix "\\" := (op_zrzr__) (at level 99).

Notation "'_\\_'" := (op_zrzr__).

Definition dropLength {a} {b} : list a -> list b -> list b :=
  fix dropLength arg_184__ arg_185__
        := match arg_184__ , arg_185__ with
             | nil , y => y
             | _ , nil => nil
             | (cons _ x') , (cons _ y') => dropLength x' y'
           end.

Definition dropLengthMaybe {a} {b} : list a -> list b -> option (list b) :=
  fix dropLengthMaybe arg_179__ arg_180__
        := match arg_179__ , arg_180__ with
             | nil , y => Some y
             | _ , nil => None
             | (cons _ x') , (cons _ y') => dropLengthMaybe x' y'
           end.

Definition isSuffixOf {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> bool :=
  fun arg_188__ arg_189__ =>
    match arg_188__ , arg_189__ with
      | ns , hs => GHC.Base.op_zd__ (Data.Maybe.maybe false GHC.Base.id)
                                    (GHC.Base.op_zgzgze__ (dropLengthMaybe ns hs) (fun delta =>
                                                            GHC.Base.op_zd__ GHC.Base.return_ (GHC.Base.op_zeze__ ns
                                                                                                                  (dropLength
                                                                                                                  delta
                                                                                                                  hs))))
    end.

Definition dropWhileEnd {a} : (a -> bool) -> list a -> list a :=
  fun arg_204__ =>
    match arg_204__ with
      | p => GHC.Base.foldr (fun arg_205__ arg_206__ =>
                              match arg_205__ , arg_206__ with
                                | x , xs => if andb (p x) (GHC.List.null xs)
                                            then nil
                                            else cons x xs
                              end) nil
    end.

Definition elem_by {a} : (a -> a -> bool) -> a -> list a -> bool :=
  fix elem_by arg_158__ arg_159__ arg_160__
        := match arg_158__ , arg_159__ , arg_160__ with
             | _ , _ , nil => false
             | eq , y , (cons x xs) => orb (eq x y) (elem_by eq y xs)
           end.

Definition nubBy {a} : (a -> a -> bool) -> list a -> list a :=
  fun arg_163__ arg_164__ =>
    match arg_163__ , arg_164__ with
      | eq , l => let nubBy' :=
                    fix nubBy' arg_165__ arg_166__
                          := match arg_165__ , arg_166__ with
                               | nil , _ => nil
                               | (cons y ys) , xs => let j_167__ := cons y (nubBy' ys (cons y xs)) in
                                                     if elem_by eq y xs
                                                     then nubBy' ys xs
                                                     else j_167__
                             end in
                  nubBy' l nil
    end.

Definition nub {a} `{(GHC.Base.Eq_ a)} : list a -> list a :=
  nubBy GHC.Base.op_zeze__.

Definition unionBy {a} : (a -> a -> bool) -> list a -> list a -> list a :=
  fun arg_172__ arg_173__ arg_174__ =>
    match arg_172__ , arg_173__ , arg_174__ with
      | eq , xs , ys => Coq.Init.Datatypes.app xs (GHC.Base.foldl (GHC.Base.flip
                                                                  (deleteBy eq)) (nubBy eq ys) xs)
    end.

Definition union {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> list a :=
  unionBy GHC.Base.op_zeze__.

Definition find {a} : (a -> bool) -> list a -> option a :=
  fun arg_196__ =>
    match arg_196__ with
      | p => Coq.Program.Basics.compose Data.Maybe.listToMaybe (GHC.List.filter p)
    end.

Definition genericLength {i} {a} `{(GHC.Num.Num i)} : list a -> i :=
  fix genericLength arg_87__
        := match arg_87__ with
             | nil => GHC.Num.fromInteger 0
             | (cons _ l) => GHC.Num.op_zp__ (GHC.Num.fromInteger 1) (genericLength l)
           end.

Definition insertBy {a} : (a -> a -> comparison) -> a -> list a -> list a :=
  fix insertBy arg_91__ arg_92__ arg_93__
        := match arg_91__ , arg_92__ , arg_93__ with
             | _ , x , nil => cons x nil
             | cmp , x , ((cons y ys') as ys) => let scrut_95__ := cmp x y in
                                                 match scrut_95__ with
                                                   | Gt => cons y (insertBy cmp x ys')
                                                   | _ => cons x ys
                                                 end
           end.

Definition insert {a} `{GHC.Base.Ord a} : a -> list a -> list a :=
  fun arg_101__ arg_102__ =>
    match arg_101__ , arg_102__ with
      | e , ls => insertBy (GHC.Base.compare) e ls
    end.

Definition intersectBy {a} : (a -> a -> bool) -> list a -> list a -> list a :=
  fun arg_142__ arg_143__ arg_144__ =>
    match arg_142__ , arg_143__ , arg_144__ with
      | _ , nil , _ => nil
      | _ , _ , nil => nil
      | eq , xs , ys => Coq.Lists.List.flat_map (fun x =>
                                                  if GHC.List.any (eq x) ys
                                                  then cons x nil
                                                  else nil) xs
    end.

Definition intersect {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> list a :=
  intersectBy GHC.Base.op_zeze__.

Definition isPrefixOf {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> bool :=
  fix isPrefixOf arg_192__ arg_193__
        := match arg_192__ , arg_193__ with
             | nil , _ => true
             | _ , nil => false
             | (cons x xs) , (cons y ys) => andb (GHC.Base.op_zeze__ x y) (isPrefixOf xs ys)
           end.

Definition mapAccumL {acc} {x} {y} : (acc -> x -> acc * y) -> acc -> list
                                     x -> acc * list y :=
  fix mapAccumL arg_120__ arg_121__ arg_122__
        := match arg_120__ , arg_121__ , arg_122__ with
             | _ , s , nil => pair s nil
             | f , s , (cons x xs) => match f s x with
                                        | (pair s' y) => match mapAccumL f s' xs with
                                                           | (pair s'' ys) => pair s'' (cons y ys)
                                                         end
                                      end
           end.

Definition mapAccumLF {acc} {x} {y} : (acc -> x -> acc * y) -> x -> (acc -> acc
                                      * list y) -> acc -> acc * list y :=
  fun arg_105__ =>
    match arg_105__ with
      | f => fun arg_106__ arg_107__ =>
               match arg_106__ , arg_107__ with
                 | x , r => GHC.Base.oneShot (fun arg_108__ =>
                                               match arg_108__ with
                                                 | s => match f s x with
                                                          | (pair s' y) => match r s' with
                                                                             | (pair s'' ys) => pair s'' (cons y ys)
                                                                           end
                                                        end
                                               end)
               end
    end.

Definition nonEmptySubsequences {a} : list a -> list (list a) :=
  fix nonEmptySubsequences arg_18__
        := match arg_18__ with
             | nil => nil
             | (cons x xs) => let f :=
                                fun arg_19__ arg_20__ =>
                                  match arg_19__ , arg_20__ with
                                    | ys , r => cons ys (cons (cons x ys) r)
                                  end in
                              cons (cons x nil) (GHC.Base.foldr f nil (nonEmptySubsequences xs))
           end.

Definition pairWithNil {acc} {y} : acc -> acc * list y :=
  fun arg_117__ => match arg_117__ with | x => pair x nil end.

Definition prependToAll {a} : a -> list a -> list a :=
  fix prependToAll arg_138__ arg_139__
        := match arg_138__ , arg_139__ with
             | _ , nil => nil
             | sep , (cons x xs) => cons sep (cons x (prependToAll sep xs))
           end.

Definition select {a} : (a -> bool) -> a -> list a * list a -> list a * list
                        a :=
  fun arg_128__ arg_129__ arg_130__ =>
    match arg_128__ , arg_129__ , arg_130__ with
      | p , x , (pair ts fs) => let j_131__ := pair ts (cons x fs) in
                                if p x
                                then pair (cons x ts) fs
                                else j_131__
    end.

Definition partition {a} : (a -> bool) -> list a -> list a * list a :=
  fun arg_134__ arg_135__ =>
    match arg_134__ , arg_135__ with
      | p , xs => GHC.Base.foldr (select p) (pair nil nil) xs
    end.

Definition strictGenericLength {i} {b} `{(GHC.Num.Num i)} : list b -> i :=
  fun arg_79__ =>
    match arg_79__ with
      | l => let gl :=
               fix gl arg_80__ arg_81__
                     := match arg_80__ , arg_81__ with
                          | nil , a => a
                          | (cons _ xs) , a => let a' := GHC.Num.op_zp__ a (GHC.Num.fromInteger 1) in
                                               GHC.Base.seq a' (gl xs a')
                        end in
             gl l (GHC.Num.fromInteger 0)
    end.

Definition stripPrefix {a} `{GHC.Base.Eq_ a} : list a -> list a -> option (list
                                                                          a) :=
  fix stripPrefix arg_199__ arg_200__
        := match arg_199__ , arg_200__ with
             | nil , ys => Some ys
             | (cons x xs) , (cons y ys) => if GHC.Base.op_zeze__ x y
                                            then stripPrefix xs ys
                                            else None
             | _ , _ => None
           end.

Definition tailUnwords : GHC.Base.String -> GHC.Base.String :=
  fun arg_8__ => match arg_8__ with | nil => nil | (cons _ xs) => xs end.

Definition unwords : list GHC.Base.String -> GHC.Base.String :=
  fun arg_10__ =>
    match arg_10__ with
      | nil => GHC.Base.hs_string__ ""
      | (cons w ws) => let go :=
                         fix go arg_12__
                               := match arg_12__ with
                                    | nil => GHC.Base.hs_string__ ""
                                    | (cons v vs) => cons (GHC.Char.hs_char__ " ") (Coq.Init.Datatypes.app v (go
                                                                                                           vs))
                                  end in
                       Coq.Init.Datatypes.app w (go ws)
    end.

Definition unwordsFB : GHC.Base.String -> GHC.Base.String -> GHC.Base.String :=
  fun arg_4__ arg_5__ =>
    match arg_4__ , arg_5__ with
      | w , r => cons (GHC.Char.hs_char__ " ") (Coq.Init.Datatypes.app w r)
    end.

Definition unzip4 {a} {b} {c} {d} : list (a * b * c * d) -> list a * list b *
                                    list c * list d :=
  GHC.Base.foldr (fun arg_40__ arg_41__ =>
                   match arg_40__ , arg_41__ with
                     | (pair (pair (pair a b) c) d) , (pair (pair (pair as_ bs) cs) ds) => pair (pair
                                                                                                (pair (cons a as_) (cons
                                                                                                      b bs)) (cons c
                                                                                                                   cs))
                                                                                                (cons d ds)
                   end) (pair (pair (pair nil nil) nil) nil).

Definition unzip5 {a} {b} {c} {d} {e} : list (a * b * c * d * e) -> list a *
                                        list b * list c * list d * list e :=
  GHC.Base.foldr (fun arg_35__ arg_36__ =>
                   match arg_35__ , arg_36__ with
                     | (pair (pair (pair (pair a b) c) d) e) , (pair (pair (pair (pair as_ bs) cs)
                                                                           ds) es) => pair (pair (pair (pair (cons a
                                                                                                                   as_)
                                                                                                             (cons b
                                                                                                                   bs))
                                                                                                       (cons c cs))
                                                                                                 (cons d ds)) (cons e
                                                                                                                    es)
                   end) (pair (pair (pair (pair nil nil) nil) nil) nil).

Definition unzip6 {a} {b} {c} {d} {e} {f} : list (a * b * c * d * e * f) -> list
                                            a * list b * list c * list d * list e * list f :=
  GHC.Base.foldr (fun arg_30__ arg_31__ =>
                   match arg_30__ , arg_31__ with
                     | (pair (pair (pair (pair (pair a b) c) d) e) f) , (pair (pair (pair (pair (pair
                                                                                                as_ bs) cs) ds) es)
                                                                              fs) => pair (pair (pair (pair (pair (cons
                                                                                                                  a as_)
                                                                                                                  (cons
                                                                                                                  b bs))
                                                                                                            (cons c cs))
                                                                                                      (cons d ds)) (cons
                                                                                                e es)) (cons f fs)
                   end) (pair (pair (pair (pair (pair nil nil) nil) nil) nil) nil).

Definition unzip7 {a} {b} {c} {d} {e} {f} {g} : list (a * b * c * d * e * f *
                                                     g) -> list a * list b * list c * list d * list e * list f * list
                                                g :=
  GHC.Base.foldr (fun arg_25__ arg_26__ =>
                   match arg_25__ , arg_26__ with
                     | (pair (pair (pair (pair (pair (pair a b) c) d) e) f) g) , (pair (pair (pair
                                                                                             (pair (pair (pair as_ bs)
                                                                                                         cs) ds) es) fs)
                                                                                       gs) => pair (pair (pair (pair
                                                                                                               (pair
                                                                                                               (pair
                                                                                                               (cons a
                                                                                                                     as_)
                                                                                                               (cons b
                                                                                                                     bs))
                                                                                                               (cons c
                                                                                                                     cs))
                                                                                                               (cons d
                                                                                                                     ds))
                                                                                                               (cons e
                                                                                                                     es))
                                                                                                         (cons f fs))
                                                                                                   (cons g gs)
                   end) (pair (pair (pair (pair (pair (pair nil nil) nil) nil) nil) nil) nil).

Definition zipWith4 {a} {b} {c} {d} {e} : (a -> b -> c -> d -> e) -> list
                                          a -> list b -> list c -> list d -> list e :=
  fix zipWith4 arg_72__ arg_73__ arg_74__ arg_75__ arg_76__
        := match arg_72__ , arg_73__ , arg_74__ , arg_75__ , arg_76__ with
             | z , (cons a as_) , (cons b bs) , (cons c cs) , (cons d ds) => cons (z a b c d)
                                                                                  (zipWith4 z as_ bs cs ds)
             | _ , _ , _ , _ , _ => nil
           end.

Definition zipWith5 {a} {b} {c} {d} {e} {f}
    : (a -> b -> c -> d -> e -> f) -> list a -> list b -> list c -> list d -> list
      e -> list f :=
  fix zipWith5 arg_64__ arg_65__ arg_66__ arg_67__ arg_68__ arg_69__
        := match arg_64__ , arg_65__ , arg_66__ , arg_67__ , arg_68__ , arg_69__ with
             | z , (cons a as_) , (cons b bs) , (cons c cs) , (cons d ds) , (cons e es) =>
               cons (z a b c d e) (zipWith5 z as_ bs cs ds es)
             | _ , _ , _ , _ , _ , _ => nil
           end.

Definition zipWith6 {a} {b} {c} {d} {e} {f} {g}
    : (a -> b -> c -> d -> e -> f -> g) -> list a -> list b -> list c -> list
      d -> list e -> list f -> list g :=
  fix zipWith6 arg_55__ arg_56__ arg_57__ arg_58__ arg_59__ arg_60__ arg_61__
        := match arg_55__
               , arg_56__
               , arg_57__
               , arg_58__
               , arg_59__
               , arg_60__
               , arg_61__ with
             | z , (cons a as_) , (cons b bs) , (cons c cs) , (cons d ds) , (cons e es) ,
               (cons f fs) => cons (z a b c d e f) (zipWith6 z as_ bs cs ds es fs)
             | _ , _ , _ , _ , _ , _ , _ => nil
           end.

Definition zipWith7 {a} {b} {c} {d} {e} {f} {g} {h}
    : (a -> b -> c -> d -> e -> f -> g -> h) -> list a -> list b -> list c -> list
      d -> list e -> list f -> list g -> list h :=
  fix zipWith7 arg_45__ arg_46__ arg_47__ arg_48__ arg_49__ arg_50__ arg_51__
               arg_52__
        := match arg_45__
               , arg_46__
               , arg_47__
               , arg_48__
               , arg_49__
               , arg_50__
               , arg_51__
               , arg_52__ with
             | z , (cons a as_) , (cons b bs) , (cons c cs) , (cons d ds) , (cons e es) ,
               (cons f fs) , (cons g gs) => cons (z a b c d e f g) (zipWith7 z as_ bs cs ds es
                                                 fs gs)
             | _ , _ , _ , _ , _ , _ , _ , _ => nil
           end.

Inductive SnocBuilder a : Type := Mk_SnocBuilder : GHC.Num.Word -> list
                                                   a -> list a -> SnocBuilder a.

Definition toListSB {a} : SnocBuilder a -> list a :=
  fun arg_0__ =>
    match arg_0__ with
      | (Mk_SnocBuilder _ f r) => Coq.Init.Datatypes.app f (GHC.List.reverse r)
    end.

Definition emptySB {a} : SnocBuilder a :=
  Mk_SnocBuilder (GHC.Num.fromInteger 0) nil nil.

(* Unbound variables:
     * Coq.Init.Datatypes.app Coq.Lists.List.flat_map Coq.Program.Basics.compose
     Data.Maybe.listToMaybe Data.Maybe.maybe GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.String GHC.Base.compare GHC.Base.flip GHC.Base.foldl GHC.Base.foldr
     GHC.Base.id GHC.Base.oneShot GHC.Base.op_zd__ GHC.Base.op_zeze__
     GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Base.seq GHC.List.any GHC.List.filter
     GHC.List.null GHC.List.reverse GHC.Num.Num GHC.Num.Word GHC.Num.op_zp__ None
     Some andb bool comparison cons false list nil option orb pair true
*)
