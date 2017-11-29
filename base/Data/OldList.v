(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Maybe.
Require Data.Ord.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Require GHC.Tuple.

(* Converted type declarations: *)

Inductive SnocBuilder a : Type := Mk_SnocBuilder : GHC.Num.Word -> list
                                                   a -> list a -> SnocBuilder a.

Arguments Mk_SnocBuilder {_} _ _ _.
(* Midamble *)

Fixpoint ascending {a0} (arg_48__: a0 -> a0 -> comparison) (a:a0) (as_:list a0 -> list a0) (bs: list a0)
         {struct bs} : list (list a0)
        := let j_53__ : list (list a0) :=
             match arg_48__ , a , as_ , bs with
               | cmp , a , as_ , bs => cons (as_ (cons a nil))
                                           (match bs with
                                           | cons a (cons b xs) =>  if GHC.Base.eq_comparison (cmp a b) Gt : bool
                                                                   then descending cmp b (cons a nil) xs
                                                                   else ascending cmp b (fun y => cons a y) xs
                                           | xs => cons xs nil
                                           end)
             end in
           match arg_48__ , a , as_ , bs with
             | cmp , a , as_ , cons b bs => if negb (GHC.Base.eq_comparison (cmp a b) Gt)
                                            then ascending cmp b (fun arg_54__ =>
                                                                   match arg_54__ with
                                                                     | ys => as_ (cons a ys)
                                                                   end) bs
                                            else j_53__
             | _ , _ , _ , _ => j_53__
           end
with descending {a0} (arg_40__: a0 -> a0 -> comparison) (a:a0) (arg_42__:list a0) arg_43__
     {struct arg_43__} :=
       let j_45__  : list (list a0) :=
           match arg_40__ , a , arg_42__ , arg_43__ with
           | cmp , a , as_ , bs => cons (cons a as_)
                                       (match bs with
                                        | cons a (cons b xs) =>  if GHC.Base.eq_comparison (cmp a b) Gt : bool
                                                                then descending cmp b (cons a nil) xs
                                                                else ascending cmp b (fun y => cons a y) xs
                                        | xs => cons xs nil
                                        end)
           end in
       match arg_40__ , a , arg_42__ , arg_43__ with
       | cmp , a , as_ , cons b bs => if GHC.Base.eq_comparison (cmp a b) Gt : bool
                                     then descending cmp b (cons a as_) bs
                                     else j_45__
       | _ , _ , _ , _ => j_45__
       end.

Definition sequences {a0} (cmp : a0 -> a0 -> comparison) (ys:list a0) : list (list a0)  :=
    match ys with
      | cons a (cons b xs) =>  if GHC.Base.eq_comparison (cmp a b) Gt : bool
                              then descending cmp b (cons a nil) xs
                              else ascending cmp b (fun y => cons a y) xs
      | xs => cons xs nil
    end.


Fixpoint merge {a0} (cmp: a0 -> a0 -> comparison) (l1:list a0) (l2: list a0) : list a0 :=
  let fix merge_aux l2 :=
      match l1 , l2 with
      | (cons a as' as as_) , (cons b bs' as bs) =>
        if GHC.Base.eq_comparison (cmp a b) Gt : bool
        then cons b (merge_aux bs')
        else cons a (merge cmp as' bs)
      | nil , bs => bs
      | as_ , nil => as_
      end in
  merge_aux l2.

Fixpoint mergePairs {a0} (cmp: a0 -> a0 -> comparison) xs
        := match xs with
             | cons a (cons b xs) => cons (merge cmp a b) (mergePairs cmp xs)
             | xs => xs
           end.

(* TODO: prove that this terminates! *)
Definition mergeAll {a0} (cmp: a0 -> a0 -> comparison) (xs : list (list a0)) : list a0. Admitted.
(*
Program Fixpoint mergeAll {a0} (cmp: a0 -> a0 -> comparison) (xs : list (list a0)) : list a0 :=
  match xs with
  | cons x nil => x
  | xs         => mergeAll cmp (mergePairs cmp xs)
  end.
*)

Definition sortBy {a} (cmp : a -> a -> comparison) (xs : list a): list a :=
     mergeAll cmp (sequences cmp xs).

(* Converted value declarations: *)

Definition deleteBy {a} : (a -> a -> bool) -> a -> list a -> list a :=
  fix deleteBy arg_158__ arg_159__ arg_160__
        := match arg_158__ , arg_159__ , arg_160__ with
             | _ , _ , nil => nil
             | eq , x , cons y ys => if eq x y : bool
                                     then ys
                                     else cons y (deleteBy eq x ys)
           end.

Definition deleteFirstsBy {a} : (a -> a -> bool) -> list a -> list a -> list
                                a :=
  fun eq => GHC.Base.foldl (GHC.Base.flip (deleteBy eq)).

Definition delete {a} `{(GHC.Base.Eq_ a)} : a -> list a -> list a :=
  deleteBy GHC.Base.op_zeze__.

Definition op_zrzr__ {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> list a :=
  GHC.Base.foldl (GHC.Base.flip delete).

Infix "\\" := (op_zrzr__) (at level 99).

Notation "'_\\_'" := (op_zrzr__).

Definition dropLength {a} {b} : list a -> list b -> list b :=
  fix dropLength arg_185__ arg_186__
        := match arg_185__ , arg_186__ with
             | nil , y => y
             | _ , nil => nil
             | cons _ x' , cons _ y' => dropLength x' y'
           end.

Definition dropLengthMaybe {a} {b} : list a -> list b -> option (list b) :=
  fix dropLengthMaybe arg_180__ arg_181__
        := match arg_180__ , arg_181__ with
             | nil , y => Some y
             | _ , nil => None
             | cons _ x' , cons _ y' => dropLengthMaybe x' y'
           end.

Definition isSuffixOf {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> bool :=
  fun ns hs =>
    GHC.Base.op_zd__ (Data.Maybe.maybe false GHC.Base.id) (GHC.Base.op_zgzgze__
                     (dropLengthMaybe ns hs) (fun delta =>
                       GHC.Base.op_zd__ GHC.Base.return_ (GHC.Base.op_zeze__ ns (dropLength delta
                                                                             hs)))).

Definition dropWhileEnd {a} : (a -> bool) -> list a -> list a :=
  fun p =>
    GHC.Base.foldr (fun x xs =>
                     if andb (p x) (GHC.List.null xs) : bool
                     then nil
                     else cons x xs) nil.

Definition elem_by {a} : (a -> a -> bool) -> a -> list a -> bool :=
  fix elem_by arg_166__ arg_167__ arg_168__
        := match arg_166__ , arg_167__ , arg_168__ with
             | _ , _ , nil => false
             | eq , y , cons x xs => orb (eq x y) (elem_by eq y xs)
           end.

Definition nubBy {a} : (a -> a -> bool) -> list a -> list a :=
  fun eq l =>
    let nubBy' :=
      fix nubBy' arg_171__ arg_172__
            := match arg_171__ , arg_172__ with
                 | nil , _ => nil
                 | cons y ys , xs => let j_173__ := cons y (nubBy' ys (cons y xs)) in
                                     if elem_by eq y xs : bool
                                     then nubBy' ys xs
                                     else j_173__
               end in
    nubBy' l nil.

Definition nub {a} `{(GHC.Base.Eq_ a)} : list a -> list a :=
  nubBy GHC.Base.op_zeze__.

Definition unionBy {a} : (a -> a -> bool) -> list a -> list a -> list a :=
  fun eq xs ys =>
    Coq.Init.Datatypes.app xs (GHC.Base.foldl (GHC.Base.flip (deleteBy eq)) (nubBy
                                                                            eq ys) xs).

Definition union {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> list a :=
  unionBy GHC.Base.op_zeze__.

Definition emptySB {a} : SnocBuilder a :=
  Mk_SnocBuilder (GHC.Num.fromInteger 0) nil nil.

Definition find {a} : (a -> bool) -> list a -> option a :=
  fun p => GHC.Base.op_z2218U__ Data.Maybe.listToMaybe (GHC.List.filter p).

Definition genericDrop {i} {a} `{(GHC.Real.Integral i)} : i -> list a -> list
                                                          a :=
  fix genericDrop arg_94__ arg_95__
        := let j_97__ :=
             match arg_94__ , arg_95__ with
               | _ , nil => nil
               | n , cons _ xs => genericDrop (GHC.Num.op_zm__ n (GHC.Num.fromInteger 1)) xs
             end in
           match arg_94__ , arg_95__ with
             | n , xs => if GHC.Base.op_zlze__ n (GHC.Num.fromInteger 0) : bool
                         then xs
                         else j_97__
           end.

Definition genericLength {i} {a} `{(GHC.Num.Num i)} : list a -> i :=
  fix genericLength arg_112__
        := match arg_112__ with
             | nil => GHC.Num.fromInteger 0
             | cons _ l => GHC.Num.op_zp__ (GHC.Num.fromInteger 1) (genericLength l)
           end.

Definition genericSplitAt {i} {a} `{(GHC.Real.Integral i)} : i -> list a -> list
                                                             a * list a :=
  fix genericSplitAt arg_86__ arg_87__
        := let j_91__ :=
             match arg_86__ , arg_87__ with
               | _ , nil => pair nil nil
               | n , cons x xs => match genericSplitAt (GHC.Num.op_zm__ n (GHC.Num.fromInteger
                                                                        1)) xs with
                                    | pair xs' xs'' => pair (cons x xs') xs''
                                  end
             end in
           match arg_86__ , arg_87__ with
             | n , xs => if GHC.Base.op_zlze__ n (GHC.Num.fromInteger 0) : bool
                         then pair nil xs
                         else j_91__
           end.

Definition genericTake {i} {a} `{(GHC.Real.Integral i)} : i -> list a -> list
                                                          a :=
  fix genericTake arg_100__ arg_101__
        := let j_103__ :=
             match arg_100__ , arg_101__ with
               | _ , nil => nil
               | n , cons x xs => cons x (genericTake (GHC.Num.op_zm__ n (GHC.Num.fromInteger
                                                                       1)) xs)
             end in
           match arg_100__ , arg_101__ with
             | n , _ => if GHC.Base.op_zlze__ n (GHC.Num.fromInteger 0) : bool
                        then nil
                        else j_103__
           end.

Definition insertBy {a} : (a -> a -> comparison) -> a -> list a -> list a :=
  fix insertBy arg_116__ arg_117__ arg_118__
        := match arg_116__ , arg_117__ , arg_118__ with
             | _ , x , nil => cons x nil
             | cmp , x , (cons y ys' as ys) => let scrut_120__ := cmp x y in
                                               match scrut_120__ with
                                                 | Gt => cons y (insertBy cmp x ys')
                                                 | _ => cons x ys
                                               end
           end.

Definition insert {a} `{GHC.Base.Ord a} : a -> list a -> list a :=
  fun e ls => insertBy (GHC.Base.compare) e ls.

Definition intersectBy {a} : (a -> a -> bool) -> list a -> list a -> list a :=
  fun arg_152__ arg_153__ arg_154__ =>
    match arg_152__ , arg_153__ , arg_154__ with
      | _ , nil , _ => nil
      | _ , _ , nil => nil
      | eq , xs , ys => Coq.Lists.List.flat_map (fun x =>
                                                  if GHC.List.any (eq x) ys : bool
                                                  then cons x nil
                                                  else nil) xs
    end.

Definition intersect {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> list a :=
  intersectBy GHC.Base.op_zeze__.

Definition isPrefixOf {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> bool :=
  fix isPrefixOf arg_190__ arg_191__
        := match arg_190__ , arg_191__ with
             | nil , _ => true
             | _ , nil => false
             | cons x xs , cons y ys => andb (GHC.Base.op_zeze__ x y) (isPrefixOf xs ys)
           end.

Definition mapAccumL {acc} {x} {y} : (acc -> x -> acc * y) -> acc -> list
                                     x -> acc * list y :=
  fix mapAccumL arg_133__ arg_134__ arg_135__
        := match arg_133__ , arg_134__ , arg_135__ with
             | _ , s , nil => pair s nil
             | f , s , cons x xs => match f s x with
                                      | pair s' y => match mapAccumL f s' xs with
                                                       | pair s'' ys => pair s'' (cons y ys)
                                                     end
                                    end
           end.

Definition mapAccumLF {acc} {x} {y} : (acc -> x -> acc * y) -> x -> (acc -> acc
                                      * list y) -> acc -> acc * list y :=
  fun f =>
    fun x r =>
      GHC.Base.oneShot (fun s =>
                         match f s x with
                           | pair s' y => match r s' with
                                            | pair s'' ys => pair s'' (cons y ys)
                                          end
                         end).

Definition nonEmptySubsequences {a} : list a -> list (list a) :=
  fix nonEmptySubsequences arg_19__
        := match arg_19__ with
             | nil => nil
             | cons x xs => let f := fun ys r => cons ys (cons (cons x ys) r) in
                            cons (cons x nil) (GHC.Base.foldr f nil (nonEmptySubsequences xs))
           end.

Definition pairWithNil {acc} {y} : acc -> acc * list y :=
  fun x => pair x nil.

Definition prependToAll {a} : a -> list a -> list a :=
  fix prependToAll arg_148__ arg_149__
        := match arg_148__ , arg_149__ with
             | _ , nil => nil
             | sep , cons x xs => cons sep (cons x (prependToAll sep xs))
           end.

Definition select {a} : (a -> bool) -> a -> list a * list a -> list a * list
                        a :=
  fun arg_141__ arg_142__ arg_143__ =>
    match arg_141__ , arg_142__ , arg_143__ with
      | p , x , pair ts fs => let j_144__ := pair ts (cons x fs) in
                              if p x : bool
                              then pair (cons x ts) fs
                              else j_144__
    end.

Definition partition {a} : (a -> bool) -> list a -> list a * list a :=
  fun p xs => GHC.Base.foldr (select p) (pair nil nil) xs.

Definition sort {a} `{(GHC.Base.Ord a)} : list a -> list a :=
  sortBy GHC.Base.compare.

Definition sortOn {b} {a} `{GHC.Base.Ord b} : (a -> b) -> list a -> list a :=
  fun f =>
    GHC.Base.op_z2218U__ (GHC.Base.map Data.Tuple.snd) (GHC.Base.op_z2218U__ (sortBy
                                                                             (Data.Ord.comparing Data.Tuple.fst))
                                                                             (GHC.Base.map (fun x =>
                                                                                             let y := f x in
                                                                                             GHC.Prim.seq y (pair y
                                                                                                                  x)))).

Definition strictGenericLength {i} {b} `{(GHC.Num.Num i)} : list b -> i :=
  fun l =>
    let gl :=
      fix gl arg_106__ arg_107__
            := match arg_106__ , arg_107__ with
                 | nil , a => a
                 | cons _ xs , a => let a' := GHC.Num.op_zp__ a (GHC.Num.fromInteger 1) in
                                    GHC.Prim.seq a' (gl xs a')
               end in
    gl l (GHC.Num.fromInteger 0).

Definition stripPrefix {a} `{GHC.Base.Eq_ a} : list a -> list a -> option (list
                                                                          a) :=
  fix stripPrefix arg_195__ arg_196__
        := match arg_195__ , arg_196__ with
             | nil , ys => Some ys
             | cons x xs , cons y ys => if GHC.Base.op_zeze__ x y : bool
                                        then stripPrefix xs ys
                                        else None
             | _ , _ => None
           end.

Definition tailUnwords : GHC.Base.String -> GHC.Base.String :=
  fun arg_5__ => match arg_5__ with | nil => nil | cons _ xs => xs end.

Definition tails {a} : list a -> list (list a) :=
  fun lst =>
    GHC.Base.build (fun c n =>
                     let tailsGo :=
                       fix tailsGo xs
                             := c xs (match xs with | nil => n | cons _ xs' => tailsGo xs' end) in
                     tailsGo lst).

Definition toListSB {a} : SnocBuilder a -> list a :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_SnocBuilder _ f r => Coq.Init.Datatypes.app f (GHC.List.reverse r)
    end.

Definition unwords : list GHC.Base.String -> GHC.Base.String :=
  fun arg_7__ =>
    match arg_7__ with
      | nil => GHC.Base.hs_string__ ""
      | cons w ws => let go :=
                       fix go arg_9__
                             := match arg_9__ with
                                  | nil => GHC.Base.hs_string__ ""
                                  | cons v vs => cons (GHC.Char.hs_char__ " ") (Coq.Init.Datatypes.app v (go vs))
                                end in
                     Coq.Init.Datatypes.app w (go ws)
    end.

Definition unwordsFB : GHC.Base.String -> GHC.Base.String -> GHC.Base.String :=
  fun w r => cons (GHC.Char.hs_char__ " ") (Coq.Init.Datatypes.app w r).

Definition unzip4 {a} {b} {c} {d} : list (a * b * c * d) -> list a * list b *
                                    list c * list d :=
  GHC.Base.foldr (fun arg_43__ arg_44__ =>
                   match arg_43__ , arg_44__ with
                     | pair (pair (pair a b) c) d , pair (pair (pair as_ bs) cs) ds => pair (pair
                                                                                            (pair (cons a as_) (cons b
                                                                                                                     bs))
                                                                                            (cons c cs)) (cons d ds)
                   end) (pair (pair (pair nil nil) nil) nil).

Definition unzip5 {a} {b} {c} {d} {e} : list (a * b * c * d * e) -> list a *
                                        list b * list c * list d * list e :=
  GHC.Base.foldr (fun arg_38__ arg_39__ =>
                   match arg_38__ , arg_39__ with
                     | pair (pair (pair (pair a b) c) d) e , pair (pair (pair (pair as_ bs) cs) ds)
                                                                  es => pair (pair (pair (pair (cons a as_) (cons b bs))
                                                                                         (cons c cs)) (cons d ds)) (cons
                                                                             e es)
                   end) (pair (pair (pair (pair nil nil) nil) nil) nil).

Definition unzip6 {a} {b} {c} {d} {e} {f} : list (a * b * c * d * e * f) -> list
                                            a * list b * list c * list d * list e * list f :=
  GHC.Base.foldr (fun arg_33__ arg_34__ =>
                   match arg_33__ , arg_34__ with
                     | pair (pair (pair (pair (pair a b) c) d) e) f , pair (pair (pair (pair (pair
                                                                                             as_ bs) cs) ds) es) fs =>
                       pair (pair (pair (pair (pair (cons a as_) (cons b bs)) (cons c cs)) (cons d ds))
                                  (cons e es)) (cons f fs)
                   end) (pair (pair (pair (pair (pair nil nil) nil) nil) nil) nil).

Definition unzip7 {a} {b} {c} {d} {e} {f} {g} : list (a * b * c * d * e * f *
                                                     g) -> list a * list b * list c * list d * list e * list f * list
                                                g :=
  GHC.Base.foldr (fun arg_28__ arg_29__ =>
                   match arg_28__ , arg_29__ with
                     | pair (pair (pair (pair (pair (pair a b) c) d) e) f) g , pair (pair (pair (pair
                                                                                                (pair (pair as_ bs) cs)
                                                                                                ds) es) fs) gs => pair
                                                                                                                  (pair
                                                                                                                  (pair
                                                                                                                  (pair
                                                                                                                  (pair
                                                                                                                  (pair
                                                                                                                  (cons
                                                                                                                  a as_)
                                                                                                                  (cons
                                                                                                                  b bs))
                                                                                                                  (cons
                                                                                                                  c cs))
                                                                                                                  (cons
                                                                                                                  d ds))
                                                                                                                  (cons
                                                                                                                  e es))
                                                                                                                  (cons
                                                                                                                  f fs))
                                                                                                                  (cons
                                                                                                                  g gs)
                   end) (pair (pair (pair (pair (pair (pair nil nil) nil) nil) nil) nil) nil).

Definition zipWith4 {a} {b} {c} {d} {e} : (a -> b -> c -> d -> e) -> list
                                          a -> list b -> list c -> list d -> list e :=
  fix zipWith4 arg_75__ arg_76__ arg_77__ arg_78__ arg_79__
        := match arg_75__ , arg_76__ , arg_77__ , arg_78__ , arg_79__ with
             | z , cons a as_ , cons b bs , cons c cs , cons d ds => cons (z a b c d)
                                                                          (zipWith4 z as_ bs cs ds)
             | _ , _ , _ , _ , _ => nil
           end.

Definition zip4 {a} {b} {c} {d} : list a -> list b -> list c -> list d -> list
                                  (a * b * c * d) :=
  zipWith4 GHC.Tuple.op_Z4T__.

Definition zipWith5 {a} {b} {c} {d} {e} {f}
    : (a -> b -> c -> d -> e -> f) -> list a -> list b -> list c -> list d -> list
      e -> list f :=
  fix zipWith5 arg_67__ arg_68__ arg_69__ arg_70__ arg_71__ arg_72__
        := match arg_67__ , arg_68__ , arg_69__ , arg_70__ , arg_71__ , arg_72__ with
             | z , cons a as_ , cons b bs , cons c cs , cons d ds , cons e es => cons (z a b
                                                                                      c d e) (zipWith5 z as_ bs cs ds
                                                                                      es)
             | _ , _ , _ , _ , _ , _ => nil
           end.

Definition zip5 {a} {b} {c} {d} {e} : list a -> list b -> list c -> list
                                      d -> list e -> list (a * b * c * d * e) :=
  zipWith5 GHC.Tuple.op_Z5T__.

Definition zipWith6 {a} {b} {c} {d} {e} {f} {g}
    : (a -> b -> c -> d -> e -> f -> g) -> list a -> list b -> list c -> list
      d -> list e -> list f -> list g :=
  fix zipWith6 arg_58__ arg_59__ arg_60__ arg_61__ arg_62__ arg_63__ arg_64__
        := match arg_58__
               , arg_59__
               , arg_60__
               , arg_61__
               , arg_62__
               , arg_63__
               , arg_64__ with
             | z , cons a as_ , cons b bs , cons c cs , cons d ds , cons e es , cons f fs =>
               cons (z a b c d e f) (zipWith6 z as_ bs cs ds es fs)
             | _ , _ , _ , _ , _ , _ , _ => nil
           end.

Definition zip6 {a} {b} {c} {d} {e} {f} : list a -> list b -> list c -> list
                                          d -> list e -> list f -> list (a * b * c * d * e * f) :=
  zipWith6 GHC.Tuple.op_Z6T__.

Definition zipWith7 {a} {b} {c} {d} {e} {f} {g} {h}
    : (a -> b -> c -> d -> e -> f -> g -> h) -> list a -> list b -> list c -> list
      d -> list e -> list f -> list g -> list h :=
  fix zipWith7 arg_48__ arg_49__ arg_50__ arg_51__ arg_52__ arg_53__ arg_54__
               arg_55__
        := match arg_48__
               , arg_49__
               , arg_50__
               , arg_51__
               , arg_52__
               , arg_53__
               , arg_54__
               , arg_55__ with
             | z , cons a as_ , cons b bs , cons c cs , cons d ds , cons e es , cons f fs ,
               cons g gs => cons (z a b c d e f g) (zipWith7 z as_ bs cs ds es fs gs)
             | _ , _ , _ , _ , _ , _ , _ , _ => nil
           end.

Definition zip7 {a} {b} {c} {d} {e} {f} {g} : list a -> list b -> list c -> list
                                              d -> list e -> list f -> list g -> list (a * b * c * d * e * f * g) :=
  zipWith7 GHC.Tuple.op_Z7T__.

Module Notations.
Infix "Data.OldList.\\" := (op_zrzr__) (at level 99).
Notation "'_Data.OldList.\\_'" := (op_zrzr__).
End Notations.

(* Unbound variables:
     None Some andb bool comparison cons false list nil op_zt__ option orb pair
     sortBy true Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Data.Maybe.listToMaybe Data.Maybe.maybe Data.Ord.comparing Data.Tuple.fst
     Data.Tuple.snd GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String GHC.Base.build
     GHC.Base.compare GHC.Base.flip GHC.Base.foldl GHC.Base.foldr GHC.Base.id
     GHC.Base.map GHC.Base.oneShot GHC.Base.op_z2218U__ GHC.Base.op_zd__
     GHC.Base.op_zeze__ GHC.Base.op_zgzgze__ GHC.Base.op_zlze__ GHC.Base.return_
     GHC.List.any GHC.List.filter GHC.List.null GHC.List.reverse GHC.Num.Num
     GHC.Num.Word GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Prim.seq GHC.Real.Integral
     GHC.Tuple.op_Z4T__ GHC.Tuple.op_Z5T__ GHC.Tuple.op_Z6T__ GHC.Tuple.op_Z7T__
*)
