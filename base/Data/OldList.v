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
Require GHC.Real.
Require GHC.Tuple.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive SnocBuilder a : Type
  := Mk_SnocBuilder : GHC.Num.Word -> list a -> list a -> SnocBuilder a.

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

Require Import Omega.
Lemma mergePairs_length : forall n, forall a cmp (xs : list (list a)) x y, 
      length xs <= n ->                                                                
      length (mergePairs cmp (cons x (cons y xs))) < 2 + n.
induction n. intros; simpl. destruct xs; inversion H. simpl. auto.
intros.
destruct xs.
simpl in *. omega.
destruct xs.
simpl in *. omega.
assert (L : length xs <= n).
simpl in H. omega.
specialize (IHn a cmp xs l l0 L).
simpl in *. omega.
Qed.

Program Fixpoint mergeAll {a0} (cmp: a0 -> a0 -> comparison) 
        (xs : list (list a0)) {measure (length xs) } : list a0 :=
  match xs with
  | nil        => nil
  | cons x nil => x
  | cons x (cons y xs) => mergeAll cmp (mergePairs cmp (cons x (cons y xs)))
  end.
Next Obligation.
simpl.
destruct xs. simpl. auto.
destruct xs. simpl. auto.
apply lt_n_S. 
pose (MP := mergePairs_length (length xs) a0 cmp xs l l0 ltac:(auto)). clearbody MP.
simpl in *.
omega.
Defined.

Definition sortBy {a} (cmp : a -> a -> comparison) (xs : list a): list a :=
     mergeAll cmp (sequences cmp xs).

(* Converted value declarations: *)

Definition deleteBy {a} : (a -> a -> bool) -> a -> list a -> list a :=
  fix deleteBy arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, _, nil => nil
           | eq, x, cons y ys => if eq x y : bool then ys else cons y (deleteBy eq x ys)
           end.

Definition deleteFirstsBy {a}
   : (a -> a -> bool) -> list a -> list a -> list a :=
  fun eq => GHC.Base.foldl (GHC.Base.flip (deleteBy eq)).

Definition delete {a} `{(GHC.Base.Eq_ a)} : a -> list a -> list a :=
  deleteBy _GHC.Base.==_.

Definition op_zrzr__ {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> list a :=
  GHC.Base.foldl (GHC.Base.flip delete).

Notation "'_\\_'" := (op_zrzr__).

Infix "\\" := (_\\_) (at level 99).

Definition dropLength {a} {b} : list a -> list b -> list b :=
  fix dropLength arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, y => y
           | _, nil => nil
           | cons _ x', cons _ y' => dropLength x' y'
           end.

Definition dropLengthMaybe {a} {b} : list a -> list b -> option (list b) :=
  fix dropLengthMaybe arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, y => Some y
           | _, nil => None
           | cons _ x', cons _ y' => dropLengthMaybe x' y'
           end.

Definition isSuffixOf {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> bool :=
  fun ns hs =>
    Data.Maybe.maybe false GHC.Base.id (dropLengthMaybe ns hs GHC.Base.>>=
                                        (fun delta => GHC.Base.return_ (ns GHC.Base.== dropLength delta hs))).

Definition dropWhileEnd {a} : (a -> bool) -> list a -> list a :=
  fun p =>
    GHC.Base.foldr (fun x xs =>
                      if andb (p x) (GHC.List.null xs) : bool
                      then nil
                      else cons x xs) nil.

Definition elem_by {a} : (a -> a -> bool) -> a -> list a -> bool :=
  fix elem_by arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, _, nil => false
           | eq, y, cons x xs => orb (eq x y) (elem_by eq y xs)
           end.

Definition nubBy {a} : (a -> a -> bool) -> list a -> list a :=
  fun eq l =>
    let fix nubBy' arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | nil, _ => nil
                 | cons y ys, xs =>
                     if elem_by eq y xs : bool then nubBy' ys xs else
                     cons y (nubBy' ys (cons y xs))
                 end in
    nubBy' l nil.

Definition nub {a} `{(GHC.Base.Eq_ a)} : list a -> list a :=
  nubBy _GHC.Base.==_.

Definition unionBy {a} : (a -> a -> bool) -> list a -> list a -> list a :=
  fun eq xs ys =>
    Coq.Init.Datatypes.app xs (GHC.Base.foldl (GHC.Base.flip (deleteBy eq)) (nubBy
                                                                             eq ys) xs).

Definition union {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> list a :=
  unionBy _GHC.Base.==_.

Definition emptySB {a} : SnocBuilder a :=
  Mk_SnocBuilder #0 nil nil.

Definition find {a} : (a -> bool) -> list a -> option a :=
  fun p => Data.Maybe.listToMaybe GHC.Base.∘ GHC.List.filter p.

Definition genericDrop {i} {a} `{(GHC.Real.Integral i)}
   : i -> list a -> list a :=
  fix genericDrop arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | n, xs =>
               if n GHC.Base.<= #0 : bool then xs else
               match arg_0__, arg_1__ with
               | _, nil => nil
               | n, cons _ xs => genericDrop (n GHC.Num.- #1) xs
               end
           end.

Definition genericLength {i} {a} `{(GHC.Num.Num i)} : list a -> i :=
  fix genericLength arg_0__
        := match arg_0__ with
           | nil => #0
           | cons _ l => #1 GHC.Num.+ genericLength l
           end.

Definition genericSplitAt {i} {a} `{(GHC.Real.Integral i)}
   : i -> list a -> (list a * list a)%type :=
  fix genericSplitAt arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | n, xs =>
               if n GHC.Base.<= #0 : bool then pair nil xs else
               match arg_0__, arg_1__ with
               | _, nil => pair nil nil
               | n, cons x xs =>
                   let 'pair xs' xs'' := genericSplitAt (n GHC.Num.- #1) xs in
                   pair (cons x xs') xs''
               end
           end.

Definition genericTake {i} {a} `{(GHC.Real.Integral i)}
   : i -> list a -> list a :=
  fix genericTake arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | n, _ =>
               if n GHC.Base.<= #0 : bool then nil else
               match arg_0__, arg_1__ with
               | _, nil => nil
               | n, cons x xs => cons x (genericTake (n GHC.Num.- #1) xs)
               end
           end.

Definition insertBy {a} : (a -> a -> comparison) -> a -> list a -> list a :=
  fix insertBy arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, x, nil => cons x nil
           | cmp, x, (cons y ys' as ys) =>
               match cmp x y with
               | Gt => cons y (insertBy cmp x ys')
               | _ => cons x ys
               end
           end.

Definition insert {a} `{GHC.Base.Ord a} : a -> list a -> list a :=
  fun e ls => insertBy (GHC.Base.compare) e ls.

Definition intersectBy {a} : (a -> a -> bool) -> list a -> list a -> list a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, nil, _ => nil
    | _, _, nil => nil
    | eq, xs, ys =>
        Coq.Lists.List.flat_map (fun x =>
                                   if GHC.List.any (eq x) ys : bool then cons x nil else
                                   nil) xs
    end.

Definition intersect {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> list a :=
  intersectBy _GHC.Base.==_.

Definition isPrefixOf {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> bool :=
  fix isPrefixOf arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, _ => true
           | _, nil => false
           | cons x xs, cons y ys => andb (x GHC.Base.== y) (isPrefixOf xs ys)
           end.

Definition mapAccumL {acc} {x} {y}
   : (acc -> x -> (acc * y)%type) -> acc -> list x -> (acc * list y)%type :=
  fix mapAccumL arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, s, nil => pair s nil
           | f, s, cons x xs =>
               let 'pair s' y := f s x in
               let 'pair s'' ys := mapAccumL f s' xs in
               pair s'' (cons y ys)
           end.

Definition mapAccumLF {acc} {x} {y}
   : (acc -> x -> (acc * y)%type) ->
     x -> (acc -> (acc * list y)%type) -> acc -> (acc * list y)%type :=
  fun f =>
    fun x r =>
      (fun s =>
         let 'pair s' y := f s x in
         let 'pair s'' ys := r s' in
         pair s'' (cons y ys)).

Definition mapAccumR {acc} {x} {y}
   : (acc -> x -> (acc * y)%type) -> acc -> list x -> (acc * list y)%type :=
  fix mapAccumR arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, s, nil => pair s nil
           | f, s, cons x xs =>
               let 'pair s' ys := mapAccumR f s xs in
               let 'pair s'' y := f s' x in
               pair s'' (cons y ys)
           end.

Definition nonEmptySubsequences {a} : list a -> list (list a) :=
  fix nonEmptySubsequences arg_0__
        := match arg_0__ with
           | nil => nil
           | cons x xs =>
               let f := fun ys r => cons ys (cons (cons x ys) r) in
               cons (cons x nil) (GHC.Base.foldr f nil (nonEmptySubsequences xs))
           end.

Definition pairWithNil {acc} {y} : acc -> (acc * list y)%type :=
  fun x => pair x nil.

Definition prependToAll {a} : a -> list a -> list a :=
  fix prependToAll arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => nil
           | sep, cons x xs => cons sep (cons x (prependToAll sep xs))
           end.

Definition select {a}
   : (a -> bool) -> a -> (list a * list a)%type -> (list a * list a)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | p, x, pair ts fs =>
        if p x : bool then pair (cons x ts) fs else
        pair ts (cons x fs)
    end.

Definition partition {a} : (a -> bool) -> list a -> (list a * list a)%type :=
  fun p xs => GHC.Base.foldr (select p) (pair nil nil) xs.

Definition sort {a} `{(GHC.Base.Ord a)} : list a -> list a :=
  sortBy GHC.Base.compare.

Definition sortOn {b} {a} `{GHC.Base.Ord b} : (a -> b) -> list a -> list a :=
  fun f =>
    GHC.Base.map Data.Tuple.snd GHC.Base.∘
    (sortBy (Data.Ord.comparing Data.Tuple.fst) GHC.Base.∘
     GHC.Base.map (fun x => let y := f x in pair y x)).

Definition strictGenericLength {i} {b} `{(GHC.Num.Num i)} : list b -> i :=
  fun l =>
    let fix gl arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | nil, a => a
                 | cons _ xs, a => let a' := a GHC.Num.+ #1 in gl xs a'
                 end in
    gl l #0.

Definition stripPrefix {a} `{GHC.Base.Eq_ a}
   : list a -> list a -> option (list a) :=
  fix stripPrefix arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, ys => Some ys
           | cons x xs, cons y ys =>
               if x GHC.Base.== y : bool then stripPrefix xs ys else
               None
           | _, _ => None
           end.

Definition tailUnwords : GHC.Base.String -> GHC.Base.String :=
  fun arg_0__ => match arg_0__ with | nil => nil | cons _ xs => xs end.

Definition tails {a} : list a -> list (list a) :=
  fun lst =>
    GHC.Base.build' (fun _ =>
                       (fun c n =>
                          let fix tailsGo xs
                                    := c xs (match xs with | nil => n | cons _ xs' => tailsGo xs' end) in
                          tailsGo lst)).

Definition toListSB {a} : SnocBuilder a -> list a :=
  fun arg_0__ =>
    let 'Mk_SnocBuilder _ f r := arg_0__ in
    Coq.Init.Datatypes.app f (GHC.List.reverse r).

Definition unwords : list GHC.Base.String -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => GHC.Base.hs_string__ ""
    | cons w ws =>
        let fix go arg_2__
                  := match arg_2__ with
                     | nil => GHC.Base.hs_string__ ""
                     | cons v vs => cons (GHC.Char.hs_char__ " ") (Coq.Init.Datatypes.app v (go vs))
                     end in
        Coq.Init.Datatypes.app w (go ws)
    end.

Definition unwordsFB : GHC.Base.String -> GHC.Base.String -> GHC.Base.String :=
  fun w r => cons (GHC.Char.hs_char__ " ") (Coq.Init.Datatypes.app w r).

Definition unzip4 {a} {b} {c} {d}
   : list (a * b * c * d)%type -> (list a * list b * list c * list d)%type :=
  GHC.Base.foldr (fun arg_0__ arg_1__ =>
                    match arg_0__, arg_1__ with
                    | pair (pair (pair a b) c) d, pair (pair (pair as_ bs) cs) ds =>
                        pair (pair (pair (cons a as_) (cons b bs)) (cons c cs)) (cons d ds)
                    end) (pair (pair (pair nil nil) nil) nil).

Definition unzip5 {a} {b} {c} {d} {e}
   : list (a * b * c * d * e)%type ->
     (list a * list b * list c * list d * list e)%type :=
  GHC.Base.foldr (fun arg_0__ arg_1__ =>
                    match arg_0__, arg_1__ with
                    | pair (pair (pair (pair a b) c) d) e
                    , pair (pair (pair (pair as_ bs) cs) ds) es =>
                        pair (pair (pair (pair (cons a as_) (cons b bs)) (cons c cs)) (cons d ds)) (cons
                              e es)
                    end) (pair (pair (pair (pair nil nil) nil) nil) nil).

Definition unzip6 {a} {b} {c} {d} {e} {f}
   : list (a * b * c * d * e * f)%type ->
     (list a * list b * list c * list d * list e * list f)%type :=
  GHC.Base.foldr (fun arg_0__ arg_1__ =>
                    match arg_0__, arg_1__ with
                    | pair (pair (pair (pair (pair a b) c) d) e) f
                    , pair (pair (pair (pair (pair as_ bs) cs) ds) es) fs =>
                        pair (pair (pair (pair (pair (cons a as_) (cons b bs)) (cons c cs)) (cons d ds))
                                   (cons e es)) (cons f fs)
                    end) (pair (pair (pair (pair (pair nil nil) nil) nil) nil) nil).

Definition unzip7 {a} {b} {c} {d} {e} {f} {g}
   : list (a * b * c * d * e * f * g)%type ->
     (list a * list b * list c * list d * list e * list f * list g)%type :=
  GHC.Base.foldr (fun arg_0__ arg_1__ =>
                    match arg_0__, arg_1__ with
                    | pair (pair (pair (pair (pair (pair a b) c) d) e) f) g
                    , pair (pair (pair (pair (pair (pair as_ bs) cs) ds) es) fs) gs =>
                        pair (pair (pair (pair (pair (pair (cons a as_) (cons b bs)) (cons c cs)) (cons
                                                d ds)) (cons e es)) (cons f fs)) (cons g gs)
                    end) (pair (pair (pair (pair (pair (pair nil nil) nil) nil) nil) nil) nil).

Definition zipWith4 {a} {b} {c} {d} {e}
   : (a -> b -> c -> d -> e) -> list a -> list b -> list c -> list d -> list e :=
  fix zipWith4 arg_0__ arg_1__ arg_2__ arg_3__ arg_4__
        := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
           | z, cons a as_, cons b bs, cons c cs, cons d ds =>
               cons (z a b c d) (zipWith4 z as_ bs cs ds)
           | _, _, _, _, _ => nil
           end.

Definition zip4 {a} {b} {c} {d}
   : list a -> list b -> list c -> list d -> list (a * b * c * d)%type :=
  zipWith4 GHC.Tuple.pair4.

Definition zipWith5 {a} {b} {c} {d} {e} {f}
   : (a -> b -> c -> d -> e -> f) ->
     list a -> list b -> list c -> list d -> list e -> list f :=
  fix zipWith5 arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__
        := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
           | z, cons a as_, cons b bs, cons c cs, cons d ds, cons e es =>
               cons (z a b c d e) (zipWith5 z as_ bs cs ds es)
           | _, _, _, _, _, _ => nil
           end.

Definition zip5 {a} {b} {c} {d} {e}
   : list a ->
     list b -> list c -> list d -> list e -> list (a * b * c * d * e)%type :=
  zipWith5 GHC.Tuple.pair5.

Definition zipWith6 {a} {b} {c} {d} {e} {f} {g}
   : (a -> b -> c -> d -> e -> f -> g) ->
     list a -> list b -> list c -> list d -> list e -> list f -> list g :=
  fix zipWith6 arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__
        := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__, arg_6__ with
           | z, cons a as_, cons b bs, cons c cs, cons d ds, cons e es, cons f fs =>
               cons (z a b c d e f) (zipWith6 z as_ bs cs ds es fs)
           | _, _, _, _, _, _, _ => nil
           end.

Definition zip6 {a} {b} {c} {d} {e} {f}
   : list a ->
     list b ->
     list c -> list d -> list e -> list f -> list (a * b * c * d * e * f)%type :=
  zipWith6 GHC.Tuple.pair6.

Definition zipWith7 {a} {b} {c} {d} {e} {f} {g} {h}
   : (a -> b -> c -> d -> e -> f -> g -> h) ->
     list a -> list b -> list c -> list d -> list e -> list f -> list g -> list h :=
  fix zipWith7 arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ arg_7__
        := match arg_0__
               , arg_1__
               , arg_2__
               , arg_3__
               , arg_4__
               , arg_5__
               , arg_6__
               , arg_7__ with
           | z
           , cons a as_
           , cons b bs
           , cons c cs
           , cons d ds
           , cons e es
           , cons f fs
           , cons g gs =>
               cons (z a b c d e f g) (zipWith7 z as_ bs cs ds es fs gs)
           | _, _, _, _, _, _, _, _ => nil
           end.

Definition zip7 {a} {b} {c} {d} {e} {f} {g}
   : list a ->
     list b ->
     list c ->
     list d -> list e -> list f -> list g -> list (a * b * c * d * e * f * g)%type :=
  zipWith7 GHC.Tuple.pair7.

Module Notations.
Notation "'_Data.OldList.\\_'" := (op_zrzr__).
Infix "Data.OldList.\\" := (_\\_) (at level 99).
End Notations.

(* External variables:
     Gt None Some andb bool comparison cons false list nil op_zt__ option orb pair
     sortBy true Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Data.Maybe.listToMaybe Data.Maybe.maybe Data.Ord.comparing Data.Tuple.fst
     Data.Tuple.snd GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String GHC.Base.build'
     GHC.Base.compare GHC.Base.flip GHC.Base.foldl GHC.Base.foldr GHC.Base.id
     GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zgzgze__
     GHC.Base.op_zlze__ GHC.Base.return_ GHC.List.any GHC.List.filter GHC.List.null
     GHC.List.reverse GHC.Num.Num GHC.Num.Word GHC.Num.fromInteger GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Real.Integral GHC.Tuple.pair4 GHC.Tuple.pair5
     GHC.Tuple.pair6 GHC.Tuple.pair7
*)
