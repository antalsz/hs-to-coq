(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Base.

Module GHC.
  Module Err.
    Axiom error : forall {a}, GHC.Base.String -> a.
  End Err.
End GHC.

(* Converted imports: *)

Require Data.Bits.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.Set.Base.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require Nat.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Size :=
  GHC.Num.Int%type.

Inductive MaybeS a : Type := NothingS : MaybeS a
                          |  JustS : a -> MaybeS a.

Inductive Map k a : Type := Bin : Size -> k -> a -> (Map k a) -> (Map k
                                  a) -> Map k a
                         |  Tip : Map k a.

Arguments NothingS {_}.

Arguments JustS {_} _.

Arguments Bin {_} {_} _ _ _ _ _.

Arguments Tip {_} {_}.
(* Midamble *)

Require Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Fixpoint map_size {a} {b} (s : Map a b) : nat :=
  match s with
  | Tip => 0
  | Bin _ _ _ s1 s2 => 1 + map_size s1 + map_size s2
  end.

(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom patternFailure : forall {a}, a.

Axiom unsafeFix : forall {a}, (a -> a) -> a.

(* Skipping instance Monoid__Map *)

(* Translating `instance forall {k} {v}, forall `{(GHC.Base.Ord k)},
   Data.Semigroup.Semigroup (Data.Map.Base.Map k v)' failed: OOPS! Cannot find
   information for class Qualified "Data.Semigroup" "Semigroup" unsupported *)

(* Translating `instance forall {k} {a}, forall `{Data.Data.Data k}
   `{Data.Data.Data a} `{GHC.Base.Ord k}, Data.Data.Data (Data.Map.Base.Map k a)'
   failed: OOPS! Cannot find information for class Qualified "Data.Data" "Data"
   unsupported *)

(* Translating `instance forall {k} {v}, forall `{(GHC.Base.Ord k)},
   GHC.Exts.IsList (Data.Map.Base.Map k v)' failed: OOPS! Cannot find information
   for class Qualified "GHC.Exts" "IsList" unsupported *)

Local Definition Foldable__Map_elem {inst_k} : forall {a},
                                                 forall `{GHC.Base.Eq_ a}, a -> (Map inst_k) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__ , arg_1__ with
                     | _ , Tip => false
                     | x , Bin _ _ v l r => orb (x GHC.Base.== v) (orb (go x l) (go x r))
                   end in
                 match arg_0__ , arg_1__ with
                   | arg , _ => j_3__
                 end in
    go.

Local Definition Foldable__Map_fold {inst_k} : forall {m},
                                                 forall `{GHC.Base.Monoid m}, (Map inst_k) m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    let fix go arg_0__
              := let j_3__ :=
                   match arg_0__ with
                     | Bin _ _ v l r => GHC.Base.mappend (go l) (GHC.Base.mappend v (go r))
                     | _ => patternFailure
                   end in
                 match arg_0__ with
                   | Tip => GHC.Base.mempty
                   | Bin num_1__ _ v _ _ => if num_1__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                            then v
                                            else j_3__
                 end in
    go.

Local Definition Foldable__Map_foldMap {inst_k} : forall {m} {a},
                                                    forall `{GHC.Base.Monoid m}, (a -> m) -> (Map inst_k) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f t =>
      let fix go arg_0__
                := let j_3__ :=
                     match arg_0__ with
                       | Bin _ _ v l r => GHC.Base.mappend (go l) (GHC.Base.mappend (f v) (go r))
                       | _ => patternFailure
                     end in
                   match arg_0__ with
                     | Tip => GHC.Base.mempty
                     | Bin num_1__ _ v _ _ => if num_1__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                              then f v
                                              else j_3__
                   end in
      go t.

(* Translating `instance forall {k} {a}, forall `{Control.DeepSeq.NFData k}
   `{Control.DeepSeq.NFData a}, Control.DeepSeq.NFData (Data.Map.Base.Map k a)'
   failed: OOPS! Cannot find information for class Qualified "Control.DeepSeq"
   "NFData" unsupported *)

(* Translating `instance forall {k} {e}, forall `{GHC.Base.Ord k}
   `{GHC.Read.Read k} `{GHC.Read.Read e}, GHC.Read.Read (Data.Map.Base.Map k e)'
   failed: OOPS! Cannot find information for class Qualified "GHC.Read" "Read"
   unsupported *)

(* Translating `instance forall {k} {a}, forall `{GHC.Show.Show k}
   `{GHC.Show.Show a}, GHC.Show.Show (Data.Map.Base.Map k a)' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

Definition delta : GHC.Num.Int :=
  GHC.Num.fromInteger 3.

Definition empty {k} {a} : Map k a :=
  Tip.

Definition find {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> a :=
  let fix go arg_0__ arg_1__
            := let j_8__ :=
                 match arg_0__ , arg_1__ with
                   | _ , Tip => GHC.Err.error (GHC.Base.hs_string__
                                              "Map.!: given key is not an element in the map")
                   | k , Bin _ kx x l r => match GHC.Base.compare k kx with
                                             | Lt => go k l
                                             | Gt => go k r
                                             | Eq => x
                                           end
                 end in
               match arg_0__ , arg_1__ with
                 | arg , _ => j_8__
               end in
  go.

Definition op_zn__ {k} {a} `{GHC.Base.Ord k} : Map k a -> k -> a :=
  fun m k => find k m.

Notation "'_!_'" := (op_zn__).

Infix "!" := (_!_) (at level 99).

Definition findMax {k} {a} : Map k a -> (k * a)%type :=
  fix findMax arg_0__
        := match arg_0__ with
             | Bin _ kx x _ Tip => pair kx x
             | Bin _ _ _ _ r => findMax r
             | Tip => GHC.Err.error (GHC.Base.hs_string__
                                    "Map.findMax: empty map has no maximal element")
           end.

Definition findMin {k} {a} : Map k a -> (k * a)%type :=
  fix findMin arg_0__
        := match arg_0__ with
             | Bin _ kx x Tip _ => pair kx x
             | Bin _ _ _ l _ => findMin l
             | Tip => GHC.Err.error (GHC.Base.hs_string__
                                    "Map.findMin: empty map has no minimal element")
           end.

Definition findWithDefault {k} {a} `{GHC.Base.Ord k} : a -> k -> Map k a -> a :=
  let fix go arg_0__ arg_1__ arg_2__
            := let j_8__ :=
                 match arg_0__ , arg_1__ , arg_2__ with
                   | def , _ , Tip => def
                   | def , k , Bin _ kx x l r => match GHC.Base.compare k kx with
                                                   | Lt => go def k l
                                                   | Gt => go def k r
                                                   | Eq => x
                                                 end
                 end in
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , arg , _ => j_8__
               end in
  go.

Definition first {a} {b} {c} : (a -> b) -> (a * c)%type -> (b * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , pair x y => pair (f x) y
    end.

Definition foldMapWithKey {m} {k} {a} `{GHC.Base.Monoid m}
    : (k -> a -> m) -> Map k a -> m :=
  fun f =>
    let fix go arg_0__
              := let j_3__ :=
                   match arg_0__ with
                     | Bin _ k v l r => GHC.Base.mappend (go l) (GHC.Base.mappend (f k v) (go r))
                     | _ => patternFailure
                   end in
                 match arg_0__ with
                   | Tip => GHC.Base.mempty
                   | Bin num_1__ k v _ _ => if num_1__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                            then f k v
                                            else j_3__
                 end in
    go.

Definition foldl {a} {b} {k} : (a -> b -> a) -> a -> Map k b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ _ x l r => go (f (go z' l) x) r
                 end in
    go z.

Local Definition Foldable__Map_foldl {inst_k} : forall {b} {a},
                                                  (b -> a -> b) -> b -> (Map inst_k) a -> b :=
  fun {b} {a} => foldl.

Definition foldl' {a} {b} {k} : (a -> b -> a) -> a -> Map k b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__ , arg_1__ with
                     | z' , Tip => z'
                     | z' , Bin _ _ x l r => go (f (go z' l) x) r
                   end in
                 match arg_0__ , arg_1__ with
                   | arg , _ => j_3__
                 end in
    go z.

Local Definition Foldable__Map_sum {inst_k} : forall {a},
                                                forall `{GHC.Num.Num a}, (Map inst_k) a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.+_ (GHC.Num.fromInteger 0).

Local Definition Foldable__Map_product {inst_k} : forall {a},
                                                    forall `{GHC.Num.Num a}, (Map inst_k) a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.*_ (GHC.Num.fromInteger 1).

Local Definition Foldable__Map_foldl' {inst_k} : forall {b} {a},
                                                   (b -> a -> b) -> b -> (Map inst_k) a -> b :=
  fun {b} {a} => foldl'.

Definition foldlWithKey {a} {k} {b} : (a -> k -> b -> a) -> a -> Map k b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ kx x l r => go (f (go z' l) kx x) r
                 end in
    go z.

Definition toDescList {k} {a} : Map k a -> list (k * a)%type :=
  foldlWithKey (fun xs k x => cons (pair k x) xs) nil.

Definition foldlFB {a} {k} {b} : (a -> k -> b -> a) -> a -> Map k b -> a :=
  foldlWithKey.

Definition foldlWithKey' {a} {k} {b} : (a -> k -> b -> a) -> a -> Map k
                                       b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__ , arg_1__ with
                     | z' , Tip => z'
                     | z' , Bin _ kx x l r => go (f (go z' l) kx x) r
                   end in
                 match arg_0__ , arg_1__ with
                   | arg , _ => j_3__
                 end in
    go z.

Definition foldr {a} {b} {k} : (a -> b -> b) -> b -> Map k a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ _ x l r => go (f x (go z' r)) l
                 end in
    go z.

Definition elems {k} {a} : Map k a -> list a :=
  foldr cons nil.

Local Definition Foldable__Map_toList {inst_k} : forall {a},
                                                   (Map inst_k) a -> list a :=
  fun {a} => elems.

Local Definition Foldable__Map_foldr {inst_k} : forall {a} {b},
                                                  (a -> b -> b) -> b -> (Map inst_k) a -> b :=
  fun {a} {b} => foldr.

Definition foldr' {a} {b} {k} : (a -> b -> b) -> b -> Map k a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__ , arg_1__ with
                     | z' , Tip => z'
                     | z' , Bin _ _ x l r => go (f x (go z' r)) l
                   end in
                 match arg_0__ , arg_1__ with
                   | arg , _ => j_3__
                 end in
    go z.

Local Definition Foldable__Map_foldr' {inst_k} : forall {a} {b},
                                                   (a -> b -> b) -> b -> (Map inst_k) a -> b :=
  fun {a} {b} => foldr'.

Definition foldrWithKey {k} {a} {b} : (k -> a -> b -> b) -> b -> Map k a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ kx x l r => go (f kx x (go z' r)) l
                 end in
    go z.

Definition keys {k} {a} : Map k a -> list k :=
  foldrWithKey (fun arg_0__ arg_1__ arg_2__ =>
                 match arg_0__ , arg_1__ , arg_2__ with
                   | k , _ , ks => cons k ks
                 end) nil.

Definition toAscList {k} {a} : Map k a -> list (k * a)%type :=
  foldrWithKey (fun k x xs => cons (pair k x) xs) nil.

Definition toList {k} {a} : Map k a -> list (k * a)%type :=
  toAscList.

Definition assocs {k} {a} : Map k a -> list (k * a)%type :=
  fun m => toAscList m.

Local Definition Ord__Map_compare {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
                                  `{GHC.Base.Ord inst_v} : (Map inst_k inst_v) -> (Map inst_k
                                                           inst_v) -> comparison :=
  fun m1 m2 => GHC.Base.compare (toAscList m1) (toAscList m2).

Local Definition Ord__Map_op_zg__ {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
                                  `{GHC.Base.Ord inst_v} : (Map inst_k inst_v) -> (Map inst_k inst_v) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Map_compare x y) Gt.

Local Definition Ord__Map_op_zgze__ {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
                                    `{GHC.Base.Ord inst_v} : (Map inst_k inst_v) -> (Map inst_k inst_v) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Map_compare x y) Lt.

Local Definition Ord__Map_op_zl__ {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
                                  `{GHC.Base.Ord inst_v} : (Map inst_k inst_v) -> (Map inst_k inst_v) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Map_compare x y) Lt.

Local Definition Ord__Map_op_zlze__ {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
                                    `{GHC.Base.Ord inst_v} : (Map inst_k inst_v) -> (Map inst_k inst_v) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Map_compare x y) Gt.

Local Definition Ord__Map_max {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
                              `{GHC.Base.Ord inst_v} : (Map inst_k inst_v) -> (Map inst_k inst_v) -> (Map
                                                       inst_k inst_v) :=
  fun x y => if Ord__Map_op_zlze__ x y : bool then y else x.

Local Definition Ord__Map_min {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
                              `{GHC.Base.Ord inst_v} : (Map inst_k inst_v) -> (Map inst_k inst_v) -> (Map
                                                       inst_k inst_v) :=
  fun x y => if Ord__Map_op_zlze__ x y : bool then x else y.

Definition foldrFB {k} {a} {b} : (k -> a -> b -> b) -> b -> Map k a -> b :=
  foldrWithKey.

Definition foldrWithKey' {k} {a} {b} : (k -> a -> b -> b) -> b -> Map k
                                       a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__ , arg_1__ with
                     | z' , Tip => z'
                     | z' , Bin _ kx x l r => go (f kx x (go z' r)) l
                   end in
                 match arg_0__ , arg_1__ with
                   | arg , _ => j_3__
                 end in
    go z.

Definition fromSet {k} {a} : (k -> a) -> Data.Set.Base.Set_ k -> Map k a :=
  fix fromSet arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Data.Set.Base.Tip => Tip
             | f , Data.Set.Base.Bin sz x l r => Bin sz x (f x) (fromSet f l) (fromSet f r)
           end.

Definition keysSet {k} {a} : Map k a -> Data.Set.Base.Set_ k :=
  fix keysSet arg_0__
        := match arg_0__ with
             | Tip => Data.Set.Base.Tip
             | Bin sz kx _ l r => Data.Set.Base.Bin sz kx (keysSet l) (keysSet r)
           end.

Definition lookup {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> option a :=
  let fix go arg_0__ arg_1__
            := let j_8__ :=
                 match arg_0__ , arg_1__ with
                   | _ , Tip => None
                   | k , Bin _ kx x l r => match GHC.Base.compare k kx with
                                             | Lt => go k l
                                             | Gt => go k r
                                             | Eq => Some x
                                           end
                 end in
               match arg_0__ , arg_1__ with
                 | arg , _ => j_8__
               end in
  go.

Definition trimLookupLo {k} {a} `{GHC.Base.Ord k} : k -> MaybeS k -> Map k
                                                    a -> (option a * Map k a)%type :=
  fun lk0 mhk0 t0 =>
    let go :=
      fun arg_0__ arg_1__ arg_2__ =>
        match arg_0__ , arg_1__ , arg_2__ with
          | lk , NothingS , t => let greater {k} {a} `{GHC.Base.Ord k} : k -> Map k
                                                                         a -> prod (option a) (Map k a) :=
                                   fix greater arg_3__ arg_4__
                                         := match arg_3__ , arg_4__ with
                                              | lo , (Bin _ kx x l r as t') => match GHC.Base.compare lo kx with
                                                                                 | Lt => pair (lookup lo l) t'
                                                                                 | Eq => (pair (Some x) r)
                                                                                 | Gt => greater lo r
                                                                               end
                                              | _ , Tip => (pair None Tip)
                                            end in
                                 greater lk t
          | lk , JustS hk , t => let lesser {k} {a} `{GHC.Base.Ord k} : k -> Map k
                                                                        a -> Map k a :=
                                   fix lesser arg_14__ arg_15__
                                         := let j_16__ := match arg_14__ , arg_15__ with | _ , t' => t' end in
                                            match arg_14__ , arg_15__ with
                                              | hi , Bin _ k _ l _ => if k GHC.Base.>= hi : bool
                                                                      then lesser hi l
                                                                      else j_16__
                                              | _ , _ => j_16__
                                            end in
                                 let middle {k} {a} `{GHC.Base.Ord k} : k -> k -> Map k a -> prod (option a) (Map
                                                                                                             k a) :=
                                   fix middle arg_19__ arg_20__ arg_21__
                                         := match arg_19__ , arg_20__ , arg_21__ with
                                              | lo , hi , (Bin _ kx x l r as t') => match GHC.Base.compare lo kx with
                                                                                      | Lt => if kx GHC.Base.< hi : bool
                                                                                              then pair (lookup lo l) t'
                                                                                              else middle lo hi l
                                                                                      | Eq => pair (Some x) (lesser hi
                                                                                                   r)
                                                                                      | Gt => middle lo hi r
                                                                                    end
                                              | _ , _ , Tip => (pair None Tip)
                                            end in
                                 middle lk hk t
        end in
    id GHC.Base.$ go lk0 mhk0 t0.

Definition lookupGE {k} {v} `{GHC.Base.Ord k} : k -> Map k v -> option (k *
                                                                       v)%type :=
  let fix goJust arg_0__ arg_1__ arg_2__ arg_3__
            := let j_11__ :=
                 match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                   | _ , kx' , x' , Tip => Some (pair kx' x')
                   | k , kx' , x' , Bin _ kx x l r => match GHC.Base.compare k kx with
                                                        | Lt => goJust k kx x l
                                                        | Eq => Some (pair kx x)
                                                        | Gt => goJust k kx' x' r
                                                      end
                 end in
               match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                 | arg , _ , _ , _ => j_11__
               end in
  let fix goNothing arg_13__ arg_14__
            := let j_21__ :=
                 match arg_13__ , arg_14__ with
                   | _ , Tip => None
                   | k , Bin _ kx x l r => match GHC.Base.compare k kx with
                                             | Lt => goJust k kx x l
                                             | Eq => Some (pair kx x)
                                             | Gt => goNothing k r
                                           end
                 end in
               match arg_13__ , arg_14__ with
                 | arg , _ => j_21__
               end in
  goNothing.

Definition lookupGT {k} {v} `{GHC.Base.Ord k} : k -> Map k v -> option (k *
                                                                       v)%type :=
  let fix goJust arg_0__ arg_1__ arg_2__ arg_3__
            := let j_7__ :=
                 match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                   | _ , kx' , x' , Tip => Some (pair kx' x')
                   | k , kx' , x' , Bin _ kx x l r => if k GHC.Base.< kx : bool
                                                      then goJust k kx x l
                                                      else goJust k kx' x' r
                 end in
               match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                 | arg , _ , _ , _ => j_7__
               end in
  let fix goNothing arg_9__ arg_10__
            := let j_13__ :=
                 match arg_9__ , arg_10__ with
                   | _ , Tip => None
                   | k , Bin _ kx x l r => if k GHC.Base.< kx : bool
                                           then goJust k kx x l
                                           else goNothing k r
                 end in
               match arg_9__ , arg_10__ with
                 | arg , _ => j_13__
               end in
  goNothing.

Definition lookupLE {k} {v} `{GHC.Base.Ord k} : k -> Map k v -> option (k *
                                                                       v)%type :=
  let fix goJust arg_0__ arg_1__ arg_2__ arg_3__
            := let j_11__ :=
                 match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                   | _ , kx' , x' , Tip => Some (pair kx' x')
                   | k , kx' , x' , Bin _ kx x l r => match GHC.Base.compare k kx with
                                                        | Lt => goJust k kx' x' l
                                                        | Eq => Some (pair kx x)
                                                        | Gt => goJust k kx x r
                                                      end
                 end in
               match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                 | arg , _ , _ , _ => j_11__
               end in
  let fix goNothing arg_13__ arg_14__
            := let j_21__ :=
                 match arg_13__ , arg_14__ with
                   | _ , Tip => None
                   | k , Bin _ kx x l r => match GHC.Base.compare k kx with
                                             | Lt => goNothing k l
                                             | Eq => Some (pair kx x)
                                             | Gt => goJust k kx x r
                                           end
                 end in
               match arg_13__ , arg_14__ with
                 | arg , _ => j_21__
               end in
  goNothing.

Definition lookupLT {k} {v} `{GHC.Base.Ord k} : k -> Map k v -> option (k *
                                                                       v)%type :=
  let fix goJust arg_0__ arg_1__ arg_2__ arg_3__
            := let j_7__ :=
                 match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                   | _ , kx' , x' , Tip => Some (pair kx' x')
                   | k , kx' , x' , Bin _ kx x l r => if k GHC.Base.<= kx : bool
                                                      then goJust k kx' x' l
                                                      else goJust k kx x r
                 end in
               match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                 | arg , _ , _ , _ => j_7__
               end in
  let fix goNothing arg_9__ arg_10__
            := let j_13__ :=
                 match arg_9__ , arg_10__ with
                   | _ , Tip => None
                   | k , Bin _ kx x l r => if k GHC.Base.<= kx : bool
                                           then goNothing k l
                                           else goJust k kx x r
                 end in
               match arg_9__ , arg_10__ with
                 | arg , _ => j_13__
               end in
  goNothing.

Definition map {a} {b} {k} : (a -> b) -> Map k a -> Map k b :=
  fix map arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | f , Bin sx kx x l r => Bin sx kx (f x) (map f l) (map f r)
           end.

Local Definition Functor__Map_fmap {inst_k} : forall {a} {b},
                                                (a -> b) -> (Map inst_k) a -> (Map inst_k) b :=
  fun {a} {b} => fun f m => map f m.

Local Definition Functor__Map_op_zlzd__ {inst_k} : forall {a} {b},
                                                     a -> (Map inst_k) b -> (Map inst_k) a :=
  fun {a} {b} => fun x => Functor__Map_fmap (GHC.Base.const x).

Program Instance Functor__Map {k} : GHC.Base.Functor (Map k) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Map_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Map_fmap |}.

Definition mapAccumL {a} {k} {b} {c} : (a -> k -> b -> (a * c)%type) -> a -> Map
                                       k b -> (a * Map k c)%type :=
  fix mapAccumL arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | _ , a , Tip => pair a Tip
             | f , a , Bin sx kx x l r => match mapAccumL f a l with
                                            | pair a1 l' => match f a1 kx x with
                                                              | pair a2 x' => match mapAccumL f a2 r with
                                                                                | pair a3 r' => pair a3 (Bin sx kx x' l'
                                                                                                     r')
                                                                              end
                                                            end
                                          end
           end.

Definition mapAccumWithKey {a} {k} {b} {c} : (a -> k -> b -> (a *
                                             c)%type) -> a -> Map k b -> (a * Map k c)%type :=
  fun f a t => mapAccumL f a t.

Definition mapAccum {a} {b} {c} {k} : (a -> b -> (a * c)%type) -> a -> Map k
                                      b -> (a * Map k c)%type :=
  fun f a m =>
    mapAccumWithKey (fun arg_0__ arg_1__ arg_2__ =>
                      match arg_0__ , arg_1__ , arg_2__ with
                        | a' , _ , x' => f a' x'
                      end) a m.

Definition mapAccumRWithKey {a} {k} {b} {c} : (a -> k -> b -> (a *
                                              c)%type) -> a -> Map k b -> (a * Map k c)%type :=
  fix mapAccumRWithKey arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | _ , a , Tip => pair a Tip
             | f , a , Bin sx kx x l r => match mapAccumRWithKey f a r with
                                            | pair a1 r' => match f a1 kx x with
                                                              | pair a2 x' => match mapAccumRWithKey f a2 l with
                                                                                | pair a3 l' => pair a3 (Bin sx kx x' l'
                                                                                                     r')
                                                                              end
                                                            end
                                          end
           end.

Definition mapKeysMonotonic {k1} {k2} {a} : (k1 -> k2) -> Map k1 a -> Map k2
                                            a :=
  fix mapKeysMonotonic arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | f , Bin sz k x l r => Bin sz (f k) x (mapKeysMonotonic f l) (mapKeysMonotonic
                                                                           f r)
           end.

Definition mapWithKey {k} {a} {b} : (k -> a -> b) -> Map k a -> Map k b :=
  fix mapWithKey arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | f , Bin sx kx x l r => Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r)
           end.

Definition member {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> bool :=
  let fix go arg_0__ arg_1__
            := let j_7__ :=
                 match arg_0__ , arg_1__ with
                   | _ , Tip => false
                   | k , Bin _ kx _ l r => match GHC.Base.compare k kx with
                                             | Lt => go k l
                                             | Gt => go k r
                                             | Eq => true
                                           end
                 end in
               match arg_0__ , arg_1__ with
                 | arg , _ => j_7__
               end in
  go.

Definition notMember {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> bool :=
  fun k m => negb GHC.Base.$ member k m.

Definition node : GHC.Base.String :=
  GHC.Base.hs_string__ "+--".

Definition null {k} {a} : Map k a -> bool :=
  fun arg_0__ => match arg_0__ with | Tip => true | Bin _ _ _ _ _ => false end.

Local Definition Foldable__Map_null {inst_k} : forall {a},
                                                 (Map inst_k) a -> bool :=
  fun {a} => null.

Definition ordered {a} {b} `{GHC.Base.Ord a} : Map a b -> bool :=
  fun t =>
    let fix bounded lo hi t'
              := match t' with
                   | Tip => true
                   | Bin _ kx _ l r => andb (lo kx) (andb (hi kx) (andb (bounded lo (fun arg_0__ =>
                                                                                      arg_0__ GHC.Base.< kx) l) (bounded
                                                                        (fun arg_1__ => arg_1__ GHC.Base.> kx) hi r)))
                 end in
    bounded (GHC.Base.const true) (GHC.Base.const true) t.

Definition ratio : GHC.Num.Int :=
  GHC.Num.fromInteger 2.

Definition singleton {k} {a} : k -> a -> Map k a :=
  fun k x => Bin (GHC.Num.fromInteger 1) k x Tip Tip.

Definition splitRoot {k} {b} : Map k b -> list (Map k b) :=
  fun orig =>
    match orig with
      | Tip => nil
      | Bin _ k v l r => cons l (cons (singleton k v) (cons r nil))
    end.

Definition size {k} {a} : Map k a -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => GHC.Num.fromInteger 0
      | Bin sz _ _ _ _ => sz
    end.

Definition validsize {a} {b} : Map a b -> bool :=
  fun t =>
    let fix realsize t'
              := match t' with
                   | Tip => Some (GHC.Num.fromInteger 0)
                   | Bin sz _ _ l r => match pair (realsize l) (realsize r) with
                                         | pair (Some n) (Some m) => if ((n GHC.Num.+ m) GHC.Num.+ GHC.Num.fromInteger
                                                                        1) GHC.Base.== sz : bool
                                                                     then Some sz
                                                                     else None
                                         | _ => None
                                       end
                 end in
    (realsize t GHC.Base.== Some (size t)).

Definition lookupIndex {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> option
                                                   GHC.Num.Int :=
  let go {k} {a} `{GHC.Base.Ord k} : GHC.Num.Int -> k -> Map k a -> option
                                     GHC.Num.Int :=
    fix go arg_0__ arg_1__ arg_2__
          := let j_9__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , _ , Tip => None
                 | idx , k , Bin _ kx _ l r => match GHC.Base.compare k kx with
                                                 | Lt => go idx k l
                                                 | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ GHC.Num.fromInteger 1) k r
                                                 | Eq => Some GHC.Base.$! (idx GHC.Num.+ size l)
                                               end
               end in
             let j_10__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , arg , _ => j_9__
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => j_10__
             end in
  go (GHC.Num.fromInteger 0).

Definition findIndex {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> GHC.Num.Int :=
  let go {k} {a} `{GHC.Base.Ord k} : GHC.Num.Int -> k -> Map k a -> GHC.Num.Int :=
    fix go arg_0__ arg_1__ arg_2__
          := let j_10__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , _ , Tip => GHC.Err.error (GHC.Base.hs_string__
                                                "Map.findIndex: element is not in the map")
                 | idx , k , Bin _ kx _ l r => match GHC.Base.compare k kx with
                                                 | Lt => go idx k l
                                                 | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ GHC.Num.fromInteger 1) k r
                                                 | Eq => idx GHC.Num.+ size l
                                               end
               end in
             let j_11__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , arg , _ => j_10__
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => j_11__
             end in
  go (GHC.Num.fromInteger 0).

Definition elemAt {k} {a} : GHC.Num.Int -> Map k a -> (k * a)%type :=
  fix elemAt arg_0__ arg_1__
        := let j_10__ :=
             match arg_0__ , arg_1__ with
               | _ , Tip => GHC.Err.error (GHC.Base.hs_string__
                                          "Map.elemAt: index out of range")
               | i , Bin _ kx x l r => let sizeL := size l in
                                       match GHC.Base.compare i sizeL with
                                         | Lt => elemAt i l
                                         | Gt => elemAt ((i GHC.Num.- sizeL) GHC.Num.- GHC.Num.fromInteger 1) r
                                         | Eq => pair kx x
                                       end
             end in
           match arg_0__ , arg_1__ with
             | arg , _ => j_10__
           end.

Definition bin {k} {a} : k -> a -> Map k a -> Map k a -> Map k a :=
  fun k x l r =>
    Bin ((size l GHC.Num.+ size r) GHC.Num.+ GHC.Num.fromInteger 1) k x l r.

Definition balanced {k} {a} : Map k a -> bool :=
  fix balanced t
        := match t with
             | Tip => true
             | Bin _ _ _ l r => andb (orb ((size l GHC.Num.+ size r) GHC.Base.<=
                                          GHC.Num.fromInteger 1) (andb (size l GHC.Base.<= (delta GHC.Num.* size r))
                                                                       (size r GHC.Base.<= (delta GHC.Num.* size l))))
                                     (andb (balanced l) (balanced r))
           end.

Definition valid {k} {a} `{GHC.Base.Ord k} : Map k a -> bool :=
  fun t => andb (balanced t) (andb (ordered t) (validsize t)).

Definition balanceR {k} {a} : k -> a -> Map k a -> Map k a -> Map k a :=
  fun k x l r =>
    match l with
      | Tip => match r with
                 | Tip => Bin (GHC.Num.fromInteger 1) k x Tip Tip
                 | Bin _ _ _ Tip Tip => Bin (GHC.Num.fromInteger 2) k x Tip r
                 | Bin _ rk rx Tip (Bin _ _ _ _ _ as rr) => Bin (GHC.Num.fromInteger 3) rk rx
                                                            (Bin (GHC.Num.fromInteger 1) k x Tip Tip) rr
                 | Bin _ rk rx (Bin _ rlk rlx _ _) Tip => Bin (GHC.Num.fromInteger 3) rlk rlx
                                                          (Bin (GHC.Num.fromInteger 1) k x Tip Tip) (Bin
                                                                                                    (GHC.Num.fromInteger
                                                                                                    1) rk rx Tip Tip)
                 | Bin rs rk rx (Bin rls rlk rlx rll rlr as rl) (Bin rrs _ _ _ _ as rr) => if rls
                                                                                              GHC.Base.< (ratio
                                                                                              GHC.Num.* rrs) : bool
                                                                                           then Bin (GHC.Num.fromInteger
                                                                                                    1 GHC.Num.+ rs) rk
                                                                                                rx (Bin
                                                                                                   (GHC.Num.fromInteger
                                                                                                   1 GHC.Num.+ rls) k x
                                                                                                   Tip rl) rr
                                                                                           else Bin (GHC.Num.fromInteger
                                                                                                    1 GHC.Num.+ rs) rlk
                                                                                                rlx (Bin
                                                                                                    (GHC.Num.fromInteger
                                                                                                    1 GHC.Num.+ size
                                                                                                    rll) k x Tip rll)
                                                                                                (Bin
                                                                                                ((GHC.Num.fromInteger 1
                                                                                                GHC.Num.+ rrs) GHC.Num.+
                                                                                                size rlr) rk rx rlr rr)
               end
      | Bin ls _ _ _ _ => match r with
                            | Tip => Bin (GHC.Num.fromInteger 1 GHC.Num.+ ls) k x l Tip
                            | Bin rs rk rx rl rr => if rs GHC.Base.> (delta GHC.Num.* ls) : bool
                                                    then let scrut_10__ := pair rl rr in
                                                         let j_12__ :=
                                                           match scrut_10__ with
                                                             | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                         "Failure in Data.Map.balanceR")
                                                           end in
                                                         match scrut_10__ with
                                                           | pair (Bin rls rlk rlx rll rlr) (Bin rrs _ _ _ _) => if rls
                                                                                                                    GHC.Base.<
                                                                                                                    (ratio
                                                                                                                    GHC.Num.*
                                                                                                                    rrs) : bool
                                                                                                                 then Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      ls)
                                                                                                                      GHC.Num.+
                                                                                                                      rs)
                                                                                                                      rk
                                                                                                                      rx
                                                                                                                      (Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      ls)
                                                                                                                      GHC.Num.+
                                                                                                                      rls)
                                                                                                                      k
                                                                                                                      x
                                                                                                                      l
                                                                                                                      rl)
                                                                                                                      rr
                                                                                                                 else Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      ls)
                                                                                                                      GHC.Num.+
                                                                                                                      rs)
                                                                                                                      rlk
                                                                                                                      rlx
                                                                                                                      (Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      ls)
                                                                                                                      GHC.Num.+
                                                                                                                      size
                                                                                                                      rll)
                                                                                                                      k
                                                                                                                      x
                                                                                                                      l
                                                                                                                      rll)
                                                                                                                      (Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      rrs)
                                                                                                                      GHC.Num.+
                                                                                                                      size
                                                                                                                      rlr)
                                                                                                                      rk
                                                                                                                      rx
                                                                                                                      rlr
                                                                                                                      rr)
                                                           | _ => j_12__
                                                         end
                                                    else Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) k x l r
                          end
    end.

Definition deleteFindMin {k} {a} : Map k a -> ((k * a)%type * Map k a)%type :=
  fix deleteFindMin t
        := match t with
             | Bin _ k x Tip r => pair (pair k x) r
             | Bin _ k x l r => match deleteFindMin l with
                                  | pair km l' => pair km (balanceR k x l' r)
                                end
             | Tip => pair (GHC.Err.error (GHC.Base.hs_string__
                                          "Map.deleteFindMin: can not return the minimal element of an empty map")) Tip
           end.

Definition minView {k} {a} : Map k a -> option (a * Map k a)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | x => Some (first Data.Tuple.snd GHC.Base.$ deleteFindMin x)
    end.

Definition minViewWithKey {k} {a} : Map k a -> option ((k * a)%type * Map k
                                                      a)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | x => Some (deleteFindMin x)
    end.

Definition deleteMin {k} {a} : Map k a -> Map k a :=
  fix deleteMin arg_0__
        := match arg_0__ with
             | Bin _ _ _ Tip r => r
             | Bin _ kx x l r => balanceR kx x (deleteMin l) r
             | Tip => Tip
           end.

Definition insertMax {k} {a} : k -> a -> Map k a -> Map k a :=
  fix insertMax kx x t
        := match t with
             | Tip => singleton kx x
             | Bin _ ky y l r => balanceR ky y l (insertMax kx x r)
           end.

Definition updateMinWithKey {k} {a} : (k -> a -> option a) -> Map k a -> Map k
                                      a :=
  fix updateMinWithKey arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | f , Bin sx kx x Tip r => match f kx x with
                                          | None => r
                                          | Some x' => Bin sx kx x' Tip r
                                        end
             | f , Bin _ kx x l r => balanceR kx x (updateMinWithKey f l) r
           end.

Definition updateMin {a} {k} : (a -> option a) -> Map k a -> Map k a :=
  fun f m =>
    updateMinWithKey (fun arg_0__ arg_1__ =>
                       match arg_0__ , arg_1__ with
                         | _ , x => f x
                       end) m.

Definition balanceL {k} {a} : k -> a -> Map k a -> Map k a -> Map k a :=
  fun k x l r =>
    match r with
      | Tip => match l with
                 | Tip => Bin (GHC.Num.fromInteger 1) k x Tip Tip
                 | Bin _ _ _ Tip Tip => Bin (GHC.Num.fromInteger 2) k x l Tip
                 | Bin _ lk lx Tip (Bin _ lrk lrx _ _) => Bin (GHC.Num.fromInteger 3) lrk lrx
                                                          (Bin (GHC.Num.fromInteger 1) lk lx Tip Tip) (Bin
                                                                                                      (GHC.Num.fromInteger
                                                                                                      1) k x Tip Tip)
                 | Bin _ lk lx (Bin _ _ _ _ _ as ll) Tip => Bin (GHC.Num.fromInteger 3) lk lx ll
                                                            (Bin (GHC.Num.fromInteger 1) k x Tip Tip)
                 | Bin ls lk lx (Bin lls _ _ _ _ as ll) (Bin lrs lrk lrx lrl lrr as lr) => if lrs
                                                                                              GHC.Base.< (ratio
                                                                                              GHC.Num.* lls) : bool
                                                                                           then Bin (GHC.Num.fromInteger
                                                                                                    1 GHC.Num.+ ls) lk
                                                                                                lx ll (Bin
                                                                                                      (GHC.Num.fromInteger
                                                                                                      1 GHC.Num.+ lrs) k
                                                                                                      x lr Tip)
                                                                                           else Bin (GHC.Num.fromInteger
                                                                                                    1 GHC.Num.+ ls) lrk
                                                                                                lrx (Bin
                                                                                                    ((GHC.Num.fromInteger
                                                                                                    1 GHC.Num.+ lls)
                                                                                                    GHC.Num.+ size lrl)
                                                                                                    lk lx ll lrl) (Bin
                                                                                                                  (GHC.Num.fromInteger
                                                                                                                  1
                                                                                                                  GHC.Num.+
                                                                                                                  size
                                                                                                                  lrr) k
                                                                                                                  x lrr
                                                                                                                  Tip)
               end
      | Bin rs _ _ _ _ => match l with
                            | Tip => Bin (GHC.Num.fromInteger 1 GHC.Num.+ rs) k x Tip r
                            | Bin ls lk lx ll lr => if ls GHC.Base.> (delta GHC.Num.* rs) : bool
                                                    then let scrut_10__ := pair ll lr in
                                                         let j_12__ :=
                                                           match scrut_10__ with
                                                             | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                         "Failure in Data.Map.balanceL")
                                                           end in
                                                         match scrut_10__ with
                                                           | pair (Bin lls _ _ _ _) (Bin lrs lrk lrx lrl lrr) => if lrs
                                                                                                                    GHC.Base.<
                                                                                                                    (ratio
                                                                                                                    GHC.Num.*
                                                                                                                    lls) : bool
                                                                                                                 then Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      ls)
                                                                                                                      GHC.Num.+
                                                                                                                      rs)
                                                                                                                      lk
                                                                                                                      lx
                                                                                                                      ll
                                                                                                                      (Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      rs)
                                                                                                                      GHC.Num.+
                                                                                                                      lrs)
                                                                                                                      k
                                                                                                                      x
                                                                                                                      lr
                                                                                                                      r)
                                                                                                                 else Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      ls)
                                                                                                                      GHC.Num.+
                                                                                                                      rs)
                                                                                                                      lrk
                                                                                                                      lrx
                                                                                                                      (Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      lls)
                                                                                                                      GHC.Num.+
                                                                                                                      size
                                                                                                                      lrl)
                                                                                                                      lk
                                                                                                                      lx
                                                                                                                      ll
                                                                                                                      lrl)
                                                                                                                      (Bin
                                                                                                                      ((GHC.Num.fromInteger
                                                                                                                      1
                                                                                                                      GHC.Num.+
                                                                                                                      rs)
                                                                                                                      GHC.Num.+
                                                                                                                      size
                                                                                                                      lrr)
                                                                                                                      k
                                                                                                                      x
                                                                                                                      lrr
                                                                                                                      r)
                                                           | _ => j_12__
                                                         end
                                                    else Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) k x l r
                          end
    end.

Definition deleteFindMax {k} {a} : Map k a -> ((k * a)%type * Map k a)%type :=
  fix deleteFindMax t
        := match t with
             | Bin _ k x l Tip => pair (pair k x) l
             | Bin _ k x l r => match deleteFindMax r with
                                  | pair km r' => pair km (balanceL k x l r')
                                end
             | Tip => pair (GHC.Err.error (GHC.Base.hs_string__
                                          "Map.deleteFindMax: can not return the maximal element of an empty map")) Tip
           end.

Definition maxView {k} {a} : Map k a -> option (a * Map k a)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | x => Some (first Data.Tuple.snd GHC.Base.$ deleteFindMax x)
    end.

Definition maxViewWithKey {k} {a} : Map k a -> option ((k * a)%type * Map k
                                                      a)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | x => Some (deleteFindMax x)
    end.

Definition deleteMax {k} {a} : Map k a -> Map k a :=
  fix deleteMax arg_0__
        := match arg_0__ with
             | Bin _ _ _ l Tip => l
             | Bin _ kx x l r => balanceL kx x l (deleteMax r)
             | Tip => Tip
           end.

Definition insert {k} {a} `{GHC.Base.Ord k} : k -> a -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k} : k -> a -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__
          := let j_10__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | kx , x , Tip => singleton kx x
                 | kx , x , Bin sz ky y l r => match GHC.Base.compare kx ky with
                                                 | Lt => balanceL ky y (go kx x l) r
                                                 | Gt => balanceR ky y l (go kx x r)
                                                 | Eq => Bin sz kx x l r
                                               end
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => j_10__
             end in
  go.

Definition insertLookupWithKey {k} {a} `{GHC.Base.Ord k}
    : (k -> a -> a -> a) -> k -> a -> Map k a -> (option a * Map k a)%type :=
  let go {k} {a} `{GHC.Base.Ord k} : (k -> a -> a -> a) -> k -> a -> Map k
                                     a -> (option a * Map k a)%type :=
    fix go arg_0__ arg_1__ arg_2__ arg_3__
          := let j_13__ :=
               match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                 | _ , kx , x , Tip => pair None (singleton kx x)
                 | f , kx , x , Bin sy ky y l r => match GHC.Base.compare kx ky with
                                                     | Lt => match go f kx x l with
                                                               | pair found l' => pair found (balanceL ky y l' r)
                                                             end
                                                     | Gt => match go f kx x r with
                                                               | pair found r' => pair found (balanceR ky y l r')
                                                             end
                                                     | Eq => pair (Some y) (Bin sy kx (f kx x y) l r)
                                                   end
               end in
             match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
               | _ , arg , _ , _ => j_13__
             end in
  go.

Definition insertMin {k} {a} : k -> a -> Map k a -> Map k a :=
  fix insertMin kx x t
        := match t with
             | Tip => singleton kx x
             | Bin _ ky y l r => balanceL ky y (insertMin kx x l) r
           end.

Definition insertR {k} {a} `{GHC.Base.Ord k} : k -> a -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k} : k -> a -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__
          := let j_9__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | kx , x , Tip => singleton kx x
                 | kx , x , (Bin _ ky y l r as t) => match GHC.Base.compare kx ky with
                                                       | Lt => balanceL ky y (go kx x l) r
                                                       | Gt => balanceR ky y l (go kx x r)
                                                       | Eq => t
                                                     end
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => j_9__
             end in
  go.

Definition insertWithKey {k} {a} `{GHC.Base.Ord k}
    : (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k} : (k -> a -> a -> a) -> k -> a -> Map k
                                     a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__ arg_3__
          := let j_11__ :=
               match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                 | _ , kx , x , Tip => singleton kx x
                 | f , kx , x , Bin sy ky y l r => match GHC.Base.compare kx ky with
                                                     | Lt => balanceL ky y (go f kx x l) r
                                                     | Gt => balanceR ky y l (go f kx x r)
                                                     | Eq => Bin sy kx (f kx x y) l r
                                                   end
               end in
             match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
               | _ , arg , _ , _ => j_11__
             end in
  go.

Definition fromListWithKey {k} {a} `{GHC.Base.Ord k}
    : (k -> a -> a -> a) -> list (k * a)%type -> Map k a :=
  fun f xs =>
    let ins :=
      fun arg_0__ arg_1__ =>
        match arg_0__ , arg_1__ with
          | t , pair k x => insertWithKey f k x t
        end in
    Data.Foldable.foldl ins empty xs.

Definition fromListWith {k} {a} `{GHC.Base.Ord k} : (a -> a -> a) -> list (k *
                                                                          a)%type -> Map k a :=
  fun f xs =>
    fromListWithKey (fun arg_0__ arg_1__ arg_2__ =>
                      match arg_0__ , arg_1__ , arg_2__ with
                        | _ , x , y => f x y
                      end) xs.

Definition mapKeysWith {k2} {a} {k1} `{GHC.Base.Ord k2}
    : (a -> a -> a) -> (k1 -> k2) -> Map k1 a -> Map k2 a :=
  fun c f =>
    fromListWith c GHC.Base.∘ foldrWithKey (fun k x xs => cons (pair (f k) x) xs)
    nil.

Definition insertWith {k} {a} `{GHC.Base.Ord k} : (a -> a -> a) -> k -> a -> Map
                                                  k a -> Map k a :=
  fun f =>
    insertWithKey (fun arg_0__ arg_1__ arg_2__ =>
                    match arg_0__ , arg_1__ , arg_2__ with
                      | _ , x' , y' => f x' y'
                    end).

Program Fixpoint link {k} {a} (arg_0__ : k) (arg_1__ : a) (arg_2__ : Map k a)
                      (arg_3__ : Map k a) { measure (Nat.add (map_size arg_2__) (map_size
                                                             arg_3__)) } : Map k a :=
match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
  | kx , x , Tip , r => insertMin kx x r
  | kx , x , l , Tip => insertMax kx x l
  | kx , x , (Bin sizeL ky y ly ry as l) , (Bin sizeR kz z lz rz as r) =>
    if (delta GHC.Num.* sizeL) GHC.Base.< sizeR : bool
    then balanceL kz z (link kx x l lz) rz
    else if (delta GHC.Num.* sizeR) GHC.Base.< sizeL : bool
         then balanceR ky y ly (link kx x ry r)
         else bin kx x l r
end.
Solve Obligations with (termination_by_omega).

Definition filterGt {k} {v} `{GHC.Base.Ord k} : MaybeS k -> Map k v -> Map k
                                                v :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | NothingS , t => t
      | JustS b , t => let fix filter' arg_2__ arg_3__
                                 := match arg_2__ , arg_3__ with
                                      | _ , Tip => Tip
                                      | b' , Bin _ kx x l r => match GHC.Base.compare b' kx with
                                                                 | Lt => link kx x (filter' b' l) r
                                                                 | Eq => r
                                                                 | Gt => filter' b' r
                                                               end
                                    end in
                       filter' b t
    end.

Definition filterLt {k} {v} `{GHC.Base.Ord k} : MaybeS k -> Map k v -> Map k
                                                v :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | NothingS , t => t
      | JustS b , t => let fix filter' arg_2__ arg_3__
                                 := match arg_2__ , arg_3__ with
                                      | _ , Tip => Tip
                                      | b' , Bin _ kx x l r => match GHC.Base.compare kx b' with
                                                                 | Lt => link kx x l (filter' b' r)
                                                                 | Eq => l
                                                                 | Gt => filter' b' l
                                                               end
                                    end in
                       filter' b t
    end.

Definition fromDistinctAscList {k} {a} : list (k * a)%type -> Map k a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Tip
      | cons (pair kx0 x0) xs0 => let create :=
                                    unsafeFix (fun create arg_1__ arg_2__ =>
                                                let j_14__ :=
                                                  match arg_1__ , arg_2__ with
                                                    | _ , nil => pair Tip nil
                                                    | s , (cons x' xs' as xs) => if s GHC.Base.== GHC.Num.fromInteger
                                                                                    1 : bool
                                                                                 then match x' with
                                                                                        | pair kx x => pair (Bin
                                                                                                            (GHC.Num.fromInteger
                                                                                                            1) kx x Tip
                                                                                                            Tip) xs'
                                                                                      end
                                                                                 else match create (Data.Bits.shiftR s
                                                                                                                     (GHC.Num.fromInteger
                                                                                                                     1))
                                                                                              xs with
                                                                                        | (pair _ nil as res) => res
                                                                                        | pair l (cons (pair ky y)
                                                                                                       ys) =>
                                                                                          match create (Data.Bits.shiftR
                                                                                                       s
                                                                                                       (GHC.Num.fromInteger
                                                                                                       1)) ys with
                                                                                            | pair r zs => pair (link ky
                                                                                                                y l r)
                                                                                                                zs
                                                                                          end
                                                                                      end
                                                  end in
                                                match arg_1__ , arg_2__ with
                                                  | arg , _ => j_14__
                                                end) in
                                  let go :=
                                    unsafeFix (fun go arg_16__ arg_17__ arg_18__ =>
                                                let j_23__ :=
                                                  match arg_16__ , arg_17__ , arg_18__ with
                                                    | _ , t , nil => t
                                                    | s , l , cons (pair kx x) xs => match create s xs with
                                                                                       | pair r ys => go
                                                                                                      (Data.Bits.shiftL
                                                                                                      s
                                                                                                      (GHC.Num.fromInteger
                                                                                                      1)) (link kx x l
                                                                                                          r) ys
                                                                                     end
                                                  end in
                                                match arg_16__ , arg_17__ , arg_18__ with
                                                  | arg , _ , _ => j_23__
                                                end) in
                                  go (GHC.Num.fromInteger 1 : GHC.Num.Int) (Bin (GHC.Num.fromInteger 1) kx0 x0 Tip
                                                                           Tip) xs0
    end.

Definition fromAscListWithKey {k} {a} `{GHC.Base.Eq_ k}
    : (k -> a -> a -> a) -> list (k * a)%type -> Map k a :=
  fun f xs =>
    let combineEq' :=
      unsafeFix (fun combineEq' arg_0__ arg_1__ =>
                  match arg_0__ , arg_1__ with
                    | z , nil => cons z nil
                    | (pair kz zz as z) , cons (pair kx xx as x) xs' => if kx GHC.Base.== kz : bool
                                                                        then let yy := f kx xx zz in
                                                                             combineEq' (pair kx yy) xs'
                                                                        else cons z (combineEq' x xs')
                  end) in
    let combineEq :=
      fun arg_7__ arg_8__ =>
        match arg_7__ , arg_8__ with
          | _ , xs' => match xs' with
                         | nil => nil
                         | cons x nil => cons x nil
                         | cons x xx => combineEq' x xx
                       end
        end in
    fromDistinctAscList (combineEq f xs).

Definition fromAscList {k} {a} `{GHC.Base.Eq_ k} : list (k * a)%type -> Map k
                                                   a :=
  fun xs =>
    fromAscListWithKey (fun arg_0__ arg_1__ arg_2__ =>
                         match arg_0__ , arg_1__ , arg_2__ with
                           | _ , x , _ => x
                         end) xs.

Definition fromAscListWith {k} {a} `{GHC.Base.Eq_ k} : (a -> a -> a) -> list (k
                                                                             * a)%type -> Map k a :=
  fun f xs =>
    fromAscListWithKey (fun arg_0__ arg_1__ arg_2__ =>
                         match arg_0__ , arg_1__ , arg_2__ with
                           | _ , x , y => f x y
                         end) xs.

Definition fromList {k} {a} `{GHC.Base.Ord k} : list (k * a)%type -> Map k a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Tip
      | cons (pair kx x) nil => Bin (GHC.Num.fromInteger 1) kx x Tip Tip
      | cons (pair kx0 x0) xs0 => let fromList' :=
                                    fun t0 xs =>
                                      let ins :=
                                        fun arg_2__ arg_3__ =>
                                          match arg_2__ , arg_3__ with
                                            | t , pair k x => insert k x t
                                          end in
                                      Data.Foldable.foldl ins t0 xs in
                                  let not_ordered :=
                                    fun arg_7__ arg_8__ =>
                                      match arg_7__ , arg_8__ with
                                        | _ , nil => false
                                        | kx , cons (pair ky _) _ => kx GHC.Base.>= ky
                                      end in
                                  let create :=
                                    unsafeFix (fun create arg_11__ arg_12__ =>
                                                let j_27__ :=
                                                  match arg_11__ , arg_12__ with
                                                    | _ , nil => pair (pair Tip nil) nil
                                                    | s , (cons xp xss as xs) => if s GHC.Base.== GHC.Num.fromInteger
                                                                                    1 : bool
                                                                                 then match xp with
                                                                                        | pair kx x => if not_ordered kx
                                                                                                          xss : bool
                                                                                                       then pair (pair
                                                                                                                 (Bin
                                                                                                                 (GHC.Num.fromInteger
                                                                                                                 1) kx x
                                                                                                                 Tip
                                                                                                                 Tip)
                                                                                                                 nil)
                                                                                                                 xss
                                                                                                       else pair (pair
                                                                                                                 (Bin
                                                                                                                 (GHC.Num.fromInteger
                                                                                                                 1) kx x
                                                                                                                 Tip
                                                                                                                 Tip)
                                                                                                                 xss)
                                                                                                                 nil
                                                                                      end
                                                                                 else match create (Data.Bits.shiftR s
                                                                                                                     (GHC.Num.fromInteger
                                                                                                                     1))
                                                                                              xs with
                                                                                        | (pair (pair _ nil)
                                                                                                _ as res) => res
                                                                                        | pair (pair l (cons (pair ky y)
                                                                                                             nil)) zs =>
                                                                                          pair (pair (insertMax ky y l)
                                                                                                     nil) zs
                                                                                        | pair (pair l (cons (pair ky y)
                                                                                                             yss as ys))
                                                                                               _ => if not_ordered ky
                                                                                                       yss : bool
                                                                                                    then pair (pair l
                                                                                                                    nil)
                                                                                                              ys
                                                                                                    else match create
                                                                                                                 (Data.Bits.shiftR
                                                                                                                 s
                                                                                                                 (GHC.Num.fromInteger
                                                                                                                 1))
                                                                                                                 yss with
                                                                                                           | pair (pair
                                                                                                                  r zs)
                                                                                                                  ws =>
                                                                                                             pair (pair
                                                                                                                  (link
                                                                                                                  ky y l
                                                                                                                  r) zs)
                                                                                                                  ws
                                                                                                         end
                                                                                      end
                                                  end in
                                                match arg_11__ , arg_12__ with
                                                  | arg , _ => j_27__
                                                end) in
                                  let go :=
                                    unsafeFix (fun go arg_29__ arg_30__ arg_31__ =>
                                                let j_39__ :=
                                                  match arg_29__ , arg_30__ , arg_31__ with
                                                    | _ , t , nil => t
                                                    | _ , t , cons (pair kx x) nil => insertMax kx x t
                                                    | s , l , (cons (pair kx x) xss as xs) => if not_ordered kx
                                                                                                 xss : bool
                                                                                              then fromList' l xs
                                                                                              else match create s
                                                                                                           xss with
                                                                                                     | pair (pair r ys)
                                                                                                            nil => go
                                                                                                                   (Data.Bits.shiftL
                                                                                                                   s
                                                                                                                   (GHC.Num.fromInteger
                                                                                                                   1))
                                                                                                                   (link
                                                                                                                   kx x
                                                                                                                   l r)
                                                                                                                   ys
                                                                                                     | pair (pair r _)
                                                                                                            ys =>
                                                                                                       fromList' (link
                                                                                                                 kx x l
                                                                                                                 r) ys
                                                                                                   end
                                                  end in
                                                match arg_29__ , arg_30__ , arg_31__ with
                                                  | arg , _ , _ => j_39__
                                                end) in
                                  if not_ordered kx0 xs0 : bool
                                  then fromList' (Bin (GHC.Num.fromInteger 1) kx0 x0 Tip Tip) xs0
                                  else go (GHC.Num.fromInteger 1 : GHC.Num.Int) (Bin (GHC.Num.fromInteger 1) kx0
                                                                                x0 Tip Tip) xs0
    end.

Definition mapKeys {k2} {k1} {a} `{GHC.Base.Ord k2} : (k1 -> k2) -> Map k1
                                                      a -> Map k2 a :=
  fun f =>
    fromList GHC.Base.∘ foldrWithKey (fun k x xs => cons (pair (f k) x) xs) nil.

Definition split {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> (Map k a * Map k
                                             a)%type :=
  fun k0 t0 =>
    let fix go k t
              := match t with
                   | Tip => (pair Tip Tip)
                   | Bin _ kx x l r => match GHC.Base.compare k kx with
                                         | Lt => match go k l with
                                                   | pair lt gt => pair lt (link kx x gt r)
                                                 end
                                         | Gt => match go k r with
                                                   | pair lt gt => pair (link kx x l lt) gt
                                                 end
                                         | Eq => (pair l r)
                                       end
                 end in
    GHC.Prim.seq k0 (id GHC.Base.$ go k0 t0).

Definition splitLookup {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> (Map k a *
                                                   option a * Map k a)%type :=
  fix splitLookup k t
        := GHC.Prim.seq k (match t with
                          | Tip => pair (pair Tip None) Tip
                          | Bin _ kx x l r => match GHC.Base.compare k kx with
                                                | Lt => match splitLookup k l with
                                                          | pair (pair lt z) gt => let gt' := link kx x gt r in
                                                                                   GHC.Prim.seq gt' (pair (pair lt z)
                                                                                                          gt')
                                                        end
                                                | Gt => match splitLookup k r with
                                                          | pair (pair lt z) gt => let lt' := link kx x l lt in
                                                                                   GHC.Prim.seq lt' (pair (pair lt' z)
                                                                                                          gt)
                                                        end
                                                | Eq => pair (pair l (Some x)) r
                                              end
                        end).

Definition submap' {a} {b} {c} `{GHC.Base.Ord a} : (b -> c -> bool) -> Map a
                                                   b -> Map a c -> bool :=
  fix submap' arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | _ , Tip , _ => true
             | _ , _ , Tip => false
             | f , Bin _ kx x l r , t => match splitLookup kx t with
                                           | pair (pair lt found) gt => match found with
                                                                          | None => false
                                                                          | Some y => andb (f x y) (andb (submap' f l
                                                                                                         lt) (submap' f
                                                                                                         r gt))
                                                                        end
                                         end
           end.

Definition updateMaxWithKey {k} {a} : (k -> a -> option a) -> Map k a -> Map k
                                      a :=
  fix updateMaxWithKey arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | f , Bin sx kx x l Tip => match f kx x with
                                          | None => l
                                          | Some x' => Bin sx kx x' l Tip
                                        end
             | f , Bin _ kx x l r => balanceL kx x l (updateMaxWithKey f r)
           end.

Definition updateMax {a} {k} : (a -> option a) -> Map k a -> Map k a :=
  fun f m =>
    updateMaxWithKey (fun arg_0__ arg_1__ =>
                       match arg_0__ , arg_1__ with
                         | _ , x => f x
                       end) m.

Definition glue {k} {a} : Map k a -> Map k a -> Map k a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Tip , r => r
      | l , Tip => l
      | l , r => if size l GHC.Base.> size r : bool
                 then match deleteFindMax l with
                        | pair (pair km m) l' => balanceR km m l' r
                      end
                 else match deleteFindMin r with
                        | pair (pair km m) r' => balanceL km m l r'
                      end
    end.

Definition delete {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__
          := let j_8__ :=
               match arg_0__ , arg_1__ with
                 | _ , Tip => Tip
                 | k , Bin _ kx x l r => match GHC.Base.compare k kx with
                                           | Lt => balanceR kx x (go k l) r
                                           | Gt => balanceL kx x l (go k r)
                                           | Eq => glue l r
                                         end
               end in
             match arg_0__ , arg_1__ with
               | arg , _ => j_8__
             end in
  go.

Program Fixpoint merge {k} {a} (arg_0__ : Map k a) (arg_1__ : Map k
                                                              a) { measure (Nat.add (map_size arg_0__) (map_size
                                                                                    arg_1__)) } : Map k a :=
match arg_0__ , arg_1__ with
  | Tip , r => r
  | l , Tip => l
  | (Bin sizeL kx x lx rx as l) , (Bin sizeR ky y ly ry as r) => if (delta
                                                                    GHC.Num.* sizeL) GHC.Base.< sizeR : bool
                                                                 then balanceL ky y (merge l ly) ry
                                                                 else if (delta GHC.Num.* sizeR) GHC.Base.< sizeL : bool
                                                                      then balanceR kx x lx (merge rx r)
                                                                      else glue l r
end.
Solve Obligations with (termination_by_omega).

Definition filterWithKey {k} {a} : (k -> a -> bool) -> Map k a -> Map k a :=
  fix filterWithKey arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | p , Bin _ kx x l r => if p kx x : bool
                                     then link kx x (filterWithKey p l) (filterWithKey p r)
                                     else merge (filterWithKey p l) (filterWithKey p r)
           end.

Definition filter {a} {k} : (a -> bool) -> Map k a -> Map k a :=
  fun p m =>
    filterWithKey (fun arg_0__ arg_1__ =>
                    match arg_0__ , arg_1__ with
                      | _ , x => p x
                    end) m.

Definition mapEitherWithKey {k} {a} {b} {c} : (k -> a -> Data.Either.Either b
                                              c) -> Map k a -> (Map k b * Map k c)%type :=
  fun f0 t0 =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | _ , Tip => (pair Tip Tip)
                   | f , Bin _ kx x l r => match go f r with
                                             | pair r1 r2 => match go f l with
                                                               | pair l1 l2 => match f kx x with
                                                                                 | Data.Either.Left y => pair (link kx y
                                                                                                              l1 r1)
                                                                                                              (merge l2
                                                                                                              r2)
                                                                                 | Data.Either.Right z => pair (merge l1
                                                                                                               r1) (link
                                                                                                               kx z l2
                                                                                                               r2)
                                                                               end
                                                             end
                                           end
                 end in
    id GHC.Base.$ go f0 t0.

Definition mapEither {a} {b} {c} {k} : (a -> Data.Either.Either b c) -> Map k
                                       a -> (Map k b * Map k c)%type :=
  fun f m =>
    mapEitherWithKey (fun arg_0__ arg_1__ =>
                       match arg_0__ , arg_1__ with
                         | _ , x => f x
                       end) m.

Definition mapMaybeWithKey {k} {a} {b} : (k -> a -> option b) -> Map k a -> Map
                                         k b :=
  fix mapMaybeWithKey arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | f , Bin _ kx x l r => match f kx x with
                                       | Some y => link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
                                       | None => merge (mapMaybeWithKey f l) (mapMaybeWithKey f r)
                                     end
           end.

Definition mapMaybe {a} {b} {k} : (a -> option b) -> Map k a -> Map k b :=
  fun f =>
    mapMaybeWithKey (fun arg_0__ arg_1__ =>
                      match arg_0__ , arg_1__ with
                        | _ , x => f x
                      end).

Definition partitionWithKey {k} {a} : (k -> a -> bool) -> Map k a -> (Map k a *
                                      Map k a)%type :=
  fun p0 t0 =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                   | _ , Tip => (pair Tip Tip)
                   | p , Bin _ kx x l r => match go p r with
                                             | pair r1 r2 => match go p l with
                                                               | pair l1 l2 => if p kx x : bool
                                                                               then pair (link kx x l1 r1) (merge l2 r2)
                                                                               else pair (merge l1 r1) (link kx x l2 r2)
                                                             end
                                           end
                 end in
    id GHC.Base.$ go p0 t0.

Definition partition {a} {k} : (a -> bool) -> Map k a -> (Map k a * Map k
                               a)%type :=
  fun p m =>
    partitionWithKey (fun arg_0__ arg_1__ =>
                       match arg_0__ , arg_1__ with
                         | _ , x => p x
                       end) m.

Definition updateLookupWithKey {k} {a} `{GHC.Base.Ord k} : (k -> a -> option
                                                           a) -> k -> Map k a -> (option a * Map k a)%type :=
  let go {k} {a} `{GHC.Base.Ord k} : (k -> a -> option a) -> k -> Map k
                                     a -> (option a * Map k a)%type :=
    fix go arg_0__ arg_1__ arg_2__
          := let j_16__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , _ , Tip => pair None Tip
                 | f , k , Bin sx kx x l r => match GHC.Base.compare k kx with
                                                | Lt => match go f k l with
                                                          | pair found l' => pair found (balanceR kx x l' r)
                                                        end
                                                | Gt => match go f k r with
                                                          | pair found r' => pair found (balanceL kx x l r')
                                                        end
                                                | Eq => match f kx x with
                                                          | Some x' => pair (Some x') (Bin sx kx x' l r)
                                                          | None => pair (Some x) (glue l r)
                                                        end
                                              end
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | _ , arg , _ => j_16__
             end in
  go.

Definition updateWithKey {k} {a} `{GHC.Base.Ord k} : (k -> a -> option
                                                     a) -> k -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k} : (k -> a -> option a) -> k -> Map k a -> Map k
                                     a :=
    fix go arg_0__ arg_1__ arg_2__
          := let j_13__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , _ , Tip => Tip
                 | f , k , Bin sx kx x l r => match GHC.Base.compare k kx with
                                                | Lt => balanceR kx x (go f k l) r
                                                | Gt => balanceL kx x l (go f k r)
                                                | Eq => match f kx x with
                                                          | Some x' => Bin sx kx x' l r
                                                          | None => glue l r
                                                        end
                                              end
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | _ , arg , _ => j_13__
             end in
  go.

Definition update {k} {a} `{GHC.Base.Ord k} : (a -> option a) -> k -> Map k
                                              a -> Map k a :=
  fun f =>
    updateWithKey (fun arg_0__ arg_1__ =>
                    match arg_0__ , arg_1__ with
                      | _ , x => f x
                    end).

Definition adjustWithKey {k} {a} `{GHC.Base.Ord k} : (k -> a -> a) -> k -> Map k
                                                     a -> Map k a :=
  fun f => updateWithKey (fun k' x' => Some (f k' x')).

Definition adjust {k} {a} `{GHC.Base.Ord k} : (a -> a) -> k -> Map k a -> Map k
                                              a :=
  fun f =>
    adjustWithKey (fun arg_0__ arg_1__ =>
                    match arg_0__ , arg_1__ with
                      | _ , x => f x
                    end).

Definition deleteAt {k} {a} : GHC.Num.Int -> Map k a -> Map k a :=
  fix deleteAt i t
        := GHC.Prim.seq i (match t with
                          | Tip => GHC.Err.error (GHC.Base.hs_string__ "Map.deleteAt: index out of range")
                          | Bin _ kx x l r => let sizeL := size l in
                                              match GHC.Base.compare i sizeL with
                                                | Lt => balanceR kx x (deleteAt i l) r
                                                | Gt => balanceL kx x l (deleteAt ((i GHC.Num.- sizeL) GHC.Num.-
                                                                                  GHC.Num.fromInteger 1) r)
                                                | Eq => glue l r
                                              end
                        end).

Definition isProperSubmapOfBy {k} {a} {b} `{GHC.Base.Ord k}
    : (a -> b -> bool) -> Map k a -> Map k b -> bool :=
  fun f t1 t2 => andb (size t1 GHC.Base.< size t2) (submap' f t1 t2).

Definition isProperSubmapOf {k} {a} `{GHC.Base.Ord k} `{GHC.Base.Eq_ a} : Map k
                                                                          a -> Map k a -> bool :=
  fun m1 m2 => isProperSubmapOfBy _GHC.Base.==_ m1 m2.

Definition isSubmapOfBy {k} {a} {b} `{GHC.Base.Ord k} : (a -> b -> bool) -> Map
                                                        k a -> Map k b -> bool :=
  fun f t1 t2 => andb (size t1 GHC.Base.<= size t2) (submap' f t1 t2).

Definition isSubmapOf {k} {a} `{GHC.Base.Ord k} `{GHC.Base.Eq_ a} : Map k
                                                                    a -> Map k a -> bool :=
  fun m1 m2 => isSubmapOfBy _GHC.Base.==_ m1 m2.

Definition updateAt {k} {a} : (k -> a -> option a) -> GHC.Num.Int -> Map k
                              a -> Map k a :=
  fix updateAt f i t
        := GHC.Prim.seq i (match t with
                          | Tip => GHC.Err.error (GHC.Base.hs_string__ "Map.updateAt: index out of range")
                          | Bin sx kx x l r => let sizeL := size l in
                                               match GHC.Base.compare i sizeL with
                                                 | Lt => balanceR kx x (updateAt f i l) r
                                                 | Gt => balanceL kx x l (updateAt f ((i GHC.Num.- sizeL) GHC.Num.-
                                                                                     GHC.Num.fromInteger 1) r)
                                                 | Eq => match f kx x with
                                                           | Some x' => Bin sx kx x' l r
                                                           | None => glue l r
                                                         end
                                               end
                        end).

Definition balance {k} {a} : k -> a -> Map k a -> Map k a -> Map k a :=
  fun k x l r =>
    match l with
      | Tip => match r with
                 | Tip => Bin (GHC.Num.fromInteger 1) k x Tip Tip
                 | Bin _ _ _ Tip Tip => Bin (GHC.Num.fromInteger 2) k x Tip r
                 | Bin _ rk rx Tip (Bin _ _ _ _ _ as rr) => Bin (GHC.Num.fromInteger 3) rk rx
                                                            (Bin (GHC.Num.fromInteger 1) k x Tip Tip) rr
                 | Bin _ rk rx (Bin _ rlk rlx _ _) Tip => Bin (GHC.Num.fromInteger 3) rlk rlx
                                                          (Bin (GHC.Num.fromInteger 1) k x Tip Tip) (Bin
                                                                                                    (GHC.Num.fromInteger
                                                                                                    1) rk rx Tip Tip)
                 | Bin rs rk rx (Bin rls rlk rlx rll rlr as rl) (Bin rrs _ _ _ _ as rr) => if rls
                                                                                              GHC.Base.< (ratio
                                                                                              GHC.Num.* rrs) : bool
                                                                                           then Bin (GHC.Num.fromInteger
                                                                                                    1 GHC.Num.+ rs) rk
                                                                                                rx (Bin
                                                                                                   (GHC.Num.fromInteger
                                                                                                   1 GHC.Num.+ rls) k x
                                                                                                   Tip rl) rr
                                                                                           else Bin (GHC.Num.fromInteger
                                                                                                    1 GHC.Num.+ rs) rlk
                                                                                                rlx (Bin
                                                                                                    (GHC.Num.fromInteger
                                                                                                    1 GHC.Num.+ size
                                                                                                    rll) k x Tip rll)
                                                                                                (Bin
                                                                                                ((GHC.Num.fromInteger 1
                                                                                                GHC.Num.+ rrs) GHC.Num.+
                                                                                                size rlr) rk rx rlr rr)
               end
      | Bin ls lk lx ll lr => match r with
                                | Tip => match pair ll lr with
                                           | pair Tip Tip => Bin (GHC.Num.fromInteger 2) k x l Tip
                                           | pair Tip (Bin _ lrk lrx _ _) => Bin (GHC.Num.fromInteger 3) lrk lrx (Bin
                                                                                                                 (GHC.Num.fromInteger
                                                                                                                 1) lk
                                                                                                                 lx Tip
                                                                                                                 Tip)
                                                                             (Bin (GHC.Num.fromInteger 1) k x Tip Tip)
                                           | pair (Bin _ _ _ _ _) Tip => Bin (GHC.Num.fromInteger 3) lk lx ll (Bin
                                                                                                              (GHC.Num.fromInteger
                                                                                                              1) k x Tip
                                                                                                              Tip)
                                           | pair (Bin lls _ _ _ _) (Bin lrs lrk lrx lrl lrr) => if lrs GHC.Base.<
                                                                                                    (ratio GHC.Num.*
                                                                                                    lls) : bool
                                                                                                 then Bin
                                                                                                      (GHC.Num.fromInteger
                                                                                                      1 GHC.Num.+ ls) lk
                                                                                                      lx ll (Bin
                                                                                                            (GHC.Num.fromInteger
                                                                                                            1 GHC.Num.+
                                                                                                            lrs) k x lr
                                                                                                            Tip)
                                                                                                 else Bin
                                                                                                      (GHC.Num.fromInteger
                                                                                                      1 GHC.Num.+ ls)
                                                                                                      lrk lrx (Bin
                                                                                                              ((GHC.Num.fromInteger
                                                                                                              1
                                                                                                              GHC.Num.+
                                                                                                              lls)
                                                                                                              GHC.Num.+
                                                                                                              size lrl)
                                                                                                              lk lx ll
                                                                                                              lrl) (Bin
                                                                                                                   (GHC.Num.fromInteger
                                                                                                                   1
                                                                                                                   GHC.Num.+
                                                                                                                   size
                                                                                                                   lrr)
                                                                                                                   k x
                                                                                                                   lrr
                                                                                                                   Tip)
                                         end
                                | Bin rs rk rx rl rr => if rs GHC.Base.> (delta GHC.Num.* ls) : bool
                                                        then let scrut_24__ := pair rl rr in
                                                             let j_26__ :=
                                                               match scrut_24__ with
                                                                 | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                             "Failure in Data.Map.balance")
                                                               end in
                                                             match scrut_24__ with
                                                               | pair (Bin rls rlk rlx rll rlr) (Bin rrs _ _ _ _) =>
                                                                 if rls GHC.Base.< (ratio GHC.Num.* rrs) : bool
                                                                 then Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls)
                                                                          GHC.Num.+ rs) rk rx (Bin ((GHC.Num.fromInteger
                                                                                                   1 GHC.Num.+ ls)
                                                                                                   GHC.Num.+ rls) k x l
                                                                                              rl) rr
                                                                 else Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls)
                                                                          GHC.Num.+ rs) rlk rlx (Bin
                                                                                                ((GHC.Num.fromInteger 1
                                                                                                GHC.Num.+ ls) GHC.Num.+
                                                                                                size rll) k x l rll)
                                                                      (Bin ((GHC.Num.fromInteger 1 GHC.Num.+ rrs)
                                                                           GHC.Num.+ size rlr) rk rx rlr rr)
                                                               | _ => j_26__
                                                             end
                                                        else if ls GHC.Base.> (delta GHC.Num.* rs) : bool
                                                             then let scrut_17__ := pair ll lr in
                                                                  let j_19__ :=
                                                                    match scrut_17__ with
                                                                      | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                                  "Failure in Data.Map.balance")
                                                                    end in
                                                                  match scrut_17__ with
                                                                    | pair (Bin lls _ _ _ _) (Bin lrs lrk lrx lrl
                                                                                                  lrr) => if lrs
                                                                                                             GHC.Base.<
                                                                                                             (ratio
                                                                                                             GHC.Num.*
                                                                                                             lls) : bool
                                                                                                          then Bin
                                                                                                               ((GHC.Num.fromInteger
                                                                                                               1
                                                                                                               GHC.Num.+
                                                                                                               ls)
                                                                                                               GHC.Num.+
                                                                                                               rs) lk lx
                                                                                                               ll (Bin
                                                                                                                  ((GHC.Num.fromInteger
                                                                                                                  1
                                                                                                                  GHC.Num.+
                                                                                                                  rs)
                                                                                                                  GHC.Num.+
                                                                                                                  lrs) k
                                                                                                                  x lr
                                                                                                                  r)
                                                                                                          else Bin
                                                                                                               ((GHC.Num.fromInteger
                                                                                                               1
                                                                                                               GHC.Num.+
                                                                                                               ls)
                                                                                                               GHC.Num.+
                                                                                                               rs) lrk
                                                                                                               lrx (Bin
                                                                                                                   ((GHC.Num.fromInteger
                                                                                                                   1
                                                                                                                   GHC.Num.+
                                                                                                                   lls)
                                                                                                                   GHC.Num.+
                                                                                                                   size
                                                                                                                   lrl)
                                                                                                                   lk lx
                                                                                                                   ll
                                                                                                                   lrl)
                                                                                                               (Bin
                                                                                                               ((GHC.Num.fromInteger
                                                                                                               1
                                                                                                               GHC.Num.+
                                                                                                               rs)
                                                                                                               GHC.Num.+
                                                                                                               size lrr)
                                                                                                               k x lrr
                                                                                                               r)
                                                                    | _ => j_19__
                                                                  end
                                                             else Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+
                                                                      rs) k x l r
                              end
    end.

Definition alter {k} {a} `{GHC.Base.Ord k} : (option a -> option a) -> k -> Map
                                             k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k} : (option a -> option a) -> k -> Map k a -> Map
                                     k a :=
    fix go arg_0__ arg_1__ arg_2__
          := let j_17__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | f , k , Tip => match f None with
                                    | None => Tip
                                    | Some x => singleton k x
                                  end
                 | f , k , Bin sx kx x l r => match GHC.Base.compare k kx with
                                                | Lt => balance kx x (go f k l) r
                                                | Gt => balance kx x l (go f k r)
                                                | Eq => match f (Some x) with
                                                          | Some x' => Bin sx kx x' l r
                                                          | None => glue l r
                                                        end
                                              end
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | _ , arg , _ => j_17__
             end in
  go.

Local Definition Foldable__Map_length {inst_k} : forall {a},
                                                   (Map inst_k) a -> GHC.Num.Int :=
  fun {a} => size.

Program Instance Foldable__Map {k} : Data.Foldable.Foldable (Map k) := fun _
                                                                           k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Map_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Map_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Map_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Map_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Map_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Map_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Map_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Map_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Map_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Map_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Map_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Map_toList |}.

Local Definition Eq___Map_op_zeze__ {inst_k} {inst_a} `{GHC.Base.Eq_ inst_k}
                                    `{GHC.Base.Eq_ inst_a} : (Map inst_k inst_a) -> (Map inst_k inst_a) -> bool :=
  fun t1 t2 =>
    andb (size t1 GHC.Base.== size t2) (toAscList t1 GHC.Base.== toAscList t2).

Local Definition Eq___Map_op_zsze__ {inst_k} {inst_a} `{GHC.Base.Eq_ inst_k}
                                    `{GHC.Base.Eq_ inst_a} : (Map inst_k inst_a) -> (Map inst_k inst_a) -> bool :=
  fun x y => negb (Eq___Map_op_zeze__ x y).

Program Instance Eq___Map {k} {a} `{GHC.Base.Eq_ k} `{GHC.Base.Eq_ a}
  : GHC.Base.Eq_ (Map k a) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Map_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Map_op_zsze__ |}.

Program Instance Ord__Map {k} {v} `{GHC.Base.Ord k} `{GHC.Base.Ord v}
  : GHC.Base.Ord (Map k v) := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Map_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Map_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Map_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Map_op_zgze__ ;
      GHC.Base.compare__ := Ord__Map_compare ;
      GHC.Base.max__ := Ord__Map_max ;
      GHC.Base.min__ := Ord__Map_min |}.

Definition traverseWithKey {t} {k} {a} {b} `{GHC.Base.Applicative t}
    : (k -> a -> t b) -> Map k a -> t (Map k b) :=
  fun f =>
    let fix go arg_0__
              := let j_3__ :=
                   match arg_0__ with
                     | Bin s k v l r => ((GHC.Base.flip (Bin s k) Data.Functor.<$> go l) GHC.Base.<*>
                                        f k v) GHC.Base.<*> go r
                     | _ => patternFailure
                   end in
                 match arg_0__ with
                   | Tip => GHC.Base.pure Tip
                   | Bin num_1__ k v _ _ => if num_1__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                            then (fun v' => Bin (GHC.Num.fromInteger 1) k v' Tip Tip) Data.Functor.<$> f
                                                 k v
                                            else j_3__
                 end in
    go.

Local Definition Traversable__Map_traverse {inst_k} : forall {f} {a} {b},
                                                        forall `{GHC.Base.Applicative f},
                                                          (a -> f b) -> (Map inst_k) a -> f ((Map inst_k) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun f => traverseWithKey (fun arg_0__ => f).

Local Definition Traversable__Map_sequenceA {inst_k} : forall {f} {a},
                                                         forall `{GHC.Base.Applicative f},
                                                           (Map inst_k) (f a) -> f ((Map inst_k) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Map_traverse GHC.Base.id.

Local Definition Traversable__Map_sequence {inst_k} : forall {m} {a},
                                                        forall `{GHC.Base.Monad m},
                                                          (Map inst_k) (m a) -> m ((Map inst_k) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Map_sequenceA.

Local Definition Traversable__Map_mapM {inst_k} : forall {m} {a} {b},
                                                    forall `{GHC.Base.Monad m},
                                                      (a -> m b) -> (Map inst_k) a -> m ((Map inst_k) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Map_traverse.

Program Instance Traversable__Map {k} : Data.Traversable.Traversable (Map k) :=
  fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Map_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Map_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Map_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Map_traverse |}.

Definition trim {k} {a} `{GHC.Base.Ord k} : MaybeS k -> MaybeS k -> Map k
                                            a -> Map k a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | NothingS , NothingS , t => t
      | JustS lk , NothingS , t => let fix greater arg_3__ arg_4__
                                             := let j_5__ := match arg_3__ , arg_4__ with | _ , t' => t' end in
                                                match arg_3__ , arg_4__ with
                                                  | lo , Bin _ k _ _ r => if k GHC.Base.<= lo : bool
                                                                          then greater lo r
                                                                          else j_5__
                                                  | _ , _ => j_5__
                                                end in
                                   greater lk t
      | NothingS , JustS hk , t => let fix lesser arg_9__ arg_10__
                                             := let j_11__ := match arg_9__ , arg_10__ with | _ , t' => t' end in
                                                match arg_9__ , arg_10__ with
                                                  | hi , Bin _ k _ l _ => if k GHC.Base.>= hi : bool
                                                                          then lesser hi l
                                                                          else j_11__
                                                  | _ , _ => j_11__
                                                end in
                                   lesser hk t
      | JustS lk , JustS hk , t => let fix middle arg_15__ arg_16__ arg_17__
                                             := let j_18__ :=
                                                  match arg_15__ , arg_16__ , arg_17__ with
                                                    | _ , _ , t' => t'
                                                  end in
                                                let j_20__ :=
                                                  match arg_15__ , arg_16__ , arg_17__ with
                                                    | lo , hi , Bin _ k _ l _ => if k GHC.Base.>= hi : bool
                                                                                 then middle lo hi l
                                                                                 else j_18__
                                                    | _ , _ , _ => j_18__
                                                  end in
                                                match arg_15__ , arg_16__ , arg_17__ with
                                                  | lo , hi , Bin _ k _ _ r => if k GHC.Base.<= lo : bool
                                                                               then middle lo hi r
                                                                               else j_20__
                                                  | _ , _ , _ => j_20__
                                                end in
                                   middle lk hk t
    end.

Definition hedgeUnion {a} {b} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Map a
                                                  b -> Map a b -> Map a b :=
  fix hedgeUnion arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | _ , _ , t1 , Tip => t1
             | blo , bhi , Tip , Bin _ kx x l r => link kx x (filterGt blo l) (filterLt bhi
                                                                              r)
             | _ , _ , t1 , Bin _ kx x Tip Tip => insertR kx x t1
             | blo , bhi , Bin _ kx x l r , t2 => let bmi := JustS kx in
                                                  link kx x (hedgeUnion blo bmi l (trim blo bmi t2)) (hedgeUnion bmi bhi
                                                                                                     r (trim bmi bhi
                                                                                                       t2))
           end.

Definition union {k} {a} `{GHC.Base.Ord k} : Map k a -> Map k a -> Map k a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Tip , t2 => t2
      | t1 , Tip => t1
      | t1 , t2 => hedgeUnion NothingS NothingS t1 t2
    end.

Definition unions {k} {a} `{GHC.Base.Ord k} : list (Map k a) -> Map k a :=
  fun ts => Data.Foldable.foldl union empty ts.

Definition hedgeDiff {a} {b} {c} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Map
                                                     a b -> Map a c -> Map a b :=
  fix hedgeDiff arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | _ , _ , Tip , _ => Tip
             | blo , bhi , Bin _ kx x l r , Tip => link kx x (filterGt blo l) (filterLt bhi
                                                                              r)
             | blo , bhi , t , Bin _ kx _ l r => let bmi := JustS kx in
                                                 merge (hedgeDiff blo bmi (trim blo bmi t) l) (hedgeDiff bmi bhi (trim
                                                                                                                 bmi bhi
                                                                                                                 t) r)
           end.

Definition difference {k} {a} {b} `{GHC.Base.Ord k} : Map k a -> Map k b -> Map
                                                      k a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Tip , _ => Tip
      | t1 , Tip => t1
      | t1 , t2 => hedgeDiff NothingS NothingS t1 t2
    end.

Definition op_zrzr__ {k} {a} {b} `{GHC.Base.Ord k} : Map k a -> Map k b -> Map k
                                                     a :=
  fun m1 m2 => difference m1 m2.

Notation "'_\\_'" := (op_zrzr__).

Infix "\\" := (_\\_) (at level 99).

Definition hedgeInt {k} {a} {b} `{GHC.Base.Ord k} : MaybeS k -> MaybeS k -> Map
                                                    k a -> Map k b -> Map k a :=
  fix hedgeInt arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | _ , _ , _ , Tip => Tip
             | _ , _ , Tip , _ => Tip
             | blo , bhi , Bin _ kx x l r , t2 => let bmi := JustS kx in
                                                  let r' := hedgeInt bmi bhi r (trim bmi bhi t2) in
                                                  let l' := hedgeInt blo bmi l (trim blo bmi t2) in
                                                  if member kx t2 : bool
                                                  then link kx x l' r'
                                                  else merge l' r'
           end.

Definition intersection {k} {a} {b} `{GHC.Base.Ord k} : Map k a -> Map k
                                                        b -> Map k a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Tip , _ => Tip
      | _ , Tip => Tip
      | t1 , t2 => hedgeInt NothingS NothingS t1 t2
    end.

Definition mergeWithKey {k} {a} {b} {c} `{GHC.Base.Ord k}
    : (k -> a -> b -> option c) -> (Map k a -> Map k c) -> (Map k b -> Map k
      c) -> Map k a -> Map k b -> Map k c :=
  fun f g1 g2 =>
    let fix hedgeMerge arg_0__ arg_1__ arg_2__ arg_3__
              := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
                   | _ , _ , t1 , Tip => g1 t1
                   | blo , bhi , Tip , Bin _ kx x l r => g2 GHC.Base.$ link kx x (filterGt blo l)
                                                         (filterLt bhi r)
                   | blo , bhi , Bin _ kx x l r , t2 => let bmi := JustS kx in
                                                        match trimLookupLo kx bhi t2 with
                                                          | pair found trim_t2 => let r' :=
                                                                                    hedgeMerge bmi bhi r trim_t2 in
                                                                                  let l' :=
                                                                                    hedgeMerge blo bmi l (trim blo bmi
                                                                                                         t2) in
                                                                                  match found with
                                                                                    | None => match g1 (singleton kx
                                                                                                       x) with
                                                                                                | Tip => merge l' r'
                                                                                                | Bin _ _ x' Tip Tip =>
                                                                                                  link kx x' l' r'
                                                                                                | _ => GHC.Err.error
                                                                                                       (GHC.Base.hs_string__
                                                                                                       "mergeWithKey: Given function only1 does not fulfil required conditions (see documentation)")
                                                                                              end
                                                                                    | Some x2 => match f kx x x2 with
                                                                                                   | None => merge l' r'
                                                                                                   | Some x' => link kx
                                                                                                                x' l' r'
                                                                                                 end
                                                                                  end
                                                        end
                 end in
    let go :=
      fun arg_24__ arg_25__ =>
        match arg_24__ , arg_25__ with
          | Tip , t2 => g2 t2
          | t1 , Tip => g1 t1
          | t1 , t2 => hedgeMerge NothingS NothingS t1 t2
        end in
    go.

Definition differenceWithKey {k} {a} {b} `{GHC.Base.Ord k}
    : (k -> a -> b -> option a) -> Map k a -> Map k b -> Map k a :=
  fun f t1 t2 => mergeWithKey f GHC.Base.id (GHC.Base.const Tip) t1 t2.

Definition differenceWith {k} {a} {b} `{GHC.Base.Ord k} : (a -> b -> option
                                                          a) -> Map k a -> Map k b -> Map k a :=
  fun f m1 m2 =>
    differenceWithKey (fun arg_0__ arg_1__ arg_2__ =>
                        match arg_0__ , arg_1__ , arg_2__ with
                          | _ , x , y => f x y
                        end) m1 m2.

Definition intersectionWithKey {k} {a} {b} {c} `{GHC.Base.Ord k}
    : (k -> a -> b -> c) -> Map k a -> Map k b -> Map k c :=
  fun f t1 t2 =>
    mergeWithKey (fun k x1 x2 => Some GHC.Base.$ f k x1 x2) (GHC.Base.const Tip)
    (GHC.Base.const Tip) t1 t2.

Definition intersectionWith {k} {a} {b} {c} `{GHC.Base.Ord k}
    : (a -> b -> c) -> Map k a -> Map k b -> Map k c :=
  fun f m1 m2 =>
    intersectionWithKey (fun arg_0__ arg_1__ arg_2__ =>
                          match arg_0__ , arg_1__ , arg_2__ with
                            | _ , x , y => f x y
                          end) m1 m2.

Definition unionWithKey {k} {a} `{GHC.Base.Ord k} : (k -> a -> a -> a) -> Map k
                                                    a -> Map k a -> Map k a :=
  fun f t1 t2 =>
    mergeWithKey (fun k x1 x2 => Some GHC.Base.$ f k x1 x2) GHC.Base.id GHC.Base.id
    t1 t2.

Definition unionWith {k} {a} `{GHC.Base.Ord k} : (a -> a -> a) -> Map k a -> Map
                                                 k a -> Map k a :=
  fun f m1 m2 =>
    unionWithKey (fun arg_0__ arg_1__ arg_2__ =>
                   match arg_0__ , arg_1__ , arg_2__ with
                     | _ , x , y => f x y
                   end) m1 m2.

Definition unionsWith {k} {a} `{GHC.Base.Ord k} : (a -> a -> a) -> list (Map k
                                                                        a) -> Map k a :=
  fun f ts => Data.Foldable.foldl (unionWith f) empty ts.

Definition withBar : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "|  ") bars.

Definition withEmpty : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "   ") bars.

Module Notations.
Notation "'_Data.Map.Base.!_'" := (op_zn__).
Infix "Data.Map.Base.!" := (_!_) (at level 99).
Notation "'_Data.Map.Base.\\_'" := (op_zrzr__).
Infix "Data.Map.Base.\\" := (_\\_) (at level 99).
End Notations.

(* Unbound variables:
     Eq Gt Lt None Some andb bool comparison cons false id list map_size negb nil
     op_zt__ option orb pair prod true Data.Bits.shiftL Data.Bits.shiftR
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Foldable.Foldable
     Data.Foldable.foldl Data.Functor.op_zlzdzg__ Data.Set.Base.Bin
     Data.Set.Base.Set_ Data.Set.Base.Tip Data.Traversable.Traversable Data.Tuple.snd
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.const
     GHC.Base.flip GHC.Base.id GHC.Base.mappend GHC.Base.mempty GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zlztzg__
     GHC.Base.op_zsze__ GHC.Base.pure GHC.Err.error GHC.Num.Int GHC.Num.Num
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq Nat.add
*)
