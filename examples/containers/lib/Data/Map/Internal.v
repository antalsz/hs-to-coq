(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* runIdentity is a record selector and we are still not qualifying those.
   So import everything from the file so that it will be in scope. *)

Require Import Data.Functor.Identity.


(* Converted imports: *)

Require Data.Bits.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Classes.
Require Data.Functor.Identity.
Require Data.Maybe.
Require Data.Set.Internal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require Nat.
Require Utils.Containers.Internal.PtrEquality.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive WhenMatched f k x y z : Type
  := Mk_WhenMatched (matchedKey : k -> x -> y -> f (option z))
   : WhenMatched f k x y z.

Inductive TraceResult a : Type
  := Mk_TraceResult : (option a) -> unit -> TraceResult a.

Inductive StrictTriple a b c : Type
  := Mk_StrictTriple : a -> b -> c -> StrictTriple a b c.

Definition Size :=
  GHC.Num.Int%type.

Definition SimpleWhenMatched :=
  (WhenMatched Data.Functor.Identity.Identity)%type.

Inductive Map k a : Type
  := Bin : Size -> k -> a -> (Map k a) -> (Map k a) -> Map k a
  |  Tip : Map k a.

Inductive MaxView k a : Type := Mk_MaxView : k -> a -> (Map k a) -> MaxView k a.

Inductive MinView k a : Type := Mk_MinView : k -> a -> (Map k a) -> MinView k a.

Inductive WhenMissing f k x y : Type
  := Mk_WhenMissing (missingSubtree : Map k x -> f (Map k y)) (missingKey
    : k -> x -> f (option y))
   : WhenMissing f k x y.

Definition SimpleWhenMissing :=
  (WhenMissing Data.Functor.Identity.Identity)%type.

Inductive AreWeStrict : Type := Strict : AreWeStrict |  Lazy : AreWeStrict.

Inductive Altered k a : Type
  := AltSmaller : (Map k a) -> Altered k a
  |  AltBigger : (Map k a) -> Altered k a
  |  AltAdj : (Map k a) -> Altered k a
  |  AltSame : Altered k a.

Arguments Mk_WhenMatched {_} {_} {_} {_} {_} _.

Arguments Mk_TraceResult {_} _ _.

Arguments Mk_StrictTriple {_} {_} {_} _ _ _.

Arguments Bin {_} {_} _ _ _ _ _.

Arguments Tip {_} {_}.

Arguments Mk_MaxView {_} {_} _ _ _.

Arguments Mk_MinView {_} {_} _ _ _.

Arguments Mk_WhenMissing {_} {_} {_} {_} _ _.

Arguments AltSmaller {_} {_} _.

Arguments AltBigger {_} {_} _.

Arguments AltAdj {_} {_} _.

Arguments AltSame {_} {_}.

Instance Default__AreWeStrict : GHC.Err.Default AreWeStrict :=
  GHC.Err.Build_Default _ Strict.

Definition matchedKey {f} {k} {x} {y} {z} (arg_0__ : WhenMatched f k x y z) :=
  let 'Mk_WhenMatched matchedKey := arg_0__ in
  matchedKey.

Definition missingKey {f} {k} {x} {y} (arg_0__ : WhenMissing f k x y) :=
  let 'Mk_WhenMissing _ missingKey := arg_0__ in
  missingKey.

Definition missingSubtree {f} {k} {x} {y} (arg_0__ : WhenMissing f k x y) :=
  let 'Mk_WhenMissing missingSubtree _ := arg_0__ in
  missingSubtree.
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

Require Import GHC.Err.

Instance Map_Default {k}{v} : Default (Map k v) :=
  Build_Default _ Tip.
Instance AlteredDefault {k}{v} : Default (Altered k v) :=
  Build_Default _ AltSame.

(* This doesn't translate automatically for two reasons:
   it should be a fixpoint.
   it reuses the variable a as both a term and type variable. *)
Fixpoint functor__Map_op_zlzd__ {inst_k} {a} {b} (f: a) (m:(Map inst_k) b):
  (Map inst_k) a :=
      match f, m with
      | _, Tip => Tip
      | f, Bin sx kx _ l r => Bin sx kx f
                                 (functor__Map_op_zlzd__ f l) 
                                 (functor__Map_op_zlzd__ f r)
      end.

(* Converted value declarations: *)

(* Skipping instance Category__WhenMatched *)

(* Skipping instance Applicative__WhenMatched *)

(* Skipping instance Monad__WhenMatched *)

(* Skipping instance Category__WhenMissing *)

(* Skipping instance Applicative__WhenMissing *)

(* Skipping instance Monad__WhenMissing *)

(* Skipping instance Data__Map of class Data *)

(* Skipping instance IsList__Map of class IsList *)

(* Skipping instance Eq1__Map *)

(* Skipping instance Ord1__Map *)

(* Translating `instance Show2__Map' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Show2" unsupported *)

(* Skipping instance Show1__Map of class Show1 *)

(* Skipping instance Read1__Map of class Read1 *)

Local Definition Functor__Map_op_zlzd__ {k : Type} {a : Type} {b : Type} :=
  (@functor__Map_op_zlzd__ k a b).

Local Definition Foldable__Map_foldMap {inst_k}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Map inst_k) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f t =>
      let fix go arg_0__
                := match arg_0__ with
                   | Tip => GHC.Base.mempty
                   | Bin num_1__ _ v _ _ =>
                       if num_1__ GHC.Base.== #1 : bool then f v else
                       match arg_0__ with
                       | Bin _ _ v l r => GHC.Base.mappend (go l) (GHC.Base.mappend (f v) (go r))
                       | _ => GHC.Err.patternFailure
                       end
                   end in
      go t.

Local Definition Foldable__Map_fold {inst_k}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Map inst_k) m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    let fix go arg_0__
              := match arg_0__ with
                 | Tip => GHC.Base.mempty
                 | Bin num_1__ _ v _ _ =>
                     if num_1__ GHC.Base.== #1 : bool then v else
                     match arg_0__ with
                     | Bin _ _ v l r => GHC.Base.mappend (go l) (GHC.Base.mappend v (go r))
                     | _ => GHC.Err.patternFailure
                     end
                 end in
    go.

(* Skipping instance NFData__Map of class NFData *)

(* Skipping instance Read__Map of class Read *)

(* Skipping instance Show__Map of class Show *)

Definition adjustWithKey {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> a) -> k -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k} : (k -> a -> a) -> k -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__
          := match arg_0__, arg_1__, arg_2__ with
             | _, _, Tip => Tip
             | f, k, Bin sx kx x l r =>
                 match GHC.Base.compare k kx with
                 | Lt => Bin sx kx x (go f k l) r
                 | Gt => Bin sx kx x l (go f k r)
                 | Eq => Bin sx kx (f kx x) l r
                 end
             end in
  go.

Definition adjust {k} {a} `{GHC.Base.Ord k}
   : (a -> a) -> k -> Map k a -> Map k a :=
  fun f =>
    adjustWithKey (fun arg_0__ arg_1__ =>
                     match arg_0__, arg_1__ with
                     | _, x => f x
                     end).

Definition boolITE {a} : a -> a -> bool -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, _, false => f
    | _, t, true => t
    end.

Definition delta : GHC.Num.Int :=
  #3.

Definition dropMissing {f} {k} {x} {y} `{GHC.Base.Applicative f}
   : WhenMissing f k x y :=
  Mk_WhenMissing (GHC.Base.const (GHC.Base.pure Tip)) (fun arg_0__ arg_1__ =>
                    GHC.Base.pure None).

Definition empty {k} {a} : Map k a :=
  Tip.

Local Definition Monoid__Map_mempty {inst_k} {inst_v} `{(GHC.Base.Ord inst_k)}
   : (Map inst_k inst_v) :=
  empty.

Definition findWithDefault {k} {a} `{GHC.Base.Ord k} : a -> k -> Map k a -> a :=
  let fix go arg_0__ arg_1__ arg_2__
            := match arg_0__, arg_1__, arg_2__ with
               | def, _, Tip => def
               | def, k, Bin _ kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt => go def k l
                   | Gt => go def k r
                   | Eq => x
                   end
               end in
  go.

Definition foldMapWithKey {m} {k} {a} `{GHC.Base.Monoid m}
   : (k -> a -> m) -> Map k a -> m :=
  fun f =>
    let fix go arg_0__
              := match arg_0__ with
                 | Tip => GHC.Base.mempty
                 | Bin num_1__ k v _ _ =>
                     if num_1__ GHC.Base.== #1 : bool then f k v else
                     match arg_0__ with
                     | Bin _ k v l r => GHC.Base.mappend (go l) (GHC.Base.mappend (f k v) (go r))
                     | _ => GHC.Err.patternFailure
                     end
                 end in
    go.

Definition foldl {a} {b} {k} : (a -> b -> a) -> a -> Map k b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Tip => z'
                 | z', Bin _ _ x l r => go (f (go z' l) x) r
                 end in
    go z.

Local Definition Foldable__Map_foldl {inst_k}
   : forall {b} {a}, (b -> a -> b) -> b -> (Map inst_k) a -> b :=
  fun {b} {a} => foldl.

Definition foldl' {a} {b} {k} : (a -> b -> a) -> a -> Map k b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Tip => z'
                 | z', Bin _ _ x l r => go (f (go z' l) x) r
                 end in
    go z.

Local Definition Foldable__Map_foldl' {inst_k}
   : forall {b} {a}, (b -> a -> b) -> b -> (Map inst_k) a -> b :=
  fun {b} {a} => foldl'.

Local Definition Foldable__Map_product {inst_k}
   : forall {a}, forall `{GHC.Num.Num a}, (Map inst_k) a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.*_ #1.

Local Definition Foldable__Map_sum {inst_k}
   : forall {a}, forall `{GHC.Num.Num a}, (Map inst_k) a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.+_ #0.

Definition foldlWithKey {a} {k} {b} : (a -> k -> b -> a) -> a -> Map k b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Tip => z'
                 | z', Bin _ kx x l r => go (f (go z' l) kx x) r
                 end in
    go z.

Definition toDescList {k} {a} : Map k a -> list (k * a)%type :=
  foldlWithKey (fun xs k x => cons (pair k x) xs) nil.

Definition foldlFB {a} {k} {b} : (a -> k -> b -> a) -> a -> Map k b -> a :=
  foldlWithKey.

Definition foldlWithKey' {a} {k} {b}
   : (a -> k -> b -> a) -> a -> Map k b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Tip => z'
                 | z', Bin _ kx x l r => go (f (go z' l) kx x) r
                 end in
    go z.

Definition foldr {a} {b} {k} : (a -> b -> b) -> b -> Map k a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Tip => z'
                 | z', Bin _ _ x l r => go (f x (go z' r)) l
                 end in
    go z.

Definition elems {k} {a} : Map k a -> list a :=
  foldr cons nil.

Local Definition Foldable__Map_toList {inst_k}
   : forall {a}, (Map inst_k) a -> list a :=
  fun {a} => elems.

Local Definition Foldable__Map_foldr {inst_k}
   : forall {a} {b}, (a -> b -> b) -> b -> (Map inst_k) a -> b :=
  fun {a} {b} => foldr.

Definition foldr' {a} {b} {k} : (a -> b -> b) -> b -> Map k a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Tip => z'
                 | z', Bin _ _ x l r => go (f x (go z' r)) l
                 end in
    go z.

Local Definition Foldable__Map_foldr' {inst_k}
   : forall {a} {b}, (a -> b -> b) -> b -> (Map inst_k) a -> b :=
  fun {a} {b} => foldr'.

Definition foldrWithKey {k} {a} {b} : (k -> a -> b -> b) -> b -> Map k a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Tip => z'
                 | z', Bin _ kx x l r => go (f kx x (go z' r)) l
                 end in
    go z.

Definition keys {k} {a} : Map k a -> list k :=
  foldrWithKey (fun arg_0__ arg_1__ arg_2__ =>
                  match arg_0__, arg_1__, arg_2__ with
                  | k, _, ks => cons k ks
                  end) nil.

Definition toAscList {k} {a} : Map k a -> list (k * a)%type :=
  foldrWithKey (fun k x xs => cons (pair k x) xs) nil.

Definition toList {k} {a} : Map k a -> list (k * a)%type :=
  toAscList.

Local Definition Ord2__Map_liftCompare2
   : forall {a} {b} {c} {d},
     (a -> b -> comparison) ->
     (c -> d -> comparison) -> Map a c -> Map b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun cmpk cmpv m n =>
      Data.Functor.Classes.liftCompare (Data.Functor.Classes.liftCompare2 cmpk cmpv)
      (toList m) (toList n).

Definition assocs {k} {a} : Map k a -> list (k * a)%type :=
  fun m => toAscList m.

Local Definition Ord__Map_compare {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
  `{GHC.Base.Ord inst_v}
   : (Map inst_k inst_v) -> (Map inst_k inst_v) -> comparison :=
  fun m1 m2 => GHC.Base.compare (toAscList m1) (toAscList m2).

Local Definition Ord__Map_op_zl__ {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
  `{GHC.Base.Ord inst_v}
   : (Map inst_k inst_v) -> (Map inst_k inst_v) -> bool :=
  fun x y => Ord__Map_compare x y GHC.Base.== Lt.

Local Definition Ord__Map_op_zlze__ {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
  `{GHC.Base.Ord inst_v}
   : (Map inst_k inst_v) -> (Map inst_k inst_v) -> bool :=
  fun x y => Ord__Map_compare x y GHC.Base./= Gt.

Local Definition Ord__Map_max {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
  `{GHC.Base.Ord inst_v}
   : (Map inst_k inst_v) -> (Map inst_k inst_v) -> (Map inst_k inst_v) :=
  fun x y => if Ord__Map_op_zlze__ x y : bool then y else x.

Local Definition Ord__Map_min {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
  `{GHC.Base.Ord inst_v}
   : (Map inst_k inst_v) -> (Map inst_k inst_v) -> (Map inst_k inst_v) :=
  fun x y => if Ord__Map_op_zlze__ x y : bool then x else y.

Local Definition Ord__Map_op_zg__ {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
  `{GHC.Base.Ord inst_v}
   : (Map inst_k inst_v) -> (Map inst_k inst_v) -> bool :=
  fun x y => Ord__Map_compare x y GHC.Base.== Gt.

Local Definition Ord__Map_op_zgze__ {inst_k} {inst_v} `{GHC.Base.Ord inst_k}
  `{GHC.Base.Ord inst_v}
   : (Map inst_k inst_v) -> (Map inst_k inst_v) -> bool :=
  fun x y => Ord__Map_compare x y GHC.Base./= Lt.

Definition foldrFB {k} {a} {b} : (k -> a -> b -> b) -> b -> Map k a -> b :=
  foldrWithKey.

Definition foldrWithKey' {k} {a} {b}
   : (k -> a -> b -> b) -> b -> Map k a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Tip => z'
                 | z', Bin _ kx x l r => go (f kx x (go z' r)) l
                 end in
    go z.

Definition fromSet {k} {a} : (k -> a) -> Data.Set.Internal.Set_ k -> Map k a :=
  fix fromSet arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Data.Set.Internal.Tip => Tip
           | f, Data.Set.Internal.Bin sz x l r =>
               Bin sz x (f x) (fromSet f l) (fromSet f r)
           end.

Definition keysSet {k} {a} : Map k a -> Data.Set.Internal.Set_ k :=
  fix keysSet arg_0__
        := match arg_0__ with
           | Tip => Data.Set.Internal.Tip
           | Bin sz kx _ l r => Data.Set.Internal.Bin sz kx (keysSet l) (keysSet r)
           end.

Definition lookup {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> option a :=
  let fix go arg_0__ arg_1__
            := match arg_0__, arg_1__ with
               | _, Tip => None
               | k, Bin _ kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt => go k l
                   | Gt => go k r
                   | Eq => Some x
                   end
               end in
  go.

Definition op_znz3fU__ {k} {a} `{GHC.Base.Ord k} : Map k a -> k -> option a :=
  fun m k => lookup k m.

Notation "'_!?_'" := (op_znz3fU__).

Infix "!?" := (_!?_) (at level 99).

Definition lookupGE {k} {v} `{GHC.Base.Ord k}
   : k -> Map k v -> option (k * v)%type :=
  let fix goJust arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | _, kx', x', Tip => Some (pair kx' x')
               | k, kx', x', Bin _ kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt => goJust k kx x l
                   | Eq => Some (pair kx x)
                   | Gt => goJust k kx' x' r
                   end
               end in
  let fix goNothing arg_12__ arg_13__
            := match arg_12__, arg_13__ with
               | _, Tip => None
               | k, Bin _ kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt => goJust k kx x l
                   | Eq => Some (pair kx x)
                   | Gt => goNothing k r
                   end
               end in
  goNothing.

Definition lookupGT {k} {v} `{GHC.Base.Ord k}
   : k -> Map k v -> option (k * v)%type :=
  let fix goJust arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | _, kx', x', Tip => Some (pair kx' x')
               | k, kx', x', Bin _ kx x l r =>
                   if k GHC.Base.< kx : bool then goJust k kx x l else
                   goJust k kx' x' r
               end in
  let fix goNothing arg_8__ arg_9__
            := match arg_8__, arg_9__ with
               | _, Tip => None
               | k, Bin _ kx x l r =>
                   if k GHC.Base.< kx : bool then goJust k kx x l else
                   goNothing k r
               end in
  goNothing.

Definition lookupLE {k} {v} `{GHC.Base.Ord k}
   : k -> Map k v -> option (k * v)%type :=
  let fix goJust arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | _, kx', x', Tip => Some (pair kx' x')
               | k, kx', x', Bin _ kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt => goJust k kx' x' l
                   | Eq => Some (pair kx x)
                   | Gt => goJust k kx x r
                   end
               end in
  let fix goNothing arg_12__ arg_13__
            := match arg_12__, arg_13__ with
               | _, Tip => None
               | k, Bin _ kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt => goNothing k l
                   | Eq => Some (pair kx x)
                   | Gt => goJust k kx x r
                   end
               end in
  goNothing.

Definition lookupLT {k} {v} `{GHC.Base.Ord k}
   : k -> Map k v -> option (k * v)%type :=
  let fix goJust arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | _, kx', x', Tip => Some (pair kx' x')
               | k, kx', x', Bin _ kx x l r =>
                   if k GHC.Base.<= kx : bool then goJust k kx' x' l else
                   goJust k kx x r
               end in
  let fix goNothing arg_8__ arg_9__
            := match arg_8__, arg_9__ with
               | _, Tip => None
               | k, Bin _ kx x l r =>
                   if k GHC.Base.<= kx : bool then goNothing k l else
                   goJust k kx x r
               end in
  goNothing.

Definition lookupMaxSure {k} {a} : k -> a -> Map k a -> (k * a)%type :=
  fix lookupMaxSure arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | k, a, Tip => pair k a
           | _, _, Bin _ k a _ r => lookupMaxSure k a r
           end.

Definition lookupMax {k} {a} : Map k a -> option (k * a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Tip => None
    | Bin _ k x _ r => Some (lookupMaxSure k x r)
    end.

Definition lookupMinSure {k} {a} : k -> a -> Map k a -> (k * a)%type :=
  fix lookupMinSure arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | k, a, Tip => pair k a
           | _, _, Bin _ k a l _ => lookupMinSure k a l
           end.

Definition lookupMin {k} {a} : Map k a -> option (k * a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Tip => None
    | Bin _ k x l _ => Some (lookupMinSure k x l)
    end.

Definition map {a} {b} {k} : (a -> b) -> Map k a -> Map k b :=
  fun f =>
    let fix go arg_0__
              := match arg_0__ with
                 | Tip => Tip
                 | Bin sx kx x l r => Bin sx kx (f x) (go l) (go r)
                 end in
    go.

Local Definition Functor__Map_fmap {inst_k}
   : forall {a} {b}, (a -> b) -> (Map inst_k) a -> (Map inst_k) b :=
  fun {a} {b} => fun f m => map f m.

Program Instance Functor__Map {k} : GHC.Base.Functor (Map k) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__Map_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Map_op_zlzd__ |}.

Definition lmapWhenMissing {b} {a} {f} {k} {x}
   : (b -> a) -> WhenMissing f k a x -> WhenMissing f k b x :=
  fun f t =>
    Mk_WhenMissing (fun m => missingSubtree t (GHC.Base.fmap f m)) (fun k x =>
                      missingKey t k (f x)).

Definition mapAccumL {a} {k} {b} {c}
   : (a -> k -> b -> (a * c)%type) -> a -> Map k b -> (a * Map k c)%type :=
  fix mapAccumL arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, a, Tip => pair a Tip
           | f, a, Bin sx kx x l r =>
               let 'pair a1 l' := mapAccumL f a l in
               let 'pair a2 x' := f a1 kx x in
               let 'pair a3 r' := mapAccumL f a2 r in
               pair a3 (Bin sx kx x' l' r')
           end.

Definition mapAccumWithKey {a} {k} {b} {c}
   : (a -> k -> b -> (a * c)%type) -> a -> Map k b -> (a * Map k c)%type :=
  fun f a t => mapAccumL f a t.

Definition mapAccum {a} {b} {c} {k}
   : (a -> b -> (a * c)%type) -> a -> Map k b -> (a * Map k c)%type :=
  fun f a m =>
    mapAccumWithKey (fun arg_0__ arg_1__ arg_2__ =>
                       match arg_0__, arg_1__, arg_2__ with
                       | a', _, x' => f a' x'
                       end) a m.

Definition mapAccumRWithKey {a} {k} {b} {c}
   : (a -> k -> b -> (a * c)%type) -> a -> Map k b -> (a * Map k c)%type :=
  fix mapAccumRWithKey arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, a, Tip => pair a Tip
           | f, a, Bin sx kx x l r =>
               let 'pair a1 r' := mapAccumRWithKey f a r in
               let 'pair a2 x' := f a1 kx x in
               let 'pair a3 l' := mapAccumRWithKey f a2 l in
               pair a3 (Bin sx kx x' l' r')
           end.

Definition mapGentlyWhenMissing {f} {a} {b} {k} {x} `{GHC.Base.Functor f}
   : (a -> b) -> WhenMissing f k x a -> WhenMissing f k x b :=
  fun f t =>
    Mk_WhenMissing (fun m => GHC.Base.fmap f Data.Functor.<$> missingSubtree t m)
                   (fun k x => GHC.Base.fmap f Data.Functor.<$> missingKey t k x).

Definition mapKeysMonotonic {k1} {k2} {a}
   : (k1 -> k2) -> Map k1 a -> Map k2 a :=
  fix mapKeysMonotonic arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Tip => Tip
           | f, Bin sz k x l r =>
               Bin sz (f k) x (mapKeysMonotonic f l) (mapKeysMonotonic f r)
           end.

Definition mapWhenMatched {f} {a} {b} {k} {x} {y} `{GHC.Base.Functor f}
   : (a -> b) -> WhenMatched f k x y a -> WhenMatched f k x y b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_WhenMatched g =>
        Mk_WhenMatched (fun k x y => GHC.Base.fmap (GHC.Base.fmap f) (g k x y))
    end.

Local Definition Functor__WhenMatched_fmap {inst_f} {inst_k} {inst_x} {inst_y}
  `{GHC.Base.Functor inst_f}
   : forall {a} {b},
     (a -> b) ->
     (WhenMatched inst_f inst_k inst_x inst_y) a ->
     (WhenMatched inst_f inst_k inst_x inst_y) b :=
  fun {a} {b} => mapWhenMatched.

Local Definition Functor__WhenMatched_op_zlzd__ {inst_f} {inst_k} {inst_x}
  {inst_y} `{GHC.Base.Functor inst_f}
   : forall {a} {b},
     a ->
     (WhenMatched inst_f inst_k inst_x inst_y) b ->
     (WhenMatched inst_f inst_k inst_x inst_y) a :=
  fun {a} {b} => Functor__WhenMatched_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__WhenMatched {f} {k} {x} {y} `{GHC.Base.Functor f}
   : GHC.Base.Functor (WhenMatched f k x y) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__WhenMatched_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__WhenMatched_op_zlzd__ |}.

Definition mapWhenMissing {f} {a} {b} {k} {x} `{GHC.Base.Applicative f}
  `{GHC.Base.Monad f}
   : (a -> b) -> WhenMissing f k x a -> WhenMissing f k x b :=
  fun f t =>
    Mk_WhenMissing (fun m =>
                      missingSubtree t m GHC.Base.>>= (fun m' => GHC.Base.pure (GHC.Base.fmap f m')))
                   (fun k x =>
                      missingKey t k x GHC.Base.>>= (fun q => (GHC.Base.pure (GHC.Base.fmap f q)))).

Local Definition Functor__WhenMissing_fmap {inst_f} {inst_k} {inst_x}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monad inst_f}
   : forall {a} {b},
     (a -> b) ->
     (WhenMissing inst_f inst_k inst_x) a -> (WhenMissing inst_f inst_k inst_x) b :=
  fun {a} {b} => mapWhenMissing.

Local Definition Functor__WhenMissing_op_zlzd__ {inst_f} {inst_k} {inst_x}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Monad inst_f}
   : forall {a} {b},
     a ->
     (WhenMissing inst_f inst_k inst_x) b -> (WhenMissing inst_f inst_k inst_x) a :=
  fun {a} {b} => Functor__WhenMissing_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__WhenMissing {f} {k} {x} `{GHC.Base.Applicative f}
  `{GHC.Base.Monad f}
   : GHC.Base.Functor (WhenMissing f k x) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__WhenMissing_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__WhenMissing_op_zlzd__ |}.

Definition mapWithKey {k} {a} {b} : (k -> a -> b) -> Map k a -> Map k b :=
  fix mapWithKey arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Tip => Tip
           | f, Bin sx kx x l r => Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r)
           end.

Definition mapMissing {f} {k} {x} {y} `{GHC.Base.Applicative f}
   : (k -> x -> y) -> WhenMissing f k x y :=
  fun f =>
    Mk_WhenMissing (fun m => GHC.Base.pure (mapWithKey f m)) (fun k x =>
                      GHC.Base.pure (Some (f k x))).

Definition member {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> bool :=
  let fix go arg_0__ arg_1__
            := match arg_0__, arg_1__ with
               | _, Tip => false
               | k, Bin _ kx _ l r =>
                   match GHC.Base.compare k kx with
                   | Lt => go k l
                   | Gt => go k r
                   | Eq => true
                   end
               end in
  go.

Definition notMember {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> bool :=
  fun k m => negb (member k m).

Definition null {k} {a} : Map k a -> bool :=
  fun arg_0__ => match arg_0__ with | Tip => true | Bin _ _ _ _ _ => false end.

Local Definition Foldable__Map_null {inst_k}
   : forall {a}, (Map inst_k) a -> bool :=
  fun {a} => null.

Definition preserveMissing {f} {k} {x} `{GHC.Base.Applicative f}
   : WhenMissing f k x x :=
  Mk_WhenMissing GHC.Base.pure (fun arg_0__ arg_1__ =>
                    match arg_0__, arg_1__ with
                    | _, v => GHC.Base.pure (Some v)
                    end).

Definition ratio : GHC.Num.Int :=
  #2.

Definition runWhenMatched {f} {k} {x} {y} {z}
   : WhenMatched f k x y z -> k -> x -> y -> f (option z) :=
  matchedKey.

Definition contramapSecondWhenMatched {b} {a} {f} {k} {x} {z}
   : (b -> a) -> WhenMatched f k x a z -> WhenMatched f k x b z :=
  fun f t => Mk_WhenMatched (fun k x y => runWhenMatched t k x (f y)).

Definition contramapFirstWhenMatched {b} {a} {f} {k} {y} {z}
   : (b -> a) -> WhenMatched f k a y z -> WhenMatched f k b y z :=
  fun f t => Mk_WhenMatched (fun k x y => runWhenMatched t k (f x) y).

Definition runWhenMissing {f} {k} {x} {y}
   : WhenMissing f k x y -> k -> x -> f (option y) :=
  missingKey.

Definition singleton {k} {a} : k -> a -> Map k a :=
  fun k x => Bin #1 k x Tip Tip.

Definition splitRoot {k} {b} : Map k b -> list (Map k b) :=
  fun orig =>
    match orig with
    | Tip => nil
    | Bin _ k v l r => cons l (cons (singleton k v) (cons r nil))
    end.

Definition size {k} {a} : Map k a -> GHC.Num.Int :=
  fun arg_0__ => match arg_0__ with | Tip => #0 | Bin sz _ _ _ _ => sz end.

Definition lookupIndex {k} {a} `{GHC.Base.Ord k}
   : k -> Map k a -> option GHC.Num.Int :=
  let go {k} {a} `{GHC.Base.Ord k}
   : GHC.Num.Int -> k -> Map k a -> option GHC.Num.Int :=
    fix go arg_0__ arg_1__ arg_2__
          := match arg_0__, arg_1__, arg_2__ with
             | _, _, Tip => None
             | idx, k, Bin _ kx _ l r =>
                 match GHC.Base.compare k kx with
                 | Lt => go idx k l
                 | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ #1) k r
                 | Eq => Some (idx GHC.Num.+ size l)
                 end
             end in
  go #0.

Definition findIndex {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> GHC.Num.Int :=
  let go {k} {a} `{GHC.Base.Ord k} : GHC.Num.Int -> k -> Map k a -> GHC.Num.Int :=
    fix go arg_0__ arg_1__ arg_2__
          := match arg_0__, arg_1__, arg_2__ with
             | _, _, Tip =>
                 GHC.Err.error (GHC.Base.hs_string__ "Map.findIndex: element is not in the map")
             | idx, k, Bin _ kx _ l r =>
                 match GHC.Base.compare k kx with
                 | Lt => go idx k l
                 | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ #1) k r
                 | Eq => idx GHC.Num.+ size l
                 end
             end in
  go #0.

Definition bin {k} {a} : k -> a -> Map k a -> Map k a -> Map k a :=
  fun k x l r => Bin ((size l GHC.Num.+ size r) GHC.Num.+ #1) k x l r.

Definition balanceR {k} {a} : k -> a -> Map k a -> Map k a -> Map k a :=
  fun k x l r =>
    match l with
    | Tip =>
        match r with
        | Tip => Bin #1 k x Tip Tip
        | Bin _ _ _ Tip Tip => Bin #2 k x Tip r
        | Bin _ rk rx Tip (Bin _ _ _ _ _ as rr) => Bin #3 rk rx (Bin #1 k x Tip Tip) rr
        | Bin _ rk rx (Bin _ rlk rlx _ _) Tip =>
            Bin #3 rlk rlx (Bin #1 k x Tip Tip) (Bin #1 rk rx Tip Tip)
        | Bin rs rk rx (Bin rls rlk rlx rll rlr as rl) (Bin rrs _ _ _ _ as rr) =>
            if rls GHC.Base.< (ratio GHC.Num.* rrs) : bool
            then Bin (#1 GHC.Num.+ rs) rk rx (Bin (#1 GHC.Num.+ rls) k x Tip rl) rr else
            Bin (#1 GHC.Num.+ rs) rlk rlx (Bin (#1 GHC.Num.+ size rll) k x Tip rll) (Bin
                                                                                     ((#1 GHC.Num.+ rrs) GHC.Num.+
                                                                                      size rlr) rk rx rlr rr)
        end
    | Bin ls _ _ _ _ =>
        match r with
        | Tip => Bin (#1 GHC.Num.+ ls) k x l Tip
        | Bin rs rk rx rl rr =>
            if rs GHC.Base.> (delta GHC.Num.* ls) : bool
            then let scrut_10__ := pair rl rr in
                 match scrut_10__ with
                 | pair (Bin rls rlk rlx rll rlr) (Bin rrs _ _ _ _) =>
                     if rls GHC.Base.< (ratio GHC.Num.* rrs) : bool
                     then Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) rk rx (Bin ((#1 GHC.Num.+ ls)
                                                                           GHC.Num.+
                                                                           rls) k x l rl) rr else
                     Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) rlk rlx (Bin ((#1 GHC.Num.+ ls) GHC.Num.+
                                                                        size rll) k x l rll) (Bin ((#1 GHC.Num.+ rrs)
                                                                                                   GHC.Num.+
                                                                                                   size rlr) rk rx rlr
                                                                                              rr)
                 | _ =>
                     let 'pair _ _ := scrut_10__ in
                     GHC.Err.error (GHC.Base.hs_string__ "Failure in Data.Map.balanceR")
                 end else
            Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) k x l r
        end
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

Definition minViewSure {k} {a} : k -> a -> Map k a -> Map k a -> MinView k a :=
  let fix go arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | k, x, Tip, r => Mk_MinView k x r
               | k, x, Bin _ kl xl ll lr, r =>
                   let 'Mk_MinView km xm l' := go kl xl ll lr in
                   Mk_MinView km xm (balanceR k x l' r)
               end in
  go.

Definition minViewWithKey {k} {a}
   : Map k a -> option ((k * a)%type * Map k a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Tip => None
    | Bin _ k x l r =>
        Some (let 'Mk_MinView km xm t := minViewSure k x l r in pair (pair km xm) t)
    end.

Definition minView {k} {a} : Map k a -> option (a * Map k a)%type :=
  fun t =>
    match minViewWithKey t with
    | None => None
    | Some (pair (pair _ x) t') => Some (pair x t')
    end.

Definition updateMinWithKey {k} {a}
   : (k -> a -> option a) -> Map k a -> Map k a :=
  fix updateMinWithKey arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Tip => Tip
           | f, Bin sx kx x Tip r =>
               match f kx x with
               | None => r
               | Some x' => Bin sx kx x' Tip r
               end
           | f, Bin _ kx x l r => balanceR kx x (updateMinWithKey f l) r
           end.

Definition updateMin {a} {k} : (a -> option a) -> Map k a -> Map k a :=
  fun f m =>
    updateMinWithKey (fun arg_0__ arg_1__ =>
                        match arg_0__, arg_1__ with
                        | _, x => f x
                        end) m.

Definition balanceL {k} {a} : k -> a -> Map k a -> Map k a -> Map k a :=
  fun k x l r =>
    match r with
    | Tip =>
        match l with
        | Tip => Bin #1 k x Tip Tip
        | Bin _ _ _ Tip Tip => Bin #2 k x l Tip
        | Bin _ lk lx Tip (Bin _ lrk lrx _ _) =>
            Bin #3 lrk lrx (Bin #1 lk lx Tip Tip) (Bin #1 k x Tip Tip)
        | Bin _ lk lx (Bin _ _ _ _ _ as ll) Tip => Bin #3 lk lx ll (Bin #1 k x Tip Tip)
        | Bin ls lk lx (Bin lls _ _ _ _ as ll) (Bin lrs lrk lrx lrl lrr as lr) =>
            if lrs GHC.Base.< (ratio GHC.Num.* lls) : bool
            then Bin (#1 GHC.Num.+ ls) lk lx ll (Bin (#1 GHC.Num.+ lrs) k x lr Tip) else
            Bin (#1 GHC.Num.+ ls) lrk lrx (Bin ((#1 GHC.Num.+ lls) GHC.Num.+ size lrl) lk lx
                                           ll lrl) (Bin (#1 GHC.Num.+ size lrr) k x lrr Tip)
        end
    | Bin rs _ _ _ _ =>
        match l with
        | Tip => Bin (#1 GHC.Num.+ rs) k x Tip r
        | Bin ls lk lx ll lr =>
            if ls GHC.Base.> (delta GHC.Num.* rs) : bool
            then let scrut_10__ := pair ll lr in
                 match scrut_10__ with
                 | pair (Bin lls _ _ _ _) (Bin lrs lrk lrx lrl lrr) =>
                     if lrs GHC.Base.< (ratio GHC.Num.* lls) : bool
                     then Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) lk lx ll (Bin ((#1 GHC.Num.+ rs)
                                                                              GHC.Num.+
                                                                              lrs) k x lr r) else
                     Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) lrk lrx (Bin ((#1 GHC.Num.+ lls) GHC.Num.+
                                                                        size lrl) lk lx ll lrl) (Bin ((#1 GHC.Num.+ rs)
                                                                                                      GHC.Num.+
                                                                                                      size lrr) k x lrr
                                                                                                 r)
                 | _ =>
                     let 'pair _ _ := scrut_10__ in
                     GHC.Err.error (GHC.Base.hs_string__ "Failure in Data.Map.balanceL")
                 end else
            Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) k x l r
        end
    end.

Definition deleteMax {k} {a} : Map k a -> Map k a :=
  fix deleteMax arg_0__
        := match arg_0__ with
           | Bin _ _ _ l Tip => l
           | Bin _ kx x l r => balanceL kx x l (deleteMax r)
           | Tip => Tip
           end.

Definition insert {k} {a} `{GHC.Base.Ord k} : k -> a -> Map k a -> Map k a :=
  fun kx0 =>
    let go {k} {a} `{GHC.Base.Ord k} : k -> k -> a -> Map k a -> Map k a :=
      fix go arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | orig, _, x, Tip => singleton (orig) x
               | orig, kx, x, (Bin sz ky y l r as t) =>
                   match GHC.Base.compare kx ky with
                   | Lt =>
                       let l' := go orig kx x l in
                       if Utils.Containers.Internal.PtrEquality.ptrEq l' l : bool then t else
                       balanceL ky y l' r
                   | Gt =>
                       let r' := go orig kx x r in
                       if Utils.Containers.Internal.PtrEquality.ptrEq r' r : bool then t else
                       balanceR ky y l r'
                   | Eq =>
                       if andb (Utils.Containers.Internal.PtrEquality.ptrEq x y) (GHC.Prim.seq orig
                                                                                               (Utils.Containers.Internal.PtrEquality.ptrEq
                                                                                                orig ky)) : bool
                       then t else
                       Bin sz (orig) x l r
                   end
               end in
    go kx0 kx0.

Definition insertLookupWithKey {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> a -> a) -> k -> a -> Map k a -> (option a * Map k a)%type :=
  fun f0 k0 x0 =>
    let go {k} {a} `{GHC.Base.Ord k}
     : (k -> a -> a -> a) -> k -> a -> Map k a -> prod (option a) (Map k a) :=
      fix go arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | _, kx, x, Tip => (pair None (singleton kx x))
               | f, kx, x, Bin sy ky y l r =>
                   match GHC.Base.compare kx ky with
                   | Lt =>
                       let 'pair found l' := go f kx x l in
                       let t' := balanceL ky y l' r in (pair found t')
                   | Gt =>
                       let 'pair found r' := go f kx x r in
                       let t' := balanceR ky y l r' in (pair found t')
                   | Eq => (pair (Some y) (Bin sy kx (f kx x y) l r))
                   end
               end in
    id GHC.Base.∘ go f0 k0 x0.

Definition insertMin {k} {a} : k -> a -> Map k a -> Map k a :=
  fix insertMin kx x t
        := match t with
           | Tip => singleton kx x
           | Bin _ ky y l r => balanceL ky y (insertMin kx x l) r
           end.

Definition insertR {k} {a} `{GHC.Base.Ord k} : k -> a -> Map k a -> Map k a :=
  fun kx0 =>
    let go {k} {a} `{GHC.Base.Ord k} : k -> k -> a -> Map k a -> Map k a :=
      fix go arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | orig, _, x, Tip => singleton (orig) x
               | orig, kx, x, (Bin _ ky y l r as t) =>
                   match GHC.Base.compare kx ky with
                   | Lt =>
                       let l' := go orig kx x l in
                       if Utils.Containers.Internal.PtrEquality.ptrEq l' l : bool then t else
                       balanceL ky y l' r
                   | Gt =>
                       let r' := go orig kx x r in
                       if Utils.Containers.Internal.PtrEquality.ptrEq r' r : bool then t else
                       balanceR ky y l r'
                   | Eq => t
                   end
               end in
    go kx0 kx0.

Definition insertWith {k} {a} `{GHC.Base.Ord k}
   : (a -> a -> a) -> k -> a -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k}
   : (a -> a -> a) -> k -> a -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__ arg_3__
          := match arg_0__, arg_1__, arg_2__, arg_3__ with
             | _, kx, x, Tip => singleton kx x
             | f, kx, x, Bin sy ky y l r =>
                 match GHC.Base.compare kx ky with
                 | Lt => balanceL ky y (go f kx x l) r
                 | Gt => balanceR ky y l (go f kx x r)
                 | Eq => Bin sy kx (f x y) l r
                 end
             end in
  go.

Definition insertWithKey {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__ arg_3__
          := match arg_0__, arg_1__, arg_2__, arg_3__ with
             | _, kx, x, Tip => singleton kx x
             | f, kx, x, Bin sy ky y l r =>
                 match GHC.Base.compare kx ky with
                 | Lt => balanceL ky y (go f kx x l) r
                 | Gt => balanceR ky y l (go f kx x r)
                 | Eq => Bin sy kx (f kx x y) l r
                 end
             end in
  go.

Definition fromListWithKey {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> a -> a) -> list (k * a)%type -> Map k a :=
  fun f xs =>
    let ins :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | t, pair k x => insertWithKey f k x t
        end in
    Data.Foldable.foldl' ins empty xs.

Definition fromListWith {k} {a} `{GHC.Base.Ord k}
   : (a -> a -> a) -> list (k * a)%type -> Map k a :=
  fun f xs =>
    fromListWithKey (fun arg_0__ arg_1__ arg_2__ =>
                       match arg_0__, arg_1__, arg_2__ with
                       | _, x, y => f x y
                       end) xs.

Definition mapKeysWith {k2} {a} {k1} `{GHC.Base.Ord k2}
   : (a -> a -> a) -> (k1 -> k2) -> Map k1 a -> Map k2 a :=
  fun c f =>
    fromListWith c GHC.Base.∘
    foldrWithKey (fun k x xs => cons (pair (f k) x) xs) nil.

Definition insertWithKeyR {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__ arg_3__
          := match arg_0__, arg_1__, arg_2__, arg_3__ with
             | _, kx, x, Tip => singleton kx x
             | f, kx, x, Bin sy ky y l r =>
                 match GHC.Base.compare kx ky with
                 | Lt => balanceL ky y (go f kx x l) r
                 | Gt => balanceR ky y l (go f kx x r)
                 | Eq => Bin sy ky (f ky y x) l r
                 end
             end in
  go.

Definition insertWithR {k} {a} `{GHC.Base.Ord k}
   : (a -> a -> a) -> k -> a -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k}
   : (a -> a -> a) -> k -> a -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__ arg_3__
          := match arg_0__, arg_1__, arg_2__, arg_3__ with
             | _, kx, x, Tip => singleton kx x
             | f, kx, x, Bin sy ky y l r =>
                 match GHC.Base.compare kx ky with
                 | Lt => balanceL ky y (go f kx x l) r
                 | Gt => balanceR ky y l (go f kx x r)
                 | Eq => Bin sy ky (f y x) l r
                 end
             end in
  go.

Program Fixpoint link {k} {a} (arg_0__ : k) (arg_1__ : a) (arg_2__ : Map k a)
                      (arg_3__ : Map k a) {measure (Nat.add (map_size arg_2__) (map_size arg_3__))}
                   : Map k a
                   := match arg_0__, arg_1__, arg_2__, arg_3__ with
                      | kx, x, Tip, r => insertMin kx x r
                      | kx, x, l, Tip => insertMax kx x l
                      | kx, x, (Bin sizeL ky y ly ry as l), (Bin sizeR kz z lz rz as r) =>
                          if Bool.Sumbool.sumbool_of_bool ((delta GHC.Num.* sizeL) GHC.Base.< sizeR)
                          then balanceL kz z (link kx x l lz) rz else
                          if Bool.Sumbool.sumbool_of_bool ((delta GHC.Num.* sizeR) GHC.Base.< sizeL)
                          then balanceR ky y ly (link kx x ry r) else
                          bin kx x l r
                      end.
Solve Obligations with (termination_by_omega).

Definition dropWhileAntitone {k} {a} : (k -> bool) -> Map k a -> Map k a :=
  fix dropWhileAntitone arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Tip => Tip
           | p, Bin _ kx x l r =>
               if p kx : bool then dropWhileAntitone p r else
               link kx x (dropWhileAntitone p l) r
           end.

Definition fromDistinctAscList {k} {a} : list (k * a)%type -> Map k a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => Tip
    | cons (pair kx0 x0) xs0 =>
        let create :=
          GHC.DeferredFix.deferredFix2 (fun create arg_1__ arg_2__ =>
                                          match arg_1__, arg_2__ with
                                          | _, nil => (pair Tip nil)
                                          | s, (cons x' xs' as xs) =>
                                              if s GHC.Base.== #1 : bool
                                              then let 'pair kx x := x' in
                                                   (pair (Bin #1 kx x Tip Tip) xs') else
                                              match create (Data.Bits.shiftR s #1) xs with
                                              | (pair _ nil as res) => res
                                              | pair l (cons (pair ky y) ys) =>
                                                  let 'pair r zs := create (Data.Bits.shiftR s #1) ys in
                                                  (pair (link ky y l r) zs)
                                              end
                                          end) in
        let go :=
          GHC.DeferredFix.deferredFix3 (fun go arg_15__ arg_16__ arg_17__ =>
                                          match arg_15__, arg_16__, arg_17__ with
                                          | _, t, nil => t
                                          | s, l, cons (pair kx x) xs =>
                                              let 'pair r ys := create s xs in
                                              let t' := link kx x l r in go (Data.Bits.shiftL s #1) t' ys
                                          end) in
        go (#1 : GHC.Num.Int) (Bin #1 kx0 x0 Tip Tip) xs0
    end.

Definition fromAscList {k} {a} `{GHC.Base.Eq_ k}
   : list (k * a)%type -> Map k a :=
  fun xs =>
    let fix combineEq' arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z, nil => cons z nil
                 | (pair kz _ as z), cons (pair kx xx as x) xs' =>
                     if kx GHC.Base.== kz : bool then combineEq' (pair kx xx) xs' else
                     cons z (combineEq' x xs')
                 end in
    let combineEq :=
      fun xs' =>
        match xs' with
        | nil => nil
        | cons x nil => cons x nil
        | cons x xx => combineEq' x xx
        end in
    fromDistinctAscList (combineEq xs).

Definition fromAscListWithKey {k} {a} `{GHC.Base.Eq_ k}
   : (k -> a -> a -> a) -> list (k * a)%type -> Map k a :=
  fun f xs =>
    let fix combineEq' arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z, nil => cons z nil
                 | (pair kz zz as z), cons (pair kx xx as x) xs' =>
                     if kx GHC.Base.== kz : bool
                     then let yy := f kx xx zz in combineEq' (pair kx yy) xs' else
                     cons z (combineEq' x xs')
                 end in
    let combineEq :=
      fun arg_7__ arg_8__ =>
        match arg_7__, arg_8__ with
        | _, xs' =>
            match xs' with
            | nil => nil
            | cons x nil => cons x nil
            | cons x xx => combineEq' x xx
            end
        end in
    fromDistinctAscList (combineEq f xs).

Definition fromAscListWith {k} {a} `{GHC.Base.Eq_ k}
   : (a -> a -> a) -> list (k * a)%type -> Map k a :=
  fun f xs =>
    fromAscListWithKey (fun arg_0__ arg_1__ arg_2__ =>
                          match arg_0__, arg_1__, arg_2__ with
                          | _, x, y => f x y
                          end) xs.

Definition fromDistinctDescList {k} {a} : list (k * a)%type -> Map k a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => Tip
    | cons (pair kx0 x0) xs0 =>
        let create :=
          GHC.DeferredFix.deferredFix2 (fun create arg_1__ arg_2__ =>
                                          match arg_1__, arg_2__ with
                                          | _, nil => (pair Tip nil)
                                          | s, (cons x' xs' as xs) =>
                                              if s GHC.Base.== #1 : bool
                                              then let 'pair kx x := x' in
                                                   (pair (Bin #1 kx x Tip Tip) xs') else
                                              match create (Data.Bits.shiftR s #1) xs with
                                              | (pair _ nil as res) => res
                                              | pair r (cons (pair ky y) ys) =>
                                                  let 'pair l zs := create (Data.Bits.shiftR s #1) ys in
                                                  (pair (link ky y l r) zs)
                                              end
                                          end) in
        let go :=
          GHC.DeferredFix.deferredFix3 (fun go arg_15__ arg_16__ arg_17__ =>
                                          match arg_15__, arg_16__, arg_17__ with
                                          | _, t, nil => t
                                          | s, r, cons (pair kx x) xs =>
                                              let 'pair l ys := create s xs in
                                              let t' := link kx x l r in go (Data.Bits.shiftL s #1) t' ys
                                          end) in
        go (#1 : GHC.Num.Int) (Bin #1 kx0 x0 Tip Tip) xs0
    end.

Definition fromDescList {k} {a} `{GHC.Base.Eq_ k}
   : list (k * a)%type -> Map k a :=
  fun xs =>
    let fix combineEq' arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z, nil => cons z nil
                 | (pair kz _ as z), cons (pair kx xx as x) xs' =>
                     if kx GHC.Base.== kz : bool then combineEq' (pair kx xx) xs' else
                     cons z (combineEq' x xs')
                 end in
    let combineEq :=
      fun xs' =>
        match xs' with
        | nil => nil
        | cons x nil => cons x nil
        | cons x xx => combineEq' x xx
        end in
    fromDistinctDescList (combineEq xs).

Definition fromDescListWithKey {k} {a} `{GHC.Base.Eq_ k}
   : (k -> a -> a -> a) -> list (k * a)%type -> Map k a :=
  fun f xs =>
    let fix combineEq' arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z, nil => cons z nil
                 | (pair kz zz as z), cons (pair kx xx as x) xs' =>
                     if kx GHC.Base.== kz : bool
                     then let yy := f kx xx zz in combineEq' (pair kx yy) xs' else
                     cons z (combineEq' x xs')
                 end in
    let combineEq :=
      fun arg_7__ arg_8__ =>
        match arg_7__, arg_8__ with
        | _, xs' =>
            match xs' with
            | nil => nil
            | cons x nil => cons x nil
            | cons x xx => combineEq' x xx
            end
        end in
    fromDistinctDescList (combineEq f xs).

Definition fromDescListWith {k} {a} `{GHC.Base.Eq_ k}
   : (a -> a -> a) -> list (k * a)%type -> Map k a :=
  fun f xs =>
    fromDescListWithKey (fun arg_0__ arg_1__ arg_2__ =>
                           match arg_0__, arg_1__, arg_2__ with
                           | _, x, y => f x y
                           end) xs.

Definition fromList {k} {a} `{GHC.Base.Ord k} : list (k * a)%type -> Map k a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => Tip
    | cons (pair kx x) nil => Bin #1 kx x Tip Tip
    | cons (pair kx0 x0) xs0 =>
        let fromList' :=
          fun t0 xs =>
            let ins :=
              fun arg_2__ arg_3__ =>
                match arg_2__, arg_3__ with
                | t, pair k x => insert k x t
                end in
            Data.Foldable.foldl' ins t0 xs in
        let not_ordered :=
          fun arg_7__ arg_8__ =>
            match arg_7__, arg_8__ with
            | _, nil => false
            | kx, cons (pair ky _) _ => kx GHC.Base.>= ky
            end in
        let create :=
          GHC.DeferredFix.deferredFix2 (fun create arg_11__ arg_12__ =>
                                          match arg_11__, arg_12__ with
                                          | _, nil => pair (pair Tip nil) nil
                                          | s, (cons xp xss as xs) =>
                                              if s GHC.Base.== #1 : bool
                                              then let 'pair kx x := xp in
                                                   if not_ordered kx xss : bool
                                                   then pair (pair (Bin #1 kx x Tip Tip) nil) xss else
                                                   pair (pair (Bin #1 kx x Tip Tip) xss) nil else
                                              match create (Data.Bits.shiftR s #1) xs with
                                              | (pair (pair _ nil) _ as res) => res
                                              | pair (pair l (cons (pair ky y) nil)) zs =>
                                                  pair (pair (insertMax ky y l) nil) zs
                                              | pair (pair l (cons (pair ky y) yss as ys)) _ =>
                                                  if not_ordered ky yss : bool then pair (pair l nil) ys else
                                                  let 'pair (pair r zs) ws := create (Data.Bits.shiftR s #1) yss in
                                                  pair (pair (link ky y l r) zs) ws
                                              end
                                          end) in
        let go :=
          GHC.DeferredFix.deferredFix3 (fun go arg_28__ arg_29__ arg_30__ =>
                                          match arg_28__, arg_29__, arg_30__ with
                                          | _, t, nil => t
                                          | _, t, cons (pair kx x) nil => insertMax kx x t
                                          | s, l, (cons (pair kx x) xss as xs) =>
                                              if not_ordered kx xss : bool then fromList' l xs else
                                              match create s xss with
                                              | pair (pair r ys) nil => go (Data.Bits.shiftL s #1) (link kx x l r) ys
                                              | pair (pair r _) ys => fromList' (link kx x l r) ys
                                              end
                                          end) in
        if not_ordered kx0 xs0 : bool then fromList' (Bin #1 kx0 x0 Tip Tip) xs0 else
        go (#1 : GHC.Num.Int) (Bin #1 kx0 x0 Tip Tip) xs0
    end.

Definition mapKeys {k2} {k1} {a} `{GHC.Base.Ord k2}
   : (k1 -> k2) -> Map k1 a -> Map k2 a :=
  fun f =>
    fromList GHC.Base.∘ foldrWithKey (fun k x xs => cons (pair (f k) x) xs) nil.

Definition spanAntitone {k} {a}
   : (k -> bool) -> Map k a -> (Map k a * Map k a)%type :=
  fun p0 m =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | _, Tip => pair Tip Tip
                 | p, Bin _ kx x l r =>
                     if p kx : bool then let 'pair u v := go p r in pair (link kx x l u) v else
                     let 'pair u v := go p l in
                     pair u (link kx x v r)
                 end in
    id (go p0 m).

Definition split {k} {a} `{GHC.Base.Ord k}
   : k -> Map k a -> (Map k a * Map k a)%type :=
  fun k0 t0 =>
    let fix go k t
              := match t with
                 | Tip => pair Tip Tip
                 | Bin _ kx x l r =>
                     match GHC.Base.compare k kx with
                     | Lt => let 'pair lt gt := go k l in pair lt (link kx x gt r)
                     | Gt => let 'pair lt gt := go k r in pair (link kx x l lt) gt
                     | Eq => (pair l r)
                     end
                 end in
    id (go k0 t0).

Definition splitLookup {k} {a} `{GHC.Base.Ord k}
   : k -> Map k a -> (Map k a * option a * Map k a)%type :=
  fun k0 m =>
    let go {k} {a} `{GHC.Base.Ord k}
     : k -> Map k a -> StrictTriple (Map k a) (option a) (Map k a) :=
      fix go k t
            := match t with
               | Tip => Mk_StrictTriple Tip None Tip
               | Bin _ kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt =>
                       let 'Mk_StrictTriple lt z gt := go k l in
                       let gt' := link kx x gt r in Mk_StrictTriple lt z gt'
                   | Gt =>
                       let 'Mk_StrictTriple lt z gt := go k r in
                       let lt' := link kx x l lt in Mk_StrictTriple lt' z gt
                   | Eq => Mk_StrictTriple l (Some x) r
                   end
               end in
    let 'Mk_StrictTriple l mv r := go k0 m in
    pair (pair l mv) r.

Definition submap' {a} {b} {c} `{GHC.Base.Ord a}
   : (b -> c -> bool) -> Map a b -> Map a c -> bool :=
  fix submap' arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, Tip, _ => true
           | _, _, Tip => false
           | f, Bin _ kx x l r, t =>
               let 'pair (pair lt found) gt := splitLookup kx t in
               match found with
               | None => false
               | Some y => andb (f x y) (andb (submap' f l lt) (submap' f r gt))
               end
           end.

Definition splitMember {k} {a} `{GHC.Base.Ord k}
   : k -> Map k a -> (Map k a * bool * Map k a)%type :=
  fun k0 m =>
    let go {k} {a} `{GHC.Base.Ord k}
     : k -> Map k a -> StrictTriple (Map k a) bool (Map k a) :=
      fix go k t
            := match t with
               | Tip => Mk_StrictTriple Tip false Tip
               | Bin _ kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt =>
                       let 'Mk_StrictTriple lt z gt := go k l in
                       let gt' := link kx x gt r in Mk_StrictTriple lt z gt'
                   | Gt =>
                       let 'Mk_StrictTriple lt z gt := go k r in
                       let lt' := link kx x l lt in Mk_StrictTriple lt' z gt
                   | Eq => Mk_StrictTriple l true r
                   end
               end in
    let 'Mk_StrictTriple l mv r := go k0 m in
    pair (pair l mv) r.

Definition takeWhileAntitone {k} {a} : (k -> bool) -> Map k a -> Map k a :=
  fix takeWhileAntitone arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Tip => Tip
           | p, Bin _ kx x l r =>
               if p kx : bool then link kx x l (takeWhileAntitone p r) else
               takeWhileAntitone p l
           end.

Definition union {k} {a} `{GHC.Base.Ord k} : Map k a -> Map k a -> Map k a :=
  fix union arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | t1, Tip => t1
           | t1, Bin _ k x Tip Tip => insertR k x t1
           | Bin _ k x Tip Tip, t2 => insert k x t2
           | Tip, t2 => t2
           | (Bin _ k1 x1 l1 r1 as t1), t2 =>
               let 'pair l2 r2 := split k1 t2 in
               let r1r2 := union r1 r2 in
               let l1l2 := union l1 l2 in
               if andb (Utils.Containers.Internal.PtrEquality.ptrEq l1l2 l1)
                       (Utils.Containers.Internal.PtrEquality.ptrEq r1r2 r1) : bool
               then t1 else
               link k1 x1 l1l2 r1r2
           end.

Definition unions {f} {k} {a} `{Data.Foldable.Foldable f} `{GHC.Base.Ord k}
   : f (Map k a) -> Map k a :=
  fun ts => Data.Foldable.foldl' union empty ts.

Local Definition Monoid__Map_mconcat {inst_k} {inst_v} `{(GHC.Base.Ord inst_k)}
   : list (Map inst_k inst_v) -> (Map inst_k inst_v) :=
  unions.

Local Definition Semigroup__Map_op_zlzlzgzg__ {inst_k} {inst_v} `{(GHC.Base.Ord
   inst_k)}
   : (Map inst_k inst_v) -> (Map inst_k inst_v) -> (Map inst_k inst_v) :=
  union.

Program Instance Semigroup__Map {k} {v} `{(GHC.Base.Ord k)}
   : GHC.Base.Semigroup (Map k v) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__Map_op_zlzlzgzg__ |}.

Local Definition Monoid__Map_mappend {inst_k} {inst_v} `{(GHC.Base.Ord inst_k)}
   : (Map inst_k inst_v) -> (Map inst_k inst_v) -> (Map inst_k inst_v) :=
  _GHC.Base.<<>>_.

Program Instance Monoid__Map {k} {v} `{(GHC.Base.Ord k)}
   : GHC.Base.Monoid (Map k v) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Map_mappend ;
         GHC.Base.mconcat__ := Monoid__Map_mconcat ;
         GHC.Base.mempty__ := Monoid__Map_mempty |}.

Definition unionWith {k} {a} `{GHC.Base.Ord k}
   : (a -> a -> a) -> Map k a -> Map k a -> Map k a :=
  fix unionWith arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _f, t1, Tip => t1
           | f, t1, Bin _ k x Tip Tip => insertWithR f k x t1
           | f, Bin _ k x Tip Tip, t2 => insertWith f k x t2
           | _f, Tip, t2 => t2
           | f, Bin _ k1 x1 l1 r1, t2 =>
               let 'pair (pair l2 mb) r2 := splitLookup k1 t2 in
               let r1r2 := unionWith f r1 r2 in
               let l1l2 := unionWith f l1 l2 in
               match mb with
               | None => link k1 x1 l1l2 r1r2
               | Some x2 => link k1 (f x1 x2) l1l2 r1r2
               end
           end.

Definition unionsWith {f} {k} {a} `{Data.Foldable.Foldable f} `{GHC.Base.Ord k}
   : (a -> a -> a) -> f (Map k a) -> Map k a :=
  fun f ts => Data.Foldable.foldl' (unionWith f) empty ts.

Definition unionWithKey {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> a -> a) -> Map k a -> Map k a -> Map k a :=
  fix unionWithKey arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _f, t1, Tip => t1
           | f, t1, Bin _ k x Tip Tip => insertWithKeyR f k x t1
           | f, Bin _ k x Tip Tip, t2 => insertWithKey f k x t2
           | _f, Tip, t2 => t2
           | f, Bin _ k1 x1 l1 r1, t2 =>
               let 'pair (pair l2 mb) r2 := splitLookup k1 t2 in
               let r1r2 := unionWithKey f r1 r2 in
               let l1l2 := unionWithKey f l1 l2 in
               match mb with
               | None => link k1 x1 l1l2 r1r2
               | Some x2 => link k1 (f k1 x1 x2) l1l2 r1r2
               end
           end.

Definition maxViewSure {k} {a} : k -> a -> Map k a -> Map k a -> MaxView k a :=
  let fix go arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | k, x, l, Tip => Mk_MaxView k x l
               | k, x, l, Bin _ kr xr rl rr =>
                   let 'Mk_MaxView km xm r' := go kr xr rl rr in
                   Mk_MaxView km xm (balanceL k x l r')
               end in
  go.

Definition maxViewWithKey {k} {a}
   : Map k a -> option ((k * a)%type * Map k a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Tip => None
    | Bin _ k x l r =>
        Some (let 'Mk_MaxView km xm t := maxViewSure k x l r in pair (pair km xm) t)
    end.

Definition maxView {k} {a} : Map k a -> option (a * Map k a)%type :=
  fun t =>
    match maxViewWithKey t with
    | None => None
    | Some (pair (pair _ x) t') => Some (pair x t')
    end.

Definition glue {k} {a} : Map k a -> Map k a -> Map k a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Tip, r => r
    | l, Tip => l
    | (Bin sl kl xl ll lr as l), (Bin sr kr xr rl rr as r) =>
        if sl GHC.Base.> sr : bool
        then let 'Mk_MaxView km m l' := maxViewSure kl xl ll lr in
             balanceR km m l' r else
        let 'Mk_MinView km m r' := minViewSure kr xr rl rr in
        balanceL km m l r'
    end.

Definition delete {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k} : k -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__
          := match arg_0__, arg_1__ with
             | _, Tip => Tip
             | k, (Bin _ kx x l r as t) =>
                 match GHC.Base.compare k kx with
                 | Lt =>
                     let l' := go k l in
                     if Utils.Containers.Internal.PtrEquality.ptrEq l' l : bool then t else
                     balanceR kx x l' r
                 | Gt =>
                     let r' := go k r in
                     if Utils.Containers.Internal.PtrEquality.ptrEq r' r : bool then t else
                     balanceL kx x l r'
                 | Eq => glue l r
                 end
             end in
  go.

Program Fixpoint link2 {k} {a} (arg_0__ : Map k a) (arg_1__ : Map k a)
                       {measure (Nat.add (map_size arg_0__) (map_size arg_1__))} : Map k a
                   := match arg_0__, arg_1__ with
                      | Tip, r => r
                      | l, Tip => l
                      | (Bin sizeL kx x lx rx as l), (Bin sizeR ky y ly ry as r) =>
                          if Bool.Sumbool.sumbool_of_bool ((delta GHC.Num.* sizeL) GHC.Base.< sizeR)
                          then balanceL ky y (link2 l ly) ry else
                          if Bool.Sumbool.sumbool_of_bool ((delta GHC.Num.* sizeR) GHC.Base.< sizeL)
                          then balanceR kx x lx (link2 rx r) else
                          glue l r
                      end.
Solve Obligations with (termination_by_omega).

Definition filterWithKey {k} {a} : (k -> a -> bool) -> Map k a -> Map k a :=
  fix filterWithKey arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Tip => Tip
           | p, (Bin _ kx x l r as t) =>
               let pr := filterWithKey p r in
               let pl := filterWithKey p l in
               if p kx x : bool
               then if andb (Utils.Containers.Internal.PtrEquality.ptrEq pl l)
                            (Utils.Containers.Internal.PtrEquality.ptrEq pr r) : bool
                    then t
                    else link kx x pl pr else
               link2 pl pr
           end.

Definition filter {a} {k} : (a -> bool) -> Map k a -> Map k a :=
  fun p m =>
    filterWithKey (fun arg_0__ arg_1__ =>
                     match arg_0__, arg_1__ with
                     | _, x => p x
                     end) m.

Definition filterMissing {f} {k} {x} `{GHC.Base.Applicative f}
   : (k -> x -> bool) -> WhenMissing f k x x :=
  fun f =>
    Mk_WhenMissing (fun m => GHC.Base.pure (filterWithKey f m)) (fun k x =>
                      GHC.Base.pure (if f k x : bool then Some x else None)).

Definition filterWithKeyA {f} {k} {a} `{GHC.Base.Applicative f}
   : (k -> a -> f bool) -> Map k a -> f (Map k a) :=
  fix filterWithKeyA arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Tip => GHC.Base.pure Tip
           | p, (Bin _ kx x l r as t) =>
               let combine :=
                 fun arg_3__ arg_4__ arg_5__ =>
                   match arg_3__, arg_4__, arg_5__ with
                   | true, pl, pr =>
                       if andb (Utils.Containers.Internal.PtrEquality.ptrEq pl l)
                               (Utils.Containers.Internal.PtrEquality.ptrEq pr r) : bool
                       then t else
                       link kx x pl pr
                   | false, pl, pr => link2 pl pr
                   end in
               GHC.Base.liftA3 combine (p kx x) (filterWithKeyA p l) (filterWithKeyA p r)
           end.

Definition filterAMissing {f} {k} {x} `{GHC.Base.Applicative f}
   : (k -> x -> f bool) -> WhenMissing f k x x :=
  fun f =>
    Mk_WhenMissing (fun m => filterWithKeyA f m) (fun k x =>
                      boolITE None (Some x) Data.Functor.<$> f k x).

Definition intersection {k} {a} {b} `{GHC.Base.Ord k}
   : Map k a -> Map k b -> Map k a :=
  fix intersection arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | Tip, _ => Tip
           | _, Tip => Tip
           | (Bin _ k x l1 r1 as t1), t2 =>
               let 'pair (pair l2 mb) r2 := splitMember k t2 in
               let l1l2 := intersection l1 l2 in
               let r1r2 := intersection r1 r2 in
               if mb : bool
               then if andb (Utils.Containers.Internal.PtrEquality.ptrEq l1l2 l1)
                            (Utils.Containers.Internal.PtrEquality.ptrEq r1r2 r1) : bool
                    then t1
                    else link k x l1l2 r1r2 else
               link2 l1l2 r1r2
           end.

Definition intersectionWith {k} {a} {b} {c} `{GHC.Base.Ord k}
   : (a -> b -> c) -> Map k a -> Map k b -> Map k c :=
  fix intersectionWith arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _f, Tip, _ => Tip
           | _f, _, Tip => Tip
           | f, Bin _ k x1 l1 r1, t2 =>
               let 'pair (pair l2 mb) r2 := splitLookup k t2 in
               let l1l2 := intersectionWith f l1 l2 in
               let r1r2 := intersectionWith f r1 r2 in
               match mb with
               | Some x2 => link k (f x1 x2) l1l2 r1r2
               | None => link2 l1l2 r1r2
               end
           end.

Definition intersectionWithKey {k} {a} {b} {c} `{GHC.Base.Ord k}
   : (k -> a -> b -> c) -> Map k a -> Map k b -> Map k c :=
  fix intersectionWithKey arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _f, Tip, _ => Tip
           | _f, _, Tip => Tip
           | f, Bin _ k x1 l1 r1, t2 =>
               let 'pair (pair l2 mb) r2 := splitLookup k t2 in
               let l1l2 := intersectionWithKey f l1 l2 in
               let r1r2 := intersectionWithKey f r1 r2 in
               match mb with
               | Some x2 => link k (f k x1 x2) l1l2 r1r2
               | None => link2 l1l2 r1r2
               end
           end.

Definition mapEitherWithKey {k} {a} {b} {c}
   : (k -> a -> Data.Either.Either b c) -> Map k a -> (Map k b * Map k c)%type :=
  fun f0 t0 =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | _, Tip => (pair Tip Tip)
                 | f, Bin _ kx x l r =>
                     let 'pair r1 r2 := go f r in
                     let 'pair l1 l2 := go f l in
                     match f kx x with
                     | Data.Either.Left y => pair (link kx y l1 r1) (link2 l2 r2)
                     | Data.Either.Right z => pair (link2 l1 r1) (link kx z l2 r2)
                     end
                 end in
    id (go f0 t0).

Definition mapEither {a} {b} {c} {k}
   : (a -> Data.Either.Either b c) -> Map k a -> (Map k b * Map k c)%type :=
  fun f m =>
    mapEitherWithKey (fun arg_0__ arg_1__ =>
                        match arg_0__, arg_1__ with
                        | _, x => f x
                        end) m.

Definition mapMaybeWithKey {k} {a} {b}
   : (k -> a -> option b) -> Map k a -> Map k b :=
  fix mapMaybeWithKey arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Tip => Tip
           | f, Bin _ kx x l r =>
               match f kx x with
               | Some y => link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
               | None => link2 (mapMaybeWithKey f l) (mapMaybeWithKey f r)
               end
           end.

Definition mapMaybe {a} {b} {k} : (a -> option b) -> Map k a -> Map k b :=
  fun f =>
    mapMaybeWithKey (fun arg_0__ arg_1__ =>
                       match arg_0__, arg_1__ with
                       | _, x => f x
                       end).

Definition mapMaybeMissing {f} {k} {x} {y} `{GHC.Base.Applicative f}
   : (k -> x -> option y) -> WhenMissing f k x y :=
  fun f =>
    Mk_WhenMissing (fun m => GHC.Base.pure (mapMaybeWithKey f m)) (fun k x =>
                      GHC.Base.pure (f k x)).

Definition mergeA {f} {k} {a} {c} {b} `{GHC.Base.Applicative f} `{GHC.Base.Ord
  k}
   : WhenMissing f k a c ->
     WhenMissing f k b c ->
     WhenMatched f k a b c -> Map k a -> Map k b -> f (Map k c) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_WhenMissing g1t g1k, Mk_WhenMissing g2t _, Mk_WhenMatched f =>
        let fix go arg_3__ arg_4__
                  := match arg_3__, arg_4__ with
                     | t1, Tip => g1t t1
                     | Tip, t2 => g2t t2
                     | Bin _ kx x1 l1 r1, t2 =>
                         let 'pair (pair l2 mx2) r2 := splitLookup kx t2 in
                         let r1r2 := go r1 r2 in
                         let l1l2 := go l1 l2 in
                         match mx2 with
                         | None =>
                             GHC.Base.liftA3 (fun l' mx' r' => Data.Maybe.maybe link2 (link kx) mx' l' r')
                             l1l2 (g1k kx x1) r1r2
                         | Some x2 =>
                             GHC.Base.liftA3 (fun l' mx' r' => Data.Maybe.maybe link2 (link kx) mx' l' r')
                             l1l2 (f kx x1 x2) r1r2
                         end
                     end in
        go
    end.

Definition merge {k} {a} {c} {b} `{GHC.Base.Ord k}
   : SimpleWhenMissing k a c ->
     SimpleWhenMissing k b c ->
     SimpleWhenMatched k a b c -> Map k a -> Map k b -> Map k c :=
  fun g1 g2 f m1 m2 => Data.Functor.Identity.runIdentity (mergeA g1 g2 f m1 m2).

Definition mergeWithKey {k} {a} {b} {c} `{GHC.Base.Ord k}
   : (k -> a -> b -> option c) ->
     (Map k a -> Map k c) -> (Map k b -> Map k c) -> Map k a -> Map k b -> Map k c :=
  fun f g1 g2 =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | Tip, t2 => g2 t2
                 | t1, Tip => g1 t1
                 | Bin _ kx x l1 r1, t2 =>
                     let 'pair (pair l2 found) r2 := splitLookup kx t2 in
                     let l' := go l1 l2 in
                     let r' := go r1 r2 in
                     match found with
                     | None =>
                         match g1 (singleton kx x) with
                         | Tip => link2 l' r'
                         | Bin _ _ x' Tip Tip => link kx x' l' r'
                         | _ =>
                             GHC.Err.error (GHC.Base.hs_string__
                                            "mergeWithKey: Given function only1 does not fulfill required conditions (see documentation)")
                         end
                     | Some x2 =>
                         match f kx x x2 with
                         | None => link2 l' r'
                         | Some x' => link kx x' l' r'
                         end
                     end
                 end in
    go.

Definition partitionWithKey {k} {a}
   : (k -> a -> bool) -> Map k a -> (Map k a * Map k a)%type :=
  fun p0 t0 =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | _, Tip => (pair Tip Tip)
                 | p, (Bin _ kx x l r as t) =>
                     let 'pair r1 r2 := go p r in
                     let 'pair l1 l2 := go p l in
                     if p kx x : bool
                     then pair (if andb (Utils.Containers.Internal.PtrEquality.ptrEq l1 l)
                                        (Utils.Containers.Internal.PtrEquality.ptrEq r1 r) : bool
                                then t
                                else link kx x l1 r1) (link2 l2 r2) else
                     pair (link2 l1 r1) (if andb (Utils.Containers.Internal.PtrEquality.ptrEq l2 l)
                                                 (Utils.Containers.Internal.PtrEquality.ptrEq r2 r) : bool
                           then t
                           else link kx x l2 r2)
                 end in
    id (go p0 t0).

Definition partition {a} {k}
   : (a -> bool) -> Map k a -> (Map k a * Map k a)%type :=
  fun p m =>
    partitionWithKey (fun arg_0__ arg_1__ =>
                        match arg_0__, arg_1__ with
                        | _, x => p x
                        end) m.

Definition restrictKeys {k} {a} `{GHC.Base.Ord k}
   : Map k a -> Data.Set.Internal.Set_ k -> Map k a :=
  fix restrictKeys arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | Tip, _ => Tip
           | _, Data.Set.Internal.Tip => Tip
           | (Bin _ k x l1 r1 as m), s =>
               let 'pair (pair l2 b) r2 := Data.Set.Internal.splitMember k s in
               let l1l2 := restrictKeys l1 l2 in
               let r1r2 := restrictKeys r1 r2 in
               if b : bool
               then if andb (Utils.Containers.Internal.PtrEquality.ptrEq l1l2 l1)
                            (Utils.Containers.Internal.PtrEquality.ptrEq r1r2 r1) : bool
                    then m
                    else link k x l1l2 r1r2 else
               link2 l1l2 r1r2
           end.

Definition traverseMaybeWithKey {f} {k} {a} {b} `{GHC.Base.Applicative f}
   : (k -> a -> f (option b)) -> Map k a -> f (Map k b) :=
  let fix go arg_0__ arg_1__
            := match arg_0__, arg_1__ with
               | _, Tip => GHC.Base.pure Tip
               | f, Bin _ kx x Tip Tip =>
                   Data.Maybe.maybe Tip (fun x' => Bin #1 kx x' Tip Tip) Data.Functor.<$> f kx x
               | f, Bin _ kx x l r =>
                   let combine :=
                     fun l' mx r' =>
                       match mx with
                       | None => link2 l' r'
                       | Some x' => link kx x' l' r'
                       end in
                   GHC.Base.liftA3 combine (go f l) (f kx x) (go f r)
               end in
  go.

Definition traverseMaybeMissing {f} {k} {x} {y} `{GHC.Base.Applicative f}
   : (k -> x -> f (option y)) -> WhenMissing f k x y :=
  fun f => Mk_WhenMissing (traverseMaybeWithKey f) f.

Definition withoutKeys {k} {a} `{GHC.Base.Ord k}
   : Map k a -> Data.Set.Internal.Set_ k -> Map k a :=
  fix withoutKeys arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | Tip, _ => Tip
           | m, Data.Set.Internal.Tip => m
           | m, Data.Set.Internal.Bin _ k ls rs =>
               let 'pair (pair lm b) rm := splitMember k m in
               let rm' := withoutKeys rm rs in
               let lm' := withoutKeys lm ls in
               if andb (negb b) (andb (Utils.Containers.Internal.PtrEquality.ptrEq lm' lm)
                                      (Utils.Containers.Internal.PtrEquality.ptrEq rm' rm)) : bool
               then m else
               link2 lm' rm'
           end.

Definition updateLookupWithKey {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> option a) -> k -> Map k a -> (option a * Map k a)%type :=
  fun f0 k0 =>
    let go {k} {a} `{GHC.Base.Ord k}
     : (k -> a -> option a) -> k -> Map k a -> prod (option a) (Map k a) :=
      fix go arg_0__ arg_1__ arg_2__
            := match arg_0__, arg_1__, arg_2__ with
               | _, _, Tip => (pair None Tip)
               | f, k, Bin sx kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt =>
                       let 'pair found l' := go f k l in
                       let t' := balanceR kx x l' r in (pair found t')
                   | Gt =>
                       let 'pair found r' := go f k r in
                       let t' := balanceL kx x l r' in (pair found t')
                   | Eq =>
                       match f kx x with
                       | Some x' => (pair (Some x') (Bin sx kx x' l r))
                       | None => let glued := glue l r in (pair (Some x) glued)
                       end
                   end
               end in
    id GHC.Base.∘ go f0 k0.

Definition updateMaxWithKey {k} {a}
   : (k -> a -> option a) -> Map k a -> Map k a :=
  fix updateMaxWithKey arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Tip => Tip
           | f, Bin sx kx x l Tip =>
               match f kx x with
               | None => l
               | Some x' => Bin sx kx x' l Tip
               end
           | f, Bin _ kx x l r => balanceL kx x l (updateMaxWithKey f r)
           end.

Definition updateMax {a} {k} : (a -> option a) -> Map k a -> Map k a :=
  fun f m =>
    updateMaxWithKey (fun arg_0__ arg_1__ =>
                        match arg_0__, arg_1__ with
                        | _, x => f x
                        end) m.

Definition updateWithKey {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> option a) -> k -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k}
   : (k -> a -> option a) -> k -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__
          := match arg_0__, arg_1__, arg_2__ with
             | _, _, Tip => Tip
             | f, k, Bin sx kx x l r =>
                 match GHC.Base.compare k kx with
                 | Lt => balanceR kx x (go f k l) r
                 | Gt => balanceL kx x l (go f k r)
                 | Eq => match f kx x with | Some x' => Bin sx kx x' l r | None => glue l r end
                 end
             end in
  go.

Definition update {k} {a} `{GHC.Base.Ord k}
   : (a -> option a) -> k -> Map k a -> Map k a :=
  fun f =>
    updateWithKey (fun arg_0__ arg_1__ =>
                     match arg_0__, arg_1__ with
                     | _, x => f x
                     end).

Definition atKeyPlain {k} {a} `{GHC.Base.Ord k}
   : AreWeStrict -> k -> (option a -> option a) -> Map k a -> Map k a :=
  fun strict k0 f0 t =>
    let go {k} {a} `{GHC.Base.Ord k}
     : k -> (option a -> option a) -> Map k a -> Altered k a :=
      fix go arg_0__ arg_1__ arg_2__
            := match arg_0__, arg_1__, arg_2__ with
               | k, f, Tip =>
                   match f None with
                   | None => AltSame
                   | Some x =>
                       match strict with
                       | Lazy => AltBigger (singleton k x)
                       | Strict => GHC.Prim.seq x (AltBigger (singleton k x))
                       end
                   end
               | k, f, Bin sx kx x l r =>
                   match GHC.Base.compare k kx with
                   | Lt =>
                       match go k f l with
                       | AltSmaller l' => AltSmaller (balanceR kx x l' r)
                       | AltBigger l' => AltBigger (balanceL kx x l' r)
                       | AltAdj l' => AltAdj (Bin sx kx x l' r)
                       | AltSame => AltSame
                       end
                   | Gt =>
                       match go k f r with
                       | AltSmaller r' => AltSmaller (balanceL kx x l r')
                       | AltBigger r' => AltBigger (balanceR kx x l r')
                       | AltAdj r' => AltAdj (Bin sx kx x l r')
                       | AltSame => AltSame
                       end
                   | Eq =>
                       match f (Some x) with
                       | Some x' =>
                           match strict with
                           | Lazy => AltAdj (Bin sx kx x' l r)
                           | Strict => GHC.Prim.seq x' (AltAdj (Bin sx kx x' l r))
                           end
                       | None => AltSmaller (glue l r)
                       end
                   end
               end in
    match go k0 f0 t with
    | AltSmaller t' => t'
    | AltBigger t' => t'
    | AltAdj t' => t'
    | AltSame => t
    end.

Definition atKeyIdentity {k} {a} `{GHC.Base.Ord k}
   : k ->
     (option a -> Data.Functor.Identity.Identity (option a)) ->
     Map k a -> Data.Functor.Identity.Identity (Map k a) :=
  fun k f t =>
    Data.Functor.Identity.Mk_Identity (atKeyPlain Lazy k (GHC.Prim.coerce f) t).

Definition drop {k} {a} : GHC.Num.Int -> Map k a -> Map k a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | i, m =>
        if i GHC.Base.>= size m : bool then Tip else
        match arg_0__, arg_1__ with
        | i0, m0 =>
            let fix go arg_2__ arg_3__
                      := match arg_2__, arg_3__ with
                         | i, m =>
                             if i GHC.Base.<= #0 : bool then m else
                             match arg_2__, arg_3__ with
                             | _, Tip => Tip
                             | i, Bin _ kx x l r =>
                                 let sizeL := size l in
                                 match GHC.Base.compare i sizeL with
                                 | Lt => link kx x (go i l) r
                                 | Gt => go ((i GHC.Num.- sizeL) GHC.Num.- #1) r
                                 | Eq => insertMin kx x r
                                 end
                             end
                         end in
            go i0 m0
        end
    end.

Definition splitAt {k} {a}
   : GHC.Num.Int -> Map k a -> (Map k a * Map k a)%type :=
  fun i0 m0 =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | i, m =>
                     if i GHC.Base.<= #0 : bool then pair Tip m else
                     match arg_0__, arg_1__ with
                     | _, Tip => pair Tip Tip
                     | i, Bin _ kx x l r =>
                         let sizeL := size l in
                         match GHC.Base.compare i sizeL with
                         | Lt => let 'pair ll lr := go i l in pair ll (link kx x lr r)
                         | Gt =>
                             let 'pair rl rr := go ((i GHC.Num.- sizeL) GHC.Num.- #1) r in
                             pair (link kx x l rl) rr
                         | Eq => pair l (insertMin kx x r)
                         end
                     end
                 end in
    if i0 GHC.Base.>= size m0 : bool then pair m0 Tip else
    id (go i0 m0).

Definition isProperSubmapOfBy {k} {a} {b} `{GHC.Base.Ord k}
   : (a -> b -> bool) -> Map k a -> Map k b -> bool :=
  fun f t1 t2 => andb (size t1 GHC.Base.< size t2) (submap' f t1 t2).

Definition isProperSubmapOf {k} {a} `{GHC.Base.Ord k} `{GHC.Base.Eq_ a}
   : Map k a -> Map k a -> bool :=
  fun m1 m2 => isProperSubmapOfBy _GHC.Base.==_ m1 m2.

Definition isSubmapOfBy {k} {a} {b} `{GHC.Base.Ord k}
   : (a -> b -> bool) -> Map k a -> Map k b -> bool :=
  fun f t1 t2 => andb (size t1 GHC.Base.<= size t2) (submap' f t1 t2).

Definition isSubmapOf {k} {a} `{GHC.Base.Ord k} `{GHC.Base.Eq_ a}
   : Map k a -> Map k a -> bool :=
  fun m1 m2 => isSubmapOfBy _GHC.Base.==_ m1 m2.

Definition take {k} {a} : GHC.Num.Int -> Map k a -> Map k a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | i, m =>
        if i GHC.Base.>= size m : bool then m else
        match arg_0__, arg_1__ with
        | i0, m0 =>
            let fix go arg_2__ arg_3__
                      := match arg_2__, arg_3__ with
                         | i, _ =>
                             if i GHC.Base.<= #0 : bool then Tip else
                             match arg_2__, arg_3__ with
                             | _, Tip => Tip
                             | i, Bin _ kx x l r =>
                                 let sizeL := size l in
                                 match GHC.Base.compare i sizeL with
                                 | Lt => go i l
                                 | Gt => link kx x l (go ((i GHC.Num.- sizeL) GHC.Num.- #1) r)
                                 | Eq => l
                                 end
                             end
                         end in
            go i0 m0
        end
    end.

Definition deleteAt {k} {a} : GHC.Num.Int -> Map k a -> Map k a :=
  fix deleteAt i t
        := match t with
           | Tip => GHC.Err.error (GHC.Base.hs_string__ "Map.deleteAt: index out of range")
           | Bin _ kx x l r =>
               let sizeL := size l in
               match GHC.Base.compare i sizeL with
               | Lt => balanceR kx x (deleteAt i l) r
               | Gt => balanceL kx x l (deleteAt ((i GHC.Num.- sizeL) GHC.Num.- #1) r)
               | Eq => glue l r
               end
           end.

Definition difference {k} {a} {b} `{GHC.Base.Ord k}
   : Map k a -> Map k b -> Map k a :=
  fix difference arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | Tip, _ => Tip
           | t1, Tip => t1
           | t1, Bin _ k _ l2 r2 =>
               let 'pair l1 r1 := split k t1 in
               let r1r2 := difference r1 r2 in
               let l1l2 := difference l1 l2 in
               if (size l1l2 GHC.Num.+ size r1r2) GHC.Base.== size t1 : bool then t1 else
               link2 l1l2 r1r2
           end.

Definition op_zrzr__ {k} {a} {b} `{GHC.Base.Ord k}
   : Map k a -> Map k b -> Map k a :=
  fun m1 m2 => difference m1 m2.

Notation "'_\\_'" := (op_zrzr__).

Infix "\\" := (_\\_) (at level 99).

Definition updateAt {k} {a}
   : (k -> a -> option a) -> GHC.Num.Int -> Map k a -> Map k a :=
  fix updateAt f i t
        := match t with
           | Tip => GHC.Err.error (GHC.Base.hs_string__ "Map.updateAt: index out of range")
           | Bin sx kx x l r =>
               let sizeL := size l in
               match GHC.Base.compare i sizeL with
               | Lt => balanceR kx x (updateAt f i l) r
               | Gt => balanceL kx x l (updateAt f ((i GHC.Num.- sizeL) GHC.Num.- #1) r)
               | Eq => match f kx x with | Some x' => Bin sx kx x' l r | None => glue l r end
               end
           end.

Definition balance {k} {a} : k -> a -> Map k a -> Map k a -> Map k a :=
  fun k x l r =>
    match l with
    | Tip =>
        match r with
        | Tip => Bin #1 k x Tip Tip
        | Bin _ _ _ Tip Tip => Bin #2 k x Tip r
        | Bin _ rk rx Tip (Bin _ _ _ _ _ as rr) => Bin #3 rk rx (Bin #1 k x Tip Tip) rr
        | Bin _ rk rx (Bin _ rlk rlx _ _) Tip =>
            Bin #3 rlk rlx (Bin #1 k x Tip Tip) (Bin #1 rk rx Tip Tip)
        | Bin rs rk rx (Bin rls rlk rlx rll rlr as rl) (Bin rrs _ _ _ _ as rr) =>
            if rls GHC.Base.< (ratio GHC.Num.* rrs) : bool
            then Bin (#1 GHC.Num.+ rs) rk rx (Bin (#1 GHC.Num.+ rls) k x Tip rl) rr else
            Bin (#1 GHC.Num.+ rs) rlk rlx (Bin (#1 GHC.Num.+ size rll) k x Tip rll) (Bin
                                                                                     ((#1 GHC.Num.+ rrs) GHC.Num.+
                                                                                      size rlr) rk rx rlr rr)
        end
    | Bin ls lk lx ll lr =>
        match r with
        | Tip =>
            match pair ll lr with
            | pair Tip Tip => Bin #2 k x l Tip
            | pair Tip (Bin _ lrk lrx _ _) =>
                Bin #3 lrk lrx (Bin #1 lk lx Tip Tip) (Bin #1 k x Tip Tip)
            | pair (Bin _ _ _ _ _) Tip => Bin #3 lk lx ll (Bin #1 k x Tip Tip)
            | pair (Bin lls _ _ _ _) (Bin lrs lrk lrx lrl lrr) =>
                if lrs GHC.Base.< (ratio GHC.Num.* lls) : bool
                then Bin (#1 GHC.Num.+ ls) lk lx ll (Bin (#1 GHC.Num.+ lrs) k x lr Tip) else
                Bin (#1 GHC.Num.+ ls) lrk lrx (Bin ((#1 GHC.Num.+ lls) GHC.Num.+ size lrl) lk lx
                                               ll lrl) (Bin (#1 GHC.Num.+ size lrr) k x lrr Tip)
            end
        | Bin rs rk rx rl rr =>
            if rs GHC.Base.> (delta GHC.Num.* ls) : bool
            then let scrut_24__ := pair rl rr in
                 match scrut_24__ with
                 | pair (Bin rls rlk rlx rll rlr) (Bin rrs _ _ _ _) =>
                     if rls GHC.Base.< (ratio GHC.Num.* rrs) : bool
                     then Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) rk rx (Bin ((#1 GHC.Num.+ ls)
                                                                           GHC.Num.+
                                                                           rls) k x l rl) rr else
                     Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) rlk rlx (Bin ((#1 GHC.Num.+ ls) GHC.Num.+
                                                                        size rll) k x l rll) (Bin ((#1 GHC.Num.+ rrs)
                                                                                                   GHC.Num.+
                                                                                                   size rlr) rk rx rlr
                                                                                              rr)
                 | _ =>
                     let 'pair _ _ := scrut_24__ in
                     GHC.Err.error (GHC.Base.hs_string__ "Failure in Data.Map.balance")
                 end else
            if ls GHC.Base.> (delta GHC.Num.* rs) : bool
            then let scrut_17__ := pair ll lr in
                 match scrut_17__ with
                 | pair (Bin lls _ _ _ _) (Bin lrs lrk lrx lrl lrr) =>
                     if lrs GHC.Base.< (ratio GHC.Num.* lls) : bool
                     then Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) lk lx ll (Bin ((#1 GHC.Num.+ rs)
                                                                              GHC.Num.+
                                                                              lrs) k x lr r) else
                     Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) lrk lrx (Bin ((#1 GHC.Num.+ lls) GHC.Num.+
                                                                        size lrl) lk lx ll lrl) (Bin ((#1 GHC.Num.+ rs)
                                                                                                      GHC.Num.+
                                                                                                      size lrr) k x lrr
                                                                                                 r)
                 | _ =>
                     let 'pair _ _ := scrut_17__ in
                     GHC.Err.error (GHC.Base.hs_string__ "Failure in Data.Map.balance")
                 end else
            Bin ((#1 GHC.Num.+ ls) GHC.Num.+ rs) k x l r
        end
    end.

Definition alter {k} {a} `{GHC.Base.Ord k}
   : (option a -> option a) -> k -> Map k a -> Map k a :=
  let go {k} {a} `{GHC.Base.Ord k}
   : (option a -> option a) -> k -> Map k a -> Map k a :=
    fix go arg_0__ arg_1__ arg_2__
          := match arg_0__, arg_1__, arg_2__ with
             | f, k, Tip => match f None with | None => Tip | Some x => singleton k x end
             | f, k, Bin sx kx x l r =>
                 match GHC.Base.compare k kx with
                 | Lt => balance kx x (go f k l) r
                 | Gt => balance kx x l (go f k r)
                 | Eq =>
                     match f (Some x) with
                     | Some x' => Bin sx kx x' l r
                     | None => glue l r
                     end
                 end
             end in
  go.

Local Definition Foldable__Map_length {inst_k}
   : forall {a}, (Map inst_k) a -> GHC.Num.Int :=
  fun {a} => size.

Program Instance Foldable__Map {k} : Data.Foldable.Foldable (Map k) :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__Map_fold ;
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

Local Definition Eq2__Map_liftEq2
   : forall {a} {b} {c} {d},
     (a -> b -> bool) -> (c -> d -> bool) -> Map a c -> Map b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun eqk eqv m n =>
      andb (size m GHC.Base.== size n) (Data.Functor.Classes.liftEq
            (Data.Functor.Classes.liftEq2 eqk eqv) (toList m) (toList n)).

Program Instance Eq2__Map : Data.Functor.Classes.Eq2 Map :=
  fun _ k =>
    k {| Data.Functor.Classes.liftEq2__ := fun {a} {b} {c} {d} =>
           Eq2__Map_liftEq2 |}.

Program Instance Ord2__Map : Data.Functor.Classes.Ord2 Map :=
  fun _ k =>
    k {| Data.Functor.Classes.liftCompare2__ := fun {a} {b} {c} {d} =>
           Ord2__Map_liftCompare2 |}.

Local Definition Eq___Map_op_zeze__ {inst_k} {inst_a} `{GHC.Base.Eq_ inst_k}
  `{GHC.Base.Eq_ inst_a}
   : (Map inst_k inst_a) -> (Map inst_k inst_a) -> bool :=
  fun t1 t2 =>
    andb (size t1 GHC.Base.== size t2) (toAscList t1 GHC.Base.== toAscList t2).

Local Definition Eq___Map_op_zsze__ {inst_k} {inst_a} `{GHC.Base.Eq_ inst_k}
  `{GHC.Base.Eq_ inst_a}
   : (Map inst_k inst_a) -> (Map inst_k inst_a) -> bool :=
  fun x y => negb (Eq___Map_op_zeze__ x y).

Program Instance Eq___Map {k} {a} `{GHC.Base.Eq_ k} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Map k a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Map_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Map_op_zsze__ |}.

Program Instance Ord__Map {k} {v} `{GHC.Base.Ord k} `{GHC.Base.Ord v}
   : GHC.Base.Ord (Map k v) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Map_op_zl__ ;
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
              := match arg_0__ with
                 | Tip => GHC.Base.pure Tip
                 | Bin num_1__ k v _ _ =>
                     if num_1__ GHC.Base.== #1 : bool
                     then (fun v' => Bin #1 k v' Tip Tip) Data.Functor.<$> f k v else
                     match arg_0__ with
                     | Bin s k v l r =>
                         GHC.Base.liftA3 (GHC.Base.flip (Bin s k)) (go l) (f k v) (go r)
                     | _ => GHC.Err.patternFailure
                     end
                 end in
    go.

Definition traverseMissing {f} {k} {x} {y} `{GHC.Base.Applicative f}
   : (k -> x -> f y) -> WhenMissing f k x y :=
  fun f =>
    Mk_WhenMissing (traverseWithKey f) (fun k x => Some Data.Functor.<$> f k x).

Local Definition Traversable__Map_traverse {inst_k}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Map inst_k) a -> f ((Map inst_k) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun f => traverseWithKey (fun arg_0__ => f).

Local Definition Traversable__Map_mapM {inst_k}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Map inst_k) a -> m ((Map inst_k) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Map_traverse.

Local Definition Traversable__Map_sequenceA {inst_k}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, (Map inst_k) (f a) -> f ((Map inst_k) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Map_traverse GHC.Base.id.

Local Definition Traversable__Map_sequence {inst_k}
   : forall {m} {a},
     forall `{GHC.Base.Monad m}, (Map inst_k) (m a) -> m ((Map inst_k) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Map_sequenceA.

Program Instance Traversable__Map {k} : Data.Traversable.Traversable (Map k) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Map_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Map_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Map_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Map_traverse |}.

Definition zipWithAMatched {f} {k} {x} {y} {z} `{GHC.Base.Applicative f}
   : (k -> x -> y -> f z) -> WhenMatched f k x y z :=
  fun f => Mk_WhenMatched (fun k x y => Some Data.Functor.<$> f k x y).

Definition zipWithMatched {f} {k} {x} {y} {z} `{GHC.Base.Applicative f}
   : (k -> x -> y -> z) -> WhenMatched f k x y z :=
  fun f =>
    Mk_WhenMatched (fun k x y => (GHC.Base.pure GHC.Base.∘ Some) (f k x y)).

Definition zipWithMaybeAMatched {k} {x} {y} {f} {z}
   : (k -> x -> y -> f (option z)) -> WhenMatched f k x y z :=
  fun f => Mk_WhenMatched (fun k x y => f k x y).

Definition mapGentlyWhenMatched {f} {a} {b} {k} {x} {y} `{GHC.Base.Functor f}
   : (a -> b) -> WhenMatched f k x y a -> WhenMatched f k x y b :=
  fun f t =>
    zipWithMaybeAMatched (fun k x y =>
                            GHC.Base.fmap f Data.Functor.<$> runWhenMatched t k x y).

Definition zipWithMaybeMatched {f} {k} {x} {y} {z} `{GHC.Base.Applicative f}
   : (k -> x -> y -> option z) -> WhenMatched f k x y z :=
  fun f => Mk_WhenMatched (fun k x y => GHC.Base.pure (f k x y)).

Module Notations.
Notation "'_Data.Map.Internal.!?_'" := (op_znz3fU__).
Infix "Data.Map.Internal.!?" := (_!?_) (at level 99).
Notation "'_Data.Map.Internal.\\_'" := (op_zrzr__).
Infix "Data.Map.Internal.\\" := (_\\_) (at level 99).
End Notations.

(* External variables:
     Bool.Sumbool.sumbool_of_bool Eq Gt Lt None Some Type andb bool comparison cons
     false functor__Map_op_zlzd__ id list map_size negb nil op_zt__ option pair prod
     true unit Data.Bits.shiftL Data.Bits.shiftR Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Foldable.Foldable Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl' Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr'__ Data.Foldable.foldr__
     Data.Foldable.length__ Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ Data.Functor.op_zlzdzg__
     Data.Functor.Classes.Eq2 Data.Functor.Classes.Ord2
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare2
     Data.Functor.Classes.liftCompare2__ Data.Functor.Classes.liftEq
     Data.Functor.Classes.liftEq2 Data.Functor.Classes.liftEq2__
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Functor.Identity.runIdentity Data.Maybe.maybe Data.Set.Internal.Bin
     Data.Set.Internal.Set_ Data.Set.Internal.Tip Data.Set.Internal.splitMember
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.compare
     GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.id GHC.Base.liftA3 GHC.Base.mappend GHC.Base.mappend__ GHC.Base.max__
     GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__
     GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zgzgze__
     GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlzd____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.pure
     GHC.DeferredFix.deferredFix2 GHC.DeferredFix.deferredFix3 GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.error GHC.Err.patternFailure GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__
     GHC.Prim.coerce GHC.Prim.seq Nat.add Utils.Containers.Internal.PtrEquality.ptrEq
*)
