(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require BitTerminationProofs.

(* Converted imports: *)

Require Coq.NArith.BinNat.
Require Coq.Numbers.BinNums.
Require Coq.ZArith.BinInt.
Require Data.Bits.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Identity.
Require Data.IntSet.Internal.
Require Data.Maybe.
Require Data.Traversable.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.Num.
Require Utils.Containers.Internal.BitUtil.
Import Data.Bits.Notations.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive WhenMatched f x y z : Type
  := Mk_WhenMatched (matchedKey
    : Data.IntSet.Internal.Key -> x -> y -> f (option z))
   : WhenMatched f x y z.

Definition SimpleWhenMatched :=
  (WhenMatched Data.Functor.Identity.Identity)%type.

Definition Prefix :=
  Coq.Numbers.BinNums.N%type.

Definition Nat :=
  GHC.Num.Word%type.

Definition Mask :=
  Coq.Numbers.BinNums.N%type.

Definition IntSetPrefix :=
  Coq.Numbers.BinNums.N%type.

Definition IntSetBitMap :=
  GHC.Num.Word%type.

Inductive IntMap a : Type
  := Bin : Prefix -> Mask -> (IntMap a) -> (IntMap a) -> IntMap a
  |  Tip : Data.IntSet.Internal.Key -> a -> IntMap a
  |  Nil : IntMap a.

Inductive SplitLookup a : Type
  := Mk_SplitLookup : (IntMap a) -> (option a) -> (IntMap a) -> SplitLookup a.

Inductive Stack a : Type
  := Push : Prefix -> (IntMap a) -> (Stack a) -> Stack a
  |  Nada : Stack a.

Inductive View a : Type
  := Mk_View : Data.IntSet.Internal.Key -> a -> (IntMap a) -> View a.

Inductive WhenMissing f x y : Type
  := Mk_WhenMissing (missingSubtree : IntMap x -> f (IntMap y)) (missingKey
    : Data.IntSet.Internal.Key -> x -> f (option y))
   : WhenMissing f x y.

Definition SimpleWhenMissing :=
  (WhenMissing Data.Functor.Identity.Identity)%type.

Arguments Mk_WhenMatched {_} {_} {_} {_} _.

Arguments Bin {_} _ _ _ _.

Arguments Tip {_} _ _.

Arguments Nil {_}.

Arguments Mk_SplitLookup {_} _ _ _.

Arguments Push {_} _ _ _.

Arguments Nada {_}.

Arguments Mk_View {_} _ _ _.

Arguments Mk_WhenMissing {_} {_} {_} _ _.

Definition matchedKey {f} {x} {y} {z} (arg_0__ : WhenMatched f x y z) :=
  let 'Mk_WhenMatched matchedKey := arg_0__ in
  matchedKey.

Definition missingKey {f} {x} {y} (arg_0__ : WhenMissing f x y) :=
  let 'Mk_WhenMissing _ missingKey := arg_0__ in
  missingKey.

Definition missingSubtree {f} {x} {y} (arg_0__ : WhenMissing f x y) :=
  let 'Mk_WhenMissing missingSubtree _ := arg_0__ in
  missingSubtree.

(* Midamble *)

Require GHC.Err.

Instance Default_Map {a} : Err.Default (IntMap a) := {| Err.default := Nil |}.

Fixpoint IntMap_op_zlzd__ {a} {b} (x: a) (m: IntMap b): IntMap a :=
      match x , m with
        | a , Bin p m l r => Bin p m (IntMap_op_zlzd__ a l)
                                (IntMap_op_zlzd__ a r)
        | a , Tip k _ => Tip k a
        | _ , Nil => Nil
      end.

Fixpoint size_nat {a} (t : IntMap a) : nat :=
  match t with
  | Bin _ _ l r => S (size_nat l + size_nat r)%nat
  | Tip _ _ => 0
  | Nil => 0
  end.

Require Omega.
Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.


Require Import Coq.Numbers.BinNums.

(* Converted value declarations: *)

Definition zipWithMaybeMatched {f} {x} {y} {z} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> x -> y -> option z) -> WhenMatched f x y z :=
  fun f => Mk_WhenMatched (fun k x y => GHC.Base.pure (f k x y)).

Definition zipWithMaybeAMatched {x} {y} {f} {z}
   : (Data.IntSet.Internal.Key -> x -> y -> f (option z)) ->
     WhenMatched f x y z :=
  fun f => Mk_WhenMatched (fun k x y => f k x y).

Definition zipWithMatched {f} {x} {y} {z} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> x -> y -> z) -> WhenMatched f x y z :=
  fun f =>
    Mk_WhenMatched (fun k x y => (GHC.Base.pure GHC.Base.∘ Some) (f k x y)).

Definition zipWithAMatched {f} {x} {y} {z} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> x -> y -> f z) -> WhenMatched f x y z :=
  fun f => Mk_WhenMatched (fun k x y => Some Data.Functor.<$> f k x y).

Definition unsafeFindMin {a}
   : IntMap a -> option (Data.IntSet.Internal.Key * a)%type :=
  fix unsafeFindMin arg_0__
        := match arg_0__ with
           | Nil => None
           | Tip ky y => Some (pair ky y)
           | Bin _ _ l _ => unsafeFindMin l
           end.

Definition unsafeFindMax {a}
   : IntMap a -> option (Data.IntSet.Internal.Key * a)%type :=
  fix unsafeFindMax arg_0__
        := match arg_0__ with
           | Nil => None
           | Tip ky y => Some (pair ky y)
           | Bin _ _ _ r => unsafeFindMax r
           end.

Definition traverseWithKey {t} {a} {b} `{GHC.Base.Applicative t}
   : (Data.IntSet.Internal.Key -> a -> t b) -> IntMap a -> t (IntMap b) :=
  fun f =>
    let fix go arg_0__
              := match arg_0__ with
                 | Nil => GHC.Base.pure Nil
                 | Tip k v => Tip k Data.Functor.<$> f k v
                 | Bin p m l r => GHC.Base.liftA2 (Bin p m) (go l) (go r)
                 end in
    go.

Definition traverseMissing {f} {x} {y} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> x -> f y) -> WhenMissing f x y :=
  fun f =>
    Mk_WhenMissing (traverseWithKey f) (fun k x => Some Data.Functor.<$> f k x).

Definition splitRoot {a} : IntMap a -> list (IntMap a) :=
  fun orig =>
    match orig with
    | Nil => nil
    | (Tip _ _ as x) => cons x nil
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool then cons r (cons l nil) else
        cons l (cons r nil)
    end.

Definition size {a} : IntMap a -> Coq.Numbers.BinNums.N :=
  let fix go arg_0__ arg_1__
            := match arg_0__, arg_1__ with
               | acc, Bin _ _ l r => go (go acc l) r
               | acc, Tip _ _ => #1 GHC.Num.+ acc
               | acc, Nil => acc
               end in
  go #0.

Definition singleton {a} : Data.IntSet.Internal.Key -> a -> IntMap a :=
  fun k x => Tip k x.

Definition shorter : Mask -> Mask -> bool :=
  fun m1 m2 => (m1) GHC.Base.> (m2).

Definition runWhenMissing {f} {x} {y}
   : WhenMissing f x y -> Data.IntSet.Internal.Key -> x -> f (option y) :=
  missingKey.

Definition runWhenMatched {f} {x} {y} {z}
   : WhenMatched f x y z -> Data.IntSet.Internal.Key -> x -> y -> f (option z) :=
  matchedKey.

Definition preserveMissing {f} {x} `{GHC.Base.Applicative f}
   : WhenMissing f x x :=
  Mk_WhenMissing GHC.Base.pure (fun arg_0__ arg_1__ =>
                    match arg_0__, arg_1__ with
                    | _, v => GHC.Base.pure (Some v)
                    end).

Definition null {a} : IntMap a -> bool :=
  fun arg_0__ => match arg_0__ with | Nil => true | _ => false end.

Definition nomatch : Data.IntSet.Internal.Key -> Prefix -> Mask -> bool :=
  fun i p m => (Data.IntSet.Internal.mask i m) GHC.Base./= p.

Definition node : GHC.Base.String :=
  GHC.Base.hs_string__ "+--".

Definition nequal {a} `{GHC.Base.Eq_ a} : IntMap a -> IntMap a -> bool :=
  fix nequal arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | Bin p1 m1 l1 r1, Bin p2 m2 l2 r2 =>
               orb (m1 GHC.Base./= m2) (orb (p1 GHC.Base./= p2) (orb (nequal l1 l2) (nequal r1
                                                                      r2)))
           | Tip kx x, Tip ky y => orb (kx GHC.Base./= ky) (x GHC.Base./= y)
           | Nil, Nil => false
           | _, _ => true
           end.

Definition member {a} : Data.IntSet.Internal.Key -> IntMap a -> bool :=
  fun k =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r =>
                     if nomatch k p m : bool then false else
                     if Data.IntSet.Internal.zero k m : bool then go l else
                     go r
                 | Tip kx _ => k GHC.Base.== kx
                 | Nil => false
                 end in
    go.

Definition notMember {a} : Data.IntSet.Internal.Key -> IntMap a -> bool :=
  fun k m => negb (member k m).

Definition match_ : Data.IntSet.Internal.Key -> Prefix -> Mask -> bool :=
  fun i p m => (Data.IntSet.Internal.mask i m) GHC.Base.== p.

Definition maskW : Nat -> Nat -> Prefix :=
  fun i m =>
    i Data.Bits..&.(**)
    (Data.Bits.xor (Coq.NArith.BinNat.N.lxor (m GHC.Num.- #1)
                                             (Coq.NArith.BinNat.N.ones (64 % N))) m).

Definition mapWithKey {a} {b}
   : (Data.IntSet.Internal.Key -> a -> b) -> IntMap a -> IntMap b :=
  fix mapWithKey f t
        := match t with
           | Bin p m l r => Bin p m (mapWithKey f l) (mapWithKey f r)
           | Tip k x => Tip k (f k x)
           | Nil => Nil
           end.

Definition map {a} {b} : (a -> b) -> IntMap a -> IntMap b :=
  fun f =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r => Bin p m (go l) (go r)
                 | Tip k x => Tip k (f x)
                 | Nil => Nil
                 end in
    go.

Local Definition Functor__IntMap_fmap
   : forall {a} {b}, (a -> b) -> IntMap a -> IntMap b :=
  fun {a} {b} => map.

Definition Functor__IntMap_op_zlzd__ {a} {b} :=
  (@IntMap_op_zlzd__ a b).

Program Instance Functor__IntMap : GHC.Base.Functor IntMap :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__IntMap_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__IntMap_op_zlzd__ |}.

Definition mapWhenMissing {f} {a} {b} {x} `{GHC.Base.Applicative f}
  `{GHC.Base.Monad f}
   : (a -> b) -> WhenMissing f x a -> WhenMissing f x b :=
  fun f t =>
    Mk_WhenMissing (fun m =>
                      missingSubtree t m GHC.Base.>>= (fun m' => GHC.Base.pure (GHC.Base.fmap f m')))
                   (fun k x =>
                      missingKey t k x GHC.Base.>>= (fun q => (GHC.Base.pure (GHC.Base.fmap f q)))).

Definition mapWhenMatched {f} {a} {b} {x} {y} `{GHC.Base.Functor f}
   : (a -> b) -> WhenMatched f x y a -> WhenMatched f x y b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_WhenMatched g =>
        Mk_WhenMatched (fun k x y => GHC.Base.fmap (GHC.Base.fmap f) (g k x y))
    end.

Definition mapMissing {f} {x} {y} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> x -> y) -> WhenMissing f x y :=
  fun f =>
    Mk_WhenMissing (fun m => GHC.Base.pure (mapWithKey f m)) (fun k x =>
                      GHC.Base.pure (Some (f k x))).

Definition mapLT {a}
   : (IntMap a -> IntMap a) -> SplitLookup a -> SplitLookup a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_SplitLookup lt fnd gt => Mk_SplitLookup (f lt) fnd gt
    end.

Definition mapGentlyWhenMissing {f} {a} {b} {x} `{GHC.Base.Functor f}
   : (a -> b) -> WhenMissing f x a -> WhenMissing f x b :=
  fun f t =>
    Mk_WhenMissing (fun m => GHC.Base.fmap f Data.Functor.<$> missingSubtree t m)
                   (fun k x => GHC.Base.fmap f Data.Functor.<$> missingKey t k x).

Definition mapGentlyWhenMatched {f} {a} {b} {x} {y} `{GHC.Base.Functor f}
   : (a -> b) -> WhenMatched f x y a -> WhenMatched f x y b :=
  fun f t =>
    zipWithMaybeAMatched (fun k x y =>
                            GHC.Base.fmap f Data.Functor.<$> runWhenMatched t k x y).

Definition mapGT {a}
   : (IntMap a -> IntMap a) -> SplitLookup a -> SplitLookup a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_SplitLookup lt fnd gt => Mk_SplitLookup lt fnd (f gt)
    end.

Definition mapAccumRWithKey {a} {b} {c}
   : (a -> Data.IntSet.Internal.Key -> b -> (a * c)%type) ->
     a -> IntMap b -> (a * IntMap c)%type :=
  fix mapAccumRWithKey f a t
        := match t with
           | Bin p m l r =>
               let 'pair a1 r' := mapAccumRWithKey f a r in
               let 'pair a2 l' := mapAccumRWithKey f a1 l in
               pair a2 (Bin p m l' r')
           | Tip k x => let 'pair a' x' := f a k x in pair a' (Tip k x')
           | Nil => pair a Nil
           end.

Definition mapAccumL {a} {b} {c}
   : (a -> Data.IntSet.Internal.Key -> b -> (a * c)%type) ->
     a -> IntMap b -> (a * IntMap c)%type :=
  fix mapAccumL f a t
        := match t with
           | Bin p m l r =>
               let 'pair a1 l' := mapAccumL f a l in
               let 'pair a2 r' := mapAccumL f a1 r in
               pair a2 (Bin p m l' r')
           | Tip k x => let 'pair a' x' := f a k x in pair a' (Tip k x')
           | Nil => pair a Nil
           end.

Definition mapAccumWithKey {a} {b} {c}
   : (a -> Data.IntSet.Internal.Key -> b -> (a * c)%type) ->
     a -> IntMap b -> (a * IntMap c)%type :=
  fun f a t => mapAccumL f a t.

Definition mapAccum {a} {b} {c}
   : (a -> b -> (a * c)%type) -> a -> IntMap b -> (a * IntMap c)%type :=
  fun f =>
    mapAccumWithKey (fun arg_0__ arg_1__ arg_2__ =>
                       match arg_0__, arg_1__, arg_2__ with
                       | a', _, x => f a' x
                       end).

Definition lookupPrefix {a} : IntSetPrefix -> IntMap a -> IntMap a :=
  fix lookupPrefix arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | kp, (Bin p m l r as t) =>
               if (m Data.Bits..&.(**) Data.IntSet.Internal.suffixBitMask) GHC.Base./=
                  #0 : bool
               then if Coq.NArith.BinNat.N.ldiff p Data.IntSet.Internal.suffixBitMask
                       GHC.Base.==
                       kp : bool
                    then t
                    else Nil else
               if nomatch kp p m : bool then Nil else
               if Data.IntSet.Internal.zero kp m : bool then lookupPrefix kp l else
               lookupPrefix kp r
           | kp, (Tip kx _ as t) =>
               if (Coq.NArith.BinNat.N.ldiff kx Data.IntSet.Internal.suffixBitMask) GHC.Base.==
                  kp : bool
               then t else
               Nil
           | _, Nil => Nil
           end.

Definition lookupMin {a}
   : IntMap a -> option (Data.IntSet.Internal.Key * a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Nil => None
    | Tip k v => Some (pair k v)
    | Bin _ m l r =>
        let fix go arg_2__
                  := match arg_2__ with
                     | Tip k v => Some (pair k v)
                     | Bin _ _ l' _ => go l'
                     | Nil => None
                     end in
        if m GHC.Base.< #0 : bool then go r else
        go l
    end.

Definition lookupMax {a}
   : IntMap a -> option (Data.IntSet.Internal.Key * a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Nil => None
    | Tip k v => Some (pair k v)
    | Bin _ m l r =>
        let fix go arg_2__
                  := match arg_2__ with
                     | Tip k v => Some (pair k v)
                     | Bin _ _ _ r' => go r'
                     | Nil => None
                     end in
        if m GHC.Base.< #0 : bool then go l else
        go r
    end.

Definition lookupLT {a}
   : Data.IntSet.Internal.Key ->
     IntMap a -> option (Data.IntSet.Internal.Key * a)%type :=
  fun k t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | def, Bin p m l r =>
                     if nomatch k p m : bool
                     then if k GHC.Base.< p : bool
                          then unsafeFindMax def
                          else unsafeFindMax r else
                     if Data.IntSet.Internal.zero k m : bool then go def l else
                     go l r
                 | def, Tip ky y =>
                     if k GHC.Base.<= ky : bool then unsafeFindMax def else
                     Some (pair ky y)
                 | def, Nil => unsafeFindMax def
                 end in
    let j_10__ := go Nil t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if k GHC.Base.>= #0 : bool
             then go r l
             else go Nil r else
        j_10__
    | _ => j_10__
    end.

Definition lookupLE {a}
   : Data.IntSet.Internal.Key ->
     IntMap a -> option (Data.IntSet.Internal.Key * a)%type :=
  fun k t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | def, Bin p m l r =>
                     if nomatch k p m : bool
                     then if k GHC.Base.< p : bool
                          then unsafeFindMax def
                          else unsafeFindMax r else
                     if Data.IntSet.Internal.zero k m : bool then go def l else
                     go l r
                 | def, Tip ky y =>
                     if k GHC.Base.< ky : bool then unsafeFindMax def else
                     Some (pair ky y)
                 | def, Nil => unsafeFindMax def
                 end in
    let j_10__ := go Nil t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if k GHC.Base.>= #0 : bool
             then go r l
             else go Nil r else
        j_10__
    | _ => j_10__
    end.

Definition lookupGT {a}
   : Data.IntSet.Internal.Key ->
     IntMap a -> option (Data.IntSet.Internal.Key * a)%type :=
  fun k t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | def, Bin p m l r =>
                     if nomatch k p m : bool
                     then if k GHC.Base.< p : bool
                          then unsafeFindMin l
                          else unsafeFindMin def else
                     if Data.IntSet.Internal.zero k m : bool then go r l else
                     go def r
                 | def, Tip ky y =>
                     if k GHC.Base.>= ky : bool then unsafeFindMin def else
                     Some (pair ky y)
                 | def, Nil => unsafeFindMin def
                 end in
    let j_10__ := go Nil t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if k GHC.Base.>= #0 : bool
             then go Nil l
             else go l r else
        j_10__
    | _ => j_10__
    end.

Definition lookupGE {a}
   : Data.IntSet.Internal.Key ->
     IntMap a -> option (Data.IntSet.Internal.Key * a)%type :=
  fun k t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | def, Bin p m l r =>
                     if nomatch k p m : bool
                     then if k GHC.Base.< p : bool
                          then unsafeFindMin l
                          else unsafeFindMin def else
                     if Data.IntSet.Internal.zero k m : bool then go r l else
                     go def r
                 | def, Tip ky y =>
                     if k GHC.Base.> ky : bool then unsafeFindMin def else
                     Some (pair ky y)
                 | def, Nil => unsafeFindMin def
                 end in
    let j_10__ := go Nil t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if k GHC.Base.>= #0 : bool
             then go Nil l
             else go l r else
        j_10__
    | _ => j_10__
    end.

Definition lookup {a} : Data.IntSet.Internal.Key -> IntMap a -> option a :=
  fun k =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r =>
                     if nomatch k p m : bool then None else
                     if Data.IntSet.Internal.zero k m : bool then go l else
                     go r
                 | Tip kx x => if k GHC.Base.== kx : bool then Some x else None
                 | Nil => None
                 end in
    go.

Definition op_znz3fU__ {a} : IntMap a -> Data.IntSet.Internal.Key -> option a :=
  fun m k => lookup k m.

Notation "'_!?_'" := (op_znz3fU__).

Infix "!?" := (_!?_) (at level 99).

Definition submapCmp {a} {b}
   : (a -> b -> bool) -> IntMap a -> IntMap b -> comparison :=
  fix submapCmp arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | predicate, (Bin p1 m1 l1 r1 as t1), Bin p2 m2 l2 r2 =>
               let submapCmpEq :=
                 match pair (submapCmp predicate l1 l2) (submapCmp predicate r1 r2) with
                 | pair Gt _ => Gt
                 | pair _ Gt => Gt
                 | pair Eq Eq => Eq
                 | _ => Lt
                 end in
               let submapCmpLt :=
                 if nomatch p1 p2 m2 : bool then Gt else
                 if Data.IntSet.Internal.zero p1 m2 : bool then submapCmp predicate t1 l2 else
                 submapCmp predicate t1 r2 in
               if shorter m1 m2 : bool then Gt else
               if shorter m2 m1 : bool then submapCmpLt else
               if p1 GHC.Base.== p2 : bool then submapCmpEq else
               Gt
           | _, _, _ =>
               match arg_0__, arg_1__, arg_2__ with
               | _, Bin _ _ _ _, _ => Gt
               | predicate, Tip kx x, Tip ky y =>
                   if andb (kx GHC.Base.== ky) (predicate x y) : bool then Eq else
                   Gt
               | _, _, _ =>
                   match arg_0__, arg_1__, arg_2__ with
                   | predicate, Tip k x, t =>
                       match lookup k t with
                       | Some y => if predicate x y : bool then Lt else Gt
                       | _ => Gt
                       end
                   | _, Nil, Nil => Eq
                   | _, Nil, _ => Lt
                   | _, _, _ => GHC.Err.patternFailure
                   end
               end
           end.

Definition lmapWhenMissing {b} {a} {f} {x}
   : (b -> a) -> WhenMissing f a x -> WhenMissing f b x :=
  fun f t =>
    Mk_WhenMissing (fun m => missingSubtree t (GHC.Base.fmap f m)) (fun k x =>
                      missingKey t k (f x)).

Definition keysSet {a} : IntMap a -> Data.IntSet.Internal.IntSet :=
  fix keysSet arg_0__
        := match arg_0__ with
           | Nil => Data.IntSet.Internal.Nil
           | Tip kx _ => Data.IntSet.Internal.singleton kx
           | Bin p m l r =>
               let fix computeBm arg_2__ arg_3__
                         := match arg_2__, arg_3__ with
                            | acc, Bin _ _ l' r' => computeBm (computeBm acc l') r'
                            | acc, Tip kx _ => acc Data.Bits..|.(**) Data.IntSet.Internal.bitmapOf kx
                            | _, Nil => GHC.Err.error (GHC.Base.hs_string__ "Data.IntSet.keysSet: Nil")
                            end in
               if (m Data.Bits..&.(**) Data.IntSet.Internal.suffixBitMask) GHC.Base.==
                  #0 : bool
               then Data.IntSet.Internal.Bin p m (keysSet l) (keysSet r) else
               Data.IntSet.Internal.Tip (Coq.NArith.BinNat.N.ldiff p
                                                                   Data.IntSet.Internal.suffixBitMask) (computeBm
                                                                                                        (computeBm #0 l)
                                                                                                        r)
           end.

Definition isSubmapOfBy {a} {b}
   : (a -> b -> bool) -> IntMap a -> IntMap b -> bool :=
  fix isSubmapOfBy arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | predicate, (Bin p1 m1 l1 r1 as t1), Bin p2 m2 l2 r2 =>
               if shorter m1 m2 : bool then false else
               if shorter m2 m1 : bool
               then andb (match_ p1 p2 m2) (if Data.IntSet.Internal.zero p1 m2 : bool
                          then isSubmapOfBy predicate t1 l2
                          else isSubmapOfBy predicate t1 r2) else
               andb (p1 GHC.Base.== p2) (andb (isSubmapOfBy predicate l1 l2) (isSubmapOfBy
                                               predicate r1 r2))
           | _, _, _ =>
               match arg_0__, arg_1__, arg_2__ with
               | _, Bin _ _ _ _, _ => false
               | predicate, Tip k x, t =>
                   match lookup k t with
                   | Some y => predicate x y
                   | None => false
                   end
               | _, Nil, _ => true
               end
           end.

Definition isSubmapOf {a} `{GHC.Base.Eq_ a} : IntMap a -> IntMap a -> bool :=
  fun m1 m2 => isSubmapOfBy _GHC.Base.==_ m1 m2.

Definition isProperSubmapOfBy {a} {b}
   : (a -> b -> bool) -> IntMap a -> IntMap b -> bool :=
  fun predicate t1 t2 =>
    match submapCmp predicate t1 t2 with
    | Lt => true
    | _ => false
    end.

Definition isProperSubmapOf {a} `{GHC.Base.Eq_ a}
   : IntMap a -> IntMap a -> bool :=
  fun m1 m2 => isProperSubmapOfBy _GHC.Base.==_ m1 m2.

Definition fromSet {a}
   : (Data.IntSet.Internal.Key -> a) -> Data.IntSet.Internal.IntSet -> IntMap a :=
  fix fromSet arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Data.IntSet.Internal.Nil => Nil
           | f, Data.IntSet.Internal.Bin p m l r => Bin p m (fromSet f l) (fromSet f r)
           | f, Data.IntSet.Internal.Tip kx bm =>
               let buildTree :=
                 GHC.DeferredFix.deferredFix4 (fun buildTree g prefix bmask bits =>
                                                 let 'num_3__ := bits in
                                                 if num_3__ GHC.Base.== #0 : bool then Tip prefix (g prefix) else
                                                 let 'bits2 := Utils.Containers.Internal.BitUtil.shiftRL (bits) #1 in
                                                 if (bmask Data.Bits..&.(**)
                                                     ((Utils.Containers.Internal.BitUtil.shiftLL #1 bits2) GHC.Num.-
                                                      #1)) GHC.Base.==
                                                    #0 : bool
                                                 then buildTree g (prefix GHC.Num.+ bits2)
                                                      (Utils.Containers.Internal.BitUtil.shiftRL bmask bits2) bits2 else
                                                 if ((Utils.Containers.Internal.BitUtil.shiftRL bmask bits2)
                                                     Data.Bits..&.(**)
                                                     ((Utils.Containers.Internal.BitUtil.shiftLL #1 bits2) GHC.Num.-
                                                      #1)) GHC.Base.==
                                                    #0 : bool
                                                 then buildTree g prefix bmask bits2 else
                                                 Bin prefix bits2 (buildTree g prefix bmask bits2) (buildTree g (prefix
                                                                                                                 GHC.Num.+
                                                                                                                 bits2)
                                                                                                    (Utils.Containers.Internal.BitUtil.shiftRL
                                                                                                     bmask bits2)
                                                                                                    bits2)) in
               buildTree f kx bm (Data.IntSet.Internal.suffixBitMask GHC.Num.+ #1)
           end.

Definition foldrWithKey' {a} {b}
   : (Data.IntSet.Internal.Key -> a -> b -> b) -> b -> IntMap a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip kx x => f kx x z'
                 | z', Bin _ _ l r => go (go z' r) l
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z l) r else go (go z r) l
      | _ => go z t
      end.

Definition foldrWithKey {a} {b}
   : (Data.IntSet.Internal.Key -> a -> b -> b) -> b -> IntMap a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip kx x => f kx x z'
                 | z', Bin _ _ l r => go (go z' r) l
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z l) r else go (go z r) l
      | _ => go z t
      end.

Definition keys {a} : IntMap a -> list Data.IntSet.Internal.Key :=
  foldrWithKey (fun arg_0__ arg_1__ arg_2__ =>
                  match arg_0__, arg_1__, arg_2__ with
                  | k, _, ks => cons k ks
                  end) nil.

Definition toAscList {a}
   : IntMap a -> list (Data.IntSet.Internal.Key * a)%type :=
  foldrWithKey (fun k x xs => cons (pair k x) xs) nil.

Definition toList {a} : IntMap a -> list (Data.IntSet.Internal.Key * a)%type :=
  toAscList.

Definition foldrFB {a} {b}
   : (Data.IntSet.Internal.Key -> a -> b -> b) -> b -> IntMap a -> b :=
  foldrWithKey.

Definition foldr' {a} {b} : (a -> b -> b) -> b -> IntMap a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip _ x => f x z'
                 | z', Bin _ _ l r => go (go z' r) l
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z l) r else go (go z r) l
      | _ => go z t
      end.

Definition foldr {a} {b} : (a -> b -> b) -> b -> IntMap a -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip _ x => f x z'
                 | z', Bin _ _ l r => go (go z' r) l
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z l) r else go (go z r) l
      | _ => go z t
      end.

Definition foldlWithKey' {a} {b}
   : (a -> Data.IntSet.Internal.Key -> b -> a) -> a -> IntMap b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip kx x => f z' kx x
                 | z', Bin _ _ l r => go (go z' l) r
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z r) l else go (go z l) r
      | _ => go z t
      end.

Definition foldlWithKey {a} {b}
   : (a -> Data.IntSet.Internal.Key -> b -> a) -> a -> IntMap b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip kx x => f z' kx x
                 | z', Bin _ _ l r => go (go z' l) r
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z r) l else go (go z l) r
      | _ => go z t
      end.

Definition toDescList {a}
   : IntMap a -> list (Data.IntSet.Internal.Key * a)%type :=
  foldlWithKey (fun xs k x => cons (pair k x) xs) nil.

Definition foldlFB {a} {b}
   : (a -> Data.IntSet.Internal.Key -> b -> a) -> a -> IntMap b -> a :=
  foldlWithKey.

Definition foldl' {a} {b} : (a -> b -> a) -> a -> IntMap b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip _ x => f z' x
                 | z', Bin _ _ l r => go (go z' l) r
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z r) l else go (go z l) r
      | _ => go z t
      end.

Definition foldl {a} {b} : (a -> b -> a) -> a -> IntMap b -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip _ x => f z' x
                 | z', Bin _ _ l r => go (go z' l) r
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z r) l else go (go z l) r
      | _ => go z t
      end.

Definition foldMapWithKey {m} {a} `{GHC.Base.Monoid m}
   : (Data.IntSet.Internal.Key -> a -> m) -> IntMap a -> m :=
  fun f =>
    let fix go arg_0__
              := match arg_0__ with
                 | Nil => GHC.Base.mempty
                 | Tip kx x => f kx x
                 | Bin _ _ l r => GHC.Base.mappend (go l) (go r)
                 end in
    go.

Definition findWithDefault {a}
   : a -> Data.IntSet.Internal.Key -> IntMap a -> a :=
  fun def k =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r =>
                     if nomatch k p m : bool then def else
                     if Data.IntSet.Internal.zero k m : bool then go l else
                     go r
                 | Tip kx x => if k GHC.Base.== kx : bool then x else def
                 | Nil => def
                 end in
    go.

Definition equal {a} `{GHC.Base.Eq_ a} : IntMap a -> IntMap a -> bool :=
  fix equal arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | Bin p1 m1 l1 r1, Bin p2 m2 l2 r2 =>
               andb (m1 GHC.Base.== m2) (andb (p1 GHC.Base.== p2) (andb (equal l1 l2) (equal r1
                                                                         r2)))
           | Tip kx x, Tip ky y => andb (kx GHC.Base.== ky) (x GHC.Base.== y)
           | Nil, Nil => true
           | _, _ => false
           end.

Definition empty {a} : IntMap a :=
  Nil.

Definition elems {a} : IntMap a -> list a :=
  foldr cons nil.

Definition dropMissing {f} {x} {y} `{GHC.Base.Applicative f}
   : WhenMissing f x y :=
  Mk_WhenMissing (GHC.Base.const (GHC.Base.pure Nil)) (fun arg_0__ arg_1__ =>
                    GHC.Base.pure None).

Definition contramapSecondWhenMatched {b} {a} {f} {x} {z}
   : (b -> a) -> WhenMatched f x a z -> WhenMatched f x b z :=
  fun f t => Mk_WhenMatched (fun k x y => runWhenMatched t k x (f y)).

Definition contramapFirstWhenMatched {b} {a} {f} {y} {z}
   : (b -> a) -> WhenMatched f a y z -> WhenMatched f b y z :=
  fun f t => Mk_WhenMatched (fun k x y => runWhenMatched t k (f x) y).

Definition branchMask : Prefix -> Prefix -> Mask :=
  fun p1 p2 =>
    Utils.Containers.Internal.BitUtil.highestBitMask (Data.Bits.xor p1 p2).

Definition link {a} : Prefix -> IntMap a -> Prefix -> IntMap a -> IntMap a :=
  fun p1 t1 p2 t2 =>
    let m := branchMask p1 p2 in
    let p := Data.IntSet.Internal.mask p1 m in
    if Data.IntSet.Internal.zero p1 m : bool then Bin p m t1 t2 else
    Bin p m t2 t1.

Definition insert {a} : Data.IntSet.Internal.Key -> a -> IntMap a -> IntMap a :=
  fix insert arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | k, x, (Bin p m l r as t) =>
               if nomatch k p m : bool then link k (Tip k x) p t else
               if Data.IntSet.Internal.zero k m : bool then Bin p m (insert k x l) r else
               Bin p m l (insert k x r)
           | k, x, (Tip ky _ as t) =>
               if k GHC.Base.== ky : bool then Tip k x else
               link k (Tip k x) ky t
           | k, x, Nil => Tip k x
           end.

Definition fromList {a}
   : list (Data.IntSet.Internal.Key * a)%type -> IntMap a :=
  fun xs =>
    let ins :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | t, pair k x => insert k x t
        end in
    Data.Foldable.foldl' ins empty xs.

Definition mapKeys {a}
   : (Data.IntSet.Internal.Key -> Data.IntSet.Internal.Key) ->
     IntMap a -> IntMap a :=
  fun f =>
    fromList GHC.Base.∘ foldrWithKey (fun k x xs => cons (pair (f k) x) xs) nil.

Definition insertLookupWithKey {a}
   : (Data.IntSet.Internal.Key -> a -> a -> a) ->
     Data.IntSet.Internal.Key -> a -> IntMap a -> (option a * IntMap a)%type :=
  fix insertLookupWithKey arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | f, k, x, (Bin p m l r as t) =>
               if nomatch k p m : bool then pair None (link k (Tip k x) p t) else
               if Data.IntSet.Internal.zero k m : bool
               then let 'pair found l' := insertLookupWithKey f k x l in
                    pair found (Bin p m l' r) else
               let 'pair found r' := insertLookupWithKey f k x r in
               pair found (Bin p m l r')
           | f, k, x, (Tip ky y as t) =>
               if k GHC.Base.== ky : bool then pair (Some y) (Tip k (f k x y)) else
               pair None (link k (Tip k x) ky t)
           | _, k, x, Nil => pair None (Tip k x)
           end.

Definition insertWithKey {a}
   : (Data.IntSet.Internal.Key -> a -> a -> a) ->
     Data.IntSet.Internal.Key -> a -> IntMap a -> IntMap a :=
  fix insertWithKey arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | f, k, x, (Bin p m l r as t) =>
               if nomatch k p m : bool then link k (Tip k x) p t else
               if Data.IntSet.Internal.zero k m : bool
               then Bin p m (insertWithKey f k x l) r else
               Bin p m l (insertWithKey f k x r)
           | f, k, x, (Tip ky y as t) =>
               if k GHC.Base.== ky : bool then Tip k (f k x y) else
               link k (Tip k x) ky t
           | _, k, x, Nil => Tip k x
           end.

Definition fromListWithKey {a}
   : (Data.IntSet.Internal.Key -> a -> a -> a) ->
     list (Data.IntSet.Internal.Key * a)%type -> IntMap a :=
  fun f xs =>
    let ins :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | t, pair k x => insertWithKey f k x t
        end in
    Data.Foldable.foldl' ins empty xs.

Definition fromListWith {a}
   : (a -> a -> a) -> list (Data.IntSet.Internal.Key * a)%type -> IntMap a :=
  fun f xs =>
    fromListWithKey (fun arg_0__ arg_1__ arg_2__ =>
                       match arg_0__, arg_1__, arg_2__ with
                       | _, x, y => f x y
                       end) xs.

Definition mapKeysWith {a}
   : (a -> a -> a) ->
     (Data.IntSet.Internal.Key -> Data.IntSet.Internal.Key) ->
     IntMap a -> IntMap a :=
  fun c f =>
    fromListWith c GHC.Base.∘
    foldrWithKey (fun k x xs => cons (pair (f k) x) xs) nil.

Definition insertWith {a}
   : (a -> a -> a) -> Data.IntSet.Internal.Key -> a -> IntMap a -> IntMap a :=
  fun f k x t =>
    insertWithKey (fun arg_0__ arg_1__ arg_2__ =>
                     match arg_0__, arg_1__, arg_2__ with
                     | _, x', y' => f x' y'
                     end) k x t.

Definition mergeWithKey' {c} {a} {b}
   : (Prefix -> Mask -> IntMap c -> IntMap c -> IntMap c) ->
     (IntMap a -> IntMap b -> IntMap c) ->
     (IntMap a -> IntMap c) ->
     (IntMap b -> IntMap c) -> IntMap a -> IntMap b -> IntMap c :=
  fun bin' f g1 g2 =>
    let maybe_link :=
      fun arg_0__ arg_1__ arg_2__ arg_3__ =>
        match arg_0__, arg_1__, arg_2__, arg_3__ with
        | _, Nil, _, t2 => t2
        | _, t1, _, Nil => t1
        | p1, t1, p2, t2 => link p1 t1 p2 t2
        end in
    let go :=
      GHC.DeferredFix.deferredFix2 (fun go arg_6__ arg_7__ =>
                                      match arg_6__, arg_7__ with
                                      | (Bin p1 m1 l1 r1 as t1), (Bin p2 m2 l2 r2 as t2) =>
                                          let merge2 :=
                                            if nomatch p1 p2 m2 : bool then maybe_link p1 (g1 t1) p2 (g2 t2) else
                                            if Data.IntSet.Internal.zero p1 m2 : bool
                                            then bin' p2 m2 (go t1 l2) (g2 r2) else
                                            bin' p2 m2 (g2 l2) (go t1 r2) in
                                          let merge1 :=
                                            if nomatch p2 p1 m1 : bool then maybe_link p1 (g1 t1) p2 (g2 t2) else
                                            if Data.IntSet.Internal.zero p2 m1 : bool
                                            then bin' p1 m1 (go l1 t2) (g1 r1) else
                                            bin' p1 m1 (g1 l1) (go r1 t2) in
                                          if shorter m1 m2 : bool then merge1 else
                                          if shorter m2 m1 : bool then merge2 else
                                          if p1 GHC.Base.== p2 : bool then bin' p1 m1 (go l1 l2) (go r1 r2) else
                                          maybe_link p1 (g1 t1) p2 (g2 t2)
                                      | (Bin _ _ _ _ as t1'), (Tip k2' _ as t2') =>
                                          let fix merge0 arg_18__ arg_19__ arg_20__
                                                    := match arg_18__, arg_19__, arg_20__ with
                                                       | t2, k2, (Bin p1 m1 l1 r1 as t1) =>
                                                           if nomatch k2 p1 m1 : bool
                                                           then maybe_link p1 (g1 t1) k2 (g2 t2) else
                                                           if Data.IntSet.Internal.zero k2 m1 : bool
                                                           then bin' p1 m1 (merge0 t2 k2 l1) (g1 r1) else
                                                           bin' p1 m1 (g1 l1) (merge0 t2 k2 r1)
                                                       | t2, k2, (Tip k1 _ as t1) =>
                                                           if k1 GHC.Base.== k2 : bool then f t1 t2 else
                                                           maybe_link k1 (g1 t1) k2 (g2 t2)
                                                       | t2, _, Nil => g2 t2
                                                       end in
                                          merge0 t2' k2' t1'
                                      | (Bin _ _ _ _ as t1), Nil => g1 t1
                                      | (Tip k1' _ as t1'), t2' =>
                                          let fix merge0 arg_30__ arg_31__ arg_32__
                                                    := match arg_30__, arg_31__, arg_32__ with
                                                       | t1, k1, (Bin p2 m2 l2 r2 as t2) =>
                                                           if nomatch k1 p2 m2 : bool
                                                           then maybe_link k1 (g1 t1) p2 (g2 t2) else
                                                           if Data.IntSet.Internal.zero k1 m2 : bool
                                                           then bin' p2 m2 (merge0 t1 k1 l2) (g2 r2) else
                                                           bin' p2 m2 (g2 l2) (merge0 t1 k1 r2)
                                                       | t1, k1, (Tip k2 _ as t2) =>
                                                           if k1 GHC.Base.== k2 : bool then f t1 t2 else
                                                           maybe_link k1 (g1 t1) k2 (g2 t2)
                                                       | t1, _, Nil => g1 t1
                                                       end in
                                          merge0 t1' k1' t2'
                                      | Nil, t2 => g2 t2
                                      end) in
    go.

Definition union {a} : IntMap a -> IntMap a -> IntMap a :=
  fun m1 m2 => mergeWithKey' Bin GHC.Base.const GHC.Base.id GHC.Base.id m1 m2.

Definition split {a}
   : Data.IntSet.Internal.Key -> IntMap a -> (IntMap a * IntMap a)%type :=
  fun k t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | k', (Bin p m l r as t') =>
                     if nomatch k' p m : bool
                     then if k' GHC.Base.> p : bool
                          then pair t' Nil
                          else pair Nil t' else
                     if Data.IntSet.Internal.zero k' m : bool
                     then let 'pair lt gt := go k' l in
                          pair lt (union gt r) else
                     let 'pair lt gt := go k' r in
                     pair (union l lt) gt
                 | k', (Tip ky _ as t') =>
                     if k' GHC.Base.> ky : bool then (pair t' Nil) else
                     if k' GHC.Base.< ky : bool then (pair Nil t') else
                     (pair Nil Nil)
                 | _, Nil => (pair Nil Nil)
                 end in
    let j_20__ := let 'pair lt gt := go k t in pair lt gt in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if k GHC.Base.>= #0 : bool
             then let 'pair lt gt := go k l in
                  let lt' := union r lt in pair lt' gt
             else let 'pair lt gt := go k r in
                  let gt' := union gt l in pair lt gt' else
        j_20__
    | _ => j_20__
    end.

Definition splitLookup {a}
   : Data.IntSet.Internal.Key ->
     IntMap a -> (IntMap a * option a * IntMap a)%type :=
  fun k t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | k', (Bin p m l r as t') =>
                     if nomatch k' p m : bool
                     then if k' GHC.Base.> p : bool
                          then Mk_SplitLookup t' None Nil
                          else Mk_SplitLookup Nil None t' else
                     if Data.IntSet.Internal.zero k' m : bool
                     then mapGT (fun arg_3__ => union arg_3__ r) (go k' l) else
                     mapLT (union l) (go k' r)
                 | k', (Tip ky y as t') =>
                     if k' GHC.Base.> ky : bool then Mk_SplitLookup t' None Nil else
                     if k' GHC.Base.< ky : bool then Mk_SplitLookup Nil None t' else
                     Mk_SplitLookup Nil (Some y) Nil
                 | _, Nil => Mk_SplitLookup Nil None Nil
                 end in
    let 'Mk_SplitLookup lt fnd gt := (let j_12__ := go k t in
                                        match t with
                                        | Bin _ m l r =>
                                            if m GHC.Base.< #0 : bool
                                            then if k GHC.Base.>= #0 : bool
                                                 then mapLT (union r) (go k l)
                                                 else mapGT (fun arg_13__ => union arg_13__ l) (go k r) else
                                            j_12__
                                        | _ => j_12__
                                        end) in
    pair (pair lt fnd) gt.

Definition unions {f} {a} `{Data.Foldable.Foldable f}
   : f (IntMap a) -> IntMap a :=
  fun xs => Data.Foldable.foldl' union empty xs.

Definition unionWithKey {a}
   : (Data.IntSet.Internal.Key -> a -> a -> a) ->
     IntMap a -> IntMap a -> IntMap a :=
  fun f m1 m2 =>
    mergeWithKey' Bin (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | Tip k1 x1, Tip _k2 x2 => Tip k1 (f k1 x1 x2)
                         | _, _ => GHC.Err.patternFailure
                         end) GHC.Base.id GHC.Base.id m1 m2.

Definition unionWith {a} : (a -> a -> a) -> IntMap a -> IntMap a -> IntMap a :=
  fun f m1 m2 =>
    unionWithKey (fun arg_0__ arg_1__ arg_2__ =>
                    match arg_0__, arg_1__, arg_2__ with
                    | _, x, y => f x y
                    end) m1 m2.

Definition unionsWith {f} {a} `{Data.Foldable.Foldable f}
   : (a -> a -> a) -> f (IntMap a) -> IntMap a :=
  fun f ts => Data.Foldable.foldl' (unionWith f) empty ts.

Definition boolITE {a} : a -> a -> bool -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, _, false => f
    | _, t, true => t
    end.

Definition bitmapOf : Coq.Numbers.BinNums.N -> IntSetBitMap :=
  fun x =>
    Utils.Containers.Internal.BitUtil.shiftLL #1 (x Data.Bits..&.(**)
                                                  Data.IntSet.Internal.suffixBitMask).

Definition binCheckRight {a}
   : Prefix -> Mask -> IntMap a -> IntMap a -> IntMap a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _, _, l, Nil => l
    | p, m, l, r => Bin p m l r
    end.

Definition binCheckLeft {a}
   : Prefix -> Mask -> IntMap a -> IntMap a -> IntMap a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _, _, Nil, r => r
    | p, m, l, r => Bin p m l r
    end.

Definition delete {a} : Data.IntSet.Internal.Key -> IntMap a -> IntMap a :=
  fix delete arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | k, (Bin p m l r as t) =>
               if nomatch k p m : bool then t else
               if Data.IntSet.Internal.zero k m : bool
               then binCheckLeft p m (delete k l) r else
               binCheckRight p m l (delete k r)
           | k, (Tip ky _ as t) => if k GHC.Base.== ky : bool then Nil else t
           | _k, Nil => Nil
           end.

Definition updateLookupWithKey {a}
   : (Data.IntSet.Internal.Key -> a -> option a) ->
     Data.IntSet.Internal.Key -> IntMap a -> (option a * IntMap a)%type :=
  fix updateLookupWithKey arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | f, k, (Bin p m l r as t) =>
               if nomatch k p m : bool then pair None t else
               if Data.IntSet.Internal.zero k m : bool
               then let 'pair found l' := updateLookupWithKey f k l in
                    pair found (binCheckLeft p m l' r) else
               let 'pair found r' := updateLookupWithKey f k r in
               pair found (binCheckRight p m l r')
           | f, k, (Tip ky y as t) =>
               if k GHC.Base.== ky : bool
               then match (f k y) with
                    | Some y' => pair (Some y) (Tip ky y')
                    | None => pair (Some y) Nil
                    end else
               pair None t
           | _, _, Nil => pair None Nil
           end.

Definition updatePrefix {a}
   : IntSetPrefix -> IntMap a -> (IntMap a -> IntMap a) -> IntMap a :=
  fix updatePrefix arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | kp, (Bin p m l r as t), f =>
               if (m Data.Bits..&.(**) Data.IntSet.Internal.suffixBitMask) GHC.Base./=
                  #0 : bool
               then if Coq.NArith.BinNat.N.ldiff p Data.IntSet.Internal.suffixBitMask
                       GHC.Base.==
                       kp : bool
                    then f t
                    else t else
               if nomatch kp p m : bool then t else
               if Data.IntSet.Internal.zero kp m : bool
               then binCheckLeft p m (updatePrefix kp l f) r else
               binCheckRight p m l (updatePrefix kp r f)
           | kp, (Tip kx _ as t), f =>
               if Coq.NArith.BinNat.N.ldiff kx Data.IntSet.Internal.suffixBitMask GHC.Base.==
                  kp : bool
               then f t else
               t
           | _, Nil, _ => Nil
           end.

Definition updateWithKey {a}
   : (Data.IntSet.Internal.Key -> a -> option a) ->
     Data.IntSet.Internal.Key -> IntMap a -> IntMap a :=
  fix updateWithKey arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | f, k, (Bin p m l r as t) =>
               if nomatch k p m : bool then t else
               if Data.IntSet.Internal.zero k m : bool
               then binCheckLeft p m (updateWithKey f k l) r else
               binCheckRight p m l (updateWithKey f k r)
           | f, k, (Tip ky y as t) =>
               if k GHC.Base.== ky : bool
               then match (f k y) with
                    | Some y' => Tip ky y'
                    | None => Nil
                    end else
               t
           | _, _, Nil => Nil
           end.

Definition update {a}
   : (a -> option a) -> Data.IntSet.Internal.Key -> IntMap a -> IntMap a :=
  fun f =>
    updateWithKey (fun arg_0__ arg_1__ =>
                     match arg_0__, arg_1__ with
                     | _, x => f x
                     end).

Definition bin {a} : Prefix -> Mask -> IntMap a -> IntMap a -> IntMap a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _, _, l, Nil => l
    | _, _, Nil, r => r
    | p, m, l, r => Bin p m l r
    end.

Definition filterWithKey {a}
   : (Data.IntSet.Internal.Key -> a -> bool) -> IntMap a -> IntMap a :=
  fun predicate =>
    let fix go arg_0__
              := match arg_0__ with
                 | Nil => Nil
                 | (Tip k x as t) => if predicate k x : bool then t else Nil
                 | Bin p m l r => bin p m (go l) (go r)
                 end in
    go.

Definition filter {a} : (a -> bool) -> IntMap a -> IntMap a :=
  fun p m =>
    filterWithKey (fun arg_0__ arg_1__ =>
                     match arg_0__, arg_1__ with
                     | _, x => p x
                     end) m.

Definition filterMissing {f} {x} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> x -> bool) -> WhenMissing f x x :=
  fun f =>
    Mk_WhenMissing (fun m => GHC.Base.pure (filterWithKey f m)) (fun k x =>
                      GHC.Base.pure (if f k x : bool then Some x else None)).

Definition filterWithKeyA {f} {a} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> a -> f bool) -> IntMap a -> f (IntMap a) :=
  fix filterWithKeyA arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, Nil => GHC.Base.pure Nil
           | f, (Tip k x as t) =>
               (fun b => if b : bool then t else Nil) Data.Functor.<$> f k x
           | f, Bin p m l r =>
               GHC.Base.liftA2 (bin p m) (filterWithKeyA f l) (filterWithKeyA f r)
           end.

Definition filterAMissing {f} {x} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> x -> f bool) -> WhenMissing f x x :=
  fun f =>
    Mk_WhenMissing (fun m => filterWithKeyA f m) (fun k x =>
                      boolITE None (Some x) Data.Functor.<$> f k x).

Definition intersection {a} {b} : IntMap a -> IntMap b -> IntMap a :=
  fun m1 m2 =>
    mergeWithKey' bin GHC.Base.const (GHC.Base.const Nil) (GHC.Base.const Nil) m1
    m2.

Definition intersectionWithKey {a} {b} {c}
   : (Data.IntSet.Internal.Key -> a -> b -> c) ->
     IntMap a -> IntMap b -> IntMap c :=
  fun f m1 m2 =>
    mergeWithKey' bin (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | Tip k1 x1, Tip _k2 x2 => Tip k1 (f k1 x1 x2)
                         | _, _ => GHC.Err.patternFailure
                         end) (GHC.Base.const Nil) (GHC.Base.const Nil) m1 m2.

Definition intersectionWith {a} {b} {c}
   : (a -> b -> c) -> IntMap a -> IntMap b -> IntMap c :=
  fun f m1 m2 =>
    intersectionWithKey (fun arg_0__ arg_1__ arg_2__ =>
                           match arg_0__, arg_1__, arg_2__ with
                           | _, x, y => f x y
                           end) m1 m2.

Definition mapEitherWithKey {a} {b} {c}
   : (Data.IntSet.Internal.Key -> a -> Data.Either.Either b c) ->
     IntMap a -> (IntMap b * IntMap c)%type :=
  fun f0 t0 =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | f, Bin p m l r =>
                     let 'pair r1 r2 := go f r in
                     let 'pair l1 l2 := go f l in
                     pair (bin p m l1 r1) (bin p m l2 r2)
                 | f, Tip k x =>
                     match f k x with
                     | Data.Either.Left y => (pair (Tip k y) Nil)
                     | Data.Either.Right z => (pair Nil (Tip k z))
                     end
                 | _, Nil => (pair Nil Nil)
                 end in
    id (go f0 t0).

Definition mapEither {a} {b} {c}
   : (a -> Data.Either.Either b c) -> IntMap a -> (IntMap b * IntMap c)%type :=
  fun f m =>
    mapEitherWithKey (fun arg_0__ arg_1__ =>
                        match arg_0__, arg_1__ with
                        | _, x => f x
                        end) m.

Definition mapMaybeWithKey {a} {b}
   : (Data.IntSet.Internal.Key -> a -> option b) -> IntMap a -> IntMap b :=
  fix mapMaybeWithKey arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | f, Bin p m l r => bin p m (mapMaybeWithKey f l) (mapMaybeWithKey f r)
           | f, Tip k x => match f k x with | Some y => Tip k y | None => Nil end
           | _, Nil => Nil
           end.

Definition mapMaybe {a} {b} : (a -> option b) -> IntMap a -> IntMap b :=
  fun f =>
    mapMaybeWithKey (fun arg_0__ arg_1__ =>
                       match arg_0__, arg_1__ with
                       | _, x => f x
                       end).

Definition mapMaybeMissing {f} {x} {y} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> x -> option y) -> WhenMissing f x y :=
  fun f =>
    Mk_WhenMissing (fun m => GHC.Base.pure (mapMaybeWithKey f m)) (fun k x =>
                      GHC.Base.pure (f k x)).

Definition mergeWithKey {a} {b} {c}
   : (Data.IntSet.Internal.Key -> a -> b -> option c) ->
     (IntMap a -> IntMap c) ->
     (IntMap b -> IntMap c) -> IntMap a -> IntMap b -> IntMap c :=
  fun f g1 g2 =>
    let combine :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | Tip k1 x1, Tip _k2 x2 =>
            match f k1 x1 x2 with
            | None => Nil
            | Some x => Tip k1 x
            end
        | _, _ => GHC.Err.patternFailure
        end in
    mergeWithKey' bin combine g1 g2.

Definition difference {a} {b} : IntMap a -> IntMap b -> IntMap a :=
  fun m1 m2 =>
    mergeWithKey (fun arg_0__ arg_1__ arg_2__ => None) GHC.Base.id (GHC.Base.const
                                                                    Nil) m1 m2.

Definition op_zrzr__ {a} {b} : IntMap a -> IntMap b -> IntMap a :=
  fun m1 m2 => difference m1 m2.

Notation "'_\\_'" := (op_zrzr__).

Infix "\\" := (_\\_) (at level 99).

Definition differenceWithKey {a} {b}
   : (Data.IntSet.Internal.Key -> a -> b -> option a) ->
     IntMap a -> IntMap b -> IntMap a :=
  fun f m1 m2 => mergeWithKey f GHC.Base.id (GHC.Base.const Nil) m1 m2.

Definition differenceWith {a} {b}
   : (a -> b -> option a) -> IntMap a -> IntMap b -> IntMap a :=
  fun f m1 m2 =>
    differenceWithKey (fun arg_0__ arg_1__ arg_2__ =>
                         match arg_0__, arg_1__, arg_2__ with
                         | _, x, y => f x y
                         end) m1 m2.

Definition partitionWithKey {a}
   : (Data.IntSet.Internal.Key -> a -> bool) ->
     IntMap a -> (IntMap a * IntMap a)%type :=
  fun predicate0 t0 =>
    let fix go predicate t
              := match t with
                 | Bin p m l r =>
                     let 'pair r1 r2 := go predicate r in
                     let 'pair l1 l2 := go predicate l in
                     pair (bin p m l1 r1) (bin p m l2 r2)
                 | Tip k x => if predicate k x : bool then (pair t Nil) else (pair Nil t)
                 | Nil => (pair Nil Nil)
                 end in
    id (go predicate0 t0).

Definition partition {a}
   : (a -> bool) -> IntMap a -> (IntMap a * IntMap a)%type :=
  fun p m =>
    partitionWithKey (fun arg_0__ arg_1__ =>
                        match arg_0__, arg_1__ with
                        | _, x => p x
                        end) m.

Definition restrictBM {a} : IntSetBitMap -> IntMap a -> IntMap a :=
  GHC.DeferredFix.deferredFix2 (fun restrictBM arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | num_2__, _ =>
                                      if num_2__ GHC.Base.== #0 : bool then Nil else
                                      match arg_0__, arg_1__ with
                                      | bm, Bin p m l r =>
                                          let leftBits := bitmapOf (p Data.Bits..|.(**) m) GHC.Num.- #1 in
                                          let bmL := bm Data.Bits..&.(**) leftBits in
                                          let bmR := Data.Bits.xor bm bmL in
                                          bin p m (restrictBM bmL l) (restrictBM bmR r)
                                      | bm, (Tip k _ as t) =>
                                          if Data.IntSet.Internal.member k (Data.IntSet.Internal.Tip
                                                                          (Coq.NArith.BinNat.N.ldiff k
                                                                                                     Data.IntSet.Internal.suffixBitMask)
                                                                          bm) : bool
                                          then t else
                                          Nil
                                      | _, Nil => Nil
                                      end
                                  end).

Definition restrictKeys {a}
   : IntMap a -> Data.IntSet.Internal.IntSet -> IntMap a :=
  GHC.DeferredFix.deferredFix2 (fun restrictKeys arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | (Bin p1 m1 l1 r1 as t1), (Data.IntSet.Internal.Bin p2 m2 l2 r2 as t2) =>
                                      let intersection2 :=
                                        if nomatch p1 p2 m2 : bool then Nil else
                                        if Data.IntSet.Internal.zero p1 m2 : bool then restrictKeys t1 l2 else
                                        restrictKeys t1 r2 in
                                      let intersection1 :=
                                        if nomatch p2 p1 m1 : bool then Nil else
                                        if Data.IntSet.Internal.zero p2 m1 : bool then restrictKeys l1 t2 else
                                        restrictKeys r1 t2 in
                                      if shorter m1 m2 : bool then intersection1 else
                                      if shorter m2 m1 : bool then intersection2 else
                                      if p1 GHC.Base.== p2 : bool
                                      then bin p1 m1 (restrictKeys l1 l2) (restrictKeys r1 r2) else
                                      Nil
                                  | (Bin p1 m1 _ _ as t1), Data.IntSet.Internal.Tip p2 bm2 =>
                                      let maxbit :=
                                        bitmapOf (p1 Data.Bits..|.(**) (m1 Data.Bits..|.(**) (m1 GHC.Num.- #1))) in
                                      let le_maxbit := maxbit Data.Bits..|.(**) (maxbit GHC.Num.- #1) in
                                      let minbit := bitmapOf p1 in
                                      let ge_minbit :=
                                        Coq.NArith.BinNat.N.lxor (minbit GHC.Num.- #1) (Coq.NArith.BinNat.N.ones (64 %
                                                                                                                  N)) in
                                      restrictBM ((bm2 Data.Bits..&.(**) ge_minbit) Data.Bits..&.(**) le_maxbit)
                                      (lookupPrefix p2 t1)
                                  | Bin _ _ _ _, Data.IntSet.Internal.Nil => Nil
                                  | (Tip k1 _ as t1), t2 =>
                                      if Data.IntSet.Internal.member k1 t2 : bool then t1 else
                                      Nil
                                  | Nil, _ => Nil
                                  end).

Definition traverseMaybeWithKey {f} {a} {b} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> a -> f (option b)) ->
     IntMap a -> f (IntMap b) :=
  fun f =>
    let fix go arg_0__
              := match arg_0__ with
                 | Nil => GHC.Base.pure Nil
                 | Tip k x => Data.Maybe.maybe Nil (Tip k) Data.Functor.<$> f k x
                 | Bin p m l r => GHC.Base.liftA2 (bin p m) (go l) (go r)
                 end in
    go.

Definition traverseMaybeMissing {f} {x} {y} `{GHC.Base.Applicative f}
   : (Data.IntSet.Internal.Key -> x -> f (option y)) -> WhenMissing f x y :=
  fun f => Mk_WhenMissing (traverseMaybeWithKey f) f.

Definition withoutBM {a} : IntSetBitMap -> IntMap a -> IntMap a :=
  GHC.DeferredFix.deferredFix2 (fun withoutBM arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | num_2__, t =>
                                      if num_2__ GHC.Base.== #0 : bool then t else
                                      match arg_0__, arg_1__ with
                                      | bm, Bin p m l r =>
                                          let leftBits := bitmapOf (p Data.Bits..|.(**) m) GHC.Num.- #1 in
                                          let bmL := bm Data.Bits..&.(**) leftBits in
                                          let bmR := Data.Bits.xor bm bmL in bin p m (withoutBM bmL l) (withoutBM bmR r)
                                      | bm, (Tip k _ as t) =>
                                          if Data.IntSet.Internal.member k (Data.IntSet.Internal.Tip
                                                                          (Coq.NArith.BinNat.N.ldiff k
                                                                                                     Data.IntSet.Internal.suffixBitMask)
                                                                          bm) : bool
                                          then Nil else
                                          t
                                      | _, Nil => Nil
                                      end
                                  end).

Definition withoutKeys {a}
   : IntMap a -> Data.IntSet.Internal.IntSet -> IntMap a :=
  GHC.DeferredFix.deferredFix2 (fun withoutKeys arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | (Bin p1 m1 l1 r1 as t1), (Data.IntSet.Internal.Bin p2 m2 l2 r2 as t2) =>
                                      let difference2 :=
                                        if nomatch p1 p2 m2 : bool then t1 else
                                        if Data.IntSet.Internal.zero p1 m2 : bool then withoutKeys t1 l2 else
                                        withoutKeys t1 r2 in
                                      let difference1 :=
                                        if nomatch p2 p1 m1 : bool then t1 else
                                        if Data.IntSet.Internal.zero p2 m1 : bool
                                        then binCheckLeft p1 m1 (withoutKeys l1 t2) r1 else
                                        binCheckRight p1 m1 l1 (withoutKeys r1 t2) in
                                      if shorter m1 m2 : bool then difference1 else
                                      if shorter m2 m1 : bool then difference2 else
                                      if p1 GHC.Base.== p2 : bool
                                      then bin p1 m1 (withoutKeys l1 l2) (withoutKeys r1 r2) else
                                      t1
                                  | (Bin p1 m1 _ _ as t1), Data.IntSet.Internal.Tip p2 bm2 =>
                                      let maxbit :=
                                        bitmapOf (p1 Data.Bits..|.(**) (m1 Data.Bits..|.(**) (m1 GHC.Num.- #1))) in
                                      let gt_maxbit :=
                                        Data.Bits.xor maxbit (Coq.NArith.BinNat.N.lxor (maxbit GHC.Num.- #1)
                                                                                       (Coq.NArith.BinNat.N.ones (64 %
                                                                                                                  N))) in
                                      let minbit := bitmapOf p1 in
                                      let lt_minbit := minbit GHC.Num.- #1 in
                                      updatePrefix p2 t1 (withoutBM ((bm2 Data.Bits..|.(**) lt_minbit)
                                                                     Data.Bits..|.(**)
                                                                     gt_maxbit))
                                  | (Bin _ _ _ _ as t1), Data.IntSet.Internal.Nil => t1
                                  | (Tip k1 _ as t1), t2 =>
                                      if Data.IntSet.Internal.member k1 t2 : bool then Nil else
                                      t1
                                  | Nil, _ => Nil
                                  end).

Definition assocs {a} : IntMap a -> list (Data.IntSet.Internal.Key * a)%type :=
  toAscList.

Definition alterF {f} {a} `{GHC.Base.Functor f}
   : (option a -> f (option a)) ->
     Data.IntSet.Internal.Key -> IntMap a -> f (IntMap a) :=
  fun f k m =>
    let mv := lookup k m in
    (fun arg_1__ => arg_1__ Data.Functor.<$> f mv) (fun fres =>
                                                      match fres with
                                                      | None => Data.Maybe.maybe m (GHC.Base.const (delete k m)) mv
                                                      | Some v' => insert k v' m
                                                      end).

Definition alter {a}
   : (option a -> option a) -> Data.IntSet.Internal.Key -> IntMap a -> IntMap a :=
  fix alter arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | f, k, (Bin p m l r as t) =>
               if nomatch k p m : bool
               then match f None with
                    | None => t
                    | Some x => link k (Tip k x) p t
                    end else
               if Data.IntSet.Internal.zero k m : bool
               then binCheckLeft p m (alter f k l) r else
               binCheckRight p m l (alter f k r)
           | f, k, (Tip ky y as t) =>
               if k GHC.Base.== ky : bool
               then match f (Some y) with
                    | Some x => Tip ky x
                    | None => Nil
                    end else
               match f None with
               | Some x => link k (Tip k x) ky t
               | None => Tip ky y
               end
           | f, k, Nil => match f None with | Some x => Tip k x | None => Nil end
           end.

Definition adjustWithKey {a}
   : (Data.IntSet.Internal.Key -> a -> a) ->
     Data.IntSet.Internal.Key -> IntMap a -> IntMap a :=
  fix adjustWithKey arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | f, k, (Bin p m l r as t) =>
               if nomatch k p m : bool then t else
               if Data.IntSet.Internal.zero k m : bool
               then Bin p m (adjustWithKey f k l) r else
               Bin p m l (adjustWithKey f k r)
           | f, k, (Tip ky y as t) => if k GHC.Base.== ky : bool then Tip ky (f k y) else t
           | _, _, Nil => Nil
           end.

Definition adjust {a}
   : (a -> a) -> Data.IntSet.Internal.Key -> IntMap a -> IntMap a :=
  fun f k m =>
    adjustWithKey (fun arg_0__ arg_1__ =>
                     match arg_0__, arg_1__ with
                     | _, x => f x
                     end) k m.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.IntMap.Internal.Read1__IntMap' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.IntMap.Internal.Read__IntMap' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.IntMap.Internal.Show1__IntMap' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.IntMap.Internal.Show__IntMap' *)

(* Skipping instance `Data.IntMap.Internal.Ord1__IntMap' of class
   `Data.Functor.Classes.Ord1' *)

Local Definition Ord__IntMap_compare {inst_a} `{GHC.Base.Ord inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> comparison :=
  fun m1 m2 => GHC.Base.compare (toList m1) (toList m2).

Local Definition Ord__IntMap_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> bool :=
  fun x y => Ord__IntMap_compare x y GHC.Base.== Lt.

Local Definition Ord__IntMap_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> bool :=
  fun x y => Ord__IntMap_compare x y GHC.Base./= Gt.

Local Definition Ord__IntMap_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> bool :=
  fun x y => Ord__IntMap_compare x y GHC.Base.== Gt.

Local Definition Ord__IntMap_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> bool :=
  fun x y => Ord__IntMap_compare x y GHC.Base./= Lt.

Local Definition Ord__IntMap_max {inst_a} `{GHC.Base.Ord inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> (IntMap inst_a) :=
  fun x y => if Ord__IntMap_op_zlze__ x y : bool then y else x.

Local Definition Ord__IntMap_min {inst_a} `{GHC.Base.Ord inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> (IntMap inst_a) :=
  fun x y => if Ord__IntMap_op_zlze__ x y : bool then x else y.

Local Definition Eq___IntMap_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> bool :=
  fun t1 t2 => equal t1 t2.

Local Definition Eq___IntMap_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> bool :=
  fun t1 t2 => nequal t1 t2.

Program Instance Eq___IntMap {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (IntMap a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___IntMap_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___IntMap_op_zsze__ |}.

Program Instance Ord__IntMap {a} `{GHC.Base.Ord a} : GHC.Base.Ord (IntMap a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__IntMap_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__IntMap_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__IntMap_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__IntMap_op_zgze__ ;
         GHC.Base.compare__ := Ord__IntMap_compare ;
         GHC.Base.max__ := Ord__IntMap_max ;
         GHC.Base.min__ := Ord__IntMap_min |}.

(* Skipping instance `Data.IntMap.Internal.Eq1__IntMap' of class
   `Data.Functor.Classes.Eq1' *)

(* Skipping all instances of class `GHC.Exts.IsList', including
   `Data.IntMap.Internal.IsList__IntMap' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.IntMap.Internal.Data__IntMap' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Data.IntMap.Internal.NFData__IntMap' *)

Local Definition Traversable__IntMap_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> IntMap a -> f (IntMap b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun f => traverseWithKey (fun arg_0__ => f).

Local Definition Traversable__IntMap_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> IntMap a -> m (IntMap b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__IntMap_traverse.

Local Definition Traversable__IntMap_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, IntMap (f a) -> f (IntMap a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__IntMap_traverse GHC.Base.id.

Local Definition Traversable__IntMap_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, IntMap (m a) -> m (IntMap a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__IntMap_sequenceA.

Local Definition Foldable__IntMap_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, IntMap m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    let fix go arg_0__
              := match arg_0__ with
                 | Nil => GHC.Base.mempty
                 | Tip _ v => v
                 | Bin _ _ l r => GHC.Base.mappend (go l) (go r)
                 end in
    go.

Local Definition Foldable__IntMap_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> IntMap a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f t =>
      let fix go arg_0__
                := match arg_0__ with
                   | Nil => GHC.Base.mempty
                   | Tip _ v => f v
                   | Bin _ _ l r => GHC.Base.mappend (go l) (go r)
                   end in
      go t.

Local Definition Foldable__IntMap_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> IntMap a -> b :=
  fun {b} {a} => foldl.

Local Definition Foldable__IntMap_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> IntMap a -> b :=
  fun {b} {a} => foldl'.

Local Definition Foldable__IntMap_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> IntMap a -> b :=
  fun {a} {b} => foldr.

Local Definition Foldable__IntMap_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> IntMap a -> b :=
  fun {a} {b} => foldr'.

Definition Foldable__IntMap_length : forall {a}, IntMap a -> GHC.Num.Int :=
  fun {a} x => Coq.ZArith.BinInt.Z.of_N (size x).

Local Definition Foldable__IntMap_null : forall {a}, IntMap a -> bool :=
  fun {a} => null.

Local Definition Foldable__IntMap_product
   : forall {a}, forall `{GHC.Num.Num a}, IntMap a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.*_ #1.

Local Definition Foldable__IntMap_sum
   : forall {a}, forall `{GHC.Num.Num a}, IntMap a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.+_ #0.

Local Definition Foldable__IntMap_toList : forall {a}, IntMap a -> list a :=
  fun {a} => elems.

Program Instance Foldable__IntMap : Data.Foldable.Foldable IntMap :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__IntMap_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__IntMap_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__IntMap_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__IntMap_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__IntMap_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__IntMap_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__IntMap_length ;
         Data.Foldable.null__ := fun {a} => Foldable__IntMap_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__IntMap_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__IntMap_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__IntMap_toList |}.

Program Instance Traversable__IntMap : Data.Traversable.Traversable IntMap :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__IntMap_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__IntMap_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__IntMap_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__IntMap_traverse |}.

Local Definition Semigroup__IntMap_op_zlzlzgzg__ {inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> (IntMap inst_a) :=
  union.

Program Instance Semigroup__IntMap {a} : GHC.Base.Semigroup (IntMap a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__IntMap_op_zlzlzgzg__ |}.

Local Definition Monoid__IntMap_mappend {inst_a}
   : (IntMap inst_a) -> (IntMap inst_a) -> (IntMap inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__IntMap_mconcat {inst_a}
   : list (IntMap inst_a) -> (IntMap inst_a) :=
  unions.

Local Definition Monoid__IntMap_mempty {inst_a} : (IntMap inst_a) :=
  empty.

Program Instance Monoid__IntMap {a} : GHC.Base.Monoid (IntMap a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__IntMap_mappend ;
         GHC.Base.mconcat__ := Monoid__IntMap_mconcat ;
         GHC.Base.mempty__ := Monoid__IntMap_mempty |}.

(* Skipping instance `Data.IntMap.Internal.Monad__WhenMissing' of class
   `GHC.Base.Monad' *)

(* Skipping instance `Data.IntMap.Internal.Applicative__WhenMissing' of class
   `GHC.Base.Applicative' *)

(* Skipping instance `Data.IntMap.Internal.Category__WhenMissing' of class
   `Control.Category.Category' *)

(* Skipping instance `Data.IntMap.Internal.Functor__WhenMissing' of class
   `GHC.Base.Functor' *)

(* Skipping instance `Data.IntMap.Internal.Monad__WhenMatched' of class
   `GHC.Base.Monad' *)

(* Skipping instance `Data.IntMap.Internal.Applicative__WhenMatched' of class
   `GHC.Base.Applicative' *)

(* Skipping instance `Data.IntMap.Internal.Category__WhenMatched' of class
   `Control.Category.Category' *)

(* Skipping instance `Data.IntMap.Internal.Functor__WhenMatched' of class
   `GHC.Base.Functor' *)

Module Notations.
Notation "'_Data.IntMap.Internal.!?_'" := (op_znz3fU__).
Infix "Data.IntMap.Internal.!?" := (_!?_) (at level 99).
Notation "'_Data.IntMap.Internal.\\_'" := (op_zrzr__).
Infix "Data.IntMap.Internal.\\" := (_\\_) (at level 99).
End Notations.

(* External variables:
     Eq Gt IntMap_op_zlzd__ Lt N None Some andb bool comparison cons false id list
     negb nil op_zt__ op_zv__ option orb pair true Coq.NArith.BinNat.N.ldiff
     Coq.NArith.BinNat.N.lxor Coq.NArith.BinNat.N.ones Coq.Numbers.BinNums.N
     Coq.ZArith.BinInt.Z.of_N Data.Bits.op_zizazi__ Data.Bits.op_zizbzi__
     Data.Bits.xor Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl' Data.Foldable.foldl'__ Data.Foldable.foldl__
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.Functor.op_zlzdzg__ Data.Functor.Identity.Identity
     Data.IntSet.Internal.Bin Data.IntSet.Internal.IntSet Data.IntSet.Internal.Key
     Data.IntSet.Internal.Nil Data.IntSet.Internal.Tip Data.IntSet.Internal.bitmapOf
     Data.IntSet.Internal.mask Data.IntSet.Internal.member
     Data.IntSet.Internal.singleton Data.IntSet.Internal.suffixBitMask
     Data.IntSet.Internal.zero Data.Maybe.maybe Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.String
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.id GHC.Base.liftA2 GHC.Base.mappend GHC.Base.mappend__ GHC.Base.max__
     GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__
     GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zgzgze__
     GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlzd____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.pure
     GHC.DeferredFix.deferredFix2 GHC.DeferredFix.deferredFix4 GHC.Err.error
     GHC.Err.patternFailure GHC.Num.Int GHC.Num.Num GHC.Num.Word GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__
     Utils.Containers.Internal.BitUtil.highestBitMask
     Utils.Containers.Internal.BitUtil.shiftLL
     Utils.Containers.Internal.BitUtil.shiftRL
*)
