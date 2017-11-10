(* Partial version of Data.IntMap.Strict using FMaps. *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.FSets.FMapAVL.
Require Coq.Structures.OrderedTypeEx.

Require Import GHC.Base.
Require Data.Monoid.

Module IM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).

Definition IntMap  := IM.t.

(*

IM.empty: forall elt : Type, IM.t elt
IM.is_empty: forall elt : Type, IM.t elt -> bool
IM.add: forall elt : Type, IM.key -> elt -> IM.t elt -> IM.t elt
IM.remove: forall elt : Type, IM.key -> IM.t elt -> IM.t elt
IM.mem: forall elt : Type, IM.key -> IM.t elt -> bool
IM.find: forall elt : Type, IM.key -> IM.t elt -> option elt
IM.map: forall elt elt' : Type, (elt -> elt') -> IM.t elt -> IM.t elt'
IM.mapi: forall elt elt' : Type, (IM.key -> elt -> elt') -> IM.t elt -> IM.t elt'
IM.map2:
  forall elt elt' elt'' : Type,
  (option elt -> option elt' -> option elt'') -> IM.t elt -> IM.t elt' -> IM.t elt''
IM.elements: forall elt : Type, IM.t elt -> list (IM.key * elt)
IM.cardinal: forall elt : Type, IM.t elt -> nat
IM.fold: forall elt A : Type, (IM.key -> elt -> A -> A) -> IM.t elt -> A -> A
IM.equal: forall elt : Type, (elt -> elt -> bool) -> IM.t elt -> IM.t elt -> bool

*)


Definition null {a} (x:IM.t a) := IM.is_empty x.
Definition empty {a} := @IM.empty a.
Definition add {a} k (v:a) := IM.add k v.
Definition insert {a} k (v:a) := IM.add k v.
Definition singleton {a} k (v:a) := IM.add k v (@IM.empty a).

Definition insertWithKey {a} : (Int -> a -> a -> a) -> Int -> a -> IntMap a -> IntMap a :=
  fun comb k v m =>
    match IM.find k m with
    | Some u => IM.add k (comb k v u) m
    | Nothing => IM.add k v m
    end.

Definition insertWith {a} : (a -> a -> a) -> Int -> a -> IntMap a -> IntMap a :=
  fun comb k v m => insertWithKey (fun _ => comb) k v m.


Definition delete {a} k (m:IntMap a) := IM.remove k m.
Definition member {a} k (m:IntMap a) := IM.mem k m.
Definition lookup {a} k (m:IntMap a) := IM.find k m.
Definition findWithDefault {a} : a -> Int -> IntMap a -> a :=
  fun def k m => match lookup k m with
                | Some v => v
                | None => def
              end.

Definition map {a}{b} (f : a -> b) (m : IntMap a) := IM.map f m.
Definition mapWithKey {a}{b} (f : Int -> a -> b) (m : IntMap a) := IM.mapi f m.
Definition union {a} (m1 : IntMap a) (m2 : IntMap a)
  := IM.map2 (fun mx my =>
                match mx with | Some x => Some x | None => my end) m1 m2.
Definition unionWith {a} (f : a -> a -> a) (m1 : IntMap a) (m2 : IntMap a)
  := IM.map2 (fun mx my =>
                match mx with
                | Some x => match my with
                         | Some y => Some (f x y)
                         | None => None
                         end
                | None => my end) m1 m2.

Definition elems {a} (m : IntMap a) : list a :=
  GHC.Base.map (fun x => match x with (y,z) => z end) (@IM.elements a m).
Definition keys {a} (m : IntMap a) : list Int :=
  GHC.Base.map (fun x => match x with (y,z) => y end) (@IM.elements a m).

Definition foldWithKey {a}{b} : (Int -> a -> b -> b) -> b -> IntMap a -> b :=
  fun f b m => IM.fold f m b.
Definition foldrWithKey {a}{b} : (Int -> a -> b -> b) -> b -> IntMap a -> b :=
  fun f b m => IM.fold f m b.
Definition foldr {a}{b} (f : a -> b -> b) := foldrWithKey (fun k => f).
Definition foldr' {a}{b} (f : a -> b -> b) := foldrWithKey (fun k => f).
Definition foldrWithKey' {a}{b} : (Int -> a -> b -> b) -> b -> IntMap a -> b :=
  fun f b m => IM.fold f m b.
Definition fold {a}{b} (f : a -> b -> b) := foldrWithKey (fun k => f).


Definition toList {a} (m: IM.t a) := IM.fold (fun k v x => cons (k,v) x) m nil.

Definition splitLookup {a} k1 (m : IM.t a) : (IM.t a * option a * IM.t a) :=
  IM.fold (fun k v tri => match tri with
                         | (lm, ko, rm) =>
                           if Z.leb k k1 then (IM.add k v lm, ko, rm)
                           else if Z.geb k k1 then (lm, ko, IM.add k v rm)
                                else (lm, Some v, rm)
                         end) m (@IM.empty a, None, @IM.empty a).


Definition size {a} (m : IM.t a) : Z := Z.of_nat (IM.cardinal m).

Definition partitionWithKey {a} : (Int -> a -> bool) -> IntMap a -> (IntMap a * IntMap a) :=
  fun f m => IM.fold (fun k v p => match p with
                           | (in_, out) => if f k v then (IM.add k v in_, out)
                                         else (in_, IM.add k v out)
                           end) m (empty, empty).

Definition partition {a} : (a -> bool) -> IntMap a -> (IntMap a * IntMap a) :=
  fun p m =>  partitionWithKey (fun _ x => p x) m.

Definition intersectionWith {a}{b}{c} : (a -> b -> c) -> IntMap a -> IntMap b -> IntMap c :=
  fun f m1 m2 =>
    IM.map2 (fun mx my => match mx,my with
                       | Some x, Some y => Some (f x y)
                       | _ , _ => None
                       end) m1 m2.
Definition intersection {a}{b}  : IntMap a -> IntMap b -> IntMap a :=
  fun m1 m2 => intersectionWith (fun x y => x) m1 m2.

Definition filterWithKey {a} : (Int -> a -> bool) -> IntMap a -> IntMap a :=
  fun p m => IM.fold (fun k v x => if p k v then IM.add k v x else x) m empty.

Definition filter {a} : (a -> bool) -> IntMap a -> IntMap a :=
  fun p m => filterWithKey (fun _ x => p x) m.



Definition difference {a} {b} : IntMap a -> IntMap b -> IntMap a :=
  fun m1 m2 =>
    IM.map2 (fun mx my =>
               match mx, my with
               | Some x, Some y => None
               | Some x, _      => Some x
               | None  , _      => None
               end) m1 m2.

Definition alter {a} : (option a -> option a) -> Int -> IntMap a -> IntMap a :=
  fun f k m =>
    match f (lookup k m) with
    | Some v => IM.add k v m
    | None => m
    end.

Definition adjust {a} : (a -> a) -> Int -> IntMap a -> IntMap a :=
  fun f k m =>
    match lookup k m with
    | Some v => IM.add k (f v) m
    | None => m
    end.


Instance instance_Eq_IntMap {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (IntMap a) := fun _ k => k {|
  op_zeze____ := IM.equal GHC.Base.op_zeze__ ;
  op_zsze____ := fun x y => negb (IM.equal GHC.Base.op_zeze__ x y)
|}.


Instance instance_Monoid_IntMap {a} `{GHC.Base.Monoid a} : GHC.Base.Monoid (IntMap a) :=
  fun _ k => k {|
  GHC.Base.mempty__ := empty;
  GHC.Base.mappend__ := unionWith GHC.Base.mempty;
  GHC.Base.mconcat__ := GHC.Base.foldr (unionWith GHC.Base.mempty) empty;
|}.

Instance instance_Functor_IntMap : GHC.Base.Functor IntMap :=
  fun _ k => k {|
    GHC.Base.fmap__ := IM.map ;
    GHC.Base.op_zlzd____ := fun {b}{c} (x:b) => IM.map (fun j => x) |}.
