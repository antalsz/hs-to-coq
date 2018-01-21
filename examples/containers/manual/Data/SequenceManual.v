(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.


(* Converted imports: *)

Require Control.Applicative.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Identity.
Require Data.Maybe.
Require Data.Monoid.
Require Data.OldList.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Tuple.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive State s a : Type := Mk_State : (s -> (s * a)%type) -> State s a.

Inductive Split t a : Type := Mk_Split : t -> a -> t -> Split t a.

(* Make nat instead of Int. *)
Record Sized__Dict a := Sized__Dict_Build {
  size__ : a -> nat }.

Definition Sized a :=
  forall r, (Sized__Dict a -> r) -> r.

Existing Class Sized.

Definition size `{g : Sized a} : a -> nat :=
  g _ (size__ a).

Inductive Place a : Type := Mk_Place : nat -> a -> Place a.

Inductive PQL e : Type := Nil : PQL e
                       |  op_ZCza__ : (PQueue e) -> PQL e -> PQL e
with PQueue e : Type := Mk_PQueue : e -> (PQL e) -> PQueue e.

Inductive Node a : Type := Node2 : nat -> a -> a -> Node a
                        |  Node3 : nat -> a -> a -> a -> Node a.

Inductive Maybe2 a b : Type := Nothing2 : Maybe2 a b
                            |  Just2 : a -> b -> Maybe2 a b.

Inductive Elem a : Type := Mk_Elem : a -> Elem a.

Definition Digit23 :=
  Node%type.

Inductive Digit12 a : Type := One12 : a -> Digit12 a
                           |  Two12 : a -> a -> Digit12 a.

Inductive Thin a : Type := EmptyTh : Thin a
                        |  SingleTh : a -> Thin a
                        |  DeepTh : nat -> (Digit12 a) -> (Thin (Node a)) -> (Digit12 a) -> Thin
                                    a.

Inductive Rigid a : Type := Mk_Rigid : nat -> (Digit23 a) -> (Thin (Node a)) -> (Digit23 a) -> Rigid a.

Inductive Rigidified a : Type := RigidEmpty : Rigidified a
                              |  RigidOne : a -> Rigidified a
                              |  RigidTwo : a -> a -> Rigidified a
                              |  RigidThree : a -> a -> a -> Rigidified a
                              |  RigidFull : (Rigid a) -> Rigidified a.

Inductive Digit a : Type := One : a -> Digit a
                         |  Two : a -> a -> Digit a
                         |  Three : a -> a -> a -> Digit a
                         |  Four : a -> a -> a -> a -> Digit a.

Inductive FingerTree a : Type := Empty : FingerTree a
                              |  Single : a -> FingerTree a
                              |  Deep : nat -> (Digit a) -> (FingerTree (Node a)) -> (Digit a) -> FingerTree a.

Inductive Seq a : Type := Mk_Seq : (FingerTree (Elem a)) -> Seq a.

Inductive ViewL a : Type := EmptyL : ViewL a
                         |  op_ZCzl__ : a -> Seq a -> ViewL a.

Inductive ViewR a : Type := EmptyR : ViewR a
                         |  op_ZCzg__ : Seq a -> a -> ViewR a.

Arguments Mk_State {_} {_} _.

Arguments Mk_Split {_} {_} _ _ _.

Arguments Mk_Place {_} _ _.

Arguments Nil {_}.

Arguments op_ZCza__ {_} _ _.

Arguments Mk_PQueue {_} _ _.

Arguments Node2 {_} _ _ _.

Arguments Node3 {_} _ _ _ _.

Arguments Nothing2 {_} {_}.

Arguments Just2 {_} {_} _ _.

Arguments Mk_Elem {_} _.

Arguments One12 {_} _.

Arguments Two12 {_} _ _.

Arguments EmptyTh {_}.

Arguments SingleTh {_} _.

Arguments DeepTh {_} _ _ _ _.

Arguments Mk_Rigid {_} _ _ _ _.

Arguments RigidEmpty {_}.

Arguments RigidOne {_} _.

Arguments RigidTwo {_} _ _.

Arguments RigidThree {_} _ _ _.

Arguments RigidFull {_} _.

Arguments One {_} _.

Arguments Two {_} _ _.

Arguments Three {_} _ _ _.

Arguments Four {_} _ _ _ _.

Arguments Empty {_}.

Arguments Single {_} _.

Arguments Deep {_} _ _ _ _.

Arguments Mk_Seq {_} _.

Arguments EmptyL {_}.

Arguments op_ZCzl__ {_} _ _.

Arguments EmptyR {_}.

Arguments op_ZCzg__ {_} _ _.

Definition runState {s} {a} (arg_0__ : State s a) :=
  match arg_0__ with
    | Mk_State runState => runState
  end.

Definition getElem {a} (arg_1__ : Elem a) :=
  match arg_1__ with
    | Mk_Elem getElem => getElem
  end.
(* Midamble *)
Require Import Omega.

(*  ----------------------------------------------------------- *)

Record Foldable1__Dict (t : Type -> Type) := Foldable1__Dict_Build {
  foldl1__ : forall {a}, (a -> a -> a) -> t a -> a  }.

Definition Foldable1 a :=
  forall r, (Foldable1__Dict a -> r) -> r.

Existing Class Foldable1.

Definition foldl1 `{g : Foldable1 t} : forall {a}, (a -> a -> a) -> t a -> a :=
  g _ (foldl1__ t).

Definition Digit_foldl1 {a} (f : a -> a -> a) (t : Digit a) : a :=
  match t with
  | One x => x
  | Two x y => f x y
  | Three x y z => f (f x y) z
  | Four x y z w => f (f (f x y) z) w
  end.

Program Instance Foldable1_Digit : Foldable1 Digit := fun _ k =>
  k {| foldl1__ := fun {a} => Digit_foldl1 |}.

(*  ----------------------------------------------------------- *)

Instance Unpeel_Elem a : GHC.Prim.Unpeel (Elem a) a :=
  GHC.Prim.Build_Unpeel _ _ (fun x => match x with Mk_Elem y => y end) Mk_Elem.

(*  ----------------------------------------------------------- *)

Local Definition Functor__Digit_fmap : forall {a} {b},
                                         (a -> b) -> Digit a -> Digit b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , One a => One (f a)
        | f , Two a b => Two (f a) (f b)
        | f , Three a b c => Three (f a) (f b) (f c)
        | f , Four a b c d => Four (f a) (f b) (f c) (f d)
      end.

Local Definition Functor__Digit_op_zlzd__ : forall {a} {b},
                                              a -> Digit b -> Digit a :=
  fun {a} {b} => fun x => Functor__Digit_fmap (GHC.Base.const x).

Program Instance Functor__Digit : GHC.Base.Functor Digit := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Digit_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Digit_fmap |}.

(*  ----------------------------------------------------------- *)

Local Definition Sized__FingerTree_size {inst_a} `{Sized inst_a} : (FingerTree inst_a) -> nat :=
  fun arg_0__ =>
    match arg_0__ with
      | Empty => 0
      | Single x => size x
      | Deep v _ _ _ => v
    end.

Program Instance Sized__FingerTree {a} `{Sized a} : Sized (FingerTree a) :=
  fun _ k => k {|size__ := Sized__FingerTree_size |}.

Local Definition Sized__Digit_size {inst_a} `{Sized inst_a} : (Digit inst_a) -> nat :=
  foldl1 (fun x y => x + y)  GHC.Base.∘ GHC.Base.fmap size.

Program Instance Sized__Digit {a} `{Sized a} : Sized (Digit a) := fun _ k =>
    k {|size__ := Sized__Digit_size |}.

Local Definition Sized__Node_size {inst_a} : (Node inst_a) -> nat :=
  fun arg_0__ => match arg_0__ with | Node2 v _ _ => v | Node3 v _ _ _ => v end.

Program Instance Sized__Node {a} : Sized (Node a) := fun _ k =>
    k {|size__ := Sized__Node_size |}.

Local Definition Sized__Elem_size {inst_a} : (Elem inst_a) -> nat :=
  fun arg_0__ => 1.

Program Instance Sized__Elem {a} : Sized (Elem a) := fun _ k =>
    k {|size__ := Sized__Elem_size |}.


(*  ----------------------------------------------------------- *)

Notation "'_:<_'" := (op_ZCzl__).

Infix ":<" := (_:<_) (at level 99).

Notation "'_:>_'" := (op_ZCzg__).

Infix ":>" := (_:>_) (at level 99).

Notation "'_:&_'" := (op_ZCza__).

Infix ":&" := (_:&_) (at level 99).


(*  ----------------------------------------------------------- *)
(* CHANGE to Default.panic *)

Parameter error : forall {a}, a.

(* Move to base: missing record selectors *)
Definition runIdentity {a} (x: Data.Functor.Identity.Identity a) : a :=
  match x with
  | Data.Functor.Identity.Mk_Identity y => y
  end.

Definition unwrapMonad {m}{a} (x: Control.Applicative.WrappedMonad m a) :=
  match x with
  | Control.Applicative.WrapMonad y => y
  end.

(*  ----------------------------------------------------------- *)

Definition map_elem {a} : list a -> list (Elem a) := fun xs => GHC.Prim.coerce xs.

Definition getNodes {a} : nat -> a -> list a -> (list (Node a) * Digit a)%type :=
    fix getNodes arg_1__ arg_2__ arg_3__
          := let j_9__ :=
               match arg_1__ , arg_2__ , arg_3__ with
                 | _ , x1 , nil => pair nil (One x1)
                 | _ , x1 , cons x2 nil => pair nil (Two x1 x2)
                 | _ , x1 , cons x2 (cons x3 nil) => pair nil (Three x1 x2 x3)
                 | s , x1 , cons x2 (cons x3 (cons x4 xs)) =>
                   match getNodes s x4 xs with
                   | pair ns d => pair (cons (Node3 s x1 x2 x3) ns) d
                   end
               end in
             match arg_1__ , arg_2__ , arg_3__ with
             | arg , _ , _ => j_9__
             end.



Program Fixpoint  mkTree {a} `{(Sized a)} (s:nat) (x : list a) {measure (length x)} : FingerTree a :=
    match x with
    | nil => Empty
    | cons x1 nil => Single x1
    | cons x1 (cons x2 nil) => Deep (2 * s) (One x1) Empty (One x2)
    | cons x1 (cons x2 (cons x3 nil)) => Deep (3 * s) (One x1) Empty (Two x2 x3)
    | cons x1 (cons x2 (cons x3 (cons x4 xs))) =>
      match getNodes (3 * s) x4 xs with
      | pair ns sf => match mkTree (3 * s) ns with
                     | m => GHC.Prim.seq m (Deep (((3 * size x1)
                                                    + size m)
                                                   + size sf)
                                                (Three x1 x2 x3) m sf)
                     end
      end
    end.
Obligation 1.
admit.
Admitted.

Definition fromList {a} : list a -> Seq a :=
  Mk_Seq GHC.Base.∘ ((@mkTree (Elem a) _ 1) GHC.Base.∘ map_elem).

(*  ----------------------------------------------------------- *)

Definition  mapWithIndexNode {a} {b} `{Sized a}
                             : (nat -> a -> b) -> nat -> Node a -> Node b :=
                             fun arg_2__ arg_3__ arg_4__ =>
                               match arg_2__ , arg_3__ , arg_4__ with
                                 | f , s , Node2 ns a b => let sPsa := s + size a in
                                                           GHC.Prim.seq sPsa (Node2 ns (f s a) (f sPsa b))
                                 | f , s , Node3 ns a b c => let sPsa := s + size a in
                                                             let sPsab := sPsa + size b in
                                                             GHC.Prim.seq sPsa (GHC.Prim.seq sPsab (Node3 ns (f s a) (f
                                                                                                                     sPsa
                                                                                                                     b)
                                                                                             (f sPsab c)))
                               end.

Definition  mapWithIndexDigit {a} {b} `{Sized a}
  : (nat -> a -> b) -> nat -> Digit a -> Digit b :=
  fun arg_11__ arg_12__ arg_13__ =>
    match arg_11__ , arg_12__ , arg_13__ with
    | f , s , One a => One (f s a)
    | f , s , Two a b => let sPsa := s + size a in
                        GHC.Prim.seq sPsa (Two (f s a) (f sPsa b))
    | f , s , Three a b c => let sPsa := s + size a in
                            let sPsab := sPsa + size b in
                            GHC.Prim.seq sPsa (GHC.Prim.seq sPsab (Three (f s a) (f sPsa
                                                                                    b) (f
                                                                                          sPsab
                                                                                          c)))
    | f , s , Four a b c d => let sPsa := s + size a in
                             let sPsab := sPsa + size b in
                             let sPsabc := sPsab + size c in
                             GHC.Prim.seq sPsa (GHC.Prim.seq sPsab (GHC.Prim.seq sPsabc
                                                                                 (Four (f
                                                                                          s
                                                                                          a)
                                                                                       (f sPsa
                                                                                          b) (f
                                                                                                sPsab
                                                                                                c) (f
                                                                                                      sPsabc
                                                                                                      d))))
    end.


Fixpoint mapWithIndexTree {a} {b} `{Sized a} (f : nat -> a -> b) (s : nat) (ft: FingerTree a) : FingerTree b :=
  match ft with
  | Empty => GHC.Prim.seq s Empty
  | Single xs => Single GHC.Base.$ f s xs
  | Deep n pr m sf =>
    let sPsprm := (s + n) - size sf in
    let sPspr := s + size pr in
    GHC.Prim.seq sPspr (GHC.Prim.seq sPsprm
                                     (Deep n  (mapWithIndexDigit
                                                                              f s pr)
                                                                           (mapWithIndexTree
                                                                              (mapWithIndexNode
                                                                                 f) sPspr m)
                                                                           (mapWithIndexDigit
                                                                              f sPsprm sf)))
  end.

Definition mapWithIndex {a} {b} : (nat -> a -> b) -> Seq a -> Seq b :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f' , Mk_Seq xs' =>  Mk_Seq GHC.Base.$ mapWithIndexTree (fun arg_34__ arg_35__ =>
                                                                match arg_34__ , arg_35__ with
                                                                  | s , Mk_Elem a => Mk_Elem (f' s a)
                                                                end) (id 0) xs'
    end.

(* ---------------------------------------- *)


(* Converted value declarations: *)

(* Translating `instance forall {a}, forall `{Control.DeepSeq.NFData a},
   Control.DeepSeq.NFData (Data.Sequence.Seq a)' failed: OOPS! Cannot find
   information for class Qualified "Control.DeepSeq" "NFData" unsupported *)

(* Translating `instance GHC.Base.MonadPlus Data.Sequence.Seq' failed: OOPS!
   Cannot find information for class Qualified "GHC.Base" "MonadPlus"
   unsupported *)

(* Translating `instance GHC.Base.Alternative Data.Sequence.Seq' failed: OOPS!
   Cannot find information for class Qualified "GHC.Base" "Alternative"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Sequence.Seq a)' failed: OOPS! Cannot find information for class Qualified
   "GHC.Show" "Show" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Sequence.Seq a)' failed: OOPS! Cannot find information for class Qualified
   "GHC.Read" "Read" unsupported *)

(* Skipping instance Monoid__Seq *)

(* Translating `instance forall {a}, Data.Semigroup.Semigroup (Data.Sequence.Seq
   a)' failed: OOPS! Cannot find information for class Qualified "Data.Semigroup"
   "Semigroup" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.Sequence.Seq a)' failed: OOPS! Cannot find information for class Qualified
   "Data.Data" "Data" unsupported *)


(* Translating `instance forall {a}, forall `{Control.DeepSeq.NFData a},
   Control.DeepSeq.NFData (Data.Sequence.FingerTree a)' failed: OOPS! Cannot find
   information for class Qualified "Control.DeepSeq" "NFData" unsupported *)

Local Definition Foldable__Digit_foldMap : forall {m} {a},
                                             forall `{GHC.Base.Monoid m}, (a -> m) -> Digit a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , One a => f a
        | f , Two a b => GHC.Base.mappend (f a) (f b)
        | f , Three a b c => GHC.Base.mappend (f a) (GHC.Base.mappend (f b) (f c))
        | f , Four a b c d => GHC.Base.mappend (f a) (GHC.Base.mappend (f b)
                                                                       (GHC.Base.mappend (f c) (f d)))
      end.

Local Definition Foldable__Digit_product : forall {a},
                                             forall `{GHC.Num.Num a}, Digit a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Digit_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Digit_sum : forall {a},
                                         forall `{GHC.Num.Num a}, Digit a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Digit_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Digit_fold : forall {m},
                                          forall `{GHC.Base.Monoid m}, Digit m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Digit_foldMap GHC.Base.id.

Local Definition Foldable__Digit_elem : forall {a},
                                          forall `{GHC.Base.Eq_ a}, a -> Digit a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Digit_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Local Definition Foldable__Digit_foldl : forall {b} {a},
                                           (b -> a -> b) -> b -> Digit a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | f , z , One a => f z a
        | f , z , Two a b => f (f z a) b
        | f , z , Three a b c => f (f (f z a) b) c
        | f , z , Four a b c d => f (f (f (f z a) b) c) d
      end.

Local Definition Foldable__Digit_foldr' : forall {a} {b},
                                            (a -> b -> b) -> b -> Digit a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Digit_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Digit_foldr : forall {a} {b},
                                           (a -> b -> b) -> b -> Digit a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | f , z , One a => f a z
        | f , z , Two a b => f a (f b z)
        | f , z , Three a b c => f a (f b (f c z))
        | f , z , Four a b c d => f a (f b (f c (f d z)))
      end.

Local Definition Foldable__Digit_null : forall {a}, Digit a -> bool :=
  fun {a} => Foldable__Digit_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Digit_toList : forall {a}, Digit a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Digit_foldr c n t
                                end)
      end.

Local Definition Foldable__Digit_foldl' : forall {b} {a},
                                            (b -> a -> b) -> b -> Digit a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Digit_foldr f' GHC.Base.id xs z0
      end.


Local Definition Foldable__Digit_length : forall {a}, Digit a -> GHC.Num.Int :=
  fun {a} d =>
    Z.of_nat (Foldable__Digit_foldl' (fun arg_64__ arg_65__ =>
                             match arg_64__ , arg_65__ with
                               | c , _ => c + (id 1)
                             end) (id 0) d).

Program Instance Foldable__Digit : Data.Foldable.Foldable Digit := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Digit_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Digit_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Digit_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Digit_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Digit_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Digit_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Digit_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Digit_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Digit_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Digit_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Digit_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Digit_toList |}.


Local Definition Traversable__Digit_traverse : forall {f} {a} {b},
                                                 forall `{GHC.Base.Applicative f},
                                                   (a -> f b) -> Digit a -> f (Digit b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , One a => One Data.Functor.<$> f a
        | f , Two a b => (Two Data.Functor.<$> f a) GHC.Base.<*> f b
        | f , Three a b c => ((Three Data.Functor.<$> f a) GHC.Base.<*> f b)
                             GHC.Base.<*> f c
        | f , Four a b c d => (((Four Data.Functor.<$> f a) GHC.Base.<*> f b)
                              GHC.Base.<*> f c) GHC.Base.<*> f d
      end.

Local Definition Traversable__Digit_sequenceA : forall {f} {a},
                                                  forall `{GHC.Base.Applicative f}, Digit (f a) -> f (Digit a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Digit_traverse GHC.Base.id.

Local Definition Traversable__Digit_sequence : forall {m} {a},
                                                 forall `{GHC.Base.Monad m}, Digit (m a) -> m (Digit a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Digit_sequenceA.

Local Definition Traversable__Digit_mapM : forall {m} {a} {b},
                                             forall `{GHC.Base.Monad m}, (a -> m b) -> Digit a -> m (Digit b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Digit_traverse.

Program Instance Traversable__Digit : Data.Traversable.Traversable Digit :=
  fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Digit_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Digit_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Digit_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Digit_traverse |}.

(* Translating `instance forall {a}, forall `{Control.DeepSeq.NFData a},
   Control.DeepSeq.NFData (Data.Sequence.Digit a)' failed: OOPS! Cannot find
   information for class Qualified "Control.DeepSeq" "NFData" unsupported *)


Local Definition Foldable__Node_foldMap : forall {m} {a},
                                            forall `{GHC.Base.Monoid m}, (a -> m) -> Node a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Node2 _ a b => GHC.Base.mappend (f a) (f b)
        | f , Node3 _ a b c => GHC.Base.mappend (f a) (GHC.Base.mappend (f b) (f c))
      end.

Local Definition Foldable__Node_product : forall {a},
                                            forall `{GHC.Num.Num a}, Node a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Node_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Node_sum : forall {a},
                                        forall `{GHC.Num.Num a}, Node a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Node_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Node_fold : forall {m},
                                         forall `{GHC.Base.Monoid m}, Node m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Node_foldMap GHC.Base.id.

Local Definition Foldable__Node_elem : forall {a},
                                         forall `{GHC.Base.Eq_ a}, a -> Node a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Node_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Local Definition Foldable__Node_foldl : forall {b} {a},
                                          (b -> a -> b) -> b -> Node a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | f , z , Node2 _ a b => f (f z a) b
        | f , z , Node3 _ a b c => f (f (f z a) b) c
      end.

Local Definition Foldable__Node_foldr' : forall {a} {b},
                                           (a -> b -> b) -> b -> Node a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Node_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Node_foldr : forall {a} {b},
                                          (a -> b -> b) -> b -> Node a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | f , z , Node2 _ a b => f a (f b z)
        | f , z , Node3 _ a b c => f a (f b (f c z))
      end.

Local Definition Foldable__Node_null : forall {a}, Node a -> bool :=
  fun {a} => Foldable__Node_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Node_toList : forall {a}, Node a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Node_foldr c n t
                                end)
      end.

Local Definition Foldable__Node_foldl' : forall {b} {a},
                                           (b -> a -> b) -> b -> Node a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Node_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Node_length : forall {a}, Node a -> GHC.Num.Int :=
  fun {a} n =>
    Z.of_nat (Foldable__Node_foldl' (fun arg_64__ arg_65__ =>
                            match arg_64__ , arg_65__ with
                              | c , _ => c + 1
                            end) 0 n).

Program Instance Foldable__Node : Data.Foldable.Foldable Node := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Node_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Node_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Node_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Node_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Node_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Node_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Node_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Node_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Node_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Node_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Node_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Node_toList |}.

Fixpoint Foldable__FingerTree_foldMap {m} {a} `{_ : GHC.Base.Monoid m} (f
                                        : a -> m) (t : FingerTree a) : m
           := match t with
                | Empty => GHC.Base.mempty
                | Single x => f x
                | Deep _ pr m sf => GHC.Base.mappend (Data.Foldable.foldMap f pr)
                                                     (GHC.Base.mappend (Foldable__FingerTree_foldMap
                                                                       (Data.Foldable.foldMap f) m)
                                                                       (Data.Foldable.foldMap f sf))
              end.

Fixpoint Foldable__FingerTree_foldl {b} {a} (f : b -> a -> b) (z : b) (t
                                      : FingerTree a) : b
           := match t with
                | Empty => z
                | Single x => f z x
                | Deep _ pr m sf => Data.Foldable.foldl f (Foldable__FingerTree_foldl
                                                        (Data.Foldable.foldl f) (Data.Foldable.foldl f z pr) m) sf
              end.

Fixpoint Foldable__FingerTree_foldr {a} {b} (f : a -> b -> b) (z : b) (t
                                      : FingerTree a) : b
           := match t with
                | Empty => z
                | Single x => f x z
                | Deep _ pr m sf => Data.Foldable.foldr f (Foldable__FingerTree_foldr
                                                        (GHC.Base.flip (Data.Foldable.foldr f)) (Data.Foldable.foldr f z
                                                                                                                     sf)
                                                        m) pr
              end.

Local Definition Foldable__FingerTree_null : forall {a}, FingerTree a -> bool :=
  fun {a} => Foldable__FingerTree_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__FingerTree_toList : forall {a},
                                                 FingerTree a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__FingerTree_foldr c n t
                                end)
      end.

Local Definition Foldable__FingerTree_foldl' : forall {b} {a},
                                                 (b -> a -> b) -> b -> FingerTree a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__FingerTree_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__FingerTree_length : forall {a},
                                                 FingerTree a -> GHC.Num.Int :=
  fun {a} t =>
    Z.of_nat (Foldable__FingerTree_foldl' (fun arg_64__ arg_65__ =>
                                  match arg_64__ , arg_65__ with
                                    | c , _ => c + 1
                                  end) 0 t).

Local Definition Foldable__FingerTree_foldr' : forall {a} {b},
                                                 (a -> b -> b) -> b -> FingerTree a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__FingerTree_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__FingerTree_product : forall {a},
                                                  forall `{GHC.Num.Num a}, FingerTree a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__FingerTree_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__FingerTree_sum : forall {a},
                                              forall `{GHC.Num.Num a}, FingerTree a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__FingerTree_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__FingerTree_fold : forall {m},
                                               forall `{GHC.Base.Monoid m}, FingerTree m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__FingerTree_foldMap GHC.Base.id.

Local Definition Foldable__FingerTree_elem : forall {a},
                                               forall `{GHC.Base.Eq_ a}, a -> FingerTree a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny
                                                                     (Foldable__FingerTree_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Local Definition Functor__Node_fmap : forall {a} {b},
                                        (a -> b) -> Node a -> Node b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Node2 v a b => Node2 v (f a) (f b)
        | f , Node3 v a b c => Node3 v (f a) (f b) (f c)
      end.

Local Definition Functor__Node_op_zlzd__ : forall {a} {b},
                                             a -> Node b -> Node a :=
  fun {a} {b} => fun x => Functor__Node_fmap (GHC.Base.const x).

Program Instance Functor__Node : GHC.Base.Functor Node := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Node_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Node_fmap |}.

Fixpoint Functor__FingerTree_fmap {a} {b} (f : a -> b) (t : FingerTree a)
           : FingerTree b
           := match t with
                | Empty => Empty
                | Single x => Single (f x)
                | Deep v pr m sf => Deep v (GHC.Base.fmap f pr) (Functor__FingerTree_fmap
                                         (GHC.Base.fmap f) m) (GHC.Base.fmap f sf)
              end.

Local Definition Functor__FingerTree_op_zlzd__ : forall {a} {b},
                                                   a -> FingerTree b -> FingerTree a :=
  fun {a} {b} => fun x => Functor__FingerTree_fmap (GHC.Base.const x).

Program Instance Functor__FingerTree : GHC.Base.Functor FingerTree := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__FingerTree_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__FingerTree_fmap |}.

Local Definition Traversable__Node_traverse : forall {f} {a} {b},
                                                forall `{GHC.Base.Applicative f}, (a -> f b) -> Node a -> f (Node b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Node2 v a b => (Node2 v Data.Functor.<$> f a) GHC.Base.<*> f b
        | f , Node3 v a b c => ((Node3 v Data.Functor.<$> f a) GHC.Base.<*> f b)
                               GHC.Base.<*> f c
      end.

Local Definition Traversable__Node_sequenceA : forall {f} {a},
                                                 forall `{GHC.Base.Applicative f}, Node (f a) -> f (Node a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Node_traverse GHC.Base.id.

Local Definition Traversable__Node_sequence : forall {m} {a},
                                                forall `{GHC.Base.Monad m}, Node (m a) -> m (Node a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Node_sequenceA.

Local Definition Traversable__Node_mapM : forall {m} {a} {b},
                                            forall `{GHC.Base.Monad m}, (a -> m b) -> Node a -> m (Node b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Node_traverse.

Program Instance Traversable__Node : Data.Traversable.Traversable Node := fun _
                                                                              k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Node_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Node_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Node_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Node_traverse |}.

Fixpoint Traversable__FingerTree_traverse {t : Type -> Type} {a} {b} `{_
                                            : GHC.Base.Applicative t} (f : a -> t b) (ft : FingerTree a) : t (FingerTree
                                                                                                             b)
           := match ft with
                | Empty => GHC.Base.pure Empty
                | Single x => GHC.Base.fmap Single (f x)
                | Deep v pr m sf => _GHC.Base.<*>_ (_GHC.Base.<*>_ (GHC.Base.fmap (Deep v)
                                                                                  (Data.Traversable.traverse f pr))
                                                                   (Traversable__FingerTree_traverse
                                                                   (Data.Traversable.traverse f) m))
                                                   (Data.Traversable.traverse f sf)
              end.

Local Definition Traversable__FingerTree_sequenceA : forall {f} {a},
                                                       forall `{GHC.Base.Applicative f},
                                                         FingerTree (f a) -> f (FingerTree a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__FingerTree_traverse GHC.Base.id.

Local Definition Traversable__FingerTree_sequence : forall {m} {a},
                                                      forall `{GHC.Base.Monad m},
                                                        FingerTree (m a) -> m (FingerTree a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__FingerTree_sequenceA.

Local Definition Traversable__FingerTree_mapM : forall {m} {a} {b},
                                                  forall `{GHC.Base.Monad m},
                                                    (a -> m b) -> FingerTree a -> m (FingerTree b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__FingerTree_traverse.

(* Translating `instance forall {a}, forall `{Control.DeepSeq.NFData a},
   Control.DeepSeq.NFData (Data.Sequence.Node a)' failed: OOPS! Cannot find
   information for class Qualified "Control.DeepSeq" "NFData" unsupported *)


Local Definition Functor__Elem_fmap : forall {a} {b},
                                        (a -> b) -> Elem a -> Elem b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Elem_op_zlzd__ : forall {a} {b},
                                             a -> Elem b -> Elem a :=
  fun {a} {b} => fun x => Functor__Elem_fmap (GHC.Base.const x).

Program Instance Functor__Elem : GHC.Base.Functor Elem := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Elem_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Elem_fmap |}.

Local Definition Foldable__Elem_foldMap : forall {m} {a},
                                            forall `{GHC.Base.Monoid m}, (a -> m) -> Elem a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | f , Mk_Elem x => f x end.

Local Definition Foldable__Elem_product : forall {a},
                                            forall `{GHC.Num.Num a}, Elem a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Elem_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Elem_sum : forall {a},
                                        forall `{GHC.Num.Num a}, Elem a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Elem_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Elem_fold : forall {m},
                                         forall `{GHC.Base.Monoid m}, Elem m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Elem_foldMap GHC.Base.id.

Local Definition Foldable__Elem_elem : forall {a},
                                         forall `{GHC.Base.Eq_ a}, a -> Elem a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Elem_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Local Definition Foldable__Elem_foldl : forall {b} {a},
                                          (b -> a -> b) -> b -> Elem a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | f , z , Mk_Elem x => f z x
      end.

Local Definition Foldable__Elem_foldr' : forall {a} {b},
                                           (a -> b -> b) -> b -> Elem a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Elem_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Elem_foldr : forall {a} {b},
                                          (a -> b -> b) -> b -> Elem a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | f , z , Mk_Elem x => f x z
      end.

Local Definition Foldable__Elem_null : forall {a}, Elem a -> bool :=
  fun {a} => Foldable__Elem_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Elem_toList : forall {a}, Elem a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Elem_foldr c n t
                                end)
      end.

Local Definition Foldable__Elem_foldl' : forall {b} {a},
                                           (b -> a -> b) -> b -> Elem a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Elem_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Elem_length : forall {a}, Elem a -> GHC.Num.Int :=
  fun {a} e =>
    Z.of_nat (Foldable__Elem_foldl' (fun arg_64__ arg_65__ =>
                            match arg_64__ , arg_65__ with
                              | c , _ => c + 1
                            end) 0 e).

Program Instance Foldable__Elem : Data.Foldable.Foldable Elem := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Elem_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Elem_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Elem_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Elem_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Elem_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Elem_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Elem_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Elem_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Elem_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Elem_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Elem_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Elem_toList |}.

Program Instance Foldable__FingerTree : Data.Foldable.Foldable FingerTree :=
  fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
        Foldable__FingerTree_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
        Foldable__FingerTree_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__FingerTree_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__FingerTree_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__FingerTree_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__FingerTree_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__FingerTree_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__FingerTree_length ;
      Data.Foldable.null__ := fun {a} => Foldable__FingerTree_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
        Foldable__FingerTree_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__FingerTree_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__FingerTree_toList |}.

Local Definition Foldable__Seq_foldMap : forall {m} {a},
                                           forall `{GHC.Base.Monoid m}, (a -> m) -> Seq a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_Seq xs => Data.Foldable.foldMap (Data.Foldable.foldMap f) xs
      end.

Local Definition Foldable__Seq_foldl : forall {b} {a},
                                         (b -> a -> b) -> b -> Seq a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | f , z , Mk_Seq xs => Data.Foldable.foldl (Data.Foldable.foldl f) z xs
      end.

Local Definition Foldable__Seq_foldr : forall {a} {b},
                                         (a -> b -> b) -> b -> Seq a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | f , z , Mk_Seq xs => Data.Foldable.foldr (GHC.Base.flip (Data.Foldable.foldr
                                                                  f)) z xs
      end.

Local Definition Foldable__Seq_toList : forall {a}, Seq a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__Seq_foldr c n t
                                end)
      end.

Local Definition Foldable__Seq_foldl' : forall {b} {a},
                                          (b -> a -> b) -> b -> Seq a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__Seq_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Seq_foldr' : forall {a} {b},
                                          (a -> b -> b) -> b -> Seq a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__Seq_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Seq_product : forall {a},
                                           forall `{GHC.Num.Num a}, Seq a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Seq_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__Seq_sum : forall {a},
                                       forall `{GHC.Num.Num a}, Seq a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Seq_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__Seq_fold : forall {m},
                                        forall `{GHC.Base.Monoid m}, Seq m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Seq_foldMap GHC.Base.id.

Local Definition Foldable__Seq_elem : forall {a},
                                        forall `{GHC.Base.Eq_ a}, a -> Seq a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Seq_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Local Definition Traversable__Elem_traverse : forall {f} {a} {b},
                                                forall `{GHC.Base.Applicative f}, (a -> f b) -> Elem a -> f (Elem b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_Elem x => Mk_Elem Data.Functor.<$> f x
      end.

Local Definition Traversable__Elem_sequenceA : forall {f} {a},
                                                 forall `{GHC.Base.Applicative f}, Elem (f a) -> f (Elem a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Elem_traverse GHC.Base.id.

Local Definition Traversable__Elem_sequence : forall {m} {a},
                                                forall `{GHC.Base.Monad m}, Elem (m a) -> m (Elem a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Elem_sequenceA.

Local Definition Traversable__Elem_mapM : forall {m} {a} {b},
                                            forall `{GHC.Base.Monad m}, (a -> m b) -> Elem a -> m (Elem b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Elem_traverse.

Program Instance Traversable__Elem : Data.Traversable.Traversable Elem := fun _
                                                                              k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Elem_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Elem_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Elem_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Elem_traverse |}.

Program Instance Traversable__FingerTree : Data.Traversable.Traversable
                                           FingerTree := fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__FingerTree_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__FingerTree_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__FingerTree_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__FingerTree_traverse |}.

Local Definition Traversable__Seq_traverse : forall {f} {a} {b},
                                               forall `{GHC.Base.Applicative f}, (a -> f b) -> Seq a -> f (Seq b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_Seq xs => Mk_Seq Data.Functor.<$> Data.Traversable.traverse
                           (Data.Traversable.traverse f) xs
      end.

Local Definition Traversable__Seq_sequenceA : forall {f} {a},
                                                forall `{GHC.Base.Applicative f}, Seq (f a) -> f (Seq a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Seq_traverse GHC.Base.id.

Local Definition Traversable__Seq_sequence : forall {m} {a},
                                               forall `{GHC.Base.Monad m}, Seq (m a) -> m (Seq a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Seq_sequenceA.

Local Definition Traversable__Seq_mapM : forall {m} {a} {b},
                                           forall `{GHC.Base.Monad m}, (a -> m b) -> Seq a -> m (Seq b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Seq_traverse.

(* Translating `instance forall {a}, forall `{Control.DeepSeq.NFData a},
   Control.DeepSeq.NFData (Data.Sequence.Elem a)' failed: OOPS! Cannot find
   information for class Qualified "Control.DeepSeq" "NFData" unsupported *)

Local Definition Monad__State_op_zgzgze__ {inst_s} : forall {a} {b},
                                                       (State inst_s) a -> (a -> (State inst_s) b) -> (State inst_s)
                                                       b :=
  fun {a} {b} =>
    fun m k =>
      Mk_State GHC.Base.$ (fun s =>
        match runState m s with
          | pair s' x => runState (k x) s'
        end).

Local Definition Applicative__State_pure {inst_s} : forall {a},
                                                      a -> (State inst_s) a :=
  fun {a} => fun x => Mk_State GHC.Base.$ (fun s => pair s x).

Definition Functor__State_fmap : forall {inst_s} {a} {b},
                                   (a -> b) -> State inst_s a -> State inst_s b :=
  fun {inst_s} {a} {b} f sa =>
    Monad__State_op_zgzgze__ sa (fun a => Applicative__State_pure (f a)).

Local Definition Functor__State_op_zlzd__ {inst_s} : forall {a} {b},
                                                       a -> (State inst_s) b -> (State inst_s) a :=
  fun {a} {b} => fun x => Functor__State_fmap (GHC.Base.const x).

Program Instance Functor__State {s} : GHC.Base.Functor (State s) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__State_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__State_fmap |}.

Definition Applicative__State_op_zlztzg__ : forall {s} {a} {b},
                                              State s (a -> b) -> State s a -> State s b :=
  fun {s} {a} {b} =>
    fun m1 m2 =>
      Monad__State_op_zgzgze__ m1 (fun x1 =>
                                 Monad__State_op_zgzgze__ m2 (fun x2 => Applicative__State_pure (x1 x2))).

Local Definition Applicative__State_op_ztzg__ {inst_s} : forall {a} {b},
                                                           (State inst_s) a -> (State inst_s) b -> (State inst_s) b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__State_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Program Instance Applicative__State {s} : GHC.Base.Applicative (State s) :=
  fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__State_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__State_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__State_pure |}.

Local Definition Monad__State_op_zgzg__ {inst_s} : forall {a} {b},
                                                     (State inst_s) a -> (State inst_s) b -> (State inst_s) b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__State_return_ {inst_s} : forall {a},
                                                   a -> (State inst_s) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__State {s} : GHC.Base.Monad (State s) := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} => Monad__State_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__State_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => Monad__State_return_ |}.

Local Definition Foldable__ViewR_null : forall {a}, ViewR a -> bool :=
  fun {a} =>
    fun arg_0__ => match arg_0__ with | EmptyR => true | op_ZCzg__ _ _ => false end.

(* Translating `instance forall {a}, GHC.Exts.IsList (Data.Sequence.Seq a)'
   failed: OOPS! Cannot find information for class Qualified "GHC.Exts" "IsList"
   unsupported *)

(* Translating `instance Data.String.IsString (Data.Sequence.Seq GHC.Char.Char)'
   failed: OOPS! Cannot find information for class Qualified "Data.String"
   "IsString" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.Sequence.ViewR a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Sequence.ViewR a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Sequence.ViewR a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.Sequence.ViewL a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Sequence.ViewL a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Sequence.ViewL a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

Definition adjustDigit {a} `{Sized a}
    : (nat -> a -> a) -> nat -> Digit a -> Digit a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , i , One a => One (f i a)
      | f , i , Two a b => let sa := size a in
                           if Nat.ltb i sa : bool
                           then Two (f i a) b
                           else Two a (f (i - sa) b)
      | f , i , Three a b c => let sa := size a in
                               let sab := sa + size b in
                               if Nat.ltb i sa : bool
                               then Three (f i a) b c
                               else if Nat.ltb i sab : bool
                                    then Three a (f (i - sa) b) c
                                    else Three a b (f (i - sab) c)
      | f , i , Four a b c d => let sa := size a in
                                let sab := sa + size b in
                                let sabc := sab + size c in
                                if Nat.ltb i sa : bool
                                then Four (f i a) b c d
                                else if Nat.ltb i sab : bool
                                     then Four a (f (i - sa) b) c d
                                     else if Nat.ltb i sabc : bool
                                          then Four a b (f (i - sab) c) d
                                          else Four a b c (f (i - sabc) d)
    end.

Definition adjustNode {a} `{Sized a}
    : (nat -> a -> a) -> nat -> Node a -> Node a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , i , Node2 s a b => let sa := size a in
                               if Nat.ltb i sa : bool
                               then Node2 s (f i a) b
                               else Node2 s a (f (i - sa) b)
      | f , i , Node3 s a b c => let sa := size a in
                                 let sab := sa + size b in
                                 if Nat.ltb i sa : bool
                                 then Node3 s (f i a) b c
                                 else if Nat.ltb i sab : bool
                                      then Node3 s a (f (i - sa) b) c
                                      else Node3 s a b (f (i - sab) c)
    end.

Fixpoint adjustTree {a} `{_ : Sized a} (f : nat -> a -> a) (i
                      : nat) (ft : FingerTree a) : FingerTree a
           := match ft with
                | Empty => error
                | Single x => Single (f i x)
                | Deep s pr m sf => let spr := size pr in
                                    let spm := spr + (size m) in
                                    if Nat.ltb i spr then Deep s (adjustDigit f i pr) m sf else if Nat.ltb
                                       i spm then Deep s pr (adjustTree (adjustNode f) (i - spr) m) sf else
                                       Deep s pr m (adjustDigit f (i - spm) sf)
              end.

Definition adjust {a} : (a -> a) -> nat -> Seq a -> Seq a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , i , Mk_Seq xs => if andb (Nat.leb 0 i) (Nat.ltb i (size xs)) : bool
                             then Mk_Seq (adjustTree (GHC.Base.const (GHC.Base.fmap f)) i xs)
                             else Mk_Seq xs
    end.

Definition update {a} : nat -> a -> Seq a -> Seq a :=
  fun i x => adjust (GHC.Base.const x) i.

Definition deep {a} `{Sized a} : Digit a -> FingerTree (Node a) -> Digit
                                 a -> FingerTree a :=
  fun pr m sf => Deep ((size pr + size m) + size sf) pr m sf.

Definition digitToTree {a} `{Sized a} : Digit a -> FingerTree a :=
  fun arg_0__ =>
    match arg_0__ with
      | One a => Single a
      | Two a b => deep (One a) Empty (One b)
      | Three a b c => deep (Two a b) Empty (One c)
      | Four a b c d => deep (Two a b) Empty (Two c d)
    end.

Definition digit12ToDigit {a} : Digit12 a -> Digit a :=
  fun arg_0__ => match arg_0__ with | One12 a => One a | Two12 a b => Two a b end.

Definition digitToTree' {a} : nat -> Digit a -> FingerTree a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | n , Four a b c d => Deep n (Two a b) Empty (Two c d)
      | n , Three a b c => Deep n (Two a b) Empty (One c)
      | n , Two a b => Deep n (One a) Empty (One b)
      | n , One a => GHC.Prim.seq n (Single a)
    end.

Definition empty {a} : Seq a :=
  Mk_Seq Empty.

Definition execState {s} {a} : State s a -> s -> a :=
  fun m x => Data.Tuple.snd (runState m x).

Definition fmapSeq {a} {b} : (a -> b) -> Seq a -> Seq b :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , Mk_Seq xs => Mk_Seq (Functor__FingerTree_fmap (GHC.Base.fmap f) xs)
    end.

Local Definition Functor__Seq_fmap : forall {a} {b},
                                       (a -> b) -> Seq a -> Seq b :=
  fun {a} {b} => fmapSeq.

Definition getSingleton {a} : Seq a -> a :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Seq (Single (Mk_Elem a)) => a
      | Mk_Seq Empty => error (GHC.Base.hs_string__ "getSingleton: Empty")
      | _ => error (GHC.Base.hs_string__ "getSingleton: Not a singleton.")
    end.

Definition initsDigit {a} : Digit a -> Digit (Digit a) :=
  fun arg_0__ =>
    match arg_0__ with
      | One a => One (One a)
      | Two a b => Two (One a) (Two a b)
      | Three a b c => Three (One a) (Two a b) (Three a b c)
      | Four a b c d => Four (One a) (Two a b) (Three a b c) (Four a b c d)
    end.

Definition initsNode {a} : Node a -> Node (Digit a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Node2 s a b => Node2 s (One a) (Two a b)
      | Node3 s a b c => Node3 s (One a) (Two a b) (Three a b c)
    end.

Definition length {a} : Seq a -> nat :=
  fun arg_0__ => match arg_0__ with | Mk_Seq xs => size xs end.

Local Definition Foldable__Seq_length : forall {a}, Seq a -> GHC.Num.Int :=
  fun {a} s => Z.of_nat (length s).

Definition listToMaybe' {a} : list a -> option a :=
  Data.Foldable.foldr (fun arg_0__ arg_1__ =>
                        match arg_0__ , arg_1__ with
                          | x , _ => Some x
                        end) None.

Definition lookupDigit {a} `{Sized a} : nat -> Digit a -> Place a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | i , One a => Mk_Place i a
      | i , Two a b => let sa := size a in
                       if Nat.ltb i sa : bool
                       then Mk_Place i a
                       else Mk_Place (i - sa) b
      | i , Three a b c => let sa := size a in
                           let sab := sa + size b in
                           if Nat.ltb i sa : bool
                           then Mk_Place i a
                           else if Nat.ltb i sab : bool
                                then Mk_Place (i - sa) b
                                else Mk_Place (i - sab) c
      | i , Four a b c d => let sa := size a in
                            let sab := sa + size b in
                            let sabc := sab + size c in
                            if Nat.ltb i sa : bool
                            then Mk_Place i a
                            else if Nat.ltb i sab : bool
                                 then Mk_Place (i - sa) b
                                 else if Nat.ltb i sabc : bool
                                      then Mk_Place (i - sab) c
                                      else Mk_Place (i - sabc) d
    end.

Definition lookupNode {a} `{Sized a} : nat -> Node a -> Place a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | i , Node2 _ a b => let sa := size a in
                           if Nat.ltb i sa : bool
                           then Mk_Place i a
                           else Mk_Place (i - sa) b
      | i , Node3 _ a b c => let sa := size a in
                             let sab := sa + size b in
                             if Nat.ltb i sa : bool
                             then Mk_Place i a
                             else if Nat.ltb i sab : bool
                                  then Mk_Place (i - sa) b
                                  else Mk_Place (i - sab) c
    end.

Fixpoint lookupTree {a} `{_ : Sized a} (i : nat) (ft : FingerTree a)
           : Place a
           := match ft with
                | Empty => error
                | Single x => Mk_Place i x
                | Deep totalSize pr m sf => let spm := totalSize - (size sf) in
                                            let spr := size pr in
                                            if Nat.ltb i spr then lookupDigit i pr else if Nat.ltb i spm then
                                               (match lookupTree (i - spr) m with
                                                 | Mk_Place i' xs => lookupNode i' xs
                                               end) else lookupDigit (i - spm) sf
              end.

Definition index {a} : Seq a -> nat -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_Seq xs , i => if andb (Nat.leb 0 i) (Nat.leb i
                                 (size xs)) : bool
                         then match lookupTree i xs with
                                | Mk_Place _ (Mk_Elem x) => x
                              end
                         else error (GHC.Base.hs_string__ "index out of bounds")
    end.

Definition mapMulNode {a} {b} : nat -> (a -> b) -> Node a -> Node b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | mul , f , Node2 s a b => Node2 (mul * s) (f a) (f b)
      | mul , f , Node3 s a b c => Node3 (mul * s) (f a) (f b) (f c)
    end.

Fixpoint mapMulFT {a} {b} (mul : nat) (f : a -> b) (ft : FingerTree a)
           : FingerTree b
           := match ft with
                | Empty => Empty
                | Single a => Single (f a)
                | Deep s pr m sf => Deep (mul * s) (GHC.Base.fmap f pr) (mapMulFT mul (mapMulNode mul f) m)
                                         (GHC.Base.fmap f sf)
              end.

Definition ap3FT {a} {b} : (a -> b) -> FingerTree (Elem (a -> b)) -> (a -> b) -> (a * a * a)%type -> FingerTree (Elem b) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | firstf , fs , lastf , pair (pair x y) z => Deep ((size fs *
                                                         3) +  6) (Three
                                                                                                                (Mk_Elem
                                                                                                                GHC.Base.$
                                                                                                                firstf
                                                                                                                x)
                                                                                                                (Mk_Elem
                                                                                                                GHC.Base.$
                                                                                                                firstf
                                                                                                                y)
                                                                                                                (Mk_Elem
                                                                                                                GHC.Base.$
                                                                                                                firstf
                                                                                                                z))
                                                   (mapMulFT ( 3) (fun arg_4__ =>
                                                                                       match arg_4__ with
                                                                                         | Mk_Elem f => Node3
                                                                                                        (
                                                                                                        3) (Mk_Elem (f
                                                                                                                    x))
                                                                                                        (Mk_Elem (f y))
                                                                                                        (Mk_Elem (f z))
                                                                                       end) fs) (Three (Mk_Elem
                                                                                                       GHC.Base.$ lastf
                                                                                                       x) (Mk_Elem
                                                                                                          GHC.Base.$
                                                                                                          lastf y)
                                                                                                (Mk_Elem GHC.Base.$
                                                                                                lastf z))
    end.

Definition ap2FT {a} {b} : (a -> b) -> FingerTree (Elem
                                                  (a -> b)) -> (a -> b) -> (a * a)%type -> FingerTree (Elem b) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | firstf , fs , lastf , pair x y => Deep ((size fs * id
                                               2) + id 4) (Two (Mk_Elem GHC.Base.$ firstf x)
                                                                                   (Mk_Elem GHC.Base.$ firstf y))
                                          (mapMulFT (id 2) (fun arg_4__ =>
                                                                              match arg_4__ with
                                                                                | Mk_Elem f => Node2
                                                                                               (id 2)
                                                                                               (Mk_Elem (f x)) (Mk_Elem
                                                                                                               (f y))
                                                                              end) fs) (Two (Mk_Elem GHC.Base.$ lastf x)
                                                                                       (Mk_Elem GHC.Base.$ lastf y))
    end.


Definition mergePQ {a} : (a -> a -> comparison) -> PQueue a -> PQueue
                         a -> PQueue a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | cmp , (Mk_PQueue x1 ts1 as q1) , (Mk_PQueue x2 ts2 as q2) => if cmp x1 x2
                                                                        GHC.Base.== Gt : bool
                                                                     then Mk_PQueue x2 (q1 :& ts2)
                                                                     else Mk_PQueue x1 (q2 :& ts1)
    end.

Definition node2 {a} `{Sized a} : a -> a -> Node a :=
  fun a b => Node2 (size a + size b) a b.

Definition node3 {a} `{Sized a} : a -> a -> a -> Node a :=
  fun a b c => Node3 ((size a + size b) + size c) a b c.

Definition squashL {a} : Digit23 a -> Digit12 (Node a) -> Digit23 (Node a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | m , One12 n => node2 m n
      | m , Two12 n1 n2 => node3 m n1 n2
    end.

Definition squashR {a} : Digit12 (Node a) -> Digit23 a -> Digit23 (Node a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | One12 n , m => node2 n m
      | Two12 n1 n2 , m => node3 n1 n2 m
    end.

Fixpoint consTree {a} `{_ : Sized a} (arg_0__ : a) (ft : FingerTree a)
           : FingerTree a
           := match arg_0__ , ft with
                | a , Empty => Single a
                | a , Single b => deep (One a) Empty (One b)
                | a , Deep s (Four b c d e) m sf => GHC.Prim.seq m (Deep ((size a) + s) (Two a b) (consTree (node3 c d
                                                                                                                    e)
                                                                                                             m) sf)
                | a , Deep s (Three b c d) m sf => Deep ((size a) + s) (Four a b c d)
                                                        m sf
                | a , Deep s (Two b c) m sf => Deep ((size a) + s) (Three a b c) m sf
                | a , Deep s (One b) m sf => Deep ((size a) + s) (Two a b) m sf
              end.

Definition op_zlzb__ {a} : a -> Seq a -> Seq a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | x , Mk_Seq xs => Mk_Seq (consTree (Mk_Elem x) xs)
    end.

Notation "'_<|_'" := (op_zlzb__).

Infix "<|" := (_<|_) (at level 99).


Definition nodeToDigit {a} : Node a -> Digit a :=
  fun arg_0__ =>
    match arg_0__ with
      | Node2 _ a b => Two a b
      | Node3 _ a b c => Three a b c
    end.

Fixpoint viewLTree {a} `{Sized a} ( arg_0__ : FingerTree a) : Maybe2 a (FingerTree a) :=
  let pullL {a} : nat -> FingerTree (Node a) -> Digit
                       a -> FingerTree a :=
  fun s m sf =>
    match viewLTree m with
      | Nothing2 => digitToTree' s sf
      | Just2 pr m' => Deep s (nodeToDigit pr) m' sf
    end in

    match arg_0__ with
      | Empty => Nothing2
      | Single a => Just2 a Empty
      | Deep s (One a) m sf => Just2 a (pullL (s - size a) m sf)
      | Deep s (Two a b) m sf => Just2 a (Deep (s - size a) (One b) m sf)
      | Deep s (Three a b c) m sf => Just2 a (Deep (s - size a) (Two b c) m
                                             sf)
      | Deep s (Four a b c d) m sf => Just2 a (Deep (s - size a) (Three b c d)
                                              m sf)
    end.

Fixpoint viewRTree {a} `{Sized a} (arg_0__ : FingerTree a) : Maybe2 (FingerTree a) a :=
  let pullR {a} : nat -> Digit a -> FingerTree (Node
                                                            a) -> FingerTree a :=
  fun s pr m =>
    match viewRTree m with
      | Nothing2 => digitToTree' s pr
      | Just2 m' sf => Deep s pr m' (nodeToDigit sf)
    end in

    match arg_0__ with
      | Empty => Nothing2
      | Single z => Just2 Empty z
      | Deep s pr m (One z) => Just2 (pullR (s - size z) pr m) z
      | Deep s pr m (Two y z) => Just2 (Deep (s - size z) pr m (One y)) z
      | Deep s pr m (Three x y z) => Just2 (Deep (s - size z) pr m (Two x y))
                                     z
      | Deep s pr m (Four w x y z) => Just2 (Deep (s - size z) pr m (Three w x
                                                                            y)) z
    end.



Fixpoint initsTree {a} {b} `{_:Sized a} (f : (FingerTree a) -> b) (arg_1__ : FingerTree a) : FingerTree b :=
      match arg_1__ with
             | Empty => Empty
             | Single x => Single (f (Single x))
             | Deep n pr m sf =>
                let f' := fun ms =>
                            (match viewRTree ms with
                            | Just2 m' node => GHC.Base.fmap (fun sf' => f (deep pr m' sf')) (initsNode node)
                            | Nothing2 => error
                            end) in
                Deep n (GHC.Base.fmap (f GHC.Base.∘ digitToTree) (initsDigit pr)) (initsTree f' m)
                     (GHC.Base.fmap (f GHC.Base.∘ deep pr m) (initsDigit sf))
           end.

Definition inits {a} : Seq a -> Seq (Seq a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Seq xs => empty <| Mk_Seq (initsTree (Mk_Elem GHC.Base.∘ Mk_Seq) xs)
    end.


Definition pullL {a} : nat -> FingerTree (Node a) -> Digit
                       a -> FingerTree a :=
  fun s m sf =>
    match viewLTree m with
      | Nothing2 => digitToTree' s sf
      | Just2 pr m' => Deep s (nodeToDigit pr) m' sf
    end.

Definition deepL {a} `{Sized a} : option (Digit a) -> FingerTree (Node
                                                                 a) -> Digit a -> FingerTree a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | None , m , sf => pullL (size m + size sf) m sf
      | Some pr , m , sf => deep pr m sf
    end.

Definition pullR {a} : nat -> Digit a -> FingerTree (Node
                                                            a) -> FingerTree a :=
  fun s pr m =>
    match viewRTree m with
      | Nothing2 => digitToTree' s pr
      | Just2 m' sf => Deep s pr m' (nodeToDigit sf)
    end.

Definition deepR {a} `{Sized a} : Digit a -> FingerTree (Node a) -> option
                                  (Digit a) -> FingerTree a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | pr , m , None => pullR (size m + size pr) pr m
      | pr , m , Some sf => deep pr m sf
    end.

Definition null {a} : Seq a -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Seq Empty => true | _ => false end.

Local Definition Foldable__Seq_null : forall {a}, Seq a -> bool :=
  fun {a} => null.

Program Fixpoint applicativeTree {f} {a} `{GHC.Base.Applicative f}
        (n : nat) (mSize : nat) (m : f a) { measure n } : f (FingerTree a) :=
        let emptyTree : f (FingerTree (Node a)) := GHC.Base.pure Empty in
        let mSize' := Nat.mul 3 mSize in
        let n3     := GHC.Base.liftA3 (Node3 mSize') m m m in
        let deepA  : f (Digit a) -> f (FingerTree (Node a)) -> f (Digit a)
                     -> f (FingerTree a)
                   := GHC.Base.liftA3 (@Deep a (Nat.mul n mSize)) in
        let three  : f (Digit a) := GHC.Base.liftA3 Three m m m in
        let two    : f (Digit a) := GHC.Base.liftA2 Two m m in
        let one    : f (Digit a) := GHC.Base.fmap One m in
        let j_24__ : f (FingerTree a) :=
            let q := (Nat.div n 3)    in
            let n := (Nat.modulo n 3) in
            let j_18__ :=
               deepA three (applicativeTree (Nat.sub q 1) mSize' n3) two in
            let j_20__ :=
               if Nat.eqb n 1 : bool
               then deepA two (applicativeTree (Nat.sub q 1) mSize' n3) two
               else j_18__ in
            if Nat.eqb n 0 : bool
            then deepA three (applicativeTree (Nat.sub q 2) mSize' n3) three
            else j_20__
            in
        let j_26__ :=
            if Nat.eqb n 6 : bool
            then deepA three emptyTree three
            else j_24__
        in
        let j_28__ :=
            if Nat.eqb n 5 : bool
            then deepA three emptyTree two
            else j_26__
        in
        let j_30__ :=
            if Nat.eqb n 4 : bool
            then deepA two emptyTree two
            else j_28__
        in
        let j_32__ :=
            if Nat.eqb n 3 : bool
            then deepA two emptyTree one
            else j_30__
        in
        let j_34__ :=
            if Nat.eqb n 2 : bool
            then deepA one emptyTree one
            else j_32__
        in
        let j_36__ :=
            if Nat.eqb n  1 : bool
            then GHC.Base.fmap Single m
            else j_34__
        in
        if Nat.eqb n 0 : bool
        then GHC.Base.pure Empty
        else j_36__
.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Definition replicateA {f} {a} `{GHC.Base.Applicative f} : nat -> f
                                                          a -> f (Seq a) :=
  fun n x =>
    if negb (Nat.ltb n 0) : bool
    then Mk_Seq Data.Functor.<$> applicativeTree n (id 1) (Mk_Elem
                                                                           Data.Functor.<$> x)
    else error (GHC.Base.hs_string__
               "replicateA takes a nonnegative integer argument").

Definition replicateM {m} {a} `{GHC.Base.Monad m} : nat -> m a -> m (Seq
                                                                            a) :=
  fun n x =>
    if negb (Nat.ltb n 0) : bool
    then unwrapMonad (replicateA n (Control.Applicative.WrapMonad x))
    else error (GHC.Base.hs_string__
               "replicateM takes a nonnegative integer argument").

Definition replicate {a} : nat -> a -> Seq a :=
  fun n x =>
    if negb (Nat.ltb n 0) : bool
    then runIdentity (replicateA n (Data.Functor.Identity.Mk_Identity x))
    else error (GHC.Base.hs_string__
               "replicate takes a nonnegative integer argument").

Local Definition Functor__Seq_op_zlzd__ : forall {a} {b}, a -> Seq b -> Seq a :=
  fun {a} {b} => fun x s => replicate (length s) x.

Program Instance Functor__Seq : GHC.Base.Functor Seq := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Seq_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Seq_fmap |}.

Program Instance Foldable__Seq : Data.Foldable.Foldable Seq := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Seq_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Seq_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Seq_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Seq_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Seq_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Seq_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Seq_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Seq_length ;
      Data.Foldable.null__ := fun {a} => Foldable__Seq_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Seq_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Seq_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Seq_toList |}.

Local Definition Ord__Seq_compare {inst_a} `{GHC.Base.Ord inst_a} : (Seq
                                                                    inst_a) -> (Seq inst_a) -> comparison :=
  fun xs ys =>
    GHC.Base.compare (Data.Foldable.toList xs) (Data.Foldable.toList ys).

Definition foldrWithIndex {a} {b} : (nat -> a -> b -> b) -> b -> Seq
                                    a -> b :=
  fun f z xs =>
    Data.Foldable.foldr (fun x g i =>
                          GHC.Prim.seq i (f i x (g (i + id 1)))) (GHC.Base.const
                                                                                          z) xs (id 0).

Definition foldlWithIndex {b} {a} : (b -> nat -> a -> b) -> b -> Seq
                                    a -> b :=
  fun f z xs =>
    Data.Foldable.foldl (fun g x i =>
                          GHC.Prim.seq i (f (g (i - id 1)) i x)) (GHC.Base.const
                                                                                          z) xs (length xs -
                                                                                                id 1).

Definition findIndicesR {a} : (a -> bool) -> Seq a -> list nat :=
  fun p xs =>
    GHC.Base.build (fun c n =>
                     let g := fun z i x => if p x : bool then c i z else z in foldlWithIndex g n xs).

Definition findIndexR {a} : (a -> bool) -> Seq a -> option nat :=
  fun p => listToMaybe' GHC.Base.∘ findIndicesR p.

Definition elemIndexR {a} `{GHC.Base.Eq_ a} : a -> Seq a -> option
                                              nat :=
  fun x => findIndexR (fun arg_0__ => x GHC.Base.== arg_0__).

Definition elemIndicesR {a} `{GHC.Base.Eq_ a} : a -> Seq a -> list
                                                nat :=
  fun x => findIndicesR (fun arg_0__ => x GHC.Base.== arg_0__).

Local Definition Eq___Seq_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : (Seq
                                                                      inst_a) -> (Seq inst_a) -> bool :=
  fun xs ys =>
    andb (Nat.eqb (length xs) (length ys)) (Data.Foldable.toList xs GHC.Base.==
         Data.Foldable.toList ys).

Local Definition Eq___Seq_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : (Seq
                                                                      inst_a) -> (Seq inst_a) -> bool :=
  fun x y => negb (Eq___Seq_op_zeze__ x y).

Program Instance Eq___Seq {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Seq a) := fun _
                                                                              k =>
    k {|GHC.Base.op_zeze____ := Eq___Seq_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Seq_op_zsze__ |}.

Definition findIndicesL {a} : (a -> bool) -> Seq a -> list nat :=
  fun p xs =>
    GHC.Base.build (fun c n =>
                     let g := fun i x z => if p x : bool then c i z else z in foldrWithIndex g n xs).

Definition findIndexL {a} : (a -> bool) -> Seq a -> option nat :=
  fun p => listToMaybe' GHC.Base.∘ findIndicesL p.

Definition elemIndexL {a} `{GHC.Base.Eq_ a} : a -> Seq a -> option
                                              nat :=
  fun x => findIndexL (fun arg_0__ => x GHC.Base.== arg_0__).

Definition elemIndicesL {a} `{GHC.Base.Eq_ a} : a -> Seq a -> list
                                                nat :=
  fun x => findIndicesL (fun arg_0__ => x GHC.Base.== arg_0__).

Local Definition Ord__Seq_op_zg__ {inst_a} `{GHC.Base.Ord inst_a} : (Seq
                                                                    inst_a) -> (Seq inst_a) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Seq_compare x y) Gt.

Local Definition Ord__Seq_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a} : (Seq
                                                                      inst_a) -> (Seq inst_a) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Seq_compare x y) Lt.

Local Definition Ord__Seq_op_zl__ {inst_a} `{GHC.Base.Ord inst_a} : (Seq
                                                                    inst_a) -> (Seq inst_a) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Seq_compare x y) Lt.

Local Definition Ord__Seq_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a} : (Seq
                                                                      inst_a) -> (Seq inst_a) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Seq_compare x y) Gt.

Local Definition Ord__Seq_max {inst_a} `{GHC.Base.Ord inst_a} : (Seq
                                                                inst_a) -> (Seq inst_a) -> (Seq inst_a) :=
  fun x y => if Ord__Seq_op_zlze__ x y : bool then y else x.

Local Definition Ord__Seq_min {inst_a} `{GHC.Base.Ord inst_a} : (Seq
                                                                inst_a) -> (Seq inst_a) -> (Seq inst_a) :=
  fun x y => if Ord__Seq_op_zlze__ x y : bool then x else y.

Program Instance Ord__Seq {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Seq a) := fun _
                                                                              k =>
    k {|GHC.Base.op_zl____ := Ord__Seq_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Seq_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Seq_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Seq_op_zgze__ ;
      GHC.Base.compare__ := Ord__Seq_compare ;
      GHC.Base.max__ := Ord__Seq_max ;
      GHC.Base.min__ := Ord__Seq_min |}.

Local Definition Eq___ViewR_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : ViewR
                                                                        inst_a -> ViewR inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | EmptyR , EmptyR => true
      | op_ZCzg__ a1 a2 , op_ZCzg__ b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2
                                                   GHC.Base.== b2)))
      | _ , _ => false
    end.

Local Definition Eq___ViewL_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : ViewL
                                                                        inst_a -> ViewL inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | EmptyL , EmptyL => true
      | op_ZCzl__ a1 a2 , op_ZCzl__ b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2
                                                   GHC.Base.== b2)))
      | _ , _ => false
    end.

Local Definition Eq___ViewL_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : ViewL
                                                                        inst_a -> ViewL inst_a -> bool :=
  fun a b => negb (Eq___ViewL_op_zeze__ a b).

Program Instance Eq___ViewL {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (ViewL a) :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___ViewL_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___ViewL_op_zsze__ |}.

Local Definition Eq___ViewR_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : ViewR
                                                                        inst_a -> ViewR inst_a -> bool :=
  fun a b => negb (Eq___ViewR_op_zeze__ a b).

Program Instance Eq___ViewR {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (ViewR a) :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___ViewR_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___ViewR_op_zsze__ |}.

Local Definition Ord__ViewR_compare {inst_a} `{GHC.Base.Ord inst_a} : ViewR
                                                                      inst_a -> ViewR inst_a -> comparison :=
  fun a b =>
    match a with
      | EmptyR => match b with
                    | EmptyR => Eq
                    | _ => Lt
                  end
      | op_ZCzg__ a1 a2 => match b with
                             | op_ZCzg__ b1 b2 => match (GHC.Base.compare a1 b1) with
                                                    | Lt => Lt
                                                    | Eq => (GHC.Base.compare a2 b2)
                                                    | Gt => Gt
                                                  end
                             | _ => Gt
                           end
    end.

Local Definition Ord__ViewL_compare {inst_a} `{GHC.Base.Ord inst_a} : ViewL
                                                                      inst_a -> ViewL inst_a -> comparison :=
  fun a b =>
    match a with
      | EmptyL => match b with
                    | EmptyL => Eq
                    | _ => Lt
                  end
      | op_ZCzl__ a1 a2 => match b with
                             | op_ZCzl__ b1 b2 => match (GHC.Base.compare a1 b1) with
                                                    | Lt => Lt
                                                    | Eq => (GHC.Base.compare a2 b2)
                                                    | Gt => Gt
                                                  end
                             | _ => Gt
                           end
    end.

Local Definition Ord__ViewR_op_zlze__ {inst_a} `{_ : GHC.Base.Ord inst_a}
    : ViewR inst_a -> ViewR inst_a -> bool :=
  fun a b =>
    match a with
      | EmptyR => match b with
                    | EmptyR => true
                    | _ => true
                  end
      | op_ZCzg__ a1 a2 => match b with
                             | op_ZCzg__ b1 b2 => match GHC.Base.compare a1 b1 with
                                                    | Lt => true
                                                    | Eq => _GHC.Base.<=_ a2 b2
                                                    | Gt => false
                                                  end
                             | _ => false
                           end
    end.

Definition Ord__ViewR_op_zl__ {inst_a} `{_ : GHC.Base.Ord inst_a} : ViewR
                                                                    inst_a -> ViewR inst_a -> bool :=
  fun a b =>
    match a with
      | EmptyR => match b with
                    | EmptyR => false
                    | _ => true
                  end
      | op_ZCzg__ a1 a2 => match b with
                             | op_ZCzg__ b1 b2 => match GHC.Base.compare a1 b1 with
                                                    | Lt => true
                                                    | Eq => _GHC.Base.<_ a2 b2
                                                    | Gt => false
                                                  end
                             | _ => false
                           end
    end.

Local Definition Ord__ViewR_op_zg__ {inst_a} `{_ : GHC.Base.Ord inst_a} : ViewR
                                                                          inst_a -> ViewR inst_a -> bool :=
  fun a b =>
    match a with
      | EmptyR => match b with
                    | EmptyR => false
                    | _ => false
                  end
      | op_ZCzg__ a1 a2 => match b with
                             | op_ZCzg__ b1 b2 => match GHC.Base.compare a1 b1 with
                                                    | Lt => false
                                                    | Eq => _GHC.Base.>_ a2 b2
                                                    | Gt => true
                                                  end
                             | _ => true
                           end
    end.

Local Definition Ord__ViewR_op_zgze__ {inst_a} `{_ : GHC.Base.Ord inst_a}
    : ViewR inst_a -> ViewR inst_a -> bool :=
  fun a b =>
    match a with
      | EmptyR => match b with
                    | EmptyR => true
                    | _ => false
                  end
      | op_ZCzg__ a1 a2 => match b with
                             | op_ZCzg__ b1 b2 => match GHC.Base.compare a1 b1 with
                                                    | Lt => false
                                                    | Eq => _GHC.Base.>=_ a2 b2
                                                    | Gt => true
                                                  end
                             | _ => true
                           end
    end.

Definition Ord__ViewL_op_zlze__ {inst_a} `{_ : GHC.Base.Ord inst_a} : ViewL
                                                                      inst_a -> ViewL inst_a -> bool :=
  fun a b =>
    match a with
      | EmptyL => match b with
                    | EmptyL => true
                    | _ => true
                  end
      | op_ZCzl__ a1 a2 => match b with
                             | op_ZCzl__ b1 b2 => match GHC.Base.compare a1 b1 with
                                                    | Lt => true
                                                    | Eq => _GHC.Base.<=_ a2 b2
                                                    | Gt => false
                                                  end
                             | _ => false
                           end
    end.

Definition Ord__ViewL_op_zl__ {inst_a} `{_ : GHC.Base.Ord inst_a} : ViewL
                                                                    inst_a -> ViewL inst_a -> bool :=
  fun a b =>
    match a with
      | EmptyL => match b with
                    | EmptyL => false
                    | _ => true
                  end
      | op_ZCzl__ a1 a2 => match b with
                             | op_ZCzl__ b1 b2 => match GHC.Base.compare a1 b1 with
                                                    | Lt => true
                                                    | Eq => _GHC.Base.<_ a2 b2
                                                    | Gt => false
                                                  end
                             | _ => false
                           end
    end.

Definition Ord__ViewL_op_zg__ {inst_a} `{_ : GHC.Base.Ord inst_a} : ViewL
                                                                    inst_a -> ViewL inst_a -> bool :=
  fun a b =>
    match a with
      | EmptyL => match b with
                    | EmptyL => false
                    | _ => false
                  end
      | op_ZCzl__ a1 a2 => match b with
                             | op_ZCzl__ b1 b2 => match GHC.Base.compare a1 b1 with
                                                    | Lt => false
                                                    | Eq => _GHC.Base.>_ a2 b2
                                                    | Gt => true
                                                  end
                             | _ => true
                           end
    end.

Definition Ord__ViewL_op_zgze__ {inst_a} `{_ : GHC.Base.Ord inst_a} : ViewL
                                                                      inst_a -> ViewL inst_a -> bool :=
  fun a b =>
    match a with
      | EmptyL => match b with
                    | EmptyL => true
                    | _ => false
                  end
      | op_ZCzl__ a1 a2 => match b with
                             | op_ZCzl__ b1 b2 => match GHC.Base.compare a1 b1 with
                                                    | Lt => false
                                                    | Eq => _GHC.Base.>=_ a2 b2
                                                    | Gt => true
                                                  end
                             | _ => true
                           end
    end.

Local Definition Ord__ViewL_max {inst_a} `{GHC.Base.Ord inst_a} : ViewL
                                                                  inst_a -> ViewL inst_a -> ViewL inst_a :=
  fun x y => if Ord__ViewL_op_zlze__ x y : bool then y else x.

Local Definition Ord__ViewL_min {inst_a} `{GHC.Base.Ord inst_a} : ViewL
                                                                  inst_a -> ViewL inst_a -> ViewL inst_a :=
  fun x y => if Ord__ViewL_op_zlze__ x y : bool then x else y.

Program Instance Ord__ViewL {a} `{GHC.Base.Ord a} : GHC.Base.Ord (ViewL a) :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__ViewL_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__ViewL_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__ViewL_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__ViewL_op_zgze__ ;
      GHC.Base.compare__ := Ord__ViewL_compare ;
      GHC.Base.max__ := Ord__ViewL_max ;
      GHC.Base.min__ := Ord__ViewL_min |}.

Local Definition Ord__ViewR_max {inst_a} `{GHC.Base.Ord inst_a} : ViewR
                                                                  inst_a -> ViewR inst_a -> ViewR inst_a :=
  fun x y => if Ord__ViewR_op_zlze__ x y : bool then y else x.

Local Definition Ord__ViewR_min {inst_a} `{GHC.Base.Ord inst_a} : ViewR
                                                                  inst_a -> ViewR inst_a -> ViewR inst_a :=
  fun x y => if Ord__ViewR_op_zlze__ x y : bool then x else y.

Program Instance Ord__ViewR {a} `{GHC.Base.Ord a} : GHC.Base.Ord (ViewR a) :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__ViewR_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__ViewR_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__ViewR_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__ViewR_op_zgze__ ;
      GHC.Base.compare__ := Ord__ViewR_compare ;
      GHC.Base.max__ := Ord__ViewR_max ;
      GHC.Base.min__ := Ord__ViewR_min |}.

Program Instance Traversable__Seq : Data.Traversable.Traversable Seq := fun _
                                                                            k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__Seq_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__Seq_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Seq_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Seq_traverse |}.

Definition scanl {a} {b} : (a -> b -> a) -> a -> Seq b -> Seq a :=
  fun f z0 xs =>
    z0 <| Data.Tuple.snd (Data.Traversable.mapAccumL (fun x z =>
                                                       let x' := f x z in pair x' x') z0 xs).

Local Definition Functor__ViewL_fmap : forall {a} {b},
                                         (a -> b) -> ViewL a -> ViewL b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | _ , EmptyL => EmptyL
        | f , op_ZCzl__ x xs => f x :< GHC.Base.fmap f xs
      end.

Local Definition Functor__ViewL_op_zlzd__ : forall {a} {b},
                                              a -> ViewL b -> ViewL a :=
  fun {a} {b} => fun x => Functor__ViewL_fmap (GHC.Base.const x).

Program Instance Functor__ViewL : GHC.Base.Functor ViewL := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__ViewL_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__ViewL_fmap |}.

Local Definition Functor__ViewR_fmap : forall {a} {b},
                                         (a -> b) -> ViewR a -> ViewR b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | _ , EmptyR => EmptyR
        | f , op_ZCzg__ xs x => GHC.Base.fmap f xs :> f x
      end.

Local Definition Traversable__ViewL_traverse : forall {f} {a} {b},
                                                 forall `{GHC.Base.Applicative f},
                                                   (a -> f b) -> ViewL a -> f (ViewL b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | _ , EmptyL => GHC.Base.pure EmptyL
        | f , op_ZCzl__ x xs => (_:<_ Data.Functor.<$> f x) GHC.Base.<*>
                                Data.Traversable.traverse f xs
      end.

Local Definition Foldable__ViewL_foldr : forall {a} {b},
                                           (a -> b -> b) -> b -> ViewL a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | _ , z , EmptyL => z
        | f , z , op_ZCzl__ x xs => f x (Data.Foldable.foldr f z xs)
      end.

Local Definition Foldable__ViewL_foldl : forall {b} {a},
                                           (b -> a -> b) -> b -> ViewL a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | _ , z , EmptyL => z
        | f , z , op_ZCzl__ x xs => Data.Foldable.foldl f (f z x) xs
      end.


Local Definition Functor__ViewR_op_zlzd__ : forall {a} {b},
                                              a -> ViewR b -> ViewR a :=
  fun {a} {b} => fun x => Functor__ViewR_fmap (GHC.Base.const x).

Program Instance Functor__ViewR : GHC.Base.Functor ViewR := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__ViewR_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__ViewR_fmap |}.

Local Definition Foldable__ViewR_foldMap : forall {m} {a},
                                             forall `{GHC.Base.Monoid m}, (a -> m) -> ViewR a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | _ , EmptyR => GHC.Base.mempty
        | f , op_ZCzg__ xs x => GHC.Base.mappend (Data.Foldable.foldMap f xs) (f x)
      end.

Local Definition Foldable__ViewR_foldl : forall {b} {a},
                                           (b -> a -> b) -> b -> ViewR a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | _ , z , EmptyR => z
        | f , z , op_ZCzg__ xs x => f (Data.Foldable.foldl f z xs) x
      end.

Local Definition Foldable__ViewR_foldr : forall {a} {b},
                                           (a -> b -> b) -> b -> ViewR a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__ , arg_1__ , arg_2__ with
        | _ , z , EmptyR => z
        | f , z , op_ZCzg__ xs x => Data.Foldable.foldr f (f x z) xs
      end.

Local Definition Traversable__ViewR_traverse : forall {f} {a} {b},
                                                 forall `{GHC.Base.Applicative f},
                                                   (a -> f b) -> ViewR a -> f (ViewR b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | _ , EmptyR => GHC.Base.pure EmptyR
        | f , op_ZCzg__ xs x => (_:>_ Data.Functor.<$> Data.Traversable.traverse f xs)
                                GHC.Base.<*> f x
      end.

Local Definition Traversable__ViewR_sequenceA : forall {f} {a},
                                                  forall `{GHC.Base.Applicative f}, ViewR (f a) -> f (ViewR a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__ViewR_traverse GHC.Base.id.

Local Definition Traversable__ViewR_sequence : forall {m} {a},
                                                 forall `{GHC.Base.Monad m}, ViewR (m a) -> m (ViewR a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__ViewR_sequenceA.

Local Definition Traversable__ViewR_mapM : forall {m} {a} {b},
                                             forall `{GHC.Base.Monad m}, (a -> m b) -> ViewR a -> m (ViewR b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__ViewR_traverse.


Local Definition Foldable__ViewR_toList : forall {a}, ViewR a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__ViewR_foldr c n t
                                end)
      end.

Local Definition Foldable__ViewR_foldl' : forall {b} {a},
                                            (b -> a -> b) -> b -> ViewR a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__ViewR_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__ViewR_foldr' : forall {a} {b},
                                            (a -> b -> b) -> b -> ViewR a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__ViewR_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__ViewR_length : forall {a}, ViewR a -> GHC.Num.Int :=
  fun {a} v =>
    Z.of_nat (Foldable__ViewR_foldr' (fun arg_0__ arg_1__ =>
                             match arg_0__ , arg_1__ with
                               | _ , k => k + id 1
                             end) (id 0) v).

Local Definition Foldable__ViewR_product : forall {a},
                                             forall `{GHC.Num.Num a}, ViewR a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__ViewR_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__ViewR_sum : forall {a},
                                         forall `{GHC.Num.Num a}, ViewR a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__ViewR_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__ViewR_fold : forall {m},
                                          forall `{GHC.Base.Monoid m}, ViewR m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__ViewR_foldMap GHC.Base.id.

Local Definition Foldable__ViewR_elem : forall {a},
                                          forall `{GHC.Base.Eq_ a}, a -> ViewR a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__ViewR_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Program Instance Foldable__ViewR : Data.Foldable.Foldable ViewR := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__ViewR_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__ViewR_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__ViewR_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__ViewR_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__ViewR_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__ViewR_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__ViewR_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__ViewR_length ;
      Data.Foldable.null__ := fun {a} => Foldable__ViewR_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__ViewR_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__ViewR_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__ViewR_toList |}.

Program Instance Traversable__ViewR : Data.Traversable.Traversable ViewR :=
  fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__ViewR_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__ViewR_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__ViewR_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__ViewR_traverse |}.


Local Definition Traversable__ViewL_sequenceA : forall {f} {a},
                                                  forall `{GHC.Base.Applicative f}, ViewL (f a) -> f (ViewL a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__ViewL_traverse GHC.Base.id.

Local Definition Traversable__ViewL_sequence : forall {m} {a},
                                                 forall `{GHC.Base.Monad m}, ViewL (m a) -> m (ViewL a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__ViewL_sequenceA.

Local Definition Traversable__ViewL_mapM : forall {m} {a} {b},
                                             forall `{GHC.Base.Monad m}, (a -> m b) -> ViewL a -> m (ViewL b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__ViewL_traverse.


Local Definition Foldable__ViewL_null : forall {a}, ViewL a -> bool :=
  fun {a} => Foldable__ViewL_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__ViewL_toList : forall {a}, ViewL a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => Foldable__ViewL_foldr c n t
                                end)
      end.

Local Definition Foldable__ViewL_foldl' : forall {b} {a},
                                            (b -> a -> b) -> b -> ViewL a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => _GHC.Base.$!_ k (f z x)
                             end in
                         Foldable__ViewL_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__ViewL_length : forall {a}, ViewL a -> GHC.Num.Int :=
  fun {a} v =>
    Z.of_nat (Foldable__ViewL_foldl' (fun arg_64__ arg_65__ =>
                             match arg_64__ , arg_65__ with
                               | c , _ => c + 1
                             end) (id 0) v).

Local Definition Foldable__ViewL_foldMap : forall {m} {a},
                                             forall `{GHC.Base.Monoid m}, (a -> m) -> ViewL a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_1__ =>
      match arg_1__ with
        | f => Foldable__ViewL_foldr (Coq.Program.Basics.compose GHC.Base.mappend f)
               GHC.Base.mempty
      end.

Local Definition Foldable__ViewL_product : forall {a},
                                             forall `{GHC.Num.Num a}, ViewL a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__ViewL_foldMap
                               Data.Monoid.Mk_Product).

Local Definition Foldable__ViewL_sum : forall {a},
                                         forall `{GHC.Num.Num a}, ViewL a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__ViewL_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition Foldable__ViewL_fold : forall {m},
                                          forall `{GHC.Base.Monoid m}, ViewL m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__ViewL_foldMap GHC.Base.id.

Local Definition Foldable__ViewL_elem : forall {a},
                                          forall `{GHC.Base.Eq_ a}, a -> ViewL a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__ViewL_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) _GHC.Base.==_.

Local Definition Foldable__ViewL_foldr' : forall {a} {b},
                                            (a -> b -> b) -> b -> ViewL a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => _GHC.Base.$!_ k (f x z)
                             end in
                         Foldable__ViewL_foldl f' GHC.Base.id xs z0
      end.

Program Instance Foldable__ViewL : Data.Foldable.Foldable ViewL := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__ViewL_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__ViewL_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__ViewL_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__ViewL_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__ViewL_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__ViewL_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__ViewL_foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__ViewL_length ;
      Data.Foldable.null__ := fun {a} => Foldable__ViewL_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__ViewL_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__ViewL_sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__ViewL_toList |}.

Program Instance Traversable__ViewL : Data.Traversable.Traversable ViewL :=
  fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__ViewL_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__ViewL_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__ViewL_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__ViewL_traverse |}.

Definition fromList2 {a} : nat -> list a -> Seq a :=
  fun n =>
    let ht :=
      fun arg_0__ =>
        match arg_0__ with
          | cons x xs => pair xs x
          | nil => error (GHC.Base.hs_string__ "fromList2: short list")
        end in
    execState (replicateA n (Mk_State ht)).

Definition sortBy {a} : (a -> a -> comparison) -> Seq a -> Seq a :=
  fun cmp xs =>
    fromList2 (length xs) (Data.OldList.sortBy cmp (Data.Foldable.toList xs)).

Definition sort {a} `{GHC.Base.Ord a} : Seq a -> Seq a :=
  sortBy GHC.Base.compare.

(*
Program Fixpoint unrollPQ {e} (cmp : e -> e -> comparison) (pq : PQueue e)  {measure (size pq)} : list e :=
    let mergePQs0 mergePQs :=
      fun arg_4__ =>
        match arg_4__ with
          | Nil => nil
          | op_ZCza__ t Nil => unrollPQ cmp t
          | op_ZCza__ t1 (op_ZCza__ t2 ts) => mergePQs (mergePQ cmp t1 t2) ts
        end in
    let fix mergePQs t ts :=
        (match ts with
         | Nil => unrollPQ cmp t
         | op_ZCza__ t1 Nil => unrollPQ cmp (mergePQ cmp t t1)
         | op_ZCza__ t1 (op_ZCza__ t2 ts') => mergePQs (mergePQ cmp t (mergePQ cmp t1 t2)) ts'
         end) in
    match pq with
    | Mk_PQueue x ts => cons x (mergePQs0 mergePQs ts)
    end.


Definition toPQ {e} {a} : (e -> e -> comparison) -> (a -> PQueue e) -> FingerTree a -> option (PQueue e) :=
  fix toPQ arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
             | _ , _ , Empty => None
             | _ , f , Single x => Some (f x)
             | cmp , f , Deep _ pr m sf => let lop_zlzpzg__ := mergePQ cmp in
                                           let fDigit :=
                                             fun digit =>
                                               match GHC.Base.fmap f digit with
                                                 | One a => a
                                                 | Two a b => mergePQ cmp a b
                                                 | Three a b c => mergePQ cmp (mergePQ cmp a b) c
                                                 | Four a b c d => mergePQ cmp (mergePQ cmp a b) (mergePQ cmp c d)
                                               end in
                                           let fNode := fDigit GHC.Base.∘ nodeToDigit in
                                           let pr' := fDigit pr in
                                           let sf' := fDigit sf in
                                           Some (Data.Maybe.maybe (mergePQ cmp pr' sf') (fun arg_14__ =>
                                                                                           mergePQ cmp (mergePQ cmp
                                                                                                        pr' sf')
                                                                                                        arg_14__) (toPQ
                                                                                                                  cmp
                                                                                                                  fNode
                                                                                                                  m))
           end.


Definition unstableSortBy {a} : (a -> a -> comparison) -> Seq a -> Seq a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | cmp , Mk_Seq xs => fromList2 (size xs) GHC.Base.$ (Data.Maybe.maybe nil
                           (unrollPQ cmp) GHC.Base.$ toPQ cmp (fun arg_2__ =>
                                                                match arg_2__ with
                                                                  | Mk_Elem x => Mk_PQueue x Nil
                                                                end) xs)
    end.

Definition unstableSort {a} `{GHC.Base.Ord a} : Seq a -> Seq a :=
  unstableSortBy GHC.Base.compare.
*)

Definition iterateN {a} : nat -> (a -> a) -> a -> Seq a :=
  fun n f x =>
    if negb (Nat.ltb n 0) : bool
    then execState (replicateA n (Mk_State (fun y => pair (f y) y))) x
    else error (GHC.Base.hs_string__
               "iterateN takes a nonnegative integer argument").

Definition reverseDigit {a} : (a -> a) -> Digit a -> Digit a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , One a => One (f a)
      | f , Two a b => Two (f b) (f a)
      | f , Three a b c => Three (f c) (f b) (f a)
      | f , Four a b c d => Four (f d) (f c) (f b) (f a)
    end.

Definition reverseNode {a} : (a -> a) -> Node a -> Node a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , Node2 s a b => Node2 s (f b) (f a)
      | f , Node3 s a b c => Node3 s (f c) (f b) (f a)
    end.

(* polyrec *)
Definition reverseTree : forall {a}, (a -> a) -> FingerTree a -> FingerTree a :=
  fix reverseTree {a} arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Empty => Empty
             | f , Single x => Single (f x)
             | f , Deep s pr m sf => Deep s (reverseDigit f sf) (reverseTree (reverseNode f)
                                                                m) (reverseDigit f pr)
           end.

Definition reverse {a} : Seq a -> Seq a :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Seq xs => Mk_Seq (reverseTree GHC.Base.id xs)
    end.

Definition singleton {a} : a -> Seq a :=
  fun x => Mk_Seq (Single (Mk_Elem x)).

Local Definition Applicative__Seq_pure : forall {a}, a -> Seq a :=
  fun {a} => singleton.

Fixpoint snocTree {a} `{_ : Sized a} (arg_0__ : FingerTree a) (arg_1__ : a)
           : FingerTree a
           := match arg_0__ , arg_1__ with
                | Empty , a => Single a
                | Single a , b => deep (One a) Empty (One b)
                | Deep s pr m (Four a b c d) , e => GHC.Prim.seq m (Deep (s + (size
                                                                                      e)) pr (snocTree m (node3 a b c))
                                                                         (Two d e))
                | Deep s pr m (Three a b c) , d => Deep (s + (size d)) pr m (Four a b
                                                                                            c d)
                | Deep s pr m (Two a b) , c => Deep (s + (size c)) pr m (Three a b c)
                | Deep s pr m (One a) , b => Deep (s + (size b)) pr m (Two a b)
              end.

Definition op_zbzg__ {a} : Seq a -> a -> Seq a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_Seq xs , x => Mk_Seq (snocTree xs (Mk_Elem x))
    end.

Notation "'_|>_'" := (op_zbzg__).

Infix "|>" := (_|>_) (at level 99).

Definition scanr {a} {b} : (a -> b -> b) -> b -> Seq a -> Seq b :=
  fun f z0 xs =>
    Data.Tuple.snd (Data.Traversable.mapAccumR (fun z x =>
                                                 let z' := f x z in pair z' z') z0 xs) |> z0.

Definition filter {a} : (a -> bool) -> Seq a -> Seq a :=
  fun p =>
    Data.Foldable.foldl (fun xs x => if p x : bool then xs |> x else xs) empty.

Definition partition {a} : (a -> bool) -> Seq a -> (Seq a * Seq a)%type :=
  fun p =>
    let part :=
      fun arg_0__ arg_1__ =>
        match arg_0__ , arg_1__ with
          | pair xs ys , x => if p x : bool
                              then pair (xs |> x) ys
                              else pair xs (ys |> x)
        end in
    Data.Foldable.foldl part (pair empty empty).

(*
Definition unfoldr {b} {a} : (b -> option (a * b)%type) -> b -> Seq a :=
  fun f =>
    let fix unfoldr' as_ b
              := Data.Maybe.maybe as_ (fun arg_0__ =>
                                        match arg_0__ with
                                          | pair a b' => unfoldr' (as_ |> a) b'
                                        end) (f b) in
    unfoldr' empty.
*)

Definition thin12 {a} `{Sized a} thin (s  : nat) (pr : Digit12 a) (m: FingerTree (Node a))
         (dd: Digit a) : Thin a :=
    match dd with
      | One a => DeepTh s pr (thin m) (One12 a)
      | Two a b => DeepTh s pr (thin m) (Two12 a b)
      | Three a b c => DeepTh s pr (thin (snocTree m (node2 a b))) (One12 c)
      | Four a b c d => DeepTh s pr (thin (snocTree m (node2 a b))) (Two12 c d)
    end.


Program Fixpoint thin {a} `{Sized a} (ft : FingerTree a) { measure  (size ft) } : Thin a :=
    let thin12 {a} `{Sized a} (s  : nat) (pr : Digit12 a) (m: FingerTree (Node a)) (dd: Digit a) : Thin a :=
    match dd with
      | One a => DeepTh s pr (thin m) (One12 a)
      | Two a b => DeepTh s pr (thin m) (Two12 a b)
      | Three a b c => DeepTh s pr (thin (snocTree m (node2 a b))) (One12 c)
      | Four a b c d => DeepTh s pr (thin (snocTree m (node2 a b))) (Two12 c d)
    end in
    (match ft with
      | Empty => EmptyTh
      | Single a => SingleTh a
      | Deep s pr m sf =>
        match pr with
        | One a => thin12 s (One12 a) m sf
        | Two a b => thin12 s (Two12 a b) m sf
        | Three a b c => thin12 s (One12 a) (consTree (node2 b c) m) sf
        | Four a b c d => thin12 s (Two12 a b) (consTree (node2 c d) m) sf
        end
    end).
Next Obligation.
unfold size, Sized__FingerTree, size__, Sized__FingerTree_size.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.


Definition rigidifyRight {a} : nat -> Digit23 (Elem a) -> FingerTree
                               (Node (Elem a)) -> Digit (Elem a) -> Rigidified (Elem a) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | s , pr , m , Two a b => RigidFull GHC.Base.$ Mk_Rigid s pr (thin m) (node2 a b)
      | s , pr , m , Three a b c => RigidFull GHC.Base.$ Mk_Rigid s pr (thin m) (node3
                                                                                a b c)
      | s , pr , m , Four a b c d => RigidFull GHC.Base.$ Mk_Rigid s pr (thin
                                                                        GHC.Base.$ snocTree m (node2 a b)) (node2 c d)
      | s , pr , m , One e => match viewRTree m with
                                | Just2 m' (Node2 _ a b) => RigidFull GHC.Base.$ Mk_Rigid s pr (thin m') (node3
                                                                                                         a b e)
                                | Just2 m' (Node3 _ a b c) => RigidFull GHC.Base.$ Mk_Rigid s pr (thin
                                                                                                 GHC.Base.$ snocTree m'
                                                                                                                     (node2
                                                                                                                     a
                                                                                                                     b))
                                                              (node2 c e)
                                | Nothing2 => match pr with
                                                | Node2 _ a b => RigidThree a b e
                                                | Node3 _ a b c => RigidFull GHC.Base.$ Mk_Rigid s (node2 a b) EmptyTh
                                                                   (node2 c e)
                                              end
                              end
    end.

Definition rigidify {a} : FingerTree (Elem a) -> Rigidified (Elem a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Empty => RigidEmpty
      | Single q => RigidOne q
      | Deep s (Two a b) m sf => rigidifyRight s (node2 a b) m sf
      | Deep s (Three a b c) m sf => rigidifyRight s (node3 a b c) m sf
      | Deep s (Four a b c d) m sf => rigidifyRight s (node2 a b) (consTree (node2 c
                                                                            d) m) sf
      | Deep s (One a) m sf => match viewLTree m with
                                 | Just2 (Node2 _ b c) m' => rigidifyRight s (node3 a b c) m' sf
                                 | Just2 (Node3 _ b c d) m' => rigidifyRight s (node2 a b) (consTree (node2 c d)
                                                                                                     m') sf
                                 | Nothing2 => match sf with
                                                 | One b => RigidTwo a b
                                                 | Two b c => RigidThree a b c
                                                 | Three b c d => RigidFull GHC.Base.$ Mk_Rigid s (node2 a b) EmptyTh
                                                                  (node2 c d)
                                                 | Four b c d e => RigidFull GHC.Base.$ Mk_Rigid s (node3 a b c) EmptyTh
                                                                   (node2 d e)
                                               end
                               end
    end.

Parameter rigid_metric : forall {c}, Rigid c -> nat.

Program Fixpoint cycleNMiddle {c} (n:nat) (r : Rigid c) {measure (rigid_metric r)} : FingerTree (Node c) :=
  match r with
  | Mk_Rigid s pr (DeepTh sm prm mm sfm) sf =>
    Deep (sm + (s * (n + 1)))  (* -- note: sm = s - size pr - size sf *)
         (digit12ToDigit prm)
         (cycleNMiddle n (Mk_Rigid s (squashL pr prm) mm (squashR sfm sf)))
         (digit12ToDigit sfm)
  | Mk_Rigid s pr EmptyTh sf =>
    let converted := node2 pr sf in
    deep (One sf) (runIdentity GHC.Base.$ applicativeTree n s
                               (Data.Functor.Identity.Mk_Identity converted)) (One pr)
  | Mk_Rigid s pr (SingleTh q) sf =>
    let converted := node3 pr q sf in
    deep (Two q sf) (runIdentity GHC.Base.$ applicativeTree n s
                                 (Data.Functor.Identity.Mk_Identity converted))
         (Two pr q)
  end.
Next Obligation.
Admitted.


Definition cycleN {a} : nat -> Seq a -> Seq a :=
  fun arg_0__ arg_1__ =>
    let j_11__ :=
      match arg_0__ , arg_1__ with
        | n , Mk_Seq xsFT => match rigidify xsFT with
                               | RigidEmpty => empty
                               | RigidOne (Mk_Elem x) => replicate n x
                               | RigidTwo x1 x2 => let pair_ := Two x1 x2 in
                                                   Mk_Seq GHC.Base.$ Deep (n * id 2) pair_
                                                   (runIdentity GHC.Base.$ applicativeTree (n -
                                                                                           id 2)
                                                   (id 2) (Data.Functor.Identity.Mk_Identity (node2 x1
                                                                                                              x2)))
                                                   pair_
                               | RigidThree x1 x2 x3 => let triple := Three x1 x2 x3 in
                                                        Mk_Seq GHC.Base.$ Deep (n * id 3)
                                                        triple (runIdentity GHC.Base.$ applicativeTree (n -
                                                                                                       id
                                                                                                       2)
                                                               (id 3)
                                                               (Data.Functor.Identity.Mk_Identity (node3 x1 x2 x3)))
                                                        triple
                               | RigidFull (Mk_Rigid s pr _m sf as r) => Mk_Seq GHC.Base.$ Deep (n * s)
                                                                         (nodeToDigit pr) (cycleNMiddle (n -
                                                                                                        id
                                                                                                        2) r)
                                                                         (nodeToDigit sf)
                             end
      end in
    match arg_0__ , arg_1__ with
      | n , xs => if Nat.ltb n 0 : bool
                  then error (GHC.Base.hs_string__ "cycleN takes a nonnegative integer argument")
                  else if Nat.eqb n 0 : bool
                       then empty
                       else if Nat.eqb n 1 : bool
                            then xs
                            else j_11__
    end.

Local Definition Applicative__Seq_op_ztzg__ : forall {a} {b},
                                                Seq a -> Seq b -> Seq b :=
  fun {a} {b} => fun xs ys => cycleN (length xs) ys.


Definition addDigits4 {a} appendTree2 appendTree3 appendTree4 :
       FingerTree (Node (Node a))  ->
       Digit (Node a) -> Node a -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree
                            (Node (Node a)) :=
  fun ft arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ arg_7__ =>
    match ft
        , arg_1__
        , arg_2__
        , arg_3__
        , arg_4__
        , arg_5__
        , arg_6__
        , arg_7__ with
      | m1 , One a , b , c , d , e , One f , m2 => appendTree2 m1 (node3 a b c) (node3
                                                                                d e f) m2
      | m1 , One a , b , c , d , e , Two f g , m2 => appendTree3 m1 (node3 a b c)
                                                     (node2 d e) (node2 f g) m2
      | m1 , One a , b , c , d , e , Three f g h , m2 => appendTree3 m1 (node3 a b c)
                                                         (node3 d e f) (node2 g h) m2
      | m1 , One a , b , c , d , e , Four f g h i , m2 => appendTree3 m1 (node3 a b c)
                                                          (node3 d e f) (node3 g h i) m2
      | m1 , Two a b , c , d , e , f , One g , m2 => appendTree3 m1 (node3 a b c)
                                                     (node2 d e) (node2 f g) m2
      | m1 , Two a b , c , d , e , f , Two g h , m2 => appendTree3 m1 (node3 a b c)
                                                       (node3 d e f) (node2 g h) m2
      | m1 , Two a b , c , d , e , f , Three g h i , m2 => appendTree3 m1 (node3 a b
                                                                          c) (node3 d e f) (node3 g h i) m2
      | m1 , Two a b , c , d , e , f , Four g h i j , m2 => appendTree4 m1 (node3 a b
                                                                           c) (node3 d e f) (node2 g h) (node2 i j) m2
      | m1 , Three a b c , d , e , f , g , One h , m2 => appendTree3 m1 (node3 a b c)
                                                         (node3 d e f) (node2 g h) m2
      | m1 , Three a b c , d , e , f , g , Two h i , m2 => appendTree3 m1 (node3 a b
                                                                          c) (node3 d e f) (node3 g h i) m2
      | m1 , Three a b c , d , e , f , g , Three h i j , m2 => appendTree4 m1 (node3 a
                                                                              b c) (node3 d e f) (node2 g h) (node2 i j)
                                                               m2
      | m1 , Three a b c , d , e , f , g , Four h i j k , m2 => appendTree4 m1 (node3
                                                                               a b c) (node3 d e f) (node3 g h i) (node2
                                                                                                                  j k)
                                                                m2
      | m1 , Four a b c d , e , f , g , h , One i , m2 => appendTree3 m1 (node3 a b c)
                                                          (node3 d e f) (node3 g h i) m2
      | m1 , Four a b c d , e , f , g , h , Two i j , m2 => appendTree4 m1 (node3 a b
                                                                           c) (node3 d e f) (node2 g h) (node2 i j) m2
      | m1 , Four a b c d , e , f , g , h , Three i j k , m2 => appendTree4 m1 (node3
                                                                               a b c) (node3 d e f) (node3 g h i) (node2
                                                                                                                  j k)
                                                                m2
      | m1 , Four a b c d , e , f , g , h , Four i j k l , m2 => appendTree4 m1 (node3
                                                                                a b c) (node3 d e f) (node3 g h i)
                                                                 (node3 j k l) m2
    end.

Definition addDigits2 {a} appendTree2 appendTree3 appendTree4 :
  FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Digit (Node a)
  -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a)) :=
  fun ft arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ =>
    match ft , arg_1__ , arg_2__ , arg_3__ , arg_4__ , arg_5__ with
      | m1 , One a , b , c , One d , m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
      | m1 , One a , b , c , Two d e , m2 => appendTree2 m1 (node3 a b c) (node2 d e)
                                             m2
      | m1 , One a , b , c , Three d e f , m2 => appendTree2 m1 (node3 a b c) (node3 d
                                                                              e f) m2
      | m1 , One a , b , c , Four d e f g , m2 => appendTree3 m1 (node3 a b c) (node2
                                                                               d e) (node2 f g) m2
      | m1 , Two a b , c , d , One e , m2 => appendTree2 m1 (node3 a b c) (node2 d e)
                                             m2
      | m1 , Two a b , c , d , Two e f , m2 => appendTree2 m1 (node3 a b c) (node3 d e
                                                                            f) m2
      | m1 , Two a b , c , d , Three e f g , m2 => appendTree3 m1 (node3 a b c) (node2
                                                                                d e) (node2 f g) m2
      | m1 , Two a b , c , d , Four e f g h , m2 => appendTree3 m1 (node3 a b c)
                                                    (node3 d e f) (node2 g h) m2
      | m1 , Three a b c , d , e , One f , m2 => appendTree2 m1 (node3 a b c) (node3 d
                                                                              e f) m2
      | m1 , Three a b c , d , e , Two f g , m2 => appendTree3 m1 (node3 a b c) (node2
                                                                                d e) (node2 f g) m2
      | m1 , Three a b c , d , e , Three f g h , m2 => appendTree3 m1 (node3 a b c)
                                                       (node3 d e f) (node2 g h) m2
      | m1 , Three a b c , d , e , Four f g h i , m2 => appendTree3 m1 (node3 a b c)
                                                        (node3 d e f) (node3 g h i) m2
      | m1 , Four a b c d , e , f , One g , m2 => appendTree3 m1 (node3 a b c) (node2
                                                                               d e) (node2 f g) m2
      | m1 , Four a b c d , e , f , Two g h , m2 => appendTree3 m1 (node3 a b c)
                                                    (node3 d e f) (node2 g h) m2
      | m1 , Four a b c d , e , f , Three g h i , m2 => appendTree3 m1 (node3 a b c)
                                                        (node3 d e f) (node3 g h i) m2
      | m1 , Four a b c d , e , f , Four g h i j , m2 => appendTree4 m1 (node3 a b c)
                                                         (node3 d e f) (node2 g h) (node2 i j) m2
    end.

Definition addDigits3 {a} appendTree2 appendTree3 appendTree4 :
  FingerTree (Node (Node a)) -> Digit (Node a) -> Node
                                                  a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node
                                                                                        a)) -> FingerTree (Node (Node
                                                                                                                a)) :=
  fun ft arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ =>
    match ft , arg_1__ , arg_2__ , arg_3__ , arg_4__ , arg_5__ , arg_6__ with
      | m1 , One a , b , c , d , One e , m2 => appendTree2 m1 (node3 a b c) (node2 d
                                                                            e) m2
      | m1 , One a , b , c , d , Two e f , m2 => appendTree2 m1 (node3 a b c) (node3 d
                                                                              e f) m2
      | m1 , One a , b , c , d , Three e f g , m2 => appendTree3 m1 (node3 a b c)
                                                     (node2 d e) (node2 f g) m2
      | m1 , One a , b , c , d , Four e f g h , m2 => appendTree3 m1 (node3 a b c)
                                                      (node3 d e f) (node2 g h) m2
      | m1 , Two a b , c , d , e , One f , m2 => appendTree2 m1 (node3 a b c) (node3 d
                                                                              e f) m2
      | m1 , Two a b , c , d , e , Two f g , m2 => appendTree3 m1 (node3 a b c) (node2
                                                                                d e) (node2 f g) m2
      | m1 , Two a b , c , d , e , Three f g h , m2 => appendTree3 m1 (node3 a b c)
                                                       (node3 d e f) (node2 g h) m2
      | m1 , Two a b , c , d , e , Four f g h i , m2 => appendTree3 m1 (node3 a b c)
                                                        (node3 d e f) (node3 g h i) m2
      | m1 , Three a b c , d , e , f , One g , m2 => appendTree3 m1 (node3 a b c)
                                                     (node2 d e) (node2 f g) m2
      | m1 , Three a b c , d , e , f , Two g h , m2 => appendTree3 m1 (node3 a b c)
                                                       (node3 d e f) (node2 g h) m2
      | m1 , Three a b c , d , e , f , Three g h i , m2 => appendTree3 m1 (node3 a b
                                                                          c) (node3 d e f) (node3 g h i) m2
      | m1 , Three a b c , d , e , f , Four g h i j , m2 => appendTree4 m1 (node3 a b
                                                                           c) (node3 d e f) (node2 g h) (node2 i j) m2
      | m1 , Four a b c d , e , f , g , One h , m2 => appendTree3 m1 (node3 a b c)
                                                      (node3 d e f) (node2 g h) m2
      | m1 , Four a b c d , e , f , g , Two h i , m2 => appendTree3 m1 (node3 a b c)
                                                        (node3 d e f) (node3 g h i) m2
      | m1 , Four a b c d , e , f , g , Three h i j , m2 => appendTree4 m1 (node3 a b
                                                                           c) (node3 d e f) (node2 g h) (node2 i j) m2
      | m1 , Four a b c d , e , f , g , Four h i j k , m2 => appendTree4 m1 (node3 a b
                                                                            c) (node3 d e f) (node3 g h i) (node2 j k)
                                                             m2
    end.



Fixpoint appendTree4 {a} (ft: FingerTree (Node a)) : Node a -> Node a -> Node
                             a -> Node a -> FingerTree (Node a) -> FingerTree (Node a) :=
  fun arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ =>
    match ft , arg_1__ , arg_2__ , arg_3__ , arg_4__ , arg_5__ with
      | Empty , a , b , c , d , xs => consTree a (consTree b (consTree c (consTree d
                                                                                   xs)))
      | xs , a , b , c , d , Empty => snocTree (snocTree (snocTree (snocTree xs a) b)
                                                         c) d
      | Single x , a , b , c , d , xs => consTree x (consTree a (consTree b (consTree
                                                                          c (consTree d xs))))
      | xs , a , b , c , d , Single x => snocTree (snocTree (snocTree (snocTree
                                                                      (snocTree xs a) b) c) d) x
      | Deep s1 pr1 m1 sf1 , a , b , c , d , Deep s2 pr2 m2 sf2 => Deep (((((s1
                                                                        + size a) + size b) +
                                                                        size c) + size d) + s2) pr1
                                                                   (addDigits4 appendTree2 appendTree3 appendTree4
                                                                               m1 sf1 a b c d pr2 m2) sf2
    end
with appendTree2 {a} (ft : FingerTree (Node a)) : Node a -> Node
                             a -> FingerTree (Node a) -> FingerTree (Node a) :=
  fun arg_1__ arg_2__ arg_3__ =>
    match ft , arg_1__ , arg_2__ , arg_3__ with
      | Empty , a , b , xs => consTree a (consTree b xs)
      | xs , a , b , Empty => snocTree (snocTree xs a) b
      | Single x , a , b , xs => consTree x (consTree a (consTree b xs))
      | xs , a , b , Single x => snocTree (snocTree (snocTree xs a) b) x
      | Deep s1 pr1 m1 sf1 , a , b , Deep s2 pr2 m2 sf2 => Deep (((s1 + size
                                                                a) + size b) + s2) pr1
                                                               (addDigits2 appendTree2 appendTree3 appendTree4 m1
                                                                                                       sf1 a b pr2 m2)
                                                           sf2
    end
with appendTree3 {a} (ft : FingerTree (Node a)) : Node a -> Node a -> Node
                             a -> FingerTree (Node a) -> FingerTree (Node a) :=
  fun arg_1__ arg_2__ arg_3__ arg_4__ =>
    match ft , arg_1__ , arg_2__ , arg_3__ , arg_4__ with
      | Empty , a , b , c , xs => consTree a (consTree b (consTree c xs))
      | xs , a , b , c , Empty => snocTree (snocTree (snocTree xs a) b) c
      | Single x , a , b , c , xs => consTree x (consTree a (consTree b (consTree c
                                                                                  xs)))
      | xs , a , b , c , Single x => snocTree (snocTree (snocTree (snocTree xs a) b)
                                                        c) x
      | Deep s1 pr1 m1 sf1 , a , b , c , Deep s2 pr2 m2 sf2 => Deep ((((s1 +
                                                                    size a) + size b) + size c)
                                                                    + s2) pr1 (addDigits3 appendTree2 appendTree3 appendTree4 m1 sf1 a b c pr2 m2)
                                                               sf2
    end.


Definition addDigits1 {a} appendTree1 : FingerTree (Node (Node a)) -> Digit (Node a) -> Node
                            a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node
                                                                                                  a)) :=
  fun ft arg_1__ arg_2__ arg_3__ arg_4__ =>
    match ft , arg_1__ , arg_2__ , arg_3__ , arg_4__ with
      | m1 , One a , b , One c , m2 => appendTree1 m1 (node3 a b c) m2
      | m1 , One a , b , Two c d , m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
      | m1 , One a , b , Three c d e , m2 => appendTree2 m1 (node3 a b c) (node2 d e)
                                             m2
      | m1 , One a , b , Four c d e f , m2 => appendTree2 m1 (node3 a b c) (node3 d e
                                                                           f) m2
      | m1 , Two a b , c , One d , m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
      | m1 , Two a b , c , Two d e , m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
      | m1 , Two a b , c , Three d e f , m2 => appendTree2 m1 (node3 a b c) (node3 d e
                                                                            f) m2
      | m1 , Two a b , c , Four d e f g , m2 => appendTree3 m1 (node3 a b c) (node2 d
                                                                             e) (node2 f g) m2
      | m1 , Three a b c , d , One e , m2 => appendTree2 m1 (node3 a b c) (node2 d e)
                                             m2
      | m1 , Three a b c , d , Two e f , m2 => appendTree2 m1 (node3 a b c) (node3 d e
                                                                            f) m2
      | m1 , Three a b c , d , Three e f g , m2 => appendTree3 m1 (node3 a b c) (node2
                                                                                d e) (node2 f g) m2
      | m1 , Three a b c , d , Four e f g h , m2 => appendTree3 m1 (node3 a b c)
                                                    (node3 d e f) (node2 g h) m2
      | m1 , Four a b c d , e , One f , m2 => appendTree2 m1 (node3 a b c) (node3 d e
                                                                           f) m2
      | m1 , Four a b c d , e , Two f g , m2 => appendTree3 m1 (node3 a b c) (node2 d
                                                                             e) (node2 f g) m2
      | m1 , Four a b c d , e , Three f g h , m2 => appendTree3 m1 (node3 a b c)
                                                    (node3 d e f) (node2 g h) m2
      | m1 , Four a b c d , e , Four f g h i , m2 => appendTree3 m1 (node3 a b c)
                                                     (node3 d e f) (node3 g h i) m2
    end.


Fixpoint appendTree1 {a} ( ft : FingerTree (Node a)) : Node a -> FingerTree (Node
                                                                         a) -> FingerTree (Node a) :=
  fun arg_1__ arg_2__ =>
    match ft , arg_1__ , arg_2__ with
      | Empty , a , xs => consTree a xs
      | xs , a , Empty => snocTree xs a
      | Single x , a , xs => consTree x (consTree a xs)
      | xs , a , Single x => snocTree (snocTree xs a) x
      | Deep s1 pr1 m1 sf1 , a , Deep s2 pr2 m2 sf2 => Deep ((s1 + size a)
                                                            + s2) pr1 (addDigits1 appendTree1 m1 sf1 a pr2 m2) sf2
    end.


Definition addDigits0 {a} `{Sized a} (ft : FingerTree (Node a)) : Digit a -> Digit
                                       a -> FingerTree (Node a) -> FingerTree (Node a) :=
  fun arg_1__ arg_2__ arg_3__ =>
    match ft , arg_1__ , arg_2__ , arg_3__ with
      | m1 , One a , One b , m2 => appendTree1 m1 (node2 a b) m2
      | m1 , One a , Two b c , m2 => appendTree1 m1 (node3 a b c) m2
      | m1 , One a , Three b c d , m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
      | m1 , One a , Four b c d e , m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
      | m1 , Two a b , One c , m2 => appendTree1 m1 (node3 a b c) m2
      | m1 , Two a b , Two c d , m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
      | m1 , Two a b , Three c d e , m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
      | m1 , Two a b , Four c d e f , m2 => appendTree2 m1 (node3 a b c) (node3 d e f)
                                            m2
      | m1 , Three a b c , One d , m2 => appendTree2 m1 (node2 a b) (node2 c d) m2
      | m1 , Three a b c , Two d e , m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
      | m1 , Three a b c , Three d e f , m2 => appendTree2 m1 (node3 a b c) (node3 d e
                                                                            f) m2
      | m1 , Three a b c , Four d e f g , m2 => appendTree3 m1 (node3 a b c) (node2 d
                                                                             e) (node2 f g) m2
      | m1 , Four a b c d , One e , m2 => appendTree2 m1 (node3 a b c) (node2 d e) m2
      | m1 , Four a b c d , Two e f , m2 => appendTree2 m1 (node3 a b c) (node3 d e f)
                                            m2
      | m1 , Four a b c d , Three e f g , m2 => appendTree3 m1 (node3 a b c) (node2 d
                                                                             e) (node2 f g) m2
      | m1 , Four a b c d , Four e f g h , m2 => appendTree3 m1 (node3 a b c) (node3 d
                                                                              e f) (node2 g h) m2
    end.

Fixpoint appendTree0 {a} ( ft : FingerTree (Elem a)) : FingerTree (Elem
                                                               a) -> FingerTree (Elem a) :=
  fun arg_1__ =>
    match ft , arg_1__ with
      | Empty , xs => xs
      | xs , Empty => xs
      | Single x , xs => consTree x xs
      | xs , Single x => snocTree xs x
      | Deep s1 pr1 m1 sf1 , Deep s2 pr2 m2 sf2 => Deep (s1 + s2) pr1
                                                   (addDigits0 m1 sf1 pr2 m2) sf2
    end.

Definition op_zgzl__ {a} : Seq a -> Seq a -> Seq a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_Seq xs , Mk_Seq ys => Mk_Seq (appendTree0 xs ys)
    end.

Notation "'_><_'" := (op_zgzl__).

Infix "><" := (_><_) (at level 99).

Local Definition Monad__Seq_op_zgzgze__ : forall {a} {b},
                                            Seq a -> (a -> Seq b) -> Seq b :=
  fun {a} {b} =>
    fun xs f =>
      let add := fun ys x => ys >< f x in Data.Foldable.foldl' add empty xs.

Definition splitDigit {a} `{Sized a} : nat -> Digit a -> Split (option
                                                                       (Digit a)) a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | i , One a => GHC.Prim.seq i (Mk_Split None a None)
      | i , Two a b => let sa := size a in
                       if Nat.ltb i sa : bool
                       then Mk_Split None a (Some (One b))
                       else Mk_Split (Some (One a)) b None
      | i , Three a b c => let sa := size a in
                           let sab := sa + size b in
                           if Nat.ltb i sa : bool
                           then Mk_Split None a (Some (Two b c))
                           else if Nat.ltb i sab : bool
                                then Mk_Split (Some (One a)) b (Some (One c))
                                else Mk_Split (Some (Two a b)) c None
      | i , Four a b c d => let sa := size a in
                            let sab := sa + size b in
                            let sabc := sab + size c in
                            if Nat.ltb i sa : bool
                            then Mk_Split None a (Some (Three b c d))
                            else if Nat.ltb i sab : bool
                                 then Mk_Split (Some (One a)) b (Some (Two c d))
                                 else if Nat.ltb i sabc : bool
                                      then Mk_Split (Some (Two a b)) c (Some (One d))
                                      else Mk_Split (Some (Three a b c)) d None
    end.

Definition splitMap {s} {a} {b} : (nat -> s -> (s * s)%type) -> (s -> a -> b) -> s -> Seq a -> Seq b :=
  fun splt' =>
    let splitMapNode {a} {s} {b} `{Sized a} : (nat -> s -> (s *
                                              s)%type) -> (s -> a -> b) -> s -> Node a -> Node b :=
      fun arg_0__ arg_1__ arg_2__ arg_3__ =>
        match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
          | splt , f , s , Node2 ns a b => match splt (size a) s with
                                             | pair first second => Node2 ns (f first a) (f second b)
                                           end
          | splt , f , s , Node3 ns a b c => match splt (size a) s with
                                               | pair first r => match splt (size b) r with
                                                                   | pair second third => Node3 ns (f first a) (f second
                                                                                                               b) (f
                                                                                                                  third
                                                                                                                  c)
                                                                 end
                                             end
        end in
    let splitMapDigit {a} {s} {b} `{Sized a} : (nat -> s -> (s * s)%type) -> (s -> a -> b) -> s -> Digit a -> Digit b :=
      fun arg_10__ arg_11__ arg_12__ arg_13__ =>
        match arg_10__ , arg_11__ , arg_12__ , arg_13__ with
          | _ , f , s , One a => One (f s a)
          | splt , f , s , Two a b => match splt (size a) s with
                                        | pair first second => Two (f first a) (f second b)
                                      end
          | splt , f , s , Three a b c => match splt (size a) s with
                                            | pair first r => match splt (size b) r with
                                                                | pair second third => Three (f first a) (f second b) (f
                                                                                                                      third
                                                                                                                      c)
                                                              end
                                          end
          | splt , f , s , Four a b c d => match splt (size a) s with
                                             | pair first s' => match splt (size b + size c) s' with
                                                                  | pair middle fourth => match splt (size b)
                                                                                                  middle with
                                                                                            | pair second third => Four
                                                                                                                   (f
                                                                                                                   first
                                                                                                                   a) (f
                                                                                                                      second
                                                                                                                      b)
                                                                                                                   (f
                                                                                                                   third
                                                                                                                   c) (f
                                                                                                                      fourth
                                                                                                                      d)
                                                                                          end
                                                                end
                                           end
        end in
    let splitMapTree : forall {a} {s} {b} `{Sized a} , (nat -> s -> (s *
                                              s)%type) -> (s -> a -> b) -> s -> FingerTree a -> FingerTree b :=
      fix splitMapTree {a} {s} {b} `{Sized a} arg_25__ arg_26__ arg_27__ arg_28__
            := match arg_25__ , arg_26__ , arg_27__ , arg_28__ with
                 | _ , _ , _ , Empty => Empty
                 | _ , f , s , Single xs => Single GHC.Base.$ f s xs
                 | splt , f , s , Deep n pr m sf => match splt (size pr) s with
                                                      | pair prs r => match splt ((n - size pr) - size
                                                                                 sf) r with
                                                                        | pair ms sfs => Deep n (splitMapDigit splt f
                                                                                                prs pr) (splitMapTree
                                                                                                        splt
                                                                                                        (splitMapNode
                                                                                                        splt f) ms m)
                                                                                         (splitMapDigit splt f sfs sf)
                                                                      end
                                                    end
               end in
    let go :=
      fun arg_34__ arg_35__ arg_36__ =>
        match arg_34__ , arg_35__ , arg_36__ with
          | f , s , Mk_Seq xs => Mk_Seq (splitMapTree _ _ _ _ splt' (fun arg_37__
                                                                           arg_38__ =>
                                                                        match arg_37__ , arg_38__ with
                                                                          | s' , Mk_Elem a => Mk_Elem (f s' a)
                                                                        end) s xs)
        end in
    go.

Definition splitNode {a} `{Sized a} : nat -> Node a -> Split (option
                                                                     (Digit a)) a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | i , Node2 _ a b => let sa := size a in
                           if Nat.ltb i sa : bool
                           then Mk_Split None a (Some (One b))
                           else Mk_Split (Some (One a)) b None
      | i , Node3 _ a b c => let sa := size a in
                             let sab := sa + size b in
                             if Nat.ltb i sa : bool
                             then Mk_Split None a (Some (Two b c))
                             else if Nat.ltb i sab : bool
                                  then Mk_Split (Some (One a)) b (Some (One c))
                                  else Mk_Split (Some (Two a b)) c None
    end.

Definition splitTree : forall {a} `{Sized a} , nat -> FingerTree a -> Split
                                      (FingerTree a) a :=
  fix splitTree {a} `{Sized a} arg_0__ arg_1__ {struct arg_1__ }
        := match arg_0__ , arg_1__ with
             | _ , Empty => error (GHC.Base.hs_string__ "splitTree of empty tree")
             | i , Single x => GHC.Prim.seq i (Mk_Split Empty x Empty)
             | i , Deep _ pr m sf => let spr := size pr in
                                     let spm := spr + size m in
                                     let im := i - spr in
                                     if Nat.ltb i spr : bool
                                     then match splitDigit i pr with
                                            | Mk_Split l x r => Mk_Split (Data.Maybe.maybe Empty digitToTree l) x (deepL
                                                                                                                  r m
                                                                                                                  sf)
                                          end
                                     else if Nat.ltb i spm : bool
                                          then match splitTree im m with
                                                 | Mk_Split ml xs mr => match splitNode (im - size ml) xs with
                                                                          | Mk_Split l x r => Mk_Split (deepR pr ml l) x
                                                                                              (deepL r mr sf)
                                                                        end
                                               end
                                          else match splitDigit (i - spm) sf with
                                                 | Mk_Split l x r => Mk_Split (deepR pr m l) x (Data.Maybe.maybe Empty
                                                                                               digitToTree r)
                                               end
           end.

Definition split {a} : nat -> FingerTree (Elem a) -> (FingerTree (Elem a) * FingerTree (Elem a))%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | i , Empty => GHC.Prim.seq i (pair Empty Empty)
      | i , xs => if negb (Nat.leb (size xs) i) : bool
                  then match splitTree i xs with
                         | Mk_Split l x r => pair l (consTree x r)
                       end
                  else pair xs Empty
    end.

Definition splitAt {a} : nat -> Seq a -> (Seq a * Seq a)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | i , Mk_Seq xs => match split i xs with
                           | pair l r => pair (Mk_Seq l) (Mk_Seq r)
                         end
    end.

Definition breakr {a} : (a -> bool) -> Seq a -> (Seq a * Seq a)%type :=
  fun p xs =>
    let flipPair := fun arg_0__ => match arg_0__ with | pair x y => pair y x end in
    Data.Foldable.foldr (fun arg_3__ arg_4__ =>
                          match arg_3__ , arg_4__ with
                            | i , _ => flipPair (splitAt (i + id 1) xs)
                          end) (pair xs empty) (findIndicesR p xs).

Definition spanr {a} : (a -> bool) -> Seq a -> (Seq a * Seq a)%type :=
  fun p => breakr (negb GHC.Base.∘ p).

Definition dropWhileR {a} : (a -> bool) -> Seq a -> Seq a :=
  fun p => Data.Tuple.snd GHC.Base.∘ spanr p.

Definition takeWhileR {a} : (a -> bool) -> Seq a -> Seq a :=
  fun p => Data.Tuple.fst GHC.Base.∘ spanr p.

Definition breakl {a} : (a -> bool) -> Seq a -> (Seq a * Seq a)%type :=
  fun p xs =>
    Data.Foldable.foldr (fun arg_0__ arg_1__ =>
                          match arg_0__ , arg_1__ with
                            | i , _ => splitAt i xs
                          end) (pair xs empty) (findIndicesL p xs).

Definition spanl {a} : (a -> bool) -> Seq a -> (Seq a * Seq a)%type :=
  fun p => breakl (negb GHC.Base.∘ p).

Definition dropWhileL {a} : (a -> bool) -> Seq a -> Seq a :=
  fun p => Data.Tuple.snd GHC.Base.∘ spanl p.

Definition takeWhileL {a} : (a -> bool) -> Seq a -> Seq a :=
  fun p => Data.Tuple.fst GHC.Base.∘ spanl p.

Definition splitAt' {a} : nat -> Seq a -> (Seq a * Seq a)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | i , Mk_Seq xs => match split i xs with
                           | pair l r => pair (Mk_Seq l) (Mk_Seq r)
                         end
    end.

Definition drop {a} : nat -> Seq a -> Seq a :=
  fun i => Data.Tuple.snd GHC.Base.∘ splitAt' i.

Definition take {a} : nat -> Seq a -> Seq a :=
  fun i => Data.Tuple.fst GHC.Base.∘ splitAt' i.

Definition zipWith' {a} {b} {c} : (a -> b -> c) -> Seq a -> Seq b -> Seq c :=
  fun f s1 s2 => splitMap splitAt' (fun s a => f a (getSingleton s)) s2 s1.


Definition zipWith {a} {b} {c} : (a -> b -> c) -> Seq a -> Seq b -> Seq c :=
  fun f s1 s2 =>
    let minLen := min (length s1) (length s2) in
    let s1' := take minLen s1 in let s2' := take minLen s2 in zipWith' f s1' s2'.


(* chooses type instead of term for some reason *)
Definition zip {a} {b} : Seq a -> Seq b -> Seq (a * b)%type :=
  zipWith GHC.Tuple.pair2.


Definition minimum_ne {t: Type -> Type} `{Data.Foldable.Foldable t}
           (x : nat) (y : t nat) : nat :=
  Data.Foldable.foldr min x y.

Definition zipWith3 {a} {b} {c} {d} : (a -> b -> c -> d) -> Seq a -> Seq
                                      b -> Seq c -> Seq d :=
  fun f s1 s2 s3 =>
    let minLen :=
      minimum_ne (length s1) ((cons (length s2) (cons (length s3) nil))) in
    let s1' := take minLen s1 in
    let s2' := take minLen s2 in
    let s3' := take minLen s3 in zipWith' _GHC.Base.$_ (zipWith' f s1' s2') s3'.

Definition zip3 {a} {b} {c} : Seq a -> Seq b -> Seq c -> Seq (a * b * c)%type :=
  zipWith3 GHC.Tuple.pair3.

Definition zipWith3' {a} {b} {c} {d} : (a -> b -> c -> d) -> Seq a -> Seq
                                       b -> Seq c -> Seq d :=
  fun f s1 s2 s3 => zipWith' _GHC.Base.$_ (zipWith' f s1 s2) s3.

Definition zipWith4 {a} {b} {c} {d} {e} : (a -> b -> c -> d -> e) -> Seq
                                          a -> Seq b -> Seq c -> Seq d -> Seq e :=
  fun f s1 s2 s3 s4 =>
    let minLen :=
      minimum_ne (length s1) ((cons (length s2) (cons (length s3)
                                                                      (cons (length s4) nil)))) in
    let s1' := take minLen s1 in
    let s2' := take minLen s2 in
    let s3' := take minLen s3 in
    let s4' := take minLen s4 in
    zipWith' _GHC.Base.$_ (zipWith3' f s1' s2' s3') s4'.

Definition zip4 {a} {b} {c} {d} : Seq a -> Seq b -> Seq c -> Seq d -> Seq (a * b
                                                                          * c * d)%type :=
  zipWith4 GHC.Tuple.pair4.

Definition tailsDigit {a} : Digit a -> Digit (Digit a) :=
  fun arg_0__ =>
    match arg_0__ with
      | One a => One (One a)
      | Two a b => Two (Two a b) (One b)
      | Three a b c => Three (Three a b c) (Two b c) (One c)
      | Four a b c d => Four (Four a b c d) (Three b c d) (Two c d) (One d)
    end.

Definition tailsNode {a} : Node a -> Node (Digit a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Node2 s a b => Node2 s (Two a b) (One b)
      | Node3 s a b c => Node3 s (Three a b c) (Two b c) (One c)
    end.


Definition tailsTree : forall {a} {b} `{Sized a} (arg_0__ : FingerTree a -> b),
  FingerTree a -> FingerTree b :=
  fix tailsTree {a} {b} `{Sized a} arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Empty => Empty
             | f , Single x => Single (f (Single x))
             | f , Deep n pr m sf =>
               let f' :=
                   fun ms  =>
                     match viewLTree ms with
                     | Just2 node m' =>
                       GHC.Base.fmap (fun pr' => f (deep pr' m' sf)) (tailsNode node)
                     | Nothing2 => error
                     end in
               Deep n (GHC.Base.fmap (fun pr' => f (deep pr' m sf)) (tailsDigit pr))
                    (tailsTree f' m)
                    (GHC.Base.fmap (f GHC.Base.∘ digitToTree) (tailsDigit sf))
           end.

Definition tails {a} : Seq a -> Seq (Seq a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Seq xs => Mk_Seq (tailsTree (Mk_Elem GHC.Base.∘ Mk_Seq) xs) |> empty
    end.

Definition viewl {a} : Seq a -> ViewL a :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Seq xs => match viewLTree xs with
                       | Nothing2 => EmptyL
                       | Just2 (Mk_Elem x) xs' => x :< Mk_Seq xs'
                     end
    end.

Definition scanl1 {a} : (a -> a -> a) -> Seq a -> Seq a :=
  fun f xs =>
    match viewl xs with
      | EmptyL => error (GHC.Base.hs_string__
                        "scanl1 takes a nonempty sequence as an argument")
      | op_ZCzl__ x xs' => scanl f x xs'
    end.

Definition viewr {a} : Seq a -> ViewR a :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Seq xs => match viewRTree xs with
                       | Nothing2 => EmptyR
                       | Just2 xs' (Mk_Elem x) => Mk_Seq xs' :> x
                     end
    end.

Definition scanr1 {a} : (a -> a -> a) -> Seq a -> Seq a :=
  fun f xs =>
    match viewr xs with
      | EmptyR => error (GHC.Base.hs_string__
                        "scanr1 takes a nonempty sequence as an argument")
      | op_ZCzg__ xs' x => scanr f x xs'
    end.


Definition aptyMiddle {c} {d} {a} {b}
    (firstf : (c -> d)) (lastf : (c -> d)) (map23 : (a -> b) -> c -> d) (fs : FingerTree (Elem (a -> b))) (r : Rigid c)
   (* { measure (rigid_metric r)} *) : FingerTree (Node d) := error.

(*
  match r with
  | Mk_Rigid s pr (DeepTh sm prm mm sfm) sf => Deep
                                                (sm + (s * ((size fs) + 1)))
                                                (GHC.Base.fmap (@GHC.Base.fmap Digit23 _ _ _ firstf)
                                                               (digit12ToDigit prm))
                                                (aptyMiddle (GHC.Base.fmap firstf)
                                                            (GHC.Base.fmap lastf)
                                                            (GHC.Base.fmap GHC.Base.∘ map23)
                                                            fs (Mk_Rigid s (squashL pr prm) mm (squashR sfm sf)))
                                                (GHC.Base.fmap (GHC.Base.fmap lastf)
                                                               (digit12ToDigit sfm))
  | Mk_Rigid s pr EmptyTh sf =>
    let converted : Node (Digit23 c) := node2 pr sf in
    deep (One (GHC.Base.fmap firstf sf)) (mapMulFT
                                            s
                                            (fun arg_7__ =>
                                               match arg_7__ with
                                               | Mk_Elem f =>
                                                 @GHC.Base.fmap Node _ _ _
                                                   (@GHC.Base.fmap Digit23 _ _ _ (map23 f))
                                                   converted
                                               end) fs)
         (One (GHC.Base.fmap lastf pr))
  | Mk_Rigid s pr (SingleTh q) sf =>
    let converted : Node (Digit23 c) := node3 pr q sf in
    deep (Two (GHC.Base.fmap firstf q) (GHC.Base.fmap firstf sf))
         (mapMulFT s
                   (fun arg_12__ =>
                      match arg_12__ with
                      | Mk_Elem f => @GHC.Base.fmap Node _ _ _ (@GHC.Base.fmap Digit23 _ _ _ (map23 f))
                                      converted
                      end) fs) (Two (GHC.Base.fmap lastf pr)
                                    (GHC.Base.fmap lastf q))
  end. *)

Local Definition Applicative__Seq_op_zlztzg__ : forall {a} {b}, Seq (a -> b) -> Seq a -> Seq b := error.
(*
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | fs , (Mk_Seq xsFT as xs) =>
          match viewl fs with
          | EmptyL => empty
          | op_ZCzl__ firstf fs' =>
            match viewr fs' with
            | EmptyR => GHC.Base.fmap firstf xs
            | op_ZCzg__ (Mk_Seq fs''FT) lastf =>
              match rigidify xsFT with
              | RigidEmpty => empty
              | RigidOne (Mk_Elem x) => GHC.Base.fmap   (fun arg_6__ =>
                                                          arg_6__
                                                            GHC.Base.$
                                                            x) fs
              | RigidTwo (Mk_Elem x1) (Mk_Elem x2) =>
                Mk_Seq
                  GHC.Base.$
                  ap2FT
                  firstf
                  fs''FT
                  lastf (pair x1 x2)
              | RigidThree (Mk_Elem x1) (Mk_Elem x2) (Mk_Elem x3) =>
                Mk_Seq
                  GHC.Base.$
                  ap3FT
                  firstf
                  fs''FT
                  lastf (pair
                           (pair
                              x1
                              x2)
                           x3)
              | RigidFull (Mk_Rigid s pr _m sf as r) =>
                Mk_Seq
                  (Deep (s * length fs)
                        (GHC.Base.fmap (GHC.Base.fmap firstf) (nodeToDigit pr))
                        (aptyMiddle
                           (GHC.Base.fmap  firstf)
                           (GHC.Base.fmap  lastf)
                           GHC.Base.fmap  fs''FT r)
                        (GHC.Base.fmap (GHC.Base.fmap  lastf) (nodeToDigit sf)))
              end
            end
          end
      end. *)

Program Instance Applicative__Seq : GHC.Base.Applicative Seq := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Seq_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Seq_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__Seq_pure |}.

Local Definition Monad__Seq_op_zgzg__ : forall {a} {b},
                                          Seq a -> Seq b -> Seq b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Seq_return_ : forall {a}, a -> Seq a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Seq : GHC.Base.Monad Seq := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Seq_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Seq_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => Monad__Seq_return_ |}.

Module Notations.
Notation "'_Data.Sequence.<|_'" := (op_zlzb__).
Infix "Data.Sequence.<|" := (_<|_) (at level 99).
Notation "'_Data.Sequence.|>_'" := (op_zbzg__).
Infix "Data.Sequence.|>" := (_|>_) (at level 99).
Notation "'_Data.Sequence.><_'" := (op_zgzl__).
Infix "Data.Sequence.><" := (_><_) (at level 99).
End Notations.
