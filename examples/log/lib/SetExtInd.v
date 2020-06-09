(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(* Converted imports: *)

Require GHC.Base.
Require MySet.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Set Printing Universes.

Inductive FreerF e r : Type := | FMap {x} : (x -> r) -> (e x) -> FreerF e r.

Inductive SetMethod : Type -> Type
  := | Empty : forall {a}, SetMethod a
  |  Singleton : forall {a}, a -> SetMethod a
  |  Add
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> FreerF SetMethod a -> SetMethod a
  |  Union
   : forall {a},
     forall `{GHC.Base.Eq_ a},
     FreerF SetMethod a -> FreerF SetMethod a -> SetMethod a
  |  PowerSet
   : forall {a},
     forall `{GHC.Base.Eq_ a}, FreerF SetMethod a -> SetMethod (MySet.Set_ a).

Definition SetExt :=
  (FreerF SetMethod)%type.

Arguments FMap {_} {_} {_} _ _.

Local Definition Functor__FreerF_fmap {inst_e}
   : forall {a} {b}, (a -> b) -> (FreerF inst_e) a -> (FreerF inst_e) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, FMap g x => FMap (f GHC.Base.∘ g) x
      end.

Local Definition Functor__FreerF_op_zlzd__ {inst_e}
   : forall {a} {b}, a -> (FreerF inst_e) b -> (FreerF inst_e) a :=
  fun {a} {b} => Functor__FreerF_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__FreerF {e} : GHC.Base.Functor (FreerF e) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__FreerF_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__FreerF_op_zlzd__ |}.

(* Converted value declarations: *)

Definition union {a} `{GHC.Base.Eq_ a} : SetExt a -> SetExt a -> SetExt a :=
  fun s1 => FMap GHC.Base.id GHC.Base.∘ Union s1.

Definition singleton {a} : a -> SetExt a :=
  FMap GHC.Base.id GHC.Base.∘ Singleton.

Section FreerFId.
  Universes a1 b1 c1 a2 b2 c2.
  Universes i1 j1 k1 l1 m1 n1 o1 i2 j2 k2 l2 m2 n2 o2.
  Variable a : Type.

  Definition freerFId : FreerF@{a1 b1 c1} SetMethod@{i1 j1 k1 l1 m1 n1} a ->
                        FreerF@{a2 b2 c2} SetMethod@{i2 j2 k2 l2 m2 n2} a.
    destruct 1.
    apply (@FMap SetMethod@{i2 j2 k2 l2 m2 n2} a x a0 s).
  Defined.
End FreerFId.

Arguments freerFId {_}.

Definition empty {a} : SetExt a :=
  FMap GHC.Base.id Empty.

Definition add {a} `{GHC.Base.Eq_ a} : a -> SetExt a -> SetExt a :=
  fun a => FMap GHC.Base.id GHC.Base.∘ Add a.

Definition reify_set {a} `{GHC.Base.Eq_ a} : MySet.Set_ a -> SetExt a :=
  fun s =>
    let go {a} `{GHC.Base.Eq_ a} : list a -> SetExt a :=
      fix go (arg_0__ : list a) : SetExt a
            := match arg_0__ with
               | nil => empty
               | cons x xs => add x (go xs)
               end in
    go (MySet.toList s).

Definition powerSet {a} `{GHC.Base.Eq_ a} : SetExt a -> SetExt (SetExt a) :=
  FMap reify_set GHC.Base.∘ PowerSet.

Fixpoint SetExtSize {a} (s : SetExt a) : nat :=
  match s with
  | FMap f Empty => 0
  | FMap f (Singleton a) => 0
  | FMap f (Add a s) => SetExtSize s + 1
  | FMap f (Union s1 s2) => SetExtSize s1 + SetExtSize s2
  | _ => 1
  end.

Fixpoint reflect_set {a} `{GHC.Base.Eq_ a} (arg_0__ : SetExt a) : MySet.Set_ a.
  destruct arg_0__, s.
  - exact (MySet.empty).
  - exact (MySet.singleton (a0 a2)).
  - exact (MySet.add (a0 a2) (reflect_set _ _ (GHC.Base.fmap a0 f))).
  - exact (MySet.union (reflect_set _ _ (GHC.Base.fmap a0 f)) (reflect_set _ _ (GHC.Base.fmap a0 f0))).
  - exact (GHC.Base.fmap a0 (MySet.powerSet (reflect_set _ _ f))).
    Show Proof.
Defined.
    pose (MySet.powerSet (reflect_set _ _ f)).
    
    pose (MySet.powerSet (reflect_set _ _ f0)).
    pose (GHC.Base.fmap reify_set s).
    pose (GHC.Base.fmap f
 s0).
    pose (a0 GHC.Base.∘ (f GHC.Base.∘ reify_set)).
    exact (GHC.Base.fmap (a0 GHC.Base.∘ (f GHC.Base.∘ reify_set)) (MySet.powerSet (reflect_set _ _ f0))).
       match arg_0__ with
   | FMap a0 s =>
       match s in (SetMethod T) return ((T -> a) -> MySet.Set_ a) with

           := match arg_0__ with
              | FMap f Empty => MySet.empty
              | FMap f (Singleton a) => MySet.singleton (f a)
              | FMap f (Add a s) => MySet.add (f a) (reflect_set (GHC.Base.fmap f s))
              | FMap f (Union s1 s2) =>
                  MySet.union (reflect_set (GHC.Base.fmap f s1)) (reflect_set (GHC.Base.fmap f
                                                                                             s2))
              | FMap f (PowerSet k s) =>
                  GHC.Base.fmap (f GHC.Base.∘ (k GHC.Base.∘ reify_set)) (MySet.powerSet (reflect_set s))
              end.

Definition member {a} `{GHC.Base.Eq_ a} : a -> SetExt a -> bool :=
  fun a s => MySet.member a (reflect_set s).

(* External variables:
     Type bool cons list nil GHC.Base.Eq_ GHC.Base.Functor GHC.Base.const
     GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.op_z2218U__
     GHC.Base.op_zlzd____ MySet.Set_ MySet.add MySet.empty MySet.member
     MySet.powerSet MySet.singleton MySet.toList MySet.union
*)
