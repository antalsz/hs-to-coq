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
Require Data.Foldable.
Require GHC.Base.

(* Converted type declarations: *)

Inductive OrdList a : Type := None : OrdList a
                           |  One : a -> OrdList a
                           |  Many : list a -> OrdList a
                           |  Cons : a -> (OrdList a) -> OrdList a
                           |  Snoc : (OrdList a) -> a -> OrdList a
                           |  Two : (OrdList a) -> (OrdList a) -> OrdList a.

Arguments None {_}.

Arguments One {_} _.

Arguments Many {_} _.

Arguments Cons {_} _ _.

Arguments Snoc {_} _ _.

Arguments Two {_} _ _.
(* Converted value declarations: *)

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (OrdList.OrdList a)' failed: OOPS! Cannot find information
   for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance forall {a}, Data.Semigroup.Semigroup (OrdList.OrdList
   a)' failed: OOPS! Cannot find information for class Qualified "Data.Semigroup"
   "Semigroup" unsupported *)

Definition appOL {a} : OrdList a -> OrdList a -> OrdList a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
    | None , b => b
    | a , None => a
    | One a , b => Cons a b
    | a , One b => Snoc a b
    | a , b => Two a b
    end.

Definition concatOL {a} : list (OrdList a) -> OrdList a :=
  fun aas => Data.Foldable.foldr appOL None aas.

Local Definition Monoid__OrdList_mconcat {inst_a} : list (OrdList
                                                         inst_a) -> (OrdList inst_a) :=
  concatOL.

Local Definition Monoid__OrdList_mappend {inst_a} : (OrdList inst_a) -> (OrdList
                                                    inst_a) -> (OrdList inst_a) :=
  appOL.

Definition consOL {a} : a -> OrdList a -> OrdList a :=
  fun a bs => Cons a bs.

Definition foldlOL {b} {a} : (b -> a -> b) -> b -> OrdList a -> b :=
  fix foldlOL arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
           | _ , z , None => z
           | k , z , One x => k z x
           | k , z , Cons x xs => foldlOL k (k z x) xs
           | k , z , Snoc xs x => k (foldlOL k z xs) x
           | k , z , Two b1 b2 => foldlOL k (foldlOL k z b1) b2
           | k , z , Many xs => Data.Foldable.foldl k z xs
           end.

Definition foldrOL {a} {b} : (a -> b -> b) -> b -> OrdList a -> b :=
  fix foldrOL arg_0__ arg_1__ arg_2__
        := match arg_0__ , arg_1__ , arg_2__ with
           | _ , z , None => z
           | k , z , One x => k x z
           | k , z , Cons x xs => k x (foldrOL k z xs)
           | k , z , Snoc xs x => foldrOL k (k x z) xs
           | k , z , Two b1 b2 => foldrOL k (foldrOL k z b2) b1
           | k , z , Many xs => Data.Foldable.foldr k z xs
           end.

Definition fromOL {a} : OrdList a -> list a :=
  fun a =>
    let fix go arg_0__ arg_1__
              := match arg_0__ , arg_1__ with
                 | None , acc => acc
                 | One a , acc => cons a acc
                 | Cons a b , acc => cons a (go b acc)
                 | Snoc a b , acc => go a (cons b acc)
                 | Two a b , acc => go a (go b acc)
                 | Many xs , acc => Coq.Init.Datatypes.app xs acc
                 end in
    go a nil.

Definition isNilOL {a} : OrdList a -> bool :=
  fun arg_0__ => match arg_0__ with | None => true | _ => false end.

Definition mapOL {a} {b} : (a -> b) -> OrdList a -> OrdList b :=
  fix mapOL arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
           | _ , None => None
           | f , One x => One (f x)
           | f , Cons x xs => Cons (f x) (mapOL f xs)
           | f , Snoc xs x => Snoc (mapOL f xs) (f x)
           | f , Two x y => Two (mapOL f x) (mapOL f y)
           | f , Many xs => Many (GHC.Base.map f xs)
           end.

Local Definition Functor__OrdList_fmap : forall {a} {b},
                                           (a -> b) -> OrdList a -> OrdList b :=
  fun {a} {b} => mapOL.

Local Definition Functor__OrdList_op_zlzd__ : forall {a} {b},
                                                a -> OrdList b -> OrdList a :=
  fun {a} {b} => fun x => Functor__OrdList_fmap (GHC.Base.const x).

Program Instance Functor__OrdList : GHC.Base.Functor OrdList := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__OrdList_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__OrdList_fmap |}.
Admit Obligations.

Definition nilOL {a} : OrdList a :=
  None.

Local Definition Monoid__OrdList_mempty {inst_a} : (OrdList inst_a) :=
  nilOL.

Program Instance Monoid__OrdList {a} : GHC.Base.Monoid (OrdList a) := fun _ k =>
    k {|GHC.Base.mappend__ := Monoid__OrdList_mappend ;
      GHC.Base.mconcat__ := Monoid__OrdList_mconcat ;
      GHC.Base.mempty__ := Monoid__OrdList_mempty |}.
Admit Obligations.

Definition snocOL {a} : OrdList a -> a -> OrdList a :=
  fun as_ b => Snoc as_ b.

Definition toOL {a} : list a -> OrdList a :=
  fun arg_0__ => match arg_0__ with | nil => None | xs => Many xs end.

Definition unitOL {a} : a -> OrdList a :=
  fun as_ => One as_.

(* Unbound variables:
     bool cons false list nil true Coq.Init.Datatypes.app Data.Foldable.foldl
     Data.Foldable.foldr GHC.Base.Functor GHC.Base.Monoid GHC.Base.const GHC.Base.map
*)
