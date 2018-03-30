Definition NonEmpty_foldr1 {a} (f : a -> a -> a) (x: GHC.Base.NonEmpty a) : a :=
  match x with 
    | GHC.Base.NEcons a as_ => List.fold_right f a as_
  end.

Definition NonEmpty_maximum {a} `{GHC.Base.Ord a} (x:GHC.Base.NonEmpty a) : a :=
  NonEmpty_foldr1 GHC.Base.max x.

Definition NonEmpty_minimum {a} `{GHC.Base.Ord a} (x:GHC.Base.NonEmpty a) : a :=
  NonEmpty_foldr1 GHC.Base.min x.

Definition toList {a} : GHC.Base.NonEmpty a -> list a :=
  fun arg_0__ => match arg_0__ with | GHC.Base.NEcons a as_ => cons a as_ end.


Definition List_size {a} : list a -> nat :=
List.fold_right (fun x y => S y) O .
Definition NonEmpty_size {a} : GHC.Base.NonEmpty a -> nat :=
  fun arg_0__ =>
    match arg_0__ with
      | GHC.Base.NEcons _ xs => 1 + List_size xs
    end.

Program Fixpoint insertBy {a} (cmp: a -> a -> comparison) (x : a)
        (xs : GHC.Base.NonEmpty a) {measure (NonEmpty_size xs)} : GHC.Base.NonEmpty a :=
  match xs with
  | GHC.Base.NEcons x nil => GHC.Base.NEcons x nil
  | (GHC.Base.NEcons y ((cons y1 ys') as ys)) => 
    match cmp x y with
    | Gt  => GHC.Base.NEcons y (toList (insertBy cmp x (GHC.Base.NEcons y1 ys')))
    | _   => GHC.Base.NEcons x ys
    end
  end.

Program Fixpoint insertBy' {a} (cmp: a -> a -> comparison) (x : a)
        (xs : list a) {measure (List_size xs)} : GHC.Base.NonEmpty a :=
  match xs with
  | nil => GHC.Base.NEcons x nil
  | cons x nil => GHC.Base.NEcons x nil
  | (cons y ((cons y1 ys') as ys)) => 
    match cmp x y with
    | Gt  => GHC.Base.NEcons y (toList (insertBy' cmp x (cons y1 ys')))
    | _   => GHC.Base.NEcons x ys
    end
  end.


Definition insert {a} `{GHC.Base.Ord a} : a ->  GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
  insertBy GHC.Base.compare.

Definition sortBy {a} : (a -> a -> comparison) -> GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
  fun f ne => match ne with
           | GHC.Base.NEcons x xs => insertBy' f x (Data.OldList.sortBy f xs)
           end.

Definition sort {a} `{GHC.Base.Ord a} : GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
             sortBy GHC.Base.compare.


