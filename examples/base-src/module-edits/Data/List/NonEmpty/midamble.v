Definition NonEmpty_foldr1 {a} (f : a -> a -> a) (x: NonEmpty a) : a :=
  match x with 
    | NEcons a as_ => List.fold_right f a as_
  end.

Definition NonEmpty_maximum {a} `{GHC.Base.Ord a} (x:NonEmpty a) : a :=
  NonEmpty_foldr1 GHC.Base.max x.

Definition NonEmpty_minimum {a} `{GHC.Base.Ord a} (x:NonEmpty a) : a :=
  NonEmpty_foldr1 GHC.Base.min x.

Definition toList {a} : NonEmpty a -> list a :=
  fun arg_0__ => match arg_0__ with | NEcons a as_ => cons a as_ end.


Definition List_size {a} : list a -> nat :=
List.fold_right (fun x y => S y) O .
Definition NonEmpty_size {a} : NonEmpty a -> nat :=
  fun arg_0__ =>
    match arg_0__ with
      | NEcons _ xs => 1 + List_size xs
    end.

Program Fixpoint insertBy {a} (cmp: a -> a -> comparison) (x : a)
        (xs : NonEmpty a) {measure (NonEmpty_size xs)} : NonEmpty a :=
  match xs with
  | NEcons x nil => NEcons x nil
  | (NEcons y ((cons y1 ys') as ys)) => 
    match cmp x y with
    | Gt  => NEcons y (toList (insertBy cmp x (NEcons y1 ys')))
    | _   => NEcons x ys
    end
  end.

Program Fixpoint insertBy' {a} (cmp: a -> a -> comparison) (x : a)
        (xs : list a) {measure (List_size xs)} : NonEmpty a :=
  match xs with
  | nil => NEcons x nil
  | cons x nil => NEcons x nil
  | (cons y ((cons y1 ys') as ys)) => 
    match cmp x y with
    | Gt  => NEcons y (toList (insertBy' cmp x (cons y1 ys')))
    | _   => NEcons x ys
    end
  end.


Definition insert {a} `{GHC.Base.Ord a} : a ->  NonEmpty a -> NonEmpty a :=
  insertBy GHC.Base.compare.

Definition sortBy {a} : (a -> a -> comparison) -> NonEmpty a -> NonEmpty a :=
  fun f ne => match ne with
           | NEcons x xs => insertBy' f x (Data.OldList.sortBy f xs)
           end.

Definition sort {a} `{GHC.Base.Ord a} : NonEmpty a -> NonEmpty a :=
             sortBy GHC.Base.compare.


