Definition NonEmpty_foldr1 {a} (f : a -> a -> a) (x: Data.List.NonEmpty.NonEmpty a) : a :=
  match x with 
    | Data.List.NonEmpty.NEcons a as_ => List.fold_right f a as_
  end.

