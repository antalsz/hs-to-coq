Fixpoint length {a} (xs : list a) : Int :=
  match xs with 
  | nil => # 0
  | cons _ ys => (1 + (length ys))%Z
  end.
