Require GHC.Err.

Instance Default_Map {a} : Err.Default (IntMap a) := {| Err.default := Nil |}.

Fixpoint IntMap_op_zlzd__ {a} {b} (x: a) (m: IntMap b): IntMap a :=
      match x , m with
        | a , Bin p m l r => Bin p m (IntMap_op_zlzd__ a l)
                                (IntMap_op_zlzd__ a r)
        | a , Tip k _ => Tip k a
        | _ , Nil => Nil
      end.
