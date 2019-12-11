Require GHC.Err.

Definition complement' x :=
  Coq.NArith.BinNat.N.lxor x (Coq.NArith.BinNat.N.ones (#64%N)).

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
