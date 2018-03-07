Require Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Fixpoint map_size {a} {b} (s : Map a b) : nat :=
  match s with
  | Tip => 0
  | Bin _ _ _ s1 s2 => 1 + map_size s1 + map_size s2
  end.

Require Import GHC.Err.

Instance Map_Default {k}{v} : Default (Map k v) :=
  Build_Default _ Tip.
Instance AlteredDefault {k}{v} : Default (Altered k v) :=
  Build_Default _ AltSame.

(* This doesn't translate automatically for two reasons:
   it should be a fixpoint.
   it reuses the variable a as both a term and type variable. *)
Fixpoint functor__Map_op_zlzd__ {inst_k} {a} {b} (f: a) (m:(Map inst_k) b):
  (Map inst_k) a :=
      match f, m with
      | _, Tip => Tip
      | f, Bin sx kx _ l r => Bin sx kx f
                                 (functor__Map_op_zlzd__ f l) 
                                 (functor__Map_op_zlzd__ f r)
      end.
