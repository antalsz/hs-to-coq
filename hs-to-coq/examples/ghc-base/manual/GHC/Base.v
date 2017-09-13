Require Export GHC.BaseGen.

Set Implicit Arguments.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Instance Eq_option {a} `{Eq_ a} : !Eq_ (option a) := {
   op_zsze__ := fun x y =>
                  match x,y with
                  | Some x0, Some y0 => x0 == y0
                  | None, None => true
                  | _,_ => false
                  end ;
   op_zeze__ := fun x y =>
                  match x,y with
                  | Some x0, Some y0 => x0 /= y0
                  | None, None => false
                  | _,_ => true
                  end
}.

Instance Ord_option {a} `{Ord a} : !Ord (option a). Admitted.

Instance Functor_option     : !Functor option. Admitted.
Instance Applicative_option : !Applicative option. Admitted.
Instance Monad_option       : !Monad option. Admitted.
Instance Alternative_option : !Alternative option. Admitted.
Instance MonadPlus_option   : !MonadPlus option := {}.

Instance Monoid_list {a} `{Monoid a} : !Monoid (list a). Admitted.
(* Still missing many monoid instances *)

Instance Functor_list     : !Functor list. Admitted.
Instance Applicative_list : !Applicative list. Admitted.
Instance Monad_list       : !Monad list. Admitted.
Instance Alternative_list : !Alternative list. Admitted.
Instance MonadPlus_list   : !MonadPlus list := {}.

Instance Functor_IO     : !Functor IO. Admitted.
Instance Applicative_IO : !Applicative IO. Admitted.
Instance Monad_IO       : !Monad IO. Admitted.
Instance Alternative_IO : !Alternative IO. Admitted.
Instance MonadPlus_IO   : !MonadPlus IO. Admitted.
