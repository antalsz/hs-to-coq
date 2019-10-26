(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.

(* Converted type declarations: *)

Record MonadTrans__Dict t := MonadTrans__Dict_Build {
  lift__ : forall {m} {a}, forall `{(GHC.Base.Monad m)}, m a -> t m a }.

Definition MonadTrans t :=
  forall r__, (MonadTrans__Dict t -> r__) -> r__.
Existing Class MonadTrans.

Definition lift `{g__0__ : MonadTrans t}
   : forall {m} {a}, forall `{(GHC.Base.Monad m)}, m a -> t m a :=
  g__0__ _ (lift__ t).

(* No value declarations to convert. *)

(* External variables:
     GHC.Base.Monad
*)
