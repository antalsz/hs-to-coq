Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require Import GHC.IO.

Inductive MVar a :=
| MkMV (v : a).

Arguments MkMV {_}.

(** Atomic primitives. *)
Inductive MemEff: Type -> Type :=
| NewMV {a} : MemEff (MVar a)
| TakeMV {a} : MVar a -> MemEff a
| ReadMV {a} : MVar a -> MemEff a
| PutMV {a} : MVar a -> a -> MemEff unit
| TryTakeMV {a} : MVar a -> MemEff (option a)
| TryReadMV {a} : MVar a -> MemEff (option a)
| TryPutMV {a} : MVar a -> a -> MemEff bool
| IsEmptyMV {a} : MVar a -> MemEff bool.

Definition IO := Freer MemEff.

(** TODO: the [Eq] instance of [MVar] *)

Definition newEmptyMVar {a} : IO (MVar a) := vis NewMV.

Definition takeMVar {a} (m : MVar a) : IO a := vis (TakeMV m).

Definition readMVar {a} (m : MVar a) : IO a := vis (ReadMV m).

Definition putMVar {a} (m : MVar a) (v : a) : IO unit := vis (PutMV m v).
                          
Definition newMVar {a} (value : a) : IO (MVar a) :=
  bind newEmptyMVar
       (fun mvar => (bind (putMVar mvar value) (fun _ => ret mvar))).

Definition tryTakeMVar {a} (m : MVar a) : IO (option a) := vis (TryTakeMV m).

Definition tryReadMVar {a} (m : MVar a) : IO (option a) := vis (TryReadMV m).

Definition tryPutMVar {a} (m : MVar a) (v : a) : IO bool := vis (TryPutMV m v).

Definition isEmptyMVar {a} (m : MVar a) : IO bool := vis (IsEmptyMV m).

(** TODO: [addMVarFinalizer] (does not seem important for now). *)

Instance functor_io : GHC.Base.Functor IO := @Functor__IO MemEff.
Instance applicative_io : GHC.Base.Applicative IO := @Applicative__IO MemEff.
Instance monad_io : GHC.Base.Monad IO := @Monad__IO MemEff.

Definition evaluate {a} : a -> IO a := @GHC.IO.evaluate MemEff a.
