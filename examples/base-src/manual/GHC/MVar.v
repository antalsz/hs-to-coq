Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require Import GHC.IO.
Require Import GHC.Num.

Class Encodable A :=
  { encode : A -> Word;
    decode : Word -> option A }.

Instance encodable_for_all : forall A : Type, Encodable A.
Proof.
  intros. constructor.
  - exact (fun _ => #0).
  - exact (fun _ => None).
Qed.

Inductive MVar (A : Type) `{Encodable A} :=
| MkMV (loc : Word).

Arguments MkMV {_} {_}.

(** Atomic primitives. *)
Inductive MemEff: Type -> Type :=
| NewMV {A} : MemEff (MVar A)
| TakeMV {A} : MVar A -> MemEff A
| ReadMV {A} : MVar A -> MemEff A
| PutMV {A} : MVar A -> A -> MemEff unit
| TryTakeMV {A} : MVar A -> MemEff (option A)
| TryReadMV {A} : MVar A -> MemEff (option A)
| TryPutMV {A} : MVar A -> A -> MemEff bool
| IsEmptyMV {A} : MVar A -> MemEff bool.

Definition IO : Type -> Type := Freer MemEff.

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
