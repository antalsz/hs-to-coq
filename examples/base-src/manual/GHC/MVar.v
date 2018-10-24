Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Inductive Freer (E : Type -> Type) (R : Type) :=
| Ret (r : R)
| Vis (X : Type) (e : E X) (k : X -> Freer E R).

Arguments Ret {_} {_}.
Arguments Vis {_} {_} {_}.

Fixpoint bind {E X Y} (a : Freer E X) (f : X -> Freer E Y) : Freer E Y :=
  match a with
  | Ret x => f x
  | Vis e k => Vis e (fun x => bind (k x) f)
  end.

Definition ret {E X} (a : X) : Freer E X := Ret a.

Definition vis {E X} (m: E X) : Freer E X := Vis m (fun x => Ret x).

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
