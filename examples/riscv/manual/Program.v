Require Import riscv.util.NameWithEq.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.

Inductive AccessType: Set := Instr | Load | Store.

Section Riscv.

  (* monad (will be instantiated with some kind of state monad) *)
  Context {M: Type -> Type}.
  Context {MM: Monad M}.

  (* type of register values *)
  Context {t: Set}.

  (* provides operations on t *)
  Context {MW: MachineWidth t}.

  Class RiscvProgram := mkRiscvProgram {
    getRegister: Register -> M t;
    setRegister: Register -> t -> M unit;

    loadByte: t -> M (word 8);
    loadHalf: t -> M (word 16);
    loadWord: t -> M (word 32);
    loadDouble: t -> M (word 64);

    storeByte: t -> word 8 -> M unit;
    storeHalf: t -> word 16 -> M unit;
    storeWord: t -> word 32 -> M unit;
    storeDouble: t -> word 64 -> M unit;

    getPC: M t;
    setPC: t -> M unit;

    (* TODO support all get/setCSRField, this one is just for the exception handler address *)
    getCSRField_MTVecBase: M MachineInt;

    step: M unit; (* updates PC *)

    endCycle: forall {A}, M A;
  }.


  (* The Haskell spec defines concrete implementations for raiseException and translate,
     but we prefer to leave them abstract, so that we can prove more general theorems *)
  Class RiscvState{MP: RiscvProgram} := mkRiscvState {
    (* ends current cycle, sets exception flag, and sets PC to exception handler address *)
    raiseException{A: Type}(isInterrupt: t)(exceptionCode: t): M A;

    (* checks that addr is aligned, and translates the (possibly virtual) addr to a physical
       address, raising an exception if the address is invalid *)
    translate(accessType: AccessType)(alignment: t)(addr: t): M t;
  }.

  Definition default_raiseException{A: Type}{MP: RiscvProgram}
    (isInterrupt: t)(exceptionCode: t): M A :=
    pc <- getPC;
    addr <- getCSRField_MTVecBase;
    setPC (fromImm (addr * 4)%Z);;
    endCycle.


  Local Open Scope alu_scope.
  Local Open Scope Z_scope.

  (* in a system with virtual memory, this would also do the translation, but in our
     case, we only verify the alignment *)
  Definition default_translate{MP: RiscvProgram}
    (accessType: AccessType)(alignment: t)(addr: t): M t :=
    if rem addr alignment /= zero
    then default_raiseException zero four
    else Return addr.

  Instance DefaultRiscvState{MP: RiscvProgram}: RiscvState := {|
    raiseException A := default_raiseException;
    translate := default_translate;
  |}.

End Riscv.

Arguments RiscvProgram (M) (t).
Arguments RiscvState (M) (t) {MP}.
