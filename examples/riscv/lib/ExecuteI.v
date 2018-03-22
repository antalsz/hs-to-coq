(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Utility.
Local Open Scope alu_scope.

(* Converted imports: *)

Require Decode.
Require Monads.
Require Program.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition execute {p} {t} `{(Program.RiscvProgram p t)}
   : Decode.InstructionI -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Decode.Lui rd imm20 => Program.setRegister rd (Utility.fromImm imm20)
    | Decode.Auipc rd oimm20 =>
        Monads.Bind Program.getPC (fun pc =>
                       Program.setRegister rd (Coq.ZArith.BinInt.Z.add (Utility.fromImm oimm20) pc))
    | Decode.Jal rd jimm20 =>
        Monads.Bind Program.getPC (fun pc =>
                       let newPC := Coq.ZArith.BinInt.Z.add pc (Utility.fromImm jimm20) in
                       if (Coq.ZArith.BinInt.Z.modulo newPC 4 /= 0) : bool
                       then Program.raiseException 0 0
                       else (Monads.Bind (Program.setRegister rd (Coq.ZArith.BinInt.Z.add pc 4))
                                         (fun _ => Program.setPC newPC)))
    | Decode.Jalr rd rs1 oimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind Program.getPC (fun pc =>
                                      let newPC :=
                                        Coq.ZArith.BinInt.Z.land (Coq.ZArith.BinInt.Z.add x (Utility.fromImm oimm12))
                                                                 (Coq.ZArith.BinInt.Z.lnot 1) in
                                      if (Coq.ZArith.BinInt.Z.modulo newPC 4 /= 0) : bool
                                      then Program.raiseException 0 0
                                      else (Monads.Bind (Program.setRegister rd (Coq.ZArith.BinInt.Z.add pc 4))
                                                        (fun _ => Program.setPC newPC))))
    | Decode.Beq rs1 rs2 sbimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Monads.Bind Program.getPC (fun pc =>
                                                     Utility.when (Utility.signed_eqb x y) (let newPC :=
                                                                                              (Coq.ZArith.BinInt.Z.add
                                                                                               pc (Utility.fromImm
                                                                                                sbimm12)) in
                                                                                            if (Coq.ZArith.BinInt.Z.modulo
                                                                                                newPC 4 /=
                                                                                                0) : bool
                                                                                            then Program.raiseException
                                                                                                 0 0
                                                                                            else Program.setPC newPC))))
    | Decode.Bne rs1 rs2 sbimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Monads.Bind Program.getPC (fun pc =>
                                                     Utility.when (x /= y) (let addr :=
                                                                              (Coq.ZArith.BinInt.Z.add pc
                                                                                                       (Utility.fromImm
                                                                                                        sbimm12)) in
                                                                            if (Coq.ZArith.BinInt.Z.modulo addr 4 /=
                                                                                0) : bool
                                                                            then Program.raiseException 0 0
                                                                            else Program.setPC addr))))
    | Decode.Blt rs1 rs2 sbimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Monads.Bind Program.getPC (fun pc =>
                                                     Utility.when (x < y) (let addr :=
                                                                             (Coq.ZArith.BinInt.Z.add pc
                                                                                                      (Utility.fromImm
                                                                                                       sbimm12)) in
                                                                           if (Coq.ZArith.BinInt.Z.modulo addr 4 /=
                                                                               0) : bool
                                                                           then Program.raiseException 0 0
                                                                           else Program.setPC addr))))
    | Decode.Bge rs1 rs2 sbimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Monads.Bind Program.getPC (fun pc =>
                                                     Utility.when (x >= y) (let addr :=
                                                                              (Coq.ZArith.BinInt.Z.add pc
                                                                                                       (Utility.fromImm
                                                                                                        sbimm12)) in
                                                                            if (Coq.ZArith.BinInt.Z.modulo addr 4 /=
                                                                                0) : bool
                                                                            then Program.raiseException 0 0
                                                                            else Program.setPC addr))))
    | Decode.Bltu rs1 rs2 sbimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Monads.Bind Program.getPC (fun pc =>
                                                     Utility.when ((Utility.ltu x y)) (let addr :=
                                                                                         (Coq.ZArith.BinInt.Z.add pc
                                                                                                                  (Utility.fromImm
                                                                                                                   sbimm12)) in
                                                                                       if (Coq.ZArith.BinInt.Z.modulo
                                                                                           addr 4 /=
                                                                                           0) : bool
                                                                                       then Program.raiseException 0 0
                                                                                       else Program.setPC addr))))
    | Decode.Bgeu rs1 rs2 sbimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Monads.Bind Program.getPC (fun pc =>
                                                     Utility.when (negb (Utility.ltu x y)) (let addr :=
                                                                                              (Coq.ZArith.BinInt.Z.add
                                                                                               pc (Utility.fromImm
                                                                                                sbimm12)) in
                                                                                            if (Coq.ZArith.BinInt.Z.modulo
                                                                                                addr 4 /=
                                                                                                0) : bool
                                                                                            then Program.raiseException
                                                                                                 0 0
                                                                                            else Program.setPC addr))))
    | Decode.Lb rd rs1 oimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun a =>
                       Monads.Bind (Program.translate Program.Load 1 (Coq.ZArith.BinInt.Z.add a
                                                                                              (Utility.fromImm oimm12)))
                                   (fun addr =>
                                      Monads.Bind (Program.loadByte addr) (fun x =>
                                                     Program.setRegister rd (Utility.int8ToReg x))))
    | Decode.Lh rd rs1 oimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun a =>
                       Monads.Bind (Program.translate Program.Load 2 (Coq.ZArith.BinInt.Z.add a
                                                                                              (Utility.fromImm oimm12)))
                                   (fun addr =>
                                      Monads.Bind (Program.loadHalf addr) (fun x =>
                                                     Program.setRegister rd (Utility.int16ToReg x))))
    | Decode.Lw rd rs1 oimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun a =>
                       Monads.Bind (Program.translate Program.Load 4 (Coq.ZArith.BinInt.Z.add a
                                                                                              (Utility.fromImm oimm12)))
                                   (fun addr =>
                                      Monads.Bind (Program.loadWord addr) (fun x =>
                                                     Program.setRegister rd (Utility.int32ToReg x))))
    | Decode.Lbu rd rs1 oimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun a =>
                       Monads.Bind (Program.translate Program.Load 1 (Coq.ZArith.BinInt.Z.add a
                                                                                              (Utility.fromImm oimm12)))
                                   (fun addr =>
                                      Monads.Bind (Program.loadByte addr) (fun x =>
                                                     Program.setRegister rd (Utility.uInt8ToReg x))))
    | Decode.Lhu rd rs1 oimm12 =>
        Monads.Bind (Program.getRegister rs1) (fun a =>
                       Monads.Bind (Program.translate Program.Load 2 (Coq.ZArith.BinInt.Z.add a
                                                                                              (Utility.fromImm oimm12)))
                                   (fun addr =>
                                      Monads.Bind (Program.loadHalf addr) (fun x =>
                                                     Program.setRegister rd (Utility.uInt16ToReg x))))
    | Decode.Sb rs1 rs2 simm12 =>
        Monads.Bind (Program.getRegister rs1) (fun a =>
                       Monads.Bind (Program.translate Program.Store 1 (Coq.ZArith.BinInt.Z.add a
                                                                                               (Utility.fromImm
                                                                                                simm12))) (fun addr =>
                                      Monads.Bind (Program.getRegister rs2) (fun x =>
                                                     Program.storeByte addr (Utility.regToInt8 x))))
    | Decode.Sh rs1 rs2 simm12 =>
        Monads.Bind (Program.getRegister rs1) (fun a =>
                       Monads.Bind (Program.translate Program.Store 2 (Coq.ZArith.BinInt.Z.add a
                                                                                               (Utility.fromImm
                                                                                                simm12))) (fun addr =>
                                      Monads.Bind (Program.getRegister rs2) (fun x =>
                                                     Program.storeHalf addr (Utility.regToInt16 x))))
    | Decode.Sw rs1 rs2 simm12 =>
        Monads.Bind (Program.getRegister rs1) (fun a =>
                       Monads.Bind (Program.translate Program.Store 4 (Coq.ZArith.BinInt.Z.add a
                                                                                               (Utility.fromImm
                                                                                                simm12))) (fun addr =>
                                      Monads.Bind (Program.getRegister rs2) (fun x =>
                                                     Program.storeWord addr (Utility.regToInt32 x))))
    | Decode.Addi rd rs1 imm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Program.setRegister rd (Coq.ZArith.BinInt.Z.add x (Utility.fromImm imm12)))
    | Decode.Slti rd rs1 imm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Program.setRegister rd (if x < Utility.fromImm imm12 : bool then 1 else 0))
    | Decode.Sltiu rd rs1 imm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Program.setRegister rd (if (Utility.ltu x (Utility.fromImm imm12)) : bool
                                               then 1
                                               else 0))
    | Decode.Xori rd rs1 imm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Program.setRegister rd (Coq.ZArith.BinInt.Z.lxor x (Utility.fromImm imm12)))
    | Decode.Ori rd rs1 imm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Program.setRegister rd (Coq.ZArith.BinInt.Z.lor x (Utility.fromImm imm12)))
    | Decode.Andi rd rs1 imm12 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Program.setRegister rd (Coq.ZArith.BinInt.Z.land x (Utility.fromImm imm12)))
    | Decode.Slli rd rs1 shamt6 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Program.setRegister rd (Utility.sll x shamt6))
    | Decode.Srli rd rs1 shamt6 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Program.setRegister rd (Utility.srl x shamt6))
    | Decode.Srai rd rs1 shamt6 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Program.setRegister rd (Utility.sra x shamt6))
    | Decode.Add rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (Coq.ZArith.BinInt.Z.add x y)))
    | Decode.Sub rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (Coq.ZArith.BinInt.Z.sub x y)))
    | Decode.Sll rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (Utility.sll x (Utility.regToShamt y))))
    | Decode.Slt rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (if x < y : bool then 1 else 0)))
    | Decode.Sltu rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (if (Utility.ltu x y) : bool then 1 else 0)))
    | Decode.Xor rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (Coq.ZArith.BinInt.Z.lxor x y)))
    | Decode.Or rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (Coq.ZArith.BinInt.Z.lor x y)))
    | Decode.Srl rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (Utility.srl x (Utility.regToShamt y))))
    | Decode.Sra rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (Utility.sra x (Utility.regToShamt y))))
    | Decode.And rd rs1 rs2 =>
        Monads.Bind (Program.getRegister rs1) (fun x =>
                       Monads.Bind (Program.getRegister rs2) (fun y =>
                                      Program.setRegister rd (Coq.ZArith.BinInt.Z.land x y)))
    | inst => Monads.Return tt
    end.

(* Unbound variables:
     bool negb op_zgze__ op_zl__ op_zsze__ tt unit Coq.ZArith.BinInt.Z.add
     Coq.ZArith.BinInt.Z.land Coq.ZArith.BinInt.Z.lnot Coq.ZArith.BinInt.Z.lor
     Coq.ZArith.BinInt.Z.lxor Coq.ZArith.BinInt.Z.modulo Coq.ZArith.BinInt.Z.sub
     Decode.Add Decode.Addi Decode.And Decode.Andi Decode.Auipc Decode.Beq Decode.Bge
     Decode.Bgeu Decode.Blt Decode.Bltu Decode.Bne Decode.InstructionI Decode.Jal
     Decode.Jalr Decode.Lb Decode.Lbu Decode.Lh Decode.Lhu Decode.Lui Decode.Lw
     Decode.Or Decode.Ori Decode.Sb Decode.Sh Decode.Sll Decode.Slli Decode.Slt
     Decode.Slti Decode.Sltiu Decode.Sltu Decode.Sra Decode.Srai Decode.Srl
     Decode.Srli Decode.Sub Decode.Sw Decode.Xor Decode.Xori Monads.Bind
     Monads.Return Program.Load Program.RiscvProgram Program.Store Program.getPC
     Program.getRegister Program.loadByte Program.loadHalf Program.loadWord
     Program.raiseException Program.setPC Program.setRegister Program.storeByte
     Program.storeHalf Program.storeWord Program.translate Utility.fromImm
     Utility.int16ToReg Utility.int32ToReg Utility.int8ToReg Utility.ltu
     Utility.regToInt16 Utility.regToInt32 Utility.regToInt8 Utility.regToShamt
     Utility.signed_eqb Utility.sll Utility.sra Utility.srl Utility.uInt16ToReg
     Utility.uInt8ToReg Utility.when
*)
