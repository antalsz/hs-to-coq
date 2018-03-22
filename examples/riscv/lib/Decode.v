(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Coq.ZArith.BinInt.
Local Open Scope Z_scope.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.ZArith.BinInt.
Require Data.Bits.
Require GHC.Err.
Require GHC.Num.
Require GHC.Real.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Register :=
  Coq.ZArith.BinInt.Z%type.

Definition Opcode :=
  Coq.ZArith.BinInt.Z%type.

Inductive InstructionSet : Type
  := RV32I : InstructionSet
  |  RV32IM : InstructionSet
  |  RV64I : InstructionSet
  |  RV64IM : InstructionSet.

Inductive InstructionM64 : Type
  := Mulw : Register -> Register -> Register -> InstructionM64
  |  Divw : Register -> Register -> Register -> InstructionM64
  |  Divuw : Register -> Register -> Register -> InstructionM64
  |  Remw : Register -> Register -> Register -> InstructionM64
  |  Remuw : Register -> Register -> Register -> InstructionM64
  |  InvalidM64 : InstructionM64.

Inductive InstructionM : Type
  := Mul : Register -> Register -> Register -> InstructionM
  |  Mulh : Register -> Register -> Register -> InstructionM
  |  Mulhsu : Register -> Register -> Register -> InstructionM
  |  Mulhu : Register -> Register -> Register -> InstructionM
  |  Div : Register -> Register -> Register -> InstructionM
  |  Divu : Register -> Register -> Register -> InstructionM
  |  Rem : Register -> Register -> Register -> InstructionM
  |  Remu : Register -> Register -> Register -> InstructionM
  |  InvalidM : InstructionM.

Inductive InstructionI64 : Type
  := Ld : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI64
  |  Lwu : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI64
  |  Addiw : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI64
  |  Slliw : Register -> Register -> GHC.Num.Int -> InstructionI64
  |  Srliw : Register -> Register -> GHC.Num.Int -> InstructionI64
  |  Sraiw : Register -> Register -> GHC.Num.Int -> InstructionI64
  |  Sd : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI64
  |  Addw : Register -> Register -> Register -> InstructionI64
  |  Subw : Register -> Register -> Register -> InstructionI64
  |  Sllw : Register -> Register -> Register -> InstructionI64
  |  Srlw : Register -> Register -> Register -> InstructionI64
  |  Sraw : Register -> Register -> Register -> InstructionI64
  |  InvalidI64 : InstructionI64.

Inductive InstructionI : Type
  := Lb : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Lh : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Lw : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Lbu : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Lhu : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Fence : Coq.ZArith.BinInt.Z -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Fence_i : InstructionI
  |  Addi : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Slli : Register -> Register -> GHC.Num.Int -> InstructionI
  |  Slti : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Sltiu : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Xori : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Ori : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Andi : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Srli : Register -> Register -> GHC.Num.Int -> InstructionI
  |  Srai : Register -> Register -> GHC.Num.Int -> InstructionI
  |  Auipc : Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Sb : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Sh : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Sw : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Add : Register -> Register -> Register -> InstructionI
  |  Sub : Register -> Register -> Register -> InstructionI
  |  Sll : Register -> Register -> Register -> InstructionI
  |  Slt : Register -> Register -> Register -> InstructionI
  |  Sltu : Register -> Register -> Register -> InstructionI
  |  Xor : Register -> Register -> Register -> InstructionI
  |  Srl : Register -> Register -> Register -> InstructionI
  |  Sra : Register -> Register -> Register -> InstructionI
  |  Or : Register -> Register -> Register -> InstructionI
  |  And : Register -> Register -> Register -> InstructionI
  |  Lui : Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Beq : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Bne : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Blt : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Bge : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Bltu : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Bgeu : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Jalr : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  Jal : Register -> Coq.ZArith.BinInt.Z -> InstructionI
  |  InvalidI : InstructionI.

Inductive InstructionCSR : Type
  := Ecall : InstructionCSR
  |  Ebreak : InstructionCSR
  |  Uret : InstructionCSR
  |  Sret : InstructionCSR
  |  Mret : InstructionCSR
  |  Wfi : InstructionCSR
  |  Sfence_vm : Register -> Register -> InstructionCSR
  |  Csrrw : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionCSR
  |  Csrrs : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionCSR
  |  Csrrc : Register -> Register -> Coq.ZArith.BinInt.Z -> InstructionCSR
  |  Csrrwi
   : Register -> Coq.ZArith.BinInt.Z -> Coq.ZArith.BinInt.Z -> InstructionCSR
  |  Csrrsi
   : Register -> Coq.ZArith.BinInt.Z -> Coq.ZArith.BinInt.Z -> InstructionCSR
  |  Csrrci
   : Register -> Coq.ZArith.BinInt.Z -> Coq.ZArith.BinInt.Z -> InstructionCSR
  |  InvalidCSR : InstructionCSR.

Inductive Instruction : Type
  := IInstruction : InstructionI -> Instruction
  |  MInstruction : InstructionM -> Instruction
  |  I64Instruction : InstructionI64 -> Instruction
  |  M64Instruction : InstructionM64 -> Instruction
  |  CSRInstruction : InstructionCSR -> Instruction
  |  InvalidInstruction : Instruction.

Definition oimm20 (arg_0__ : InstructionI) :=
  match arg_0__ with
  | Lb _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Lb' of type `InstructionI'")
  | Lh _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Lh' of type `InstructionI'")
  | Lw _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Lw' of type `InstructionI'")
  | Lbu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Lbu' of type `InstructionI'")
  | Lhu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Lhu' of type `InstructionI'")
  | Fence _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Fence' of type `InstructionI'")
  | Fence_i =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Fence_i' of type `InstructionI'")
  | Addi _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Addi' of type `InstructionI'")
  | Slli _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Slli' of type `InstructionI'")
  | Slti _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Slti' of type `InstructionI'")
  | Sltiu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Sltiu' of type `InstructionI'")
  | Xori _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Xori' of type `InstructionI'")
  | Ori _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Ori' of type `InstructionI'")
  | Andi _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Andi' of type `InstructionI'")
  | Srli _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Srli' of type `InstructionI'")
  | Srai _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Srai' of type `InstructionI'")
  | Auipc _ oimm20 => oimm20
  | Sb _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Sb' of type `InstructionI'")
  | Sh _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Sh' of type `InstructionI'")
  | Sw _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Sw' of type `InstructionI'")
  | Add _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Add' of type `InstructionI'")
  | Sub _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Sub' of type `InstructionI'")
  | Sll _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Sll' of type `InstructionI'")
  | Slt _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Slt' of type `InstructionI'")
  | Sltu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Sltu' of type `InstructionI'")
  | Xor _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Xor' of type `InstructionI'")
  | Srl _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Srl' of type `InstructionI'")
  | Sra _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Sra' of type `InstructionI'")
  | Or _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Or' of type `InstructionI'")
  | And _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `And' of type `InstructionI'")
  | Lui _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Lui' of type `InstructionI'")
  | Beq _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Beq' of type `InstructionI'")
  | Bne _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Bne' of type `InstructionI'")
  | Blt _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Blt' of type `InstructionI'")
  | Bge _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Bge' of type `InstructionI'")
  | Bltu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Bltu' of type `InstructionI'")
  | Bgeu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Bgeu' of type `InstructionI'")
  | Jalr _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Jalr' of type `InstructionI'")
  | Jal _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `Jal' of type `InstructionI'")
  | InvalidI =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `oimm20' has no match in constructor `InvalidI' of type `InstructionI'")
  end.

Definition jimm20 (arg_1__ : InstructionI) :=
  match arg_1__ with
  | Lb _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Lb' of type `InstructionI'")
  | Lh _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Lh' of type `InstructionI'")
  | Lw _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Lw' of type `InstructionI'")
  | Lbu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Lbu' of type `InstructionI'")
  | Lhu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Lhu' of type `InstructionI'")
  | Fence _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Fence' of type `InstructionI'")
  | Fence_i =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Fence_i' of type `InstructionI'")
  | Addi _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Addi' of type `InstructionI'")
  | Slli _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Slli' of type `InstructionI'")
  | Slti _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Slti' of type `InstructionI'")
  | Sltiu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Sltiu' of type `InstructionI'")
  | Xori _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Xori' of type `InstructionI'")
  | Ori _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Ori' of type `InstructionI'")
  | Andi _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Andi' of type `InstructionI'")
  | Srli _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Srli' of type `InstructionI'")
  | Srai _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Srai' of type `InstructionI'")
  | Auipc _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Auipc' of type `InstructionI'")
  | Sb _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Sb' of type `InstructionI'")
  | Sh _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Sh' of type `InstructionI'")
  | Sw _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Sw' of type `InstructionI'")
  | Add _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Add' of type `InstructionI'")
  | Sub _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Sub' of type `InstructionI'")
  | Sll _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Sll' of type `InstructionI'")
  | Slt _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Slt' of type `InstructionI'")
  | Sltu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Sltu' of type `InstructionI'")
  | Xor _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Xor' of type `InstructionI'")
  | Srl _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Srl' of type `InstructionI'")
  | Sra _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Sra' of type `InstructionI'")
  | Or _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Or' of type `InstructionI'")
  | And _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `And' of type `InstructionI'")
  | Lui _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Lui' of type `InstructionI'")
  | Beq _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Beq' of type `InstructionI'")
  | Bne _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Bne' of type `InstructionI'")
  | Blt _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Blt' of type `InstructionI'")
  | Bge _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Bge' of type `InstructionI'")
  | Bltu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Bltu' of type `InstructionI'")
  | Bgeu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Bgeu' of type `InstructionI'")
  | Jalr _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `Jalr' of type `InstructionI'")
  | Jal _ jimm20 => jimm20
  | InvalidI =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `jimm20' has no match in constructor `InvalidI' of type `InstructionI'")
  end.

Definition imm20 (arg_2__ : InstructionI) :=
  match arg_2__ with
  | Lb _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Lb' of type `InstructionI'")
  | Lh _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Lh' of type `InstructionI'")
  | Lw _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Lw' of type `InstructionI'")
  | Lbu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Lbu' of type `InstructionI'")
  | Lhu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Lhu' of type `InstructionI'")
  | Fence _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Fence' of type `InstructionI'")
  | Fence_i =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Fence_i' of type `InstructionI'")
  | Addi _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Addi' of type `InstructionI'")
  | Slli _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Slli' of type `InstructionI'")
  | Slti _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Slti' of type `InstructionI'")
  | Sltiu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Sltiu' of type `InstructionI'")
  | Xori _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Xori' of type `InstructionI'")
  | Ori _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Ori' of type `InstructionI'")
  | Andi _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Andi' of type `InstructionI'")
  | Srli _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Srli' of type `InstructionI'")
  | Srai _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Srai' of type `InstructionI'")
  | Auipc _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Auipc' of type `InstructionI'")
  | Sb _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Sb' of type `InstructionI'")
  | Sh _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Sh' of type `InstructionI'")
  | Sw _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Sw' of type `InstructionI'")
  | Add _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Add' of type `InstructionI'")
  | Sub _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Sub' of type `InstructionI'")
  | Sll _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Sll' of type `InstructionI'")
  | Slt _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Slt' of type `InstructionI'")
  | Sltu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Sltu' of type `InstructionI'")
  | Xor _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Xor' of type `InstructionI'")
  | Srl _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Srl' of type `InstructionI'")
  | Sra _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Sra' of type `InstructionI'")
  | Or _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Or' of type `InstructionI'")
  | And _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `And' of type `InstructionI'")
  | Lui _ imm20 => imm20
  | Beq _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Beq' of type `InstructionI'")
  | Bne _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Bne' of type `InstructionI'")
  | Blt _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Blt' of type `InstructionI'")
  | Bge _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Bge' of type `InstructionI'")
  | Bltu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Bltu' of type `InstructionI'")
  | Bgeu _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Bgeu' of type `InstructionI'")
  | Jalr _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Jalr' of type `InstructionI'")
  | Jal _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `Jal' of type `InstructionI'")
  | InvalidI =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `imm20' has no match in constructor `InvalidI' of type `InstructionI'")
  end.
(* Converted value declarations: *)

Definition bitwidth : InstructionSet -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
    | RV32I => 32
    | RV32IM => 32
    | RV64I => 64
    | RV64IM => 64
    end.

Definition funct12_EBREAK : Coq.ZArith.BinInt.Z :=
  1.

Definition funct12_ECALL : Coq.ZArith.BinInt.Z :=
  0.

Definition funct12_MRET : Coq.ZArith.BinInt.Z :=
  770.

Definition funct12_SRET : Coq.ZArith.BinInt.Z :=
  258.

Definition funct12_URET : Coq.ZArith.BinInt.Z :=
  2.

Definition funct12_WFI : Coq.ZArith.BinInt.Z :=
  261.

Definition funct3_ADD : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_ADDI : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_ADDIW : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_ADDW : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_AND : Coq.ZArith.BinInt.Z :=
  7.

Definition funct3_ANDI : Coq.ZArith.BinInt.Z :=
  7.

Definition funct3_BEQ : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_BGE : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_BGEU : Coq.ZArith.BinInt.Z :=
  7.

Definition funct3_BLT : Coq.ZArith.BinInt.Z :=
  4.

Definition funct3_BLTU : Coq.ZArith.BinInt.Z :=
  6.

Definition funct3_BNE : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_CSRRC : Coq.ZArith.BinInt.Z :=
  3.

Definition funct3_CSRRCI : Coq.ZArith.BinInt.Z :=
  7.

Definition funct3_CSRRS : Coq.ZArith.BinInt.Z :=
  2.

Definition funct3_CSRRSI : Coq.ZArith.BinInt.Z :=
  6.

Definition funct3_CSRRW : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_CSRRWI : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_DIV : Coq.ZArith.BinInt.Z :=
  4.

Definition funct3_DIVU : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_DIVUW : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_DIVW : Coq.ZArith.BinInt.Z :=
  4.

Definition funct3_FENCE : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_FENCE_I : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_LB : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_LBU : Coq.ZArith.BinInt.Z :=
  4.

Definition funct3_LD : Coq.ZArith.BinInt.Z :=
  3.

Definition funct3_LH : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_LHU : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_LW : Coq.ZArith.BinInt.Z :=
  2.

Definition funct3_LWU : Coq.ZArith.BinInt.Z :=
  6.

Definition funct3_MUL : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_MULH : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_MULHSU : Coq.ZArith.BinInt.Z :=
  2.

Definition funct3_MULHU : Coq.ZArith.BinInt.Z :=
  3.

Definition funct3_MULW : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_OR : Coq.ZArith.BinInt.Z :=
  6.

Definition funct3_ORI : Coq.ZArith.BinInt.Z :=
  6.

Definition funct3_PRIV : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_REM : Coq.ZArith.BinInt.Z :=
  6.

Definition funct3_REMU : Coq.ZArith.BinInt.Z :=
  7.

Definition funct3_REMUW : Coq.ZArith.BinInt.Z :=
  7.

Definition funct3_REMW : Coq.ZArith.BinInt.Z :=
  6.

Definition funct3_SB : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_SD : Coq.ZArith.BinInt.Z :=
  3.

Definition funct3_SH : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_SLL : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_SLLI : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_SLLIW : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_SLLW : Coq.ZArith.BinInt.Z :=
  1.

Definition funct3_SLT : Coq.ZArith.BinInt.Z :=
  2.

Definition funct3_SLTI : Coq.ZArith.BinInt.Z :=
  2.

Definition funct3_SLTIU : Coq.ZArith.BinInt.Z :=
  3.

Definition funct3_SLTU : Coq.ZArith.BinInt.Z :=
  3.

Definition funct3_SRA : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_SRAI : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_SRAIW : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_SRAW : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_SRL : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_SRLI : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_SRLIW : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_SRLW : Coq.ZArith.BinInt.Z :=
  5.

Definition funct3_SUB : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_SUBW : Coq.ZArith.BinInt.Z :=
  0.

Definition funct3_SW : Coq.ZArith.BinInt.Z :=
  2.

Definition funct3_XOR : Coq.ZArith.BinInt.Z :=
  4.

Definition funct3_XORI : Coq.ZArith.BinInt.Z :=
  4.

Definition funct6_SLLI : Coq.ZArith.BinInt.Z :=
  0.

Definition funct6_SRAI : Coq.ZArith.BinInt.Z :=
  16.

Definition funct6_SRLI : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_ADD : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_ADDW : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_AND : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_DIV : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_DIVU : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_DIVUW : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_DIVW : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_MUL : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_MULH : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_MULHSU : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_MULHU : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_MULW : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_OR : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_REM : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_REMU : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_REMUW : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_REMW : Coq.ZArith.BinInt.Z :=
  1.

Definition funct7_SFENCE_VM : Coq.ZArith.BinInt.Z :=
  9.

Definition funct7_SLL : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_SLLIW : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_SLLW : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_SLT : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_SLTU : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_SRA : Coq.ZArith.BinInt.Z :=
  32.

Definition funct7_SRAIW : Coq.ZArith.BinInt.Z :=
  32.

Definition funct7_SRAW : Coq.ZArith.BinInt.Z :=
  32.

Definition funct7_SRL : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_SRLIW : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_SRLW : Coq.ZArith.BinInt.Z :=
  0.

Definition funct7_SUB : Coq.ZArith.BinInt.Z :=
  32.

Definition funct7_SUBW : Coq.ZArith.BinInt.Z :=
  32.

Definition funct7_XOR : Coq.ZArith.BinInt.Z :=
  0.

Definition machineIntToShamt : Coq.ZArith.BinInt.Z -> GHC.Num.Int :=
  GHC.Real.fromIntegral.

Definition opcode_AMO : Opcode :=
  47.

Definition opcode_AUIPC : Opcode :=
  23.

Definition opcode_BRANCH : Opcode :=
  99.

Definition opcode_JAL : Opcode :=
  111.

Definition opcode_JALR : Opcode :=
  103.

Definition opcode_LOAD : Opcode :=
  3.

Definition opcode_LOAD_FP : Opcode :=
  7.

Definition opcode_LUI : Opcode :=
  55.

Definition opcode_MADD : Opcode :=
  67.

Definition opcode_MISC_MEM : Opcode :=
  15.

Definition opcode_MSUB : Opcode :=
  71.

Definition opcode_NMADD : Opcode :=
  79.

Definition opcode_NMSUB : Opcode :=
  75.

Definition opcode_OP : Opcode :=
  51.

Definition opcode_OP_32 : Opcode :=
  59.

Definition opcode_OP_FP : Opcode :=
  83.

Definition opcode_OP_IMM : Opcode :=
  19.

Definition opcode_OP_IMM_32 : Opcode :=
  27.

Definition opcode_STORE : Opcode :=
  35.

Definition opcode_STORE_FP : Opcode :=
  39.

Definition opcode_SYSTEM : Opcode :=
  115.

Definition signExtend
   : GHC.Num.Int -> Coq.ZArith.BinInt.Z -> Coq.ZArith.BinInt.Z :=
  fun l n =>
    if Data.Bits.testBit n (l GHC.Num.- 1) : bool
    then n GHC.Num.- Coq.ZArith.BinInt.Z.pow 2 l
    else n.

Definition supportsM : InstructionSet -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | RV32I => false
    | RV32IM => true
    | RV64I => false
    | RV64IM => true
    end.

Definition decode : InstructionSet -> Coq.ZArith.BinInt.Z -> Instruction :=
  fun iset inst =>
    let zimm := GHC.Err.undefined inst 15 20 in
    let funct6 := GHC.Err.undefined inst 26 32 in
    let shamtHi := GHC.Err.undefined inst 25 26 in
    let shamtHiTest :=
      orb (Coq.ZArith.BinInt.Z.eqb shamtHi 0) (Coq.ZArith.BinInt.Z.eqb (bitwidth iset)
                                                                       64) in
    let shamt6 := machineIntToShamt (GHC.Err.undefined inst 20 26) in
    let shamt5 := machineIntToShamt (GHC.Err.undefined inst 20 25) in
    let sbimm12 :=
      signExtend 13 (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.lor
                                              (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined
                                                                                                    inst 31 32) 12)
                                                                       (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined
                                                                                                    inst 25 31) 5))
                                              (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined inst 8 12) 1))
                                             (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined inst 7 8) 11)) in
    let simm12 :=
      signExtend 12 (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.shiftl
                                              (GHC.Err.undefined inst 25 32) 5) (GHC.Err.undefined inst 7 12)) in
    let csr12 := GHC.Err.undefined inst 20 32 in
    let oimm12 := signExtend 12 (GHC.Err.undefined inst 20 32) in
    let imm12 := signExtend 12 (GHC.Err.undefined inst 20 32) in
    let jimm20 :=
      signExtend 21 (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.lor
                                              (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined
                                                                                                    inst 31 32) 20)
                                                                       (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined
                                                                                                    inst 21 31) 1))
                                              (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined inst 20 21) 11))
                                             (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined inst 12 20) 12)) in
    let oimm20 :=
      signExtend 32 (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined inst 12 32) 12) in
    let imm20 :=
      signExtend 32 (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined inst 12 32) 12) in
    let msb4 := GHC.Err.undefined inst 28 32 in
    let pred := GHC.Err.undefined inst 24 28 in
    let succ := GHC.Err.undefined inst 20 24 in
    let rs3 := GHC.Err.undefined inst 27 32 in
    let rs2 := GHC.Err.undefined inst 20 25 in
    let rs1 := GHC.Err.undefined inst 15 20 in
    let rd := GHC.Err.undefined inst 7 12 in
    let funct12 := GHC.Err.undefined inst 20 32 in
    let funct10 :=
      Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.shiftl (GHC.Err.undefined inst 25
                                                           32) 3) (GHC.Err.undefined inst 12 15) in
    let funct7 := GHC.Err.undefined inst 25 32 in
    let funct3 := GHC.Err.undefined inst 12 15 in
    let opcode := GHC.Err.undefined inst 0 7 in
    let decodeI :=
      if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_LOAD) (Coq.ZArith.BinInt.Z.eqb
               funct3 funct3_LB) : bool
      then Lb rd rs1 oimm12
      else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_LOAD)
                   (Coq.ZArith.BinInt.Z.eqb funct3 funct3_LH) : bool
           then Lh rd rs1 oimm12
           else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_LOAD)
                        (Coq.ZArith.BinInt.Z.eqb funct3 funct3_LW) : bool
                then Lw rd rs1 oimm12
                else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_LOAD)
                             (Coq.ZArith.BinInt.Z.eqb funct3 funct3_LBU) : bool
                     then Lbu rd rs1 oimm12
                     else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_LOAD)
                                  (Coq.ZArith.BinInt.Z.eqb funct3 funct3_LHU) : bool
                          then Lhu rd rs1 oimm12
                          else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_MISC_MEM) (andb
                                        (Coq.ZArith.BinInt.Z.eqb rd 0) (andb (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                                      funct3_FENCE)
                                                                             (andb (Coq.ZArith.BinInt.Z.eqb rs1 0)
                                                                                   (Coq.ZArith.BinInt.Z.eqb msb4
                                                                                                            0)))) : bool
                               then Fence pred succ
                               else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_MISC_MEM) (andb
                                             (Coq.ZArith.BinInt.Z.eqb rd 0) (andb (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                                           funct3_FENCE_I)
                                                                                  (andb (Coq.ZArith.BinInt.Z.eqb rs1 0)
                                                                                        (Coq.ZArith.BinInt.Z.eqb imm12
                                                                                                                 0)))) : bool
                                    then Fence_i
                                    else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM)
                                                 (Coq.ZArith.BinInt.Z.eqb funct3 funct3_ADDI) : bool
                                         then Addi rd rs1 imm12
                                         else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM)
                                                      (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SLTI) : bool
                                              then Slti rd rs1 imm12
                                              else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM)
                                                           (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SLTIU) : bool
                                                   then Sltiu rd rs1 imm12
                                                   else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM)
                                                                (Coq.ZArith.BinInt.Z.eqb funct3 funct3_XORI) : bool
                                                        then Xori rd rs1 imm12
                                                        else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM)
                                                                     (Coq.ZArith.BinInt.Z.eqb funct3 funct3_ORI) : bool
                                                             then Ori rd rs1 imm12
                                                             else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM)
                                                                          (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                                   funct3_ANDI) : bool
                                                                  then Andi rd rs1 imm12
                                                                  else if andb (Coq.ZArith.BinInt.Z.eqb opcode
                                                                                                        opcode_OP_IMM)
                                                                               (andb (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                                              funct3_SLLI)
                                                                                     (andb (Coq.ZArith.BinInt.Z.eqb
                                                                                            funct6 funct6_SLLI)
                                                                                           shamtHiTest)) : bool
                                                                       then Slli rd rs1 shamt6
                                                                       else if andb (Coq.ZArith.BinInt.Z.eqb opcode
                                                                                                             opcode_OP_IMM)
                                                                                    (andb (Coq.ZArith.BinInt.Z.eqb
                                                                                           funct3 funct3_SRLI) (andb
                                                                                           (Coq.ZArith.BinInt.Z.eqb
                                                                                            funct6 funct6_SRLI)
                                                                                           shamtHiTest)) : bool
                                                                            then Srli rd rs1 shamt6
                                                                            else if andb (Coq.ZArith.BinInt.Z.eqb opcode
                                                                                                                  opcode_OP_IMM)
                                                                                         (andb (Coq.ZArith.BinInt.Z.eqb
                                                                                                funct3 funct3_SRAI)
                                                                                               (andb
                                                                                                (Coq.ZArith.BinInt.Z.eqb
                                                                                                 funct6 funct6_SRAI)
                                                                                                shamtHiTest)) : bool
                                                                                 then Srai rd rs1 shamt6
                                                                                 else if Coq.ZArith.BinInt.Z.eqb opcode
                                                                                                                 opcode_AUIPC : bool
                                                                                      then Auipc rd oimm20
                                                                                      else if andb
                                                                                              (Coq.ZArith.BinInt.Z.eqb
                                                                                               opcode opcode_STORE)
                                                                                              (Coq.ZArith.BinInt.Z.eqb
                                                                                               funct3 funct3_SB) : bool
                                                                                           then Sb rs1 rs2 simm12
                                                                                           else if andb
                                                                                                   (Coq.ZArith.BinInt.Z.eqb
                                                                                                    opcode opcode_STORE)
                                                                                                   (Coq.ZArith.BinInt.Z.eqb
                                                                                                    funct3
                                                                                                    funct3_SH) : bool
                                                                                                then Sh rs1 rs2 simm12
                                                                                                else if andb
                                                                                                        (Coq.ZArith.BinInt.Z.eqb
                                                                                                         opcode
                                                                                                         opcode_STORE)
                                                                                                        (Coq.ZArith.BinInt.Z.eqb
                                                                                                         funct3
                                                                                                         funct3_SW) : bool
                                                                                                     then Sw rs1 rs2
                                                                                                          simm12
                                                                                                     else if andb
                                                                                                             (Coq.ZArith.BinInt.Z.eqb
                                                                                                              opcode
                                                                                                              opcode_OP)
                                                                                                             (andb
                                                                                                              (Coq.ZArith.BinInt.Z.eqb
                                                                                                               funct3
                                                                                                               funct3_ADD)
                                                                                                              (Coq.ZArith.BinInt.Z.eqb
                                                                                                               funct7
                                                                                                               funct7_ADD)) : bool
                                                                                                          then Add rd
                                                                                                               rs1 rs2
                                                                                                          else if andb
                                                                                                                  (Coq.ZArith.BinInt.Z.eqb
                                                                                                                   opcode
                                                                                                                   opcode_OP)
                                                                                                                  (andb
                                                                                                                   (Coq.ZArith.BinInt.Z.eqb
                                                                                                                    funct3
                                                                                                                    funct3_SUB)
                                                                                                                   (Coq.ZArith.BinInt.Z.eqb
                                                                                                                    funct7
                                                                                                                    funct7_SUB)) : bool
                                                                                                               then Sub
                                                                                                                    rd
                                                                                                                    rs1
                                                                                                                    rs2
                                                                                                               else if andb
                                                                                                                       (Coq.ZArith.BinInt.Z.eqb
                                                                                                                        opcode
                                                                                                                        opcode_OP)
                                                                                                                       (andb
                                                                                                                        (Coq.ZArith.BinInt.Z.eqb
                                                                                                                         funct3
                                                                                                                         funct3_SLL)
                                                                                                                        (Coq.ZArith.BinInt.Z.eqb
                                                                                                                         funct7
                                                                                                                         funct7_SLL)) : bool
                                                                                                                    then Sll
                                                                                                                         rd
                                                                                                                         rs1
                                                                                                                         rs2
                                                                                                                    else if andb
                                                                                                                            (Coq.ZArith.BinInt.Z.eqb
                                                                                                                             opcode
                                                                                                                             opcode_OP)
                                                                                                                            (andb
                                                                                                                             (Coq.ZArith.BinInt.Z.eqb
                                                                                                                              funct3
                                                                                                                              funct3_SLT)
                                                                                                                             (Coq.ZArith.BinInt.Z.eqb
                                                                                                                              funct7
                                                                                                                              funct7_SLT)) : bool
                                                                                                                         then Slt
                                                                                                                              rd
                                                                                                                              rs1
                                                                                                                              rs2
                                                                                                                         else if andb
                                                                                                                                 (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                  opcode
                                                                                                                                  opcode_OP)
                                                                                                                                 (andb
                                                                                                                                  (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                   funct3
                                                                                                                                   funct3_SLTU)
                                                                                                                                  (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                   funct7
                                                                                                                                   funct7_SLTU)) : bool
                                                                                                                              then Sltu
                                                                                                                                   rd
                                                                                                                                   rs1
                                                                                                                                   rs2
                                                                                                                              else if andb
                                                                                                                                      (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                       opcode
                                                                                                                                       opcode_OP)
                                                                                                                                      (andb
                                                                                                                                       (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                        funct3
                                                                                                                                        funct3_XOR)
                                                                                                                                       (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                        funct7
                                                                                                                                        funct7_XOR)) : bool
                                                                                                                                   then Xor
                                                                                                                                        rd
                                                                                                                                        rs1
                                                                                                                                        rs2
                                                                                                                                   else if andb
                                                                                                                                           (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                            opcode
                                                                                                                                            opcode_OP)
                                                                                                                                           (andb
                                                                                                                                            (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                             funct3
                                                                                                                                             funct3_SRL)
                                                                                                                                            (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                             funct7
                                                                                                                                             funct7_SRL)) : bool
                                                                                                                                        then Srl
                                                                                                                                             rd
                                                                                                                                             rs1
                                                                                                                                             rs2
                                                                                                                                        else if andb
                                                                                                                                                (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                 opcode
                                                                                                                                                 opcode_OP)
                                                                                                                                                (andb
                                                                                                                                                 (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                  funct3
                                                                                                                                                  funct3_SRA)
                                                                                                                                                 (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                  funct7
                                                                                                                                                  funct7_SRA)) : bool
                                                                                                                                             then Sra
                                                                                                                                                  rd
                                                                                                                                                  rs1
                                                                                                                                                  rs2
                                                                                                                                             else if andb
                                                                                                                                                     (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                      opcode
                                                                                                                                                      opcode_OP)
                                                                                                                                                     (andb
                                                                                                                                                      (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                       funct3
                                                                                                                                                       funct3_OR)
                                                                                                                                                      (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                       funct7
                                                                                                                                                       funct7_OR)) : bool
                                                                                                                                                  then Or
                                                                                                                                                       rd
                                                                                                                                                       rs1
                                                                                                                                                       rs2
                                                                                                                                                  else if andb
                                                                                                                                                          (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                           opcode
                                                                                                                                                           opcode_OP)
                                                                                                                                                          (andb
                                                                                                                                                           (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                            funct3
                                                                                                                                                            funct3_AND)
                                                                                                                                                           (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                            funct7
                                                                                                                                                            funct7_AND)) : bool
                                                                                                                                                       then And
                                                                                                                                                            rd
                                                                                                                                                            rs1
                                                                                                                                                            rs2
                                                                                                                                                       else if Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                               opcode
                                                                                                                                                               opcode_LUI : bool
                                                                                                                                                            then Lui
                                                                                                                                                                 rd
                                                                                                                                                                 imm20
                                                                                                                                                            else if andb
                                                                                                                                                                    (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                     opcode
                                                                                                                                                                     opcode_BRANCH)
                                                                                                                                                                    (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                     funct3
                                                                                                                                                                     funct3_BEQ) : bool
                                                                                                                                                                 then Beq
                                                                                                                                                                      rs1
                                                                                                                                                                      rs2
                                                                                                                                                                      sbimm12
                                                                                                                                                                 else if andb
                                                                                                                                                                         (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                          opcode
                                                                                                                                                                          opcode_BRANCH)
                                                                                                                                                                         (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                          funct3
                                                                                                                                                                          funct3_BNE) : bool
                                                                                                                                                                      then Bne
                                                                                                                                                                           rs1
                                                                                                                                                                           rs2
                                                                                                                                                                           sbimm12
                                                                                                                                                                      else if andb
                                                                                                                                                                              (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                               opcode
                                                                                                                                                                               opcode_BRANCH)
                                                                                                                                                                              (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                               funct3
                                                                                                                                                                               funct3_BLT) : bool
                                                                                                                                                                           then Blt
                                                                                                                                                                                rs1
                                                                                                                                                                                rs2
                                                                                                                                                                                sbimm12
                                                                                                                                                                           else if andb
                                                                                                                                                                                   (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                                    opcode
                                                                                                                                                                                    opcode_BRANCH)
                                                                                                                                                                                   (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                                    funct3
                                                                                                                                                                                    funct3_BGE) : bool
                                                                                                                                                                                then Bge
                                                                                                                                                                                     rs1
                                                                                                                                                                                     rs2
                                                                                                                                                                                     sbimm12
                                                                                                                                                                                else if andb
                                                                                                                                                                                        (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                                         opcode
                                                                                                                                                                                         opcode_BRANCH)
                                                                                                                                                                                        (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                                         funct3
                                                                                                                                                                                         funct3_BLTU) : bool
                                                                                                                                                                                     then Bltu
                                                                                                                                                                                          rs1
                                                                                                                                                                                          rs2
                                                                                                                                                                                          sbimm12
                                                                                                                                                                                     else if andb
                                                                                                                                                                                             (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                                              opcode
                                                                                                                                                                                              opcode_BRANCH)
                                                                                                                                                                                             (Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                                              funct3
                                                                                                                                                                                              funct3_BGEU) : bool
                                                                                                                                                                                          then Bgeu
                                                                                                                                                                                               rs1
                                                                                                                                                                                               rs2
                                                                                                                                                                                               sbimm12
                                                                                                                                                                                          else if Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                                                  opcode
                                                                                                                                                                                                  opcode_JALR : bool
                                                                                                                                                                                               then Jalr
                                                                                                                                                                                                    rd
                                                                                                                                                                                                    rs1
                                                                                                                                                                                                    oimm12
                                                                                                                                                                                               else if Coq.ZArith.BinInt.Z.eqb
                                                                                                                                                                                                       opcode
                                                                                                                                                                                                       opcode_JAL : bool
                                                                                                                                                                                                    then Jal
                                                                                                                                                                                                         rd
                                                                                                                                                                                                         jimm20
                                                                                                                                                                                                    else InvalidI in
    let decodeM :=
      if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP) (andb
               (Coq.ZArith.BinInt.Z.eqb funct3 funct3_MUL) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                    funct7_MUL)) : bool
      then Mul rd rs1 rs2
      else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP) (andb
                    (Coq.ZArith.BinInt.Z.eqb funct3 funct3_MULH) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                          funct7_MULH)) : bool
           then Mulh rd rs1 rs2
           else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP) (andb
                         (Coq.ZArith.BinInt.Z.eqb funct3 funct3_MULHSU) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                 funct7_MULHSU)) : bool
                then Mulhsu rd rs1 rs2
                else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP) (andb
                              (Coq.ZArith.BinInt.Z.eqb funct3 funct3_MULHU) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                     funct7_MULHU)) : bool
                     then Mulhu rd rs1 rs2
                     else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP) (andb
                                   (Coq.ZArith.BinInt.Z.eqb funct3 funct3_DIV) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                        funct7_DIV)) : bool
                          then Div rd rs1 rs2
                          else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP) (andb
                                        (Coq.ZArith.BinInt.Z.eqb funct3 funct3_DIVU) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                              funct7_DIVU)) : bool
                               then Divu rd rs1 rs2
                               else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP) (andb
                                             (Coq.ZArith.BinInt.Z.eqb funct3 funct3_REM) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                                  funct7_REM)) : bool
                                    then Rem rd rs1 rs2
                                    else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP) (andb
                                                  (Coq.ZArith.BinInt.Z.eqb funct3 funct3_REMU) (Coq.ZArith.BinInt.Z.eqb
                                                   funct7 funct7_REMU)) : bool
                                         then Remu rd rs1 rs2
                                         else InvalidM in
    let decodeI64 :=
      if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_LOAD) (Coq.ZArith.BinInt.Z.eqb
               funct3 funct3_LD) : bool
      then Ld rd rs1 oimm12
      else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_LOAD)
                   (Coq.ZArith.BinInt.Z.eqb funct3 funct3_LWU) : bool
           then Lwu rd rs1 oimm12
           else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM_32)
                        (Coq.ZArith.BinInt.Z.eqb funct3 funct3_ADDIW) : bool
                then Addiw rd rs1 imm12
                else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM_32) (andb
                              (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SLLIW) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                     funct7_SLLIW)) : bool
                     then Slliw rd rs1 shamt5
                     else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM_32) (andb
                                   (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SRLIW) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                          funct7_SRLIW)) : bool
                          then Srliw rd rs1 shamt5
                          else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_IMM_32) (andb
                                        (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SRAIW) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                               funct7_SRAIW)) : bool
                               then Sraiw rd rs1 shamt5
                               else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_STORE)
                                            (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SD) : bool
                                    then Sd rs1 rs2 simm12
                                    else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
                                                  (Coq.ZArith.BinInt.Z.eqb funct3 funct3_ADDW) (Coq.ZArith.BinInt.Z.eqb
                                                   funct7 funct7_ADDW)) : bool
                                         then Addw rd rs1 rs2
                                         else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
                                                       (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SUBW)
                                                       (Coq.ZArith.BinInt.Z.eqb funct7 funct7_SUBW)) : bool
                                              then Subw rd rs1 rs2
                                              else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
                                                            (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SLLW)
                                                            (Coq.ZArith.BinInt.Z.eqb funct7 funct7_SLLW)) : bool
                                                   then Sllw rd rs1 rs2
                                                   else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
                                                                 (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SRLW)
                                                                 (Coq.ZArith.BinInt.Z.eqb funct7 funct7_SRLW)) : bool
                                                        then Srlw rd rs1 rs2
                                                        else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
                                                                      (Coq.ZArith.BinInt.Z.eqb funct3 funct3_SRAW)
                                                                      (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                               funct7_SRAW)) : bool
                                                             then Sraw rd rs1 rs2
                                                             else InvalidI64 in
    let decodeM64 :=
      if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
               (Coq.ZArith.BinInt.Z.eqb funct3 funct3_MULW) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                     funct7_MULW)) : bool
      then Mulw rd rs1 rs2
      else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
                    (Coq.ZArith.BinInt.Z.eqb funct3 funct3_DIVW) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                          funct7_DIVW)) : bool
           then Divw rd rs1 rs2
           else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
                         (Coq.ZArith.BinInt.Z.eqb funct3 funct3_DIVUW) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                funct7_DIVUW)) : bool
                then Divuw rd rs1 rs2
                else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
                              (Coq.ZArith.BinInt.Z.eqb funct3 funct3_REMW) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                    funct7_REMW)) : bool
                     then Remw rd rs1 rs2
                     else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_OP_32) (andb
                                   (Coq.ZArith.BinInt.Z.eqb funct3 funct3_REMUW) (Coq.ZArith.BinInt.Z.eqb funct7
                                                                                                          funct7_REMUW)) : bool
                          then Remuw rd rs1 rs2
                          else InvalidM64 in
    let decodeCSR :=
      if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM) (andb
               (Coq.ZArith.BinInt.Z.eqb rd 0) (andb (Coq.ZArith.BinInt.Z.eqb funct3
                                                                             funct3_PRIV) (andb (Coq.ZArith.BinInt.Z.eqb
                                                                                                 rs1 0)
                                                                                                (Coq.ZArith.BinInt.Z.eqb
                                                                                                 funct12
                                                                                                 funct12_ECALL)))) : bool
      then Ecall
      else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM) (andb
                    (Coq.ZArith.BinInt.Z.eqb rd 0) (andb (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                  funct3_PRIV) (andb
                                                          (Coq.ZArith.BinInt.Z.eqb rs1 0) (Coq.ZArith.BinInt.Z.eqb
                                                           funct12 funct12_EBREAK)))) : bool
           then Ebreak
           else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM) (andb
                         (Coq.ZArith.BinInt.Z.eqb rd 0) (andb (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                       funct3_PRIV) (andb
                                                               (Coq.ZArith.BinInt.Z.eqb rs1 0) (Coq.ZArith.BinInt.Z.eqb
                                                                funct12 funct12_URET)))) : bool
                then Uret
                else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM) (andb
                              (Coq.ZArith.BinInt.Z.eqb rd 0) (andb (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                            funct3_PRIV) (andb
                                                                    (Coq.ZArith.BinInt.Z.eqb rs1 0)
                                                                    (Coq.ZArith.BinInt.Z.eqb funct12
                                                                                             funct12_SRET)))) : bool
                     then Sret
                     else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM) (andb
                                   (Coq.ZArith.BinInt.Z.eqb rd 0) (andb (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                                 funct3_PRIV) (andb
                                                                         (Coq.ZArith.BinInt.Z.eqb rs1 0)
                                                                         (Coq.ZArith.BinInt.Z.eqb funct12
                                                                                                  funct12_MRET)))) : bool
                          then Mret
                          else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM) (andb
                                        (Coq.ZArith.BinInt.Z.eqb rd 0) (andb (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                                      funct3_PRIV) (andb
                                                                              (Coq.ZArith.BinInt.Z.eqb rs1 0)
                                                                              (Coq.ZArith.BinInt.Z.eqb funct12
                                                                                                       funct12_WFI)))) : bool
                               then Wfi
                               else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM)
                                            (Coq.ZArith.BinInt.Z.eqb funct3 funct3_CSRRW) : bool
                                    then Csrrw rd rs1 csr12
                                    else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM)
                                                 (Coq.ZArith.BinInt.Z.eqb funct3 funct3_CSRRS) : bool
                                         then Csrrs rd rs1 csr12
                                         else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM)
                                                      (Coq.ZArith.BinInt.Z.eqb funct3 funct3_CSRRC) : bool
                                              then Csrrc rd rs1 csr12
                                              else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM)
                                                           (Coq.ZArith.BinInt.Z.eqb funct3 funct3_CSRRWI) : bool
                                                   then Csrrwi rd zimm csr12
                                                   else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM)
                                                                (Coq.ZArith.BinInt.Z.eqb funct3 funct3_CSRRSI) : bool
                                                        then Csrrsi rd zimm csr12
                                                        else if andb (Coq.ZArith.BinInt.Z.eqb opcode opcode_SYSTEM)
                                                                     (Coq.ZArith.BinInt.Z.eqb funct3
                                                                                              funct3_CSRRCI) : bool
                                                             then Csrrci rd zimm csr12
                                                             else InvalidCSR in
    let resultCSR :=
      match decodeCSR with
      | InvalidCSR => nil
      | _ => cons (CSRInstruction decodeCSR) nil
      end in
    let resultM64 :=
      match decodeM64 with
      | InvalidM64 => nil
      | _ => cons (M64Instruction decodeM64) nil
      end in
    let resultI64 :=
      match decodeI64 with
      | InvalidI64 => nil
      | _ => cons (I64Instruction decodeI64) nil
      end in
    let resultM :=
      match decodeM with
      | InvalidM => nil
      | _ => cons (MInstruction decodeM) nil
      end in
    let resultI :=
      match decodeI with
      | InvalidI => nil
      | _ => cons (IInstruction decodeI) nil
      end in
    let results : list Instruction :=
      Coq.Init.Datatypes.app resultI (Coq.Init.Datatypes.app (if supportsM iset : bool
                                                              then resultM
                                                              else nil) (Coq.Init.Datatypes.app
                                                              (if Coq.ZArith.BinInt.Z.eqb (bitwidth iset) 64 : bool
                                                               then resultI64
                                                               else nil) (Coq.Init.Datatypes.app (if andb
                                                                                                     (Coq.ZArith.BinInt.Z.eqb
                                                                                                      (bitwidth iset)
                                                                                                      64) (supportsM
                                                                                                      iset) : bool
                                                                                                  then resultM64
                                                                                                  else nil)
                                                                                                 resultCSR))) in
    match results with
    | cons singleResult nil => singleResult
    | nil => InvalidInstruction
    | _ => GHC.Err.error (GHC.Base.hs_string__ "ambiguous decoding result")
    end.

(* Unbound variables:
     andb bool cons false list nil orb true Coq.Init.Datatypes.app
     Coq.ZArith.BinInt.Z Coq.ZArith.BinInt.Z.eqb Coq.ZArith.BinInt.Z.lor
     Coq.ZArith.BinInt.Z.pow Coq.ZArith.BinInt.Z.shiftl Data.Bits.testBit
     GHC.Err.error GHC.Err.undefined GHC.Num.Int GHC.Num.op_zm__
     GHC.Real.fromIntegral
*)
