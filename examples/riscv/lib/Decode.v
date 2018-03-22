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
Require Data.Bits.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Real.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition MachineInt :=
  GHC.Num.Int%type.

Definition Opcode :=
  MachineInt%type.

Definition Register :=
  MachineInt%type.

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
  := Ld : Register -> Register -> MachineInt -> InstructionI64
  |  Lwu : Register -> Register -> MachineInt -> InstructionI64
  |  Addiw : Register -> Register -> MachineInt -> InstructionI64
  |  Slliw : Register -> Register -> GHC.Num.Int -> InstructionI64
  |  Srliw : Register -> Register -> GHC.Num.Int -> InstructionI64
  |  Sraiw : Register -> Register -> GHC.Num.Int -> InstructionI64
  |  Sd : Register -> Register -> MachineInt -> InstructionI64
  |  Addw : Register -> Register -> Register -> InstructionI64
  |  Subw : Register -> Register -> Register -> InstructionI64
  |  Sllw : Register -> Register -> Register -> InstructionI64
  |  Srlw : Register -> Register -> Register -> InstructionI64
  |  Sraw : Register -> Register -> Register -> InstructionI64
  |  InvalidI64 : InstructionI64.

Inductive InstructionI : Type
  := Lb : Register -> Register -> MachineInt -> InstructionI
  |  Lh : Register -> Register -> MachineInt -> InstructionI
  |  Lw : Register -> Register -> MachineInt -> InstructionI
  |  Lbu : Register -> Register -> MachineInt -> InstructionI
  |  Lhu : Register -> Register -> MachineInt -> InstructionI
  |  Fence : MachineInt -> MachineInt -> InstructionI
  |  Fence_i : InstructionI
  |  InvalidI : InstructionI.

Inductive InstructionCSR : Type
  := Ecall : InstructionCSR
  |  Ebreak : InstructionCSR
  |  Uret : InstructionCSR
  |  Sret : InstructionCSR
  |  Mret : InstructionCSR
  |  Wfi : InstructionCSR
  |  Sfence_vm : Register -> Register -> InstructionCSR
  |  Csrrw : Register -> Register -> MachineInt -> InstructionCSR
  |  Csrrs : Register -> Register -> MachineInt -> InstructionCSR
  |  Csrrc : Register -> Register -> MachineInt -> InstructionCSR
  |  Csrrwi : Register -> MachineInt -> MachineInt -> InstructionCSR
  |  Csrrsi : Register -> MachineInt -> MachineInt -> InstructionCSR
  |  Csrrci : Register -> MachineInt -> MachineInt -> InstructionCSR
  |  InvalidCSR : InstructionCSR.

Inductive Instruction : Type
  := IInstruction : InstructionI -> Instruction
  |  MInstruction : InstructionM -> Instruction
  |  I64Instruction : InstructionI64 -> Instruction
  |  M64Instruction : InstructionM64 -> Instruction
  |  CSRInstruction : InstructionCSR -> Instruction
  |  InvalidInstruction : Instruction.
(* Converted value declarations: *)

(* Translating `instance GHC.Show.Show Decode.Instruction' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Read.Read Decode.Instruction' failed: OOPS! Cannot
   find information for class Qualified "GHC.Read" "Read" unsupported *)

(* Skipping instance Eq___Instruction *)

(* Translating `instance GHC.Show.Show Decode.InstructionI' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Read.Read Decode.InstructionI' failed: OOPS! Cannot
   find information for class Qualified "GHC.Read" "Read" unsupported *)

(* Skipping instance Eq___InstructionI *)

(* Translating `instance GHC.Show.Show Decode.InstructionM' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Read.Read Decode.InstructionM' failed: OOPS! Cannot
   find information for class Qualified "GHC.Read" "Read" unsupported *)

(* Skipping instance Eq___InstructionM *)

(* Translating `instance GHC.Show.Show Decode.InstructionI64' failed: OOPS!
   Cannot find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Read.Read Decode.InstructionI64' failed: OOPS!
   Cannot find information for class Qualified "GHC.Read" "Read" unsupported *)

(* Skipping instance Eq___InstructionI64 *)

(* Translating `instance GHC.Show.Show Decode.InstructionM64' failed: OOPS!
   Cannot find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Read.Read Decode.InstructionM64' failed: OOPS!
   Cannot find information for class Qualified "GHC.Read" "Read" unsupported *)

(* Skipping instance Eq___InstructionM64 *)

(* Translating `instance GHC.Show.Show Decode.InstructionCSR' failed: OOPS!
   Cannot find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Read.Read Decode.InstructionCSR' failed: OOPS!
   Cannot find information for class Qualified "GHC.Read" "Read" unsupported *)

(* Skipping instance Eq___InstructionCSR *)

(* Translating `instance GHC.Show.Show Decode.InstructionSet' failed: OOPS!
   Cannot find information for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Eq___InstructionSet_op_zeze__
   : InstructionSet -> InstructionSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV32I, RV32I => true
    | RV32IM, RV32IM => true
    | RV64I, RV64I => true
    | RV64IM, RV64IM => true
    | _, _ => false
    end.

Local Definition Eq___InstructionSet_op_zsze__
   : InstructionSet -> InstructionSet -> bool :=
  fun a b => negb (Eq___InstructionSet_op_zeze__ a b).

Program Instance Eq___InstructionSet : GHC.Base.Eq_ InstructionSet :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___InstructionSet_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___InstructionSet_op_zsze__ |}.

Definition bitSlice {a} `{Data.Bits.Bits a} `{GHC.Num.Num a}
   : a -> GHC.Num.Int -> GHC.Num.Int -> a :=
  GHC.Err.undefined.

Definition bitwidth : InstructionSet -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
    | RV32I => 32
    | RV32IM => 32
    | RV64I => 64
    | RV64IM => 64
    end.

Definition funct12_EBREAK : MachineInt :=
  1.

Definition funct12_ECALL : MachineInt :=
  0.

Definition funct12_MRET : MachineInt :=
  770.

Definition funct12_SRET : MachineInt :=
  258.

Definition funct12_URET : MachineInt :=
  2.

Definition funct12_WFI : MachineInt :=
  261.

Definition funct3_ADD : MachineInt :=
  0.

Definition funct3_ADDI : MachineInt :=
  0.

Definition funct3_ADDIW : MachineInt :=
  0.

Definition funct3_ADDW : MachineInt :=
  0.

Definition funct3_AND : MachineInt :=
  7.

Definition funct3_ANDI : MachineInt :=
  7.

Definition funct3_BEQ : MachineInt :=
  0.

Definition funct3_BGE : MachineInt :=
  5.

Definition funct3_BGEU : MachineInt :=
  7.

Definition funct3_BLT : MachineInt :=
  4.

Definition funct3_BLTU : MachineInt :=
  6.

Definition funct3_BNE : MachineInt :=
  1.

Definition funct3_CSRRC : MachineInt :=
  3.

Definition funct3_CSRRCI : MachineInt :=
  7.

Definition funct3_CSRRS : MachineInt :=
  2.

Definition funct3_CSRRSI : MachineInt :=
  6.

Definition funct3_CSRRW : MachineInt :=
  1.

Definition funct3_CSRRWI : MachineInt :=
  5.

Definition funct3_DIV : MachineInt :=
  4.

Definition funct3_DIVU : MachineInt :=
  5.

Definition funct3_DIVUW : MachineInt :=
  5.

Definition funct3_DIVW : MachineInt :=
  4.

Definition funct3_FENCE : MachineInt :=
  0.

Definition funct3_FENCE_I : MachineInt :=
  1.

Definition funct3_LB : MachineInt :=
  0.

Definition funct3_LBU : MachineInt :=
  4.

Definition funct3_LD : MachineInt :=
  3.

Definition funct3_LH : MachineInt :=
  1.

Definition funct3_LHU : MachineInt :=
  5.

Definition funct3_LW : MachineInt :=
  2.

Definition funct3_LWU : MachineInt :=
  6.

Definition funct3_MUL : MachineInt :=
  0.

Definition funct3_MULH : MachineInt :=
  1.

Definition funct3_MULHSU : MachineInt :=
  2.

Definition funct3_MULHU : MachineInt :=
  3.

Definition funct3_MULW : MachineInt :=
  0.

Definition funct3_OR : MachineInt :=
  6.

Definition funct3_ORI : MachineInt :=
  6.

Definition funct3_PRIV : MachineInt :=
  0.

Definition funct3_REM : MachineInt :=
  6.

Definition funct3_REMU : MachineInt :=
  7.

Definition funct3_REMUW : MachineInt :=
  7.

Definition funct3_REMW : MachineInt :=
  6.

Definition funct3_SB : MachineInt :=
  0.

Definition funct3_SD : MachineInt :=
  3.

Definition funct3_SH : MachineInt :=
  1.

Definition funct3_SLL : MachineInt :=
  1.

Definition funct3_SLLI : MachineInt :=
  1.

Definition funct3_SLLIW : MachineInt :=
  1.

Definition funct3_SLLW : MachineInt :=
  1.

Definition funct3_SLT : MachineInt :=
  2.

Definition funct3_SLTI : MachineInt :=
  2.

Definition funct3_SLTIU : MachineInt :=
  3.

Definition funct3_SLTU : MachineInt :=
  3.

Definition funct3_SRA : MachineInt :=
  5.

Definition funct3_SRAI : MachineInt :=
  5.

Definition funct3_SRAIW : MachineInt :=
  5.

Definition funct3_SRAW : MachineInt :=
  5.

Definition funct3_SRL : MachineInt :=
  5.

Definition funct3_SRLI : MachineInt :=
  5.

Definition funct3_SRLIW : MachineInt :=
  5.

Definition funct3_SRLW : MachineInt :=
  5.

Definition funct3_SUB : MachineInt :=
  0.

Definition funct3_SUBW : MachineInt :=
  0.

Definition funct3_SW : MachineInt :=
  2.

Definition funct3_XOR : MachineInt :=
  4.

Definition funct3_XORI : MachineInt :=
  4.

Definition funct6_SLLI : MachineInt :=
  0.

Definition funct6_SRAI : MachineInt :=
  16.

Definition funct6_SRLI : MachineInt :=
  0.

Definition funct7_ADD : MachineInt :=
  0.

Definition funct7_ADDW : MachineInt :=
  0.

Definition funct7_AND : MachineInt :=
  0.

Definition funct7_DIV : MachineInt :=
  1.

Definition funct7_DIVU : MachineInt :=
  1.

Definition funct7_DIVUW : MachineInt :=
  1.

Definition funct7_DIVW : MachineInt :=
  1.

Definition funct7_MUL : MachineInt :=
  1.

Definition funct7_MULH : MachineInt :=
  1.

Definition funct7_MULHSU : MachineInt :=
  1.

Definition funct7_MULHU : MachineInt :=
  1.

Definition funct7_MULW : MachineInt :=
  1.

Definition funct7_OR : MachineInt :=
  0.

Definition funct7_REM : MachineInt :=
  1.

Definition funct7_REMU : MachineInt :=
  1.

Definition funct7_REMUW : MachineInt :=
  1.

Definition funct7_REMW : MachineInt :=
  1.

Definition funct7_SFENCE_VM : MachineInt :=
  9.

Definition funct7_SLL : MachineInt :=
  0.

Definition funct7_SLLIW : MachineInt :=
  0.

Definition funct7_SLLW : MachineInt :=
  0.

Definition funct7_SLT : MachineInt :=
  0.

Definition funct7_SLTU : MachineInt :=
  0.

Definition funct7_SRA : MachineInt :=
  32.

Definition funct7_SRAIW : MachineInt :=
  32.

Definition funct7_SRAW : MachineInt :=
  32.

Definition funct7_SRL : MachineInt :=
  0.

Definition funct7_SRLIW : MachineInt :=
  0.

Definition funct7_SRLW : MachineInt :=
  0.

Definition funct7_SUB : MachineInt :=
  32.

Definition funct7_SUBW : MachineInt :=
  32.

Definition funct7_XOR : MachineInt :=
  0.

Definition machineIntToShamt : MachineInt -> GHC.Num.Int :=
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

Definition signExtend : GHC.Num.Int -> MachineInt -> MachineInt :=
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

Definition decode : InstructionSet -> MachineInt -> Instruction :=
  fun iset inst =>
    let zimm := bitSlice inst 15 20 in
    let funct6 := bitSlice inst 26 32 in
    let shamtHi := bitSlice inst 25 26 in
    let shamtHiTest := orb (shamtHi GHC.Base.== 0) (bitwidth iset GHC.Base.== 64) in
    let shamt6 := machineIntToShamt (bitSlice inst 20 26) in
    let shamt5 := machineIntToShamt (bitSlice inst 20 25) in
    let sbimm12 :=
      signExtend 13 (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.lor
                                              (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst 31 32)
                                                                        12) (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst
                                                                                                         25 31) 5))
                                              (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst 8 12) 1))
                                             (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst 7 8) 11)) in
    let simm12 :=
      signExtend 12 (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.shiftl (bitSlice
                                                                          inst 25 32) 5) (bitSlice inst 7 12)) in
    let csr12 := bitSlice inst 20 32 in
    let oimm12 := signExtend 12 (bitSlice inst 20 32) in
    let imm12 := signExtend 12 (bitSlice inst 20 32) in
    let jimm20 :=
      signExtend 21 (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.lor
                                              (Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst 31 32)
                                                                        20) (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst
                                                                                                         21 31) 1))
                                              (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst 20 21) 11))
                                             (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst 12 20) 12)) in
    let oimm20 :=
      signExtend 32 (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst 12 32) 12) in
    let imm20 :=
      signExtend 32 (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst 12 32) 12) in
    let msb4 := bitSlice inst 28 32 in
    let pred := bitSlice inst 24 28 in
    let succ := bitSlice inst 20 24 in
    let rs3 := bitSlice inst 27 32 in
    let rs2 := bitSlice inst 20 25 in
    let rs1 := bitSlice inst 15 20 in
    let rd := bitSlice inst 7 12 in
    let funct12 := bitSlice inst 20 32 in
    let funct10 :=
      Coq.ZArith.BinInt.Z.lor (Coq.ZArith.BinInt.Z.shiftl (bitSlice inst 25 32) 3)
                              (bitSlice inst 12 15) in
    let funct7 := bitSlice inst 25 32 in
    let funct3 := bitSlice inst 12 15 in
    let opcode := bitSlice inst 0 7 in
    let decodeI :=
      if andb (opcode GHC.Base.== opcode_LOAD) (funct3 GHC.Base.== funct3_LB) : bool
      then Lb rd rs1 oimm12
      else if andb (opcode GHC.Base.== opcode_LOAD) (funct3 GHC.Base.==
                    funct3_LH) : bool
           then Lh rd rs1 oimm12
           else if andb (opcode GHC.Base.== opcode_LOAD) (funct3 GHC.Base.==
                         funct3_LW) : bool
                then Lw rd rs1 oimm12
                else if andb (opcode GHC.Base.== opcode_LOAD) (funct3 GHC.Base.==
                              funct3_LBU) : bool
                     then Lbu rd rs1 oimm12
                     else if andb (opcode GHC.Base.== opcode_LOAD) (funct3 GHC.Base.==
                                   funct3_LHU) : bool
                          then Lhu rd rs1 oimm12
                          else if andb (opcode GHC.Base.== opcode_MISC_MEM) (andb (rd GHC.Base.== 0) (andb
                                                                                   (funct3 GHC.Base.== funct3_FENCE)
                                                                                   (andb (rs1 GHC.Base.== 0) (msb4
                                                                                          GHC.Base.==
                                                                                          0)))) : bool
                               then Fence pred succ
                               else if andb (opcode GHC.Base.== opcode_MISC_MEM) (andb (rd GHC.Base.== 0) (andb
                                                                                        (funct3 GHC.Base.==
                                                                                         funct3_FENCE_I) (andb (rs1
                                                                                                                GHC.Base.==
                                                                                                                0)
                                                                                                               (imm12
                                                                                                                GHC.Base.==
                                                                                                                0)))) : bool
                                    then Fence_i
                                    else InvalidI in
    let decodeM :=
      if andb (opcode GHC.Base.== opcode_OP) (andb (funct3 GHC.Base.== funct3_MUL)
                                                   (funct7 GHC.Base.== funct7_MUL)) : bool
      then Mul rd rs1 rs2
      else if andb (opcode GHC.Base.== opcode_OP) (andb (funct3 GHC.Base.==
                                                         funct3_MULH) (funct7 GHC.Base.== funct7_MULH)) : bool
           then Mulh rd rs1 rs2
           else if andb (opcode GHC.Base.== opcode_OP) (andb (funct3 GHC.Base.==
                                                              funct3_MULHSU) (funct7 GHC.Base.== funct7_MULHSU)) : bool
                then Mulhsu rd rs1 rs2
                else if andb (opcode GHC.Base.== opcode_OP) (andb (funct3 GHC.Base.==
                                                                   funct3_MULHU) (funct7 GHC.Base.==
                                                                   funct7_MULHU)) : bool
                     then Mulhu rd rs1 rs2
                     else if andb (opcode GHC.Base.== opcode_OP) (andb (funct3 GHC.Base.==
                                                                        funct3_DIV) (funct7 GHC.Base.==
                                                                        funct7_DIV)) : bool
                          then Div rd rs1 rs2
                          else if andb (opcode GHC.Base.== opcode_OP) (andb (funct3 GHC.Base.==
                                                                             funct3_DIVU) (funct7 GHC.Base.==
                                                                             funct7_DIVU)) : bool
                               then Divu rd rs1 rs2
                               else if andb (opcode GHC.Base.== opcode_OP) (andb (funct3 GHC.Base.==
                                                                                  funct3_REM) (funct7 GHC.Base.==
                                                                                  funct7_REM)) : bool
                                    then Rem rd rs1 rs2
                                    else if andb (opcode GHC.Base.== opcode_OP) (andb (funct3 GHC.Base.==
                                                                                       funct3_REMU) (funct7 GHC.Base.==
                                                                                       funct7_REMU)) : bool
                                         then Remu rd rs1 rs2
                                         else InvalidM in
    let decodeI64 :=
      if andb (opcode GHC.Base.== opcode_LOAD) (funct3 GHC.Base.== funct3_LD) : bool
      then Ld rd rs1 oimm12
      else if andb (opcode GHC.Base.== opcode_LOAD) (funct3 GHC.Base.==
                    funct3_LWU) : bool
           then Lwu rd rs1 oimm12
           else if andb (opcode GHC.Base.== opcode_OP_IMM_32) (funct3 GHC.Base.==
                         funct3_ADDIW) : bool
                then Addiw rd rs1 imm12
                else if andb (opcode GHC.Base.== opcode_OP_IMM_32) (andb (funct3 GHC.Base.==
                                                                          funct3_SLLIW) (funct7 GHC.Base.==
                                                                          funct7_SLLIW)) : bool
                     then Slliw rd rs1 shamt5
                     else if andb (opcode GHC.Base.== opcode_OP_IMM_32) (andb (funct3 GHC.Base.==
                                                                               funct3_SRLIW) (funct7 GHC.Base.==
                                                                               funct7_SRLIW)) : bool
                          then Srliw rd rs1 shamt5
                          else if andb (opcode GHC.Base.== opcode_OP_IMM_32) (andb (funct3 GHC.Base.==
                                                                                    funct3_SRAIW) (funct7 GHC.Base.==
                                                                                    funct7_SRAIW)) : bool
                               then Sraiw rd rs1 shamt5
                               else if andb (opcode GHC.Base.== opcode_STORE) (funct3 GHC.Base.==
                                             funct3_SD) : bool
                                    then Sd rs1 rs2 simm12
                                    else if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3 GHC.Base.==
                                                                                          funct3_ADDW) (funct7
                                                                                          GHC.Base.==
                                                                                          funct7_ADDW)) : bool
                                         then Addw rd rs1 rs2
                                         else if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3 GHC.Base.==
                                                                                               funct3_SUBW) (funct7
                                                                                               GHC.Base.==
                                                                                               funct7_SUBW)) : bool
                                              then Subw rd rs1 rs2
                                              else if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3 GHC.Base.==
                                                                                                    funct3_SLLW) (funct7
                                                                                                    GHC.Base.==
                                                                                                    funct7_SLLW)) : bool
                                                   then Sllw rd rs1 rs2
                                                   else if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3
                                                                                                         GHC.Base.==
                                                                                                         funct3_SRLW)
                                                                                                        (funct7
                                                                                                         GHC.Base.==
                                                                                                         funct7_SRLW)) : bool
                                                        then Srlw rd rs1 rs2
                                                        else if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3
                                                                                                              GHC.Base.==
                                                                                                              funct3_SRAW)
                                                                                                             (funct7
                                                                                                              GHC.Base.==
                                                                                                              funct7_SRAW)) : bool
                                                             then Sraw rd rs1 rs2
                                                             else InvalidI64 in
    let decodeM64 :=
      if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3 GHC.Base.== funct3_MULW)
                                                      (funct7 GHC.Base.== funct7_MULW)) : bool
      then Mulw rd rs1 rs2
      else if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3 GHC.Base.==
                                                            funct3_DIVW) (funct7 GHC.Base.== funct7_DIVW)) : bool
           then Divw rd rs1 rs2
           else if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3 GHC.Base.==
                                                                 funct3_DIVUW) (funct7 GHC.Base.== funct7_DIVUW)) : bool
                then Divuw rd rs1 rs2
                else if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3 GHC.Base.==
                                                                      funct3_REMW) (funct7 GHC.Base.==
                                                                      funct7_REMW)) : bool
                     then Remw rd rs1 rs2
                     else if andb (opcode GHC.Base.== opcode_OP_32) (andb (funct3 GHC.Base.==
                                                                           funct3_REMUW) (funct7 GHC.Base.==
                                                                           funct7_REMUW)) : bool
                          then Remuw rd rs1 rs2
                          else InvalidM64 in
    let decodeCSR :=
      if andb (opcode GHC.Base.== opcode_SYSTEM) (andb (rd GHC.Base.== 0) (andb
                                                        (funct3 GHC.Base.== funct3_PRIV) (andb (rs1 GHC.Base.== 0)
                                                                                               (funct12 GHC.Base.==
                                                                                                funct12_ECALL)))) : bool
      then Ecall
      else if andb (opcode GHC.Base.== opcode_SYSTEM) (andb (rd GHC.Base.== 0) (andb
                                                             (funct3 GHC.Base.== funct3_PRIV) (andb (rs1 GHC.Base.== 0)
                                                                                                    (funct12 GHC.Base.==
                                                                                                     funct12_EBREAK)))) : bool
           then Ebreak
           else if andb (opcode GHC.Base.== opcode_SYSTEM) (andb (rd GHC.Base.== 0) (andb
                                                                  (funct3 GHC.Base.== funct3_PRIV) (andb (rs1
                                                                                                          GHC.Base.==
                                                                                                          0) (funct12
                                                                                                          GHC.Base.==
                                                                                                          funct12_URET)))) : bool
                then Uret
                else if andb (opcode GHC.Base.== opcode_SYSTEM) (andb (rd GHC.Base.== 0) (andb
                                                                       (funct3 GHC.Base.== funct3_PRIV) (andb (rs1
                                                                                                               GHC.Base.==
                                                                                                               0)
                                                                                                              (funct12
                                                                                                               GHC.Base.==
                                                                                                               funct12_SRET)))) : bool
                     then Sret
                     else if andb (opcode GHC.Base.== opcode_SYSTEM) (andb (rd GHC.Base.== 0) (andb
                                                                            (funct3 GHC.Base.== funct3_PRIV) (andb (rs1
                                                                                                                    GHC.Base.==
                                                                                                                    0)
                                                                                                                   (funct12
                                                                                                                    GHC.Base.==
                                                                                                                    funct12_MRET)))) : bool
                          then Mret
                          else if andb (opcode GHC.Base.== opcode_SYSTEM) (andb (rd GHC.Base.== 0) (andb
                                                                                 (funct3 GHC.Base.== funct3_PRIV) (andb
                                                                                  (rs1 GHC.Base.== 0) (funct12
                                                                                   GHC.Base.==
                                                                                   funct12_WFI)))) : bool
                               then Wfi
                               else if andb (opcode GHC.Base.== opcode_SYSTEM) (funct3 GHC.Base.==
                                             funct3_CSRRW) : bool
                                    then Csrrw rd rs1 csr12
                                    else if andb (opcode GHC.Base.== opcode_SYSTEM) (funct3 GHC.Base.==
                                                  funct3_CSRRS) : bool
                                         then Csrrs rd rs1 csr12
                                         else if andb (opcode GHC.Base.== opcode_SYSTEM) (funct3 GHC.Base.==
                                                       funct3_CSRRC) : bool
                                              then Csrrc rd rs1 csr12
                                              else if andb (opcode GHC.Base.== opcode_SYSTEM) (funct3 GHC.Base.==
                                                            funct3_CSRRWI) : bool
                                                   then Csrrwi rd zimm csr12
                                                   else if andb (opcode GHC.Base.== opcode_SYSTEM) (funct3 GHC.Base.==
                                                                 funct3_CSRRSI) : bool
                                                        then Csrrsi rd zimm csr12
                                                        else if andb (opcode GHC.Base.== opcode_SYSTEM) (funct3
                                                                      GHC.Base.==
                                                                      funct3_CSRRCI) : bool
                                                             then Csrrci rd zimm csr12
                                                             else InvalidCSR in
    let resultCSR :=
      if decodeCSR GHC.Base.== InvalidCSR : bool
      then nil
      else cons (CSRInstruction decodeCSR) nil in
    let resultM64 :=
      if decodeM64 GHC.Base.== InvalidM64 : bool
      then nil
      else cons (M64Instruction decodeM64) nil in
    let resultI64 :=
      if decodeI64 GHC.Base.== InvalidI64 : bool
      then nil
      else cons (I64Instruction decodeI64) nil in
    let resultM :=
      if decodeM GHC.Base.== InvalidM : bool
      then nil
      else cons (MInstruction decodeM) nil in
    let resultI :=
      if decodeI GHC.Base.== InvalidI : bool
      then nil
      else cons (IInstruction decodeI) nil in
    let results : list Instruction :=
      Coq.Init.Datatypes.app resultI (Coq.Init.Datatypes.app (if supportsM iset : bool
                                                              then resultM
                                                              else nil) (Coq.Init.Datatypes.app (if bitwidth iset
                                                                                                    GHC.Base.==
                                                                                                    64 : bool
                                                                                                 then resultI64
                                                                                                 else nil)
                                                                                                (Coq.Init.Datatypes.app
                                                                                                 (if andb (bitwidth iset
                                                                                                           GHC.Base.==
                                                                                                           64)
                                                                                                          (supportsM
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
     andb bool cons false list negb nil orb true Coq.Init.Datatypes.app
     Coq.ZArith.BinInt.Z.lor Coq.ZArith.BinInt.Z.pow Coq.ZArith.BinInt.Z.shiftl
     Data.Bits.Bits Data.Bits.testBit GHC.Base.Eq_ GHC.Base.op_zeze__ GHC.Err.error
     GHC.Err.undefined GHC.Num.Int GHC.Num.Num GHC.Num.op_zm__ GHC.Real.fromIntegral
*)
