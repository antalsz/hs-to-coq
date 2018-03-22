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

Definition bitSlice : Coq.ZArith.BinInt.Z -> Coq.ZArith.BinInt.Z -> Coq.ZArith.BinInt.Z ->  Coq.ZArith.BinInt.Z.
Admitted.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Import Coq.ZArith.BinInt.

(* Converted type declarations: *)

Definition Register :=
  Z%type.

Definition Opcode :=
  Z%type.

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
  := Ld : Register -> Register -> Z -> InstructionI64
  |  Lwu : Register -> Register -> Z -> InstructionI64
  |  Addiw : Register -> Register -> Z -> InstructionI64
  |  Slliw : Register -> Register -> Z -> InstructionI64
  |  Srliw : Register -> Register -> Z -> InstructionI64
  |  Sraiw : Register -> Register -> Z -> InstructionI64
  |  Sd : Register -> Register -> Z -> InstructionI64
  |  Addw : Register -> Register -> Register -> InstructionI64
  |  Subw : Register -> Register -> Register -> InstructionI64
  |  Sllw : Register -> Register -> Register -> InstructionI64
  |  Srlw : Register -> Register -> Register -> InstructionI64
  |  Sraw : Register -> Register -> Register -> InstructionI64
  |  InvalidI64 : InstructionI64.

Inductive InstructionI : Type
  := Lb : Register -> Register -> Z -> InstructionI
  |  Lh : Register -> Register -> Z -> InstructionI
  |  Lw : Register -> Register -> Z -> InstructionI
  |  Lbu : Register -> Register -> Z -> InstructionI
  |  Lhu : Register -> Register -> Z -> InstructionI
  |  Fence : Z -> Z -> InstructionI
  |  Fence_i : InstructionI
  |  Addi : Register -> Register -> Z -> InstructionI
  |  Slli : Register -> Register -> Z -> InstructionI
  |  Slti : Register -> Register -> Z -> InstructionI
  |  Sltiu : Register -> Register -> Z -> InstructionI
  |  Xori : Register -> Register -> Z -> InstructionI
  |  Ori : Register -> Register -> Z -> InstructionI
  |  Andi : Register -> Register -> Z -> InstructionI
  |  Srli : Register -> Register -> Z -> InstructionI
  |  Srai : Register -> Register -> Z -> InstructionI
  |  Auipc : Register -> Z -> InstructionI
  |  Sb : Register -> Register -> Z -> InstructionI
  |  Sh : Register -> Register -> Z -> InstructionI
  |  Sw : Register -> Register -> Z -> InstructionI
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
  |  Lui : Register -> Z -> InstructionI
  |  Beq : Register -> Register -> Z -> InstructionI
  |  Bne : Register -> Register -> Z -> InstructionI
  |  Blt : Register -> Register -> Z -> InstructionI
  |  Bge : Register -> Register -> Z -> InstructionI
  |  Bltu : Register -> Register -> Z -> InstructionI
  |  Bgeu : Register -> Register -> Z -> InstructionI
  |  Jalr : Register -> Register -> Z -> InstructionI
  |  Jal : Register -> Z -> InstructionI
  |  InvalidI : InstructionI.

Inductive InstructionCSR : Type
  := Ecall : InstructionCSR
  |  Ebreak : InstructionCSR
  |  Uret : InstructionCSR
  |  Sret : InstructionCSR
  |  Mret : InstructionCSR
  |  Wfi : InstructionCSR
  |  Sfence_vm : Register -> Register -> InstructionCSR
  |  Csrrw : Register -> Register -> Z -> InstructionCSR
  |  Csrrs : Register -> Register -> Z -> InstructionCSR
  |  Csrrc : Register -> Register -> Z -> InstructionCSR
  |  Csrrwi : Register -> Z -> Z -> InstructionCSR
  |  Csrrsi : Register -> Z -> Z -> InstructionCSR
  |  Csrrci : Register -> Z -> Z -> InstructionCSR
  |  InvalidCSR : InstructionCSR.

Inductive Instruction : Type
  := IInstruction : InstructionI -> Instruction
  |  MInstruction : InstructionM -> Instruction
  |  I64Instruction : InstructionI64 -> Instruction
  |  M64Instruction : InstructionM64 -> Instruction
  |  CSRInstruction : InstructionCSR -> Instruction
  |  InvalidInstruction : Instruction.
(* Converted value declarations: *)

Definition bitwidth : InstructionSet -> Z :=
  fun arg_0__ =>
    match arg_0__ with
    | RV32I => 32
    | RV32IM => 32
    | RV64I => 64
    | RV64IM => 64
    end.

Definition funct12_EBREAK : Z :=
  1.

Definition funct12_ECALL : Z :=
  0.

Definition funct12_MRET : Z :=
  770.

Definition funct12_SRET : Z :=
  258.

Definition funct12_URET : Z :=
  2.

Definition funct12_WFI : Z :=
  261.

Definition funct3_ADD : Z :=
  0.

Definition funct3_ADDI : Z :=
  0.

Definition funct3_ADDIW : Z :=
  0.

Definition funct3_ADDW : Z :=
  0.

Definition funct3_AND : Z :=
  7.

Definition funct3_ANDI : Z :=
  7.

Definition funct3_BEQ : Z :=
  0.

Definition funct3_BGE : Z :=
  5.

Definition funct3_BGEU : Z :=
  7.

Definition funct3_BLT : Z :=
  4.

Definition funct3_BLTU : Z :=
  6.

Definition funct3_BNE : Z :=
  1.

Definition funct3_CSRRC : Z :=
  3.

Definition funct3_CSRRCI : Z :=
  7.

Definition funct3_CSRRS : Z :=
  2.

Definition funct3_CSRRSI : Z :=
  6.

Definition funct3_CSRRW : Z :=
  1.

Definition funct3_CSRRWI : Z :=
  5.

Definition funct3_DIV : Z :=
  4.

Definition funct3_DIVU : Z :=
  5.

Definition funct3_DIVUW : Z :=
  5.

Definition funct3_DIVW : Z :=
  4.

Definition funct3_FENCE : Z :=
  0.

Definition funct3_FENCE_I : Z :=
  1.

Definition funct3_LB : Z :=
  0.

Definition funct3_LBU : Z :=
  4.

Definition funct3_LD : Z :=
  3.

Definition funct3_LH : Z :=
  1.

Definition funct3_LHU : Z :=
  5.

Definition funct3_LW : Z :=
  2.

Definition funct3_LWU : Z :=
  6.

Definition funct3_MUL : Z :=
  0.

Definition funct3_MULH : Z :=
  1.

Definition funct3_MULHSU : Z :=
  2.

Definition funct3_MULHU : Z :=
  3.

Definition funct3_MULW : Z :=
  0.

Definition funct3_OR : Z :=
  6.

Definition funct3_ORI : Z :=
  6.

Definition funct3_PRIV : Z :=
  0.

Definition funct3_REM : Z :=
  6.

Definition funct3_REMU : Z :=
  7.

Definition funct3_REMUW : Z :=
  7.

Definition funct3_REMW : Z :=
  6.

Definition funct3_SB : Z :=
  0.

Definition funct3_SD : Z :=
  3.

Definition funct3_SH : Z :=
  1.

Definition funct3_SLL : Z :=
  1.

Definition funct3_SLLI : Z :=
  1.

Definition funct3_SLLIW : Z :=
  1.

Definition funct3_SLLW : Z :=
  1.

Definition funct3_SLT : Z :=
  2.

Definition funct3_SLTI : Z :=
  2.

Definition funct3_SLTIU : Z :=
  3.

Definition funct3_SLTU : Z :=
  3.

Definition funct3_SRA : Z :=
  5.

Definition funct3_SRAI : Z :=
  5.

Definition funct3_SRAIW : Z :=
  5.

Definition funct3_SRAW : Z :=
  5.

Definition funct3_SRL : Z :=
  5.

Definition funct3_SRLI : Z :=
  5.

Definition funct3_SRLIW : Z :=
  5.

Definition funct3_SRLW : Z :=
  5.

Definition funct3_SUB : Z :=
  0.

Definition funct3_SUBW : Z :=
  0.

Definition funct3_SW : Z :=
  2.

Definition funct3_XOR : Z :=
  4.

Definition funct3_XORI : Z :=
  4.

Definition funct6_SLLI : Z :=
  0.

Definition funct6_SRAI : Z :=
  16.

Definition funct6_SRLI : Z :=
  0.

Definition funct7_ADD : Z :=
  0.

Definition funct7_ADDW : Z :=
  0.

Definition funct7_AND : Z :=
  0.

Definition funct7_DIV : Z :=
  1.

Definition funct7_DIVU : Z :=
  1.

Definition funct7_DIVUW : Z :=
  1.

Definition funct7_DIVW : Z :=
  1.

Definition funct7_MUL : Z :=
  1.

Definition funct7_MULH : Z :=
  1.

Definition funct7_MULHSU : Z :=
  1.

Definition funct7_MULHU : Z :=
  1.

Definition funct7_MULW : Z :=
  1.

Definition funct7_OR : Z :=
  0.

Definition funct7_REM : Z :=
  1.

Definition funct7_REMU : Z :=
  1.

Definition funct7_REMUW : Z :=
  1.

Definition funct7_REMW : Z :=
  1.

Definition funct7_SFENCE_VM : Z :=
  9.

Definition funct7_SLL : Z :=
  0.

Definition funct7_SLLIW : Z :=
  0.

Definition funct7_SLLW : Z :=
  0.

Definition funct7_SLT : Z :=
  0.

Definition funct7_SLTU : Z :=
  0.

Definition funct7_SRA : Z :=
  32.

Definition funct7_SRAIW : Z :=
  32.

Definition funct7_SRAW : Z :=
  32.

Definition funct7_SRL : Z :=
  0.

Definition funct7_SRLIW : Z :=
  0.

Definition funct7_SRLW : Z :=
  0.

Definition funct7_SUB : Z :=
  32.

Definition funct7_SUBW : Z :=
  32.

Definition funct7_XOR : Z :=
  0.

Definition machineIntToShamt : Z -> Z :=
  id.

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

Definition signExtend : Z -> Z -> Z :=
  fun l n => if Z.testbit n (Z.sub l 1) : bool then Z.sub n (Z.pow 2 l) else n.

Definition supportsM : InstructionSet -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | RV32I => false
    | RV32IM => true
    | RV64I => false
    | RV64IM => true
    end.

Definition decode : InstructionSet -> Z -> Instruction :=
  fun iset inst =>
    let zimm := bitSlice inst 15 20 in
    let funct6 := bitSlice inst 26 32 in
    let shamtHi := bitSlice inst 25 26 in
    let shamtHiTest := orb (Z.eqb shamtHi 0) (Z.eqb (bitwidth iset) 64) in
    let shamt6 := machineIntToShamt (bitSlice inst 20 26) in
    let shamt5 := machineIntToShamt (bitSlice inst 20 25) in
    let sbimm12 :=
      signExtend 13 (Z.lor (Z.lor (Z.lor (Z.shiftl (bitSlice inst 31 32) 12) (Z.shiftl
                                          (bitSlice inst 25 31) 5)) (Z.shiftl (bitSlice inst 8 12) 1)) (Z.shiftl
                            (bitSlice inst 7 8) 11)) in
    let simm12 :=
      signExtend 12 (Z.lor (Z.shiftl (bitSlice inst 25 32) 5) (bitSlice inst 7 12)) in
    let csr12 := bitSlice inst 20 32 in
    let oimm12 := signExtend 12 (bitSlice inst 20 32) in
    let imm12 := signExtend 12 (bitSlice inst 20 32) in
    let jimm20 :=
      signExtend 21 (Z.lor (Z.lor (Z.lor (Z.shiftl (bitSlice inst 31 32) 20) (Z.shiftl
                                          (bitSlice inst 21 31) 1)) (Z.shiftl (bitSlice inst 20 21) 11)) (Z.shiftl
                            (bitSlice inst 12 20) 12)) in
    let oimm20 := signExtend 32 (Z.shiftl (bitSlice inst 12 32) 12) in
    let imm20 := signExtend 32 (Z.shiftl (bitSlice inst 12 32) 12) in
    let msb4 := bitSlice inst 28 32 in
    let pred := bitSlice inst 24 28 in
    let succ := bitSlice inst 20 24 in
    let rs3 := bitSlice inst 27 32 in
    let rs2 := bitSlice inst 20 25 in
    let rs1 := bitSlice inst 15 20 in
    let rd := bitSlice inst 7 12 in
    let funct12 := bitSlice inst 20 32 in
    let funct10 := Z.lor (Z.shiftl (bitSlice inst 25 32) 3) (bitSlice inst 12 15) in
    let funct7 := bitSlice inst 25 32 in
    let funct3 := bitSlice inst 12 15 in
    let opcode := bitSlice inst 0 7 in
    let decodeI :=
      if andb (Z.eqb opcode opcode_LOAD) (Z.eqb funct3 funct3_LB) : bool
      then Lb rd rs1 oimm12
      else if andb (Z.eqb opcode opcode_LOAD) (Z.eqb funct3 funct3_LH) : bool
           then Lh rd rs1 oimm12
           else if andb (Z.eqb opcode opcode_LOAD) (Z.eqb funct3 funct3_LW) : bool
                then Lw rd rs1 oimm12
                else if andb (Z.eqb opcode opcode_LOAD) (Z.eqb funct3 funct3_LBU) : bool
                     then Lbu rd rs1 oimm12
                     else if andb (Z.eqb opcode opcode_LOAD) (Z.eqb funct3 funct3_LHU) : bool
                          then Lhu rd rs1 oimm12
                          else if andb (Z.eqb opcode opcode_MISC_MEM) (andb (Z.eqb rd 0) (andb (Z.eqb
                                                                                                funct3 funct3_FENCE)
                                                                                               (andb (Z.eqb rs1 0)
                                                                                                     (Z.eqb msb4
                                                                                                            0)))) : bool
                               then Fence pred succ
                               else if andb (Z.eqb opcode opcode_MISC_MEM) (andb (Z.eqb rd 0) (andb (Z.eqb
                                                                                                     funct3
                                                                                                     funct3_FENCE_I)
                                                                                                    (andb (Z.eqb rs1 0)
                                                                                                          (Z.eqb imm12
                                                                                                                 0)))) : bool
                                    then Fence_i
                                    else if andb (Z.eqb opcode opcode_OP_IMM) (Z.eqb funct3 funct3_ADDI) : bool
                                         then Addi rd rs1 imm12
                                         else if andb (Z.eqb opcode opcode_OP_IMM) (Z.eqb funct3 funct3_SLTI) : bool
                                              then Slti rd rs1 imm12
                                              else if andb (Z.eqb opcode opcode_OP_IMM) (Z.eqb funct3
                                                                                               funct3_SLTIU) : bool
                                                   then Sltiu rd rs1 imm12
                                                   else if andb (Z.eqb opcode opcode_OP_IMM) (Z.eqb funct3
                                                                                                    funct3_XORI) : bool
                                                        then Xori rd rs1 imm12
                                                        else if andb (Z.eqb opcode opcode_OP_IMM) (Z.eqb funct3
                                                                                                         funct3_ORI) : bool
                                                             then Ori rd rs1 imm12
                                                             else if andb (Z.eqb opcode opcode_OP_IMM) (Z.eqb funct3
                                                                                                              funct3_ANDI) : bool
                                                                  then Andi rd rs1 imm12
                                                                  else if andb (Z.eqb opcode opcode_OP_IMM) (andb (Z.eqb
                                                                                                                   funct3
                                                                                                                   funct3_SLLI)
                                                                                                                  (andb
                                                                                                                   (Z.eqb
                                                                                                                    funct6
                                                                                                                    funct6_SLLI)
                                                                                                                   shamtHiTest)) : bool
                                                                       then Slli rd rs1 shamt6
                                                                       else if andb (Z.eqb opcode opcode_OP_IMM) (andb
                                                                                     (Z.eqb funct3 funct3_SRLI) (andb
                                                                                      (Z.eqb funct6 funct6_SRLI)
                                                                                      shamtHiTest)) : bool
                                                                            then Srli rd rs1 shamt6
                                                                            else if andb (Z.eqb opcode opcode_OP_IMM)
                                                                                         (andb (Z.eqb funct3
                                                                                                      funct3_SRAI) (andb
                                                                                                (Z.eqb funct6
                                                                                                       funct6_SRAI)
                                                                                                shamtHiTest)) : bool
                                                                                 then Srai rd rs1 shamt6
                                                                                 else if Z.eqb opcode
                                                                                               opcode_AUIPC : bool
                                                                                      then Auipc rd oimm20
                                                                                      else if andb (Z.eqb opcode
                                                                                                          opcode_STORE)
                                                                                                   (Z.eqb funct3
                                                                                                          funct3_SB) : bool
                                                                                           then Sb rs1 rs2 simm12
                                                                                           else if andb (Z.eqb opcode
                                                                                                               opcode_STORE)
                                                                                                        (Z.eqb funct3
                                                                                                               funct3_SH) : bool
                                                                                                then Sh rs1 rs2 simm12
                                                                                                else if andb (Z.eqb
                                                                                                              opcode
                                                                                                              opcode_STORE)
                                                                                                             (Z.eqb
                                                                                                              funct3
                                                                                                              funct3_SW) : bool
                                                                                                     then Sw rs1 rs2
                                                                                                          simm12
                                                                                                     else if andb (Z.eqb
                                                                                                                   opcode
                                                                                                                   opcode_OP)
                                                                                                                  (andb
                                                                                                                   (Z.eqb
                                                                                                                    funct3
                                                                                                                    funct3_ADD)
                                                                                                                   (Z.eqb
                                                                                                                    funct7
                                                                                                                    funct7_ADD)) : bool
                                                                                                          then Add rd
                                                                                                               rs1 rs2
                                                                                                          else if andb
                                                                                                                  (Z.eqb
                                                                                                                   opcode
                                                                                                                   opcode_OP)
                                                                                                                  (andb
                                                                                                                   (Z.eqb
                                                                                                                    funct3
                                                                                                                    funct3_SUB)
                                                                                                                   (Z.eqb
                                                                                                                    funct7
                                                                                                                    funct7_SUB)) : bool
                                                                                                               then Sub
                                                                                                                    rd
                                                                                                                    rs1
                                                                                                                    rs2
                                                                                                               else if andb
                                                                                                                       (Z.eqb
                                                                                                                        opcode
                                                                                                                        opcode_OP)
                                                                                                                       (andb
                                                                                                                        (Z.eqb
                                                                                                                         funct3
                                                                                                                         funct3_SLL)
                                                                                                                        (Z.eqb
                                                                                                                         funct7
                                                                                                                         funct7_SLL)) : bool
                                                                                                                    then Sll
                                                                                                                         rd
                                                                                                                         rs1
                                                                                                                         rs2
                                                                                                                    else if andb
                                                                                                                            (Z.eqb
                                                                                                                             opcode
                                                                                                                             opcode_OP)
                                                                                                                            (andb
                                                                                                                             (Z.eqb
                                                                                                                              funct3
                                                                                                                              funct3_SLT)
                                                                                                                             (Z.eqb
                                                                                                                              funct7
                                                                                                                              funct7_SLT)) : bool
                                                                                                                         then Slt
                                                                                                                              rd
                                                                                                                              rs1
                                                                                                                              rs2
                                                                                                                         else if andb
                                                                                                                                 (Z.eqb
                                                                                                                                  opcode
                                                                                                                                  opcode_OP)
                                                                                                                                 (andb
                                                                                                                                  (Z.eqb
                                                                                                                                   funct3
                                                                                                                                   funct3_SLTU)
                                                                                                                                  (Z.eqb
                                                                                                                                   funct7
                                                                                                                                   funct7_SLTU)) : bool
                                                                                                                              then Sltu
                                                                                                                                   rd
                                                                                                                                   rs1
                                                                                                                                   rs2
                                                                                                                              else if andb
                                                                                                                                      (Z.eqb
                                                                                                                                       opcode
                                                                                                                                       opcode_OP)
                                                                                                                                      (andb
                                                                                                                                       (Z.eqb
                                                                                                                                        funct3
                                                                                                                                        funct3_XOR)
                                                                                                                                       (Z.eqb
                                                                                                                                        funct7
                                                                                                                                        funct7_XOR)) : bool
                                                                                                                                   then Xor
                                                                                                                                        rd
                                                                                                                                        rs1
                                                                                                                                        rs2
                                                                                                                                   else if andb
                                                                                                                                           (Z.eqb
                                                                                                                                            opcode
                                                                                                                                            opcode_OP)
                                                                                                                                           (andb
                                                                                                                                            (Z.eqb
                                                                                                                                             funct3
                                                                                                                                             funct3_SRL)
                                                                                                                                            (Z.eqb
                                                                                                                                             funct7
                                                                                                                                             funct7_SRL)) : bool
                                                                                                                                        then Srl
                                                                                                                                             rd
                                                                                                                                             rs1
                                                                                                                                             rs2
                                                                                                                                        else if andb
                                                                                                                                                (Z.eqb
                                                                                                                                                 opcode
                                                                                                                                                 opcode_OP)
                                                                                                                                                (andb
                                                                                                                                                 (Z.eqb
                                                                                                                                                  funct3
                                                                                                                                                  funct3_SRA)
                                                                                                                                                 (Z.eqb
                                                                                                                                                  funct7
                                                                                                                                                  funct7_SRA)) : bool
                                                                                                                                             then Sra
                                                                                                                                                  rd
                                                                                                                                                  rs1
                                                                                                                                                  rs2
                                                                                                                                             else if andb
                                                                                                                                                     (Z.eqb
                                                                                                                                                      opcode
                                                                                                                                                      opcode_OP)
                                                                                                                                                     (andb
                                                                                                                                                      (Z.eqb
                                                                                                                                                       funct3
                                                                                                                                                       funct3_OR)
                                                                                                                                                      (Z.eqb
                                                                                                                                                       funct7
                                                                                                                                                       funct7_OR)) : bool
                                                                                                                                                  then Or
                                                                                                                                                       rd
                                                                                                                                                       rs1
                                                                                                                                                       rs2
                                                                                                                                                  else if andb
                                                                                                                                                          (Z.eqb
                                                                                                                                                           opcode
                                                                                                                                                           opcode_OP)
                                                                                                                                                          (andb
                                                                                                                                                           (Z.eqb
                                                                                                                                                            funct3
                                                                                                                                                            funct3_AND)
                                                                                                                                                           (Z.eqb
                                                                                                                                                            funct7
                                                                                                                                                            funct7_AND)) : bool
                                                                                                                                                       then And
                                                                                                                                                            rd
                                                                                                                                                            rs1
                                                                                                                                                            rs2
                                                                                                                                                       else if Z.eqb
                                                                                                                                                               opcode
                                                                                                                                                               opcode_LUI : bool
                                                                                                                                                            then Lui
                                                                                                                                                                 rd
                                                                                                                                                                 imm20
                                                                                                                                                            else if andb
                                                                                                                                                                    (Z.eqb
                                                                                                                                                                     opcode
                                                                                                                                                                     opcode_BRANCH)
                                                                                                                                                                    (Z.eqb
                                                                                                                                                                     funct3
                                                                                                                                                                     funct3_BEQ) : bool
                                                                                                                                                                 then Beq
                                                                                                                                                                      rs1
                                                                                                                                                                      rs2
                                                                                                                                                                      sbimm12
                                                                                                                                                                 else if andb
                                                                                                                                                                         (Z.eqb
                                                                                                                                                                          opcode
                                                                                                                                                                          opcode_BRANCH)
                                                                                                                                                                         (Z.eqb
                                                                                                                                                                          funct3
                                                                                                                                                                          funct3_BNE) : bool
                                                                                                                                                                      then Bne
                                                                                                                                                                           rs1
                                                                                                                                                                           rs2
                                                                                                                                                                           sbimm12
                                                                                                                                                                      else if andb
                                                                                                                                                                              (Z.eqb
                                                                                                                                                                               opcode
                                                                                                                                                                               opcode_BRANCH)
                                                                                                                                                                              (Z.eqb
                                                                                                                                                                               funct3
                                                                                                                                                                               funct3_BLT) : bool
                                                                                                                                                                           then Blt
                                                                                                                                                                                rs1
                                                                                                                                                                                rs2
                                                                                                                                                                                sbimm12
                                                                                                                                                                           else if andb
                                                                                                                                                                                   (Z.eqb
                                                                                                                                                                                    opcode
                                                                                                                                                                                    opcode_BRANCH)
                                                                                                                                                                                   (Z.eqb
                                                                                                                                                                                    funct3
                                                                                                                                                                                    funct3_BGE) : bool
                                                                                                                                                                                then Bge
                                                                                                                                                                                     rs1
                                                                                                                                                                                     rs2
                                                                                                                                                                                     sbimm12
                                                                                                                                                                                else if andb
                                                                                                                                                                                        (Z.eqb
                                                                                                                                                                                         opcode
                                                                                                                                                                                         opcode_BRANCH)
                                                                                                                                                                                        (Z.eqb
                                                                                                                                                                                         funct3
                                                                                                                                                                                         funct3_BLTU) : bool
                                                                                                                                                                                     then Bltu
                                                                                                                                                                                          rs1
                                                                                                                                                                                          rs2
                                                                                                                                                                                          sbimm12
                                                                                                                                                                                     else if andb
                                                                                                                                                                                             (Z.eqb
                                                                                                                                                                                              opcode
                                                                                                                                                                                              opcode_BRANCH)
                                                                                                                                                                                             (Z.eqb
                                                                                                                                                                                              funct3
                                                                                                                                                                                              funct3_BGEU) : bool
                                                                                                                                                                                          then Bgeu
                                                                                                                                                                                               rs1
                                                                                                                                                                                               rs2
                                                                                                                                                                                               sbimm12
                                                                                                                                                                                          else if Z.eqb
                                                                                                                                                                                                  opcode
                                                                                                                                                                                                  opcode_JALR : bool
                                                                                                                                                                                               then Jalr
                                                                                                                                                                                                    rd
                                                                                                                                                                                                    rs1
                                                                                                                                                                                                    oimm12
                                                                                                                                                                                               else if Z.eqb
                                                                                                                                                                                                       opcode
                                                                                                                                                                                                       opcode_JAL : bool
                                                                                                                                                                                                    then Jal
                                                                                                                                                                                                         rd
                                                                                                                                                                                                         jimm20
                                                                                                                                                                                                    else InvalidI in
    let decodeM :=
      if andb (Z.eqb opcode opcode_OP) (andb (Z.eqb funct3 funct3_MUL) (Z.eqb funct7
                                                                              funct7_MUL)) : bool
      then Mul rd rs1 rs2
      else if andb (Z.eqb opcode opcode_OP) (andb (Z.eqb funct3 funct3_MULH) (Z.eqb
                                                   funct7 funct7_MULH)) : bool
           then Mulh rd rs1 rs2
           else if andb (Z.eqb opcode opcode_OP) (andb (Z.eqb funct3 funct3_MULHSU) (Z.eqb
                                                        funct7 funct7_MULHSU)) : bool
                then Mulhsu rd rs1 rs2
                else if andb (Z.eqb opcode opcode_OP) (andb (Z.eqb funct3 funct3_MULHU) (Z.eqb
                                                             funct7 funct7_MULHU)) : bool
                     then Mulhu rd rs1 rs2
                     else if andb (Z.eqb opcode opcode_OP) (andb (Z.eqb funct3 funct3_DIV) (Z.eqb
                                                                  funct7 funct7_DIV)) : bool
                          then Div rd rs1 rs2
                          else if andb (Z.eqb opcode opcode_OP) (andb (Z.eqb funct3 funct3_DIVU) (Z.eqb
                                                                       funct7 funct7_DIVU)) : bool
                               then Divu rd rs1 rs2
                               else if andb (Z.eqb opcode opcode_OP) (andb (Z.eqb funct3 funct3_REM) (Z.eqb
                                                                            funct7 funct7_REM)) : bool
                                    then Rem rd rs1 rs2
                                    else if andb (Z.eqb opcode opcode_OP) (andb (Z.eqb funct3 funct3_REMU) (Z.eqb
                                                                                 funct7 funct7_REMU)) : bool
                                         then Remu rd rs1 rs2
                                         else InvalidM in
    let decodeI64 :=
      if andb (Z.eqb opcode opcode_LOAD) (Z.eqb funct3 funct3_LD) : bool
      then Ld rd rs1 oimm12
      else if andb (Z.eqb opcode opcode_LOAD) (Z.eqb funct3 funct3_LWU) : bool
           then Lwu rd rs1 oimm12
           else if andb (Z.eqb opcode opcode_OP_IMM_32) (Z.eqb funct3 funct3_ADDIW) : bool
                then Addiw rd rs1 imm12
                else if andb (Z.eqb opcode opcode_OP_IMM_32) (andb (Z.eqb funct3 funct3_SLLIW)
                                                                   (Z.eqb funct7 funct7_SLLIW)) : bool
                     then Slliw rd rs1 shamt5
                     else if andb (Z.eqb opcode opcode_OP_IMM_32) (andb (Z.eqb funct3 funct3_SRLIW)
                                                                        (Z.eqb funct7 funct7_SRLIW)) : bool
                          then Srliw rd rs1 shamt5
                          else if andb (Z.eqb opcode opcode_OP_IMM_32) (andb (Z.eqb funct3 funct3_SRAIW)
                                                                             (Z.eqb funct7 funct7_SRAIW)) : bool
                               then Sraiw rd rs1 shamt5
                               else if andb (Z.eqb opcode opcode_STORE) (Z.eqb funct3 funct3_SD) : bool
                                    then Sd rs1 rs2 simm12
                                    else if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3 funct3_ADDW) (Z.eqb
                                                                                    funct7 funct7_ADDW)) : bool
                                         then Addw rd rs1 rs2
                                         else if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3 funct3_SUBW)
                                                                                        (Z.eqb funct7
                                                                                               funct7_SUBW)) : bool
                                              then Subw rd rs1 rs2
                                              else if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3 funct3_SLLW)
                                                                                             (Z.eqb funct7
                                                                                                    funct7_SLLW)) : bool
                                                   then Sllw rd rs1 rs2
                                                   else if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3
                                                                                                         funct3_SRLW)
                                                                                                  (Z.eqb funct7
                                                                                                         funct7_SRLW)) : bool
                                                        then Srlw rd rs1 rs2
                                                        else if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3
                                                                                                              funct3_SRAW)
                                                                                                       (Z.eqb funct7
                                                                                                              funct7_SRAW)) : bool
                                                             then Sraw rd rs1 rs2
                                                             else InvalidI64 in
    let decodeM64 :=
      if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3 funct3_MULW) (Z.eqb
                                                 funct7 funct7_MULW)) : bool
      then Mulw rd rs1 rs2
      else if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3 funct3_DIVW) (Z.eqb
                                                      funct7 funct7_DIVW)) : bool
           then Divw rd rs1 rs2
           else if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3 funct3_DIVUW)
                                                          (Z.eqb funct7 funct7_DIVUW)) : bool
                then Divuw rd rs1 rs2
                else if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3 funct3_REMW) (Z.eqb
                                                                funct7 funct7_REMW)) : bool
                     then Remw rd rs1 rs2
                     else if andb (Z.eqb opcode opcode_OP_32) (andb (Z.eqb funct3 funct3_REMUW)
                                                                    (Z.eqb funct7 funct7_REMUW)) : bool
                          then Remuw rd rs1 rs2
                          else InvalidM64 in
    let decodeCSR :=
      if andb (Z.eqb opcode opcode_SYSTEM) (andb (Z.eqb rd 0) (andb (Z.eqb funct3
                                                                           funct3_PRIV) (andb (Z.eqb rs1 0) (Z.eqb
                                                                                               funct12
                                                                                               funct12_ECALL)))) : bool
      then Ecall
      else if andb (Z.eqb opcode opcode_SYSTEM) (andb (Z.eqb rd 0) (andb (Z.eqb funct3
                                                                                funct3_PRIV) (andb (Z.eqb rs1 0) (Z.eqb
                                                                                                    funct12
                                                                                                    funct12_EBREAK)))) : bool
           then Ebreak
           else if andb (Z.eqb opcode opcode_SYSTEM) (andb (Z.eqb rd 0) (andb (Z.eqb funct3
                                                                                     funct3_PRIV) (andb (Z.eqb rs1 0)
                                                                                                        (Z.eqb funct12
                                                                                                               funct12_URET)))) : bool
                then Uret
                else if andb (Z.eqb opcode opcode_SYSTEM) (andb (Z.eqb rd 0) (andb (Z.eqb funct3
                                                                                          funct3_PRIV) (andb (Z.eqb rs1
                                                                                                                    0)
                                                                                                             (Z.eqb
                                                                                                              funct12
                                                                                                              funct12_SRET)))) : bool
                     then Sret
                     else if andb (Z.eqb opcode opcode_SYSTEM) (andb (Z.eqb rd 0) (andb (Z.eqb funct3
                                                                                               funct3_PRIV) (andb (Z.eqb
                                                                                                                   rs1
                                                                                                                   0)
                                                                                                                  (Z.eqb
                                                                                                                   funct12
                                                                                                                   funct12_MRET)))) : bool
                          then Mret
                          else if andb (Z.eqb opcode opcode_SYSTEM) (andb (Z.eqb rd 0) (andb (Z.eqb funct3
                                                                                                    funct3_PRIV) (andb
                                                                                              (Z.eqb rs1 0) (Z.eqb
                                                                                               funct12
                                                                                               funct12_WFI)))) : bool
                               then Wfi
                               else if andb (Z.eqb opcode opcode_SYSTEM) (Z.eqb funct3 funct3_CSRRW) : bool
                                    then Csrrw rd rs1 csr12
                                    else if andb (Z.eqb opcode opcode_SYSTEM) (Z.eqb funct3 funct3_CSRRS) : bool
                                         then Csrrs rd rs1 csr12
                                         else if andb (Z.eqb opcode opcode_SYSTEM) (Z.eqb funct3 funct3_CSRRC) : bool
                                              then Csrrc rd rs1 csr12
                                              else if andb (Z.eqb opcode opcode_SYSTEM) (Z.eqb funct3
                                                                                               funct3_CSRRWI) : bool
                                                   then Csrrwi rd zimm csr12
                                                   else if andb (Z.eqb opcode opcode_SYSTEM) (Z.eqb funct3
                                                                                                    funct3_CSRRSI) : bool
                                                        then Csrrsi rd zimm csr12
                                                        else if andb (Z.eqb opcode opcode_SYSTEM) (Z.eqb funct3
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
                                                              else nil) (Coq.Init.Datatypes.app (if Z.eqb (bitwidth
                                                                                                           iset)
                                                                                                          64 : bool
                                                                                                 then resultI64
                                                                                                 else nil)
                                                                                                (Coq.Init.Datatypes.app
                                                                                                 (if andb (Z.eqb
                                                                                                           (bitwidth
                                                                                                            iset) 64)
                                                                                                          (supportsM
                                                                                                           iset) : bool
                                                                                                  then resultM64
                                                                                                  else nil)
                                                                                                 resultCSR))) in
    match results with
    | cons singleResult nil => singleResult
    | nil => InvalidInstruction
    | _ => InvalidInstruction
    end.

(* Unbound variables:
     Z Z.eqb Z.lor Z.pow Z.shiftl Z.sub Z.testbit andb bitSlice bool cons false id
     list nil orb true Coq.Init.Datatypes.app
*)
