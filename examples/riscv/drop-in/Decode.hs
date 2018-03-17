{-# LANGUAGE DuplicateRecordFields #-}

module Decode where

-- Haskell lib imports

import Data.Bits    -- For bit-wise 'and' (.&.) etc.
import Data.Word    -- For Word32 type (unsigned 32-bit ints)
import Prelude
-- Local imports

--import Utility
type MachineInt = Int

bitSlice :: (Bits a, Num a) => a -> Int -> Int -> a
bitSlice = undefined

-- ================================================================
-- Decoded instructions

data InstructionI =
  Lb { rd :: Register, rs1 :: Register, oimm12 :: MachineInt } |
  Lh { rd :: Register, rs1 :: Register, oimm12 :: MachineInt } |
  Lw { rd :: Register, rs1 :: Register, oimm12 :: MachineInt } |
  Lbu { rd :: Register, rs1 :: Register, oimm12 :: MachineInt } |
  Lhu { rd :: Register, rs1 :: Register, oimm12 :: MachineInt } |

  Fence { pred :: MachineInt, succ :: MachineInt } |
  Fence_i |

{-
  Addi { rd :: Register, rs1 :: Register, imm12 :: MachineInt } |
  Slli { rd :: Register, rs1 :: Register, shamt6 :: Int } |
  Slti { rd :: Register, rs1 :: Register, imm12 :: MachineInt } |
  Sltiu { rd :: Register, rs1 :: Register, imm12 :: MachineInt } |
  Xori { rd :: Register, rs1 :: Register, imm12 :: MachineInt } |
  Ori { rd :: Register, rs1 :: Register, imm12 :: MachineInt } |
  Andi { rd :: Register, rs1 :: Register, imm12 :: MachineInt } |
  Srli { rd :: Register, rs1 :: Register, shamt6 :: Int } |
  Srai { rd :: Register, rs1 :: Register, shamt6 :: Int } |

  Auipc { rd :: Register, oimm20 :: MachineInt } |

  Sb { rs1 :: Register, rs2 :: Register, simm12 :: MachineInt } |
  Sh { rs1 :: Register, rs2 :: Register, simm12 :: MachineInt } |
  Sw { rs1 :: Register, rs2 :: Register, simm12 :: MachineInt } |

  Add { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sub { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sll { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Slt { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sltu { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Xor { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Srl { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sra { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Or { rd :: Register, rs1 :: Register, rs2 :: Register } |
  And { rd :: Register, rs1 :: Register, rs2 :: Register } |

  Lui { rd :: Register, imm20 :: MachineInt } |

  Beq { rs1 :: Register, rs2 :: Register, sbimm12 :: MachineInt } |
  Bne { rs1 :: Register, rs2 :: Register, sbimm12 :: MachineInt } |
  Blt { rs1 :: Register, rs2 :: Register, sbimm12 :: MachineInt } |
  Bge { rs1 :: Register, rs2 :: Register, sbimm12 :: MachineInt } |
  Bltu { rs1 :: Register, rs2 :: Register, sbimm12 :: MachineInt } |
  Bgeu { rs1 :: Register, rs2 :: Register, sbimm12 :: MachineInt } |

  Jalr { rd :: Register, rs1 :: Register, oimm12 :: MachineInt } |
  Jal { rd :: Register, jimm20 :: MachineInt } |
-}
  InvalidI 
  deriving (Eq, Read, Show)


data InstructionM =
  Mul { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Mulh { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Mulhsu { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Mulhu { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Div { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Divu { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Rem { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Remu { rd :: Register, rs1 :: Register, rs2 :: Register } |
  InvalidM
  deriving (Eq, Read, Show)


data InstructionI64 =
  Ld { rd :: Register, rs1 :: Register, oimm12 :: MachineInt } |
  Lwu { rd :: Register, rs1 :: Register, oimm12 :: MachineInt } |

  Addiw { rd :: Register, rs1 :: Register, imm12 :: MachineInt } |
  Slliw { rd :: Register, rs1 :: Register, shamt5 :: Int } |
  Srliw { rd :: Register, rs1 :: Register, shamt5 :: Int } |
  Sraiw { rd :: Register, rs1 :: Register, shamt5 :: Int } |

  Sd { rs1 :: Register, rs2 :: Register, simm12 :: MachineInt } |

  Addw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Subw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sllw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Srlw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Sraw { rd :: Register, rs1 :: Register, rs2 :: Register } |

  InvalidI64
  deriving (Eq, Read, Show)


data InstructionM64 =
  Mulw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Divw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Divuw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Remw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  Remuw { rd :: Register, rs1 :: Register, rs2 :: Register } |
  InvalidM64
  deriving (Eq, Read, Show)


data InstructionCSR =
  Ecall |
  Ebreak |
  Uret |
  Sret |
  Mret |
  Wfi |
  Sfence_vm { rs1 :: Register, rs2 :: Register } |
  Csrrw { rd :: Register, rs1 :: Register, csr12 :: MachineInt } |
  Csrrs { rd :: Register, rs1 :: Register, csr12 :: MachineInt } |
  Csrrc { rd :: Register, rs1 :: Register, csr12 :: MachineInt } |
  Csrrwi { rd :: Register, zimm :: MachineInt, csr12 :: MachineInt } |
  Csrrsi { rd :: Register, zimm :: MachineInt, csr12 :: MachineInt } |
  Csrrci { rd :: Register, zimm :: MachineInt, csr12 :: MachineInt } |
  InvalidCSR
  deriving (Eq, Read, Show)


data Instruction =
  IInstruction   { iInstruction   :: InstructionI   } |
  MInstruction   { mInstruction   :: InstructionM   } |
  I64Instruction { i64Instruction :: InstructionI64 } |
  M64Instruction { m64Instruction :: InstructionM64 } |
  CSRInstruction { csrInstruction :: InstructionCSR } |
  InvalidInstruction
  deriving (Eq, Read, Show)

-- ================================================================

data InstructionSet = RV32I | RV32IM | RV64I | RV64IM deriving (Eq, Show)

bitwidth :: InstructionSet -> Int
bitwidth RV32I = 32
bitwidth RV32IM = 32
bitwidth RV64I = 64
bitwidth RV64IM = 64

supportsM :: InstructionSet -> Bool
supportsM RV32I = False
supportsM RV32IM = True
supportsM RV64I = False
supportsM RV64IM = True

-- ================================================================

type Register = MachineInt

-- ================================================================
-- Instruction bit fields

-- Major opcode (instr [6:0]), see Table 19.1 in spec
type Opcode = MachineInt


opcode_LOAD      :: Opcode;    opcode_LOAD      = 0x03    -- 7'b_00_000_11
opcode_LOAD_FP   :: Opcode;    opcode_LOAD_FP   = 0x07    -- 7'b_00_001_11
opcode_MISC_MEM  :: Opcode;    opcode_MISC_MEM  = 0x0F    -- 7'b_00_011_11
opcode_OP_IMM    :: Opcode;    opcode_OP_IMM    = 0x13    -- 7'b_00_100_11
opcode_AUIPC     :: Opcode;    opcode_AUIPC     = 0x17    -- 7'b_00_101_11
opcode_OP_IMM_32 :: Opcode;    opcode_OP_IMM_32 = 0x1B    -- 7'b_00_110_11

opcode_STORE     :: Opcode;    opcode_STORE     = 0x23    -- 7'b_01_000_11
opcode_STORE_FP  :: Opcode;    opcode_STORE_FP  = 0x27    -- 7'b_01_001_11
opcode_AMO       :: Opcode;    opcode_AMO       = 0x2F    -- 7'b_01_011_11
opcode_OP        :: Opcode;    opcode_OP        = 0x33    -- 7'b_01_100_11
opcode_LUI       :: Opcode;    opcode_LUI       = 0x37    -- 7'b_01_101_11
opcode_OP_32     :: Opcode;    opcode_OP_32     = 0x3B    -- 7'b_01_110_11

opcode_MADD      :: Opcode;    opcode_MADD      = 0x43    -- 7'b_10_000_11
opcode_MSUB      :: Opcode;    opcode_MSUB      = 0x47    -- 7'b_10_001_11
opcode_NMSUB     :: Opcode;    opcode_NMSUB     = 0x4B    -- 7'b_10_010_11
opcode_NMADD     :: Opcode;    opcode_NMADD     = 0x4F    -- 7'b_10_011_11
opcode_OP_FP     :: Opcode;    opcode_OP_FP     = 0x53    -- 7'b_10_100_11

opcode_BRANCH    :: Opcode;    opcode_BRANCH    = 0x63    -- 7'b_11_000_11
opcode_JALR      :: Opcode;    opcode_JALR      = 0x67    -- 7'b_11_001_11
opcode_JAL       :: Opcode;    opcode_JAL       = 0x6F    -- 7'b_11_011_11
opcode_SYSTEM    :: Opcode;    opcode_SYSTEM    = 0x73    -- 7'b_11_100_11

-- LOAD sub-opcodes
funct3_LB  :: MachineInt;    funct3_LB  = 0x0     -- 3'b_000
funct3_LH  :: MachineInt;    funct3_LH  = 0x1     -- 3'b_001
funct3_LW  :: MachineInt;    funct3_LW  = 0x2     -- 3'b_010
funct3_LD  :: MachineInt;    funct3_LD  = 0x3     -- 3'b_011
funct3_LBU :: MachineInt;    funct3_LBU = 0x4     -- 3'b_100
funct3_LHU :: MachineInt;    funct3_LHU = 0x5     -- 3'b_101
funct3_LWU :: MachineInt;    funct3_LWU = 0x6     -- 3'b_110

-- MISC_MEM sub-opcodes
funct3_FENCE   :: MachineInt;    funct3_FENCE   = 0x0      -- 3'b_000
funct3_FENCE_I :: MachineInt;    funct3_FENCE_I = 0x1      -- 3'b_001

-- OP_IMM sub-opcodes
funct3_ADDI  :: MachineInt;    funct3_ADDI  = 0x0      -- 3'b_000
funct3_SLLI  :: MachineInt;    funct3_SLLI  = 0x1      -- 3'b_001
funct3_SLTI  :: MachineInt;    funct3_SLTI  = 0x2      -- 3'b_010
funct3_SLTIU :: MachineInt;    funct3_SLTIU = 0x3      -- 3'b_011
funct3_XORI  :: MachineInt;    funct3_XORI  = 0x4      -- 3'b_100
funct3_SRLI  :: MachineInt;    funct3_SRLI  = 0x5      -- 3'b_101
funct3_SRAI  :: MachineInt;    funct3_SRAI  = 0x5      -- 3'b_101
funct3_ORI   :: MachineInt;    funct3_ORI   = 0x6      -- 3'b_110
funct3_ANDI  :: MachineInt;    funct3_ANDI  = 0x7      -- 3'b_111

-- OP_IMM.SLLI/SRLI/SRAI
funct6_SLLI  :: MachineInt;    funct6_SLLI  = 0x00     -- 6'b_000000
funct6_SRLI  :: MachineInt;    funct6_SRLI  = 0x00     -- 6'b_000000
funct6_SRAI  :: MachineInt;    funct6_SRAI  = 0x10     -- 6'b_010000

-- OP_IMM_32 sub-opcodes (RV64 only)
funct3_ADDIW :: MachineInt;    funct3_ADDIW = 0x0     -- 3'b_000

funct3_SLLIW :: MachineInt;    funct3_SLLIW = 0x1     -- 3'b_001
funct7_SLLIW :: MachineInt;    funct7_SLLIW = 0x00    -- 7'b_0000000

funct3_SRLIW :: MachineInt;    funct3_SRLIW = 0x5     -- 3'b_101
funct7_SRLIW :: MachineInt;    funct7_SRLIW = 0x00    -- 7'b_0000000

funct3_SRAIW :: MachineInt;    funct3_SRAIW = 0x5     -- 3'b_101
funct7_SRAIW :: MachineInt;    funct7_SRAIW = 0x20    -- 7'b_0100000

-- STORE sub-opcodes
funct3_SB :: MachineInt;    funct3_SB = 0x0     -- 3'b_000
funct3_SH :: MachineInt;    funct3_SH = 0x1     -- 3'b_001
funct3_SW :: MachineInt;    funct3_SW = 0x2     -- 3'b_010
funct3_SD :: MachineInt;    funct3_SD = 0x3     -- 3'b_011

-- OP sub-opcodes
funct3_ADD  :: MachineInt;    funct3_ADD  = 0x0     -- 3'b_000
funct7_ADD  :: MachineInt;    funct7_ADD  = 0x00    -- 7'b_000_0000

funct3_SUB  :: MachineInt;    funct3_SUB  = 0x0     -- 3'b_000
funct7_SUB  :: MachineInt;    funct7_SUB  = 0x20    -- 7'b_010_0000

funct3_SLL  :: MachineInt;    funct3_SLL  = 0x1     -- 3'b_001
funct7_SLL  :: MachineInt;    funct7_SLL  = 0x00    -- 7'b_000_0000

funct3_SLT  :: MachineInt;    funct3_SLT  = 0x2     -- 3'b_010
funct7_SLT  :: MachineInt;    funct7_SLT  = 0x00    -- 7'b_000_0000

funct3_SLTU :: MachineInt;    funct3_SLTU = 0x3     -- 3'b_011
funct7_SLTU :: MachineInt;    funct7_SLTU = 0x00    -- 7'b_000_0000

funct3_XOR  :: MachineInt;    funct3_XOR  = 0x4     -- 3'b_100
funct7_XOR  :: MachineInt;    funct7_XOR  = 0x00    -- 7'b_000_0000

funct3_SRL  :: MachineInt;    funct3_SRL  = 0x5     -- 3'b_101
funct7_SRL  :: MachineInt;    funct7_SRL  = 0x00    -- 7'b_000_0000

funct3_SRA  :: MachineInt;    funct3_SRA  = 0x5     -- 3'b_101
funct7_SRA  :: MachineInt;    funct7_SRA  = 0x20    -- 7'b_010_0000

funct3_OR   :: MachineInt;    funct3_OR   = 0x6     -- 3'b_110
funct7_OR   :: MachineInt;    funct7_OR   = 0x00    -- 7'b_000_0000

funct3_AND  :: MachineInt;    funct3_AND  = 0x7     -- 3'b_111
funct7_AND  :: MachineInt;    funct7_AND  = 0x00    -- 7'b_000_0000

-- OP sub-opcodes, M standard extension

funct3_MUL    :: MachineInt;    funct3_MUL    = 0x0     -- 3'b_000
funct7_MUL    :: MachineInt;    funct7_MUL    = 0x01    -- 7'b_000_0001

funct3_MULH   :: MachineInt;    funct3_MULH   = 0x1     -- 3'b_001
funct7_MULH   :: MachineInt;    funct7_MULH   = 0x01    -- 7'b_000_0001

funct3_MULHSU :: MachineInt;    funct3_MULHSU = 0x2     -- 3'b_010
funct7_MULHSU :: MachineInt;    funct7_MULHSU = 0x01    -- 7'b_000_0001

funct3_MULHU  :: MachineInt;    funct3_MULHU  = 0x3     -- 3'b_011
funct7_MULHU  :: MachineInt;    funct7_MULHU  = 0x01    -- 7'b_000_0001

funct3_DIV    :: MachineInt;    funct3_DIV    = 0x4     -- 3'b_100
funct7_DIV    :: MachineInt;    funct7_DIV    = 0x01    -- 7'b_000_0001

funct3_DIVU   :: MachineInt;    funct3_DIVU   = 0x5     -- 3'b_101
funct7_DIVU   :: MachineInt;    funct7_DIVU   = 0x01    -- 7'b_000_0001

funct3_REM    :: MachineInt;    funct3_REM    = 0x6     -- 3'b_110
funct7_REM    :: MachineInt;    funct7_REM    = 0x01    -- 7'b_000_0001

funct3_REMU   :: MachineInt;    funct3_REMU   = 0x7     -- 3'b_111
funct7_REMU   :: MachineInt;    funct7_REMU   = 0x01    -- 7'b_000_0001

-- OP_32 sub-opcodes (RV64 only)
funct3_ADDW  :: MachineInt;    funct3_ADDW  = 0x0     --- 3'b_000
funct7_ADDW  :: MachineInt;    funct7_ADDW  = 0x00    --- 7'b_000_0000

funct3_SUBW  :: MachineInt;    funct3_SUBW  = 0x0     --- 3'b_000
funct7_SUBW  :: MachineInt;    funct7_SUBW  = 0x20    --- 7'b_010_0000

funct3_SLLW  :: MachineInt;    funct3_SLLW  = 0x1     --- 3'b_001
funct7_SLLW  :: MachineInt;    funct7_SLLW  = 0x00    --- 7'b_000_0000

funct3_SRLW  :: MachineInt;    funct3_SRLW  = 0x5     --- 3'b_101
funct7_SRLW  :: MachineInt;    funct7_SRLW  = 0x00    --- 7'b_000_0000

funct3_SRAW  :: MachineInt;    funct3_SRAW  = 0x5     --- 3'b_101
funct7_SRAW  :: MachineInt;    funct7_SRAW  = 0x20    --- 7'b_010_0000

-- OP_32 sub-opcodes, M standard extension (RV64 only)
funct3_MULW  :: MachineInt;    funct3_MULW  = 0x0     --- 3'b_000
funct7_MULW  :: MachineInt;    funct7_MULW  = 0x01    --- 7'b_000_0001

funct3_DIVW  :: MachineInt;    funct3_DIVW  = 0x4     --- 3'b_100
funct7_DIVW  :: MachineInt;    funct7_DIVW  = 0x01    --- 7'b_000_0001

funct3_DIVUW :: MachineInt;    funct3_DIVUW = 0x5     --- 3'b_101
funct7_DIVUW :: MachineInt;    funct7_DIVUW = 0x01    --- 7'b_000_0001

funct3_REMW  :: MachineInt;    funct3_REMW  = 0x6     --- 3'b_110
funct7_REMW  :: MachineInt;    funct7_REMW  = 0x01    --- 7'b_000_0001

funct3_REMUW :: MachineInt;    funct3_REMUW = 0x7     --- 3'b_111
funct7_REMUW :: MachineInt;    funct7_REMUW = 0x01    --- 7'b_000_0001

-- BRANCH sub-opcodes
funct3_BEQ  :: MachineInt;    funct3_BEQ  = 0x0     -- 3'b_000
funct3_BNE  :: MachineInt;    funct3_BNE  = 0x1     -- 3'b_001
funct3_BLT  :: MachineInt;    funct3_BLT  = 0x4     -- 3'b_100
funct3_BGE  :: MachineInt;    funct3_BGE  = 0x5     -- 3'b_101
funct3_BLTU :: MachineInt;    funct3_BLTU = 0x6     -- 3'b_110
funct3_BGEU :: MachineInt;    funct3_BGEU = 0x7     -- 3'b_111

-- SYSTEM sub-opcodes
funct3_PRIV   :: MachineInt;    funct3_PRIV   = 0x0     -- 3'b_000
--- SYSTEM.PRIV sub-sub-opcodes
funct12_ECALL    :: MachineInt;    funct12_ECALL  = 0x000    -- 12'b_0000_0000_0000
funct12_EBREAK   :: MachineInt;    funct12_EBREAK = 0x001    -- 12'b_0000_0000_0001
funct12_URET     :: MachineInt;    funct12_URET   = 0x002    -- 12'b_0000_0000_0010
funct12_SRET     :: MachineInt;    funct12_SRET   = 0x102    -- 12'b_0001_0000_0010
funct12_MRET     :: MachineInt;    funct12_MRET   = 0x302    -- 12'b_0011_0000_0010
funct12_WFI      :: MachineInt;    funct12_WFI    = 0x105    -- 12'b_0001_0000_0101

funct7_SFENCE_VM :: MachineInt;    funct7_SFENCE_VM = 0x09     -- 7'b_000_1001

funct3_CSRRW  :: MachineInt;    funct3_CSRRW  = 0x1     -- 3'b_001
funct3_CSRRS  :: MachineInt;    funct3_CSRRS  = 0x2     -- 3'b_010
funct3_CSRRC  :: MachineInt;    funct3_CSRRC  = 0x3     -- 3'b_011
funct3_CSRRWI :: MachineInt;    funct3_CSRRWI = 0x5     -- 3'b_101
funct3_CSRRSI :: MachineInt;    funct3_CSRRSI = 0x6     -- 3'b_110
funct3_CSRRCI :: MachineInt;    funct3_CSRRCI = 0x7     -- 3'b_111

-- TODO: sub-opcodes for LOAD_FP, STORE_FP, OP_FP
-- TODO: sub-opcodes for AMO
-- TODO: sub-opcodes for MADD, MSUB, NMSUB, NMADD

-- ================================================================

signExtend :: Int -> MachineInt -> MachineInt
signExtend l n = if testBit n (l-1)
                 then n-2^l
                 else n

machineIntToShamt :: MachineInt -> Int
machineIntToShamt = fromIntegral

-- ================================================================
-- The main decoder function


decode :: InstructionSet -> MachineInt -> Instruction
decode iset inst = case results of
    [singleResult] -> singleResult         -- this case is the "normal" case
    [] -> InvalidInstruction               -- this case is also part of the spec
    _ -> error "ambiguous decoding result" -- this case means there's a bug in the spec

  where
    results :: [Instruction]
    results =
      resultI ++
      (if supportsM iset then resultM else []) ++
      (if bitwidth iset == 64 then resultI64 else []) ++
      (if bitwidth iset == 64 && supportsM iset then resultM64 else []) ++
      resultCSR

    resultI   = if decodeI   == InvalidI   then [] else [IInstruction   decodeI  ]
    resultM   = if decodeM   == InvalidM   then [] else [MInstruction   decodeM  ]
    resultI64 = if decodeI64 == InvalidI64 then [] else [I64Instruction decodeI64]
    resultM64 = if decodeM64 == InvalidM64 then [] else [M64Instruction decodeM64]
    resultCSR = if decodeCSR == InvalidCSR then [] else [CSRInstruction decodeCSR]

    -- Symbolic names for notable bitfields in the 32b instruction 'inst'
    -- Note: 'bitSlice x i j' is, roughly, Verilog's 'x [j-1, i]'
    opcode  = bitSlice inst 0 7        -- = Verilog's: inst [6:0]
    funct3  = bitSlice inst 12 15
    funct7  = bitSlice inst 25 32
    funct10 = (shift (bitSlice inst 25 32) 3) .|. (bitSlice inst 12 15)
    funct12 = bitSlice inst 20 32

    rd      = bitSlice inst 7 12
    rs1     = bitSlice inst 15 20
    rs2     = bitSlice inst 20 25
    rs3     = bitSlice inst 27 32    -- for FMADD, FMSUB, FNMSUB

    succ    = bitSlice inst 20 24    -- for FENCE
    pred    = bitSlice inst 24 28    -- for FENCE
    msb4    = bitSlice inst 28 32    -- for FENCE

    imm20   = signExtend 32 $ shift (bitSlice inst 12 32) 12    -- for LUI
    oimm20  = signExtend 32 $ shift (bitSlice inst 12 32) 12    -- for AUIPC

    jimm20  = signExtend 21 $ (shift (bitSlice inst 31 32) 20  .|.        -- for JAL
                                shift (bitSlice inst 21 31) 1  .|.
                                shift (bitSlice inst 20 21) 11 .|.
                                shift (bitSlice inst 12 20) 12)

    imm12   = signExtend 12 $ bitSlice inst 20 32
    oimm12  = signExtend 12 $ bitSlice inst 20 32

    csr12   = bitSlice inst 20 32

    simm12  = signExtend 12 $ shift (bitSlice inst 25 32) 5 .|. bitSlice inst 7 12    -- for STORE

    sbimm12 = signExtend 13 $ (shift (bitSlice inst 31 32) 12 .|.    -- for BRANCH
                                shift (bitSlice inst 25 31) 5 .|.
                                shift (bitSlice inst 8 12) 1  .|.
                                shift (bitSlice inst 7 8) 11)

    shamt5  = machineIntToShamt (bitSlice inst 20 25)
    shamt6  = machineIntToShamt (bitSlice inst 20 26)
    shamtHi = bitSlice inst 25 26
    funct6  = bitSlice inst 26 32
    shamtHiTest = shamtHi == 0 || bitwidth iset == 64

    zimm    = bitSlice inst 15 20    -- for CSRRxI

    decodeI
      | opcode==opcode_LOAD, funct3==funct3_LB  = Lb  {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LH  = Lh  {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LW  = Lw  {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LBU = Lbu {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LHU = Lhu {rd=rd, rs1=rs1, oimm12=oimm12}

      | opcode==opcode_MISC_MEM, rd==0, funct3==funct3_FENCE,   rs1==0, msb4==0  = Fence {Decode.pred=pred, Decode.succ=succ}
      | opcode==opcode_MISC_MEM, rd==0, funct3==funct3_FENCE_I, rs1==0, imm12==0 = Fence_i
{-
      | opcode==opcode_OP_IMM, funct3==funct3_ADDI  = Addi  {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_SLTI  = Slti  {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_SLTIU = Sltiu {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_XORI  = Xori  {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_ORI   = Ori   {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM, funct3==funct3_ANDI  = Andi  {rd=rd, rs1=rs1, imm12=imm12}

      | opcode==opcode_OP_IMM, funct3==funct3_SLLI, funct6==funct6_SLLI, shamtHiTest = Slli {rd=rd, rs1=rs1, shamt6=shamt6}
      | opcode==opcode_OP_IMM, funct3==funct3_SRLI, funct6==funct6_SRLI, shamtHiTest = Srli {rd=rd, rs1=rs1, shamt6=shamt6}
      | opcode==opcode_OP_IMM, funct3==funct3_SRAI, funct6==funct6_SRAI, shamtHiTest = Srai {rd=rd, rs1=rs1, shamt6=shamt6}

      | opcode==opcode_AUIPC = Auipc {rd=rd, oimm20=oimm20}

      | opcode==opcode_STORE, funct3==funct3_SB = Sb {rs1=rs1, rs2=rs2, simm12=simm12}
      | opcode==opcode_STORE, funct3==funct3_SH = Sh {rs1=rs1, rs2=rs2, simm12=simm12}
      | opcode==opcode_STORE, funct3==funct3_SW = Sw {rs1=rs1, rs2=rs2, simm12=simm12}

      | opcode==opcode_OP, funct3==funct3_ADD,  funct7==funct7_ADD  = Add  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SUB,  funct7==funct7_SUB  = Sub  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SLL,  funct7==funct7_SLL  = Sll  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SLT,  funct7==funct7_SLT  = Slt  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SLTU, funct7==funct7_SLTU = Sltu {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_XOR,  funct7==funct7_XOR  = Xor  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SRL,  funct7==funct7_SRL  = Srl  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_SRA,  funct7==funct7_SRA  = Sra  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_OR,   funct7==funct7_OR   = Or   {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_AND,  funct7==funct7_AND  = And  {rd=rd, rs1=rs1, rs2=rs2}

      | opcode==opcode_LUI = Lui {rd=rd, imm20=imm20}

      | opcode==opcode_BRANCH, funct3==funct3_BEQ  = Beq  {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BNE  = Bne  {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BLT  = Blt  {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BGE  = Bge  {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BLTU = Bltu {rs1=rs1, rs2=rs2, sbimm12=sbimm12}
      | opcode==opcode_BRANCH, funct3==funct3_BGEU = Bgeu {rs1=rs1, rs2=rs2, sbimm12=sbimm12}

      | opcode==opcode_JALR = Jalr {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_JAL  = Jal {rd=rd, jimm20=jimm20}
-}
      | True = InvalidI

    decodeM
      | opcode==opcode_OP, funct3==funct3_MUL,    funct7==funct7_MUL    = Mul    {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_MULH,   funct7==funct7_MULH   = Mulh   {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_MULHSU, funct7==funct7_MULHSU = Mulhsu {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_MULHU,  funct7==funct7_MULHU  = Mulhu  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_DIV,    funct7==funct7_DIV    = Div    {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_DIVU,   funct7==funct7_DIVU   = Divu   {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_REM,    funct7==funct7_REM    = Rem    {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP, funct3==funct3_REMU,   funct7==funct7_REMU   = Remu   {rd=rd, rs1=rs1, rs2=rs2}
      | True = InvalidM

    decodeI64
      | opcode==opcode_LOAD, funct3==funct3_LD  = Ld  {rd=rd, rs1=rs1, oimm12=oimm12}
      | opcode==opcode_LOAD, funct3==funct3_LWU = Lwu {rd=rd, rs1=rs1, oimm12=oimm12}

      | opcode==opcode_OP_IMM_32, funct3==funct3_ADDIW                       = Addiw  {rd=rd, rs1=rs1, imm12=imm12}
      | opcode==opcode_OP_IMM_32, funct3==funct3_SLLIW, funct7==funct7_SLLIW = Slliw  {rd=rd, rs1=rs1, shamt5=shamt5}
      | opcode==opcode_OP_IMM_32, funct3==funct3_SRLIW, funct7==funct7_SRLIW = Srliw  {rd=rd, rs1=rs1, shamt5=shamt5}
      | opcode==opcode_OP_IMM_32, funct3==funct3_SRAIW, funct7==funct7_SRAIW = Sraiw  {rd=rd, rs1=rs1, shamt5=shamt5}

      | opcode==opcode_STORE, funct3==funct3_SD = Sd {rs1=rs1, rs2=rs2, simm12=simm12}

      | opcode==opcode_OP_32, funct3==funct3_ADDW, funct7==funct7_ADDW = Addw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_SUBW, funct7==funct7_SUBW = Subw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_SLLW, funct7==funct7_SLLW = Sllw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_SRLW, funct7==funct7_SRLW = Srlw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_SRAW, funct7==funct7_SRAW = Sraw  {rd=rd, rs1=rs1, rs2=rs2}

      | True = InvalidI64

    decodeM64
      | opcode==opcode_OP_32, funct3==funct3_MULW,  funct7==funct7_MULW  = Mulw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_DIVW,  funct7==funct7_DIVW  = Divw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_DIVUW, funct7==funct7_DIVUW = Divuw {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_REMW,  funct7==funct7_REMW  = Remw  {rd=rd, rs1=rs1, rs2=rs2}
      | opcode==opcode_OP_32, funct3==funct3_REMUW, funct7==funct7_REMUW = Remuw {rd=rd, rs1=rs1, rs2=rs2}
      | True = InvalidM64

    decodeCSR
      | opcode==opcode_SYSTEM, rd==0, funct3==funct3_PRIV, rs1==0, funct12==funct12_ECALL  = Ecall
      | opcode==opcode_SYSTEM, rd==0, funct3==funct3_PRIV, rs1==0, funct12==funct12_EBREAK = Ebreak
      | opcode==opcode_SYSTEM, rd==0, funct3==funct3_PRIV, rs1==0, funct12==funct12_URET   = Uret
      | opcode==opcode_SYSTEM, rd==0, funct3==funct3_PRIV, rs1==0, funct12==funct12_SRET   = Sret
      | opcode==opcode_SYSTEM, rd==0, funct3==funct3_PRIV, rs1==0, funct12==funct12_MRET   = Mret
      | opcode==opcode_SYSTEM, rd==0, funct3==funct3_PRIV, rs1==0, funct12==funct12_WFI    = Wfi
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRW  = Csrrw   {rd=rd, rs1=rs1,   csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRS  = Csrrs   {rd=rd, rs1=rs1,   csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRC  = Csrrc   {rd=rd, rs1=rs1,   csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRWI = Csrrwi  {rd=rd, zimm=zimm, csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRSI = Csrrsi  {rd=rd, zimm=zimm, csr12=csr12}
      | opcode==opcode_SYSTEM, funct3==funct3_CSRRCI = Csrrci  {rd=rd, zimm=zimm, csr12=csr12}
      | True = InvalidCSR


-- ================================================================
