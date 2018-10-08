{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module ExtractedNumbers where

import qualified Base
import qualified Datatypes
import qualified BinNums
import qualified BinInt
import qualified BinNat
import qualified Num
import qualified Real
import qualified Bits
import qualified BitUtil

import qualified Data.Bits
import Test.QuickCheck(NonNegative(..))
import System.Random

deriving instance Num a => Num (NonNegative a)
deriving instance Data.Bits.Bits a => Data.Bits.Bits (NonNegative a)
deriving instance Integral a => Integral (NonNegative a)
deriving instance Real a => Real (NonNegative a)
deriving instance System.Random.Random a => System.Random.Random (NonNegative a)
----------------------------------------------------

-- instance Show BinNums.Coq_positive where
--   show bn = reverse (go bn) where
--     go BinNums.Coq_xH = "1"
--     go (BinNums.Coq_xI bn) = '1' : go bn
--     go (BinNums.Coq_xO bn) = 'O' : go bn
  

-- toPositive :: Integer -> BinNums.Coq_positive
-- toPositive x | x <= 0 = error "must call with positive int"
-- toPositive 1 = BinNums.Coq_xH
-- toPositive x = let b1 = x `mod` 2
--                    b2 = x `div` 2 in
--                if b1 == 1 then BinNums.Coq_xI (toPositive b2) else
--                                BinNums.Coq_xO (toPositive b2)

-- fromPositive :: BinNums.Coq_positive -> Integer
-- fromPositive BinNums.Coq_xH = 1
-- fromPositive (BinNums.Coq_xI bn) = fromPositive bn * 2 + 1
-- fromPositive (BinNums.Coq_xO bn) = fromPositive bn * 2
 
toBinZ :: Integer -> Integer
toBinZ = Prelude.id

toBinN :: Integer -> Integer
toBinN = Prelude.id

fromBinZ :: Integer -> Integer
fromBinZ = Prelude.id

fromBinN :: Integer -> Integer
fromBinN = Prelude.id

-- toBinZ :: Integer -> BinNums.Z
-- toBinZ 0 = BinNums.Z0
-- toBinZ x | x < 0 = BinNums.Zneg (toPositive (abs x))
-- toBinZ x | x > 0 = BinNums.Zpos (toPositive x)

-- toBinN :: Integer -> BinNums.N
-- toBinN 0 = BinNums.N0
-- toBinN x = BinNums.Npos (toPositive x)

-- fromBinZ :: BinNums.Z -> Integer
-- fromBinZ BinNums.Z0 = 0
-- fromBinZ (BinNums.Zneg bn) = - (fromPositive bn)
-- fromBinZ (BinNums.Zpos bn) = fromPositive bn

-- fromBinN :: BinNums.N -> Integer
-- fromBinN BinNums.N0 = 0
-- fromBinN (BinNums.Npos bn) = fromPositive bn

----------------------------------------------------

{-

instance Integral Num.Int where
  quot      = BinInt._Z__quot
  rem       = BinInt._Z__rem
  div       = BinInt._Z__div
  mod       = BinInt._Z__modulo
  quotRem   = BinInt._Z__quotrem
  divMod    = (\x y -> (,) (BinInt._Z__div x y) (BinInt._Z__modulo x y))
  toInteger = toInteger . fromBinZ

instance Eq Num.Int where
  (==) = BinInt._Z__eqb

instance Num Num.Int where
  (+)         = BinInt._Z__add
  (-)         = BinInt._Z__sub
  (*)         = BinInt._Z__mul
  negate      = BinInt._Z__opp
  abs         = BinInt._Z__abs
  signum      = BinInt._Z__sgn
  fromInteger = toBinZ . fromInteger

instance Ord Num.Int where
  compare = BinInt._Z__compare


instance Data.Bits.Bits Num.Int where
  (.&.)         = BinInt._Z__land
  (.|.)         = BinInt._Z__lor
  bit           = Bits.bit_Int . toBinZ . fromIntegral
  bitSizeMaybe  = \_ -> Prelude.Nothing
  clearBit      = \x i -> BinInt._Z__land x (Bits.complement_Int (Bits.bit_Int (toBinZ (fromIntegral i))))
  complement    = Bits.complement_Int
  complementBit = \ x i -> Bits.complementBit_Int x (toBinZ (fromIntegral i))
  isSigned      = \_ -> Prelude.False
  popCount      = fromIntegral . fromBinZ . Bits.popCount_Int
  rotate        = \x i -> Bits.shiftL_Int x (toBinZ (fromIntegral i))
  rotateL       = \x i -> Bits.shiftL_Int x (toBinZ (fromIntegral i))
  rotateR       = \x i ->  BinInt._Z__shiftr x (toBinZ (fromIntegral i))
  setBit        = \x i -> BinInt._Z__lor x (Bits.bit_Int (toBinZ (fromIntegral i)))
  shift         = \x i -> Bits.shift_Int x (toBinZ (fromIntegral i))
  shiftL        = \x i -> BinInt._Z__shiftl x (toBinZ (fromIntegral i))
  shiftR        = \x i -> BinInt._Z__shiftr x (toBinZ (fromIntegral i))
  testBit       = \x i -> BinInt._Z__testbit x (toBinZ (fromIntegral i))
  unsafeShiftL  = \x i ->  BinInt._Z__shiftl x (toBinZ (fromIntegral i))
  unsafeShiftR  = \x i -> BinInt._Z__shiftr x (toBinZ (fromIntegral i))
  xor           = BinInt._Z__lxor 
  zeroBits      = (Num.fromInteger Num.coq_Num_Integer__ BinNums.Z0)
  bitSize       = error "untranslated"


instance Integral Num.Word where
  quot      = BinNat._N__div
  rem       = BinNat._N__modulo
  div       = BinNat._N__div
  mod       = BinNat._N__modulo
  quotRem   = (\x y -> (,) (BinNat._N__div x y) (BinNat._N__modulo x y))
  divMod    = (\x y -> (,) (BinNat._N__div x y) (BinNat._N__modulo x y))
  toInteger = toInteger . fromBinN

instance Eq Num.Word where
  (==) = BinNat._N__eqb

instance Num Num.Word where
  (+)         = BinNat._N__add
  (-)         = BinNat._N__sub
  (*)         = BinNat._N__mul
  negate      = error "negate on Word does not make sense"
  abs         = (\ x -> x)
  signum      = (\x -> if x == 0 then 0 else 1)
  fromInteger = toBinN . fromInteger

instance Ord Num.Word where
  compare = BinNat._N__compare


instance Data.Bits.Bits Num.Word where
  (.&.)         = BinNat._N__land
  (.|.)         = BinNat._N__lor
  bit           = (BitUtil.shiftLL (BinNums.Npos BinNums.Coq_xH)) . toBinN . fromIntegral
  bitSizeMaybe  = \_ -> Prelude.Nothing
  clearBit      = \x i -> BinNat._N__clearbit x (toBinN (fromIntegral i))
  complement    = error "complement on Word undefined"
  complementBit = error "complementBit on Word undefined"
  isSigned      = \_ -> Prelude.True
  popCount      = fromIntegral . fromBinN . Bits.coq_N_popcount
  rotate        = \x i -> BinNat._N__shiftl x (toBinN (fromIntegral i))
  rotateL       = \x i -> BinNat._N__shiftl x (toBinN (fromIntegral i))
  rotateR       = \x i -> BinNat._N__shiftr x (toBinN (fromIntegral i))
  setBit        = \x i -> BinNat._N__setbit x (toBinN (fromIntegral i))
  shift         = \x i -> BinNat._N__shiftl x (toBinN (fromIntegral i))
  shiftL        = \x i -> BinNat._N__shiftl x (toBinN (fromIntegral i))
  shiftR        = \x i -> BinNat._N__shiftr x (toBinN (fromIntegral i))
  testBit       = \x i -> BinNat._N__testbit x (toBinN (fromIntegral i))
  unsafeShiftL  = \x i -> BinNat._N__shiftl x (toBinN (fromIntegral i))
  unsafeShiftR  = \x i -> BinNat._N__shiftr x (toBinN (fromIntegral i))
  xor           = BinNat._N__lxor 
  zeroBits      = 0
  bitSize       = error "untranslated"


----------------------------------------------------

instance Real Num.Int where
  toRational = error "TODO" 

instance Enum Num.Int where
  toEnum = undefined
  fromEnum = undefined
  
instance Real Num.Word where
  toRational = error "TODO" 

instance Enum Num.Word where
  toEnum = undefined
  fromEnum = undefined
-}
