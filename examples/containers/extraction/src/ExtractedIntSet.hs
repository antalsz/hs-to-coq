{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- This module is a wrapper (shim) for the extracted version of
-- Data.IntSet.Internal


module ExtractedIntSet where

import Unsafe.Coerce

-- import other extracted modules
import qualified Base
import qualified Datatypes
import qualified BinNums
import qualified Num
import qualified Foldable

import qualified Internal0 as S2

import qualified Data.Semigroup
import qualified Data.Monoid
import qualified Data.Foldable
import qualified Data.Bits
import qualified Control.Arrow as A
import Control.DeepSeq(NFData,rnf)

import Test.QuickCheck(NonNegative(..))

-- Shim for number types
import ExtractedNumbers

type IntSet = S2.IntSet
pattern Nil = S2.Nil
pattern Tip x y = S2.Tip x y
pattern Bin x1 x2 x3 x4 = S2.Bin x1 x2 x3 x4

type Mask   = S2.Mask
type BitMap = S2.BitMap
type Prefix = S2.Prefix
type Key    = S2.Key

type Nat = NonNegative Integer

binZToNonNeg :: Num.Word -> Nat
binZToNonNeg = NonNegative . fromBinN

nonNegToBinZ :: Nat -> Num.Word
nonNegToBinZ = toBinN . getNonNegative 

----------------------------------------------------

instance NFData (S2.IntSet) where
    rnf (S2.Tip p b)     = p `seq` b `seq` ()
    rnf (S2.Bin p y l r) = p `seq` y `seq` rnf l `seq` rnf r
    rnf S2.Nil           = ()

----------------------------------------------------

instance Eq (S2.IntSet) where
  (==) = S2.coq_Eq___IntSet_op_zeze__ 
  (/=) = S2.coq_Eq___IntSet_op_zsze__ 

instance Prelude.Ord (S2.IntSet) where
  compare = S2.coq_Ord__IntSet_compare
  (>)     = S2.coq_Ord__IntSet_op_zg__
  (>=)    = S2.coq_Ord__IntSet_op_zgze__ 
  (<)     = S2.coq_Ord__IntSet_op_zl__ 
  (<=)    = S2.coq_Ord__IntSet_op_zlze__ 
  max     = S2.coq_Ord__IntSet_max 
  min     = S2.coq_Ord__IntSet_min 

instance Data.Semigroup.Semigroup (S2.IntSet) where
  (<>)    = S2.coq_Semigroup__IntSet_op_zlzlzgzg__ 
  sconcat = error "no defn"
  stimes  = error "no defn"

instance Data.Monoid.Monoid (S2.IntSet) where
  mempty  = S2.coq_Monoid__IntSet_mempty  
  mappend = S2.coq_Monoid__IntSet_mappend 
  mconcat = S2.coq_Monoid__IntSet_mconcat 

instance Show (S2.IntSet) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (toList xs)

zero :: Nat -> Mask -> Bool
zero x m = S2.zero (nonNegToBinZ x) m

----------------------------------------------------------------
-- for unit tests
----------------------------------------------------------------

lookupLT :: Nat  -> IntSet -> Maybe Nat
lookupLT x s = binZToNonNeg <$> S2.lookupLT (nonNegToBinZ x) s

lookupGT :: Nat -> IntSet -> Maybe Nat
lookupGT x s = binZToNonNeg <$> S2.lookupGT  (nonNegToBinZ x) s

lookupLE :: Nat -> IntSet -> Maybe Nat
lookupLE x s = binZToNonNeg <$> S2.lookupLE  (nonNegToBinZ x) s

lookupGE :: Nat -> IntSet -> Maybe Nat
lookupGE x s = binZToNonNeg <$> S2.lookupGE  (nonNegToBinZ x) s


--------------------------------------------------
-- Indexed
--------------------------------------------------

-- findIndex   = error "findIndex: partial function"
-- elemAt      = error "elemAt: partial function"
-- deleteAt    = error "deleteAt: partial function"

--------------------------------------------------
-- Valid Trees
--------------------------------------------------

-- I dunno how to get pattern synonyms to do this
bin s = S2.Bin (toBinN s)

-- need to translate BinNums.Z -> Int
size :: IntSet -> Int
size x = fromIntegral $ fromBinN (S2.size x)

--------------------------------------------------
-- Single, Member, Insert, Delete
--------------------------------------------------
empty :: IntSet
empty = S2.empty

singleton :: Nat -> IntSet
singleton x = S2.singleton (nonNegToBinZ x)

member ::  Nat -> IntSet -> Bool
member x = S2.member (nonNegToBinZ x)

notMember ::  Nat -> IntSet -> Bool
notMember x = S2.notMember (nonNegToBinZ x)

insert ::  Nat -> IntSet -> IntSet
insert x = S2.insert (nonNegToBinZ x)

delete ::  Nat -> IntSet -> IntSet
delete x = S2.delete (nonNegToBinZ x)

{--------------------------------------------------------------------
  Balance
--------------------------------------------------------------------}

split :: Nat -> IntSet -> (IntSet, IntSet)
split x = S2.split (nonNegToBinZ x)

link = S2.link

{--------------------------------------------------------------------
  Union
--------------------------------------------------------------------}

union :: (IntSet) -> (IntSet) -> IntSet
union = S2.union 

difference :: (IntSet) -> (IntSet) -> IntSet
difference = S2.difference 

intersection ::  (IntSet) -> (IntSet) -> IntSet
intersection = S2.intersection

disjoint ::  (IntSet) -> (IntSet) -> Bool
disjoint = S2.disjoint

null :: IntSet -> Bool
null = S2.null

{--------------------------------------------------------------------
  Lists
--------------------------------------------------------------------}

--fromAscList :: [Nat] -> IntSet
--fromAscList xs = error "fromAscList: untranslated"

--fromDistinctAscList :: [Nat] -> IntSet
--fromDistinctAscList xs = error "fromDistinctAscList: untranslated"


fromList :: [Nat] -> IntSet
fromList xs = S2.fromList (Prelude.map nonNegToBinZ xs)


toDescList :: IntSet -> [Nat]
toDescList x = Prelude.map binZToNonNeg (S2.toDescList x)

toAscList :: IntSet -> [Nat]
toAscList x = Prelude.map binZToNonNeg (S2.toAscList x)

toList :: IntSet -> [Nat]
toList x = Prelude.map binZToNonNeg (S2.toList x)


{--------------------------------------------------------------------
  Set operations are like IntSet operations
--------------------------------------------------------------------}


foldr :: (Nat -> a -> a) -> a -> IntSet -> a
foldr f b s = S2.foldr (f . binZToNonNeg) b s

foldr' :: (Nat -> a -> a) -> a -> IntSet -> a
foldr' f b s = S2.foldr' (f . binZToNonNeg) b s

foldl' :: (a -> Nat -> a) -> a -> IntSet -> a
foldl' f b s = S2.foldl' (\ x y -> f x (binZToNonNeg y)) b s

foldl :: (a -> Nat -> a) -> a -> IntSet -> a
foldl f b s = S2.foldl (\x y -> f x (binZToNonNeg y)) b s

fold   = S2.fold
filter = S2.filter
map    = S2.map


elems  :: IntSet -> [Nat]
elems x = Prelude.map binZToNonNeg (S2.elems x) 

isProperSubsetOf :: IntSet -> IntSet -> Bool
isProperSubsetOf = S2.isProperSubsetOf 

isSubsetOf :: IntSet -> IntSet -> Bool
isSubsetOf = S2.isSubsetOf 

findMax :: IntSet -> Nat
findMax = error "partial"

findMin :: IntSet -> Nat
findMin = error "partial"


minView :: IntSet -> Maybe (Nat,IntSet)
minView s = (A.first binZToNonNeg) <$> S2.minView s

maxView :: IntSet -> Maybe (Nat,IntSet)
maxView s = (A.first binZToNonNeg) <$> S2.maxView s

splitMember :: Nat -> IntSet -> (IntSet, Bool, IntSet)
splitMember m s = (x,y,z) where
  ((x,y),z) = S2.splitMember (nonNegToBinZ m) s

-- See comment in src/ExtractedSet.hs
unions :: [IntSet] -> IntSet
unions = S2.unions (unsafeCoerce (\_ -> Foldable.coq_Foldable__list))

splitRoot :: IntSet -> [IntSet]
splitRoot = S2.splitRoot

partition :: (Nat -> Bool) -> IntSet -> (IntSet, IntSet)
partition f = S2.partition (f . binZToNonNeg)

match :: Nat -> S2.Prefix -> S2.Mask -> Prelude.Bool
match x y z = S2.match_ (nonNegToBinZ x) y z


