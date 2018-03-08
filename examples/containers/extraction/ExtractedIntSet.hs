{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- This module is a wrapper (shim) for the extracted version of
-- Data.IntSet.Internal


module ExtractedIntSet where

import qualified Base
import qualified Datatypes
import qualified BinNums
import qualified Num

import qualified Semigroup
import qualified Monoid

import qualified Internal0 as S2

import qualified Data.Semigroup
import qualified Data.Monoid
import qualified Data.Foldable
import qualified Data.Bits

import qualified Control.Arrow as A
import Control.DeepSeq(NFData,rnf)

import Test.QuickCheck(NonNegative(..))

import ExtractedNumbers

type IntSet = S2.IntSet
pattern Nil = S2.Nil
pattern Tip x y = S2.Tip x y
pattern Bin x1 x2 x3 x4 = S2.Bin x1 x2 x3 x4

type Mask   = S2.Mask
type BitMap = S2.BitMap
type Prefix = S2.Prefix
type Key    = S2.Key

binZToNonNeg :: Num.Int -> NonNegative Int
binZToNonNeg = NonNegative . fromBinZ

nonNegToBinZ :: NonNegative Int -> Num.Int
nonNegToBinZ = toBinZ . getNonNegative 

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
  (<>)    = S2.coq_Semigroup__IntSet_op_zlzg__ 
  sconcat = error "no defn"
  stimes  = error "no defn"

instance Data.Monoid.Monoid (S2.IntSet) where
  mempty  = S2.coq_Monoid__IntSet_mempty  
  mappend = S2.coq_Monoid__IntSet_mappend 
  mconcat = S2.coq_Monoid__IntSet_mconcat 

instance Show (S2.IntSet) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (toList xs)

{-
instance Data.Foldable.Foldable S2.IntSet where
  fold    = fold
  foldMap = S2.coq_Foldable__IntSet_foldMap monoid_a
  foldr   = S2.foldr
  foldr'  = S2.foldr'
  foldl   = S2.foldl
  foldl'  = S2.foldl'
  foldr1  = error "foldr1: partial"
  foldl1  = error "foldl1: partial"
  toList  = S2.toList
  null    = S2.null
  length  = error "fix int problem" -- S2.length
  elem    = S2.coq_Foldable__IntSet_elem eq_a
  maximum = error "maximum: partial"
  minimum = error "minimum: partial"
  sum     = error "TODO, figure out Num shim"
  product = error "TODO, figure out Num shim"
-}

zero :: (NonNegative Int) -> Mask -> Bool
zero x m = S2.zero (nonNegToBinZ x) m

----------------------------------------------------------------
-- for unit tests
----------------------------------------------------------------

lookupLT :: (NonNegative Int)  -> IntSet -> Maybe (NonNegative Int)
lookupLT x s = binZToNonNeg <$> S2.lookupLT (nonNegToBinZ x) s

lookupGT :: (NonNegative Int) -> IntSet -> Maybe (NonNegative Int)
lookupGT x s = binZToNonNeg <$> S2.lookupGT  (nonNegToBinZ x) s

lookupLE :: (NonNegative Int) -> IntSet -> Maybe (NonNegative Int)
lookupLE x s = binZToNonNeg <$> S2.lookupLE  (nonNegToBinZ x) s

lookupGE :: (NonNegative Int) -> IntSet -> Maybe (NonNegative Int)
lookupGE x s = binZToNonNeg <$> S2.lookupGE  (nonNegToBinZ x) s


--------------------------------------------------
-- Indexed
--------------------------------------------------

findIndex   = error "findIndex: partial function"
elemAt      = error "elemAt: partial function"
deleteAt    = error "deleteAt: partial function"

--------------------------------------------------
-- Valid Trees
--------------------------------------------------

-- I dunno how to get pattern synonyms to do this
bin s = S2.Bin (toBinZ s)

-- need to translate BinNums.Z -> Int
size :: IntSet -> Int
size x = fromBinZ (S2.size x)

--------------------------------------------------
-- Single, Member, Insert, Delete
--------------------------------------------------
empty :: IntSet
empty = S2.empty

singleton :: NonNegative Int -> IntSet
singleton x = S2.singleton (nonNegToBinZ x)

member ::  (NonNegative Int) -> IntSet -> Bool
member x = S2.member (nonNegToBinZ x)

notMember ::  (NonNegative Int) -> IntSet -> Bool
notMember x = S2.notMember (nonNegToBinZ x)

insert ::  (NonNegative Int) -> IntSet -> IntSet
insert x = S2.insert (nonNegToBinZ x)

delete ::  (NonNegative Int) -> IntSet -> IntSet
delete x = S2.delete (nonNegToBinZ x)

{--------------------------------------------------------------------
  Balance
--------------------------------------------------------------------}

split :: NonNegative Int -> IntSet -> (IntSet, IntSet)
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

fromAscList :: [(NonNegative Int)] -> IntSet
fromAscList xs = error "fromAscList: untranslated"

fromDistinctAscList :: [(NonNegative Int)] -> IntSet
fromDistinctAscList xs = error "fromDistinctAscList: untranslated"


fromList :: [(NonNegative Int)] -> IntSet
fromList xs = S2.fromList (Prelude.map nonNegToBinZ xs)


toDescList :: IntSet -> [(NonNegative Int)]
toDescList x = Prelude.map binZToNonNeg (S2.toDescList x)

toAscList :: IntSet -> [(NonNegative Int)]
toAscList x = Prelude.map binZToNonNeg (S2.toAscList x)

toList :: IntSet -> [(NonNegative Int)]
toList x = Prelude.map binZToNonNeg (S2.toList x)


{--------------------------------------------------------------------
  Set operations are like IntSet operations
--------------------------------------------------------------------}


foldr :: ((NonNegative Int) -> a -> a) -> a -> IntSet -> a
foldr f b s = S2.foldr (f . binZToNonNeg) b s

foldr' :: ((NonNegative Int) -> a -> a) -> a -> IntSet -> a
foldr' f b s = S2.foldr' (f . binZToNonNeg) b s

foldl' :: (a -> (NonNegative Int) -> a) -> a -> IntSet -> a
foldl' f b s = S2.foldl' (\ x y -> f x (binZToNonNeg y)) b s

foldl :: (a -> (NonNegative Int) -> a) -> a -> IntSet -> a
foldl f b s = S2.foldl (\x y -> f x (binZToNonNeg y)) b s

fold   = S2.fold
filter = S2.filter
map    = S2.map


elems  :: IntSet -> [(NonNegative Int)]
elems x = Prelude.map binZToNonNeg (S2.elems x) 

isProperSubsetOf :: IntSet -> IntSet -> Bool
isProperSubsetOf = S2.isProperSubsetOf 

isSubsetOf :: IntSet -> IntSet -> Bool
isSubsetOf = S2.isSubsetOf 

findMax :: IntSet -> (NonNegative Int)
findMax = error "partial"

findMin :: IntSet -> (NonNegative Int)
findMin = error "partial"


minView :: IntSet -> Maybe (NonNegative Int,IntSet)
minView s = (A.first binZToNonNeg) <$> S2.minView s

maxView :: IntSet -> Maybe ((NonNegative Int),IntSet)
maxView s = (A.first binZToNonNeg) <$> S2.maxView s

splitMember :: (NonNegative Int) -> IntSet -> (IntSet, Bool, IntSet)
splitMember m s = (x,y,z) where
  ((x,y),z) = S2.splitMember (nonNegToBinZ m) s


unions :: [IntSet] -> IntSet
unions = S2.unions 

splitRoot :: IntSet -> [IntSet]
splitRoot = S2.splitRoot

partition :: ((NonNegative Int) -> Bool) -> IntSet -> (IntSet, IntSet)
partition f = S2.partition (f . binZToNonNeg)

match :: (NonNegative Int) -> S2.Prefix -> S2.Mask -> Prelude.Bool
match x y z = S2.match_ (nonNegToBinZ x) y z


