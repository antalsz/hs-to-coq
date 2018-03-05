module ExtractedSet where

import Base
import Datatypes

import qualified Semigroup
import qualified Monoid
import qualified Internal as S2

import qualified Data.Semigroup
import qualified Data.Monoid
import qualified Data.Foldable


type Set = S2.Set_

eq_a :: Eq a => Base.Eq_ a
eq_a _ f = f (Base.Eq___Dict_Build (==) (/=))

ord_a :: Prelude.Ord a => Base.Ord a
ord_a _ = ord_default Prelude.compare eq_a
  
semigroup_a :: Data.Semigroup.Semigroup a => Semigroup.Semigroup a
semigroup_a _ f = f ((Data.Semigroup.<>))

monoid_a :: Data.Monoid.Monoid a => Base.Monoid a
monoid_a _ f = f (Base.Monoid__Dict_Build Data.Monoid.mappend
                   Data.Monoid.mconcat Data.Monoid.mempty)

instance (Eq a) => Eq (S2.Set_ a) where
  (==) = S2.coq_Eq___Set__op_zeze__ eq_a
  (/=) = S2.coq_Eq___Set__op_zsze__ eq_a

instance (Prelude.Ord a) => Prelude.Ord (S2.Set_ a) where
  compare = S2.coq_Ord__Set__compare eq_a ord_a
  (>)     = S2.coq_Ord__Set__op_zg__ eq_a ord_a
  (>=)    = S2.coq_Ord__Set__op_zgze__ eq_a ord_a
  (<)     = S2.coq_Ord__Set__op_zl__ eq_a ord_a
  (<=)    = S2.coq_Ord__Set__op_zlze__ eq_a ord_a
  max     = S2.coq_Ord__Set__max eq_a ord_a
  min     = S2.coq_Ord__Set__min eq_a ord_a

instance (Prelude.Ord a) => Data.Semigroup.Semigroup (S2.Set_ a) where
  (<>)    = S2.coq_Semigroup__Set__op_zlzg__ eq_a ord_a
  sconcat = error "no defn"
  stimes  = error "no defn"

instance (Prelude.Ord a) => Data.Monoid.Monoid (S2.Set_ a) where
  mempty  = S2.coq_Monoid__Set__mempty  eq_a ord_a
  mappend = S2.coq_Monoid__Set__mappend eq_a ord_a
  mconcat = S2.coq_Monoid__Set__mconcat eq_a ord_a

instance (Show a) => Show (S2.Set_ a) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (Data.Foldable.toList xs)


instance Data.Foldable.Foldable S2.Set_ where
  fold    = S2.coq_Foldable__Set__fold    monoid_a
  foldMap = S2.coq_Foldable__Set__foldMap monoid_a
  foldr   = S2.foldr
  foldr'  = S2.foldr'
  foldl   = S2.foldl
  foldl'  = S2.foldl'
  foldr1  = error "partial"
  foldl1  = error "partial"
  toList  = S2.toList
  null    = S2.null
  length  = error "fix int problem" -- S2.length
  elem    = S2.coq_Foldable__Set__elem eq_a
  maximum = error "partial"
  minimum = error "partial"
  sum     = error "TODO"
  product = error "TODO"
  

-- need to translate BinNums.Z -> Int
--size :: Set a -> Int
--size = S2.size

member :: Prelude.Ord a => a -> Set a -> Bool
member = S2.member eq_a ord_a

toAscList :: Set a -> [a]
toAscList = S2.toAscList

fromAscList :: Eq a => [a] -> Set a
fromAscList = S2.fromAscList eq_a

lookupLT :: Prelude.Ord a => a -> Set a -> Maybe a
lookupLT = S2.lookupLT eq_a ord_a

lookupGT :: Prelude.Ord a => a -> Set a -> Maybe a
lookupGT = S2.lookupGT eq_a ord_a

lookupLE :: Prelude.Ord a => a -> Set a -> Maybe a
lookupLE = S2.lookupLE eq_a ord_a

lookupGE :: Prelude.Ord a => a -> Set a -> Maybe a
lookupGE = S2.lookupGE eq_a ord_a


fromList :: Prelude.Ord a => [a] -> Set a
fromList = S2.fromList eq_a ord_a
