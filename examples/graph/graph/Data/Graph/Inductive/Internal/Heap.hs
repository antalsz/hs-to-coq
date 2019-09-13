{-# LANGUAGE CPP #-}

-- | Pairing heap implementation of dictionary
module Data.Graph.Inductive.Internal.Heap(
    -- * Type
    Heap(..),
    prettyHeap,
    printPrettyHeap,
    -- * Operations
    empty,unit,insert,merge,mergeAll,
    isEmpty,findMin,deleteMin,splitMin,
    build, toList, heapsort
) where

import Text.Show (showListWith)

#if MIN_VERSION_containers (0,4,2)
import Control.DeepSeq (NFData (..))
#endif

data Heap a b = Empty | Node a b [Heap a b]
     deriving (Eq, Show, Read)

#if MIN_VERSION_containers (0,4,2)
instance (NFData a, NFData b) => NFData (Heap a b) where
  rnf Empty         = ()
  rnf (Node a b hs) = rnf a `seq` rnf b `seq` rnf hs
#endif

prettyHeap :: (Show a, Show b) => Heap a b -> String
prettyHeap = (`showsHeap` "")
  where
    showsHeap Empty             = id
    showsHeap (Node key val []) = shows key . (": "++) . shows val
    showsHeap (Node key val hs) = shows key . (": "++) . shows val
                                  .  (' ':) . showListWith showsHeap hs

printPrettyHeap :: (Show a, Show b) => Heap a b -> IO ()
printPrettyHeap = putStrLn . prettyHeap

----------------------------------------------------------------------
-- MAIN FUNCTIONS
----------------------------------------------------------------------

empty :: Heap a b
empty = Empty

unit :: a -> b -> Heap a b
unit key val = Node key val []

insert :: (Ord a) => (a, b) -> Heap a b -> Heap a b
insert (key, val) = merge (unit key val)

merge :: (Ord a) => Heap a b -> Heap a b -> Heap a b
merge h Empty = h
merge Empty h = h
merge h@(Node key1 val1 hs) h'@(Node key2 val2 hs')
    | key1<key2 = Node key1 val1 (h':hs)
    | otherwise = Node key2 val2 (h:hs')

mergeAll:: (Ord a) => [Heap a b] -> Heap a b
mergeAll []        = Empty
mergeAll [h]       = h
mergeAll (h:h':hs) = merge (merge h h') (mergeAll hs)

isEmpty :: Heap a b -> Bool
isEmpty Empty = True
isEmpty _     = False

findMin :: Heap a b -> (a, b)
findMin Empty      = error "Heap.findMin: empty heap"
findMin (Node key val _) = (key, val)

deleteMin :: (Ord a) => Heap a b -> Heap a b
deleteMin Empty             = Empty
deleteMin (Node _ _ hs) = mergeAll hs

splitMin :: (Ord a) => Heap a b -> (a,b,Heap a b)
splitMin Empty             = error "Heap.splitMin: empty heap"
splitMin (Node key val hs) = (key,val,mergeAll hs)


----------------------------------------------------------------------
-- APPLICATION FUNCTIONS, EXAMPLES
----------------------------------------------------------------------


build :: (Ord a) => [(a,b)] -> Heap a b
build = foldr insert Empty

toList :: (Ord a) => Heap a b -> [(a,b)]
toList Empty = []
toList h = x:toList r
           where (x,r) = (findMin h,deleteMin h)

heapsort :: (Ord a) => [a] -> [a]
heapsort = map fst . toList . build . map (\x->(x,x))
{-
l :: (Num a) => [a]
l  = [6,9,2,13,6,8,14,9,10,7,5]
l' = reverse l

h1  = build $ map (\x->(x,x)) l
h1' = build $ map (\x->(x,x)) l'

s1  = heapsort l
s1' = heapsort l'
-}
