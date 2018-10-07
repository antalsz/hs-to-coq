module Memo where

import Numeric.Natural

data NatTrie a = TrieNode
    { here       :: a
    , div2       :: NatTrie a
    , minus1div2 :: NatTrie a
    }

mkTrie :: (Natural -> a) -> NatTrie a
mkTrie f = TrieNode
    { here       = f 0
    , div2       = mkTrie $ f . (*2)
    , minus1div2 = mkTrie $ f . (+1) . (*2)
    }

lookupTrie :: NatTrie a -> Natural -> a
lookupTrie (TrieNode here div2 minus1div2) n
    | n == 0    = here
    | odd n     = lookupTrie minus1div2 (n `div` 2)
    | otherwise = lookupTrie div2 (n `div` 2)

slowFib, cachedFib :: Natural -> Natural
slowFib 0 = 0
slowFib 1 = 1
slowFib n = slowFib (n - 1) + slowFib (n - 2)

cachedFib = lookupTrie (mkTrie slowFib)
