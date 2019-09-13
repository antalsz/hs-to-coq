{- |
   Module      : Data.Graph.Inductive.Proxy
   Description : Proxy type for graph tests
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : BSD3
   Maintainer  : Ivan.Miljenovic@gmail.com

   To avoid relying upon a newer version of base, this defines a
   custom Proxy type and convenience functions.

 -}
module Data.Graph.Inductive.Proxy where

import qualified Data.Graph.Inductive.PatriciaTree as P
import qualified Data.Graph.Inductive.Tree         as T

import Data.Word (Word8)

-- -----------------------------------------------------------------------------

-- By default, we want to avoid using 'Int' to avoid clashing with the
-- 'Node' type.  Don't want to use a floating type in case of
-- potential Eq problems.
type GraphType gr = gr Char Word8

type GraphProxy gr = Proxy (GraphType gr)

type TreeP = GraphProxy T.Gr

type PatriciaTreeP = GraphProxy P.Gr

-- Not using the Data.Proxy module so this also works with older
-- versions of GHC.

data Proxy a = Proxy
  deriving (Eq, Ord, Show, Read)

asProxyTypeOf :: a -> Proxy a -> a
asProxyTypeOf a _ = a

withProxy :: Proxy a -> a -> a
withProxy _ a = a

asProxyGraphTypeOf :: gr () () -> Proxy (gr a b) -> gr () ()
asProxyGraphTypeOf gr _ = gr
