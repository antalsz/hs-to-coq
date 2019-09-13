-- (c) 2000 - 2002 by Martin Erwig [see file COPYRIGHT]
-- | Maximum Independent Node Sets
module Data.Graph.Inductive.Query.Indep (
    indep
  , indepSize
  ) where

import Data.Graph.Inductive.Graph

import Control.Arrow ((***))
import Data.Function (on)
import Data.List     (maximumBy)

-- -----------------------------------------------------------------------------

-- | Calculate the maximum independent node set of the specified
--   graph.
indep :: (DynGraph gr) => gr a b -> [Node]
indep = fst . indepSize

-- | The maximum independent node set along with its size.
indepSize :: (DynGraph gr) => gr a b -> ([Node], Int)
indepSize g
  | isEmpty g = ([], 0)
  | l1 > l2   = il1
  | otherwise = il2
  where
    vs          = nodes g
    v           = snd . maximumBy (compare `on` fst)
                  . map ((,) =<< deg g) $ vs
    (Just c,g') = match v g
    il1@(_,l1)  = indepSize g'
    il2@(_,l2)  = ((v:) *** (+1)) $ indepSize (delNodes (neighbors' c) g')
