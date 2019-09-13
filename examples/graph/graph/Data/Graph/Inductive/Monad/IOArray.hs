{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}

-- (c) 2002 by Martin Erwig [see file COPYRIGHT]
-- | Static IOArray-based Graphs
module Data.Graph.Inductive.Monad.IOArray(
    -- * Graph Representation
    SGr(..), GraphRep, Context', USGr,
    defaultGraphSize, emptyN,
    -- * Utilities
    removeDel,
) where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Monad

import Control.Monad
import Data.Array
import Data.Array.IO
import System.IO.Unsafe



----------------------------------------------------------------------
-- GRAPH REPRESENTATION
----------------------------------------------------------------------

newtype SGr a b = SGr (GraphRep a b)

type GraphRep a b = (Int,Array Node (Context' a b),IOArray Node Bool)
type Context' a b = Maybe (Adj b,a,Adj b)

type USGr = SGr () ()


----------------------------------------------------------------------
-- CLASS INSTANCES
----------------------------------------------------------------------

-- Show
--
showGraph :: (Show a,Show b) => GraphRep a b -> String
showGraph (_,a,m) = concatMap showAdj (indices a)
    where showAdj v | unsafePerformIO (readArray m v) = ""
                    | otherwise = case a!v of
                        Nothing      -> ""
                        Just (_,l,s) -> '\n':show v++":"++show l++"->"++show s'
                          where s' = unsafePerformIO (removeDel m s)

-- | Please note that this instance is unsafe.
instance (Show a,Show b) => Show (SGr a b) where
  show (SGr g) = showGraph g

-- | Please note that this instance is unsafe.
instance (Show a,Show b) => Show (IO (SGr a b)) where
  show g = unsafePerformIO (do {(SGr g') <- g; return (showGraph g')})

{-
run :: Show (IO a) => IO a -> IO ()
run x = seq x (print x)
-}

-- GraphM
--
instance GraphM IO SGr where
  emptyM = emptyN defaultGraphSize
  isEmptyM g = do {SGr (n,_,_) <- g; return (n==0)}
  matchM v g = do g'@(SGr (n,a,m)) <- g
                  case a!v of
                    Nothing -> return (Nothing,g')
                    Just (pr,l,su) ->
                       do b <- readArray m v
                          if b then return (Nothing,g') else
                             do s  <- removeDel m su
                                p' <- removeDel m pr
                                let p = filter ((/=v).snd) p'
                                writeArray m v True
                                return (Just (p,v,l,s),SGr (n-1,a,m))
  mkGraphM vs es = do m <- newArray (1,n) False
                      return (SGr (n,pr,m))
          where nod  = array bnds (map (\(v,l)->(v,Just ([],l,[]))) vs)
                su   = accum addSuc nod (map (\(v,w,l)->(v,(l,w))) es)
                pr   = accum addPre su (map (\(v,w,l)->(w,(l,v))) es)
                bnds = (minimum vs',maximum vs')
                vs'  = map fst vs
                n    = length vs
                addSuc (Just (p,l',s)) (l,w) = Just (p,l',(l,w):s)
                addSuc Nothing _ = error "mkGraphM (SGr): addSuc Nothing"
                addPre (Just (p,l',s)) (l,w) = Just ((l,w):p,l',s)
                addPre Nothing _ = error "mkGraphM (SGr): addPre Nothing"
  labNodesM g = do (SGr (_,a,m)) <- g
                   let getLNode vs (_,Nothing)      = return vs
                       getLNode vs (v,Just (_,l,_)) =
                           do b <- readArray m v
                              return (if b then vs else (v,l):vs)
                   foldM getLNode [] (assocs a)

defaultGraphSize :: Int
defaultGraphSize = 100

emptyN :: Int -> IO (SGr a b)
emptyN n = do m <- newArray (1,n) False
              return (SGr (0,array (1,n) [(i,Nothing) | i <- [1..n]],m))

----------------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------------



-- | filter list (of successors\/predecessors) through a boolean ST array
-- representing deleted marks
removeDel :: IOArray Node Bool -> Adj b -> IO (Adj b)
removeDel m = filterM (\(_,v)->do {b<-readArray m v;return (not b)})
