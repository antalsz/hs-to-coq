-- (c) 1999 by Martin Erwig
-- | Threading Combinators.
module Data.Graph.Inductive.Internal.Thread(
    -- * Types
    Split, SplitM, Thread, Collect,
    -- * Operations
    threadList', threadList, threadMaybe', threadMaybe, splitPar, splitParM
) where

-- import Graph
-- import GraphData
-- import qualified Diet as D

-- import ADT

----------------------------------------------------------------------
-- CLASSES AND TYPES
----------------------------------------------------------------------

{-
class Thread t a b where
  split :: a -> t -> (b,t)


instance Thread (Graph a b) Node (MContext a b) where
  split = match

instance (D.Discrete a) => Thread (D.Diet a) a a where
  split x s = (x,D.delete x s)
-}

{-
   Make clear different notions:

   "thread" = data structure + split operation
   ...      = threadable data structure
   ...      = split operation

-}


----------------------------------------------------------------------
-- THREAD COMBINATORS
----------------------------------------------------------------------


-- (A) split along a list of indexes and thread data structure
--
-- there are different ways to consume the returned elements:

{-
--  (1) simple collect in a list
--
foldT1' ys []     d = ys
foldT1' ys (x:xs) d = foldT1' (y:ys) xs d'  where (y,d') = split x d
foldT1 xs d = foldT1' [] xs d

--  (2) combine by a function
--
foldT2' f ys []     d = ys
foldT2' f ys (x:xs) d = foldT2' f (f y ys) xs d'  where (y,d') = split x d
foldT2 f u xs d = foldT2' f u xs d
-}


-- Mnemonics:
--
--  t : thread type
--  i : index type
--  r : result type
--  c : collection type
--
type Split t i r  = i -> t -> (r,t)
type Thread t i r = (t,Split t i r)
type Collect r c  = (r -> c -> c,c)

--  (3) abstract from split
--
threadList' :: Collect r c -> Split t i r -> [i] -> t -> (c,t)
threadList' (_,c) _ []         t = (c,t)
threadList' (f,c) split (i:is) t = threadList' (f,f r c) split is t'
                                   where (r,t') = split i t

{-
   Note: threadList' works top-down (or, from left),
         whereas dfs,gfold,... have been defined bottom-up (or from right).

   ==> therefore, we define a correpsonding operator for folding
       bottom-up/from right.
-}
threadList :: Collect r c -> Split t i r -> [i] -> t -> (c,t)
threadList (_,c) _ []     t  = (c,t)
threadList (f,c) split (i:is) t = (f r c',t'')
                                  where (r,t')   = split i t
                                        (c',t'') = threadList (f,c) split is t'



-- (B) thread "maybes", ie, apply f to Just-values and continue
--     threading with "continuation" c, and ignore Nothing-values, ie,
--     stop threading and return current data structure.
--
-- threadMaybe' :: (r -> b) -> Split t i r -> (e -> f -> (Maybe i,t))
--                 -> e -> f -> (Maybe b,t)

type SplitM t i r = Split t i (Maybe r)

threadMaybe' :: (r->a)->Split t i r->Split t j (Maybe i)->Split t j (Maybe a)
threadMaybe' f cont split j t =
      case mi of Just i  -> (Just (f r),t'') where (r,t'') = cont i t'
                 Nothing -> (Nothing,t')
      where (mi,t') = split j t

-- extension:  grant f access also to y, the result of split.
--
-- threadMaybe :: (a -> b -> c) -> (a -> d -> (b,d)) -> (e -> f -> (Maybe a,d))
--                -> e -> f -> (Maybe c,d)
-- threadMaybe :: (i->r->a)->Split t i r->Split t j (Maybe i)->Split t j (Maybe a)
threadMaybe :: (i -> r -> a) -> Split t i r -> SplitM t j i -> SplitM t j a
threadMaybe f cont split j t =
      case mi of Just i  -> (Just (f i r),t'') where (r,t'') = cont i t'
                 Nothing -> (Nothing,t')
      where (mi,t') = split j t


-- (C) compose splits in parallel (is a kind of generalized zip)
--
-- splitPar :: (a -> b -> (c,d)) -> (e -> f -> (g,h))
--             -> (a,e) -> (b,f) -> ((c,g),(d,h))
splitPar :: Split t i r -> Split u j s -> Split (t,u) (i,j) (r,s)
splitPar split split' (i,j) (t,u) = ((r,s),(t',u'))
                                    where (r,t') = split i t
                                          (s,u') = split' j u

splitParM :: SplitM t i r -> Split u j s -> SplitM (t,u) (i,j) (r,s)
splitParM splitm split (i,j) (t,u) =
          case mr of Just r  -> (Just (r,s),(t',u'))
                     Nothing -> (Nothing,(t',u))   -- ignore 2nd split
          where (mr,t') = splitm i t
                (s,u')  = split j u


-- (D) merge a thread with/into a computation
--
{-
   Example: assign consecutive numbers to the nodes of a tree

   Input: type d, thread (t,split), fold operation on d
-}
