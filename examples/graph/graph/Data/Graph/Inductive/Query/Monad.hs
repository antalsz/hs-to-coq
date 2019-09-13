{-# LANGUAGE CPP, MultiParamTypeClasses #-}

-- (c) 2002 by Martin Erwig [see file COPYRIGHT]
-- | Monadic Graph Algorithms

module Data.Graph.Inductive.Query.Monad(
    -- * Additional Graph Utilities
    mapFst, mapSnd, (><), orP,
    -- * Graph Transformer Monad
    GT(..), apply, apply', applyWith, applyWith', runGT, condMGT', recMGT',
    condMGT, recMGT,
    -- * Graph Computations Based on Graph Monads
    -- ** Monadic Graph Accessing Functions
    getNode, getContext, getNodes', getNodes, sucGT, sucM,
    -- ** Derived Graph Recursion Operators
    graphRec, graphRec', graphUFold,
    -- * Examples: Graph Algorithms as Instances of Recursion Operators
    -- ** Instances of graphRec
    graphNodesM0, graphNodesM, graphNodes, graphFilterM, graphFilter,
    -- * Example: Monadic DFS Algorithm(s)
    dfsGT, dfsM, dfsM', dffM, graphDff, graphDff',
) where


-- Why all this?
--
-- graph monad ensures single-threaded access
--  ==> we can safely use imperative updates in the graph implementation
--

import Control.Monad (ap, liftM, liftM2)
import Data.Tree

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative (Applicative (..))
#endif

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Monad

-- some additional (graph) utilities
--
mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (x,y) = (f x,y)
mapSnd :: (a -> b) -> (c, a) -> (c, b)
mapSnd f (x,y) = (x,f y)

infixr 8 ><
(><) :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
(f >< g) (x,y) = (f x,g y)

orP :: (a -> Bool) -> (b -> Bool) -> (a,b) -> Bool
orP p q (x,y) = p x || q y

----------------------------------------------------------------------
-- "wrapped" state transformer monad   ==
-- monadic graph transformer monad
----------------------------------------------------------------------

newtype GT m g a = MGT (m g -> m (a,g))

apply :: GT m g a -> m g -> m (a,g)
apply (MGT f) = f

apply' :: (Monad m) => GT m g a -> g -> m (a,g)
apply' gt = apply gt . return

applyWith :: (Monad m) => (a -> b) -> GT m g a -> m g -> m (b,g)
applyWith h (MGT f) gm = do {(x,g) <- f gm; return (h x,g)}

applyWith' :: (Monad m) => (a -> b) -> GT m g a -> g -> m (b,g)
applyWith' h gt = applyWith h gt . return

runGT :: (Monad m) => GT m g a -> m g -> m a
runGT gt mg = do {(x,_) <- apply gt mg; return x}

instance (Monad m) => Functor (GT m g) where
    fmap  = liftM

instance (Monad m) => Applicative (GT m g) where
    pure  = return
    (<*>) = ap

instance (Monad m) => Monad (GT m g) where
  return x = MGT (\mg->do {g<-mg; return (x,g)})
  f >>= h  = MGT (\mg->do {(x,g)<-apply f mg; apply' (h x) g})

condMGT' :: (Monad m) => (s -> Bool) -> GT m s a -> GT m s a -> GT m s a
condMGT' p f g = MGT (\mg->do {h<-mg; if p h then apply f mg else apply g mg})

recMGT' :: (Monad m) => (s -> Bool) -> GT m s a -> (a -> b -> b) -> b -> GT m s b
recMGT' p mg f u = condMGT' p (return u)
                            (do {x<-mg;y<-recMGT' p mg f u;return (f x y)})

condMGT :: (Monad m) => (m s -> m Bool) -> GT m s a -> GT m s a -> GT m s a
condMGT p f g = MGT (\mg->do {b<-p mg; if b then apply f mg else apply g mg})

recMGT :: (Monad m) => (m s -> m Bool) -> GT m s a -> (a -> b -> b) -> b -> GT m s b
recMGT p mg f u = condMGT p (return u)
                          (do {x<-mg;y<-recMGT p mg f u;return (f x y)})


----------------------------------------------------------------------
-- graph computations based on state monads/graph monads
----------------------------------------------------------------------


-- some monadic graph accessing functions
--
getNode :: (GraphM m gr) => GT m (gr a b) Node
getNode = MGT (\mg->do {((_,v,_,_),g) <- matchAnyM mg; return (v,g)})

getContext :: (GraphM m gr) => GT m (gr a b) (Context a b)
getContext = MGT matchAnyM

-- some functions defined by using the do-notation explicitly
-- Note: most of these can be expressed as an instance of graphRec
--
getNodes' :: (Graph gr,GraphM m gr) => GT m (gr a b) [Node]
getNodes' = condMGT' isEmpty (return []) nodeGetter

getNodes :: (GraphM m gr) => GT m (gr a b) [Node]
getNodes = condMGT isEmptyM (return []) nodeGetter

nodeGetter :: (GraphM m gr) => GT m (gr a b) [Node]
nodeGetter = liftM2 (:) getNode getNodes

sucGT :: (GraphM m gr) => Node -> GT m (gr a b) (Maybe [Node])
sucGT v = MGT (\mg->do (c,g) <- matchM v mg
                       case c of
                         Just (_,_,_,s) -> return (Just (map snd s),g)
                         Nothing        -> return (Nothing,g)
              )

sucM :: (GraphM m gr) => Node -> m (gr a b) -> m (Maybe [Node])
sucM v = runGT (sucGT v)



----------------------------------------------------------------------
-- some derived graph recursion operators
----------------------------------------------------------------------

--
-- graphRec :: GraphMonad a b c -> (c -> d -> d) -> d -> GraphMonad a b d
-- graphRec f g u = cond isEmpty (return u)
--                               (do x <- f
--                                   y <- graphRec f g u
--                                   return (g x y))

-- | encapsulates a simple recursion schema on graphs
graphRec :: (GraphM m gr) => GT m (gr a b) c ->
                           (c -> d -> d) -> d -> GT m (gr a b) d
graphRec = recMGT isEmptyM

graphRec' :: (Graph gr,GraphM m gr) => GT m (gr a b) c ->
                           (c -> d -> d) -> d -> GT m (gr a b) d
graphRec' = recMGT' isEmpty

graphUFold :: (GraphM m gr) => (Context a b -> c -> c) -> c -> GT m (gr a b) c
graphUFold = graphRec getContext



----------------------------------------------------------------------
-- Examples: graph algorithms as instances of recursion operators
----------------------------------------------------------------------

-- instances of graphRec
--
graphNodesM0 :: (GraphM m gr) => GT m (gr a b) [Node]
graphNodesM0 = graphRec getNode (:) []

graphNodesM :: (GraphM m gr) => GT m (gr a b) [Node]
graphNodesM = graphUFold (\(_,v,_,_)->(v:)) []

graphNodes :: (GraphM m gr) => m (gr a b) -> m [Node]
graphNodes = runGT graphNodesM

graphFilterM :: (GraphM m gr) => (Context a b -> Bool) ->
                              GT m (gr a b) [Context a b]
graphFilterM p = graphUFold (\c cs->if p c then c:cs else cs) []

graphFilter :: (GraphM m gr) => (Context a b -> Bool) -> m (gr a b) -> m [Context a b]
graphFilter p = runGT (graphFilterM p)




----------------------------------------------------------------------
-- Example: monadic dfs algorithm(s)
----------------------------------------------------------------------

-- | Monadic graph algorithms are defined in two steps:
--
--  (1) define the (possibly parameterized) graph transformer (e.g., dfsGT)
--  (2) run the graph transformer (applied to arguments) (e.g., dfsM)
--

dfsGT :: (GraphM m gr) => [Node] -> GT m (gr a b) [Node]
dfsGT []     = return []
dfsGT (v:vs) = MGT (\mg->
               do (mc,g') <- matchM v mg
                  case mc of
                    Just (_,_,_,s) -> applyWith' (v:) (dfsGT (map snd s++vs)) g'
                    Nothing        -> apply' (dfsGT vs) g'  )

-- | depth-first search yielding number of nodes
dfsM :: (GraphM m gr) => [Node] -> m (gr a b) -> m [Node]
dfsM vs = runGT (dfsGT vs)

dfsM' :: (GraphM m gr) => m (gr a b) -> m [Node]
dfsM' mg = do {vs <- nodesM mg; runGT (dfsGT vs) mg}


-- | depth-first search yielding dfs forest
dffM :: (GraphM m gr) => [Node] -> GT m (gr a b) [Tree Node]
dffM vs = MGT (\mg->
          do g<-mg
             b<-isEmptyM mg
             if b||null vs then return ([],g) else
                let (v:vs') = vs in
                do (mc,g1) <- matchM v mg
                   case mc of
                     Nothing -> apply (dffM vs') (return g1)
                     Just c  -> do (ts, g2) <- apply (dffM (suc' c)) (return g1)
                                   (ts',g3) <- apply (dffM vs') (return g2)
                                   return (Node (node' c) ts:ts',g3)
          )

graphDff :: (GraphM m gr) => [Node] -> m (gr a b) -> m [Tree Node]
graphDff vs = runGT (dffM vs)

graphDff' :: (GraphM m gr) => m (gr a b) -> m [Tree Node]
graphDff' mg = do {vs <- nodesM mg; runGT (dffM vs) mg}
