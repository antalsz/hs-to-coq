module MapAccumR where

-- This test demonstrates a bug in lifting where clauses.
-- we need to topo sort them even if they are not mutually recursive.

data List a = Nil | Cons a (List a)

mapAccumR :: (acc -> x -> (acc, y))     -- Function of elt of input list
                                        -- and accumulator, returning new
                                        -- accumulator and elt of result list
            -> acc              -- Initial accumulator
            -> List x           -- Input list
            -> (acc, List y)    -- Final accumulator and result list
mapAccumR _ s Nil         =  (s, Nil)
mapAccumR f s (Cons x xs) =  (s'', Cons y ys)
                           where (s'',y ) = f s' x
                                 (s', ys) = mapAccumR f s xs
