-- This test demonstrates a bug in lifting where clauses.
-- we need to topo sort them even if they are not mutually recursive.

mapAccumR :: (acc -> x -> (acc, y))     -- Function of elt of input list
                                        -- and accumulator, returning new
                                        -- accumulator and elt of result list
            -> acc              -- Initial accumulator
            -> [x]              -- Input list
            -> (acc, [y])               -- Final accumulator and result list
mapAccumR _ s []        =  (s, [])
mapAccumR f s (x:xs)    =  (s'', y:ys)
                           where (s'',y ) = f s' x
                                 (s', ys) = mapAccumR f s xs
