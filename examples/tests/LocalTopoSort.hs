module LocalTopoSort where

foo :: () -> ()
foo x = f x
  where
    f y = g y
    g y = y

bar :: () -> ()
bar x = f x
  where
    g y = y
    f y = g y
