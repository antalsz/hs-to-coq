module RecordConstruction where

data R = MkR { a :: Bool }

r :: R
r = MkR { a = True }
