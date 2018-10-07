module Records where

data Rec = MkRec { field :: Bool }

foo :: Rec -> Rec
foo i1 = i1 { field = True }

bar :: Rec -> Rec
bar = foo
