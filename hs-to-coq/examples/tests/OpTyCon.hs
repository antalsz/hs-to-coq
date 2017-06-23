module OpTyCon where

class C t where
   m :: t a -> t a

instance C ((->) Int) where
   m = \x -> x
