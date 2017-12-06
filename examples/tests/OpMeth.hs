module OpMeth where

-- example where using a method named 'op' fails to translate
-- correctly

class Magma a where
    op :: a -> a -> a

instance Magma Bool where op = (&&)
