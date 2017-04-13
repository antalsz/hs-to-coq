{-# LANGUAGE TypeFamilies, PatternSynonyms, DataKinds, UndecidableInstances #-}

module Main where

import Data.Type.Equality

(+!) :: ()
(+!) = ()
infix 3 +!

data T = V

class C a where m :: a

instance C Int where m = 0
instance Show (a -> b)

type family TFO (a :: *) :: *
type instance TFO Int = Bool

type family TFC (a :: *) :: * where
  TFC Int  = Bool
  TFC Bool = Int
  TFC ()   = ()

type family TEq (a :: T) (b :: T) :: Bool where
  TEq 'V 'V = 'True

type instance a == b = TEq a b

pattern X = ()
pattern Y <- ~() where
  Y = minBound :: ()

main :: IO ()
main = pure ()
{-# VECTORIZE main = main #-}
{-# NOVECTORIZE (+!) #-}
  
{-# RULES
"map/map"    [2] forall f g xs.  map f (map g xs) = map (f.g) xs
"map/append" [~2] forall f xs ys. map f (xs ++ ys) = map f xs ++ map f ys
  #-}
