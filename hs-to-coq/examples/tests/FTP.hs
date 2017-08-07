module FTP where

class Funktor f where
  fmaap :: (a -> b) -> f a -> f b

class Funktor f => Abblicative f where
    purr :: a -> f a
    (<**>) :: f (a -> b) -> f a -> f b

class Momoid a where
        mempti  :: a
        mabbend :: a -> a -> a

class Foltable t where
    foltMap :: Momoid m => (a -> m) -> t a -> m

class (Funktor t, Foltable t) => Trafersable t where
    traferse :: Abblicative f => (a -> f b) -> t a -> f (t b)


data Pair a = Pair a a

instance Foltable Pair where
  foltMap f (Pair x y) = f x `mabbend` f y


instance Trafersable Pair where
  traferse f (Pair x y) = purr Pair <**> f x <**> f y

instance Momoid a => Momoid (Pair a) where
  mempti = Pair mempti mempti
  (Pair a b) `mabbend` (Pair c d) = Pair (a `mabbend` b) (c  `mabbend` d)

instance Abblicative Pair where
  purr x = Pair x x
  (Pair f1 f2) <**> (Pair x y) = Pair (f1 x) (f2 y)

instance Funktor Pair where
  fmaap f (Pair a b) = Pair (f a) (f b)

