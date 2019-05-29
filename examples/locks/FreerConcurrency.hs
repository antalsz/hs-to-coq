module FreerConcurrency where

import           Freer (IO')

data Action = Atom (IO' Action)
            | Fork Action Action
            | Stop

newtype Concurrency a = Concurrency ((a -> Action) -> Action)


instance Functor Concurrency where
   fmap k (Concurrency f) = Concurrency $ \c -> f (c . k)

instance Applicative Concurrency where
  pure x = Concurrency $ \c -> c x
  Concurrency k <*> Concurrency f = Concurrency $ \c ->
    f (\a -> k (\g -> c $ g a))

instance Monad Concurrency where
  return = pure
  Concurrency f >>= k = Concurrency $ \c ->
    f (\a -> case k a of Concurrency m -> m c)


action :: Concurrency a -> Action
action (Concurrency m) = m (const Stop)

atom :: IO' a -> Concurrency a
atom m = Concurrency $ \c -> Atom (do a <- m; return (c a))

stop :: Concurrency a
stop = Concurrency $ const Stop

par :: Concurrency a -> Concurrency a -> Concurrency a
par (Concurrency m1) (Concurrency m2) = Concurrency $ \c -> Fork (m1 c) (m2 c)

fork :: Concurrency a -> Concurrency ()
fork m = Concurrency $ \c -> Fork (action m) (c ())
