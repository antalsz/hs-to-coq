module Counter (Counter, runC, inc) where

newtype Counter a = Counter { runC :: Int -> (a, Int) }

instance Functor Counter where
  fmap f x = Counter (\s -> let (a, s') = runC x s in (f a, s'))

instance Applicative Counter where
  pure a  = Counter ((,) a)
  f <*> a = Counter (\s -> let (f', s') = runC f s in
                           let (a', s'') = runC a s' in
                           (f' a', s''))

instance Monad Counter where
  return a = Counter ((,) a)
  m >>= f  = Counter (\s -> let (a, s') = runC m s in runC (f a) s')

inc :: Counter ()
inc = Counter (\x -> ((), x + 1))
