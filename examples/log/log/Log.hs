module Log (out, collect, Output) where

newtype Output a = Output {runO :: String -> (a, String)}

instance Functor Output where
  fmap f x = Output (\s -> let (a, s') = runO x s in (f a, s'))

instance Applicative Output where
  pure a  = Output ((,) a)
  f <*> a = Output (\s -> let (f', s') = runO f s in
                          let (a', s'') = runO a s' in
                          ((f' a'), s''))

instance Monad Output where
  return a = Output ((,) a)
  m >>= f  = Output (\s -> let (a, s') = runO m s in runO (f a) s')

out :: Char -> Output ()
out c = Output (\s -> ((), c : s))

collect :: Output () -> String
collect  m = let ((), s) = runO m [] in reverse s
