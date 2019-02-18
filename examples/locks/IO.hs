{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module IO where

-- General freer monads stuff

data Freer e r = Ret r | forall x. Vis (e x) (x -> Freer e r)

bind :: Freer e x -> (x -> Freer e y) -> Freer e y
bind (Ret x) f   = f x
bind (Vis e k) f = Vis e (\x -> bind (k x) f)

ret :: x -> Freer e x
ret = Ret

vis :: e x -> Freer e x
vis m = Vis m ret

instance Functor (Freer e) where
  fmap f x = bind x (ret . f)

instance Applicative (Freer e) where
  pure = ret
  fs <*> xs = bind fs (`fmap` xs)

instance Monad (Freer e) where
  xs >>= f = bind xs f

-- Specific mvar stuff

class Encodable a where
  encode :: a -> Int
  decode :: Int -> Maybe a

instance Encodable Int where
  encode = id
  decode = Just

instance Encodable (MVar a) where
  encode (MVar loc) = loc
  decode = Just . MVar

data MVar a = MVar Int

data MemEff :: (* -> *) -> * -> * where
  NewMV     :: MemEff m (m a)
  TakeMV    :: Encodable a => m a -> MemEff m a
  ReadMV    :: Encodable a => m a -> MemEff m a
  PutMV     :: Encodable a => m a -> a -> MemEff m ()
  TryTakeMV :: Encodable a => m a -> MemEff m (Maybe a)
  TryReadMV :: Encodable a => m a -> MemEff m (Maybe a)
  TryPutMV  :: Encodable a => m a -> a -> MemEff m Bool
  IsEmptyMV :: m a -> MemEff m Bool

type IO' = Freer (MemEff MVar)

newEmptyMVar :: IO' (MVar a)
newEmptyMVar = vis NewMV

takeMVar :: Encodable a => MVar a -> IO' a
takeMVar = vis . TakeMV

readMVar :: Encodable a => MVar a -> IO' a
readMVar = vis . ReadMV

putMVar :: Encodable a => MVar a -> a -> IO' ()
putMVar m = vis . PutMV m

newMVar :: Encodable a => a -> IO' (MVar a)
newMVar a = do
  m <- newEmptyMVar
  putMVar m a
  ret m

tryTakeMVar :: Encodable a => MVar a -> IO' (Maybe a)
tryTakeMVar = vis . TryTakeMV

tryReadMVar :: Encodable a => MVar a -> IO' (Maybe a)
tryReadMVar = vis . TryReadMV

tryPutMVar :: Encodable a => MVar a -> a -> IO' Bool
tryPutMVar m = vis . TryPutMV m

isEmptyMVar :: MVar a -> IO' Bool
isEmptyMVar = vis . IsEmptyMV
