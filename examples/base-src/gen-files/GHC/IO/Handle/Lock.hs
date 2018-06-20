{-# LINE 1 "libraries/base/GHC/IO/Handle/Lock.hsc" #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE InterruptibleFFI #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoImplicitPrelude #-}
module GHC.IO.Handle.Lock (
    FileLockingNotSupported(..)
  , LockMode(..)
  , hLock
  , hTryLock
  , hUnlock
  ) where




{-# LINE 17 "libraries/base/GHC/IO/Handle/Lock.hsc" #-}



import Data.Bits
import Data.Function
import Foreign.C.Error
import Foreign.C.Types
import GHC.IO.Exception
import GHC.IO.FD
import GHC.IO.Handle.FD


{-# LINE 56 "libraries/base/GHC/IO/Handle/Lock.hsc" #-}

import Data.Functor
import GHC.Base
import GHC.Exception
import GHC.IO.Handle.Types
import GHC.Show

-- | Exception thrown by 'hLock' on non-Windows platforms that don't support
-- 'flock'.
data FileLockingNotSupported = FileLockingNotSupported
  deriving Show

instance Exception FileLockingNotSupported

-- | Indicates a mode in which a file should be locked.
data LockMode = SharedLock | ExclusiveLock

-- | If a 'Handle' references a file descriptor, attempt to lock contents of the
-- underlying file in appropriate mode. If the file is already locked in
-- incompatible mode, this function blocks until the lock is established. The
-- lock is automatically released upon closing a 'Handle'.
--
-- Things to be aware of:
--
-- 1) This function may block inside a C call. If it does, in order to be able
-- to interrupt it with asynchronous exceptions and/or for other threads to
-- continue working, you MUST use threaded version of the runtime system.
--
-- 2) The implementation uses 'LockFileEx' on Windows and 'flock' otherwise,
-- hence all of their caveats also apply here.
--
-- 3) On non-Windows plaftorms that don't support 'flock' (e.g. Solaris) this
-- function throws 'FileLockingNotImplemented'. We deliberately choose to not
-- provide fcntl based locking instead because of its broken semantics.
--
-- @since 4.10.0.0
hLock :: Handle -> LockMode -> IO ()
hLock h mode = void $ lockImpl h "hLock" mode True

-- | Non-blocking version of 'hLock'.
--
-- @since 4.10.0.0
hTryLock :: Handle -> LockMode -> IO Bool
hTryLock h mode = lockImpl h "hTryLock" mode False

-- | Release a lock taken with 'hLock' or 'hTryLock'.
hUnlock :: Handle -> IO ()
hUnlock = unlockImpl

----------------------------------------


{-# LINE 177 "libraries/base/GHC/IO/Handle/Lock.hsc" #-}

lockImpl :: Handle -> String -> LockMode -> Bool -> IO Bool
lockImpl h ctx mode block = do
  FD{fdFD = fd} <- handleToFd h
  let flags = cmode .|. (if block then 0 else 4)
{-# LINE 182 "libraries/base/GHC/IO/Handle/Lock.hsc" #-}
  fix $ \retry -> c_flock fd flags >>= \case
    0 -> return True
    _ -> getErrno >>= \errno -> if
      | not block
      , errno == eAGAIN || errno == eACCES -> return False
      | errno == eINTR -> retry
      | otherwise -> ioException $ errnoToIOError ctx errno (Just h) Nothing
  where
    cmode = case mode of
      SharedLock    -> 1
{-# LINE 192 "libraries/base/GHC/IO/Handle/Lock.hsc" #-}
      ExclusiveLock -> 2
{-# LINE 193 "libraries/base/GHC/IO/Handle/Lock.hsc" #-}

unlockImpl :: Handle -> IO ()
unlockImpl h = do
  FD{fdFD = fd} <- handleToFd h
  throwErrnoIfMinus1_ "flock" $ c_flock fd 8
{-# LINE 198 "libraries/base/GHC/IO/Handle/Lock.hsc" #-}

foreign import ccall interruptible "flock"
  c_flock :: CInt -> CInt -> IO CInt


{-# LINE 264 "libraries/base/GHC/IO/Handle/Lock.hsc" #-}
