module MultiCore where

import Types
import Control.Monad
import Data.Traversable
import Data.Bits
import GHC.Conc (numCapabilities)
-- import Control.Concurrent.Async
import Data.Foldable
import System.IO
import System.Posix.Files
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.ByteString.Internal (c2w)
import GHC.IO.Handle

forConcurrently :: Traversable t => t a -> (a -> IO b) -> IO (t b)
forConcurrently = undefined

multiCoreCount :: FilePath -> IO Counts
multiCoreCount fp = do
    putStrLn ("Using available cores: " <> show numCapabilities)
    size <- fromIntegral . fileSize <$> getFileStatus fp
    let chunkSize = fromIntegral (size `div` numCapabilities)
    fold <$!> (forConcurrently [0..numCapabilities-1] $ \n -> do
        -- Take all remaining bytes on the last capability due to integer division anomolies
        let limiter = if n == numCapabilities - 1
                         then id
                         else BL.take (fromIntegral chunkSize)
        let offset = fromIntegral (n * chunkSize)
        fileHandle <- openBinaryFile fp ReadMode
        hSeek fileHandle AbsoluteSeek offset
        countBytes . limiter <$!> BL.hGetContents fileHandle)

countBytes :: BL.ByteString -> Counts
countBytes = BL.foldl' (\a b -> a <> countChar b) mempty
{-# INLINE countBytes #-}
