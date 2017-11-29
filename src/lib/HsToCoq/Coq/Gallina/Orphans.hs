{-# OPTIONS_GHC -Wno-orphans #-}
-- |
-- This module contains orphan instancs to use string literatls to refer to
-- variables in terms, which is convenient when building expressions in the
-- Haskell code (e.g. in Monad.hs).
--
-- Orphans are frowned upon in libraries, but not quite as bad in programs.
-- We still put them in a separte module, to make it (somewhat) clear where
-- they are used.
module HsToCoq.Coq.Gallina.Orphans () where

import qualified Data.Text as T
import Data.String

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

-- For internal use only (e.g. hardcoded names)
instance IsString Term where
    fromString x = Qualid (unsafeIdentToQualid (T.pack x))
instance IsString Qualid where
    fromString x = unsafeIdentToQualid (T.pack x)
instance IsString Binder where
    fromString x = Inferred Explicit (Ident (unsafeIdentToQualid (T.pack x)))
