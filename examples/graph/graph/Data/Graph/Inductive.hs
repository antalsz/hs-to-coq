------------------------------------------------------------------------------
--
--  Inductive.hs -- Functional Graph Library
--
--  (c) 1999-2007 by Martin Erwig [see file COPYRIGHT]
--
------------------------------------------------------------------------------

module Data.Graph.Inductive
  ( module I
    -- * Version Information
  , version
  ) where

import Data.Graph.Inductive.Basic         as I
import Data.Graph.Inductive.Graph         as I
import Data.Graph.Inductive.Monad         as I
import Data.Graph.Inductive.Monad.IOArray as I
import Data.Graph.Inductive.NodeMap       as I
import Data.Graph.Inductive.PatriciaTree  as I
import Data.Graph.Inductive.Query         as I

import           Data.Version (showVersion)
import qualified Paths_fgl    as Paths (version)

-- | Version info
version :: IO ()
version = putStrLn $ "\nFGL - Functional Graph Library, version "
                      ++ showVersion Paths.version
